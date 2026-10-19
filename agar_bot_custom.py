#!/usr/bin/env python3
"""
agar_bot.py — complete autonomous Agar.io (mobile) bot.

Reverse-engineered from live captures of the real app.  Plain TCP, frames are
`4-byte big-endian length + protobuf`.  Two services are involved:

MATCHMAKER  <region>.mobile-live-v26.agario.miniclippt.com:9000
  C->S mt=70   {f58{f2:0}}                       -> S->C mt=104 {f104{f8:0}}
  C->S mt=119  {f111{}}                          -> S->C mt=120 {f112{f1:<key>}}
  C->S op1 zlib {f85{f1:<token>}, f109:51}       -> S->C profile (op1 zlib)
  C->S mt=23                                     (ack)
  C->S mt=27   {f99{f1:<party code>}}            -> S->C mt=98 (party lobby)
  C->S mt=110  {f96{f1:13, f2:""}}               -> S->C mt=33  ARENA REDIRECT
      mt=33: f39 { f2:<host>, f3:<port>, f1:"<serverId>.<epoch_ms>" }

ARENA NODE  <host>:<port>
  C->S mt=40   {f59{f1:"<serverId>.<epoch_ms>"}}   (reuse f39.f1 verbatim!)
  S->C mt=106  arena info        f100{f1{f3:host,f4:port,f1:id,f2:region}}
  S->C op1 zlib mt=88  full world snapshot  f81{f2,f1{f5,f2[entity]},f6:arena,f7:id}
  S->C mt=45   own player        f14{f1{f3:color, f2:score, f1:name}}
  S->C mt=90   world delta       f48{ f5:seq, f2+f6:[entity],
                                        f3:[{f2:victim, f1:eater}],
                                        f4:[removed ids] }
  S->C mt=102  leaderboard       f25{f2[{f3:color, f1:name}], f1:own score}
  S->C mt=70   ping {f58{f2:nonce}}   -> C->S mt=104 {f104{f8:nonce}}
  C->S mt=50   joystick {f53{f2:x, f3:y}}  unit vector, ~20 Hz

ENTITY
  f10 kind   2=food  3=virus  7=small  8=player cell
  f4  id     f5 {f2:x, f1:y} floats   f8 radius   ->  mass = (radius/10)**2
  f9  name   f3 colour   f6 uuid      f7 == 1  ->  THIS IS YOU

Radius calibration (verified against three independent anchors):
  food r=10.00 -> mass 1     virus r=100.01 -> mass 100     own r=31.623 -> 10.0
  (and own r stepped 31.623 / 33.166 / 34.641 / 36.056 == 10*sqrt(10..13))

Usage
  python agar_bot.py --region ap-southeast-1 --code QNVXJG --run 120
  python agar_bot.py --code QNVXJG --strategy hunt
  python agar_bot.py --token <base64> --nick me --run 300 --forever
  python agar_bot.py --replay capture-node-5.json     # offline brain test

Options: --region --code --token --nick --run --forever --strategy
         --tick --no-party --no-calibrate --stats-json --dump --replay
"""
from __future__ import annotations

import argparse
import base64
import configparser
import hashlib
import json
import math
import os
import queue
import random
import re
import select
import socket
import struct
import sys
import threading
import time
import urllib.error
import urllib.request
import zlib

HERE = os.path.dirname(os.path.abspath(__file__))

try:
    import follow_train as _follow_train
except ImportError:
    _follow_train = None  # type: ignore

# In-game command channel: the only text the game renders from the protocol is
# the entity NAME (nick).  If the operator sets their nick to "/code SGH6TG", a
# bot in the same arena sees that name in the world snapshot and acts on it. No
# install, no patch, no MITM, no DNS. Optional: the bot runs perfectly well
# without it. The module lives next to this file (D:\agarBot\nick_cmd.py). If it
# is missing or broken, the hook is a no-op. If the operator renames their nick,
# the command arrives in-game and the bot can answer by renaming itself, which the
# operator then reads inside the game. Reply nicks are applied on the next
# mt=110, i.e. on respawn.
try:
    import nick_cmd as _nick_cmd
except Exception:                                       # noqa: BLE001
    _nick_cmd = None  # type: ignore

# Discord / panel live knobs (nick, code, region, uid) without fleet restart.
try:
    _lc_dir = os.path.join(HERE, "bot")
    if _lc_dir not in sys.path:
        sys.path.insert(0, _lc_dir)
    import live_ctrl as _live_ctrl
except Exception:                                       # noqa: BLE001
    _live_ctrl = None  # type: ignore

# --------------------------------------------------------------------------- #
# constants
# --------------------------------------------------------------------------- #

DEFAULT_HOST = 'mobile-live-v26.agario.miniclippt.com'
MM_PORT = 9000
NODE_PORT = 9001          # fallback; the real port comes from the mt=33 redirect
TICK = 0.05               # 20 Hz joystick, matches the app

# Sentinel: stay on the matchmaker after party join/leave (no arena play).
PARTY_HOLD = '__party_hold__'
INLINE_ARENA = '__inline_arena__'   # matchmaker streams the world on its own socket

# Fleet-wide pin so every bot lands in the SAME Burst/party ROOM.
# Prefer world arena_id (works for INLINE + EC2). Host alone is not enough —
# Burst often hosts INLINE on the MM socket (proxy IP) and scatters rooms.
_bot_state_dir = os.environ.get("AGAR_STATE_DIR")
if not _bot_state_dir:
    if os.path.isdir(os.path.join(HERE, 'bot')):
        _bot_state_dir = os.path.join(HERE, 'bot')
    else:
        _bot_state_dir = HERE
try:
    os.makedirs(_bot_state_dir, exist_ok=True)
except Exception:
    pass

PARTY_ARENA_PIN = os.path.join(_bot_state_dir, 'party_arena_pin.json')
PARTY_ROOM_OPENER = os.path.join(_bot_state_dir, 'party_room_opener.json')
# Long enough for a 10-bot login storm (PACE + pin-hunt drops) without the
# fleet forgetting the operator shard and scattering to 2–3 visible.
PARTY_ARENA_PIN_TTL = 300.0
# Wrong-arena bail window — slightly under TTL so a fresh pin still migrates.
PARTY_ARENA_PIN_FRESH = 240.0
PARTY_ROOM_OPENER_TTL = 120.0
PARTY_ROOM_WAIT_S = 90.0


def _read_party_arena_pin():
    try:
        with open(PARTY_ARENA_PIN, encoding='utf-8') as f:
            d = json.load(f)
        if time.time() - float(d.get('ts', 0) or 0) > PARTY_ARENA_PIN_TTL:
            return None
        host = d.get('host') or ''
        arena_id = (d.get('arena_id') or '').strip()
        if not host and not arena_id:
            return None
        return {
            'host': host,
            'port': int(d.get('port') or NODE_PORT),
            'ts': float(d.get('ts') or 0),
            'seen_target': bool(d.get('seen_target')),
            'arena_id': arena_id,
            'code': (d.get('code') or '').strip().upper(),
        }
    except Exception:
        return None


def _write_party_arena_pin(host, port, seen_target=False, arena_id='', code=''):
    arena_id = (arena_id or '').strip()
    host = host or ''
    if not host and not arena_id:
        return
    cur = _read_party_arena_pin()
    # Never overwrite a pin that already saw the follow target with a blind one.
    if cur and cur.get('seen_target') and not seen_target:
        if arena_id and cur.get('arena_id') and arena_id != cur.get('arena_id'):
            return
        if (host and cur.get('host') and _is_pinable_arena_host(host)
                and _is_pinable_arena_host(cur.get('host'))
                and not _same_arena_host(host, cur.get('host'))):
            return
    # First writer wins the fleet ROOM (arena_id). Others remash toward it.
    if (cur and cur.get('arena_id') and arena_id
            and cur.get('arena_id') != arena_id and not seen_target):
        return
    try:
        os.makedirs(os.path.dirname(PARTY_ARENA_PIN), exist_ok=True)
        tmp = PARTY_ARENA_PIN + '.tmp'
        same_room = bool(
            cur and (
                (arena_id and cur.get('arena_id') == arena_id)
                or (host and cur.get('host')
                    and _same_arena_host(host, cur.get('host')))
            ))
        with open(tmp, 'w', encoding='utf-8') as f:
            json.dump({
                'host': host or (cur.get('host') if cur else ''),
                'port': int(port or (cur.get('port') if cur else NODE_PORT)
                            or NODE_PORT),
                'ts': time.time(),
                'seen_target': bool(
                    seen_target or (same_room and cur and cur.get('seen_target'))),
                'arena_id': arena_id or (cur.get('arena_id') if cur else ''),
                'code': (code or (cur.get('code') if cur else '')
                         or '').strip().upper(),
            }, f)
        os.replace(tmp, PARTY_ARENA_PIN)
    except Exception:
        pass


def _clear_party_arena_pin():
    try:
        if os.path.isfile(PARTY_ARENA_PIN):
            os.remove(PARTY_ARENA_PIN)
    except Exception:
        pass
    try:
        if os.path.isfile(PARTY_ROOM_OPENER):
            os.remove(PARTY_ROOM_OPENER)
    except Exception:
        pass


def _try_claim_room_opener(code: str) -> bool:
    """First bot claims the right to OPEN the Burst room; others wait for pin."""
    code = (code or '').strip().upper()
    if not code:
        return True
    try:
        os.makedirs(os.path.dirname(PARTY_ROOM_OPENER), exist_ok=True)
        if os.path.isfile(PARTY_ROOM_OPENER):
            try:
                with open(PARTY_ROOM_OPENER, encoding='utf-8') as f:
                    d = json.load(f)
                if (str(d.get('code') or '').upper() == code
                        and time.time() - float(d.get('ts', 0) or 0)
                        < PARTY_ROOM_OPENER_TTL):
                    return False
            except Exception:
                pass
        tmp = PARTY_ROOM_OPENER + '.tmp'
        with open(tmp, 'w', encoding='utf-8') as f:
            json.dump({'code': code, 'ts': time.time(), 'pid': os.getpid()}, f)
        os.replace(tmp, PARTY_ROOM_OPENER)
        return True
    except Exception:
        return True


def _same_fleet_room(pin, arena_id: str, host: str = '') -> bool:
    """True if this land matches the fleet pin (arena_id preferred)."""
    if not pin:
        return True
    want = (pin.get('arena_id') or '').strip()
    have = (arena_id or '').strip()
    if want and have:
        return want == have
    want_h = (pin.get('host') or '').strip()
    have_h = (host or '').strip()
    if want_h and have_h:
        if want_h == INLINE_ARENA or have_h == INLINE_ARENA:
            return want_h == have_h
        if _is_pinable_arena_host(want_h) and _is_pinable_arena_host(have_h):
            return _same_arena_host(want_h, have_h)
    return True


def _norm_arena_host(host) -> str:
    """Collapse ec2-A-B-C-D… and A.B.C.D to the same key."""
    if not host:
        return ''
    h = str(host).strip().lower()
    m = re.search(r'ec2-(\d+)-(\d+)-(\d+)-(\d+)', h)
    if m:
        return '.'.join(m.groups())
    if re.match(r'^\d{1,3}(?:\.\d{1,3}){3}$', h):
        return h
    return h


def _is_pinable_arena_host(host) -> bool:
    """Ignore SOCKS peer IPs / empty — only real arena node names."""
    if not host:
        return False
    h = str(host).lower()
    return ('amazonaws.com' in h or 'agario.miniclip' in h
            or bool(re.search(r'^ec2-\d+-\d+-\d+-\d+', h)))


def _same_arena_host(a, b) -> bool:
    na, nb = _norm_arena_host(a), _norm_arena_host(b)
    if not na or not nb:
        return True
    return na == nb


# The arena node answers mt=40 with this and then closes the socket.
# mt=97 is already known on the MATCHMAKER side (it is how a boost request is
# refused, see _activate_boosts), but it was never handled on the ARENA socket,
# so a refused join looked like "connection closed while waiting for node
# assignment" -- a message that points at the network instead of at the refusal.
#
# MEASURED (tools/_live_check3.log, 2026-09-30): `<- mt=97 (12b)
# hex=10021a08e80661e206020802` = {f109:97, f108{f1:2}}, `reader exit eof
# total=16b`, and NO cell ever spawned.  Every same-token redial and every
# 12 s wait that followed it was wasted, and the cause was invisible.
ARENA_REFUSAL_MT = 97


def _arena_refusal_code(m) -> int | None:
    """Reason code out of mt=97 {f108{f1:<code>}} (2 = refused)."""
    try:
        f108 = one(m.inner, 108)
        if f108 is None:
            return None
        code = one(fields(f108), 1)
        return int(code) if isinstance(code, int) else None
    except Exception:
        return None

# mt=98 {f41{f2:<status>, f1:{f3:code, f2:n, f1:[member]}}}
# Party codes are REGION-SCOPED, so a code from another region comes back
# as PARTY_NOT_FOUND with no payload at all.
PARTY_NOT_FOUND = 4
PARTY_JOINED = 5

# Region prefixes taken from the APK's GameConfiguration.json.  The region *is*
# the matchmaker hostname prefix.
REGIONS = {
    'us-east-1': 'us-east-1.' + DEFAULT_HOST,
    'us-east-2': 'us-east-2.' + DEFAULT_HOST,
    'us-west-1': 'us-west-1.' + DEFAULT_HOST,
    'ap-northeast-1': 'ap-northeast-1.' + DEFAULT_HOST,
    'ap-south-1': 'ap-south-1.' + DEFAULT_HOST,
    'ap-southeast-1': 'ap-southeast-1.' + DEFAULT_HOST,
    'eu-central-1': 'eu-central-1.' + DEFAULT_HOST,
    'eu-west-1': 'eu-west-1.' + DEFAULT_HOST,
    'eu-west-2': 'eu-west-2.' + DEFAULT_HOST,
    'eu-west-3': 'eu-west-3.' + DEFAULT_HOST,
    'sa-east-1': 'sa-east-1.' + DEFAULT_HOST,
    'me-south-1': 'me-south-1.' + DEFAULT_HOST,
}

# Config shortcuts users type without the AWS "-1" suffix.
REGION_ALIASES = {
    'eu-central': 'eu-central-1',
    'eu-west': 'eu-west-1',
    'ap-south': 'ap-south-1',
    'ap-southeast': 'ap-southeast-1',
    'us-east': 'us-east-1',
    'us-west': 'us-west-1',
}


def normalize_region(region: str | None) -> str:
    r = (region or '').strip().lower()
    if not r:
        return 'eu-central-1'
    return REGION_ALIASES.get(r, r)


# Matchmaker IPs observed live (host DNS sometimes hands out unreachable ones).
KNOWN_IPS = [
    '52.74.140.1', '52.74.140.136',
    '13.202.66.138', '13.202.85.79', '15.207.146.55',
]
KNOWN_IPS_BY_REGION = {
    'eu-central-1': ['18.195.77.186', '63.176.234.35', '63.179.160.38'],
    'eu-west-2': ['13.41.133.197', '16.60.254.103', '3.9.30.161'],
    'eu-west-3': ['13.36.50.160', '13.38.226.253', '15.236.65.71'],
    'ap-south-1': ['13.202.66.138', '13.202.85.79', '15.207.146.55'],
}

# entity kinds
K_FOOD, K_VIRUS, K_SMALL, K_CELL = 2, 3, 7, 8
EDIBLE_KINDS = (K_FOOD, K_SMALL)

# game rules (agar.io conventions, confirmed against the capture)
MASS_PER_RADIUS = 10.0          # mass = (r / 10) ** 2
EAT_RATIO = 1.15                # must be this much heavier to eat a cell
WALL_MARGIN = 520.0             # start steering away this far from a wall
PINNED_URGENCY = 0.6            # beyond this, wall escape overrides farming
STUCK_DISTANCE = 45.0           # moved less than this over STUCK_WINDOW => stuck
STUCK_WINDOW = 2.5
VIRUS_SPLIT_MASS = 130.0        # above this a virus splits you -> avoid
VIRUS_AVOID_MASS = 110.0


def host_for(region: str | None) -> str:
    """Region -> matchmaker hostname (accepts a full hostname too)."""
    if not region:
        return DEFAULT_HOST
    r = normalize_region(region)
    if r in REGIONS:
        return REGIONS[r]
    if '.mobile-live-' in r:
        return r
    return f'{r}.{DEFAULT_HOST}'


# --------------------------------------------------------------------------- #
# protobuf primitives
# --------------------------------------------------------------------------- #

def varint(n: int) -> bytes:
    out = bytearray()
    n = int(n) & 0xFFFFFFFFFFFFFFFF
    while n > 0x7F:
        out.append((n & 0x7F) | 0x80)
        n >>= 7
    out.append(n)
    return bytes(out)


def tag(f: int, wt: int) -> bytes:
    return varint((f << 3) | wt)


def vint(f: int, n: int) -> bytes:
    return tag(f, 0) + varint(n)


def ld(f: int, b) -> bytes:
    b = b.encode() if isinstance(b, str) else bytes(b)
    return tag(f, 2) + varint(len(b)) + b


def f32(f: int, v: float) -> bytes:
    return tag(f, 5) + struct.pack('<f', v)


def read_varint(b: bytes, i: int):
    sh = v = 0
    while i < len(b):
        x = b[i]
        i += 1
        v |= (x & 0x7F) << sh
        if not (x & 0x80):
            return v, i
        sh += 7
        if sh > 63:
            raise ValueError('varint too long')
    raise ValueError('eof')


def fields(b: bytes) -> list:
    """Parse a protobuf message into [(field, wiretype, value)] preserving order."""
    out = []
    i = 0
    while i < len(b):
        try:
            k, i = read_varint(b, i)
        except ValueError:
            break
        fn, wt = k >> 3, k & 7
        if not fn:
            break
        if wt == 0:
            try:
                v, i = read_varint(b, i)
            except ValueError:
                break
            out.append((fn, 0, v))
        elif wt == 2:
            try:
                l, i = read_varint(b, i)
            except ValueError:
                break
            out.append((fn, 2, b[i:i + l]))
            i += l
        elif wt == 5:
            out.append((fn, 5, b[i:i + 4]))
            i += 4
        elif wt == 1:
            out.append((fn, 1, b[i:i + 8]))
            i += 8
        else:
            break
    return out


def one(fl: list, n: int, default=None):
    for fn, _wt, v in fl:
        if fn == n:
            return v
    return default


def allv(fl: list, n: int) -> list:
    return [v for fn, _wt, v in fl if fn == n]


def as_f32(b, default=0.0) -> float:
    if not b or len(b) != 4:
        return default
    return struct.unpack('<f', b)[0]


def as_str(b) -> str:
    if b is None:
        return ''
    if isinstance(b, str):
        return b
    if isinstance(b, (bytes, bytearray)):
        return b.decode('utf8', 'ignore')
    return str(b)




def frame(body: bytes) -> bytes:
    return struct.pack('>I', len(body)) + body


def dns_query_a(host: str, ns: str, timeout=4.0) -> list:
    """Minimal UDP A-record query (stdlib only, no dnspython)."""
    q = b'\x12\x34\x01\x00\x00\x01\x00\x00\x00\x00\x00\x00'
    for part in host.split('.'):
        q += bytes([len(part)]) + part.encode()
    q += b'\x00\x00\x01\x00\x01'
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    s.settimeout(timeout)
    try:
        s.sendto(q, (ns, 53))
        data, _ = s.recvfrom(2048)
    finally:
        s.close()
    i = 12
    while i < len(data) and data[i] != 0:
        i += 1 + data[i]
    i += 5
    ancount = struct.unpack('>H', data[6:8])[0]
    out = []
    for _ in range(ancount):
        if data[i] & 0xC0 == 0xC0:
            i += 2
        else:
            while i < len(data) and data[i] != 0:
                i += 1 + data[i]
            i += 1
        rtype, _cls, _ttl, rdlen = struct.unpack('>HHIH', data[i:i + 10])
        i += 10
        rd = data[i:i + rdlen]
        i += rdlen
        if rtype == 1 and rdlen == 4:
            out.append('.'.join(str(x) for x in rd))
    return out


# --------------------------------------------------------------------------- #
# proxies
# --------------------------------------------------------------------------- #
#
# The matchmaker rate-limits per *source IP*, and the block follows us across
# regions and address families -- so a different source is the only way round
# it.  The protocol is plain TCP with no TLS, so a CONNECT tunnel is all we
# need; nothing has to be re-encrypted or MITM'd.
#
# One caveat worth stating plainly: this is for getting back to normal after
# tripping the limiter during debugging.  Rotating through a whole pool to get
# more logins than the limiter allows is abuse, not debugging.  One proxy, one
# attempt, same discipline as a direct connection.

def parse_proxy(spec: str):
    """'[user:pass@]host:port' -> (host, port, user, pass), or None."""
    spec = (spec or '').strip()
    if not spec:
        return None
    user = pw = ''
    if '@' in spec:
        cred, _, spec = spec.rpartition('@')
        user, _, pw = cred.partition(':')
    host, _, port = spec.rpartition(':')
    if not host or not port:
        raise ValueError(f'bad proxy spec {spec!r}; want [user:pass@]host:port')
    return host, int(port), user, pw


def _recv_until(sock, marker, limit=8192):
    buf = b''
    while marker not in buf and len(buf) < limit:
        chunk = sock.recv(512)
        if not chunk:
            break
        buf += chunk
    return buf


def http_connect(proxy, host, port, timeout=10.0):
    """HTTP CONNECT tunnel.  `proxy` is (host, port, user, pass)."""
    ph, pp, user, pw = proxy
    s = socket.create_connection((ph, pp), timeout=timeout)
    s.settimeout(timeout)
    hdr = f'CONNECT {host}:{port} HTTP/1.1\r\nHost: {host}:{port}\r\n'
    if user:
        tok = base64.b64encode(f'{user}:{pw}'.encode()).decode()
        hdr += f'Proxy-Authorization: Basic {tok}\r\n'
    try:
        s.sendall((hdr + '\r\n').encode())
        resp = _recv_until(s, b'\r\n\r\n')
        status = resp.split(b'\r\n', 1)[0].decode('latin1', 'replace')
        if ' 200' not in status:
            raise OSError(f'HTTP CONNECT refused: {status or "(no reply)"}')
        return s
    except Exception:
        s.close()
        raise


def socks5_connect(proxy, host, port, timeout=10.0):
    """SOCKS5 tunnel with optional username/password auth (RFC 1928/1929)."""
    ph, pp, user, pw = proxy
    s = socket.create_connection((ph, pp), timeout=timeout)
    s.settimeout(timeout)
    try:
        s.sendall(b'\x05\x02\x00\x02' if user else b'\x05\x01\x00')
        sel = s.recv(2)
        if len(sel) < 2:
            raise OSError('SOCKS5: short greeting')
        if sel[1] == 0x02:
            u, p = user.encode(), pw.encode()
            s.sendall(b'\x01' + bytes([len(u)]) + u + bytes([len(p)]) + p)
            r = s.recv(2)
            if len(r) < 2 or r[1] != 0:
                raise OSError('SOCKS5: username/password rejected')
        elif sel[1] != 0x00:
            raise OSError(f'SOCKS5: no acceptable auth method (0x{sel[1]:02x})')
        # IPv4 literal = ATYP 1 (proxy DNS of ec2-*.amazonaws.com often hangs).
        parts = host.split('.')
        if len(parts) == 4 and all(p.isdigit() and 0 <= int(p) <= 255 for p in parts):
            s.sendall(b'\x05\x01\x00\x01' + socket.inet_aton(host) +
                      struct.pack('>H', port))
        else:
            th = host.encode()
            s.sendall(b'\x05\x01\x00\x03' + bytes([len(th)]) + th +
                      struct.pack('>H', port))
        rep = s.recv(4)
        if len(rep) < 4:
            raise OSError('SOCKS5: short reply')
        if rep[1] != 0x00:
            raise OSError(f'SOCKS5: connect failed (rep={rep[1]})')
        atyp = rep[3]
        if atyp == 0x01:
            s.recv(6)
        elif atyp == 0x04:
            s.recv(18)
        elif atyp == 0x03:
            s.recv(s.recv(1)[0] + 2)
        return s
    except Exception:
        s.close()
        raise


def proxy_dial(proxy, host, port, timeout=10.0, protocol='auto'):
    """Tunnel to host:port through `proxy`, trying both protocols if unsure."""
    if protocol == 'socks5':
        return socks5_connect(proxy, host, port, timeout)
    if protocol == 'http':
        return http_connect(proxy, host, port, timeout)
    try:
        return socks5_connect(proxy, host, port, timeout)
    except Exception:
        return http_connect(proxy, host, port, timeout)


class Msg:
    """A decoded server frame."""
    __slots__ = ('op', 'mt', 'inner', 'top', 'size')

    def __init__(self, op, mt, inner, top, size):
        self.op, self.mt, self.inner, self.top, self.size = op, mt, inner, top, size

    def __repr__(self):
        return f'<Msg op={self.op} mt={self.mt} {self.size}b>'


def decode_frame(body: bytes) -> Msg:
    """Decode one length-prefixed frame body into a Msg (opcode 1 = zlib)."""
    top = fields(body)
    op = one(top, 2)
    if op == 2:
        pay = one(top, 3)
        inner = fields(pay) if pay is not None else []
        return Msg(2, one(inner, 109), inner, top, len(body))
    if op == 1:
        blob = one(top, 4)
        if blob is None:
            return Msg(1, None, [], top, len(body))
        try:
            raw = zlib.decompress(blob)
        except zlib.error:
            return Msg(1, None, [], top, len(body))
        inner = fields(raw)
        return Msg(1, one(inner, 109), inner, top, len(body))
    return Msg(op, None, [], top, len(body))


# --------------------------------------------------------------------------- #
# outbound packets
# --------------------------------------------------------------------------- #

# Field order below mirrors the real app byte-for-byte (protobuf does not care,
# but matching the capture exactly removes one class of "why did it fail").

def pkt_hello() -> bytes:                      # mt=70 ping, nonce 0
    return vint(2, 2) + ld(3, ld(58, vint(2, 0)) + vint(109, 70))


def pkt_hello2() -> bytes:                     # mt=119 client hello
    return vint(2, 2) + ld(3, vint(109, 119) + ld(111, b''))


def pkt_ack23() -> bytes:                      # mt=23
    return bytes.fromhex('10021a03e80617')


def pkt_ping(nonce: int) -> bytes:             # mt=70 with our own nonce
    return vint(2, 2) + ld(3, ld(58, vint(2, int(nonce))) + vint(109, 70))


def pkt_pong(nonce: int) -> bytes:             # mt=104 {f104{f1:nonce}} echo
    return vint(2, 2) + ld(3, ld(104, vint(1, int(nonce))) + vint(109, 104))


def pkt_party(code: str) -> bytes:             # mt=27 {f99{f1:<code>}}
    return vint(2, 2) + ld(3, ld(99, ld(1, code)) + vint(109, 27))


def pkt_create_party() -> bytes:
    """mt=49 {f3:empty}. Request matchmaker to generate a new party room.
    Miniclip responds with mt=37 carrying the new 6-character party code!
    """
    return vint(2, 2) + ld(3, vint(109, 49))


def pkt_leave_party(code: str = '') -> bytes:
    """Leave the current party.

    Verified byte-for-byte against the official client (capture 2026-09-25,
    session 36/40): leaving a party is a bare mt=80 with an empty body
    (10021a03e80650), NOT an mt=27.  The app sends this same mt=80 both to
    leave a party outright and immediately *before* joining a different code.
    The `code` argument is ignored and kept only for call-site compatibility.
    """
    return vint(2, 2) + ld(3, vint(109, 80))


def pkt_play(nick: str = '', game_type: int = 13) -> bytes:
    """mt=110 {f96{f1:<game_type>, f2:<nick>}}. Classic=13; Burst=learned id."""
    name = (nick or '').encode('utf-8')
    try:
        gt = int(game_type)
    except Exception:
        gt = 13
    if gt <= 0:
        gt = 13
    return vint(2, 2) + ld(3, ld(96, vint(1, gt) + ld(2, name)) + vint(109, 110))


def pkt_shop_buy(product_id: str) -> bytes:
    """mt=68 {f70{f1:<product_id>}}. Official client shop purchase (coins/rewards).
    Captured 2026-10-10 session 10: buying e.g. '1_xp_boost_3x_24h' or '1_mass_boost_3x_24h'.
    """
    return vint(2, 2) + ld(3, ld(70, ld(1, product_id)) + vint(109, 68))


def pkt_mass_boost(name: str = 'mass_boost_3x_24h') -> bytes:
    """mt=94 {f32{f1:<item>}}. The app sends this before play.

    Capture-main-22: Prince activates mass_boost_3x_24h, the server answers
    mt=43, and the next spawn is 132. A fresh guest does not own that item,
    so the same packet is refused and the spawn stays 10.
    """
    return vint(2, 2) + ld(3, ld(32, ld(1, name)) + vint(109, 94))


def is_persist_token(tok: str) -> bool:
    """App-saved identity (g2gD...), not the encrypted mt=51 wire ticket."""
    t = (tok or '').strip()
    return t.startswith('g2gD') or (len(t) < 200 and t.startswith('g2g'))


def handshake_key_from_mt120(msg) -> str:
    """f112.f1 = 44-char b64 / 32 raw bytes from login_handshake_response."""
    if msg is None:
        return ''
    f112 = one(msg.inner, 112)
    if not f112:
        return ''
    return as_str(one(fields(f112), 1))


def _b64d_raw(s: str) -> bytes:
    s = (s or '').replace('\r', '').replace('\n', '')
    return base64.b64decode(s + '=' * ((4 - len(s) % 4) % 4))


def _b64_crlf(raw: bytes, at: int = 208) -> str:
    """App wraps the ticket with a literal CRLF (208 for remint, 48 for v6)."""
    s = base64.b64encode(raw).decode('ascii')
    if len(s) > at:
        return s[:at] + '\r\n' + s[at:]
    return s


def _fb_account_parts():
    """233-byte credential + 152-char g2gD from the live Facebook login."""
    base = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'device_prefs')
    try:
        f2b = open(os.path.join(base, 'fb_f2.bin'), 'rb').read()
        f3b = open(os.path.join(base, 'fb_f3.bin'), 'rb').read()
    except Exception:
        return None
    if len(f2b) < 20 or len(f3b) < 20:
        return None
    return f2b, f3b


def _facebook_persist_token() -> str:
    """g2gD for the emulator Facebook account only."""
    base = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'device_prefs')
    for name in ('fb_account_token.txt', 'fb_f3.bin'):
        try:
            raw = open(os.path.join(base, name), 'rb').read().strip()
        except Exception:
            continue
        try:
            s = raw.decode('utf-8')
        except Exception:
            s = raw.decode('latin1', 'ignore')
        s = s.strip()
        if s.startswith('g2gD') and len(s) > 80:
            return s
    return ''


def _is_facebook_token(tok: str) -> bool:
    fb = _facebook_persist_token()
    return bool(fb and tok and tok.strip() == fb)


def _account_uuid() -> str:
    p = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                     'device_prefs', 'account_uuid.txt')
    try:
        t = open(p, encoding='utf8').read().strip()
        return t if t else ''
    except Exception:
        return ''


def _persist_embedded_uuid(persist: str) -> str:
    """16-byte id inside a g2gD account token, as a UUID string."""
    import base64
    import uuid
    try:
        raw = base64.b64decode(persist.strip())
    except Exception:
        return ''
    i = raw.find(bytes([109, 0, 0, 0, 16]))
    if i < 0 or i + 21 > len(raw):
        return ''
    try:
        return str(uuid.UUID(bytes=raw[i + 5:i + 21]))
    except Exception:
        return ''


_FLEET_UUIDS = None


def party_member_identity(entry: bytes) -> tuple[str, str]:
    """(display name, account uuid) out of one mt=98/mt=42 party member entry.

    The two account kinds use DIFFERENT layouts, and reading only one of them
    silently drops half the roster:

      * guest account     -> f3 = name, f1 = { f4 = <account uuid> }
      * registered (FB)   -> f3 = name, f2 = <account uuid>,
                             f1 = { f2: 5, f4 = <facebook numeric id>,
                                    f1 = <profile pic url>, f3 = <nick> }

    The registered layout is the trap: ``f1.f4`` exists but holds the Facebook
    id (``103699340801826``), a bare number with no dashes, so a parser that
    only looks there sees "no uuid" and drops the member.  That is why a real
    account was invisible in the roster while every guest bot parsed fine.
    """
    mf = fields(entry)
    nm = as_str(one(mf, 3))
    uu = ''
    cand = as_str(one(mf, 2))          # registered accounts: uuid at member f2
    if cand and '-' in cand:
        uu = cand
    if not uu:                          # guest accounts: uuid inside f1{f4}
        sub = one(mf, 1)
        if isinstance(sub, bytes):
            cand = as_str(one(fields(sub), 4))
            if cand and '-' in cand:
                uu = cand
    return nm, uu

# Arena uuids of the bots in THIS run, published by each bot as soon as it has
# a cell.  The uuid embedded in a g2gD token is a different identifier from the
# one the arena/party roster uses, so the token pool cannot be used to tell our
# bots from the human -- but the live cells can.
FLEET_UUID_FILE = os.path.join(_bot_state_dir, 'fleet_uuids.json')

# Shared party roster: every bot that joins the party code writes members
# here so siblings know "ye log isi party me hain" even if their own mt=98
# snapshot was incomplete.  Used by _friendly_uuids / _is_party_mate.
PARTY_ROSTER_FILE = os.path.join(_bot_state_dir, 'party_roster.json')
PARTY_ROSTER_MAX_AGE = 600.0  # 10 min — party codes are short-lived anyway

# Last place ANY bot of the fleet saw the follow target.  The arena only
# streams a window around us, so a bot that has never seen the human has no
# idea where to go.  Publishing the sighting means one bot finding them pulls
# the whole fleet in, instead of eight bots sweeping eight different arcs of a
# 11180-unit map and none of them ever crossing the target.
FLEET_TARGET_FILE = os.path.join(_bot_state_dir, 'fleet_target.json')
# How long a sighting stays good.  The target moves, but "walk to where they
# were 4 minutes ago" is enormously better than sweeping an 11180-unit map at
# random, and any bot that arrives re-publishes a fresh position.
#
# 60 s, not 300 s: the operator asked for a LIVE location.  A five-minute-old
# fix on a player who walks across the arena is worse than searching, because
# it makes every bot in the fleet walk confidently to an empty corner and then
# stand there.  A minute is roughly how long it takes the fastest bot to cross
# Target fix stays fresh for 25s; if player dies/moves, fleet fans out to find new spot
FLEET_TARGET_MAX_AGE = 60.0
# Publish every second rather than every three.  Eight bots all writing the
# same file is the reason for any throttle at all, but a 3 s gap means the
# freshest fix the fleet can see is already 3 s stale before it is even read.
SIGHTING_PUBLISH_S = 0.35

# How long a fix stays useful as a search centre before fanning out.
AREA_MEMORY = 240.0


APP_TARGET_FILE = os.path.join(_bot_state_dir, 'app_target.json')
# The app publishes its own cell position every second while it is piped
# through capture-server.js, so this stays fresh.  A slightly tighter window
# than the fleet sighting: the human is walking around, and a stale app fix
# would send the fleet to an empty corner.
APP_TARGET_MAX_AGE = 20.0

# How long the arena socket may go completely silent before we call it dead.
# A healthy node pushes snapshots several times a second and pings us (mt=104)
# on its own clock, so this only ever fires on a half-open connection -- the
# server or the SOCKS hop stopped sending without a FIN.  Without this the
# recv() loop spins on its 0.5 s timeout forever: no EOF, ar_closed never set,
# and the bot keeps playing against a world that stopped advancing.
# MEASURED: four of eight bots froze at spawn mass 14.0 for 100+ ticks this way.
ARENA_SILENT = 20.0

# Frames that prove only that the TCP path is alive, not that the MATCH is
# running.  The arena node pings (mt=70) on its own clock and we answer mt=104,
# so on a half-open-but-not-closed stream these keep arriving forever while
# snapshots stop.  The reader's silence deadline must ignore them, or it can
# never fire on the one failure it exists to catch.
ARENA_KEEPALIVE_MT = frozenset({70, 104})

# Every arena socket timeout, in seconds.  The arena is a STREAMING socket, so
# it must never be left in blocking mode (settimeout(None)):
#
#   sendall() on a blocking socket has no upper bound.  If the peer stops
#   reading -- which is exactly what a half-open SOCKS hop looks like -- the
#   call parks forever holding the GIL-free send lock, and because send() logs
#   only AFTER sendall returns, the bot goes completely silent: no
#   `[arena] reader exit`, no `[done]`, no traceback, and mainBot's poll()
#   still reports the process alive, so it is never restarted.
#   MEASURED (bot_run.log, 2026-09-30): bots #1 and #6 logged a FOLLOW line and
#   a [world] census and then produced ZERO further output for the remaining
#   ~2700 lines of the run while the other eight bots kept playing.
#
# A bounded send converts that silent hang into a catchable timeout, and a
# timed-out sendall may have written only part of a frame -- so the socket is
# torn down rather than retried (see _arena_send).
ARENA_SOCK_TIMEOUT = 2.0

# How many times a soft bail ([pin] / [stale] / wrong-arena) may re-dial the
# SAME arena node with the SAME bearer token before the caller falls back to a
# fresh matchmaker login.  A soft bail leaves the matchmaker session intact, so
# re-logging-in for it spends throttle budget for nothing -- and a 10-bot fleet
# doing that is a login storm, which produces more drops.
SOFT_REDIALS = 4

# How long the follow loop waits for the node to hand us a cell before it
# gives up on that node.  A node that completes the TCP handshake and then
# never spawns us is a dead end; waiting on it forever looks exactly like a
# dropped bot (process alive, nothing logged, nothing played).
NO_SELF_BAIL_S = 45.0

# If the play loop makes no progress at all for this long, the stall watchdog
# force-drops the arena so the caller can reconnect.  Must stay above the
# longest legitimate blocking stretch inside a play loop: the same-socket
# respawn window (20 s), leave-mode's mass dump (25 s) and the no-self-cell
# wait (NO_SELF_BAIL_S) all sit below it on purpose.
STALL_WATCH_S = 70.0

# Below this mass a follower is food for almost everything in a live arena, and
# the physics change: a spawn-mass cell outruns everything that can eat it, so
# it should LEAVE rather than bend.  Measured spawn mass on these accounts is
# 15-19 because the 3x boost grants 0 s (the wallet owns none), so this is the
# normal case, not an edge case.
TINY_MASS = 60.0

# How far a tiny cell looks for things that can eat it.  900 is the reference
# bot's `threat_radius`, and it is a FLOOR: config's `threat-radius` (280) was
# tuned for the sidestep that bigger cells use, and at spawn mass everything
# inside 900 is lethal.  `threat-radius` is read here, so the knob is no longer
# decorative -- raising it above 900 widens the tiny-cell escape.
TINY_FLEE_RADIUS = 900.0


def _app_target_sighting(want=None):
    """(x, y) of the human's own cell, straight from their own client.

    The capture proxy sits on the app's arena socket and decodes the
    f7==1 (self) entity out of every snapshot, so this is exact rather than
    inferred.  Preferred over the fleet sighting because it is always live
    and always the right player.

    `want` is the uuid we are actually following.  The beacon is published by
    whichever client happens to be piped through the proxy, and that is not
    always the right one -- the emulator account (1d3385dc) is a different
    human from the phone account (7603dde7) that owns ZTZ2MC.  Without this
    check the whole fleet would walk to the wrong player.
    """
    try:
        with open(APP_TARGET_FILE, encoding='utf8') as fh:
            d = json.load(fh)
        x, y, t = float(d['x']), float(d['y']), float(d['t'])
    except Exception:
        return None
    if time.time() - t > APP_TARGET_MAX_AGE:
        return None
    if want:
        u = str(d.get('uuid') or '').lower().strip()
        w_list = [w.strip().lower() for w in str(want).split(',') if w.strip()]
        if u and not any(u.startswith(w[:8]) or w.startswith(u[:8]) or u == w for w in w_list):
            return None
    return x, y, t


def _fleet_uid_ok(d, want=None) -> bool:
    """True if fleet beacon uuid or name matches the follow UID (prefix OK)."""
    if not want:
        return True
    u = str(d.get('uuid') or d.get('by') or '').lower().strip()
    nm = str(d.get('name') or '').lower().strip()
    w_list = [w.strip().lower() for w in str(want).split(',') if w.strip()]
    for w in w_list:
        if u and (u.startswith(w[:8]) or w.startswith(u[:8]) or u == w):
            return True
        if nm and (nm == w or w in nm or nm in w):
            return True
    return False



def _fleet_target_sighting(want=None):
    """(x, y, t[, vx, vy]) of the most recent target sighting, or None.

    Includes velocity so hunters lead a moving operator (COME TO ME).
    """
    try:
        with open(FLEET_TARGET_FILE, encoding='utf8') as fh:
            d = json.load(fh)
        x, y, t = float(d['x']), float(d['y']), float(d['t'])
        vx = float(d.get('vx') or 0.0)
        vy = float(d.get('vy') or 0.0)
    except Exception:
        return None
    if time.time() - t > FLEET_TARGET_MAX_AGE:
        return None
    if not _fleet_uid_ok(d, want):
        return None
    # Lead ahead of a moving target so bots arrive where you WILL be.
    age = max(0.0, time.time() - t)
    lead = min(1.2, 0.25 + age * 0.35)
    return x + vx * lead, y + vy * lead, t


def _fleet_target_raw(want=None):
    """(x, y, t) of the last sighting, ignoring how old it is.

    Only used to bias the *search*: once a fix is too old to walk to, a bot
    that falls back to a random sector has thrown away the single fact it
    knows about the human.  Sweeping a ring around the last known area keeps
    the fleet in the right neighbourhood so the next sighting comes from a
    bot that is already close enough to feed.
    """
    try:
        with open(FLEET_TARGET_FILE, encoding='utf8') as fh:
            d = json.load(fh)
        if not _fleet_uid_ok(d, want):
            return None
        return float(d['x']), float(d['y']), float(d['t'])
    except Exception:
        return None


def _target_hint(want=None):
    """(x, y, t) of the freshest known fix for the human, or None.

    Returns the timestamp as well as the position because the caller has to
    compare it against its OWN last sighting.  The old version returned a
    bare (x, y) and _seek_point always preferred the bot's private
    last_pos, which is kept for SEEK_MEMORY=600s -- so a bot that saw the
    human once spent the next ten minutes walking to that stale spot while
    its siblings were publishing a much newer fix.  Measured live: bots
    #3/#4/#5/#6 converged on the shared fix (6374,8089) while #0/#1/#2
    walked to their own ten-minute-old memories.
    """
    cands = [c for c in (_app_target_sighting(want),
                         _fleet_target_sighting(want)) if c]
    if not cands:
        return None
    return max(cands, key=lambda c: c[2])


def _fleet_live_uuids() -> set:
    """Arena uuids of sibling bots, as published to FLEET_UUID_FILE."""
    try:
        d = json.load(open(FLEET_UUID_FILE, encoding='utf8'))
    except Exception:
        return set()
    if not isinstance(d, dict):
        return set()
    # Drop stale entries (>30 min) so a previous run's uuids don't linger.
    now = time.time()
    out = set()
    for k, v in d.items():
        try:
            ts = float(v) if not isinstance(v, dict) else float(v.get('t', 0))
        except Exception:
            ts = now
        if now - ts < 1800.0:
            out.add(str(k).lower())
    return out


def _read_party_roster(want_code: str | None = None) -> tuple[str, dict[str, str], set[str]]:
    """Shared party roster -> (code, name->uuid, all_uuids).

    Empty if missing/stale, or if want_code is set and does not match.
    """
    try:
        d = json.load(open(PARTY_ROSTER_FILE, encoding='utf8'))
    except Exception:
        return '', {}, set()
    if not isinstance(d, dict):
        return '', {}, set()
    try:
        t = float(d.get('t') or 0)
    except Exception:
        return '', {}, set()
    if time.time() - t > PARTY_ROSTER_MAX_AGE:
        return '', {}, set()
    code = str(d.get('code') or '').strip().upper()
    if want_code:
        wc = str(want_code).strip().upper()
        if code and wc and code != wc:
            return '', {}, set()
    members = d.get('members') or {}
    if not isinstance(members, dict):
        members = {}
    name_map = {str(n): str(u).lower()
                for n, u in members.items() if n and u}
    uuids = {u for u in name_map.values() if u}
    return code, name_map, uuids


def _party_roster_names(want_code: str | None = None) -> set[str]:
    try:
        d = json.load(open(PARTY_ROSTER_FILE, encoding='utf8'))
    except Exception:
        return set()
    if not isinstance(d, dict):
        return set()
    try:
        if time.time() - float(d.get('t') or 0) > PARTY_ROSTER_MAX_AGE:
            return set()
    except Exception:
        return set()
    code = str(d.get('code') or '').strip().upper()
    if want_code:
        wc = str(want_code).strip().upper()
        if code and wc and code != wc:
            return set()
    members = d.get('members') or {}
    if not isinstance(members, dict):
        return set()
    return {str(n).lower() for n in members if n}


def _publish_party_roster(code: str, name_to_uuid: dict[str, str],
                          names: list[str] | None = None) -> None:
    """Merge this bot's party view into the shared roster file."""
    code = (code or '').strip().upper()
    if not code:
        return
    try:
        try:
            d = json.load(open(PARTY_ROSTER_FILE, encoding='utf8'))
            if not isinstance(d, dict):
                d = {}
        except Exception:
            d = {}
        # New party code replaces the old roster entirely.
        old_code = str(d.get('code') or '').strip().upper()
        members = dict(d.get('members') or {}) if old_code == code else {}
        if not isinstance(members, dict):
            members = {}
        for nm, uu in (name_to_uuid or {}).items():
            if not nm:
                continue
            if uu:
                members[str(nm)] = str(uu).lower()
            elif str(nm) not in members:
                members[str(nm)] = ''
        for nm in (names or []):
            if nm and str(nm) not in members:
                members[str(nm)] = ''
        out = {'code': code, 't': time.time(), 'members': members}
        tmp = PARTY_ROSTER_FILE + '.tmp'
        with open(tmp, 'w', encoding='utf8') as fh:
            json.dump(out, fh, indent=1, sort_keys=True)
        os.replace(tmp, PARTY_ROSTER_FILE)
    except Exception:
        pass


def _fleet_uuids() -> set:
    """Account uuids of every bot account in our own token pool.

    Each g2gD token carries the account uuid the arena stamps on that account's
    cells (f6) and that the party roster carries for each member.  Anything in
    the roster that is NOT in this set is a human, which is how the follow
    target is found without hard-coding a uuid that changes on every reinstall.
    """
    global _FLEET_UUIDS
    if _FLEET_UUIDS is not None:
        return _FLEET_UUIDS
    out = set()
    for p in (os.path.join(HERE, 'token.txt'),
              os.path.join(HERE, 'bot', 'token.txt')):
        try:
            for line in open(p, encoding='utf8'):
                u = _persist_embedded_uuid(line.strip())
                if u:
                    out.add(u.lower())
        except Exception:
            continue
    _FLEET_UUIDS = out
    return out


# Dumped from the official client (Java encryptAES128 during live login).
# Savedata AES is a different key; this one is protoEncryptionSecret.
_LOGIN_AES_KEY = b'Bn.uEbJ@QNnJb3Ly'
# azhar v4/v1 embed this device blob; v6 leaves f5 empty.
_AZHAR_DEVICE = (
    'g2gDYQFtAAAAEBHUxOaQz6aVHA8lIVHz6DxtAAAAVaraMwtVx6cL+nBRWKEUYcBxbfar'
    'SVtOTAKGlhLJt774ytfzVFwlXqqJwxcy3X9CHAE/lWhgbJJFItTmmFrN9gdysqTq0r4gnLk'
    'He/BZDwIRq4y6epQ='
)
# Only f1=3 (outer f3 / v6) is accepted on ap-south. f1=2 and f1=5 close
# the socket if we answer with a different outer field, so keep sending v6
# and let the next dial draw a fresh handshake.
_LOGIN_FMT_BY_F1 = {3: 'v6', 2: 'v6', 5: 'v6', 4: 'v4', 1: 'v1'}


def _decrypt_login_token(handshake_b64: str):
    """Decrypt mt=120. Returns plaintext bytes, or None."""
    try:
        from Crypto.Cipher import AES
        raw = _b64d_raw(handshake_b64)
        if len(raw) < 32:
            return None
        pt = AES.new(_LOGIN_AES_KEY, AES.MODE_CBC, raw[:16]).decrypt(raw[16:])
        if pt:
            pad = pt[-1]
            if isinstance(pad, int) and 1 <= pad <= 16 and pt.endswith(bytes([pad]) * pad):
                pt = pt[:-pad]
        return pt
    except Exception:
        return None


def _server_login_f1(handshake_b64: str):
    """Decrypt mt=120 token and return its f1 (picks v6/v4/v1)."""
    pt = _decrypt_login_token(handshake_b64)
    if not pt:
        return None
    return one(fields(pt), 1)


def _unique_device() -> str:
    """Per-login device string so v4 does not reuse the shared Guest account."""
    alphabet = 'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789-_+'
    return 'g2gD' + ''.join(random.choice(alphabet) for _ in range(140))


def encode_login_plaintext(persist: str, shape: str = 'f5') -> bytes:
    """Login blob the live app encrypts after mt=120.

    Successful captures for the same guest have used three outer wraps:

      f5 (capture-main-1):  outer{f1:2, f2:{f2:persist}, f3:ver}
      f2 (capture-main-10): outer{f1:2, f2:{f2:persist}, f3:ver}  # same inner, top=2
      f1 (capture-main-44): outer{f1:2, f2:ver, f3:{f2:persist}}

    Default is the latest live-app shape (f5).
    """
    ver = vint(1, 942) + ld(2, '26.6.0') + vint(3, 3) + vint(4, 530)
    tokens = ld(2, persist)
    shape = (shape or 'f5').lower()
    if shape in ('f1', 'remint_f1', 'old'):
        # version before token
        inner = vint(1, 2) + ld(2, ver) + ld(3, tokens)
        return ld(1, inner)
    if shape in ('f2', 'remint_f2'):
        inner = vint(1, 2) + ld(2, tokens) + ld(3, ver)
        return ld(2, inner)
    if shape in ('fb', 'fb1', 'fb2', 'fb3', 'fb4', 'fb5'):
        # Outer field is the handshake f1. Inner layout is from the live app.
        parts = _fb_account_parts()
        if not parts:
            raise OSError('facebook login parts missing')
        f2b, f3b = parts
        ver = vint(1, 942) + ld(2, '26.6.0') + vint(3, 3) + vint(4, 530)
        ident = ld(2, f2b) + ld(3, f3b)
        n = {'fb1': 1, 'fb2': 2, 'fb3': 3, 'fb4': 4, 'fb5': 5, 'fb': 2}[shape]
        if n == 1:
            inner = vint(1, 5) + ld(2, ver) + ld(3, ident)
        elif n == 3:
            inner = vint(3, 5) + ld(4, ver) + ld(5, ident)
        elif n == 4:
            inner = ld(3, ver) + ld(4, ident) + vint(5, 5)
        elif n == 5:
            inner = vint(1, 5) + ld(2, ident) + ld(3, ver)
        else:
            inner = ld(1, ident) + vint(2, 5) + ld(5, ver)
        return ld(n, inner)
    if shape in ('acct1', 'acct2', 'acct3', 'acct4', 'acct5', 'v1', 'v4', 'f5', 'remint_f5'):
        # Account layouts taken byte-for-byte from real eu-central-1 tickets
        # (captured_tokens_by_region.json & live PCAP). The matchmaker picks the outer
        # field number at random per connection and the login MUST answer with
        # that same field, so each value of f1 has its own layout:
        #
        #   f1=1  f1{ f1:2, f2:ver, f3{ f2:persist } }   <- 'acct1'
        #   f1=2  f2{ f1{ f2:persist }, f2:2, f5:ver }   <- 'acct2'
        #   f1=3  f3{ f3:2, f4:ver, f5{ f2:persist } }   <- 'acct3'
        #   f1=4  f4{ f3:ver, f4{ f2:persist }, f5:2 }   <- 'acct4'
        #   f1=5  f5{ f1:2, f2{ f2:persist }, f3:ver }   <- 'acct5'
        ver = vint(1, 942) + ld(2, '26.6.0') + vint(3, 3) + vint(4, 530)
        tok = ld(2, persist or '')
        if shape in ('acct1', 'v1'):
            inner = vint(1, 2) + ld(2, ver) + ld(3, tok)
            return ld(1, inner)
        if shape == 'acct2':
            inner = ld(1, tok) + vint(2, 2) + ld(5, ver)
            return ld(2, inner)
        if shape == 'acct3':
            inner = vint(3, 2) + ld(4, ver) + ld(5, tok)
            return ld(3, inner)
        if shape in ('acct4', 'v4'):
            inner = ld(3, ver) + ld(4, tok) + vint(5, 2)
            return ld(4, inner)
        inner = vint(1, 2) + ld(2, tok) + ld(3, ver)
        return ld(5, inner)
    if shape in ('v6', 'guest_v6', 'v2', 'guest_v2', 'v5', 'guest_v5',
                 'v6_acct', 'v2_acct', 'v5_acct'):
        ver6 = vint(1, 1054) + ld(2, '26.6.0') + vint(3, 3) + vint(4, 474)
        # Logged-in account: persist sits in f5. Guest leaves f5 empty.
        tail = ld(5, persist or '') if shape.endswith('_acct') else ld(5, b'')
        inner = vint(3, 2) + ld(4, ver6) + tail
        outer = 3
        if shape in ('v2', 'guest_v2', 'v2_acct'):
            outer = 2
        elif shape in ('v5', 'guest_v5', 'v5_acct'):
            outer = 5
        return ld(outer, inner)
    if shape in ('guest_v4',):
        ver6 = vint(1, 1054) + ld(2, '26.6.0') + vint(3, 3) + vint(4, 474)
        inner = ld(3, ver6) + ld(4, ld(2, persist or '')) + vint(5, 2)
        return ld(4, inner)
    if shape in ('guest_v1',):
        ver6 = vint(1, 1054) + ld(2, '26.6.0') + vint(3, 3) + vint(4, 474)
        inner = vint(1, 2) + ld(2, ver6) + ld(3, ld(2, persist or ''))
        return ld(1, inner)
    # f5 / remint / remint_f5 (current app)
    inner = vint(1, 2) + ld(2, tokens) + ld(3, ver)
    return ld(5, inner)


# App remints once (zlib, current outer f5).  Fallbacks exist but a single
# run must NOT burn them back-to-back — that is exactly the refuse loop
# the live app also hits (capture-main-6/7/8 = handshake ok, profile closed).
_LOGIN_STYLES = ('remint_f5',)
_LOGIN_FALLBACKS = ()  # enable manually if f5 stays refused after a long cool-down
_login_style_i = 0


def _next_login_style() -> str:
    global _login_style_i
    all_styles = _LOGIN_STYLES + _LOGIN_FALLBACKS
    if not all_styles:
        all_styles = ('remint_f5',)
    s = all_styles[_login_style_i % len(all_styles)]
    _login_style_i += 1
    return s


def remint_wire_ticket(persist: str, handshake_b64: str = '',
                       shape: str = 'f5') -> str:
    """Mint login_request_encrypted the way the official client does.

    AES-128-CBC, static key, random IV prepended to ciphertext (16+192=208),
    then base64 with a CRLF at index 208 — byte-identical to the app.
    Handshake is still required on the TCP session (mt=119/120) but is not
    the AES key.
    """
    from Crypto.Cipher import AES
    from Crypto.Util.Padding import pad

    pt = encode_login_plaintext(persist, shape=shape)
    iv = os.urandom(16)
    ct = AES.new(_LOGIN_AES_KEY, AES.MODE_CBC, iv).encrypt(pad(pt, 16))
    shape_l = (shape or '').lower()
    if shape_l.startswith('fb'):
        crlf_at = 448
    elif shape_l in (
        'v6', 'guest_v6', 'guest_v4', 'guest_v1',
        'v2', 'guest_v2', 'v5', 'guest_v5', 'v6_acct', 'v2_acct', 'v5_acct'):
        crlf_at = 48
    else:
        crlf_at = 208
    return _b64_crlf(iv + ct, at=crlf_at)


def pkt_login(token_b64: str, plain: bool = False) -> bytes:
    """mt=51 login.

    App (capture-main-30, successful profile): remint 282c ticket as
    opcode-1 zlib {f85{f1:ticket}, f109:51}.  Short persist/JWT stays
    opcode-2 uncompressed.  ``plain=True`` forces opcode-2 for a remint
    ticket (capture-main-14).
    """
    tok = token_b64.encode('latin1') if isinstance(token_b64, str) else token_b64
    inner = ld(85, ld(1, tok)) + vint(109, 51)
    persist = tok.startswith(b'g2gD') or tok.startswith(b'eyJ')
    if plain or persist or len(tok) <= 160:
        return vint(2, 2) + ld(3, inner)
    return vint(2, 1) + ld(4, zlib.compress(inner, 6))


def pkt_login_persist_identity(persist: str, uuid: str) -> bytes:
    """mt=51 identity login the client also sends: f85.f5 {f1:1, f4:g2gD, f5:uuid}.

    Byte-identical to capture-main-18 (opcode-2, 214b).  Used as a fallback
    when AES remint is refused — persist as f85.f1 is the wrong shape.
    """
    ident = vint(1, 1) + ld(4, persist) + ld(5, uuid)
    inner = ld(85, ld(5, ident)) + vint(109, 51)
    return vint(2, 2) + ld(3, inner)


def pkt_post_login_76() -> bytes:              # mt=76 empty (seen after every guest login)
    return vint(2, 2) + ld(3, vint(109, 76))


def pkt_settings99() -> bytes:
    """mt=99 {f10{f1:1}} — live app (capture-main-4/6/7) after login."""
    return vint(2, 2) + ld(3, ld(10, vint(1, 1)) + vint(109, 99))


def pkt_fcm(push_token: str = '') -> bytes:    # mt=74 {f52{f1:<fcm>}} zlib
    inner = ld(52, ld(1, push_token)) + vint(109, 74)
    return vint(2, 1) + ld(4, zlib.compress(inner, 6))


def pkt_client_event(tag_b64: str) -> bytes:   # mt=21 {f51{f1:<b64>}}
    return vint(2, 2) + ld(3, ld(51, ld(1, tag_b64)) + vint(109, 21))


def pkt_node_join(node_token: str) -> bytes:   # mt=40 {f59{f1:"<id>.<epoch>"}}
    return vint(2, 2) + ld(3, ld(59, ld(1, node_token)) + vint(109, 40))


def pkt_joy(x: float, y: float) -> bytes:      # mt=50 {f53{f2:y, f3:x}}
    # Ground truth: field 2 is vertical (+y down in arena), field 3 is horizontal (+x right in arena)
    return vint(2, 2) + ld(3, ld(53, f32(2, y) + f32(3, x)) + vint(109, 50))



# Arena actions -- captured 2026-09-24 from the official client (capture-node-6):
#   feed  (eject mass)  mt=69 {f30{}}   sent 13x while the player held FEED
#   split               mt=47 {f82{}}   sent 4x on SPLIT taps
#   leave game          mt=80 {}        sent once when quitting to the menu
# Direction of an eject/split is the current joystick heading (mt=50).
# Death respawn (capture 2026-09-28, arena session 5, 10 deaths): the app
# stays on the same node socket. It does not send mt=111. Each death is
#   C->S mt=12 {}  ->  S->C mt=8  ->  C->S mt=110 {f96{f1:13, f2:<nick>}}
# and the server answers with a fresh mt=88 snapshot.
def pkt_feed() -> bytes:                       # mt=69 {f30{}}
    return vint(2, 2) + ld(3, ld(30, b'') + vint(109, 69))


def pkt_split() -> bytes:                      # mt=47 {f82{}}
    return vint(2, 2) + ld(3, ld(82, b'') + vint(109, 47))


def pkt_leave_game() -> bytes:                 # mt=80 {}
    return vint(2, 2) + ld(3, vint(109, 80))


def pkt_continue() -> bytes:                   # mt=111 {f23{f1:1}}
    return vint(2, 2) + ld(3, ld(23, vint(1, 1)) + vint(109, 111))


def pkt_respawn() -> bytes:                    # mt=12 {}
    """Empty mt=12 the app sends on death, before mt=110. Capture session 5."""
    return vint(2, 2) + ld(3, vint(109, 12))


# --------------------------------------------------------------------------- #
# world model
# --------------------------------------------------------------------------- #

class Entity:
    __slots__ = ('id', 'kind', 'x', 'y', 'r', 'name', 'color', 'uuid',
                 'is_self', 'seen')

    def __init__(self, eid, kind=None, x=0.0, y=0.0, r=0.0, name=None,
                 color=None, uuid=None, is_self=False):
        self.id = eid
        self.kind = kind
        self.x, self.y, self.r = x, y, r
        self.name = name
        self.color = color
        self.uuid = uuid
        self.is_self = is_self
        self.seen = time.time()

    @property
    def mass(self) -> float:
        return max(1.0, (self.r / MASS_PER_RADIUS) ** 2)

    def dist_to(self, other) -> float:
        return math.hypot(self.x - other[0], self.y - other[1])

    def __repr__(self):
        return (f'<E{self.id} k{self.kind} ({self.x:.0f},{self.y:.0f}) '
                f'r{self.r:.1f} m{self.mass:.1f} {self.name or ""!r}>')


def parse_entity(buf: bytes, old: Entity | None = None) -> Entity:
    """Parse an entity blob.  Deltas are partial -> merge onto `old` if given."""
    fl = fields(buf)
    eid = one(fl, 4)
    if eid is None:
        eid = old.id if old else -1
    e = Entity(eid)
    if old is not None:
        e.kind, e.x, e.y, e.r = old.kind, old.x, old.y, old.r
        e.name, e.color, e.uuid, e.is_self = old.name, old.color, old.uuid, old.is_self

    kind = one(fl, 10)
    if kind is not None:
        e.kind = kind
    pos = one(fl, 5)
    if pos is not None:
        p = fields(pos)
        e.x = as_f32(one(p, 2), e.x)
        e.y = as_f32(one(p, 1), e.y)
    rad = one(fl, 8)
    if rad is not None:
        e.r = as_f32(rad, e.r)
    nm = one(fl, 9)
    if nm is not None:
        e.name = as_str(nm)
    col = one(fl, 3)
    if col is not None:
        e.color = col
    uu = one(fl, 6)
    if uu is not None:
        e.uuid = as_str(uu)
    f7 = one(fl, 7)
    if f7 is not None:
        e.is_self = (f7 == 1)
    return e


class World:
    """Everything the server has told us about the match."""

    def __init__(self):
        self.entities: dict[int, Entity] = {}
        self.seq = 0
        # Counts every snapshot/delta we actually applied.  Used to tell a
        # *stalled stream* from a *pinned cell*: if the world has not advanced
        # we cannot conclude anything about whether we are moving.
        self.updates = 0
        self.arena = 11180.0
        self.arena_id = ''
        self.self_id: int | None = None
        self.color = None
        self.score = None
        self.name = ''
        self.leaderboard: list[tuple[str, int]] = []
        self.rank = None
        self.eats: list[tuple[int, int]] = []      # (eater, victim)
        self.ate = 0                               # things WE ate
        self.entity_history: dict[int, tuple[str, str, float]] = {}
        # -- life cycle ---------------------------------------------------- #
        # The server announces a death explicitly: f48.f3 carries the eat pair
        # and f48.f4 removes our id.  Trusting that beats waiting for a timeout.
        # After death the server re-spawns us itself (mt=112 -> full mt=88
        # snapshot -> mt=45 own-info) under a NEW entity id, so `self_id` must
        # be rediscovered through `f7 == 1` -- see _resolve_self.
        self.dead = False
        self.dead_at = 0.0
        self.killed_by = None
        self.deaths = 0
        self.lives = 0
        self.snapshots = 0
        self.deltas = 0
        self.t_node = 0.0
        self.t_self = 0.0
        self.spawn_time = 0.0
        self.peak_mass = 0.0
        self.pings = 0

    # -- lookups ---------------------------------------------------------- #
    @property
    def self_ent(self) -> Entity | None:
        return self.entities.get(self.self_id) if self.self_id is not None else None

    @property
    def me(self) -> Entity | None:
        """Own cell: prefer the f7==1 entity, fall back to the colour match."""
        if self.self_id is not None:
            e = self.entities.get(self.self_id)
            if e is not None:
                return e
        return None

    @property
    def my_cells(self) -> list[Entity]:
        """All living cells belonging to our bot."""
        return [e for e in self.entities.values() if e.is_self and e.kind == K_CELL]

    @property
    def total_mass(self) -> float:
        own_cells = [e for e in self.entities.values() if e.is_self and e.kind == K_CELL]
        return sum(e.mass for e in own_cells) if own_cells else (self.me.mass if self.me else 0.0)

    def enemies(self):
        me = self.me
        if not me:
            return []
        out = []
        for e in self.entities.values():
            if e.kind == K_CELL and not e.is_self and e.id != me.id:
                dist = math.hypot(e.x - me.x, e.y - me.y)
                if e.mass >= me.mass * EAT_RATIO:
                    threat = 'THREAT'
                elif me.mass >= e.mass * EAT_RATIO:
                    threat = 'PREY'
                else:
                    threat = 'EQUAL'
                out.append({
                    'id': e.id,
                    'name': e.name or f'Enemy_{e.id}',
                    'mass': e.mass,
                    'radius': e.r,
                    'dist': dist,
                    'threat': threat,
                    'x': e.x,
                    'y': e.y
                })
        out.sort(key=lambda x: x['dist'])
        return out

    def cells(self):
        return [e for e in self.entities.values() if e.kind == K_CELL]

    def food(self):
        return [e for e in self.entities.values() if e.kind in EDIBLE_KINDS]

    def viruses(self):
        return [e for e in self.entities.values() if e.kind == K_VIRUS]

    # -- ingestion -------------------------------------------------------- #
    def apply(self, m: Msg, now: float | None = None) -> str:
        now = now or time.time()
        self.t_node = now
        mt = m.mt
        if mt == 88:
            self._snapshot(m, now)
            return 'snapshot'
        if mt == 90:
            self._delta(m, now)
            return 'delta'
        if mt == 45:
            self._own(m, now)
            return 'own'
        if mt == 102:
            self._leaderboard(m)
            return 'leaderboard'
        if mt == 106:
            return 'arena-info'
        if mt == 70:
            self.pings += 1
            return 'ping'
        return f'mt{mt}'

    def _mark_dead(self, eater, now: float):
        """Record our death once per life (idempotent).

        Called from the explicit server signals -- the eat pair in f48.f3 or
        the id removal in f48.f4 -- so we know we died the moment it happens
        instead of inferring it from a timeout.
        """
        # f48.f4 (id removed) can arrive before f48.f3 (eat pair), so take the
        # killer whenever it turns up but only count the death once.
        if eater is not None:
            self.killed_by = eater
        if self.dead:
            return
        self.dead = True
        self.dead_at = now
        self.deaths += 1

    def _resolve_self(self, now: float):
        """f7==1 marks our own cell; confirm with the colour from mt=45."""
        cands = [e for e in self.entities.values() if e.is_self and e.kind == K_CELL]
        if len(cands) > 1 and self.color is not None:
            exact = [e for e in cands if e.color == self.color]
            if exact:
                cands = exact
        if cands:
            best = max(cands, key=lambda e: e.r)
            if self.self_id != best.id:
                self.self_id = best.id
                self.spawn_time = now
                if self.dead:
                    # back in with a new id -> the server re-spawned us
                    self.dead = False
                    self.lives += 1
            self.t_self = now
        elif self.self_id is not None and self.self_id not in self.entities:
            # our cell was removed -> we died
            self.self_id = None
            if not self.dead:
                self._mark_dead(self.killed_by, now)

    def _snapshot(self, m: Msg, now: float):
        f81 = one(m.inner, 81)
        if f81 is None:
            return
        s = fields(f81)
        arena = one(s, 6)
        if arena is not None:
            self.arena = as_f32(arena, self.arena)
        aid = one(s, 7)
        if aid is not None:
            self.arena_id = as_str(aid)
        w = one(s, 1)
        if w is None:
            return
        new: dict[int, Entity] = {}
        for fn, _wt, v in fields(w):
            if fn == 2:
                e = parse_entity(v)
                new[e.id] = e
                self.entity_history[e.id] = (e.name or '', e.uuid or '', e.mass)
        self.entities = new
        self.snapshots += 1
        self.updates += 1
        self._resolve_self(now)

    def _delta(self, m: Msg, now: float):
        f48 = one(m.inner, 48)
        if f48 is None:
            return
        f = fields(f48)
        seq = one(f, 5)
        if seq is not None:
            self.seq = seq
        self.updates += 1
        for fn, _wt, v in f:
            if fn in (2, 6):
                eid = one(fields(v), 4)
                old = self.entities.get(eid) if eid is not None else None
                e = parse_entity(v, old)
                self.entities[e.id] = e
                self.entity_history[e.id] = (e.name or '', e.uuid or '', e.mass)
            elif fn == 4:                      # removed ids
                self.entities.pop(v, None)
                if v == self.self_id:
                    remaining_self = [e for e in self.entities.values() if e.is_self and e.kind == K_CELL]
                    if remaining_self:
                        self.self_id = max(remaining_self, key=lambda e: e.r).id
                    else:
                        self._mark_dead(self.killed_by, now)
            elif fn == 3:                      # eat event {f2:victim, f1:eater}
                p = fields(v)
                victim, eater = one(p, 2), one(p, 1)
                if eater is not None and victim is not None:
                    self.eats.append((eater, victim))
                    if eater == self.self_id:
                        self.ate += 1
                    if victim == self.self_id:
                        # someone ate us: check if other self cells remain
                        self.entities.pop(victim, None)
                        remaining_self = [e for e in self.entities.values() if e.is_self and e.kind == K_CELL]
                        if remaining_self:
                            self.self_id = max(remaining_self, key=lambda e: e.r).id
                        else:
                            self._mark_dead(eater, now)

        if len(self.eats) > 200:
            self.eats = self.eats[-200:]
        self.deltas += 1
        self._resolve_self(now)
        me = self.me
        if me is not None:
            self.peak_mass = max(self.peak_mass, me.mass)

    def _own(self, m: Msg, now: float):
        f14 = one(m.inner, 14)
        if f14 is None:
            return
        f1 = one(fields(f14), 1)
        if f1 is None:
            return
        f = fields(f1)
        col, score, name = one(f, 3), one(f, 2), one(f, 1)
        if col is not None:
            self.color = col
        if score is not None:
            self.score = score
        if name is not None:
            self.name = as_str(name)
        self._resolve_self(now)

    def _leaderboard(self, m: Msg):
        """Leaderboard (a top-N list) plus our own score.

        An entry is ``{f1: name, f3: score}``.  Note there is deliberately no
        colour in this message, so the previous attempt at a rank was comparing
        our *colour* against other players' *scores* -- it either never matched
        (rank stuck at None) or matched by coincidence and reported a rank that
        was simply wrong.

        The board is a top-N, so scoring below the lowest listed entry means we
        are not on the board: that is ``None``, not "rank N+1".
        """
        f25 = one(m.inner, 25)
        if f25 is None:
            return
        f = fields(f25)
        entries = []
        for fn, _wt, v in f:
            if fn == 2:
                e = fields(v)
                sc = one(e, 3)
                entries.append((as_str(one(e, 1)),
                                sc if isinstance(sc, int) else None))
        self.leaderboard = entries
        sc = one(f, 1)
        if sc is not None:
            self.score = sc
        self.rank = self._rank_of(entries, sc)

    @staticmethod
    def _rank_of(entries, score):
        """Our position on a top-N board, or None when we are not on it."""
        if score is None:
            return None
        listed = [s for _nm, s in entries if isinstance(s, int)]
        if not listed or score < min(listed):
            return None
        return sum(1 for s in listed if s > score) + 1

    def stats(self) -> dict:
        me = self.me
        now = time.time()
        return {
            'alive': me is not None,
            'mass': round(me.mass, 1) if me else 0,
            'total_mass': round(self.total_mass, 1),
            'radius': round(me.r, 1) if me else 0,
            'score': self.score,
            'rank': self.rank,
            'x': round(me.x) if me else None,
            'y': round(me.y) if me else None,
            'ate': self.ate,
            'deaths': self.deaths,
            'lives': self.lives,
            'dead': self.dead,
            'killed_by': self.killed_by,
            'peak_mass': round(self.peak_mass, 1),
            'uptime': round(now - self.spawn_time, 1) if me else 0,
            'entities': len(self.entities),
            'enemies': len(self.enemies()),
            'food': sum(1 for e in self.entities.values() if e.kind in EDIBLE_KINDS),
            'cells': sum(1 for e in self.entities.values() if e.kind == K_CELL),
            'viruses': sum(1 for e in self.entities.values() if e.kind == K_VIRUS),
            'arena': round(self.arena),
            'seq': self.seq,
        }

    def minimap(self, limit=400) -> list:
        """Compact entity list for a live map in the control panel."""
        me = self.me
        out = []
        for e in self.entities.values():
            out.append({
                'id': e.id, 'k': e.kind,
                'x': round(e.x), 'y': round(e.y),
                'r': round(e.r, 1), 'm': round(e.mass, 1),
                's': 1 if (me is not None and e.id == me.id) else 0,
                'n': (e.name or '')[:16],
            })
            if len(out) >= limit:
                break
        return out


# --------------------------------------------------------------------------- #
# heading calibration
# --------------------------------------------------------------------------- #

class HeadingMap:
    """Maps a commanded joystick vector to the direction the cell really moves.

    Most likely identity, but the app->server input path is lossy, so the bot
    measures the response to two probe moves at spawn and inverts the result.
    Any rotation *or* axis swap is handled, and a bad calibration is rejected.
    """

    def __init__(self):
        self.A = (1.0, 0.0, 0.0, 1.0)      # observed = A . commanded
        self.calibrated = False
        self.note = 'identity'

    def build(self, vx, vy):
        """vx/vy = net displacement measured while commanding +x / +y."""
        ax = math.hypot(*vx)
        ay = math.hypot(*vy)
        if ax < 1e-6 or ay < 1e-6:
            self.note = 'identity (no motion during probe)'
            return
        a = (vx[0] / ax, vx[1] / ax)
        b = (vy[0] / ay, vy[1] / ay)
        # sanity: the two basis responses must not be collinear
        if abs(a[0] * b[1] - a[1] * b[0]) < 0.35:
            self.note = 'identity (degenerate probe)'
            return
        self.A = (a[0], b[0], a[1], b[1])
        self.calibrated = True
        ang = math.degrees(math.atan2(a[1], a[0]))
        swap = abs(b[0]) > abs(b[1])
        self.note = f'rotated {ang:+.1f}deg{" + axis-swapped" if swap else ""}'

    def command(self, desired) -> tuple[float, float]:
        dx, dy = desired
        n = math.hypot(dx, dy)
        if n < 1e-9:
            return 0.0, 0.0
        dx, dy = dx / n, dy / n
        a, b, c, d = self.A
        det = a * d - b * c
        if abs(det) < 0.2:
            return dx, dy
        cx = (d * dx - b * dy) / det
        cy = (-c * dx + a * dy) / det
        n = math.hypot(cx, cy)
        if n < 1e-9:
            return dx, dy
        cx, cy = cx / n, cy / n
        # never deviate more than 70 deg from the desired heading
        dot = max(-1.0, min(1.0, cx * dx + cy * dy))
        ang = math.degrees(math.acos(dot))
        if ang <= 70.0:
            return cx, cy
        return _rotate(dx, dy, math.copysign(70.0, _cross(dx, dy, cx, cy)))


def _rotate(x, y, deg):
    r = math.radians(deg)
    c, s = math.cos(r), math.sin(r)
    return x * c - y * s, x * s + y * c


def _cross(ax, ay, bx, by):
    return ax * by - ay * bx


# --------------------------------------------------------------------------- #
# brain
# --------------------------------------------------------------------------- #

class Brain:
    """Chooses a heading every decision tick.

    Priority:  survive -> (optionally) hunt -> farm food -> wander.
    """

    def __init__(self, strategy='balanced', seed=None):
        self.strategy = strategy
        self.rng = random.Random(seed if seed is not None else 0xA6A7)
        self.heading = (1.0, 0.0)
        self.mode = 'idle'
        self.target = None
        self.danger = 0.0
        self.wander_until = 0.0
        self.last_decision = 0.0
        # Wall escape / progress tracking.  ``safe_heading`` is the last
        # heading known to point away from a wall; it is what we fall back
        # on when the escape vector degenerates to nothing.
        self.safe_heading = (1.0, 0.0)
        self.wall_urgency = 0.0
        self.win_pos = None
        self.win_t = 0.0
        self.win_updates = 0
        self.stuck = False
        self.stalled = False

    def reset(self):
        """Forget per-life state after a respawn.

        The heading is deliberately dropped: whatever we were fleeing no
        longer exists, and carrying it over would drive the fresh cell
        straight back into the same fight.
        """
        self.heading = (1.0, 0.0)
        self.mode = 'idle'
        self.target = None
        self.danger = 0.0
        self.wander_until = 0.0
        self.last_decision = 0.0
        # We respawn somewhere else entirely, so the progress window must be
        # re-based; keeping the old one would read as "moved a lot" and mask
        # a genuine corner pin.
        self.wall_urgency = 0.0
        self.win_pos = None
        self.win_t = 0.0
        self.win_updates = 0
        self.stuck = False
        self.stalled = False

    # -- helpers ---------------------------------------------------------- #
    def _threats(self, w: World, me: Entity):
        """Cells that can eat us, sorted by how close the *bodies* are."""
        out = []
        for e in w.entities.values():
            if e.id == me.id or e.kind != K_CELL:
                continue
            if e.mass <= me.mass * EAT_RATIO:
                continue
            gap = math.hypot(e.x - me.x, e.y - me.y) - e.r - me.r
            # a much heavier cell is a threat from further away
            reach = 300.0 + 220.0 * min(2.0, e.mass / max(me.mass * 6.0, 1.0))
            if gap < reach:
                out.append((gap, e))
        out.sort(key=lambda t: t[0])
        return out

    def _nearby_predators(self, w: World, me: Entity, radius: float = 1200.0):
        """Find any enemy player cell with dangerous mass (>= 0.85x our mass) within radius."""
        predators = []
        for e in w.entities.values():
            if e.id == me.id or e.kind != K_CELL or getattr(e, 'is_self', False):
                continue
            # If enemy has at least 85% of our mass, they are dangerous if we split
            if e.mass >= me.mass * 0.85:
                d = math.hypot(e.x - me.x, e.y - me.y)
                if d <= radius:
                    predators.append((d, e))
        predators.sort(key=lambda t: t[0])
        return predators

    def _hazards(self, w: World, me: Entity):
        """Viruses: harmless while small (< VIRUS_AVOID_MASS).
        When big (>= VIRUS_AVOID_MASS):
        - If dangerous predator is nearby, virus is a deadly HAZARD (stay far away).
        - If NO predator is nearby, virus is NOT a hazard (we will eat it for +100 mass!).
        """
        if me.mass < VIRUS_AVOID_MASS:
            return []
        # If area is clear of big enemies, we want to farm the virus!
        if not self._nearby_predators(w, me, 1200.0):
            return []
        out = []
        for e in w.entities.values():
            if e.kind != K_VIRUS:
                continue
            gap = math.hypot(e.x - me.x, e.y - me.y) - e.r - me.r
            if gap < 360.0:
                out.append((gap, e))
        out.sort(key=lambda t: t[0])
        return out

    def _food_candidates(self, w, me, reach, limit=64):
        cand = []
        has_predators = bool(self._nearby_predators(w, me, 1200.0))
        for e in w.entities.values():
            # Standard food: pellets (K_FOOD = 2) and token feed / drops (K_SMALL = 7)
            if e.kind in EDIBLE_KINDS:
                d = math.hypot(e.x - me.x, e.y - me.y)
                if d <= reach:
                    cand.append((d, e))
            # VIRUS FARMING: Eat virus when big enough (>= 125 mass) AND no big enemy nearby!
            elif e.kind == K_VIRUS and me.mass >= 125.0 and not has_predators:
                d = math.hypot(e.x - me.x, e.y - me.y)
                if d <= reach:
                    cand.append((d, e))

        # Priority ordering:
        # 0: K_SMALL (tokens / ejected feeds in Burst Arena) -> absolute #1 priority
        # 1: K_VIRUS (safe virus for massive 100 mass) -> #2 priority
        # 2: K_FOOD (pellets) -> standard food
        def _pri(ent):
            if getattr(ent, 'kind', None) == K_SMALL:
                return 0
            if getattr(ent, 'kind', None) == K_VIRUS:
                return 1
            return 2

        cand.sort(key=lambda t: (_pri(t[1]), t[0]))
        return cand[:limit]

    @staticmethod
    def _food_score(me, e, cand, d):
        """Nearest-first, but tokens and viruses get huge multipliers.
        - K_SMALL (Tokens in Burst Arena / Ejected mass): 25x priority boost!
        - K_VIRUS (Popping safe virus for +100 mass): 50x priority boost!
        """
        near = 0
        for d2, o in cand:
            if o.id == e.id:
                continue
            if abs(o.x - e.x) < 140 and abs(o.y - e.y) < 140:
                near += 1
                if near >= 6:
                    break

        kind = getattr(e, 'kind', None)
        if kind == K_SMALL:
            mult = 25.0
        elif kind == K_VIRUS:
            mult = 50.0
        else:
            mult = 1.0

        return mult * (1.0 + 0.6 * near) / (d + 45.0)

    def decide(self, w: World, now: float):
        me = w.me
        if me is None:
            self.mode = 'waiting'
            self.heading = (0.0, 0.0)
            self.win_pos = None
            return self.heading

        self._update_motion(w, me, now)
        threats = self._threats(w, me)
        hazards = self._hazards(w, me)

        # ---- 1. survive -------------------------------------------------- #
        if threats:
            d0, t0 = threats[0]
            self.danger = max(0.0, 1.0 - d0 / 420.0)
            fx = fy = 0.0
            for d, e in threats[:6]:
                wgt = (500.0 / max(d, 40.0)) ** 2
                ux, uy = me.x - e.x, me.y - e.y
                n = math.hypot(ux, uy) or 1.0
                fx += wgt * ux / n
                fy += wgt * uy / n
            self.heading = self._blend(self.heading, (fx, fy), 0.55)
            self.mode = f'FLEE {t0.mass:.0f}>{me.mass:.0f}'
            self.target = t0.id
            return self._final_heading(w, me, self.heading, now)

        self.danger = 0.0
        # gentle repulsion so we drift away instead of sitting in a lap
        rep = self._repel(me, threats, hazards)

        # ---- 2. hunt (optional) ------------------------------------------ #
        if self.strategy in ('hunt', 'balanced'):
            reach = 760.0 if self.strategy == 'hunt' else 460.0
            best, bs = None, 0.0
            for e in w.entities.values():
                if e.kind != K_CELL or e.id == me.id:
                    continue
                if e.mass * EAT_RATIO >= me.mass:
                    continue
                d = math.hypot(e.x - me.x, e.y - me.y)
                if d > reach:
                    continue
                ratio = me.mass / max(e.mass, 1.0)
                s = ratio * (2.4 if self.strategy == 'hunt' else 1.0) / (d + 90.0)
                if s > bs:
                    best, bs = e, s
            if best is not None and bs > 0.004:
                self.target = best.id
                self.mode = f'HUNT m{best.mass:.0f}'
                h = (best.x - me.x + rep[0], best.y - me.y + rep[1])
                self.heading = self._blend(self.heading, h, 0.4)
                return self._final_heading(w, me, self.heading, now)

        # ---- 3. farm tokens, safe viruses & food -------------------------- #
        cand = self._food_candidates(w, me, 1600.0)
        best, bs = None, 0.0
        for d, e in cand:
            s = self._food_score(me, e, cand, d)
            if s > bs:
                best, bs = e, s
        if best is not None:
            self.target = best.id
            if best.kind == K_SMALL:
                self.mode = 'EAT_TOKEN'
            elif best.kind == K_VIRUS:
                self.mode = f'EAT_VIRUS (m:{me.mass:.0f})'
            else:
                self.mode = 'EAT_PELLET'
            h = (best.x - me.x + rep[0] * 1.5, best.y - me.y + rep[1] * 1.5)
            self.heading = self._blend(self.heading, h, 0.35)
            return self._final_heading(w, me, self.heading, now)

        # ---- 4. wander --------------------------------------------------- #
        if now > self.wander_until:
            a = self.rng.uniform(0, 2 * math.pi)
            self.heading = (math.cos(a), math.sin(a))
            self.wander_until = now + self.rng.uniform(2.0, 4.0)
        self.mode = 'WANDER'
        self.target = None
        return self._final_heading(w, me, self.heading, now)

    @staticmethod
    def _repel(me, threats, hazards):
        """Small outward push from anything dangerous that is nonetheless far."""
        fx = fy = 0.0
        for d, e in list(threats)[:4] + list(hazards)[:4]:
            wgt = 60.0 / max(d + 200.0, 1.0)
            ux, uy = me.x - e.x, me.y - e.y
            n = math.hypot(ux, uy) or 1.0
            fx += wgt * ux / n
            fy += wgt * uy / n
        return fx, fy


    # -- walls ------------------------------------------------------------ #
    def _wall_vec(self, w: World, me: Entity):
        """Raw escape vector: points away from whichever walls we are near.

        Magnitude is 0 at ``WALL_MARGIN`` from a wall and 1 when touching
        it, so ``max(|x|, |y|)`` doubles as a 0..1 "how pinned am I" value.
        """
        if w.arena <= 0:
            return 0.0, 0.0
        m = WALL_MARGIN
        bx = by = 0.0
        if me.x < m:
            bx += (m - me.x) / m
        elif me.x > w.arena - m:
            bx -= (me.x - (w.arena - m)) / m
        if me.y < m:
            by += (m - me.y) / m
        elif me.y > w.arena - m:
            by -= (me.y - (w.arena - m)) / m
        return bx, by

    def _update_motion(self, w: World, me: Entity, now: float):
        """Notice when we are not actually going anywhere.

        Being merely *near* a wall is handled by the urgency term.  This
        catches the other failure mode: pressed flat against a wall (or
        wedged into a corner) so that although the joystick is pushed, the
        cell makes no progress — which is exactly how the bot used to sit in
        a corner burning mass while reporting ``mode=FARM``.

        Crucially this needs the world to have *advanced*.  If no deltas
        arrived during the window, our position is simply a stale copy of
        where we were, so "we did not move" is an artefact of a stalled
        stream and says nothing about whether we are pinned.  Judging anyway
        used to fire ``stuck`` during a connection stall — seen live at
        ``pos=(808,5014) wall=0.0``, nowhere near a wall — and the spurious
        ``ESCAPE`` that followed steered the bot at nothing.
        """
        if self.win_pos is None:
            self.win_pos = (me.x, me.y)
            self.win_t = now
            self.win_updates = w.updates
            return
        if now - self.win_t < STUCK_WINDOW:
            return
        advanced = w.updates != self.win_updates
        moved = math.hypot(me.x - self.win_pos[0], me.y - self.win_pos[1])
        self.stuck = advanced and moved < STUCK_DISTANCE
        self.stalled = not advanced
        self.win_pos = (me.x, me.y)
        self.win_t = now
        self.win_updates = w.updates

    def _final_heading(self, w: World, me: Entity, desired, now: float):
        """Steer, fold in wall escape, and *store* the result on self.heading.

        Every branch of ``decide`` must return through here.  An earlier
        version computed the wall bias and merely *returned* it while
        ``_play`` drove the joystick from ``self.heading`` — so the whole
        avoidance term was computed and discarded, and the bot would wedge
        itself into a corner and starve.
        """
        ex, ey = self._wall_vec(w, me)
        urgency = max(abs(ex), abs(ey))
        self.wall_urgency = urgency

        if math.hypot(desired[0], desired[1]) > 1e-9:
            dx, dy = self._unit(desired[0], desired[1])
        else:
            dx, dy = self.safe_heading

        # Hard floor: never steer *into* a wall we are already up against,
        # whatever farming or hunting would prefer.
        if (ex > 0 and dx < 0) or (ex < 0 and dx > 0):
            dx = 0.0
        if (ey > 0 and dy < 0) or (ey < 0 and dy > 0):
            dy = 0.0

        if urgency >= PINNED_URGENCY or self.stuck:
            # Escape takes priority.  Keep the old intent only as a minor
            # component so we slide *along* the wall rather than dithering
            # on the spot.
            # Fleeing while pinned is the nasty case: a purely perpendicular
            # escape would run straight off the wall and into the predator.
            # Weight the escape lower there so we slide *along* the wall
            # instead of committing to a dive across open ground.
            alpha = 0.55 if self.mode.startswith('FLEE') else 0.85
            vx, vy = self._blend((dx, dy), (ex, ey), alpha)
            self.mode = 'ESCAPE ' + self.mode
        elif urgency > 0.02:
            # Drifting near a wall: ease away, proportional to how close.
            vx, vy = self._blend((dx, dy), (ex, ey), min(0.7, 1.1 * urgency))
        else:
            vx, vy = dx, dy

        vx, vy = self._unit(vx, vy)
        if vx or vy:
            self.safe_heading = (vx, vy)
        self.heading = self.safe_heading
        return self.heading

    @staticmethod
    def _unit(x, y):
        n = math.hypot(x, y)
        if n < 1e-9:
            return 0.0, 0.0
        return x / n, y / n

    @staticmethod
    def _blend(cur, new, alpha):
        nx, ny = new
        n = math.hypot(nx, ny)
        if n < 1e-9:
            return cur
        nx, ny = nx / n, ny / n
        cx, cy = cur
        c = math.hypot(cx, cy)
        if c < 1e-9:
            return nx, ny
        cx, cy = cx / c, cy / c
        return (cx * (1 - alpha) + nx * alpha, cy * (1 - alpha) + ny * alpha)


# --------------------------------------------------------------------------- #
# auth tokens
# --------------------------------------------------------------------------- #
# The real app keeps a *persistent* guest identity in
# ``guestToken.plist`` (``account_guestMCUserToken``, Erlang ETF).
# What we capture on the wire as mt=51 is a *session ticket* derived from
# that identity after the mt=119/120 handshake (AES-128).  Session tickets
# are short-lived and not safely replayable across handshakes -- which is
# why a captured 282-char blob works in the app forever (it remints) but
# goes stale for the bot within minutes.
#
# Separately, an older bug stripped the mid-token CRLF the app embeds in
# the base64, which made *every* login look refused.  ``_tok_norm`` now
# preserves that CRLF.
TOKEN_LEDGER = os.path.join(HERE, 'tokens-used.json')
CONTRAST_WINDOW = 900.0        # seconds: how close a success must be to attribute
GUEST_TOKEN_PLIST = os.path.join(HERE, 'device_prefs', 'guestToken.plist')

# Soft age hint for *capture files* only.  Session tickets go stale much
# sooner; the persistent guest identity in guestToken.plist does not.
TOKEN_TTL = 30 * 24 * 3600.0

# A token is an opaque base64 blob.  The live app embeds a single CRLF around
# offset ~200 (soft line-wrap baked into the string the server expects).
_TOKEN_RE = re.compile(
    r'^[A-Za-z0-9+/=_-]{40,400}(?:\r?\n[A-Za-z0-9+/=_-]{20,400})?$'
)


def _tok_id(tok: str) -> str:
    return hashlib.sha1(tok.encode()).hexdigest()[:12]


def _tok_norm(tok: str) -> str:
    """Normalize a token the way the app sends it.

    CRITICAL: the real app's login blob contains a literal ``\\r\\n`` in the
    middle of the base64 string.  Stripping all whitespace (the old behaviour)
    produces a 280-char impostor that the matchmaker rejects -- which looked
    exactly like a "stale token" / rate-limit.  Only trim file-edge newlines;
    if a single mid-token ``\\n`` remains (editor converted CRLF), restore
    ``\\r\\n``.
    """
    if not tok:
        return tok
    if tok.startswith('\ufeff'):
        tok = tok[1:]
    # Drop a single trailing newline written by capture-server / editors.
    while tok.endswith('\n') or tok.endswith('\r'):
        tok = tok[:-1]
    if '\r\n' in tok:
        return tok
    if '\n' in tok and tok.count('\n') == 1 and '\r' not in tok:
        a, b = tok.split('\n', 1)
        if a and b:
            return a + '\r\n' + b
    return tok

def _ledger_load() -> dict:
    try:
        d = json.load(open(TOKEN_LEDGER, encoding='utf8'))
        return d if isinstance(d, dict) else {}
    except Exception:
        return {}


def _ledger_save(d: dict) -> None:
    try:
        tmp = TOKEN_LEDGER + '.tmp'
        with open(tmp, 'w', encoding='utf8') as fh:
            json.dump(d, fh, indent=1, sort_keys=True)
        os.replace(tmp, TOKEN_LEDGER)
    except Exception:
        pass


def _tok_burned(rec: dict) -> bool:
    """True only for a refusal that a same-source success has corroborated."""
    return rec.get('state') == 'refused'


def _ledger_note_refusal(tid: str, region: str, source: str) -> None:
    """Record a refusal as pending -- deliberately not yet a verdict."""
    led = _ledger_load()
    rec = led.setdefault(tid, {})
    if _tok_burned(rec):
        return                       # already proven bad; keep the verdict
    rec.update(state='pending',
               refused_at=time.strftime('%Y-%m-%d %H:%M:%S'),
               refused_ts=time.time(),
               region=region, source=source)
    _ledger_save(led)


def _ledger_note_success(tid: str, region: str) -> list:
    """Record a working token and settle any recent pendings.

    A success proves the *source* is fine at this moment, so a token refused
    moments earlier really was the problem -- that is the contrast we need.
    Older pendings are marked inconclusive instead: too far away in time to
    attribute, so we leave the token usable rather than guess.
    """
    led = _ledger_load()
    now = time.time()
    promoted, inconclusive = [], []
    for other, rec in led.items():
        if other == tid or rec.get('state') != 'pending':
            # ``other == tid``: this very token was refused earlier and has now
            # logged in -- which proves it is fine, not broken.  Never promote
            # a token on the strength of its own later success.
            continue
        ts = rec.get('refused_ts')
        if ts is not None and now - ts <= CONTRAST_WINDOW:
            rec['state'] = 'refused'
            rec['confirmed_by'] = tid
            promoted.append(other)
        else:
            rec['state'] = 'inconclusive'
            inconclusive.append(other)
    rec = led.setdefault(tid, {})
    if rec.get('state') == 'pending':
        rec.pop('state', None)          # it just worked, so it is not refused
    rec['ok_at'] = time.strftime('%Y-%m-%d %H:%M:%S')
    rec['ok_ts'] = now
    rec['ok_region'] = region
    _ledger_save(led)
    return promoted


def _tokens_in_capture(path: str) -> list:
    """Every mt=51 login token inside one capture, in the order it was sent."""
    out = []
    try:
        d = json.load(open(path, encoding='utf8'))
    except Exception:
        return out
    for x in d.get('c2s', []):
        try:
            m = decode_frame(bytes.fromhex(x['hex']))
        except Exception:
            continue
        if m.op != 1:
            continue
        blob = one(m.top, 4)
        if not blob:
            continue
        try:
            it = fields(zlib.decompress(blob))
        except Exception:
            continue
        f85 = one(it, 85)
        if f85 is None:
            continue
        t = as_str(one(fields(f85), 1))
        if t:
            out.append(_tok_norm(t))
    return out


def token_candidates() -> list:
    """``(token, source, rank)`` for every token on disk, freshest first.

    ``rank`` is a sort key, not a timestamp.  A capture is a live app launch,
    so its mtime is a fair proxy for when its token was minted.  A loose
    ``.txt`` file is a manual override, so it *inherits* the rank of the token
    it holds rather than getting credit for when the file was written --
    otherwise a token copied out this morning would outrank the same token's
    capture from last night and the ordering would drift.
    """
    by_id = {}

    for name in os.listdir(HERE):
        if not (name.startswith('capture-main-') and name.endswith('.json')):
            continue
        p = os.path.join(HERE, name)
        try:
            rank = os.path.getmtime(p)
        except OSError:
            continue
        for t in _tokens_in_capture(p):
            tid = _tok_id(t)
            cur = by_id.get(tid)
            if cur is None or rank > cur[2]:
                by_id[tid] = (t, name, rank)

    # Specifically check token.txt: support the app's mid-token CRLF form.
    token_txt_path = os.path.join(HERE, 'token.txt')
    if os.path.exists(token_txt_path):
        try:
            mtime = os.path.getmtime(token_txt_path)
            # Binary-safe read so embedded \\r\\n survives.
            raw = open(token_txt_path, 'rb').read().decode('latin1')
            whole = _tok_norm(raw)
            if _TOKEN_RE.match(whole):
                tid = _tok_id(whole)
                by_id[tid] = (whole, 'token.txt', mtime + 1e9)  # always prefer live token.txt
            else:
                for idx, line in enumerate(raw.splitlines()):
                    t = _tok_norm(line)
                    if _TOKEN_RE.match(t):
                        tid = _tok_id(t)
                        if tid not in by_id:
                            by_id[tid] = (t, f'token.txt:L{idx+1}', mtime + (idx * 0.001))
        except Exception:
            pass

    # Loose files: a token the user dropped here by hand.
    for name in os.listdir(HERE):
        if not name.endswith('.txt') or name == 'token.txt':
            continue
        p = os.path.join(HERE, name)
        try:
            raw = open(p, encoding='utf8', errors='ignore').read()
        except Exception:
            continue
        t = _tok_norm(raw)
        if not _TOKEN_RE.match(t):
            continue
        tid = _tok_id(t)
        if tid in by_id:
            continue                       # already ranked, from its capture
        try:
            rank = os.path.getmtime(p)
        except OSError:
            rank = 0.0
        by_id[tid] = (t, name, rank)

    return sorted(by_id.values(), key=lambda r: -r[2])


def token_report() -> str:
    """Human-readable view of what tokens exist and which are burned."""
    cands = token_candidates()
    if not cands:
        return ('no auth tokens found.  Capture one by launching the real app '
                'with capture-server.js, or pass --token.')
    led = _ledger_load()
    lines = [f'{len(cands)} token(s) on disk, freshest first:', '']
    for i, (t, src, rank) in enumerate(cands):
        tid = _tok_id(t)
        rec = led.get(tid, {})
        state = rec.get('state', '')
        if _tok_burned(rec):
            note = f'REFUSED {rec.get("refused_at", "?")}'
        elif state == 'pending':
            note = f'refused once {rec.get("refused_at", "?")}, unconfirmed'
        elif state == 'inconclusive':
            note = 'refused once, not attributable to the token'
        elif rec.get('ok_at'):
            note = f'ok {rec["ok_at"]}'
        else:
            note = 'unused'
        when = time.strftime('%m-%d %H:%M', time.localtime(rank)) if rank else '?'
        age = (time.time() - rank) if rank else None
        aged = ''
        if age is not None:
            aged = f'{age / 3600:4.1f}h'
            if age > TOKEN_TTL:
                aged += ' STALE'
        lines.append(f'  {i}. {tid}  {len(t):3d} chars  {when}  {aged:>11s}  '
                     f'{src:<24s} {note}')
    burned = [c for c in cands if _tok_burned(led.get(_tok_id(c[0]), {}))]
    n_stale = sum(1 for _t, _s, r in cands if r and time.time() - r > TOKEN_TTL)
    lines += ['', f'{len(cands) - len(burned)} in the rotation.  The bot picks '
                  f'#1 and only skips a token once a success has proven it bad.']
    if n_stale == len(cands):
        lines.append(f'Every token is older than the ~{TOKEN_TTL / 3600:.1f}h '
                     f'working life measured here, so a refused login is the '
                     f'expected outcome.')
        lines.append('Fix: launch the real app through capture-server.js to '
                     'mint a fresh one, then re-run.')
    elif n_stale:
        lines.append(f'{n_stale} token(s) look stale (> '
                     f'{TOKEN_TTL / 3600:.1f}h); the freshest is #1.')
    lines.append('A refusal on every token in a row means the source is '
                 'blocked or every token is stale -- not that one token is bad.')
    return '\n'.join(lines)


# --------------------------------------------------------------------------- #
# the bot
# --------------------------------------------------------------------------- #

class AgarBot:
    _direct_dead_until = 0.0
    # _arena() sets this when the node answers with a redirect back to a host
    # we already dialled on the same bearer token (see _arena).
    _arena_token_bounced = False
    # Landed on a different Burst arena_id than the fleet pin — skip soft
    # remash; fresh login hunts the pinned room.
    _fleet_wrong_room = False
    # How long the last known target position stays worth walking to while
    # the target is off-screen.  The arena only streams a local window, so a
    # freshly spawned follower is almost never looking at its target; without
    # this the bot just mills around its spawn point forever.
    #
    # 600s was far too long: the human moves, so a ten-minute-old fix is not a
    # destination, it is a place they left.  45s is about how long it takes a
    # bot to cross the useful part of the arena, and the shared fleet sighting
    # (newest wins, see _seek_point) takes over after that.
    SEEK_MEMORY = 300.0

    def __init__(self, region='ap-south-1', code=None, nick=None, run_s=60,
                 token=None, strategy='balanced', tick=TICK, node_port=None,
                 verbose=True, logger=None, on_stats=None, on_event=None,
                 respawn=True, calibrate=True, no_party=False,
                 mm_tries=3, mm_wait=10.0, prefer='auto',
                 proxy=None, proxy_protocol='auto', token_retry=0,
                 leave_party=False, party_status_only=False,
                 join_then_leave=False, party_hold=False,
                 mode='play', follow=None, feed_keep=32.0,
                 leave_at=150.0, cycle_s=90.0, split_feed=True,
                 guest_v6=False, auto_target=False, boost_force=True,
                 safe_mass=90.0, threat_radius=900.0, require_proxy=False,
                 close_range=1500.0, boost_items=None, sticky_proxy=False,
                 game_type: int = 13, arena_mode: str = 'classic',
                 follow_name: str | None = None, create_party: bool = False,
                 enemy_clearance: str | float = '1'):
        self.create_party = bool(create_party)
        self.enemy_clearance = str(enemy_clearance or '1').strip()
        # mode: 'play'   -> normal brain
        #       'follow' -> follow `follow` (player uuid / uuid prefix / name)
        #                   and give them mass: split toward them + 2 feeds
        #       'leave'  -> classic play, eject everything, mt=80 leave, repeat
        self.mode = mode
        self.follow = (follow or '').strip() or None
        # In-game nick of the operator (e.g. CaffeinatedAwe16) — UID match
        # primary, name is backup when f6 is missing on a cell.
        self.follow_name = (follow_name or '').strip() or None
        # World-space joystick in follow (no 90deg calib miss).
        self._follow_raw_joy = True
        # Arena playlist: classic (13) or burst (captured game_type id)
        try:
            self.game_type = int(game_type) if game_type else 13
        except Exception:
            self.game_type = 13
        if self.game_type <= 0:
            self.game_type = 13
        self.arena_mode = (arena_mode or 'classic').strip().lower() or 'classic'
        # Auto-targeting: let a follower pick its own target out of the party
        # roster instead of using config's `uid`.  OFF by default -- see
        # _party_human_key() for why guessing here is dangerous.
        self.auto_target = bool(auto_target)
        self.feed_keep = float(feed_keep)      # never eject below this mass
        # follow-mode: do not start the trip to the target until we are this
        # heavy.  Measured on ZTZ2MC: 17 of 44 deaths happened while GROWing at
        # ~15 mass, because the sector sweep was dragging a spawn-mass bot
        # thousands of units through live traffic.  Farm locally first.
        self.safe_mass = float(safe_mass)
        # follow-mode: an eater within this distance makes dodging the whole
        # decision for the tick (reference follow bot uses 900).
        self.threat_radius = float(threat_radius)
        # follow-mode: if the target is VISIBLE inside this range, walk to them
        # at any mass instead of waiting for safe_mass.  The safe_mass gate is
        # there to stop a spawn-mass bot crossing an 11180-unit map; it was
        # never meant to stop a bot that can already SEE the operator from
        # closing the last 600 units.  Measured live: the fleet sat at 14-26
        # mass against a 36 gate, so every bot spent whole rounds grazing in a
        # ring around the operator -- "bot mere aas paas ghum raha hai".
        # 0 disables the override and restores the old behaviour exactly.
        self.close_range = float(close_range)
        # require-proxy: never dial this PC's own IP.  If no SOCKS is pinned or
        # left to rotate to, the bot refuses instead of quietly going direct.
        self.require_proxy = bool(require_proxy)
        # Stick to the assigned --proxy: no rotate through proxies_live on
        # refuse. Required for bots-per-proxy fleets (5 bots / SOCKS) so they
        # do not all stampede onto the same "next" IP after one reject.
        self.sticky_proxy = bool(sticky_proxy)
        self.leave_at = float(leave_at)        # leave-mode: dump mass at this
        self.cycle_s = float(cycle_s)          # leave-mode: max secs per cycle
        self.split_feed = bool(split_feed)
        self.guest_v6 = bool(guest_v6)
        # Arm mass_boost_3x_1h (mt=94) before play even when the wallet reports
        # zero.  The app does exactly this and spawns ~132 instead of ~13, which
        # is the difference between a bot that survives long enough to feed and
        # one that is eaten at 13 mass within a few seconds -- the "bots slowly
        # drop to 0" loop.  A refusal (mt=97) kills the session, so _activate_
        # mass_boost() sets _skip_mass_boost and the next dial plays without it.
        self.boost_force = bool(boost_force)
        self.region = normalize_region(region)
        self.host = host_for(self.region)
        self.code = code.upper() if code else None
        self.nick = nick
        self.run_s = run_s

        def play_pkt(nick=None):
            n = (nick if nick is not None else (self.nick or '')).strip() or 'b'
            return pkt_play(n, self.game_type)

        self.play_pkt = play_pkt
        self._want_play = False
        self._inline_need_reenter = False
        self._death_play_n = 0
        self._death_ask_at = 0.0
        self._skip_mass_boost = False
        self._mass_boost_on = False
        # Which boosts to arm before play, in order.  `xp` and `mass` are
        # separate types in the game's catalogue (Gameplay - Boosts), so the
        # mass boost alone does nothing for level/XP -- both are sent.
        self.boost_items = list(boost_items or ('mass_boost_3x_24h',
                                                'xp_boost_3x_24h'))
        self._boosts_on: set[str] = set()
        self._inventory: dict[str, int] = {}
        self.token = token
        self.leave_party = leave_party
        self.party_status_only = party_status_only
        self.join_then_leave = join_then_leave
        self.party_hold = party_hold
        self.leave_party_only = False
        self.current_party_code = None
        self.current_party_host = None
        self.current_party_members: list[str] = []
        # True when the login was answered with mt=33 instead of the profile.
        # We then do NOT know which party the server still holds this account
        # in, so the party join must leave first -- otherwise the fleet splits
        # across the old and the new code.
        self._party_state_unknown = False
        # Tokens tried during this session (so a rotation never re-presents the
        # same one) and whether the matchmaker refused one -- which is the only
        # condition under which spending another dial is worth it.
        self._tried_tokens = set()
        self._token_refused = False
        self.token_retry = token_retry
        self.used_token = None
        self.persist_token = None
        self.strategy = strategy
        self.tick = tick
        self.node_port = node_port
        self.verbose = verbose
        self.logger = logger                 # optional callback(line) (ws_control)
        self.on_stats = on_stats
        self.on_event = on_event
        self.respawn = respawn
        self.calibrate = calibrate
        self.no_party = no_party
        # Re-arm the boosts before every mt=110 instead of only the first dial.
        # Set from --boost-every-play.
        self.boost_every_play = False
        # The matchmaker blocks a source that reconnects too often, so keep the
        # per-session retry budget small when you are probing.
        self.mm_tries = mm_tries
        self.mm_wait = mm_wait
        # 'auto' | 'ipv6' | 'ipv4' -- see _sockaddrs.  The two families are
        # throttled independently, so being able to pin one is a real escape
        # hatch when the other has been rate-limited.
        self.prefer = prefer
        # Optional '[user:pass@]host:port' tunnel.  Everything -- matchmaker
        # *and* arena node -- goes through it, so the server sees one
        # consistent source IP for the whole session.
        self.proxy = parse_proxy(proxy) if isinstance(proxy, str) else proxy
        self.proxy_protocol = proxy_protocol
        self.party_code = None
        self.party_members: list[str] = []
        self.party_uuids: dict[str, str] = {}   # member display name -> uuid
        self.party_raw: dict[str, str] = {}     # member whose entry we could not
                                                # parse -> raw hex (diagnostic)
        self.feeds = 0
        self.splits = 0
        self.leaves = 0

        self.mm = None
        self.arena = None
        self.q_mm: queue.Queue = queue.Queue()
        self.q_ar: queue.Queue = queue.Queue()
        self.mm_closed = threading.Event()
        self.ar_closed = threading.Event()
        self._stop = threading.Event()
        # Bumped by the play loops every tick.  The stall watchdog (see
        # _start_stall_watchdog) watches this and nothing else, so it can never
        # fight the pacer, the watchdogs or the reconnect logic -- it only
        # fires when the loop has made no progress at all.
        self._heartbeat = 0
        self.world = World()
        self.brain = Brain(strategy)
        self.hmap = HeadingMap()
        self.node_token = None
        self.arena_host = None
        self.arena_port = NODE_PORT
        self.joystick = (0.0, 0.0)
        self.log_lines: list[str] = []

    # ------------------------------------------------------------ logging
    def log(self, *a):
        line = ' '.join(str(x) for x in a)
        self.log_lines.append(line)
        if len(self.log_lines) > 400:
            self.log_lines = self.log_lines[-400:]
        cb = self.logger
        if cb:
            try:
                cb(line)
            except Exception:
                pass
        # Per-bot file (mainBot sets BOT_LOG_FILE) — fleet check without scraping
        # console windows. Console print still happens when verbose.
        _lf = getattr(self, '_bot_log_file', None)
        if _lf is None:
            _lf = (os.environ.get('BOT_LOG_FILE') or '').strip() or False
            self._bot_log_file = _lf
        if _lf:
            try:
                with open(_lf, 'a', encoding='utf-8', errors='replace') as fh:
                    fh.write(line + '\n')
            except Exception:
                pass
        if self.verbose:
            try:
                print(line, flush=True)
            except UnicodeEncodeError:
                print(line.encode('ascii', 'replace').decode('ascii'), flush=True)

    def event(self, name, **kw):
        if self.on_event:
            try:
                self.on_event(name, kw)
            except Exception:
                pass

    # ------------------------------------------------------------ tokens
    def captured_token(self) -> str | None:
        """Freshest token that has neither been refused nor tried this session.

        Falls back to the freshest candidate at all if every one is burned --
        the ledger is a heuristic, not gospel, and a throttle does decay -- but
        says so, because that login is the one most likely to be refused.
        """
        cands = token_candidates()
        if not cands:
            return None
        led = _ledger_load()

        def _burned(t):
            return _tok_burned(led.get(_tok_id(t), {}))

        usable = [c for c in cands
                  if not _burned(c[0]) and _tok_id(c[0]) not in self._tried_tokens]
        if usable:
            tok, src, rank = usable[0]
            note = []
            n_burned = sum(1 for c in cands if _burned(c[0]))
            if n_burned:
                note.append(f'{n_burned} proven bad')
            if self._tried_tokens:
                note.append(f'{len(self._tried_tokens)} tried this session')
            tail = f' ({", ".join(note)})' if note else ''
            self.log(f'[token] {len(tok)} chars from {src}, '
                     f'{len(usable)} of {len(cands)} in the rotation{tail}')
            # Warn, do not refuse: the TTL is inferred from measurements, and a
            # stale-looking token sometimes still works.
            age = time.time() - rank if rank else 0.0
            if age > TOKEN_TTL:
                self.log(f'[token] note: capture source is {age / 3600:.1f}h old '
                         f'(guest tokens persist until app data is cleared; '
                         f'age alone does not invalidate them)')
            if '\r\n' not in tok and len(tok) in (280, 64):
                self.log('[token] WARNING token has no mid-CRLF — the live app '
                         'sends 282-char blobs with an embedded line break. '
                         'Re-capture if login is refused.')
            return tok

        tok, src, _rank = cands[0]
        self.log(f'[token] WARNING: every candidate has been proven bad by a '
                 f'contrasting success; reusing the freshest ({src}).  Launch '
                 f'the real app to mint a new token, or pass --token.')
        return tok

    def _mark_token_spent(self, tok, reason='login refused'):
        """Record a refusal -- as *pending*, never as a verdict on its own.

        An explicit ``--token`` is never recorded: that is the user's decision,
        and they may be retrying deliberately after a throttle decayed.
        """
        if not tok or self.token:
            return
        tid = _tok_id(tok)
        src = next((s for t, s, _r in token_candidates()
                    if _tok_id(t) == tid), '?')
        _ledger_note_refusal(tid, self.region, src)
        self.log(f'[token] noted {tid} as refused ({reason}); it stays in the '
                 f'rotation until a success proves it, not the source, was bad')

    def _mark_token_ok(self, tok):
        """Record a working token, and settle any recent unconfirmed refusals."""
        if not tok or self.token:
            return
        promoted = _ledger_note_success(_tok_id(tok), self.region)
        if promoted:
            self.log(f'[token] {len(promoted)} earlier refusal(s) now confirmed '
                     f'against this success: {", ".join(promoted)} -- those '
                     f'will be skipped from now on')

    # ------------------------------------------------------------ network
    def _reader(self, sock, q: queue.Queue, name: str, closed=None,
                silent_after=None, poll=0.5):
        buf = b''
        total = 0
        reason = 'eof'
        last_rx = time.time()
        # Clock for "is the MATCH still advancing?", which is a different
        # question from "did any byte arrive?".  See ARENA_KEEPALIVE_MT.
        last_data = last_rx
        try:
            while not self._stop.is_set():
                try:
                    # The socket timeout is SHARED between recv and sendall, so
                    # this is the same value _arena() put on the socket -- it is
                    # not lowered here, because a short recv poll would also
                    # shorten every outbound send and turn a briefly busy tunnel
                    # into a false "node is dead".
                    sock.settimeout(poll)
                    chunk = sock.recv(65536)
                except socket.timeout:
                    # A live arena streams snapshots several times a second, so
                    # sustained silence is not an idle moment -- it is a
                    # half-open socket.  The server (or the SOCKS hop) stopped
                    # sending but never sent FIN, so recv() blocks on the
                    # timeout forever and nothing else in the bot can tell.
                    #
                    # MEASURED (bot-logs/fleet_follow.log): this is what froze
                    # four of eight bots at exactly spawn mass 14.0 on one
                    # coordinate for 100+ ticks.  Their world stopped advancing
                    # (the [world] census printed byte-identical masses on
                    # consecutive lines), world.dead stayed False, world.me
                    # stayed pinned to the last spawn snapshot, and the follow
                    # loop went on commanding a joystick into a black hole.
                    #
                    # CRITICAL: this must be measured against `last_data`, not
                    # `last_rx`.  The node pings us (mt=70) on its own clock
                    # while the world is frozen, and each ping used to refresh
                    # `last_rx`, so the deadline could NEVER fire on the exact
                    # failure it exists to catch.
                    # MEASURED (2026-09-30 live run): four of ten bots sat at
                    # `upd: 0 mv: 0` at spawn mass while `-> pong mt=104` lines
                    # kept arriving, and the loop only recovered them via the
                    # 3-hit [stale] watchdog ~54 s later.
                    if (silent_after
                            and time.time() - last_data > silent_after):
                        reason = (f'no world frames for '
                                  f'{time.time() - last_data:.1f}s')
                        self.log(f'[{name}] {reason} (pings only) -- treating '
                                 f'as closed (dead stream on a live socket)')
                        break
                    continue
                except OSError as e:
                    reason = f'{type(e).__name__}: {e}'
                    break
                if not chunk:
                    reason = 'eof'
                    break
                now_rx = time.time()
                last_rx = now_rx
                total += len(chunk)
                buf += chunk
                if os.environ.get('FRAME_HEX') and name == 'arena':
                    self.log(f'[{name}] RAW {len(chunk)}b {chunk[:80].hex()}')
                while len(buf) >= 4:
                    n = struct.unpack('>I', buf[:4])[0]
                    if n == 0 or n > 8 << 20:
                        reason = f'bad frame len {n} after {total}b'
                        self.log(f'[{name}] {reason}')
                        buf = b''
                        break
                    if len(buf) < 4 + n:
                        break
                    body = buf[4:4 + n]
                    buf = buf[4 + n:]
                    if silent_after is not None:
                        # Only frames that say something about the match reset
                        # the clock.  A pure keepalive proves the TCP path is
                        # up, not that the match is running.
                        try:
                            mt = decode_frame(body).mt
                        except Exception:
                            mt = None
                        if mt not in ARENA_KEEPALIVE_MT or self.world.dead or self.world.me is None:
                            last_data = now_rx
                    q.put(body)
                # The deadline has to be evaluated on the DATA path as well as
                # the timeout path.  A ping-only stream keeps recv() succeeding,
                # so `except socket.timeout` never runs and a check that lived
                # only there could never fire -- which is precisely how four of
                # ten bots stayed frozen while `-> pong mt=104` lines scrolled
                # past.  MEASURED: tools/_watchdog_probe.py PROBE 5 caught this
                # on the first run of the fix.
                if (silent_after
                        and time.time() - last_data > silent_after):
                    reason = (f'no world frames for '
                              f'{time.time() - last_data:.1f}s')
                    self.log(f'[{name}] {reason} (pings only) -- treating '
                             f'as closed (dead stream on a live socket)')
                    break
        finally:
            # Log BOTH sockets.  The matchmaker reader used to exit silently,
            # so when the re-enter path reported "matchmaker socket closed"
            # there was nothing anywhere in the log saying when or why it
            # closed -- which made "why can't we re-use this session?" a
            # question with no evidence attached to it.
            self.log(f'[{name}] reader exit {reason} total={total}b '
                     f'left={len(buf)}')
            if closed is not None:
                closed.set()
            q.put(None)

    def _start_reader(self, sock, q, name, closed=None, silent_after=None,
                      poll=0.5):
        t = threading.Thread(target=self._reader,
                             args=(sock, q, name, closed, silent_after, poll),
                             daemon=True)
        t.start()
        return t

    def _drain(self, q: queue.Queue, handler=None, deadline=None) -> int:
        """Process everything queued; returns frames handled."""
        n = 0
        while True:
            try:
                body = q.get_nowait()
            except queue.Empty:
                break
            if body is None:
                break
            m = decode_frame(body)
            kind = self.world.apply(m)
            n += 1
            if handler is not None:
                handler(m, kind)
            if deadline is not None and time.time() > deadline:
                break
        return n

    def _wait_for(self, q: queue.Queue, pred, timeout, label='', on_frame=None,
                  log_frames=True, closed=None, quiet=False):
        """Pump frames until pred(msg, world) is true or the timeout expires."""
        end = time.time() + timeout
        while time.time() < end:
            self._heartbeat += 1
            try:
                body = q.get(timeout=0.2)
            except queue.Empty:
                if closed is not None and closed.is_set():
                    self.log(f'  [!] connection closed while waiting for '
                             f'{label or "condition"}')
                    return None
                continue
            if body is None:
                self.log(f'  [!] connection closed while waiting for '
                         f'{label or "condition"}')
                return None
            m = decode_frame(body)
            self.world.apply(m)
            if log_frames:
                extra = ''
                if m.size <= 24 or os.environ.get('FRAME_HEX'):
                    extra = f' hex={body.hex()}'
                self.log(f'  <- mt={m.mt} ({m.size}b){extra}')
            if on_frame:
                on_frame(m)
            if pred(m, self.world):
                return m
        if not quiet:
            self.log(f'  [!] timeout waiting for {label or "condition"}')
        return None

    def resolve_all(self) -> list:
        ips = set()
        if self.host == DEFAULT_HOST:
            ips |= set(KNOWN_IPS)
        ips |= set(KNOWN_IPS_BY_REGION.get((self.region or '').strip().lower(), []))
        for ns in ('8.8.8.8', '1.1.1.1', '9.9.9.9'):
            try:
                ips |= set(dns_query_a(self.host, ns))
            except Exception:
                pass
        return sorted(ips)

    @staticmethod
    def _v4_to_nat64(ip: str) -> str:
        """Well-known NAT64 prefix — same path the app/emulator uses here."""
        a, b, c, d = (int(x) for x in ip.split('.'))
        return f'64:ff9b::{a << 8 | b:x}:{c << 8 | d:x}'

    @staticmethod
    def _sockaddrs(host: str, port: int, prefer: str = 'auto',
                   extra_ips=()) -> list:
        """IPv6 + synthesized NAT64 first; plain IPv4 last (often blackholed)."""
        v6, v4 = [], []
        try:
            for fam, _t, _p, _c, sa in socket.getaddrinfo(
                    host, port, socket.AF_UNSPEC, socket.SOCK_STREAM):
                if fam == socket.AF_INET6:
                    if (fam, sa) not in v6:
                        v6.append((fam, sa))
                elif fam == socket.AF_INET:
                    if (fam, sa) not in v4:
                        v4.append((fam, sa))
        except Exception:
            pass
        for ip in extra_ips or ():
            if ':' in ip:
                sa = (ip, port, 0, 0)
                if (socket.AF_INET6, sa) not in v6:
                    v6.append((socket.AF_INET6, sa))
            else:
                sa = (ip, port)
                if (socket.AF_INET, sa) not in v4:
                    v4.append((socket.AF_INET, sa))
                try:
                    n64 = AgarBot._v4_to_nat64(ip)
                    sa6 = (n64, port, 0, 0)
                    if (socket.AF_INET6, sa6) not in v6:
                        v6.append((socket.AF_INET6, sa6))
                except Exception:
                    pass
        if prefer == 'ipv6':
            return v6
        if prefer == 'ipv4':
            return v4
        return v6 + v4

    def connect_to(self, host: str, port: int, timeout=4.0,
                   extra_ips=(), tries=1, prefer: str = 'auto'):
        """Happy-eyeballs: race IPv6/NAT64 + IPv4. First SYN that completes wins.

        Sequential 15s IPv4 timeouts are why EU looked dead while the app
        (same host, IPv6/NAT64) was already logged in.
        """
        cands = self._sockaddrs(host, port, prefer, extra_ips)
        if not cands:
            raise OSError(f'cannot resolve {host}')
        last = [OSError(f'cannot reach {host}:{port}')]
        won = queue.Queue()

        def _one(fam, sa):
            s = None
            per = 2.0 if fam == socket.AF_INET else min(timeout, 4.0)
            try:
                s = socket.socket(fam, socket.SOCK_STREAM)
                s.settimeout(per)
                s.connect(sa)
                s.settimeout(None)
                s.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
                won.put(s)
            except OSError as e:
                last[0] = e
                if s is not None:
                    try:
                        s.close()
                    except Exception:
                        pass

        threads = []
        for fam, sa in cands[:8]:
            t = threading.Thread(target=_one, args=(fam, sa), daemon=True)
            t.start()
            threads.append(t)
        try:
            sock = won.get(timeout=min(max(timeout, 4.5), 5.0))
        except queue.Empty:
            raise last[0]

        def _reap():
            while True:
                try:
                    extra = won.get(timeout=1.5)
                except queue.Empty:
                    return
                try:
                    extra.close()
                except Exception:
                    pass

        threading.Thread(target=_reap, daemon=True).start()
        return sock

    # capture-server.js regional listeners — same path the emulator app uses.
    _CAPTURE_PORTS = {
        'us-east-1': 9011, 'us-east-2': 9012, 'us-west-1': 9013,
        'us-west-2': 9014, 'ap-northeast-1': 9015, 'ap-south-1': 9016,
        'ap-southeast-1': 9017, 'ap-southeast-2': 9018,
        'eu-central-1': 9019, 'eu-west-1': 9020, 'eu-west-2': 9021,
        'eu-west-3': 9022, 'sa-east-1': 9023,
    }

    def _disable_capture_steal(self):
        """STEAL_LOGIN drops our mt=51.  Always turn it off before we dial."""
        try:
            req = urllib.request.Request(
                'http://127.0.0.1:9080/steal',
                data=b'{"on":0}',
                method='POST',
                headers={'Content-Type': 'application/json'})
            urllib.request.urlopen(req, timeout=0.4).read()
        except Exception:
            pass

    def _try_local_capture(self):
        """If capture-server is up, dial 127.0.0.1 — it already reaches AWS."""
        if os.environ.get('SKIP_CAPTURE') == '1':
            return None
        port = self._CAPTURE_PORTS.get((self.region or '').strip().lower())
        if not port:
            return None
        self._disable_capture_steal()
        s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        s.settimeout(0.4)
        try:
            s.connect(('127.0.0.1', port))
            s.settimeout(None)
            s.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
            return s
        except OSError:
            try:
                s.close()
            except Exception:
                pass
            return None

    def connect_mm(self, tries=6, base_wait=5.0):
        """Dial the matchmaker with exponential backoff.

        The real service drops SYNs from a source that reconnects too often, so
        hammering it makes things strictly worse.
        """
        last = None
        # A previous session's socket may still be lying around (a token
        # rotation redials in the same process).  Close it, or every retry
        # leaks a descriptor and a reader thread.
        if self.mm is not None:
            try:
                self.mm.close()
            except OSError:
                pass
            self.mm = None
        self._via_capture = False
        for i in range(tries):
            try:
                if self.proxy:
                    ph, pp = self.proxy[0], self.proxy[1]
                    dest = self.host
                    # SOCKS ATYP=3 DNS of MM hostname often hangs; ATYP=1
                    # to a known regional IPv4 completes.
                    reg = (self.region or '').strip().lower()
                    ips = list(KNOWN_IPS_BY_REGION.get(reg) or [])
                    if not ips:
                        ips = list(self.resolve_all() or [])
                    if ips:
                        dest = ips[i % len(ips)]
                    self.log(f'[mm] dialing {dest}:{MM_PORT} via proxy '
                             f'{ph}:{pp} ({self.proxy_protocol})')
                    self.mm = proxy_dial(self.proxy, dest, MM_PORT, 12,
                                         self.proxy_protocol)
                    self.log(f'[mm] tunnel up via {ph}:{pp} '
                             f'-> {dest}:{MM_PORT}')
                else:
                    # App path first: capture-server (emulator iptables → same
                    # SOCKS egress). Direct/NAT64 only if capture is down.
                    local = self._try_local_capture()
                    if local is not None:
                        self.mm = local
                        self._via_capture = True
                        self.log(f'[mm] via capture-server 127.0.0.1:'
                                 f'{self._CAPTURE_PORTS.get(self.region)} '
                                 f'(app path)')
                        return
                    extra = list(KNOWN_IPS_BY_REGION.get(self.region) or [])
                    if not extra:
                        extra = list(self.resolve_all() or [])
                    self.log(f'[mm] dialing {self.host}:{MM_PORT} '
                             f'(prefer={self.prefer}, ipv4 {extra})')
                    last = None
                    if extra:
                        for ip in extra[:4]:
                            s = None
                            try:
                                n64 = self._v4_to_nat64(ip)
                                s = socket.socket(socket.AF_INET6,
                                                  socket.SOCK_STREAM)
                                s.settimeout(5.0)
                                s.connect((n64, MM_PORT, 0, 0))
                                s.settimeout(None)
                                s.setsockopt(socket.IPPROTO_TCP,
                                             socket.TCP_NODELAY, 1)
                                self.mm = s
                                self.log(f'[mm] connected NAT64 {n64}')
                                return
                            except OSError as e:
                                last = e
                                if s is not None:
                                    try:
                                        s.close()
                                    except Exception:
                                        pass
                    try:
                        self.mm = self.connect_to(
                            self.host, MM_PORT, timeout=4,
                            extra_ips=extra, prefer=self.prefer)
                        self.log(f'[mm] connected {self.mm.getpeername()}')
                        return
                    except Exception as e:
                        last = e
                    raise last or OSError('matchmaker unreachable')
                return
            except Exception as e:
                last = e
                if i + 1 >= tries:
                    break
                wait = min(base_wait * (2 ** i), 15.0)
                self.log(f'[mm] retry {i + 1}/{tries} ({type(e).__name__}) '
                         f'— waiting {wait:.0f}s')
                time.sleep(wait)
        raise last if last else RuntimeError('matchmaker unreachable')

    def send(self, sock, body, label='', *, silent=False):
        if sock is None:
            return
        sock.sendall(frame(body))
        if silent:
            return
        m = decode_frame(body)
        self.log(f'  -> {label or ("mt=" + str(m.mt))} ({len(body)}b)')

    # ------------------------------------------------------------ pacing
    # The matchmaker throttles login bursts per source IP *and* per account.
    # Shared SOCKS (bots-per-proxy > 1) used to skip pacing entirely
    # (`if self.proxy: return`), so 5 bots on one IP all fired mt=51 at once
    # and only ~10/50 reached LIVE. Pace is keyed by egress IP.
    PACE_FILE = os.path.join(
        os.path.dirname(os.path.abspath(__file__)),
        os.environ.get('BOT_PACE_FILE', 'login_pace.json'))
    PACE_MIN_GAP = 45.0
    # Per-IP gap.  Was 30s — fine for 5 bots/SOCKS share, but with 1 bot per
    # proxy a failed pin/redirect made each bot wait ~20–30s alone, so the
    # fleet dribbled in as 1,3,4,2,5… instead of all 10 together.
    PACE_PROXY_GAP = 4.0  # was 8 — pin-hunt reconnects need faster retries
    PACE_BACKOFF = (20.0, 40.0, 60.0, 90.0)
    HOT_FILE = os.path.join(
        os.path.dirname(os.path.abspath(__file__)), 'proxies_hot.json')
    HOT_SECS = 480.0

    def _pace_key(self) -> str:
        if self.proxy:
            return f'{self.proxy[0]}:{self.proxy[1]}'
        return 'direct'

    def _pace_lock_dir(self, key: str) -> str:
        safe = ''.join(c if c.isalnum() or c in '-_.' else '_' for c in key)
        return os.path.join(
            os.path.dirname(self.PACE_FILE), f'.pace_lock_{safe}')

    def _pace_acquire(self, key: str, timeout: float = 90.0) -> bool:
        path = self._pace_lock_dir(key)
        end = time.time() + timeout
        while time.time() < end and not self._stop.is_set():
            try:
                os.mkdir(path)
                try:
                    with open(os.path.join(path, 'pid'), 'w', encoding='utf8') as f:
                        f.write(str(os.getpid()))
                except Exception:
                    pass
                return True
            except FileExistsError:
                try:
                    age = time.time() - os.path.getmtime(path)
                    if age > 180:
                        import shutil
                        shutil.rmtree(path, ignore_errors=True)
                        continue
                except Exception:
                    pass
                time.sleep(0.25)
            except Exception:
                time.sleep(0.5)
        return False

    def _pace_release(self, key: str) -> None:
        path = self._pace_lock_dir(key)
        try:
            import shutil
            shutil.rmtree(path, ignore_errors=True)
        except Exception:
            pass

    def _pace_load(self) -> dict:
        try:
            return json.load(open(self.PACE_FILE, encoding='utf8'))
        except Exception:
            return {}

    def _pace_save(self, d: dict) -> None:
        try:
            tmp = f'{self.PACE_FILE}.{os.getpid()}.tmp'
            with open(tmp, 'w', encoding='utf8') as f:
                json.dump(d, f)
            os.replace(tmp, self.PACE_FILE)
        except Exception:
            try:
                json.dump(d, open(self.PACE_FILE, 'w', encoding='utf8'))
            except Exception:
                pass

    def _pace_slot(self, d: dict, key: str) -> dict:
        by = d.setdefault('by', {})
        if key not in by:
            if key == 'direct' and ('last_login' in d or 'refusals' in d):
                by[key] = {
                    'last_login': float(d.get('last_login', 0) or 0),
                    'refusals': int(d.get('refusals', 0) or 0),
                }
            else:
                by[key] = {'last_login': 0.0, 'refusals': 0}
        return by[key]

    def _pace_wait(self) -> None:
        if self.proxy:
            return
        try:
            d = self._pace_load()
            slot = self._pace_slot(d, key)
            last = float(slot.get('last_login', 0.0) or 0.0)
            streak = int(slot.get('refusals', 0) or 0)
            gap = self.PACE_PROXY_GAP if self.proxy else self.PACE_MIN_GAP
            if streak > 0:
                gap = max(
                    gap,
                    self.PACE_BACKOFF[min(streak, len(self.PACE_BACKOFF)) - 1])
            wait = last + gap - time.time()
            if wait < 0:
                wait = 0.0
            # Reserve this slot NOW and drop the lock so sibling bots on the
            # same SOCKS can queue their own reservations (instead of blocking
            # behind our sleep).
            slot['last_login'] = time.time() + wait
            self._pace_save(d)
        finally:
            if got:
                self._pace_release(key)
        if wait > 0 and not self._stop.is_set():
            why = f'spacing logins on {key}'
            self.log(f'[pace] waiting {wait:.0f}s before login ({why})')
            end = time.time() + wait
            while time.time() < end and not self._stop.is_set():
                time.sleep(min(1.0, end - time.time()))

    def _mark_proxy_hot(self) -> None:
        if not self.proxy:
            return
        key = f'{self.proxy[0]}:{self.proxy[1]}'
        try:
            d = json.load(open(self.HOT_FILE, encoding='utf8'))
        except Exception:
            d = {}
        d[key] = time.time()
        try:
            tmp = f'{self.HOT_FILE}.{os.getpid()}.tmp'
            with open(tmp, 'w', encoding='utf8') as f:
                json.dump(d, f, indent=0)
            os.replace(tmp, self.HOT_FILE)
        except Exception:
            pass

    def _is_spec_hot(self, spec: str) -> bool:
        key = spec.split('@')[-1]
        try:
            d = json.load(open(self.HOT_FILE, encoding='utf8'))
            return time.time() - float(d.get(key, 0)) < self.HOT_SECS
        except Exception:
            return False

    def _save_next_px(self, spec: str | None) -> None:
        self._next_px = spec
        if getattr(self, 'sticky_proxy', False):
            return
        d = self._pace_load()
        if spec:
            d['next_px'] = spec
        else:
            d.pop('next_px', None)
        self._pace_save(d)

    def _next_cool_spec(self, fallback_px: list, px_i: int) -> tuple[str | None, int]:
        if not fallback_px:
            return None, px_i
        n = len(fallback_px)
        for _ in range(n):
            spec = fallback_px[px_i % n]
            px_i = (px_i + 1) % n
            if not self._is_spec_hot(spec):
                return spec, px_i
        spec = fallback_px[px_i % n]
        px_i = (px_i + 1) % n
        return spec, px_i

    def _pace_result(self, ok: bool) -> None:
        key = self._pace_key()
        d = self._pace_load()
        slot = self._pace_slot(d, key)
        slot['refusals'] = 0 if ok else int(slot.get('refusals', 0) or 0) + 1
        slot['last_login'] = time.time()
        if not ok:
            nxt = self.PACE_BACKOFF[
                min(max(slot['refusals'], 1), len(self.PACE_BACKOFF)) - 1]
            self.log(
                f'[pace] refusal #{slot["refusals"]} on {key}: '
                f'wait {nxt:.0f}s then one try')
        self._pace_save(d)

    # ------------------------------------------------------------ sessions
    def _matchmaker(self):
        """Handshake, login, party, play.  Returns (host, port, node_token)."""
        # Per-dial, so a token refusal on an earlier dial cannot make a later
        # dial look like one too.
        self._token_refused = False
        paced = False
        self._pace_wait()

        tok = self.token or self.captured_token()
        ap_south = (self.region or '').strip().lower() == 'ap-south-1'
        # A real account token (Facebook g2gD) must stay on the persist
        # login. Forcing guest v6 on ap-south would mint a different Guest.
        guest_v6 = bool(getattr(self, 'guest_v6', False) or ap_south)
        if is_persist_token(tok):
            guest_v6 = False
        persist_login = bool(tok) and is_persist_token(tok) and not guest_v6
        if not tok and not guest_v6:
            self.log('[!] no auth token available — pass --token')
            return None
        if not tok:
            tok = ''

        # App (capture-main-30): 70, 119, 51 back-to-back.  Remint AES does
        # not use the mt=120 bytes, so we mint locally and send login in the
        # same burst.  Waiting for 104/120 first is what made EU look hung
        # and let the matchmaker drop the session before mt=51.
        fallback_px = []
        def _load_px(path, socks_only=False):
            try:
                for line in open(path, encoding='utf8'):
                    line = line.strip()
                    if not line or line.startswith('#'):
                        continue
                    low = line.lower()
                    if socks_only and not low.startswith('socks5://'):
                        continue
                    for pfx in ('socks5://', 'socks4://', 'http://', 'https://'):
                        if low.startswith(pfx):
                            line = line[len(pfx):]
                            break
                    if ':' in line:
                        fallback_px.append(line)
            except Exception:
                pass
        # LIVE list first, then bot file. Dedup so rotate does not
        # walk the same dead host twice.
        _load_px(os.path.join(HERE, 'proxies_live.txt'))
        _load_px(os.path.join(HERE, 'proxies_auth.txt'))
        _load_px(os.path.join(HERE, 'bot', 'proxies.txt'))
        _seen_px, _uniq_px = set(), []
        for spec in fallback_px:
            key = spec.strip()
            if key in _seen_px:
                continue
            _seen_px.add(key)
            _uniq_px.append(spec)
        fallback_px = _uniq_px
        saved_proxy = self.proxy
        # No --proxy means stay on this PC. Do not walk the SOCKS list.
        if not saved_proxy:
            fallback_px = []
        # Sticky: keep the launcher-assigned SOCKS. Rotating 50 shared-proxy
        # bots across 10 IPs after every refuse is what burned every IP.
        if self.sticky_proxy and saved_proxy:
            fallback_px = []
            self.log(f'[proxy] sticky '
                     f'{saved_proxy[0]}:{saved_proxy[1]} (no rotate)')
        prof = None
        saw = []
        if persist_login:
            # Guest pool tokens reconnect often. Allow proxy rotation so a
            # closed arena does not leave the bot stuck on one burned SOCKS.
            # Sticky fleets retry the same SOCKS a few times with pace gaps.
            if self.sticky_proxy and saved_proxy:
                max_dials = 4
            else:
                max_dials = 12 if (fallback_px or saved_proxy) else 1
        elif guest_v6:
            # Most handshakes are f1!=3. Those are skipped with no login.
            # 12 tries still makes an f1=3 guest likely, while keeping the
            # handshake burst small: 30 dials x 10 bots re-dialled the
            # matchmaker faster than it decays the throttle.
            max_dials = 12
        elif ap_south and fallback_px and saved_proxy is None:
            max_dials = min(5, 1 + len(fallback_px))
        else:
            max_dials = 2
        remint_login_sent = False
        px_i = 0
        explicit_proxy = saved_proxy
        dpace = self._pace_load()
        # require-proxy: the operator does not want a retry that leaves from
        # this PC's own address.  Refuse the bot outright instead of playing
        # direct -- a bot that shows up from the wrong IP is worse than one
        # that never shows up.
        if self.require_proxy and not explicit_proxy:
            # Nothing to reuse: --proxy was not given and the pool is empty.
            # Retrying is pointless without a SOCKS, and going direct is
            # exactly what the operator forbade.
            self.log('[proxy] require-proxy: koi SOCKS nahi mila — direct '
                     'dial nahi karunga (--proxy do ya proxies pool bharo)')
            return None
        # v6 with no --proxy: this PC reaches Mumbai directly. next_px must
        # not drag us onto a SOCKS that cannot open ap-south.
        if guest_v6 and not explicit_proxy:
            self.proxy = None
            saved_proxy = None
        elif not explicit_proxy:
            if dpace.get('next_px'):
                self._next_px = dpace['next_px']
            nxt = getattr(self, '_next_px', None)
            if nxt and fallback_px:
                self.proxy = parse_proxy(nxt)
                self.proxy_protocol = 'socks5'
                saved_proxy = self.proxy
            if saved_proxy and fallback_px and self._is_spec_hot(
                    f"{saved_proxy[0]}:{saved_proxy[1]}"):
                spec, px_i = self._next_cool_spec(fallback_px, px_i)
                if spec:
                    self.log(f'[mm] skip hot {saved_proxy[0]}:{saved_proxy[1]}'
                             f' -> {spec.split("@")[-1]}')
                    self.proxy = parse_proxy(spec)
                    self.proxy_protocol = 'socks5'
                    saved_proxy = self.proxy
        if saved_proxy and fallback_px:
            want = f"{saved_proxy[0]}:{saved_proxy[1]}"
            for i, spec in enumerate(fallback_px):
                if want in spec.split("@")[-1]:
                    px_i = (i + 1) % len(fallback_px)
                    break
        for dial_n in range(1, max_dials + 1):
            login_body = None
            login_label = ''
            if (persist_login and fallback_px and dial_n > 1
                    and not _is_facebook_token(tok)
                    and not self.require_proxy):
                # Guest pool: rotate SOCKS on every retry, even when the
                # launcher pinned an initial --proxy.
                # require-proxy switches this off: the retry must reuse the
                # SAME SOCKS, not jump to another one and never go direct.
                spec, px_i = self._next_cool_spec(fallback_px, px_i)
                if spec:
                    self.proxy = parse_proxy(spec)
                    self.proxy_protocol = 'socks5'
                    self.log(f'[mm] socks rotate {spec.split("@")[-1]}')
            if guest_v6:
                login_body = None
                login_label = 'login mt=51 (v6 LOGIN_ENC)'
            elif not persist_login:
                self.used_token = tok
                self._tried_tokens.add(_tok_id(tok))
                login_body = pkt_login(tok)
                login_label = f'login mt=51 (token {len(tok)} chars)'
            if (not guest_v6
                    and (self.region or '').strip().lower() == 'ap-south-1'
                    and fallback_px and saved_proxy is None
                    and not self.require_proxy):
                if dial_n == 1:
                    self.proxy = None
                    self.log('[mm] ap-south via capture-server first')
                else:
                    spec = fallback_px[(dial_n - 2) % len(fallback_px)]
                    self.proxy = parse_proxy(spec)
                    self.proxy_protocol = 'socks5'
                    self.log(f'[mm] ap-south via socks {spec.split("@")[-1]}')
            try:
                self.connect_mm(tries=1, base_wait=1.0)
            except Exception as e:
                self.log(f'[mm] dial {dial_n}/{max_dials} failed: {type(e).__name__}')
                if fallback_px:
                    spec, px_i = self._next_cool_spec(fallback_px, px_i)
                    self._save_next_px(spec)
                    if spec:
                        self.proxy = parse_proxy(spec)
                        self.proxy_protocol = 'socks5'
                        self.log(f'[proxy] rotated to next SOCKS {spec.split("@")[-1]}')
                elif self.require_proxy:
                    where = f'{self.proxy[0]}:{self.proxy[1]}' if self.proxy else 'none'
                    self.log(f'[proxy] require-proxy: retry {dial_n + 1}/{max_dials} on same SOCKS {where} (no direct)')
                time.sleep(0.4)
                continue
            q = self.q_mm
            self.mm_closed.clear()
            self._start_reader(self.mm, q, 'mm', self.mm_closed)
            saw.clear()
            # Live capture session 15 (app): 70+119, wait 104+120, THEN 51.
            # Sending 51 before 120 on this path = s2c=0 (capture-main-16).
            self.send(self.mm, pkt_hello(), 'hello mt=70')
            self.send(self.mm, pkt_hello2(), 'hello mt=119')
            hs_wait = (3.0 if guest_v6 else
                       (12.0 if (getattr(self, '_via_capture', False) or self.proxy)
                        else 4.0))
            # Never treat mt=104 as enough — sending 51 before 120 closes the
            # session (EU capture-main-16 and this ap-south v6 test).
            hello = self._wait_for(
                q, lambda m, w: (saw.append(m.mt) or m.mt == 120),
                hs_wait, 'mt=120', closed=self.mm_closed)
            if hello is None and guest_v6 and not self.mm_closed.is_set():
                self.log('[mm] v6: no 120 — next proxy')
                self._mark_proxy_hot()
                try:
                    self.mm.close()
                except Exception:
                    pass
                self.mm = None
                spec, px_i = self._next_cool_spec(fallback_px, px_i)
                if spec:
                    self.proxy = parse_proxy(spec)
                    self.proxy_protocol = 'socks5'
                    self.log(f'[mm] next socks {spec.split("@")[-1]}')
                time.sleep(1.2)
                continue
            elif hello is None:
                dropped = self.mm_closed.is_set()
                try:
                    self.mm.close()
                except Exception:
                    pass
                self.mm = None
                if 120 not in saw:
                    why = 'dropped after 104' if 104 in saw else (
                        'handshake dropped' if dropped else 'silent pipe')
                    if explicit_proxy:
                        self.log(f'[mm] {why} (dial {dial_n}/{max_dials}) — staying on this proxy')
                        time.sleep(0.4)
                        continue
                    self.log(f'[mm] {why} (dial {dial_n}/{max_dials}) — next SOCKS')
                    spec, px_i = self._next_cool_spec(fallback_px, px_i)
                    self._save_next_px(spec)
                    time.sleep(0.4)
                    continue
                time.sleep(0.4)
                continue
            if guest_v6:
                fmt = 'v6'
                hs = handshake_key_from_mt120(hello) if hello is not None else ''
                f1 = _server_login_f1(hs) if hs else None
                # A fresh guest is only the empty v6 ticket, and only when
                # the server asked for f1=3. Any other f1 with an empty
                # device is mt=97. v1/v4 with the shared device would make
                # all ten bots the same Guest. SHARED_GUEST uses that one
                # guest only to ask which region a party code lives in.
                shared = os.environ.get('SHARED_GUEST') == '1' and f1 in (1, 2, 4, 5)
                if f1 != 3 and not shared:
                    self.log(f'[login] server f1={f1} — fresh guest needs f1=3, next proxy')
                    self._mark_proxy_hot()
                    try:
                        self.mm.close()
                    except Exception:
                        pass
                    self.mm = None
                    spec, px_i = self._next_cool_spec(fallback_px, px_i)
                    if spec:
                        self.proxy = parse_proxy(spec)
                        self.proxy_protocol = 'socks5'
                        self.log(f'[mm] next socks {spec.split("@")[-1]}')
                    time.sleep(1.2)
                    continue
                try:
                    if shared:
                        fmt = {1: 'v1', 2: 'v2_acct', 4: 'v4', 5: 'v5_acct'}[f1]
                        wire = remint_wire_ticket(_AZHAR_DEVICE, shape=fmt)
                        self.log(f'[login] server f1={f1} -> shared {fmt}')
                    else:
                        wire = remint_wire_ticket('', shape=fmt)
                        self.log(f'[login] server f1={f1} -> {fmt}')
                    login_body = pkt_login(wire, plain=True)
                    login_label = f'login mt=51 ({fmt} LOGIN_ENC {len(wire)}c)'
                    self.used_token = wire
                    self.log(f'[login] azhar {fmt} LOGIN_ENC {len(wire)}c')
                except Exception as e:
                    self.log(f'[!] {fmt} mint fail: {e}')
                    return None
            if persist_login and _fb_account_parts() and _is_facebook_token(tok):
                hs = handshake_key_from_mt120(hello) if hello is not None else ''
                f1 = _server_login_f1(hs) if hs else None
                fmt = {1: 'fb1', 2: 'fb2', 3: 'fb3', 4: 'fb4', 5: 'fb5'}.get(f1)
                if fmt is None:
                    self.log(f'[login] server f1={f1} — skip, new handshake')
                    try:
                        self.mm.close()
                    except Exception:
                        pass
                    self.mm = None
                    time.sleep(0.3)
                    continue
                try:
                    wire = remint_wire_ticket(tok, shape=fmt)
                    login_body = pkt_login(wire, plain=False)
                    login_label = f'login mt=51 (facebook {fmt} {len(wire)}c)'
                    self.used_token = tok
                    self._tried_tokens.add(_tok_id(tok))
                    self._fb_sent = True
                    self.log(f'[login] facebook f1={f1} {fmt} {len(wire)}c')
                except Exception as e:
                    self.log(f'[!] facebook login fail: {e}')
                    try:
                        self.mm.close()
                    except Exception:
                        pass
                    self.mm = None
                    return None
            elif persist_login:
                # Guest pool / explicit g2gD: remint THIS token, never the
                # Facebook binary credential sitting on disk.
                hs = handshake_key_from_mt120(hello) if hello is not None else ''
                f1 = _server_login_f1(hs) if hs else None
                # The matchmaker picks the login's outer field at random per
                # connection, and answering with a different field closes the
                # socket with no reply.  Measured against eu-central-1:
                # f1=1 ('v1') and f1=4 ('v4') are accepted; f1=2/3/5 need the
                # account layouts 'acct2'/'acct3'/'f5' -- the old
                # v2_acct/v6_acct/v5_acct shapes were all refused.
                fmt = {1: 'acct1', 2: 'acct2', 3: 'acct3',
                       4: 'acct4', 5: 'acct5'}.get(f1, 'acct1')
                self.log(f'[login] persist f1={f1} -> {fmt}')
                try:
                    wire = remint_wire_ticket(tok, shape=fmt)
                    # The live app ships a reminted ticket in opcode-1 zlib
                    # (capture-main-1: f2=1 f4[495]); plain=True forces
                    # opcode-2 and was never accepted on this path.
                    login_body = pkt_login(wire, plain=False)
                    login_label = f'login mt=51 (persist {fmt} {len(wire)}c)'
                    self.used_token = tok
                    self._tried_tokens.add(_tok_id(tok))
                    self.log(f'[login] persist {fmt} {len(wire)}c')
                except Exception as e:
                    self.log(f'[!] persist login fail: {e}')
                    try:
                        self.mm.close()
                    except Exception:
                        pass
                    self.mm = None
                    return None
            remint_login_sent = bool(persist_login)
            # Facebook account is IP-bound tightly. Guest persist tokens are
            # not — marking them hot made every forever-reconnect fail.
            if persist_login and _is_facebook_token(tok):
                self._mark_proxy_hot()
            self.send(self.mm, login_body, login_label)
            # Official client waits for profile (or mt=33) after mt=51 before
            # post-login housekeeping.  Sending mt=23/76 immediately was
            # closing remint sessions on this path.
            prof = self._wait_for(
                q,
                lambda m, w: (saw.append(m.mt) or m.op == 1 or m.mt in (42, 33)),
                12, 'profile', closed=self.mm_closed)
            if prof is not None:
                # Auto-play gave mt=33: stash arena for arena-direct play.
                if getattr(prof, 'mt', None) == 33:
                    # mt=33 is NOT the profile -- it carries no party block, so
                    # current_party_code stays None and the bot believes it is
                    # Solo.  It is not: the account keeps whatever party the
                    # server still holds it in, and a bare mt=27 to a NEW code
                    # is then ignored (MEASURED: mt=42 arriving right after the
                    # join still reports the OLD party).  The fleet then splits
                    # across two parties -- some bots on the new code, some
                    # stuck on the old one.  Mark the state unknown so the join
                    # always leaves first.
                    self._party_state_unknown = True
                    try:
                        blob = one(prof.top, 3) or one(prof.top, 4)
                        raw = blob
                        if blob:
                            try:
                                raw = zlib.decompress(blob)
                            except Exception:
                                raw = blob
                            fl = fields(raw)
                            f39 = one(fl, 39)
                            if f39:
                                ff = fields(f39)
                                host = as_str(one(ff, 2))
                                port = one(ff, 3) or 9001
                                token = as_str(one(ff, 1))
                                # f1 is the NODE BEARER and only f1 works.
                                # Measured: mt=40 built from f1 is ~34 b and the
                                # node accepts it; the same packet built from the
                                # 157-char persist token is ~171 b and comes back
                                # `mt=97 {f108{f1:2}}` + 16 b then close.  An
                                # empty bearer is refused the same way.  So a
                                # redirect WITHOUT f1 is not an arena we can
                                # take -- claiming it just burned a dial and
                                # poisoned the node.  Leave arena_direct unset
                                # and let the caller make a fresh login.
                                if host and token:
                                    self.arena_direct = (host, int(port), token)
                                    self.log(f'[login] auto mt=33 -> arena '
                                             f'{host}:{port} (node bearer)')
                                elif host:
                                    self.log(f'[login] mt=33 has no node bearer '
                                             f'({host}:{port}) — skipping this '
                                             f'redirect, fresh login needed')
                    except Exception as e:
                        self.log(f'[login] mt=33 parse fail: {e}')
                break
            # Handshake-only saw (104/120) is not a hard stop — try next
            # login style on a fresh dial.
            post = [m for m in saw if m not in (70, 104, 119, 120)]
            if post:
                self.log(f'[mm] post-login msgs {post} — stop styles')
                break
            self.log(f'[mm] login style refused (dial {dial_n}/{max_dials}) — stop')
            try:
                self.mm.close()
            except Exception:
                pass
            self.mm = None
            spec, px_i = self._next_cool_spec(fallback_px, px_i)
            self._save_next_px(spec)
            # Facebook account: same proxy, next handshake, then stop.
            if persist_login:
                if _is_facebook_token(tok):
                    if (not getattr(self, '_fb_sent', False)
                            and explicit_proxy and dial_n < max_dials):
                        time.sleep(0.8)
                        continue
                    break
                # Guest pool: keep rotating SOCKS until max_dials.
                # Sticky: stay put — pace_wait on the next dial spaces us.
                if self.sticky_proxy:
                    self.log('[!] login rejected — sticky retry same proxy')
                    time.sleep(2.0)
                    continue
                self.log('[!] login rejected — next proxy')
                time.sleep(0.35)
                continue
            time.sleep(1.5)
            continue
        if prof is None:
            self.proxy = saved_proxy
            # A refused *token* looks exactly like a throttle: the handshake
            # completed, then the session died at the login.  Record it, so the
            # next run presents a different token instead of re-presenting the
            # same stale one until the heat death of the universe.
            self._token_refused = True
            if not persist_login and not guest_v6:
                self._mark_token_spent(tok)
            if not paced:
                self._pace_result(False)
            self.log('[!] login rejected / matchmaker closed the session')
            return None
        self._mark_token_ok(tok)
        self._pace_result(True)
        self._drain(q)

        # The server sometimes answers the LOGIN itself with an mt=33 arena
        # redirect (no mt=42 profile, and the matchmaker socket closes right
        # after).  When that happens the arena is already in hand: return it
        # instead of walking into the play loop on a socket that is gone, which
        # used to end as "[!] matchmaker closed the session -> could not reach
        # an arena" while a perfectly good arena sat unused.
        if getattr(self, 'arena_direct', None):
            h, p, t = self.arena_direct
            self.arena_direct = None
            self.log(f'[mm] login handed us the arena directly: {h}:{p}')
            return h, int(p), t

        # mt=33 without bearer often EOFs the MM socket.  Walking into
        # settings/party on a dead socket → WinError 10053 + leave spam.
        if self.mm is None or self.mm_closed.is_set():
            self.log('[mm] session closed after login (no bearer redirect) — '
                     'fresh dial (non-drop)')
            return None

        # Check current party membership from profile
        self.current_party_code = None
        self.current_party_host = None
        self.current_party_members = []
        try:
            p_blob = one(prof.top, 4)
            if p_blob:
                p_top = fields(zlib.decompress(p_blob))
                f76 = one(p_top, 76)
                if f76:
                    f76_fl = fields(f76)
                    f13 = one(f76_fl, 13)
                    if f13:
                        for _fn, _wt, v in fields(f13):
                            s = as_str(v)
                            if s.startswith('g2gD') and len(s) > 80:
                                self.persist_token = s
                                self.log(f'[token] persistent identity {len(s)} chars '
                                         f'(app isi ko 10 din baad bhi use karti hai)')
                                try:
                                    pth = os.path.join(HERE, 'bot', 'persist_token.txt')
                                    open(pth, 'w', encoding='utf8').write(s + '\n')
                                except Exception:
                                    pass
                                break
                    # Wallet / boost inventory lives in repeated f76.f7 records.
                    inv = {}
                    for fn, _wt, v in f76_fl:
                        if fn != 7 or not isinstance(v, bytes):
                            continue
                        rf = fields(v)
                        name = as_str(one(rf, 1))
                        qty = one(rf, 2)
                        if name and isinstance(qty, int):
                            inv[name] = qty
                    self._inventory = inv
                    f10 = one(f76_fl, 10)
                    if f10:
                        pff = fields(f10)
                        self.current_party_code = as_str(one(pff, 3))
                        for fn, _wt, v in pff:
                            if fn == 1 and isinstance(v, bytes):
                                nm, uu = party_member_identity(v)
                                if nm:
                                    self.current_party_members.append(nm)
                                    # Both layouts (guest f1{f4} and
                                    # registered f2) are handled by
                                    # party_member_identity().  Without a uuid
                                    # the roster is names-only, so the follow
                                    # target never resolved and every follower
                                    # searched for a uuid it could not match.
                                    if uu:
                                        self.party_uuids[nm] = uu
                                    elif nm not in self.party_raw:
                                        # Unknown layout: keep the raw entry
                                        # once so it can be taught, and keep the
                                        # NAME so the target can still resolve.
                                        self.party_raw[nm] = v.hex()
                                        self.log(f'[party] member {nm} has no '
                                                 f'parsed uuid — raw={v.hex()}')
                        if self.current_party_members:
                            self.current_party_host = self.current_party_members[0]
        except Exception:
            pass

        if self.current_party_code:
            members_str = ", ".join(self.current_party_members) if self.current_party_members else "(only us)"
            self.log(f'[party status] Currently JOINED in party: {self.current_party_code} — {len(self.current_party_members)} member(s): {members_str}')
            # Already in party: publish so siblings know these are party mates.
            if not self.party_code:
                self.party_code = self.current_party_code
            if not self.party_members:
                self.party_members = list(self.current_party_members)
            self._publish_party_now()
            _c, _nm, shared_u = _read_party_roster(self.current_party_code)
            self.log(f'[party] aware: code={self.current_party_code} '
                     f'shared_uuids={len(shared_u)} '
                     f'names={len(self._party_mate_names())}')
            if self.party_uuids:
                self.log(f'[party] roster {self._party_roster_report()}')
                want = (self.follow or '').lower()
                in_roster = any(
                    (u or '').lower() == want
                    or (want and (u or '').lower().startswith(want[:8]))
                    for u in self.party_uuids.values())
                if want:
                    self.log(f'[party] config uid {want[:8]} '
                             f'{"IS" if in_roster else "is NOT"} in the roster '
                             f'(roster is not how the target is matched — the '
                             f'arena cell uuid is)')
                human, hkind = self._party_human_key()
                if human:
                    self.log(f'[party] follow target resolves to {hkind}={human}')
                elif not getattr(self, "auto_target", False):
                    self.log('[party] auto-target off — following config uid '
                             f'{want[:8] or "(unset)"} only')
                else:
                    self.log('[party] follow target: no single non-bot member in '
                             'the roster — will keep trying')
        else:
            self.log('[party status] NOT in any party (Solo)')

        if getattr(self, 'party_status_only', False):
            self.log('[party status] Check complete. Exiting.')
            return PARTY_HOLD, 0, ''

        if getattr(self, 'leave_party', False):
            if self.current_party_code:
                self.log(f'[party] Leaving party {self.current_party_code}...')
                self.send(self.mm, pkt_leave_party(), 'leave party mt=80')
                self.log(f'[party] Successfully left party {self.current_party_code}!')
                self.current_party_code = None
                self.code = None
            else:
                self.log('[party] Not currently in any party, nothing to leave.')
            self.send(self.mm, pkt_ack23(), 'ack mt=23')
            time.sleep(2.0)
            self._drain(q)
            if getattr(self, 'leave_party_only', False):
                return None

        # Live app (capture-main-4): mt=99 settings, then 23, then events.
        self.send(self.mm, pkt_settings99(), 'settings mt=99')
        self.send(self.mm, pkt_ack23(), 'ack mt=23')
        self.send(self.mm, pkt_post_login_76(), 'post-login mt=76')
        fcm = ''
        if tok and ':APA91b' in tok:
            fcm = tok
        self.send(self.mm, pkt_fcm(fcm), 'fcm mt=74')
        # App always sends a base64 client-event tag here; without it the
        # matchmaker sometimes never answers the following mt=27 party join.
        self.send(self.mm, pkt_client_event('1vrPJpi2Rq0h89ixiFbNnA=='),
                  'client-event mt=21')
        self._drain(q)
        time.sleep(0.3)

        # Auto-Create Party: if create_party=True or code == 'CREATE':
        if (getattr(self, 'create_party', False) or (self.code and str(self.code).upper() == 'CREATE')) and not self.no_party:
            self.log('[party] Requesting matchmaker to CREATE a new party room (mt=49)...')
            self.send(self.mm, pkt_create_party(), 'create party mt=49')
            got_37 = self._wait_for(
                q, lambda m, w: m.mt == 37, 5,
                'party create mt=37', closed=self.mm_closed, quiet=True)
            if got_37 is not None and hasattr(got_37, 'raw'):
                raw_b = got_37.raw
                idx = raw_b.find(b"\x1a\x06")
                if idx != -1:
                    new_code = raw_b[idx+2 : idx+8].decode("ascii", errors="ignore")
                    if len(new_code) == 6 and new_code.isalnum():
                        self.log(f'[party] MATCHMAKER CREATED NEW PARTY CODE: {new_code}!')
                        self.code = new_code
                        self.party_code = new_code
                        try:
                            _p_json = os.path.join(PARENT, "captured_party.json")
                            with open(_p_json, "w", encoding="utf-8") as _pf:
                                _pf.write(f'{{"code": "{new_code}", "time": {time.time()}}}\n')
                        except Exception:
                            pass

        if self.code and not self.no_party:
            if self.current_party_code == self.code:
                # Party membership is per ACCOUNT, but the matchmaker still
                # needs the join on THIS socket to route us into the party's
                # arena.  Skipping it left every bot in its own public arena:
                # three different arena hosts, spawns scattered over the whole
                # map, and 400 mt=12 respawn asks against 28 real deaths.
                # Re-asserting is also what populates the member roster (with
                # the uuids the follow target is matched on).
                self.log(f'[party] re-asserting {self.code} on this session')
                self.party_code = self.current_party_code
                self.party_members = self.current_party_members
                self.send(self.mm, pkt_party(self.code),
                          f'party mt=27 "{self.code}" (re-assert)')
                # A RE-ASSERT OF AN EXISTING MEMBERSHIP DOES NOT GET A LOBBY
                # REPLY.  mt=98 is the answer to a real JOIN; when the account
                # is already in the party the matchmaker just pushes party
                # frames (mt=25 / mt=83 / mt=59) and stays quiet about mt=27.
                #
                # Waiting 12 s x 4 for an mt=98 that is never coming cost ~48 s
                # of EVERY session, with the bot nowhere near an arena -- and
                # because each reconnect re-ran it, the fleet spent most of its
                # time in this loop instead of playing.
                # MEASURED (tools/_live_check3.log, 2026-09-30): all five bots
                # sat here, retrying 2/4 -> 3/4, and NOT ONE of them ever
                # reached `mt=110 play`.
                #
                # So: send the join (the server needs it for routing), wait a
                # short grace period, accept ANY party frame as "routing is
                # warm", and move on.  Worst case is now ~10 s, not ~48 s.
                # Existing membership answers with mt=83/59/29 — NOT mt=98.
                # Waiting only for 98 timed out every session (~10 s of "drop"
                # while the fleet was already in the party).
                _party_ack = (98, 99, 33, 25, 83, 59, 29)
                got = self._wait_for(
                    q, lambda m, w: m.mt in _party_ack, 1.5,
                    'party ack', closed=self.mm_closed, quiet=True)
                if got is not None and got.mt == 98:
                    self._check_party(got)
                elif got is None:
                    self.log('[party] re-assert quiet — keep membership '
                             '(non-drop play)')
                if got is not None and got.mt != 98:
                    # Any party frame proves routing is warm — move on NOW.
                    self.log(f'[party] re-assert answered with mt={got.mt} — '
                             f'keeping {self.party_code or self.code}')
                if self.code and self.party_code != self.code:
                    # Account already in party — keep membership, play on.
                    self.log(f'[party] re-assert quiet — keep '
                             f'{self.current_party_code} (non-drop play)')
                    self.party_code = self.current_party_code
                    self.party_members = list(
                        self.current_party_members or [])
            else:
                # leave-before-join ONLY when we KNOW we are in a DIFFERENT
                # party.  mt=33 sets `_party_state_unknown` without clearing
                # the account's real membership — leave mt=80 there was
                # ConnectionAbortedError + Solo + Round finished drops.
                # Unknown / Solo → plain mt=27 re-assert of the config code.
                _need_leave = bool(
                    self.current_party_code
                    and self.current_party_code != self.code)
                if self.mm_closed.is_set() or self.mm is None:
                    self.log('[party] MM closed before join — fresh login')
                    return None
                if _need_leave:
                    _from = self.current_party_code
                    self.log(f'[party] switching {_from} -> {self.code}')
                    self.send(self.mm, pkt_leave_party(), 'leave-before-join mt=80')
                    time.sleep(1.2)
                    self._drain(q)
                elif getattr(self, '_party_state_unknown', False):
                    self.log(f'[party] state unknown — re-assert {self.code} '
                             f'(no leave)')
                else:
                    self.log(f'[party] joining code {self.code}')
                self.send(self.mm, pkt_party(self.code), f'party mt=27 "{self.code}"')
                _party_ack = (98, 37)

                def _take_party_ack(msg):
                    if msg is None:
                        return False
                    if msg.mt == 98:
                        return bool(self._check_party(msg))
                    if msg.mt == 37:
                        self.party_code = self.code
                        return True
                    return False

                got = self._wait_for(
                    q, lambda m, w: m.mt in _party_ack, 5,
                    'party ack', closed=self.mm_closed, quiet=True)
                if not _take_party_ack(got):
                    self.log('[party] retry join')
                    time.sleep(0.4)
                    if _need_leave and not self.mm_closed.is_set():
                        self.send(self.mm, pkt_leave_party(), 'leave-before-join mt=80')
                        time.sleep(0.05)
                    if self.mm_closed.is_set() or self.mm is None:
                        self.log('[party] MM closed on retry — fresh login')
                        return None
                    self.send(self.mm, pkt_party(self.code), f'party mt=27 "{self.code}"')
                    got = self._wait_for(
                        q, lambda m, w: m.mt in _party_ack, 5,
                        'party ack', closed=self.mm_closed, quiet=True)
                    _take_party_ack(got)
                if self.code and self.party_code != self.code:
                    # Unknown state: assume config code (account was already in)
                    if getattr(self, '_party_state_unknown', False):
                        self.party_code = self.code
                        self.log(f'[party] assume still in {self.code} '
                                 f'(non-drop play)')
                    else:
                        self.log(f'[party] not in {self.code} — not starting solo')
                        return None
        elif self.current_party_code and not self.no_party:
            self.log(f'[party] Retaining current party {self.current_party_code}')
            self.party_code = self.current_party_code
            self.party_members = self.current_party_members

        if getattr(self, 'join_then_leave', False):
            left = self.party_code or self.code
            if left:
                self.log(f'[party] join-then-leave: leaving {left}')
                self.send(self.mm, pkt_leave_party(), 'leave party mt=80')
                time.sleep(1.5)
                self._drain(q)
                self.log(f'[party] left {left} — exiting without play')
            else:
                self.log('[party] join-then-leave: nothing to leave')
            return None

        if getattr(self, 'party_hold', False):
            # Interactive party controller: stay connected, do not play.
            return PARTY_HOLD, 0, ''

        # The app arms its boosts right before mt=110 and spawns ~132 instead
        # of ~13 (capture-main-22: C2S mt=94 -> S2C mt=43).  Guest wallets
        # report no count, which is why this used to be gated off -- but a
        # 13-mass bot is eaten before it ever reaches the operator, and that is
        # the whole "bots slowly drop to 0" complaint.  So try it regardless:
        # if the server has no item to grant it answers mt=97 and drops the
        # session, and _skip_mass_boost makes the next dial play without it.
        # One extra login per bot worst case.
        #
        # We arm EVERY configured item, not just the mass one.  `xp` and `mass`
        # are distinct boost types in the game's own catalogue, so mass alone
        # levels nothing: the operator asked for both, and they stack.
        if getattr(self, '_skip_mass_boost', False):
            self.log('[boost] skipped — server refused it on an earlier dial')
        elif self.boost_force or any(self._profile_boost_count(n) > 0
                                     for n in self.boost_items):
            self.log('[boost] arming ' + ', '.join(
                f'{n}(wallet={self._profile_boost_count(n)})'
                for n in self.boost_items)
                + f' forced={self.boost_force}'
                + f' every-play={int(bool(getattr(self, "boost_every_play", False)))}')
            self._activate_boosts(q)
            if getattr(self, '_skip_mass_boost', False) and self.mm_closed.is_set():
                return None
            if self._boosts_on:
                self.log('[boost] active: ' + ', '.join(sorted(self._boosts_on)))
        else:
            self.log('[boost] wallet owns none of ' + ', '.join(self.boost_items)
                     + ' — spawn at default')
        # Party Classic is flaky the same way players see it: Play sits on
        # "Connecting…" until you mash it.  Do NOT stop after 3–4 tries — keep
        # mt=110 going until mt=33 (or inline world) actually arrives.
        _am = (getattr(self, 'arena_mode', None) or 'classic').strip().lower()
        _gt = int(getattr(self, 'game_type', 13) or 13)
        # Player path: party already joined → mash Play (Burst/Classic) only.
        # No fleet room wait / opener — matchmaker assigns the arena.
        self.log(f'[play] requesting {_am.upper()} game_type={_gt} '
                 f'(mash Play until slot opens — arena full = keep retrying)')
        # Humans mash Play while "Connecting…" / arena full.  Stay on this
        # session a long time — a death frees a seat and the next mash gets in.
        play_deadline = time.time() + 900.0  # 15 min mash (Classic + Burst)
        attempt = 0
        pin_rejects = 0
        busy_hits = 0
        # Set when this session refused an arena because it was not the pinned
        # one.  The matchmaker tends to close the session shortly after a
        # refusal (it sees "here is your arena" answered with another mt=110).
        # Soft pin (cap 2) + clear-on-MM-close below keep the fleet from
        # burning whole logins on every pin miss.
        pin_refused = False

        def _pin_lost_session():
            """MM closed while we were hunting the pin host.

            Do NOT clear the pin here.  Clearing it (old behaviour) made the
            fleet forget the operator's arena and scatter across EC2 shards —
            operator only saw 2–3 bots.  Pin stays; next login hunts it again.
            """
            if not pin_refused:
                return
            self.log('[play] session closed while hunting pin — pin KEPT '
                     '(next login retries the operator arena)')

        while time.time() < play_deadline:
            attempt += 1
            if self.mm_closed.is_set():
                self.log('[!] matchmaker closed the session')
                _pin_lost_session()
                return None
            # Keep party routing warm — silent drop here is why bots land
            # in a different public arena while the operator sees only 1–2.
            if (self.code and not self.no_party
                    and attempt > 1 and attempt % 8 == 1):
                try:
                    self.send(self.mm, pkt_party(self.code),
                              f'party mt=27 "{self.code}" (pre-play keep)')
                except OSError:
                    return None
            # ALWAYS send nick — empty mt=110 => in-game name "UNNAMED".
            _pn = (self.nick or '').strip() or 'b'
            _pkt = self.play_pkt(_pn)
            if attempt == 1:
                self.log(f'[play] mt=110 hex={_pkt.hex()} '
                         f'(expect f1={_gt})')
            # Log sparsely — mash is fast; flooding hides FULL/retry story.
            _log_send = (attempt <= 3 or attempt % 20 == 0)
            self.send(
                self.mm, _pkt,
                f'play mt=110 {_am} gt={_gt} nick={_pn!r} (attempt {attempt})',
                silent=not _log_send)
            # mt=52 = arena busy / connecting (app keeps mashing Play).
            # mt=33 = redirect, mt=88+me = inline world.
            got = self._wait_for(
                q,
                lambda m, w: (
                    m.mt in (33, 52)
                    or m.mt == 88 or w.me is not None
                ),
                0.7, 'mt=33/52 (redirect or busy)',
                closed=self.mm_closed, quiet=True, log_frames=False)
            if got is None:
                if self.mm_closed.is_set():
                    _pin_lost_session()
                    return None
                if attempt == 1 or attempt % 15 == 0:
                    self.log(f'[play] still connecting — mash mt=110 '
                             f'(attempt {attempt}, busy={busy_hits})')
                try:
                    self.mm.sendall(frame(pkt_ack23()))
                except OSError:
                    return None
                time.sleep(0.05)
                continue
            if got.mt == 52:
                busy_hits += 1
                if busy_hits == 1 or busy_hits % 8 == 0:
                    self.log(f'[play] arena FULL/busy (mt=52) — mash again '
                             f'#{busy_hits} (slot opens on death)')
                try:
                    self.mm.sendall(frame(pkt_ack23()))
                except OSError:
                    return None
                time.sleep(0.05)
                continue
            if got.mt == 88 or self.world.me is not None:
                self.log('[arena] server is hosting the arena INLINE on the '
                         'matchmaker socket (no mt=33 redirect)')
                return INLINE_ARENA, 0, ''
            f39 = one(got.inner, 39)
            if f39 is None:
                self.log('[!] mt=33 without f39')
                continue
            f = fields(f39)
            host = as_str(one(f, 2))
            port = one(f, 3) or NODE_PORT
            token = as_str(one(f, 1))
            pin = _read_party_arena_pin()
            # Only hunt pin host after a sibling SEEN the follow target there.
            # Blind arena_id/host pin made Burst bots loop remash forever.
            #
            # NEVER answer a wrong-host mt=33 with another mt=110 — that is
            # what hangs up the matchmaker (MEASURED: reject → MM closed).
            # Instead DROP this session and re-login; pin is kept so the next
            # mt=33 can still hunt.  After 4 drops take the offer.
            _target_is_inline = bool(pin and pin.get('seen_target') and pin.get('host') == INLINE_ARENA)
            _target_is_ec2 = bool(pin and pin.get('seen_target') and _is_pinable_arena_host(pin.get('host')))
            _hunt_pin = False
            if self.code and not self.no_party:
                # Party mode: party code groups players, gateway nodes forward to shard.
                # Never drop sessions in party mode!
                _hunt_pin = False
            elif _target_is_inline and host:
                _hunt_pin = True
            elif _target_is_ec2 and host and _is_pinable_arena_host(host):
                _hunt_pin = not _same_arena_host(host, pin['host'])
            if _hunt_pin:
                pin_rejects += 1
                pin_refused = True
                if pin_rejects >= 4:
                    self.log(f'[play] pin {pin["host"]} missed {pin_rejects}x '
                             f'— take {host}, migrate via wrong-arena bail')
                else:
                    self.log(f'[play] got {host} want pin {pin["host"]} — '
                             f'drop session for fresh mt=33 '
                             f'(hunt {pin_rejects}/4, pin kept)')
                    return None
            self.log(f'[arena] host={host} port={port} token={token}'
                     + (f' (after {busy_hits} full/busy mashes)'
                        if busy_hits else ''))
            return host, int(port), token
        self.log('[play] no arena redirect after 15min of mt=110 mash')
        return None

    def _profile_boost_count(self, name: str) -> int:
        return int(getattr(self, '_inventory', {}).get(name, 0) or 0)

    def _boost_ack_secs(self, m) -> int:
        """Seconds the server actually granted, 0 when the grant is empty.

        Kept separate from the human-readable `_decode_boost_ack` because the
        caller has to make a DECISION on this number: a 0-second grant must not
        be recorded as an active boost, or every later log line ("active",
        "3x on") is a lie built on an accept that gave us nothing.
        """
        try:
            f33 = one(m.inner, 33)
            if not f33:
                return 0
            grant = one(fields(f33), 2)
            if not grant:
                return 0
            secs = one(fields(grant), 1)
            return int(secs) if isinstance(secs, int) and secs > 0 else 0
        except Exception:
            return 0

    def _decode_boost_ack(self, m) -> str:
        """Pull "(item for Ns)" out of the mt=43 accept frame.

        Decoded from capture-main-22 and confirmed against the live server:

            mt=43
              f33.f2.f2 = "mass_boost_3x_1h"   <- the item actually granted
              f33.f2.f1 = 3600                 <- duration, SECONDS (1 hour)
              f33.f1.f1 = 49                   <- grant id

        Reading it back matters because mt=43 is also the accept for *other*
        product types, so "server accepted" alone does not prove the item we
        asked for, or the duration we expected, is what came back.  Logging the
        echo turns a hopeful success line into a checkable one.
        """
        try:
            f33 = one(m.inner, 33)
            if not f33:
                return ''
            ff = fields(f33)
            grant = one(ff, 2)
            if not grant:
                return ''
            gg = fields(grant)
            item = as_str(one(gg, 2))
            secs = one(gg, 1)
            if not item:
                return ''
            if not isinstance(secs, int) or secs <= 0:
                # Seen live: the server answers mt=43 with the right item name
                # but a DURATION OF 0.  That is an accept that grants nothing --
                # which is why the boost "works" (no refusal, no mt=97, the
                # session survives) and yet the spawn is still ~14 and nothing
                # is multiplied.  Report it as the no-op it is instead of
                # printing a success line that implies an effect.
                extra = ', '.join(f'f{fn}={v}' for fn, _, v in gg
                                  if not isinstance(v, bytes))
                return (f'{item} for 0s — ACCEPTED BUT NO EFFECT'
                        + (f' (grant fields: {extra})' if extra else ''))
            if secs % 3600 == 0:
                return f'{item} for {secs // 3600}h'
            return f'{item} for {secs}s'
        except Exception:
            return ''

    def _arm_boosts_before_play(self, q) -> None:
        """Arm the configured boosts right before an mt=110 play request.

        Same packet, same order, same gating as the first dial -- the point of
        this wrapper is that the play request NEVER goes out without the boost
        request in front of it.  An account that owns the item looks exactly
        like this on the wire: mt=94, mt=94, then mt=110, every single time.

        It does not make the server grant anything it would not otherwise
        grant.  Read the mt=43 echo for that -- a 0-second grant is an accept
        that changes nothing, and _activate_boosts logs it as such.
        """
        if not self.boost_items:
            return
        if getattr(self, '_skip_mass_boost', False):
            return
        if not (self.boost_force
                or any(self._profile_boost_count(n) > 0 for n in self.boost_items)):
            return
        self.log('[boost] arming ' + ', '.join(
            f'{n}(wallet={self._profile_boost_count(n)})'
            for n in self.boost_items) + f' forced={self.boost_force}'
            + ' (every-play re-arm)')
        self._activate_boosts(q)

    def _activate_boosts(self, q) -> None:
        """Arm every configured boost the way the app does before play.

        mt=94 {f32{f1:<item>}} is a *generic* activate request -- the item name
        is the whole payload -- so the same packet arms any entry from the
        game's boost catalogue.  Read straight out of the APK's
        assets/unpack/GameConfiguration.json, section "Gameplay - Boosts",
        which lists each product with its own `type`:

            productId              type    multiplier  durationMins
            xp_boost_3x_1h         xp      3           60
            mass_boost_3x_1h       mass    3           60
            ...plus 2x and 24h variants, and token_boost_2x_*

        `xp` and `mass` are SEPARATE types, so they are separate items and
        neither implies the other: arming only mass_boost_3x_1h triples the
        mass you gain and does nothing for XP/level.  The game itself sells
        them together (bundle `1_mass_boost_3x_1h_1_xp_boost_2x_1h`), which is
        the confirmation that both are meant to be active at once.

        So send one mt=94 per item, in order, and wait for each reply:
        mt=43 = accepted, mt=97 = refused (and the server drops the session).
        A refusal must abort this dial cleanly so the retry can play without
        the boost -- see _skip_mass_boost.
        """
        items = list(getattr(self, 'boost_items', None) or [])
        if not items:
            return
        def _arm(name):
            """Send mt=94 and read back (reply, ack_text, granted_secs)."""
            self.send(self.mm, pkt_mass_boost(name), f'boost mt=94 {name}')
            got = self._wait_for(
                q, lambda m, w: m.mt in (43, 97), 3,
                f'mt=43 boost {name}', closed=self.mm_closed)
            if got is None or got.mt != 43:
                return got, None, 0
            return got, self._decode_boost_ack(got), self._boost_ack_secs(got)

        for name in items:
            if self.mm_closed.is_set():
                return
            bought = False
            if self._profile_boost_count(name) <= 0:
                prod = f'1_{name}' if not name.startswith('1_') else name
                self.send(self.mm, pkt_shop_buy(prod), f'shop buy mt=68 {prod}')
                buy_reply = self._wait_for(
                    q, lambda m, w: m.mt in (93, 97), 2,
                    f'mt=93 buy {prod}', closed=self.mm_closed)
                if buy_reply and buy_reply.mt == 93:
                    self.log(f'[boost] shop purchase confirmed: {prod}')
                    bought = True
            got, ack, secs = _arm(name)
            if got is None:
                self.log(f'[boost] no reply for {name} — continuing without it')
                continue
            if got.mt == 43:
                ack = self._decode_boost_ack(got)
                secs = self._boost_ack_secs(got)
                self.log(f'[boost] server accepted {name}'
                         + (f' — granted {ack}' if ack else ''))
                if ack and not ack.startswith(name):
                    # The server echoed a DIFFERENT item than we asked for.
                    # Say so rather than quietly reporting success for the
                    # wrong boost.
                    self.log(f'[boost] WARNING: asked for {name}, '
                             f'server granted {ack}')
                # A purchase is credited ASYNCHRONOUSLY.  Arming in the same
                # breath as the mt=93 confirmation comes back
                #   "accepted ... granted for 0s ... (grant fields: f1=0)"
                # and the bot then spawns at the default mass -- which is
                # exactly the "bots come without boost" report.  MEASURED:
                # 32 of 50 arms granted 0 s right after a confirmed purchase,
                # while arms that landed later granted 78225 s (21.7 h).
                # Give the credit a moment and re-arm ONCE before believing
                # the empty grant.
                if secs <= 0 and bought:
                    time.sleep(1.2)
                    self._drain(q)
                    got2, ack2, secs2 = _arm(name)
                    if got2 is not None and got2.mt == 43 and secs2 > 0:
                        ack, secs = ack2, secs2
                        self.log(f'[boost] {name} granted on the retry — '
                                 f'the wallet credit had not landed yet')
                if secs > 0:
                    self._boosts_on.add(name)
                    if name.startswith('mass') or name.startswith('rush'):
                        self._mass_boost_on = True
                else:
                    # Accepted but empty: the wallet owns none of this item, so
                    # the server is happy to answer and grants nothing.  Do NOT
                    # put it in _boosts_on -- "active" has to mean something.
                    self._boosts_on.discard(name)
                continue
            self.log(f'[boost] server refused {name} (mt={got.mt})')
            self._mass_boost_on = False
            # mt=97 kills this matchmaker session.  Mark so the next dial skips
            # the boost packets and can actually play.
            self._skip_mass_boost = True
            return

    def _check_party(self, m) -> bool:
        """Decode the mt=98 party reply and say plainly whether we got in.

        `f41.f2` is the status: PARTY_JOINED (5) comes with the member list,
        PARTY_NOT_FOUND (4) is a 12-byte stub with no payload.  Codes are
        region-scoped, so a valid code from another region lands here as
        not-found -- which used to be silently ignored, leaving the bot to
        play a solo game while claiming it had joined.
        """
        if m is None:
            self.log('[party] no reply to mt=27 — continuing solo')
            return False
        if m.mt != 98:
            return False
        f41 = one(m.inner, 41)
        if f41 is None:
            return False
        f = fields(f41)
        status = one(f, 2)
        if status != PARTY_JOINED:
            self.log(f'[party] code {self.code} NOT FOUND (status={status}). '
                     f'Party codes only exist in the region that created them '
                     f'— this one is not in {self.region}. Playing solo.')
            self.event('party_failed', code=self.code, status=status,
                       region=self.region)
            return False
        payload = one(f, 1)
        code, members = self.code, []
        if payload is not None:
            pf = fields(payload)
            code = as_str(one(pf, 3)) or code
            for fn, _wt, v in pf:
                if fn == 1 and isinstance(v, bytes):
                    nm, uu = party_member_identity(v)
                    if nm:
                        members.append(nm)
                        # Both account layouts are handled here; see
                        # party_member_identity() for why reading only
                        # f1{f4} drops every registered account.
                        if uu:
                            self.party_uuids[nm] = uu
        self.party_code = code
        self.party_members = members
        who = ', '.join(members) if members else '(only us)'
        self.log(f'[party] JOINED {code} — {len(members)} member(s): {who}')
        # Share roster so EVERY bot knows "ye party code ke log hain".
        self._publish_party_now()
        if self.party_uuids:
            self.log(f'[party] roster {self._party_roster_report()}')
            human, hkind = self._party_human_key()
            if human:
                self.log(f'[party] follow target resolves to {hkind}={human} '
                         f'(party member that is not one of our bots)')
            else:
                self.log('[party] follow target: no single non-bot member '
                         'found in the roster yet' if getattr(self, "auto_target", False)
                         else '[party] auto-target off — config uid only')
        _c, _nm, shared_u = _read_party_roster(code)
        self.log(f'[party] aware: code={code} local={len(members)} '
                 f'shared_uuids={len(shared_u)} '
                 f'names={len(self._party_mate_names())} '
                 f'(fleet will treat these as FRIENDLY)')
        self.event('party', code=code, members=members, region=self.region)
        return True

    def do_leave_party_fast(self) -> bool:
        """Fire mt=80 leave only — no verify reconnect. For fleet stop/scale."""
        code_to_leave = self.party_code or self.current_party_code or self.code or ''
        if not self.mm:
            self.log('[party] fast-leave: no MM socket')
            return False
        try:
            # Send twice — one packet can be lost under load; stop/scale needs
            # every bot out of the party, not just the lucky one.
            self.send(self.mm, pkt_leave_party(), 'leave party mt=80 (fast)')
            time.sleep(0.05)
            try:
                self.send(self.mm, pkt_leave_party(), 'leave party mt=80 (fast2)')
            except Exception:
                pass
            # Brief drain so the packet actually leaves the NIC before we die.
            try:
                self._wait_for(self.q_mm, lambda m, w: m.mt in (98, 99), 2.0,
                               'mt=98 after fast-leave', closed=self.mm_closed)
            except Exception:
                time.sleep(0.5)
            self.code = None
            self.party_code = None
            self.current_party_code = None
            self.no_party = True
            self.log(f'[party] FAST LEFT {code_to_leave or "(party)"}')
            return True
        except Exception as e:
            self.log(f'[party] fast-leave fail: {e}')
            return False

    def tick_live_ctrl(self) -> bool:
        """Called from play loops — honor leave_stop / scale without waiting
        for the poller thread. Returns True if this bot should exit NOW."""
        if _live_ctrl is None:
            return False
        try:
            doc = _live_ctrl.read_ctrl()
        except Exception:
            return False
        if not doc:
            return False
        cmd = (doc.get("cmd") or "").strip().lower()
        if cmd == "leave_stop":
            try:
                self.do_leave_party_fast()
            except Exception:
                pass
            self.log('[live] leave_stop (tick) — stopping')
            try:
                self.stop()
            except Exception:
                pass
            return True
        try:
            want = int(doc.get("bots") or 0)
        except Exception:
            want = 0
        try:
            _bi = getattr(self, 'bot_index', None)
            my = (_bi + 1) if _bi is not None else (int(os.environ.get("BOT_INDEX", "0")) + 1)
        except Exception:
            my = 1
        if want > 0 and my > want:
            try:
                self.do_leave_party_fast()
            except Exception:
                pass
            self.log(f'[live] scale-down tick #{my}>{want} — stopping')
            try:
                self.stop()
            except Exception:
                pass
            return True
        # Keep nick fresh from live_ctrl (fixes UNNAMED after empty play)
        nick = (doc.get("nick") or "").strip()
        if nick:
            want_n = nick[:15]
            if (self.nick or "") != want_n:
                self.apply_live_nick(want_n)
        return False

    def do_leave_party(self) -> bool:
        """Leave current party and verify against a fresh profile login."""
        code_to_leave = self.party_code or self.current_party_code or self.code or ''
        if not self.mm:
            print(' [!] Not connected to matchmaker.', flush=True)
            return False
        self.log(f'[party] Leaving party {code_to_leave or "(current)"}...')
        try:
            # App-exact leave: a single bare mt=80 (verified capture 2026-09-25).
            self.send(self.mm, pkt_leave_party(), 'leave party mt=80')
            got = self._wait_for(self.q_mm, lambda m, w: m.mt in (98, 99), 6,
                                 'mt=98 after leave', closed=self.mm_closed)
            if got and got.mt == 98:
                self._check_party(got)
            else:
                time.sleep(1.0)
                self._drain(self.q_mm)
        except Exception as e:
            print(f' [!] leave send failed: {e}', flush=True)
            return False

        # Ground truth: reconnect and read party from profile.
        region = self.region
        print(' [*] Verifying leave via fresh profile...', flush=True)
        try:
            self.close()
        except Exception:
            pass
        time.sleep(1.0)
        verify = AgarBot(
            region=region, code=None, verbose=False, mm_tries=2, mm_wait=6.0,
            prefer=getattr(self, 'prefer', 'ipv4'),
            token_retry=max(1, len(token_candidates()) - 1),
            party_hold=True, no_party=True,
        )
        ok = False
        try:
            ok = verify.run()
        except Exception as e:
            print(f' [!] verify connect failed: {e}', flush=True)
            verify.close()
            return False
        if not ok or not verify.mm:
            print(' [!] Could not verify (login failed). Leave status unknown.', flush=True)
            verify.close()
            return False

        # Steal the live session so party_control keeps working.
        self.mm = verify.mm
        self.q_mm = verify.q_mm
        self.mm_closed = verify.mm_closed
        self.used_token = verify.used_token
        self.region = verify.region
        self.host = verify.host
        self.current_party_code = verify.current_party_code
        self.current_party_host = verify.current_party_host
        self.current_party_members = list(verify.current_party_members)
        self.party_code = verify.party_code or verify.current_party_code
        self.party_members = list(verify.party_members or verify.current_party_members)
        self.code = None
        self.no_party = not bool(self.party_code)
        # Prevent verify.__del__/close from killing our stolen socket
        verify.mm = None
        verify.q_mm = queue.Queue()
        verify.close()

        still = self.party_code or self.current_party_code
        print('\n' + '=' * 50, flush=True)
        if still:
            print(f' [!] LEAVE FAILED — still in party: {still}', flush=True)
            print(' [STATUS] Account party membership did NOT clear.', flush=True)
            print('=' * 50 + '\n', flush=True)
            return False
        print(f' [PARTY] LEFT {code_to_leave or "(party)"} — verified SOLO', flush=True)
        print(f' [STATUS] SOLO | Region: {self.region}', flush=True)
        print('=' * 50 + '\n', flush=True)
        self.party_code = None
        self.current_party_code = None
        self.party_members = []
        self.current_party_members = []
        return True

    def apply_live_nick(self, nick: str) -> None:
        """Hot-swap arena nick (mt=110). Party roster still shows Guest_*."""
        nick = (nick or '').strip()[:15]
        if not nick:
            return
        self.nick = nick
        sent = False
        try:
            if self.arena and not self.ar_closed.is_set():
                sent = bool(self._arena_send(self.play_pkt(nick)))
        except Exception:
            sent = False
        if sent:
            self.log(f'[live] nick -> {nick} (mt=110 sent)')
        else:
            # Next death/respawn / connecting burst will use the new nick.
            self._want_play = True
            self.log(f'[live] nick -> {nick} (queued for next play)')

    def do_join_party(self, new_code: str) -> bool:
        """Join a party code on the open matchmaker socket. Returns True if JOINED."""
        new_code = (new_code or '').strip().upper()
        if not new_code:
            print(' [!] Usage: join <CODE>', flush=True)
            return False
        if not self.mm:
            print(' [!] Not connected to matchmaker.', flush=True)
            return False
        self.code = new_code
        self.no_party = False
        self.log(f'[party] Joining party {new_code}...')
        try:
            # App-exact: leave any current party (mt=80) before joining a new
            # code, then send the join (mt=27).  Matches the official client.
            self.send(self.mm, pkt_leave_party(), 'leave-before-join mt=80')
            time.sleep(0.05)
            self.send(self.mm, pkt_party(new_code), f'party mt=27 "{new_code}"')
            got = self._wait_for(self.q_mm, lambda m, w: m.mt in (98, 99), 12,
                                 'mt=98 party lobby', closed=self.mm_closed)
        except Exception as e:
            print(f' [!] join failed: {e}', flush=True)
            return False
        ok = self._check_party(got)
        print('\n' + '=' * 50, flush=True)
        if ok:
            print(f' [PARTY] JOINED {self.party_code}', flush=True)
            who = ', '.join(self.party_members) if self.party_members else '(only us)'
            print(f' [MEMBERS] {who}', flush=True)
            print(f' [REGION] {self.region}', flush=True)
        else:
            print(f' [PARTY] JOIN FAILED for {new_code}', flush=True)
            print(f' [HINT] Wrong region? Current: {self.region}', flush=True)
            cur = self.party_code or self.current_party_code
            if cur:
                print(f' [STATUS] Still in: {cur}', flush=True)
            else:
                print(' [STATUS] SOLO', flush=True)
        print('=' * 50 + '\n', flush=True)
        return ok

    def do_change_region(self, new_region: str):
        """Change current region and trigger reconnection."""
        new_region = new_region.strip()
        self.region = new_region
        self.host = host_for(new_region)
        print("\n" + "="*60)
        print(f" [REGION] Switching region to {new_region} ({self.host})...")
        print("="*60 + "\n", flush=True)
        self._stop.set()

    def print_status(self):
        """Print visual status banner with current region, party, and game stats."""
        st = self.world.stats() if self.world else {}
        party_str = f"JOINED in Party '{self.party_code or self.current_party_code}'" if (self.party_code or self.current_party_code) else "SOLO (Not in any party)"
        members_str = ", ".join(self.party_members) if self.party_members else ("None" if not (self.party_code or self.current_party_code) else "(only us)")
        enem = self.world.enemies() if self.world else []
        virs = self.world.viruses() if self.world else []
        me = self.world.me if self.world else None
        near_e = f"{enem[0]['name']} (mass: {enem[0]['mass']:.0f}, dist: {enem[0]['dist']:.0f}, [{enem[0]['threat']}])" if enem else "None"
        near_v = f"{min(math.hypot(v.x - me.x, v.y - me.y) for v in virs):.0f} units" if (virs and me) else "None"
        threats_n = sum(1 for e in enem if e['threat'] == 'THREAT')
        prey_n = sum(1 for e in enem if e['threat'] == 'PREY')

        print("\n" + "="*66)
        print("                 CURRENT BOT STATUS")
        print("="*66)
        print(f"  [Region]          : {self.region} ({self.host})")
        print(f"  [Party Status]    : {party_str}")
        print(f"  [Party Members]   : {members_str}")
        print(f"  [Nickname]        : {self.nick or '(Facebook / Guest)'}")
        print(f"  [Player Mass]     : {st.get('mass', 0.0):.1f} (Total: {st.get('total_mass', 0.0):.1f} | Peak: {st.get('peak_mass', 0.0):.1f})")
        print(f"  [Enemies Visible] : {len(enem)} (Threats: {threats_n}, Prey: {prey_n})")
        print(f"  [Nearest Enemy]   : {near_e}")
        print(f"  [Viruses Visible] : {len(virs)} (Nearest: {near_v})")
        print(f"  [Food / Pellets]  : {st.get('food', 0)} visible (Ate: {st.get('ate', 0)} | Score: {st.get('score', 0)})")
        print(f"  [Position]        : ({st.get('x', 0)}, {st.get('y', 0)}) | Mode: {st.get('mode', 'IDLE')}")
        print(f"  [Deaths / Lives]  : {st.get('deaths', 0)} deaths, life #{st.get('lives', 0) + 1}")
        print("="*66 + "\n", flush=True)

    def _node_redirect(self, m):
        """mt=33 {f39{f1:token, f2:host, f3:port}} — same shape on MM and node."""
        f39 = one(m.inner, 39)
        if not f39:
            return None
        f = fields(f39)
        host = as_str(one(f, 2))
        port = int(one(f, 3) or NODE_PORT)
        token = as_str(one(f, 1))
        if not host or not token:
            return None
        return host, port, token

    def _arena(self, host, port, node_token, deadline, hops=0, visited=None) -> bool:
        self._pending_redirect = None
        self._arena_refused = None
        self.arena_host, self.arena_port = host, port
        # Redirect handling lives at the bottom of this method, where BOTH the
        # node we are on and the node we are being sent to are known -- see the
        # ping-pong guard there.
        if visited is None:
            visited = set()
        visited.add(_norm_arena_host(host))
        # MM login via capture SOCKS must use the SAME egress for the arena
        # node token, or we get mt=106 with no self spawn.  Phone/app keeps
        # one IP; NAT64 here is a different source → "no self".
        used_capture_arena = False
        if getattr(self, '_via_capture', False) and not self.proxy:
            try:
                req = urllib.request.Request(
                    'http://127.0.0.1:9080/node',
                    data=json.dumps({
                        'host': host, 'port': int(port),
                        'token': node_token or '',
                    }).encode(),
                    method='POST',
                    headers={'Content-Type': 'application/json'})
                urllib.request.urlopen(req, timeout=2).read()
            except Exception as e:
                self.log(f'[arena] capture /node register fail: {e}')
            s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            s.settimeout(8.0)
            try:
                s.connect(('127.0.0.1', 9001))
                s.settimeout(ARENA_SOCK_TIMEOUT)
                s.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
                self.arena = s
                used_capture_arena = True
                self.log(f'[arena] via capture-server 127.0.0.1:9001 '
                         f'-> {host}:{port} (same SOCKS as MM)')
            except OSError as e:
                try:
                    s.close()
                except Exception:
                    pass
                self.log(f'[arena] capture :9001 failed ({e}); falling back')
                self.arena = None

        if used_capture_arena:
            pass  # self.arena already set
        elif self.proxy:
            ph, pp = self.proxy[0], self.proxy[1]
            dest = host
            m = re.search(r'ec2-(\d+)-(\d+)-(\d+)-(\d+)', host or '')
            if m:
                dest = '.'.join(m.groups())
            self.log(f'[arena] dialing {dest}:{port} via socks {ph}:{pp}')
            box = {}

            def _dial():
                try:
                    box['s'] = proxy_dial(self.proxy, dest, port, 6,
                                          self.proxy_protocol)
                except Exception as e:
                    box['e'] = e

            th = threading.Thread(target=_dial, daemon=True)
            th.start()
            th.join(8.0)
            if 's' not in box:
                err = box.get('e', TimeoutError('arena SOCKS hung'))
                self.log(f'[arena] dial failed: {type(err).__name__}: {err}')
                return False
            self.arena = box['s']
            try:
                self.arena.settimeout(ARENA_SOCK_TIMEOUT)
                self.arena.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
            except OSError:
                pass
            self.log(f'[arena] tunnel up via {ph}:{pp} -> {dest}:{port}')
        else:
            extra = []
            m = re.search(r'ec2-(\d+)-(\d+)-(\d+)-(\d+)', host or '')
            if m:
                extra.append('.'.join(m.groups()))
            try:
                extra += [ai[4][0] for ai in socket.getaddrinfo(
                    host, port, socket.AF_INET, socket.SOCK_STREAM)]
            except Exception:
                pass
            extra = list(dict.fromkeys(extra))
            last_err = None
            sock = None
            for ip4 in extra:
                s = None
                try:
                    s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
                    s.settimeout(4.0)
                    s.connect((ip4, int(port)))
                    s.settimeout(ARENA_SOCK_TIMEOUT)
                    s.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
                    sock = s
                    self.log(f'[arena] connected {host}:{port} via {ip4}')
                    break
                except OSError as e:
                    last_err = e
                    if s is not None:
                        try:
                            s.close()
                        except Exception:
                            pass
            if sock is None:
                for ip4 in extra:
                    s = None
                    try:
                        n64 = self._v4_to_nat64(ip4)
                        s = socket.socket(socket.AF_INET6, socket.SOCK_STREAM)
                        s.settimeout(4.0)
                        s.connect((n64, int(port), 0, 0))
                        s.settimeout(ARENA_SOCK_TIMEOUT)
                        s.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
                        sock = s
                        self.log(f'[arena] connected {host}:{port} via NAT64 {n64}')
                        break
                    except OSError as e:
                        last_err = e
                        if s is not None:
                            try:
                                s.close()
                            except Exception:
                                pass
            if sock is not None:
                self.arena = sock
            else:
                e = last_err or OSError(f'cannot reach {host}:{port}')
                try:
                    req = urllib.request.Request(
                        'http://127.0.0.1:9080/node',
                        data=json.dumps({
                            'host': host, 'port': int(port),
                            'token': node_token or '',
                        }).encode(),
                        method='POST',
                        headers={'Content-Type': 'application/json'})
                    urllib.request.urlopen(req, timeout=0.5).read()
                except Exception:
                    pass
                s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
                s.settimeout(0.6)
                try:
                    s.connect(('127.0.0.1', 9001))
                    s.settimeout(ARENA_SOCK_TIMEOUT)
                    s.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
                    self.arena = s
                    self.log(f'[arena] direct failed ({type(e).__name__}); '
                             f'via capture-server 127.0.0.1:9001 -> {host}:{port}')
                except OSError:
                    try:
                        s.close()
                    except Exception:
                        pass
                    raise e
        q = self.q_ar
        self.ar_closed.clear()
        # A half-open arena socket is fatal in a way EOF is not: recv() just
        # keeps timing out, ar_closed is never set, and the bot spends the rest
        # of the round commanding a world that stopped updating.  Give the
        # arena reader an explicit silence deadline so it raises the same flag
        # a real EOF would.  Generous (ARENA_SILENT) because a healthy node
        # pushes snapshots many times a second.  The reader polls on the same
        # timeout the socket carries, so recv and sendall cannot disagree.
        self._start_reader(self.arena, q, 'arena', self.ar_closed,
                           silent_after=ARENA_SILENT, poll=ARENA_SOCK_TIMEOUT)

        # Connecting phase: players keep rejoining with the SAME node token
        # until the cell appears.  New mt=110 here is what scatters the fleet
        # across other arenas (operator only sees 1–2 bots).
        if self._arena_send(pkt_node_join(node_token)):
            self.log('  -> node join mt=40 '
                     f'({len(pkt_node_join(node_token))}b)')
        else:
            return False
        # The live app's 132-mass spawn is mt=110 alone (capture session 23).
        # mt=111 on this burst is what the older node join used, and that
        # path came back as mass 10. Ask for the play spawn first.
        if not self._arena_send(pkt_joy(0.0, 0.0)):
            self.log('[arena] burst send failed — node unresponsive')
            return False
        _pn = (self.nick or '').strip() or 'b'
        if not self._arena_send(self.play_pkt(_pn)):
            self.log('[arena] burst send failed — node unresponsive')
            return False
        got = self._wait_for(q, lambda m, w: m.mt in (88, 45, 106,
                                                     ARENA_REFUSAL_MT)
                             or w.me is not None,
                             12, 'node assignment (mt=106)', closed=self.ar_closed)
        if self._arena_refused is not None:
            # Do NOT fall through to the 18 s "connecting" loop or the
            # same-token redials: the node has already answered.
            self._arena_token_bounced = True
            return False
        if got is not None and got.mt == 106:
            info = ''
            try:
                f100 = one(got.inner, 100)
                if f100:
                    inner = one(fields(f100), 1) or f100
                    ff = fields(inner)
                    info = (f"id={as_str(one(ff, 1))} "
                            f"region={as_str(one(ff, 2))} "
                            f"host={as_str(one(ff, 3))} port={one(ff, 4)}")
            except Exception as e:
                info = f'parse {type(e).__name__}'
            self.log(f'[arena] mt=106 {info}')
        if got is None and self.ar_closed.is_set():
            # Dead socket mid-connect — caller will redial SAME token.
            self.log('[arena] closed while connecting — same-token redial')
            return False
        if not self._arena_send(pkt_joy(0.15, 0.0)):
            return False
        time.sleep(0.08)
        self._pump_arena()
        _pn = (self.nick or '').strip() or 'b'
        if self.world.me is None:
            if not self._arena_send(self.play_pkt(_pn)):
                return False
        t0 = time.time()
        last_join = t0
        last_play = t0
        join_n = 1
        # Keep mt=40 (same token) + mt=110 until we actually have a cell.
        while time.time() - t0 < 18.0:
            self._heartbeat += 1
            self._pump_arena()
            if self.world.me is not None:
                break
            if self._arena_refused is not None:
                self.log(f'[arena] join refused (code {self._arena_refused}) — '
                         f'not redialling this token')
                self._arena_token_bounced = True
                return False
            if self.ar_closed.is_set() and self.q_ar.empty():
                self.log('[arena] socket closed before a cell — same-token redial')
                break
            now = time.time()
            # Player "connecting" mash: send play packet (mt=110), do NOT re-send mt=40 (bearer token is single-use and already consumed)
            if now - last_play >= 0.8 and self.world.me is None:
                _pn = (self.nick or '').strip() or 'b'
                if not self._arena_send(self.play_pkt(_pn)):
                    break
                last_play = now
            self._send_joy((0.25, 0.05))
            time.sleep(0.08)
        self._pump_arena()

        if self.world.me is not None:
            return self._announce_world()
        red = getattr(self, '_pending_redirect', None)
        if red and hops < 3:
            self._pending_redirect = None
            same_node = _same_arena_host(red[0], host)
            # Cross-host: gateway node points at the real party shard.
            # Remember that host as the fleet pin (so siblings hunt it).
            # If it matches the SEEN pin, try the redirect token ONCE —
            # otherwise skip (mt=97) and force a fresh login.
            if not same_node:
                if hops == 0 and red[0] and red[2]:
                    self.log(f'[arena] following gateway redirect hop 1 -> {red[0]}:{red[1]} (party shard)')
                    try:
                        self.arena.close()
                    except OSError:
                        pass
                    return self._arena(red[0], red[1], red[2], deadline,
                                       hops + 1, visited)
                self._arena_token_bounced = True
                self.log(f'[arena] node says move to {red[0]}:{red[1]} — '
                         f'cross-host hop skipped; fresh login')
                try:
                    self.arena.close()
                except OSError:
                    pass
                return False
            # Same-node retry (bounded by hops).
            if _norm_arena_host(red[0]) in visited and hops >= 1:
                self._arena_token_bounced = True
                self.log(f'[arena] same-node redirect already tried — '
                         f'giving up on this token')
                return False
            self.log(f'[arena] following redirect hop {hops + 1} -> '
                     f'{red[0]}:{red[1]} (same node — retry)')
            try:
                self.arena.close()
            except OSError:
                pass
            return self._arena(red[0], red[1], red[2], deadline, hops + 1,
                               visited)
        # Same-token redial: close half-open socket and dial again with the
        # EXACT mt=33 token.  Fresh mt=110 is what dumps bots into other arenas.
        if hops < 4 and node_token:
            self.log(f'[arena] still connecting — redial same token '
                     f'(hop {hops + 1}/4)')
            try:
                if self.arena is not None:
                    self.arena.close()
            except OSError:
                pass
            self.arena = None
            self.ar_closed.set()
            time.sleep(0.2)
            return self._arena(host, port, node_token, deadline, hops + 1,
                               visited)
        return self._announce_world()

    def _announce_world(self) -> bool:
        """Log the decoded world + our cell.  True if we can actually play."""
        me = self.world.me
        if me is None:
            self.log('[!] no self entity in snapshot — cannot play')
            return False
        self.log(f'[world] arena={self.world.arena:.0f} id={self.world.arena_id} '
                 f'entities={len(self.world.entities)}')
        self.log(f'[self] id={me.id} at ({me.x:.0f},{me.y:.0f}) r={me.r:.1f} '
                 f'mass={me.mass:.1f} score={self.world.score}')
        # Stay on whatever arena Play gave us (player click Burst/Classic).
        # Soft pin only refreshes when we already match a huntable pin host;
        # never bounce for a different arena_id.
        if self.code and not self.no_party:
            pin = _read_party_arena_pin()
            _is_inline = self._arena_is_inline()
            _cur_host = INLINE_ARENA if _is_inline else (self.arena_host or '')
            _cur_ar = (self.world.arena_id or '').strip()
            if pin and pin.get('seen_target'):
                if not _same_fleet_room(pin, _cur_ar, _cur_host):
                    self.log(f'[party] landed in {_cur_ar or _cur_host} but target is in '
                             f'{pin.get("arena_id") or pin.get("host")} — will migrate to Prince')
                else:
                    self.log(f'[party] confirmed in target arena {_cur_ar or _cur_host} with Prince')
        self.event('joined', host=self.arena_host, port=self.arena_port,
                   mass=me.mass)
        return True

    def _calibrate(self, deadline=None):
        """Probe +x then +y for ~1s each to learn the input->motion map."""
        if not self.calibrate or self.mode in ('follow', 'leave', 'feed-leave', 'feedleave'):
            return
        me = self.world.me
        if me is None:
            return
        self.log('[calib] probing input->motion map (2 x 1.1s)')
        res = {}
        for name, vec in (('+x', (1.0, 0.0)), ('+y', (0.0, 1.0))):
            self._pump_arena()
            t0 = time.time()
            start = None
            warm = t0 + 0.55
            while time.time() < t0 + 1.15 and (deadline is None or time.time() < deadline):
                me = self.world.me
                if me is None:
                    break
                if time.time() >= warm and start is None:
                    start = (me.x, me.y)
                self._pump_arena()
                self._send_joy(vec)
                time.sleep(self.tick)
            me = self.world.me
            if me is not None and start is not None:
                res[name] = (me.x - start[0], me.y - start[1])
                self.log(f'[calib] cmd {name} -> move ({res[name][0]:+.0f},{res[name][1]:+.0f})')
        if '+x' in res and '+y' in res:
            self.hmap.build(res['+x'], res['+y'])
            self.log(f'[calib] input map: {self.hmap.note}')

    def _arena_is_inline(self) -> bool:
        """True when the arena is the matchmaker socket (no separate EC2 node).

        Burst/party often host the world INLINE.  Closing `arena` there closes
        MM too — that was the fleet "drop" (WinError 10038 + Round finished).
        """
        if self.arena is None or self.mm is None:
            return False
        if self.arena is self.mm:
            return True
        # Events are aliased on inline attach — treat that as inline too.
        try:
            if self.ar_closed is self.mm_closed:
                return True
        except Exception:
            pass
        return False

    def _mark_arena_wedged(self, reason: str) -> None:
        """A bounded send timed out or failed: the node is gone.

        `sendall` that times out may already have written PART of a frame, so
        the stream is corrupt -- the connection has to be torn down, not
        retried.  Setting `ar_closed` is how every other failure path in this
        class reports "node dead", so the play loop picks it up on its next
        tick and does a soft reconnect instead of hanging.

        The socket is CLOSED as well as flagged, because that is the only way
        to unblock a thread already parked inside send()/recv() on it -- and
        that parked thread is the whole reason this method exists.

        INLINE exception: arena IS the matchmaker.  Closing it kills the whole
        session.  Flag play-loop exit without tearing MM so run() can remash.
        """
        if self._arena_is_inline():
            self.log(f'[arena] {reason} — inline socket wedged, soft remash '
                     f'(MM kept open)')
            try:
                self.world.dead = True
                self.world.self_id = None
            except Exception:
                pass
            # Detach only; do NOT set mm_closed / close mm.
            self.arena = None
            self._inline_need_reenter = True
            return
        if self.ar_closed.is_set():
            return
        self.log(f'[arena] {reason} — node unresponsive, marking it dead '
                 f'so the loop can reconnect')
        try:
            self.ar_closed.set()
        except Exception:
            pass
        try:
            if self.arena is not None:
                self.arena.close()
        except Exception:
            pass

    def _force_session_drop(self, reason: str) -> None:
        """Tear down BOTH sockets.  For the stall watchdog only.

        _mark_arena_wedged() deliberately leaves the matchmaker alone, because
        an ordinary arena failure can still be recovered cheaply on the same
        session (see the soft-bail path in run()).  A *stalled* process is a
        different animal: the parked call may be on either socket -- a blocked
        matchmaker send hangs the main thread just as effectively as a blocked
        arena send -- and a stalled session is not worth keeping.  Closing both
        is what actually unblocks whichever one is parked.
        """
        self.log(f'[watchdog] dropping the whole session: {reason}')
        for ev in (self.ar_closed, self.mm_closed):
            try:
                ev.set()
            except Exception:
                pass
        for name in ('arena', 'mm'):
            try:
                s = getattr(self, name, None)
                if s is not None:
                    s.close()
            except Exception:
                pass

    def _start_stall_watchdog(self, stall_s=STALL_WATCH_S) -> None:
        """Last-resort bypass: force a reconnect if the play loop stops.

        Every other failure path in this class reports itself -- EOF sets
        ar_closed, a silent socket trips the reader's deadline, a bounded send
        raises.  The one case none of them can cover is a thread parked inside
        a blocking call: it cannot log, cannot set a flag, and cannot notice
        its own deadline.  From outside it looks exactly like a bot that
        "dropped off" while its process stays alive.

        This thread only watches a tick counter, so it cannot second-guess the
        pacer, the pin/stale watchdogs or the reconnect logic: it fires only
        when literally nothing has advanced for `stall_s`.  When it does, it
        closes the arena socket, which is what actually unblocks the parked
        call, and flags the session so the loop bails on its next tick.
        """
        if getattr(self, '_stall_thread', None) is not None \
                and self._stall_thread.is_alive():
            return

        def _watch():
            last = self._heartbeat
            last_change = time.time()
            while not self._stop.is_set():
                time.sleep(1.0)
                if self._heartbeat != last:
                    last = self._heartbeat
                    last_change = time.time()
                    continue
                if time.time() - last_change > stall_s:
                    last_change = time.time()
                    if self.ar_closed.is_set() and self.mm_closed.is_set():
                        continue
                    self.log(f'[watchdog] play loop made no progress for '
                             f'{stall_s:.0f}s — forcing a reconnect '
                             f'(bypass for a parked socket call)')
                    self._force_session_drop('play loop stalled')

        self._stall_thread = threading.Thread(target=_watch, daemon=True)
        self._stall_thread.start()

    def _arena_send(self, pkt: bytes) -> bool:
        """Send one frame on the arena socket with a hard upper bound.

        Never call `self.arena.sendall(...)` directly: the arena socket used to
        be left in blocking mode, and a peer that stops reading made sendall
        park forever -- with no log line, because callers log after the send.
        That is the "bot silently drops off" signature.
        """
        if self.arena is None:
            return False
        try:
            self.arena.sendall(frame(pkt))
            return True
        except socket.timeout:
            self._mark_arena_wedged(f'send timed out after '
                                    f'{ARENA_SOCK_TIMEOUT:.0f}s')
            return False
        except OSError as e:
            self._mark_arena_wedged(f'send failed ({type(e).__name__})')
            return False

    def _send_joy(self, vec, raw: bool = False):
        if self.arena is None:
            return
        # FOLLOW COME-TO-ME: use WORLD direction, skip HeadingMap.
        # Measured: +90deg / axis-swap calib made bots walk PAST the operator
        # ("mere samne se nikal gaye") while thinking they aimed at them.
        use_raw = (raw or (self.mode == 'follow'
                           and getattr(self, '_follow_raw_joy', True)))
        if use_raw:
            v = vec
        else:
            v = self.hmap.command(vec)
        n = math.hypot(*v)
        if n < 1e-9:
            v = (0.0, 0.0)
        else:
            v = (v[0] / n, v[1] / n)
        self.joystick = v
        self._arena_send(pkt_joy(v[0], v[1]))

    def _pump_arena(self):
        """Drain the arena queue, answering pings and reacting to death."""
        while True:
            try:
                body = self.q_ar.get_nowait()
            except queue.Empty:
                return
            if body is None:
                return
            m = decode_frame(body)
            if m.mt == 33 and self.world.me is None:
                red = self._node_redirect(m)
                if red:
                    self._pending_redirect = red
                    self.log(f'[arena] node says move to {red[0]}:{red[1]}')
            if m.mt == ARENA_REFUSAL_MT and self.world.me is None:
                # The node refused the join and is about to close.  Record it
                # so the connect loop can stop waiting and stop redialling a
                # token this node has already said no to.
                code = _arena_refusal_code(m)
                if self._arena_refused is None:
                    self._arena_refused = code if code is not None else -1
                    self.log(f'[arena] node REFUSED the join '
                             f'(mt=97 code={self._arena_refused}) — this '
                             f'bearer token is not usable on this node')
            if m.mt == 8 and self._want_play:
                self._want_play = False
                _pn = (self.nick or '').strip() or 'b'
                if self._arena_send(self.play_pkt(_pn)):
                    self.log(f'[death] mt=110 play nick={_pn!r}')
            was_dead = self.world.dead
            self.world.apply(m)
            # App respawn: ONE mt=12 on death edge (or mt=112).  Rate-limit
            # inside _ask_respawn stops the flood that was dropping the fleet.
            if m.mt == 112 or (self.world.dead and not was_dead):
                if not self._want_play:
                    self._ask_respawn()
            if m.mt == 70:
                nonce = one(fields(one(m.inner, 58) or b''), 2)
                if nonce is not None:
                    if self._arena_send(pkt_pong(nonce)):
                        self.log(f'  -> pong mt=104 nonce={nonce}')

    def _play(self, deadline, until=None) -> str:
        """Main play loop.  Returns 'done' | 'dead' | 'closed' | 'goal'.

        `until` is an optional predicate checked every tick; when it returns
        True the loop exits with 'goal' (used by leave-mode to farm up to a
        target mass before dumping it).
        """
        brain = self.brain
        last_decision = 0.0
        last_stats = 0.0
        last_seen_alive = time.time()
        ramp = 0.0
        aim = (0.0, 0.0)
        death_logged = False
        _live_chk = 0.0
        while time.time() < deadline and not self._stop.is_set():
            self._heartbeat += 1
            self._pump_arena()
            now = time.time()
            if now - _live_chk >= 0.5:
                _live_chk = now
                if self.tick_live_ctrl():
                    return 'closed'

            if self.arena is None or (
                    self.ar_closed.is_set() and not self._arena_is_inline()):
                self.log('[!] arena connection closed by the server')
                return 'closed'
            if self._arena_is_inline() and self.mm_closed.is_set():
                self.log('[!] matchmaker closed (inline arena)')
                return 'closed'

            if until is not None and self.world.me is not None and until():
                return 'goal'

            if self.world.me is None:
                # The server announces death explicitly (f48.f3 / f48.f4), so
                # report it the instant we learn of it rather than on timeout.
                if self.world.dead and not death_logged:
                    death_logged = True
                    kb = self.world.killed_by
                    self.log(f'[death] eaten by id={kb} '
                             f'(death #{self.world.deaths}, life #{self.world.lives + 1})')
                    self.event('death', killed_by=kb,
                               deaths=self.world.deaths)
                if now - last_seen_alive > 2.5:
                    return 'dead'
                self._send_joy((0.0, 0.0))
                time.sleep(self.tick)
                continue

            if death_logged:
                # the server re-spawned us under a new id: start the new life
                # with a clean heading so we don't keep fleeing the old threat
                death_logged = False
                ramp = 0.0
                aim = (0.0, 0.0)
                brain.reset()
                me = self.world.me
                self.log(f'[respawn] back in as id={me.id} mass={me.mass:.1f} '
                         f'(life #{self.world.lives + 1})')
                self.event('respawn', id=me.id, mass=round(me.mass, 1),
                           lives=self.world.lives)
            last_seen_alive = now

            if now - last_decision >= 0.1:
                last_decision = now
                # decide() returns the heading the joystick must use, with
                # wall escape already folded in.  Read the return value
                # rather than a private field so the two can never drift
                # apart again (that drift is what wedged us in a corner).
                aim = brain.decide(self.world, now)
                if aim and (aim[0] != 0.0 or aim[1] != 0.0) and self.world.me:
                    # Pass through zero-ingress obstacle skirting:
                    # Guarantees the bot glides safely around enemies while vacuuming token feeds/pellets
                    aim = self._skirt_enemies(self.world.me, aim[0], aim[1], tgt=None)

            ramp = min(1.0, ramp + self.tick * 4.0)
            h = aim if (aim[0] or aim[1]) else brain.heading
            self._send_joy((h[0] * ramp, h[1] * ramp))

            if now - last_stats >= 4.0:
                last_stats = now
                st = self.world.stats()
                st['mode'] = brain.mode
                st['danger'] = round(brain.danger, 2)
                st['wall'] = round(brain.wall_urgency, 2)
                st['stuck'] = bool(brain.stuck)
                st['stalled'] = bool(brain.stalled)
                st['heading'] = [round(brain.heading[0], 2), round(brain.heading[1], 2)]
                st['joystick'] = [round(self.joystick[0], 2), round(self.joystick[1], 2)]
                st['map'] = self.world.minimap()
                party_lbl = f"Party: {self.party_code or self.current_party_code}" if (self.party_code or self.current_party_code) else "Solo"
                enem = self.world.enemies()
                near_enem = f"{enem[0]['name']}(m:{enem[0]['mass']:.0f},d:{enem[0]['dist']:.0f},{enem[0]['threat']})" if enem else "None"
                virs = self.world.viruses()
                near_vir = f"d:{min(math.hypot(v.x - self.world.me.x, v.y - self.world.me.y) for v in virs):.0f}" if (virs and self.world.me) else "-"
                self.log(f"[LIVE] Region: {self.region:<14} | {party_lbl:<13} | "
                         f"Mass: {st['mass']:<5.1f} | Enemies: {len(enem):<2} [Near: {near_enem}] | "
                         f"Viruses: {len(virs):<2} ({near_vir}) | Pellets: {st['food']:<4} | Ate: {st['ate']:<3} | "
                         f"Score: {st['score']} | Pos: ({st['x']},{st['y']}) | Mode: {st['mode']}{' (STALLED)' if st.get('stalled') else ''}")
                if self.on_stats:
                    try:
                        self.on_stats(st)
                    except Exception:
                        pass
                self.event('stats', **st)
            time.sleep(self.tick)
        return 'done'

    def _ask_respawn(self) -> bool:
        """Send the app's death packet (mt=12) on the current arena socket.

        Hard rate-limit: spamming mt=12 on a living/stuck cell (old pin path)
        is what made the log fill with `[death] mt=12` and the fleet drop.
        """
        if self.arena is None:
            return False
        now = time.time()
        last = getattr(self, '_death_ask_at', 0.0) or 0.0
        if now - last < 0.85:
            return True  # already asked recently — do not flood
        if not self._arena_send(pkt_respawn()):
            return False
        self._want_play = True
        self._death_ask_at = now
        n = getattr(self, '_death_ask_n', 0) + 1
        self._death_ask_n = n
        # Log first ask + every 4th to keep the console readable.
        if n == 1 or n % 4 == 0:
            self.log(f'[death] mt=12 (ask #{n})')
        return True

    def _mash_play_after_death(self) -> None:
        """Burst/inline often skips mt=8 — mash mt=110 ourselves after mt=12."""
        if self.arena is None:
            return
        _pn = (self.nick or '').strip() or 'b'
        if self._arena_send(self.play_pkt(_pn)):
            self._want_play = False
            n = getattr(self, '_death_play_n', 0) + 1
            self._death_play_n = n
            if n == 1 or n % 4 == 0:
                self.log(f'[death] mt=110 play nick={_pn!r} (mash #{n})')

    def _respawn(self, deadline) -> bool:
        """Same socket as the app: mt=12, then mt=110 the instant mt=8 arrives.

        Capture session 23 (18 deaths): mt=110 follows mt=12 by ~0.58s, which
        is just how fast the server sends mt=8. Sending mt=110 before that
        answer is ignored, and the next life then waits a full extra retry.

        Burst/inline sometimes never sends mt=8 — after a few mt=12 asks we
        mash mt=110 ourselves so the bot does not bail → full re-login drop.
        """
        if self.arena is None:
            return False
        # Inline: ar_closed IS mm_closed — only abort if MM really died.
        if self._arena_is_inline():
            if self.mm is None or self.mm_closed.is_set():
                return False
        elif self.ar_closed.is_set():
            return False
        # Only respawn when we are actually dead.  Calling this on a living
        # pinned cell just floods mt=12 and freezes the bot.
        if not self.world.dead and self.world.me is not None:
            return True
        self.log('[death] respawn on this arena (mt=12 then mt=110)')
        old_id = self.world.self_id
        self.world.self_id = None
        self._death_ask_n = 0
        self._death_play_n = 0
        asks = 0
        if not self._want_play:
            if not self._ask_respawn():
                return False
        while time.time() < deadline:
            if self._arena_is_inline():
                if self.mm is None or self.mm_closed.is_set():
                    return False
            elif self.ar_closed.is_set():
                return False
            self._pump_arena()
            me = self.world.me
            if me is not None and not self.world.dead and (old_id is None or me.id != old_id):
                self.brain.reset()
                self._want_play = False
                self._death_ask_n = 0
                self._death_play_n = 0
                # Immediate initial motion impulse so the cell starts moving immediately
                ar = float(getattr(self.world, 'arena', 0.0) or 11180.0)
                cx, cy = ar * 0.5, ar * 0.5
                dx, dy = cx - me.x, cy - me.y
                dist = math.hypot(dx, dy) or 1.0
                self._send_joy((dx / dist, dy / dist), raw=True)
                self.log(f'[death] respawned as id={self.world.self_id} '
                         f'mass={me.mass:.0f} at ({me.x:.0f},{me.y:.0f}) -> moving')
                return True
            # After many asks same-socket is stuck — soft reconnect (no leave).
            if asks >= 16:
                self.log('[death] respawn no cell after 16 asks — soft reconnect '
                         '(non-drop, no leave)')
                return False
            gap = min(0.70 * (1.0 + 0.25 * asks), 2.2)
            elapsed = time.time() - (getattr(self, '_death_ask_at', 0.0) or 0.0)
            if elapsed >= gap:
                asks += 1
                if not self._ask_respawn():
                    return False
                # After 2 asks without mt=8→cell, mash play ourselves.
                if asks >= 2:
                    self._mash_play_after_death()
            time.sleep(0.02)
        return False

    # ------------------------------------------------------------ actions
    # Byte-exact copies of what the official client sends (see pkt_feed &
    # friends).  Direction of an eject/split is the joystick heading, so the
    # callers below always _send_joy() toward the target first.
    def _send_raw(self, pkt: bytes) -> bool:
        return self._arena_send(pkt)

    def do_feed(self, n: int = 1, gap: float = 0.04, heading: tuple[float, float] | None = None) -> None:
        for i in range(n):
            if heading is not None:
                self._send_joy(heading, raw=True)
            if self._send_raw(pkt_feed()):
                self.feeds += 1
            if i < n - 1 and gap > 0:
                time.sleep(gap)

    def do_split(self, count: int = 1, gap: float = 0.015, heading: tuple[float, float] | None = None) -> None:
        for i in range(count):
            if heading is not None:
                self._send_joy(heading, raw=True)
            if self._send_raw(pkt_split()):
                self.splits += 1
            if count > 1 and gap > 0:
                time.sleep(gap)

    def do_16_split(self, gap: float = 0.015, heading: tuple[float, float] | None = None) -> None:
        """Macro 16-split: fires 4 rapid splits (1->2->4->8->16) straight into operator."""
        self.do_split(count=4, gap=gap, heading=heading)

    def do_split_feed(self) -> None:
        """'Split + feed together': one split toward the heading, then two
        feeds right behind it -- the half we split off plus two pellets all
        land on the player we are facing."""
        self.do_split()
        time.sleep(0.04)
        self.do_feed(2, 0.05)

    def do_leave_game(self) -> None:
        """mt=80: quit the match to the menu, exactly like the app's leave.
        STRICT: only allowed when mode is 'leave' (feed-leave mode)."""
        if getattr(self, 'mode', '') != 'leave':
            return
        if self._send_raw(pkt_leave_game()):
            self.leaves += 1
            self.log('[leave] sent mt=80 (leave game)')
            self.event('leave_game', mass=round(self.world.total_mass, 1))

    def _wait_fleet_room_before_play(self):
        """One bot opens the Burst room; siblings wait for its arena_id pin.

        Without this, 10 bots mash Play 8s apart and land in 3–4 rooms —
        phone only sees the 3–4 that share the operator's map.
        """
        code = (self.code or '').strip().upper()
        if not code:
            return
        pin = _read_party_arena_pin()
        if pin and pin.get('arena_id'):
            self.log(f'[party] fleet room already pinned id={pin["arena_id"]}')
            return
        if _try_claim_room_opener(code):
            self.log('[party] I open the Burst room — siblings wait for my '
                     'arena_id pin')
            return
        self.log(f'[party] waiting up to {PARTY_ROOM_WAIT_S:.0f}s for fleet '
                 f'room pin (same map)...')
        t0 = time.time()
        while time.time() - t0 < PARTY_ROOM_WAIT_S:
            if self.mm_closed.is_set():
                return
            pin = _read_party_arena_pin()
            if pin and pin.get('arena_id'):
                self.log(f'[party] fleet room ready id={pin["arena_id"]} — '
                         f'Play now')
                return
            time.sleep(0.4)
        self.log('[party] pin wait timeout — opening room myself')

    def _bail_arena(self, reason: str) -> str:
        """Soft exit → 'closed' so forever opens a fresh node — NO mt=80.

        Separate EC2 arena: CLOSE that socket (half-open node = silent drop).

        INLINE (arena is MM): do NOT close / do NOT set mm_closed. Closing MM
        was WinError 10038 + Round finished — fleet looked like it "dropped".
        Detach arena and let run() remash mt=110 on the same session.
        """
        # Follow mode stays on arena socket for normal respawns,
        # BUT if trapped in the wrong arena shard, it must bail to migrate to target's room.
        if getattr(self, 'mode', '') == 'follow' and 'wrong arena' not in reason:
            self.log(reason + ' (ignored in follow mode — staying on arena socket)')
            try:
                self.world.dead = True
                self.world.self_id = None
                self._mash_play_after_death()
            except Exception:
                pass
            return 'dead'

        inline = self._arena_is_inline()
        self.log(reason + ' (non-drop, no leave)')
        try:
            self.world.dead = True
            self.world.self_id = None
        except Exception:
            pass
        if inline:
            self.arena = None
            self._inline_need_reenter = True
            return 'closed'
        try:
            self.ar_closed.set()
        except Exception:
            pass
        try:
            if self.arena is not None:
                self.arena.close()
        except Exception:
            pass
        self.arena = None
        return 'closed'

    def _fleet_known_uuids(self) -> set:
        """Every uuid we know belongs to one of our own bots.

        Two independent sources, because neither is complete on its own: the
        token pool (available immediately, but uses a different id space from
        the arena) and the live cells published by siblings this run.
        """
        return _fleet_uuids() | _fleet_live_uuids()

    def _record_own_uuid(self) -> None:
        """Publish our own arena uuid so siblings can tell us from the human."""
        me = self.world.me
        if me is None or not me.uuid:
            return
        if getattr(self, '_own_uuid_saved', None) == me.uuid:
            return
        try:
            try:
                d = json.load(open(FLEET_UUID_FILE, encoding='utf8'))
                if not isinstance(d, dict):
                    d = {}
            except Exception:
                d = {}
            d[me.uuid.lower()] = int(time.time())
            tmp = FLEET_UUID_FILE + '.tmp'
            with open(tmp, 'w', encoding='utf8') as fh:
                json.dump(d, fh, indent=1, sort_keys=True)
            os.replace(tmp, FLEET_UUID_FILE)
            self._own_uuid_saved = me.uuid
        except Exception:
            pass
        # Also stamp ourselves into the shared party roster (uuid + name),
        # so every sibling knows "ye isi party code ka bot hai".
        # NEVER publish under a name that already maps to the FOLLOW uid —
        # that was how "prince" stole the human's roster slot.
        try:
            code = (self.party_code or self.code or '').strip()
            if code and me.uuid:
                nm = me.name or f'bot_{(me.uuid or "")[:8]}'
                follow = (self.follow or '').lower()
                steal = False
                if follow:
                    for existing_nm, existing_uu in list(
                            (getattr(self, 'party_uuids', {}) or {}).items()):
                        if (existing_uu or '').lower() == follow \
                                and (existing_nm or '').lower() == (nm or '').lower():
                            steal = True
                            break
                if not steal:
                    if nm and nm not in (getattr(self, 'party_uuids', {}) or {}):
                        self.party_uuids[nm] = me.uuid.lower()
                    self._publish_party_now()
        except Exception:
            pass

    def _record_target_sighting(self, tgt) -> None:
        """Publish the target's position so the rest of the fleet converges.

        Throttled: one write every few seconds is plenty and keeps eight bots
        from thrashing the same file.
        """
        if tgt is None:
            return
        now = time.time()
        if now - getattr(self, '_sighting_t', 0.0) < SIGHTING_PUBLISH_S:
            return
        self._sighting_t = now
        try:
            # Lead: publish velocity so siblings chase WHERE you are going.
            vx = vy = 0.0
            prev = getattr(self, '_sighting_prev', None)
            if prev and now - float(prev[2]) < 1.5:
                dt = max(0.05, now - float(prev[2]))
                vx = (float(tgt.x) - float(prev[0])) / dt
                vy = (float(tgt.y) - float(prev[1])) / dt
            self._sighting_prev = (float(tgt.x), float(tgt.y), now)
            u_pub = str(tgt.uuid or getattr(self, 'follow', '') or '').lower().strip()
            nm_pub = str(tgt.name or getattr(self, 'follow_name', '') or '').lower().strip()
            tmp = f"{FLEET_TARGET_FILE}.tmp.{os.getpid()}"
            with open(tmp, 'w', encoding='utf8') as fh:
                json.dump({
                    'x': float(tgt.x), 'y': float(tgt.y), 't': now,
                    'vx': vx, 'vy': vy,
                    'uuid': u_pub,
                    'name': nm_pub,
                    'by': u_pub[:8],
                }, fh)
            os.replace(tmp, FLEET_TARGET_FILE)
        except Exception:
            pass

    def _friendly_uuids(self) -> set:
        """Arena uuids of everyone on our side (fleet + party code mates).

        Sources (merged):
          1. Live cells siblings published this run (fleet_uuids.json)
          2. Account uuids embedded in our token pool
          3. Local mt=98 party_uuids this bot saw
          4. Shared party_roster.json — so EVERY bot knows the full party
             even if its own mt=98 snapshot missed someone

        The follow target is excluded: we still want to dive into / feed them.
        """
        out = set(_fleet_live_uuids()) | set(_fleet_uuids())
        for u in getattr(self, 'party_uuids', {}).values():
            if u:
                out.add(u.lower())
        want = (self.party_code or self.code or '').strip().upper()
        if want:
            _code, _nmap, shared = _read_party_roster(want)
            out |= shared
        # Exclude the human we must follow / feed.
        for part in (self.follow or '').split(','):
            p = part.strip().lower()
            if p:
                out.discard(p)
                out.discard(p[:8])
                to_remove = [u for u in out if u.startswith(p[:8]) or p.startswith(u[:8])]
                for u in to_remove:
                    out.discard(u)
        out.discard(str(getattr(self, 'uid_target', '') or '').lower())
        # Also drop any resolved follow uuid from party map by name.
        try:
            raw_follows = [p.strip().lower() for p in (getattr(self, 'follow', None) or '').split(',') if p.strip()]
            for nm, uu in getattr(self, 'party_uuids', {}).items():
                if uu:
                    u_low = uu.lower()
                    n_low = (nm or '').lower()
                    if any(u_low == f or n_low == f or u_low.startswith(f[:8]) or f.startswith(u_low[:8]) for f in raw_follows):
                        out.discard(u_low)
        except Exception:
            pass
        return out

    def _party_mate_names(self) -> set[str]:
        """Lowercased display names of everyone in our party code."""
        names = set()
        for nm in getattr(self, 'party_members', []) or []:
            if nm:
                names.add(nm.lower())
        for nm in getattr(self, 'party_uuids', {}) or {}:
            if nm:
                names.add(nm.lower())
        want = (self.party_code or self.code or '').strip().upper()
        if want:
            names |= _party_roster_names(want)
        return names

    def _is_party_mate(self, ent) -> bool:
        """True if this cell belongs to someone in our party code.

        Matches by arena uuid OR display name.  The follow target returns
        False — we must still dive into them to deliver mass.
        """
        if ent is None or getattr(ent, 'is_self', False):
            return False
        eu = (getattr(ent, 'uuid', None) or '').lower().strip()
        en = (getattr(ent, 'name', None) or '').lower().strip()
        if not eu and hasattr(self.world, 'entity_history') and ent.id in self.world.entity_history:
            try:
                eu = (self.world.entity_history[ent.id][1] or '').lower().strip()
            except Exception:
                pass
        if not en and hasattr(self.world, 'entity_history') and ent.id in self.world.entity_history:
            try:
                en = (self.world.entity_history[ent.id][0] or '').lower().strip()
            except Exception:
                pass

        raw_follows = [p.strip().lower() for p in (self.follow or '').split(',') if p.strip()]
        for f in raw_follows:
            if eu and (eu == f or eu.startswith(f[:8]) or f.startswith(eu[:8])):
                return False
            if en and (en == f or en in f or f in en):
                return False
        # Resolved follow uuid from party map
        for nm, uu in getattr(self, 'party_uuids', {}).items():
            if uu:
                u_low = uu.lower()
                n_low = (nm or '').lower()
                if any(u_low == f or n_low == f for f in raw_follows):
                    if eu == u_low or en == n_low:
                        return False

        # Recognize fleet siblings by bot nickname or standard fleet alias
        bot_nick = (getattr(self, 'nick', None) or '').lower().strip()
        if en and bot_nick and (en == bot_nick or en.startswith(bot_nick)):
            return True
        if en in ('b', 'ggs'):
            return True

        if eu and eu in self._friendly_uuids():
            return True
        if en and en in self._party_mate_names():
            return True
        return False

    def _publish_party_now(self) -> None:
        """Write our view of the party into the shared roster file."""
        code = (self.party_code or self.code or '').strip()
        if not code:
            return
        _publish_party_roster(code, dict(getattr(self, 'party_uuids', {}) or {}),
                              list(getattr(self, 'party_members', []) or []))

    def _party_human_key(self) -> tuple[str, str]:
        """Follow key for the party member that is not one of our own bots.

        Returns ``(key, kind)`` where kind is ``'uuid'`` or ``'name'``, or
        ``('', '')`` when nothing can be resolved with confidence.

        DISABLED unless ``--auto-target`` is set.  Measured on eu-central-1:
        the arena DOES stamp every cell with its owner's account uuid (f6), and
        ``config.uid`` matched the operator's cell exactly (``prince[7603dde7]``)
        on the first run after the uid path was fixed.  So the configured uid is
        the reliable handle, and guessing a target is a pure downside: a wrong
        guess sends every follower to the wrong player, which is precisely the
        "no bot ever came to me, and the one that did had no idea it was me"
        bug.  Worse, the roster lagged behind fleet_uuids.json, so the
        "not one of ours" test picked OUR OWN BOT as the human.

        When enabled, two signals are tried:
          1. a member whose roster entry carried NO readable uuid -- registered
             accounts do not use the guest layout (``f1{f4=uuid}``);
          2. a member whose parsed uuid is not in our fleet registry, but ONLY
             once the registry is complete, otherwise "not ours" just means
             "not published yet".
        """
        if not getattr(self, 'auto_target', False):
            return '', ''

        ours = self._fleet_known_uuids()
        me_uu = ''
        me_nm = ''
        if self.world.me is not None:
            me_uu = (self.world.me.uuid or '').lower()
            me_nm = self.world.me.name or ''

        unknown = [nm for nm in getattr(self, 'current_party_members', [])
                   if nm not in self.party_uuids and nm != me_nm]
        if len(unknown) == 1:
            return unknown[0], 'name'

        # Signal 2 needs a COMPLETE registry.  BOT_COUNT is set by the
        # launcher.  Only the LIVE registry counts: the uuid embedded in a g2gD
        # token lives in a different id space from the arena, so the 50-uuid
        # token pool cannot tell us that every sibling has been accounted for.
        # Without this check a sibling that has not published yet looks exactly
        # like a stranger -- which is how the fleet ended up chasing itself.
        try:
            want = int(os.environ.get('BOT_COUNT', '0') or 0)
        except ValueError:
            want = 0
        if want < 1 or len(_fleet_live_uuids()) < want:
            return '', ''

        cands = []
        for nm, uu in self.party_uuids.items():
            ul = (uu or '').lower()
            if not ul or ul == me_uu or ul in ours:
                continue
            cands.append((nm, uu))
        if len(cands) == 1:
            return cands[0][1], 'uuid'
        return '', ''

    def _party_human_uuid(self) -> str:
        """The resolved follow key when it is a uuid (else empty)."""
        key, kind = self._party_human_key()
        return key if kind == 'uuid' else ''

    def _party_roster_report(self) -> str:
        """One-line roster: which members are ours and which is the human."""
        ours = self._fleet_known_uuids()
        want = (self.follow or '').lower()
        key, kind = self._party_human_key()
        bits = []
        for nm, uu in self.party_uuids.items():
            ul = (uu or '').lower()
            if ul in ours:
                tag = 'OURS'
            elif want and (ul == want or ul.startswith(want[:8])):
                tag = 'TARGET'
            elif kind == 'uuid' and uu == key:
                tag = 'HUMAN'
            else:
                tag = 'HUMAN?'
            bits.append(f'{nm}={uu[:8]}[{tag}]')
        # Members with no readable uuid never appear above; without them the
        # roster looks like "all ours" while the human is standing right there.
        for nm in self.current_party_members:
            if nm in self.party_uuids:
                continue
            tag = 'HUMAN' if (kind == 'name' and nm == key) else 'HUMAN?'
            bits.append(f'{nm}=<no-uuid>[{tag}]')
        return ', '.join(bits) if bits else '(roster empty)'

    def _follow_aliases(self, key: str) -> set[str]:
        """All keys that identify the follow target: uuid + party display names.

        Roster example: uid 7603dde7 maps to name 'Chua_1019'.  Without the
        name alias, a bot that sees the cell tagged only by name (or whose
        uuid field is briefly missing) reports NOT VISIBLE forever and never
        walks in.
        """
        out: set[str] = set()
        if not key:
            return out
        keys = [k.strip().lower() for k in key.split(',') if k.strip()]
        GENERIC_NAMES = {'?', '', 'none', 'null', 'guest', 'test', 'b', 'bot'}
        for kl in keys:
            out.add(kl)
            if len(kl) >= 8:
                out.add(kl[:8])
            # Local party map name -> uuid
            for nm, uu in (getattr(self, 'party_uuids', {}) or {}).items():
                u = (uu or '').lower()
                n = (nm or '').lower().strip()
                if not u or not n or n in GENERIC_NAMES or len(n.strip('?._- ')) == 0:
                    continue
                if u == kl or (len(kl) >= 8 and u.startswith(kl[:8])) or kl.startswith(u[:8]):
                    out.add(n)
            # Shared party roster
            want = (self.party_code or self.code or '').strip().upper()
            if want:
                _c, nmap, _u = _read_party_roster(want)
                for nm, uu in nmap.items():
                    u = (uu or '').lower()
                    n = (nm or '').lower().strip()
                    if not u or not n or n in GENERIC_NAMES or len(n.strip('?._- ')) == 0:
                        continue
                    if (u == kl or (len(kl) >= 8 and u.startswith(kl[:8]))
                              or kl.startswith(u[:8])):
                        out.add(n)
        # Config follow-name (operator in-game nick)
        fn = (getattr(self, 'follow_name', None) or '').lower().strip()
        if fn and fn not in GENERIC_NAMES and len(fn.strip('?._- ')) > 0:
            out.add(fn)
        # Live nick we already saw for this uid (e.g. Prince)
        seen = (getattr(self, '_follow_seen_name', '') or '').lower().strip()
        if seen and seen not in GENERIC_NAMES and len(seen.strip('?._- ')) > 0:
            out.add(seen)
        return out

    @staticmethod
    def _uid_hit(want: str, uu: str) -> bool:
        """agar-mobile find_target: exact OR prefix (truncated uid OK)."""
        if not want or not uu:
            return False
        w, u = want.lower().strip(), uu.lower().strip()
        if not w or not u:
            return False
        if w == u:
            return True
        # Partial / truncated uid (old mobile bot behaviour)
        return u.startswith(w) or w.startswith(u)

    @staticmethod
    def _nick_norm(s: str) -> str:
        """Lowercase + strip spaces/underscores for soft nick match."""
        if not s:
            return ''
        return ''.join(ch for ch in s.lower() if ch.isalnum())

    def find_player(self, key: str) -> Entity | None:
        """Largest visible cell of the follow target — UID-first like agar-mobile.

        Old ``agar-mobile-bots`` / azhar AI matched ONLY:
          1) cell.uid exact
          2) owner_id / cell_id string
          3) uid prefix (truncated uuid)
        Name was NOT used to pick a feed target (avoids Guest_ nick collisions).
        We keep name as a LAST resort only when the cell has no uuid at all.
        """
        if not key:
            return None
        # Support comma-separated UIDs: "ddad693e-...,2259f871-..."
        raw_keys = [k.strip() for k in (key or '').split(',') if k.strip()]
        if not raw_keys:
            raw_keys = [key] if key else []
        uid_aliases: list[str] = []
        name_aliases: set[str] = set()
        for rk in raw_keys:
            rk = self.party_uuids.get(rk, rk)
            want = (rk or '').lower().strip()
            aliases = self._follow_aliases(rk)
            if want:
                aliases.add(want)
            for a in aliases:
                if not a:
                    continue
                if '-' in a or len(a) >= 8:
                    if a not in uid_aliases:
                        uid_aliases.append(a)
                elif not a[0:1].isdigit():
                    name_aliases.add(a)
        fn = (getattr(self, 'follow_name', None) or '').lower().strip()
        if fn:
            name_aliases.add(fn)
        fn_norm = self._nick_norm(fn)
        name_norms = {self._nick_norm(a) for a in name_aliases if a}
        if fn_norm:
            name_norms.add(fn_norm)
        friendly = self._friendly_uuids()
        best = None
        best_rank = 99  # 0=exact uid, 1=prefix uid, 2=cell/name, 3=name-only
        GENERIC_NAMES = {'?', '', 'none', 'null', 'guest', 'test', 'b', 'bot'}
        for e in self.world.entities.values():
            if e.kind != K_CELL or e.is_self:
                continue
            uu = (e.uuid or '').lower().strip()
            if not uu and hasattr(self.world, 'entity_history') and e.id in self.world.entity_history:
                try:
                    uu = (self.world.entity_history[e.id][1] or '').lower().strip()
                except Exception:
                    pass
            nm = (e.name or '').lower().strip()
            if not nm and hasattr(self.world, 'entity_history') and e.id in self.world.entity_history:
                try:
                    nm = (self.world.entity_history[e.id][0] or '').lower().strip()
                except Exception:
                    pass
            nm_n = self._nick_norm(nm)
            eid = str(getattr(e, 'id', '') or '')
            rank = None
            if uu:
                for a in uid_aliases:
                    if uu == a:
                        rank = 0
                        break
                    if self._uid_hit(a, uu):
                        rank = 1
                        break
                # CRITICAL SECURITY: If target UID was specified, and this cell has a UUID that doesn't match,
                # it is 100% an ENEMY player! NEVER treat as operator!
                if rank is None and uid_aliases:
                    continue

            if rank is None and eid:
                for a in uid_aliases:
                    if eid == a or (a.isdigit() and eid == a):
                        rank = 2
                        break

            # Name match — ONLY as a last resort if cell has NO UUID at all, and name is not generic
            if rank is None and not uu and nm and nm not in GENERIC_NAMES and len(nm.strip('?._- ')) > 0:
                if (nm in name_aliases or nm_n in name_norms):
                    if uu and uu in friendly:
                        pass  # fleet sibling nick collision
                    else:
                        rank = 2 if (fn and (nm == fn or nm_n == fn_norm)) else 3

            if rank is None:
                continue
            # Never lock onto a fleet sibling unless uuid IS the follow target
            if uu and uu in friendly:
                if not any(self._uid_hit(a, uu) for a in uid_aliases):
                    continue
            if best is None or rank < best_rank:
                best = e
                best_rank = rank
            elif rank == best_rank:
                # User rule: ALWAYS target the LARGEST piece of the operator!
                # Never feed or split into a small piece just because it is closer.
                if e.mass > best.mass:
                    best = e
                elif abs(e.mass - best.mass) < 1.0:
                    me = self.world.me
                    if me is not None:
                        d_new = math.hypot(e.x - me.x, e.y - me.y)
                        d_best = math.hypot(best.x - me.x, best.y - me.y)
                        if d_new < d_best:
                            best = e
        return best

    def _scan_follow_target(self, key: str):
        """Every-tick scan: lock follow cell OR publish if we see their name/uuid.

        Also returns the best candidate even when mass is small — used so a
        freshly-seen operator is never ignored while we farm.
        """
        return self.find_player(key)

    def _find_nearby_bigger_friendly(self, me) -> Entity | None:
        """When the human operator is absent / not on screen:
        Smaller bots find nearby larger friendly bots to feed and split into,
        allowing the bots to cluster and grow into giant super-bots!
        "jo bada hoga usko mass denge sirf 1 ko nahi jo bhi aas pass bada mila use"
        """
        if me is None:
            return None
        my_m = float(getattr(me, 'mass', 0.0) or 0.0)
        bot_x, bot_y = getattr(me, 'x', 0.0), getattr(me, 'y', 0.0)

        # Exclude human operator from being treated as a bot sibling
        tu = (getattr(self, 'follow', '') or '').lower()
        tn = (getattr(self, 'follow_name', '') or '').lower()
        bot_nick = (getattr(self, 'bot_name', '') or 'pnc bots').strip().lower()

        candidates = []
        for e in self.world.entities.values():
            if getattr(e, 'kind', 0) != K_CELL or getattr(e, 'is_self', False):
                continue
            eu = (getattr(e, 'uuid', '') or '').lower()
            en = (getattr(e, 'name', '') or '').strip().lower()

            # Ignore the human operator
            if tu and eu and (eu == tu or eu.startswith(tu[:8]) or tu.startswith(eu[:8])):
                continue
            if tn and en and en == tn:
                continue

            # Check if this cell is a friendly fleet bot
            is_friendly = False
            if hasattr(self, '_is_party_mate') and self._is_party_mate(e):
                is_friendly = True
            elif eu and hasattr(self, '_friendly_uuids') and eu in self._friendly_uuids():
                is_friendly = True
            elif hasattr(self, '_party_mate_names') and en and en in self._party_mate_names():
                is_friendly = True
            elif bot_nick and en and (en == bot_nick or bot_nick in en or en in bot_nick):
                is_friendly = True

            if not is_friendly:
                continue

            # Must be larger than us so it can safely absorb our mass!
            e_m = float(getattr(e, 'mass', 0.0) or 0.0)
            if e_m >= max(my_m * 1.15, 30.0):
                d = math.hypot(e.x - bot_x, e.y - bot_y)
                # Within reasonable vicinity ("aas pass")
                if d <= 3200.0:
                    candidates.append((e, d))

        if not candidates:
            return None

        # Prioritize the largest nearby friendly bot; tie-break with distance
        candidates.sort(key=lambda item: (-getattr(item[0], 'mass', 0.0), item[1]))
        return candidates[0][0]

    def _dump_mass(self, timeout: float = 20.0, toward: str | None = None) -> int:
        """Eject everything we can (down to the server's eject floor)."""
        t0 = time.time()
        n0 = self.feeds
        floor = max(18.0, self.feed_keep if self.mode == 'follow' else 18.0)
        heading = (1.0, 0.0)
        while time.time() - t0 < timeout and not self._stop.is_set():
            self._pump_arena()
            me = self.world.me
            if me is None or self.ar_closed.is_set():
                break
            if self.world.total_mass <= floor:
                break
            tgt = self.find_player(toward) if toward else None
            if tgt is not None:
                dx, dy = tgt.x - me.x, tgt.y - me.y
                nrm = math.hypot(dx, dy)
                if nrm > 1e-6:
                    heading = (dx / nrm, dy / nrm)
            # hold position (tiny joystick) so the cell just faces the heading
            self._send_joy((heading[0] * 0.15, heading[1] * 0.15))
            self.do_feed(2)
            time.sleep(0.02)
        n = self.feeds - n0
        self.log(f'[feed] dumped {n} ejects -> mass {self.world.total_mass:.1f}')
        return n

    def _line_blockers(self, me, tx, ty, target_uuid, pad=90.0):
        """Enemy cells on the segment me -> target (would steal feed/split)."""
        mx, my = me.x, me.y
        dx, dy = tx - mx, ty - my
        length = math.hypot(dx, dy)
        if length < 1e-6:
            return []
        ux, uy = dx / length, dy / length
        hits = []
        tuid = (target_uuid or '').lower()
        for e in self.world.entities.values():
            if e.is_self:
                continue
            if e.kind == K_VIRUS:
                vx, vy = e.x - mx, e.y - my
                t = vx * ux + vy * uy
                if -e.r < t < length + e.r:
                    px, py = mx + ux * t, my + uy * t
                    if math.hypot(e.x - px, e.y - py) < e.r + me.r + 40:
                        hits.append(e)
                continue
            if e.kind != K_CELL:
                continue
            if tuid and (e.uuid or '').lower() == tuid:
                continue
            vx, vy = e.x - mx, e.y - my
            t = vx * ux + vy * uy
            if t < -e.r or t > length + e.r:
                continue
            px, py = mx + ux * t, my + uy * t
            if math.hypot(e.x - px, e.y - py) < e.r + me.r + pad:
                hits.append(e)
        return hits

    def _train(self, key: str, default: float) -> float:
        """Live-trainable follow knob (bot/train_follow.txt, hot-reload ~1.5s)."""
        if _follow_train is None:
            return default
        try:
            return float(_follow_train.get(key, default))
        except Exception:
            return default

    def _resolve_clearance(self, dist_to_tgt=999999.0):
        """Resolves (skin_margin_base, lip_margin, split_cushion, angle_pad) based on enemy_clearance level."""
        raw = getattr(self, 'enemy_clearance', '1')
        train_val = self._train('enemy_clearance', -1.0)
        if train_val > 0:
            raw = str(train_val)
        raw_s = str(raw).strip().lower()

        is_near = dist_to_tgt <= 800.0

        # Level 1: Ultra-Tight / Chipak Ke Nikalna (Max closeness)
        # Margin: 15u, Lip: 6u, Split: 0u (if tgt near) / 40u, AngPad: 0.02 rad (~1.1 deg)
        if raw_s in ('1', 'chipak', 'razor', 'ultra', 'tight', 'extreme', 'max'):
            return 15.0, 6.0, (0.0 if is_near else 40.0), 0.02

        # Level 2: Close / Aggressive
        # Margin: 25u, Lip: 10u, Split: 0u (if tgt near) / 60u, AngPad: 0.04 rad (~2.3 deg)
        elif raw_s in ('2', 'close', 'aggressive', 'near'):
            return 25.0, 10.0, (0.0 if is_near else 60.0), 0.04

        # Level 3: Balanced / Normal
        # Margin: 40u, Lip: 16u, Split: 40u (if tgt near) / 100u, AngPad: 0.08 rad (~4.5 deg)
        elif raw_s in ('3', 'normal', 'balanced', 'medium', 'mid'):
            return 40.0, 16.0, (40.0 if is_near else 100.0), 0.08

        # Level 4: Safe
        # Margin: 65u, Lip: 25u, Split: 100u (if tgt near) / 150u, AngPad: 0.12 rad (~6.9 deg)
        elif raw_s in ('4', 'safe', 'wide'):
            return 65.0, 25.0, (100.0 if is_near else 150.0), 0.12

        # Level 5: Ultra Safe / Wide
        # Margin: 100u, Lip: 35u, Split: 150u (if tgt near) / 200u, AngPad: 0.18 rad (~10.3 deg)
        elif raw_s in ('5', 'ultra-safe', 'paranoid', 'max-safe'):
            return 100.0, 35.0, (150.0 if is_near else 200.0), 0.18

        else:
            try:
                val = float(raw_s)
                if val == 1.0:
                    return 15.0, 6.0, (0.0 if is_near else 40.0), 0.02
                elif val == 2.0:
                    return 25.0, 10.0, (0.0 if is_near else 60.0), 0.04
                elif val == 3.0:
                    return 40.0, 16.0, (40.0 if is_near else 100.0), 0.08
                elif val == 4.0:
                    return 65.0, 25.0, (100.0 if is_near else 150.0), 0.12
                elif val == 5.0:
                    return 100.0, 35.0, (150.0 if is_near else 200.0), 0.18
                else:
                    # Custom clearance margin in game units (e.g. 18.0)
                    margin = max(8.0, val)
                    lip = max(4.0, min(margin * 0.42, 30.0))
                    split_buf = 0.0 if is_near else max(20.0, margin)
                    pad = max(0.01, min(0.15, margin * 0.002))
                    return margin, lip, split_buf, pad
            except Exception:
                return 15.0, 6.0, (0.0 if is_near else 40.0), 0.02

    def _skirt_enemies(self, me, ux, uy, tgt=None):
        """Pass safely around enemies with wide clearance without getting eaten.

        Calculates skin-tight tangent clearance past enemy perimeter so the bot
        skims along their boundary without ever entering inside the enemy mouth.
        Never dodges the operator or party siblings.
        """
        if me is None or self.world is None:
            return ux, uy

        dist_to_tgt = math.hypot(tgt.x - me.x, tgt.y - me.y) if tgt is not None else 999999.0
        skin_margin_base, lip_margin, split_cushion, angle_pad = self._resolve_clearance(dist_to_tgt)

        target_uuids = set(self._follow_aliases(self.follow or ''))
        target_name = (getattr(self, 'follow_name', '') or '').lower().strip()
        if target_name in {'?', '', 'none', 'null', 'guest', 'test', 'b', 'bot'} or len(target_name.strip('?._- ')) == 0:
            target_name = ''

        bot_nick = (getattr(self, 'nick', '') or '').lower().strip()

        obstacles = []
        for e in self.world.entities.values():
            if e.is_self or e.kind not in (K_CELL, K_VIRUS):
                continue
            if e.kind == K_CELL:
                eu = (e.uuid or '').lower().strip()
                en = (e.name or '').lower().strip()
                if not eu and hasattr(self.world, 'entity_history') and e.id in self.world.entity_history:
                    try:
                        eu = (self.world.entity_history[e.id][1] or '').lower().strip()
                    except Exception:
                        pass
                if not en and hasattr(self.world, 'entity_history') and e.id in self.world.entity_history:
                    try:
                        en = (self.world.entity_history[e.id][0] or '').lower().strip()
                    except Exception:
                        pass

                # Target operator is our destination, never dodge operator
                if tgt is not None and e.id == tgt.id:
                    continue
                if eu and (eu in target_uuids or self._uid_hit(self.follow, eu)):
                    continue
                if target_name and en == target_name:
                    continue

                # Operator split cells: any nearby cell sharing operator color or within cluster
                if tgt is not None:
                    if getattr(tgt, 'color', None) is not None and getattr(e, 'color', None) == tgt.color:
                        if math.hypot(e.x - tgt.x, e.y - tgt.y) < max(900.0, (tgt.r + e.r) * 2.5):
                            continue

                # Party mates and fleet siblings: NEVER dodge our own fleet siblings!
                if self._is_party_mate(e):
                    continue
                if en and bot_nick and (en == bot_nick or en.startswith(bot_nick)):
                    continue
                if en in ('b', 'ggs'):
                    continue

                # Genuine hostile threat: cell can eat us (mass >= me.mass * 1.12)
                if e.mass < me.mass * 1.12:
                    continue
            elif e.kind == K_VIRUS:
                if me.mass < VIRUS_SPLIT_MASS:
                    continue
                # If no dangerous enemy is nearby, we WANT to eat the virus for mass!
                has_predators = any(
                    oe.kind == K_CELL and oe.id != me.id and not getattr(oe, 'is_self', False)
                    and oe.mass >= me.mass * 0.85
                    and math.hypot(oe.x - me.x, oe.y - me.y) <= 1200.0
                    for oe in self.world.entities.values()
                )
                if not has_predators:
                    continue

            vx = e.x - me.x
            vy = e.y - me.y
            d = math.hypot(vx, vy)
            kill_r = e.r + me.r

            # If this obstacle is further than the user, and user is close, user takes priority
            if tgt is not None and dist_to_tgt <= 350.0 and d > dist_to_tgt + 30.0:
                continue

            # Lookahead radius: account for enemy radius and approach speed
            can_split = (e.kind == K_CELL and e.mass >= me.mass * 2.2 and e.mass > 200.0)
            split_buffer = split_cushion if can_split else 0.0

            # Skin-tight safety margin:
            # Hugs close to enemy contour; scaled gently by enemy size
            skin_margin = skin_margin_base + min(skin_margin_base * 0.5, e.r * 0.08) + split_buffer
            safe_r = kill_r + skin_margin

            scan_r = safe_r + (750.0 if can_split else 450.0)
            if d < scan_r:
                obstacles.append((d, kill_r, safe_r, vx, vy, e))

        if not obstacles:
            return ux, uy

        # Sort obstacles by proximity: closest threat takes priority
        obstacles.sort(key=lambda item: item[0])

        # If user is right here (<= 250 units) and the closest threat is outside our safe perimeter:
        if tgt is not None and dist_to_tgt <= 250.0 and obstacles[0][0] > obstacles[0][2]:
            return ux, uy

        cur_x, cur_y = ux, uy

        # --- TIGHT BOUNDARY SKIMMING & ZERO-INGRESS CONSTRAINT ---
        for d, kill_r, safe_r, vx, vy, e in obstacles:
            if d < 1e-4:
                continue

            rx = vx / d  # Unit vector towards enemy center
            ry = vy / d

            # 1. HARD ZERO-INGRESS BOUNDARY (When inside or near safe perimeter):
            # If d <= safe_r, the bot MUST NOT have any velocity pointing towards the enemy center!
            if d <= safe_r:
                # Two tangent directions perpendicular to the radial vector
                t1_x, t1_y = -ry, rx   # Left tangent
                t2_x, t2_y = ry, -rx   # Right tangent

                # Pick the tangent that aligns with forward heading and player while avoiding other nearby threats
                best_t = (t1_x, t1_y)
                best_t_score = -1e9
                for cand_tx, cand_ty in ((t1_x, t1_y), (t2_x, t2_y)):
                    score = cand_tx * cur_x + cand_ty * cur_y
                    if tgt is not None and dist_to_tgt > 1e-4:
                        # Extra pull towards target operator to shave through the corridor
                        to_tgt_x = (tgt.x - me.x) / dist_to_tgt
                        to_tgt_y = (tgt.y - me.y) / dist_to_tgt
                        score += 1.8 * (cand_tx * to_tgt_x + cand_ty * to_tgt_y)
                    # Check if this candidate tangent steers directly towards another threat
                    for d2, kr2, sr2, vx2, vy2, e2 in obstacles[1:4]:
                        rx2, ry2 = vx2 / max(d2, 1e-4), vy2 / max(d2, 1e-4)
                        dot_e2 = cand_tx * rx2 + cand_ty * ry2
                        if dot_e2 > 0.2:
                            score -= 2.5 * dot_e2
                    if score > best_t_score:
                        best_t_score = score
                        best_t = (cand_tx, cand_ty)
                tangent_x, tangent_y = best_t
                # Radial push strictly OUTWARD away from enemy center (-rx, -ry)
                outward_x = -rx
                outward_y = -ry

                # EMERGENCY HARD BORDER REPULSION: if touching the lip (d < kill_r + lip_margin),
                # 100% PURE OUTWARD FORCE! Never allow any tangent or forward push into mouth!
                if d < kill_r + lip_margin:
                    cur_x, cur_y = outward_x, outward_y
                    break

                penetration = (safe_r - d) / max(1.0, safe_r - kill_r)
                penetration = max(0.0, min(1.0, penetration))

                # Normal push outward (increases as we approach lip)
                n_push = max(0.18, penetration * 0.95)
                t_pull = math.sqrt(max(0.0, 1.0 - n_push * n_push))

                deflect_x = outward_x * n_push + tangent_x * t_pull
                deflect_y = outward_y * n_push + tangent_y * t_pull
                dn = math.hypot(deflect_x, deflect_y) or 1.0
                cur_x, cur_y = deflect_x / dn, deflect_y / dn
                break

            # 2. ANTICIPATORY TANGENT DEFLECTION (When approaching enemy from outside safe_r):
            along = vx * cur_x + vy * cur_y
            perp = vx * (-cur_y) + vy * cur_x

            # Enemy is behind us — no collision ahead
            if along < 0.0:
                continue

            # Heading passes within enemy's safe circle -> deflect along tangent
            if abs(perp) < safe_r:
                sign = -1.0 if perp > 0.0 else 1.0
                sin_theta = min(0.96, safe_r / d)
                theta = math.asin(sin_theta) + angle_pad
                e_ang = math.atan2(vy, vx)
                tangent_ang = e_ang + sign * theta
                cur_x = math.cos(tangent_ang)
                cur_y = math.sin(tangent_ang)
                break

        return cur_x, cur_y

    def _avoid_heading(self, me, ux, uy, tx, ty, target_uuid,
                       commit: bool = False, threats_only: bool = True):

        """Path bend around REAL threats only.

        Root cause of the "bots dance left-right in front of me" bug: every
        fleet sibling counted as a blocker, so 10 bots converging on the
        operator sidestepped each other forever.  Rules now:

          * ``commit=True`` (close to operator): arrow locked straight —
            no sidestep at all.  Walking into the operator IS the goal.
          * Friendly / fleet uuids: NEVER blockers.
          * ``threats_only``: only cells that can eat us + dangerous viruses.
        """
        if commit:
            return ux, uy, False, 0

        tuid = (target_uuid or '').lower()
        lx, ly = -uy, ux
        path = math.hypot(tx - me.x, ty - me.y)
        look_min = self._train('avoid_look_min', 80.0)
        look_cap = self._train('avoid_look_cap', 520.0)
        look = min(max(path, look_min), max(look_cap, me.r * 10.0))
        side_w = self._train('avoid_side', 0.55)
        fwd_w = self._train('avoid_forward', 0.75)
        push_w = self._train('avoid_push', 0.55)
        sticky_s = max(1.0, self._train('avoid_sticky_s', 0.70))
        push = 0.0
        hard = None
        blockers = 0
        for e in self.world.entities.values():
            if e.is_self or e.kind not in (K_CELL, K_VIRUS):
                continue
            eu = (e.uuid or '').lower()
            if e.kind == K_CELL and tuid and eu == tuid:
                continue
            # Party-code mates (uuid OR name): never bend around them.
            # Fleet stacking on the operator was the L/R dance.
            if e.kind == K_CELL and self._is_party_mate(e):
                continue
            if threats_only and e.kind == K_CELL:
                # Only dodge something that can actually eat us.
                if e.mass < me.mass * EAT_RATIO:
                    continue
            if e.kind == K_VIRUS and me.mass < VIRUS_SPLIT_MASS:
                # Small cells pass viruses safely — don't waste a sidestep.
                continue
            vx, vy = e.x - me.x, e.y - me.y
            dist = math.hypot(vx, vy)
            if dist < 1.0:
                continue
            along = vx * ux + vy * uy
            side = vx * lx + vy * ly
            reach = e.r + me.r + 40.0
            if along < -reach * 0.35 or along > look + e.r:
                continue
            if abs(side) > reach:
                continue
            blockers += 1
            sticky = getattr(self, '_avoid_side', 0.0) or 0.0
            sticky_until = getattr(self, '_avoid_side_until', 0.0) or 0.0
            prefer = sticky if time.time() < sticky_until and sticky != 0.0 else 0.0
            if dist < e.r + me.r + 70.0:
                if prefer != 0.0:
                    sign = prefer
                else:
                    sign = -1.0 if side >= 0.0 else 1.0
                    if abs(side) < 14.0:
                        sign = -1.0
                if hard is None or dist < hard[0]:
                    hard = (dist, sign)
            else:
                gap = reach - abs(side)
                weight = max(0.35, gap / max(reach, 1.0))
                if e.kind == K_VIRUS or e.mass >= me.mass * 0.9:
                    weight *= 1.35
                if prefer != 0.0:
                    push += prefer * weight
                else:
                    push += -math.copysign(weight, side if abs(side) > 6.0 else 1.0)
        if hard is not None:
            sign = hard[1]
            self._avoid_side = sign
            self._avoid_side_until = time.time() + sticky_s
            hx = lx * sign * side_w + ux * fwd_w
            hy = ly * sign * side_w + uy * fwd_w
            n = math.hypot(hx, hy) or 1.0
            return hx / n, hy / n, True, blockers
        if abs(push) < 0.2:
            return ux, uy, False, blockers
        push = max(-1.4, min(1.4, push))
        self._avoid_side = 1.0 if push > 0 else -1.0
        self._avoid_side_until = time.time() + sticky_s
        hx, hy = ux + lx * push * push_w, uy + ly * push * push_w
        n = math.hypot(hx, hy) or 1.0
        return hx / n, hy / n, True, blockers

    def _surrounded_heading(self, me, ux, uy, target_uuid):
        """When REAL enemies ring us, probe for a gap toward the player.

        Fleet siblings are ignored — they are not threats.
        """
        tuid = (target_uuid or '').lower()
        probe_reach = self._train('probe_reach', 220.0)
        probe_fwd = self._train('probe_forward', 2.5)
        sticky_s = max(1.0, self._train('avoid_sticky_s', 0.70))
        threats = []
        for e in self.world.entities.values():
            if e.is_self or e.kind not in (K_CELL, K_VIRUS):
                continue
            eu = (e.uuid or '').lower()
            if e.kind == K_CELL and tuid and eu == tuid:
                continue
            if e.kind == K_CELL and self._is_party_mate(e):
                continue
            if e.kind == K_CELL and e.mass < me.mass * EAT_RATIO:
                continue
            if e.kind == K_VIRUS and me.mass < VIRUS_SPLIT_MASS:
                continue
            d = math.hypot(e.x - me.x, e.y - me.y)
            if d < max(380.0, me.r * 8.0 + e.r):
                threats.append(e)
        if len(threats) < 2:
            return None
        best = None
        best_s = -1e18
        base = math.atan2(uy, ux)
        for i in range(12):
            a = base + (i / 11.0 - 0.5) * (200.0 * math.pi / 180.0)
            hx, hy = math.cos(a), math.sin(a)
            s = probe_fwd * (hx * ux + hy * uy)
            clear = True
            for e in threats:
                qx = me.x + hx * probe_reach
                qy = me.y + hy * probe_reach
                gap = math.hypot(e.x - qx, e.y - qy) - e.r - me.r
                if gap < 20.0:
                    clear = False
                    s -= 80.0
                else:
                    s += min(gap, 200.0) * 0.15
            if clear and s > best_s:
                best_s = s
                best = (hx, hy)
            elif not clear and best is None and s > best_s:
                best_s = s
                best = (hx, hy)
        if best is None:
            side = getattr(self, '_avoid_side', 0.0) or -1.0
            self._avoid_side = side
            self._avoid_side_until = time.time() + sticky_s
            lx, ly = -uy, ux
            hx = lx * side * 0.9 + ux * 0.15
            hy = ly * side * 0.9 + uy * 0.15
            n = math.hypot(hx, hy) or 1.0
            return hx / n, hy / n
        return best

    def _approach_offset(self, ux, uy):
        """Fan fleet approaches so bots don't stack on one ray.

        Only used FAR from the operator.  Close-range COMMIT ignores this
        and drives straight into their centre.
        """
        try:
            slot = getattr(self, 'bot_index', None)
            if slot is None:
                slot = int(os.environ.get('BOT_INDEX', '0') or 0)
            count = getattr(self, 'bot_count', None)
            if count is None:
                count = max(1, int(os.environ.get('BOT_COUNT', '1') or 1))
        except (ValueError, TypeError):
            slot, count = 0, 1
        if count <= 1:
            return ux, uy
        # ±18° spread across the fleet
        span = 0.32
        ang = ((slot - (count - 1) * 0.5) / max(count - 1, 1)) * span
        ca, sa = math.cos(ang), math.sin(ang)
        hx = ux * ca - uy * sa
        hy = ux * sa + uy * ca
        n = math.hypot(hx, hy) or 1.0
        return hx / n, hy / n

    def _follow_wall_blend(self, me, hx, hy):
        """Keep bots safely in open arena, deflecting smoothly along boundaries without sticking."""
        w = self.world
        if w is None or me is None:
            return hx, hy
        ar = float(w.arena if (w.arena or 0) > 0 else 11180.0)
        margin = 150.0
        nx, ny = hx, hy

        near_left = me.x < margin
        near_right = me.x > ar - margin
        near_top = me.y < margin
        near_bottom = me.y > ar - margin

        # If jammed tight against border (< 80), emergency center steer
        if me.x < 80.0 or me.x > ar - 80.0 or me.y < 80.0 or me.y > ar - 80.0:
            cx, cy = ar * 0.5, ar * 0.5
            cdx, cdy = cx - me.x, cy - me.y
            cn = math.hypot(cdx, cdy) or 1.0
            return cdx / cn, cdy / cn

        # Wall avoidance with tangent slide: ONLY prevent velocity pointing directly into the wall
        if near_left and nx < 0.0:
            nx = 0.15
        elif near_right and nx > 0.0:
            nx = -0.15

        if near_top and ny < 0.0:
            ny = 0.15
        elif near_bottom and ny > 0.0:
            ny = -0.15

        n = math.hypot(nx, ny) or 1.0
        return nx / n, ny / n


    def _dodge_nearby(self, me):
        """While the target is hidden, get out of the way of a cell that eats us.

        Two different answers for two different situations, because a small
        cell and a big one have opposite physics:

          * TINY (below TINY_MASS): a spawn-mass cell is FASTER than anything
            that can eat it, so it can simply leave.  It must also react much
            earlier, because everything around it is lethal.
          * otherwise: sidestep.  A big cell cannot outrun its threats, so
            turning tail just runs it into whatever is behind it -- that is
            what the original comment meant by "pure reverse runs back into
            the next player".

        MEASURED (tools/_live_check4.log, 2026-09-30): 136 of 154 deaths
        happened at 16-30 mass, most of them in the FARM/AVOID phases -- i.e.
        while grazing with the sidestep already engaged.  The bots were dying
        of the sidestep, not of the walking.

        Iteration 2 (`tools/_live_check5.log`) made tiny cells flee the NEAREST
        eater and cut deaths 56 -> 39, but AVOID rose 45 -> 65 while the mass at
        death stayed at 16-25: they were now leaving one eater straight into the
        next.  So for tiny cells the heading comes from _flee_vector, which sums
        repulsion from EVERY threat and therefore points through the gap --
        exactly what its (previously uncalled) docstring describes.
        """
        if me.mass < TINY_MASS:
            radius = max(float(self.threat_radius or 0.0), TINY_FLEE_RADIUS)
            threats = self._threats_near(me, radius)
            if not threats:
                return None
            v = self._flee_vector(me, threats)
            if v is not None:
                return v
            # DEGENERATE CASE, and the reason the old code sidestepped at all:
            # eaters on opposite sides give a repulsion sum of exactly zero.
            # Returning that (or None) parks us between them, so move
            # PERPENDICULAR to the nearest eater -- that is the gap.
            # Caught by the offline probe: two 400-mass cells at x-400 and x+400
            # around a 17-mass bot cancelled exactly.
            nearest = min(threats,
                          key=lambda e: math.hypot(e.x - me.x, e.y - me.y))
            vx, vy = me.x - nearest.x, me.y - nearest.y
            d = math.hypot(vx, vy) or 1.0
            return (-vy / d, vx / d)

        best = None
        for e in self.world.entities.values():
            if e.is_self or e.kind not in (K_CELL, K_VIRUS):
                continue
            if e.kind == K_CELL and e.mass < me.mass * 0.95:
                continue
            dist = math.hypot(e.x - me.x, e.y - me.y)
            danger = e.r + me.r + (200.0 if me.mass < 60.0 else 110.0)
            if dist < danger and (best is None or dist < best[0]):
                best = (dist, e)
        if best is None:
            return None
        e = best[1]
        vx, vy = e.x - me.x, e.y - me.y
        dist = math.hypot(vx, vy) or 1.0
        ax, ay = -vx / dist, -vy / dist
        # Bigger: blend a lateral component so we do not back into the next
        # player on the far side.
        lx, ly = -vy / dist, vx / dist
        hx, hy = lx * 0.85 + ax * 0.45, ly * 0.85 + ay * 0.45
        n = math.hypot(hx, hy) or 1.0
        return hx / n, hy / n

    def _touch_dodge(self, me, target_uuid: str = ''):
        """Sidestep a cell that can eat us.

        Small cells need a much wider flee radius — a 10-mass bot that only
        dodges at body-contact dies every few seconds and the party count
        looks like bots are dropping.
        """
        tuid = (target_uuid or '').lower()
        best = None
        # A 10-mass bot cannot outrun anything that eats it, so a body-to-body
        # dodge is already too late.  Start leaving much earlier while small.
        # This is the LAST-RESORT flee, for a threat already on top of us.
        # Widening it (tried 430 at <25 mass) made the bot flee 57 of 61 ticks
        # and starve -- it still died at 13.9 because it never ate.  Steady
        # threat handling lives in _safe_farm_heading, which eats and evades
        # at the same time.
        if me.mass < 25.0:
            reach = 300.0
        elif me.mass < 60.0:
            reach = 200.0
        else:
            reach = 55.0
        for e in self.world.entities.values():
            if e.is_self or e.kind != K_CELL:
                continue
            if tuid and (e.uuid or '').lower() == tuid:
                continue
            if e.mass < me.mass * EAT_RATIO:
                continue
            gap = math.hypot(e.x - me.x, e.y - me.y) - e.r - me.r
            if gap < reach and (best is None or gap < best[0]):
                best = (gap, e)
        if best is None:
            return None
        e = best[1]
        vx, vy = me.x - e.x, me.y - e.y
        n = math.hypot(vx, vy) or 1.0
        return vx / n, vy / n

    def _search_point(self, me, now, near=None):
        """A deterministic waypoint that guarantees the fleet covers the map.

        Falling back to the map centre put every bot of the fleet on the same
        spot, where a single enemy farmed them: 45 deaths in ten minutes, mass
        pinned at 10, zero feeds.  A rotating ring spread them out but still
        left the map statistically uncovered: an 11180-unit arena against a
        ~2000-unit streaming window is a few percent per bot per pass, which is
        why 330 of 331 samples read "Target: NOT VISIBLE".

        So carve the arena into `count` disjoint sectors and give each bot a
        boustrophedon (lawn-mower) path over its own sector, lanes spaced well
        inside one streaming window.  Every point on the map is then visited
        within about half a minute, and whichever bot crosses the human
        publishes the sighting, which pulls the rest of the fleet straight in.

        `near` overrides the sector sweep: when the human was seen recently but
        has since walked out of everyone's window, the fleet walks a rotating
        ring around that last known area instead of a sector on the other side
        of the map.  The ring radius is well inside one streaming window, so a
        bot on it picks the human up as soon as they drift back.
        """
        size = float(getattr(self.world, 'arena', 0.0) or 11180.0)
        try:
            slot = getattr(self, 'bot_index', None)
            if slot is None:
                slot = int(os.environ.get('BOT_INDEX', '0') or 0)
            count = getattr(self, 'bot_count', None)
            if count is None:
                count = max(1, int(os.environ.get('BOT_COUNT', '1') or 1))
        except (ValueError, TypeError):
            slot, count = 0, 1
        PAD = 1000.0
        usable_min = PAD
        usable_max = size - PAD
        
        # If we have a recent sighting location, move straight towards it!
        if near is not None:
            nx = min(usable_max, max(usable_min, near[0]))
            ny = min(usable_max, max(usable_min, near[1]))
            return nx, ny

        # Grouped fleet rally: head straight for the arena center hub where action is
        cx, cy = size * 0.5, size * 0.5
        return cx, cy

    def _seek_point(self, me, tgt, last_pos, last_pos_t, now):
        """Where to walk while the follow target is not on screen.

        The arena streams only a window around us, so a follower that has
        just spawned is normally nowhere near its target.  The old code sent
        a zero joystick in that case ("hold still so we don't farm away"),
        which left the bot parked on its spawn point: 454 of 525 logged
        samples said "Target: NOT VISIBLE" and it never fed once.  Walk to
        the last place we saw them, and if we never have, sweep the map --
        picking them up on the way.
        """
        if tgt is not None:
            return tgt.x, tgt.y

        def _corner(x, y, ar=11180.0, m=220.0):
            # Only ignore bogus uninitialized (0, 0) coordinates
            return (x <= 15.0 and y <= 15.0)

        # Newest fix wins.  Our own last_pos is only useful while it is the
        # freshest information we have; a sibling that saw the human 5s ago
        # knows more than we do about a spot we saw two minutes ago, and
        # preferring our own stale memory is what left bots wandering to a
        # ten-minute-old position instead of following.
        hint = _target_hint(getattr(self, 'follow', None))
        if hint is not None and _corner(hint[0], hint[1]):
            hint = None
        mine_ok = (last_pos is not None
                   and now - last_pos_t <= self.SEEK_MEMORY
                   and not _corner(last_pos[0], last_pos[1]))
        if hint is not None and (not mine_ok or hint[2] > last_pos_t):
            if math.hypot(me.x - hint[0], me.y - hint[1]) < 180.0:
                return self._search_point(me, now, near=(hint[0], hint[1]))
            return hint[0], hint[1]
        if mine_ok:
            if math.hypot(me.x - last_pos[0], me.y - last_pos[1]) < 180.0:
                return self._search_point(me, now, near=(last_pos[0], last_pos[1]))
            return last_pos[0], last_pos[1]

        # Nothing fresh enough to walk straight to.  Head for wherever the
        # human was last seen -- ours or a sibling's -- and sweep a ring
        # around it, rather than abandoning that knowledge for a sector on
        # the far side of an 11180-unit map.  AREA_MEMORY is longer than
        # FLEET_TARGET_MAX_AGE on purpose: a fix can be too old to aim at
        # while still being a perfectly good place to look.
        area = None
        if last_pos is not None and now - last_pos_t < AREA_MEMORY:
            area = (last_pos[0], last_pos[1])
        else:
            raw = _fleet_target_raw(getattr(self, 'follow', None))
            if raw is not None and now - raw[2] < AREA_MEMORY:
                area = (raw[0], raw[1])
        return self._search_point(me, now, near=area)

    def _start_mass_aim(self, me, tgt, last_pos, aim=None, slack=80.0):
        """Eat the pellets on the way to the player.

        The server hands every fresh cell about 10 mass. The rest of a
        start-of-round 130 comes from the pellets sitting in front of you,
        so pick one that also moves us closer to them.

        `aim` is the destination to use when the target itself is off-screen
        (its last known spot, or the middle of the map) -- see _seek_point.
        `slack` is how far a pellet may push us AWAY from `aim` before it is
        ignored -- measured as the perpendicular offset from the aim ray, which
        is the literal reading of "how far off course will we go for this".
        The tight 80 keeps a grown bot on course; the farming branch passes a
        loose value so a small bot still eats its local field but drifts toward
        the meet-up point instead of circling its spawn forever.

        NOTE: this parameter used to be declared, documented, and never read --
        the body used a fixed 60-degree cone instead, so every caller that
        tuned `slack` was silently tuning nothing.  The cone is now derived
        from it, so the two cannot disagree.
        """
        if tgt is not None:
            tx, ty = tgt.x, tgt.y
        elif aim is not None:
            tx, ty = aim
        elif last_pos is not None:
            tx, ty = last_pos[0], last_pos[1]
        else:
            tx = ty = None
        best = None
        best_s = -1e9
        # Unit vector toward the objective, so a pellet can be judged by whether
        # it lies *ahead* of us rather than merely nearby.
        if tx is not None:
            _ax, _ay = tx - me.x, ty - me.y
            _an = math.hypot(_ax, _ay)
        else:
            _ax = _ay = _an = 0.0
        for e in self.world.entities.values():
            if e.kind not in EDIBLE_KINDS:
                continue
            d = math.hypot(e.x - me.x, e.y - me.y)
            if d > 1100.0 or d < 1.0:
                continue
            worth = (3.0 if e.kind == K_SMALL else 1.0) * max(e.mass, 1.0)
            if _an > 1.0:
                ux, uy = _ax / _an, _ay / _an
                ex, ey = e.x - me.x, e.y - me.y
                align = (ex * ux + ey * uy) / d
                if align <= 0.0:
                    continue              # behind us: never worth a detour
                # Perpendicular offset from the aim ray -- the literal "how far
                # off course does this pellet take us".  Replaces the old fixed
                # 60-degree cone so `slack` actually controls the detour.
                perp = abs(ex * uy - ey * ux)
                if perp > slack and d > 90.0:
                    continue
                score = worth * (1.0 + 2.0 * align) / (d + 40.0)
            else:
                score = worth / (d + 40.0)
            if score > best_s:
                best_s = score
                best = e
        if best is not None:
            dx, dy = best.x - me.x, best.y - me.y
        elif tx is not None:
            dx, dy = tx - me.x, ty - me.y
        else:
            h = self.brain.heading
            return h if h else (1.0, 0.0)
        n = math.hypot(dx, dy) or 1.0
        return dx / n, dy / n

    def _threats_near(self, me, radius):
        """Enemy cells that can eat us and are within `radius` of our edge.

        Follow target and party members are strictly excluded: the bot must
        NEVER flee from the operator, regardless of how much mass the operator has.
        """
        out = []
        target_uuids = set(self._follow_aliases(self.follow or ''))
        target_name = (getattr(self, 'follow_name', '') or '').lower().strip()
        for e in self.world.entities.values():
            if e.is_self or e.kind != K_CELL:
                continue
            eu = (e.uuid or '').lower().strip()
            en = (e.name or '').lower().strip()
            if eu and (eu in target_uuids or self._uid_hit(self.follow, eu)):
                continue
            if target_name and en == target_name:
                continue
            if self._is_party_mate(e):
                continue
            if e.mass < me.mass * EAT_RATIO:
                continue
            if math.hypot(e.x - me.x, e.y - me.y) - e.r <= radius:
                out.append(e)
        return out

    def _flee_vector(self, me, threats):
        """Escape direction: sum of 1/d-weighted repulsion from EVERY threat.

        The reference bot does this and it is the reason it survives crowds.
        Our old dodge reacted to the single nearest threat only, so a bot
        stepping away from one eater walked straight into the next one.
        Weighting by 1/d lets the vector point through the gap instead.
        """
        ax = ay = 0.0
        for e in threats:
            dx, dy = me.x - e.x, me.y - e.y
            d = math.hypot(dx, dy)
            if d < 1e-6:
                ax += 1.0
                continue
            ax += (dx / d) / max(d, 1.0)
            ay += (dy / d) / max(d, 1.0)
        n = math.hypot(ax, ay)
        if n < 1e-9:
            return None
        return ax / n, ay / n

    def _safe_farm_heading(self, me, aim=None):
        """One heading that both feeds us and keeps us alive.

        The two previous strategies each failed on their own, and the numbers
        are in the ZTZ2MC logs:

          * nearest/best pellet (no threat logic)  -> 17 GROW deaths, median
            mass 14.  A 15-mass bot walked straight into 500+ mass cells.
          * flee when a threat is near               -> 57 of 61 samples were
            AVOID, 9 deaths, 0 feeds.  The bot ran and starved at 13 mass.

        So sample 16 headings and score each one by the food it walks onto
        minus how close it passes to something that can eat us.  The winner
        eats while it retreats, which neither branch could do.
        """
        R = 520.0
        threats = []
        food = []
        for e in self.world.entities.values():
            if e.is_self:
                continue
            if e.kind == K_CELL and e.mass >= me.mass * EAT_RATIO:
                threats.append(e)
            elif e.kind in EDIBLE_KINDS:
                d0 = math.hypot(e.x - me.x, e.y - me.y)
                if d0 <= R and d0 >= 1.0:
                    food.append((e, d0))
        if aim is not None:
            ax, ay = aim[0] - me.x, aim[1] - me.y
            an = math.hypot(ax, ay)
            ux0, uy0 = (ax / an, ay / an) if an > 1.0 else (0.0, 0.0)
        else:
            ux0 = uy0 = 0.0
        best = None
        best_s = -1e18
        for i in range(16):
            a = 2.0 * math.pi * i / 16.0
            ux, uy = math.cos(a), math.sin(a)
            px, py = me.x + ux * R, me.y + uy * R
            s = 0.0
            for e, d0 in food:
                align = ((e.x - me.x) * ux + (e.y - me.y) * uy) / d0
                if align < 0.30:          # only food we are heading into
                    continue
                w = (3.0 if e.kind == K_SMALL else 1.0) * max(e.mass, 1.0)
                s += 100.0 * w * align / (d0 + 60.0)
            if ux0 or uy0:
                s += 2.0 * (ux * ux0 + uy * uy0)
            for e in threats:
                # Sample the path, not just where we end up: a heading that
                # passes through a big cell and out the other side scored clean
                # when only the far endpoint was checked.
                worst = None
                for frac in (0.4, 0.7, 1.0):
                    qx = me.x + ux * R * frac
                    qy = me.y + uy * R * frac
                    c = math.hypot(e.x - qx, e.y - qy) - (e.r + me.r)
                    worst = c if worst is None else min(worst, c)
                if worst < 0.0:
                    s -= 400.0            # this heading walks into their mouth
                elif worst < 260.0:
                    s -= (260.0 - worst)
            if s > best_s:
                best_s = s
                best = (ux, uy)
        return best if best is not None else (1.0, 0.0)

    def _farm_aim(self, me, aim):
        """Eat the local pellet field while drifting toward `aim`.

        Two earlier strategies both failed.  Nearest-pellet farming parks the
        bot where it spawned, so it never closes on the operator.  Pellet-on-
        the-line-to-the-target farming (tight slack) marches at spawn mass and
        gets eaten.  This weights pellets by how well they line up with `aim`,
        but only among the ones actually near us -- so the bot keeps eating and
        still walks toward the meet-up point.
        """
        if aim is None:
            return self._start_mass_aim(me, None, None)
        ax, ay = aim
        vx, vy = ax - me.x, ay - me.y
        n = math.hypot(vx, vy)
        if n < 1.0:
            return self._start_mass_aim(me, None, None)
        ux, uy = vx / n, vy / n
        # When the meet-up point is far away we are *travelling*, not grazing.
        # The old weighting let a pellet directly behind us win on proximity
        # (align only scaled the score by up to 3.5x), so the bot orbited its
        # spawn forever while the log claimed it was "growing".  Restrict the
        # menu to a forward cone in that case: the bot still eats, but every
        # pellet it takes also moves it toward the target.
        travelling = n > 600.0
        min_align = 0.20 if travelling else -1.0
        best = None
        best_s = -1e9
        for e in self.world.entities.values():
            if e.kind not in EDIBLE_KINDS:
                continue
            dx, dy = e.x - me.x, e.y - me.y
            d = math.hypot(dx, dy)
            if d > 900.0 or d < 1.0:
                continue
            align = (dx * ux + dy * uy) / d          # -1 .. 1
            if align < min_align:
                continue
            worth = (3.0 if e.kind == K_SMALL else 1.0) * max(e.mass, 1.0)
            score = worth * (1.0 + 2.5 * max(0.0, align)) / (d + 40.0)
            if score > best_s:
                best_s = score
                best = e
        if best is not None:
            dx, dy = best.x - me.x, best.y - me.y
        else:
            # No food in sight at all: walk the line to the meet-up point.
            dx, dy = ux, uy
        m = math.hypot(dx, dy) or 1.0
        return dx / m, dy / m

    def _play_follow(self, deadline) -> str:
        """Lock the follow UID and deliver mass — any mass, no farm gate.

        Behaviour (what the operator asked for):
          * Arrow always locks onto the follow player (or last known spot).
          * Mass does not matter (2 / 5 / 8 / 10 / 20 / 50 / 100…): walk
            INTO them.  Being eaten by the operator IS the mass hand-off
            when we are light; when we are heavier we also eject.
          * Mass > 20 + split_feed on: split + feed together once close.
          * Enemy on the line me→player: sticky left/right bend around them
            (no left-right flicker).
          * Surrounded: orbit / probe for a gap, still biased at the player.
        """
        key = self.follow
        eff = key
        aliases = self._follow_aliases(key or '')
        self.log(f'[follow] v3 hunt uid={key!r} aliases={sorted(aliases)[:10]} '
                 f'(name+uuid — yehi pe lock hoga)')
        last_auto = 0.0
        last_stats = 0.0
        last_feed = 0.0
        last_split = 0.0
        last_seen_alive = time.time()
        _no_self_logged = 0.0
        lost_since = None
        death_logged = False
        last_pos = None
        last_pos_t = 0.0
        _last_stat_xy = None
        _last_stat_upd = self.world.updates
        _still_since = time.time()
        _pin_xy = None
        _pin_recoveries = 0
        PIN_S = 1.8
        STALE_S = 14.0
        _stream_upd = self.world.updates
        _stream_t = time.time()
        _stale_hits = 0
        phase = 'SEEK'
        self._avoid_side = 0.0
        self._avoid_side_until = 0.0
        _last_train_log = 0.0
        _mismatch_since = None
        # Auto-learn sensors
        _lr_sign = 0.0
        _lr_flips = 0
        _lr_window_t = time.time()
        _avoid_streak_t = 0.0
        _life_feeds0 = self.feeds
        _last_tgt_dist = float('inf')
        # Target velocity + smooth stick — kills L/R thrash when operator strafes
        _tgt_prev = None
        _tgt_prev_t = 0.0
        _tvx = 0.0
        _tvy = 0.0
        _joy_s = None  # smoothed joystick
        BRAIN = 'v3-autolearn'

        while time.time() < deadline and not self._stop.is_set():
            self._heartbeat += 1
            # Live train knobs — auto-learn + bot/train_follow.txt
            EJECT_FLOOR = max(10.0, self._train('feed_keep', float(self.feed_keep)))
            SPLIT_MASS = self._train('split_mass', 20.0)
            DELIVER_RANGE = self._train('deliver_range', 800.0)
            DIVE_PAD = self._train('dive_pad', 16.0)
            LOCK_MEMORY = self._train('lock_memory', 12.0)
            SPLIT_CD = self._train('split_cooldown', 0.90)
            FEED_GAP = self._train('feed_gap', 0.035)
            FEED_BURST = max(1, int(self._train('feed_burst', 5.0)))
            FEED_DRIP = max(1, int(self._train('feed_drip', 3.0)))
            SURROUND_MIN = max(2, int(self._train('surround_min', 4.0)))
            COMMIT_BOOST = self._train('commit_boost', 0.0)
            # Survival gate.  Live-tunable from bot/train_follow.txt as
            # `safe_mass`, falling back to --safe-mass.  0 disables the gate
            # (the old "mass does not matter" behaviour).
            SAFE_MASS = max(0.0, self._train('safe_mass',
                                             float(self.safe_mass or 0.0)))

            self._pump_arena()
            now = time.time()
            # Stop/scale leave must work even if poller thread is late
            if not hasattr(self, '_live_chk_t'):
                self._live_chk_t = 0.0
            if now - self._live_chk_t >= 0.45:
                self._live_chk_t = now
                if self.tick_live_ctrl():
                    return 'closed'
            if now - _last_train_log >= 20.0:
                _last_train_log = now
                self.log(f'[train] {BRAIN} split>{SPLIT_MASS:.0f} '
                         f'range={DELIVER_RANGE:.0f}+{COMMIT_BOOST:.0f} '
                         f'dive={DIVE_PAD:.0f} side={self._train("avoid_side", 0.35):.2f} '
                         f'fwd={self._train("avoid_forward", 0.9):.2f} '
                         f'sticky={self._train("avoid_sticky_s", 1.5):.2f}s '
                         f'safe_mass={SAFE_MASS:.0f}'
                         f'{" (gate OFF)" if SAFE_MASS <= 0 else ""}')
            if self.arena is None or (
                    self.ar_closed.is_set() and not self._arena_is_inline()):
                self.log('[!] arena connection closed by the server')
                return 'closed'
            if self._arena_is_inline() and self.mm_closed.is_set():
                self.log('[!] matchmaker closed (inline arena)')
                return 'closed'
            me = self.world.me
            # Alive cell missing but not marked dead = usually pin/self_id
            # race.  Re-resolve once before treating as death (stops the
            # eaten-by-None + mt=12 flood that dropped the fleet).
            if me is None and not self.world.dead:
                try:
                    self.world._resolve_self(now)
                except Exception:
                    pass
                me = self.world.me
            if me is None or self.world.dead:
                # Auto-learn: died near target without giving mass this life.
                if (self.world.dead
                        and _last_tgt_dist < 900.0
                        and (self.feeds - _life_feeds0) <= 0
                        and _follow_train is not None):
                    try:
                        msg = _follow_train.learn(
                            'death_near',
                            detail=f'dist={_last_tgt_dist:.0f}')
                        if msg:
                            self.log(f'[{msg}]')
                    except Exception:
                        pass
                if not death_logged and self.world.dead:
                    death_logged = True
                    kb_ent = self.world.entities.get(self.world.killed_by)
                    if kb_ent:
                        kb_name = kb_ent.name or '?'
                        kb_uuid = getattr(kb_ent, 'uuid', '') or ''
                    elif self.world.killed_by in getattr(self.world, 'entity_history', {}):
                        hist = self.world.entity_history[self.world.killed_by]
                        kb_name = hist[0] or '?'
                        kb_uuid = hist[1] or ''
                    else:
                        kb_name = '?'
                        kb_uuid = ''
                    is_operator = bool(
                        self._uid_hit(self.follow, kb_uuid)
                        or (getattr(self, 'follow_name', '') and kb_name.lower() == self.follow_name.lower())
                        or (tgt is not None and self.world.killed_by == tgt.id)
                    )
                    if is_operator:
                        self.log(f'>>> [MASS DELIVERED TO YOU!] Bot absorbed by YOU ({kb_name}[{kb_uuid[:8]}]) (death #{self.world.deaths})')
                    else:
                        self.log(f'!!! [EATEN BY ENEMY: {kb_name}] Bot absorbed by enemy {kb_name}[{kb_uuid[:8]}] (id={self.world.killed_by}, death #{self.world.deaths})')
                    self.event('death', killed_by=self.world.killed_by,
                               deaths=self.world.deaths)

                if not self.respawn:
                    return 'dead'
                # No self + not dead → wait; do NOT leave the arena (non-drop).
                if me is None and not self.world.dead:
                    # Bounded wait.  This branch used to `continue` until the
                    # run deadline, which is 100000 s in the fleet config: a
                    # node that accepted the socket but never assigned us a
                    # cell left the process alive, silent, and playing
                    # nothing -- indistinguishable from a drop, and never
                    # restarted because poll() still said "alive".
                    if now - last_seen_alive > NO_SELF_BAIL_S:
                        # In follow mode, NEVER bail out of the arena. Mash play mt=110 to spawn cell.
                        last_seen_alive = now
                        try:
                            nick = (self.nick or '').strip() or 'b'
                            self._arena_send(self.play_pkt(nick))
                        except Exception:
                            pass
                        continue
                    # Soft recover: try resolve again; stay on node.
                    try:
                        self.world._resolve_self(now)
                    except Exception:
                        pass
                    if now - _no_self_logged >= 8.0:
                        _no_self_logged = now
                        self.log(f'[follow] no self cell for '
                                 f'{now - last_seen_alive:.0f}s — waiting '
                                 f'(non-drop, never bails)')
                    self._heartbeat += 1
                    time.sleep(0.05)
                    continue
                # ONE same-socket respawn window (longer — avoid Round finished
                # drop). Fail → soft reconnect (inline keeps MM open).
                window = min(deadline, time.time() + 20.0)
                if self._respawn(window):
                    last_seen_alive = time.time()
                    death_logged = False
                    lost_since = None
                    _life_feeds0 = self.feeds
                    _last_tgt_dist = float('inf')
                    _lr_flips = 0
                    _avoid_streak_t = 0.0
                    _pin_xy = None
                    _pin_recoveries = 0
                    _last_stat_xy = None
                    _still_since = time.time()
                    _stream_upd = self.world.updates
                    _stream_t = time.time()
                    _stale_hits = 0
                    continue
                # In follow mode, NEVER bail on respawn timeout — mash play mt=110 on same socket!
                try:
                    nick = (self.nick or '').strip() or 'b'
                    self._arena_send(self.play_pkt(nick))
                except Exception:
                    pass
                last_seen_alive = time.time()
                time.sleep(0.5)
                continue
            if death_logged:
                death_logged = False
                self.log(f'[respawn] back as id={me.id} mass={me.mass:.1f} — seeking')
            last_seen_alive = now
            self._record_own_uuid()

            # --- stale world stream (upd freeze) ---------------------------
            # Empty FOV often pauses updates while the cell is still moving.
            # Only soft-bail when BOTH stream AND cell are dead — otherwise
            # Round-finished reconnect empties the party (user saw 10→4).
            _upd_now = self.world.updates
            if _upd_now != _stream_upd:
                _stream_upd = _upd_now
                _stream_t = now
                _stale_hits = 0
            elif now - _stream_t > STALE_S:
                cell_moving = (
                    _pin_xy is not None
                    and math.hypot(me.x - _pin_xy[0], me.y - _pin_xy[1]) > 12.0)
                if cell_moving:
                    # Alive, just quiet FOV — reset timer, keep seeking.
                    _stream_t = now
                    _stale_hits = 0
                else:
                    _stale_hits += 1
                    self.log(f'[stale] no world updates for {STALE_S:.0f}s '
                             f'(upd={_upd_now}, still) — keeping alive '
                             f'(hit {_stale_hits})')
                    _stale_hits = 0
                    _stream_t = now
                    arena = float(self.world.arena or 11180.0)
                    cx, cy = arena * 0.5, arena * 0.5
                    dx, dy = cx - me.x, cy - me.y
                    n = math.hypot(dx, dy) or 1.0
                    self._send_joy((dx / n, dy / n), raw=True)
                    continue

            # --- pinned-cell watchdog -------------------------------------
            # Nudge once; third CONSECUTIVE pin → soft reconnect (no mt=80
            # leave).
            #
            # The counter MUST be cleared by real movement.  It used to only
            # ever increase within a life, so a bot that pinned at spawn,
            # recovered, played for a while, pinned again near a wall and
            # recovered once more would bail on its third pin -- however much
            # healthy play happened in between -- and each bail costs a full
            # matchmaker login.  MEASURED (tools/_watchdog_probe.py): a bot
            # that moved 12 s between three 25 s pins was torn down and
            # reconnected even though its stream never stalled.
            #
            # The reference point deliberately SURVIVES the nudge.  Clearing
            # it (the old `_pin_xy = None`) re-entered the "has it moved?"
            # branch on the very next tick, which would clear the counter
            # immediately and make the third-pin bail unreachable.
            if _pin_xy is None:
                _pin_xy = (me.x, me.y)
                _still_since = now
            if math.hypot(me.x - _pin_xy[0], me.y - _pin_xy[1]) > 8.0:
                if _pin_recoveries:
                    self.log(f'[pin] cell moving again after '
                             f'{_pin_recoveries} nudge(s) — counter cleared')
                _pin_recoveries = 0
                _pin_xy = (me.x, me.y)
                _still_since = now
            elif now - _still_since > PIN_S:
                _pin_recoveries += 1
                self.log(f'[pin] cell stuck at ({me.x:.0f},{me.y:.0f}) '
                         f'mass={me.mass:.1f} for {now - _still_since:.0f}s '
                         f'(updates={self.world.updates}) — '
                         f'{"soft reconnect" if _pin_recoveries >= 8 else "nudge"} '
                         f'#{_pin_recoveries}')
                if _pin_recoveries == 3 and me.mass >= 36.0:
                    self.do_split()
                elif _pin_recoveries >= 4 and me.mass >= 36.0:
                    self.do_16_split()
                if _pin_recoveries >= 6:
                    _pin_recoveries = 0
                    _still_since = now
                    _pin_xy = None
                    if me.mass >= 36.0:
                        self.do_16_split()
                    continue
                _still_since = now
                _pin_xy = None
                # Find the most open escape heading (away from any nearby obstacle or wall)
                best_heading = None
                best_score = -1e9
                arena_max = float(self.world.arena or 11180.0)
                for ang_i in range(12):
                    ang = (ang_i / 12.0) * 2.0 * math.pi
                    tx_dir = math.cos(ang)
                    ty_dir = math.sin(ang)
                    future_x = me.x + tx_dir * 300.0
                    future_y = me.y + ty_dir * 300.0
                    if future_x < 180.0 or future_x > arena_max - 180.0 or future_y < 180.0 or future_y > arena_max - 180.0:
                        continue
                    min_obs_d = 9999.0
                    for e in self.world.entities.values():
                        if e.is_self or e.kind not in (K_CELL, K_VIRUS):
                            continue
                        if e.kind == K_CELL and e.mass < me.mass * 1.05:
                            continue
                        edx, edy = e.x - me.x, e.y - me.y
                        edist = math.hypot(edx, edy)
                        along = (edx * tx_dir + edy * ty_dir)
                        if along > 0:
                            min_obs_d = min(min_obs_d, edist)
                    if min_obs_d > best_score:
                        best_score = min_obs_d
                        best_heading = (tx_dir, ty_dir)

                nudge = best_heading if best_heading is not None else (random.choice([-1.0, 1.0]), random.choice([-1.0, 1.0]))
                t_end = time.time() + 1.2
                while time.time() < t_end and not self._stop.is_set():
                    self._pump_arena()
                    if self.world.dead or self.world.me is None:
                        break
                    self._send_joy(nudge, raw=True)
                    time.sleep(0.04)
                continue

            tgt = self.find_player(eff)
            if tgt is None and now - last_auto >= 10.0:
                last_auto = now
                human, hkind = self._party_human_key()
                if human and human != eff:
                    eff = human
                    tgt = self.find_player(eff)
                    if tgt is not None:
                        self.log(f'[follow] config uid {key!r} not in this '
                                 f'arena — locked onto party human '
                                 f'{tgt.name!r} uuid={tgt.uuid} (via {hkind})')
                    else:
                        self.log(f'[follow] party human {hkind}={human} known '
                                 f'but not on screen yet — searching')
            my_mass = self.world.total_mass
            if tgt is not None:
                # Smooth target velocity so we LEAD their strafe instead of
                # chasing the instantaneous centre (that is the L/R dance).
                if (_tgt_prev is not None
                        and now - _tgt_prev_t >= 0.04
                        and now - _tgt_prev_t < 1.2):
                    dt = max(0.04, now - _tgt_prev_t)
                    rx = (tgt.x - _tgt_prev[0]) / dt
                    ry = (tgt.y - _tgt_prev[1]) / dt
                    _tvx = 0.65 * _tvx + 0.35 * rx
                    _tvy = 0.65 * _tvy + 0.35 * ry
                _tgt_prev = (tgt.x, tgt.y)
                _tgt_prev_t = now
                last_pos = (tgt.x, tgt.y, tgt.r, tgt.mass, tgt.name, tgt.uuid)
                last_pos_t = now
                self._record_target_sighting(tgt)
                _mismatch_since = None
                _is_inline = self._arena_is_inline()
                if _is_inline or _is_pinable_arena_host(self.arena_host):
                    _host = INLINE_ARENA if _is_inline else self.arena_host
                    _write_party_arena_pin(
                        _host, self.arena_port or MM_PORT, seen_target=True,
                        arena_id=(self.world.arena_id or ''),
                        code=self.code)
            else:
                _tvx *= 0.85
                _tvy *= 0.85
                pin = _read_party_arena_pin()
                pin_age = (time.time() - float(pin.get('ts') or 0)
                           if pin else 9999.0)
                _is_inline = self._arena_is_inline()
                _cur_host = INLINE_ARENA if _is_inline else (self.arena_host or '')
                _cur_ar = (self.world.arena_id or '').strip()
                _in_same_room = _same_fleet_room(pin, _cur_ar, _cur_host)
                _migrate = False
                if pin and pin.get('seen_target') and pin_age < PARTY_ARENA_PIN_FRESH:
                    # If target has been spotted in another arena/shard, migrate to join target's room
                    if not _in_same_room:
                        _migrate = True
                if _migrate:
                    if _mismatch_since is None:
                        _mismatch_since = now
                    elif now - _mismatch_since > 5.0:
                        self._arena_token_bounced = True
                        self.node_token = None
                        return self._bail_arena(
                            f'[party] wrong arena ({_cur_ar or _cur_host}) — '
                            f'target in {pin.get("arena_id") or pin.get("host")}, migrating to target')
                else:
                    if pin and (pin_age >= PARTY_ARENA_PIN_FRESH or not pin.get('seen_target')):
                        _clear_party_arena_pin()
                    _mismatch_since = None

            if tgt is None and last_pos is not None:
                # If bot reached the ghost position and target is not there, clear it immediately
                if math.hypot(me.x - last_pos[0], me.y - last_pos[1]) < 220.0:
                    last_pos = None

            ghost = (tgt is None and last_pos is not None
                     and now - last_pos_t < 4.0)
            aim = self._seek_point(me, tgt, last_pos, last_pos_t, now)

            # Resolve lock point: live target > ghost memory > seek aim.
            # Only do sibling merge if NO operator target is configured at all!
            is_sibling_lock = False
            sibling = None
            if tgt is not None:
                tx, ty, tr, tm, tname, tuuid = (
                    tgt.x, tgt.y, tgt.r, tgt.mass, tgt.name, tgt.uuid)
                locked = True
            elif ghost:
                tx, ty, tr, tm, tname, tuuid = last_pos
                locked = True
            elif not (getattr(self, 'follow', None) or getattr(self, 'follow_name', None)):
                sibling = self._find_nearby_bigger_friendly(me)
                if sibling is not None:
                    tx, ty, tr, tm, tname, tuuid = (
                        sibling.x, sibling.y, sibling.r, sibling.mass, sibling.name, sibling.uuid)
                    locked = True
                    is_sibling_lock = True
                else:
                    tx, ty = aim
            else:
                tx, ty = aim
                tr = tm = 0.0
                tname, tuuid = None, (eff or '')
                locked = False

            # EXE follow logic: compute true center of mass of bot's cells
            my_cells = [c for c in self.world.entities.values() if c.is_self]
            if my_cells:
                bot_x = sum(c.x for c in my_cells) / len(my_cells)
                bot_y = sum(c.y for c in my_cells) / len(my_cells)
            else:
                bot_x, bot_y = me.x, me.y

            # EXE follow logic: direct target aim (no lead prediction, no trail offset)
            aim_x, aim_y = tx, ty
            dx, dy = aim_x - bot_x, aim_y - bot_y
            dist = math.hypot(dx, dy)
            dist_true = (math.hypot(tx - bot_x, ty - bot_y) if locked else dist)
            ux, uy = (dx / dist, dy / dist) if dist > 1e-6 else (1.0, 0.0)

            # ---- COME TO ME: chase config UID anywhere + dump mass -------
            TOUCH = (tr + me.r + 80.0) if locked else 200.0
            FEED_DIST = (tr + me.r + 250.0) if locked else 350.0
            _last_tgt_dist = dist_true if locked else _last_tgt_dist

            if not locked:
                if lost_since is None:
                    lost_since = now
                    self.log(f'[follow] target {eff!r} hidden — hunting UID '
                             f'across arena ({aim[0]:.0f},{aim[1]:.0f})')
                phase = 'SEEK'
                # Skirt closely around any enemies in our path without going under them
                ux, uy = self._skirt_enemies(me, ux, uy, tgt=None)
                wx, wy = self._follow_wall_blend(me, ux, uy)
                self._send_joy((wx, wy), raw=True)
            else:
                if tgt is not None and lost_since is not None:
                    self.log(f'[follow] LOCK {tgt.name or "?"} uuid={tgt.uuid} '
                             f'mass={tgt.mass:.0f} — coming to you')
                    lost_since = None
                if tgt is not None and tgt.name:
                    n_clean = tgt.name.strip().lower()
                    if n_clean not in ('?', '', 'guest', 'none', 'null', 'test', 'b', 'bot') and len(n_clean.strip('?._- ')) > 0:
                        self._follow_seen_name = tgt.name
                        try:
                            uu = (tgt.uuid or key or '').lower()
                            if uu:
                                self.party_uuids[tgt.name] = uu
                                self._publish_party_now()
                        except Exception:
                            pass
                elif is_sibling_lock:
                    lost_since = None

                active_target = tgt if tgt is not None else sibling
                is_user_target = (tgt is not None)

                # Direct vector from bot center to user center (or ghost / aim point tx, ty)
                target_x = active_target.x if active_target is not None else tx
                target_y = active_target.y if active_target is not None else ty
                dir_u_x = (target_x - bot_x)
                dir_u_y = (target_y - bot_y)
                du = math.hypot(dir_u_x, dir_u_y) or 1.0
                ux_user = dir_u_x / du
                uy_user = dir_u_y / du

                # Status phase
                if dist_true <= 250.0:
                    phase = 'DIVE'
                elif dist_true <= 650.0:
                    phase = 'LOCK'
                else:
                    phase = 'COMMIT'

                # Line of sight enemy check: only block if an ENEMY is directly in the path to the user
                enemy_between = False
                target_uuids = set(self._follow_aliases(self.follow or ''))
                if active_target is not None and getattr(active_target, 'uuid', None):
                    target_uuids.add(str(active_target.uuid).lower().strip())
                for e in self.world.entities.values():
                    if e.kind != K_CELL or e.is_self or e.mass <= me.mass:
                        continue
                    if active_target is not None and e.id == active_target.id:
                        continue
                    eu = (e.uuid or '').lower().strip()
                    en = (e.name or '').lower().strip()
                    if not eu and hasattr(self.world, 'entity_history') and e.id in self.world.entity_history:
                        try:
                            eu = (self.world.entity_history[e.id][1] or '').lower().strip()
                        except Exception:
                            pass
                    if not en and hasattr(self.world, 'entity_history') and e.id in self.world.entity_history:
                        try:
                            en = (self.world.entity_history[e.id][0] or '').lower().strip()
                        except Exception:
                            pass
                    if eu and (eu in target_uuids or self._uid_hit(self.follow, eu)):
                        continue
                    if active_target is not None and getattr(active_target, 'color', None) is not None and getattr(e, 'color', None) == active_target.color:
                        if math.hypot(e.x - active_target.x, e.y - active_target.y) < max(900.0, (active_target.r + e.r) * 2.5):
                            continue
                    if self._is_party_mate(e):
                        continue
                    bot_nick = (getattr(self, 'nick', '') or '').lower().strip()
                    if en and bot_nick and (en == bot_nick or en.startswith(bot_nick)):
                        continue
                    if en in ('b', 'ggs'):
                        continue
                    edx, edy = e.x - bot_x, e.y - bot_y
                    edist = math.hypot(edx, edy)
                    if edist < dist_true:
                        align = (edx * ux_user + edy * uy_user) / max(edist, 1.0)
                        if align > 0.85:
                            enemy_between = True
                            break

                # 1. MOVEMENT STEERING:
                # Protect bot from enemies at all times using skin-tight zero-ingress avoidance
                jx, jy = self._skirt_enemies(me, ux_user, uy_user, tgt=active_target)
                wx, wy = self._follow_wall_blend(me, jx, jy)
                self._send_joy((wx, wy), raw=True)

                # 2. MASS DELIVERY (16-SPLIT & W FEED) DIRECTLY INTO USER:
                if is_user_target and not enemy_between:
                    try:
                        # Golden split range: <= 650 units distance
                        # At this range, splitting shoots pieces straight into the user!
                        if self.split_feed and my_mass >= 36.0 and dist_true <= 650.0:
                            if len(my_cells) < 16 and (now - last_split >= 0.12):
                                last_split = now
                                self.do_16_split(gap=0.015, heading=(ux_user, uy_user))
                                if now - getattr(self, '_give_log_t', 0) > 1.0:
                                    self._give_log_t = now
                                    self.log(f'>>> [16-SPLIT -> USER] Macro 16-split fired directly into {tname or (tuuid or "")[:8]}!')

                        # Continuous rapid feed within 550 units
                        if my_mass >= 32.5 and dist_true <= 550.0:
                            if now - last_feed >= 0.035:
                                last_feed = now
                                self.do_feed(4, gap=0.015, heading=(ux_user, uy_user))
                                if now - getattr(self, '_give_log_t', 0) > 1.0:
                                    self._give_log_t = now
                                    self.log(f'>>> [FEED W -> USER] Rapid feed stream directly into {tname or (tuuid or "")[:8]}!')
                    except Exception as e:
                        self.log(f'[follow] delivery err: {e}')


            if now - last_stats >= 4.0:
                last_stats = now
                # In-game command channel (see nick_cmd.py): the operator's own
                # nick is the only string the game renders inside the arena, so
                # it doubles as a command line -- no install, no patch, no MITM,
                # no DNS. Checked every stats tick (~4s), and a failure here can
                # never take the bot down.
                if _nick_cmd is not None:
                    try:
                        _nick_cmd.poll(self, self.world, now)
                    except Exception:                   # noqa: BLE001
                        pass
                st = self.world.stats()
                st.update(mode='follow', feeds=self.feeds, splits=self.splits,
                          target=(tgt.uuid if tgt else None),
                          target_mass=(round(tgt.mass, 1) if tgt else None),
                          target_dist=(round(math.hypot(tgt.x - me.x, tgt.y - me.y))
                                       if tgt else None))
                tl = (f"{tgt.name or '?'}[{(tgt.uuid or '')[:8]}] "
                      f"m:{tgt.mass:.0f} d:{st['target_dist']}"
                      if tgt else 'NOT VISIBLE')
                _bc = _app_target_sighting()
                _bc = (_bc[0], _bc[1]) if _bc else None
                _fx = _target_hint(getattr(self, 'follow', None))
                _age = (f'{now - _fx[2]:.0f}s' if _fx else 'none')
                if _last_stat_xy is None:
                    _mv = 0.0
                else:
                    _mv = math.hypot(me.x - _last_stat_xy[0],
                                     me.y - _last_stat_xy[1])
                _last_stat_xy = (me.x, me.y)
                _d_upd = self.world.updates - _last_stat_upd
                _last_stat_upd = self.world.updates
                _bi = getattr(self, 'bot_index', None)
                _bid = str(_bi + 1) if _bi is not None else os.environ.get('BOT_INDEX', '?')
                self.log(f"[FOLLOW] {BRAIN} #{_bid} Region: {self.region:<14} | "
                         f"Party: {self.party_code or '-':<7} | "
                         f"Me: {st['mass']:<5.1f} at ({st['x']},{st['y']}) "
                         f"-> ({tx:.0f},{ty:.0f}) | Target: {tl} | "
                         f"fix: {_age} | "
                         f"beacon: {'(%.0f,%.0f)' % _bc if _bc else 'none'} | "
                         f"upd: {_d_upd} mv: {_mv:.0f} | "
                         f"Feeds: {self.feeds} | Splits: {self.splits} | {phase}")
                _oth = [e for e in self.world.entities.values()
                        if e.kind == K_CELL and not e.is_self]
                self.log(f"[world] cells={len(_oth)} "
                         f"with_uuid={sum(1 for e in _oth if e.uuid)} | "
                         + (', '.join(
                             f'{(e.name or "?")}[{(e.uuid or "-")[:8]}]:{e.mass:.0f}'
                             for e in sorted(_oth, key=lambda x: -x.mass)[:6])
                            or '(empty)'))
                if self.on_stats:
                    try:
                        self.on_stats(st)
                    except Exception:
                        pass
                self.event('stats', **st)
            time.sleep(self.tick)
        return 'done'

    def _request_arena_redirect(self, max_tries: int = 25) -> bool:
        """Send mt=110 to Matchmaker (self.mm) to get a fresh mt=33 arena redirect and connect to it."""
        if self.mm is None or self.mm_closed.is_set():
            return False
        _pn = (self.nick or '').strip() or 'b'
        for retry in range(1, max_tries + 1):
            if self._stop.is_set() or self.mm is None or self.mm_closed.is_set():
                return False
            try:
                if self.code and not self.no_party and retry % 8 == 1:
                    self.send(self.mm, pkt_party(self.code), f'party mt=27 "{self.code}" (reenter keep)', silent=True)
                if getattr(self, 'boost_every_play', False) and retry == 1:
                    self._arm_boosts_before_play(self.q_mm)
                self.send(self.mm, self.play_pkt(_pn), f'play mt=110 arena-reenter {retry}', silent=(retry > 1))
            except Exception:
                return False

            got = self._wait_for(
                self.q_mm,
                lambda m, w: m.mt in (33, 52) or m.mt == 88 or w.me is not None,
                0.7, 'mt=33/52 arena-reenter',
                closed=self.mm_closed, quiet=True, log_frames=False)

            if got is not None and got.mt == 52:
                time.sleep(0.05)
                continue
            if got is None or got.mt not in (33, 88):
                time.sleep(0.05)
                continue
            if got.mt == 88 or self.world.me is not None:
                self.arena = self.mm
                self.q_ar = self.q_mm
                self.ar_closed = self.mm_closed
                return True

            f39 = one(got.inner, 39)
            if f39 is None:
                continue
            f = fields(f39)
            host = as_str(one(f, 2))
            port = int(one(f, 3) or NODE_PORT)
            node_token = as_str(one(f, 1))

            if host and self._arena(host, port, node_token, None):
                return True
        return False

    def _play_leave(self, deadline) -> str:
        """Feed-Leave mode:
        1. Enters arena.
        2. Waits for spawn (mass >= 40).
        3. Aims at target and dumps feed at normal official speed (70ms gap) until mass floor (<= 32.5).
        4. Pulls backward cleanly.
        5. Sends mt=80 (leave game), leaves arena, and closes arena socket.
        6. Re-enters arena and repeats endlessly until stopped. No in-arena cycles / no mt=12 respawn.
        """
        nick_str = (self.nick or '').strip() or 'b'
        play_packet = self.play_pkt(nick_str)
        pkt_f = pkt_feed()

        while not self._stop.is_set() and time.time() < deadline:
            self._heartbeat += 1

            # 1. Wait for cell to spawn in arena (mass >= 40.0)
            t0 = time.time()
            spawned = False
            while time.time() - t0 < 4.0 and not self._stop.is_set() and not self.ar_closed.is_set():
                self._heartbeat += 1
                self._pump_arena()
                if self.world.me is not None and not self.world.dead and self.world.total_mass >= 40.0:
                    spawned = True
                    break
                # Mash mt=110 every 0.6s if waiting for spawn
                if time.time() - t0 > 0.6 and (self.world.me is None or self.world.dead):
                    self._want_play = False
                    self._arena_send(play_packet)
                    t0 = time.time() - 0.1
                time.sleep(0.02)

            if self._stop.is_set() or time.time() >= deadline:
                break

            if not spawned or self.world.me is None or self.world.dead or self.world.total_mass < 40.0:
                self.log('[feed-leave] spawn wait ended -> leaving arena to re-enter')
            else:
                me = self.world.me
                init_mass = self.world.total_mass

                # 2. Aim towards target if known, else random heading
                tgt = None
                try:
                    tgt = self._resolve_target()
                except Exception:
                    pass
                if tgt is not None:
                    dx, dy = tgt.x - me.x, tgt.y - me.y
                    d = math.hypot(dx, dy) or 1.0
                    hx, hy = dx / d, dy / d
                else:
                    angle = random.uniform(0, 2 * math.pi)
                    hx, hy = math.cos(angle), math.sin(angle)
                self._send_joy((hx, hy), raw=True)

                self.log(f'[feed-leave] entered arena: mass {init_mass:.0f} -> feeding target')

                # 3. Dump feed at normal official speed (70ms gap) until mass floor reached (<= 32.5 or stuck)
                t_dump = time.time()
                ejects = 0
                last_m = self.world.total_mass
                last_drop_t = time.time()
                while time.time() - t_dump < 8.0 and not self._stop.is_set() and not self.ar_closed.is_set():
                    self._heartbeat += 1
                    self._pump_arena()
                    cur_m = self.world.total_mass
                    if self.world.me is None or self.world.dead or cur_m <= 32.5:
                        break

                    if cur_m < last_m - 0.4:
                        last_m = cur_m
                        last_drop_t = time.time()
                    elif time.time() - last_drop_t > 1.2:
                        break

                    # Keep tracking target dynamically as target moves
                    if tgt is not None and self.world.me is not None:
                        t_cur = self.world.entities.get(tgt.id)
                        if t_cur is not None:
                            dx, dy = t_cur.x - self.world.me.x, t_cur.y - self.world.me.y
                            d = math.hypot(dx, dy) or 1.0
                            hx, hy = dx / d, dy / d
                            self._send_joy((hx, hy), raw=True)

                    self._send_raw(pkt_f)
                    self.feeds += 1
                    ejects += 1
                    time.sleep(0.070)  # Normal official feed speed (~14 feeds/sec)

                # Pull backward slightly so tiny cell backs away from feed pile
                self._send_joy((-hx * 0.75, -hy * 0.75), raw=True)
                time.sleep(0.12)

                self.log(f'[feed-leave] dumped {ejects} feeds (mass {init_mass:.0f} -> {self.world.total_mass:.0f}) -> leaving arena (mt=80)')

            # 4. Leave arena (send mt=80 leave game packet)
            self.do_leave_game()
            time.sleep(0.05)

            # 5. Cleanly close arena socket
            is_inline = self._arena_is_inline()
            try:
                self.ar_closed.set()
                if self.arena is not None and not is_inline:
                    self.arena.close()
            except Exception:
                pass
            self.arena = None

            if self._stop.is_set() or time.time() >= deadline:
                break

            # 6. Re-enter arena:
            # First try re-entering on existing Matchmaker session
            reentered = False
            if not is_inline and self.mm is not None and not self.mm_closed.is_set():
                self.world = World()
                self.brain = Brain(self.strategy)
                self.hmap = HeadingMap()
                if self._request_arena_redirect(max_tries=20):
                    self._calibrate(deadline)
                    reentered = True

            if not reentered:
                # MM was closed, inline, or couldn't redirect — exit run() so main() forever loop reconnects cleanly
                self._arena_token_bounced = True
                return 'done'

        return 'done'

    def run(self) -> bool:
        """One full session: matchmaker -> arena -> play.  True if we played."""
        self.world = World()
        self.brain = Brain(self.strategy)
        self.hmap = HeadingMap()
        # Set by _arena() when the node answers a redirect back to a host we
        # already dialled with this bearer token: the token is stale, so
        # spending the same-token redial budget on it is pure delay.
        self._arena_token_bounced = False
        self._fleet_wrong_room = False

        # A refused token is the one failure worth a second dial: the handshake
        # already proved the source gets through, so the retry is not being
        # spent on a block.  Off by default -- retrying a genuine *throttle*
        # makes it worse -- and unnecessary in the common case, because the
        # ledger already rotates the next run onto a fresher token.
        info = None
        if getattr(self, 'arena_direct', None):
            # Arena-only: a captured mt=33 redirect (bearer node token) lets us
            # take the arena leg without a challenge-bound MM login.  The app
            # supplied the login + party + play; we are the arena presence.
            h, p, t = self.arena_direct
            self.log(f'[arena-direct] using captured redirect {h}:{p} token={t}')
            info = (h, int(p), t)
            # ONE-SHOT.  A node bearer token is single-use, so leaving this set
            # makes every later session in this process skip the matchmaker and
            # re-present a token the arena has already consumed.  The bot then
            # loops "arena rejected it -> retry -> same stale token" and never
            # recovers -- a permanent drop that looks like a throttle.
            self.arena_direct = None
        else:
            for try_n in range(1 + max(0, self.token_retry)):
                info = self._matchmaker()
                if info is not None or not self._token_refused:
                    break
                if try_n < self.token_retry:
                    self.log(f'[token] rotating to the next candidate '
                             f'({try_n + 1}/{self.token_retry})')
        if info is None:
            self.log('[!] could not reach an arena')
            return False
        host, port, node_token = info
        self.node_token = node_token

        if host == PARTY_HOLD:
            self.log('[party] holding matchmaker session (no play)')
            return True

        if host == INLINE_ARENA:
            # The matchmaker is hosting the arena on the socket we already
            # hold: no node to dial, no mt=40 join, the world is already
            # streaming into q_mm.  Point the play loop at that socket.
            self.arena = self.mm
            self.q_ar = self.q_mm
            self.ar_closed = self.mm_closed
            try:
                self.arena_host, self.arena_port = self.mm.getpeername()[:2]
            except OSError:
                self.arena_host, self.arena_port = self.host, MM_PORT
            self.log(f'[arena] playing inline on {self.arena_host}:'
                     f'{self.arena_port}')
            if not self._announce_world():
                if getattr(self, '_fleet_wrong_room', False):
                    self.log('[play] wrong fleet ROOM on inline — fresh login '
                             '(pin kept, non-drop)')
                return False
        elif not self._arena(host, port, node_token, None):
            # Prefer SAME-token reconnect first (player behaviour on
            # "Connecting…").  Only then mash mt=110 for a fresh redirect.
            #
            # Skip the whole same-token budget when _arena() told us the node
            # answered with a redirect back to a host we had already dialled:
            # the bearer token is stale, and 5 redials + 24 mt=110 re-enters on
            # a stale token is exactly the loop that filled bot_run.log with
            # `[arena] reader exit eof total=192b` while the bot never spawned.
            if getattr(self, '_fleet_wrong_room', False):
                self.log('[play] wrong fleet ROOM — fresh login (pin kept, '
                         'non-drop)')
                return False
            played_arena = False
            same_token = node_token
            same_host, same_port = host, port
            if self._arena_token_bounced:
                self.log('[play] node rejected this token (refused or bounced '
                         'between nodes) — skipping same-token redials, asking '
                         'for a fresh mt=33')
            else:
                for same_try in range(1, 6):
                    if self.mm is None or self.mm_closed.is_set():
                        break
                    self.log(f'[play] connecting — same token redial '
                             f'({same_try}/5) {same_host}:{same_port}')
                    time.sleep(0.3)
                    if self._arena(same_host, same_port, same_token, None):
                        played_arena = True
                        break
                    if self._arena_token_bounced:
                        break
            # Arena full / connecting: mash Play hard (same as humans).
            for retry in range(1, 1000):
                if played_arena:
                    break
                if self.mm is None or self.mm_closed.is_set():
                    self.log(f'[play] cannot re-enter on this session — '
                             f'matchmaker '
                             f'{"socket closed" if self.mm_closed.is_set() else "gone"}'
                             f'; a fresh login is the only way forward')
                    break
                if retry <= 3 or retry % 20 == 0:
                    self.log(f'[play] still connecting — mash mt=110 '
                             f'({retry}/1000)')
                try:
                    if (self.code and not self.no_party and retry % 8 == 1):
                        self.send(self.mm, pkt_party(self.code),
                                  f'party mt=27 "{self.code}" (reenter keep)')
                    if getattr(self, 'boost_every_play', False) and retry == 1:
                        self._arm_boosts_before_play(self.q_mm)
                    _pn = (self.nick or '').strip() or 'b'
                    self.send(self.mm, self.play_pkt(_pn),
                              f'play mt=110 reenter {retry}',
                              silent=(retry > 3 and retry % 20 != 0))
                except Exception:
                    break
                got = self._wait_for(
                    self.q_mm,
                    lambda m, w: m.mt in (33, 52) or m.mt == 88 or w.me is not None,
                    0.7, 'mt=33/52 reenter',
                    closed=self.mm_closed, quiet=True, log_frames=False)
                if got is not None and got.mt == 52:
                    if retry == 1 or retry % 10 == 0:
                        self.log(f'[play] arena FULL (mt=52) — keep mashing, do not leave '
                                 f'{retry}/1000')
                    time.sleep(0.05)
                    continue
                if got is None or got.mt not in (33, 88):
                    time.sleep(0.05)
                    continue
                if got.mt == 88 or self.world.me is not None:
                    self.arena = self.mm
                    self.q_ar = self.q_mm
                    self.ar_closed = self.mm_closed
                    played_arena = True
                    break
                f39 = one(got.inner, 39)
                if f39 is None:
                    continue
                f = fields(f39)
                host = as_str(one(f, 2))
                port = int(one(f, 3) or NODE_PORT)
                node_token = as_str(one(f, 1))
                pin = _read_party_arena_pin()
                # In party mode, party code groups bots — never drop session on host difference!
                _hunt_pin = bool(
                    (not self.code or self.no_party)
                    and pin and pin.get('seen_target') and host and pin.get('host')
                    and _is_pinable_arena_host(host)
                    and _is_pinable_arena_host(pin['host'])
                    and not _same_arena_host(host, pin['host']))
                if _hunt_pin:
                    self.log(f'[play] reenter {host} != pin {pin["host"]} '
                             f'— drop for fresh login (pin kept)')
                    return False
                if host and self._arena(host, port, node_token, None):
                    played_arena = True
                    break
            if not played_arena:
                return False

        # `--run` counts seconds actually spent playing, not connection setup
        deadline = time.time() + self.run_s
        # Arm the last-resort stall bypass before the loop can park itself.
        self._start_stall_watchdog()
        self._calibrate(deadline)
        if self.mode == 'follow' and self.follow:
            self.log(f'[mode] FOLLOW {self.follow!r} brain=v3-autolearn '
                     f'(party-aware dive+lock, auto-learn ON, '
                     f'split-feed={"on" if self.split_feed else "off"})')
            if _follow_train is not None:
                try:
                    tp = _follow_train.force_reload()
                    self.log(f'[train] v3 loaded split_mass={tp["split_mass"]:g} '
                             f'deliver={tp["deliver_range"]:g} '
                             f'dive={tp["dive_pad"]:g} '
                             f'commit_boost={tp.get("commit_boost", 0):g} '
                             f'sticky={tp["avoid_sticky_s"]:g}s')
                except Exception as e:
                    self.log(f'[train] load fail: {e}')
            play_fn = self._play_follow
        elif self.mode == 'leave':
            self.log(f'[mode] LEAVE (enter arena -> feed -> leave arena loop'
                     + (f', target={self.follow!r}' if self.follow else '') + ')')
            play_fn = self._play_leave
        else:
            play_fn = self._play
        state = play_fn(deadline)

        # ---- soft-bail recovery: re-dial the SAME node, not the matchmaker --
        # `[pin]` / `[stale]` return 'closed' from _bail_arena() with the MM
        # session + bearer still good — same-node redial matches the app's
        # "Connecting…" mash.  wrong-arena sets _arena_token_bounced so this
        # loop is skipped (re-landing on the wrong EC2 is how the operator
        # only ever saw ~3 bots).
        _soft = 0
        while (state == 'closed' and self.respawn
               and node_token and host not in ('', INLINE_ARENA, PARTY_HOLD)
               and not self._arena_token_bounced
               and _soft < SOFT_REDIALS
               and time.time() < deadline
               and self.mm is not None and not self.mm_closed.is_set()):
            _soft += 1
            time.sleep(0.8 * _soft)
            self.log(f'[play] soft bail — same-node redial {_soft}/{SOFT_REDIALS} '
                     f'{host}:{port} (no re-login)')
            self.world = World()
            self.brain = Brain(self.strategy)
            self.hmap = HeadingMap()
            if not self._arena(host, port, node_token, None):
                continue
            self._calibrate(deadline)
            state = play_fn(deadline)

        # ---- INLINE soft remash: death/bail must NOT Round-finished re-login
        # Arena was MM; _bail_arena kept MM open. Re-attach + mash play.
        # Skip when wrong fleet ROOM — remashing the same MM re-enters the
        # wrong Burst map; fresh login is the only way to hunt the pin.
        _inline = 0
        while (state == 'closed' and self.respawn
               and host == INLINE_ARENA
               and not self._arena_token_bounced
               and not getattr(self, '_fleet_wrong_room', False)
               and _inline < SOFT_REDIALS
               and time.time() < deadline
               and self.mm is not None and not self.mm_closed.is_set()):
            _inline += 1
            self.log(f'[play] soft bail — inline remash {_inline}/{SOFT_REDIALS} '
                     f'(no re-login)')
            self.world = World()
            self.brain = Brain(self.strategy)
            self.hmap = HeadingMap()
            self.arena = self.mm
            self.q_ar = self.q_mm
            self.ar_closed = self.mm_closed
            self._inline_need_reenter = False
            self._want_play = True
            self._death_ask_n = 0
            self._death_play_n = 0
            # mt=12 then mash mt=110 until we have a cell (or give up this try).
            try:
                self._arena_send(pkt_respawn())
            except Exception:
                pass
            time.sleep(0.25)
            got_cell = False
            t_end = time.time() + 8.0
            while time.time() < t_end and not self.mm_closed.is_set():
                self._mash_play_after_death()
                self._pump_arena()
                me = self.world.me
                if me is not None and not self.world.dead:
                    got_cell = True
                    break
                time.sleep(0.15)
            if not got_cell:
                self.log('[play] inline remash — no cell yet, mash again')
                continue
            self.log(f'[play] inline remash OK id={self.world.self_id} '
                     f'mass={self.world.me.mass:.0f}')
            self._calibrate(deadline)
            state = play_fn(deadline)

        while state == 'dead' and self.respawn and time.time() < deadline:
            if not self.world.dead:
                # We only got here on the 2.5 s timeout, i.e. no explicit
                # eat-pair arrived -- count the death ourselves so the tally
                # is still right.  Normally the server re-spawns us within a
                # second and _play never returns 'dead' at all.
                self.world.deaths += 1
                self.world.dead = True
            self.log(f'[death] #{self.world.deaths} killed_by='
                     f'{self.world.killed_by} at mass '
                     f'{self.world.peak_mass:.0f}')
            if self._respawn(deadline):
                state = play_fn(deadline)
            else:
                if self.mode == 'follow' and self.arena is not None and not self.ar_closed.is_set():
                    try:
                        nick = (self.nick or '').strip() or 'b'
                        self._arena_send(self.play_pkt(nick))
                    except Exception:
                        pass
                    time.sleep(0.5)
                    continue
                # Do NOT stay in 'dead' — that used to re-enter this loop / leave
                # the party slot empty while mt=12 spam ran on a closed socket.
                state = 'closed'
                break

        st = self.world.stats()
        self.log(f'[done] state={state} mass={st["mass"]} ate={st["ate"]} '
                 f'deaths={st["deaths"]} lives={st["lives"]} '
                 f'peak={st["peak_mass"]} feeds={self.feeds} '
                 f'splits={self.splits} leaves={self.leaves}')
        self.event('finished', **st)
        return True

    def close(self):
        self._stop.set()
        for s in (self.mm, self.arena):
            try:
                if s:
                    s.close()
            except Exception:
                pass
        self.mm = self.arena = None


# --------------------------------------------------------------------------- #
# self test — every outbound packet must match a real capture byte-for-byte
# --------------------------------------------------------------------------- #

# (name, produced bytes, captured bytes from bot/capture-*.json)
_GOLDEN = [
    ('mt=70  hello',    lambda: pkt_hello(),                 '10021a08d203021000e80646'),
    ('mt=119 hello2',   lambda: pkt_hello2(),                '10021a06e80677fa0600'),
    ('mt=23  ack',      lambda: pkt_ack23(),                 '10021a03e80617'),
    ('mt=50  joy 0,0',  lambda: pkt_joy(0.0, 0.0),           '10021a10aa030a15000000001d00000000e80632'),
    ('mt=50  joy x,y',  lambda: pkt_joy(0.30608433, 0.63486475),
                                                             '10021a10aa030a1516b79c3e1d7f86223fe80632'),
    ('mt=40  join',     lambda: pkt_node_join('47850046.1789920786090'),
     '10021a1eda03180a1634373835303034362e31373839393230373836303930e80628'),
    ('mt=94  boost',    lambda: pkt_mass_boost(),            '10021a188202120a106d6173735f626f6f73745f33785f3168e8065e'),
    ('mt=110 play',     lambda: pkt_play(),                  '10021a0a820604080d1200e8066e'),
    ('mt=110 play nick', lambda: pkt_play('Prince'),         '10021a1082060a080d12065072696e6365e8066e'),
    ('mt=12  respawn',  lambda: pkt_respawn(),               '10021a03e8060c'),
    ('mt=27  party',    lambda: pkt_party('CYDS3S'),         '10021a0e9a06080a06435944533353e8061b'),
    ('mt=104 pong',     lambda: pkt_pong(187505746),         '10021a0bc2060508d2b8b459e80668'),
    # official client, capture-node-6/3 (2026-09-24)
    ('mt=69  feed',     lambda: pkt_feed(),                  '10021a06f20100e80645'),
    ('mt=47  split',    lambda: pkt_split(),                 '10021a06920500e8062f'),
    ('mt=80  leave',    lambda: pkt_leave_game(),            '10021a03e80650'),
    ('mt=111 continue', lambda: pkt_continue(),              '10021a08ba01020801e8066f'),
]


def selftest() -> int:
    bad = 0
    for name, fn, want in _GOLDEN:
        got = fn().hex()
        ok = got == want
        if not ok:
            bad += 1
        print(f'  {"OK " if ok else "BAD"} {name}')
        if not ok:
            print(f'      want {want}')
            print(f'      got  {got}')
    # login: compare the *decoded* structure (opcode-2 plain, or opcode-1 zlib)
    blob = pkt_login('TESTTOKEN')
    m = decode_frame(blob)
    raw = one(m.top, 3) if m.op == 2 else zlib.decompress(one(m.top, 4))
    inner = fields(raw)
    ok = (one(inner, 109) == 51
          and as_str(one(fields(one(inner, 85) or b''), 1)) == 'TESTTOKEN')
    print(f'  {"OK " if ok else "BAD"} mt=51  login (decoded)')
    bad += 0 if ok else 1
    print('  all good' if not bad else f'  {bad} FAILED')
    return bad


# --------------------------------------------------------------------------- #
# offline replay (brain/world validation without a network)
# --------------------------------------------------------------------------- #

def replay(path: str, strategy='balanced', step=1):
    d = json.load(open(path))
    w = World()
    b = Brain(strategy)
    from collections import Counter
    hist = Counter()
    print(f'[replay] {path}  c2s={len(d["c2s"])} s2c={len(d["s2c"])}')
    shown = 0
    for i, x in enumerate(d['s2c']):
        if i % step:
            continue
        body = bytes.fromhex(x['hex'])
        try:
            m = decode_frame(body)
        except Exception:
            continue
        kind = w.apply(m)
        if kind in ('snapshot', 'own'):
            me = w.me
            print(f'  [{kind}] arena={w.arena:.0f} entities={len(w.entities)} '
                  f'self={w.self_id} score={w.score} color={w.color}')
        if kind == 'leaderboard':
            top = ', '.join(f'{n or "?"}:{s}' for n, s in w.leaderboard[:3])
            print(f'  [leaderboard] rank={w.rank} our score={w.score}  '
                  f'top3 {top}')
        if w.me is None:
            continue
        if i % max(1, step * 8) == 0:
            h = b.decide(w, time.time())
            hist[b.mode.split()[0]] += 1
            me = w.me
            print(f'  #{i:5d} {kind:10s} mass={me.mass:6.1f} ({me.x:6.0f},{me.y:6.0f}) '
                  f'{b.mode:18s} head=({h[0]:+.2f},{h[1]:+.2f}) '
                  f'food={len(w.food())} cells={len(w.cells())} '
                  f'ate={w.ate} peak={w.peak_mass:.0f}')
            shown += 1
    print(f'[replay] decisions={shown} modes={dict(hist)}')
    print(f'[replay] final: {w.stats()}')


# --------------------------------------------------------------------------- #
# config file
# --------------------------------------------------------------------------- #
# `bot.ini` next to this script is loaded automatically, so editing it and
# running `python agar_bot.py` is enough -- no flags to remember.  Command-line
# flags still win over the file, so a one-off run does not need an edit.
#
# INI rather than JSON because it takes comments: the useful thing to write
# beside `region` is the list of regions, and beside `code` is the reminder that
# codes are region-scoped.
DEFAULT_CONFIG = os.path.join(HERE, 'bot.ini')

# section -> {ini key: (argparse dest, type)}
CONFIG_SPEC = {
    'game': {
        'region': ('region', str),
        'code': ('code', str),
        'nick': ('nick', str),
        'token': ('token', str),
    },
    'play': {
        'run': ('run', int),
        'strategy': ('strategy', str),
        'tick': ('tick', float),
        'no_party': ('no_party', bool),
        'no_respawn': ('no_respawn', bool),
        'no_calibrate': ('no_calibrate', bool),
        'forever': ('forever', bool),
    },
    'network': {
        'prefer': ('prefer', str),
        'proxy': ('proxy', str),
        'proxy_protocol': ('proxy_protocol', str),
        'proxy_file': ('proxy_file', str),
        'proxy_index': ('proxy_index', int),
        'attempts': ('attempts', int),
        'mm_tries': ('mm_tries', int),
        'mm_wait': ('mm_wait', float),
        'token_retry': ('token_retry', int),
    },
    'output': {
        'stats_json': ('stats_json', str),
        'quiet': ('quiet', bool),
        'dump': ('dump', bool),
    },
}

# Blanks in these mean "explicitly off" -- most importantly a blank party code,
# which is how you switch back to a public game.
_BLANK_MEANS_NONE = {'code', 'nick', 'token', 'proxy', 'proxy_file', 'stats_json'}

_TRUE = ('1', 'true', 'yes', 'on')
_FALSE = ('0', 'false', 'no', 'off')

# argparse does NOT validate defaults against `choices`, so a typo in the file
# would otherwise be accepted silently and do something surprising later.
_CHOICES = {
    'strategy': ('balanced', 'farm', 'hunt'),
    'prefer': ('auto', 'ipv6', 'ipv4'),
    'proxy_protocol': ('auto', 'socks5', 'http'),
}


def load_config(path: str) -> dict:
    """Read an INI file into a dict of argparse defaults.

    Raises SystemExit with a message naming the file, section and key on any
    problem -- a config file that silently ignores a line is worse than one that
    refuses to start.
    """
    cp = configparser.ConfigParser(interpolation=None)
    try:
        with open(path, encoding='utf8') as fh:
            cp.read_file(fh)
    except OSError as e:
        raise SystemExit(f'[config] cannot read {path}: {e}')
    except configparser.Error as e:
        raise SystemExit(f'[config] {os.path.basename(path)} is not valid INI: '
                         f'{e}')

    base = os.path.basename(path)
    out: dict = {}
    for section, keys in CONFIG_SPEC.items():
        if not cp.has_section(section):
            continue
        for key, (dest, typ) in keys.items():
            if not cp.has_option(section, key):
                continue
            raw = cp.get(section, key).strip()
            if len(raw) >= 2 and raw[0] == raw[-1] and raw[0] in '"\'':
                raw = raw[1:-1].strip()

            if raw == '':
                if dest in _BLANK_MEANS_NONE:
                    out[dest] = None
                elif dest == 'region':
                    raise SystemExit(f'[config] {base}: [game] region cannot '
                                     f'be blank -- pick one, e.g. '
                                     f'ap-south-1')
                continue                      # blank = use the built-in default

            try:
                if typ is bool:
                    low = raw.lower()
                    if low not in _TRUE + _FALSE:
                        raise ValueError
                    out[dest] = low in _TRUE
                elif typ is int:
                    out[dest] = int(raw)
                elif typ is float:
                    out[dest] = float(raw)
                else:
                    out[dest] = raw
            except ValueError:
                want = ('true/false' if typ is bool
                        else 'a whole number' if typ is int
                        else 'a number' if typ is float
                        else 'text')
                raise SystemExit(f'[config] {base}: [{section}] {key} = '
                                 f'{raw!r} is not {want}')

    for dest, allowed in _CHOICES.items():
        if dest in out and out[dest] not in allowed:
            raise SystemExit(f'[config] {base}: {out[dest]!r} is not one of '
                             f'{", ".join(allowed)}')
    return out


def describe_config(cfg: dict) -> str:
    """One-line summary of what the file actually set, for the startup log."""
    if not cfg:
        return 'nothing (all built-in defaults)'
    return '  '.join(f'{k}={v!r}' for k, v in sorted(cfg.items()))


def show_config(path, cfg: dict, a) -> str:
    """The effective settings, after the file and the command line are merged."""
    lines = [f'config file : {path or "(none)"}',
             f'file sets   : {describe_config(cfg)}', '',
             'effective (command-line flags override the file):']
    for name in ('region', 'code', 'nick', 'run', 'strategy', 'tick',
                 'no_party', 'no_respawn', 'no_calibrate', 'forever',
                 'attempts', 'mm_tries', 'mm_wait', 'prefer', 'proxy',
                 'proxy_protocol', 'proxy_file', 'proxy_index', 'token_retry',
                 'stats_json', 'quiet', 'dump'):
        v = getattr(a, name, None)
        if name == 'token' and v:
            v = f'<{len(v)} chars>'
        lines.append(f'  {name:<15s} = {v!r}')
    return '\n'.join(lines)


# --------------------------------------------------------------------------- #
# CLI
# --------------------------------------------------------------------------- #

def main():
    global FLEET_TARGET_MAX_AGE
    global AREA_MEMORY
    ap = argparse.ArgumentParser(description='Agar.io mobile bot')
    ap.add_argument('--region', default='ap-south-1',
                    help='region prefix, e.g. ap-south-1 (or a full hostname)')
    ap.add_argument('--interactive', '-i', action='store_true',
                    help='interactive prompt to choose region, enter party code, and start')
    ap.add_argument('--code', default=None, help='party code to join (optional)')
    ap.add_argument('--leave-party', action='store_true',
                    help='leave current party and switch to solo play')
    ap.add_argument('--party-status', action='store_true',
                    help='check and display whether account is currently in a party, then exit')
    ap.add_argument('--join-then-leave', action='store_true',
                    help='join --code, then leave that party and exit without playing')
    ap.add_argument('--nick', default=None)
    ap.add_argument('--run', type=int, default=60, help='seconds to play')
    ap.add_argument('--token', default=None, help='base64 auth token (else auto)')
    ap.add_argument('--guest-v6', action='store_true',
                    help='azhar v6 LOGIN_ENC (no persist remint) — ap-south default')
    ap.add_argument('--tokens', action='store_true',
                    help='list every token on disk with its freshness and '
                         'whether it has been refused, then exit')
    ap.add_argument('--reset-tokens', action='store_true',
                    help='clear the refused-token ledger (use after a throttle '
                         'has decayed) and then continue')
    ap.add_argument('--token-retry', type=int, default=0,
                    help='extra dials to spend rotating onto a fresh token when '
                         'the matchmaker refuses one (default 0: the ledger '
                         'rotates the *next* run instead, which is gentler)')
    ap.add_argument('--strategy', default='balanced',
                    choices=['balanced', 'farm', 'hunt'])
    ap.add_argument('--mode', default='play', choices=['play', 'follow', 'leave'],
                    help='play: normal bot.  follow: shadow --follow player and '
                         'give them mass (split + 2 feeds).  leave: farm, eject '
                         'everything, leave game (mt=80), repeat')
    ap.add_argument('--follow-name', default=None, metavar='NICK',
                    help='operator in-game nick (backup lock when uuid FOV miss)')
    ap.add_argument('--follow', default=None, metavar='UID',
                    help='player to follow / feed: account uuid (or prefix), '
                         'party member name (Guest_123...) or nick.  Implies '
                         '--mode follow unless --mode leave is given')
    ap.add_argument('--auto-target', action='store_true',
                    help='let a follower pick its target out of the party '
                         'roster when --follow matches nothing.  Off by '
                         'default: a wrong guess makes bots chase each other.')
    ap.add_argument('--arena-host', default=None,
                    help='arena-only: connect straight to this arena node '
                         '(from a captured mt=33 redirect), skipping the MM login')
    ap.add_argument('--arena-port', type=int, default=9001)
    ap.add_argument('--arena-token', default=None,
                    help='arena-only: bearer node token (serverId.epoch) from mt=33')
    ap.add_argument('--feed-keep', type=float, default=45.0, metavar='MASS',
                    help='follow-mode: never eject below this mass (default 45)')
    ap.add_argument('--leave-at', type=float, default=150.0, metavar='MASS',
                    help='leave-mode: dump + leave once mass reaches this (default 150)')
    ap.add_argument('--cycle', type=float, default=90.0, metavar='SEC',
                    help='leave-mode: max seconds farming per cycle (default 90)')
    ap.add_argument('--require-proxy', action='store_true',
                    help='never dial from this PC directly: if no SOCKS is '
                         'available the bot refuses instead of going direct')
    ap.add_argument('--sticky-proxy', action='store_true',
                    help='keep the assigned --proxy on refuse (no rotate '
                         'through proxies_live). Use with bots-per-proxy fleets')
    ap.add_argument('--threat-radius', type=float, default=350.0, metavar='DIST',
                    help='follow-mode: dodge any eater within this distance '
                         '(default 350; reference bot uses 900)')
    ap.add_argument('--enemy-clearance', default='1', metavar='LEVEL_OR_UNITS',
                    help='follow-mode clearance level for enemy skirting: '
                         '1 or "chipak" (15u margin, ultra-tight razor skimming), '
                         '2 or "close" (25u margin), '
                         '3 or "normal" (40u margin), '
                         '4 or "safe" (65u margin), '
                         '5 or "wide" (100u margin), '
                         'or custom numeric margin in game units.')
    ap.add_argument('--safe-mass', type=float, default=90.0, metavar='MASS',
                    help='follow-mode: farm locally until this mass before '
                         'travelling to the target (default 90)')
    ap.add_argument('--fix-ttl', type=float, default=FLEET_TARGET_MAX_AGE,
                    metavar='SEC', dest='fix_ttl',
                    help='follow-mode: how long a sighting of the target stays '
                         'good enough to walk to (default 60).  Longer keeps the '
                         'fleet converging on stale ground; shorter makes it '
                         'search more.  The search itself is always centred on '
                         'the last known area for AREA_MEMORY seconds either way.')
    ap.add_argument('--area-memory', type=float, default=AREA_MEMORY,
                    metavar='SEC', dest='area_memory',
                    help='follow-mode: how long the LAST KNOWN AREA keeps being '
                         'the centre of the search after the fix itself has gone '
                         'stale (default 240, config `area-memory`).  This is the '
                         'knob that decides "does the whole fleet keep walking '
                         'back to where it last saw the operator" (long) versus '
                         '"does it scatter over the whole map looking" (short). '
                         'Once this expires the bots fall back to a per-bot '
                         'sector sweep of the entire arena.')
    ap.add_argument('--close-range', type=float, default=1500.0, metavar='DIST',
                    dest='close_range',
                    help='follow-mode: once the target is visible inside this '
                         'range, walk to them at ANY mass instead of waiting to '
                         'grow to --safe-mass (default 1500).  Set 0 to restore '
                         'the old "must reach safe-mass first" behaviour.')
    ap.add_argument('--boost', default='1', metavar='0|1',
                    help='send mt=94 mass_boost_3x_1h before play even when the '
                         'wallet shows no count (app does it; spawn becomes ~132)')
    ap.add_argument('--boost-items', default='mass_boost_3x_24h,xp_boost_3x_24h',
                    metavar='A,B', dest='boost_items',
                    help='comma-separated boost items to arm before play '
                         '(default "mass_boost_3x_24h,xp_boost_3x_24h").  The '
                         'game catalogue (APK GameConfiguration.json, section '
                         '"Gameplay - Boosts") has separate `xp` and `mass` '
                         'types -- mass alone does not level you up.  Also '
                         'available: xp_boost_3x_24h, mass_boost_3x_24h, '
                         'xp_boost_2x_1h, mass_boost_2x_1h, token_boost_2x_2h.')
    ap.add_argument('--boost-every-play', action='store_true',
                    dest='boost_every_play',
                    help='re-arm the boosts before EVERY mt=110 play request, '
                         'not just the first dial.  The request then always '
                         'goes out "as if the boost were taken" -- which is '
                         'what an account that owns the item looks like on the '
                         'wire.  Whether the server GRANTS it still depends on '
                         'the wallet, so read the mt=43 echo, not the send.')
    ap.add_argument('--no-split-feed', action='store_true',
                    help='follow-mode: only eject pellets, never split toward the target')
    ap.add_argument('--arena-mode', default='classic',
                    choices=('classic', 'burst'),
                    help='playlist: classic (game_type 13) or burst (captured id, usually 7)')
    ap.add_argument('--game-type', type=int, default=0,
                    help='mt=110 f96.f1 override (0 = resolve from --arena-mode)')
    ap.add_argument('--tick', type=float, default=TICK)
    ap.add_argument('--no-party', action='store_true', help='skip the mt=27 join')
    ap.add_argument('--no-calibrate', action='store_true')
    ap.add_argument('--no-respawn', action='store_true')
    ap.add_argument('--forever', action='store_true',
                    help='retry until it plays (default: up to --attempts)')
    ap.add_argument('--attempts', type=int, default=1,
                    help='session attempts before giving up (default 1).  The '
                         'matchmaker throttles a source that reconnects often '
                         'and every attempt spends budget, so one shot is the '
                         'safe default -- raise this only when you know the '
                         'source is clean')
    ap.add_argument('--mm-tries', type=int, default=1,
                    help='matchmaker dial retries per session (default 1; '
                         'lower = gentler on the rate limiter)')
    ap.add_argument('--mm-wait', type=float, default=10.0,
                    help='base seconds between matchmaker retries (doubles each time)')
    ap.add_argument('--prefer', default='auto', choices=('auto', 'ipv6', 'ipv4'),
                    help='pin the address family for the matchmaker; the two '
                         'families present different source IPs and are '
                         'throttled separately, so this is the escape hatch '
                         'when one path has been rate-limited')
    ap.add_argument('--proxy', default=None,
                    help="tunnel through a proxy: '[user:pass@]host:port'. "
                         'The matchmaker throttles per source IP, so a proxy '
                         'presents a different source.  SOCKS5 or HTTP CONNECT')
    ap.add_argument('--proxy-protocol', default='auto',
                    choices=('auto', 'socks5', 'http'),
                    help='tunnel protocol (default: try SOCKS5 then HTTP)')
    ap.add_argument('--proxy-file', default=None,
                    help='read proxies from a file: "host:port user pass" per '
                         'line.  NOTE this file holds credentials')
    ap.add_argument('--proxy-index', type=int, default=0,
                    help='which entry of --proxy-file to use (default 0).  '
                         'One proxy, one attempt -- see the rate-limit note')
    ap.add_argument('--stats-json', default=None, help='write live stats here')
    ap.add_argument('--dump', action='store_true', help='log every world change')
    ap.add_argument('--replay', default=None, help='offline: run the brain on a capture')
    ap.add_argument('--selftest', action='store_true', help='check packet encoders')
    ap.add_argument('--quiet', action='store_true')
    ap.add_argument('--config', default=None, metavar='FILE',
                    help=f'read settings from an INI file (default: '
                         f'{os.path.basename(DEFAULT_CONFIG)} next to this '
                         f'script, if it exists).  Command-line flags override '
                         f'the file')
    ap.add_argument('--no-config', action='store_true',
                    help='ignore the config file entirely and use built-in '
                         'defaults')
    ap.add_argument('--show-config', action='store_true',
                    help='print the effective settings, merged from the file '
                         'and the command line, then exit')

    # Pre-scan for --config/--no-config only, so the file can supply the
    # defaults for every other flag.  parse_known_args is safe here: it
    # validates the flags defined so far, and the real parse is below.
    pre, _ = ap.parse_known_args()
    cfg_path, cfg = None, {}
    if not pre.no_config:
        cfg_path = pre.config
        if cfg_path is None and os.path.exists(DEFAULT_CONFIG):
            cfg_path = DEFAULT_CONFIG
        if cfg_path:
            cfg = load_config(cfg_path)
            ap.set_defaults(**cfg)

    a = ap.parse_args()

    # The fix window is read by module-level helpers (_fleet_target_sighting),
    # so it has to be published as a global rather than passed down.
    if a.fix_ttl and a.fix_ttl > 0:
        FLEET_TARGET_MAX_AGE = float(a.fix_ttl)
    if getattr(a, 'area_memory', 0) and a.area_memory > 0:
        AREA_MEMORY = float(a.area_memory)

    if a.show_config:
        print(show_config(cfg_path, cfg, a))
        return

    # The offline/lookup modes below never connect, so the config banner would
    # be noise in front of their output -- e.g. a token table.  It is printed
    # further down, once we are actually about to dial.
    if a.selftest:
        sys.exit(1 if selftest() else 0)

    if a.reset_tokens:
        _ledger_save({})
        print(f'[token] cleared {TOKEN_LEDGER}')

    if a.tokens:
        print(token_report())
        return

    if a.replay:
        replay(a.replay, a.strategy)
        return

    # Interactive menu for region and party code
    if a.interactive or (len(sys.argv) == 1 and sys.stdin.isatty()):
        REGION_MENU = [
            ('1', 'ap-south-1', 'India / South Asia (Default)'),
            ('2', 'ap-southeast-1', 'Singapore'),
            ('3', 'eu-central-1', 'Europe (Frankfurt)'),
            ('4', 'us-east-1', 'US East (N. Virginia)'),
            ('5', 'us-west-1', 'US West (N. California)'),
            ('6', 'eu-west-2', 'London'),
            ('7', 'ap-northeast-1', 'Tokyo'),
        ]
        print('\n' + '='*55)
        print('         AGAR.IO BOT (Custom Setup)')
        print('='*55)
        print('\nAvailable Regions:')
        for num, reg_code, reg_desc in REGION_MENU:
            print(f'  {num}. {reg_code:<16} - {reg_desc}')
        print('  8. Other / Custom Host')

        try:
            reg_choice = input('\nChoose Region [1-8] (Press Enter for ap-south-1): ').strip()
            if reg_choice:
                matched = False
                for num, reg_code, _ in REGION_MENU:
                    if reg_choice == num or reg_choice.lower() == reg_code.lower():
                        a.region = reg_code
                        matched = True
                        break
                if not matched:
                    if reg_choice == '8':
                        custom_reg = input('Enter custom region code/host: ').strip()
                        if custom_reg:
                            a.region = custom_reg
                    else:
                        a.region = reg_choice

            pcode = input('Enter Party Code to join (or Enter for solo, or type LEAVE to leave party): ').strip()
            if pcode.upper() == 'LEAVE':
                a.leave_party = True
                a.code = None
            elif pcode:
                a.code = pcode.upper()

            pnick = input('Enter Bot Nickname (or press Enter for default): ').strip()
            if pnick:
                a.nick = pnick

            prun = input(f'Enter Run Time in seconds (Press Enter for {a.run}s): ').strip()
            if prun and prun.isdigit():
                a.run = int(prun)

            print(f"\n[+] Configured: Region = {a.region} | Party Code = {a.code or '(Solo)'} | Run = {a.run}s\n")
        except (EOFError, KeyboardInterrupt):
            print('\nCancelled.')
            return

    if cfg_path:
        print(f'[config] {os.path.basename(cfg_path)} -> region={a.region} '
              f'code={a.code or "(none)"} run={a.run}s', flush=True)

    stats_path = a.stats_json

    def _proxy_from_file(path, index):
        entries = []
        for line in open(path, encoding='utf8'):
            line = line.split('#')[0].strip()
            if not line:
                continue
            parts = line.split()
            if len(parts) >= 3:                 # host:port  user  pass
                entries.append(f'{parts[1]}:{parts[2]}@{parts[0]}')
            else:                               # already [user:pass@]host:port
                entries.append(parts[0])
        if not entries:
            raise SystemExit(f'no proxies found in {path}')
        if not 0 <= index < len(entries):
            raise SystemExit(f'--proxy-index {index} out of range; '
                             f'{path} has {len(entries)} entr(y/ies)')
        return entries[index]

    proxy_spec = a.proxy
    if not proxy_spec and a.proxy_file:
        proxy_spec = _proxy_from_file(a.proxy_file, a.proxy_index)
    if proxy_spec:
        ph, pp, pu, _pw = parse_proxy(proxy_spec)
        print(f'[proxy] tunnelling via {ph}:{pp}'
              f'{f" as {pu}" if pu else ""} ({a.proxy_protocol})', flush=True)

    def on_stats(st):
        if stats_path:
            try:
                json.dump(st, open(stats_path, 'w'), indent=1)
            except Exception:
                pass

    bot_state = {
        'bot': None,
        'stop': False,
        'region': a.region,
        'code': a.code,
        'leave_requested': a.leave_party,
    }

    # File-based live control (Discord panel) — works even with stdin=DEVNULL.
    if _live_ctrl is not None:
        try:
            _live_ctrl.start_poller(bot_state)
            print(f'[live] watching {_live_ctrl.ctrl_path()}', flush=True)
        except Exception as e:
            print(f'[live] poller fail: {e}', flush=True)

    # Live command listener thread for runtime commands (leave, join, region, status, exit)
    if sys.stdin.isatty() or a.interactive:
        print('\n' + '='*62)
        print('         AGAR.IO BOT CONTROLLER & LIVE MONITOR')
        print('='*62)
        print(f'  [Current Region] : {bot_state["region"]}')
        print(f'  [Party Status]   : {"JOIN: " + bot_state["code"] if bot_state["code"] else "SOLO (No Party)"}')
        print(f'  [Nickname]       : {a.nick or "Guest"}')
        print('-'*62)
        print('  LIVE COMMANDS (Type anytime in terminal while running):')
        print('    leave          - Instantly LEAVE party & switch to Solo')
        print('    join <CODE>    - JOIN party code (e.g. join 3WB7AV)')
        print('    region <REG>   - Switch region (e.g. region ap-southeast-1)')
        print('    status         - Display full Region, Party & Game status')
        print('    feed [n]       - Eject mass n times (mt=69) toward current heading')
        print('    split          - Split (mt=47);  splitfeed = split + 2 feeds')
        print('    follow <UID>   - Follow-bot: shadow & feed this player (uuid/Guest_x/nick)')
        print('    leavegame      - Leave the match like the app (mt=80)')
        print('    exit / quit    - Stop bot and exit cleanly')
        print('='*62 + '\n', flush=True)

        def _console_listener():
            while not bot_state['stop']:
                try:
                    line = sys.stdin.readline()
                    if not line:
                        break
                    cmd = line.strip()
                    if not cmd:
                        continue
                    parts = cmd.split()
                    op = parts[0].lower()

                    if op in ('help', '?'):
                        print('\n' + '='*56)
                        print('              LIVE COMMANDS HELP')
                        print('='*56)
                        print('  leave          : Instantly LEAVE party & play Solo')
                        print('  join <CODE>    : JOIN party code (e.g. join 3WB7AV)')
                        print('  region <REG>   : Switch region (e.g. region ap-southeast-1)')
                        print('  status         : Print current Region, Party & Stats')
                        print('  exit / quit    : Stop bot and exit cleanly')
                        print('='*56 + '\n', flush=True)
                    elif op == 'status':
                        b = bot_state.get('bot')
                        if b:
                            b.print_status()
                        else:
                            p_str = f"JOINED in {bot_state.get('code')}" if bot_state.get('code') else "SOLO"
                            print(f"\n[STATUS] Region: {bot_state.get('region')} | Party: {p_str}\n", flush=True)
                    elif op == 'leave':
                        bot_state['code'] = None
                        bot_state['leave_requested'] = True
                        b = bot_state.get('bot')
                        if b:
                            b.do_leave_party()
                        else:
                            print("\n[PARTY] Switched to Solo mode.\n", flush=True)
                    elif op in ('join', 'party'):
                        if len(parts) > 1:
                            new_code = parts[1].upper()
                            bot_state['code'] = new_code
                            bot_state['leave_requested'] = False
                            b = bot_state.get('bot')
                            if b:
                                b.do_join_party(new_code)
                            else:
                                print(f"\n[PARTY] Configured to join: {new_code}\n", flush=True)
                        else:
                            print("[!] Usage: join <PARTY_CODE> (e.g. join 3WB7AV)", flush=True)
                    elif op == 'region':
                        if len(parts) > 1:
                            new_reg = parts[1].lower()
                            bot_state['region'] = new_reg
                            b = bot_state.get('bot')
                            if b:
                                b.do_change_region(new_reg)
                            else:
                                print(f"\n[REGION] Configured region: {new_reg}\n", flush=True)
                        else:
                            print("[!] Usage: region <ap-southeast-1 | ap-south-1 | eu-central-1 | ...>", flush=True)
                    elif op == 'feed':
                        b = bot_state.get('bot')
                        n = int(parts[1]) if len(parts) > 1 and parts[1].isdigit() else 1
                        if b and b.arena:
                            b.do_feed(n)
                            print(f"[FEED] sent {n} eject(s) (total {b.feeds})", flush=True)
                        else:
                            print("[!] Not in a match.", flush=True)
                    elif op == 'split':
                        b = bot_state.get('bot')
                        if b and b.arena:
                            b.do_split()
                            print(f"[SPLIT] sent (total {b.splits})", flush=True)
                        else:
                            print("[!] Not in a match.", flush=True)
                    elif op == 'splitfeed':
                        b = bot_state.get('bot')
                        if b and b.arena:
                            b.do_split_feed()
                            print("[SPLIT+FEED] split + 2 feeds sent", flush=True)
                        else:
                            print("[!] Not in a match.", flush=True)
                    elif op == 'follow':
                        b = bot_state.get('bot')
                        if len(parts) > 1:
                            if b:
                                b.follow = parts[1]
                                b.mode = 'follow'
                                print(f"[FOLLOW] target -> {parts[1]} (applies from next round if mid-game)", flush=True)
                            else:
                                print(f"[FOLLOW] configured target: {parts[1]}", flush=True)
                        else:
                            print("[!] Usage: follow <uuid|Guest_name|nick>", flush=True)
                    elif op == 'leavegame':
                        b = bot_state.get('bot')
                        if b and b.arena:
                            b.do_leave_game()
                        else:
                            print("[!] Not in a match.", flush=True)
                    elif op in ('exit', 'quit', 'q'):
                        print("\n[+] Stopping bot and exiting...", flush=True)
                        bot_state['stop'] = True
                        b = bot_state.get('bot')
                        if b:
                            b.stop()
                        break
                    else:
                        print(f"[?] Unknown command: '{cmd}'. Type 'help' for commands.", flush=True)
                except Exception:
                    pass

        t_cmd = threading.Thread(target=_console_listener, daemon=True)
        t_cmd.start()

    bot_mode = a.mode
    if a.follow and bot_mode == 'play':
        bot_mode = 'follow'
    if bot_mode == 'follow' and not a.follow:
        raise SystemExit('--mode follow needs --follow <uuid|Guest_name|nick>')
    if bot_mode == 'leave':
        a.forever = True
    if bot_mode != 'play':
        print(f'[mode] {bot_mode.upper()}'
              + (f' target={a.follow}' if a.follow else '')
              + (' (enter arena -> feed -> leave arena loop)' if bot_mode == 'leave' else ''),
              flush=True)

    attempt = 0
    while not bot_state['stop']:
        attempt += 1
        cur_region = bot_state['region']
        cur_code = bot_state['code']
        cur_leave = bot_state['leave_requested']

        print(f'\n===== attempt {attempt} [{cur_region} | {("Party: " + cur_code) if cur_code else "Solo"}] =====', flush=True)
        cand_count = len(token_candidates())
        # Explicit --token is the one the user asked to use.  Do not rotate
        # through stale captures just because they exist on disk.
        if a.token:
            retries = max(0, a.token_retry)
        elif getattr(a, 'guest_v6', False):
            retries = 0
        else:
            retries = a.token_retry if a.token_retry > 0 else max(0, cand_count - 1)
        _amode = (getattr(a, 'arena_mode', None) or 'classic').strip().lower()
        if _amode not in ('classic', 'burst'):
            _amode = 'classic'
        try:
            _gt = int(getattr(a, 'game_type', 0) or 0)
        except Exception:
            _gt = 0
        if _gt <= 0:
            try:
                import arena_mode as _amod
                _gt = int(_amod.mode_id(_amode) or (7 if _amode == 'burst' else 13))
            except Exception:
                _gt = 7 if _amode == 'burst' else 13
        bot = AgarBot(cur_region, cur_code, a.nick, a.run, token=a.token,
                      strategy=a.strategy, tick=a.tick, verbose=not a.quiet,
                      respawn=not a.no_respawn, calibrate=not a.no_calibrate,
                      no_party=a.no_party or (cur_leave and not cur_code),
                      on_stats=on_stats,
                      mm_tries=a.mm_tries, mm_wait=a.mm_wait,
                      prefer=a.prefer, proxy=proxy_spec,
                      proxy_protocol=a.proxy_protocol,
                      token_retry=retries,
                      leave_party=cur_leave,
                      party_status_only=a.party_status,
                      join_then_leave=a.join_then_leave,
                      mode=bot_mode, follow=a.follow,
                      follow_name=getattr(a, 'follow_name', None),
                      auto_target=bool(getattr(a, 'auto_target', False)),
                      feed_keep=a.feed_keep, leave_at=a.leave_at,
                      guest_v6=bool(
                          not is_persist_token(a.token or '')
                          and (getattr(a, 'guest_v6', False)
                               or (a.token and ':APA91b' in (a.token or ''))
                               or (cur_region or '').lower() == 'ap-south-1')),
                      cycle_s=a.cycle, split_feed=not a.no_split_feed,
                      safe_mass=a.safe_mass,
                      threat_radius=a.threat_radius,
                      close_range=float(getattr(a, 'close_range', 1500.0) or 0.0),
                      require_proxy=bool(getattr(a, 'require_proxy', False)),
                      sticky_proxy=bool(getattr(a, 'sticky_proxy', False)),
                      boost_items=[s.strip() for s in
                                   str(getattr(a, 'boost_items', '') or '').split(',')
                                   if s.strip()],
                      boost_force=str(a.boost).strip().lower()
                      not in ('0', 'off', 'no', 'false', ''),
                      game_type=_gt, arena_mode=_amode,
                      enemy_clearance=getattr(a, 'enemy_clearance', '1'))
        if a.leave_party and not any(arg.startswith('--run') for arg in sys.argv) and not (a.interactive or sys.stdin.isatty()):
            bot.leave_party_only = True
        bot.boost_every_play = bool(getattr(a, 'boost_every_play', False))
        bot_state['bot'] = bot
        print(f'[arena] {_amode} game_type={_gt}', flush=True)

        if a.arena_host and a.arena_token:
            bot.arena_direct = (a.arena_host, a.arena_port, a.arena_token)
        if a.dump:
            bot.on_event = lambda name, kw: print(f'  [event] {name} {kw}', flush=True)
        try:
            played = bot.run()
        except Exception as e:
            bot.log(f'[!] CRASH in bot.run(): {type(e).__name__}: {e}')
            print(f'[!] {type(e).__name__}: {e}', flush=True)
            played = False
        finally:
            bot.close()
            bot_state['bot'] = None

        if a.party_status or a.join_then_leave or (a.leave_party and getattr(bot, 'leave_party_only', False)):
            break
        if bot_state['stop']:
            break

        if not played:
            # App logs in once.  Do NOT keep hammering just because stdin is a
            # TTY (Cursor / bot.bat).  Only --forever / --interactive loop.
            if not a.forever and attempt >= a.attempts and not a.interactive:
                break
            # Forever fleet: reconnect fast. Long sleeps are why the party
            # sits at 0 players after a drop.
            # Forever fleet: reconnect fast, but not flat-out.  A flat 2 s
            # retry re-dials the matchmaker before the throttle has decayed,
            # which is what turns a one-off "connection closed while waiting
            # for profile" into a permanent block for the whole fleet.
            # Forever: max 6s between failed dials (was 60s → party looks empty).
            # Arena-full / play fail: reconnect FAST (slot opens on deaths).
            wait = (min(0.4 + 0.2 * attempt, 2.0) if a.forever
                    else min(20 + 15 * attempt, 60))
            print(f'[retry] next try in {wait:.1f}s (Type "exit" to stop)',
                  flush=True)
            time.sleep(wait)
            continue
        if not a.forever and not a.interactive:
            break
        print(f"\n[LIVE] Round finished. Reconnecting to {bot_state['region']} in 0.5s... (Type 'exit' to stop)", flush=True)
        time.sleep(0.5)

    if not played and not a.join_then_leave and not a.party_status and not a.leave_party:
        print('\n[!] gave up without playing.  Three things cause this, and they\n'
              '    look alike; the log above tells them apart.\n'
              '\n'
              '      SYN block        ":9000" times out, while ":443" still '
              'answers.\n'
              '                       Nothing connects at all.\n'
              '      login block      TCP connects and the handshake completes,\n'
              '                       then the server closes right after\n'
              '                       "login mt=51".  A *stale token* produces\n'
              '                       this identical shape -- and is far more\n'
              '                       common.  Check with:\n'
              '                         python agar_bot.py --tokens\n'
              '                       If it printed "[token] marked ... refused"\n'
              '                       above, the ledger already rotated you onto\n'
              '                       the next token: just run it again.\n'
              '\n'
              '    If it was a throttle, it follows your source, so switching\n'
              '    region or --prefer buys you a login or two, not immunity.\n'
              '    Retrying makes it worse: stop, wait, then make ONE attempt.\n',
              flush=True)
        print(token_report(), flush=True)
        # Hand back the exact command so retrying later needs no recall.
        cmd = f'python agar_bot.py --region {a.region}'
        if a.code:
            cmd += f' --code {a.code}'
        print(f'\n    Re-run later with:\n      {cmd} --run {a.run}\n', flush=True)


if __name__ == '__main__':
    main()
