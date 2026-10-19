"""modes/follow.py — hunt the operator down anywhere in the arena and feed them.

Locks onto the follow UID (or the fleet's shared sighting of it),
walks there, dives under them and feeds mass. Repeats for as long as
the round lasts. This is the mode that makes the bots "come to me".

STRICT UID TRACKING:
  1. Identifies the operator exclusively through their verified account UID / UUID prefix.
     NEVER matches by in-game nickname, party member names, or copycats.
  2. Fallback to world entity_history ensures UID identity is preserved across delta packets.
  3. Real-time fleet sighting sync across all 50 bot processes with sub-second disk cache.
  4. Dynamic per-tick UID refresh from self.follow.
  5. 360-degree hostile enemy avoidance protects all cells while navigating.
  6. Direct sacrifice dive straight into operator center without boundary stall.

`self` is an AgarBot instance — see agar_bot_custom.py.
"""

import json
import math
import os
import random
import time

# Module-level shared sighting cache for 0ms in-process inter-bot communication
_FOLLOW_SIGHTING_CACHE: dict = {}

# Fallback only: the real TTL comes from agar_bot_custom.FLEET_TARGET_MAX_AGE
# (CLI --fix-ttl, config fix-ttl). A stale fix is worse than no fix — it
# sends the whole fleet to where the operator is not.
SIGHTING_TTL_FALLBACK = 25.0
# Arena identity may be older: used only to decide "wrong arena -> migrate".
AREA_INFO_MAX_AGE = 600.0
# Disk read cache for the shared fleet_target.json (seconds) — sub-second for instant fleet sync.
SIGHTING_DISK_CACHE_S = 0.35
# How far ahead of a moving sighting we aim (seconds).
CHASE_LEAD_MAX = 1.0
# Sweep waypoint lifetime (seconds) per lane.
SWEEP_WP_S = 9.0
# Never farm-gate below this mass even when safe_mass is configured lower.
GATE_FLOOR = 30.0


class FollowMode:
    """Follow and deliver mass to human operator strictly by UID."""

    # ------------------------------------------------------------ timings  #
    def _sighting_ttl(self) -> float:
        """How long a shared fix stays worth walking to (engine TTL)."""
        try:
            from agar_bot_custom import FLEET_TARGET_MAX_AGE
            return float(FLEET_TARGET_MAX_AGE)
        except Exception:
            return SIGHTING_TTL_FALLBACK

    def _publish_interval(self) -> float:
        try:
            from agar_bot_custom import SIGHTING_PUBLISH_S
            return float(SIGHTING_PUBLISH_S)
        except Exception:
            return 0.25

    def _area_memory(self) -> float:
        try:
            from agar_bot_custom import AREA_MEMORY
            return float(AREA_MEMORY)
        except Exception:
            return 240.0

    # ----------------------------------------------------------- sightings  #
    def _get_target_file_path(self) -> str:
        state_dir = os.environ.get('AGAR_STATE_DIR')
        if state_dir and os.path.isdir(state_dir):
            return os.path.join(state_dir, 'fleet_target.json')
        return os.path.join(
            os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
            'fleet_target.json'
        )

    def _record_follow_sighting(self, tgt) -> None:
        """Publish target sighting with velocity and arena_id to shared cache + fleet_target.json."""
        if tgt is None:
            return
        now = time.time()
        if now - getattr(self, '_follow_sighting_pub_t', 0.0) < self._publish_interval():
            return
        self._follow_sighting_pub_t = now

        size = float(getattr(self.world, 'arena', 0.0) or 11180.0)
        cx = min(size - 30.0, max(30.0, float(tgt.x)))
        cy = min(size - 30.0, max(30.0, float(tgt.y)))

        global _FOLLOW_SIGHTING_CACHE
        prev = _FOLLOW_SIGHTING_CACHE
        vx, vy = 0.0, 0.0
        if prev and isinstance(prev, dict):
            dt = now - float(prev.get('t', 0.0) or 0.0)
            if 0.02 < dt < 1.0:
                vx = (cx - float(prev.get('x', cx))) / dt
                vy = (cy - float(prev.get('y', cy))) / dt
                v_mag = math.hypot(vx, vy)
                if v_mag > 600.0:
                    vx = (vx / v_mag) * 600.0
                    vy = (vy / v_mag) * 600.0

        arena_id = str(getattr(self.world, 'arena_id', '') or '')
        arena_host = str(getattr(self, 'arena_host', '') or '')

        # Resolve verified target UID
        tgt_uuid = str(getattr(tgt, 'uuid', '') or '').strip()
        if not tgt_uuid and hasattr(self.world, 'entity_history') and tgt.id in self.world.entity_history:
            try:
                tgt_uuid = str(self.world.entity_history[tgt.id][1] or '').strip()
            except Exception:
                pass
        if not tgt_uuid:
            tgt_uuid = str(getattr(self, 'follow', '') or getattr(self, 'uid_target', '') or '').strip()

        sighting = {
            'x': cx,
            'y': cy,
            'vx': vx,
            'vy': vy,
            'arena_id': arena_id,
            'arena_host': arena_host,
            't': now,
            'mass': float(getattr(tgt, 'mass', 0.0) or 0.0),
            'r': float(getattr(tgt, 'r', 0.0) or 0.0),
            'name': str(getattr(tgt, 'name', '') or ''),
            'uuid': tgt_uuid,
            'by': str(getattr(self, 'bot_index', 0)),
        }
        _FOLLOW_SIGHTING_CACHE = sighting

        try:
            target_file = self._get_target_file_path()
            tmp_file = target_file + f'.tmp.{os.getpid()}'
            with open(tmp_file, 'w', encoding='utf8') as fh:
                json.dump(sighting, fh)
            os.replace(tmp_file, target_file)
        except Exception:
            pass

        try:
            from agar_bot_custom import _write_party_arena_pin, _is_pinable_arena_host
            target_pin_host = arena_host
            if not _is_pinable_arena_host(target_pin_host):
                prev_s = _FOLLOW_SIGHTING_CACHE or {}
                if _is_pinable_arena_host(prev_s.get('arena_host')):
                    target_pin_host = prev_s.get('arena_host')
            if target_pin_host and hasattr(self, 'arena_port'):
                _write_party_arena_pin(
                    target_pin_host, self.arena_port,
                    seen_target=True,
                    arena_id=arena_id,
                    code=getattr(self, 'code', '') or ''
                )
        except Exception:
            pass

    def _read_sighting_disk(self) -> dict | None:
        """Read fleet_target.json with sub-second cache for rapid inter-process sync."""
        now = time.time()
        if now - getattr(self, '_sighting_disk_t', 0.0) < SIGHTING_DISK_CACHE_S:
            return getattr(self, '_sighting_disk_cache', None)
        try:
            target_file = self._get_target_file_path()
            if os.path.exists(target_file):
                with open(target_file, encoding='utf8') as fh:
                    sighting = json.load(fh)
            else:
                sighting = None
        except Exception:
            sighting = getattr(self, '_sighting_disk_cache', None)
        self._sighting_disk_cache = sighting
        self._sighting_disk_t = now
        return sighting

    def _get_follow_sighting(self, follow_key: str, follow_name: str = ''):
        """(sighting, age_s) of the operator strictly by UID, honouring engine fix TTL.

        Picks the freshest sighting between in-process memory and shared disk cache.
        Rejects any sighting without a matching target UID.
        """
        global _FOLLOW_SIGHTING_CACHE
        now = time.time()

        disk_sighting = self._read_sighting_disk()
        t_mem = float(_FOLLOW_SIGHTING_CACHE.get('t', 0.0) or 0.0) if _FOLLOW_SIGHTING_CACHE else 0.0
        t_disk = float(disk_sighting.get('t', 0.0) or 0.0) if disk_sighting else 0.0

        if t_disk > t_mem:
            sighting = disk_sighting
            _FOLLOW_SIGHTING_CACHE = disk_sighting
        else:
            sighting = _FOLLOW_SIGHTING_CACHE or disk_sighting

        if not sighting:
            return None, 1e9

        t = float(sighting.get('t', 0.0) or 0.0)
        age = now - t
        if age < -2.0 or age > AREA_INFO_MAX_AGE:
            return None, 1e9

        # Fallback to self.follow if follow_key wasn't provided
        if not follow_key:
            follow_key = (getattr(self, 'follow', '') or getattr(self, 'uid_target', '') or '').strip()

        # STRICT UID CHECK: sighting must contain and match follow_key UID!
        if follow_key:
            su = str(sighting.get('uuid', '') or '').lower().strip().replace('-', '')
            if not su:
                return None, 1e9
            matched = False
            for part in follow_key.lower().split(','):
                pk = part.strip().replace('-', '')
                if not pk:
                    continue
                if su == pk or (len(pk) >= 8 and len(su) >= 8 and (su.startswith(pk[:8]) or pk.startswith(su[:8]))):
                    matched = True
                    break
            if not matched:
                return None, 1e9

        if age > self._sighting_ttl():
            return None, age
        return sighting, age

    def _get_target_arena_info(self, follow_key: str, follow_name: str = '') -> tuple[str, str]:
        """Return (target_arena_id, target_host) if operator's location is known strictly by UID."""
        if not follow_key:
            follow_key = (getattr(self, 'follow', '') or getattr(self, 'uid_target', '') or '').strip()

        try:
            target_file = self._get_target_file_path()
            if os.path.exists(target_file):
                with open(target_file, encoding='utf8') as fh:
                    d = json.load(fh)
                su = str(d.get('uuid', '') or '').lower().strip().replace('-', '')
                aid = str(d.get('arena_id') or '').strip()
                ahost = str(d.get('arena_host') or '').strip()
                t_val = float(d.get('t', 0.0) or 0.0)
                if aid and (time.time() - t_val <= AREA_INFO_MAX_AGE):
                    if follow_key:
                        matched = False
                        for part in follow_key.lower().split(','):
                            pk = part.strip().replace('-', '')
                            if pk and (su == pk or (len(pk) >= 8 and len(su) >= 8 and (su.startswith(pk[:8]) or pk.startswith(su[:8])))):
                                matched = True
                                break
                        if matched:
                            return aid, ahost
                    elif su:
                        return aid, ahost
        except Exception:
            pass

        try:
            from agar_bot_custom import _read_party_arena_pin
            pin = _read_party_arena_pin()
            if pin and pin.get('seen_target') and pin.get('arena_id'):
                return str(pin.get('arena_id') or '').strip(), str(pin.get('host') or '').strip()
        except Exception:
            pass
        return '', ''

    # -------------------------------------------------------------- slots    #
    def _resolve_slot(self) -> tuple[int, int]:
        """(slot, count) for fleet fan-out — NEVER all bots on one waypoint."""
        slot = None
        for attr in ('bot_index',):
            v = getattr(self, attr, None)
            if isinstance(v, int) and v >= 0:
                slot = v
                break
        if slot is None:
            env = os.environ.get('BOT_INDEX')
            if env is not None:
                try:
                    slot = max(0, int(env))
                except ValueError:
                    slot = None
        if slot is None:
            lf = os.environ.get('BOT_LOG_FILE', '') or getattr(self, '_bot_log_file', '') or ''
            import re as _re
            m = _re.search(r'(\d+)', os.path.basename(lf))
            if m:
                slot = max(0, int(m.group(1)) - 1)
        if slot is None:
            slot = (os.getpid() * 2654435761) % 8192

        count = None
        v = getattr(self, 'bot_count', None)
        if isinstance(v, int) and v > 0:
            count = v
        if count is None:
            env = os.environ.get('BOT_COUNT')
            if env is not None:
                try:
                    count = max(1, int(env))
                except ValueError:
                    count = None
        if count is None:
            count = 50
        return slot, count

    # ---------------------------------------------------------- navigation   #
    def _find_follow_target(self, follow_key: str, follow_name: str = ''):
        """Directly locate follow target cell STRICTLY by UID (UUID / hex / prefix).

        NEVER matches by player name, ensuring the bot exclusively tracks the operator's
        true account identity regardless of in-game nicknames, party member names, or copycats.
        """
        if not follow_key:
            follow_key = (getattr(self, 'follow', '') or getattr(self, 'uid_target', '') or '').strip()
        if not follow_key:
            return None

        # Build clean lookup sets of UID keys (full UUID, stripped hyphens, 8-char prefixes)
        keys_set = set()
        prefixes_8 = set()
        fk = follow_key.lower().strip()
        for part in fk.split(','):
            p = part.strip()
            if not p:
                continue
            p_clean = p.replace('-', '')
            keys_set.add(p)
            keys_set.add(p_clean)
            if len(p_clean) >= 8:
                prefixes_8.add(p_clean[:8])
            if len(p) >= 8:
                prefixes_8.add(p[:8].replace('-', ''))

        candidates = []
        for e in self.world.entities.values():
            if getattr(e, 'is_self', False):
                continue
            # Must be a player cell (kind 8, or unclassified 0)
            k = getattr(e, 'kind', 0)
            if k not in (8, 0):
                continue

            # Extract entity UUID from entity itself, or fallback to world entity_history
            eu = (getattr(e, 'uuid', '') or '').lower().strip()
            if not eu and hasattr(self.world, 'entity_history') and e.id in self.world.entity_history:
                try:
                    eu = (self.world.entity_history[e.id][1] or '').lower().strip()
                except Exception:
                    pass

            if not eu:
                continue

            eu_clean = eu.replace('-', '')
            eu_pfx8 = eu_clean[:8] if len(eu_clean) >= 8 else eu[:8].replace('-', '')

            matched = False
            if eu in keys_set or eu_clean in keys_set:
                matched = True
            elif eu_pfx8 and eu_pfx8 in prefixes_8:
                matched = True
            elif any(eu_clean.startswith(k) or k.startswith(eu_clean) for k in prefixes_8 if len(k) >= 8):
                matched = True

            if matched:
                candidates.append(e)

        if not candidates:
            return None

        me = self.world.me
        my_m = float(getattr(me, 'mass', 0.0) or 0.0) if me else 0.0
        my_x, my_y = (me.x, me.y) if me else (0.0, 0.0)

        # If operator has split cells:
        # Prefer a cell that is large enough to absorb us (safe delivery)
        # Otherwise pick the largest cell to feed mass efficiently
        # User rule: ALWAYS select the LARGEST piece of the operator!
        # Never feed or split into small pieces just because they are closer.
        best = max(candidates, key=lambda c: getattr(c, 'mass', 0.0))

        if best.name and not best.name.startswith('?'):
            self._follow_seen_name = best.name
        return best

    def _compute_patrol_seek(self, me, now: float) -> tuple[float, float]:
        """Deprecated name kept for compatibility — routes to the fan-out sweep."""
        return self._compute_sweep_seek(me, now)

    def _compute_sweep_seek(self, me, now: float) -> tuple[float, float]:
        """Rally all bots together towards the central arena hub so 100% of fleet stays grouped."""
        size = float(getattr(self.world, 'arena', 0.0) or 11180.0)
        cx, cy = size * 0.5, size * 0.5
        slot, count = self._resolve_slot()
        # Grouped search around center where players fight
        radius = 650.0 + (slot % 6) * 150.0
        ang = (now * 0.3) + (slot * (2.0 * math.pi / max(1, count)))
        return cx + math.cos(ang) * radius, cy + math.sin(ang) * radius

    def _compute_local_search(self, sx: float, sy: float, now: float) -> tuple[float, float]:
        """Tight local search ring around last known sighting coordinates.
        Stepped smoothly every 2.5s to prevent joystick jitter/spin.
        """
        slot, count = self._resolve_slot()
        ring_r = 300.0 + (slot % 3) * 120.0
        step = int(now / 2.5)
        ang = (step * 0.9) + (slot * 1.25)
        return sx + math.cos(ang) * ring_r, sy + math.sin(ang) * ring_r

    def _compute_radar_seek(self, me, now: float) -> tuple[float, float]:
        return self._compute_sweep_seek(me, now)

    def _last_known_area(self, key: str, fn: str = ''):
        """Newest (x, y, t) the operator was seen — strictly by UID within AREA_MEMORY."""
        best = None
        if not key:
            key = (getattr(self, 'follow', '') or getattr(self, 'uid_target', '') or '').strip()

        try:
            target_file = self._get_target_file_path()
            if os.path.exists(target_file):
                with open(target_file, encoding='utf8') as fh:
                    d = json.load(fh)
                su = str(d.get('uuid', '') or '').lower().strip().replace('-', '')
                if key:
                    fk_clean = key.lower().strip().replace('-', '')
                    if su and (su == fk_clean or (len(fk_clean) >= 8 and len(su) >= 8 and (su.startswith(fk_clean[:8]) or fk_clean.startswith(su[:8])))):
                        best = (float(d['x']), float(d['y']), float(d['t']))
                elif su:
                    best = (float(d['x']), float(d['y']), float(d['t']))
        except Exception:
            pass

        s, age = self._get_follow_sighting(key, fn)
        if s is not None:
            st = float(s.get('t', 0.0) or 0.0)
            if best is None or st > best[2]:
                best = (float(s.get('x', 0.0)), float(s.get('y', 0.0)), st)

        if best is None:
            return None
        if time.time() - best[2] > self._area_memory():
            return None
        return (best[0], best[1], best[2])

    def _apply_safety_cushion(self, me, bot_x: float, bot_y: float, jx: float, jy: float) -> tuple[float, float]:
        """Apply minimal boundary cushion to avoid getting stuck in arena walls."""
        size = float(getattr(self.world, 'arena', 0.0) or 11180.0)
        WALL_PAD = 120.0

        if bot_x < WALL_PAD:
            w_blend = (WALL_PAD - bot_x) / WALL_PAD
            jx = jx * (1.0 - w_blend) + 1.0 * w_blend
        elif bot_x > size - WALL_PAD:
            w_blend = (bot_x - (size - WALL_PAD)) / WALL_PAD
            jx = jx * (1.0 - w_blend) - 1.0 * w_blend

        if bot_y < WALL_PAD:
            w_blend = (WALL_PAD - bot_y) / WALL_PAD
            jy = jy * (1.0 - w_blend) + 1.0 * w_blend
        elif bot_y > size - WALL_PAD:
            w_blend = (bot_y - (size - WALL_PAD)) / WALL_PAD
            jy = jy * (1.0 - w_blend) - 1.0 * w_blend

        jn = math.hypot(jx, jy)
        if jn > 1e-5:
            return jx / jn, jy / jn
        return jx, jy

    def _bias_to_food(self, me, aim_x: float, aim_y: float, my_cells):
        """Nudge the heading toward nearby food while growing (mass gate on)."""
        try:
            adx, ady = aim_x - me.x, aim_y - me.y
            adist = math.hypot(adx, ady)
            if adist < 1e-6:
                return None
            ux, uy = adx / adist, ady / adist
            best = None
            best_score = 0.0
            for e in self.world.entities.values():
                if getattr(e, 'is_self', False):
                    continue
                if getattr(e, 'kind', 0) not in (2, 7):
                    continue
                dx = e.x - me.x
                dy = e.y - me.y
                d = math.hypot(dx, dy)
                if d > 900.0 or d < 1e-3:
                    continue
                dot = (dx * ux + dy * uy) / d
                if dot < 0.55:
                    continue
                perp = abs(dx * uy - dy * ux)
                if perp > 260.0:
                    continue
                score = (1.0 + 0.6 * dot) / d
                if score > best_score:
                    best_score = score
                    best = (dx / d, dy / d)
            return best
        except Exception:
            return None

    # ------------------------------------------------------------ main loop  #
    def _play_follow(self, deadline) -> str:
        """Lock the follow target strictly by UID and deliver mass continuously.

        States:
          LOCK  — operator cell visible (STRICT UID MATCH): dive / split-feed / stream.
          CHASE — fresh shared sighting (matching UID): beeline to the led position.
          SWEEP — nothing fresh: per-bot sector sweep, ringed around the last
                  known area, so the fleet re-acquires instead of scattering.
        """
        from agar_bot_custom import (
            K_CELL, NO_SELF_BAIL_S, _nick_cmd
        )

        key = (getattr(self, 'follow', '') or getattr(self, 'uid_target', '') or '').strip()
        fn = (getattr(self, 'follow_name', '') or '').strip()
        self.log(f'[follow] hunt target uid={key!r} — locking strictly by UID, dodging enemies & feeding')

        last_stats = 0.0
        last_feed = 0.0
        last_split = 0.0
        last_seen_alive = time.time()
        death_logged = False

        _last_stat_xy = None
        _last_stat_upd = self.world.updates
        _pin_xy = None
        _still_since = time.time()
        _pin_recoveries = 0
        PIN_S = 3.5
        STALE_S = 18.0

        _stream_upd = self.world.updates
        _stream_t = time.time()
        _stale_hits = 0
        phase = 'SWEEP'

        tgt = None
        BRAIN = 'follow-direct'
        gate = max(float(getattr(self, 'safe_mass', 0.0) or 0.0), 0.0)
        close_range = float(getattr(self, 'close_range', 0.0) or 0.0)

        while time.time() < deadline and not self._stop.is_set():
            self._heartbeat += 1
            now = time.time()

            # Dynamic UID refresh from self.follow on every tick
            key = (getattr(self, 'follow', '') or getattr(self, 'uid_target', '') or '').strip()

            if hasattr(self, 'tick_live_ctrl') and self.tick_live_ctrl():
                return 'closed'

            self._pump_arena()

            if self.arena is None or (
                self.ar_closed.is_set() and not self._arena_is_inline()
            ):
                self.log('[!] arena connection closed by the server')
                return 'closed'
            if self._arena_is_inline() and self.mm_closed.is_set():
                self.log('[!] matchmaker closed (inline arena)')
                return 'closed'

            me = self.world.me
            if me is None and not self.world.dead:
                try:
                    self.world._resolve_self(now)
                except Exception:
                    pass
                me = self.world.me

            # Death / respawn handling
            if me is None or self.world.dead:
                if not death_logged and self.world.dead:
                    death_logged = True
                    kb_ent = self.world.entities.get(self.world.killed_by)
                    kb_name = kb_ent.name if kb_ent else '?'
                    kb_uuid = getattr(kb_ent, 'uuid', '') if kb_ent else ''
                    if not kb_uuid and kb_ent and hasattr(self.world, 'entity_history') and kb_ent.id in self.world.entity_history:
                        try:
                            kb_uuid = self.world.entity_history[kb_ent.id][1] or ''
                        except Exception:
                            pass

                    # STRICT UID-ONLY CHECK: operator absorption identified by UID
                    is_operator = False
                    if tgt is not None and self.world.killed_by == tgt.id:
                        is_operator = True
                    elif key and kb_uuid:
                        ku = kb_uuid.lower().replace('-', '')
                        for part in key.lower().split(','):
                            pk = part.strip().replace('-', '')
                            if pk and (ku == pk or (len(pk) >= 8 and len(ku) >= 8 and (ku.startswith(pk[:8]) or pk.startswith(ku[:8])))):
                                is_operator = True
                                break

                    is_sibling = bool(
                        (hasattr(self, '_is_sibling') and kb_ent and self._is_sibling(kb_ent))
                        or (kb_name.lower() == (getattr(self, 'nick', '') or 'ggs').lower())
                        or (kb_name.lower() == 'ggs')
                    )
                    if is_operator:
                        self.log(f'>>> [MASS DELIVERED!] Bot absorbed by YOU ({kb_name}[{kb_uuid[:8]}]) (death #{self.world.deaths})')
                    elif is_sibling:
                        self.log(f'[fleet] Absorbed by sibling {kb_name}[{kb_uuid[:8]}] (id={self.world.killed_by}, death #{self.world.deaths})')
                    else:
                        self.log(f'!!! [EATEN BY ENEMY: {kb_name}] Bot absorbed by {kb_name}[{kb_uuid[:8]}] (id={self.world.killed_by}, death #{self.world.deaths})')
                    self.event('death', killed_by=self.world.killed_by, deaths=self.world.deaths)

                if not self.respawn:
                    return 'dead'

                if me is None and not self.world.dead:
                    if now - last_seen_alive > NO_SELF_BAIL_S:
                        return self._bail_arena(f'[follow] no self cell for {NO_SELF_BAIL_S:.0f}s — fresh node')
                    time.sleep(0.04)
                    continue

                window = min(deadline, time.time() + 20.0)
                if self._respawn(window):
                    last_seen_alive = time.time()
                    death_logged = False
                    _pin_xy = None
                    _pin_recoveries = 0
                    _last_stat_xy = None
                    _still_since = time.time()
                    _stream_upd = self.world.updates
                    _stream_t = time.time()
                    _stale_hits = 0
                    continue
                return self._bail_arena('[death] same-socket respawn failed — fresh reconnect')

            if death_logged:
                death_logged = False
                self.log(f'[respawn] back as id={me.id} mass={me.mass:.1f} — seeking operator')

            last_seen_alive = now
            if hasattr(self, '_record_own_uuid'):
                self._record_own_uuid()

            # Stale stream watchdog
            _upd_now = self.world.updates
            if _upd_now != _stream_upd:
                _stream_upd = _upd_now
                _stream_t = now
                _stale_hits = 0
            elif now - _stream_t > STALE_S:
                cell_moving = (
                    _pin_xy is not None
                    and math.hypot(me.x - _pin_xy[0], me.y - _pin_xy[1]) > 12.0
                )
                if cell_moving:
                    _stream_t = now
                    _stale_hits = 0
                else:
                    _stale_hits += 1
                    self.log(f'[stale] no updates for {STALE_S:.0f}s — soft reconnect #{_stale_hits}')
                    if _stale_hits >= 3:
                        return self._bail_arena('[stale] world frozen — fresh reconnect')
                    _stream_t = now

            # Pinned watchdog: ONLY trigger if stuck against an actual arena wall!
            arena_sz = float(self.world.arena or 11180.0)
            is_near_wall = (
                me.x < 160.0 or me.x > arena_sz - 160.0 or
                me.y < 160.0 or me.y > arena_sz - 160.0
            )

            if _pin_xy is None:
                _pin_xy = (me.x, me.y)
                _still_since = now
            if math.hypot(me.x - _pin_xy[0], me.y - _pin_xy[1]) > 10.0:
                _pin_recoveries = 0
                _pin_xy = (me.x, me.y)
                _still_since = now
            elif is_near_wall and (now - _still_since > PIN_S):
                _pin_recoveries += 1
                if _pin_recoveries >= 4:
                    self.log(f'[pin] trapped in wall #{_pin_recoveries} — respawn on this arena')
                    _pin_recoveries = 0
                    _pin_xy = None
                    _still_since = now
                    try:
                        from agar_bot_custom import pkt_respawn
                        self._arena_send(pkt_respawn())
                    except Exception:
                        pass
                    continue
                cx, cy = arena_sz * 0.5, arena_sz * 0.5
                dx, dy = cx - me.x, cy - me.y
                jitter = (random.random() - 0.5) * 0.8
                cj, sj = math.cos(jitter), math.sin(jitter)
                kx = dx * cj - dy * sj
                ky = dx * sj + dy * cj
                n = math.hypot(kx, ky) or 1.0
                nudge = (kx / n, ky / n)
                t_esc = time.time() + 0.5
                while time.time() < t_esc and not self._stop.is_set():
                    self._pump_arena()
                    self._send_joy(nudge, raw=True)
                    time.sleep(0.04)
                _still_since = time.time()
                _pin_xy = None
                continue

            # Arena migration check — operator must be followed across rooms strictly by UID
            tgt_arena, tgt_host = self._get_target_arena_info(key, fn)
            my_arena = str(getattr(self.world, 'arena_id', '') or '').strip()
            if tgt_arena and my_arena and my_arena != tgt_arena:
                self.log(f'[migrate] Operator is in {tgt_arena} ({tgt_host}), I am in {my_arena} — migrating!')
                self._fleet_wrong_room = True
                self._arena_token_bounced = True
                time.sleep(1.5)
                return self._bail_arena('[migrate] switching to operator arena')

            # Target resolution (strict UID only: entity UID match or fresh UID sighting)
            sighting, s_age = self._get_follow_sighting(key, fn)
            tgt = self._find_follow_target(key, fn)
            is_sibling_lock = False
            if tgt is None and sighting is None and hasattr(self, '_find_nearby_bigger_friendly'):
                # User request: when operator is absent, smaller bots feed nearby larger friendly bots!
                sibling = self._find_nearby_bigger_friendly(me)
                if sibling is not None:
                    tgt = sibling
                    is_sibling_lock = True

            my_mass = self.world.total_mass
            my_cells = [c for c in self.world.entities.values()
                        if getattr(c, 'is_self', False) and getattr(c, 'kind', 0) == K_CELL]
            if not my_cells and me is not None:
                my_cells = [me]
            if my_cells:
                bot_x = sum(c.x for c in my_cells) / len(my_cells)
                bot_y = sum(c.y for c in my_cells) / len(my_cells)
            else:
                bot_x, bot_y = me.x, me.y

            # ============================ LOCK ============================== #
            if tgt is not None:
                phase = 'FEED_DELIVERY'
                if not is_sibling_lock:
                    self._record_follow_sighting(tgt)
                tx, ty = tgt.x, tgt.y
                dist_true = math.hypot(tx - bot_x, ty - bot_y)
                locked = True
                dx = tx - bot_x
                dy = ty - bot_y
                dist = dist_true
                tgt_r = float(getattr(tgt, 'r', 0.0) or 0.0)
                tgt_m = float(getattr(tgt, 'mass', 0.0) or 0.0)
                my_m = float(getattr(me, 'mass', 0.0) or 0.0)

                # Intercept ahead if target is moving
                aim_tx, aim_ty = tx, ty
                if sighting and isinstance(sighting, dict):
                    svx = float(sighting.get('vx', 0.0) or 0.0)
                    svy = float(sighting.get('vy', 0.0) or 0.0)
                    if math.hypot(svx, svy) > 4.0 and dist <= 800.0:
                        lead_factor = 0.22 if my_m < max(35.0, tgt_m * 1.15) else 0.10
                        aim_tx = tx + svx * lead_factor
                        aim_ty = ty + svy * lead_factor

                dx = aim_tx - bot_x
                dy = aim_ty - bot_y
                aim_dist = math.hypot(dx, dy)
                raw_ux, raw_uy = (dx / aim_dist, dy / aim_dist) if aim_dist > 1e-5 else (1.0, 0.0)

                # Avoid hostile enemies in 360 degrees — protects EVERY own cell
                if hasattr(self, '_avoid_enemies'):
                    jx, jy = self._avoid_enemies(me, raw_ux, raw_uy, tgt=tgt, cells=my_cells)
                else:
                    jx, jy = raw_ux, raw_uy

                # Boundary cushion: only when far from target so wall-cushion never blocks us from reaching operator
                if dist > 350.0:
                    jx, jy = self._apply_safety_cushion(me, bot_x, bot_y, jx, jy)

                j_mag = math.hypot(jx, jy)
                is_aligned = True
                if j_mag > 0.1:
                    dot = (jx * raw_ux + jy * raw_uy) / j_mag
                    is_aligned = (dot >= 0.55)

                # Mass Transfer (split-feed combo + continuous rapid feed stream)
                delivery_dist = tgt_r + getattr(me, 'r', 0.0) + 180.0
                if dist <= max(delivery_dist, 250.0):
                    split_done = False
                    if hasattr(self, '_check_safe_split_feed'):
                        split_done, last_split = self._check_safe_split_feed(
                            me, tgt, dist, tgt_r, my_mass, my_cells, is_aligned, now, last_split
                        )
                    if not split_done and my_mass >= 20.0 and (now - last_feed >= 0.04):
                        if hasattr(self, '_stream_feed'):
                            fed_done, last_feed = self._stream_feed(
                                me, tgt, bot_x, bot_y, jx, jy, dist, my_mass, is_aligned, now, last_feed
                            )
                        else:
                            last_feed = now
                            self.do_feed(4, gap=0.015)

                # Movement execution
                if my_m >= max(35.0, tgt_m * 1.15) and tgt_m > 0:
                    # Bot larger than operator: keep safe standoff to avoid eating operator!
                    standoff_dist = tgt_r + getattr(me, 'r', 0.0) + 70.0
                    if dist > standoff_dist:
                        self._send_joy((jx, jy), raw=True)
                    else:
                        if is_aligned:
                            self._send_joy((raw_ux, raw_uy), raw=True)
                        else:
                            self._send_joy((jx, jy), raw=True)
                        if now - last_feed >= 0.04:
                            last_feed = now
                            self.do_feed(4, gap=0.015)
                else:
                    # Operator larger: direct sacrifice dive straight into operator center!
                    # When close, dive DIRECTLY into operator (raw_ux, raw_uy)
                    if dist <= tgt_r + getattr(me, 'r', 0.0) + 120.0:
                        self._send_joy((raw_ux, raw_uy), raw=True)
                    else:
                        self._send_joy((jx, jy), raw=True)

            # ============================ CHASE ============================= #
            elif sighting is not None:
                phase = 'CHASE'
                svx = float(sighting.get('vx', 0.0) or 0.0)
                svy = float(sighting.get('vy', 0.0) or 0.0)
                s_speed = math.hypot(svx, svy)

                # lead the moving operator
                lead_t = min(max(s_age, 0.0), CHASE_LEAD_MAX)
                tx = float(sighting['x']) + svx * lead_t
                ty = float(sighting['y']) + svy * lead_t
                dist_true = math.hypot(tx - bot_x, ty - bot_y)
                locked = True

                if dist_true < 500.0 and s_age > 2.5:
                    if s_speed > 15.0:
                        # Operator is on the move: extrapolate forward along their velocity vector
                        extrap_tx = tx + svx * min(s_age, 6.0)
                        extrap_ty = ty + svy * min(s_age, 6.0)
                        lux, luy = (extrap_tx - bot_x, extrap_ty - bot_y)
                        lnorm = math.hypot(lux, luy)
                        lux, luy = (lux / lnorm, luy / lnorm) if lnorm > 1e-5 else (1.0, 0.0)
                    else:
                        phase = 'SEEK_LOCAL'
                        lx, ly = self._compute_local_search(tx, ty, now)
                        ldx, ldy = lx - bot_x, ly - bot_y
                        ldist = math.hypot(ldx, ldy)
                        lux, luy = (ldx / ldist, ldy / ldist) if ldist > 1e-5 else (1.0, 0.0)
                else:
                    lux, luy = (tx - bot_x, ty - bot_y)
                    lnorm = math.hypot(lux, luy)
                    lux, luy = (lux / lnorm, luy / lnorm) if lnorm > 1e-5 else (1.0, 0.0)

                # Mass gate: only while operator is far AND we cannot see them
                hungry = (gate > 0.0 and my_mass < max(gate, GATE_FLOOR)
                          and dist_true > max(close_range, 0.0))
                if hungry:
                    food_h = self._bias_to_food(me, tx, ty, my_cells)
                    if food_h is not None:
                        lux, luy = food_h

                if hasattr(self, '_avoid_enemies'):
                    jx, jy = self._avoid_enemies(me, lux, luy, tgt=None, cells=my_cells)
                else:
                    jx, jy = lux, luy
                jx, jy = self._apply_safety_cushion(me, bot_x, bot_y, jx, jy)
                self._send_joy((jx, jy), raw=True)

            # ============================ SWEEP ============================= #
            else:
                phase = 'SWEEP'
                locked = False
                tx, ty = 0.0, 0.0
                dist_true = 9999.0
                area = self._last_known_area(key, fn)
                if area is not None:
                    # ring the last known area — the fix is stale, not wrong
                    rx_, ry_ = self._compute_local_search(area[0], area[1], now)
                    pdx, pdy = rx_ - bot_x, ry_ - bot_y
                else:
                    sx_, sy_ = self._compute_sweep_seek(me, now)
                    pdx, pdy = sx_ - bot_x, sy_ - bot_y
                pdist = math.hypot(pdx, pdy)
                pux, puy = (pdx / pdist, pdy / pdist) if pdist > 1e-5 else (1.0, 0.0)

                # even a sweep is a chance to grow before the long trip
                if gate > 0.0 and my_mass < max(gate, GATE_FLOOR):
                    food_h = self._bias_to_food(me, bot_x + pux * 1000.0, bot_y + puy * 1000.0,
                                                my_cells)
                    if food_h is not None:
                        pux, puy = food_h

                if hasattr(self, '_avoid_enemies'):
                    jx, jy = self._avoid_enemies(me, pux, puy, tgt=None, cells=my_cells)
                else:
                    jx, jy = pux, puy
                jx, jy = self._apply_safety_cushion(me, bot_x, bot_y, jx, jy)
                self._send_joy((jx, jy), raw=True)

            # Stats & logging
            if now - last_stats >= 4.0:
                last_stats = now
                if _nick_cmd is not None:
                    try:
                        _nick_cmd.poll(self, self.world, now)
                    except Exception:
                        pass

                st = self.world.stats()
                st.update(
                    mode='follow',
                    feeds=self.feeds,
                    splits=self.splits,
                    target=(tgt.uuid if tgt else None),
                    target_mass=(round(tgt.mass, 1) if tgt else None),
                    target_dist=(round(dist_true) if (tgt is not None or sighting is not None) else None),
                )

                if _last_stat_xy is None:
                    _mv = 0.0
                else:
                    _mv = math.hypot(me.x - _last_stat_xy[0], me.y - _last_stat_xy[1])
                _last_stat_xy = (me.x, me.y)
                _d_upd = self.world.updates - _last_stat_upd
                _last_stat_upd = self.world.updates

                t_name = ''
                if tgt and tgt.name and not tgt.name.startswith('?'):
                    t_name = tgt.name
                if not t_name:
                    t_name = getattr(self, '_follow_seen_name', '')
                if not t_name and sighting and sighting.get('name'):
                    t_name = str(sighting.get('name') or '')
                if not t_name:
                    t_name = 'Operator'

                t_uuid = ''
                if tgt and getattr(tgt, 'uuid', ''):
                    t_uuid = tgt.uuid
                elif sighting and sighting.get('uuid'):
                    t_uuid = str(sighting.get('uuid') or '')
                elif key:
                    t_uuid = key

                tl = (
                    f"{t_name}[{t_uuid[:8]}] m:{tgt.mass:.0f} d:{dist_true:.0f}"
                    if tgt
                    else ('SIGHTING ' + (f"({tx:.0f},{ty:.0f}) d:{dist_true:.0f}" if sighting is not None else 'NOT VISIBLE'))
                )

                _slot, _count = self._resolve_slot()
                _bid = str(_slot + 1)
                if _slot == 0 or True:
                    self.log(
                        f"[FOLLOW] {BRAIN} #{_bid} Region: {self.region:<14} | "
                        f"Party: {self.party_code or '-':<7} | "
                        f"Me: {st['mass']:<5.1f} at ({st['x']},{st['y']}) "
                        f"-> ({tx:.0f},{ty:.0f}) | Target: {tl} | "
                        f"upd: {_d_upd} mv: {_mv:.0f} | "
                        f"Feeds: {self.feeds} | Splits: {self.splits} | {phase}"
                    )

                if self.on_stats:
                    try:
                        self.on_stats(st)
                    except Exception:
                        pass
                self.event('stats', **st)

            time.sleep(self.tick)

        return 'done'
