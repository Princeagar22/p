#!/usr/bin/env python3
"""
claim_mission_takedown.py — Automated Mission Takedown Claimer & Potion Opener
=============================================================================
Reverse-Engineered directly from live MEmu packet capture:
- Event: "fungus_amongus_v13" (Active Mission Takedown)
- Claims all available Tiers (1 to 20)
- Automatically cracks open all awarded Brewless Potions (Rare, Exotic, Battle)
- Gives instant Coins, DNA, and Skin pieces!
"""

import os
import socket
import sys
import time
from pathlib import Path

TOOLKIT_DIR = Path(__file__).resolve().parent
BASE_DIR = TOOLKIT_DIR.parent
COLLECTOR_DIR = BASE_DIR / "collector"
sys.path.insert(0, str(COLLECTOR_DIR))
sys.path.insert(0, str(BASE_DIR))

try:
    from agar_bot_custom import (
        vint,
        ld,
        frame,
        read_frame,
        decode_frame,
        fields,
        one,
        pkt_hello,
        pkt_hello2,
        pkt_login,
        handshake_key_from_mt120,
        _server_login_f1,
        remint_wire_ticket,
        socks5_connect,
        parse_proxy,
    )
except ImportError as e:
    print(f"[!] Import error: {e}")
    sys.exit(1)

EVENT_NAME = "fungus_amongus_v13"

GW_HOSTS = [
    "mobile-live-v26.agario.miniclippt.com",
    "eu-central-1.mobile-live-v26.agario.miniclippt.com",
    "us-east-1.mobile-live-v26.agario.miniclippt.com",
    "ap-south-1.mobile-live-v26.agario.miniclippt.com",
]


def make_claim_mission_takedown(event_name: str, tier: str) -> bytes:
    """Builds the exact client claim packet for Mission Takedown."""
    f105_val = ld(1, tier.encode("utf-8")) + ld(2, event_name.encode("utf-8"))
    f3_val = ld(105, f105_val) + vint(109, 10)
    return vint(2, 2) + ld(3, f3_val)


def make_open_brewless_potion(potion_name: str) -> bytes:
    """Builds the instant potion open packet for brewless potions."""
    f9_val = ld(1, potion_name.encode("utf-8"))
    f3_val = ld(9, f9_val) + vint(109, 2)
    return vint(2, 2) + ld(3, f3_val)


def claim_for_token(token: str, proxy: str = None):
    token = token.strip()
    if not token.startswith("g2g"):
        return {"status": "INVALID_TOKEN"}

    # Resolve gateway IP
    gw_ip = "13.202.85.79"
    try:
        infos = socket.getaddrinfo(GW_HOSTS[0], 9000, socket.AF_INET, socket.SOCK_STREAM)
        if infos:
            gw_ip = infos[0][4][0]
    except Exception:
        pass

    s = None
    try:
        if proxy:
            px = parse_proxy(proxy)
            s = socks5_connect(px, gw_ip, 9000, timeout=5.0)
        else:
            s = socket.create_connection((gw_ip, 9000), timeout=5.0)

        if not s:
            return {"status": "CONN_FAILED"}

        # 1. Handshake
        s.sendall(frame(pkt_hello()) + frame(pkt_hello2()))
        raw_120 = None
        for _ in range(5):
            raw = read_frame(s, timeout=2.0)
            if not raw:
                break
            msg = decode_frame(raw)
            if msg.mt == 120:
                raw_120 = raw
                break

        if not raw_120:
            s.close()
            return {"status": "HANDSHAKE_FAILED"}

        # 2. Login
        msg_120 = decode_frame(raw_120)
        hs = handshake_key_from_mt120(msg_120)
        f1 = _server_login_f1(hs) if hs else None
        fmt = {1: "v1", 2: "acct2", 3: "acct3", 4: "v4", 5: "f5"}.get(f1, "v1")
        wire = remint_wire_ticket(token, shape=fmt)
        s.sendall(frame(pkt_login(wire, plain=False)))

        # Wait for profile login confirmation
        logged_in = False
        for _ in range(6):
            raw = read_frame(s, timeout=2.0)
            if not raw:
                break
            msg = decode_frame(raw)
            if msg.op == 1 or len(raw) > 400:
                logged_in = True
                break

        if not logged_in:
            s.close()
            return {"status": "LOGIN_FAILED"}

        # 3. Claim Mission Takedown Tiers (1 to 20)
        results = []
        potions_to_open = []

        for tier_num in range(1, 21):
            tier_str = str(tier_num)
            claim_pkt = make_claim_mission_takedown(EVENT_NAME, tier_str)
            s.sendall(frame(claim_pkt))
            time.sleep(0.12)

            resp_raw = read_frame(s, timeout=1.2)
            if resp_raw:
                resp_str = "".join(chr(b) if 32 <= b <= 126 else "." for b in resp_raw)
                if EVENT_NAME in resp_str:
                    # Successfully claimed tier!
                    rewards_found = []
                    if "coin" in resp_str:
                        rewards_found.append("Coins")
                    if "potion_rare_brewless" in resp_str:
                        rewards_found.append("Rare Potion")
                        potions_to_open.append("potion_rare_brewless")
                    if "potion_exotic_brewless" in resp_str:
                        rewards_found.append("Exotic Potion")
                        potions_to_open.append("potion_exotic_brewless")
                    if "potion_battle_brewless" in resp_str:
                        rewards_found.append("Battle Potion")
                        potions_to_open.append("potion_battle_brewless")

                    r_label = ", ".join(rewards_found) if rewards_found else "Progress"
                    results.append(f"Tier {tier_str}: {r_label}")

        # 4. Open any won brewless potions
        opened_potions = []
        for pot in potions_to_open:
            open_pkt = make_open_brewless_potion(pot)
            s.sendall(frame(open_pkt))
            time.sleep(0.15)
            pot_resp = read_frame(s, timeout=1.5)
            opened_potions.append(pot)

        s.close()
        return {
            "status": "OK",
            "claimed_tiers": results,
            "opened_potions": opened_potions,
        }

    except Exception as e:
        if s:
            try:
                s.close()
            except Exception:
                pass
        return {"status": "ERROR", "error": str(e)}


if __name__ == "__main__":
    print("=" * 65)
    print(" 🎯 AGAR.IO MISSION TAKEDOWN (FUNGUS AMONGUS) AUTO-CLAIMER ")
    print("=" * 65)

    if len(sys.argv) > 1:
        target_token = sys.argv[1].strip()
    else:
        target_token = input("Token paste karein (ya Enter dabayein default token ke liye):\n> ").strip()

    if not target_token:
        target_token = "g2gDYQFtAAAAEBU5ykcB4wfMSWiCFxnIUYFtAAAAVWlbNBcTAXT3JAyXPVVNvFTJjsmJw2+q1SWxpLUQ0uwGxQZyCSeoO8CFImiVcmQ/ZF1YZNnYw0vnLcIBWciCXZvt8oVMQ6XqmFL1+Jl4mTmr3xy0zoQ="

    print(f"\n[*] Connecting & claiming Mission Takedown rewards...")
    res = claim_for_token(target_token)

    if res.get("status") == "OK":
        print(f"[✔] Success! Claimed {len(res.get('claimed_tiers', []))} tiers:")
        for t in res.get("claimed_tiers", []):
            print(f"    - {t}")
        if res.get("opened_potions"):
            print(f"[✔] Instant Potions Opened: {', '.join(res.get('opened_potions'))}")
    else:
        print(f"[!] Result: {res}")
