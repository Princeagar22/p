#!/usr/bin/env python3
"""
main.py — Production 24/7 Burst Arena Token, Virus & Pellet Farming Fleet
========================================================================
Optimized for Railway & Local Deployment.
- High-priority Burst Arena token vacuuming (25x weight)
- Safe virus consumption (+100 mass) when no larger enemy is nearby
- 360-degree predictive predator evasion & survival
- Multi-proxy rotation (SOCKS5/HTTP) or direct connection
- Built-in lightweight health check server for Railway cloud hosting
"""

import http.server
import json
import math
import os
import random
import signal
import socketserver
import sys
import threading
import time
from pathlib import Path

# Ensure local imports work cleanly
BASE_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(BASE_DIR))

try:
    from agar_bot_custom import AgarBot
except ImportError as err:
    print(f"[FATAL] Could not import AgarBot: {err}")
    sys.exit(1)

CONFIG_FILE = BASE_DIR / "config.txt"
TOKEN_FILE = BASE_DIR / "token.txt"
PROXIES_FILE = BASE_DIR / "proxies.txt"


def load_config():
    cfg = {
        "region": os.environ.get("REGION", "all"),
        "gamemode": os.environ.get("GAMEMODE", "burst"),
        "bot-mode": "solo",
        "solo-strategy": "farm",
        "bot-name": os.environ.get("BOT_NAME", "BURST-FARM"),
        "bot-num": int(os.environ.get("BOT_NUM", 10)),
        "proxy": int(os.environ.get("USE_PROXY", 1)),
        "bots-per-proxy": int(os.environ.get("BOTS_PER_PROXY", 1)),
    }
    if CONFIG_FILE.exists():
        for line in CONFIG_FILE.read_text(encoding="utf-8", errors="ignore").splitlines():
            line = line.strip()
            if not line or line.startswith("#") or "=" not in line:
                continue
            k, v = line.split("=", 1)
            cfg[k.strip().lower()] = v.strip()
    return cfg


def load_lines(filepath: Path):
    if not filepath.exists():
        return []
    lines = []
    for line in filepath.read_text(encoding="utf-8", errors="ignore").splitlines():
        line = line.strip()
        if line and not line.startswith("#"):
            lines.append(line)
    return lines


def format_proxy(raw: str) -> str:
    raw = raw.strip()
    if not raw:
        return ""
    if "@" in raw:
        return raw
    parts = raw.split()
    if len(parts) >= 3:
        return f"{parts[1]}:{parts[2]}@{parts[0]}"
    return parts[0]


# --- Optional Health Server for Railway HTTP Port Binding ---
class HealthHandler(http.server.SimpleHTTPRequestHandler):
    def do_GET(self):
        self.send_response(200)
        self.send_header("Content-Type", "application/json")
        self.end_headers()
        status = {
            "service": "agar-burst-farm",
            "uptime": time.time() - START_TIME,
            "bots_running": len([b for b in ACTIVE_BOTS if b.is_alive()]),
            "timestamp": time.strftime("%Y-%m-%d %H:%M:%S"),
        }
        self.wfile.write(json.dumps(status, indent=2).encode())

    def log_message(self, format, *args):
        pass  # Silent HTTP logs


def start_health_server(port):
    def run_srv():
        try:
            with socketserver.TCPServer(("", port), HealthHandler) as httpd:
                print(f"[+] Health-check HTTP server listening on port {port}")
                httpd.serve_forever()
        except Exception as e:
            print(f"[!] Health-check server error: {e}")

    t = threading.Thread(target=run_srv, daemon=True)
    t.start()


# --- Fleet Runner ---
ACTIVE_BOTS = []
STOP_EVENT = threading.Event()
START_TIME = time.time()

ALL_REGIONS = [
    "ap-south-1",
    "eu-central-1",
    "us-east-1",
    "ap-southeast-1",
    "us-west-1",
    "eu-west-2",
]


def run_single_bot(bot_idx, token, proxy, cfg):
    target_region = cfg.get("region", "all").strip().lower()
    if target_region == "all":
        region = ALL_REGIONS[bot_idx % len(ALL_REGIONS)]
    else:
        region = target_region

    gamemode = cfg.get("gamemode", "burst").strip().lower()
    nick = cfg.get("bot-name", "BURST-FARM")

    while not STOP_EVENT.is_set():
        try:
            print(f"[Bot #{bot_idx+1}] Connecting to {region} ({gamemode.upper()})...")
            bot = AgarBot(
                region=region,
                nick=nick,
                code=None,
                run_s=1000000,
                token=token,
                guest_v6=True,
                strategy="farm",
                no_party=True,
                proxy=proxy if cfg.get("proxy", 1) else None,
                proto="socks5" if proxy else "auto",
                enemy_clearance=1,
                arena_mode=gamemode,
            )

            # Register stats callback
            def on_stats_cb(st):
                if bot_idx == 0 or bot_idx % 5 == 0:
                    print(
                        f"[Bot #{bot_idx+1}] Mass: {st.get('mass', 0):<5.1f} | "
                        f"Ate: {st.get('ate', 0):<3} | Score: {st.get('score', 0):<4} | "
                        f"Mode: {st.get('mode', 'IDLE')}"
                    )

            bot.on_stats = on_stats_cb
            bot.run()
        except Exception as e:
            print(f"[Bot #{bot_idx+1}] Disconnected: {e}. Reconnecting in 5s...")
            time.sleep(5)


def main():
    print("=" * 65)
    print(" 🚀 AGAR.IO BURST ARENA TOKEN & VIRUS FARM FLEET ")
    print("=" * 65)

    # Railway assigns a dynamic PORT
    port = os.environ.get("PORT")
    if port:
        try:
            start_health_server(int(port))
        except Exception:
            pass

    cfg = load_config()
    tokens = load_lines(TOKEN_FILE)
    raw_proxies = load_lines(PROXIES_FILE)
    proxies = [format_proxy(p) for p in raw_proxies if p.strip()]

    num_bots = int(cfg.get("bot-num", 10))
    if not tokens:
        print("[!] No tokens found in token.txt! Running in guest mode.")
        tokens = [None] * num_bots

    print(f"[*] Configuration Loaded:")
    print(f"    - Target Gamemode : {cfg.get('gamemode', 'burst').upper()}")
    print(f"    - Target Region   : {cfg.get('region', 'all')}")
    print(f"    - Bots to Launch  : {num_bots}")
    print(f"    - Loaded Tokens   : {len(tokens)}")
    print(f"    - Loaded Proxies  : {len(proxies)}")
    print(f"    - Smart Virus Eat : ENABLED (Safe check without nearby predators)")
    print(f"    - Token Vacuum    : ENABLED (Highest Priority)")
    print("=" * 65)

    for i in range(num_bots):
        token = tokens[i % len(tokens)] if tokens else None
        proxy = proxies[i % len(proxies)] if proxies else None

        t = threading.Thread(
            target=run_single_bot,
            args=(i, token, proxy, cfg),
            name=f"FarmBot-{i+1}",
            daemon=True,
        )
        t.start()
        ACTIVE_BOTS.append(t)
        time.sleep(0.4)

    print(f"\n[✔] All {num_bots} bots successfully dispatched!")

    def handle_signal(sig, frame):
        print("\n[*] Stopping all bots gracefully...")
        STOP_EVENT.set()
        sys.exit(0)

    signal.signal(signal.SIGINT, handle_signal)
    signal.signal(signal.SIGTERM, handle_signal)

    while not STOP_EVENT.is_set():
        time.sleep(1)


if __name__ == "__main__":
    main()
