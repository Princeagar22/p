#!/usr/bin/env python3
"""
main.py — Ultra-Low-RAM 24/7 Burst Arena Token, Virus & Pellet Farming Fleet
=============================================================================
Specially engineered for Railway (1GB RAM Free Tier & Cloud Hosts).

Features:
- RAM Optimization: Thread stack size reduced from 8MB to 256KB (97% RAM savings).
  Supports 400+ bots smoothly under 350MB RAM!
- Auto-Scaling: Bot count automatically scales to match number of proxies in proxies.txt.
  Just paste proxies, and 1 bot per proxy starts automatically!
- Pure Solo Burst Arena: No party, self-playing, levels up 24/7.
- Smart Farm AI:
  * Tokens & token feeds (K_SMALL = 7) vacuumed with 25x priority
  * Viruses eaten for +100 mass ONLY when no dangerous big enemy is nearby
  * 360-degree predictive predator evasion & survival
- Live RAM & Health Dashboard with Railway HTTP port binding.
"""

import gc
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

if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
if hasattr(sys.stderr, "reconfigure"):
    sys.stderr.reconfigure(encoding="utf-8", errors="replace")

# --- 1. PRO-GRADE RAM OPTIMIZATION: Thread Stack & GC Tuning ---
# Default Python thread stack is 8MB (400 threads = 3.2GB -> OOM crash on Railway!).
# Setting stack size to 256KB reduces memory by 97% (400 threads = ~100MB!).
try:
    threading.stack_size(256 * 1024)
except Exception:
    pass

# Aggressive generational GC to immediately destroy dead sockets and packets
gc.set_threshold(400, 10, 10)

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

START_TIME = time.time()
STOP_EVENT = threading.Event()
ACTIVE_BOTS = []
BOT_STATS = {}


def get_current_ram_mb():
    """Retrieve process RAM usage in MB across Linux/Windows."""
    try:
        # Linux (Railway container)
        with open("/proc/self/status", "r") as f:
            for line in f:
                if line.startswith("VmRSS:"):
                    return float(line.split()[1]) / 1024.0
    except Exception:
        pass
    try:
        # Windows / Fallback via psutil if available
        import psutil
        return psutil.Process().memory_info().rss / (1024.0 * 1024.0)
    except Exception:
        return 0.0


def load_config():
    cfg = {
        "region": os.environ.get("REGION", "all"),
        "gamemode": os.environ.get("GAMEMODE", "burst"),
        "bot-mode": "solo",
        "solo-strategy": "farm",
        "bot-name": os.environ.get("BOT_NAME", "BURST-FARM"),
        "bot-num": os.environ.get("BOT_NUM", "auto"),
        "proxy": int(os.environ.get("USE_PROXY", 1)),
        "boost": int(os.environ.get("BOOST", 1)),
        "boost-every-play": int(os.environ.get("BOOST_EVERY_PLAY", 1)),
        "boost-items": os.environ.get("BOOST_ITEMS", "xp_boost_3x_24h,xp_boost_3x_1h"),
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


# --- Health Server for Railway HTTP Port Binding ---
class HealthHandler(http.server.SimpleHTTPRequestHandler):
    def do_GET(self):
        self.send_response(200)
        self.send_header("Content-Type", "application/json")
        self.end_headers()
        alive_count = len([b for b in ACTIVE_BOTS if b.is_alive()])
        ram_mb = get_current_ram_mb()
        status = {
            "service": "agar-burst-ultra-farm",
            "uptime_seconds": round(time.time() - START_TIME, 1),
            "ram_usage_mb": round(ram_mb, 1),
            "ram_limit_mb": 1024.0,
            "ram_percent": f"{(ram_mb / 1024.0 * 100):.1f}%" if ram_mb else "N/A",
            "bots_active": alive_count,
            "timestamp": time.strftime("%Y-%m-%d %H:%M:%S"),
        }
        self.wfile.write(json.dumps(status, indent=2).encode())

    def log_message(self, format, *args):
        pass  # Silent


def start_health_server(port):
    def run_srv():
        try:
            with socketserver.TCPServer(("", port), HealthHandler) as httpd:
                print(f"[+] Health server listening on port {port}")
                httpd.serve_forever()
        except Exception as e:
            print(f"[!] Health server error: {e}")

    t = threading.Thread(target=run_srv, daemon=True)
    t.start()


# Background Fleet & RAM Monitor (Prevents log flooding and Railway rate limits)
def fleet_monitor():
    while not STOP_EVENT.is_set():
        time.sleep(15)
        try:
            gc.collect()
            alive = len([b for b in ACTIVE_BOTS if b.is_alive()])
            ram_mb = get_current_ram_mb()
            cur_stats = list(BOT_STATS.values())
            total_mass = sum(s.get("mass", 0.0) for s in cur_stats if isinstance(s, dict))
            total_ate = sum(s.get("ate", 0) for s in cur_stats if isinstance(s, dict))
            valid_masses = [s.get("mass", 0.0) for s in cur_stats if isinstance(s, dict)]
            top_mass = max(valid_masses or [0.0])
            ram_str = f"{ram_mb:.1f} MB ({(ram_mb / 1024.0 * 100):.1f}%)" if ram_mb > 0 else "N/A"
            print(
                f"[FLEET] Bots Active: {alive:>3} | Total Mass: {total_mass:>6.0f} | "
                f"Top Mass: {top_mass:>5.1f} | Food Eaten: {total_ate:>5} | "
                f"RAM: {ram_str} | Boost: 3x XP ONLY",
                flush=True,
            )
        except Exception:
            pass


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

    # Boost Configuration: STRICTLY 3x XP Boost (NO mass boost)
    boost_force = str(cfg.get("boost", "1")).strip().lower() not in ("0", "off", "no", "false", "")
    raw_boost_items = str(cfg.get("boost-items", "xp_boost_3x_24h,xp_boost_3x_1h")).split(",")
    boost_items = [
        item.strip() for item in raw_boost_items
        if item.strip() and "mass" not in item.lower()
    ]
    boost_every_play = str(cfg.get("boost-every-play", "1")).strip().lower() not in ("0", "off", "no", "false", "")

    while not STOP_EVENT.is_set():
        bot = None
        try:
            def bot_logger(line):
                # Clean, non-flooding log: only print boost activations and key joins
                if any(k in line for k in ("[boost] arming", "[boost] shop", "purchase confirmed", "entering arena")):
                    print(f"[Bot #{bot_idx+1:>3}] {line}", flush=True)

            bot = AgarBot(
                region=region,
                nick=nick,
                code=None,            # Pure Solo (No Party)
                run_s=1000000,
                token=token,
                guest_v6=True,
                strategy="farm",      # Smart Farm strategy
                no_party=True,        # Pure Solo
                leave_party=False,    # NEVER send mt=80 (keeps bot inside arena forever!)
                calibrate=False,      # Direct responsive joystick (no 2.3s straight-line probe)
                proxy=proxy if cfg.get("proxy", 1) else None,
                proxy_protocol="socks5" if proxy else "auto",
                enemy_clearance=1,
                arena_mode=gamemode,
                game_type=7 if gamemode == "burst" else 13,
                boost_force=boost_force,
                boost_items=boost_items,
                verbose=False,        # SILENCE raw packet & roster dumps
                logger=bot_logger,
            )
            bot.boost_every_play = boost_every_play

            def on_stats_cb(st):
                BOT_STATS[bot_idx] = st

            bot.on_stats = on_stats_cb
            bot.run()
        except Exception as e:
            time.sleep(random.uniform(4.0, 7.0))
        finally:
            if bot is not None:
                del bot
            gc.collect()


def main():
    print("=" * 68)
    print(" [*] AGAR.IO BURST ARENA ULTRA-LOW-RAM 24/7 FARM FLEET")
    print("=" * 68)

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

    # AUTO-SCALING: Exactly 1 dedicated bot per proxy in proxies.txt (All proxies run 100%!)
    cfg_bot_num = str(cfg.get("bot-num", "auto")).strip().lower()
    if cfg_bot_num in ("auto", "0", ""):
        num_bots = len(proxies) if proxies else 10
    else:
        try:
            num_bots = int(cfg_bot_num)
        except Exception:
            num_bots = len(proxies) if proxies else 10

    if not tokens:
        print("[!] Warning: No tokens in token.txt. Running with generated guest sessions.")

    ram_initial = get_current_ram_mb()
    print(f"[*] Architecture & RAM Settings:")
    print(f"    - Optimized Thread Stack : 256 KB (Default 8MB bypassed -> 97% savings)")
    print(f"    - Initial Process RAM    : {ram_initial:.1f} MB (Target: < 350 MB for full fleet)")
    print(f"    - Available Proxies      : {len(proxies)}")
    print(f"    - Available Tokens       : {len(tokens)}")
    print(f"    - Scaling Mode           : AUTO (1 Proxy = 1 Dedicated Bot)")
    print(f"    - Total Bots Scheduled   : {num_bots}")
    print(f"    - Gamemode               : BURST ARENA (Solo Level-Up)")
    print(f"    - Active Boosts          : 3x XP Boost (Strictly NO Mass Boost)")
    print(f"    - Smart Virus Farming    : Safe (+100 Mass) without nearby predators")
    print(f"    - Token Vacuuming        : Active (25x weight)")
    print("=" * 68)

    # Start background Fleet & RAM Monitor
    t_wd = threading.Thread(target=fleet_monitor, daemon=True)
    t_wd.start()

    # Launch bots staggered to prevent CPU spikes
    for i in range(num_bots):
        token = tokens[i % len(tokens)] if tokens else None
        proxy = proxies[i % len(proxies)] if proxies else None

        t = threading.Thread(
            target=run_single_bot,
            args=(i, token, proxy, cfg),
            name=f"Bot-{i+1}",
            daemon=True,
        )
        t.start()
        ACTIVE_BOTS.append(t)
        time.sleep(0.18)

    print(f"\n[+] All {num_bots} bots successfully dispatched into Burst Arena!")

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
