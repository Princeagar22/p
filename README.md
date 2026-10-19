# 🚀 Agar.io Burst Arena Token, Virus & Pellet 24/7 Farm Fleet

Automated high-performance cloud farming bot fleet for **Agar.io Mobile (Burst Arena & Classic FFA)**. Ready to deploy on **Railway** or any Docker/VPS environment.

---

## ✨ Features

- **🎯 Burst Arena Token Vacuuming:**
  Automatically tracks and vacuums tokens, token feeds, and ejected mass (`K_SMALL = 7`) with a **25x priority weight**.
- **🦠 Intelligent Safe Virus Farming:**
  - **Safe Zone:** When cell mass is $\ge 125$ and **NO dangerous enemy player** is within 1200 units, the bot aggressively eats the virus for an instant **+100 mass boost** and rapid token leveling.
  - **Danger Zone:** If a predator with mass $\ge 85\%$ of the bot is nearby, viruses are treated as hard hazards and avoided at all costs so the bot never gets split and eaten!
  - **Small Cell Defense:** While small ($< 125$ mass), viruses cannot split the bot and can be used as shields against predators.
- **🛡️ 360° Predictive Threat Evasion:**
  Real-time enemy velocity modeling with hard veto rays around hostile kill radii.
- **🌐 Cloud Ready:**
  Pre-configured with `Dockerfile` and `Procfile` for instant 1-click Railway deployment.
- **🔄 Multi-Proxy Rotation:**
  Supports SOCKS5/HTTP proxy pools or direct connections.

---

## 📁 Repository Structure

```text
burst-farm-railway/
├── main.py                # Fleet orchestrator & Railway entrypoint
├── agar_bot_custom.py     # Protocol parser & game engine
├── game_types.json        # Burst (7) & Classic (13) playlist mappings
├── modes/                 # 360-degree avoidance & steering algorithms
├── config.txt             # Easy fleet configuration
├── token.txt              # Accounts / tokens to farm
├── proxies.txt            # Live proxies for multi-botting
├── Dockerfile             # Production container for Railway
├── Procfile               # Railway worker process specification
├── requirements.txt       # Python dependencies
└── START_BURST_FARM.bat   # 1-click local launcher for Windows
```

---

## 🛠️ How to Push to GitHub

In PowerShell / Terminal:
```bash
cd d:\agarBot\burst-farm-railway
git init
git add .
git commit -m "feat: initial commit for agar burst farm bot"
git branch -M main
git remote add origin https://github.com/YOUR_USERNAME/YOUR_REPO_NAME.git
git push -u origin main
```

---

## 🚂 How to Deploy on Railway

1. Go to [railway.app](https://railway.app/) and log in with your GitHub account.
2. Click **New Project** -> **Deploy from GitHub repo**.
3. Select this repository.
4. Railway will automatically detect the `Dockerfile` or `Procfile` and begin building.
5. In **Variables** (Environment Settings), you can optionally set:
   - `BOT_NUM`: Number of bots (default: `10`)
   - `GAMEMODE`: `burst` (default) or `classic`
   - `REGION`: `all` (distributes across 6 global regions)
6. That's it! Your bot fleet will run 24/7 in the cloud.

---

## 💻 Local Testing on Windows

Simply double-click:
`START_BURST_FARM.bat`
