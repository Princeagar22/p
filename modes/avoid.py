"""modes/avoid.py — 360-degree pro-human enemy avoidance & fleet collision system.

Guarantees the bot NEVER enters or gets absorbed by ANY hostile enemy cell or dangerous virus.
Fleet sibling bots ('ggs' and party members) are recognized as allies so the 50-bot swarm
never deadlocks, blocks, or freezes each other, while larger siblings are gently skirted around
to completely prevent friendly cannibalism.
Includes accurate operator safe-haven shielding: when your operator is physically nearby
and larger than the enemy, the bot utilizes the operator as a protective shield.

v2 — PREDICTIVE AVOIDANCE (bug-free rewrite)
--------------------------------------------
The old version scored 32 rays against enemies' CURRENT positions at three fixed
look steps (120/240/420) and treated them as static.  Measured in crowded live
traffic that left the bot grazing inside kill radii (negative margins of a few
units -> "galti se bhi enemy ke andar").  The rewrite:

  1. Every entity gets a REAL VELOCITY (per-id position cache, ~20 Hz samples).
  2. Each candidate ray is simulated forward 1.25 s against every threat's
     estimated motion, for EVERY one of our own cells (split pieces included).
  3. A ray is INFEASIBLE (hard veto) if any own cell would come within
     ``kill_r + SAFE_MARGIN`` of any enemy at any sampled time.
  4. Among feasible rays we minimise: threat proximity + distance-to-goal +
     angular jitter + wall/corner penalties.  Among infeasible rays (truly
     surrounded) we take the maximum-clearance escape — still better than
     beelining into the kill radius.
  5. Giant enemies (>= 1.85x our mass) are modelled with a split-dash cone:
     they can split toward us, so their effective approach speed is multiplied
     by DASH_MUL and aimed at us.
  6. Viruses only count once we are heavy enough to be split by them (>= 130).

`self` is an AgarBot instance — see agar_bot_custom.py.
"""

import math
import time

# Entity kinds (matching agar_bot_custom definitions)
K_FOOD = 2
K_VIRUS = 3
K_SMALL = 7
K_CELL = 8

VIRUS_SPLIT_MASS = 130.0
DEFAULT_MARGIN = 75.0

# ---- predictive avoidance constants ------------------------------------- #
NUM_RAYS = 48                 # 7.5-degree directional resolution
HORIZON_TICKS = 25            # 1.25 s at the 20 Hz control rate
HORIZON_SAMPLES = 9           # time slices simulated along each ray
SAFE_MARGIN = 62.0            # hard veto margin beyond the kill radius
BOT_SPEED = 60.0              # units/tick at mass 10 (conservative-high)
ENEMY_SPEED = 56.0            # units/tick at mass 10 (assume they are FAST)
SPEED_EXP = -0.44             # agar.io speed ~ mass^-0.44
DASH_MUL = 1.7                # giant split-dash speed multiplier
STANDOFF_PAD = 400.0          # preferred standoff (normal threat)
STANDOFF_PAD_GIANT = 720.0    # preferred standoff (giant splitter)
WALL_PAD = 260.0
CORNER_MUL = 2.2
EMERGENCY_R = 190.0           # closer than kill_r+this -> emergency (no inertia)
ARENA_FALLBACK = 11180.0


def _speed_at(mass: float, base: float) -> float:
    """Cell speed in units/tick for a given mass (agar.io ~mass^-0.44)."""
    return base * (max(float(mass), 1.0) / 10.0) ** SPEED_EXP


class AvoidEnemyMixin:
    """360-degree obstacle and enemy avoidance mixin.

    Ensures the bot stays safely outside the kill radius of all enemy cells
    and dangerous viruses from any direction (front, flank, or rear), using a
    predictive collision model instead of reactive steering.
    """

    def _is_target_cell(self, e) -> bool:
        """True if entity e strictly matches our follow target UUID / key (NO name matching)."""
        if e is None or getattr(e, 'is_self', False):
            return False
        eu = (getattr(e, 'uuid', '') or '').lower().strip()
        if not eu:
            return False

        eu_clean = eu.replace('-', '')

        raw_key = (getattr(self, 'follow', '') or '').lower().strip()
        uid_t = str(getattr(self, 'uid_target', '') or '').lower().strip()

        all_keys = set()
        for k_src in [raw_key, uid_t]:
            if not k_src:
                continue
            for part in k_src.split(','):
                p = part.strip()
                if p:
                    all_keys.add(p)
                    p_clean = p.replace('-', '')
                    all_keys.add(p_clean)
                    if len(p_clean) >= 8:
                        all_keys.add(p_clean[:8])
                    if len(p) >= 8:
                        all_keys.add(p[:8])

        if not all_keys:
            return False

        if eu in all_keys or eu_clean in all_keys:
            return True

        return any(len(k) >= 8 and (eu.startswith(k[:8]) or eu_clean.startswith(k[:8]) or k.startswith(eu[:8])) for k in all_keys if k)

    def _is_sibling(self, e) -> bool:
        """True if entity e is a fleet sibling bot ('ggs' or party roster member)."""
        if e is None or getattr(e, 'is_self', False):
            return False

        # Exclude operator target
        if self._is_target_cell(e):
            return False

        en = (getattr(e, 'name', '') or '').lower().strip()
        bot_nick = (getattr(self, 'nick', '') or 'ggs').lower().strip()
        if en and (en == bot_nick or en == 'ggs'):
            return True

        eu = (getattr(e, 'uuid', '') or '').lower().strip()
        if eu:
            friendly = getattr(self, '_friendly_uuids_cache', None)
            now = time.time()
            cache_t = getattr(self, '_friendly_uuids_cache_t', 0.0)
            if friendly is None or (now - cache_t > 3.0):
                friendly = self._friendly_uuids() if hasattr(self, '_friendly_uuids') else set()
                self._friendly_uuids_cache = friendly
                self._friendly_uuids_cache_t = now
            if eu in friendly or any(eu.startswith(f[:8]) or f.startswith(eu[:8]) for f in friendly if len(f) >= 8):
                return True

        if hasattr(self, '_party_mate_names'):
            try:
                p_names = getattr(self, '_party_names_cache', None)
                now = time.time()
                p_cache_t = getattr(self, '_party_names_cache_t', 0.0)
                if p_names is None or (now - p_cache_t > 3.0):
                    p_names = self._party_mate_names()
                    self._party_names_cache = p_names
                    self._party_names_cache_t = now
                if en and en in p_names:
                    return True
            except Exception:
                pass

        return False

    def _is_enemy_threat(self, me, e, tgt=None) -> bool:
        """Return True if entity e is a hostile enemy that can eat or split me."""
        if e is None or me is None or getattr(e, 'is_self', False):
            return False

        # Target / operator cell is NEVER an enemy (operator is our destination!)
        if tgt is not None and e.id == tgt.id:
            return False
        if self._is_target_cell(e):
            return False

        # Sibling bots are allies (handled separately for close-range collision avoidance)
        if self._is_sibling(e):
            return False

        if e.kind == K_CELL:
            # Genuine hostile player cell that can absorb us (>= 1.12x mass)
            return e.mass >= me.mass * 1.12

        if e.kind == K_VIRUS:
            return me.mass >= VIRUS_SPLIT_MASS

        return False

    # ------------------------------------------------------------- helpers #
    def _entity_velocity(self, e, now: float) -> tuple[float, float]:
        """Measured world-space velocity of an entity (units/sec), 0 if unknown.

        The arena streams full snapshots and deltas at ~40 Hz while our control
        loop runs at 20 Hz, so consecutive ticks are a good velocity sample.
        The cache is per entity id and pruned so it cannot grow unbounded.
        """
        cache = getattr(self, '_avoid_ent_xy', None)
        if cache is None:
            cache = {}
            self._avoid_ent_xy = cache
        prev = cache.get(e.id)
        vx = vy = 0.0
        if prev is not None:
            px, py, pt = prev
            dt = now - pt
            if 0.015 < dt < 0.6:
                vx = (e.x - px) / dt
                vy = (e.y - py) / dt
                sp = math.hypot(vx, vy)
                if sp > 1800.0:
                    vx = vx * 1800.0 / sp
                    vy = vy * 1800.0 / sp
        cache[e.id] = (e.x, e.y, now)
        if len(cache) > 600:
            # keep only the most recently sampled half
            items = sorted(cache.items(), key=lambda kv: kv[1][2])
            self._avoid_ent_xy = dict(items[len(items) // 2:])
        return vx, vy

    def _predict_threats(self, me, cells=None, tgt=None) -> list:
        """Static-distance threat scan shared by follow/feed/split gating.

        Returns a list of ``(entity, dist, kill_r)`` for hostile enemies and
        dangerous viruses that could catch us within their danger horizon.
        """
        out = []
        if me is None or self.world is None:
            return out
        cells = list(cells) if cells else [me]
        biggest = max(cells, key=lambda c: getattr(c, 'mass', 0.0))
        for e in self.world.entities.values():
            if getattr(e, 'is_self', False):
                continue
            if not self._is_enemy_threat(biggest, e, tgt=tgt):
                continue
            dist = math.hypot(e.x - biggest.x, e.y - biggest.y)
            kill_r = float(getattr(e, 'r', 0.0)) + float(getattr(biggest, 'r', 0.0))
            out.append((e, dist, kill_r))
        out.sort(key=lambda t: t[1])
        return out

    def _nearest_threat_dist(self, me, cells=None, tgt=None) -> float:
        """Distance (world units) to the closest hostile threat, or 1e9."""
        ts = self._predict_threats(me, cells=cells, tgt=tgt)
        if not ts:
            return 1e9
        return ts[0][1]

    # ------------------------------------------------------- main avoider  #
    def _avoid_enemies(self, me, ux: float, uy: float, tgt=None, cells=None):
        """Pro-human 360-degree PREDICTIVE directional avoidance.

        Evaluates ``NUM_RAYS`` radial directions, simulating our own motion and
        every threat's measured motion forward ``HORIZON_TICKS`` ticks, and
        picks the direction that keeps every one of our cells outside
        ``kill_r + SAFE_MARGIN`` of every enemy at ALL times — while staying
        as close to the goal (ux, uy) as safety allows.

        Threat model (verified against capture-node-22.json):
          * enemies move with the agar.io speed curve (~mass^-0.44);
          * giants (>=1.85x our mass) get a split-dash cone: they can launch a
            piece at us, so they are simulated at DASH_MUL speed aimed at us;
          * viruses only threaten once we are >=130 mass;
          * measured entity velocity is preferred over the speed curve when the
            sample is fresh, so a player actively running at us is modelled
            accurately.
        """
        if me is None or self.world is None:
            return ux, uy

        cells = [c for c in (cells or []) if c is not None]
        if not cells:
            cells = [me]
        biggest = max(cells, key=lambda c: getattr(c, 'mass', 0.0))

        now = time.time()
        arena_size = float(getattr(self.world, 'arena', 0.0) or ARENA_FALLBACK)
        tgt_m = float(getattr(tgt, 'mass', 0.0) or 0.0) if tgt else 0.0
        tgt_r = float(getattr(tgt, 'r', 0.0) or 0.0) if tgt else 0.0

        # 1. gather threats ------------------------------------------------ #
        threats = []            # hostile enemies / dangerous viruses
        sibling_obstacles = []  # bigger fleet mates / operator-when-we-are-bigger
        is_emergency = False

        for e in self.world.entities.values():
            if getattr(e, 'is_self', False):
                continue
            dist = math.hypot(e.x - me.x, e.y - me.y)
            if dist < 1e-4:
                dist = 1e-4
            kill_r = float(getattr(e, 'r', 0.0)) + float(getattr(me, 'r', 0.0))

            # Sibling bot obstacle: if a larger sibling cell can absorb us, skirt it
            if self._is_sibling(e):
                for c in cells:
                    ck = float(getattr(e, 'r', 0.0)) + float(getattr(c, 'r', 0.0))
                    if e.mass >= c.mass * 1.15 and dist < ck + 120.0:
                        sibling_obstacles.append((dist, ck, e.x - me.x, e.y - me.y, e))
                continue

            # Operator when bot is larger: do not collide directly into operator
            if (tgt is not None and e.id == tgt.id) or self._is_target_cell(e):
                for c in cells:
                    ck = float(getattr(e, 'r', 0.0)) + float(getattr(c, 'r', 0.0))
                    dc = math.hypot(e.x - c.x, e.y - c.y)
                    if c.mass >= max(35.0, tgt_m * 1.15) and dc < ck + 60.0:
                        sibling_obstacles.append((dc, ck, e.x - c.x, e.y - c.y, e))
                continue

            if not self._is_enemy_threat(biggest, e, tgt=tgt):
                continue

            is_giant = (e.kind == K_CELL and e.mass >= biggest.mass * 1.85)
            is_virus = (e.kind == K_VIRUS)

            # Real geometric operator shield: operator is bigger than the enemy
            # AND physically between us and them -> the enemy cannot reach us.
            operator_shields = False
            if tgt is not None and tgt_m >= e.mass * 1.15:
                dist_to_tgt = math.hypot(tgt.x - me.x, tgt.y - me.y)
                if dist_to_tgt <= tgt_r + 350.0:
                    dist_tgt_to_e = math.hypot(e.x - tgt.x, e.y - tgt.y)
                    if dist_tgt_to_e <= dist + 80.0:
                        operator_shields = True

            # measured velocity (units/sec) -> per tick
            mvx, mvy = self._entity_velocity(e, now)
            tvx, tvy = mvx / 20.0, mvy / 20.0

            pairs = []
            for c in cells:
                ck = float(getattr(e, 'r', 0.0)) + float(getattr(c, 'r', 0.0))
                # is this enemy a threat to THIS cell specifically?
                if e.kind == K_CELL and e.mass < c.mass * 1.12:
                    continue
                if e.kind == K_VIRUS and c.mass < VIRUS_SPLIT_MASS:
                    continue
                pairs.append((c, ck))

            if not pairs:
                continue

            threat = {
                'e': e, 'x': e.x, 'y': e.y, 'r': float(getattr(e, 'r', 0.0)),
                'vx': tvx, 'vy': tvy, 'is_giant': is_giant, 'is_virus': is_virus,
                'shielded': operator_shields, 'pairs': pairs,
                'dist': dist, 'kill_r': kill_r,
            }
            threats.append(threat)
            emer = kill_r + EMERGENCY_R
            if dist <= emer and not operator_shields:
                is_emergency = True

        if not threats and not sibling_obstacles:
            self._last_avoid_heading = (ux, uy)
            self._last_avoid_angle = math.atan2(uy, ux)
            return ux, uy

        threats.sort(key=lambda t: t['dist'])

        # 2. ray search ---------------------------------------------------- #
        last_ang = getattr(self, '_last_avoid_angle', math.atan2(uy, ux))
        best_ang = math.atan2(uy, ux)
        best_cost = float('inf')
        best_feasible = False
        best_clear = -1.0          # max-clearance fallback bookkeeping
        escape_ang = math.atan2(uy, ux)

        # pre-compute per-threat per-pair simulation-independent data.
        # The FEASIBILITY scan samples EVERY tick — sampling every 2nd tick
        # left a ~100 ms blind window in which a closing enemy could cross the
        # kill band (measured: -1..-9 unit grazes in dense traffic).
        horizon = list(range(1, HORIZON_TICKS + 1))
        horizon_coarse = horizon[::max(1, HORIZON_TICKS // HORIZON_SAMPLES)]

        for i in range(NUM_RAYS):
            ang = i * (2.0 * math.pi / NUM_RAYS)
            rx = math.cos(ang)
            ry = math.sin(ang)

            cost = 0.0
            feasible = True
            min_clear_all = 1e9

            # 2a. wall / corner penalties
            future_x = me.x + rx * 350.0
            future_y = me.y + ry * 350.0
            wall_cost_x = wall_cost_y = 0.0
            if future_x < WALL_PAD:
                wall_cost_x = 35000.0 * (1.0 - max(0.0, future_x) / WALL_PAD) ** 2
            elif future_x > arena_size - WALL_PAD:
                wall_cost_x = 35000.0 * (1.0 - max(0.0, arena_size - future_x) / WALL_PAD) ** 2
            if future_y < WALL_PAD:
                wall_cost_y = 35000.0 * (1.0 - max(0.0, future_y) / WALL_PAD) ** 2
            elif future_y > arena_size - WALL_PAD:
                wall_cost_y = 35000.0 * (1.0 - max(0.0, arena_size - future_y) / WALL_PAD) ** 2
            if wall_cost_x > 0.0 and wall_cost_y > 0.0:
                cost += (wall_cost_x + wall_cost_y) * CORNER_MUL
            else:
                cost += wall_cost_x + wall_cost_y

            # 2b. sibling / operator obstacle penalties (static-ish, generous pad)
            for s_dist, s_kill_r, s_dx, s_dy, s_e in sibling_obstacles:
                s_dir_x = s_dx / s_dist
                s_dir_y = s_dy / s_dist
                s_approach = rx * s_dir_x + ry * s_dir_y
                if s_approach > 0.2:
                    for step_dist in (90.0, 180.0, 300.0):
                        px = me.x + rx * step_dist
                        py = me.y + ry * step_dist
                        if math.hypot(s_e.x - px, s_e.y - py) <= s_kill_r + 25.0:
                            cost += 250000.0 * (1.0 + s_approach)
                            break
                    proj = rx * s_dx + ry * s_dy
                    proj_s = max(0.0, min(s_dist, proj))
                    closest_d = math.hypot(s_dx - rx * proj_s, s_dy - ry * proj_s)
                    if closest_d <= s_kill_r + 30.0:
                        cost += 120000.0 * (1.0 + s_approach)

            # 2c. predictive enemy collision model
            for t in threats:
                shielded = t['shielded']
                shield_relief = 0.30 if shielded else 1.0
                # giant split-dash: aim their velocity straight at us, faster
                if t['is_giant']:
                    dx_us = (me.x - t['x'])
                    dy_us = (me.y - t['y'])
                    dn = math.hypot(dx_us, dy_us) or 1.0
                    e_mass = float(getattr(t['e'], 'mass', 0.0) or 0.0)
                    dash_v = _speed_at(e_mass if e_mass > 0 else (t['r'] ** 2) / 100.0,
                                       ENEMY_SPEED) * DASH_MUL
                    tvx_t = dx_us / dn * dash_v
                    tvy_t = dy_us / dn * dash_v
                else:
                    tvx_t = t['vx']
                    tvy_t = t['vy']

                worst_clear = 1e9
                max_kill = 0.0
                for (cell, ck) in t['pairs']:
                    if ck > max_kill:
                        max_kill = ck
                    vc = _speed_at(getattr(cell, 'mass', 10.0), BOT_SPEED)
                    for k in horizon:
                        px = cell.x + rx * vc * k
                        py = cell.y + ry * vc * k
                        ex = t['x'] + tvx_t * k
                        ey = t['y'] + tvy_t * k
                        sep = math.hypot(px - ex, py - ey) - (t['r'] + getattr(cell, 'r', 0.0))
                        if sep < worst_clear:
                            worst_clear = sep
                        if sep < -400.0:
                            break
                if worst_clear < min_clear_all:
                    min_clear_all = worst_clear

                if worst_clear < SAFE_MARGIN:
                    feasible = False

                # proximity preference even when feasible
                standoff = max_kill + (STANDOFF_PAD_GIANT if t['is_giant'] else STANDOFF_PAD)
                if worst_clear < standoff:
                    f = 1.0 - worst_clear / standoff
                    w = (9000.0 if t['is_giant'] else 6000.0) * f * f * shield_relief
                    cost += w

            # 2d. goal alignment reward
            goal_dot = rx * ux + ry * uy
            cost -= 700.0 * goal_dot

            # 2e. angular inertia smoothing (skip in emergency)
            if not is_emergency:
                ang_diff = (ang - last_ang + math.pi) % (2.0 * math.pi) - math.pi
                cost += 90.0 * (ang_diff * ang_diff)

            if feasible and (not best_feasible or cost < best_cost):
                best_cost = cost
                best_ang = ang
                best_feasible = True
            if (not best_feasible) and min_clear_all > best_clear:
                best_clear = min_clear_all
                escape_ang = ang

        if best_feasible:
            final_ang = best_ang
        else:
            # truly surrounded: take the maximum-clearance escape (never the
            # straight-into-the-enemy default)
            final_ang = escape_ang

        # 3. angular smoothing on the chosen heading ------------------------ #
        if best_feasible and not is_emergency:
            d_theta = (final_ang - last_ang + math.pi) % (2.0 * math.pi) - math.pi
            final_ang = last_ang + d_theta * 0.80
        elif is_emergency:
            # hard rule: in an emergency the heading must move AWAY from the
            # nearest threat; never let smoothing pull it back toward danger.
            nearest = threats[0]
            away = math.atan2(me.y - nearest['y'], me.x - nearest['x'])
            d_theta = (final_ang - away + math.pi) % (2.0 * math.pi) - math.pi
            final_ang = away + d_theta * 0.35

        final_h = (math.cos(final_ang), math.sin(final_ang))

        # 4. ABSOLUTE last-resort guard: never keep steering INTO a close
        #    threat, whatever the ray search decided (surrounded fallback,
        #    smoothing pull-back).  Guarantees an away-component whenever a
        #    threat is inside its stand band — the "galti se bhi andar nahi"
        #    rule, enforced even when every ray was infeasible.
        nearest = threats[0]
        band = nearest['kill_r'] + 260.0
        if nearest['dist'] < band:
            ax, ay = (me.x - nearest['x']), (me.y - nearest['y'])
            an = math.hypot(ax, ay) or 1.0
            ax, ay = ax / an, ay / an
            toward = final_h[0] * (-ax) + final_h[1] * (-ay)   # >0 == toward enemy
            if toward > 0.10:
                blend = min(1.0, 0.35 + toward * 1.6)
                bx = final_h[0] * (1.0 - blend) + ax * blend
                by = final_h[1] * (1.0 - blend) + ay * blend
                bn = math.hypot(bx, by) or 1.0
                final_h = (bx / bn, by / bn)
                final_ang = math.atan2(final_h[1], final_h[0])

        self._last_avoid_heading = final_h
        self._last_avoid_angle = final_ang
        return final_h

    def _skirt_enemies(self, me, ux: float, uy: float, tgt=None, cells=None):
        """Alias kept for compatibility — delegates to the predictive avoider."""
        return self._avoid_enemies(me, ux, uy, tgt=tgt, cells=cells)
