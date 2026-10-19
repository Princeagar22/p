"""modes/split.py — Split mechanics for agar bot.

Contains all split logic:
  1. Clear-corridor sprint: full map-travel when far from the operator (> 2500 units)
     — only while the entire travel corridor is provably clear of enemies.
     The old version SPLIT to sprint, which created a second ~22-mass piece
     that flew into unchecked space and was eaten (the split pieces also stole
     the joystick from the main cell).  A merged cell is already at full
     speed, so the sprint is now the beeline itself with a hard corridor veto.
  2. Safe Split Feed: Continuous double-split feed combo directly into the operator
     (Space + Space + W rapid burst) safely transferring all mass down to the operator,
     strictly conditioned on having zero enemy threats nearby — now checked with the
     predictive threat model (measured enemy velocity included).

Separated into its own file so split distances, safety ratios, and split triggers
can be edited and tuned without touching follow, feed, avoid, or leave logic.

self is an AgarBot instance — see agar_bot_custom.py.
"""

import math
import time

# A threat closer than kill_r + SPLIT_DANGER_PAD blocks any split.
SPLIT_DANGER_PAD = 380.0
SPLIT_DANGER_PAD_GIANT = 750.0
# The travel corridor must be clear this far ahead before a far sprint.
CORRIDOR_CLEAR = 1500.0


class SplitMixin:
    """Split logic mixin: corridor sprint rush and safe operator feeding."""

    def _check_sprint_rush(
        self,
        me,
        ux: float,
        uy: float,
        dist_true: float,
        my_mass: float,
        my_cells: list,
        now: float,
        last_split: float,
    ) -> tuple[bool, float]:
        """Full-speed map-travel when far from operator (> 2500 units).

        ONLY while the whole corridor is 100% clear of enemies.  No split:
        splitting mid-journey created an unprotected second piece and halved
        the mass of both cells for zero speed gain (a merged cell already
        moves at full speed).
        """
        if dist_true <= 2500.0 or my_mass < 45.0 or len(my_cells) > 1:
            return False, last_split

        if hasattr(self, '_nearest_threat_dist'):
            nd = self._nearest_threat_dist(me, cells=my_cells, tgt=None)
            if nd < CORRIDOR_CLEAR:
                return False, last_split  # enemy in the corridor: never sprint

        self._send_joy((ux, uy), raw=True)
        return True, now

    def _check_safe_split_feed(
        self,
        me,
        tgt,
        dist_true: float,
        touch_dist: float,
        my_mass: float,
        my_cells: list,
        is_aligned: bool,
        now: float,
        last_split: float,
    ) -> tuple[bool, float]:
        """Safely split mass directly into the operator using rapid double-split combo.

        Matches exact pro-human split pattern recorded in capture-main-8.json:
          - Re-aim directly at operator center
          - First split piece flies directly into operator (mt=47)
          - Immediate rapid ejects (mt=69)
          - If mass permits, second split (double-split! mt=47) directly into operator
          - Continuous cycles until all mass is transferred!
          - STRICTLY ABORT if any enemy threat is nearby (predictive check)
        """
        if tgt is None:
            return False, last_split

        # Split enabled by default in follow & feed modes unless explicitly turned off
        if not getattr(self, 'split_feed', True):
            return False, last_split

        # 1. ENEMY THREAT CHECK (predictive): never split if an enemy can
        #    intercept, eat a piece, or eat us while we are in 2 pieces!
        if hasattr(self, '_predict_threats'):
            biggest = max(my_cells, key=lambda c: getattr(c, 'mass', 0.0), default=me)
            for e, d, kill_r in self._predict_threats(me, cells=my_cells, tgt=tgt):
                is_giant = (getattr(e, 'mass', 0.0) >= biggest.mass * 1.85)
                danger = kill_r + (SPLIT_DANGER_PAD_GIANT if is_giant else SPLIT_DANGER_PAD)
                if d < danger:
                    return False, last_split  # Enemy too close: hold pieces together and evade!
        elif hasattr(self, 'world') and self.world and hasattr(self, '_is_enemy_threat'):
            for e in self.world.entities.values():
                if self._is_enemy_threat(me, e, tgt=tgt):
                    d = math.hypot(e.x - me.x, e.y - me.y)
                    kill_r = getattr(e, 'r', 0.0) + getattr(me, 'r', 0.0)
                    is_giant = (getattr(e, 'mass', 0.0) >= me.mass * 1.85)
                    danger_d = kill_r + (SPLIT_DANGER_PAD_GIANT if is_giant else SPLIT_DANGER_PAD)
                    if d < danger_d:
                        return False, last_split

        tm = float(getattr(tgt, 'mass', 0.0) or 0.0)
        if tm <= 0:
            return False, last_split

        largest_piece = max((c.mass for c in my_cells), default=getattr(me, 'mass', 0.0))
        if largest_piece < 36.0:
            return False, last_split

        split_piece_mass = largest_piece * 0.50

        # Safety: operator MUST be safely larger than our bot (1.20x) to avoid eating/killing operator!
        is_safe_for_operator = (tm >= max(my_mass * 1.20, 50.0))

        # Distance threshold: Agar.io split ejection travels ~500 to 650 units
        split_range = max(touch_dist + 480.0, 650.0)

        # Alignment: aiming at operator center (or already close enough that alignment is guaranteed)
        aim_valid = is_aligned or dist_true <= 320.0

        can_split = (
            is_safe_for_operator
            and dist_true <= split_range
            and aim_valid
            and (now - last_split >= 0.22)
            and len(my_cells) < 8
        )

        if not can_split:
            return False, last_split

        # 1. Aim joystick directly at target cell center
        dx = tgt.x - me.x
        dy = tgt.y - me.y
        d_norm = math.hypot(dx, dy)
        if d_norm > 1e-5:
            aim_x, aim_y = dx / d_norm, dy / d_norm
            self._send_joy((aim_x, aim_y), raw=True)

        # 2. 16-Split macro directly into operator center
        if hasattr(self, 'do_16_split'):
            self.do_16_split(gap=0.015)
        else:
            self.do_split(count=4, gap=0.015)
        self.do_feed(4, gap=0.015)

        if now - getattr(self, '_give_log_t', 0.0) > 0.8:
            self._give_log_t = now
            tname = getattr(tgt, 'name', '') or 'operator'
            self.log(
                f'>>> [SPLIT-FEED -> OPERATOR] double-split mass delivered to {tname} '
                f'(bot={my_mass:.0f}, target={tm:.0f})'
            )

        return True, now
