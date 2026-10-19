"""modes/feed.py — Eject and feed mechanics for agar bot.

Contains feed stream and mass dumping logic:
  1. Continuous rapid feed stream (W ejects) aimed directly at the operator center.
  2. Mass dump loop (_dump_mass) for emptying all mass down to server floor (18.0).
  3. FeedMode runner (_play_feed).

The stream's threat gate now uses the predictive threat scan (measured enemy
velocity), so a hunter running at us blocks the feed the instant it is inside
the danger horizon instead of a fixed static radius.

self is an AgarBot instance — see agar_bot_custom.py.
"""

import math
import time

FEED_FLOOR = 18.0
STREAM_DANGER_PAD = 320.0
STREAM_DANGER_PAD_GIANT = 680.0


class FeedMixin:
    """Feed mechanics mixin: continuous pellet streams and mass dumping."""

    def _stream_feed(
        self,
        me,
        tgt,
        bot_x: float,
        bot_y: float,
        jx: float,
        jy: float,
        dist_true: float,
        my_mass: float,
        is_aligned: bool,
        now: float,
        last_feed: float,
    ) -> tuple[bool, float]:
        """Aim directly at the operator cell center and emit a rapid stream of pellets."""
        if tgt is None or my_mass < 20.0:
            return False, last_feed

        # Check if an enemy is threatening us nearby (predictive threat scan)
        has_close_threat = False
        if hasattr(self, '_predict_threats'):
            for e, d, kill_r in self._predict_threats(me, tgt=tgt):
                is_giant = (getattr(e, 'mass', 0.0) >= my_mass * 1.85)
                danger_d = kill_r + (STREAM_DANGER_PAD_GIANT if is_giant else STREAM_DANGER_PAD)
                if d < danger_d:
                    has_close_threat = True
                    break
        elif hasattr(self, 'world') and self.world and hasattr(self, '_is_enemy_threat'):
            for e in self.world.entities.values():
                if self._is_enemy_threat(me, e, tgt=tgt):
                    d = math.hypot(e.x - bot_x, e.y - bot_y)
                    kill_r = getattr(e, 'r', 0.0) + getattr(me, 'r', 0.0)
                    is_giant = (getattr(e, 'mass', 0.0) >= my_mass * 1.85)
                    danger_d = kill_r + (STREAM_DANGER_PAD_GIANT if is_giant else STREAM_DANGER_PAD)
                    if d < danger_d:
                        has_close_threat = True
                        break

        if has_close_threat or not is_aligned:
            # Under active pursuit or dodging: keep joystick on escape heading (jx, jy)!
            self._send_joy((jx, jy), raw=True)
            return False, last_feed

        # Aim joystick directly at target cell center
        adx = tgt.x - bot_x
        ady = tgt.y - bot_y
        adist = math.hypot(adx, ady)
        if adist > 1e-5:
            aim_ux, aim_uy = adx / adist, ady / adist
        else:
            aim_ux, aim_uy = jx, jy

        self._send_joy((aim_ux, aim_uy), raw=True)

        # Rapid continuous stream into target
        self.do_feed(4, gap=0.015)

        tm = float(getattr(tgt, 'mass', 0.0) or 0.0)
        tname = getattr(tgt, 'name', '') or 'operator'

        if now - getattr(self, '_give_log_t', 0.0) > 1.0:
            self._give_log_t = now
            self.log(
                f'>>> [STREAM FEED -> OPERATOR] streaming continuous mass into {tname} '
                f'(bot={my_mass:.0f}, target={tm:.0f})'
            )

        return True, now

    def _dump_mass(self, timeout: float = 20.0, toward: str | None = None) -> int:
        """Eject everything we can down to the server's minimum floor (18.0)."""
        t0 = time.time()
        n0 = getattr(self, 'feeds', 0)
        floor = max(18.0, getattr(self, 'feed_keep', 18.0) if getattr(self, 'mode', '') == 'follow' else 18.0)
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

            # Send direct heading so mass ejects right at the target
            self._send_joy((heading[0], heading[1]), raw=True)
            self.do_feed(4, gap=0.015)
            time.sleep(0.015)

        n = getattr(self, 'feeds', 0) - n0
        self.log(f'[feed] dumped {n} ejects -> mass {self.world.total_mass:.1f}')
        return n

    def _play_feed(self, deadline) -> str:
        """botmode = feed — walk to the operator, dump all mass, repeat."""
        self.log('[feed-mode] every gram goes to the operator — walk in, dump, respawn, walk in again')
        prev_mode = self.mode
        prev_keep = self.feed_keep
        prev_split = getattr(self, 'split_feed', False)
        self.mode = 'follow'
        self.feed_keep = FEED_FLOOR
        self.split_feed = True
        try:
            return self._play_follow(deadline)
        finally:
            self.mode = prev_mode
            self.feed_keep = prev_keep
            self.split_feed = prev_split


# Alias for backward compatibility
FeedMode = FeedMixin
