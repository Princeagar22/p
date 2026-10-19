"""modes/leave.py — feed-leave mode without in-arena cycles.

Flow:
  1. Enters arena.
  2. Spawns with boost mass.
  3. Dumps feed to target cleanly (normal 70ms pacing) until mass floor reached (<= 32.5).
  4. Pulls backward cleanly.
  5. Leaves arena with mt=80 (pkt_leave_game) and closes arena connection.
  6. Re-enters arena and repeats endlessly until stopped.
"""

import math
import random
import time


class LeaveMode:
    """botmode = feed-leave (or leave) — enter arena -> feed -> leave arena loop."""

    def _play_leave(self, deadline) -> str:
        nick_str = (self.nick or '').strip() or 'b'
        play_packet = self.play_pkt(nick_str)

        from agar_bot_custom import pkt_feed, World, Brain, HeadingMap

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

                    # Keep tracking target dynamically
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
                    time.sleep(0.070)

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
            reentered = False
            if not is_inline and self.mm is not None and not self.mm_closed.is_set():
                self.world = World()
                self.brain = Brain(self.strategy)
                self.hmap = HeadingMap()
                if hasattr(self, '_request_arena_redirect') and self._request_arena_redirect(max_tries=20):
                    self._calibrate(deadline)
                    reentered = True

            if not reentered:
                self._arena_token_bounced = True
                return 'done'

        return 'done'


# Alias for feed-leave mode
FeedLeaveMode = LeaveMode
