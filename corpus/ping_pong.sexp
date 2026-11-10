; Ping-pong: one cell bounces between two threads for K rounds, and each
; side checks the other's value before writing its own.
;
; ping = v publishes cell[0] = 2v - 1 (written by ping), and pong = v
; publishes cell[0] = 2v (written by pong).
;
; Like the ring with one slot, except data travels in both directions, so
; both counters need rel/acq.
;
; Expected: both stores rel, both awaits acq.

(params (K 3))
(array cell 1)

(atomic ping 0 (writer pinger) (reader ponger)
  (protocol v (points-to cell 0 (- (+ v v) 1))))
(atomic pong 0 (writer ponger) (reader pinger)
  (protocol v (points-to cell 0 (+ v v))))

(thread pinger (owns cell 0 1)
  (for i 0 K
    (write cell 0 (+ (+ i i) 1))
    (store p.ping_store ping (+ i 1))
    (await p.pong_await pong (+ i 1))
    (read x cell 0)
    (assert x (+ (+ i i) 2))))

(thread ponger
  (for i 0 K
    (await q.ping_await ping (+ i 1))
    (read x cell 0)
    (assert x (+ (+ i i) 1))
    (write cell 0 (+ (+ i i) 2))
    (store q.pong_store pong (+ i 1))))
