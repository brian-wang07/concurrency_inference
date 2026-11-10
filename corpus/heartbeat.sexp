; Heartbeat: a counter that carries no data. The worker bumps it K times,
; and the monitor waits until it reaches K.
;
; The protocol publishes nothing, so no access needs to synchronize.
;
; Expected: everything rlx. This checks the engine doesn't add orderings
; just because a thread waits on an atomic.

(params (K 3))

(atomic beat 0 (writer worker) (reader monitor)
  (protocol v))

(thread worker
  (for i 0 K
    (store w.beat_store beat (+ i 1))))

(thread monitor
  (await m.beat_await beat K))
