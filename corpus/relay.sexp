; Relay: a cell passes from a to b to c through two flags. b gains the cell
; from a, changes it, and passes it on.
;
; c never synchronizes with a directly: it sees a's write only through b, so
; this checks that ownership composes across a chain of hand-offs.
;
; Expected: both stores rel, both awaits acq.

(array buf 1)

(atomic f1 0 (writer a) (reader b)
  (protocol v (points-to buf 0 1)))
(atomic f2 0 (writer b) (reader c)
  (protocol v (points-to buf 0 2)))

(thread a (owns buf 0 1)
  (write buf 0 1)
  (store a.f1_store f1 1))

(thread b
  (await b.f1_await f1 1)
  (read x buf 0)
  (assert x 1)
  (write buf 0 2)
  (store b.f2_store f2 1))

(thread c
  (await c.f2_await f2 1)
  (read y buf 0)
  (assert y 2))
