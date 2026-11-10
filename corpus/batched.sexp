; Batched publication: the producer writes all N cells, then publishes them
; with one store of N. The consumer takes them one at a time.
;
; Value v of count publishes data[v-1] = v, so the single store of N carries
; every cell at once, and each await gains just the next one.
;
; Expected: the store is rel, and the await is acq at every iteration.

(params (N 3))
(array data N)

(atomic count 0 (writer producer) (reader consumer)
  (protocol v (points-to data (- v 1) v)))

(thread producer (owns data 0 N)
  (for i 0 N
    (write data i (+ i 1)))
  (store p.count_store count N))

(thread consumer
  (for i 0 N
    (await c.count_await count (+ i 1))
    (read x data i)
    (assert x (+ i 1))))
