(params (N 2) (K 3))
(array slots N)

(atomic tail 0 (writer producer) (reader consumer)
  (protocol v (points-to slots (% (- v 1) N) v)))
(atomic head 0 (writer consumer) (reader producer)
  (protocol v (own slots (% (- v 1) N))))

(thread producer (owns slots 0 N)
  (for i 0 K
    (load t p.tail_load tail)
    (await p.head_await head (+ (- t N) 1))
    (write slots (% t N) (+ t 1))
    (store p.tail_store tail (+ t 1))))

(thread consumer
  (for i 0 K
    (load h c.head_load head)
    (await c.tail_await tail (+ h 1))
    (read x slots (% h N))
    (assert x (+ h 1))
    (store c.head_store head (+ h 1))))
