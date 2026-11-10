; Message passing: the producer fills a buffer, then raises a flag. The
; consumer waits for the flag, then reads the buffer.
;
; Expected: the flag's store is rel (it publishes both cells) and the await
; is acq (it gains them). The classic MP litmus test, with a payload.

(array data 2)

(atomic ready 0 (writer producer) (reader consumer)
  (protocol v (points-to data 0 42) (points-to data 1 43)))

(thread producer (owns data 0 2)
  (write data 0 42)
  (write data 1 43)
  (store p.ready_store ready 1))

(thread consumer
  (await c.ready_await ready 1)
  (read x data 0)
  (assert x 42)
  (read y data 1)
  (assert y 43))
