; Load buffering (LB): each thread loads the other's flag, then raises its
; own. The litmus question is whether both loads can read 1.
;
; With all four accesses relaxed, ISO C++ allows that outcome, but RC11
; forbids it: its no-thin-air axiom makes po ∪ rf acyclic, and r1 = r2 = 1
; would need the cycle load_y -po-> store_x -rf-> load_x -po-> store_y -rf->
; load_y. So under RC11 no ordering is needed to rule it out.
;
; Neither flag carries data, and a loaded value is unknown to the checker,
; so the outcome can't be written as an assertion here; GenMC is where it
; gets checked.
;
; Expected: everything rlx.

(atomic x 0 (writer t1) (reader t2)
  (protocol v))
(atomic y 0 (writer t2) (reader t1)
  (protocol v))

(thread t1
  (load r1 a.y_load y)
  (store a.x_store x 1))

(thread t2
  (load r2 b.x_load x)
  (store b.y_store y 1))
