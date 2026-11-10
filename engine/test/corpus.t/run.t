Inferred orderings for every corpus program. Each program's header comment
states what it expects; a change here means inference changed.

  $ for f in ../../../corpus/*.sexp; do echo "== $(basename $f)"; engine infer $f; done
  == batched.sexp
  c.count_await  acq      gains data[0] = 1 (i=0)
  p.count_store  rel      publishes data[0] = 1, data[1] = 2, data[2] = 3
  == heartbeat.sexp
  m.beat_await  rlx
  w.beat_store  rlx
  == load_buffering.sexp
  a.x_store  rlx
  a.y_load   rlx
  b.x_load   rlx
  b.y_store  rlx
  == message_passing.sexp
  c.ready_await  acq      gains data[0] = 42, data[1] = 43
  p.ready_store  rel      publishes data[0] = 42, data[1] = 43
  == ping_pong.sexp
  p.ping_store  rel      publishes cell[0] = 1 (i=0)
  p.pong_await  acq      gains cell[0] = 2 (i=0)
  q.ping_await  acq      gains cell[0] = 1 (i=0)
  q.pong_store  rel      publishes cell[0] = 2 (i=0)
  == relay.sexp
  a.f1_store  rel      publishes buf[0] = 1
  b.f1_await  acq      gains buf[0] = 1
  b.f2_store  rel      publishes buf[0] = 2
  c.f2_await  acq      gains buf[0] = 2
  == spsc_ring.sexp
  c.head_load   rlx
  c.head_store  rel      publishes slots[0] (i=0)
  c.tail_await  acq      gains slots[0] = 1 (i=0)
  p.head_await  acq      gains slots[0] (i=2)
  p.tail_load   rlx
  p.tail_store  rel      publishes slots[0] = 1 (i=0)
