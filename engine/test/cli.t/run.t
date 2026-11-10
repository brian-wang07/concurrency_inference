The SPSC ring from the corpus.

  $ cp ../../../corpus/spsc_ring.sexp ring.sexp

Inferred orderings for the ring, with the reason for each one above rlx.

  $ engine infer ring.sexp
  c.head_load   rlx
  c.head_store  rel      publishes slots[0] (i=0)
  c.tail_await  acq      gains slots[0] = 1 (i=0)
  p.head_await  acq      gains slots[0] (i=2)
  p.tail_load   rlx
  p.tail_store  rel      publishes slots[0] = 1 (i=0)

Emitting with no pins uses the inferred orderings.

  $ engine emit ring.sexp -o ring.cpp
  $ grep -c memory_order ring.cpp
  6
  $ grep 'tail.store' ring.cpp
      tail.store(t + 1, std::memory_order_release);  // p.tail_store: rel, publishes slots[0] = 1 (i=0)

Pinning p.tail_store below what it needs warns, but still writes the file.

  $ engine emit ring.sexp --pin p.tail_store=rlx -o weak.cpp
  warning: p.tail_store pinned to rlx, but needs at least rel
    rel: publishes slots[0] = 1 (i=0)
    rel: publishes slots[1] = 2 (i=1)
    rel: publishes slots[0] = 3 (i=2)
  $ grep 'tail.store' weak.cpp
      tail.store(t + 1, std::memory_order_relaxed);  // p.tail_store: rlx, publishes slots[0] = 1 (i=0)

A pin at or above what is needed is silent, and stdout is used without -o.

  $ engine emit ring.sexp --pin p.tail_store=sc --pin c.head_load=acq | grep -E 'tail.store|head.load\('
      while (head.load(std::memory_order_acquire) < (t - N) + 1) {}  // p.head_await: acq, gains slots[0] (i=2)
      tail.store(t + 1, std::memory_order_seq_cst);  // p.tail_store: sc, publishes slots[0] = 1 (i=0)
      h = head.load(std::memory_order_acquire);  // c.head_load: acq

An access that never runs is rlx, and can be pinned.

  $ engine infer unreached.sexp
  l  rlx
  $ engine emit unreached.sexp --pin l=sc | grep store
      a.store(1, std::memory_order_seq_cst);  // l: sc

Bad pins.

  $ engine emit ring.sexp --pin nope=rel
  ring.sexp: no access labelled nope
  [1]
  $ engine emit ring.sexp --pin p.tail_store=release
  engine: unknown ordering release in --pin p.tail_store=release (expected rlx, acq, rel, acq_rel, sc)
  usage: engine infer FILE
         engine emit FILE [-o OUT] [--pin LABEL=ORD]...
  [2]
  $ engine emit ring.sexp --pin p.tail_store
  engine: --pin expects LABEL=ORD, got p.tail_store
  usage: engine infer FILE
         engine emit FILE [-o OUT] [--pin LABEL=ORD]...
  [2]

Rejected programs: one per stage.

  $ engine infer bad_parse.sexp
  bad_parse.sexp:2: unclosed (
  [1]
  $ engine infer bad_wf.sexp
  bad_wf.sexp: array N clashes with param N
  [1]
  $ engine infer bad_check.sexp
  bad_check.sexp: type error: read s[0] without ownership
  [1]
  $ engine infer missing.sexp
  missing.sexp: No such file or directory
  [1]

Usage errors.

  $ engine
  engine: missing command
  usage: engine infer FILE
         engine emit FILE [-o OUT] [--pin LABEL=ORD]...
  [2]
  $ engine frobnicate ring.sexp
  engine: unknown command frobnicate
  usage: engine infer FILE
         engine emit FILE [-o OUT] [--pin LABEL=ORD]...
  [2]
  $ engine infer
  engine: infer takes exactly one FILE
  usage: engine infer FILE
         engine emit FILE [-o OUT] [--pin LABEL=ORD]...
  [2]
  $ engine emit ring.sexp other.sexp
  engine: emit takes exactly one FILE
  usage: engine infer FILE
         engine emit FILE [-o OUT] [--pin LABEL=ORD]...
  [2]
