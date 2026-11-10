The oracle, run against a stub GenMC (genmc_stub.sh). Its path has a space,
to check that commands are quoted. Temp files go in the test directory, and
their names are random, so the "see" lines are rewritten.

  $ mkdir "stub dir" && cp genmc_stub.sh "stub dir/genmc"
  $ export GENMC="$PWD/stub dir/genmc"
  $ export TMPDIR="$PWD"
  $ cp ../../corpus/spsc_ring.sexp ../../corpus/heartbeat.sexp .
  $ oracle() { ../oracle.exe "$@" > out; echo "exit $?"; sed 's|see .*\.cpp\.out|see <tmp>.out|' out; }

A stub that behaves like a correct GenMC: the inferred orderings are clean,
and every one-step weakening is caught.

  $ STUB=sound oracle spsc_ring.sexp heartbeat.sexp
  exit 0
  ok         spsc_ring.sexp: inferred
  ok         spsc_ring.sexp: c.head_store rel -> rlx
  ok         spsc_ring.sexp: c.tail_await acq -> rlx
  ok         spsc_ring.sexp: p.head_await acq -> rlx
  ok         spsc_ring.sexp: p.tail_store rel -> rlx
  ok         heartbeat.sexp: inferred
  6 runs, 0 failed

A checker that finds nothing makes every weakening look unnecessary.

  $ STUB=pass oracle spsc_ring.sexp
  exit 1
  ok         spsc_ring.sexp: inferred
  IMPRECISE  spsc_ring.sexp: c.head_store rel -> rlx
              see <tmp>.out
  IMPRECISE  spsc_ring.sexp: c.tail_await acq -> rlx
              see <tmp>.out
  IMPRECISE  spsc_ring.sexp: p.head_await acq -> rlx
              see <tmp>.out
  IMPRECISE  spsc_ring.sexp: p.tail_store rel -> rlx
              see <tmp>.out
  5 runs, 4 failed

A checker that always finds an error makes the inferred orderings unsound.
Programs with no orderings above rlx have only the baseline run.

  $ STUB=fail oracle heartbeat.sexp
  exit 1
  UNSOUND    heartbeat.sexp: inferred
              see <tmp>.out
  1 runs, 1 failed

Compile failures and timeouts are reported as such, not as results.

  $ STUB=crash oracle heartbeat.sexp
  exit 1
  ERROR 5    heartbeat.sexp: inferred
              see <tmp>.out
  1 runs, 1 failed
  $ STUB=timeout oracle heartbeat.sexp
  exit 1
  TIMEOUT    heartbeat.sexp: inferred
              see <tmp>.out
  1 runs, 1 failed

A file that doesn't load is reported, and the remaining files still run.

  $ STUB=sound oracle missing.sexp heartbeat.sexp
  exit 1
  ERROR 0    missing.sexp: No such file or directory
  ok         heartbeat.sexp: inferred
  2 runs, 1 failed

No files is a usage error.

  $ ../oracle.exe
  usage: oracle FILE...
  [2]
