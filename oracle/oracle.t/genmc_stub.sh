#!/bin/sh
# A stand-in for GenMC, so the oracle can be tested without it. Called as
#   genmc_stub.sh --disable-estimation FILE
# and behaves according to STUB:
#   sound    errors (42) exactly on weakened programs, like a correct GenMC.
#            Codegen's comment on an access pinned below what it needs reads
#            "label: rlx, <reason>"; a truly relaxed access has no reason.
#   pass     never finds an error (0)
#   fail     always finds an error (42)
#   crash    fails to compile (5)
#   timeout  as if `timeout` killed it (124)
[ "$1" = "--disable-estimation" ] || { echo "stub: bad args: $*"; exit 99; }
case "$STUB" in
  sound) if grep -q ': rlx, ' "$2"; then echo "Error: stub race"; exit 42; fi
         echo "No errors were detected."; exit 0 ;;
  pass) exit 0 ;;
  fail) exit 42 ;;
  crash) exit 5 ;;
  timeout) exit 124 ;;
  *) echo "stub: unknown STUB=$STUB"; exit 99 ;;
esac
