(* The SPSC ring as an Ir value, shared by every test file. Not listed in
   the tests stanza's names, so dune makes it a module the tests can use. *)

open Engine.Ir

let v x = Var x
let p x = Param x
let i n = Int n

(* v => own slots[(v-1) % N] *)
let head_protocol =
  {
    binder = "v";
    payload = [ Own { arr = "slots"; idx = Mod (Sub (v "v", i 1), p "N") } ];
  }

(* v => slots[(v-1) % N] |-> v *)
let tail_protocol =
  {
    binder = "v";
    payload =
      [
        PointsTo
          { arr = "slots"; idx = Mod (Sub (v "v", i 1), p "N"); value = v "v" };
      ];
  }

let producer =
  {
    thread_name = "producer";
    owns = [ { owned_arr = "slots"; from_idx = i 0; to_idx = p "N" } ];
    body =
      [
        For
          {
            var = "i";
            lo = i 0;
            hi = p "K";
            body =
              [
                (* t := load tail @p.tail_load *)
                Load
                  { dst = "t"; acc = { label = "p.tail_load"; atom = "tail" } };
                (* await head >= t-N+1 @p.head_await *)
                Await
                  {
                    acc = { label = "p.head_await"; atom = "head" };
                    bound = Add (Sub (v "t", p "N"), i 1);
                  };
                (* slots[t % N] := t + 1 *)
                NaWrite
                  {
                    arr = "slots";
                    idx = Mod (v "t", p "N");
                    value = Add (v "t", i 1);
                  };
                (* store tail (t + 1) @p.tail_store *)
                Store
                  {
                    acc = { label = "p.tail_store"; atom = "tail" };
                    value = Add (v "t", i 1);
                  };
              ];
          };
      ];
  }

let consumer =
  {
    thread_name = "consumer";
    owns = [];
    body =
      [
        For
          {
            var = "i";
            lo = i 0;
            hi = p "K";
            body =
              [
                (* h := load head @c.head_load *)
                Load
                  { dst = "h"; acc = { label = "c.head_load"; atom = "head" } };
                (* await tail >= h + 1 @c.tail_await *)
                Await
                  {
                    acc = { label = "c.tail_await"; atom = "tail" };
                    bound = Add (v "h", i 1);
                  };
                (* x := slots[h % N] *)
                NaRead { dst = "x"; arr = "slots"; idx = Mod (v "h", p "N") };
                (* assert x == h + 1 *)
                Assert { lhs = v "x"; rhs = Add (v "h", i 1) };
                (* store head (h + 1) @c.head_store *)
                Store
                  {
                    acc = { label = "c.head_store"; atom = "head" };
                    value = Add (v "h", i 1);
                  };
              ];
          };
      ];
  }

let ring =
  {
    params = [ ("N", 2); ("K", 3) ];
    arrays = [ { arr_name = "slots"; size = p "N" } ];
    atomics =
      [
        {
          atom_name = "tail";
          init = 0;
          writer = "producer";
          reader = Some "consumer";
          protocol = tail_protocol;
        };
        {
          atom_name = "head";
          init = 0;
          writer = "consumer";
          reader = Some "producer";
          protocol = head_protocol;
        };
      ];
    threads = [ producer; consumer ];
  }
