# sinc: Typed Synchronization Inference for Weak Memory Concurrency

An inference engine written in OCaml that deduces the weakest memory orderings for a given spec. Currently supports single producer/single consumer, acquire-release synchronization, and weakened release sequences (see [here for more info](docs/decisions/cxx20-release-sequences.md))

## How to run 
First write a spec (s-expression notation: see [corpus](corpus) for examples) - memory orderings are left blank. Each atomic memory operation is annotated with a unique label. Then, run 
```
dune exec engine -- infer <program>.sexp
```
To see inferred orderings. To generate a C++ file, use 
```
dune exec engine -- emit <program>.sexp -o <program>.cpp
```
Individual operations can be pinned to a memory ordering. Use
```
dune exec engine -- emit <program>.sexp --pin some.label=[rlx, acq, rel, acq_rel, sc] -o <program>.cpp
```
Inferred orderings can be cross-checked with genmc to verify that the program is consistent as well as ensuring that the orderings are the weakest possible. use
```
GENMC = path/to/genmc/binary dune exec oracle/oracle.exe -- <program>.sexp
```
Unsound means that GenMC found an error in the inferred orderings: please report this! Imprecise means that a weaker ordering was found, and ERROR n / TIMEOUT means that GenMC failed, usually because codegen created a C++ file that GenMC couldnt handle or the parameters are too big. 

## How it works
Currently, in its core this engine is essentially just a small interpreter; this works for now given the constraints as loops are guaranteed to be bounded (and loop bounds are static, i.e. nested loop spaces are always rectangular). Per thread, the parser creates an AST and maintains a typing context that represents the resources that that thread owns at a given time. `cells (value CellMap.t)` is the set of array elements `(array_name, idx)` that the thread owns (i.e. the thread has exclusive ownership over that element and may perform non-atomic operations on it), along with a role per atomic, being either a writer (allowed to write to the atomic), reader (allowed to read from/gain resources from the atomic) or bystander. Each atomic variable defines a protocol, being one of:
- `Owns { arr; idx }`: transfers ownership of the cell `arr[idx]`
- `PointsTo { arr; idx; value }`: transfers ownership of the cell `arr[idx]` and guarantees that the value read from `arr[idx]` is `value`

The function `Ord.delta prog proto from to_: program -> protocol -> int -> int -> ((string * int) * value) list` computes a list of cells that are associated with steps [`from + 1`, `to`). For a writer, this means that the cells in delta are the set of cells that it must publish and release ownership of, and for a reader it is the set of cells that it gains and acquires ownership of. When a non-atomic operation is done, the set of cells currently owned by that thread is stored in `ctx.cells` and if it is not present, it raises a type error. 

In this IR, atomic loads will always emit a relaxed ordering; raw loads dont claim ownership, and ownership acquisition is done with awaits. Atomic stores instead first check that the thread has ownership over the cell to write to (through the `PointsTo` protocol): if it does, it removes those cells as it is giving up ownership. If nothing was published up to that value, then it emits a relaxed ordering, however if there was an earlier store that did publish (i.e. a store that is sb this store) it must emit a release ordering (see [docs/decisions/cxx20-release-sequences.md](docs/decisions/cxx20-release-sequences.md) for details); otherwise, it emits a release ordering. Await expressions represent a spin loop waiting for an atomic variable to reach a precondition: once this is met, it calculates the delta of cells to be claimed and adds them to that thread's `ctx.cells`. if the list of cells to acquire is empty, it emits relaxed ordering, else it emits acquire. Loops are handled by unrolling then from [lo, hi) and computing each iteration, and any arithmetic is evaluated as the interpreter walks the program. 

# Stuff still left to implement 
- execution graph (emit dot file)
- Symbolic loop bounds (evaluate with Z3)
- RMW (and cas, but that follows)
- Release sequences
- Memory fences and if statements
- Rocq verification of inference engine
 