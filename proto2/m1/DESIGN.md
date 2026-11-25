# M1 notes: port of the Rust search core

Rust source (read only): `~/projects/wordle-opt/src/{solver,heuristic,cache}.rs`.
Target: `proto2/` only. Safe Bend (no `@unsafe`).

## The structural blocker, and the plan

Rust's search is mutually recursive:
`min_state_val_with_hash` calls `min_guess_val_inner`, which recurses into
`min_state_val_with_hash` for each bucket. Bend forbids mutual recursion and
forward references in safe code, and has no `let`-bound continuation. A literal
two-function transcription is therefore impossible. The written rule (Bend
guide, "Recursion and Termination") is: two mutually recursive functions become
one def with an extra argument selecting which to run.

Plan: one `step` def with an explicit frame stack (a `List<Frame>` or a flat
frame array), exactly the pattern the existing solver uses for its drain. The
*order of operations* of the Rust functions is preserved; only the call/return
mechanism changes:

- `State` frame: the `min_state_val_with_hash` fields (`set` region, `beta`,
  `parent_max_k`, best, local_lb, phase, tuple list cursor, counters).
- `Guess` frame: the `min_guess_val_inner` fields (`guess`, bucket list,
  current bucket, accumulated cost).
- A child result is delivered into the parent's top frame; the frame stack is
  the Rust call stack. Frames are pushed/popped once per node/guess, never per
  candidate.

Hot loops stay flat: candidate sets are `(start,len)` ranges in a flat stack
array, feedback and scratch counts/sort buffers are flat `Array<U32>`, the TT
is a flat array passed through `step`. No record is built per candidate.

## Rust step -> Bend plan

| Rust step (file:line) | Bend target | Status |
|---|---|---|
| `capacity_bound`, `forest_bound`, `all_candidates_fill`, `forest_g` (heuristic.rs 1024-1142) | `bounds.bend` same names | **done**, validated: cap(1,3)=1, (2,3)=3, (3,3)=5, (4,3)=8, (7,3)=17, (20,100)=39 |
| `phase2_capacity_bound`, `tight_capacity_bound`, `bucket_capacity_bound` (1211-1257) | `bounds.bend` same names | **done**, validated: n=5,k=2 -> tight 15, phase2 14, bucket 14 |
| `capacity_bounds_2d` table (solver.rs 10483-10488) | build once into a flat `Array<U32>` indexed `k*(C+1)+n`, k=2..max_k | pending |
| `compute_max_branching_factor` (heuristic.rs ~900) | root-only fold over candidate profiles | pending |
| `compute_branching_factor_upper_bound` (413-500) | needs per-candidate letter profiles (present/dup/at masks) | pending |
| candidate letter profiles / `candidate_masks`, `guess_masks` | flat `Array<U32>` built from parsed words (5 letters, 26 bits) | pending |
| `matrix.data_u8` / `data_cg` feedback matrix | flat `Array<U32>` `FB[g*C + c]`, response code base-3 (WIN=242) | pending (need a direct 5-letter evaluator; do not use list feedback per pair) |
| `zobrist` (matrix.rs) | two independent 32-bit Zobrist arrays (Bend has no U64); set/bucket hash = XOR pair | pending |
| `GlobalCache::get/insert` (cache.rs 76-199) | flat arrays: key1, key2, value (exact bit in bit 31), 2 slots per bucket, 2^20 buckets | pending (policy to be copied exactly) |
| `sort_guess_tuples` (solver.rs 119-429) | insertion sort on a flat `(lb,exp,g)` buffer (generic, not the unrolled networks) | pending |
| `quick_bucket_eval_elem` (759-1682) | generic exact small eval: n<=2 exact; scan each in-set guess, 0 collisions -> (2n-1,exact), exactly one collision -> (2n,exact), else (2n,lb) | pending; logic derived from the unrolled cases, must be tested against them on real sets |
| `min_state_val_with_hash` (2532-3945) | `State` phase machine: base cases, TT lookup, quick eval n<=15, parent cap lb, phase1 candidate scan + cheap lb/exp, tuple sort + beta cut, phase2 scan + tuples, tight/phase2 `local_lb`, exact/lb store | pending |
| `min_guess_val_inner` (3961-6200) | `Guess` phase machine, generic bucket path for all n: partition, `cost=n+sum cap[p]` over non-win buckets, TT/quick per bucket, recurse into p>=3 buckets sorted by p desc, beta cut per bucket | pending; the c_len<=16 and c_len>16 Rust paths compute the same generic formula, so one body covers both |
| `get_or_compute_active_guesses` / equivalence dedup | **omitted in M1**; M2. report-gap: 1.02x at N=800, so counts stay within 2x | M2 |
| root pre-filter + static sort (10457-10481) | **omitted in M1**; M2. Root is a plain `State` on all C candidates | M2 |
| `greedy_solve` initial bound (10461, 10558) | M1 uses a simple greedy upper bound only so the search terminates in 120 s; full greedy/root bound is M2 | partial |
| shared global beta / depth-2 parallel root | M1 single thread, `global_beta = 0xFFFFFFFF`, so cutoff == beta | n/a in M1 |
| `Metrics` counters (states before quick eval, guesses at `min_guess_val_inner` entry) | two `U32` accumulators carried in the frame state, incremented at the same points | pending |
| root solve (`solve`, 10434) | M1 driver calls `step` once on the full set and prints cost/states/guesses | pending |

## Counting comparison caveat

Rust's root does not call `min_state_val` (`solve` evaluates buckets directly),
so its `states`/`guesses` exclude the root layer. A plain M1 root `State` adds
one state and counts root guess scans. The progress file records both the raw
counters and a root-excluded count so the comparison at N=100/300/500 is
meaningful.

## M0 result carried forward

`Array<U32>` is a flat block; the generation-stamped partition loop runs at
1.43x the identical C loop at n=300 and 1.69x at n=10 (remote, 1 thread). Use
that loop shape for the per-guess partition in `Guess`.

## Immediate next steps

1. `words.bend`: parse the two files, build letter arrays, `cand_to_guess`.
2. Direct 5-letter feedback evaluator on letter codes; fill `FB`; verify codes
   and bucket sizes against a Python reference on N<=200.
3. Letter profiles + `compute_branching_factor_upper_bound`; cap2d table.
4. `quick_bucket_eval` generic; test against a brute-force minimax for random
   small sets.
5. TT flat arrays; unit test get/insert policy.
6. `step` frame machine in the order of the Rust table above; start with the
   full set at N=100 and check cost 253, then counts at N=100/300/500.
