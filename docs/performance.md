# Performance

## Current status

The exact solver in `src/solve.bend` (delegating to `src/solve_fast.bend`) is proved directly valid
and optimal for every input (`Laws.solve_valid` and `Laws.solve_optimal` in `PROOF.bend`). It uses
a precomputed `|G| x |C|` `Array<U32>` feedback table and single root-threaded `Buf5` scratch
buffer for 5-letter duplicate-free runs, depth-two lower bounds, tight recursive cutoff propagation,
O(1) singleton, duplicate-free two-word, and table-backed three-word (`DoneItem`) class resolution,
largest-class-first child ordering, candidate-first staged search (`S` before `G` with a `2*|S|`
post-`S` floor and stage-2 self-guess skipping), and mid-histogram collision-budget early abort. The
exhaustive reference solver in `src/solve_ref.bend` (`Ref.solve_valid`, `Ref.solve_optimal`) and the
parallel root solver in `src/solve_par.bend` (`Par.solve_eq`) stay in the tree as specifications.
The full bundled lists in `words/` still need stronger move ordering, greedy upper-bound seeding,
deeper capacity bounds, and a proved multi-core root split; speed is the remaining work, correctness
is not.

## Chunked root

`src/solve_k.bend` can split the root guess list into `2^d <= k` contiguous segments and evaluate
the segments in parallel, where `k` is the number of threads the runtime was started with. Each
segment runs the fast search machine from the neutral accumulator over only its own guesses, with
the full guess list still available at every child node, and the results are folded in guess order
with the reference `better`. The fold keeps the first strictly cheapest result, which is the
sequential root's tie-break, so the chunked run returns the same tree as the sequential one; only
the amount of work done without a shared bound changes. `k <= 1` is the sequential root unchanged.

The split costs some pruning: the segments cannot share the running best cost, so each segment pays
for its first guesses at the neutral bound. On the bundled benchmark inputs the four-thread split
is about twice as fast as the sequential root. The chunked path is not covered by the eight laws
yet: the proof needs a job specification whose reference is the best tree over a segment of the
guess list rather than over the whole list, plus a composition lemma over the segments.

## Smoke baseline

The rows below are a small-size laptop smoke baseline, not a benchmark result. They were measured
with the reference solver, with the guesses list made of the sampled candidates followed by the
first 200 lines of `words/guesses.txt`, at seed 1, from commit `f2387b2`:

| Candidates | Wall time |
| --- | --- |
| 6 | 0.66 s |
| 8 | 2.39 s |
| 10 | 7.26 s |

They show the growth of the reference search on one machine and are not comparable with rows in
`bench/results.csv`, which follow the protocol in [benchmarking.md](benchmarking.md). Use them only
as a sanity check that the current solver is in the expected range.

## Planned optimisations

The plan is to keep the exact result while avoiding work that cannot improve it. The first step is
pruning by a lower bound: before a guess or a feedback class is searched, compare a bound on the
best cost it can still achieve with the best tree found so far, and skip it when it cannot win.
Evaluating guesses in an order that finds a good tree early makes that pruning more effective.

The reference solver stays in the tree as the specification. An optimised solver is compared
against it on small inputs, where the reference result is cheap to compute.

Every optimisation must keep all eight laws proved. A change that weakens a law, leaves a proof
broken, or adds a law to `PENDING_LAWS` is not a performance improvement, however fast it is. Run
the proof gate before proposing one:

```sh
scripts/check-proofs.sh
```

If an optimisation replaces `solve`, the laws and their proofs are updated for the new
implementation, and `PENDING_LAWS` stays empty. If it is a separate path, it must return a tree
that satisfies the same laws; returning a different optimal tree is allowed, returning a worse one
is not. New timing numbers belong in the benchmark CSV, not in this document.

## Recording results

Benchmarks append rows to `bench/results.csv`, which is committed alongside pull requests that
claim a speedup (while per-run logs under `bench/runs/` stay gitignored). Each row records the
commit, whether the tree was dirty, the caller's hardware label, the CPU and GPU, the requested
size, the seed, the repeat number, the wall-clock seconds, the exit code, the output hash and the
repeatability flag.

The full protocol, the column meanings and the remote run helper are in
[benchmarking.md](benchmarking.md). Compare rows only within one `(commit, dirty, label, cpu_model,
gpu, size, seed)` group, and compare minima over repeats rather than single runs.
