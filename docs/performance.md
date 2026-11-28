# Performance

## Current status

The exact solver in `src/solve.bend` (the `k = 1` instance of `src/solve_k.bend`, combining
`src/greedy.bend` and `src/solve_fast.bend`) is proved directly valid and optimal for every input
(`Laws.solve_valid` and `Laws.solve_optimal` in `PROOF.bend`). It uses a precomputed `|G| x |C|`
`Array<U32>` feedback table and single root-threaded `Buf5` scratch buffer for 5-letter
duplicate-free runs, Pass-1 root bucket sorting by depth-two lower bound (`n + 2*m - k`), top-5
table-backed `greedy(lb)` upper-bound seeding (`src/greedy.bend`), depth-two lower bounds, tight
recursive cutoff propagation, O(1) singleton, duplicate-free two-word, and table-backed three-word
(`DoneItem`) class resolution, largest-class-first child ordering, candidate-first staged search
(`S` before `G` with a `2*|S|` post-`S` floor and stage-2 self-guess skipping), and mid-histogram
collision-budget early abort. The exhaustive reference solver in `src/solve_ref.bend`
(`Ref.solve_valid`, `Ref.solve_optimal`) and the parallel root solver in `src/solve_par.bend`
(`Par.solve_eq`) stay in the tree as specifications. The full bundled lists in `words/` still need
stronger interior lower bounds (such as sibling-level depth-two tightening and capacity bounds) and
interior move ordering; speed is the remaining work, correctness is not.

## Seeded and chunked root

For candidate lists of at least three words, `src/solve_k.bend` first calls `Greedy.root_prepare`
(`src/greedy.bend`) on a single root buffer to bucket-sort usable root guesses by their Pass-1
depth-two lower bound and run up to five `greedy(lb)` rollouts from the lowest-bound guesses to
seed a valid initial upper bound `b0`.

- When `k <= 1` (`d = 0`), the sorted root queue runs directly on the root buffer starting from
  `b0`.
- When `k >= 2` (`d >= 1`), the sorted root queue is dealt round-robin (`deal_even` / `deal_odd`)
  into `2^d <= k` balanced chunks, every chunk starts from the shared seeded bound `b0` with its
  own feedback-table buffer while child nodes still see the whole guess list, and the chunk results
  are folded with `SolveRef.better`.

Seeding `b0` before splitting gives every parallel chunk a tight initial upper bound immediately,
and round-robin dealing balances low-bound and high-bound guesses across chunks. Both phases are
proved in `proofs/greedy.bend` and `proofs/par_chunk.bend` for every chunk count `k`: every greedy
rollout produces a valid tree within its reported cost, Pass-1 bucket sorting covers every usable
root guess in `G`, every chunk result is valid and beats every usable guess in its chunk, and the
folded result costs at most the reference solver over `G`. The laws are proved through that general
argument at the production entry point's chunk count.

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
