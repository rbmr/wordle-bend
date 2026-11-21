# Performance

## Current status

The reference solver in `src/solve.bend` (through `src/solve_ref.bend`) is exact and exhaustive. It
is verified correct for every input, including optimality, but it is not fast: for every candidate
list it tries every usable guess, partitions the candidates by feedback, and solves every class
recursively. The work grows exponentially with the number of candidates.

The command line uses `src/solve_fast.bend`, which skips any guess whose lower bound cannot beat the
best cost found so far and is proved to return the exact reference tree (`Fast.solve_eq` in
`PROOF.bend`). The parallel root solver in `src/solve_par.bend` (`Par.solve_eq`) and the reference
solver stay in the tree. The search is still exponential in the candidate count, so the full bundled
lists in `words/` are not practical yet. Speed is the remaining work; correctness is not.

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

Benchmarks append rows to `bench/results.csv`. The file is gitignored because its numbers are
machine-specific measurements, not source. Each row records the commit, whether the tree was dirty,
the caller's hardware label, the CPU and GPU, the requested size, the seed, the repeat number, the
wall-clock seconds, the exit code, the output hash and the repeatability flag.

The full protocol, the column meanings and the remote run helper are in
[benchmarking.md](benchmarking.md). Compare rows only within one `(commit, dirty, label, cpu_model,
gpu, size, seed)` group, and compare minima over repeats rather than single runs.
