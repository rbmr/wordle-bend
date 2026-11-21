# wordle-bend

An exact, formally verified solver for Wordle-style games.

Given a guesses list and a candidates list, the solver produces the decision tree (the policy) of an
optimal guessing strategy, minimising the total number of guesses over all candidates. The game is
treated generically: any words, any length, any alphabet. Both lists are inputs, so the solver is
not tied to the five-letter English game.

Two properties distinguish this solver from a heuristic one:

- **Exact.** The tree it returns is optimal, not merely good. Optimality is over the stated
  objective: the sum of the number of guesses needed for every candidate.
- **Formally verified.** The solver carries machine-checked proofs, called laws, that the returned
  tree is valid and optimal for every input. The guarantee is part of the artifact, not a claim
  checked by a handful of examples.

The solver is written in [Bend](https://github.com/HigherOrderCO/Bend) for HVM, a runtime built for
massive parallelism across GPUs and CPUs. The earlier solver for this problem was written in Rust
and was unverified. This project succeeds it with the same goal of practical wall-clock speed, plus
a correctness guarantee that the earlier work could not give.

## Status

**Scaffolding, in progress.** The repository currently contains the project documentation, the
repository hooks, a CI check for commit and branch conventions, and the standardised benchmark
harness in `bench/`. There is no solver, no laws, no word data and no CLI yet, so the harness cannot
run until those exist; anything below that is not the harness is planned layout, not an implemented
feature.

## Planned layout

| Path | Purpose |
| --- | --- |
| `words/` | Bundled word lists used by the CLI and benchmarks. To be added. |
| `src/` | The Bend solver: search over guess sequences and construction of the optimal tree. |
| `laws/` | Formal statements of the validity and optimality properties, and their machine-checked proofs. |
| `cli/` | Command-line entry point: word lists in, decision tree out. |
| `bench/` | Standardised benchmarking of solver runs, so results are comparable across machines and changes. |
| `docs/` | Detailed documentation, one file per concern. Start here after this README. |

## Documentation

- [docs/architecture.md](docs/architecture.md) — the components and how data flows between them.
- [docs/contributing.md](docs/contributing.md) — branch names, commit format, pull request workflow,
  and repository hygiene rules.
- [docs/testing.md](docs/testing.md) — why correctness is established by laws and proofs rather than
  example tests, and how benchmarks differ from tests.
- [docs/benchmarking.md](docs/benchmarking.md) — how the benchmark harness times the solver, how to
  read `bench/results.csv`, and how to add a benchmark scenario.
- [docs/licenses.md](docs/licenses.md) — the MIT licence for the code, and the provenance requirement
  for bundled word lists.

## Licence

MIT. See [LICENSE](LICENSE) and [docs/licenses.md](docs/licenses.md).
