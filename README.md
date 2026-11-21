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

The solver is written in [Bend](https://github.com/bendlang/bend) for HVM, a runtime built for
massive parallelism across GPUs and CPUs. The earlier solver for this problem was written in Rust
and was unverified. This project succeeds it with the same goal of practical wall-clock speed, plus
a correctness guarantee that the earlier work could not give.

## Status

**Exact and verified; performance work remains.** All eight laws in `LAWS.bend` are proved in
`PROOF.bend` and the modules under `proofs/`, and `PENDING_LAWS` is empty. The reference solver in
`src/solve.bend` is the exact, exhaustive specification: it is verified correct for every input,
including optimality, but it is not fast. Its search is exponential and takes a few seconds at 10
candidates, so the full bundled lists are not practical yet. The command line uses
`src/solve_fast.bend`, which prunes any guess whose lower bound cannot beat the best cost found so
far and is proved to return the exact reference tree (`Fast.solve_eq` in `PROOF.bend`). The
command-line interface is
documented in [docs/cli.md](docs/cli.md), the bundled word lists are in `words/`, and the benchmark
harness is in `bench/`. [docs/performance.md](docs/performance.md) records the current performance
status and the plan for speeding the solver up.

## Quick start

Install Bend 2.0.40 and clang 19 or newer, then from the repository root:

```sh
# requires Bend 2.0.40 and clang 19+
bend src/main.bend -o wordle-bend

# a small slice of the bundled lists: 6 candidates and 40 guesses
head -n 6 words/candidates.txt > c.txt
head -n 40 words/guesses.txt > g.txt
./wordle-bend --guesses g.txt --candidates c.txt

# a two-word list of your own, used as both the guesses and the candidates
printf 'abc\nabd\n' > my-words.txt
./wordle-bend --guesses my-words.txt --candidates my-words.txt
```

The first run prints the tree for the six candidates in the slice; the first 40 lines of the
bundled guesses include all six:

```text
[[65,66,65,84,69],[[[2,2,2,0,0],[[65,66,65,67,75],[]]],[[2,2,2,0,2],[[65,66,65,83,69],[]]],[[2,2,0,0,1],[[65,66,66,69,89],[]]],[[2,2,0,1,0],[[65,66,66,79,84],[]]],[[2,2,0,0,0],[[65,66,72,79,82],[]]]]]
```

The second run uses the two-word list as both the guesses and the candidates, and prints
`[[97,98,99],[[[2,2,0],[[97,98,100],[]]]]]`, the tree for `abc` and `abd`. The search is
exponential, so keep both lists small until pruning lands.

## Where the proofs are

`LAWS.bend` states the eight laws. `PROOF.bend` defines `def Laws.<name>` for each one and imports
the helper lemmas in `proofs/`. `scripts/check-proofs.sh` is the gate that CI runs, and
[docs/proofs.md](docs/proofs.md) maps every proof file and explains how to run the checks locally.
[docs/laws.md](docs/laws.md) gives each law and its proof strategy in plain English.

## Layout

| Path | Purpose |
| --- | --- |
| `LAWS.bend` | The eight laws the solver must satisfy. |
| `PROOF.bend` | The proofs of the laws, one `def Laws.<name>` each. |
| `proofs/` | Helper lemmas used by the proofs, grouped by purpose. |
| `PENDING_LAWS` | Laws allowed to be open. Currently empty. |
| `src/` | The Bend code: feedback, groups, tree, the reference and parallel solvers, JSON, CLI. |
| `words/` | The bundled candidate and guess lists. |
| `bench/` | The benchmark harness. |
| `scripts/` | `check-proofs.sh`, the proof gate. |
| `docs/` | Detailed documentation, one file per concern. Start here after this README. |

## Documentation

- [docs/architecture.md](docs/architecture.md) — the components and how data flows between them.
- [docs/cli.md](docs/cli.md) — the command line: flags, input and output formats, exit codes, examples.
- [docs/laws.md](docs/laws.md) — each law in plain English, with its Bend definition and proof strategy.
- [docs/proofs.md](docs/proofs.md) — what each file under `proofs/` proves, the gate, and the local checks.
- [docs/performance.md](docs/performance.md) — current speed, the smoke baseline, and the optimisation plan.
- [docs/testing.md](docs/testing.md) — why correctness is established by laws and proofs rather than
  example tests, and how benchmarks differ from tests.
- [docs/benchmarking.md](docs/benchmarking.md) — the benchmark protocol, the CSV format, and how to run a benchmark.
- [docs/contributing.md](docs/contributing.md) — branch names, commit format, pull request workflow,
  and repository hygiene rules.
- [docs/licenses.md](docs/licenses.md) — the MIT licence for the code, and the provenance of the
  bundled word lists.

## Licence

MIT. See [LICENSE](LICENSE) and [docs/licenses.md](docs/licenses.md).
