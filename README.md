# wordle-bend

An exact, formally verified solver for Wordle-style games.

Given a guesses list and a candidates list, the solver is intended to produce
the decision tree (the policy) of an optimal guessing strategy, minimising the
total number of guesses over all candidates. The game is treated generically:
any words, any length, any alphabet. Both lists are inputs, so the solver is
not tied to the five-letter English game.

Two properties distinguish this solver from a heuristic one:

- **Exact.** The tree it returns is optimal, not merely good. Optimality is
  over the stated objective: the sum of the number of guesses needed for every
  candidate.
- **Formally verified.** The solver carries machine-checked proofs, called
  laws, that the returned tree is valid and optimal for every input. The
  guarantee is part of the artifact, not a claim checked by a handful of
  examples.

The solver is written in [Bend](https://github.com/HigherOrderCO/Bend) for HVM,
a runtime built for massive parallelism across GPUs and CPUs. The earlier solver
for this problem was written in Rust and was unverified. This project succeeds
it with the same goal of practical wall-clock speed, plus a correctness
guarantee that the earlier work could not give.

## Status

**Core code and laws, in progress.** The feedback function, the tree structure,
the validity and cost definitions, the JSON printer, the command-line entry
point, and the bundled word lists are present. Laws 1 to 3 are proved. Laws 4
to 6 are stated and still open. The solver itself is a placeholder that returns
`None`; Phase 4 replaces it with the search.

The JSON parser is not implemented yet. `Json.print` works; `Json.parse`
currently rejects every input, and law 6 is open for that reason.

## Layout

| Path | Purpose |
| --- | --- |
| `LAWS.bend` | The six laws, each an open claim until `PROOF.bend` proves it. |
| `PROOF.bend` | The proofs, plus the helper lemmas they use. |
| `src/` | The Bend code: feedback, tree, solver placeholder, JSON, CLI. |
| `words/` | The bundled candidate and guess lists. |
| `docs/` | Detailed documentation, one file per concern. Start here after this README. |

## Documentation

- [docs/architecture.md](docs/architecture.md) — the components and how data flows between them.
- [docs/laws.md](docs/laws.md) — each law in plain English, with its Bend definition and status.
- [docs/contributing.md](docs/contributing.md) — branch names, commit format, pull request workflow,
  and repository hygiene rules.
- [docs/testing.md](docs/testing.md) — why correctness is established by laws and proofs rather than
  example tests, and how benchmarks differ from tests.
- [docs/licenses.md](docs/licenses.md) — the MIT licence for the code, and the provenance of the
  bundled word lists.

## Licence

MIT. See [LICENSE](LICENSE) and [docs/licenses.md](docs/licenses.md).
