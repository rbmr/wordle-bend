# Testing

## Correctness is established by laws, not examples

For a solver of this kind, example tests are a weak argument. A test that runs one word list and
checks a known answer says something about that one input. It says nothing about the inputs nobody
chose to test, and the interesting failures in a search algorithm are exactly the inputs nobody
thought of.

So correctness here is a proof obligation, carried by the laws in `LAWS.bend` and proved in
`PROOF.bend`:

- the returned tree is **valid** for its input: every node's guess is in the guesses list, and
  every candidate has a depth in the tree;
- the returned tree is **optimal** for its input: no valid tree for the same input has a lower
  total number of guesses over all candidates.

The laws are stated formally and checked mechanically, and the check is part of the repository
rather than a claim about a run.

## Current state

| Law | State |
| --- | --- |
| `feedback_all_green_when_equal` | proved |
| `feedback_all_green_only_if_equal` | proved |
| `feedback_length` | proved |
| `solve_valid` | proved |
| `solve_optimal` | pending: the optimality proof is open |
| `tree_roundtrip` | proved |

Every proved law has a `def Laws.<name>` in `PROOF.bend`. The open ones are listed in
`PENDING_LAWS`.

## The proof gate

`scripts/check-proofs.sh` is the proof gate. CI runs it on every pull request, and contributors run
the same script locally, so a green run means the same thing in both places:

```sh
scripts/check-proofs.sh
```

The script fails unless `LAWS.bend` and `PROOF.bend` exist, then checks the lists before running
`bend`:

- It reads the law names from the `law <name>:` lines in `LAWS.bend` and the proved names from the
  `def Laws.<name>(` lines in `PROOF.bend`.
- Every law that is not listed in `PENDING_LAWS` must have a proof def.
- Every name in `PENDING_LAWS` must be a law in `LAWS.bend` and must not have a proof def. Listing a
  law that is already proved fails with `remove it from PENDING_LAWS`.

`PENDING_LAWS` is a plain text file at the repository root, one law name per line. Blank lines and
`#` comments are ignored.

When `PENDING_LAWS` is empty, the gate requires `bend PROOF.bend` to exit 0 with `ALL PROOFS CHECK`,
then runs `bend PROOF.bend --verdict` and requires the same. The verdict kernel checks the laws
against Lean, and it needs every proof to be present.

While `PENDING_LAWS` is non-empty, the gate requires `bend PROOF.bend` to exit 1 with
`SOME PROOFS FAIL` and exactly one error, `Error: N TODOs found.`, where `N` is the number of
pending laws. Any other error output fails the gate: pending means "not attempted", not "broken".
A type error in a proof therefore fails the gate even though some laws are allowed to be open. The
script prints the pending laws, notes that `--verdict` was skipped, and ends with a one-line summary
of the proved and pending counts.

## PENDING_LAWS

`PENDING_LAWS` exists so that a law can be stated before its implementation and still pass the
gate. It is not a place for broken proofs.

- Adding a law to `PENDING_LAWS` needs an explicit explanation in the pull request description:
  which law, why it cannot be proved yet, and what will make it provable.
- The list should only shrink over time. Remove a name in the same pull request that adds its proof.
- The target is an empty list. When it is empty, the gate also runs the Lean verdict kernel and
  every law must be proved with no error output.

To type-check the law statements alone, without proving them, run `bend LAWS.bend --check-only`;
open laws appear there as TODOs.

## No example or unit tests

There are no example or unit tests, and none should be added as a correctness argument. A passing
example suite never substitutes for a law that has not been stated or proved. The CLI is
deliberately thin: reading arguments and files, mapping letters, and printing.

## Benchmarks are not tests

A benchmark measures how long the solver takes on fixed inputs. It answers "how fast", not "is it
right". A faster solver that returns a wrong tree is a regression, not a performance win. A correct
solver that is slow is still correct. The benchmark harness is not in this tree yet.

## Current checks in CI

CI runs two jobs on every pull request:

- `conventions`: the pull request title, every commit subject, and the head branch name follow the
  rules in [contributing.md](contributing.md).
- `proofs`: `scripts/check-proofs.sh`, the proof gate described above, using the pinned Bend and
  Lean toolchain. The job is skipped when the tree has no `PROOF.bend`.
