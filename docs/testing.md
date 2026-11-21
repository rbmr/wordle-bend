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
| `solve_valid` | open: the solver is a placeholder |
| `solve_optimal` | open: the solver is a placeholder |
| `tree_roundtrip` | open: the JSON parser is not implemented |

The checks are:

```sh
bend LAWS.bend --check-only   # type-checks the statements; open laws appear as TODOs
bend PROOF.bend               # prints SOME PROOFS FAIL while any law is open
```

`SOME PROOFS FAIL` is expected while laws 4 to 6 are open. Once all six hold, the check prints
`ALL PROOFS CHECK`.

## No example or unit tests

There are no example or unit tests, and none should be added as a correctness argument. A passing
example suite never substitutes for a law that has not been stated or proved. The CLI is
deliberately thin: reading arguments and files, mapping letters, and printing.

## Benchmarks are not tests

A benchmark measures how long the solver takes on fixed inputs. It answers "how fast", not "is it
right". A faster solver that returns a wrong tree is a regression, not a performance win. A correct
solver that is slow is still correct. The benchmark harness is not in this tree yet.

## Current checks in CI

CI currently checks pull request conventions only: the PR title and every commit subject are
conventional commits, and the head branch name matches the branch naming rule. See
[contributing.md](contributing.md). The law check is not wired into CI yet.
