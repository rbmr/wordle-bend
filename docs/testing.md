# Testing

**Status: scaffolding, in progress.** No tests or laws exist yet. The benchmark harness exists in
`bench/`, but there is no solver for it to measure yet. This document states the principle the
project is built on, so that the first code added follows it.

## Correctness is established by laws, not examples

For a solver of this kind, example tests are a weak argument. A test that runs one word list and
checks a known answer says something about that one input. It says nothing about the inputs nobody
chose to test, and the interesting failures in a search algorithm are exactly the inputs nobody
thought of.

So correctness here is a proof obligation, carried by `laws/`:

- the returned tree is **valid** for its input: every leaf is a candidate, and following the tree
  for a candidate reaches that candidate;
- the returned tree is **optimal** for its input: no valid tree for the same input has a lower
  total number of guesses over all candidates.

The laws are stated formally and checked mechanically, and the check is part of the repository
rather than a claim about a run. The target is a guarantee that holds for every input the solver
accepts, not for a sample of inputs. When the implementation changes, the laws are the thing that
must still hold; the proof check is what fails if it does not.

Example tests may still exist for narrow purposes, such as pinning down an output format or
checking argument parsing in the CLI. They are not the correctness argument, and a passing example
suite never substitutes for a law that has not been stated or proved.

## Benchmarks are not tests

`bench/` measures how long the solver takes on fixed inputs. It answers "how fast", not "is it
right". A benchmark result is a wall-clock number, and it is reported so that runs are comparable
across machines and across changes. The protocol and the result format are described in
[benchmarking.md](benchmarking.md).

Keeping the two separate matters:

| | Tests and laws | Benchmarks |
| --- | --- | --- |
| Question | is the output correct for every input | how long did this run take |
| Basis | proof, mechanically checked | measurement |
| Failure | the law does not hold, or the proof does not check | the run is slower, or fails to finish in time |
| Effect on the guarantee | this is the guarantee | none |

A faster solver that returns a wrong tree is a regression, not a performance win. A correct solver
that is slow is still correct. Performance work is judged against benchmark results, and correctness
work is judged by the laws.

## Current checks in CI

CI currently checks pull request conventions only: the PR title and every commit subject are
conventional commits, and the head branch name matches the branch naming rule. See
[contributing.md](contributing.md). Solver checks, law checks, and benchmarks are not wired into CI
yet.
