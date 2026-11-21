# Testing

**Status: scaffolding, in progress.** No tests, laws, or benchmarks exist yet. This document states
the principle the project is built on, so that the first code added follows it.

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
across machines and across changes.

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

## Proof gate on pull requests

`.github/workflows/proofs.yml` runs the proof checks on every pull request. While `PROOF.bend` is
absent from the repository root the job passes with a notice and skips the checks, because the file
arrives in a later change. Once it exists, both checks must pass:

| Command | Contract |
| --- | --- |
| `bend PROOF.bend` | prints `ALL PROOFS CHECK` and exits 0; prints `SOME PROOFS FAIL` and exits 1 when any law is open or false |
| `bend PROOF.bend --verdict` | the same contract, as a second independent check with the kernel proven in Lean |

### Running the checks locally

Install the pinned Bend release into `~/.bend`, which is where the binary looks for its runtime
data:

```sh
curl -O https://github.com/bendlang/bend/releases/download/v2.0.40/bend-2.0.40-linux-x64.tar.gz
tar -xzf bend-2.0.40-linux-x64.tar.gz
mkdir -p ~/.bend/bin
install -m 0755 bend/bin/bend ~/.bend/bin/bend
mv bend/bend2 bend/guide ~/.bend/
export PATH="$HOME/.bend/bin:$PATH"
```

Then run the two checks from the repository root:

```sh
bend PROOF.bend
bend PROOF.bend --verdict
```

`--verdict` builds the Lean kernel on first use. That takes about 40 seconds and the result is
cached under `~/.bend/bendtt`. It needs elan with the pinned Lean toolchain, which the workflow sets
through `ELAN_TOOLCHAIN`:

```sh
elan toolchain install leanprover/lean4:v4.34.0
ELAN_TOOLCHAIN=leanprover/lean4:v4.34.0 bend PROOF.bend --verdict
```

CI caches `~/.elan/toolchains` and `~/.bend/bendtt` under a key built from the Bend and Lean
versions.

### Bumping the pinned Bend version

`BEND_VERSION` and `BEND_SHA256` at the top of `.github/workflows/proofs.yml` pin the release that
CI installs. To bump, download the new `bend-<version>-linux-x64.tar.gz`, confirm its sha256, and
update both values together. Do it in its own pull request: the proof checks are tied to the
toolchain, so a version bump is a deliberate change rather than routine maintenance.

## Current checks in CI

CI checks pull request conventions: the PR title and every commit subject are conventional commits,
and the head branch name matches the branch naming rule. See [contributing.md](contributing.md).
It also runs the proof gate above, which passes with a notice until `PROOF.bend` lands. Solver
benchmarks are not wired into CI yet.
