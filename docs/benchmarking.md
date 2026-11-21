# Benchmarking

The benchmark harness measures how long the solver takes on fixed inputs and records the numbers in
a CSV so that runs are comparable across commits, machines and hardware classes. It answers "how
fast", never "is it right": correctness is established by the laws in `LAWS.bend`, `PROOF.bend` and
`proofs/`, as [testing.md](testing.md) explains. A faster run that prints a different tree is a
regression, not a win.

The harness is in `bench/`, the solver is in `src/`, and the bundled lists are in `words/`. The
reference solver is exact but exponential, so benchmark sizes must stay small until the faster
search lands. [performance.md](performance.md) records the current status and the optimisation
plan.

## What is measured

The measured command is the solver CLI:

```sh
<binary> --guesses <file> --candidates <file>
```

Its stdout is the policy tree. The harness builds the binary once from `src/main.bend` with
`bend src/main.bend -o <binary>` (clang 19 or newer must be on `PATH`), then times each run with a
monotonic clock and records the wall-clock seconds. Build time is not part of a row: it is paid once
per invocation and would otherwise be counted against every input.

Wall-clock time is the reported quantity because it is what a user waits for. It includes process
startup, file reads and all the work HVM does on CPU and GPU. It does not separate CPU time from GPU
time; that is deliberate, since the result the project cares about is the complete run.

## Inputs are seeded subsets

`words/candidates.txt` is the full candidate list. For each `(seed, size)` pair, `bench/sample.sh`
prints a deterministic subset of `size` candidate lines. For the same seed, size and file the output
is identical on every machine:

- the PRNG is a hand-written 32-bit linear congruential generator in awk, using only integer
  arithmetic that is exact in an IEEE-754 double;
- lines are chosen by a partial Fisher-Yates shuffle over line numbers;
- the chosen lines are printed in their original file order.

If `size` is at least the number of lines in the file, every line is printed. Seeds and sizes are
non-negative integers.

The guesses list for a run is the sampled candidate subset followed by the first 200 lines of
`words/guesses.txt`. This is a fixed, small guess pool: using the full guesses list would make every
row more expensive as the bundled list grows, and would change the meaning of old and new rows. The
subset plus the fixed prefix keeps the inputs small and comparable across commits. The choice is
part of the protocol; changing it changes the benchmark and requires new rows rather than edits to
old ones.

## Repeats and consistency

Each `(size, seed)` group is run `--repeats` times. Every run's stdout is hashed with sha256, and
all rows of the group carry `consistent=1` only when every repeat produced the same hash.

`consistent` is not a correctness result. It says the run was repeatable for this input; a wrong
tree that is wrong the same way every time still hashes identically. Correctness comes from the
laws. A `consistent=0` group does mean the solver is non-deterministic on that input, which makes
its timings hard to compare and should be investigated before the numbers are used.

## One job at a time

Run benchmarks on an idle machine, with no other solver, build or GPU workload running. Wall-clock
time includes contention from other processes, so a busy machine produces rows that look slower for
reasons unrelated to the commit. Run one benchmark at a time per machine: `bench/remote.sh` refuses
to start when a remote `bench/run.sh` is already running, and the same rule applies locally. Pin
the hardware class in `--label` and do not mix labels in one comparison.

Wall-clock numbers are noisy even on an idle machine. That is why a group has several repeats:
compare the minimum of the repeats for the least-noise estimate, and treat small differences
between commits as noise rather than signal.

## Running

From the repository root:

```sh
bench/run.sh --sizes "50 100 200" --seeds "1 2 3" --repeats 3 --label "cpu-class-a"
```

Options:

| Option | Meaning |
| --- | --- |
| `--sizes "50 100 200"` | candidate counts to sample |
| `--seeds "1 2 3"` | sampling seeds |
| `--repeats 3` | runs per `(size, seed)` |
| `--main src/main.bend` | Bend source to build |
| `--label <text>` | free-form tag for the hardware class; `BENCH_LABEL` is the fallback |
| `--out bench/results.csv` | CSV to append to |
| `--allow-dirty` | run with a dirty tree and record `dirty=1` |

The harness refuses to start when `git status --porcelain` is non-empty unless `--allow-dirty` is
given. It records the short commit hash from `git rev-parse --short HEAD`.

`BENCH_BINARY` skips the build and runs the given executable. It exists so a prebuilt solver can be
timed without rebuilding, and so the harness can be checked against a known executable; the binary
must accept the same `--guesses` and `--candidates` arguments.

`BENCH_COMMIT` supplies the commit hash when the tree has no `.git`, as in a remote run. The label is
always supplied by the caller, never auto-detected: no hostname or machine name is recorded.

To use another machine:

```sh
BENCH_HOST=<ssh-target> bench/remote.sh --sizes "50 100 200" --seeds "1 2 3" --repeats 3 --label "gpu-class-a"
```

`bench/remote.sh` requires `BENCH_HOST`, refuses if the local tree is dirty, refuses if a benchmark
is already running remotely, and rsyncs the tree (without `.git` and without `bench/results.csv`)
to `~/wordle-bend-bench` on the target. It runs `bench/run.sh` there with the same options, passing
the local commit hash as `BENCH_COMMIT`, then appends the remote rows to the local CSV. `timeout`
guards the ssh calls; `BENCH_SSH_TIMEOUT` sets the benchmark call's limit in seconds (default 3600).

## Reading results.csv

Rows are appended, never rewritten. The header is:

```
date_utc,commit,dirty,label,cpu_model,gpu,size,seed,repeat,wall_s,exit_code,output_sha256,consistent
```

| Column | Meaning |
| --- | --- |
| `date_utc` | UTC timestamp when the group's rows were written |
| `commit` | short commit hash the binary was built from |
| `dirty` | `1` if the tree had uncommitted changes, else `0` |
| `label` | caller-supplied hardware or scenario tag |
| `cpu_model` | CPU model from `/proc/cpuinfo` |
| `gpu` | first GPU name from `nvidia-smi`, or `none` |
| `size` | requested candidate count |
| `seed` | sampling seed |
| `repeat` | 1-based repeat number inside the group |
| `wall_s` | wall-clock seconds, six decimals |
| `exit_code` | process exit status |
| `output_sha256` | sha256 of stdout |
| `consistent` | `1` when all repeats in the group hashed identically, else `0` |

A group is one `(commit, dirty, label, cpu_model, gpu, size, seed)` tuple. Compare commits only
inside a group: the same commit on a different label, CPU or GPU is a different measurement.
`bench/run.sh` exits non-zero if any run exited non-zero, and still records the failing row with its
`exit_code` and hash. Filter those out before averaging.

A practical read is: select one label and CPU/GPU class, take the minimum `wall_s` per
`(commit, size, seed)` over repeats, then compare those minima across commits at the same size. Look
at how time grows with `size` before drawing conclusions from a handful of small inputs.

## Adding a row type

A row type is a benchmark scenario: a distinct `(--main, label, sizes, seeds)` combination. The CSV
schema does not change for a new scenario. The usual way to add one is a separate invocation with a
distinct `--label`, for example a different hardware class or a different solver entry point.
Existing rows keep their meaning because each row carries its own label.

To add a new column (a new thing measured rather than a new scenario), append it at the end of the
header, write it in `bench/run.sh`'s row `printf`, and document it in the table above. Appending
keeps older rows readable with the new field empty; do not rename or reorder existing columns.
Changing the inputs (the candidate source, the fixed guess prefix, the sampling algorithm) is not a
row type change: it invalidates comparison with older rows, so record such a change explicitly in
the commit and start a new label rather than mixing results.
