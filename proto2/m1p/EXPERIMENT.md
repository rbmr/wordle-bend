# Parallel-scan experiment (`@unsafe`, separate from `proto2/m1`)

`proto2/m1` is the safe build. This tree copies it and adds one experiment:
split the per-bucket branching-factor scan (`kmax`, Rust's
`compute_max_branching_factor_seq_with_target`) over four lanes.

Entry points (extra CLI argument):

| argument | configuration |
|---|---|
| (none) | safe sequential build of this tree (flag cell = 0) |
| `70000` | parallel root only (same as `proto2/m1`) |
| `80000` | four-lane scan, per-lane maxima merged at the end |
| `80001` | `80000` + parallel root |
| `80002` | four-lane scan with one shared `mx` cell (atomic max) |
| `80003` | `80002` + parallel root |

Mechanism: `Array.fork` gives four handles to one block; lanes only read the
tables (feedback, set, guess/profile masks) and write only their own
count/touched/result cells, so no write is raced. `80002`/`80003` share the
running maximum through `Array.atomic.max`.

`test/lanes.bend` is the minimal runtime-scaling check: four independent lanes
of dependent arithmetic. It measures 3.9x on the 4-core test machine, so the
scheduler is not the limit; the scan's row-major feedback reads are.

Measured (pc2, whole process, costs exact): N=300 1.86 s -> 1.43 s (3.0 s of
user CPU), N=500 63.8 s -> 30.9 s (102 s of user CPU).
