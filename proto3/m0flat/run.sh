#!/bin/bash
# Build the C twin with the same flags pc2 uses for the Bend build, then time
# both over a few repetition counts, one process at a time.
# Usage: [CC=clang] bash run.sh
set -eu
export PATH=$HOME/tc/bin:$PATH
C=${CC:-clang}
$C -std=c11 -O3 bench.c -o bench_c
now() { date +%s%N; }
run() {
  local bin=$1 n=$2 reps=$3 var=$4
  local t0 t1 out
  t0=$(now)
  out=$("$bin" "$n" "$reps" "$var")
  t1=$(now)
  echo "$bin n=$n reps=$reps var=$var ns=$((t1 - t0)) out=$out"
}
one() { local n=$1 var=$2; shift 2
  ./solver "$n" 1 "$var" >/dev/null; ./bench_c "$n" 1 "$var" >/dev/null
  for reps in "$@"; do
    run ./solver "$n" "$reps" "$var"
    run ./bench_c "$n" "$reps" "$var"
  done
}
for var in 0 1; do
  one 10 "$var" 1000 2000 4000
  one 300 "$var" 25 50 100
done
