#!/bin/bash
# Compile the C twin with the same flags pc2 used for the Bend build, then
# time both over a few repetition counts. Usage: run.sh
set -eu
export PATH=$HOME/tc/bin:$PATH
C=${CC:-clang}
$C -std=c11 -O3 bench_c.c -o bench_c
now() { date +%s%N; }
run() {
  local bin=$1 n=$2 reps=$3
  local t0 t1 out
  t0=$(now)
  out=$("$bin" "$n" "$reps")
  t1=$(now)
  echo "$bin n=$n reps=$reps ns=$((t1 - t0)) out=$out"
}
one() {
  local n=$1
  shift
  ./solver "$n" 1 >/dev/null
  ./bench_c "$n" 1 >/dev/null
  for reps in "$@"; do
    run ./solver "$n" "$reps"
    run ./bench_c "$n" "$reps"
  done
}
one 10 1000 2000 4000
one 300 25 50 100
