#!/bin/bash
set -eu
export PATH=$HOME/tc/bin:$PATH
C=${CC:-clang}
$C -std=c11 -O3 bench_c3.c -o bench_c3
now() { date +%s%N; }
run() {
  local bin=$1 n=$2 reps=$3
  local t0 t1 out
  t0=$(now); out=$("$bin" "$n" "$reps"); t1=$(now)
  echo "$bin n=$n reps=$reps ns=$((t1 - t0)) out=$out"
}
one() { local n=$1; shift
  ./solver "$n" 1 >/dev/null; ./bench_c3 "$n" 1 >/dev/null
  for reps in "$@"; do run ./solver "$n" "$reps"; run ./bench_c3 "$n" "$reps"; done
}
one 10 50 100 200
one 300 25 50 100
