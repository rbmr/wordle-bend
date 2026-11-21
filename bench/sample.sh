#!/bin/sh
# Print a deterministic seeded subset of a file, one line per line.
#
# Usage: sample.sh <seed> <size> <input-file>
#
# For the same seed, size and file the output is identical on every machine:
# the PRNG below is written by hand in awk and uses only integer arithmetic
# that is exact in an IEEE-754 double. Lines are chosen with a partial
# Fisher-Yates shuffle over line numbers, then printed in their original file
# order. If size is at least the number of lines, every line is printed.

set -eu

usage() {
	echo "usage: sample.sh <seed> <size> <input-file>" >&2
	exit 2
}

[ "$#" -eq 3 ] || usage

seed=$1
size=$2
input=$3

case $seed in
'' | *[!0-9]*)
	echo "sample.sh: seed must be a non-negative integer" >&2
	exit 2
	;;
esac

case $size in
'' | *[!0-9]*)
	echo "sample.sh: size must be a non-negative integer" >&2
	exit 2
	;;
esac

[ -f "$input" ] || {
	echo "sample.sh: no such file: $input" >&2
	exit 2
}

awk -v seed="$seed" -v want="$size" '
function next_rand() {
	# 32-bit linear congruential generator (Numerical Recipes constants).
	# 1664525 * (2^32 - 1) is below 2^53, so every intermediate value is an
	# exact integer in a double and the sequence is portable.
	state = (1664525 * state + 1013904223) % 4294967296
	return state
}
{ line[NR] = $0 }
END {
	n = NR
	if (want >= n) {
		for (i = 1; i <= n; i++) print line[i]
		exit
	}
	if (want == 0) exit

	state = seed % 4294967296
	# Discard the first few values so that small seeds diverge quickly.
	for (i = 0; i < 8; i++) next_rand()

	for (i = 1; i <= n; i++) idx[i] = i
	for (i = 1; i <= want; i++) {
		j = i + next_rand() % (n - i + 1)
		t = idx[i]
		idx[i] = idx[j]
		idx[j] = t
	}

	# Put the chosen line numbers back into ascending order so the subset
	# keeps the order of the input file.
	for (i = 2; i <= want; i++) {
		t = idx[i]
		for (j = i - 1; j >= 1 && idx[j] > t; j--) idx[j + 1] = idx[j]
		idx[j + 1] = t
	}

	for (i = 1; i <= want; i++) print line[idx[i]]
}
' "$input"
