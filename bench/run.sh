#!/usr/bin/env bash
# Run the solver benchmark on fixed inputs and append the results to a CSV.
#
# Usage: bench/run.sh [options]
#
#   --sizes "50 100 200"   candidate counts to benchmark (default "50 100 200")
#   --seeds "1 2 3"        sampling seeds (default "1 2 3")
#   --repeats 3            runs per (size, seed) (default 3)
#   --main src/main.bend   Bend source of the solver (default src/main.bend)
#   --label <text>         free-form tag such as a hardware class
#   --out bench/results.csv  CSV to append to (default bench/results.csv)
#   --allow-dirty          run even if the working tree has uncommitted changes
#
# Environment:
#   BENCH_LABEL   used when --label is not given
#   BENCH_BINARY  skip the build and use this executable instead
#   BENCH_COMMIT  commit hash to record when the tree has no .git (remote runs)
#
# The candidate subset is sample.sh(seed, size, words/candidates.txt). The
# guesses are that subset followed by the first 200 lines of
# words/guesses.txt: a fixed, small guess pool that keeps runs comparable.
#
# Paths are relative to the repository root. Exits non-zero if any run failed.

set -u -o pipefail

die() {
	echo "bench: $*" >&2
	exit 2
}

usage() {
	cat <<'EOF'
usage: bench/run.sh [options]

  --sizes "50 100 200"     candidate counts (default "50 100 200")
  --seeds "1 2 3"          sampling seeds (default "1 2 3")
  --repeats 3              runs per (size, seed) (default 3)
  --main src/main.bend     Bend source of the solver (default src/main.bend)
  --label <text>           free-form tag such as a hardware class
  --out bench/results.csv  CSV to append to (default bench/results.csv)
  --allow-dirty            run even if the working tree is dirty

Environment: BENCH_LABEL (label fallback), BENCH_BINARY (skip the build and
use this executable), BENCH_COMMIT (commit to record when the tree has no
.git, as in a remote run).
EOF
}

script_dir=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
root=$(CDPATH='' cd -- "$script_dir/.." && pwd)
cd "$root" || exit 2

sizes="50 100 200"
seeds="1 2 3"
repeats=3
main=src/main.bend
label=${BENCH_LABEL:-}
out=bench/results.csv
allow_dirty=0

while [ "$#" -gt 0 ]; do
	case $1 in
	--sizes)
		[ "$#" -ge 2 ] || die "--sizes needs a value"
		sizes=$2
		shift 2
		;;
	--seeds)
		[ "$#" -ge 2 ] || die "--seeds needs a value"
		seeds=$2
		shift 2
		;;
	--repeats)
		[ "$#" -ge 2 ] || die "--repeats needs a value"
		repeats=$2
		shift 2
		;;
	--main)
		[ "$#" -ge 2 ] || die "--main needs a value"
		main=$2
		shift 2
		;;
	--label)
		[ "$#" -ge 2 ] || die "--label needs a value"
		label=$2
		shift 2
		;;
	--out)
		[ "$#" -ge 2 ] || die "--out needs a value"
		out=$2
		shift 2
		;;
	--allow-dirty)
		allow_dirty=1
		shift
		;;
	-h | --help)
		usage
		exit 0
		;;
	*)
		die "unknown option: $1"
		;;
	esac
done

case $repeats in
'' | *[!0-9]*) die "--repeats must be a positive integer" ;;
0) die "--repeats must be a positive integer" ;;
esac

for size in $sizes; do
	case $size in
	'' | *[!0-9]*) die "--sizes must be a space-separated list of integers" ;;
	esac
done
for seed in $seeds; do
	case $seed in
	'' | *[!0-9]*) die "--seeds must be a space-separated list of integers" ;;
	esac
done

candidates_all=words/candidates.txt
guesses_all=words/guesses.txt

[ -f "$candidates_all" ] || die "missing $candidates_all"
[ -f "$guesses_all" ] || die "missing $guesses_all"

if git rev-parse --git-dir >/dev/null 2>&1; then
	if [ -n "$(git status --porcelain)" ]; then
		dirty=1
		if [ "$allow_dirty" -ne 1 ]; then
			die "working tree is dirty; commit or stash, or pass --allow-dirty"
		fi
	else
		dirty=0
	fi
	commit=$(git rev-parse --short HEAD) || die "cannot read HEAD"
else
	# A benchmark tree copied to another machine has no .git. The caller
	# passes the real commit in BENCH_COMMIT so the rows stay attributable.
	dirty=0
	commit=${BENCH_COMMIT:-}
	[ -n "$commit" ] || die "no .git here and BENCH_COMMIT is not set"
fi

tmpdir=$(mktemp -d "${TMPDIR:-/tmp}/wordle-bench.XXXXXX") || die "cannot create temp dir"
trap 'rm -rf "$tmpdir"' EXIT INT TERM

if [ -n "${BENCH_BINARY:-}" ]; then
	binary=$BENCH_BINARY
	[ -x "$binary" ] || die "BENCH_BINARY is not executable: $binary"
else
	[ -f "$main" ] || die "missing Bend source: $main"
	command -v bend >/dev/null 2>&1 ||
		die "bend is not on PATH; the build needs bend and clang 19+"
	binary=$tmpdir/solver
	if ! bend "$main" -o "$binary" >"$tmpdir/build.log" 2>&1; then
		cat "$tmpdir/build.log" >&2
		die "build failed: bend $main -o <binary> (needs clang 19+)"
	fi
	[ -x "$binary" ] || die "build produced no executable: $binary"
fi

cpu_model=$(awk -F: '/^model name/ {
	sub(/^[ \t]+/, "", $2)
	sub(/[ \t]+$/, "", $2)
	print $2
	exit
}' /proc/cpuinfo 2>/dev/null)
[ -n "$cpu_model" ] || cpu_model=unknown

gpu=none
if command -v nvidia-smi >/dev/null 2>&1; then
	gpu_name=$(nvidia-smi --query-gpu=name --format=csv,noheader 2>/dev/null | head -n 1)
	if [ -n "$gpu_name" ]; then
		gpu=$gpu_name
	fi
fi

csv_field() {
	local value=$1
	value=${value//\"/\"\"}
	printf '"%s"' "$value"
}

header='date_utc,commit,dirty,label,cpu_model,gpu,size,seed,repeat,wall_s,exit_code,output_sha256,consistent'
mkdir -p -- "$(dirname -- "$out")" || die "cannot create directory for $out"
if [ ! -s "$out" ]; then
	printf '%s\n' "$header" >"$out" || die "cannot write $out"
fi

failed=0

for size in $sizes; do
	for seed in $seeds; do
		echo "bench: size=$size seed=$seed" >&2

		candidates=$tmpdir/candidates-$size-$seed.txt
		guesses=$tmpdir/guesses-$size-$seed.txt

		"$script_dir/sample.sh" "$seed" "$size" "$candidates_all" >"$candidates" ||
			die "sampling candidates failed"

		# Fixed guess pool: the sampled candidates plus the first 200 lines
		# of words/guesses.txt. Using the full guesses list would make the
		# benchmark cost grow with the bundled word list.
		{
			cat "$candidates"
			head -n 200 "$guesses_all"
		} >"$guesses"

		walls=()
		codes=()
		hashes=()

		for ((repeat = 1; repeat <= repeats; repeat++)); do
			start=$(date +%s.%N)
			"$binary" --guesses "$guesses" --candidates "$candidates" >"$tmpdir/stdout" 2>"$tmpdir/stderr"
			code=$?
			end=$(date +%s.%N)

			wall=$(awk -v a="$start" -v b="$end" 'BEGIN { printf "%.6f", b - a }')
			hash=$(sha256sum "$tmpdir/stdout" | cut -d' ' -f1)

			walls[repeat]=$wall
			codes[repeat]=$code
			hashes[repeat]=$hash

			[ "$code" -ne 0 ] && failed=1
		done

		consistent=1
		for ((repeat = 2; repeat <= repeats; repeat++)); do
			[ "${hashes[repeat]}" = "${hashes[1]}" ] || consistent=0
		done

		date_utc=$(date -u +%Y-%m-%dT%H:%M:%SZ)

		for ((repeat = 1; repeat <= repeats; repeat++)); do
			printf '%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s\n' \
				"$date_utc" \
				"$commit" \
				"$dirty" \
				"$(csv_field "$label")" \
				"$(csv_field "$cpu_model")" \
				"$(csv_field "$gpu")" \
				"$size" \
				"$seed" \
				"$repeat" \
				"${walls[repeat]}" \
				"${codes[repeat]}" \
				"${hashes[repeat]}" \
				"$consistent" >>"$out" || die "cannot append to $out"
		done
	done
done

exit "$failed"
