#!/usr/bin/env bash
# Append the rows of a finished detached run to bench/results.csv.
#
# Usage: bench/record.sh [run-id]
#
# With no argument it records the run named by bench/runs/CURRENT. Only a run
# that finished with exit 0 is recorded: a missing status file (still running
# or killed), a non-zero exit code (a failed run) and a timed-out run are all
# refused, as is a run that was already recorded (the run directory then holds
# a `recorded` marker).
#
# The run's rows.csv rows are appended verbatim, without the header. Existing
# rows of bench/results.csv are never edited or removed: the file is
# append-only.

set -u -o pipefail

die() {
	echo "bench/record.sh: $*" >&2
	exit 2
}

usage() {
	cat <<'EOF'
usage: bench/record.sh [run-id]

Appends the rows of a finished run with exit code 0 to bench/results.csv.
With no argument, uses the run in bench/runs/CURRENT.
EOF
}

script_dir=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
root=$(CDPATH='' cd -- "$script_dir/.." && pwd)
cd "$root" || exit 2

runs=bench/runs
out=bench/results.csv

field() {
	awk -v key="$2:" '$1 == key { print $2; exit }' "$1" 2>/dev/null
}

if [ "$#" -gt 1 ]; then
	usage >&2
	exit 2
fi
case ${1:-} in
-h | --help)
	usage
	exit 0
	;;
esac

run_id=${1:-}
if [ -z "$run_id" ]; then
	run_id=$(cat "$runs/CURRENT" 2>/dev/null || true)
	[ -n "$run_id" ] || die "no run id given and $runs/CURRENT does not exist"
fi

dir=$runs/$run_id
[ -d "$dir" ] || die "no such run: $run_id (see bench/status.sh --list)"
[ -f "$dir/status.txt" ] ||
	die "run $run_id has not finished yet; check it with bench/status.sh"

timed_out=$(field "$dir/status.txt" timed_out)
if [ "$timed_out" = yes ]; then
	die "run $run_id timed out at the time limit; nothing recorded"
fi

exit_code=$(field "$dir/status.txt" exit_code)
if [ "$exit_code" != 0 ]; then
	die "run $run_id finished with exit code ${exit_code:-unknown}; nothing recorded"
fi

if [ -e "$dir/recorded" ]; then
	die "run $run_id is already recorded in $out"
fi

rows=$dir/rows.csv
[ -s "$rows" ] || die "run $run_id has no rows in $rows"
row_lines=$(wc -l <"$rows")
[ "$row_lines" -gt 1 ] || die "run $run_id has only a header in $rows; nothing recorded"

if [ ! -s "$out" ]; then
	head -n 1 "$rows" >"$out" || die "cannot write the header of $out"
fi

# Claim the run before appending, so that two records of the same run cannot
# both add its rows. The marker is removed again if the append fails.
if ! (set -C; printf 'recorded_utc: %s\n' "$(date -u +%Y-%m-%dT%H:%M:%SZ)" >"$dir/recorded") 2>/dev/null; then
	die "run $run_id is already recorded in $out"
fi
if ! tail -n +2 "$rows" >>"$out"; then
	rm -f "$dir/recorded"
	die "cannot append to $out"
fi

printf 'recorded %s rows from %s in %s\n' "$((row_lines - 1))" "$run_id" "$out"
