#!/usr/bin/env bash
# Report on a detached benchmark run started with bench/start.sh.
#
# Usage: bench/status.sh [run-id]
#        bench/status.sh --list
#
# With no argument it reports the run named by bench/runs/CURRENT. It prints
# one of RUNNING, FINISHED (exit 0), FAILED (exit code) or TIMED OUT, the
# elapsed time against the limit, the run's meta.txt, the last 25 lines of
# console.log and the rows collected so far.
#
# It returns at once: it reads files, checks liveness with kill -0 and never
# waits for the run or follows the log.

set -u -o pipefail

die() {
	echo "bench/status.sh: $*" >&2
	exit 2
}

usage() {
	cat <<'EOF'
usage: bench/status.sh [run-id]
       bench/status.sh --list

Reports the run given on the command line, or the one in bench/runs/CURRENT.
--list prints every run, one per line, with its state.
EOF
}

script_dir=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
root=$(CDPATH='' cd -- "$script_dir/.." && pwd)
cd "$root" || exit 2

runs=bench/runs

# field <file> <key>  prints the value of a "key: value" line, if any.
field() {
	awk -v key="$2:" '$1 == key { print $2; exit }' "$1" 2>/dev/null
}

# state_of <run-dir> <run-id>  prints the state line for one run.
state_of() {
	local dir=$1
	local id=$2
	local exit_code timed_out pid
	if [ -f "$dir/status.txt" ]; then
		exit_code=$(field "$dir/status.txt" exit_code)
		timed_out=$(field "$dir/status.txt" timed_out)
		if [ "$timed_out" = yes ]; then
			printf 'TIMED OUT'
		elif [ "${exit_code:-1}" = 0 ]; then
			printf 'FINISHED (exit 0)'
		else
			printf 'FAILED (exit %s)' "${exit_code:-unknown}"
		fi
		return
	fi
	# No status file: the run is alive only if this is the locked run and its
	# recorded supervisor is still there. A run that is still starting has no
	# pid yet.
	if [ "$id" = "$(cat "$runs/CURRENT" 2>/dev/null || true)" ] &&
		[ "$id" = "$(cat "$runs/lock" 2>/dev/null || true)" ]; then
		pid=$(cat "$dir/pid" 2>/dev/null || true)
		if [ -z "$pid" ]; then
			printf 'RUNNING (starting)'
			return
		fi
		if kill -0 "$pid" 2>/dev/null; then
			printf 'RUNNING (pid %s)' "$pid"
			return
		fi
	fi
	printf 'FAILED (no status file)'
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
--list)
	found=0
	for dir in "$runs"/*/; do
		[ -d "$dir" ] || continue
		dir=${dir%/}
		id=${dir##*/}
		printf '%s %s\n' "$id" "$(state_of "$dir" "$id")"
		found=1
	done
	[ "$found" -eq 1 ] || echo "bench/status.sh: no runs yet" >&2
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

state=$(state_of "$dir" "$run_id")
started=$(field "$dir/meta.txt" started_epoch)
limit=$(field "$dir/meta.txt" time_limit)

elapsed=
if [ -n "$started" ]; then
	if [ -f "$dir/status.txt" ]; then
		ended=$(field "$dir/status.txt" ended_epoch)
		if [ -n "$ended" ]; then
			elapsed=$((ended - started))
		fi
	else
		elapsed=$(($(date +%s) - started))
	fi
fi

printf 'run: %s\n' "$run_id"
printf 'state: %s\n' "$state"
if [ -n "$elapsed" ] && [ -n "$limit" ]; then
	printf 'elapsed: %ss of %ss time limit\n' "$elapsed" "$limit"
fi
printf 'dir: %s\n' "$dir"

printf '%s\n' '--- meta.txt ---'
if [ -f "$dir/meta.txt" ]; then
	cat "$dir/meta.txt"
else
	echo '(no meta.txt)'
fi

printf '%s\n' '--- last 25 lines of console.log ---'
if [ -s "$dir/console.log" ]; then
	tail -n 25 "$dir/console.log"
else
	echo '(no output yet)'
fi

printf '%s\n' '--- rows.csv ---'
if [ -s "$dir/rows.csv" ]; then
	cat "$dir/rows.csv"
else
	echo '(no rows yet)'
fi

exit 0
