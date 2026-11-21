#!/usr/bin/env bash
# Start a benchmark in the background and return at once.
#
# Usage: bench/start.sh [options]
#
#   --sizes "50 100 200"   candidate counts (default "50 100 200")
#   --seeds "1 2 3"        sampling seeds (default "1 2 3")
#   --repeats 3            runs per (size, seed) (default 3)
#   --label <text>         free-form tag such as a hardware class
#   --main src/main.bend   Bend source of the solver (default src/main.bend)
#   --time-limit 7200      hard wall-clock limit in seconds (default 7200,
#                          and 7200 is the largest accepted value)
#
# The work runs detached under nohup, setsid and timeout. This script records
# the run under bench/runs/<UTC timestamp>-<commit>/ and exits immediately:
#
#   meta.txt     commit, command line, label, sizes, seeds, repeats, limit,
#                start time and CPU model
#   console.log  everything bench/run.sh printed
#   rows.csv     the rows for this run (bench/run.sh --out)
#   pid          the detached supervisor's process id
#   status.txt   written when the run ends: exit code, end time, timed out
#
# The run id is also written to bench/runs/CURRENT. Check on the run with
# bench/status.sh and append its rows to bench/results.csv with
# bench/record.sh.
#
# The tree must be clean, except for bench/runs/ and bench/results.csv, and
# only one benchmark may run at a time on a machine.
#
# Environment passed through to bench/run.sh: BENCH_LABEL (used when --label
# is not given) and BENCH_BINARY (run this executable instead of building).
# Nothing raises the time limit: a run that needs more than two hours should
# use smaller sizes or fewer seeds, not a longer wait.

set -u -o pipefail

max_time_limit=7200

die() {
	echo "bench/start.sh: $*" >&2
	exit 2
}

usage() {
	cat <<'EOF'
usage: bench/start.sh [options]

  --sizes "50 100 200"     candidate counts (default "50 100 200")
  --seeds "1 2 3"          sampling seeds (default "1 2 3")
  --repeats 3              runs per (size, seed) (default 3)
  --label <text>           free-form tag such as a hardware class
  --main src/main.bend     Bend source of the solver (default src/main.bend)
  --time-limit 7200        hard wall-clock limit in seconds; at most 7200

Starts the run detached, prints the run id, the limit and the command to
check on it, then exits. See also bench/status.sh and bench/record.sh.
EOF
}

script_dir=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
root=$(CDPATH='' cd -- "$script_dir/.." && pwd)
cd "$root" || exit 2

runs=bench/runs
lock=$runs/lock

sizes="50 100 200"
seeds="1 2 3"
repeats=3
label=${BENCH_LABEL:-}
main=src/main.bend
time_limit=$max_time_limit

original_args=("$@")

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
	--label)
		[ "$#" -ge 2 ] || die "--label needs a value"
		label=$2
		shift 2
		;;
	--main)
		[ "$#" -ge 2 ] || die "--main needs a value"
		main=$2
		shift 2
		;;
	--time-limit)
		[ "$#" -ge 2 ] || die "--time-limit needs a value"
		time_limit=$2
		shift 2
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

case $time_limit in
'' | *[!0-9]*) die "--time-limit must be a positive integer number of seconds" ;;
esac
# Strip leading zeros so the comparison below is decimal, not octal.
time_limit=$(printf '%s\n' "$time_limit" | sed 's/^0*//')
[ -n "$time_limit" ] || time_limit=0
if [ "${#time_limit}" -gt 5 ] || [ "$time_limit" -gt "$max_time_limit" ]; then
	die "--time-limit exceeds the ${max_time_limit} s cap; a longer run needs smaller sizes or fewer seeds, not a longer limit"
fi
[ "$time_limit" -gt 0 ] || die "--time-limit must be greater than zero"

git rev-parse --git-dir >/dev/null 2>&1 ||
	die "not a git repository; a run is labelled with a commit"
commit=$(git rev-parse --short HEAD) || die "cannot read HEAD"

# Only the run directory and the results CSV may differ from HEAD; everything
# else means the binary would not match the commit in the metadata.
status_output=$(git status --porcelain) || die "cannot read git status"
dirty=
while IFS= read -r line; do
	[ -n "$line" ] || continue
	path=${line:3}
	case $path in
	*' -> '*) path=${path##* -> } ;;
	esac
	case $path in
	'"'*'"')
		path=${path#\"}
		path=${path%\"}
		;;
	esac
	case $path in
	bench/runs | bench/runs/* | bench/results.csv) continue ;;
	esac
	dirty+="$line; "
done <<<"$status_output"
[ -z "$dirty" ] ||
	die "working tree is dirty (only bench/runs/ and bench/results.csv may change): $dirty"

mkdir -p "$runs" || die "cannot create $runs"

# The lock names the run that owns the machine. A lock is stale only when the
# pid recorded for that run is gone; a lock without a pid may be a start in
# progress, so it is left alone.
if [ -e "$lock" ]; then
	other_run=$(cat "$lock" 2>/dev/null || true)
	other_pid=$(cat "$runs/$other_run/pid" 2>/dev/null || true)
	if [ -n "$other_pid" ]; then
		if kill -0 "$other_pid" 2>/dev/null; then
			die "a benchmark is already running (run $other_run, pid $other_pid); check it with bench/status.sh"
		fi
	elif [ -n "$other_run" ] && [ -d "$runs/$other_run" ]; then
		die "a benchmark is already starting or its supervisor died (run $other_run); if it is gone, remove $lock and bench/runs/$other_run/pid"
	else
		die "a benchmark lock exists ($lock) without a run; if nothing is running, remove it"
	fi
	rm -f "$lock" || die "cannot remove the stale lock $lock"
fi

stamp=$(date -u +%Y%m%dT%H%M%SZ)
run_id=$stamp-$commit
if [ -e "$runs/$run_id" ]; then
	n=2
	while [ -e "$runs/$run_id-$n" ]; do
		n=$((n + 1))
	done
	run_id=$run_id-$n
fi
rundir=$runs/$run_id
mkdir -p "$rundir" || die "cannot create $rundir"

# Create the lock without overwriting one that appeared meanwhile, so that two
# starts in the same instant cannot both run.
if ! (set -C; printf '%s\n' "$run_id" >"$lock") 2>/dev/null; then
	rmdir "$rundir" 2>/dev/null
	die "another start is in progress; check with bench/status.sh"
fi

cpu_model=$(awk -F: '/^model name/ {
	sub(/^[ \t]+/, "", $2)
	sub(/[ \t]+$/, "", $2)
	print $2
	exit
}' /proc/cpuinfo 2>/dev/null)
[ -n "$cpu_model" ] || cpu_model=unknown

started_epoch=$(date +%s)
cmd_line=$(printf '%q ' bench/start.sh "${original_args[@]}")
cmd_line=${cmd_line% }

{
	printf 'commit: %s\n' "$commit"
	printf 'command: %s\n' "$cmd_line"
	printf 'label: %s\n' "$label"
	printf 'sizes: %s\n' "$sizes"
	printf 'seeds: %s\n' "$seeds"
	printf 'repeats: %s\n' "$repeats"
	printf 'main: %s\n' "$main"
	printf 'time_limit: %s\n' "$time_limit"
	printf 'started_utc: %s\n' "$(date -u +%Y-%m-%dT%H:%M:%SZ)"
	printf 'started_epoch: %s\n' "$started_epoch"
	printf 'cpu_model: %s\n' "$cpu_model"
} >"$rundir/meta.txt" || {
	rm -f "$lock"
	die "cannot write $rundir/meta.txt"
}

# The supervisor writes its own pid so that the recorded pid is the process
# bench/status.sh checks with kill -0, whatever setsid does on the way.
# The body runs in a new bash: its $ references must stay literal here.
# shellcheck disable=SC2016
launcher='
root=$1
rundir=$2
limit=$3
shift 3
printf "%s\n" "$$" >"$rundir/pid"
cd "$root" || exit 2
timeout --signal=TERM --kill-after=30 "$limit" bench/run.sh "$@"
rc=$?
ended_epoch=$(date +%s)
timed_out=no
case $rc in
124 | 137) timed_out=yes ;;
esac
{
	printf "exit_code: %s\n" "$rc"
	printf "ended_utc: %s\n" "$(date -u +%Y-%m-%dT%H:%M:%SZ)"
	printf "ended_epoch: %s\n" "$ended_epoch"
	printf "timed_out: %s\n" "$timed_out"
} >"$rundir/status.txt"
'

run_args=(
	--sizes "$sizes"
	--seeds "$seeds"
	--repeats "$repeats"
	--label "$label"
	--main "$main"
	--out "$rundir/rows.csv"
)

nohup setsid bash -c "$launcher" bench-start-detach \
	"$root" "$rundir" "$time_limit" "${run_args[@]}" \
	>"$rundir/console.log" 2>&1 </dev/null &
run_pid=$!

printf '%s\n' "$run_id" >"$runs/CURRENT" || {
	if kill -0 "$run_pid" 2>/dev/null; then
		kill "$run_pid" 2>/dev/null
	fi
	die "cannot write $runs/CURRENT"
}

printf 'run: %s\n' "$run_id"
printf 'time limit: %s s\n' "$time_limit"
printf 'check: bench/status.sh %s\n' "$run_id"
