#!/usr/bin/env bash
# Run the benchmark harness on another machine over ssh.
#
# Usage: BENCH_HOST=<ssh-target> bench/remote.sh [bench/run.sh options]
#
# The target comes from BENCH_HOST and is never stored in the repository. The
# working tree is rsynced to ~/wordle-bend-bench on that machine (without .git
# and without bench/results.csv), bench/run.sh runs there with the same
# options, and the rows it produces are appended to the local CSV. The local
# commit hash is passed as BENCH_COMMIT so remote rows carry the real commit
# even though the remote tree has no .git.
#
# BENCH_SSH_TIMEOUT sets the timeout in seconds for the benchmark ssh call
# (default 3600).

set -u -o pipefail

die() {
	echo "remote: $*" >&2
	exit 2
}

host=${BENCH_HOST:-}
[ -n "$host" ] || die "BENCH_HOST is not set; set it to the ssh target to benchmark on"

script_dir=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
root=$(CDPATH='' cd -- "$script_dir/.." && pwd)
cd "$root" || exit 2

git rev-parse --git-dir >/dev/null 2>&1 || die "not a git repository"
if [ -n "$(git status --porcelain)" ]; then
	die "local working tree is dirty; commit or stash before running remotely"
fi
commit=$(git rev-parse --short HEAD) || die "cannot read HEAD"

ssh_timeout=${BENCH_SSH_TIMEOUT:-3600}

# Separate our own handling from the options forwarded to bench/run.sh.
# --allow-dirty is refused locally anyway and is replaced by BENCH_COMMIT;
# --out is replaced so the remote CSV contains only this run's rows.
args=()
out=bench/results.csv
while [ "$#" -gt 0 ]; do
	case $1 in
	--allow-dirty)
		shift
		;;
	--out)
		[ "$#" -ge 2 ] || die "--out needs a value"
		out=$2
		shift 2
		;;
	--out=*)
		out=${1#--out=}
		shift
		;;
	*)
		args+=("$1")
		shift
		;;
	esac
done

status=0
timeout 60 ssh "$host" "pgrep -f '[b]ench/run.sh'" >/dev/null 2>&1 || status=$?
case $status in
0) die "a benchmark is already running on $host" ;;
1) ;;
*) die "ssh check on $host failed (exit $status)" ;;
esac

timeout "$ssh_timeout" rsync -a --delete \
	--exclude='/.git' \
	--exclude='/bench/results.csv' \
	./ "$host:wordle-bend-bench/" ||
	die "rsync to $host failed"

remote_cmd="cd wordle-bend-bench && rm -f bench/results.csv &&"
if [ -n "${BENCH_LABEL:-}" ]; then
	remote_cmd+=" BENCH_LABEL=$(printf '%q' "$BENCH_LABEL")"
fi
remote_cmd+=" BENCH_COMMIT=$(printf '%q' "$commit") bash bench/run.sh"
for arg in "${args[@]}"; do
	remote_cmd+=" $(printf '%q' "$arg")"
done
remote_cmd+=" --out bench/results.csv"

echo "remote: running on $host at $commit" >&2
timeout "$ssh_timeout" ssh "$host" "$remote_cmd"
run_status=$?

rows=$(mktemp "${TMPDIR:-/tmp}/wordle-bench-rows.XXXXXX") || die "cannot create temp file"
trap 'rm -f "$rows"' EXIT INT TERM

copy_status=0
timeout 120 ssh "$host" "cat wordle-bend-bench/bench/results.csv" >"$rows" || copy_status=$?

if [ "$copy_status" -eq 0 ] && [ -s "$rows" ]; then
	mkdir -p -- "$(dirname -- "$out")"
	if [ ! -s "$out" ]; then
		printf '%s\n' 'date_utc,commit,dirty,label,cpu_model,gpu,size,seed,repeat,wall_s,exit_code,output_sha256,consistent' >"$out"
	fi
	# The remote CSV has the same header; append only its data rows.
	tail -n +2 "$rows" >>"$out" || die "cannot append to $out"
fi

[ "$run_status" -eq 124 ] && die "benchmark on $host timed out after ${ssh_timeout}s"
[ "$run_status" -ne 0 ] && exit "$run_status"
[ "$copy_status" -ne 0 ] && die "could not read the remote CSV (exit $copy_status)"

exit 0
