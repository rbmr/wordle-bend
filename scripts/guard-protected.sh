#!/usr/bin/env bash
# Fail a pull request that changes the files which define what the program
# must do and how it is measured.
#
# Run from a checkout of the base branch. The base and head commits are the
# only inputs, and the head is read as git data: it is never checked out and
# none of its content is executed.
#
# Usage: scripts/guard-protected.sh <base-sha> <head-sha>
#
# bench/start.sh, bench/status.sh and bench/record.sh are optional until they
# land on the base branch. Adding one is allowed while it is missing; once it
# exists on the base branch it is protected like the rest.
#
# See docs/contributing.md, section "Protected files".

set -u -o pipefail

usage() {
	printf 'usage: scripts/guard-protected.sh <base-sha> <head-sha>\n' >&2
	exit 2
}

[ "$#" -eq 2 ] || usage
base=$1
head=$2

status=0

fail() {
	printf 'protected-files: rule (%s): %s\n' "$1" "$2" >&2
	status=1
}

if ! git cat-file -e "${base}^{commit}" 2>/dev/null; then
	printf 'protected-files: cannot read base commit %s\n' "$base" >&2
	exit 2
fi

if ! git cat-file -e "${head}^{commit}" 2>/dev/null; then
	printf 'protected-files: cannot read head commit %s\n' "$head" >&2
	exit 2
fi

merge_base=$(git merge-base "$base" "$head") || {
	printf 'protected-files: %s and %s have no common ancestor\n' "$base" "$head" >&2
	exit 2
}

tmp=$(mktemp -d "${TMPDIR:-/tmp}/protected-files.XXXXXX") || {
	printf 'protected-files: cannot create a temporary directory\n' >&2
	exit 2
}
trap 'rm -rf "$tmp"' EXIT HUP INT TERM

is_protected() {
	case $1 in
	LAWS.bend | scripts/check-proofs.sh | scripts/guard-protected.sh | \
		bench/run.sh | bench/sample.sh)
		return 0
		;;
	bench/start.sh | bench/status.sh | bench/record.sh)
		# Allowed only while the base branch does not have the file yet.
		git cat-file -e "${base}:$1" 2>/dev/null
		return
		;;
	.githooks/* | .github/workflows/*.yml)
		return 0
		;;
	esac
	return 1
}

change_word() {
	case $1 in
	A*) printf 'added' ;;
	M*) printf 'modified' ;;
	D*) printf 'deleted' ;;
	R*) printf 'renamed' ;;
	C*) printf 'copied' ;;
	T*) printf 'type changed' ;;
	*) printf 'changed' ;;
	esac
}

# Rule (a): no change, of any kind, to a protected path.
if ! changes=$(git -c core.quotePath=false diff --no-ext-diff --no-textconv \
	--name-status -M "$base...$head"); then
	printf 'protected-files: cannot diff %s...%s\n' "$base" "$head" >&2
	exit 2
fi

while IFS=$'\t' read -r change path_from path_to; do
	[ -n "$change" ] || continue
	case $change in
	R* | C*)
		for path in "$path_from" "$path_to"; do
			[ -n "$path" ] || continue
			if is_protected "$path"; then
				fail a "protected file $(change_word "$change") (${change}): $path"
			fi
		done
		;;
	*)
		if is_protected "$path_from"; then
			fail a "protected file $(change_word "$change") (${change}): $path_from"
		fi
		;;
	esac
done <<<"$changes"

# Rule (b): PENDING_LAWS may lose names but never gain one.
normalize_pending() {
	sed -e 's/#.*//' -e 's/^[[:space:]]*//' -e 's/[[:space:]]*$//' -e '/^$/d'
}

base_pending=$(git show "${merge_base}:PENDING_LAWS" 2>/dev/null |
	normalize_pending | sort -u || true)
head_pending=$(git show "${head}:PENDING_LAWS" 2>/dev/null |
	normalize_pending | sort -u || true)

while IFS= read -r name; do
	[ -n "$name" ] || continue
	if ! grep -Fxq -- "$name" <<<"$base_pending"; then
		fail b "PENDING_LAWS adds the law '$name'; the list may only shrink"
	fi
done <<<"$head_pending"

# Rule (c): bench/results.csv may only grow, by whole rows at the end.
ends_with_newline() {
	[ -s "$1" ] || return 1
	[ "$(tail -c 1 -- "$1" | od -An -t u1 | tr -d '[:space:]')" = 10 ]
}

results=bench/results.csv
if git cat-file -e "${merge_base}:${results}" 2>/dev/null; then
	if ! git cat-file -e "${head}:${results}" 2>/dev/null; then
		fail c "$results is deleted; existing rows may not be removed"
	else
		git show "${merge_base}:${results}" >"$tmp/results.base"
		git show "${head}:${results}" >"$tmp/results.head"
		base_size=$(wc -c <"$tmp/results.base")
		head_size=$(wc -c <"$tmp/results.head")
		if [ "$head_size" -lt "$base_size" ]; then
			fail c "$results removes or rewrites existing rows; only appending rows at the end is allowed"
		elif ! cmp -s -n "$base_size" "$tmp/results.base" "$tmp/results.head"; then
			fail c "$results modifies existing rows; only appending rows at the end is allowed"
		elif [ "$head_size" -gt "$base_size" ]; then
			if ! ends_with_newline "$tmp/results.base"; then
				fail c "$results appends to the last existing row; only whole rows at the end are allowed"
			elif ! ends_with_newline "$tmp/results.head"; then
				fail c "$results appends an incomplete row; only whole rows at the end are allowed"
			fi
		fi
	fi
fi

# Rule (d): the pinned toolchain versions and checksums may not move, and no
# law statement may be withdrawn. The env: block is also covered by rule (a)
# through .github/workflows/proofs.yml, and LAWS.bend through rule (a); the
# checks below name the specific change.
toolchain_env() {
	git show "$1:.github/workflows/proofs.yml" 2>/dev/null | awk '
		/^env:[[:space:]]*$/ { in_env = 1; next }
		in_env && /^[^[:space:]#]/ { exit }
		in_env { print }
	'
}

base_env=$(toolchain_env "$merge_base" || true)
head_env=$(toolchain_env "$head" || true)

if [ "$base_env" != "$head_env" ]; then
	fail d "the pinned toolchain env: block changed in .github/workflows/proofs.yml; a version or checksum bump needs its own merge"
fi

base_law_lines=$(git show "${merge_base}:LAWS.bend" 2>/dev/null | grep '^law ' || true)
head_law_lines=$(git show "${head}:LAWS.bend" 2>/dev/null | grep '^law ' || true)

while IFS= read -r line; do
	[ -n "$line" ] || continue
	if ! grep -Fxq -- "$line" <<<"$head_law_lines"; then
		fail d "LAWS.bend deletes the law statement '$line'; a law may not be withdrawn"
	fi
done <<<"$base_law_lines"

if [ "$status" -ne 0 ]; then
	printf 'protected-files: the pull request changes protected files or measurements; see docs/contributing.md\n' >&2
	exit 1
fi

printf 'protected-files: no protected file or measurement change\n'
