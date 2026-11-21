#!/bin/sh
# The proof gate. Every law in LAWS.bend must have a matching
# def Laws.<name> in PROOF.bend, except the laws listed in PENDING_LAWS.
#
# CI runs this script, and contributors run the same script locally. See
# docs/testing.md for the rules.
#
# Exit 0: all laws are proved, or the only open laws are the pending ones and
#         bend reports nothing except the expected TODOs.

set -eu

CDPATH=
root=$(cd -- "$(dirname -- "$0")/.." && pwd)
cd "$root"

die() {
	printf 'check-proofs: %s\n' "$*" >&2
	exit 1
}

note() {
	printf 'check-proofs: %s\n' "$*"
}

for file in LAWS.bend PROOF.bend PENDING_LAWS; do
	[ -f "$file" ] || die "$file is missing"
done

tmp=$(mktemp -d) || die "cannot create a temporary directory"
trap 'rm -rf "$tmp"' EXIT HUP INT TERM

laws=$tmp/laws
proven=$tmp/proven
pending=$tmp/pending

sed -n 's/^law \([A-Za-z_][A-Za-z0-9_]*\):$/\1/p' LAWS.bend | sort >"$laws"
sed -n 's/^def Laws\.\([A-Za-z_][A-Za-z0-9_]*\)(.*/\1/p' PROOF.bend | sort -u >"$proven"
sed -e 's/#.*//' -e 's/^[[:space:]]*//' -e 's/[[:space:]]*$//' -e '/^$/d' PENDING_LAWS >"$pending.new"
mv "$pending.new" "$pending"

[ -s "$laws" ] || die "no 'law <name>:' lines found in LAWS.bend"

has_law() { grep -Fxq -- "$1" "$laws"; }
has_proof() { grep -Fxq -- "$1" "$proven"; }
has_pending() { grep -Fxq -- "$1" "$pending"; }

pending_count=0
duplicates=$(sort "$pending" | uniq -d)
[ -z "$duplicates" ] || die "PENDING_LAWS lists '$duplicates' more than once"

while IFS= read -r name; do
	case $name in
	*[!A-Za-z0-9_]*)
		die "PENDING_LAWS has an invalid law name: '$name'"
		;;
	esac

	pending_count=$((pending_count + 1))

	has_law "$name" ||
		die "PENDING_LAWS names '$name', which is not a law in LAWS.bend"

	has_proof "$name" &&
		die "'$name' already has a proof def in PROOF.bend; remove it from PENDING_LAWS"
done <"$pending"

law_count=0
proven_count=0
while IFS= read -r name; do
	law_count=$((law_count + 1))

	if has_proof "$name"; then
		proven_count=$((proven_count + 1))
	elif ! has_pending "$name"; then
		die "law '$name' has no proof def in PROOF.bend and is not listed in PENDING_LAWS"
	fi
done <"$laws"

if bend_output=$(bend PROOF.bend 2>&1); then
	bend_status=0
else
	bend_status=$?
fi

if [ "$pending_count" -eq 0 ]; then
	[ "$bend_status" -eq 0 ] || {
		printf '%s\n' "$bend_output" >&2
		die "bend PROOF.bend exited $bend_status, but PENDING_LAWS is empty and every law has a proof"
	}

	case $bend_output in
	*"ALL PROOFS CHECK"*) ;;
	*)
		printf '%s\n' "$bend_output" >&2
		die "bend PROOF.bend exited 0 without printing ALL PROOFS CHECK"
		;;
	esac

	if verdict_output=$(bend PROOF.bend --verdict 2>&1); then
		verdict_status=0
	else
		verdict_status=$?
	fi

	[ "$verdict_status" -eq 0 ] || {
		printf '%s\n' "$verdict_output" >&2
		die "bend PROOF.bend --verdict exited $verdict_status"
	}

	case $verdict_output in
	*"ALL PROOFS CHECK"*) ;;
	*)
		printf '%s\n' "$verdict_output" >&2
		die "bend PROOF.bend --verdict exited 0 without printing ALL PROOFS CHECK"
		;;
	esac
else
	[ "$bend_status" -eq 1 ] || {
		printf '%s\n' "$bend_output" >&2
		die "bend PROOF.bend exited $bend_status; expected 1 while $pending_count law(s) are pending"
	}

	case $bend_output in
	*"SOME PROOFS FAIL"*) ;;
	*)
		printf '%s\n' "$bend_output" >&2
		die "bend PROOF.bend did not print SOME PROOFS FAIL"
		;;
	esac

	if [ "$pending_count" -eq 1 ]; then
		todo_line="Error: 1 TODO found."
	else
		todo_line="Error: $pending_count TODOs found."
	fi
	todo_count=$(printf '%s\n' "$bend_output" | grep -Fxc -- "$todo_line" || true)
	[ "$todo_count" -eq 1 ] || {
		printf '%s\n' "$bend_output" >&2
		die "expected exactly one '$todo_line' line in the bend output, found $todo_count"
	}

	other_errors=$(printf '%s\n' "$bend_output" | grep -E '^Error' | grep -Fxv -- "$todo_line" || true)
	[ -z "$other_errors" ] || {
		printf '%s\n' "$bend_output" >&2
		die "unexpected error output besides '$todo_line': $other_errors"
	}

	note "$pending_count law(s) are pending in PENDING_LAWS:"
	sed 's/^/  /' "$pending"
	note "--verdict was skipped because laws are open; it runs once PENDING_LAWS is empty"
fi

note "$proven_count of $law_count law(s) proved, $pending_count pending"
