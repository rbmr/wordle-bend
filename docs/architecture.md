# Architecture

## Shape of the problem

The solver takes two lists of words:

- the **guesses list**: the words that may be played as a guess;
- the **candidates list**: the words that may be the answer.

Words are arbitrary over some alphabet. A letter is a `Nat` (its code point), a word is a
`List<Nat>`, and all words in a run have the same length. Each guess against a candidate produces a
`Feedback`: one `Color` per guess letter, either Gray, Yellow or Green. A strategy is a decision
tree: each node is a guess, and each child edge carries a feedback pattern toward the next node.

The objective is to minimise the total number of guesses over all candidates. This is a sum over
candidates, not a worst case, so the optimal tree can favour a guess that resolves many likely
candidates quickly over one that shortens the worst branch.

## Components

### `words/`

The bundled candidates and guesses lists. Their provenance is recorded in
[licenses.md](licenses.md). The CLI reads paths given on the command line, so other lists can be
used without changing the code.

### `src/feedback.bend`

`Color` is `Gray`, `Yellow` or `Green`. `feedback(guess, answer)` is total on every pair of words.
It marks equal positions Green, then scans the remaining positions left to right. A non-green
position is Yellow when the guess letter still has an unconsumed occurrence among the answer's
non-green positions, and Gray otherwise. A position past the end of the answer is Gray. The result
always has one colour per guess letter.

The module also provides `word_eq`, `feedback_eq`, `non_green` and the `AllGreen` predicate used by
the laws.

### `src/tree.bend`

`Tree` is a node holding a guess and a list of `Child` values. A `Child` pairs a feedback with a
subtree. `lookup` finds the child for a feedback. `depth` follows the tree for a candidate and
returns `Maybe<Nat>`, or `None` when a feedback has no child. `cost` sums the depths over the
candidate list, counting duplicates. `Valid` is a type-level proposition: every guess in the tree is
in the guesses list, and every candidate has a `Some` depth.

The depth walk searches the child list directly, with the list as the recursion argument, so Bend's
structural termination check accepts it without `@unsafe`.

### `src/groups.bend`

`groups_build(guess, candidates)` partitions a candidate list into feedback classes, one per
distinct feedback pattern. A `Group` holds the pattern and its candidates in input order. The
candidate equal to the guess is not put in a class: it ends at the node that guessed it. The
first occurrence of a pattern fixes the child order.

`groups_smaller` checks that every class is strictly shorter than the candidate list. A guess that
fails the check does not make progress on some class, so the solver skips it. This is also the fact
that lets each child search use less fuel.

### `src/solve_ref.bend`

The exact reference solver. For a candidate list `S` and a guess `g`, the tree is
`Node(g, kids)`: candidates equal to `g` end at the node with depth one, and every other candidate
is partitioned by feedback into one child per class. A guess is used only when every class is
strictly smaller than `S`. Among the usable guesses the solver keeps the cheapest tree, and ties go
to the guess that appears first in the guesses list.

The empty candidate list produces `Node(g0, [])` for the first guess `g0`, at cost zero, or `None`
when the guess list is empty. A cost of infinity marks a class with no valid tree, and a guess whose
classes sum to infinity is unusable.

The implementation is deliberately simple rather than fast. The recursion is fused into one
definition, `step`, driven by a flat schedule of `Begin`, `ClassItem`, `Add` and `End` items. `step`
shrinks the schedule on every step and descends into a class's own search with one less fuel, which
is why the initial fuel, the candidate count, is enough. The result is exponential in the candidate
count and is intended as the correctness reference, not the final fast path. See
[performance.md](performance.md).

### `src/solve.bend`

The entry point the laws talk about. It delegates to the reference solver in `src/solve_ref.bend`.

### `src/json.bend`

Prints a tree as a JSON array. The encoding is:

```text
tree     = [ guess, kids ]
guess    = [ letter, ... ]
kids     = [ child, ... ]
child    = [ feedback, tree ]
feedback = [ colour, ... ]
```

A colour is `0` (Gray), `1` (Yellow) or `2` (Green). A letter is its decimal code point, printed
as an ordinary decimal numeral: `97` for `a`, `0` for code point zero, and no leading zeros.
`Json.parse` reads each run of digits back to its value and accepts exactly this grammar,
rejecting anything else, including trailing text.

### `src/spec_json.bend`

An independent specification of the same text: `render` is a direct translation of the documented
format, and `well_formed` is a recogniser for the JSON subset it uses. It shares no helper with the
printer, so laws 7 and 8 compare two implementations rather than one implementation with itself.

### `LAWS.bend`, `PROOF.bend` and `proofs/`

`LAWS.bend` states the eight claims. All eight are proved: `PROOF.bend` defines
`def Laws.<name>` for each law and imports the helper lemmas in `proofs/`. `PENDING_LAWS` is empty.
See [laws.md](laws.md) for each proof strategy and [proofs.md](proofs.md) for a map of the proof
modules.

### `src/main.bend`

The command-line entry point:

```sh
bend src/main.bend -o wordle-bend
./wordle-bend --guesses words/guesses.txt --candidates words/candidates.txt
```

It reads the two files named by `--guesses` and `--candidates`, maps letters to `Nat` by code
point, calls `solve`, and prints the JSON tree on stdout. The whole of each file is read, in
chunks, so a list is never truncated. Leading and trailing whitespace on a line is ignored, which
handles CRLF files and blank lines, and letters are left exactly as they are, so any alphabet
works. `--help` prints the usage. Every error, including a missing or unknown flag, an unreadable
file, an empty list and a `None` from `solve`, prints one line on stderr and exits non-zero. See
[cli.md](cli.md) for the full command-line contract.

### `bench/`

The benchmark harness. It builds the CLI once, samples fixed subsets of the bundled candidate list
with a deterministic PRNG, runs each input several times, and appends rows to
`bench/results.csv`. See [benchmarking.md](benchmarking.md) for the protocol and
[performance.md](performance.md) for the current baseline.

### `scripts/check-proofs.sh`

The proof gate. It checks that every law has a proof, except laws named in `PENDING_LAWS`, and then
runs Bend's checker and, when the pending list is empty, the Lean kernel recheck. CI runs the same
script. See [proofs.md](proofs.md) and [testing.md](testing.md).

## Data flow

```text
guesses file, candidates file
          │
          ▼
     src/main.bend  ──►  src/solve.bend  ──►  src/solve_ref.bend
          │                                        │
          │                                        ▼
          │                                 Tree (Maybe)
          │                                        │
          ▼                                        ▼
   error on stderr                      src/json.bend ──► JSON on stdout

LAWS.bend ── checked by PROOF.bend and proofs/ ──► validity and optimality claims
```

## Current limits

- `solve` is exact but exhaustive. The search is exponential and takes a few seconds at 10
  candidates, so the full bundled lists are not practical yet. Planned work and the rule that every
  optimisation must keep the laws proved are in [performance.md](performance.md).
- All eight laws are proved, including validity and optimality for every input. There are no open
  laws in `PENDING_LAWS`.
