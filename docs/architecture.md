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

### `src/solve.bend`

The placeholder solver. It returns `None`; Phase 4 replaces it with the search over guesses and
candidates.

### `src/json.bend`

Prints a tree as a JSON array. The encoding is:

```text
tree     = [ guess, kids ]
guess    = [ letter, ... ]
kids     = [ child, ... ]
child    = [ feedback, tree ]
feedback = [ colour, ... ]
```

A colour is `0` (Gray), `1` (Yellow) or `2` (Green). The parser is a rejecting stub; law 6 is open.

### `LAWS.bend` and `PROOF.bend`

`LAWS.bend` states the six claims. `PROOF.bend` proves laws 1 to 3 and leaves 4 to 6 open. Each
proof is a definition named after the law, `def Laws.<law>`. See [laws.md](laws.md).

### `src/main.bend`

The command-line entry point:

```sh
bend src/main.bend --guesses words/guesses.txt --candidates words/candidates.txt
```

It reads both files (one word per line), maps letters to `Nat` by code point with lower-case ASCII
folded to upper case, calls `solve`, prints the JSON tree on stdout, or a clear error on stderr when
`solve` returns `None`. No other flags are accepted.

## Data flow

```text
guesses file, candidates file
          │
          ▼
     src/main.bend  ──►  src/solve.bend
          │                    │
          │                    ▼
          │             Tree (Maybe)
          │                    │
          ▼                    ▼
   error on stderr       src/json.bend ──► JSON on stdout

LAWS.bend ── checked by PROOF.bend ──► validity and optimality claims
```

## Current limits

- `solve` is a placeholder, so laws 4 and 5 are open.
- The JSON parser is not implemented, so law 6 is open.
- `depth` is total and structurally recursive, but the validity and optimality proofs are still to
  be written.
- There is no benchmark harness yet.
