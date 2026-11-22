# Laws

The laws are the correctness statement for the solver. `LAWS.bend` states them;
`PROOF.bend` proves each one with a definition of the same name, so `law foo` is
proven by `def Laws.foo`. All eight laws are proved and `PENDING_LAWS` is empty.
The helper lemmas live under `proofs/`; [proofs.md](proofs.md) maps them. A law
with no proof would be an open claim, and `bend PROOF.bend` reports it.

## Types

- `Letter` is `Nat`.
- `Word` is `List<Nat>`.
- `Color` is `Gray`, `Yellow` or `Green`.
- `Feedback` is `List<Color>`.
- `Tree` is a node holding a guess and one `Child` per feedback pattern.
  A `Child` pairs a feedback with the subtree to use after it.

`src/feedback.bend` defines `Color`, the feedback function and `AllGreen`.
`src/tree.bend` defines `Tree`, `depth`, `Valid` and `cost`.
`src/solve.bend` delegates to the bound-pruned solver in `src/solve_fast.bend`,
while `src/solve_ref.bend` stays in the tree as the reference specification.
`src/json.bend` prints a tree as JSON and parses that text back, and
`src/spec_json.bend` is the independent renderer and recogniser used by laws 7
and 8.

## Feedback

`feedback(guess, answer)` is total on every pair of words, with no equal-length
precondition. Positions where the letters are equal are Green. Every other
position is Yellow when its guess letter still has an unconsumed occurrence
among the answer's non-green positions, consumed from left to right; otherwise
it is Gray. If the answer is shorter than the guess, the missing positions are
Gray. The length of the result is the length of the guess.

`AllGreen(fb)` is the proposition that every colour in `fb` is Green. In Bend:

```python
def AllGreen(fb: +List<Color>) -> Type:
  match fb:
    case Nil{}:
      Unit
    case Con{h, t}:
      {h == Green{} : Color} & AllGreen(t)
```

## 1. feedback_all_green_when_equal

Plain English: a word compared with itself produces Green in every position.
This pins down the Green half of the feedback definition.

```python
law feedback_all_green_when_equal:
  for +w: +List<Nat>
  Feedback.AllGreen(Feedback.feedback(w, w))
```

Proved in `PROOF.bend` by induction on the word. The helper
`Proof.all_green_go` carries an arbitrary pool and the proof that the current
equality decision is `True`.

## 2. feedback_all_green_only_if_equal

Plain English: if feedback is all Green and the two words have the same length,
the words are equal. This pins down the other direction: nothing except an
equal letter can produce Green, and a position past the end of the answer is
Gray.

```python
law feedback_all_green_only_if_equal:
  for +g: +List<Nat>
  for +a: +List<Nat>
  for p: Feedback.AllGreen(Feedback.feedback(g, a))
  for e: {List.length(&2, Nat, g) == List.length(&2, Nat, a) : Nat}
  {g == a : +List<Nat>}
```

Proved in `PROOF.bend`. The helper `FeedbackProof.all_green_equal_go` walks the
two words together, inverts the all-Green premise at each position, and uses
`Nat.is_eq_true` to turn the equality decision into a proof of letter equality.
The length premise excludes a proper prefix; the empty-versus-cons cases are
refuted from the length or from a Gray head.

## 3. feedback_length

Plain English: feedback has exactly one colour per guess letter, including when
the answer is shorter.

```python
law feedback_length:
  for +g: +List<Nat>
  for +a: +List<Nat>
  {List.length(&2, Feedback.Color, Feedback.feedback(g, a)) == List.length(&2, Nat, g) : Nat}
```

Proved in `PROOF.bend` by induction on the guess. The helper
`FeedbackProof.feedback_length_go` allows an arbitrary pool and equality
decision, because neither affects the number of colours emitted.

## 4. solve_valid

Plain English: if `solve` returns a tree, that tree is valid for the input.
Validity means two things. Every node's guess is a member of the guesses list,
and every candidate has a `Some` depth in the tree.

```python
law solve_valid:
  for G: +List<+List<Nat>>
  for C: +List<+List<Nat>>
  for T: Tree.Tree
  for e: {Solve.solve(G, C) == Some{T} : Maybe<Tree.Tree>}
  Tree.Valid(T, G, C)
```

Proved in `proofs/fast_opt.bend` (using `proofs/fast_valid.bend` and the
reference solver proofs in `proofs/mainvalid.bend`). For `|C| = 0`, `SolveFast`
agrees with `SolveRef` (`mainvalid.bend`). For `|C| = 1` and `|C| = 2`, the
direct root trees (`Node{w, []}`, `two_tree(w1, w2)`) are proved valid once the
root confirms all candidates belong to `G`. For `|C| >= 3`, fuel induction over
the staged guess queue maintains the boolean accumulator invariant
`FV.best_ok_b(limit, G, S, best)`: either the accumulator stayed at or above
`limit`, or its tree satisfies `FV.valid_b(tree, G, S)` with
`Tree.cost(tree, S) <= cost`. `OneItem` and `TwoItem` children satisfy this
directly, `ClassItem` children satisfy it by the fuel induction hypothesis, and
`FV.end_node_ok` reconstructs validity and the cost bound when `End` finishes a
guess. When `solve` returns `Some{T}`, the final cost is strictly below `inf`,
so `FV.best_ok_extract` and `FV.valid_of_b` yield `Tree.Valid(T, G, C)`. The
reference solver also remains proved valid in `PROOF.bend` (`Ref.solve_valid`).

## 5. solve_optimal

Plain English: for every valid tree for the same input, there is a tree returned
by `solve` whose total cost is no larger. Cost is the sum of the depth of every
candidate, with duplicates counted once per occurrence.

```python
law solve_optimal:
  for G: +List<+List<Nat>>
  for C: +List<+List<Nat>>
  for T2: Tree.Tree
  for v: Tree.Valid(T2, G, C)
  Exists(Tree.Tree, T =>
    {Solve.solve(G, C) == Some{T} : Maybe<Tree.Tree>}
    & {Nat.is_le(Tree.cost(T, C), Tree.cost(T2, C)) == True{} : Bool})
```

Proved in `proofs/fast_opt.bend` on top of the reference optimality proof in
`proofs/opt*.bend`. First, `proofs/optstrong.bend` proves that for any valid
tree `T2`, `SolveRef`'s stored cost is strictly below `inf` and at most
`Tree.cost(T2, C)` (`Ref.solve_optimal` in `PROOF.bend`). Second,
`proofs/fast_opt.bend` proves by fuel induction over the staged `GList` search
that `SolveFast` never worsens its cutoff accumulator, satisfies `FV.best_ok_b`
(so any tree with cost below `inf` has `Tree.cost(T, C) <= stored_cost`), and
achieves a stored cost at most `SolveRef`'s stored cost — even though
`SolveFast` tries candidate words `S` before `G`, resolves duplicate-free
two-word classes in O(1), raises the early-exit floor from `2*|S| - 1` to
`2*|S|` after `S`, and may pick a different tie-breaking optimal tree. Chaining
`Tree.cost(T, C) <= fast_cost <= ref_cost <= Tree.cost(T2, C)` establishes
optimality for every valid input.

## 6. tree_roundtrip

Plain English: printing a tree as JSON and parsing the text returns the same
tree.

```python
law tree_roundtrip:
  for t: Tree.Tree
  {Json.parse(Json.print(t)) == Some{t} : Maybe<Tree.Tree>}
```

Proved in `PROOF.bend`. The printer writes the tree as a right-nested JSON array
and the parser is a state machine over its characters. A letter's digits are
built least significant first by adding one (`digits_lsb`), printed most
significant first, and the parser pushes each digit back onto the accumulator,
so `Digits.value_digits` shows that the parsed value is the original number.
The proof is an induction on the tree: `KidsProof.body` proves that the body of
a kids array parses back to exactly the same children, and the digit and
feedback traces prove that each decimal letter and each colour is consumed
correctly. The top-level `TreeProof.parsed` chains those traces from `MStart`
and `Laws.tree_roundtrip` applies `finish`, which keeps the tree only when no
text remains.

## 7. tree_json_wellformed

Plain English: the text `Json.print` produces is a well-formed string in the
documented JSON subset.

```python
law tree_json_wellformed:
  for t: Tree.Tree
  {Spec.well_formed(Json.print(t)) == True{} : Bool}
```

Proved in `PROOF.bend` by `JsonProof.Rec.tree`. `src/spec_json.bend` defines
`Spec.well_formed`, an independent recogniser for the subset `array | number`
with no whitespace, no sign, no leading zero and no trailing text, and the law
shows that it accepts the printer's output. A roundtrip law cannot replace it:
a printer that emits invalid JSON could still parse back through a matching
parser.

The recogniser lemmas in `proofs/json_spec.bend` cover the decimal letters
(through `Digits.show_letter` and the canonical `digits_lsb` lists), the guess
arrays, the feedback arrays, and the kids arrays. `Rec.kids_run` walks a kids
body with a mode for the first child and for a child after a comma, pushes and
pops one stack entry per open array, and `Rec.child_core` reads one child's
feedback, guess and nested kids. `Rec.tree` then reads the whole tree from
`SValue`, and `Laws.tree_json_wellformed` instantiates it at the empty stack and
empty suffix.

## 8. print_matches_render

Plain English: the printer and the reference renderer `Spec.render` agree byte
for byte on every tree.

```python
law print_matches_render:
  for t: Tree.Tree
  {Json.print(t) == Spec.render(t) : String}
```

Proved in `PROOF.bend` by `JsonProof.RenderProof.print`, an induction on the
tree with an inner induction over the kids list. `Spec.render` is the plain
concatenation of the documented format. It writes letters with `Spec.decimal`,
an independent quotient-and-remainder numeral defined in `src/spec_json.bend`,
so the law does not depend on Base's `Nat.show`. The digit-level equality is
`Dig.show_letter`: the printer's least-significant-first digit list, printed
most significant first, is the same numeral as `Spec.decimal`. The law
therefore rules out a printer that emits letters in unary or in any other
parseable form, which a roundtrip law cannot see.

