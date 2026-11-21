# Laws

The laws are the correctness statement for the solver. `LAWS.bend` states them;
`PROOF.bend` proves each one with a definition of the same name, so `law foo` is
proven by `def Laws.foo`. A law with no proof is an open claim, and
`bend PROOF.bend` reports it.

## Types

- `Letter` is `Nat`.
- `Word` is `List<Nat>`.
- `Color` is `Gray`, `Yellow` or `Green`.
- `Feedback` is `List<Color>`.
- `Tree` is a node holding a guess and one `Child` per feedback pattern.
  A `Child` pairs a feedback with the subtree to use after it.

`src/feedback.bend` defines `Color`, the feedback function and `AllGreen`.
`src/tree.bend` defines `Tree`, `depth`, `Valid` and `cost`.
`src/solve.bend` holds the placeholder solver. `src/json.bend` prints a tree as
JSON and parses that text back.

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

Open. The placeholder solver always returns `None`, so the premise is never
inhabited in a run, but the law is not proved.

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

Open. It becomes provable when the search replaces the placeholder.

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
