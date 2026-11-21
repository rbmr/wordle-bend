# The laws of the solver. Each is an open claim proven in PROOF.bend by a def
# of the same name. The spec is the source of truth; do not weaken a law to
# make it prove.
import Base
import ./src/feedback.bend as Feedback
import ./src/tree.bend as Tree
import ./src/solve.bend as Solve
import ./src/json.bend as Json
import ./src/spec_json.bend as Spec

# 1. A word against itself is all Green.
law feedback_all_green_when_equal:
  for +w: +List<Nat>
  Feedback.AllGreen(Feedback.feedback(w, w))

# 2. All-Green feedback on equal-length words means the words are equal.
law feedback_all_green_only_if_equal:
  for +g: +List<Nat>
  for +a: +List<Nat>
  for p: Feedback.AllGreen(Feedback.feedback(g, a))
  for e: {List.length(&2, Nat, g) == List.length(&2, Nat, a) : Nat}
  {g == a : +List<Nat>}

# 3. Feedback has exactly one colour per guess letter.
law feedback_length:
  for +g: +List<Nat>
  for +a: +List<Nat>
  {List.length(&2, Feedback.Color, Feedback.feedback(g, a)) == List.length(&2, Nat, g) : Nat}

# 4. A tree returned by solve is valid for its input.
law solve_valid:
  for G: +List<+List<Nat>>
  for C: +List<+List<Nat>>
  for T: Tree.Tree
  for e: {Solve.solve(G, C) == Some{T} : Maybe<Tree.Tree>}
  Tree.Valid(T, G, C)

# 5. A tree returned by solve is optimal for its input.
law solve_optimal:
  for G: +List<+List<Nat>>
  for C: +List<+List<Nat>>
  for T2: Tree.Tree
  for v: Tree.Valid(T2, G, C)
  Exists(Tree.Tree, T =>
    {Solve.solve(G, C) == Some{T} : Maybe<Tree.Tree>}
    & {Nat.is_le(Tree.cost(T, C), Tree.cost(T2, C)) == True{} : Bool})

# 6. Printing a tree and parsing the text gives the tree back.
law tree_roundtrip:
  for t: Tree.Tree
  {Json.parse(Json.print(t)) == Some{t} : Maybe<Tree.Tree>}

# 7. The printed text is well-formed JSON for the documented subset.
law tree_json_wellformed:
  for t: Tree.Tree
  {Spec.well_formed(Json.print(t)) == True{} : Bool}

# 8. The printer agrees with the reference renderer, byte for byte.
law print_matches_render:
  for t: Tree.Tree
  {Json.print(t) == Spec.render(t) : String}

# guard smoke test, not for merging
