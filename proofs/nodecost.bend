# The cost of a node splits into one guess per candidate plus the children.
#
# `Tree.depth` at a node is one plus the depth of the looked-up child, so the
# cost of `Node(g, kids)` over a candidate list is the number of candidates
# plus the sum of the children's depths, one per non-guess candidate. This is
# the pointwise half of the cost decomposition the optimality proof needs.
import Base
import ../src/tree.bend as Tree
import ../src/feedback.bend as Feedback
import ./logic.bend as Logic
import ./nat.bend as NatProof
import ./feedback.bend as FbProof
import ./depth.bend as DepthProof

# `bump` keeps whether a depth exists.
def NodeCost.is_some_bump(m: Maybe<Nat>) ->
  {Maybe.is_some(&1, Nat, Tree.depth.bump(m)) == Maybe.is_some(&1, Nat, m) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{n}:
      {==}

# A `Some` depth is the successor of its default.
def NodeCost.bump_default(m: Maybe<Nat>,
    s: {Maybe.is_some(&1, Nat, m) == True{} : Bool}) ->
  {Tree.depth.bump(m) == Some{(1n + Maybe.default(&1, Nat, m, 0n) : Nat)} : Maybe<Nat>}:
  match m:
    case None{}:
      Empty.absurd(
        {Tree.depth.bump(None{}) == Some{(1n + Maybe.default(&1, Nat, None{}, 0n) : Nat)} : Maybe<Nat>},
        Logic.Proof.false_ne_true(s))
    case Some{n}:
      {==}

# If a looked-up depth exists then the lookup found a tree.
def NodeCost.some_of_lookup_depth(m: Maybe<Tree.Tree>, +a: +List<Nat>,
    s: {Maybe.is_some(&1, Nat, DepthProof.DepthProof.lookup_depth(m, a)) == True{} : Bool}) ->
  {Maybe.is_some(&1, Tree.Tree, m) == True{} : Bool}:
  match m:
    case None{}:
      Empty.absurd({Maybe.is_some(&1, Tree.Tree, None{}) == True{} : Bool},
                   Logic.Proof.false_ne_true(s))
    case Some{t}:
      {==}

# The depth contribution of a looked-up child, or zero when there is none.
def NodeCost.maybe_depth(m: Maybe<Tree.Tree>, +a: +List<Nat>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{t}:
      Maybe.default(&1, Nat, Tree.depth(t, a), 0n)

def NodeCost.kid_depth(+kids: +List<Tree.Child>, +fb: +List<Feedback.Color>,
    +a: +List<Nat>) -> Nat:
  NodeCost.maybe_depth(Tree.lookup(fb, kids), a)

# `step` is exactly the depth of its child.
def NodeCost.step_is_depth(t: Tree.Tree, +a: +List<Nat>) ->
  {DepthProof.DepthProof.step(t, a) == Tree.depth(t, a) : Maybe<Nat>}:
  match t:
    case Tree.Node{+g, kids}:
      {==}

# A `Maybe` that is `Some` is the `Some` of its value.
def MaybePrf.some_of_is_some(-A: Type, m: Maybe<A>,
    s: {Maybe.is_some(&1, A, m) == True{} : Bool}) ->
  &x: A -> {m == Some{x} : Maybe<A>}:
  match m:
    case None{}:
      Empty.absurd(&x: A -> {None{} == Some{x} : Maybe<A>},
                   Logic.Proof.false_ne_true(s))
    case Some{x}:
      (x, {==})
