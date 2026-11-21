# Lower bounds for valid trees, part 1: every candidate costs at least one.
#
# `Tree.cost(T, S)` sums the depth of every candidate (duplicates counted once
# per occurrence), and a candidate's depth is `None` when the tree does not
# reach it. Lemma `LB.cost_ge_size` says that on a tree where every candidate
# has a depth, the cost is at least the number of candidates:
#
#   cost(T, S) >= |S|            when AllHaveDepth(T, S)
#
# The proof needs one structural fact: every depth the tree produces is either
# absent or at least one, so a present depth contributes at least one to the
# cost. That fact is `LB.depth_positive`. `LB.valid_cost_ge_size` is the same
# statement for `Tree.Valid`, which is how the pruning proof states it.
import Base
import ../src/tree.bend as Tree
import ../src/feedback.bend as Feedback
import ./logic.bend as Logic
import ./nat.bend as NatProof

# A `Maybe Nat` that is either absent or a number at least one.
def LB.Positive(m: Maybe<Nat>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{n}:
      {Nat.is_le(1n, n) == True{} : Bool}

# A bump keeps a `Maybe Nat` positive.
def LB.bump_positive(m: Maybe<Nat>, p: LB.Positive(m)) -> LB.Positive(Tree.depth.bump(m)):
  match m:
    case None{}:
      Unit{}
    case Some{+n}:
      NatProof.Nat.is_le_succ(0n, n, NatProof.Nat.is_le_zero_l(n))

# The depth of a node with the equality decision as a parameter. The decision is
# a parameter because a computed `Bool` cannot be matched in a proof; the real
# `Tree.depth` is this function at `Feedback.word_eq(g, w)`.
def LB.node_depth(+g: +List<Nat>, +kids: +List<Tree.Child>, +w: +List<Nat>,
    b: Bool) -> Maybe<Nat>:
  Feedback.Bool.case(Maybe<Nat>, b, Some{1n},
    Tree.depth.bump(Tree.depth.go(kids, Feedback.feedback(g, w), w)))

# The positive node depth, given the positive depth of the scanned child list.
def LB.node_depth_positive(+g: +List<Nat>, +kids: +List<Tree.Child>,
    +w: +List<Nat>, b: Bool,
    p: LB.Positive(Tree.depth.go(kids, Feedback.feedback(g, w), w))) ->
  LB.Positive(LB.node_depth(g, kids, w, b)):
  match b:
    case True{}:
      {==}
    case False{}:
      LB.bump_positive(Tree.depth.go(kids, Feedback.feedback(g, w), w), p)

# One step of the child scan with both equality decisions as parameters.
def LB.go_step(+kids: +List<Tree.Child>, +fb: +List<Feedback.Color>,
    +a: +List<Nat>, +ckids: +List<Tree.Child>, +g: +List<Nat>,
    +rest: +List<Tree.Child>, bfb: Bool, bw: Bool) -> Maybe<Nat>:
  Feedback.Bool.case(Maybe<Nat>, bfb,
    Feedback.Bool.case(Maybe<Nat>, bw, Some{1n},
      Tree.depth.bump(Tree.depth.go(ckids, Feedback.feedback(g, a), a))),
    Tree.depth.go(rest, fb, a))

# The positive step, given the positive results of both recursive scans.
def LB.go_step_positive(+kids: +List<Tree.Child>, +fb: +List<Feedback.Color>,
    +a: +List<Nat>, +ckids: +List<Tree.Child>, +g: +List<Nat>,
    +rest: +List<Tree.Child>, bfb: Bool, bw: Bool,
    p1: LB.Positive(Tree.depth.go(ckids, Feedback.feedback(g, a), a)),
    p2: LB.Positive(Tree.depth.go(rest, fb, a))) ->
  LB.Positive(LB.go_step(kids, fb, a, ckids, g, rest, bfb, bw)):
  match bfb:
    case True{}:
      match bw:
        case True{}:
          {==}
        case False{}:
          LB.bump_positive(Tree.depth.go(ckids, Feedback.feedback(g, a), a), p1)
    case False{}:
      p2

# Every depth the child scan produces is positive.
def LB.go_positive(+kids: +List<Tree.Child>, +fb: +List<Feedback.Color>,
    +a: +List<Nat>) -> LB.Positive(Tree.depth.go(kids, fb, a)):
  match kids:
    case Nil{}:
      Unit{}
    case Con{c, rest}:
      match c:
        case Tree.Child{f, child}:
          match child:
            case Tree.Node{g, ckids}:
              LB.go_step_positive(c <> rest, fb, a, ckids, g, rest,
                Feedback.feedback_eq(f, fb), Feedback.word_eq(g, a),
                LB.go_positive(ckids, Feedback.feedback(g, a), a),
                LB.go_positive(rest, fb, a))

# Every depth the tree produces is positive.
def LB.depth_positive(t: Tree.Tree, +w: +List<Nat>) -> LB.Positive(Tree.depth(t, w)):
  match t:
    case Tree.Node{+g, +kids}:
      LB.node_depth_positive(g, kids, w, Feedback.word_eq(g, w),
        LB.go_positive(kids, Feedback.feedback(g, w), w))

# A present depth is at least one, so its default is at least one.
def LB.default_ge_one(m: Maybe<Nat>, p: LB.Positive(m),
    s: {Maybe.is_some(&1, Nat, m) == True{} : Bool}) ->
  {Nat.is_le(1n, Maybe.default(&1, Nat, m, 0n)) == True{} : Bool}:
  match m:
    case None{}:
      Empty.absurd({Nat.is_le(1n, Maybe.default(&1, Nat, None{}, 0n)) == True{} : Bool},
                   Logic.Proof.false_ne_true(s))
    case Some{n}:
      p

# Every candidate of a tree that reaches it costs at least one.
def LB.cost_ge_size(+t: Tree.Tree, +S: +List<+List<Nat>>,
    v: Tree.AllHaveDepth(t, S)) ->
  {Nat.is_le(List.length(&2, +List<Nat>, S), Tree.cost(t, S)) == True{} : Bool}:
  match S:
    case Nil{}:
      NatProof.Nat.is_le_zero_l(Tree.cost(t, Nil{}))
    case Con{h, tail}:
      (sh, st) = v
      +ih : {Nat.is_le(List.length(&2, +List<Nat>, tail), Tree.cost(t, tail)) == True{} : Bool} =
        LB.cost_ge_size(t, tail, st)
      +p : {Nat.is_le(1n, Maybe.default(&1, Nat, Tree.depth(t, h), 0n)) == True{} : Bool} =
        LB.default_ge_one(Tree.depth(t, h), LB.depth_positive(t, h), sh)
      +e1 : {Nat.is_le(Nat.add(1n, List.length(&2, +List<Nat>, tail)),
                      Nat.add(1n, Tree.cost(t, tail))) == True{} : Bool} =
        NatProof.Nat.is_le_succ(List.length(&2, +List<Nat>, tail), Tree.cost(t, tail), ih)
      +e2 : {Nat.is_le(Nat.add(1n, Tree.cost(t, tail)),
                      Nat.add(Maybe.default(&1, Nat, Tree.depth(t, h), 0n),
                              Tree.cost(t, tail))) == True{} : Bool} =
        NatProof.Nat.is_le_add_r(1n, Maybe.default(&1, Nat, Tree.depth(t, h), 0n),
                                 Tree.cost(t, tail), p)
      NatProof.Nat.is_le_trans(Nat.add(1n, List.length(&2, +List<Nat>, tail)),
        Nat.add(1n, Tree.cost(t, tail)),
        Nat.add(Maybe.default(&1, Nat, Tree.depth(t, h), 0n), Tree.cost(t, tail)),
        e1, e2)

# The lower bound for a valid tree: its cost is at least the candidate count.
def LB.valid_cost_ge_size(+t: Tree.Tree, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    v: Tree.Valid(t, G, S)) ->
  {Nat.is_le(List.length(&2, +List<Nat>, S), Tree.cost(t, S)) == True{} : Bool}:
  (vi, vd) = v
  LB.cost_ge_size(t, S, vd)
