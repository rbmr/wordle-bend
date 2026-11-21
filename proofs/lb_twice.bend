# Lower bounds for valid trees, part 2: only the root guess can end a candidate.
#
# A candidate ends at depth one exactly when it equals the guess of the node it
# reaches. Every other candidate is at depth at least two, because `depth`
# bumps the child's depth by one. So for a node with guess `g` and candidate
# list `S`, with `mult(g, S)` the number of candidates equal to `g`,
#
#   cost(T, S) >= |S| + (|S| - mult(g, S))
#
# which `LB.cost_plus_mult` states without subtraction as
#
#   2 * |S| <= cost(T, S) + mult(g, S).
#
# With duplicates this is the sharp statement: if every candidate equals the
# root guess, every candidate is at depth one and the cost is `|S|`, while
# `2|S| - 1` would be false. When no candidate repeats, `mult(g, S)` is at most
# one, and the classical `cost(T, S) >= 2|S| - 1` follows; `LB.maxMult` gives
# the same bound with the largest multiplicity of the list, which covers a list
# with duplicates of several words.
import Base
import ../src/tree.bend as Tree
import ../src/feedback.bend as Feedback
import ./logic.bend as Logic
import ./nat.bend as NatProof
import ./feedback.bend as FbProof
import ./classbound_nat.bend as CB
import ./cover_list.bend as CoverList
import ./lb_size.bend as SizeProof

# One when the candidate equals the guess, zero otherwise.
def LB.hit_bool(b: Bool) -> Nat:
  Feedback.Bool.case(Nat, b, 1n, 0n)

def LB.hit(+g: +List<Nat>, +w: +List<Nat>) -> Nat:
  LB.hit_bool(Feedback.word_eq(g, w))

# The number of candidates equal to `g`, duplicates counted.
def LB.mult(+g: +List<Nat>, +S: +List<+List<Nat>>) -> Nat:
  match S:
    case Nil{}:
      0n
    case Con{h, t}:
      Nat.add(LB.hit(g, h), LB.mult(g, t))

# The largest multiplicity any candidate of the list has.
def LB.maxMult(+S: +List<+List<Nat>>) -> Nat:
  match S:
    case Nil{}:
      0n
    case Con{h, t}:
      Nat.max(LB.mult(h, S), LB.maxMult(t))

# A bump keeps whether a depth exists.
def LB.is_some_bump(m: Maybe<Nat>) ->
  {Maybe.is_some(&1, Nat, Tree.depth.bump(m)) == Maybe.is_some(&1, Nat, m) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{n}:
      {==}

# A bump adds one to the default, when the argument exists.
def LB.default_bump(m: Maybe<Nat>,
    s: {Maybe.is_some(&1, Nat, Tree.depth.bump(m)) == True{} : Bool}) ->
  {Maybe.default(&1, Nat, Tree.depth.bump(m), 0n)
   == Nat.add(1n, Maybe.default(&1, Nat, m, 0n)) : Nat}:
  match m:
    case None{}:
      Empty.absurd(
        {Maybe.default(&1, Nat, Tree.depth.bump(None{}), 0n)
         == Nat.add(1n, Maybe.default(&1, Nat, None{}, 0n)) : Nat},
        Logic.Proof.false_ne_true(s))
    case Some{n}:
      {==}

# The node's depth with the equality decision as a parameter.
def LB.node_default(+g: +List<Nat>, +kids: +List<Tree.Child>, +w: +List<Nat>,
    b: Bool) -> Nat:
  Maybe.default(&1, Nat, SizeProof.LB.node_depth(g, kids, w, b), 0n)

# One candidate contributes at least two to the cost plus the root guess's
# multiplicity: one for its depth and one when it is the root guess.
def LB.node_pair_ge_two(+g: +List<Nat>, +kids: +List<Tree.Child>, +w: +List<Nat>,
    b: Bool,
    p: SizeProof.LB.Positive(Tree.depth.go(kids, Feedback.feedback(g, w), w)),
    s: {Maybe.is_some(&1, Nat, SizeProof.LB.node_depth(g, kids, w, b)) == True{} : Bool}) ->
  {Nat.is_le(2n, Nat.add(LB.node_default(g, kids, w, b), LB.hit_bool(b))) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      +sc : {Maybe.is_some(&1, Nat, SizeProof.LB.node_depth(g, kids, w, False{})) == True{} : Bool} = s
      +eb : {Maybe.is_some(&1, Nat,
                 Tree.depth.bump(Tree.depth.go(kids, Feedback.feedback(g, w), w)))
             == Maybe.is_some(&1, Nat,
                  Tree.depth.go(kids, Feedback.feedback(g, w), w)) : Bool} =
        LB.is_some_bump(Tree.depth.go(kids, Feedback.feedback(g, w), w))
      +sg : {Maybe.is_some(&1, Nat,
                 Tree.depth.go(kids, Feedback.feedback(g, w), w)) == True{} : Bool} =
        Equal.trans(Bool,
          Maybe.is_some(&1, Nat, Tree.depth.go(kids, Feedback.feedback(g, w), w)),
          Maybe.is_some(&1, Nat, Tree.depth.bump(Tree.depth.go(kids, Feedback.feedback(g, w), w))),
          True{}, Equal.sym(Bool,
            Maybe.is_some(&1, Nat, Tree.depth.bump(Tree.depth.go(kids, Feedback.feedback(g, w), w))),
            Maybe.is_some(&1, Nat, Tree.depth.go(kids, Feedback.feedback(g, w), w)), eb), sc)
      +dg : {Nat.is_le(1n,
                 Maybe.default(&1, Nat,
                   Tree.depth.go(kids, Feedback.feedback(g, w), w), 0n)) == True{} : Bool} =
        SizeProof.LB.default_ge_one(Tree.depth.go(kids, Feedback.feedback(g, w), w), p, sg)
      +h : {Nat.is_le(2n,
                 Nat.add(1n, Maybe.default(&1, Nat,
                   Tree.depth.go(kids, Feedback.feedback(g, w), w), 0n))) == True{} : Bool} =
        NatProof.Nat.is_le_succ(1n,
          Maybe.default(&1, Nat, Tree.depth.go(kids, Feedback.feedback(g, w), w), 0n), dg)
      +db : {Maybe.default(&1, Nat,
                 Tree.depth.bump(Tree.depth.go(kids, Feedback.feedback(g, w), w)), 0n)
             == Nat.add(1n, Maybe.default(&1, Nat,
                  Tree.depth.go(kids, Feedback.feedback(g, w), w), 0n)) : Nat} =
        LB.default_bump(Tree.depth.go(kids, Feedback.feedback(g, w), w), sc)
      +e1 : {Nat.is_le(2n,
                 Nat.add(Maybe.default(&1, Nat,
                   Tree.depth.bump(Tree.depth.go(kids, Feedback.feedback(g, w), w)), 0n), 0n))
             == True{} : Bool} =
        NatProof.Nat.is_le_eq_r(2n,
          Nat.add(1n, Maybe.default(&1, Nat, Tree.depth.go(kids, Feedback.feedback(g, w), w), 0n)),
          Nat.add(Maybe.default(&1, Nat,
            Tree.depth.bump(Tree.depth.go(kids, Feedback.feedback(g, w), w)), 0n), 0n),
          Equal.trans(Nat,
            Nat.add(1n, Maybe.default(&1, Nat,
              Tree.depth.go(kids, Feedback.feedback(g, w), w), 0n)),
            Maybe.default(&1, Nat,
              Tree.depth.bump(Tree.depth.go(kids, Feedback.feedback(g, w), w)), 0n),
            Nat.add(Maybe.default(&1, Nat,
              Tree.depth.bump(Tree.depth.go(kids, Feedback.feedback(g, w), w)), 0n), 0n),
            Equal.sym(Nat,
              Maybe.default(&1, Nat,
                Tree.depth.bump(Tree.depth.go(kids, Feedback.feedback(g, w), w)), 0n),
              Nat.add(1n, Maybe.default(&1, Nat,
                Tree.depth.go(kids, Feedback.feedback(g, w), w), 0n)), db),
            Equal.sym(Nat,
              Nat.add(Maybe.default(&1, Nat,
                Tree.depth.bump(Tree.depth.go(kids, Feedback.feedback(g, w), w)), 0n), 0n),
              Maybe.default(&1, Nat,
                Tree.depth.bump(Tree.depth.go(kids, Feedback.feedback(g, w), w)), 0n),
              NatProof.NatPrf.add_zero(Maybe.default(&1, Nat,
                Tree.depth.bump(Tree.depth.go(kids, Feedback.feedback(g, w), w)), 0n)))),
          h)
      e1

# The cost of a node plus the root guess's multiplicity is at least twice the
# candidate count.
def LB.node_cost_plus_mult(+g: +List<Nat>, +kids: +List<Tree.Child>,
    +S: +List<+List<Nat>>, v: Tree.AllHaveDepth(Tree.Node{g, kids}, S)) ->
  {Nat.is_le(Nat.add(List.length(&2, +List<Nat>, S), List.length(&2, +List<Nat>, S)),
             Nat.add(Tree.cost(Tree.Node{g, kids}, S), LB.mult(g, S))) == True{} : Bool}:
  match S:
    case Nil{}:
      {==}
    case Con{h, t}:
      (sh, st) = v
      +lt : Nat = List.length(&2, +List<Nat>, t)
      +ct : Nat = Tree.cost(Tree.Node{g, kids}, t)
      +mt : Nat = LB.mult(g, t)
      +d : Nat = Maybe.default(&1, Nat, Tree.depth(Tree.Node{g, kids}, h), 0n)
      +hit : Nat = LB.hit(g, h)
      +ih : {Nat.is_le(Nat.add(lt, lt), Nat.add(ct, mt)) == True{} : Bool} =
        LB.node_cost_plus_mult(g, kids, t, st)
      +per : {Nat.is_le(2n, Nat.add(d, hit)) == True{} : Bool} =
        LB.node_pair_ge_two(g, kids, h, Feedback.word_eq(g, h),
          SizeProof.LB.go_positive(kids, Feedback.feedback(g, h), h), sh)
      +c0 : {Nat.is_le(Nat.add(2n, Nat.add(lt, lt)),
                       Nat.add(Nat.add(d, hit), Nat.add(ct, mt))) == True{} : Bool} =
        CB.CB.is_le_add(2n, Nat.add(d, hit), Nat.add(lt, lt), Nat.add(ct, mt), per, ih)
      +right : {Nat.add(Nat.add(d, hit), Nat.add(ct, mt))
                == Nat.add(Nat.add(d, ct), Nat.add(hit, mt)) : Nat} =
        NatProof.NatPrf.add4(d, hit, ct, mt)
      +left : {Nat.add(Nat.add(1n, lt), Nat.add(1n, lt))
               == Nat.add(2n, Nat.add(lt, lt)) : Nat} =
        NatProof.NatPrf.add4(1n, lt, 1n, lt)
      +c1 : {Nat.is_le(Nat.add(2n, Nat.add(lt, lt)),
                       Nat.add(Nat.add(d, ct), Nat.add(hit, mt))) == True{} : Bool} =
        NatProof.Nat.is_le_eq_r(Nat.add(2n, Nat.add(lt, lt)),
          Nat.add(Nat.add(d, hit), Nat.add(ct, mt)),
          Nat.add(Nat.add(d, ct), Nat.add(hit, mt)), right, c0)
      NatProof.Nat.is_le_eq_l(Nat.add(Nat.add(d, ct), Nat.add(hit, mt)),
        Nat.add(2n, Nat.add(lt, lt)), Nat.add(Nat.add(1n, lt), Nat.add(1n, lt)),
        Equal.sym(Nat, Nat.add(Nat.add(1n, lt), Nat.add(1n, lt)),
                  Nat.add(2n, Nat.add(lt, lt)), left), c1)

# The root guess of a tree.
def LB.guess(t: Tree.Tree) -> +List<Nat>:
  match t:
    case Tree.Node{g, kids}:
      g

# The same bound for a tree, with `LB.guess` naming its root guess.
def LB.cost_plus_mult(t: Tree.Tree, +S: +List<+List<Nat>>,
    v: Tree.AllHaveDepth(t, S)) ->
  {Nat.is_le(Nat.add(List.length(&2, +List<Nat>, S), List.length(&2, +List<Nat>, S)),
             Nat.add(Tree.cost(t, S), LB.mult(LB.guess(t), S))) == True{} : Bool}:
  match t:
    case Tree.Node{g, kids}:
      LB.node_cost_plus_mult(g, kids, S, v)

# The bound for a valid tree.
def LB.valid_cost_plus_mult(t: Tree.Tree, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    v: Tree.Valid(t, G, S)) ->
  {Nat.is_le(Nat.add(List.length(&2, +List<Nat>, S), List.length(&2, +List<Nat>, S)),
             Nat.add(Tree.cost(t, S), LB.mult(LB.guess(t), S))) == True{} : Bool}:
  (vi, vd) = v
  LB.cost_plus_mult(t, S, vd)

# When the root guess has multiplicity at most one, the cost exceeds twice the
# candidate count by at most one: `2|S| <= cost + 1`, the classical
# `2|S| - 1` bound without subtraction.
def LB.cost_plus_one(t: Tree.Tree, +S: +List<+List<Nat>>,
    v: Tree.AllHaveDepth(t, S),
    m1: {Nat.is_le(LB.mult(LB.guess(t), S), 1n) == True{} : Bool}) ->
  {Nat.is_le(Nat.add(List.length(&2, +List<Nat>, S), List.length(&2, +List<Nat>, S)),
             Nat.add(Tree.cost(t, S), 1n)) == True{} : Bool}:
  +tc : Tree.Tree = t
  +core : {Nat.is_le(Nat.add(List.length(&2, +List<Nat>, S), List.length(&2, +List<Nat>, S)),
                    Nat.add(Tree.cost(t, S), LB.mult(LB.guess(t), S))) == True{} : Bool} =
    LB.cost_plus_mult(tc, S, v)
  +step : {Nat.is_le(Nat.add(Tree.cost(tc, S), LB.mult(LB.guess(tc), S)),
                     Nat.add(Tree.cost(tc, S), 1n)) == True{} : Bool} =
    NatProof.Nat.is_le_add_l(LB.mult(LB.guess(tc), S), 1n, Tree.cost(tc, S), m1)
  NatProof.Nat.is_le_trans(
    Nat.add(List.length(&2, +List<Nat>, S), List.length(&2, +List<Nat>, S)),
    Nat.add(Tree.cost(tc, S), LB.mult(LB.guess(tc), S)),
    Nat.add(Tree.cost(tc, S), 1n), core, step)

# A hit value only depends on its boolean.
def LB.hit_bool_eq(b: Bool, c: Bool, e: {b == c : Bool}) ->
  {LB.hit_bool(b) == LB.hit_bool(c) : Nat}:
  Equal.cong(Bool, Nat, LB.hit_bool, b, c, e)

# One multiplicity step, with the equality decision as a parameter.
def LB.maxMult_step(+g: +List<Nat>, +h: +List<Nat>, +t: +List<+List<Nat>>, b: Bool,
    +e: {Feedback.word_eq(g, h) == b : Bool},
    acc: {Nat.is_le(LB.mult(g, t), LB.maxMult(h <> t)) == True{} : Bool}) ->
  {Nat.is_le(LB.mult(g, h <> t), LB.maxMult(h <> t)) == True{} : Bool}:
  match b:
    case True{}:
      +eq : {g == h : +List<Nat>} = CoverList.Cover.word_eq_true(g, h, e)
      +hitg : {LB.hit(g, h) == 1n : Nat} =
        Equal.trans(Nat, LB.hit(g, h), LB.hit_bool(True{}), 1n,
          LB.hit_bool_eq(Feedback.word_eq(g, h), True{}, e), {==})
      +hith : {LB.hit(h, h) == 1n : Nat} =
        Equal.trans(Nat, LB.hit(h, h), LB.hit_bool(True{}), 1n,
          LB.hit_bool_eq(Feedback.word_eq(h, h), True{}, FbProof.FbPrf.word_eq_refl(h)), {==})
      +mt : {LB.mult(g, t) == LB.mult(h, t) : Nat} =
        Equal.cong(+List<Nat>, Nat, x => LB.mult(x, t), g, h, eq)
      +lg : {LB.mult(g, h <> t) == Nat.add(1n, LB.mult(h, t)) : Nat} =
        Equal.trans(Nat, LB.mult(g, h <> t), Nat.add(1n, LB.mult(g, t)),
          Nat.add(1n, LB.mult(h, t)),
          Equal.cong(Nat, Nat, x => Nat.add(x, LB.mult(g, t)), LB.hit(g, h), 1n, hitg),
          Equal.cong(Nat, Nat, x => Nat.add(1n, x), LB.mult(g, t), LB.mult(h, t), mt))
      +lh : {LB.mult(h, h <> t) == Nat.add(1n, LB.mult(h, t)) : Nat} =
        Equal.trans(Nat, LB.mult(h, h <> t), Nat.add(1n, LB.mult(h, t)),
          Nat.add(1n, LB.mult(h, t)),
          Equal.cong(Nat, Nat, x => Nat.add(x, LB.mult(h, t)), LB.hit(h, h), 1n, hith),
          {==})
      +same : {LB.mult(g, h <> t) == LB.mult(h, h <> t) : Nat} =
        Equal.trans(Nat, LB.mult(g, h <> t), Nat.add(1n, LB.mult(h, t)),
          LB.mult(h, h <> t), lg, Equal.sym(Nat, LB.mult(h, h <> t),
            Nat.add(1n, LB.mult(h, t)), lh))
      +head : {Nat.is_le(LB.mult(h, h <> t), LB.maxMult(h <> t)) == True{} : Bool} =
        CB.CB.is_le_of_ge(Nat.max(LB.mult(h, h <> t), LB.maxMult(t)),
          LB.mult(h, h <> t), Nat.max_ge_l(LB.mult(h, h <> t), LB.maxMult(t)))
      NatProof.Nat.is_le_eq_l(LB.maxMult(h <> t), LB.mult(h, h <> t), LB.mult(g, h <> t),
        Equal.sym(Nat, LB.mult(g, h <> t), LB.mult(h, h <> t), same), head)
    case False{}:
      +hit0 : {LB.hit(g, h) == 0n : Nat} =
        Equal.trans(Nat, LB.hit(g, h), LB.hit_bool(False{}), 0n,
          LB.hit_bool_eq(Feedback.word_eq(g, h), False{}, e), {==})
      +left : {LB.mult(g, h <> t) == LB.mult(g, t) : Nat} =
        Equal.trans(Nat, LB.mult(g, h <> t), Nat.add(0n, LB.mult(g, t)),
          LB.mult(g, t),
          Equal.cong(Nat, Nat, x => Nat.add(x, LB.mult(g, t)), LB.hit(g, h), 0n, hit0),
          {==})
      NatProof.Nat.is_le_eq_l(LB.maxMult(h <> t), LB.mult(g, t), LB.mult(g, h <> t),
        Equal.sym(Nat, LB.mult(g, h <> t), LB.mult(g, t), left), acc)

# Every multiplicity is at most the largest one.
def LB.mult_le_maxMult(+g: +List<Nat>, +S: +List<+List<Nat>>) ->
  {Nat.is_le(LB.mult(g, S), LB.maxMult(S)) == True{} : Bool}:
  match S:
    case Nil{}:
      NatProof.Nat.is_le_refl(0n)
    case Con{h, t}:
      +ih : {Nat.is_le(LB.mult(g, t), LB.maxMult(t)) == True{} : Bool} =
        LB.mult_le_maxMult(g, t)
      +max_t : {Nat.is_le(LB.maxMult(t), LB.maxMult(h <> t)) == True{} : Bool} =
        CB.CB.is_le_of_ge(Nat.max(LB.mult(h, h <> t), LB.maxMult(t)), LB.maxMult(t),
          Nat.max_ge_r(LB.mult(h, h <> t), LB.maxMult(t)))
      +acc : {Nat.is_le(LB.mult(g, t), LB.maxMult(h <> t)) == True{} : Bool} =
        NatProof.Nat.is_le_trans(LB.mult(g, t), LB.maxMult(t), LB.maxMult(h <> t), ih, max_t)
      LB.maxMult_step(g, h, t, Feedback.word_eq(g, h), {==}, acc)

# The bound with the largest multiplicity of the candidate list.
def LB.cost_plus_maxMult(t: Tree.Tree, +S: +List<+List<Nat>>,
    v: Tree.AllHaveDepth(t, S)) ->
  {Nat.is_le(Nat.add(List.length(&2, +List<Nat>, S), List.length(&2, +List<Nat>, S)),
             Nat.add(Tree.cost(t, S), LB.maxMult(S))) == True{} : Bool}:
  +tc : Tree.Tree = t
  +core : {Nat.is_le(Nat.add(List.length(&2, +List<Nat>, S), List.length(&2, +List<Nat>, S)),
                    Nat.add(Tree.cost(t, S), LB.mult(LB.guess(t), S))) == True{} : Bool} =
    LB.cost_plus_mult(tc, S, v)
  +step : {Nat.is_le(Nat.add(Tree.cost(tc, S), LB.mult(LB.guess(tc), S)),
                     Nat.add(Tree.cost(tc, S), LB.maxMult(S))) == True{} : Bool} =
    NatProof.Nat.is_le_add_l(LB.mult(LB.guess(tc), S), LB.maxMult(S), Tree.cost(tc, S),
      LB.mult_le_maxMult(LB.guess(tc), S))
  NatProof.Nat.is_le_trans(
    Nat.add(List.length(&2, +List<Nat>, S), List.length(&2, +List<Nat>, S)),
    Nat.add(Tree.cost(tc, S), LB.mult(LB.guess(tc), S)),
    Nat.add(Tree.cost(tc, S), LB.maxMult(S)), core, step)
