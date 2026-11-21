# The search state is either absent or a valid tree.
#
# `better` keeps the cheaper of a candidate and the best so far. This module
# defines the invariant the guess fold carries, `BestOK`: the stored cost is at
# least infinity, or it is finite and the stored tree is valid. `better`
# preserves it, the initial dummy state satisfies it, and the zero-fuel fold
# keeps it. That is the base case of the validity induction.
import Base
import ../src/solve_ref.bend as SolveRef
import ../src/tree.bend as Tree
import ../src/feedback.bend as Feedback
import ../src/groups.bend as Groups
import ./feedback.bend as Fb
import ./logic.bend as Logic
import ./nat.bend as NatProof
import ./eval.bend as Eval
import ./sat.bend as Sat

def BO.BestOK(+inf: Nat, best: SolveRef.Best, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>) -> Type:
  match best:
    case SolveRef.Best{tree, +cost}:
      {Nat.is_ge(cost, inf) == True{} : Bool}
      | ({Nat.is_lt(cost, inf) == True{} : Bool} & Tree.Valid(tree, G, S))

# A valid tree is an OK state whatever its cost is.
def BO.ok_of_valid(+inf: Nat, +tree: Tree.Tree, +cost: Nat,
    +G: +List<+List<Nat>>, +S: +List<+List<Nat>>, b: Bool,
    +eb: {b == Nat.is_ge(cost, inf) : Bool},
    v: Tree.Valid(tree, G, S)) ->
  BO.BestOK(inf, SolveRef.Best{tree, cost}, G, S):
  match b:
    case True{}:
      Inl{Equal.sym(Bool, b, Nat.is_ge(cost, inf), eb)}
    case False{}:
      Inr{(Sat.SB.lt_of_ge_false(cost, inf,
             Equal.sym(Bool, False{}, Nat.is_ge(cost, inf), eb)), v)}

# `better` preserves the state invariant.
def BO.better_go(+inf: Nat, +candCost: Nat, +candTree: Tree.Tree,
    +tree: Tree.Tree, +cost: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    b: Bool, +eb: {b == Nat.is_lt(candCost, cost) : Bool},
    vc: Tree.Valid(candTree, G, S),
    vb: BO.BestOK(inf, SolveRef.Best{tree, cost}, G, S)) ->
  BO.BestOK(inf,
    Feedback.Bool.case(SolveRef.Best, b,
      SolveRef.Best{candTree, candCost}, SolveRef.Best{tree, cost}), G, S):
  match b:
    case True{}:
      BO.ok_of_valid(inf, candTree, candCost, G, S, Nat.is_ge(candCost, inf),
        {==}, vc)
    case False{}:
      vb

def BO.better_ok(+inf: Nat, +candCost: Nat, +candTree: Tree.Tree,
    best: SolveRef.Best, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    vc: Tree.Valid(candTree, G, S), vb: BO.BestOK(inf, best, G, S)) ->
  BO.BestOK(inf, SolveRef.better(candCost, candTree, best), G, S):
  match best:
    case SolveRef.Best{tree, +cost}:
      BO.better_go(inf, candCost, candTree, tree, cost, G, S,
        Nat.is_lt(candCost, cost), {==}, vc, vb)

# The initial dummy state is OK.
def BO.base_ok(+inf: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>) ->
  BO.BestOK(inf, Eval.Eval.dummy_inf(inf), G, S):
  Inl{Nat.ge_refl(inf)}

# An empty tree at a word in the guess list is valid for no candidates.
def BO.nil_tree_valid(+g: +List<Nat>, +G: +List<+List<Nat>>,
    w: Tree.WordIn(g, G)) ->
  Tree.Valid(Tree.Node{g, Nil{}}, G, Nil{}):
  ((w, Unit{}), Unit{})

def BO.word_in_cons(+g: +List<Nat>, +rest: +List<+List<Nat>>) ->
  Tree.WordIn(g, g <> rest):
  %Equal.sym(Bool, Feedback.word_eq(g, g), True{}, Fb.FbPrf.word_eq_refl(g)) : {
    Feedback.Bool.case(Bool, _, True{}, Tree.member_word(g, rest)) == True{} : Bool}
  {==}

def BO.EveryIn(+gs: +List<+List<Nat>>, +G: +List<+List<Nat>>) -> Type:
  match gs:
    case Nil{}:
      Unit
    case Con{g, t}:
      Tree.WordIn(g, G) & BO.EveryIn(t, G)


def BO.member_case(+w: +List<Nat>, +t: +List<+List<Nat>>, b: Bool,
    e: {Tree.member_word(w, t) == True{} : Bool}) ->
  {Feedback.Bool.case(Bool, b, True{}, Tree.member_word(w, t)) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      e

def BO.member_weaken(+w: +List<Nat>, +g: +List<Nat>, +t: +List<+List<Nat>>,
    e: {Tree.member_word(w, t) == True{} : Bool}) ->
  {Tree.member_word(w, g <> t) == True{} : Bool}:
  BO.member_case(w, t, Feedback.word_eq(w, g), e)

def BO.every_in_weaken(+gs: +List<+List<Nat>>, +g: +List<Nat>,
    +t: +List<+List<Nat>>, p: BO.EveryIn(gs, t)) ->
  BO.EveryIn(gs, g <> t):
  match gs:
    case Nil{}:
      Unit{}
    case Con{h, rest}:
      (ph, pr) = p
      (BO.member_weaken(h, g, t, ph), BO.every_in_weaken(rest, g, t, pr))

def BO.every_in_self(+G: +List<+List<Nat>>) ->
  BO.EveryIn(G, G):
  match G:
    case Nil{}:
      Unit{}
    case Con{g, t}:
      (BO.word_in_cons(g, t),
       BO.every_in_weaken(t, g, t, BO.every_in_self(t)))

# The zero-fuel fold over the guess list keeps the invariant.
def BO.guesses_zero_ok(+G: +List<+List<Nat>>, +inf: Nat,
    +gs: +List<+List<Nat>>, +best: SolveRef.Best,
    every: BO.EveryIn(gs, G), ok: BO.BestOK(inf, best, G, Nil{})) ->
  BO.BestOK(inf, Eval.Eval.guesses(0n, G, Nil{}, inf, gs, best), G, Nil{}):
  match gs:
    case Nil{}:
      ok
    case Con{g, rest}:
      (wg, every_rest) = every
      +next : SolveRef.Best =
        SolveRef.finish_guess(inf, g, Nil{}, 0n, Groups.len_words(Nil{}), best)
      BO.guesses_zero_ok(G, inf, rest, next, every_rest,
        BO.better_ok(inf, SolveRef.sat_add(inf, 0n, 0n),
          Tree.Node{g, Nil{}}, best, G, Nil{},
          BO.nil_tree_valid(g, G, wg), ok))
