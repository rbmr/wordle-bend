# Validity of the solver at every fuel.
#
# The fused search `step` returns a `Best` whose cost is either infinity or a
# valid tree. That invariant is proved by induction on the fuel, with no bound
# on the candidate count: too little fuel only ever turns a class into infinity,
# and infinity is the case where validity is vacuous. The per-class results are
# then folded into a node, and the candidates recover their depths from the
# classes they belong to.
#
# This module holds the arithmetic and fold plumbing. The group walk and the
# node construction follow below it.
import Base
import ../src/solve_ref.bend as SolveRef
import ../src/tree.bend as Tree
import ../src/groups.bend as Groups
import ../src/feedback.bend as Feedback
import ./logic.bend as Logic
import ./nat.bend as NatProof
import ./feedback.bend as Fb
import ./eval.bend as Eval
import ./sat.bend as Sat
import ./bestok.bend as BO
import ./children.bend as CH
import ./kids.bend as KidsProof
import ./nodecost.bend as NodeCost
import ./depthgroups.bend as DG
import ./nodevalid.bend as NV
import ./groupsdistinct.bend as GD
import ./groups.bend as Grp

# A cost that is below infinity cannot also be at least infinity.
def SV.lt_ge_absurd_go(+a: Nat, +b: Nat, c: Cmp,
    +ec: {c == Nat.cmp(a, b) : Cmp},
    lt: {Cmp.is_lt(c) == True{} : Bool},
    ge: {Cmp.is_ge(c) == True{} : Bool}) -> Empty:
  match c:
    case LT{}:
      Logic.Proof.false_ne_true(ge)
    case EQ{}:
      Logic.Proof.false_ne_true(lt)
    case GT{}:
      Logic.Proof.false_ne_true(lt)

def SV.lt_ge_absurd(+a: Nat, +b: Nat,
    lt: {Nat.is_lt(a, b) == True{} : Bool},
    ge: {Nat.is_ge(a, b) == True{} : Bool}) -> Empty:
  SV.lt_ge_absurd_go(a, b, Nat.cmp(a, b), {==}, lt, ge)

# The tree of a finite best result is valid.
def SV.valid_of_ok_lt(+inf: Nat, best: SolveRef.Best,
    +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    lt: {Nat.is_lt(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    ok: BO.BO.BestOK(inf, best, G, S)) -> Tree.Valid(Eval.Eval.tree_of(best), G, S):
  match best:
    case SolveRef.Best{tree, +cost}:
      match ok:
        case Inl{ge}:
          Empty.absurd(Tree.Valid(tree, G, S),
                       SV.lt_ge_absurd(cost, inf, lt, ge))
        case Inr{p}:
          (lt2, v) = p
          v

# A candidate result is OK when its tree is valid whenever its cost is finite.
def SV.cand_ok_go(+inf: Nat, +candCost: Nat, +candTree: Tree.Tree,
    +G: +List<+List<Nat>>, +S: +List<+List<Nat>>, b: Bool,
    +eb: {b == Nat.is_ge(candCost, inf) : Bool},
    cond: {Nat.is_lt(candCost, inf) == True{} : Bool} -> Tree.Valid(candTree, G, S)) ->
  BO.BO.BestOK(inf, SolveRef.Best{candTree, candCost}, G, S):
  match b:
    case True{}:
      Inl{Equal.sym(Bool, b, Nat.is_ge(candCost, inf), eb)}
    case False{}:
      Inr{(Sat.SB.lt_of_ge_false(candCost, inf,
             Equal.sym(Bool, b, Nat.is_ge(candCost, inf), eb)),
           cond(Sat.SB.lt_of_ge_false(candCost, inf,
             Equal.sym(Bool, b, Nat.is_ge(candCost, inf), eb))))}

def SV.cand_ok(+inf: Nat, +candCost: Nat, +candTree: Tree.Tree,
    +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    cond: {Nat.is_lt(candCost, inf) == True{} : Bool} -> Tree.Valid(candTree, G, S)) ->
  BO.BO.BestOK(inf, SolveRef.Best{candTree, candCost}, G, S):
  SV.cand_ok_go(inf, candCost, candTree, G, S, Nat.is_ge(candCost, inf), {==}, cond)

# `better` keeps the invariant when the candidate is valid on its finite costs.
def SV.better_cond_go(+inf: Nat, +candCost: Nat, +candTree: Tree.Tree,
    +G: +List<+List<Nat>>, +S: +List<+List<Nat>>, +tree: Tree.Tree, +cost: Nat,
    b: Bool, +eb: {b == Nat.is_lt(candCost, cost) : Bool},
    cond: {Nat.is_lt(candCost, inf) == True{} : Bool} -> Tree.Valid(candTree, G, S),
    ok: BO.BO.BestOK(inf, SolveRef.Best{tree, cost}, G, S)) ->
  BO.BO.BestOK(inf,
    Feedback.Bool.case(SolveRef.Best, b,
      SolveRef.Best{candTree, candCost}, SolveRef.Best{tree, cost}), G, S):
  match b:
    case True{}:
      SV.cand_ok(inf, candCost, candTree, G, S, cond)
    case False{}:
      ok

def SV.better_cond(+inf: Nat, +candCost: Nat, +candTree: Tree.Tree,
    best: SolveRef.Best, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    cond: {Nat.is_lt(candCost, inf) == True{} : Bool} -> Tree.Valid(candTree, G, S),
    ok: BO.BO.BestOK(inf, best, G, S)) ->
  BO.BO.BestOK(inf, SolveRef.better(candCost, candTree, best), G, S):
  match best:
    case SolveRef.Best{tree, +cost}:
      SV.better_cond_go(inf, candCost, candTree, G, S, tree, cost,
        Nat.is_lt(candCost, cost), {==}, cond, ok)
