# Validity of the fused search at every fuel.
#
# `step` returns a `Best` whose cost is either at least infinity or a valid
# tree. The proof is an induction on the fuel. At fuel `1+p` one guess is
# evaluated by the specification fold `Eval.guess` at fuel `p`; the fold over
# the guess list then keeps the invariant. The classes of a guess are searched
# at `p`, so the induction has to hand every class of every guess its own
# result: a single recursive call returns the conjunction over all of them,
# and the per-guess conjunctions are read off by splitting that conjunction.
#
# This module proves the guess step (`guess_ok`), the fuel recursion (`flat`)
# and finally `solve_valid`.
import Base
import ../src/solve_ref.bend as SolveRef
import ../src/tree.bend as Tree
import ../src/groups.bend as Groups
import ../src/feedback.bend as Feedback
import ./logic.bend as Logic
import ./nat.bend as NatProof
import ./eval.bend as Eval
import ./sat.bend as Sat
import ./bestok.bend as BO
import ./children.bend as CH
import ./groupsmeasure.bend as GM
import ./solvevalid.bend as SV

# The class obligations of one guess, only when the guess is usable. An
# unusable guess contributes no class to the schedule, so it needs none.
def MV.OksIf(b: Bool, +p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +g: +List<Nat>, +inf: Nat) -> Type:
  match b:
    case True{}:
      SV.SV.Oks(p, G, inf, Groups.groups_build(g, S, Nil{}))
    case False{}:
      Unit

# `better` keeps the invariant when the candidate is at least infinity.
def MV.better_ge_go(+inf: Nat, +candCost: Nat, +candTree: Tree.Tree,
    +tree: Tree.Tree, +cost: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    b: Bool, +eb: {b == Nat.is_lt(candCost, cost) : Bool},
    ge: {Nat.is_ge(candCost, inf) == True{} : Bool},
    ok: BO.BO.BestOK(inf, SolveRef.Best{tree, cost}, G, S)) ->
  BO.BO.BestOK(inf,
    Feedback.Bool.case(SolveRef.Best, b,
      SolveRef.Best{candTree, candCost}, SolveRef.Best{tree, cost}), G, S):
  match b:
    case True{}:
      Inl{ge}
    case False{}:
      ok

def MV.better_ge_ok(+inf: Nat, +candCost: Nat, +candTree: Tree.Tree,
    best: SolveRef.Best, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    ge: {Nat.is_ge(candCost, inf) == True{} : Bool},
    ok: BO.BO.BestOK(inf, best, G, S)) ->
  BO.BO.BestOK(inf, SolveRef.better(candCost, candTree, best), G, S):
  match best:
    case SolveRef.Best{tree, +cost}:
      MV.better_ge_go(inf, candCost, candTree, tree, cost, G, S,
        Nat.is_lt(candCost, cost), {==}, ge, ok)

# The finished guess at a group fold: the node cost decides whether the
# candidate can be used at all.
def MV.finish_ge_case(+inf: Nat, +p: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +g: +List<Nat>, +kids: +List<Tree.Child>, +sum: Nat,
    best: SolveRef.Best, b: Bool,
    +eb: {b == Nat.is_ge(SolveRef.sat_add(inf, Groups.len_words(S), sum), inf) : Bool},
    +eks: {Eval.KS{kids, sum}
          == Eval.Eval.items(p, G, S, g, Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)
          : Eval.KS},
    wg: Tree.WordIn(g, G),
    oks: SV.SV.Oks(p, G, inf, Groups.groups_build(g, S, Nil{})),
    ok: BO.BO.BestOK(inf, best, G, S)) ->
  BO.BO.BestOK(inf,
    SolveRef.better(SolveRef.sat_add(inf, Groups.len_words(S), sum),
      Tree.Node{g, SolveRef.rev_kids(kids, Nil{})}, best), G, S):
  match b:
    case True{}:
      MV.better_ge_ok(inf,
        SolveRef.sat_add(inf, Groups.len_words(S), sum),
        Tree.Node{g, SolveRef.rev_kids(kids, Nil{})}, best, G, S,
        Equal.sym(Bool, True{},
          Nat.is_ge(SolveRef.sat_add(inf, Groups.len_words(S), sum), inf), eb),
        ok)
    case False{}:
      +lt : {Nat.is_lt(SolveRef.sat_add(inf, Groups.len_words(S), sum), inf) == True{}
             : Bool} =
        Sat.SB.lt_of_ge_false(SolveRef.sat_add(inf, Groups.len_words(S), sum), inf,
          Equal.sym(Bool, False{},
            Nat.is_ge(SolveRef.sat_add(inf, Groups.len_words(S), sum), inf), eb))
      +eSum : {sum == Sat.SB.ks_sum(Eval.Eval.items(p, G, S, g,
                 Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)) : Nat} =
        Equal.cong(Eval.KS, Nat, Sat.SB.ks_sum, Eval.KS{kids, sum},
          Eval.Eval.items(p, G, S, g, Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf),
          eks)
      +eKids : {kids == SolveRef.rev_kids(
                  CH.CH.children(p, G, S, Groups.groups_build(g, S, Nil{}), inf), Nil{})
                : +List<Tree.Child>} =
        Equal.trans(+List<Tree.Child>, kids,
          CH.CH.kids_of(Eval.Eval.items(p, G, S, g,
            Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)),
          SolveRef.rev_kids(CH.CH.children(p, G, S,
            Groups.groups_build(g, S, Nil{}), inf), Nil{}),
          Equal.cong(Eval.KS, +List<Tree.Child>, CH.CH.kids_of, Eval.KS{kids, sum},
            Eval.Eval.items(p, G, S, g, Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf),
            eks),
          CH.CH.items_kids(p, G, S, g, Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf))
      vc : Tree.Valid(Tree.Node{g, SolveRef.rev_kids(kids, Nil{})}, G, S) =
        SV.SV.end_valid(p, G, S, g, inf, kids, sum, lt, oks, eSum, eKids, wg)
      BO.BO.better_ok(inf, SolveRef.sat_add(inf, Groups.len_words(S), sum),
        Tree.Node{g, SolveRef.rev_kids(kids, Nil{})}, best, G, S, vc, ok)

# The group fold of one guess leaves the invariant intact.
def MV.finish_go(+inf: Nat, +p: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +g: +List<Nat>, ks: Eval.KS, best: SolveRef.Best,
    b: Bool,
    +eb: {b == Nat.is_ge(SolveRef.sat_add(inf, Groups.len_words(S),
             Sat.SB.ks_sum(ks)), inf) : Bool},
    +eks: {ks == Eval.Eval.items(p, G, S, g, Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)
           : Eval.KS},
    wg: Tree.WordIn(g, G),
    oks: SV.SV.Oks(p, G, inf, Groups.groups_build(g, S, Nil{})),
    ok: BO.BO.BestOK(inf, best, G, S)) ->
  BO.BO.BestOK(inf, Eval.Eval.finish_ks(inf, g, S, ks, best), G, S):
  match ks:
    case Eval.KS{kids, sum}:
      MV.finish_ge_case(inf, p, G, S, g, kids, sum, best, b, eb, eks, wg, oks, ok)

# The usable-guess branch: `Eval.block` is the group fold.
def MV.guess_ok_go(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +g: +List<Nat>, +inf: Nat, best: SolveRef.Best, b: Bool,
    +eb: {b == Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})) : Bool},
    wg: Tree.WordIn(g, G),
    oks: MV.OksIf(b, p, G, S, g, inf),
    ok: BO.BO.BestOK(inf, best, G, S)) ->
  BO.BO.BestOK(inf,
    Eval.Eval.guess_bool(p, G, S, g, Groups.groups_build(g, S, Nil{}), inf, b, best),
    G, S):
  match b:
    case True{}:
      MV.finish_go(inf, p, G, S, g,
        Eval.Eval.items(p, G, S, g, Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf),
        best,
        Nat.is_ge(SolveRef.sat_add(inf, Groups.len_words(S),
          Sat.SB.ks_sum(Eval.Eval.items(p, G, S, g,
            Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf))), inf),
        {==}, {==}, wg, oks, ok)
    case False{}:
      ok

# The guess step preserves the invariant.
def MV.guess_ok(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +g: +List<Nat>, +inf: Nat, best: SolveRef.Best,
    b: Bool,
    +eb: {b == Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})) : Bool},
    wg: Tree.WordIn(g, G),
    oks: MV.OksIf(b, p, G, S, g, inf),
    ok: BO.BO.BestOK(inf, best, G, S)) ->
  BO.BO.BestOK(inf,
    Eval.Eval.guess_bool(p, G, S, g, Groups.groups_build(g, S, Nil{}), inf, b, best),
    G, S):
  MV.guess_ok_go(p, G, S, g, inf, best, b, eb, wg, oks, ok)
