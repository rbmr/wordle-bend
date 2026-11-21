# The pruning lemma: a skipped block leaves the best result unchanged.
#
# `better` replaces the accumulator only on a strictly lower cost, so a guess
# whose own cost is at least the accumulator's cost cannot change the fold. The
# search skips exactly the guesses whose lower bound is at least the
# accumulator's cost, so the lemma needs only that the bound is below the
# guess's own cost.
import Base
import ../src/solve_fast.bend as SolveFast
import ../src/solve_ref.bend as SolveRef
import ../src/tree.bend as Tree
import ../src/groups.bend as Groups
import ../src/feedback.bend as Feedback
import ./logic.bend as Logic
import ./nat.bend as NatProof
import ./eval.bend as Eval
import ./optfold.bend as Fold

# `a <= b` means `b < a` is false.
def FS.is_lt_false_of_le(a: Nat, b: Nat,
    e: {Nat.is_le(a, b) == True{} : Bool}) ->
  {Nat.is_lt(b, a) == False{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      {==}
    case 1n+ap 0n:
      Empty.absurd({Nat.is_lt(0n, 1n+ap) == False{} : Bool},
        Logic.Proof.false_ne_true(e))
    case 1n+ap 1n+bp:
      FS.is_lt_false_of_le(ap, bp, e)

# `better` keeps the accumulator when the candidate is not strictly cheaper.
def FS.keep_go(+candCost: Nat, +candTree: Tree.Tree, +tree: Tree.Tree,
    +cost: Nat, +lb: Nat, b: Bool,
    +eb: {b == Nat.is_lt(candCost, cost) : Bool},
    +le: {Nat.is_le(cost, lb) == True{} : Bool},
    +bl: {Nat.is_le(lb, candCost) == True{} : Bool}) ->
  {Feedback.Bool.case(SolveRef.Best, b,
      SolveRef.Best{candTree, candCost}, SolveRef.Best{tree, cost})
   == SolveRef.Best{tree, cost} : SolveRef.Best}:
  match b:
    case True{}:
      +ge : {Nat.is_le(cost, candCost) == True{} : Bool} =
        NatProof.Nat.is_le_trans(cost, lb, candCost, le, bl)
      +lf : {Nat.is_lt(candCost, cost) == False{} : Bool} =
        FS.is_lt_false_of_le(cost, candCost, ge)
      Empty.absurd({SolveRef.Best{candTree, candCost}
                    == SolveRef.Best{tree, cost} : SolveRef.Best},
        Logic.Proof.true_ne_false(Equal.trans(Bool, True{},
          Nat.is_lt(candCost, cost), False{}, eb, lf)))
    case False{}:
      {==}

def FS.keep(+candCost: Nat, +candTree: Tree.Tree, +best: SolveRef.Best,
    +lb: Nat,
    +le: {Nat.is_le(Eval.Eval.cost_of(best), lb) == True{} : Bool},
    +bl: {Nat.is_le(lb, candCost) == True{} : Bool}) ->
  {SolveRef.better(candCost, candTree, best) == best : SolveRef.Best}:
  match best:
    case SolveRef.Best{+tree, +cost}:
      FS.keep_go(candCost, candTree, tree, cost, lb,
        Nat.is_lt(candCost, cost), {==}, le, bl)

# The reference guess is skipped: its own cost is at least the accumulator's.
def FS.guess_skip(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +g: +List<Nat>, +inf: Nat, +lb: Nat, +best: SolveRef.Best,
    +us: {Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})) == True{}
         : Bool},
    +le: {Nat.is_le(Eval.Eval.cost_of(best), lb) == True{} : Bool},
    +bl: {Nat.is_le(lb, Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g,
             Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf))) == True{} : Bool}) ->
  {Eval.Eval.guess(p, G, S, g, inf, best) == best : SolveRef.Best}:
  +grp : +List<Groups.Group> = Groups.groups_build(g, S, Nil{})
  +ks : Eval.KS = Eval.Eval.items(p, G, S, g, grp, Nil{}, 0n, inf)
  +e1 : {Eval.Eval.guess(p, G, S, g, inf, best)
         == Eval.Eval.block(p, G, S, g, inf, grp, best) : SolveRef.Best} =
    Equal.cong(Bool, SolveRef.Best,
      b => Feedback.Bool.case(SolveRef.Best, b,
             Eval.Eval.block(p, G, S, g, inf, grp, best), best),
      Groups.groups_smaller(S, grp), True{}, us)
  +e2 : {Eval.Eval.block(p, G, S, g, inf, grp, best)
         == SolveRef.better(Fold.OQ.ks_cost(inf, S, ks),
              Fold.OQ.ks_tree(g, ks), best) : SolveRef.Best} =
    Fold.OQ.block_eq(inf, g, S, ks, best)
  +e3 : {SolveRef.better(Fold.OQ.ks_cost(inf, S, ks),
              Fold.OQ.ks_tree(g, ks), best) == best : SolveRef.Best} =
    FS.keep(Fold.OQ.ks_cost(inf, S, ks), Fold.OQ.ks_tree(g, ks), best, lb,
      le, bl)
  Equal.trans(SolveRef.Best,
    Eval.Eval.guess(p, G, S, g, inf, best),
    Eval.Eval.block(p, G, S, g, inf, grp, best),
    best, e1, Equal.trans(SolveRef.Best,
      Eval.Eval.block(p, G, S, g, inf, grp, best),
      SolveRef.better(Fold.OQ.ks_cost(inf, S, ks),
        Fold.OQ.ks_tree(g, ks), best),
      best, e2, e3))
