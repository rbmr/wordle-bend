# The cost bookkeeping of the guess fold.
#
# The optimality proof compares the cost the search stores with the cost of an
# arbitrary valid tree. `better` keeps the cheaper of two `Best`s, so the cost
# of the folded result is below every candidate cost the fold ever produced.
# This module states that in plain `Nat` order: `is_le` facts are `Bool`
# equalities, which are `Data`, so the same fact can be used in several places.
import Base
import ../src/solve_ref.bend as SolveRef
import ../src/tree.bend as Tree
import ../src/groups.bend as Groups
import ../src/feedback.bend as Feedback
import ./logic.bend as Logic
import ./nat.bend as NatProof
import ./eval.bend as Eval
import ./sat.bend as Sat
import ./cover_groups.bend as CoverGroups

# The candidate cost of one guess: its class sum plus the candidate count.
def OQ.ks_cost(+inf: Nat, +S: +List<+List<Nat>>, ks: Eval.KS) -> Nat:
  match ks:
    case Eval.KS{kids, sum}:
      SolveRef.sat_add(inf, Groups.len_words(S), sum)

# The node the guess fold builds, before `better`.
def OQ.ks_tree(+g: +List<Nat>, ks: Eval.KS) -> Tree.Tree:
  match ks:
    case Eval.KS{kids, sum}:
      Tree.Node{g, SolveRef.rev_kids(kids, Nil{})}

def OQ.cand_cost(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +g: +List<Nat>, +groups: +List<Groups.Group>, +inf: Nat) -> Nat:
  OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf))

def OQ.cand_tree(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +g: +List<Nat>, +groups: +List<Groups.Group>, +inf: Nat) -> Tree.Tree:
  OQ.ks_tree(g, Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf))

# `block` folds the classes and then offers the node to `better`.
def OQ.block_eq(+inf: Nat, +g: +List<Nat>, +S: +List<+List<Nat>>, ks: Eval.KS,
    best: SolveRef.Best) ->
  {Eval.Eval.finish_ks(inf, g, S, ks, best)
   == SolveRef.better(OQ.ks_cost(inf, S, ks), OQ.ks_tree(g, ks), best)
   : SolveRef.Best}:
  match ks:
    case Eval.KS{kids, sum}:
      {==}

# `block` is the class fold followed by `finish_ks`.
def OQ.block_unfold(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +g: +List<Nat>, +groups: +List<Groups.Group>, +inf: Nat,
    best: SolveRef.Best) ->
  {Eval.Eval.block(p, G, S, g, inf, groups, best)
   == Eval.Eval.finish_ks(inf, g, S,
        Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf), best)
   : SolveRef.Best}:
  {==}

# A branch of `better`, with the comparison as a parameter.
def OQ.better_le_cand_go(+candCost: Nat, +candTree: Tree.Tree, +tree: Tree.Tree,
    +cost: Nat, b: Bool, +eb: {b == Nat.is_lt(candCost, cost) : Bool}) ->
  {Nat.is_le(Eval.Eval.cost_of(Feedback.Bool.case(SolveRef.Best, b,
      SolveRef.Best{candTree, candCost}, SolveRef.Best{tree, cost})), candCost)
   == True{} : Bool}:
  match b:
    case True{}:
      NatProof.Nat.is_le_refl(candCost)
    case False{}:
      +e : {Nat.is_lt(candCost, cost) == False{} : Bool} =
        Equal.sym(Bool, b, Nat.is_lt(candCost, cost), eb)
      CoverGroups.Cover.is_le_of_lt_false(candCost, cost, e)

def OQ.better_le_cand(+candCost: Nat, +candTree: Tree.Tree, best: SolveRef.Best) ->
  {Nat.is_le(Eval.Eval.cost_of(SolveRef.better(candCost, candTree, best)), candCost)
   == True{} : Bool}:
  match best:
    case SolveRef.Best{+tree, +cost}:
      OQ.better_le_cand_go(candCost, candTree, tree, cost,
        Nat.is_lt(candCost, cost), {==})

def OQ.better_le_best_go(+candCost: Nat, +candTree: Tree.Tree, +tree: Tree.Tree,
    +cost: Nat, b: Bool, +eb: {b == Nat.is_lt(candCost, cost) : Bool}) ->
  {Nat.is_le(Eval.Eval.cost_of(Feedback.Bool.case(SolveRef.Best, b,
      SolveRef.Best{candTree, candCost}, SolveRef.Best{tree, cost})), cost)
   == True{} : Bool}:
  match b:
    case True{}:
      NatProof.Nat.is_le_of_lt(candCost, cost,
        Equal.sym(Bool, True{}, Nat.is_lt(candCost, cost), eb))
    case False{}:
      NatProof.Nat.is_le_refl(cost)

def OQ.better_le_best(+candCost: Nat, +candTree: Tree.Tree, best: SolveRef.Best) ->
  {Nat.is_le(Eval.Eval.cost_of(SolveRef.better(candCost, candTree, best)),
      Eval.Eval.cost_of(best)) == True{} : Bool}:
  match best:
    case SolveRef.Best{+tree, +cost}:
      OQ.better_le_best_go(candCost, candTree, tree, cost,
        Nat.is_lt(candCost, cost), {==})

# The guess step never raises the cost of the accumulator.

# Rewriting the left side of a `Nat` order fact.
def OQ.le_cong_l(+x: Nat, +y: Nat, +z: Nat, e: {x == y : Nat},
    p: {Nat.is_le(y, z) == True{} : Bool}) ->
  {Nat.is_le(x, z) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_le(x, z), Nat.is_le(y, z), True{},
    Equal.cong(Nat, Bool, w => Nat.is_le(w, z), x, y, e), p)

def OQ.le_cong_r(+x: Nat, +y: Nat, +z: Nat, e: {y == z : Nat},
    p: {Nat.is_le(x, y) == True{} : Bool}) ->
  {Nat.is_le(x, z) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_le(x, z), Nat.is_le(x, y), True{},
    Equal.sym(Bool, Nat.is_le(x, y), Nat.is_le(x, z),
      Equal.cong(Nat, Bool, w => Nat.is_le(x, w), y, z, e)), p)

# The cost of the block is the cost of the `better` state.
def OQ.block_cost_eq(+inf: Nat, +g: +List<Nat>, +S: +List<+List<Nat>>, ks: Eval.KS,
    best: SolveRef.Best) ->
  {Eval.Eval.cost_of(Eval.Eval.finish_ks(inf, g, S, ks, best))
   == Eval.Eval.cost_of(SolveRef.better(OQ.ks_cost(inf, S, ks),
        OQ.ks_tree(g, ks), best)) : Nat}:
  Equal.cong(SolveRef.Best, Nat, Eval.Eval.cost_of,
    Eval.Eval.finish_ks(inf, g, S, ks, best),
    SolveRef.better(OQ.ks_cost(inf, S, ks), OQ.ks_tree(g, ks), best),
    OQ.block_eq(inf, g, S, ks, best))

# The guess step never raises the cost of the accumulator.
def OQ.guess_cost_le_acc_go(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +g: +List<Nat>, +inf: Nat, +best: SolveRef.Best, b: Bool,
    +eb: {b == Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})) : Bool}) ->
  {Nat.is_le(Eval.Eval.cost_of(Eval.Eval.guess_bool(p, G, S, g,
      Groups.groups_build(g, S, Nil{}), inf, b, best)),
      Eval.Eval.cost_of(best)) == True{} : Bool}:
  match b:
    case True{}:
      +ceq : {Eval.Eval.cost_of(Eval.Eval.block(p, G, S, g, inf,
                Groups.groups_build(g, S, Nil{}), best))
              == Eval.Eval.cost_of(SolveRef.better(
                   OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g,
                     Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)),
                   OQ.ks_tree(g, Eval.Eval.items(p, G, S, g,
                     Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)),
                   best)) : Nat} =
        Equal.trans(Nat,
          Eval.Eval.cost_of(Eval.Eval.block(p, G, S, g, inf,
            Groups.groups_build(g, S, Nil{}), best)),
          Eval.Eval.cost_of(Eval.Eval.finish_ks(inf, g, S,
            Eval.Eval.items(p, G, S, g, Groups.groups_build(g, S, Nil{}),
              Nil{}, 0n, inf), best)),
          Eval.Eval.cost_of(SolveRef.better(
            OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g,
              Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)),
            OQ.ks_tree(g, Eval.Eval.items(p, G, S, g,
              Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)), best)),
          Equal.cong(SolveRef.Best, Nat, Eval.Eval.cost_of,
            Eval.Eval.block(p, G, S, g, inf,
              Groups.groups_build(g, S, Nil{}), best),
            Eval.Eval.finish_ks(inf, g, S,
              Eval.Eval.items(p, G, S, g, Groups.groups_build(g, S, Nil{}),
                Nil{}, 0n, inf), best),
            OQ.block_unfold(p, G, S, g, Groups.groups_build(g, S, Nil{}),
              inf, best)),
          OQ.block_cost_eq(inf, g, S,
            Eval.Eval.items(p, G, S, g, Groups.groups_build(g, S, Nil{}),
              Nil{}, 0n, inf), best))
      +cl : {Eval.Eval.cost_of(Eval.Eval.block(p, G, S, g, inf,
                Groups.groups_build(g, S, Nil{}), best))
              == Eval.Eval.cost_of(Eval.Eval.guess_bool(p, G, S, g,
                   Groups.groups_build(g, S, Nil{}), inf, b, best)) : Nat} =
        Equal.cong(SolveRef.Best, Nat, Eval.Eval.cost_of,
          Eval.Eval.block(p, G, S, g, inf, Groups.groups_build(g, S, Nil{}),
            best),
          Eval.Eval.guess_bool(p, G, S, g, Groups.groups_build(g, S, Nil{}),
            inf, b, best),
          Equal.sym(SolveRef.Best,
            Eval.Eval.guess_bool(p, G, S, g, Groups.groups_build(g, S, Nil{}),
              inf, b, best),
            Eval.Eval.block(p, G, S, g, inf, Groups.groups_build(g, S, Nil{}),
              best), {==}))
      +inner : {Nat.is_le(Eval.Eval.cost_of(SolveRef.better(
                    OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g,
                      Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)),
                    OQ.ks_tree(g, Eval.Eval.items(p, G, S, g,
                      Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)),
                    best)),
                  Eval.Eval.cost_of(best)) == True{} : Bool} =
        OQ.better_le_best(
          OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g,
            Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)),
          OQ.ks_tree(g, Eval.Eval.items(p, G, S, g,
            Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)), best)
      +mid : {Nat.is_le(Eval.Eval.cost_of(Eval.Eval.block(p, G, S, g, inf,
                 Groups.groups_build(g, S, Nil{}), best)),
                 Eval.Eval.cost_of(best)) == True{} : Bool} =
        OQ.le_cong_l(
          Eval.Eval.cost_of(Eval.Eval.block(p, G, S, g, inf,
            Groups.groups_build(g, S, Nil{}), best)),
          Eval.Eval.cost_of(SolveRef.better(
            OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g,
              Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)),
            OQ.ks_tree(g, Eval.Eval.items(p, G, S, g,
              Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)), best)),
          Eval.Eval.cost_of(best), ceq, inner)
      OQ.le_cong_l(
        Eval.Eval.cost_of(Eval.Eval.guess_bool(p, G, S, g,
          Groups.groups_build(g, S, Nil{}), inf, b, best)),
        Eval.Eval.cost_of(Eval.Eval.block(p, G, S, g, inf,
          Groups.groups_build(g, S, Nil{}), best)),
        Eval.Eval.cost_of(best), Equal.sym(Nat,
          Eval.Eval.cost_of(Eval.Eval.block(p, G, S, g, inf,
            Groups.groups_build(g, S, Nil{}), best)),
          Eval.Eval.cost_of(Eval.Eval.guess_bool(p, G, S, g,
            Groups.groups_build(g, S, Nil{}), inf, b, best)), cl),
        mid)
    case False{}:
      NatProof.Nat.is_le_refl(Eval.Eval.cost_of(best))

def OQ.guess_cost_le_acc(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +g: +List<Nat>, +inf: Nat, +best: SolveRef.Best) ->
  {Nat.is_le(Eval.Eval.cost_of(Eval.Eval.guess(p, G, S, g, inf, best)),
      Eval.Eval.cost_of(best)) == True{} : Bool}:
  OQ.guess_cost_le_acc_go(p, G, S, g, inf, best,
    Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})), {==})

# The guess fold never raises the cost of the accumulator.
def OQ.guesses_cost_le_acc(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +inf: Nat, +gs: +List<+List<Nat>>, +best: SolveRef.Best) ->
  {Nat.is_le(Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, gs, best)),
      Eval.Eval.cost_of(best)) == True{} : Bool}:
  match gs:
    case Nil{}:
      NatProof.Nat.is_le_refl(Eval.Eval.cost_of(best))
    case Con{g, t}:
      +ih : {Nat.is_le(Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, t,
                 Eval.Eval.guess(p, G, S, g, inf, best))),
               Eval.Eval.cost_of(Eval.Eval.guess(p, G, S, g, inf, best)))
             == True{} : Bool} =
        OQ.guesses_cost_le_acc(p, G, S, inf, t,
          Eval.Eval.guess(p, G, S, g, inf, best))
      NatProof.Nat.is_le_trans(
        Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, g <> t, best)),
        Eval.Eval.cost_of(Eval.Eval.guess(p, G, S, g, inf, best)),
        Eval.Eval.cost_of(best), ih,
        OQ.guess_cost_le_acc(p, G, S, g, inf, best))
