# Replaying the reference fold over independently computed guess results.
#
# The parallel solver evaluates every guess from the neutral accumulator and
# then folds the results with `better`. A result is `better(cost, tree, inf)`,
# so replaying it on the running accumulator must be the same as evaluating the
# guess on that accumulator directly. This module proves that replay step, the
# one place where the accumulator matters.
import Base
import ../src/feedback.bend as Feedback
import ../src/tree.bend as Tree
import ../src/groups.bend as Groups
import ../src/solve_ref.bend as SolveRef
import ../src/solve_par.bend as SolvePar
import ./logic.bend as Logic
import ./nat.bend as NatProof
import ./eval.bend as Eval
import ./optfold.bend as OQProof

# A `Nat.is_le` fact rules out the opposite strict comparison.
def ParElt.not_lt_of_le(a: Nat, b: Nat,
    h: {Nat.is_le(a, b) == True{} : Bool}) ->
  {Nat.is_lt(b, a) == False{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      {==}
    case 1n+ap 0n:
      Empty.absurd({Nat.is_lt(0n, 1n+ap) == False{} : Bool},
                   Logic.Proof.false_ne_true(h))
    case 1n+ap 1n+bp:
      ParElt.not_lt_of_le(ap, bp, h)

# A two-way choice on a comparison result: the candidate if the comparison
# says it is strictly cheaper, the accumulator otherwise.
def ParElt.pick(+ct: Tree.Tree, +cc: Nat, +ta: Tree.Tree, +ca: Nat,
                b: Bool) -> SolveRef.Best:
  Feedback.Bool.case(SolveRef.Best, b,
                     SolveRef.Best{ct, cc}, SolveRef.Best{ta, ca})

# `better` is the same choice, with the comparison computed.
def ParElt.pick_better(+cc: Nat, +ct: Tree.Tree, +ta: Tree.Tree, +ca: Nat,
    b: Bool, eb: {b == Nat.is_lt(cc, ca) : Bool}) ->
  {SolveRef.better(cc, ct, SolveRef.Best{ta, ca})
   == ParElt.pick(ct, cc, ta, ca, b) : SolveRef.Best}:
  Equal.cong(Bool, SolveRef.Best, v => ParElt.pick(ct, cc, ta, ca, v),
    Nat.is_lt(cc, ca), b, Equal.sym(Bool, b, Nat.is_lt(cc, ca), eb))

# Replaying a result on an accumulator: a strictly cheaper result replaces it.
def ParElt.apply(r: SolveRef.Best, best: SolveRef.Best) -> SolveRef.Best:
  match r:
    case SolveRef.Best{+tree, +cost}:
      SolveRef.better(cost, tree, best)

# Replaying the neutral result changes nothing, because its cost is infinity.
def ParElt.init_apply(+ti: Tree.Tree, +ta: Tree.Tree, +inf: Nat, +ca: Nat,
    h: {Nat.is_le(ca, inf) == True{} : Bool}) ->
  {ParElt.apply(SolveRef.Best{ti, inf}, SolveRef.Best{ta, ca})
   == SolveRef.Best{ta, ca} : SolveRef.Best}:
  +nlt : {Nat.is_lt(inf, ca) == False{} : Bool} =
    ParElt.not_lt_of_le(ca, inf, h)
  +e : {ParElt.pick(ti, inf, ta, ca, Nat.is_lt(inf, ca))
        == ParElt.pick(ti, inf, ta, ca, False{}) : SolveRef.Best} =
    Equal.cong(Bool, SolveRef.Best, v => ParElt.pick(ti, inf, ta, ca, v),
               Nat.is_lt(inf, ca), False{}, nlt)
  Equal.trans(SolveRef.Best,
    ParElt.apply(SolveRef.Best{ti, inf}, SolveRef.Best{ta, ca}),
    ParElt.pick(ti, inf, ta, ca, False{}),
    SolveRef.Best{ta, ca}, e, {==})

# A candidate whose cost is not below infinity loses against an accumulator
# whose cost is at most infinity.
def ParElt.pick_acc(+cc: Nat, +ct: Tree.Tree, +ta: Tree.Tree, +ca: Nat,
    +inf: Nat, z: Bool, ez: {z == Nat.is_lt(cc, ca) : Bool},
    nf: {Nat.is_lt(cc, inf) == False{} : Bool},
    h: {Nat.is_le(ca, inf) == True{} : Bool}) ->
  {ParElt.pick(ct, cc, ta, ca, z) == SolveRef.Best{ta, ca} : SolveRef.Best}:
  match z:
    case True{}:
      +lt : {Nat.is_lt(cc, ca) == True{} : Bool} =
        Equal.sym(Bool, True{}, Nat.is_lt(cc, ca), ez)
      +ltinf : {Nat.is_lt(cc, inf) == True{} : Bool} =
        NatProof.Nat.is_lt_le_trans(cc, ca, inf, lt, h)
      +bad : {False{} == True{} : Bool} =
        Equal.trans(Bool, False{}, Nat.is_lt(cc, inf), True{},
          Equal.sym(Bool, Nat.is_lt(cc, inf), False{}, nf), ltinf)
      Empty.absurd({ParElt.pick(ct, cc, ta, ca, True{})
                    == SolveRef.Best{ta, ca} : SolveRef.Best},
                   Logic.Proof.false_ne_true(bad))
    case False{}:
      {==}

# The cost of replaying a result is at most the accumulator's cost.
def ParElt.apply_cost_le(r: SolveRef.Best, best: SolveRef.Best) ->
  {Nat.is_le(Eval.Eval.cost_of(ParElt.apply(r, best)), Eval.Eval.cost_of(best))
   == True{} : Bool}:
  match r:
    case SolveRef.Best{+tree, +cost}:
      OQProof.OQ.better_le_best(cost, tree, best)

# Replaying `better(cc, ct, inf)` on an accumulator is the same as comparing
# `cc` and `ct` with that accumulator directly. This is the core step: the
# result computed from the neutral accumulator carries the candidate, and the
# comparison with the accumulator is exactly `better`'s comparison.
def ParElt.better_apply_go(+cc: Nat, +ct: Tree.Tree, +ti: Tree.Tree,
    +ta: Tree.Tree, +inf: Nat, +ca: Nat,
    +h: {Nat.is_le(ca, inf) == True{} : Bool},
    x: Bool, +ex: {x == Nat.is_lt(cc, inf) : Bool}) ->
  {ParElt.apply(SolveRef.better(cc, ct, SolveRef.Best{ti, inf}),
                SolveRef.Best{ta, ca})
   == SolveRef.better(cc, ct, SolveRef.Best{ta, ca}) : SolveRef.Best}:
  match x:
    case True{}:
      +beq : {SolveRef.better(cc, ct, SolveRef.Best{ti, inf})
              == ParElt.pick(ct, cc, ti, inf, True{}) : SolveRef.Best} =
        ParElt.pick_better(cc, ct, ti, inf, True{}, ex)
      +lhs : {ParElt.apply(SolveRef.better(cc, ct, SolveRef.Best{ti, inf}),
                           SolveRef.Best{ta, ca})
              == ParElt.apply(ParElt.pick(ct, cc, ti, inf, True{}),
                              SolveRef.Best{ta, ca}) : SolveRef.Best} =
        Equal.cong(SolveRef.Best, SolveRef.Best,
          r => ParElt.apply(r, SolveRef.Best{ta, ca}),
          SolveRef.better(cc, ct, SolveRef.Best{ti, inf}),
          ParElt.pick(ct, cc, ti, inf, True{}), beq)
      Equal.trans(SolveRef.Best,
        ParElt.apply(SolveRef.better(cc, ct, SolveRef.Best{ti, inf}),
                     SolveRef.Best{ta, ca}),
        ParElt.apply(SolveRef.Best{ct, cc}, SolveRef.Best{ta, ca}),
        SolveRef.better(cc, ct, SolveRef.Best{ta, ca}), lhs, {==})
    case False{}:
      +nf : {Nat.is_lt(cc, inf) == False{} : Bool} =
        Equal.sym(Bool, False{}, Nat.is_lt(cc, inf), ex)
      +beq : {SolveRef.better(cc, ct, SolveRef.Best{ti, inf})
              == ParElt.pick(ct, cc, ti, inf, False{}) : SolveRef.Best} =
        ParElt.pick_better(cc, ct, ti, inf, False{}, ex)
      +lhs : {ParElt.apply(SolveRef.better(cc, ct, SolveRef.Best{ti, inf}),
                           SolveRef.Best{ta, ca})
              == ParElt.apply(ParElt.pick(ct, cc, ti, inf, False{}),
                              SolveRef.Best{ta, ca}) : SolveRef.Best} =
        Equal.cong(SolveRef.Best, SolveRef.Best,
          r => ParElt.apply(r, SolveRef.Best{ta, ca}),
          SolveRef.better(cc, ct, SolveRef.Best{ti, inf}),
          ParElt.pick(ct, cc, ti, inf, False{}), beq)
      +ia : {ParElt.apply(SolveRef.Best{ti, inf}, SolveRef.Best{ta, ca})
             == SolveRef.Best{ta, ca} : SolveRef.Best} =
        ParElt.init_apply(ti, ta, inf, ca, h)
      +racc : {SolveRef.better(cc, ct, SolveRef.Best{ta, ca})
               == SolveRef.Best{ta, ca} : SolveRef.Best} =
        Equal.trans(SolveRef.Best,
          SolveRef.better(cc, ct, SolveRef.Best{ta, ca}),
          ParElt.pick(ct, cc, ta, ca, Nat.is_lt(cc, ca)),
          SolveRef.Best{ta, ca},
          ParElt.pick_better(cc, ct, ta, ca, Nat.is_lt(cc, ca), {==}),
          ParElt.pick_acc(cc, ct, ta, ca, inf, Nat.is_lt(cc, ca), {==}, nf, h))
      Equal.trans(SolveRef.Best,
        ParElt.apply(SolveRef.better(cc, ct, SolveRef.Best{ti, inf}),
                     SolveRef.Best{ta, ca}),
        SolveRef.Best{ta, ca},
        SolveRef.better(cc, ct, SolveRef.Best{ta, ca}),
        Equal.trans(SolveRef.Best,
          ParElt.apply(SolveRef.better(cc, ct, SolveRef.Best{ti, inf}),
                       SolveRef.Best{ta, ca}),
          ParElt.apply(SolveRef.Best{ti, inf}, SolveRef.Best{ta, ca}),
          SolveRef.Best{ta, ca}, lhs, ia),
        Equal.sym(SolveRef.Best, SolveRef.better(cc, ct, SolveRef.Best{ta, ca}),
                  SolveRef.Best{ta, ca}, racc))

def ParElt.better_apply(+cc: Nat, +ct: Tree.Tree, +ti: Tree.Tree,
    +ta: Tree.Tree, +inf: Nat, +ca: Nat,
    h: {Nat.is_le(ca, inf) == True{} : Bool}) ->
  {ParElt.apply(SolveRef.better(cc, ct, SolveRef.Best{ti, inf}),
                SolveRef.Best{ta, ca})
   == SolveRef.better(cc, ct, SolveRef.Best{ta, ca}) : SolveRef.Best}:
  ParElt.better_apply_go(cc, ct, ti, ta, inf, ca, h,
    Nat.is_lt(cc, inf), {==})

# One guess's result is the guess evaluated from the neutral accumulator.
def ParElt.one_eq(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +inf: Nat, +g: +List<Nat>, +groups: +List<Groups.Group>, b: Bool) ->
  {SolvePar.one(1n+p, G, S, inf, g, groups, b)
   == Eval.Eval.guess_bool(p, G, S, g, groups, inf, b, SolvePar.init_best(inf))
   : SolveRef.Best}:
  Eval.Eval.schedule_step(p, G, S, g, groups, inf, b, Nil{},
    SolvePar.init_best(inf))

# Replaying one guess's result on an accumulator is the guess's own step on
# that accumulator.
def ParElt.guess_bool_apply(+p: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +g: +List<Nat>, +groups: +List<Groups.Group>,
    +inf: Nat, b: Bool, +acc: SolveRef.Best,
    h: {Nat.is_le(Eval.Eval.cost_of(acc), inf) == True{} : Bool}) ->
  {ParElt.apply(Eval.Eval.guess_bool(p, G, S, g, groups, inf, b,
                                SolvePar.init_best(inf)), acc)
   == Eval.Eval.guess_bool(p, G, S, g, groups, inf, b, acc) : SolveRef.Best}:
  match b:
    case True{}:
      match acc:
        case SolveRef.Best{+ta, +ca}:
          +init : SolveRef.Best = SolvePar.init_best(inf)
          +here : SolveRef.Best = SolveRef.Best{ta, ca}
          +cc : Nat = OQProof.OQ.ks_cost(inf, S,
            Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf))
          +ct : Tree.Tree = OQProof.OQ.ks_tree(g,
            Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf))
          +lhs_rewrite : {Eval.Eval.guess_bool(p, G, S, g, groups, inf, True{}, init)
                          == SolveRef.better(cc, ct, init) : SolveRef.Best} =
            OQProof.OQ.block_eq(inf, g, S,
              Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf), init)
          +rhs_rewrite : {Eval.Eval.guess_bool(p, G, S, g, groups, inf, True{}, here)
                          == SolveRef.better(cc, ct, here) : SolveRef.Best} =
            OQProof.OQ.block_eq(inf, g, S,
              Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf), here)
          +step1 : {ParElt.apply(Eval.Eval.guess_bool(p, G, S, g, groups, inf, True{}, init), here)
                    == ParElt.apply(SolveRef.better(cc, ct, init), here)
                    : SolveRef.Best} =
            Equal.cong(SolveRef.Best, SolveRef.Best, r => ParElt.apply(r, here),
              Eval.Eval.guess_bool(p, G, S, g, groups, inf, True{}, init),
              SolveRef.better(cc, ct, init), lhs_rewrite)
          +step2 : {ParElt.apply(SolveRef.better(cc, ct, init), here)
                    == SolveRef.better(cc, ct, here) : SolveRef.Best} =
            ParElt.better_apply(cc, ct, Tree.Node{Nil{}, Nil{}}, ta, inf, ca, h)
          Equal.trans(SolveRef.Best,
            ParElt.apply(Eval.Eval.guess_bool(p, G, S, g, groups, inf, True{}, init), here),
            SolveRef.better(cc, ct, here),
            Eval.Eval.guess_bool(p, G, S, g, groups, inf, True{}, here),
            Equal.trans(SolveRef.Best,
              ParElt.apply(Eval.Eval.guess_bool(p, G, S, g, groups, inf, True{}, init), here),
              ParElt.apply(SolveRef.better(cc, ct, init), here),
              SolveRef.better(cc, ct, here), step1, step2),
            Equal.sym(SolveRef.Best,
              Eval.Eval.guess_bool(p, G, S, g, groups, inf, True{}, here),
              SolveRef.better(cc, ct, here), rhs_rewrite))
    case False{}:
      match acc:
        case SolveRef.Best{+ta, +ca}:
          Equal.trans(SolveRef.Best,
            ParElt.apply(Eval.Eval.guess_bool(p, G, S, g, groups, inf, False{},
                                         SolvePar.init_best(inf)),
                         SolveRef.Best{ta, ca}),
            SolveRef.Best{ta, ca},
            Eval.Eval.guess_bool(p, G, S, g, groups, inf, False{},
                            SolveRef.Best{ta, ca}),
            ParElt.init_apply(Tree.Node{Nil{}, Nil{}}, ta, inf, ca, h), {==})

# The same replay step for the guess-level evaluator.
def ParElt.guess_apply(+p: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +g: +List<Nat>, +inf: Nat, +acc: SolveRef.Best,
    h: {Nat.is_le(Eval.Eval.cost_of(acc), inf) == True{} : Bool}) ->
  {ParElt.apply(Eval.Eval.guess(p, G, S, g, inf, SolvePar.init_best(inf)), acc)
   == Eval.Eval.guess(p, G, S, g, inf, acc) : SolveRef.Best}:
  ParElt.guess_bool_apply(p, G, S, g, Groups.groups_build(g, S, Nil{}), inf,
    Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})), acc, h)
