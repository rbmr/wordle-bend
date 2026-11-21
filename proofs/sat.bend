# Satisfying addition and the accumulated cost of a guess.
#
# `sat_add inf a b` is infinity whenever either side is, and the sum otherwise.
# The guess loop accumulates a running sum with it. The lemmas here say that a
# finite accumulated sum means every part is finite, which turns a finite guess
# cost into finite, valid child costs.
import Base
import ../src/solve_ref.bend as SolveRef
import ../src/groups.bend as Groups
import ../src/tree.bend as Tree
import ../src/feedback.bend as Feedback
import ./logic.bend as Logic
import ./nat.bend as NatProof
import ./eval.bend as Eval

# The comparison is a parameter so the proof can match it.
def SB.lt_of_ge_false_go(a: Nat, b: Nat, c: Cmp,
    +ec: {c == Nat.cmp(a, b) : Cmp},
    e: {Nat.is_ge(a, b) == False{} : Bool}) ->
  {Nat.is_lt(a, b) == True{} : Bool}:
  match c:
    case LT{}:
      %ec : {Cmp.is_lt(_) == True{} : Bool}
      {==}
    case EQ{}:
      +e2 : {Cmp.is_ge(EQ{}) == False{} : Bool} =
        Equal.trans(Bool, Cmp.is_ge(EQ{}), Cmp.is_ge(Nat.cmp(a, b)), False{},
          Equal.cong(Cmp, Bool, Cmp.is_ge, EQ{}, Nat.cmp(a, b), ec), e)
      Empty.absurd({Nat.is_lt(a, b) == True{} : Bool}, Logic.Proof.true_ne_false(e2))
    case GT{}:
      +e2 : {Cmp.is_ge(GT{}) == False{} : Bool} =
        Equal.trans(Bool, Cmp.is_ge(GT{}), Cmp.is_ge(Nat.cmp(a, b)), False{},
          Equal.cong(Cmp, Bool, Cmp.is_ge, GT{}, Nat.cmp(a, b), ec), e)
      Empty.absurd({Nat.is_lt(a, b) == True{} : Bool}, Logic.Proof.true_ne_false(e2))

def SB.lt_of_ge_false(+a: Nat, +b: Nat,
    e: {Nat.is_ge(a, b) == False{} : Bool}) ->
  {Nat.is_lt(a, b) == True{} : Bool}:
  SB.lt_of_ge_false_go(a, b, Nat.cmp(a, b), {==}, e)

def SB.sat_add_lt_l_go(+inf: Nat, +a: Nat, +b: Nat, +ga: Bool, +gb: Bool,
    +ea: {ga == Nat.is_ge(a, inf) : Bool},
    +eb: {gb == Nat.is_ge(b, inf) : Bool},
    +e: {Nat.is_lt(Feedback.Bool.case(Nat, ga, inf,
                            Feedback.Bool.case(Nat, gb, inf, Nat.add(a, b))), inf) == True{} : Bool}) ->
  {Nat.is_lt(a, inf) == True{} : Bool}:
  match ga:
    case True{}:
      Empty.absurd({Nat.is_lt(a, inf) == True{} : Bool},
                   NatProof.Nat.not_lt_self(inf, e))
    case False{}:
      SB.lt_of_ge_false(a, inf, Equal.sym(Bool, False{}, Nat.is_ge(a, inf), ea))

def SB.sat_add_lt_l(+inf: Nat, +a: Nat, +b: Nat,
    +e: {Nat.is_lt(SolveRef.sat_add(inf, a, b), inf) == True{} : Bool}) ->
  {Nat.is_lt(a, inf) == True{} : Bool}:
  SB.sat_add_lt_l_go(inf, a, b, Nat.is_ge(a, inf), Nat.is_ge(b, inf), {==}, {==}, e)

def SB.sat_add_lt_r_go(+inf: Nat, +a: Nat, +b: Nat, +ga: Bool, +gb: Bool,
    +ea: {ga == Nat.is_ge(a, inf) : Bool},
    +eb: {gb == Nat.is_ge(b, inf) : Bool},
    +e: {Nat.is_lt(Feedback.Bool.case(Nat, ga, inf,
                            Feedback.Bool.case(Nat, gb, inf, Nat.add(a, b))), inf) == True{} : Bool}) ->
  {Nat.is_lt(b, inf) == True{} : Bool}:
  match ga:
    case True{}:
      Empty.absurd({Nat.is_lt(b, inf) == True{} : Bool},
                   NatProof.Nat.not_lt_self(inf, e))
    case False{}:
      match gb:
        case True{}:
          Empty.absurd({Nat.is_lt(b, inf) == True{} : Bool},
                       NatProof.Nat.not_lt_self(inf, e))
        case False{}:
          SB.lt_of_ge_false(b, inf, Equal.sym(Bool, False{}, Nat.is_ge(b, inf), eb))

def SB.sat_add_lt_r(+inf: Nat, +a: Nat, +b: Nat,
    +e: {Nat.is_lt(SolveRef.sat_add(inf, a, b), inf) == True{} : Bool}) ->
  {Nat.is_lt(b, inf) == True{} : Bool}:
  SB.sat_add_lt_r_go(inf, a, b, Nat.is_ge(a, inf), Nat.is_ge(b, inf), {==}, {==}, e)

def SB.ks_sum(ks: Eval.KS) -> Nat:
  match ks:
    case Eval.KS{kids, +sum}:
      sum

# The cost of one group's child search.
def SB.child_cost(+p: Nat, +G: +List<+List<Nat>>, +ws: +List<+List<Nat>>,
    +inf: Nat) -> Nat:
  Eval.Eval.cost_of(SolveRef.step(p, SolveRef.mk_schedule(G, ws), G, ws, inf,
    Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero()))

# Every cost in the list is finite.
def SB.CostsLt(+inf: Nat, +costs: +List<Nat>) -> Type:
  match costs:
    case Nil{}:
      Unit
    case Con{c, t}:
      {Nat.is_lt(c, inf) == True{} : Bool} & SB.CostsLt(inf, t)

def SB.child_costs(+p: Nat, +G: +List<+List<Nat>>, +groups: +List<Groups.Group>,
    +inf: Nat) -> +List<Nat>:
  match groups:
    case Nil{}:
      Nil{}
    case Con{gp, rest}:
      match gp:
        case Groups.Group{fb, ws}:
          SB.child_cost(p, G, ws, inf) <> SB.child_costs(p, G, rest, inf)

def SB.children_lt(+p: Nat, +G: +List<+List<Nat>>, +groups: +List<Groups.Group>,
    +inf: Nat) -> Type:
  SB.CostsLt(inf, SB.child_costs(p, G, groups, inf))


def SB.both_use(-A: Type, -B: Type, C: Type, pair: A & B,
    k: A -> B -> C) -> C:
  match pair:
    case (a, b):
      k(a, b)

# One group of the accumulated sum. The child result is never matched: the
# child cost is read with `cost_of`, so the induction hypothesis and the two
# saturating bounds all talk about the same expression.
def SB.items_cons_lt(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +g: +List<Nat>, +fb: +List<Feedback.Color>, +ws: +List<+List<Nat>>,
    +rest: +List<Groups.Group>, +kids: +List<Tree.Child>, +sum: Nat, +inf: Nat,
    +pending: SolveRef.Best,
    k: @k2: +List<Tree.Child> -> @s2: Nat ->
       {Nat.is_lt(SB.ks_sum(Eval.Eval.items(p, G, S, g, rest, k2, s2, inf)), inf) == True{} : Bool}
       -> ({Nat.is_lt(s2, inf) == True{} : Bool} & SB.CostsLt(inf, SB.child_costs(p, G, rest, inf))),
    +e: {Nat.is_lt(SB.ks_sum(Eval.Eval.with_kid(fb, kids, sum, inf, pending,
          k2 => s2 => Eval.Eval.items(p, G, S, g, rest, k2, s2, inf))), inf) == True{} : Bool}) ->
  {Nat.is_lt(sum, inf) == True{} : Bool}
  & SB.CostsLt(inf, Eval.Eval.cost_of(pending) <> SB.child_costs(p, G, rest, inf)):
  +eq : {Eval.Eval.with_kid(fb, kids, sum, inf, pending,
            k2 => s2 => Eval.Eval.items(p, G, S, g, rest, k2, s2, inf))
         == (k2 => s2 => Eval.Eval.items(p, G, S, g, rest, k2, s2, inf))(
              Tree.Child{fb, Eval.Eval.tree_of(pending)} <> kids,
              SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(pending)))
         : Eval.KS} =
    Eval.Eval.with_kid_eq(fb, kids, sum, inf, pending,
      k2 => s2 => Eval.Eval.items(p, G, S, g, rest, k2, s2, inf))
  +e_eq : {SB.ks_sum(Eval.Eval.items(p, G, S, g, rest,
                Tree.Child{fb, Eval.Eval.tree_of(pending)} <> kids,
                SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(pending)), inf))
           == SB.ks_sum(Eval.Eval.with_kid(fb, kids, sum, inf, pending,
                k2 => s2 => Eval.Eval.items(p, G, S, g, rest, k2, s2, inf)))
           : Nat} =
    Equal.sym(Nat,
      SB.ks_sum(Eval.Eval.with_kid(fb, kids, sum, inf, pending,
        k2 => s2 => Eval.Eval.items(p, G, S, g, rest, k2, s2, inf))),
      SB.ks_sum(Eval.Eval.items(p, G, S, g, rest,
        Tree.Child{fb, Eval.Eval.tree_of(pending)} <> kids,
        SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(pending)), inf)),
      Equal.cong(Eval.KS, Nat, SB.ks_sum,
        Eval.Eval.with_kid(fb, kids, sum, inf, pending,
          k2 => s2 => Eval.Eval.items(p, G, S, g, rest, k2, s2, inf)),
        Eval.Eval.items(p, G, S, g, rest,
          Tree.Child{fb, Eval.Eval.tree_of(pending)} <> kids,
          SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(pending)), inf), eq))
  +e2 : {Nat.is_lt(SB.ks_sum(Eval.Eval.items(p, G, S, g, rest,
              Tree.Child{fb, Eval.Eval.tree_of(pending)} <> kids,
              SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(pending)), inf)), inf)
          == Nat.is_lt(SB.ks_sum(Eval.Eval.with_kid(fb, kids, sum, inf, pending,
              k2 => s2 => Eval.Eval.items(p, G, S, g, rest, k2, s2, inf))), inf)
          : Bool} =
    Equal.cong(Nat, Bool, n => Nat.is_lt(n, inf),
      SB.ks_sum(Eval.Eval.items(p, G, S, g, rest,
        Tree.Child{fb, Eval.Eval.tree_of(pending)} <> kids,
        SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(pending)), inf)),
      SB.ks_sum(Eval.Eval.with_kid(fb, kids, sum, inf, pending,
        k2 => s2 => Eval.Eval.items(p, G, S, g, rest, k2, s2, inf))), e_eq)
  +e3 : {Nat.is_lt(SB.ks_sum(Eval.Eval.items(p, G, S, g, rest,
              Tree.Child{fb, Eval.Eval.tree_of(pending)} <> kids,
              SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(pending)), inf)), inf)
          == True{} : Bool} =
    Equal.trans(Bool,
      Nat.is_lt(SB.ks_sum(Eval.Eval.items(p, G, S, g, rest,
        Tree.Child{fb, Eval.Eval.tree_of(pending)} <> kids,
        SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(pending)), inf)), inf),
      Nat.is_lt(SB.ks_sum(Eval.Eval.with_kid(fb, kids, sum, inf, pending,
        k2 => s2 => Eval.Eval.items(p, G, S, g, rest, k2, s2, inf))), inf),
      True{}, e2, e)
  SB.both_use({Nat.is_lt(SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(pending)), inf)
               == True{} : Bool},
              SB.CostsLt(inf, SB.child_costs(p, G, rest, inf)),
              {Nat.is_lt(sum, inf) == True{} : Bool}
              & SB.CostsLt(inf, Eval.Eval.cost_of(pending)
                  <> SB.child_costs(p, G, rest, inf)),
              k(Tree.Child{fb, Eval.Eval.tree_of(pending)} <> kids,
                SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(pending)), e3),
              +slt => clt =>
                (SB.sat_add_lt_l(inf, sum, Eval.Eval.cost_of(pending), slt),
                 (SB.sat_add_lt_r(inf, sum, Eval.Eval.cost_of(pending), slt), clt)))

# A finite final sum has a finite start and finite child costs.
def SB.items_lt(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +g: +List<Nat>, +groups: +List<Groups.Group>, +kids: +List<Tree.Child>,
    +sum: Nat, +inf: Nat,
    +e: {Nat.is_lt(SB.ks_sum(Eval.Eval.items(p, G, S, g, groups, kids, sum, inf)), inf)
         == True{} : Bool}) ->
  {Nat.is_lt(sum, inf) == True{} : Bool} & SB.CostsLt(inf, SB.child_costs(p, G, groups, inf)):
  match groups:
    case Nil{}:
      (e, Unit{})
    case Con{gp, rest}:
      match gp:
        case Groups.Group{+fb, +ws}:
          SB.items_cons_lt(p, G, S, g, fb, ws, rest, kids, sum, inf,
            SolveRef.step(p, SolveRef.mk_schedule(G, ws), G, ws, inf,
              Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero()),
            k2 => s2 => e2 => SB.items_lt(p, G, S, g, rest, k2, s2, inf, e2),
            e)
