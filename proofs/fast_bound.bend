# The lower bound of a guess is below the cost of its node.
#
# A tree rooted at a guess costs one per candidate at the node plus the cost of
# every class. Every class costs at least one per candidate in it, so
#
#   |S| + sum over classes of |class|   <=   node cost
#
# This module proves that against the search's own candidate cost
# `sat_add inf |S| (class sum)`, from one size fact per class
# (`FS.SizesLe`: a class costs at least its number of candidates) and the
# partition fact that the class sizes sum to at most `|S|`. The size facts and
# the partition bound together also place the bound below the solver's
# infinity, which is the other hypothesis of the pruning rule.
import Base
import ../src/solve_ref.bend as SolveRef
import ../src/solve_fast.bend as SolveFast
import ../src/groups.bend as Groups
import ../src/tree.bend as Tree
import ../src/feedback.bend as Feedback
import ./logic.bend as Logic
import ./nat.bend as NatProof
import ./eval.bend as Eval
import ./sat.bend as Sat
import ./optimalvalue.bend as OV
import ./classbound_sum.bend as CU
import ./classbound_nat.bend as CBN
import ./classbound.bend as CBProof
import ./optfold.bend as Fold

# The class sizes of `groups` sum to the number of candidates in its classes.
def FS.class_words_sum(+groups: +List<Groups.Group>) ->
  {SolveFast.class_words(groups) == CBN.CB.sum(CBProof.CB.sizes(groups)) : Nat}:
  match groups:
    case Nil{}:
      {==}
    case Con{gp, rest}:
      match gp:
        case Groups.Group{f, ws}:
          Equal.cong(Nat, Nat, x => Nat.add(Groups.len_words(ws), x),
            SolveFast.class_words(rest), CBN.CB.sum(CBProof.CB.sizes(rest)),
            FS.class_words_sum(rest))

# Every number is below its square.
def FS.sq_le(m: Nat) -> {Nat.is_le(m, Nat.mul(m, m)) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n++r:
      Fold.OQ.is_le_add_self_r(1n+r, Nat.mul(r, 1n+r))

# A failing `is_lt` is an `is_ge`.
def FS.ge_of_lt_false(a: Nat, b: Nat,
    e: {Nat.is_lt(a, b) == False{} : Bool}) ->
  {Nat.is_ge(a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      Empty.absurd({Nat.is_ge(0n, 1n+bp) == True{} : Bool},
        Logic.Proof.true_ne_false(e))
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      FS.ge_of_lt_false(ap, bp, e)

# Substitution in the first argument of `is_lt`.
def FS.lt_eq_l(+y: Nat, x: Nat, z: Nat, e: {x == z : Nat},
    p: {Nat.is_lt(x, y) == True{} : Bool}) ->
  {Nat.is_lt(z, y) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_lt(z, y), Nat.is_lt(x, y), True{},
    Equal.sym(Bool, Nat.is_lt(x, y), Nat.is_lt(z, y),
      Equal.cong(Nat, Bool, w => Nat.is_lt(w, y), x, z, e)), p)

# Substitution in the second argument of `is_lt`.
def FS.lt_eq_r(+x: Nat, y: Nat, z: Nat, e: {y == z : Nat},
    p: {Nat.is_lt(x, y) == True{} : Bool}) ->
  {Nat.is_lt(x, z) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_lt(x, z), Nat.is_lt(x, y), True{},
    Equal.sym(Bool, Nat.is_lt(x, y), Nat.is_lt(x, z),
      Equal.cong(Nat, Bool, w => Nat.is_lt(x, w), y, z, e)), p)

# The order survives a change of names.
def FS.all_lt_of_costs(+inf: Nat, +cs: +List<Nat>,
    p: Sat.SB.CostsLt(inf, cs)) -> CU.CU.AllLt(inf, cs):
  match cs:
    case Nil{}:
      Unit{}
    case Con{+c, +t}:
      (h, t2) = p
      (h, FS.all_lt_of_costs(inf, t, t2))

# The per-class finiteness facts of a finite class sum.
def FS.items_all_go(+inf: Nat, cs: List<&2, Nat>,
    p: ({Nat.is_lt(0n, inf) == True{} : Bool} & Sat.SB.CostsLt(inf, cs))) ->
  CU.CU.AllLt(inf, cs):
  (h, t) = p
  FS.all_lt_of_costs(inf, cs, t)

def FS.items_all(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +g: +List<Nat>, +groups: +List<Groups.Group>, +inf: Nat,
    +slt: {Nat.is_lt(Sat.SB.ks_sum(Eval.Eval.items(p, G, S, g, groups,
              Nil{}, 0n, inf)), inf) == True{} : Bool}) ->
  CU.CU.AllLt(inf, Sat.SB.child_costs(p, G, groups, inf)):
  FS.items_all_go(inf, Sat.SB.child_costs(p, G, groups, inf),
    Sat.SB.items_lt(p, G, S, g, groups, Nil{}, 0n, inf, slt))

# The candidate cost is the saturating sum of the candidate count and the
# class sum.
def FS.ks_cost_eq(+inf: Nat, +S: +List<+List<Nat>>, ks: Eval.KS) ->
  {Fold.OQ.ks_cost(inf, S, ks)
   == SolveRef.sat_add(inf, Groups.len_words(S), Sat.SB.ks_sum(ks)) : Nat}:
  match ks:
    case Eval.KS{kids, +sum}:
      {==}

# The plain-sum half of `CU.sumL_both`.
def FS.sumL_plain(+inf: Nat, cs: List<&2, Nat>, +acc: Nat,
    +tot: {Nat.is_lt(Nat.add(acc, CBN.CB.sum(cs)), inf) == True{} : Bool},
    all: CU.CU.AllLt(inf, cs)) ->
  {OV.OV.sumL(inf, cs, acc) == Nat.add(acc, CBN.CB.sum(cs)) : Nat}:
  CU.CU.use_pair(
    {OV.OV.sumL(inf, cs, acc) == Nat.add(acc, CBN.CB.sum(cs)) : Nat},
    {OV.OV.sumL(inf, cs, acc) == Nat.add(acc, CBN.CB.sum(cs)) : Nat},
    {CU.CU.madds(inf, cs) == Some{CBN.CB.sum(cs)} : Maybe<&2, Nat>},
    CU.CU.sumL_both(inf, cs, acc, tot, all),
    h => t => h)

# A finite saturating sum is the plain sum.
def FS.sat_fin_go(+inf: Nat, +a: Nat, +b: Nat,
    +la: {Nat.is_lt(a, inf) == True{} : Bool},
    +lb: {Nat.is_lt(b, inf) == True{} : Bool}) ->
  {SolveRef.sat_add(inf, a, b) == Nat.add(a, b) : Nat}:
  OV.OV.sat_fin(inf, a, b,
    OV.OV.ge_false_of_lt(a, inf, la), OV.OV.ge_false_of_lt(b, inf, lb))

# An infinite left argument makes the sum infinite.
def FS.sat_ge_l(+inf: Nat, +a: Nat, +b: Nat,
    +e: {Nat.is_ge(a, inf) == True{} : Bool}) ->
  {SolveRef.sat_add(inf, a, b) == inf : Nat}:
  Equal.cong(Bool, Nat,
    x => Feedback.Bool.case(Nat, x, inf,
      Feedback.Bool.case(Nat, Nat.is_ge(b, inf), inf, Nat.add(a, b))),
    Nat.is_ge(a, inf), True{}, e)

# An infinite right argument makes the sum infinite.
def FS.sat_ge_r(+inf: Nat, +a: Nat, +b: Nat,
    +ea: {Nat.is_ge(a, inf) == False{} : Bool},
    +eb: {Nat.is_ge(b, inf) == True{} : Bool}) ->
  {SolveRef.sat_add(inf, a, b) == inf : Nat}:
  +e1 : {SolveRef.sat_add(inf, a, b)
         == Feedback.Bool.case(Nat, Nat.is_ge(b, inf), inf, Nat.add(a, b)) : Nat} =
    Equal.cong(Bool, Nat,
      x => Feedback.Bool.case(Nat, x, inf,
        Feedback.Bool.case(Nat, Nat.is_ge(b, inf), inf, Nat.add(a, b))),
      Nat.is_ge(a, inf), False{}, ea)
  Equal.trans(Nat, SolveRef.sat_add(inf, a, b),
    Feedback.Bool.case(Nat, Nat.is_ge(b, inf), inf, Nat.add(a, b)), inf, e1,
    Equal.cong(Bool, Nat,
      y => Feedback.Bool.case(Nat, y, inf, Nat.add(a, b)),
      Nat.is_ge(b, inf), True{}, eb))

# A finite saturating fold has a finite plain sum.
def FS.sumL_lt_plain(+inf: Nat, xs: List<&2, Nat>, +sum: Nat,
    +e: {Nat.is_lt(OV.OV.sumL(inf, xs, sum), inf) == True{} : Bool}) ->
  {Nat.is_lt(Nat.add(sum, CBN.CB.sum(xs)), inf) == True{} : Bool}:
  match xs:
    case Nil{}:
      FS.lt_eq_l(inf, sum, Nat.add(sum, 0n),
        Equal.sym(Nat, Nat.add(sum, 0n), sum, NatProof.NatPrf.add_zero(sum)), e)
    case Con{+c, +t}:
      +ep : {Nat.is_lt(OV.OV.sumL(inf, t, SolveRef.sat_add(inf, sum, c)), inf)
             == True{} : Bool} = e
      +ih : {Nat.is_lt(Nat.add(SolveRef.sat_add(inf, sum, c), CBN.CB.sum(t)), inf)
             == True{} : Bool} =
        FS.sumL_lt_plain(inf, t, SolveRef.sat_add(inf, sum, c), ep)
      +slt : {Nat.is_lt(SolveRef.sat_add(inf, sum, c), inf) == True{} : Bool} =
        CU.CU.acc_part_lt(inf, SolveRef.sat_add(inf, sum, c), t, ih)
      +sl : {Nat.is_lt(sum, inf) == True{} : Bool} = Sat.SB.sat_add_lt_l(inf, sum, c, slt)
      +cl : {Nat.is_lt(c, inf) == True{} : Bool} = Sat.SB.sat_add_lt_r(inf, sum, c, slt)
      +esat : {SolveRef.sat_add(inf, sum, c) == Nat.add(sum, c) : Nat} =
        FS.sat_fin_go(inf, sum, c, sl, cl)
      +esumcong : {Nat.add(SolveRef.sat_add(inf, sum, c), CBN.CB.sum(t))
                   == Nat.add(Nat.add(sum, c), CBN.CB.sum(t)) : Nat} =
        Equal.cong(Nat, Nat, w => Nat.add(w, CBN.CB.sum(t)),
          SolveRef.sat_add(inf, sum, c), Nat.add(sum, c), esat)
      +ih2 : {Nat.is_lt(Nat.add(Nat.add(sum, c), CBN.CB.sum(t)), inf) == True{} : Bool} =
        FS.lt_eq_l(inf, Nat.add(SolveRef.sat_add(inf, sum, c), CBN.CB.sum(t)),
          Nat.add(Nat.add(sum, c), CBN.CB.sum(t)), esumcong, ih)
      FS.lt_eq_l(inf, Nat.add(Nat.add(sum, c), CBN.CB.sum(t)),
        Nat.add(sum, Nat.add(c, CBN.CB.sum(t))),
        NatProof.NatPrf.add_assoc(sum, c, CBN.CB.sum(t)), ih2)

# The class bounds `CB.fits_inf` asks for, read off `groups_smaller`.
def FS.class_bounds(+S: +List<+List<Nat>>, +groups: +List<Groups.Group>,
    +e: {Groups.groups_smaller(S, groups) == True{} : Bool}) ->
  CBProof.CB.Bounds(Groups.len_words(S), groups, CBProof.CB.sizes(groups)):
  match groups:
    case Nil{}:
      Unit{}
    case Con{gp, rest}:
      match gp:
        case Groups.Group{+f, +ws}:
          +lt : {Nat.is_lt(Groups.len_words(ws), Groups.len_words(S)) == True{} : Bool} =
            Logic.Proof.and_true_l(Nat.is_lt(Groups.len_words(ws), Groups.len_words(S)),
              Groups.groups_smaller(S, rest), e)
          +sm : {Groups.groups_smaller(S, rest) == True{} : Bool} =
            Logic.Proof.and_true_r(Nat.is_lt(Groups.len_words(ws), Groups.len_words(S)),
              Groups.groups_smaller(S, rest), e)
          (lt, (FS.sq_le(Groups.len_words(ws)),
                FS.class_bounds(S, rest, sm)))

# The lower bound over a guess's classes fits below the solver's infinity.
def FS.lb_fits(+N: Nat, +S: +List<+List<Nat>>, +g: +List<Nat>,
    +us: {Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})) == True{}
         : Bool},
    +leN: {Nat.is_le(Groups.len_words(S), N) == True{} : Bool}) ->
  {Nat.is_le(
      SolveFast.lower_bound(Groups.len_words(S), Groups.groups_build(g, S, Nil{})),
      Nat.add(Nat.mul(N, N), 1n)) == True{} : Bool}:
  +grp : +List<Groups.Group> = Groups.groups_build(g, S, Nil{})
  +cw : {SolveFast.class_words(grp) == CBN.CB.sum(CBProof.CB.sizes(grp)) : Nat} =
    FS.class_words_sum(grp)
  +lt : {Nat.is_lt(Nat.add(Groups.len_words(S), CBN.CB.sum(CBProof.CB.sizes(grp))),
             Nat.add(Nat.mul(N, N), 1n)) == True{} : Bool} =
    CBProof.CB.fits_inf_classes(N, S, g, CBProof.CB.sizes(grp),
      FS.class_bounds(S, grp, us), leN)
  +le : {Nat.is_le(Nat.add(Groups.len_words(S), CBN.CB.sum(CBProof.CB.sizes(grp))),
             Nat.add(Nat.mul(N, N), 1n)) == True{} : Bool} =
    NatProof.Nat.is_le_of_lt(Nat.add(Groups.len_words(S), CBN.CB.sum(CBProof.CB.sizes(grp))),
      Nat.add(Nat.mul(N, N), 1n), lt)
  +cw2 : {SolveFast.lower_bound(Groups.len_words(S), grp)
          == Nat.add(Groups.len_words(S), CBN.CB.sum(CBProof.CB.sizes(grp))) : Nat} =
    Equal.cong(Nat, Nat, x => Nat.add(Groups.len_words(S), x),
      SolveFast.class_words(grp), CBN.CB.sum(CBProof.CB.sizes(grp)), cw)
  NatProof.Nat.is_le_eq_l(Nat.add(Nat.mul(N, N), 1n),
    Nat.add(Groups.len_words(S), CBN.CB.sum(CBProof.CB.sizes(grp))),
    SolveFast.lower_bound(Groups.len_words(S), grp),
    Equal.sym(Nat, SolveFast.lower_bound(Groups.len_words(S), grp),
      Nat.add(Groups.len_words(S), CBN.CB.sum(CBProof.CB.sizes(grp))), cw2),
    le)

# One size fact per class: the class costs at least its candidates.
def FS.SizesLe(+p: Nat, +G: +List<+List<Nat>>, +inf: Nat,
    +groups: +List<Groups.Group>) -> Type:
  match groups:
    case Nil{}:
      Unit
    case Con{gp, rest}:
      match gp:
        case Groups.Group{f, ws}:
          {Nat.is_le(Groups.len_words(ws), Sat.SB.child_cost(p, G, ws, inf))
           == True{} : Bool}
          & FS.SizesLe(p, G, inf, rest)

# The pointwise order between the class sizes and the class costs.
def FS.size_le_costs(+p: Nat, +G: +List<+List<Nat>>, +inf: Nat,
    +groups: +List<Groups.Group>, facts: FS.SizesLe(p, G, inf, groups)) ->
  CBN.CB.PointLe(CBProof.CB.sizes(groups), Sat.SB.child_costs(p, G, groups, inf)):
  match groups:
    case Nil{}:
      Unit{}
    case Con{gp, rest}:
      match gp:
        case Groups.Group{+f, +ws}:
          (h, t) = facts
          (h, FS.size_le_costs(p, G, inf, rest, t))

# The bound under the two finiteness facts: the plain class sum is at most the
# class costs, and the candidate cost is the plain sum.
def FS.lb_fin(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +g: +List<Nat>, +inf: Nat, +groups: +List<Groups.Group>,
    facts: FS.SizesLe(p, G, inf, groups),
    +nlt: {Nat.is_lt(Groups.len_words(S), inf) == True{} : Bool},
    +slt: {Nat.is_lt(Sat.SB.ks_sum(Eval.Eval.items(p, G, S, g, groups,
              Nil{}, 0n, inf)), inf) == True{} : Bool}) ->
  {Nat.is_le(SolveFast.lower_bound(Groups.len_words(S), groups),
      Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf)))
   == True{} : Bool}:
  +items : Eval.KS = Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf)
  +costs : List<&2, Nat> = Sat.SB.child_costs(p, G, groups, inf)
  +sizes : List<&2, Nat> = CBProof.CB.sizes(groups)
  +lb : Nat = SolveFast.lower_bound(Groups.len_words(S), groups)
  +cand : Nat = Fold.OQ.ks_cost(inf, S, items)
  +cw : {lb == Nat.add(Groups.len_words(S), CBN.CB.sum(sizes)) : Nat} =
    Equal.cong(Nat, Nat, x => Nat.add(Groups.len_words(S), x),
      SolveFast.class_words(groups), CBN.CB.sum(sizes),
      FS.class_words_sum(groups))
  +sum_fold : {Sat.SB.ks_sum(items) == OV.OV.sumL(inf, costs, 0n) : Nat} =
    OV.OV.sum_fold(p, G, S, g, groups, Nil{}, 0n, inf)
  +f_lt : {Nat.is_lt(OV.OV.sumL(inf, costs, 0n), inf) == True{} : Bool} =
    FS.lt_eq_l(inf, Sat.SB.ks_sum(items), OV.OV.sumL(inf, costs, 0n),
      sum_fold, slt)
  +plain : {Nat.is_lt(Nat.add(0n, CBN.CB.sum(costs)), inf) == True{} : Bool} =
    FS.sumL_lt_plain(inf, costs, 0n, f_lt)
  all : CU.CU.AllLt(inf, costs) = FS.items_all(p, G, S, g, groups, inf, slt)
  +both : {OV.OV.sumL(inf, costs, 0n) == CBN.CB.sum(costs) : Nat} =
    FS.sumL_plain(inf, costs, 0n, plain, all)
  +esum : {Sat.SB.ks_sum(items) == CBN.CB.sum(costs) : Nat} =
    Equal.trans(Nat, Sat.SB.ks_sum(items), OV.OV.sumL(inf, costs, 0n),
      CBN.CB.sum(costs), sum_fold, both)
  +esat : {SolveRef.sat_add(inf, Groups.len_words(S), Sat.SB.ks_sum(items))
           == Nat.add(Groups.len_words(S), Sat.SB.ks_sum(items)) : Nat} =
    FS.sat_fin_go(inf, Groups.len_words(S), Sat.SB.ks_sum(items), nlt, slt)
  +esat2 : {SolveRef.sat_add(inf, Groups.len_words(S), Sat.SB.ks_sum(items))
            == Nat.add(Groups.len_words(S), CBN.CB.sum(costs)) : Nat} =
    Equal.trans(Nat,
      SolveRef.sat_add(inf, Groups.len_words(S), Sat.SB.ks_sum(items)),
      Nat.add(Groups.len_words(S), Sat.SB.ks_sum(items)),
      Nat.add(Groups.len_words(S), CBN.CB.sum(costs)), esat,
      Equal.cong(Nat, Nat, x => Nat.add(Groups.len_words(S), x),
        Sat.SB.ks_sum(items), CBN.CB.sum(costs), esum))
  +ecand : {cand == Nat.add(Groups.len_words(S), CBN.CB.sum(costs)) : Nat} =
    Equal.trans(Nat, cand,
      SolveRef.sat_add(inf, Groups.len_words(S), Sat.SB.ks_sum(items)),
      Nat.add(Groups.len_words(S), CBN.CB.sum(costs)),
      FS.ks_cost_eq(inf, S, items), esat2)
  +slice : {Nat.is_le(CBN.CB.sum(sizes), CBN.CB.sum(costs)) == True{} : Bool} =
    CBN.CB.sum_le(sizes, costs, FS.size_le_costs(p, G, inf, groups, facts))
  +mono : {Nat.is_le(Nat.add(Groups.len_words(S), CBN.CB.sum(sizes)),
             Nat.add(Groups.len_words(S), CBN.CB.sum(costs))) == True{} : Bool} =
    NatProof.Nat.is_le_add_l(CBN.CB.sum(sizes), CBN.CB.sum(costs),
      Groups.len_words(S), slice)
  +left : {Nat.is_le(lb, Nat.add(Groups.len_words(S), CBN.CB.sum(costs)))
           == True{} : Bool} =
    NatProof.Nat.is_le_eq_l(Nat.add(Groups.len_words(S), CBN.CB.sum(costs)),
      Nat.add(Groups.len_words(S), CBN.CB.sum(sizes)), lb,
      Equal.sym(Nat, lb, Nat.add(Groups.len_words(S), CBN.CB.sum(sizes)), cw),
      mono)
  NatProof.Nat.is_le_eq_r(lb, Nat.add(Groups.len_words(S), CBN.CB.sum(costs)),
    cand,
    Equal.sym(Nat, cand, Nat.add(Groups.len_words(S), CBN.CB.sum(costs)), ecand),
    left)

# The candidate count is infinite, so the candidate cost is infinity.
def FS.lb_inf_l(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +g: +List<Nat>, +inf: Nat, +groups: +List<Groups.Group>,
    +hinf: {Nat.is_le(SolveFast.lower_bound(Groups.len_words(S), groups), inf)
            == True{} : Bool},
    +nge: {Nat.is_ge(Groups.len_words(S), inf) == True{} : Bool}) ->
  {Nat.is_le(SolveFast.lower_bound(Groups.len_words(S), groups),
      Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf)))
   == True{} : Bool}:
  +items : Eval.KS = Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf)
  +inf_eq : {SolveRef.sat_add(inf, Groups.len_words(S), Sat.SB.ks_sum(items))
             == inf : Nat} =
    FS.sat_ge_l(inf, Groups.len_words(S), Sat.SB.ks_sum(items), nge)
  +ecand : {Fold.OQ.ks_cost(inf, S, items) == inf : Nat} =
    Equal.trans(Nat, Fold.OQ.ks_cost(inf, S, items),
      SolveRef.sat_add(inf, Groups.len_words(S), Sat.SB.ks_sum(items)),
      inf, FS.ks_cost_eq(inf, S, items), inf_eq)
  NatProof.Nat.is_le_eq_r(SolveFast.lower_bound(Groups.len_words(S), groups),
    inf, Fold.OQ.ks_cost(inf, S, items),
    Equal.sym(Nat, Fold.OQ.ks_cost(inf, S, items), inf, ecand), hinf)

# The class sum is infinite, so the candidate cost is infinity.
def FS.lb_inf_r(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +g: +List<Nat>, +inf: Nat, +groups: +List<Groups.Group>,
    +hinf: {Nat.is_le(SolveFast.lower_bound(Groups.len_words(S), groups), inf)
            == True{} : Bool},
    +nlt: {Nat.is_lt(Groups.len_words(S), inf) == True{} : Bool},
    +sge: {Nat.is_ge(Sat.SB.ks_sum(Eval.Eval.items(p, G, S, g, groups,
              Nil{}, 0n, inf)), inf) == True{} : Bool}) ->
  {Nat.is_le(SolveFast.lower_bound(Groups.len_words(S), groups),
      Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf)))
   == True{} : Bool}:
  +items : Eval.KS = Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf)
  +inf_eq : {SolveRef.sat_add(inf, Groups.len_words(S), Sat.SB.ks_sum(items))
             == inf : Nat} =
    FS.sat_ge_r(inf, Groups.len_words(S), Sat.SB.ks_sum(items),
      OV.OV.ge_false_of_lt(Groups.len_words(S), inf, nlt), sge)
  +ecand : {Fold.OQ.ks_cost(inf, S, items) == inf : Nat} =
    Equal.trans(Nat, Fold.OQ.ks_cost(inf, S, items),
      SolveRef.sat_add(inf, Groups.len_words(S), Sat.SB.ks_sum(items)),
      inf, FS.ks_cost_eq(inf, S, items), inf_eq)
  NatProof.Nat.is_le_eq_r(SolveFast.lower_bound(Groups.len_words(S), groups),
    inf, Fold.OQ.ks_cost(inf, S, items),
    Equal.sym(Nat, Fold.OQ.ks_cost(inf, S, items), inf, ecand), hinf)

# The lower bound is below the candidate cost of the guess.
#
# The two `Bool`s are the finiteness decisions of the candidate count and of the
# class sum; they are parameters because a computed comparison cannot be matched
# in a proof, and the caller passes the comparisons themselves.
def FS.lb_le_cand(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +g: +List<Nat>, +inf: Nat, +groups: +List<Groups.Group>,
    facts: FS.SizesLe(p, G, inf, groups),
    +hinf: {Nat.is_le(SolveFast.lower_bound(Groups.len_words(S), groups), inf)
            == True{} : Bool},
    ln: Bool, +eln: {ln == Nat.is_lt(Groups.len_words(S), inf) : Bool},
    lsum: Bool, +elsum: {lsum == Nat.is_lt(
            Sat.SB.ks_sum(Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf)), inf)
          : Bool}) ->
  {Nat.is_le(SolveFast.lower_bound(Groups.len_words(S), groups),
      Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf)))
   == True{} : Bool}:
  match ln:
    case True{}:
      match lsum:
        case True{}:
          FS.lb_fin(p, G, S, g, inf, groups, facts,
            Equal.sym(Bool, True{}, Nat.is_lt(Groups.len_words(S), inf), eln),
            Equal.sym(Bool, True{}, Nat.is_lt(Sat.SB.ks_sum(Eval.Eval.items(p, G, S,
              g, groups, Nil{}, 0n, inf)), inf), elsum))
        case False{}:
          FS.lb_inf_r(p, G, S, g, inf, groups, hinf,
            Equal.sym(Bool, True{}, Nat.is_lt(Groups.len_words(S), inf), eln),
            FS.ge_of_lt_false(Sat.SB.ks_sum(Eval.Eval.items(p, G, S, g, groups,
              Nil{}, 0n, inf)), inf,
              Equal.sym(Bool, False{}, Nat.is_lt(Sat.SB.ks_sum(Eval.Eval.items(p, G,
                S, g, groups, Nil{}, 0n, inf)), inf), elsum)))
    case False{}:
      FS.lb_inf_l(p, G, S, g, inf, groups, hinf,
        FS.ge_of_lt_false(Groups.len_words(S), inf,
          Equal.sym(Bool, False{}, Nat.is_lt(Groups.len_words(S), inf), eln)))
