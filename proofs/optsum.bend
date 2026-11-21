# The class sums of one guess, in plain `Nat` order.
#
# The guess fold adds the class results with the saturating sum. For the
# optimality bound the saturated sum has to be compared with the children's
# cost total of a valid node: the fold is below the total whenever every class
# result is below its child's cost. The two facts are stated as `Bool`
# equalities so the proof can reuse them.
import Base
import ../src/solve_ref.bend as SolveRef
import ../src/tree.bend as Tree
import ../src/groups.bend as Groups
import ../src/feedback.bend as Feedback
import ./logic.bend as Logic
import ./nat.bend as NatProof
import ./eval.bend as Eval
import ./sat.bend as Sat
import ./groupcost.bend as GC
import ./optimalvalue.bend as OV
import ./optfold.bend as Fold

# The saturated sum is below the plain sum of its arguments.
def OQ.sat_add_le_add_go(+inf: Nat, +a: Nat, +b: Nat, ga: Bool, gb: Bool,
    +ea: {ga == Nat.is_ge(a, inf) : Bool},
    +eb: {gb == Nat.is_ge(b, inf) : Bool}) ->
  {Nat.is_le(Feedback.Bool.case(Nat, ga, inf,
      Feedback.Bool.case(Nat, gb, inf, Nat.add(a, b))), Nat.add(a, b))
   == True{} : Bool}:
  match ga:
    case True{}:
      +ge : {Nat.is_ge(a, inf) == True{} : Bool} =
        Equal.sym(Bool, ga, Nat.is_ge(a, inf), ea)
      +le_a : {Nat.is_le(a, Nat.add(a, b)) == True{} : Bool} =
        Fold.OQ.is_le_add_self_r(a, b)
      NatProof.Nat.is_le_trans(inf, a, Nat.add(a, b),
        Fold.OQ.is_le_of_ge(a, inf, ge), le_a)
    case False{}:
      match gb:
        case True{}:
          +ge : {Nat.is_ge(b, inf) == True{} : Bool} =
            Equal.sym(Bool, gb, Nat.is_ge(b, inf), eb)
          NatProof.Nat.is_le_trans(inf, b, Nat.add(a, b),
            Fold.OQ.is_le_of_ge(b, inf, ge),
            NatProof.Nat.is_le_add_self_l(a, b))
        case False{}:
          NatProof.Nat.is_le_refl(Nat.add(a, b))

# The saturated sum is below the plain sum of its arguments.
def OQ.sat_add_le_add(+inf: Nat, +a: Nat, +b: Nat) ->
  {Nat.is_le(SolveRef.sat_add(inf, a, b), Nat.add(a, b)) == True{} : Bool}:
  +u : {SolveRef.sat_add(inf, a, b)
        == Feedback.Bool.case(Nat, Nat.is_ge(a, inf), inf,
             Feedback.Bool.case(Nat, Nat.is_ge(b, inf), inf, Nat.add(a, b)))
        : Nat} = {==}
  Equal.trans(Bool,
    Nat.is_le(SolveRef.sat_add(inf, a, b), Nat.add(a, b)),
    Nat.is_le(Feedback.Bool.case(Nat, Nat.is_ge(a, inf), inf,
      Feedback.Bool.case(Nat, Nat.is_ge(b, inf), inf, Nat.add(a, b))),
      Nat.add(a, b)),
    True{},
    Equal.cong(Nat, Bool, x => Nat.is_le(x, Nat.add(a, b)),
      SolveRef.sat_add(inf, a, b),
      Feedback.Bool.case(Nat, Nat.is_ge(a, inf), inf,
        Feedback.Bool.case(Nat, Nat.is_ge(b, inf), inf, Nat.add(a, b))), u),
    OQ.sat_add_le_add_go(inf, a, b, Nat.is_ge(a, inf), Nat.is_ge(b, inf),
      {==}, {==}))

# One class's result is below the cost of the child it stands for.
def OQ.ClassLe(+p: Nat, +G: +List<+List<Nat>>, +inf: Nat,
    +groups: +List<Groups.Group>, +kids: +List<Tree.Child>) -> Type:
  match groups:
    case Nil{}:
      Unit
    case Con{gp, rest}:
      match gp:
        case Groups.Group{fb, ws}:
          {Nat.is_le(Sat.SB.child_cost(p, G, ws, inf), GC.GC.GroupCost(kids, gp))
           == True{} : Bool}
          & OQ.ClassLe(p, G, inf, rest, kids)

# The saturated sum of the class costs is below the children's total.
def OQ.sumL_le_total(+p: Nat, +G: +List<+List<Nat>>, +inf: Nat,
    +groups: +List<Groups.Group>, +kids: +List<Tree.Child>, +acc: Nat, +acc2: Nat,
    +ha: {Nat.is_le(acc, acc2) == True{} : Bool},
    le: OQ.ClassLe(p, G, inf, groups, kids)) ->
  {Nat.is_le(OV.OV.sumL(inf, Sat.SB.child_costs(p, G, groups, inf), acc),
      Nat.add(acc2, GC.GC.Total(kids, groups))) == True{} : Bool}:
  match groups:
    case Nil{}:
      Fold.OQ.le_cong_r(acc, acc2, Nat.add(acc2, 0n),
        Equal.sym(Nat, Nat.add(acc2, 0n), acc2,
          NatProof.NatPrf.add_zero(acc2)), ha)
    case Con{gp, rest}:
      match gp:
        case Groups.Group{fb, ws}:
          (lh, lt) = le
          +c : Nat = Sat.SB.child_cost(p, G, ws, inf)
          +t : Nat = GC.GC.GroupCost(kids, Groups.Group{fb, ws})
          +acc1 : Nat = SolveRef.sat_add(inf, acc, c)
          +acc21 : Nat = Nat.add(acc2, t)
          +h1 : {Nat.is_le(acc1, acc21) == True{} : Bool} =
            NatProof.Nat.is_le_trans(acc1, Nat.add(acc, c), acc21,
              OQ.sat_add_le_add(inf, acc, c),
              NatProof.Nat.is_le_trans(Nat.add(acc, c), Nat.add(acc2, c),
                Nat.add(acc2, t),
                NatProof.Nat.is_le_add_r(acc, acc2, c, ha),
                NatProof.Nat.is_le_add_l(c, t, acc2, lh)))
          +ih : {Nat.is_le(OV.OV.sumL(inf, Sat.SB.child_costs(p, G, rest, inf), acc1),
                    Nat.add(acc21, GC.GC.Total(kids, rest))) == True{} : Bool} =
            OQ.sumL_le_total(p, G, inf, rest, kids, acc1, acc21, h1, lt)
          +e : {Nat.add(acc21, GC.GC.Total(kids, rest))
                == Nat.add(acc2, GC.GC.Total(kids, Groups.Group{fb, ws} <> rest))
                : Nat} =
            NatProof.NatPrf.add_assoc(acc2, t, GC.GC.Total(kids, rest))
          Fold.OQ.le_cong_r(OV.OV.sumL(inf, Sat.SB.child_costs(p, G, groups, inf), acc),
            Nat.add(acc21, GC.GC.Total(kids, rest)),
            Nat.add(acc2, GC.GC.Total(kids, groups)), e, ih)
