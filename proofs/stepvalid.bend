# Validity of the fused reference search.
#
# `src/solve_ref.bend` runs `step` over a flat schedule. This module proves that
# every finite result `step` returns is a valid tree. The proof is an induction
# on the fuel together with a loop invariant over the schedule: the best result
# so far is valid, and the accumulated children are exactly the results of the
# classes already processed. The schedule is represented as a `Sched`, whose
# constructors mirror the four item kinds and whose `items` function is the
# flat list the solver consumes.
import Base
import ../src/solve_ref.bend as SolveRef
import ../src/tree.bend as Tree
import ../src/feedback.bend as Feedback
import ../src/groups.bend as Groups
import ./logic.bend as Logic
import ./nat.bend as NatProof
import ./feedback.bend as Fb
import ./groupsdistinct.bend as GD
import ./eval.bend as Eval
import ./sat.bend as Sat
import ./bestok.bend as BO
import ./children.bend as CH
import ./kids.bend as KidsProof
import ./nodecost.bend as NodeCost
import ./depthgroups.bend as DG

# The result of searching one class at the parent fuel. At zero fuel the
# solver cannot descend, so the class contributes infinity.
def SV.classResult(+fuel: Nat, +G: +List<+List<Nat>>,
    +ws: +List<+List<Nat>>, +inf: Nat) -> SolveRef.Best:
  match fuel:
    case 0n:
      Eval.Eval.dummy_inf(inf)
    case 1n+p:
      SolveRef.step(p, SolveRef.mk_schedule(G, ws), G, ws, inf,
        Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero())

# The accumulator fold of the classes, using the parent fuel. This is the
# `Eval.items` fold generalized to the zero-fuel case, where the machine stores
# an infinite child instead of descending.
def SV.items(+fuel: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +g: +List<Nat>, +groups: +List<Groups.Group>, +kids: +List<Tree.Child>,
    +sum: Nat, +inf: Nat) -> Eval.KS:
  match groups:
    case Nil{}:
      Eval.KS{kids, sum}
    case Con{gp, rest}:
      match gp:
        case Groups.Group{+fb, +ws}:
          Eval.Eval.with_kid(fb, kids, sum, inf, SV.classResult(fuel, G, ws, inf),
            k2 => s2 => SV.items(fuel, G, S, g, rest, k2, s2, inf))

def SV.kids_of(ks: Eval.KS) -> +List<Tree.Child>:
  match ks:
    case Eval.KS{+kids, sum}:
      kids

def SV.sum_of(ks: Eval.KS) -> Nat:
  match ks:
    case Eval.KS{kids, +sum}:
      sum

# The machine's children and sum are the fold over the processed classes.
def SV.ItemsEq(+fuel: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +g: +List<Nat>, +processed: +List<Groups.Group>, +inf: Nat,
    +kids: +List<Tree.Child>, +sum: Nat) -> Type:
  {kids == SV.kids_of(SV.items(fuel, G, S, g, processed, Nil{}, 0n, inf))
   : +List<Tree.Child>}
  & {sum == SV.sum_of(SV.items(fuel, G, S, g, processed, Nil{}, 0n, inf)) : Nat}

# Eliminate a pair with a continuation, so a computed result is destructured
# exactly once.
def SV.use_pair(-R: Type, -A: Type, -B: Type, p: A & B,
    k: A -> B -> R) -> R:
  match p:
    case (a, b):
      k(a, b)

# Appending one class to the fold prepends its child and saturates the sum.
def SV.items_append(+fuel: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +g: +List<Nat>, +fb: +List<Feedback.Color>, +ws: +List<+List<Nat>>,
    +inf: Nat, +processed: +List<Groups.Group>, +kids: +List<Tree.Child>,
    +sum: Nat) ->
  {SV.kids_of(SV.items(fuel, G, S, g,
      List.append(&2, Groups.Group, processed, Groups.Group{fb, ws} <> Nil{}), kids, sum, inf))
   == Tree.Child{fb, Eval.Eval.tree_of(SV.classResult(fuel, G, ws, inf))}
      <> SV.kids_of(SV.items(fuel, G, S, g, processed, kids, sum, inf))
   : +List<Tree.Child>}
  & {SV.sum_of(SV.items(fuel, G, S, g,
      List.append(&2, Groups.Group, processed, Groups.Group{fb, ws} <> Nil{}), kids, sum, inf))
     == SolveRef.sat_add(inf,
          SV.sum_of(SV.items(fuel, G, S, g, processed, kids, sum, inf)),
          Eval.Eval.cost_of(SV.classResult(fuel, G, ws, inf)))
     : Nat}:
  match processed:
    case Nil{}:
      +eq : {SV.items(fuel, G, S, g, Groups.Group{fb, ws} <> Nil{},
               kids, sum, inf)
            == Eval.Eval.with_kid(fb, kids, sum, inf, SV.classResult(fuel, G, ws, inf),
                 k2 => s2 => Eval.KS{k2, s2}) : Eval.KS} =
        {==}
      +eq2 : {Eval.Eval.with_kid(fb, kids, sum, inf, SV.classResult(fuel, G, ws, inf),
                k2 => s2 => Eval.KS{k2, s2})
             == Eval.KS{Tree.Child{fb, Eval.Eval.tree_of(SV.classResult(fuel, G, ws, inf))} <> kids,
                  SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(SV.classResult(fuel, G, ws, inf)))} : Eval.KS} =
        Eval.Eval.with_kid_eq(fb, kids, sum, inf, SV.classResult(fuel, G, ws, inf),
          k2 => s2 => Eval.KS{k2, s2})
      (Equal.trans(+List<Tree.Child>,
         SV.kids_of(SV.items(fuel, G, S, g, Groups.Group{fb, ws} <> Nil{},
           kids, sum, inf)),
         SV.kids_of(Eval.Eval.with_kid(fb, kids, sum, inf, SV.classResult(fuel, G, ws, inf),
           k2 => s2 => Eval.KS{k2, s2})),
         Tree.Child{fb, Eval.Eval.tree_of(SV.classResult(fuel, G, ws, inf))} <> kids,
         Equal.cong(Eval.KS, +List<Tree.Child>, SV.kids_of,
           SV.items(fuel, G, S, g, Groups.Group{fb, ws} <> Nil{}, kids, sum, inf),
           Eval.Eval.with_kid(fb, kids, sum, inf, SV.classResult(fuel, G, ws, inf),
             k2 => s2 => Eval.KS{k2, s2}), eq),
         Equal.cong(Eval.KS, +List<Tree.Child>, SV.kids_of,
           Eval.Eval.with_kid(fb, kids, sum, inf, SV.classResult(fuel, G, ws, inf),
             k2 => s2 => Eval.KS{k2, s2}),
           Eval.KS{Tree.Child{fb, Eval.Eval.tree_of(SV.classResult(fuel, G, ws, inf))} <> kids,
             SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(SV.classResult(fuel, G, ws, inf)))},
           eq2)),
       Equal.trans(Nat,
         SV.sum_of(SV.items(fuel, G, S, g, Groups.Group{fb, ws} <> Nil{},
           kids, sum, inf)),
         SV.sum_of(Eval.Eval.with_kid(fb, kids, sum, inf, SV.classResult(fuel, G, ws, inf),
           k2 => s2 => Eval.KS{k2, s2})),
         SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(SV.classResult(fuel, G, ws, inf))),
         Equal.cong(Eval.KS, Nat, SV.sum_of,
           SV.items(fuel, G, S, g, Groups.Group{fb, ws} <> Nil{}, kids, sum, inf),
           Eval.Eval.with_kid(fb, kids, sum, inf, SV.classResult(fuel, G, ws, inf),
             k2 => s2 => Eval.KS{k2, s2}), eq),
         Equal.cong(Eval.KS, Nat, SV.sum_of,
           Eval.Eval.with_kid(fb, kids, sum, inf, SV.classResult(fuel, G, ws, inf),
             k2 => s2 => Eval.KS{k2, s2}),
           Eval.KS{Tree.Child{fb, Eval.Eval.tree_of(SV.classResult(fuel, G, ws, inf))} <> kids,
             SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(SV.classResult(fuel, G, ws, inf)))},
           eq2)))
    case Con{gp, rest}:
      match gp:
        case Groups.Group{+fb0, +ws0}:
          +head : SolveRef.Best = SV.classResult(fuel, G, ws0, inf)
          +kids0 : +List<Tree.Child> = Tree.Child{fb0, Eval.Eval.tree_of(head)} <> kids
          +sum0 : Nat = SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(head))
          +eq_head : {SV.items(fuel, G, S, g,
                List.append(&2, Groups.Group, Groups.Group{fb0, ws0} <> rest, Groups.Group{fb, ws} <> Nil{}),
                kids, sum, inf)
              == SV.items(fuel, G, S, g,
                List.append(&2, Groups.Group, rest, Groups.Group{fb, ws} <> Nil{}), kids0, sum0, inf) : Eval.KS} =
            Eval.Eval.with_kid_eq(fb0, kids, sum, inf, head,
              k2 => s2 => SV.items(fuel, G, S, g,
                List.append(&2, Groups.Group, rest, Groups.Group{fb, ws} <> Nil{}), k2, s2, inf))
          +eq_old : {SV.items(fuel, G, S, g, Groups.Group{fb0, ws0} <> rest,
                kids, sum, inf)
              == SV.items(fuel, G, S, g, rest, kids0, sum0, inf) : Eval.KS} =
            Eval.Eval.with_kid_eq(fb0, kids, sum, inf, head,
              k2 => s2 => SV.items(fuel, G, S, g, rest, k2, s2, inf))
          +e_head_kids : {SV.kids_of(SV.items(fuel, G, S, g,
                List.append(&2, Groups.Group, Groups.Group{fb0, ws0} <> rest, Groups.Group{fb, ws} <> Nil{}),
                kids, sum, inf))
              == SV.kids_of(SV.items(fuel, G, S, g,
                List.append(&2, Groups.Group, rest, Groups.Group{fb, ws} <> Nil{}), kids0, sum0, inf))
              : +List<Tree.Child>} =
            Equal.cong(Eval.KS, +List<Tree.Child>, SV.kids_of,
              SV.items(fuel, G, S, g,
                List.append(&2, Groups.Group, Groups.Group{fb0, ws0} <> rest, Groups.Group{fb, ws} <> Nil{}),
                kids, sum, inf),
              SV.items(fuel, G, S, g,
                List.append(&2, Groups.Group, rest, Groups.Group{fb, ws} <> Nil{}), kids0, sum0, inf), eq_head)
          +e_head_sum : {SV.sum_of(SV.items(fuel, G, S, g,
                List.append(&2, Groups.Group, Groups.Group{fb0, ws0} <> rest, Groups.Group{fb, ws} <> Nil{}),
                kids, sum, inf))
              == SV.sum_of(SV.items(fuel, G, S, g,
                List.append(&2, Groups.Group, rest, Groups.Group{fb, ws} <> Nil{}), kids0, sum0, inf))
              : Nat} =
            Equal.cong(Eval.KS, Nat, SV.sum_of,
              SV.items(fuel, G, S, g,
                List.append(&2, Groups.Group, Groups.Group{fb0, ws0} <> rest, Groups.Group{fb, ws} <> Nil{}),
                kids, sum, inf),
              SV.items(fuel, G, S, g,
                List.append(&2, Groups.Group, rest, Groups.Group{fb, ws} <> Nil{}), kids0, sum0, inf), eq_head)
          +e_old_kids : {SV.kids_of(SV.items(fuel, G, S, g,
                Groups.Group{fb0, ws0} <> rest, kids, sum, inf))
              == SV.kids_of(SV.items(fuel, G, S, g, rest, kids0, sum0, inf))
              : +List<Tree.Child>} =
            Equal.cong(Eval.KS, +List<Tree.Child>, SV.kids_of,
              SV.items(fuel, G, S, g, Groups.Group{fb0, ws0} <> rest, kids, sum, inf),
              SV.items(fuel, G, S, g, rest, kids0, sum0, inf), eq_old)
          +e_old_sum : {SV.sum_of(SV.items(fuel, G, S, g,
                Groups.Group{fb0, ws0} <> rest, kids, sum, inf))
              == SV.sum_of(SV.items(fuel, G, S, g, rest, kids0, sum0, inf))
              : Nat} =
            Equal.cong(Eval.KS, Nat, SV.sum_of,
              SV.items(fuel, G, S, g, Groups.Group{fb0, ws0} <> rest, kids, sum, inf),
              SV.items(fuel, G, S, g, rest, kids0, sum0, inf), eq_old)
          SV.use_pair(
            {SV.kids_of(SV.items(fuel, G, S, g,
               List.append(&2, Groups.Group, Groups.Group{fb0, ws0} <> rest, Groups.Group{fb, ws} <> Nil{}),
               kids, sum, inf))
             == Tree.Child{fb, Eval.Eval.tree_of(SV.classResult(fuel, G, ws, inf))}
                <> SV.kids_of(SV.items(fuel, G, S, g,
                     Groups.Group{fb0, ws0} <> rest, kids, sum, inf))
             : +List<Tree.Child>}
            & {SV.sum_of(SV.items(fuel, G, S, g,
                 List.append(&2, Groups.Group, Groups.Group{fb0, ws0} <> rest, Groups.Group{fb, ws} <> Nil{}),
                 kids, sum, inf))
               == SolveRef.sat_add(inf,
                    SV.sum_of(SV.items(fuel, G, S, g,
                      Groups.Group{fb0, ws0} <> rest, kids, sum, inf)),
                    Eval.Eval.cost_of(SV.classResult(fuel, G, ws, inf)))
               : Nat},
            {SV.kids_of(SV.items(fuel, G, S, g,
               List.append(&2, Groups.Group, rest, Groups.Group{fb, ws} <> Nil{}), kids0, sum0, inf))
             == Tree.Child{fb, Eval.Eval.tree_of(SV.classResult(fuel, G, ws, inf))}
                <> SV.kids_of(SV.items(fuel, G, S, g, rest, kids0, sum0, inf))
             : +List<Tree.Child>},
            {SV.sum_of(SV.items(fuel, G, S, g,
               List.append(&2, Groups.Group, rest, Groups.Group{fb, ws} <> Nil{}), kids0, sum0, inf))
             == SolveRef.sat_add(inf,
                  SV.sum_of(SV.items(fuel, G, S, g, rest, kids0, sum0, inf)),
                  Eval.Eval.cost_of(SV.classResult(fuel, G, ws, inf)))
             : Nat},
            SV.items_append(fuel, G, S, g, fb, ws, inf, rest, kids0, sum0),
            ih_kids => ih_sum =>
              (Equal.trans(+List<Tree.Child>,
                 SV.kids_of(SV.items(fuel, G, S, g,
                   List.append(&2, Groups.Group, Groups.Group{fb0, ws0} <> rest, Groups.Group{fb, ws} <> Nil{}),
                   kids, sum, inf)),
                 SV.kids_of(SV.items(fuel, G, S, g,
                   List.append(&2, Groups.Group, rest, Groups.Group{fb, ws} <> Nil{}), kids0, sum0, inf)),
                 Tree.Child{fb, Eval.Eval.tree_of(SV.classResult(fuel, G, ws, inf))}
                   <> SV.kids_of(SV.items(fuel, G, S, g,
                        Groups.Group{fb0, ws0} <> rest, kids, sum, inf)),
                 e_head_kids,
                 Equal.trans(+List<Tree.Child>,
                   SV.kids_of(SV.items(fuel, G, S, g,
                     List.append(&2, Groups.Group, rest, Groups.Group{fb, ws} <> Nil{}), kids0, sum0, inf)),
                   Tree.Child{fb, Eval.Eval.tree_of(SV.classResult(fuel, G, ws, inf))}
                     <> SV.kids_of(SV.items(fuel, G, S, g, rest, kids0, sum0, inf)),
                   Tree.Child{fb, Eval.Eval.tree_of(SV.classResult(fuel, G, ws, inf))}
                     <> SV.kids_of(SV.items(fuel, G, S, g,
                          Groups.Group{fb0, ws0} <> rest, kids, sum, inf)),
                   ih_kids,
                   Equal.cong(+List<Tree.Child>, +List<Tree.Child>,
                     l => Tree.Child{fb, Eval.Eval.tree_of(SV.classResult(fuel, G, ws, inf))} <> l,
                     SV.kids_of(SV.items(fuel, G, S, g, rest, kids0, sum0, inf)),
                     SV.kids_of(SV.items(fuel, G, S, g,
                       Groups.Group{fb0, ws0} <> rest, kids, sum, inf)),
                     Equal.sym(+List<Tree.Child>,
                       SV.kids_of(SV.items(fuel, G, S, g,
                         Groups.Group{fb0, ws0} <> rest, kids, sum, inf)),
                       SV.kids_of(SV.items(fuel, G, S, g, rest, kids0, sum0, inf)),
                       e_old_kids)))),
              Equal.trans(Nat,
                 SV.sum_of(SV.items(fuel, G, S, g,
                   List.append(&2, Groups.Group, Groups.Group{fb0, ws0} <> rest, Groups.Group{fb, ws} <> Nil{}),
                   kids, sum, inf)),
                 SV.sum_of(SV.items(fuel, G, S, g,
                   List.append(&2, Groups.Group, rest, Groups.Group{fb, ws} <> Nil{}), kids0, sum0, inf)),
                 SolveRef.sat_add(inf,
                   SV.sum_of(SV.items(fuel, G, S, g,
                     Groups.Group{fb0, ws0} <> rest, kids, sum, inf)),
                   Eval.Eval.cost_of(SV.classResult(fuel, G, ws, inf))),
                 e_head_sum,
                 Equal.trans(Nat,
                   SV.sum_of(SV.items(fuel, G, S, g,
                     List.append(&2, Groups.Group, rest, Groups.Group{fb, ws} <> Nil{}), kids0, sum0, inf)),
                   SolveRef.sat_add(inf,
                     SV.sum_of(SV.items(fuel, G, S, g, rest, kids0, sum0, inf)),
                     Eval.Eval.cost_of(SV.classResult(fuel, G, ws, inf))),
                   SolveRef.sat_add(inf,
                     SV.sum_of(SV.items(fuel, G, S, g,
                       Groups.Group{fb0, ws0} <> rest, kids, sum, inf)),
                     Eval.Eval.cost_of(SV.classResult(fuel, G, ws, inf))),
                   ih_sum,
                   Equal.cong(Nat, Nat,
                     x => SolveRef.sat_add(inf, x,
                       Eval.Eval.cost_of(SV.classResult(fuel, G, ws, inf))),
                     SV.sum_of(SV.items(fuel, G, S, g, rest, kids0, sum0, inf)),
                     SV.sum_of(SV.items(fuel, G, S, g,
                       Groups.Group{fb0, ws0} <> rest, kids, sum, inf)),
                     Equal.sym(Nat,
                       SV.sum_of(SV.items(fuel, G, S, g,
                         Groups.Group{fb0, ws0} <> rest, kids, sum, inf)),
                       SV.sum_of(SV.items(fuel, G, S, g, rest, kids0, sum0, inf)),
                       e_old_sum))))))
