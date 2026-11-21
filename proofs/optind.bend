# The fuel induction of the optimality bound.
#
# The bound is proved at every fuel: if the candidate lists at the next level
# have at most `fuel` words, the search at that fuel costs at most any valid
# tree. The induction hands every class of every guess its own obligation at
# the smaller fuel, in one conjunction, and the node step of `optnode` reads
# them off. All the facts are `Bool` equalities, so they can be reused.
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
import ./nodecost.bend as NodeCost
import ./cover.bend as Cover
import ./cover_oracle.bend as Cora
import ./cover_groups.bend as Cgrp
import ./cover_kids.bend as Ckids
import ./cover_list.bend as Clist
import ./optimalvalue.bend as OV
import ./optsum.bend as Sums
import ./optfold.bend as Fold
import ./optnode.bend as Node
import ./mainvalid.bend as MV

# The class obligations of one guess, only when the guess is usable.
def OQ.AClassIf(b: Bool, fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +groups: +List<Groups.Group>) -> Type:
  match b:
    case True{}:
      Node.OQ.AClass(fuel, inf, G, groups)
    case False{}:
      Unit

# The class obligations of every guess in a guess list, in guess order.
def OQ.AByGs(fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +gs: +List<+List<Nat>>) -> Type:
  match gs:
    case Nil{}:
      Unit
    case Con{g, t}:
      OQ.AClassIf(Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
        fuel, inf, G, Groups.groups_build(g, S, Nil{}))
      & OQ.AByGs(fuel, inf, G, S, t)

# Split a flat conjunction of jobs at an append.
def OQ.aflat_append(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +xs: +List<+List<+List<Nat>>>, +ys: +List<+List<+List<Nat>>>,
    f: Node.OQ.AFlat(fuel, inf, G,
        List.append(&2, +List<+List<Nat>>, xs, ys))) ->
  Node.OQ.AFlat(fuel, inf, G, xs) & Node.OQ.AFlat(fuel, inf, G, ys):
  match xs:
    case Nil{}:
      Tuple{Unit{}, f}
    case Con{S, t}:
      (jh, jt) = f
      MV.MV.use_pair(
        (Node.OQ.AJob(fuel, inf, G, S) & Node.OQ.AFlat(fuel, inf, G, t))
        & Node.OQ.AFlat(fuel, inf, G, ys),
        Node.OQ.AFlat(fuel, inf, G, t), Node.OQ.AFlat(fuel, inf, G, ys),
        OQ.aflat_append(fuel, inf, G, t, ys, jt),
        ft => fys => Tuple{Tuple{jh, ft}, fys})

# A class list conjunction read from a flat conjunction over its classes.
def OQ.aclass_of_flat(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +groups: +List<Groups.Group>,
    f: Node.OQ.AFlat(fuel, inf, G, MV.MV.next_groups(groups))) ->
  Node.OQ.AClass(fuel, inf, G, groups):
  match groups:
    case Nil{}:
      Unit{}
    case Con{gp, rest}:
      match gp:
        case Groups.Group{fb, ws}:
          (fh, ft) = f
          (fh, OQ.aclass_of_flat(fuel, inf, G, rest, ft))

# A filtered class conjunction is a class conjunction when the test is true.
def OQ.aclass_if(+b: Bool, +eb: {b == True{} : Bool}, fuel: Nat, +inf: Nat,
    +G: +List<+List<Nat>>, +groups: +List<Groups.Group>,
    f: OQ.AClassIf(b, fuel, inf, G, groups)) ->
  Node.OQ.AClass(fuel, inf, G, groups):
  match b:
    case True{}:
      f
    case False{}:
      Empty.absurd(Node.OQ.AClass(fuel, inf, G, groups),
        Logic.Proof.true_ne_false(Equal.sym(Bool, b, True{}, eb)))

# Transport a class conjunction along an equality of group lists.
def OQ.aclass_transport(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +gs1: +List<Groups.Group>, +gs2: +List<Groups.Group>,
    e: {gs1 == gs2 : +List<Groups.Group>},
    f: Node.OQ.AClass(fuel, inf, G, gs1)) ->
  Node.OQ.AClass(fuel, inf, G, gs2):
  %e : Node.OQ.AClass(fuel, inf, G, _)
  f

# The head of the class-obligation search over a guess list.
def OQ.bygs_head(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +h: +List<Nat>, +t: +List<+List<Nat>>,
    +g: +List<Nat>, +mem: {Tree.member_word(g, h <> t) == True{} : Bool},
    +us: {Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})) == True{}
         : Bool},
    b: Bool, +eb: {b == Feedback.word_eq(g, h) : Bool},
    f: OQ.AByGs(fuel, inf, G, S, h <> t),
    k: OQ.AByGs(fuel, inf, G, S, t) -> {Tree.member_word(g, t) == True{} : Bool}
       -> Node.OQ.AClass(fuel, inf, G, Groups.groups_build(g, S, Nil{}))) ->
  Node.OQ.AClass(fuel, inf, G, Groups.groups_build(g, S, Nil{})):
  match b:
    case True{}:
      (fh, ft) = f
      +egh : {g == h : +List<Nat>} =
        Clist.Cover.word_eq_true(g, h,
          Equal.sym(Bool, True{}, Feedback.word_eq(g, h), eb))
      +egrp : {Groups.groups_build(g, S, Nil{})
               == Groups.groups_build(h, S, Nil{}) : +List<Groups.Group>} =
        Equal.cong(+List<Nat>, +List<Groups.Group>,
          x => Groups.groups_build(x, S, Nil{}), g, h, egh)
      +ush : {Groups.groups_smaller(S, Groups.groups_build(h, S, Nil{}))
              == True{} : Bool} =
        Equal.trans(Bool,
          Groups.groups_smaller(S, Groups.groups_build(h, S, Nil{})),
          Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})), True{},
          Equal.cong(+List<Groups.Group>, Bool,
            z => Groups.groups_smaller(S, z),
            Groups.groups_build(h, S, Nil{}), Groups.groups_build(g, S, Nil{}),
            Equal.sym(+List<Groups.Group>, Groups.groups_build(g, S, Nil{}),
              Groups.groups_build(h, S, Nil{}), egrp)),
          us)
      fac : Node.OQ.AClass(fuel, inf, G, Groups.groups_build(h, S, Nil{})) =
        OQ.aclass_if(Groups.groups_smaller(S, Groups.groups_build(h, S, Nil{})),
          ush, fuel, inf, G, Groups.groups_build(h, S, Nil{}), fh)
      OQ.aclass_transport(fuel, inf, G, Groups.groups_build(h, S, Nil{}),
        Groups.groups_build(g, S, Nil{}),
        Equal.sym(+List<Groups.Group>, Groups.groups_build(g, S, Nil{}),
          Groups.groups_build(h, S, Nil{}), egrp), fac)
    case False{}:
      (fh, ft) = f
      +mt : {Tree.member_word(g, t) == True{} : Bool} =
        Cora.Cover.member_tail(g, h, t, b, eb, {==}, mem)
      k(ft, mt)

# The class obligations of a usable guess, searched in a guess list.
def OQ.bygs_at(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +gs: +List<+List<Nat>>, +g: +List<Nat>,
    +mem: {Tree.member_word(g, gs) == True{} : Bool},
    +us: {Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})) == True{}
         : Bool},
    f: OQ.AByGs(fuel, inf, G, S, gs)) ->
  Node.OQ.AClass(fuel, inf, G, Groups.groups_build(g, S, Nil{})):
  match gs:
    case Nil{}:
      Empty.absurd(Node.OQ.AClass(fuel, inf, G,
          Groups.groups_build(g, S, Nil{})),
        Logic.Proof.false_ne_true(mem))
    case Con{h, t}:
      OQ.bygs_head(fuel, inf, G, S, h, t, g, mem, us,
        Feedback.word_eq(g, h), {==}, f,
        ft => mt => OQ.bygs_at(fuel, inf, G, S, t, g, mt, us, ft))
