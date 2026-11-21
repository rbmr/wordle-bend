# Completeness: a valid tree makes the search finite and small.
#
# The law `solve_optimal` has to exhibit the tree the solver returns, so the
# stored cost must be below infinity. This module proves that: if a valid tree
# for the candidate list exists, the search at that list has a finite cost, and
# that cost fits the square of the candidate count. The proof is the same fuel
# induction as the optimality bound, with the per-class tree facts supplied by
# the valid tree itself. An unusable root descends structurally into the class
# that holds the whole candidate list, so the same fuel applies again.
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
import ./classbound.bend as CBProof
import ./classbound_nat.bend as CBN
import ./classbound_sum.bend as CBS
import ./classbound_kids.bend as CBK
import ./optimalvalue.bend as OV
import ./optsum.bend as Sums
import ./optfold.bend as Fold
import ./optnode.bend as Node
import ./optind.bend as Ind
import ./optguess.bend as Guess
import ./optcost.bend as Cost
import ./groupsmeasure.bend as GM
import ./groupsdistinct.bend as GD
import ./groupcost.bend as GC
import ./nodecost.bend as NodeCost
import ./solvevalid.bend as SV
import ./mainvalid.bend as MV
import ./cover.bend as Cover
import ./cover_oracle.bend as Cora
import ./cover_groups.bend as Cgrp
import ./cover_list.bend as Clist
import ./cover_kids.bend as Ckids
import ./kids.bend as KidPr
import ./groups.bend as Grp
import ./validbag.bend as VB

# Eliminate a computed pair with a continuation.
def FC.use_pair(-R: Type, -A: Type, -B: Type, p: A & B,
    k: A -> B -> R) -> R:
  match p:
    case (a, b):
      k(a, b)

# A number below `n` has its square below `n*n`, which is below infinity.
def FC.sq_lt(+inf: Nat, +m: Nat, +n: Nat,
    e: {Nat.is_lt(m, n) == True{} : Bool},
    hz: {Nat.is_lt(Nat.mul(n, n), inf) == True{} : Bool}) ->
  {Nat.is_lt(Nat.mul(m, m), inf) == True{} : Bool}:
  +le : {Nat.is_le(m, n) == True{} : Bool} = NatProof.Nat.is_le_of_lt(m, n, e)
  +h1 : {Nat.is_le(Nat.mul(m, m), Nat.mul(n, m)) == True{} : Bool} =
    CBN.CB.is_le_mul_l(m, n, m, le)
  +h2 : {Nat.is_le(Nat.mul(n, m), Nat.mul(n, n)) == True{} : Bool} =
    CBN.CB.is_le_mul_r(m, n, n, le)
  +h3 : {Nat.is_le(Nat.mul(m, m), Nat.mul(n, n)) == True{} : Bool} =
    NatProof.Nat.is_le_trans(Nat.mul(m, m), Nat.mul(n, m), Nat.mul(n, n), h1, h2)
  NatProof.Nat.is_le_lt_trans(Nat.mul(m, m), Nat.mul(n, n), inf, h3, hz)

# A saturating fold is at most the plain sum, with the accumulator up front.
def FC.sumL_le(+inf: Nat, +cs: +List<Nat>, +acc: Nat) ->
  {Nat.is_le(OV.OV.sumL(inf, cs, acc), Nat.add(acc, CBN.CB.sum(cs))) == True{}
   : Bool}:
  match cs:
    case Nil{}:
      NatProof.Nat.is_le_eq_r(acc, acc, Nat.add(acc, 0n),
        Equal.sym(Nat, Nat.add(acc, 0n), acc, NatProof.NatPrf.add_zero(acc)),
        NatProof.Nat.is_le_refl(acc))
    case Con{c, t}:
      +ih : {Nat.is_le(OV.OV.sumL(inf, t, SolveRef.sat_add(inf, acc, c)),
                 Nat.add(SolveRef.sat_add(inf, acc, c), CBN.CB.sum(t)))
             == True{} : Bool} =
        FC.sumL_le(inf, t, SolveRef.sat_add(inf, acc, c))
      +sat : {Nat.is_le(SolveRef.sat_add(inf, acc, c), Nat.add(acc, c))
              == True{} : Bool} =
        Sums.OQ.sat_add_le_add(inf, acc, c)
      +step : {Nat.is_le(Nat.add(SolveRef.sat_add(inf, acc, c), CBN.CB.sum(t)),
                  Nat.add(Nat.add(acc, c), CBN.CB.sum(t))) == True{} : Bool} =
        NatProof.Nat.is_le_add_r(SolveRef.sat_add(inf, acc, c),
          Nat.add(acc, c), CBN.CB.sum(t), sat)
      +mid : {Nat.is_le(OV.OV.sumL(inf, t, SolveRef.sat_add(inf, acc, c)),
                  Nat.add(Nat.add(acc, c), CBN.CB.sum(t))) == True{} : Bool} =
        NatProof.Nat.is_le_trans(
          OV.OV.sumL(inf, t, SolveRef.sat_add(inf, acc, c)),
          Nat.add(SolveRef.sat_add(inf, acc, c), CBN.CB.sum(t)),
          Nat.add(Nat.add(acc, c), CBN.CB.sum(t)), ih, step)
      NatProof.Nat.is_le_eq_r(
        OV.OV.sumL(inf, Con{c, t}, acc),
        Nat.add(Nat.add(acc, c), CBN.CB.sum(t)),
        Nat.add(acc, CBN.CB.sum(Con{c, t})),
        NatProof.NatPrf.add_assoc(acc, c, CBN.CB.sum(t)), mid)

# The completeness obligation for one candidate list.
def FC.FinJob(fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>) -> Type:
  @hz: {Nat.is_lt(Nat.mul(Groups.len_words(S), Groups.len_words(S)), inf)
        == True{} : Bool}
  -> @T: Tree.Tree -> Tree.Valid(T, G, S)
  -> {Nat.is_lt(Eval.Eval.cost_of(SolveRef.step(fuel, SolveRef.mk_schedule(G, S),
        G, S, inf, Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf),
        Eval.Eval.dummy_zero())), inf) == True{} : Bool}
     & {Nat.is_le(Eval.Eval.cost_of(SolveRef.step(fuel,
          SolveRef.mk_schedule(G, S), G, S, inf, Nil{}, Nil{}, 0n,
          Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero())),
        Nat.mul(Groups.len_words(S), Groups.len_words(S))) == True{} : Bool}

# The conjunction of the obligations over a list of candidate lists.
def FC.FinFlat(fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    jobs: +List<+List<+List<Nat>>>) -> Type:
  match jobs:
    case Nil{}:
      Unit
    case Con{S, t}:
      FC.FinJob(fuel, inf, G, S) & FC.FinFlat(fuel, inf, G, t)

# The obligations of one guess's classes.
def FC.FinClass(fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +groups: +List<Groups.Group>) -> Type:
  match groups:
    case Nil{}:
      Unit
    case Con{gp, rest}:
      match gp:
        case Groups.Group{fb, ws}:
          FC.FinJob(fuel, inf, G, ws) & FC.FinClass(fuel, inf, G, rest)

# The class obligations of one guess, only when the guess is usable.
def FC.FinClassIf(fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>, b: Bool,
    +groups: +List<Groups.Group>) -> Type:
  match b:
    case True{}:
      FC.FinClass(fuel, inf, G, groups)
    case False{}:
      Unit

# The class obligations of every guess in a guess list, in guess order.
def FC.FinByGs(fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +gs: +List<+List<Nat>>) -> Type:
  match gs:
    case Nil{}:
      Unit
    case Con{g, t}:
      FC.FinClassIf(fuel, inf, G,
        Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
        Groups.groups_build(g, S, Nil{}))
      & FC.FinByGs(fuel, inf, G, S, t)

# The empty guess list has an infinite search cost, which a valid tree rules out.
def FC.fin_zero_empty(+inf: Nat, T: Tree.Tree, v: Tree.Valid(T, Nil{}, Nil{}),
    +hz: {Nat.is_lt(Nat.mul(Groups.len_words(Nil{}), Groups.len_words(Nil{})), inf)
          == True{} : Bool}) ->
  {Nat.is_lt(Eval.Eval.cost_of(SolveRef.step(0n, SolveRef.mk_schedule(Nil{}, Nil{}),
      Nil{}, Nil{}, inf, Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf),
      Eval.Eval.dummy_zero())), inf) == True{} : Bool}
  & {Nat.is_le(Eval.Eval.cost_of(SolveRef.step(0n,
       SolveRef.mk_schedule(Nil{}, Nil{}), Nil{}, Nil{}, inf, Nil{}, Nil{}, 0n,
       Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero())),
      Nat.mul(Groups.len_words(Nil{}), Groups.len_words(Nil{}))) == True{} : Bool}:
  match T:
    case Tree.Node{g, kids}:
      (ti, ad) = v
      (wg, kidsin) = ti
      Empty.absurd(
        {Nat.is_lt(Eval.Eval.cost_of(SolveRef.step(0n,
           SolveRef.mk_schedule(Nil{}, Nil{}), Nil{}, Nil{}, inf, Nil{}, Nil{}, 0n,
           Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero())), inf) == True{}
         : Bool}
        & {Nat.is_le(Eval.Eval.cost_of(SolveRef.step(0n,
             SolveRef.mk_schedule(Nil{}, Nil{}), Nil{}, Nil{}, inf, Nil{}, Nil{},
             0n, Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero())),
            Nat.mul(Groups.len_words(Nil{}), Groups.len_words(Nil{}))) == True{}
           : Bool},
        Logic.Proof.false_ne_true(wg))

# A nonempty guess list at zero fuel gives the candidate count, at cost zero.
def FC.fin_zero_cons(+inf: Nat, +g: +List<Nat>, +t: +List<+List<Nat>>,
    +hz: {Nat.is_lt(Nat.mul(Groups.len_words(Nil{}), Groups.len_words(Nil{})), inf)
          == True{} : Bool}) ->
  {Nat.is_lt(Eval.Eval.cost_of(SolveRef.step(0n,
      SolveRef.mk_schedule(g <> t, Nil{}), g <> t, Nil{}, inf, Nil{}, Nil{}, 0n,
      Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero())), inf) == True{} : Bool}
  & {Nat.is_le(Eval.Eval.cost_of(SolveRef.step(0n,
       SolveRef.mk_schedule(g <> t, Nil{}), g <> t, Nil{}, inf, Nil{}, Nil{}, 0n,
       Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero())),
      Nat.mul(Groups.len_words(Nil{}), Groups.len_words(Nil{}))) == True{} : Bool}:
  +eb : {SolveRef.step(0n, SolveRef.mk_schedule(g <> t, Nil{}), g <> t, Nil{}, inf,
            Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero())
          == Eval.Eval.guesses(0n, g <> t, Nil{}, inf, g <> t,
               Eval.Eval.dummy_inf(inf)) : SolveRef.Best} =
    Eval.Eval.guesses_zero(g <> t, inf, g <> t, Eval.Eval.dummy_inf(inf))
  +ec : {Eval.Eval.cost_of(SolveRef.step(0n, SolveRef.mk_schedule(g <> t, Nil{}),
              g <> t, Nil{}, inf, Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf),
              Eval.Eval.dummy_zero()))
          == Eval.Eval.cost_of(Eval.Eval.guesses(0n, g <> t, Nil{}, inf, g <> t,
               Eval.Eval.dummy_inf(inf))) : Nat} =
    Equal.cong(SolveRef.Best, Nat, Eval.Eval.cost_of,
      SolveRef.step(0n, SolveRef.mk_schedule(g <> t, Nil{}), g <> t, Nil{}, inf,
        Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero()),
      Eval.Eval.guesses(0n, g <> t, Nil{}, inf, g <> t, Eval.Eval.dummy_inf(inf)), eb)
  +ec2 : {Eval.Eval.cost_of(Eval.Eval.guesses(0n, g <> t, Nil{}, inf, g <> t,
             Eval.Eval.dummy_inf(inf))) == 0n : Nat} =
    Cost.OC.zero_first_cost(g <> t, inf, g, t, hz)
  +ec3 : {Eval.Eval.cost_of(SolveRef.step(0n, SolveRef.mk_schedule(g <> t, Nil{}),
             g <> t, Nil{}, inf, Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf),
             Eval.Eval.dummy_zero())) == 0n : Nat} =
    Equal.trans(Nat,
      Eval.Eval.cost_of(SolveRef.step(0n, SolveRef.mk_schedule(g <> t, Nil{}),
        g <> t, Nil{}, inf, Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf),
        Eval.Eval.dummy_zero())),
      Eval.Eval.cost_of(Eval.Eval.guesses(0n, g <> t, Nil{}, inf, g <> t,
        Eval.Eval.dummy_inf(inf))), 0n, ec, ec2)
  +f1 : {Nat.is_lt(Eval.Eval.cost_of(SolveRef.step(0n,
              SolveRef.mk_schedule(g <> t, Nil{}), g <> t, Nil{}, inf, Nil{}, Nil{},
              0n, Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero())), inf)
          == True{} : Bool} =
    CBN.CB.lt_eq_l(inf, 0n,
      Eval.Eval.cost_of(SolveRef.step(0n, SolveRef.mk_schedule(g <> t, Nil{}),
        g <> t, Nil{}, inf, Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf),
        Eval.Eval.dummy_zero())),
      Equal.sym(Nat, Eval.Eval.cost_of(SolveRef.step(0n,
        SolveRef.mk_schedule(g <> t, Nil{}), g <> t, Nil{}, inf, Nil{}, Nil{}, 0n,
        Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero())), 0n, ec3), hz)
  +f2 : {Nat.is_le(Eval.Eval.cost_of(SolveRef.step(0n,
              SolveRef.mk_schedule(g <> t, Nil{}), g <> t, Nil{}, inf, Nil{}, Nil{},
              0n, Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero())),
             Nat.mul(Groups.len_words(Nil{}), Groups.len_words(Nil{})))
          == True{} : Bool} =
    NatProof.Nat.is_le_eq_l(0n, 0n, Eval.Eval.cost_of(SolveRef.step(0n,
        SolveRef.mk_schedule(g <> t, Nil{}), g <> t, Nil{}, inf, Nil{}, Nil{}, 0n,
        Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero())),
      Equal.sym(Nat, Eval.Eval.cost_of(SolveRef.step(0n,
        SolveRef.mk_schedule(g <> t, Nil{}), g <> t, Nil{}, inf, Nil{}, Nil{}, 0n,
        Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero())), 0n, ec3),
      NatProof.Nat.is_le_refl(0n))
  (f1, f2)

# Zero fuel at the empty candidate list.
def FC.fin_zero_nil(+inf: Nat, +G: +List<+List<Nat>>) ->
  FC.FinJob(0n, inf, G, Nil{}):
  match G:
    case Nil{}:
      hz => T => v => FC.fin_zero_empty(inf, T, v, hz)
    case Con{g, t}:
      hz => T => v => FC.fin_zero_cons(inf, g, t, hz)

# Move a filtered class obligation to an equal test.
def FC.classif_b(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    b1: Bool, b2: Bool, +eb: {b1 == b2 : Bool}, +groups: +List<Groups.Group>,
    f: FC.FinClassIf(fuel, inf, G, b1, groups)) ->
  FC.FinClassIf(fuel, inf, G, b2, groups):
  %eb : FC.FinClassIf(fuel, inf, G, _, groups)
  f

# Move a class obligation to an equal group list.
def FC.classif_g(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>, +b: Bool,
    +g1: +List<Groups.Group>, +g2: +List<Groups.Group>,
    e: {g1 == g2 : +List<Groups.Group>},
    f: FC.FinClassIf(fuel, inf, G, b, g1)) ->
  FC.FinClassIf(fuel, inf, G, b, g2):
  %e : FC.FinClassIf(fuel, inf, G, b, _)
  f

# The head branch of the membership walk, with the word test as a parameter.
def FC.finbygs_at_head(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +h: +List<Nat>, +t: +List<+List<Nat>>,
    +g: +List<Nat>, +mem: {Tree.member_word(g, h <> t) == True{} : Bool},
    head: FC.FinClassIf(fuel, inf, G,
      Groups.groups_smaller(S, Groups.groups_build(h, S, Nil{})),
      Groups.groups_build(h, S, Nil{})),
    b: Bool,
    +eb: {b == Feedback.word_eq(g, h) : Bool},
    k: {Tree.member_word(g, t) == True{} : Bool}
       -> FC.FinClassIf(fuel, inf, G,
            Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
            Groups.groups_build(g, S, Nil{}))) ->
  FC.FinClassIf(fuel, inf, G,
    Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
    Groups.groups_build(g, S, Nil{})):
  match b:
    case True{}:
      +egh : {g == h : +List<Nat>} =
        Clist.Cover.word_eq_true(g, h, Equal.sym(Bool, True{}, Feedback.word_eq(g, h), eb))
      +egrp : {Groups.groups_build(g, S, Nil{})
               == Groups.groups_build(h, S, Nil{}) : +List<Groups.Group>} =
        Equal.cong(+List<Nat>, +List<Groups.Group>,
          x => Groups.groups_build(x, S, Nil{}), g, h, egh)
      +e_back : {Groups.groups_build(h, S, Nil{})
                 == Groups.groups_build(g, S, Nil{}) : +List<Groups.Group>} =
        Equal.sym(+List<Groups.Group>, Groups.groups_build(g, S, Nil{}),
          Groups.groups_build(h, S, Nil{}), egrp)
      +ebk : {Groups.groups_smaller(S, Groups.groups_build(h, S, Nil{}))
              == Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{}))
              : Bool} =
        Equal.cong(+List<Groups.Group>, Bool,
          z => Groups.groups_smaller(S, z),
          Groups.groups_build(h, S, Nil{}), Groups.groups_build(g, S, Nil{}), e_back)
      f1 : FC.FinClassIf(fuel, inf, G,
        Groups.groups_smaller(S, Groups.groups_build(h, S, Nil{})),
        Groups.groups_build(g, S, Nil{})) =
        FC.classif_g(fuel, inf, G,
          Groups.groups_smaller(S, Groups.groups_build(h, S, Nil{})),
          Groups.groups_build(h, S, Nil{}), Groups.groups_build(g, S, Nil{}),
          e_back, head)
      FC.classif_b(fuel, inf, G,
        Groups.groups_smaller(S, Groups.groups_build(h, S, Nil{})),
        Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})), ebk,
        Groups.groups_build(g, S, Nil{}), f1)
    case False{}:
      +mt : {Tree.member_word(g, t) == True{} : Bool} =
        Cora.Cover.member_tail(g, h, t, b, eb, {==}, mem)
      k(mt)

# The class obligation of the guess a membership points at.
def FC.finbygs_at(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +gs: +List<+List<Nat>>, +g: +List<Nat>,
    +mem: {Tree.member_word(g, gs) == True{} : Bool},
    f: FC.FinByGs(fuel, inf, G, S, gs)) ->
  FC.FinClassIf(fuel, inf, G,
    Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
    Groups.groups_build(g, S, Nil{})):
  match gs:
    case Nil{}:
      Empty.absurd(
        FC.FinClassIf(fuel, inf, G,
          Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
          Groups.groups_build(g, S, Nil{})),
        Logic.Proof.false_ne_true(mem))
    case Con{h, t}:
      (fh, ft) = f
      FC.finbygs_at_head(fuel, inf, G, S, h, t, g, mem, fh,
        Feedback.word_eq(g, h), {==},
        mt => FC.finbygs_at(fuel, inf, G, S, t, g, mt, ft))

# A filtered class obligation with a true test is a class obligation.
def FC.classif_true(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +g: +List<Nat>, b: Bool,
    +eb: {b == Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})) : Bool},
    +us: {Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})) == True{}
         : Bool},
    f: FC.FinClassIf(fuel, inf, G, b, Groups.groups_build(g, S, Nil{}))) ->
  FC.FinClass(fuel, inf, G, Groups.groups_build(g, S, Nil{})):
  match b:
    case True{}:
      f
    case False{}:
      Empty.absurd(FC.FinClass(fuel, inf, G, Groups.groups_build(g, S, Nil{})),
        Logic.Proof.false_ne_true(Equal.trans(Bool, False{},
          Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})), True{}, eb, us)))

# Apply a class obligation to the tree the class's child really is.
def FC.kid_fit(-R: Type, +p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +kids: +List<Tree.Child>, +fb: +List<Feedback.Color>,
    +ws: +List<+List<Nat>>,
    kid: Cora.Cover.GroupKid(G, kids, Groups.Group{fb, ws}),
    job: FC.FinJob(p, inf, G, ws),
    +hzw: {Nat.is_lt(Nat.mul(Groups.len_words(ws), Groups.len_words(ws)), inf)
           == True{} : Bool},
    k: {Nat.is_lt(Sat.SB.child_cost(p, G, ws, inf), inf) == True{} : Bool}
       -> {Nat.is_le(Sat.SB.child_cost(p, G, ws, inf),
            Nat.mul(Groups.len_words(ws), Groups.len_words(ws))) == True{} : Bool}
       -> R) -> R:
  match kid:
    case Tuple{T, kp}:
      (e_look, valid) = kp
      FC.use_pair(R,
        {Nat.is_lt(Sat.SB.child_cost(p, G, ws, inf), inf) == True{} : Bool},
        {Nat.is_le(Sat.SB.child_cost(p, G, ws, inf),
           Nat.mul(Groups.len_words(ws), Groups.len_words(ws))) == True{} : Bool},
        job(hzw)(T)(valid),
        f1 => f2 => k(f1, f2))

# The per-class facts that bound a node, from the class obligations.
def FC.class_fits(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +kids: +List<Tree.Child>, +groups: +List<Groups.Group>,
    gk: Cora.Cover.GroupKids(G, kids, groups),
    fj: FC.FinClass(p, inf, G, groups),
    sm: GM.GM.GroupsSmaller(S, groups),
    +hz: {Nat.is_lt(Nat.mul(Groups.len_words(S), Groups.len_words(S)), inf)
          == True{} : Bool}) ->
  CBK.CBK.ClassFits(p, G, S, groups, inf, Groups.len_words(S)):
  match groups:
    case Nil{}:
      Unit{}
    case Con{gp, rest}:
      match gp:
        case Groups.Group{f, ws}:
          (kid, gkt) = gk
          (job, fjt) = fj
          (lt0, smt) = sm
          +lt : {Nat.is_lt(Groups.len_words(ws), Groups.len_words(S)) == True{}
                 : Bool} = lt0
          FC.kid_fit(
            CBK.CBK.ClassFits(p, G, S, groups, inf, Groups.len_words(S)),
            p, inf, G, kids, f, ws, kid, job,
            FC.sq_lt(inf, Groups.len_words(ws), Groups.len_words(S), lt, hz),
            fl => fr =>
              ((lt, (fr,
                 FC.class_fits(p, inf, G, S, kids, rest, gkt, fjt, smt, hz)))))

# The usable node: the guess fold is finite and fits the square.
def FC.fin_succ(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +g: +List<Nat>, +kids: +List<Tree.Child>,
    flatS: FC.FinByGs(p, inf, G, S, G),
    v: Tree.Valid(Tree.Node{g, kids}, G, S),
    +hz: {Nat.is_lt(Nat.mul(Groups.len_words(S), Groups.len_words(S)), inf)
          == True{} : Bool},
    +us: {Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})) == True{}
         : Bool}) ->
  {Nat.is_lt(Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, G,
      Eval.Eval.dummy_inf(inf))), inf) == True{} : Bool}
  & {Nat.is_le(Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, G,
       Eval.Eval.dummy_inf(inf))),
      Nat.mul(Groups.len_words(S), Groups.len_words(S))) == True{} : Bool}:
  ((wg0, kidsin), depths) = v
  +wg : {Tree.member_word(g, G) == True{} : Bool} = wg0
  +n : Nat = Groups.len_words(S)
  +gb : +List<Groups.Group> = Groups.groups_build(g, S, Nil{})
  +items : Eval.KS = Eval.Eval.items(p, G, S, g, gb, Nil{}, 0n, inf)
  +cs : +List<Nat> = Sat.SB.child_costs(p, G, gb, inf)
  fj : FC.FinClass(p, inf, G, gb) =
    FC.classif_true(p, inf, G, S, g,
      Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})), {==}, us,
      FC.finbygs_at(p, inf, G, S, G, g, wg, flatS))
  Cover.Cover.depths_agd(
    {Nat.is_lt(Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, G,
        Eval.Eval.dummy_inf(inf))), inf) == True{} : Bool}
    & {Nat.is_le(Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, G,
         Eval.Eval.dummy_inf(inf))),
        Nat.mul(Groups.len_words(S), Groups.len_words(S))) == True{} : Bool},
    g, kids, S, Nil{}, depths, Unit{},
    ok => d2 =>
      Cover.Cover.depths_agd(
        {Nat.is_lt(Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, G,
            Eval.Eval.dummy_inf(inf))), inf) == True{} : Bool}
        & {Nat.is_le(Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, G,
             Eval.Eval.dummy_inf(inf))),
            Nat.mul(Groups.len_words(S), Groups.len_words(S))) == True{} : Bool},
        g, kids, S, Nil{}, d2, Unit{},
        ok2 => d3 =>
          +neokb : {Ckids.Cover.all_ne(gb) == True{} : Bool} =
            Ckids.Cover.groups_build_ne(g, S, Nil{}, {==})
          +kb : {Ckids.Cover.kids_in_b(kids, G) == True{} : Bool} =
            Ckids.Cover.kids_in_to_b(kids, G, kidsin)
          Ckids.Cover.groupkids_from(
            {Nat.is_lt(Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, G,
                Eval.Eval.dummy_inf(inf))), inf) == True{} : Bool}
            & {Nat.is_le(Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, G,
                 Eval.Eval.dummy_inf(inf))),
                Nat.mul(Groups.len_words(S), Groups.len_words(S))) == True{}
               : Bool},
            G, g, kids, gb, kb, neokb, ok2,
            gk =>
              sm : GM.GM.GroupsSmaller(S, gb) =
                GM.GM.groups_smaller_sound(S, gb, us)
              fits : CBK.CBK.ClassFits(p, G, S, gb, inf, n) =
                FC.class_fits(p, inf, G, S, kids, gb, gk, fj, sm, hz)
              +bsq : {Nat.is_le(Nat.add(n, CBN.CB.sum(cs)), Nat.mul(n, n))
                      == True{} : Bool} =
                CBK.CBK.node_bound_sq(p, G, S, g, inf, fits)
              +cl : {Nat.is_le(Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S,
                         inf, G, Eval.Eval.dummy_inf(inf))),
                       Fold.OQ.ks_cost(inf, S, items)) == True{} : Bool} =
                Guess.OQ.guesses_le_cand(p, G, S, inf, G, g,
                  Eval.Eval.dummy_inf(inf), wg, us)
              +sumle : {Nat.is_le(Sat.SB.ks_sum(items), CBN.CB.sum(cs))
                        == True{} : Bool} =
                Fold.OQ.le_cong_l(Sat.SB.ks_sum(items),
                  OV.OV.sumL(inf, cs, 0n), CBN.CB.sum(cs),
                  OV.OV.sum_fold(p, G, S, g, gb, Nil{}, 0n, inf),
                  Fold.OQ.le_cong_r(OV.OV.sumL(inf, cs, 0n),
                    Nat.add(0n, CBN.CB.sum(cs)), CBN.CB.sum(cs), {==},
                    FC.sumL_le(inf, cs, 0n)))
              +satle : {Nat.is_le(SolveRef.sat_add(inf, n, Sat.SB.ks_sum(items)),
                          Nat.add(n, CBN.CB.sum(cs))) == True{} : Bool} =
                NatProof.Nat.is_le_trans(
                  SolveRef.sat_add(inf, n, Sat.SB.ks_sum(items)),
                  Nat.add(n, Sat.SB.ks_sum(items)),
                  Nat.add(n, CBN.CB.sum(cs)),
                  Sums.OQ.sat_add_le_add(inf, n, Sat.SB.ks_sum(items)),
                  NatProof.Nat.is_le_add_l(Sat.SB.ks_sum(items),
                    CBN.CB.sum(cs), n, sumle))
              +ksle : {Nat.is_le(Fold.OQ.ks_cost(inf, S, items),
                          Nat.add(n, CBN.CB.sum(cs))) == True{} : Bool} =
                Fold.OQ.le_cong_l(Fold.OQ.ks_cost(inf, S, items),
                  SolveRef.sat_add(inf, n, Sat.SB.ks_sum(items)),
                  Nat.add(n, CBN.CB.sum(cs)),
                  Node.OQ.ks_cost_unfold(inf, S, items), satle)
              +f2 : {Nat.is_le(Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S,
                         inf, G, Eval.Eval.dummy_inf(inf))), Nat.mul(n, n))
                     == True{} : Bool} =
                NatProof.Nat.is_le_trans(
                  Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, G,
                    Eval.Eval.dummy_inf(inf))),
                  Nat.add(n, CBN.CB.sum(cs)), Nat.mul(n, n),
                  NatProof.Nat.is_le_trans(
                    Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, G,
                      Eval.Eval.dummy_inf(inf))),
                    Fold.OQ.ks_cost(inf, S, items),
                    Nat.add(n, CBN.CB.sum(cs)), cl, ksle),
                  bsq)
              +f1 : {Nat.is_lt(Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf,
                         G, Eval.Eval.dummy_inf(inf))), inf) == True{} : Bool} =
                NatProof.Nat.is_le_lt_trans(
                  Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, G,
                    Eval.Eval.dummy_inf(inf))),
                  Nat.mul(n, n), inf, f2, hz)
              (f1, f2))))
