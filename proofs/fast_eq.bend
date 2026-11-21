# The bound-pruned solver returns the reference tree for every input.
#
# By fuel induction over the jobs of a level, `FS.run_at(fuel, inf, G, S)`
# equals `FS.ref_run_at(fuel, inf, G, S)`. At zero fuel every bounded candidate
# list is empty and both machines run the same zero-cost guess fold. At
# positive fuel `1+p`, an unusable guess is skipped by both schedules; a usable
# guess either has `cost_of(best) <= lb` (skipped by `SolveFast` via
# `FS.block_dead`, and a no-op on `Eval.block` via `FS.block_skip_eq`) or
# searches its feedback classes at fuel `p` (where the induction hypothesis
# equates `FS.items` with `Eval.items`).
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
import ./optind.bend as Ind
import ./mainvalid.bend as MV
import ./fast_step.bend as FS
import ./fast_groups.bend as FG
import ./fast_lb.bend as FLB

# One job of the equality induction at a given fuel.
def FE.EJob(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>) -> Type:
  {FS.FS.run_at(fuel, inf, G, S) == FS.FS.ref_run_at(fuel, inf, G, S)
   : SolveRef.Best}

# The conjunction of job equalities over a list of candidate lists.
def FE.EFlat(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    jobs: +List<+List<+List<Nat>>>) -> Type:
  match jobs:
    case Nil{}:
      Unit
    case Con{S, t}:
      FE.EJob(fuel, inf, G, S) & FE.EFlat(fuel, inf, G, t)

# The class equalities of one group list.
def FE.EClass(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +groups: +List<Groups.Group>) -> Type:
  match groups:
    case Nil{}:
      Unit
    case Con{gp, rest}:
      match gp:
        case Groups.Group{fb, ws}:
          FE.EJob(p, inf, G, ws) & FE.EClass(p, inf, G, rest)

# The class equalities of a guess, only when the guess is usable.
def FE.EClassIf(b: Bool, +p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +groups: +List<Groups.Group>) -> Type:
  match b:
    case True{}:
      FE.EClass(p, inf, G, groups)
    case False{}:
      Unit

# The per-guess class equalities of a guess list.
def FE.EByGs(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    gs: +List<+List<Nat>>) -> Type:
  match gs:
    case Nil{}:
      Unit
    case Con{g, t}:
      FE.EClassIf(
        Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
        p, inf, G, Groups.groups_build(g, S, Nil{}))
      & FE.EByGs(p, inf, G, S, t)

# Split the flat conjunction at an append.
def FE.eflat_append(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +xs: +List<+List<+List<Nat>>>, +ys: +List<+List<+List<Nat>>>,
    f: FE.EFlat(fuel, inf, G, List.append(&2, +List<+List<Nat>>, xs, ys))) ->
  FE.EFlat(fuel, inf, G, xs) & FE.EFlat(fuel, inf, G, ys):
  match xs:
    case Nil{}:
      Tuple{Unit{}, f}
    case Con{S, t}:
      (j, fr) = f
      MV.MV.use_pair(
        FE.EFlat(fuel, inf, G, S <> t) & FE.EFlat(fuel, inf, G, ys),
        FE.EFlat(fuel, inf, G, t), FE.EFlat(fuel, inf, G, ys),
        FE.eflat_append(fuel, inf, G, t, ys, fr),
        ft => fys => Tuple{Tuple{j, ft}, fys})

def FE.eclass_of_flat(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +groups: +List<Groups.Group>,
    f: FE.EFlat(p, inf, G, MV.MV.next_groups(groups))) ->
  FE.EClass(p, inf, G, groups):
  match groups:
    case Nil{}:
      Unit{}
    case Con{gp, t}:
      match gp:
        case Groups.Group{fb, ws}:
          (j, fr) = f
          (j, FE.eclass_of_flat(p, inf, G, t, fr))

def FE.eclass_if(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +groups: +List<Groups.Group>, b: Bool,
    f: FE.EFlat(p, inf, G, MV.MV.classes_b(b, groups))) ->
  FE.EClassIf(b, p, inf, G, groups):
  match b:
    case True{}:
      FE.eclass_of_flat(p, inf, G, groups, f)
    case False{}:
      Unit{}

def FE.eby_gs(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +gs: +List<+List<Nat>>,
    f: FE.EFlat(p, inf, G, MV.MV.next_guess(gs, S))) ->
  FE.EByGs(p, inf, G, S, gs):
  match gs:
    case Nil{}:
      Unit{}
    case Con{g, t}:
      MV.MV.use_pair(FE.EByGs(p, inf, G, S, g <> t),
        FE.EFlat(p, inf, G, MV.MV.classes(g, S)),
        FE.EFlat(p, inf, G, MV.MV.next_guess(t, S)),
        FE.eflat_append(p, inf, G, MV.MV.classes(g, S),
          MV.MV.next_guess(t, S), f),
        fg => ft =>
          Tuple{FE.eclass_if(p, inf, G, Groups.groups_build(g, S, Nil{}),
                  Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
                  fg),
                FE.eby_gs(p, inf, G, S, t, ft)})

# When every class search at fuel `p` agrees with the reference, the pruned
# class fold `FS.items` agrees with `Eval.items`.
def FE.items_eq(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +g: +List<Nat>, +groups: +List<Groups.Group>, +kids: +List<Tree.Child>,
    +sum: Nat, +inf: Nat, ec: FE.EClass(p, inf, G, groups)) ->
  {FS.FS.items(p, G, S, g, groups, kids, sum, inf)
   == Eval.Eval.items(p, G, S, g, groups, kids, sum, inf) : Eval.KS}:
  match groups:
    case Nil{}:
      {==}
    case Con{gp, rest}:
      match gp:
        case Groups.Group{+fb, +ws}:
          (eh, et) = ec
          +fast_c : SolveRef.Best = FS.FS.run_at(p, inf, G, ws)
          +ref_c : SolveRef.Best = FS.FS.ref_run_at(p, inf, G, ws)
          +k2 : +List<Tree.Child> =
            Tree.Child{fb, Eval.Eval.tree_of(ref_c)} <> kids
          +s2 : Nat = SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(ref_c))
          +e1 : {Eval.Eval.with_kid(fb, kids, sum, inf, fast_c,
                   ka => sa => FS.FS.items(p, G, S, g, rest, ka, sa, inf))
                 == Eval.Eval.with_kid(fb, kids, sum, inf, ref_c,
                      ka => sa => FS.FS.items(p, G, S, g, rest, ka, sa, inf))
                 : Eval.KS} =
            Equal.cong(SolveRef.Best, Eval.KS,
              b => Eval.Eval.with_kid(fb, kids, sum, inf, b,
                     ka => sa => FS.FS.items(p, G, S, g, rest, ka, sa, inf)),
              fast_c, ref_c, eh)
          +e2 : {Eval.Eval.with_kid(fb, kids, sum, inf, ref_c,
                   ka => sa => FS.FS.items(p, G, S, g, rest, ka, sa, inf))
                 == FS.FS.items(p, G, S, g, rest, k2, s2, inf) : Eval.KS} =
            Eval.Eval.with_kid_eq(fb, kids, sum, inf, ref_c,
              ka => sa => FS.FS.items(p, G, S, g, rest, ka, sa, inf))
          +e3 : {FS.FS.items(p, G, S, g, rest, k2, s2, inf)
                 == Eval.Eval.items(p, G, S, g, rest, k2, s2, inf) : Eval.KS} =
            FE.items_eq(p, G, S, g, rest, k2, s2, inf, et)
          +e4 : {Eval.Eval.with_kid(fb, kids, sum, inf, ref_c,
                   ka => sa => Eval.Eval.items(p, G, S, g, rest, ka, sa, inf))
                 == Eval.Eval.items(p, G, S, g, rest, k2, s2, inf) : Eval.KS} =
            Eval.Eval.with_kid_eq(fb, kids, sum, inf, ref_c,
              ka => sa => Eval.Eval.items(p, G, S, g, rest, ka, sa, inf))
          Equal.trans(Eval.KS,
            FS.FS.items(p, G, S, g, Groups.Group{fb, ws} <> rest, kids, sum, inf),
            FS.FS.items(p, G, S, g, rest, k2, s2, inf),
            Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> rest, kids, sum, inf),
            Equal.trans(Eval.KS,
              Eval.Eval.with_kid(fb, kids, sum, inf, fast_c,
                ka => sa => FS.FS.items(p, G, S, g, rest, ka, sa, inf)),
              Eval.Eval.with_kid(fb, kids, sum, inf, ref_c,
                ka => sa => FS.FS.items(p, G, S, g, rest, ka, sa, inf)),
              FS.FS.items(p, G, S, g, rest, k2, s2, inf), e1, e2),
            Equal.trans(Eval.KS,
              FS.FS.items(p, G, S, g, rest, k2, s2, inf),
              Eval.Eval.items(p, G, S, g, rest, k2, s2, inf),
              Eval.Eval.with_kid(fb, kids, sum, inf, ref_c,
                ka => sa => Eval.Eval.items(p, G, S, g, rest, ka, sa, inf)),
              e3,
              Equal.sym(Eval.KS,
                Eval.Eval.with_kid(fb, kids, sum, inf, ref_c,
                  ka => sa => Eval.Eval.items(p, G, S, g, rest, ka, sa, inf)),
                Eval.Eval.items(p, G, S, g, rest, k2, s2, inf), e4)))

# Unfolding `FS.resume` into `Eval.finish_ks`.
def FE.resume_eq(+fuel: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +inf: Nat, +g: +List<Nat>, ks: Eval.KS, +rest: +List<SolveFast.Item>,
    +best: SolveRef.Best) ->
  {FS.FS.resume(fuel, G, S, inf, g, ks, rest, best)
   == SolveFast.step(fuel, rest, G, S, inf, Nil{}, Nil{}, 0n,
        Eval.Eval.finish_ks(inf, g, S, ks, best),
        SolveFast.dummy_zero(), False{})
   : SolveRef.Best}:
  match ks:
    case Eval.KS{kids, sum}:
      {==}

# The outcome of a usable guess block in `SolveFast` agrees with `Eval.block`
# in both the skipped and the searched mode.
def FE.block_out_eq(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +inf: Nat, +g: +List<Nat>, +groups: +List<Groups.Group>,
    +rest: +List<SolveFast.Item>, +best: SolveRef.Best,
    skip: Bool,
    +esk: {skip == SolveFast.skippable(best,
             SolveFast.lower_bound(Groups.len_words(S), groups)) : Bool},
    +us: {Groups.groups_smaller(S, groups) == True{} : Bool},
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    ec: FE.EClass(p, inf, G, groups)) ->
  {FS.FS.block_out(p, G, S, inf, g, groups, Nil{}, 0n, best, rest, skip)
   == SolveFast.step(1n+p, rest, G, S, inf, Nil{}, Nil{}, 0n,
        Eval.Eval.block(p, G, S, g, inf, groups, best),
        SolveFast.dummy_zero(), False{})
   : SolveRef.Best}:
  match skip:
    case True{}:
      +le : {Nat.is_le(Eval.Eval.cost_of(best),
               SolveFast.lower_bound(Groups.len_words(S), groups))
             == True{} : Bool} =
        FLB.FS.skippable_to_le(best,
          SolveFast.lower_bound(Groups.len_words(S), groups),
          Equal.sym(Bool, True{},
            SolveFast.skippable(best,
              SolveFast.lower_bound(Groups.len_words(S), groups)), esk))
      +beq : {Eval.Eval.block(p, G, S, g, inf, groups, best) == best
              : SolveRef.Best} =
        FLB.FS.block_skip_eq(p, inf, G, S, g, groups, best, us, ele, hz,
          hbest, le)
      Equal.cong(SolveRef.Best, SolveRef.Best,
        b => SolveFast.step(1n+p, rest, G, S, inf, Nil{}, Nil{}, 0n, b,
               SolveFast.dummy_zero(), False{}),
        best, Eval.Eval.block(p, G, S, g, inf, groups, best),
        Equal.sym(SolveRef.Best,
          Eval.Eval.block(p, G, S, g, inf, groups, best), best, beq))
    case False{}:
      +ieq : {FS.FS.items(p, G, S, g, groups, Nil{}, 0n, inf)
              == Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf)
              : Eval.KS} =
        FE.items_eq(p, G, S, g, groups, Nil{}, 0n, inf, ec)
      +e1 : {FS.FS.resume(1n+p, G, S, inf, g,
               FS.FS.items(p, G, S, g, groups, Nil{}, 0n, inf), rest, best)
             == FS.FS.resume(1n+p, G, S, inf, g,
                  Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf),
                  rest, best)
             : SolveRef.Best} =
        Equal.cong(Eval.KS, SolveRef.Best,
          ks => FS.FS.resume(1n+p, G, S, inf, g, ks, rest, best),
          FS.FS.items(p, G, S, g, groups, Nil{}, 0n, inf),
          Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf), ieq)
      +e2 : {FS.FS.resume(1n+p, G, S, inf, g,
               Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf), rest, best)
             == SolveFast.step(1n+p, rest, G, S, inf, Nil{}, Nil{}, 0n,
                  Eval.Eval.block(p, G, S, g, inf, groups, best),
                  SolveFast.dummy_zero(), False{})
             : SolveRef.Best} =
        FE.resume_eq(1n+p, G, S, inf, g,
          Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf), rest, best)
      Equal.trans(SolveRef.Best,
        FS.FS.resume(1n+p, G, S, inf, g,
          FS.FS.items(p, G, S, g, groups, Nil{}, 0n, inf), rest, best),
        FS.FS.resume(1n+p, G, S, inf, g,
          Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf), rest, best),
        SolveFast.step(1n+p, rest, G, S, inf, Nil{}, Nil{}, 0n,
          Eval.Eval.block(p, G, S, g, inf, groups, best),
          SolveFast.dummy_zero(), False{}),
        e1, e2)

# Stepping one guess block in `SolveFast` at positive fuel agrees with
# `Eval.guess_bool`.
def FE.schedule_guess_step(+p: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +inf: Nat, +g: +List<Nat>,
    +groups: +List<Groups.Group>, +rest: +List<SolveFast.Item>,
    +best: SolveRef.Best, usable: Bool,
    +eus: {usable == Groups.groups_smaller(S, groups) : Bool},
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    ecif: FE.EClassIf(usable, p, inf, G, groups)) ->
  {SolveFast.step(1n+p,
     SolveFast.schedule_guess(g, groups, Groups.len_words(S), rest, usable),
     G, S, inf, Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{})
   == SolveFast.step(1n+p, rest, G, S, inf, Nil{}, Nil{}, 0n,
        Eval.Eval.guess_bool(p, G, S, g, groups, inf, usable, best),
        SolveFast.dummy_zero(), False{})
   : SolveRef.Best}:
  match usable:
    case False{}:
      {==}
    case True{}:
      +lb : Nat = SolveFast.lower_bound(Groups.len_words(S), groups)
      +skip : Bool = SolveFast.skippable(best, lb)
      +body : +List<SolveFast.Item> =
        List.append(&2, SolveFast.Item, SolveFast.group_items(groups),
          SolveFast.End{} <> rest)
      +us : {Groups.groups_smaller(S, groups) == True{} : Bool} =
        Equal.sym(Bool, True{}, Groups.groups_smaller(S, groups), eus)
      +e1 : {SolveFast.step(1n+p, SolveFast.Begin{g, lb} <> body, G, S, inf,
               Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{})
             == FS.FS.after_begin(1n+p, G, S, inf, g, body, best, skip)
             : SolveRef.Best} =
        FS.FS.begin_succ(p, G, S, inf, Nil{}, g, lb, Nil{}, 0n, best,
          SolveFast.dummy_zero(), False{}, body, skip, {==})
      +e2 : {FS.FS.after_begin(1n+p, G, S, inf, g, body, best, skip)
             == FS.FS.block_out(p, G, S, inf, g, groups, Nil{}, 0n, best,
                  rest, skip)
             : SolveRef.Best} =
        FS.FS.block(p, G, S, inf, g, groups, Nil{}, 0n, best, rest, skip)
      +e3 : {FS.FS.block_out(p, G, S, inf, g, groups, Nil{}, 0n, best,
               rest, skip)
             == SolveFast.step(1n+p, rest, G, S, inf, Nil{}, Nil{}, 0n,
                  Eval.Eval.block(p, G, S, g, inf, groups, best),
                  SolveFast.dummy_zero(), False{})
             : SolveRef.Best} =
        FE.block_out_eq(p, G, S, inf, g, groups, rest, best, skip, {==},
          us, ele, hz, hbest, ecif)
      Equal.trans(SolveRef.Best,
        SolveFast.step(1n+p, SolveFast.Begin{g, lb} <> body, G, S, inf,
          Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{}),
        FS.FS.block_out(p, G, S, inf, g, groups, Nil{}, 0n, best, rest, skip),
        SolveFast.step(1n+p, rest, G, S, inf, Nil{}, Nil{}, 0n,
          Eval.Eval.block(p, G, S, g, inf, groups, best),
          SolveFast.dummy_zero(), False{}),
        Equal.trans(SolveRef.Best,
          SolveFast.step(1n+p, SolveFast.Begin{g, lb} <> body, G, S, inf,
            Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{}),
          FS.FS.after_begin(1n+p, G, S, inf, g, body, best, skip),
          FS.FS.block_out(p, G, S, inf, g, groups, Nil{}, 0n, best, rest, skip),
          e1, e2),
        e3)

# Folding the pruned schedule over a guess list at positive fuel equals
# `Eval.guesses`.
def FE.guesses_step(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +inf: Nat, +gs: +List<+List<Nat>>, +best: SolveRef.Best,
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    f: FE.EByGs(p, inf, G, S, gs)) ->
  {SolveFast.step(1n+p,
     SolveFast.schedule_go(gs, S, Groups.len_words(S)),
     G, S, inf, Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{})
   == Eval.Eval.guesses(1n+p, G, S, inf, gs, best) : SolveRef.Best}:
  match gs:
    case Nil{}:
      {==}
    case Con{+g, +t}:
      (ecif, ft) = f
      +fgrp : +List<Groups.Group> = SolveFast.groups_build_fast(g, S, Nil{})
      +groups : +List<Groups.Group> = Groups.groups_build(g, S, Nil{})
      +egrp : {fgrp == groups : +List<Groups.Group>} =
        FG.FG.groups_build_eq(g, S, Nil{})
      +usable : Bool = Groups.groups_smaller(S, groups)
      +rest : +List<SolveFast.Item> =
        SolveFast.schedule_go(t, S, Groups.len_words(S))
      +next_best : SolveRef.Best = Eval.Eval.guess(p, G, S, g, inf, best)
      +hnext : {Nat.is_le(Eval.Eval.cost_of(next_best), inf) == True{} : Bool} =
        NatProof.Nat.is_le_trans(
          Eval.Eval.cost_of(next_best), Eval.Eval.cost_of(best), inf,
          Fold.OQ.guess_cost_le_acc(p, G, S, g, inf, best), hbest)
      +e0 : {SolveFast.step(1n+p,
               SolveFast.schedule_guess(g, fgrp, Groups.len_words(S), rest,
                 Groups.groups_smaller(S, fgrp)),
               G, S, inf, Nil{}, Nil{}, 0n, best,
               SolveFast.dummy_zero(), False{})
             == SolveFast.step(1n+p,
                  SolveFast.schedule_guess(g, groups, Groups.len_words(S), rest,
                    usable),
                  G, S, inf, Nil{}, Nil{}, 0n, best,
                  SolveFast.dummy_zero(), False{})
             : SolveRef.Best} =
        Equal.cong(+List<Groups.Group>, SolveRef.Best,
          grp => SolveFast.step(1n+p,
                   SolveFast.schedule_guess(g, grp, Groups.len_words(S), rest,
                     Groups.groups_smaller(S, grp)),
                   G, S, inf, Nil{}, Nil{}, 0n, best,
                   SolveFast.dummy_zero(), False{}),
          fgrp, groups, egrp)
      +e1 : {SolveFast.step(1n+p,
               SolveFast.schedule_guess(g, groups, Groups.len_words(S),
                 rest, usable),
               G, S, inf, Nil{}, Nil{}, 0n, best,
               SolveFast.dummy_zero(), False{})
             == SolveFast.step(1n+p, rest, G, S, inf, Nil{}, Nil{}, 0n,
                  next_best, SolveFast.dummy_zero(), False{})
             : SolveRef.Best} =
        FE.schedule_guess_step(p, G, S, inf, g, groups, rest, best,
          usable, {==}, ele, hz, hbest, ecif)
      +e2 : {SolveFast.step(1n+p, rest, G, S, inf, Nil{}, Nil{}, 0n,
               next_best, SolveFast.dummy_zero(), False{})
             == Eval.Eval.guesses(1n+p, G, S, inf, t, next_best)
             : SolveRef.Best} =
        FE.guesses_step(p, G, S, inf, t, next_best, ele, hz, hnext, ft)
      Equal.trans(SolveRef.Best,
        SolveFast.step(1n+p,
          SolveFast.schedule_go(g <> t, S, Groups.len_words(S)),
          G, S, inf, Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{}),
        SolveFast.step(1n+p, rest, G, S, inf, Nil{}, Nil{}, 0n,
          next_best, SolveFast.dummy_zero(), False{}),
        Eval.Eval.guesses(1n+p, G, S, inf, g <> t, best),
        Equal.trans(SolveRef.Best,
          SolveFast.step(1n+p,
            SolveFast.schedule_go(g <> t, S, Groups.len_words(S)),
            G, S, inf, Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{}),
          SolveFast.step(1n+p,
            SolveFast.schedule_guess(g, groups, Groups.len_words(S),
              rest, usable),
            G, S, inf, Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{}),
          SolveFast.step(1n+p, rest, G, S, inf, Nil{}, Nil{}, 0n,
            next_best, SolveFast.dummy_zero(), False{}),
          e0, e1),
        e2)

# One job at positive fuel `1+p`: `FS.run_at` equals `FS.ref_run_at`.
def FE.ejob_succ(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>,
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    f: FE.EByGs(p, inf, G, S, G)) ->
  FE.EJob(1n+p, inf, G, S):
  +hinit : {Nat.is_le(Eval.Eval.cost_of(SolveFast.dummy_inf(inf)), inf)
            == True{} : Bool} =
    NatProof.Nat.is_le_refl(inf)
  +e1 : {FS.FS.run_at(1n+p, inf, G, S)
         == Eval.Eval.guesses(1n+p, G, S, inf, G, SolveFast.dummy_inf(inf))
         : SolveRef.Best} =
    FE.guesses_step(p, G, S, inf, G, SolveFast.dummy_inf(inf), ele, hz,
      hinit, f)
  +e2 : {FS.FS.ref_run_at(1n+p, inf, G, S)
         == Eval.Eval.guesses(1n+p, G, S, inf, G, Eval.Eval.dummy_inf(inf))
         : SolveRef.Best} =
    Eval.Eval.guesses_step(p, G, S, inf, G, Eval.Eval.dummy_inf(inf))
  Equal.trans(SolveRef.Best,
    FS.FS.run_at(1n+p, inf, G, S),
    Eval.Eval.guesses(1n+p, G, S, inf, G, Eval.Eval.dummy_inf(inf)),
    FS.FS.ref_run_at(1n+p, inf, G, S),
    e1,
    Equal.sym(SolveRef.Best,
      FS.FS.ref_run_at(1n+p, inf, G, S),
      Eval.Eval.guesses(1n+p, G, S, inf, G, Eval.Eval.dummy_inf(inf)),
      e2))

# Zero fuel on the empty candidate list: `SolveFast` folds the guesses with
# cost zero, matching `Eval.guesses(0n, ...)`.
def FE.guesses_zero(+G: +List<+List<Nat>>, +inf: Nat,
    +gs: +List<+List<Nat>>, +best: SolveRef.Best) ->
  {SolveFast.step(0n, SolveFast.schedule_go(gs, Nil{}, 0n), G, Nil{}, inf,
     Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{})
   == Eval.Eval.guesses(0n, G, Nil{}, inf, gs, best) : SolveRef.Best}:
  match gs:
    case Nil{}:
      {==}
    case Con{g, rest}:
      FE.guesses_zero(G, inf, rest,
        SolveRef.finish_guess(inf, g, Nil{}, 0n, Groups.len_words(Nil{}), best))

def FE.ejob_nil(+inf: Nat, +G: +List<+List<Nat>>) -> FE.EJob(0n, inf, G, Nil{}):
  +e1 : {FS.FS.run_at(0n, inf, G, Nil{})
         == Eval.Eval.guesses(0n, G, Nil{}, inf, G, Eval.Eval.dummy_inf(inf))
         : SolveRef.Best} =
    FE.guesses_zero(G, inf, G, Eval.Eval.dummy_inf(inf))
  +e2 : {FS.FS.ref_run_at(0n, inf, G, Nil{})
         == Eval.Eval.guesses(0n, G, Nil{}, inf, G, Eval.Eval.dummy_inf(inf))
         : SolveRef.Best} =
    Eval.Eval.guesses_zero(G, inf, G, Eval.Eval.dummy_inf(inf))
  Equal.trans(SolveRef.Best,
    FS.FS.run_at(0n, inf, G, Nil{}),
    Eval.Eval.guesses(0n, G, Nil{}, inf, G, Eval.Eval.dummy_inf(inf)),
    FS.FS.ref_run_at(0n, inf, G, Nil{}),
    e1,
    Equal.sym(SolveRef.Best,
      FS.FS.ref_run_at(0n, inf, G, Nil{}),
      Eval.Eval.guesses(0n, G, Nil{}, inf, G, Eval.Eval.dummy_inf(inf)),
      e2))

def FE.ejob_transport(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S1: +List<+List<Nat>>, +S2: +List<+List<Nat>>,
    e: {S1 == S2 : +List<+List<Nat>>},
    j: FE.EJob(fuel, inf, G, S1)) -> FE.EJob(fuel, inf, G, S2):
  %e : FE.EJob(fuel, inf, G, _)
  j

def FE.ejob_zero(+inf: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    le: {Nat.is_le(Groups.len_words(S), 0n) == True{} : Bool}) ->
  FE.EJob(0n, inf, G, S):
  +eS : {S == Nil{} : +List<+List<Nat>>} =
    MV.MV.nil_of_len_zero(S,
      NatProof.Nat.eq_zero_of_le_zero(Groups.len_words(S), le))
  FE.ejob_transport(0n, inf, G, Nil{}, S,
    Equal.sym(+List<+List<Nat>>, S, Nil{}, eS), FE.ejob_nil(inf, G))

def FE.eflat_zero(+inf: Nat, +G: +List<+List<Nat>>,
    +jobs: +List<+List<+List<Nat>>>,
    bounds: MV.MV.Bounds(0n, jobs)) -> FE.EFlat(0n, inf, G, jobs):
  match jobs:
    case Nil{}:
      Unit{}
    case Con{S, t}:
      (ble, bt) = bounds
      Tuple{FE.ejob_zero(inf, G, S, ble), FE.eflat_zero(inf, G, t, bt)}

def FE.eflat_step(+inf: Nat, +p: Nat, +G: +List<+List<Nat>>,
    +jobs: +List<+List<+List<Nat>>>,
    bounds: MV.MV.Bounds(1n+p, jobs),
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    f: FE.EFlat(p, inf, G, MV.MV.next_jobs(G, jobs))) ->
  FE.EFlat(1n+p, inf, G, jobs):
  match jobs:
    case Nil{}:
      Unit{}
    case Con{S, t}:
      (ble, bt) = bounds
      MV.MV.use_pair(FE.EFlat(1n+p, inf, G, S <> t),
        FE.EFlat(p, inf, G, MV.MV.next_guess(G, S)),
        FE.EFlat(p, inf, G, MV.MV.next_jobs(G, t)),
        FE.eflat_append(p, inf, G, MV.MV.next_guess(G, S),
          MV.MV.next_jobs(G, t), f),
        fS => ft =>
          Tuple{FE.ejob_succ(p, inf, G, S, ble, hz,
                  FE.eby_gs(p, inf, G, S, G, fS)),
                FE.eflat_step(inf, p, G, t, bt, hz, ft)})

# Copy a `Bounds` witness so it can be used at this level and stepped to the
# next. Every entry is a `Bool` equality (`Data`), so it duplicates cleanly.
def FE.bounds_copy(+fuel: Nat, +jobs: +List<+List<+List<Nat>>>,
    bounds: MV.MV.Bounds(fuel, jobs)) ->
  MV.MV.Bounds(fuel, jobs) & MV.MV.Bounds(fuel, jobs):
  match jobs:
    case Nil{}:
      Tuple{Unit{}, Unit{}}
    case Con{S, t}:
      (+ble, bt) = bounds
      MV.MV.use_pair(
        MV.MV.Bounds(fuel, S <> t) & MV.MV.Bounds(fuel, S <> t),
        MV.MV.Bounds(fuel, t), MV.MV.Bounds(fuel, t),
        FE.bounds_copy(fuel, t, bt),
        b1 => b2 => Tuple{Tuple{ble, b1}, Tuple{ble, b2}})

# The fuel induction over all jobs at a level.
def FE.eflat(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +jobs: +List<+List<+List<Nat>>>,
    bounds: MV.MV.Bounds(fuel, jobs),
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool}) ->
  FE.EFlat(fuel, inf, G, jobs):
  match fuel:
    case 0n:
      FE.eflat_zero(inf, G, jobs, bounds)
    case 1n+p:
      MV.MV.use_pair(FE.EFlat(1n+p, inf, G, jobs),
        MV.MV.Bounds(1n+p, jobs), MV.MV.Bounds(1n+p, jobs),
        FE.bounds_copy(1n+p, jobs, bounds),
        b1 => b2 =>
          FE.eflat_step(inf, p, G, jobs, b1, hz,
            FE.eflat(p, inf, G, MV.MV.next_jobs(G, jobs),
              MV.MV.next_bounds(p, G, jobs, b2), hz)))

# The top-level equality of the pruned and reference search states.
def FE.main_eq(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>,
    +le: {Nat.is_le(Groups.len_words(S), fuel) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool}) ->
  FE.EJob(fuel, inf, G, S):
  MV.MV.use_pair(FE.EJob(fuel, inf, G, S),
    FE.EJob(fuel, inf, G, S), FE.EFlat(fuel, inf, G, Nil{}),
    FE.eflat(fuel, inf, G, S <> Nil{}, Tuple{le, Unit{}}, hz),
    j => u => j)

# The bound-pruned solver returns the exact reference tree for every input.
def FE.solve_fast_eq(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>) ->
  {SolveFast.solve_fast(G, C) == SolveRef.solve(G, C) : Maybe<Tree.Tree>}:
  +n : Nat = Groups.len_words(C)
  +inf : Nat = SolveRef.inf_of(n)
  +hz : {Nat.is_lt(0n, inf) == True{} : Bool} =
    Ind.OQ.zero_lt_succ_add(Nat.mul(n, n))
  +le : {Nat.is_le(Groups.len_words(C), n) == True{} : Bool} =
    NatProof.Nat.is_le_refl(n)
  Equal.cong(SolveRef.Best, Maybe<Tree.Tree>,
    b => SolveRef.best_to_maybe(inf, b),
    FS.FS.run_at(n, inf, G, C),
    FS.FS.ref_run_at(n, inf, G, C),
    FE.main_eq(n, inf, G, C, le, hz))
