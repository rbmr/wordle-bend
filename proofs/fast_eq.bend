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
import ./groupsmeasure.bend as GM
import ./mainvalid.bend as MV
import ./cover_groups.bend as CoverGroups
import ./fast_step.bend as FS
import ./fast_groups.bend as FG
import ./fast_lb.bend as FLB
import ./fast_one.bend as FO

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

# One class step of a live block after `Check` has set the mode to `sk`.
def FE.live_group_step(+p: Nat, +gs: +List<+List<Nat>>, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +inf: Nat, +g: +List<Nat>,
    +fb: +List<Feedback.Color>, +ws: +List<+List<Nat>>,
    +restg: +List<Groups.Group>, +kids: +List<Tree.Child>, +sum: Nat,
    +best: SolveRef.Best, +rest: +List<SolveFast.Item>,
    sk: Bool,
    +esk: {sk == SolveFast.skippable(best,
             Nat.add(sum,
               SolveFast.lower_bound(Groups.len_words(S),
                 Groups.Group{fb, ws} <> restg))) : Bool},
    +ble: {Nat.is_le(Groups.len_words(ws), p) == True{} : Bool},
    bt: MV.MV.Bounds(p, MV.MV.next_groups(restg)),
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    eh: FE.EJob(p, inf, G, ws),
    rec_live: {SolveFast.step(1n+p, gs,
                  List.append(&2, SolveFast.Item,
                    SolveFast.group_items(Groups.len_words(S), restg),
                    SolveFast.End{} <> rest),
                  G, S, inf, g,
                  Tree.Child{fb, Eval.Eval.tree_of(FS.FS.ref_run_at(p, inf, G, ws))}
                    <> kids,
                  SolveRef.sat_add(inf, sum,
                    Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, ws))),
                  best, SolveFast.dummy_zero(), False{})
                == SolveFast.step(1n+p, gs, rest, G, S, inf, Nil{}, Nil{}, 0n,
                     Eval.Eval.finish_ks(inf, g, S,
                       Eval.Eval.items(p, G, S, g, restg,
                         Tree.Child{fb, Eval.Eval.tree_of(FS.FS.ref_run_at(p, inf, G, ws))}
                           <> kids,
                         SolveRef.sat_add(inf, sum,
                           Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, ws))),
                         inf),
                       best),
                     SolveFast.dummy_zero(), False{})
                : SolveRef.Best}) ->
  {SolveFast.step(1n+p, gs,
     SolveFast.ClassItem{fb, ws}
       <> (SolveFast.Add{fb}
           <> List.append(&2, SolveFast.Item,
                SolveFast.group_items(Groups.len_words(S), restg),
                SolveFast.End{} <> rest)),
     G, S, inf, g, kids, sum, best, SolveFast.dummy_zero(), sk)
   == SolveFast.step(1n+p, gs, rest, G, S, inf, Nil{}, Nil{}, 0n,
        Eval.Eval.finish_ks(inf, g, S,
          Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg,
            kids, sum, inf),
          best),
        SolveFast.dummy_zero(), False{})
   : SolveRef.Best}:
  match sk:
    case True{}:
      +n : Nat = Groups.len_words(S)
      +groups : +List<Groups.Group> = Groups.Group{fb, ws} <> restg
      +rem_lb : Nat = SolveFast.lower_bound(n, groups)
      +inner : +List<SolveFast.Item> =
        List.append(&2, SolveFast.Item, SolveFast.group_items(n, restg),
          SolveFast.End{} <> rest)
      +le : {Nat.is_le(Eval.Eval.cost_of(best), Nat.add(sum, rem_lb))
             == True{} : Bool} =
        FLB.FS.skippable_to_le(best, Nat.add(sum, rem_lb),
          Equal.sym(Bool, True{},
            SolveFast.skippable(best, Nat.add(sum, rem_lb)), esk))
      +feq : {Eval.Eval.finish_ks(inf, g, S,
                Eval.Eval.items(p, G, S, g, groups, kids, sum, inf), best)
              == best : SolveRef.Best} =
        FLB.FS.finish_skip_eq(p, inf, G, S, g, groups, kids, sum, best,
          Tuple{ble, bt}, hz, hbest, le)
      +e1 : {SolveFast.step(1n+p, gs,
               SolveFast.ClassItem{fb, ws} <> (SolveFast.Add{fb} <> inner),
               G, S, inf, g, kids, sum, best, SolveFast.dummy_zero(), True{})
             == SolveFast.step(1n+p, gs, rest, G, S, inf, Nil{}, Nil{}, 0n, best,
                  SolveFast.dummy_zero(), False{})
             : SolveRef.Best} =
        FS.FS.tail_dead(p, gs, G, S, n, inf, g, fb, ws, restg, kids, sum, best,
          rest)
      +e2 : {SolveFast.step(1n+p, gs, rest, G, S, inf, Nil{}, Nil{}, 0n, best,
               SolveFast.dummy_zero(), False{})
             == SolveFast.step(1n+p, gs, rest, G, S, inf, Nil{}, Nil{}, 0n,
                  Eval.Eval.finish_ks(inf, g, S,
                    Eval.Eval.items(p, G, S, g, groups, kids, sum, inf), best),
                  SolveFast.dummy_zero(), False{})
             : SolveRef.Best} =
        Equal.cong(SolveRef.Best, SolveRef.Best,
          b => SolveFast.step(1n+p, gs, rest, G, S, inf, Nil{}, Nil{}, 0n, b,
                 SolveFast.dummy_zero(), False{}),
          best,
          Eval.Eval.finish_ks(inf, g, S,
            Eval.Eval.items(p, G, S, g, groups, kids, sum, inf), best),
          Equal.sym(SolveRef.Best,
            Eval.Eval.finish_ks(inf, g, S,
              Eval.Eval.items(p, G, S, g, groups, kids, sum, inf), best),
            best, feq))
      Equal.trans(SolveRef.Best,
        SolveFast.step(1n+p, gs,
          SolveFast.ClassItem{fb, ws} <> (SolveFast.Add{fb} <> inner),
          G, S, inf, g, kids, sum, best, SolveFast.dummy_zero(), True{}),
        SolveFast.step(1n+p, gs, rest, G, S, inf, Nil{}, Nil{}, 0n, best,
          SolveFast.dummy_zero(), False{}),
        SolveFast.step(1n+p, gs, rest, G, S, inf, Nil{}, Nil{}, 0n,
          Eval.Eval.finish_ks(inf, g, S,
            Eval.Eval.items(p, G, S, g, groups, kids, sum, inf), best),
          SolveFast.dummy_zero(), False{}),
        e1, e2)
    case False{}:
      +n : Nat = Groups.len_words(S)
      +inner : +List<SolveFast.Item> =
        List.append(&2, SolveFast.Item, SolveFast.group_items(n, restg),
          SolveFast.End{} <> rest)
      +fast_c : SolveRef.Best = FS.FS.run_at(p, inf, G, ws)
      +ref_c : SolveRef.Best = FS.FS.ref_run_at(p, inf, G, ws)
      +kf : +List<Tree.Child> =
        Tree.Child{fb, Eval.Eval.tree_of(fast_c)} <> kids
      +sf : Nat = SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(fast_c))
      +kr : +List<Tree.Child> =
        Tree.Child{fb, Eval.Eval.tree_of(ref_c)} <> kids
      +sr : Nat = SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(ref_c))
      +e1 : {SolveFast.step(1n+p, gs,
               SolveFast.ClassItem{fb, ws} <> (SolveFast.Add{fb} <> inner),
               G, S, inf, g, kids, sum, best, SolveFast.dummy_zero(), False{})
             == SolveFast.step(1n+p, gs, inner, G, S, inf, g, kf, sf, best,
                  SolveFast.dummy_zero(), False{})
             : SolveRef.Best} =
        FS.FS.class_add_live(p, gs, G, S, inf, g, fb, ws, inner, kids, sum,
          best)
      +e2 : {SolveFast.step(1n+p, gs, inner, G, S, inf, g, kf, sf, best,
               SolveFast.dummy_zero(), False{})
             == SolveFast.step(1n+p, gs, inner, G, S, inf, g, kr, sr, best,
                  SolveFast.dummy_zero(), False{})
             : SolveRef.Best} =
        Equal.cong(SolveRef.Best, SolveRef.Best,
          c => SolveFast.step(1n+p, gs, inner, G, S, inf, g,
                 Tree.Child{fb, Eval.Eval.tree_of(c)} <> kids,
                 SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(c)),
                 best, SolveFast.dummy_zero(), False{}),
          fast_c, ref_c, eh)
      +wk : {Eval.Eval.items(p, G, S, g, restg, kr, sr, inf)
             == Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg,
                  kids, sum, inf)
             : Eval.KS} =
        Equal.sym(Eval.KS,
          Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg,
            kids, sum, inf),
          Eval.Eval.items(p, G, S, g, restg, kr, sr, inf),
          Eval.Eval.with_kid_eq(fb, kids, sum, inf, ref_c,
            ka => sa => Eval.Eval.items(p, G, S, g, restg, ka, sa, inf)))
      +e4 : {SolveFast.step(1n+p, gs, rest, G, S, inf, Nil{}, Nil{}, 0n,
               Eval.Eval.finish_ks(inf, g, S,
                 Eval.Eval.items(p, G, S, g, restg, kr, sr, inf), best),
               SolveFast.dummy_zero(), False{})
             == SolveFast.step(1n+p, gs, rest, G, S, inf, Nil{}, Nil{}, 0n,
                  Eval.Eval.finish_ks(inf, g, S,
                    Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg,
                      kids, sum, inf),
                    best),
                  SolveFast.dummy_zero(), False{})
             : SolveRef.Best} =
        Equal.cong(Eval.KS, SolveRef.Best,
          ks => SolveFast.step(1n+p, gs, rest, G, S, inf, Nil{}, Nil{}, 0n,
                  Eval.Eval.finish_ks(inf, g, S, ks, best),
                  SolveFast.dummy_zero(), False{}),
          Eval.Eval.items(p, G, S, g, restg, kr, sr, inf),
          Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg,
            kids, sum, inf),
          wk)
      Equal.trans(SolveRef.Best,
        SolveFast.step(1n+p, gs,
          SolveFast.ClassItem{fb, ws} <> (SolveFast.Add{fb} <> inner),
          G, S, inf, g, kids, sum, best, SolveFast.dummy_zero(), False{}),
        SolveFast.step(1n+p, gs, inner, G, S, inf, g, kr, sr, best,
          SolveFast.dummy_zero(), False{}),
        SolveFast.step(1n+p, gs, rest, G, S, inf, Nil{}, Nil{}, 0n,
          Eval.Eval.finish_ks(inf, g, S,
            Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg,
              kids, sum, inf),
            best),
          SolveFast.dummy_zero(), False{}),
        Equal.trans(SolveRef.Best,
          SolveFast.step(1n+p, gs,
            SolveFast.ClassItem{fb, ws} <> (SolveFast.Add{fb} <> inner),
            G, S, inf, g, kids, sum, best, SolveFast.dummy_zero(), False{}),
          SolveFast.step(1n+p, gs, inner, G, S, inf, g, kf, sf, best,
            SolveFast.dummy_zero(), False{}),
          SolveFast.step(1n+p, gs, inner, G, S, inf, g, kr, sr, best,
            SolveFast.dummy_zero(), False{}),
          e1, e2),
        Equal.trans(SolveRef.Best,
          SolveFast.step(1n+p, gs, inner, G, S, inf, g, kr, sr, best,
            SolveFast.dummy_zero(), False{}),
          SolveFast.step(1n+p, gs, rest, G, S, inf, Nil{}, Nil{}, 0n,
            Eval.Eval.finish_ks(inf, g, S,
              Eval.Eval.items(p, G, S, g, restg, kr, sr, inf), best),
            SolveFast.dummy_zero(), False{}),
          SolveFast.step(1n+p, gs, rest, G, S, inf, Nil{}, Nil{}, 0n,
            Eval.Eval.finish_ks(inf, g, S,
              Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg,
                kids, sum, inf),
              best),
            SolveFast.dummy_zero(), False{}),
          rec_live, e4))

# Step `Check` in a live block and hand the resulting mode to `FE.live_group_step`.
def FE.live_groups_cons(+p: Nat, +gs: +List<+List<Nat>>, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +inf: Nat, +g: +List<Nat>,
    +fb: +List<Feedback.Color>, +ws: +List<+List<Nat>>,
    +restg: +List<Groups.Group>, +kids: +List<Tree.Child>, +sum: Nat,
    +best: SolveRef.Best, +rest: +List<SolveFast.Item>,
    +ble: {Nat.is_le(Groups.len_words(ws), p) == True{} : Bool},
    bt: MV.MV.Bounds(p, MV.MV.next_groups(restg)),
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    eh: FE.EJob(p, inf, G, ws),
    rec_live: {SolveFast.step(1n+p, gs,
                  List.append(&2, SolveFast.Item,
                    SolveFast.group_items(Groups.len_words(S), restg),
                    SolveFast.End{} <> rest),
                  G, S, inf, g,
                  Tree.Child{fb, Eval.Eval.tree_of(FS.FS.ref_run_at(p, inf, G, ws))}
                    <> kids,
                  SolveRef.sat_add(inf, sum,
                    Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, ws))),
                  best, SolveFast.dummy_zero(), False{})
                == SolveFast.step(1n+p, gs, rest, G, S, inf, Nil{}, Nil{}, 0n,
                     Eval.Eval.finish_ks(inf, g, S,
                       Eval.Eval.items(p, G, S, g, restg,
                         Tree.Child{fb, Eval.Eval.tree_of(FS.FS.ref_run_at(p, inf, G, ws))}
                           <> kids,
                         SolveRef.sat_add(inf, sum,
                           Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, ws))),
                         inf),
                       best),
                     SolveFast.dummy_zero(), False{})
                : SolveRef.Best}) ->
  {SolveFast.step(1n+p, gs,
     SolveFast.Check{SolveFast.lower_bound(Groups.len_words(S),
       Groups.Group{fb, ws} <> restg)}
       <> (SolveFast.ClassItem{fb, ws}
           <> (SolveFast.Add{fb}
               <> List.append(&2, SolveFast.Item,
                    SolveFast.group_items(Groups.len_words(S), restg),
                    SolveFast.End{} <> rest))),
     G, S, inf, g, kids, sum, best, SolveFast.dummy_zero(), False{})
   == SolveFast.step(1n+p, gs, rest, G, S, inf, Nil{}, Nil{}, 0n,
        Eval.Eval.finish_ks(inf, g, S,
          Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg,
            kids, sum, inf),
          best),
        SolveFast.dummy_zero(), False{})
   : SolveRef.Best}:
  +n : Nat = Groups.len_words(S)
  +rem_lb : Nat = SolveFast.lower_bound(n, Groups.Group{fb, ws} <> restg)
  +sk : Bool = SolveFast.skippable(best, Nat.add(sum, rem_lb))
  +after_check : +List<SolveFast.Item> =
    SolveFast.ClassItem{fb, ws}
      <> (SolveFast.Add{fb}
          <> List.append(&2, SolveFast.Item,
               SolveFast.group_items(n, restg),
               SolveFast.End{} <> rest))
  +e1 : {SolveFast.step(1n+p, gs, SolveFast.Check{rem_lb} <> after_check,
           G, S, inf, g, kids, sum, best, SolveFast.dummy_zero(), False{})
         == SolveFast.step(1n+p, gs, after_check, G, S, inf, g, kids, sum, best,
              SolveFast.dummy_zero(), sk)
         : SolveRef.Best} =
    FS.FS.check_live(p, gs, G, S, inf, g, rem_lb, after_check, kids, sum, best,
      SolveFast.dummy_zero(), sk, {==})
  +e2 : {SolveFast.step(1n+p, gs, after_check, G, S, inf, g, kids, sum, best,
           SolveFast.dummy_zero(), sk)
         == SolveFast.step(1n+p, gs, rest, G, S, inf, Nil{}, Nil{}, 0n,
              Eval.Eval.finish_ks(inf, g, S,
                Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg,
                  kids, sum, inf),
                best),
              SolveFast.dummy_zero(), False{})
         : SolveRef.Best} =
    FE.live_group_step(p, gs, G, S, inf, g, fb, ws, restg, kids, sum, best,
      rest, sk, {==}, ble, bt, hz, hbest, eh, rec_live)
  Equal.trans(SolveRef.Best,
    SolveFast.step(1n+p, gs, SolveFast.Check{rem_lb} <> after_check,
      G, S, inf, g, kids, sum, best, SolveFast.dummy_zero(), False{}),
    SolveFast.step(1n+p, gs, after_check, G, S, inf, g, kids, sum, best,
      SolveFast.dummy_zero(), sk),
    SolveFast.step(1n+p, gs, rest, G, S, inf, Nil{}, Nil{}, 0n,
      Eval.Eval.finish_ks(inf, g, S,
        Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg,
          kids, sum, inf),
        best),
      SolveFast.dummy_zero(), False{}),
    e1, e2)

# Step a live singleton `OneItem{fb, w}` directly into `Node{w, []}` of cost 1.
def FE.live_groups_one(+p: Nat, +gs: +List<+List<Nat>>, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +inf: Nat, +g: +List<Nat>,
    +fb: +List<Feedback.Color>, +w: +List<Nat>,
    +restg: +List<Groups.Group>, +kids: +List<Tree.Child>, +sum: Nat,
    +best: SolveRef.Best, +rest: +List<SolveFast.Item>,
    +ble: {Nat.is_le(1n, p) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +win: {Tree.member_word(w, G) == True{} : Bool},
    rec_live: {SolveFast.step(1n+p, gs,
                  List.append(&2, SolveFast.Item,
                    SolveFast.group_items(Groups.len_words(S), restg),
                    SolveFast.End{} <> rest),
                  G, S, inf, g,
                  Tree.Child{fb, Eval.Eval.tree_of(
                    FS.FS.ref_run_at(p, inf, G, w <> Nil{}))} <> kids,
                  SolveRef.sat_add(inf, sum,
                    Eval.Eval.cost_of(
                      FS.FS.ref_run_at(p, inf, G, w <> Nil{}))),
                  best, SolveFast.dummy_zero(), False{})
                == SolveFast.step(1n+p, gs, rest, G, S, inf, Nil{}, Nil{}, 0n,
                     Eval.Eval.finish_ks(inf, g, S,
                       Eval.Eval.items(p, G, S, g, restg,
                         Tree.Child{fb, Eval.Eval.tree_of(
                           FS.FS.ref_run_at(p, inf, G, w <> Nil{}))} <> kids,
                         SolveRef.sat_add(inf, sum,
                           Eval.Eval.cost_of(
                             FS.FS.ref_run_at(p, inf, G, w <> Nil{}))),
                         inf),
                       best),
                     SolveFast.dummy_zero(), False{})
                : SolveRef.Best}) ->
  {SolveFast.step(1n+p, gs,
     SolveFast.OneItem{fb, w}
       <> List.append(&2, SolveFast.Item,
            SolveFast.group_items(Groups.len_words(S), restg),
            SolveFast.End{} <> rest),
     G, S, inf, g, kids, sum, best, SolveFast.dummy_zero(), False{})
   == SolveFast.step(1n+p, gs, rest, G, S, inf, Nil{}, Nil{}, 0n,
        Eval.Eval.finish_ks(inf, g, S,
          Eval.Eval.items(p, G, S, g,
            Groups.Group{fb, w <> Nil{}} <> restg, kids, sum, inf),
          best),
        SolveFast.dummy_zero(), False{})
   : SolveRef.Best}:
  +n : Nat = Groups.len_words(S)
  +inner : +List<SolveFast.Item> =
    List.append(&2, SolveFast.Item, SolveFast.group_items(n, restg),
      SolveFast.End{} <> rest)
  +b1 : SolveRef.Best = SolveRef.Best{Tree.Node{w, Nil{}}, 1n}
  +ref_c : SolveRef.Best = FS.FS.ref_run_at(p, inf, G, w <> Nil{})
  +eone : {b1 == ref_c : SolveRef.Best} =
    FO.FO.ref_run_one_eq(p, inf, G, w, ble, h1, win)
  +kr : +List<Tree.Child> = Tree.Child{fb, Eval.Eval.tree_of(ref_c)} <> kids
  +sr : Nat = SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(ref_c))
  +e1 : {SolveFast.step(1n+p, gs, SolveFast.OneItem{fb, w} <> inner,
           G, S, inf, g, kids, sum, best, SolveFast.dummy_zero(), False{})
         == SolveFast.step(1n+p, gs, inner, G, S, inf, g,
              Tree.Child{fb, Tree.Node{w, Nil{}}} <> kids,
              SolveRef.sat_add(inf, sum, 1n), best,
              SolveFast.dummy_zero(), False{})
         : SolveRef.Best} =
    FS.FS.one_live(p, gs, G, S, inf, g, fb, w, inner, kids, sum, best)
  +e2 : {SolveFast.step(1n+p, gs, inner, G, S, inf, g,
           Tree.Child{fb, Tree.Node{w, Nil{}}} <> kids,
           SolveRef.sat_add(inf, sum, 1n), best,
           SolveFast.dummy_zero(), False{})
         == SolveFast.step(1n+p, gs, inner, G, S, inf, g, kr, sr, best,
              SolveFast.dummy_zero(), False{})
         : SolveRef.Best} =
    Equal.cong(SolveRef.Best, SolveRef.Best,
      c => SolveFast.step(1n+p, gs, inner, G, S, inf, g,
             Tree.Child{fb, Eval.Eval.tree_of(c)} <> kids,
             SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(c)),
             best, SolveFast.dummy_zero(), False{}),
      b1, ref_c, eone)
  +wk : {Eval.Eval.items(p, G, S, g, restg, kr, sr, inf)
         == Eval.Eval.items(p, G, S, g,
              Groups.Group{fb, w <> Nil{}} <> restg, kids, sum, inf)
         : Eval.KS} =
    Equal.sym(Eval.KS,
      Eval.Eval.items(p, G, S, g, Groups.Group{fb, w <> Nil{}} <> restg,
        kids, sum, inf),
      Eval.Eval.items(p, G, S, g, restg, kr, sr, inf),
      Eval.Eval.with_kid_eq(fb, kids, sum, inf, ref_c,
        ka => sa => Eval.Eval.items(p, G, S, g, restg, ka, sa, inf)))
  +e4 : {SolveFast.step(1n+p, gs, rest, G, S, inf, Nil{}, Nil{}, 0n,
           Eval.Eval.finish_ks(inf, g, S,
             Eval.Eval.items(p, G, S, g, restg, kr, sr, inf), best),
           SolveFast.dummy_zero(), False{})
         == SolveFast.step(1n+p, gs, rest, G, S, inf, Nil{}, Nil{}, 0n,
              Eval.Eval.finish_ks(inf, g, S,
                Eval.Eval.items(p, G, S, g,
                  Groups.Group{fb, w <> Nil{}} <> restg, kids, sum, inf),
                best),
              SolveFast.dummy_zero(), False{})
         : SolveRef.Best} =
    Equal.cong(Eval.KS, SolveRef.Best,
      ks => SolveFast.step(1n+p, gs, rest, G, S, inf, Nil{}, Nil{}, 0n,
              Eval.Eval.finish_ks(inf, g, S, ks, best),
              SolveFast.dummy_zero(), False{}),
      Eval.Eval.items(p, G, S, g, restg, kr, sr, inf),
      Eval.Eval.items(p, G, S, g, Groups.Group{fb, w <> Nil{}} <> restg,
        kids, sum, inf),
      wk)
  Equal.trans(SolveRef.Best,
    SolveFast.step(1n+p, gs, SolveFast.OneItem{fb, w} <> inner,
      G, S, inf, g, kids, sum, best, SolveFast.dummy_zero(), False{}),
    SolveFast.step(1n+p, gs, inner, G, S, inf, g, kr, sr, best,
      SolveFast.dummy_zero(), False{}),
    SolveFast.step(1n+p, gs, rest, G, S, inf, Nil{}, Nil{}, 0n,
      Eval.Eval.finish_ks(inf, g, S,
        Eval.Eval.items(p, G, S, g, Groups.Group{fb, w <> Nil{}} <> restg,
          kids, sum, inf),
        best),
      SolveFast.dummy_zero(), False{}),
    Equal.trans(SolveRef.Best,
      SolveFast.step(1n+p, gs, SolveFast.OneItem{fb, w} <> inner,
        G, S, inf, g, kids, sum, best, SolveFast.dummy_zero(), False{}),
      SolveFast.step(1n+p, gs, inner, G, S, inf, g,
        Tree.Child{fb, Tree.Node{w, Nil{}}} <> kids,
        SolveRef.sat_add(inf, sum, 1n), best,
        SolveFast.dummy_zero(), False{}),
      SolveFast.step(1n+p, gs, inner, G, S, inf, g, kr, sr, best,
        SolveFast.dummy_zero(), False{}),
      e1, e2),
    Equal.trans(SolveRef.Best,
      SolveFast.step(1n+p, gs, inner, G, S, inf, g, kr, sr, best,
        SolveFast.dummy_zero(), False{}),
      SolveFast.step(1n+p, gs, rest, G, S, inf, Nil{}, Nil{}, 0n,
        Eval.Eval.finish_ks(inf, g, S,
          Eval.Eval.items(p, G, S, g, restg, kr, sr, inf), best),
        SolveFast.dummy_zero(), False{}),
      SolveFast.step(1n+p, gs, rest, G, S, inf, Nil{}, Nil{}, 0n,
        Eval.Eval.finish_ks(inf, g, S,
          Eval.Eval.items(p, G, S, g, Groups.Group{fb, w <> Nil{}} <> restg,
            kids, sum, inf),
          best),
        SolveFast.dummy_zero(), False{}),
      rec_live, e4))

# Stepping the remaining class items of a live block agrees with `Eval.finish_ks`
# on `Eval.items`, whether a class resolves in O(1) as a singleton, triggers
# mid-guess pruning, or searches recursively.
def FE.live_groups_eq(+p: Nat, +gs: +List<+List<Nat>>, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +inf: Nat, +g: +List<Nat>,
    +groups: +List<Groups.Group>, +kids: +List<Tree.Child>, +sum: Nat,
    +best: SolveRef.Best, +rest: +List<SolveFast.Item>,
    bounds: MV.MV.Bounds(p, MV.MV.next_groups(groups)),
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +ag: {FO.FO.all_in_jobs_b(MV.MV.next_groups(groups), G) == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    ec: FE.EClass(p, inf, G, groups)) ->
  {SolveFast.step(1n+p, gs,
     List.append(&2, SolveFast.Item,
       SolveFast.group_items(Groups.len_words(S), groups),
       SolveFast.End{} <> rest),
     G, S, inf, g, kids, sum, best, SolveFast.dummy_zero(), False{})
   == SolveFast.step(1n+p, gs, rest, G, S, inf, Nil{}, Nil{}, 0n,
        Eval.Eval.finish_ks(inf, g, S,
          Eval.Eval.items(p, G, S, g, groups, kids, sum, inf), best),
        SolveFast.dummy_zero(), False{})
   : SolveRef.Best}:
  match groups:
    case Nil{}:
      FS.FS.end_step(p, gs, G, S, inf, g, kids, sum, best,
        SolveFast.dummy_zero(), rest, False{})
    case Con{gp, restg}:
      match gp:
        case Groups.Group{+fb, +ws}:
          match ws:
            case Nil{}:
              (+ble, bt) = bounds
              (eh, et) = ec
              +ag_rest : {FO.FO.all_in_jobs_b(MV.MV.next_groups(restg), G)
                          == True{} : Bool} =
                Logic.Proof.and_true_r(FO.FO.all_in_ref(Nil{}, G),
                  FO.FO.all_in_jobs_b(MV.MV.next_groups(restg), G), ag)
              MV.MV.use_pair(
                {SolveFast.step(1n+p, gs,
                   List.append(&2, SolveFast.Item,
                     SolveFast.group_items(Groups.len_words(S),
                       Groups.Group{fb, Nil{}} <> restg),
                     SolveFast.End{} <> rest),
                   G, S, inf, g, kids, sum, best,
                   SolveFast.dummy_zero(), False{})
                 == SolveFast.step(1n+p, gs, rest, G, S, inf, Nil{}, Nil{}, 0n,
                      Eval.Eval.finish_ks(inf, g, S,
                        Eval.Eval.items(p, G, S, g,
                          Groups.Group{fb, Nil{}} <> restg, kids, sum, inf),
                        best),
                      SolveFast.dummy_zero(), False{})
                 : SolveRef.Best},
                MV.MV.Bounds(p, MV.MV.next_groups(restg)),
                MV.MV.Bounds(p, MV.MV.next_groups(restg)),
                FE.bounds_copy(p, MV.MV.next_groups(restg), bt),
                bt1 => bt2 =>
                  FE.live_groups_cons(p, gs, G, S, inf, g, fb, Nil{}, restg,
                    kids, sum, best, rest, ble, bt2, hz, hbest, eh,
                    FE.live_groups_eq(p, gs, G, S, inf, g, restg,
                      Tree.Child{fb, Eval.Eval.tree_of(
                        FS.FS.ref_run_at(p, inf, G, Nil{}))} <> kids,
                      SolveRef.sat_add(inf, sum,
                        Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, Nil{}))),
                      best, rest, bt1, hz, h1, ag_rest, hbest, et)))
            case Con{+w, +wt}:
              match wt:
                case Nil{}:
                  (+ble, bt) = bounds
                  (eh, et) = ec
                  +ai_ws : {FO.FO.all_in_ref(w <> Nil{}, G) == True{} : Bool} =
                    Logic.Proof.and_true_l(FO.FO.all_in_ref(w <> Nil{}, G),
                      FO.FO.all_in_jobs_b(MV.MV.next_groups(restg), G), ag)
                  +ag_rest : {FO.FO.all_in_jobs_b(MV.MV.next_groups(restg), G)
                              == True{} : Bool} =
                    Logic.Proof.and_true_r(FO.FO.all_in_ref(w <> Nil{}, G),
                      FO.FO.all_in_jobs_b(MV.MV.next_groups(restg), G), ag)
                  +win : {Tree.member_word(w, G) == True{} : Bool} =
                    FO.FO.all_in_head(w, Nil{}, G, ai_ws)
                  FE.live_groups_one(p, gs, G, S, inf, g, fb, w, restg,
                    kids, sum, best, rest, ble, h1, win,
                    FE.live_groups_eq(p, gs, G, S, inf, g, restg,
                      Tree.Child{fb, Eval.Eval.tree_of(
                        FS.FS.ref_run_at(p, inf, G, w <> Nil{}))} <> kids,
                      SolveRef.sat_add(inf, sum,
                        Eval.Eval.cost_of(
                          FS.FS.ref_run_at(p, inf, G, w <> Nil{}))),
                      best, rest, bt, hz, h1, ag_rest, hbest, et))
                case Con{+w2, +wt2}:
                  (+ble, bt) = bounds
                  (eh, et) = ec
                  +ws2 : +List<+List<Nat>> = w <> (w2 <> wt2)
                  +ag_rest : {FO.FO.all_in_jobs_b(MV.MV.next_groups(restg), G)
                              == True{} : Bool} =
                    Logic.Proof.and_true_r(FO.FO.all_in_ref(ws2, G),
                      FO.FO.all_in_jobs_b(MV.MV.next_groups(restg), G), ag)
                  MV.MV.use_pair(
                    {SolveFast.step(1n+p, gs,
                       List.append(&2, SolveFast.Item,
                         SolveFast.group_items(Groups.len_words(S),
                           Groups.Group{fb, ws2} <> restg),
                         SolveFast.End{} <> rest),
                       G, S, inf, g, kids, sum, best,
                       SolveFast.dummy_zero(), False{})
                     == SolveFast.step(1n+p, gs, rest, G, S, inf, Nil{}, Nil{},
                          0n, Eval.Eval.finish_ks(inf, g, S,
                            Eval.Eval.items(p, G, S, g,
                              Groups.Group{fb, ws2} <> restg, kids, sum, inf),
                            best),
                          SolveFast.dummy_zero(), False{})
                     : SolveRef.Best},
                    MV.MV.Bounds(p, MV.MV.next_groups(restg)),
                    MV.MV.Bounds(p, MV.MV.next_groups(restg)),
                    FE.bounds_copy(p, MV.MV.next_groups(restg), bt),
                    bt1 => bt2 =>
                      FE.live_groups_cons(p, gs, G, S, inf, g, fb, ws2, restg,
                        kids, sum, best, rest, ble, bt2, hz, hbest, eh,
                        FE.live_groups_eq(p, gs, G, S, inf, g, restg,
                          Tree.Child{fb, Eval.Eval.tree_of(
                            FS.FS.ref_run_at(p, inf, G, ws2))} <> kids,
                          SolveRef.sat_add(inf, sum,
                            Eval.Eval.cost_of(
                              FS.FS.ref_run_at(p, inf, G, ws2))),
                          best, rest, bt1, hz, h1, ag_rest, hbest, et)))

# Stepping the body of a usable guess block after `Begin` agrees with
# `Eval.block` in both the skipped and the searched mode.
def FE.block_step_eq(+p: Nat, +gs: +List<+List<Nat>>, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +inf: Nat, +g: +List<Nat>,
    +groups: +List<Groups.Group>, +rest: +List<SolveFast.Item>,
    +best: SolveRef.Best, skip: Bool,
    +esk: {skip == SolveFast.skippable(best,
             SolveFast.lower_bound(Groups.len_words(S), groups)) : Bool},
    +us: {Groups.groups_smaller(S, groups) == True{} : Bool},
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +ag: {FO.FO.all_in_jobs_b(MV.MV.next_groups(groups), G) == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    ec: FE.EClass(p, inf, G, groups)) ->
  {FS.FS.after_begin(1n+p, gs, G, S, inf, g,
     List.append(&2, SolveFast.Item,
       SolveFast.group_items(Groups.len_words(S), groups),
       SolveFast.End{} <> rest),
     best, skip)
   == SolveFast.step(1n+p, gs, rest, G, S, inf, Nil{}, Nil{}, 0n,
        Eval.Eval.block(p, G, S, g, inf, groups, best),
        SolveFast.dummy_zero(), False{})
   : SolveRef.Best}:
  match skip:
    case True{}:
      +n : Nat = Groups.len_words(S)
      +le : {Nat.is_le(Eval.Eval.cost_of(best),
               SolveFast.lower_bound(n, groups))
             == True{} : Bool} =
        FLB.FS.skippable_to_le(best,
          SolveFast.lower_bound(n, groups),
          Equal.sym(Bool, True{},
            SolveFast.skippable(best,
              SolveFast.lower_bound(n, groups)), esk))
      +beq : {Eval.Eval.block(p, G, S, g, inf, groups, best) == best
              : SolveRef.Best} =
        FLB.FS.block_skip_eq(p, inf, G, S, g, groups, best, us, ele, hz,
          hbest, le)
      +e1 : {FS.FS.after_begin(1n+p, gs, G, S, inf, g,
               List.append(&2, SolveFast.Item,
                 SolveFast.group_items(n, groups),
                 SolveFast.End{} <> rest),
               best, True{})
             == SolveFast.step(1n+p, gs, rest, G, S, inf, Nil{}, Nil{}, 0n,
                  best, SolveFast.dummy_zero(), False{})
             : SolveRef.Best} =
        FS.FS.block_dead(p, gs, G, S, n, inf, g, groups, Nil{}, 0n, best, rest)
      +e2 : {SolveFast.step(1n+p, gs, rest, G, S, inf, Nil{}, Nil{}, 0n, best,
               SolveFast.dummy_zero(), False{})
             == SolveFast.step(1n+p, gs, rest, G, S, inf, Nil{}, Nil{}, 0n,
                  Eval.Eval.block(p, G, S, g, inf, groups, best),
                  SolveFast.dummy_zero(), False{})
             : SolveRef.Best} =
        Equal.cong(SolveRef.Best, SolveRef.Best,
          b => SolveFast.step(1n+p, gs, rest, G, S, inf, Nil{}, Nil{}, 0n, b,
                 SolveFast.dummy_zero(), False{}),
          best, Eval.Eval.block(p, G, S, g, inf, groups, best),
          Equal.sym(SolveRef.Best,
            Eval.Eval.block(p, G, S, g, inf, groups, best), best, beq))
      Equal.trans(SolveRef.Best,
        FS.FS.after_begin(1n+p, gs, G, S, inf, g,
          List.append(&2, SolveFast.Item,
            SolveFast.group_items(n, groups),
            SolveFast.End{} <> rest),
          best, True{}),
        SolveFast.step(1n+p, gs, rest, G, S, inf, Nil{}, Nil{}, 0n, best,
          SolveFast.dummy_zero(), False{}),
        SolveFast.step(1n+p, gs, rest, G, S, inf, Nil{}, Nil{}, 0n,
          Eval.Eval.block(p, G, S, g, inf, groups, best),
          SolveFast.dummy_zero(), False{}),
        e1, e2)
    case False{}:
      bounds : MV.MV.Bounds(p, MV.MV.next_groups(groups)) =
        MV.MV.group_bounds(p, S, groups, ele,
          GM.GM.groups_smaller_sound(S, groups, us))
      FE.live_groups_eq(p, gs, G, S, inf, g, groups, Nil{}, 0n, best, rest,
        bounds, hz, h1, ag, hbest, ec)

# Stepping one guess block in `SolveFast` at positive fuel agrees with
# `Eval.guess_bool`.
def FE.schedule_guess_step(+p: Nat, +gs: +List<+List<Nat>>,
    +G: +List<+List<Nat>>, +S: +List<+List<Nat>>, +inf: Nat, +g: +List<Nat>,
    +groups: +List<Groups.Group>, +rest: +List<SolveFast.Item>,
    +best: SolveRef.Best, usable: Bool,
    +eus: {usable == Groups.groups_smaller(S, groups) : Bool},
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +ag: {FO.FO.all_in_jobs_b(MV.MV.next_groups(groups), G) == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    ecif: FE.EClassIf(usable, p, inf, G, groups)) ->
  {SolveFast.step(1n+p, gs,
     SolveFast.schedule_guess(g, groups, Groups.len_words(S), rest, usable),
     G, S, inf, Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{})
   == SolveFast.step(1n+p, gs, rest, G, S, inf, Nil{}, Nil{}, 0n,
        Eval.Eval.guess_bool(p, G, S, g, groups, inf, usable, best),
        SolveFast.dummy_zero(), False{})
   : SolveRef.Best}:
  match usable:
    case False{}:
      {==}
    case True{}:
      +n : Nat = Groups.len_words(S)
      +lb : Nat = SolveFast.lower_bound(n, groups)
      +skip : Bool = SolveFast.skippable(best, lb)
      +body : +List<SolveFast.Item> =
        List.append(&2, SolveFast.Item,
          SolveFast.group_items(n, groups),
          SolveFast.End{} <> rest)
      +us : {Groups.groups_smaller(S, groups) == True{} : Bool} =
        Equal.sym(Bool, True{}, Groups.groups_smaller(S, groups), eus)
      +e0 : {SolveFast.step(1n+p, gs,
               SolveFast.schedule_guess_ib(g,
                 SolveFast.group_items_build(n, groups, SolveFast.End{} <> rest)),
               G, S, inf, Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{})
             == SolveFast.step(1n+p, gs, SolveFast.Begin{g, lb} <> body, G, S,
                  inf, Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{})
             : SolveRef.Best} =
        Equal.cong(SolveFast.ItemsBound, SolveRef.Best,
          ib => SolveFast.step(1n+p, gs, SolveFast.schedule_guess_ib(g, ib),
                  G, S, inf, Nil{}, Nil{}, 0n, best,
                  SolveFast.dummy_zero(), False{}),
          SolveFast.group_items_build(n, groups, SolveFast.End{} <> rest),
          SolveFast.ItemsBound{lb, body},
          FLB.FS.group_items_build_eq(n, groups, SolveFast.End{} <> rest))
      +e1 : {SolveFast.step(1n+p, gs, SolveFast.Begin{g, lb} <> body, G, S, inf,
               Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{})
             == FS.FS.after_begin(1n+p, gs, G, S, inf, g, body, best, skip)
             : SolveRef.Best} =
        FS.FS.begin_succ(p, gs, G, S, inf, Nil{}, g, lb, Nil{}, 0n, best,
          SolveFast.dummy_zero(), False{}, body, skip, {==})
      +e2 : {FS.FS.after_begin(1n+p, gs, G, S, inf, g, body, best, skip)
             == SolveFast.step(1n+p, gs, rest, G, S, inf, Nil{}, Nil{}, 0n,
                  Eval.Eval.block(p, G, S, g, inf, groups, best),
                  SolveFast.dummy_zero(), False{})
             : SolveRef.Best} =
        FE.block_step_eq(p, gs, G, S, inf, g, groups, rest, best, skip, {==},
          us, ele, hz, h1, ag, hbest, ecif)
      Equal.trans(SolveRef.Best,
        SolveFast.step(1n+p, gs,
          SolveFast.schedule_guess_ib(g,
            SolveFast.group_items_build(n, groups, SolveFast.End{} <> rest)),
          G, S, inf, Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{}),
        SolveFast.step(1n+p, gs, SolveFast.Begin{g, lb} <> body, G, S, inf,
          Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{}),
        SolveFast.step(1n+p, gs, rest, G, S, inf, Nil{}, Nil{}, 0n,
          Eval.Eval.block(p, G, S, g, inf, groups, best),
          SolveFast.dummy_zero(), False{}),
        e0,
        Equal.trans(SolveRef.Best,
          SolveFast.step(1n+p, gs, SolveFast.Begin{g, lb} <> body, G, S, inf,
            Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{}),
          FS.FS.after_begin(1n+p, gs, G, S, inf, g, body, best, skip),
          SolveFast.step(1n+p, gs, rest, G, S, inf, Nil{}, Nil{}, 0n,
            Eval.Eval.block(p, G, S, g, inf, groups, best),
            SolveFast.dummy_zero(), False{}),
          e1, e2))

# Step one popped guess `g` according to the pre-grouping bound decision
# `pre_skip`.
def FE.guess_pop_step(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +inf: Nat, +g: +List<Nat>, +t: +List<+List<Nat>>, +best: SolveRef.Best,
    pre_skip: Bool,
    +ep: {pre_skip == SolveFast.skippable(best,
            SolveFast.pre_lb(Groups.len_words(S), g, S)) : Bool},
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +ai: {FO.FO.all_in_ref(S, G) == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    ecif: FE.EClassIf(
            Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
            p, inf, G, Groups.groups_build(g, S, Nil{}))) ->
  {SolveFast.step(1n+p, t,
     SolveFast.guess_items_go(g, S, Groups.len_words(S), pre_skip),
     G, S, inf, Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{})
   == SolveFast.step(1n+p, t, Nil{}, G, S, inf, Nil{}, Nil{}, 0n,
        Eval.Eval.guess(p, G, S, g, inf, best),
        SolveFast.dummy_zero(), False{})
   : SolveRef.Best}:
  match pre_skip:
    case True{}:
      +le : {Nat.is_le(Eval.Eval.cost_of(best),
               SolveFast.pre_lb(Groups.len_words(S), g, S))
             == True{} : Bool} =
        FLB.FS.skippable_to_le(best,
          SolveFast.pre_lb(Groups.len_words(S), g, S),
          Equal.sym(Bool, True{},
            SolveFast.skippable(best,
              SolveFast.pre_lb(Groups.len_words(S), g, S)), ep))
      +geq : {Eval.Eval.guess(p, G, S, g, inf, best) == best : SolveRef.Best} =
        FLB.FS.pre_guess_skip_eq(p, inf, G, S, g, best, ele, hz, hbest, le)
      Equal.cong(SolveRef.Best, SolveRef.Best,
        b => SolveFast.step(1n+p, t, Nil{}, G, S, inf, Nil{}, Nil{}, 0n, b,
               SolveFast.dummy_zero(), False{}),
        best, Eval.Eval.guess(p, G, S, g, inf, best),
        Equal.sym(SolveRef.Best,
          Eval.Eval.guess(p, G, S, g, inf, best), best, geq))
    case False{}:
      +n : Nat = Groups.len_words(S)
      +fgrp : +List<Groups.Group> = SolveFast.groups_build_fast(g, S, Nil{})
      +groups : +List<Groups.Group> = Groups.groups_build(g, S, Nil{})
      +egrp : {fgrp == groups : +List<Groups.Group>} =
        FG.FG.groups_build_eq(g, S, Nil{})
      +usable : Bool = Groups.groups_smaller(S, groups)
      +ag : {FO.FO.all_in_jobs_b(MV.MV.next_groups(groups), G)
             == True{} : Bool} =
        FO.FO.all_in_next_groups(groups, S, G,
          CoverGroups.Cover.all_subseq_nil(g, S), ai)
      +ebody : {SolveFast.step(1n+p, t, SolveFast.guess_body(g, S, n),
                  G, S, inf, Nil{}, Nil{}, 0n, best,
                  SolveFast.dummy_zero(), False{})
                == SolveFast.step(1n+p, t,
                     SolveFast.schedule_guess(g, fgrp, n, Nil{},
                       SolveFast.groups_smaller_fast(n, fgrp)),
                     G, S, inf, Nil{}, Nil{}, 0n, best,
                     SolveFast.dummy_zero(), False{})
                : SolveRef.Best} =
        Equal.cong(+List<SolveFast.Item>, SolveRef.Best,
          cs => SolveFast.step(1n+p, t, cs, G, S, inf, Nil{}, Nil{}, 0n, best,
                  SolveFast.dummy_zero(), False{}),
          SolveFast.guess_body(g, S, n),
          SolveFast.schedule_guess(g, fgrp, n, Nil{},
            SolveFast.groups_smaller_fast(n, fgrp)),
          FG.FG.guess_body_eq(g, S))
      +e0a : {SolveFast.step(1n+p, t,
                SolveFast.schedule_guess(g, fgrp, n, Nil{},
                  SolveFast.groups_smaller_fast(n, fgrp)),
                G, S, inf, Nil{}, Nil{}, 0n, best,
                SolveFast.dummy_zero(), False{})
              == SolveFast.step(1n+p, t,
                   SolveFast.schedule_guess(g, groups, n, Nil{},
                     SolveFast.groups_smaller_fast(n, groups)),
                   G, S, inf, Nil{}, Nil{}, 0n, best,
                   SolveFast.dummy_zero(), False{})
              : SolveRef.Best} =
        Equal.cong(+List<Groups.Group>, SolveRef.Best,
          grp => SolveFast.step(1n+p, t,
                   SolveFast.schedule_guess(g, grp, n, Nil{},
                     SolveFast.groups_smaller_fast(n, grp)),
                   G, S, inf, Nil{}, Nil{}, 0n, best,
                   SolveFast.dummy_zero(), False{}),
          fgrp, groups, egrp)
      +e0b : {SolveFast.step(1n+p, t,
                SolveFast.schedule_guess(g, groups, n, Nil{},
                  SolveFast.groups_smaller_fast(n, groups)),
                G, S, inf, Nil{}, Nil{}, 0n, best,
                SolveFast.dummy_zero(), False{})
              == SolveFast.step(1n+p, t,
                   SolveFast.schedule_guess(g, groups, n, Nil{}, usable),
                   G, S, inf, Nil{}, Nil{}, 0n, best,
                   SolveFast.dummy_zero(), False{})
              : SolveRef.Best} =
        Equal.cong(Bool, SolveRef.Best,
          u => SolveFast.step(1n+p, t,
                 SolveFast.schedule_guess(g, groups, n, Nil{}, u),
                 G, S, inf, Nil{}, Nil{}, 0n, best,
                 SolveFast.dummy_zero(), False{}),
          SolveFast.groups_smaller_fast(n, groups), usable,
          FG.FG.groups_smaller_fast_eq(S, groups))
      +e1 : {SolveFast.step(1n+p, t,
               SolveFast.schedule_guess(g, groups, n, Nil{}, usable),
               G, S, inf, Nil{}, Nil{}, 0n, best,
               SolveFast.dummy_zero(), False{})
             == SolveFast.step(1n+p, t, Nil{}, G, S, inf, Nil{}, Nil{}, 0n,
                  Eval.Eval.guess(p, G, S, g, inf, best),
                  SolveFast.dummy_zero(), False{})
             : SolveRef.Best} =
        FE.schedule_guess_step(p, t, G, S, inf, g, groups, Nil{}, best,
          usable, {==}, ele, hz, h1, ag, hbest, ecif)
      Equal.trans(SolveRef.Best,
        SolveFast.step(1n+p, t, SolveFast.guess_body(g, S, n),
          G, S, inf, Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{}),
        SolveFast.step(1n+p, t,
          SolveFast.schedule_guess(g, groups, n, Nil{}, usable),
          G, S, inf, Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{}),
        SolveFast.step(1n+p, t, Nil{}, G, S, inf, Nil{}, Nil{}, 0n,
          Eval.Eval.guess(p, G, S, g, inf, best),
          SolveFast.dummy_zero(), False{}),
        Equal.trans(SolveRef.Best,
          SolveFast.step(1n+p, t, SolveFast.guess_body(g, S, n),
            G, S, inf, Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{}),
          SolveFast.step(1n+p, t,
            SolveFast.schedule_guess(g, fgrp, n, Nil{},
              SolveFast.groups_smaller_fast(n, fgrp)),
            G, S, inf, Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{}),
          SolveFast.step(1n+p, t,
            SolveFast.schedule_guess(g, groups, n, Nil{}, usable),
            G, S, inf, Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{}),
          ebody,
          Equal.trans(SolveRef.Best,
            SolveFast.step(1n+p, t,
              SolveFast.schedule_guess(g, fgrp, n, Nil{},
                SolveFast.groups_smaller_fast(n, fgrp)),
              G, S, inf, Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{}),
            SolveFast.step(1n+p, t,
              SolveFast.schedule_guess(g, groups, n, Nil{},
                SolveFast.groups_smaller_fast(n, groups)),
              G, S, inf, Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{}),
            SolveFast.step(1n+p, t,
              SolveFast.schedule_guess(g, groups, n, Nil{}, usable),
              G, S, inf, Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{}),
            e0a, e0b)),
        e1)

# Folding the pruned schedule over a guess list at positive fuel equals
# `Eval.guesses`.
def FE.guesses_step(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +inf: Nat, +gs: +List<+List<Nat>>, +best: SolveRef.Best,
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +ai: {FO.FO.all_in_ref(S, G) == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    f: FE.EByGs(p, inf, G, S, gs)) ->
  {SolveFast.step(1n+p, gs, Nil{},
     G, S, inf, Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{})
   == Eval.Eval.guesses(1n+p, G, S, inf, gs, best) : SolveRef.Best}:
  match gs:
    case Nil{}:
      {==}
    case Con{+g, +t}:
      (ecif, ft) = f
      +pre_skip : Bool =
        SolveFast.skippable(best,
          SolveFast.pre_lb(Groups.len_words(S), g, S))
      +next_best : SolveRef.Best = Eval.Eval.guess(p, G, S, g, inf, best)
      +hnext : {Nat.is_le(Eval.Eval.cost_of(next_best), inf) == True{} : Bool} =
        NatProof.Nat.is_le_trans(
          Eval.Eval.cost_of(next_best), Eval.Eval.cost_of(best), inf,
          Fold.OQ.guess_cost_le_acc(p, G, S, g, inf, best), hbest)
      +epop : {SolveFast.step(1n+p, g <> t, Nil{}, G, S, inf,
                 Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{})
               == SolveFast.step(1n+p, t,
                    SolveFast.guess_items_go(g, S, Groups.len_words(S),
                      pre_skip),
                    G, S, inf, Nil{}, Nil{}, 0n, best,
                    SolveFast.dummy_zero(), False{})
               : SolveRef.Best} =
        FS.FS.pop_guess_succ(p, g, t, G, S, inf, Nil{}, Nil{}, 0n, best,
          SolveFast.dummy_zero(), False{}, pre_skip, {==})
      +e1 : {SolveFast.step(1n+p, t,
               SolveFast.guess_items_go(g, S, Groups.len_words(S), pre_skip),
               G, S, inf, Nil{}, Nil{}, 0n, best,
               SolveFast.dummy_zero(), False{})
             == SolveFast.step(1n+p, t, Nil{}, G, S, inf, Nil{}, Nil{}, 0n,
                  next_best, SolveFast.dummy_zero(), False{})
             : SolveRef.Best} =
        FE.guess_pop_step(p, G, S, inf, g, t, best, pre_skip, {==}, ele, hz,
          h1, ai, hbest, ecif)
      +e2 : {SolveFast.step(1n+p, t, Nil{}, G, S, inf, Nil{}, Nil{}, 0n,
               next_best, SolveFast.dummy_zero(), False{})
             == Eval.Eval.guesses(1n+p, G, S, inf, t, next_best)
             : SolveRef.Best} =
        FE.guesses_step(p, G, S, inf, t, next_best, ele, hz, h1, ai, hnext, ft)
      Equal.trans(SolveRef.Best,
        SolveFast.step(1n+p, g <> t, Nil{}, G, S, inf,
          Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{}),
        SolveFast.step(1n+p, t, Nil{}, G, S, inf, Nil{}, Nil{}, 0n,
          next_best, SolveFast.dummy_zero(), False{}),
        Eval.Eval.guesses(1n+p, G, S, inf, g <> t, best),
        Equal.trans(SolveRef.Best,
          SolveFast.step(1n+p, g <> t, Nil{}, G, S, inf,
            Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{}),
          SolveFast.step(1n+p, t,
            SolveFast.guess_items_go(g, S, Groups.len_words(S), pre_skip),
            G, S, inf, Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{}),
          SolveFast.step(1n+p, t, Nil{}, G, S, inf, Nil{}, Nil{}, 0n,
            next_best, SolveFast.dummy_zero(), False{}),
          epop, e1),
        e2)

# One job at positive fuel `1+p`: `FS.run_at` equals `FS.ref_run_at`.
def FE.ejob_succ(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>,
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +ai: {FO.FO.all_in_ref(S, G) == True{} : Bool},
    f: FE.EByGs(p, inf, G, S, G)) ->
  FE.EJob(1n+p, inf, G, S):
  +hinit : {Nat.is_le(Eval.Eval.cost_of(SolveFast.dummy_inf(inf)), inf)
            == True{} : Bool} =
    NatProof.Nat.is_le_refl(inf)
  +e1 : {FS.FS.run_at(1n+p, inf, G, S)
         == Eval.Eval.guesses(1n+p, G, S, inf, G, SolveFast.dummy_inf(inf))
         : SolveRef.Best} =
    FE.guesses_step(p, G, S, inf, G, SolveFast.dummy_inf(inf), ele, hz, h1,
      ai, hinit, f)
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

def FE.zero_guess_step(+G: +List<+List<Nat>>, +inf: Nat, +g: +List<Nat>,
    +rest: +List<+List<Nat>>, +best: SolveRef.Best) ->
  {SolveFast.step(0n, g <> rest, Nil{}, G, Nil{}, inf,
     Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{})
   == SolveFast.step(0n, rest, Nil{}, G, Nil{}, inf,
        Nil{}, Nil{}, 0n,
        SolveRef.finish_guess(inf, g, Nil{}, 0n, Groups.len_words(Nil{}), best),
        SolveFast.dummy_zero(), False{})
   : SolveRef.Best}:
  match rest:
    case Nil{}:
      {==}
    case Con{gh, gt}:
      {==}

# Zero fuel on the empty candidate list: `SolveFast` folds the guesses with
# cost zero, matching `Eval.guesses(0n, ...)`.
def FE.guesses_zero(+G: +List<+List<Nat>>, +inf: Nat,
    +gs: +List<+List<Nat>>, +best: SolveRef.Best) ->
  {SolveFast.step(0n, gs, Nil{}, G, Nil{}, inf,
     Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{})
   == Eval.Eval.guesses(0n, G, Nil{}, inf, gs, best) : SolveRef.Best}:
  match gs:
    case Nil{}:
      {==}
    case Con{+g, +rest}:
      +next_best : SolveRef.Best =
        SolveRef.finish_guess(inf, g, Nil{}, 0n, Groups.len_words(Nil{}), best)
      Equal.trans(SolveRef.Best,
        SolveFast.step(0n, g <> rest, Nil{}, G, Nil{}, inf,
          Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{}),
        SolveFast.step(0n, rest, Nil{}, G, Nil{}, inf,
          Nil{}, Nil{}, 0n, next_best, SolveFast.dummy_zero(), False{}),
        Eval.Eval.guesses(0n, G, Nil{}, inf, g <> rest, best),
        FE.zero_guess_step(G, inf, g, rest, best),
        FE.guesses_zero(G, inf, rest, next_best))

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
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +aj: {FO.FO.all_in_jobs_b(jobs, G) == True{} : Bool},
    f: FE.EFlat(p, inf, G, MV.MV.next_jobs(G, jobs))) ->
  FE.EFlat(1n+p, inf, G, jobs):
  match jobs:
    case Nil{}:
      Unit{}
    case Con{+S, +t}:
      (ble, bt) = bounds
      +ai : {FO.FO.all_in_ref(S, G) == True{} : Bool} =
        Logic.Proof.and_true_l(FO.FO.all_in_ref(S, G),
          FO.FO.all_in_jobs_b(t, G), aj)
      +at : {FO.FO.all_in_jobs_b(t, G) == True{} : Bool} =
        Logic.Proof.and_true_r(FO.FO.all_in_ref(S, G),
          FO.FO.all_in_jobs_b(t, G), aj)
      MV.MV.use_pair(FE.EFlat(1n+p, inf, G, S <> t),
        FE.EFlat(p, inf, G, MV.MV.next_guess(G, S)),
        FE.EFlat(p, inf, G, MV.MV.next_jobs(G, t)),
        FE.eflat_append(p, inf, G, MV.MV.next_guess(G, S),
          MV.MV.next_jobs(G, t), f),
        fS => ft =>
          Tuple{FE.ejob_succ(p, inf, G, S, ble, hz, h1, ai,
                  FE.eby_gs(p, inf, G, S, G, fS)),
                FE.eflat_step(inf, p, G, t, bt, hz, h1, at, ft)})

# The fuel induction over all jobs at a level.
def FE.eflat(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +jobs: +List<+List<+List<Nat>>>,
    bounds: MV.MV.Bounds(fuel, jobs),
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +aj: {FO.FO.all_in_jobs_b(jobs, G) == True{} : Bool}) ->
  FE.EFlat(fuel, inf, G, jobs):
  match fuel:
    case 0n:
      FE.eflat_zero(inf, G, jobs, bounds)
    case 1n+p:
      MV.MV.use_pair(FE.EFlat(1n+p, inf, G, jobs),
        MV.MV.Bounds(1n+p, jobs), MV.MV.Bounds(1n+p, jobs),
        FE.bounds_copy(1n+p, jobs, bounds),
        b1 => b2 =>
          FE.eflat_step(inf, p, G, jobs, b1, hz, h1, aj,
            FE.eflat(p, inf, G, MV.MV.next_jobs(G, jobs),
              MV.MV.next_bounds(p, G, jobs, b2), hz, h1,
              FO.FO.all_in_next_jobs(G, jobs, aj))))

# The top-level equality of the pruned and reference search states.
def FE.main_eq(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>,
    +le: {Nat.is_le(Groups.len_words(S), fuel) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +ai: {FO.FO.all_in_ref(S, G) == True{} : Bool}) ->
  FE.EJob(fuel, inf, G, S):
  +aj : {FO.FO.all_in_jobs_b(S <> Nil{}, G) == True{} : Bool} =
    FO.FO.bool_and_intro(FO.FO.all_in_ref(S, G), True{}, ai, {==})
  MV.MV.use_pair(FE.EJob(fuel, inf, G, S),
    FE.EJob(fuel, inf, G, S), FE.EFlat(fuel, inf, G, Nil{}),
    FE.eflat(fuel, inf, G, S <> Nil{}, Tuple{le, Unit{}}, hz, h1, aj),
    j => u => j)

def FE.solve_fast_valid_eq(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +ai: {FO.FO.all_in_ref(C, G) == True{} : Bool}) ->
  {SolveFast.solve_fast_valid(G, C) == SolveRef.solve(G, C)
   : Maybe<Tree.Tree>}:
  match C:
    case Nil{}:
      Equal.cong(SolveRef.Best, Maybe<Tree.Tree>,
        b => SolveRef.best_to_maybe(1n, b),
        FS.FS.run_at(0n, 1n, G, Nil{}),
        FS.FS.ref_run_at(0n, 1n, G, Nil{}),
        FE.ejob_nil(1n, G))
    case Con{+w, +t}:
      match t:
        case Nil{}:
          +win : {Tree.member_word(w, G) == True{} : Bool} =
            FO.FO.all_in_head(w, Nil{}, G, ai)
          Equal.cong(SolveRef.Best, Maybe<Tree.Tree>,
            b => SolveRef.best_to_maybe(2n, b),
            SolveRef.Best{Tree.Node{w, Nil{}}, 1n},
            FS.FS.ref_run_at(1n, 2n, G, w <> Nil{}),
            FO.FO.ref_run_one_eq(1n, 2n, G, w, {==}, {==}, win))
        case Con{+w2, +t2}:
          +cs : +List<+List<Nat>> = w <> (w2 <> t2)
          +n : Nat = Groups.len_words(cs)
          +inf : Nat = SolveRef.inf_of(n)
          +hz : {Nat.is_lt(0n, inf) == True{} : Bool} =
            Ind.OQ.zero_lt_succ_add(Nat.mul(n, n))
          +h1 : {Nat.is_lt(1n, inf) == True{} : Bool} =
            FO.FO.one_lt_inf_ge2(w, w2, t2)
          +le : {Nat.is_le(Groups.len_words(cs), n) == True{} : Bool} =
            NatProof.Nat.is_le_refl(n)
          Equal.cong(SolveRef.Best, Maybe<Tree.Tree>,
            b => SolveRef.best_to_maybe(inf, b),
            FS.FS.run_at(n, inf, G, cs),
            FS.FS.ref_run_at(n, inf, G, cs),
            FE.main_eq(n, inf, G, cs, le, hz, h1, ai))

def FE.solve_fast_checked_eq(ok: Bool, +G: +List<+List<Nat>>,
    +C: +List<+List<Nat>>,
    +eok: {ok == SolveFast.all_in_fast(C, G) : Bool}) ->
  {SolveFast.solve_fast_checked(ok, G, C) == SolveRef.solve(G, C)
   : Maybe<Tree.Tree>}:
  match ok:
    case False{}:
      +ef : {FO.FO.all_in_ref(C, G) == False{} : Bool} =
        Equal.trans(Bool, FO.FO.all_in_ref(C, G), SolveFast.all_in_fast(C, G),
          False{},
          Equal.sym(Bool, SolveFast.all_in_fast(C, G), FO.FO.all_in_ref(C, G),
            FO.FO.all_in_fast_eq(C, G)),
          Equal.sym(Bool, False{}, SolveFast.all_in_fast(C, G), eok))
      FO.FO.solve_ref_none_of_all_in_false(G, C, ef)
    case True{}:
      +ai : {FO.FO.all_in_ref(C, G) == True{} : Bool} =
        Equal.trans(Bool, FO.FO.all_in_ref(C, G), SolveFast.all_in_fast(C, G),
          True{},
          Equal.sym(Bool, SolveFast.all_in_fast(C, G), FO.FO.all_in_ref(C, G),
            FO.FO.all_in_fast_eq(C, G)),
          Equal.sym(Bool, True{}, SolveFast.all_in_fast(C, G), eok))
      FE.solve_fast_valid_eq(G, C, ai)

# The bound-pruned solver returns the exact reference tree for every input.
def FE.solve_fast_eq(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>) ->
  {SolveFast.solve_fast(G, C) == SolveRef.solve(G, C) : Maybe<Tree.Tree>}:
  FE.solve_fast_checked_eq(SolveFast.all_in_fast(C, G), G, C, {==})
