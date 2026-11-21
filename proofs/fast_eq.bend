# The bound-pruned solver returns the reference tree for every input.
#
# By fuel induction over the jobs of a level, `FS.run_from(fuel, inf, G, S,
# nodup, b0)` equals `Eval.guesses(fuel, G, S, inf, G, b0)` for any starting
# accumulator `b0` with `cost_of(b0) <= inf` whenever `S` satisfies both
# candidate membership (`FO.all_in_ref`) and the duplicate-free invariant
# (`FN.nodup_ok`).
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
import ./fast_cutoff.bend as FC
import ./fast_one.bend as FO
import ./fast_nodup.bend as FN

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

# One job of the equality induction at a given fuel, quantified over any
# starting accumulator `best0` with `cost_of(best0) <= inf`.
def FE.EJob(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +nodup: Bool) -> Type:
  @best0: SolveRef.Best ->
  {Nat.is_le(Eval.Eval.cost_of(best0), inf) == True{} : Bool} ->
  {FS.FS.run_from(fuel, inf, G, S, nodup, best0)
   == Eval.Eval.guesses(fuel, G, S, inf, G, best0)
   : SolveRef.Best}

# The conjunction of job equalities over a list of candidate lists.
def FE.EFlat(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>, +nodup: Bool,
    jobs: +List<+List<+List<Nat>>>) -> Type:
  match jobs:
    case Nil{}:
      Unit
    case Con{S, t}:
      FE.EJob(fuel, inf, G, S, nodup) & FE.EFlat(fuel, inf, G, nodup, t)

# The class equalities of one group list.
def FE.EClass(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>, +nodup: Bool,
    +groups: +List<Groups.Group>) -> Type:
  match groups:
    case Nil{}:
      Unit
    case Con{gp, rest}:
      match gp:
        case Groups.Group{fb, ws}:
          FE.EJob(p, inf, G, ws, nodup) & FE.EClass(p, inf, G, nodup, rest)

# The class equalities of a guess, only when the guess is usable.
def FE.EClassIf(b: Bool, +p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +nodup: Bool, +groups: +List<Groups.Group>) -> Type:
  match b:
    case True{}:
      FE.EClass(p, inf, G, nodup, groups)
    case False{}:
      Unit

# The per-guess class equalities of a guess list.
def FE.EByGs(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +nodup: Bool, gs: +List<+List<Nat>>) -> Type:
  match gs:
    case Nil{}:
      Unit
    case Con{g, t}:
      FE.EClassIf(
        Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
        p, inf, G, nodup, Groups.groups_build(g, S, Nil{}))
      & FE.EByGs(p, inf, G, S, nodup, t)

# Split the flat conjunction at an append.
def FE.eflat_append(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +nodup: Bool, +xs: +List<+List<+List<Nat>>>, +ys: +List<+List<+List<Nat>>>,
    f: FE.EFlat(fuel, inf, G, nodup,
         List.append(&2, +List<+List<Nat>>, xs, ys))) ->
  FE.EFlat(fuel, inf, G, nodup, xs) & FE.EFlat(fuel, inf, G, nodup, ys):
  match xs:
    case Nil{}:
      Tuple{Unit{}, f}
    case Con{S, t}:
      (j, fr) = f
      MV.MV.use_pair(
        FE.EFlat(fuel, inf, G, nodup, S <> t)
        & FE.EFlat(fuel, inf, G, nodup, ys),
        FE.EFlat(fuel, inf, G, nodup, t),
        FE.EFlat(fuel, inf, G, nodup, ys),
        FE.eflat_append(fuel, inf, G, nodup, t, ys, fr),
        ft => fys => Tuple{Tuple{j, ft}, fys})

def FE.eclass_of_flat(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>, +nodup: Bool,
    +groups: +List<Groups.Group>,
    f: FE.EFlat(p, inf, G, nodup, MV.MV.next_groups(groups))) ->
  FE.EClass(p, inf, G, nodup, groups):
  match groups:
    case Nil{}:
      Unit{}
    case Con{gp, t}:
      match gp:
        case Groups.Group{fb, ws}:
          (j, fr) = f
          (j, FE.eclass_of_flat(p, inf, G, nodup, t, fr))

def FE.eclass_if(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>, +nodup: Bool,
    +groups: +List<Groups.Group>, b: Bool,
    f: FE.EFlat(p, inf, G, nodup, MV.MV.classes_b(b, groups))) ->
  FE.EClassIf(b, p, inf, G, nodup, groups):
  match b:
    case True{}:
      FE.eclass_of_flat(p, inf, G, nodup, groups, f)
    case False{}:
      Unit{}

def FE.eby_gs(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +nodup: Bool, +gs: +List<+List<Nat>>,
    f: FE.EFlat(p, inf, G, nodup, MV.MV.next_guess(gs, S))) ->
  FE.EByGs(p, inf, G, S, nodup, gs):
  match gs:
    case Nil{}:
      Unit{}
    case Con{g, t}:
      MV.MV.use_pair(FE.EByGs(p, inf, G, S, nodup, g <> t),
        FE.EFlat(p, inf, G, nodup, MV.MV.classes(g, S)),
        FE.EFlat(p, inf, G, nodup, MV.MV.next_guess(t, S)),
        FE.eflat_append(p, inf, G, nodup, MV.MV.classes(g, S),
          MV.MV.next_guess(t, S), f),
        fg => ft =>
          Tuple{FE.eclass_if(p, inf, G, nodup, Groups.groups_build(g, S, Nil{}),
                  Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
                  fg),
                FE.eby_gs(p, inf, G, S, nodup, t, ft)})

# Translate `skippable(best, x)` to and from `Eval.cost_of(best)`.
def FE.skippable_false_of_lt(+best: SolveRef.Best, +x: Nat,
    +lt: {Nat.is_lt(x, Eval.Eval.cost_of(best)) == True{} : Bool}) ->
  {SolveFast.skippable(best, x) == False{} : Bool}:
  Equal.trans(Bool,
    Nat.is_le(SolveFast.best_cost(best), x),
    Nat.is_le(Eval.Eval.cost_of(best), x),
    False{},
    Equal.cong(Nat, Bool, c => Nat.is_le(c, x),
      SolveFast.best_cost(best), Eval.Eval.cost_of(best),
      FLB.FS.best_cost_eq(best)),
    FC.FC.le_false_of_lt(Eval.Eval.cost_of(best), x, lt))

def FE.skippable_true_of_le(+best: SolveRef.Best, +x: Nat,
    +le: {Nat.is_le(Eval.Eval.cost_of(best), x) == True{} : Bool}) ->
  {SolveFast.skippable(best, x) == True{} : Bool}:
  Equal.trans(Bool,
    Nat.is_le(SolveFast.best_cost(best), x),
    Nat.is_le(Eval.Eval.cost_of(best), x),
    True{},
    Equal.cong(Nat, Bool, c => Nat.is_le(c, x),
      SolveFast.best_cost(best), Eval.Eval.cost_of(best),
      FLB.FS.best_cost_eq(best)),
    le)

def FE.lt_of_skippable_false(+best: SolveRef.Best, +x: Nat,
    +ef: {SolveFast.skippable(best, x) == False{} : Bool}) ->
  {Nat.is_lt(x, Eval.Eval.cost_of(best)) == True{} : Bool}:
  +ef2 : {Nat.is_le(Eval.Eval.cost_of(best), x) == False{} : Bool} =
    Equal.trans(Bool,
      Nat.is_le(Eval.Eval.cost_of(best), x),
      Nat.is_le(SolveFast.best_cost(best), x),
      False{},
      Equal.cong(Nat, Bool, c => Nat.is_le(c, x),
        Eval.Eval.cost_of(best), SolveFast.best_cost(best),
        Equal.sym(Nat, SolveFast.best_cost(best), Eval.Eval.cost_of(best),
          FLB.FS.best_cost_eq(best))),
      ef)
  FC.FC.lt_of_le_false(Eval.Eval.cost_of(best), x, ef2)

# Step a live `ClassItem` + `Add` using its recursive cutoff, branching on
# whether the reference child cost beats the cutoff.
def FE.live_group_cutoff_go(+p: Nat, +gs: +List<+List<Nat>>,
    +G: +List<+List<Nat>>, +S: +List<+List<Nat>>, +nodup: Bool, +inf: Nat,
    +g: +List<Nat>, +fb: +List<Feedback.Color>, +ws: +List<+List<Nat>>,
    +restg: +List<Groups.Group>, +kids: +List<Tree.Child>, +sum: Nat,
    +best: SolveRef.Best,
    +ble: {Nat.is_le(Groups.len_words(ws), p) == True{} : Bool},
    bt: MV.MV.Bounds(p, MV.MV.next_groups(restg)),
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    +hd: {SolveFast.is_floor_hit(nodup, Groups.len_words(S), best)
          == False{} : Bool},
    +alive: {Nat.is_lt(
               Nat.add(sum,
                 SolveFast.lower_bound(Groups.len_words(S),
                   Groups.Group{fb, ws} <> restg)),
               Eval.Eval.cost_of(best)) == True{} : Bool},
    eh: FE.EJob(p, inf, G, ws, nodup),
    lt_cut: Bool,
    +elt: {lt_cut == Nat.is_lt(
             Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, ws)),
             FS.FS.child_cutoff(best, sum,
               SolveFast.lower_bound(Groups.len_words(S), restg))) : Bool},
    rec_live: {Nat.is_lt(
                 Nat.add(
                   SolveRef.sat_add(inf, sum,
                     Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, ws))),
                   SolveFast.lower_bound(Groups.len_words(S), restg)),
                 Eval.Eval.cost_of(best)) == True{} : Bool} ->
              {SolveFast.step(1n+p, gs,
                 List.append(&2, SolveFast.Item,
                   SolveFast.group_items(Groups.len_words(S), restg),
                   SolveFast.End{} <> Nil{}),
                 G, S, Groups.len_words(S), nodup, inf, g,
                 Tree.Child{fb, Eval.Eval.tree_of(
                   FS.FS.ref_run_at(p, inf, G, ws))} <> kids,
                 SolveRef.sat_add(inf, sum,
                   Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, ws))),
                 best, SolveFast.dummy_zero(), False{}, False{})
               == SolveFast.step(1n+p, gs, Nil{}, G, S, Groups.len_words(S),
                    nodup, inf, Nil{}, Nil{}, 0n,
                    Eval.Eval.finish_ks(inf, g, S,
                      Eval.Eval.items(p, G, S, g, restg,
                        Tree.Child{fb, Eval.Eval.tree_of(
                          FS.FS.ref_run_at(p, inf, G, ws))} <> kids,
                        SolveRef.sat_add(inf, sum,
                          Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, ws))),
                        inf),
                      best),
                    SolveFast.dummy_zero(), False{},
                    SolveFast.is_floor_hit(nodup, Groups.len_words(S),
                      Eval.Eval.finish_ks(inf, g, S,
                        Eval.Eval.items(p, G, S, g, restg,
                          Tree.Child{fb, Eval.Eval.tree_of(
                            FS.FS.ref_run_at(p, inf, G, ws))} <> kids,
                          SolveRef.sat_add(inf, sum,
                            Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, ws))),
                          inf),
                        best)))
               : SolveRef.Best}) ->
  {SolveFast.step(1n+p, gs,
     SolveFast.ClassItem{fb, ws, Groups.len_words(ws),
       SolveFast.lower_bound(Groups.len_words(S), restg)}
       <> (SolveFast.Add{fb,
             SolveFast.lower_bound(Groups.len_words(S), restg)}
           <> List.append(&2, SolveFast.Item,
                SolveFast.group_items(Groups.len_words(S), restg),
                SolveFast.End{} <> Nil{})),
     G, S, Groups.len_words(S), nodup, inf, g, kids, sum, best,
     SolveFast.dummy_zero(), False{}, False{})
   == SolveFast.step(1n+p, gs, Nil{}, G, S, Groups.len_words(S), nodup, inf,
        Nil{}, Nil{}, 0n,
        Eval.Eval.finish_ks(inf, g, S,
          Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg,
            kids, sum, inf),
          best),
        SolveFast.dummy_zero(), False{},
        SolveFast.is_floor_hit(nodup, Groups.len_words(S),
          Eval.Eval.finish_ks(inf, g, S,
            Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg,
              kids, sum, inf),
            best)))
   : SolveRef.Best}:
  match lt_cut:
    case True{}:
      +n : Nat = Groups.len_words(S)
      +tlb : Nat = SolveFast.lower_bound(n, restg)
      +B : Nat = Eval.Eval.cost_of(best)
      +cut : Nat = FS.FS.child_cutoff(best, sum, tlb)
      +cut_eq : {cut == Nat.sub(B, Nat.add(sum, tlb)) : Nat} =
        Equal.cong(Nat, Nat, x => Nat.sub(x, Nat.add(sum, tlb)),
          SolveFast.best_cost(best), B, FLB.FS.best_cost_eq(best))
      +st_le : {Nat.is_le(Nat.add(sum, tlb), B) == True{} : Bool} =
        FC.FC.sum_tail_le(sum, SolveFast.class_lb(ws), tlb, B, alive)
      +cut_le_B : {Nat.is_le(cut, B) == True{} : Bool} =
        NatProof.Nat.is_le_eq_l(B, Nat.sub(B, Nat.add(sum, tlb)), cut,
          Equal.sym(Nat, cut, Nat.sub(B, Nat.add(sum, tlb)), cut_eq),
          FC.FC.sub_le_self(B, Nat.add(sum, tlb)))
      +cut_le_inf : {Nat.is_le(cut, inf) == True{} : Bool} =
        NatProof.Nat.is_le_trans(cut, B, inf, cut_le_B, hbest)
      +inner : +List<SolveFast.Item> =
        List.append(&2, SolveFast.Item, SolveFast.group_items(n, restg),
          SolveFast.End{} <> Nil{})
      +fast_c : SolveRef.Best =
        FS.FS.run_from(p, inf, G, ws, nodup, SolveFast.dummy_inf(cut))
      +ref_c : SolveRef.Best = FS.FS.ref_run_at(p, inf, G, ws)
      +efast : {fast_c == FC.FC.better_best(ref_c, SolveFast.dummy_inf(cut))
                : SolveRef.Best} =
        Equal.trans(SolveRef.Best,
          fast_c,
          Eval.Eval.guesses(p, G, ws, inf, G, SolveFast.dummy_inf(cut)),
          FC.FC.better_best(ref_c, SolveFast.dummy_inf(cut)),
          eh(SolveFast.dummy_inf(cut), cut_le_inf),
          FC.FC.eval_guesses_from(p, inf, G, ws, SolveFast.dummy_inf(cut),
            ble, cut_le_inf))
      +hlt_cut : {Nat.is_lt(Eval.Eval.cost_of(ref_c), cut) == True{} : Bool} =
        Equal.sym(Bool, True{}, Nat.is_lt(Eval.Eval.cost_of(ref_c), cut), elt)
      +ec : {fast_c == ref_c : SolveRef.Best} =
        Equal.trans(SolveRef.Best,
          fast_c,
          FC.FC.better_best(ref_c, SolveFast.dummy_inf(cut)),
          ref_c,
          efast,
          FC.FC.better_best_lt(ref_c, SolveFast.dummy_inf(cut), hlt_cut))
      +hlt_sub : {Nat.is_lt(Eval.Eval.cost_of(ref_c),
                    Nat.sub(B, Nat.add(sum, tlb))) == True{} : Bool} =
        Equal.trans(Bool,
          Nat.is_lt(Eval.Eval.cost_of(ref_c), Nat.sub(B, Nat.add(sum, tlb))),
          Nat.is_lt(Eval.Eval.cost_of(ref_c), cut),
          True{},
          Equal.cong(Nat, Bool, x => Nat.is_lt(Eval.Eval.cost_of(ref_c), x),
            Nat.sub(B, Nat.add(sum, tlb)), cut,
            Equal.sym(Nat, cut, Nat.sub(B, Nat.add(sum, tlb)), cut_eq)),
          hlt_cut)
      +kf : +List<Tree.Child> =
        Tree.Child{fb, Eval.Eval.tree_of(fast_c)} <> kids
      +sf : Nat = SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(fast_c))
      +kr : +List<Tree.Child> =
        Tree.Child{fb, Eval.Eval.tree_of(ref_c)} <> kids
      +sr : Nat = SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(ref_c))
      +alive2 : {Nat.is_lt(Nat.add(sr, tlb), B) == True{} : Bool} =
        FC.FC.alive_cut_lt(inf, sum, Eval.Eval.cost_of(ref_c), tlb, B, hbest,
          st_le, hlt_sub)
      +sk_f : {SolveFast.skippable(best, Nat.add(sr, tlb)) == False{} : Bool} =
        FE.skippable_false_of_lt(best, Nat.add(sr, tlb), alive2)
      +e1 : {SolveFast.step(1n+p, gs,
               SolveFast.ClassItem{fb, ws, Groups.len_words(ws), tlb}
                 <> (SolveFast.Add{fb, tlb} <> inner),
               G, S, n, nodup, inf, g, kids, sum, best,
               SolveFast.dummy_zero(), False{}, False{})
             == SolveFast.step(1n+p, gs, inner, G, S, n, nodup, inf, g, kf, sf,
                  best, SolveFast.dummy_zero(),
                  SolveFast.skippable(best, Nat.add(sf, tlb)), False{})
             : SolveRef.Best} =
        FS.FS.class_add_live(p, gs, G, S, n, nodup, inf, g, fb, ws, tlb, inner,
          kids, sum, best)
      +e2 : {SolveFast.step(1n+p, gs, inner, G, S, n, nodup, inf, g, kf, sf,
               best, SolveFast.dummy_zero(),
               SolveFast.skippable(best, Nat.add(sf, tlb)), False{})
             == SolveFast.step(1n+p, gs, inner, G, S, n, nodup, inf, g, kr, sr,
                  best, SolveFast.dummy_zero(),
                  SolveFast.skippable(best, Nat.add(sr, tlb)), False{})
             : SolveRef.Best} =
        Equal.cong(SolveRef.Best, SolveRef.Best,
          c => SolveFast.step(1n+p, gs, inner, G, S, n, nodup, inf, g,
                 Tree.Child{fb, Eval.Eval.tree_of(c)} <> kids,
                 SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(c)),
                 best, SolveFast.dummy_zero(),
                 SolveFast.skippable(best,
                   Nat.add(SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(c)),
                     tlb)),
                 False{}),
          fast_c, ref_c, ec)
      +e3 : {SolveFast.step(1n+p, gs, inner, G, S, n, nodup, inf, g, kr, sr,
               best, SolveFast.dummy_zero(),
               SolveFast.skippable(best, Nat.add(sr, tlb)), False{})
             == SolveFast.step(1n+p, gs, inner, G, S, n, nodup, inf, g, kr, sr,
                  best, SolveFast.dummy_zero(), False{}, False{})
             : SolveRef.Best} =
        Equal.cong(Bool, SolveRef.Best,
          sk => SolveFast.step(1n+p, gs, inner, G, S, n, nodup, inf, g, kr, sr,
                  best, SolveFast.dummy_zero(), sk, False{}),
          SolveFast.skippable(best, Nat.add(sr, tlb)), False{}, sk_f)
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
      +e5 : {SolveFast.step(1n+p, gs, Nil{}, G, S, n, nodup, inf, Nil{}, Nil{},
               0n,
               Eval.Eval.finish_ks(inf, g, S,
                 Eval.Eval.items(p, G, S, g, restg, kr, sr, inf), best),
               SolveFast.dummy_zero(), False{},
               SolveFast.is_floor_hit(nodup, n,
                 Eval.Eval.finish_ks(inf, g, S,
                   Eval.Eval.items(p, G, S, g, restg, kr, sr, inf), best)))
             == SolveFast.step(1n+p, gs, Nil{}, G, S, n, nodup, inf, Nil{},
                  Nil{}, 0n,
                  Eval.Eval.finish_ks(inf, g, S,
                    Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg,
                      kids, sum, inf),
                    best),
                  SolveFast.dummy_zero(), False{},
                  SolveFast.is_floor_hit(nodup, n,
                    Eval.Eval.finish_ks(inf, g, S,
                      Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg,
                        kids, sum, inf),
                      best)))
             : SolveRef.Best} =
        Equal.cong(Eval.KS, SolveRef.Best,
          ks => SolveFast.step(1n+p, gs, Nil{}, G, S, n, nodup, inf, Nil{},
                  Nil{}, 0n, Eval.Eval.finish_ks(inf, g, S, ks, best),
                  SolveFast.dummy_zero(), False{},
                  SolveFast.is_floor_hit(nodup, n,
                    Eval.Eval.finish_ks(inf, g, S, ks, best))),
          Eval.Eval.items(p, G, S, g, restg, kr, sr, inf),
          Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg,
            kids, sum, inf),
          wk)
      +e123 : {SolveFast.step(1n+p, gs,
                 SolveFast.ClassItem{fb, ws, Groups.len_words(ws), tlb}
                   <> (SolveFast.Add{fb, tlb} <> inner),
                 G, S, n, nodup, inf, g, kids, sum, best,
                 SolveFast.dummy_zero(), False{}, False{})
               == SolveFast.step(1n+p, gs, inner, G, S, n, nodup, inf, g,
                    kr, sr, best, SolveFast.dummy_zero(), False{}, False{})
               : SolveRef.Best} =
        Equal.trans(SolveRef.Best,
          SolveFast.step(1n+p, gs,
            SolveFast.ClassItem{fb, ws, Groups.len_words(ws), tlb}
              <> (SolveFast.Add{fb, tlb} <> inner),
            G, S, n, nodup, inf, g, kids, sum, best,
            SolveFast.dummy_zero(), False{}, False{}),
          SolveFast.step(1n+p, gs, inner, G, S, n, nodup, inf, g, kr, sr, best,
            SolveFast.dummy_zero(),
            SolveFast.skippable(best, Nat.add(sr, tlb)), False{}),
          SolveFast.step(1n+p, gs, inner, G, S, n, nodup, inf, g, kr, sr, best,
            SolveFast.dummy_zero(), False{}, False{}),
          Equal.trans(SolveRef.Best,
            SolveFast.step(1n+p, gs,
              SolveFast.ClassItem{fb, ws, Groups.len_words(ws), tlb}
                <> (SolveFast.Add{fb, tlb} <> inner),
              G, S, n, nodup, inf, g, kids, sum, best,
              SolveFast.dummy_zero(), False{}, False{}),
            SolveFast.step(1n+p, gs, inner, G, S, n, nodup, inf, g, kf, sf,
              best, SolveFast.dummy_zero(),
              SolveFast.skippable(best, Nat.add(sf, tlb)), False{}),
            SolveFast.step(1n+p, gs, inner, G, S, n, nodup, inf, g, kr, sr,
              best, SolveFast.dummy_zero(),
              SolveFast.skippable(best, Nat.add(sr, tlb)), False{}),
            e1, e2),
          e3)
      Equal.trans(SolveRef.Best,
        SolveFast.step(1n+p, gs,
          SolveFast.ClassItem{fb, ws, Groups.len_words(ws), tlb}
            <> (SolveFast.Add{fb, tlb} <> inner),
          G, S, n, nodup, inf, g, kids, sum, best,
          SolveFast.dummy_zero(), False{}, False{}),
        SolveFast.step(1n+p, gs, inner, G, S, n, nodup, inf, g, kr, sr, best,
          SolveFast.dummy_zero(), False{}, False{}),
        SolveFast.step(1n+p, gs, Nil{}, G, S, n, nodup, inf, Nil{}, Nil{}, 0n,
          Eval.Eval.finish_ks(inf, g, S,
            Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg,
              kids, sum, inf),
            best),
          SolveFast.dummy_zero(), False{},
          SolveFast.is_floor_hit(nodup, n,
            Eval.Eval.finish_ks(inf, g, S,
              Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg,
                kids, sum, inf),
              best))),
        e123,
        Equal.trans(SolveRef.Best,
          SolveFast.step(1n+p, gs, inner, G, S, n, nodup, inf, g, kr, sr, best,
            SolveFast.dummy_zero(), False{}, False{}),
          SolveFast.step(1n+p, gs, Nil{}, G, S, n, nodup, inf, Nil{}, Nil{}, 0n,
            Eval.Eval.finish_ks(inf, g, S,
              Eval.Eval.items(p, G, S, g, restg, kr, sr, inf), best),
            SolveFast.dummy_zero(), False{},
            SolveFast.is_floor_hit(nodup, n,
              Eval.Eval.finish_ks(inf, g, S,
                Eval.Eval.items(p, G, S, g, restg, kr, sr, inf), best))),
          SolveFast.step(1n+p, gs, Nil{}, G, S, n, nodup, inf, Nil{}, Nil{}, 0n,
            Eval.Eval.finish_ks(inf, g, S,
              Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg,
                kids, sum, inf),
              best),
            SolveFast.dummy_zero(), False{},
            SolveFast.is_floor_hit(nodup, n,
              Eval.Eval.finish_ks(inf, g, S,
                Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg,
                  kids, sum, inf),
                best))),
          rec_live(alive2), e5))
    case False{}:
      +n : Nat = Groups.len_words(S)
      +tlb : Nat = SolveFast.lower_bound(n, restg)
      +B : Nat = Eval.Eval.cost_of(best)
      +cut : Nat = FS.FS.child_cutoff(best, sum, tlb)
      +cut_eq : {cut == Nat.sub(B, Nat.add(sum, tlb)) : Nat} =
        Equal.cong(Nat, Nat, x => Nat.sub(x, Nat.add(sum, tlb)),
          SolveFast.best_cost(best), B, FLB.FS.best_cost_eq(best))
      +st_le : {Nat.is_le(Nat.add(sum, tlb), B) == True{} : Bool} =
        FC.FC.sum_tail_le(sum, SolveFast.class_lb(ws), tlb, B, alive)
      +cut_le_B : {Nat.is_le(cut, B) == True{} : Bool} =
        NatProof.Nat.is_le_eq_l(B, Nat.sub(B, Nat.add(sum, tlb)), cut,
          Equal.sym(Nat, cut, Nat.sub(B, Nat.add(sum, tlb)), cut_eq),
          FC.FC.sub_le_self(B, Nat.add(sum, tlb)))
      +cut_le_inf : {Nat.is_le(cut, inf) == True{} : Bool} =
        NatProof.Nat.is_le_trans(cut, B, inf, cut_le_B, hbest)
      +inner : +List<SolveFast.Item> =
        List.append(&2, SolveFast.Item, SolveFast.group_items(n, restg),
          SolveFast.End{} <> Nil{})
      +fast_c : SolveRef.Best =
        FS.FS.run_from(p, inf, G, ws, nodup, SolveFast.dummy_inf(cut))
      +ref_c : SolveRef.Best = FS.FS.ref_run_at(p, inf, G, ws)
      +dcut : SolveRef.Best = SolveFast.dummy_inf(cut)
      +efast : {fast_c == FC.FC.better_best(ref_c, dcut) : SolveRef.Best} =
        Equal.trans(SolveRef.Best,
          fast_c,
          Eval.Eval.guesses(p, G, ws, inf, G, dcut),
          FC.FC.better_best(ref_c, dcut),
          eh(dcut, cut_le_inf),
          FC.FC.eval_guesses_from(p, inf, G, ws, dcut, ble, cut_le_inf))
      +hge_cut : {Nat.is_lt(Eval.Eval.cost_of(ref_c), cut) == False{} : Bool} =
        Equal.sym(Bool, False{}, Nat.is_lt(Eval.Eval.cost_of(ref_c), cut), elt)
      +ec : {fast_c == dcut : SolveRef.Best} =
        Equal.trans(SolveRef.Best,
          fast_c, FC.FC.better_best(ref_c, dcut), dcut,
          efast, FC.FC.better_best_ge(ref_c, dcut, hge_cut))
      +kf : +List<Tree.Child> =
        Tree.Child{fb, Eval.Eval.tree_of(fast_c)} <> kids
      +sf : Nat = SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(fast_c))
      +kd : +List<Tree.Child> =
        Tree.Child{fb, Eval.Eval.tree_of(dcut)} <> kids
      +sd : Nat = SolveRef.sat_add(inf, sum, cut)
      +le_cut_self : {Nat.is_le(Nat.sub(B, Nat.add(sum, tlb)), cut)
                      == True{} : Bool} =
        NatProof.Nat.is_le_eq_l(cut, cut, Nat.sub(B, Nat.add(sum, tlb)),
          cut_eq, NatProof.Nat.is_le_refl(cut))
      +le_d : {Nat.is_le(B, Nat.add(sd, tlb)) == True{} : Bool} =
        FC.FC.dead_cut_ge(inf, sum, cut, tlb, B, hbest, st_le, le_cut_self)
      +sk_t : {SolveFast.skippable(best, Nat.add(sd, tlb)) == True{} : Bool} =
        FE.skippable_true_of_le(best, Nat.add(sd, tlb), le_d)
      +e1 : {SolveFast.step(1n+p, gs,
               SolveFast.ClassItem{fb, ws, Groups.len_words(ws), tlb}
                 <> (SolveFast.Add{fb, tlb} <> inner),
               G, S, n, nodup, inf, g, kids, sum, best,
               SolveFast.dummy_zero(), False{}, False{})
             == SolveFast.step(1n+p, gs, inner, G, S, n, nodup, inf, g, kf, sf,
                  best, SolveFast.dummy_zero(),
                  SolveFast.skippable(best, Nat.add(sf, tlb)), False{})
             : SolveRef.Best} =
        FS.FS.class_add_live(p, gs, G, S, n, nodup, inf, g, fb, ws, tlb, inner,
          kids, sum, best)
      +e2 : {SolveFast.step(1n+p, gs, inner, G, S, n, nodup, inf, g, kf, sf,
               best, SolveFast.dummy_zero(),
               SolveFast.skippable(best, Nat.add(sf, tlb)), False{})
             == SolveFast.step(1n+p, gs, inner, G, S, n, nodup, inf, g, kd, sd,
                  best, SolveFast.dummy_zero(),
                  SolveFast.skippable(best, Nat.add(sd, tlb)), False{})
             : SolveRef.Best} =
        Equal.cong(SolveRef.Best, SolveRef.Best,
          c => SolveFast.step(1n+p, gs, inner, G, S, n, nodup, inf, g,
                 Tree.Child{fb, Eval.Eval.tree_of(c)} <> kids,
                 SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(c)),
                 best, SolveFast.dummy_zero(),
                 SolveFast.skippable(best,
                   Nat.add(SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(c)),
                     tlb)),
                 False{}),
          fast_c, dcut, ec)
      +e3 : {SolveFast.step(1n+p, gs, inner, G, S, n, nodup, inf, g, kd, sd,
               best, SolveFast.dummy_zero(),
               SolveFast.skippable(best, Nat.add(sd, tlb)), False{})
             == SolveFast.step(1n+p, gs, inner, G, S, n, nodup, inf, g, kd, sd,
                  best, SolveFast.dummy_zero(), True{}, False{})
             : SolveRef.Best} =
        Equal.cong(Bool, SolveRef.Best,
          sk => SolveFast.step(1n+p, gs, inner, G, S, n, nodup, inf, g, kd, sd,
                  best, SolveFast.dummy_zero(), sk, False{}),
          SolveFast.skippable(best, Nat.add(sd, tlb)), True{}, sk_t)
      +e4 : {SolveFast.step(1n+p, gs, inner, G, S, n, nodup, inf, g, kd, sd,
               best, SolveFast.dummy_zero(), True{}, False{})
             == SolveFast.step(1n+p, gs, Nil{}, G, S, n, nodup, inf, Nil{},
                  Nil{}, 0n, best, SolveFast.dummy_zero(), False{}, False{})
             : SolveRef.Best} =
        FS.FS.block_dead(p, gs, G, S, n, nodup, inf, g, restg, kd, sd, best,
          Nil{})
      +e4b : {SolveFast.step(1n+p, gs, Nil{}, G, S, n, nodup, inf, Nil{},
                Nil{}, 0n, best, SolveFast.dummy_zero(), False{}, False{})
              == SolveFast.step(1n+p, gs, Nil{}, G, S, n, nodup, inf, Nil{},
                   Nil{}, 0n, best, SolveFast.dummy_zero(), False{},
                   SolveFast.is_floor_hit(nodup, n, best))
              : SolveRef.Best} =
        Equal.cong(Bool, SolveRef.Best,
          dn => SolveFast.step(1n+p, gs, Nil{}, G, S, n, nodup, inf, Nil{},
                  Nil{}, 0n, best, SolveFast.dummy_zero(), False{}, dn),
          False{}, SolveFast.is_floor_hit(nodup, n, best),
          Equal.sym(Bool, SolveFast.is_floor_hit(nodup, n, best), False{}, hd))
      +lhs_eq : {SolveFast.step(1n+p, gs,
                   SolveFast.ClassItem{fb, ws, Groups.len_words(ws), tlb}
                     <> (SolveFast.Add{fb, tlb} <> inner),
                   G, S, n, nodup, inf, g, kids, sum, best,
                   SolveFast.dummy_zero(), False{}, False{})
                 == SolveFast.step(1n+p, gs, Nil{}, G, S, n, nodup, inf, Nil{},
                      Nil{}, 0n, best, SolveFast.dummy_zero(), False{},
                      SolveFast.is_floor_hit(nodup, n, best))
                 : SolveRef.Best} =
        Equal.trans(SolveRef.Best,
          SolveFast.step(1n+p, gs,
            SolveFast.ClassItem{fb, ws, Groups.len_words(ws), tlb}
              <> (SolveFast.Add{fb, tlb} <> inner),
            G, S, n, nodup, inf, g, kids, sum, best,
            SolveFast.dummy_zero(), False{}, False{}),
          SolveFast.step(1n+p, gs, Nil{}, G, S, n, nodup, inf, Nil{}, Nil{},
            0n, best, SolveFast.dummy_zero(), False{}, False{}),
          SolveFast.step(1n+p, gs, Nil{}, G, S, n, nodup, inf, Nil{}, Nil{},
            0n, best, SolveFast.dummy_zero(), False{},
            SolveFast.is_floor_hit(nodup, n, best)),
          Equal.trans(SolveRef.Best,
            SolveFast.step(1n+p, gs,
              SolveFast.ClassItem{fb, ws, Groups.len_words(ws), tlb}
                <> (SolveFast.Add{fb, tlb} <> inner),
              G, S, n, nodup, inf, g, kids, sum, best,
              SolveFast.dummy_zero(), False{}, False{}),
            SolveFast.step(1n+p, gs, inner, G, S, n, nodup, inf, g, kd, sd,
              best, SolveFast.dummy_zero(), True{}, False{}),
            SolveFast.step(1n+p, gs, Nil{}, G, S, n, nodup, inf, Nil{}, Nil{},
              0n, best, SolveFast.dummy_zero(), False{}, False{}),
            Equal.trans(SolveRef.Best,
              SolveFast.step(1n+p, gs,
                SolveFast.ClassItem{fb, ws, Groups.len_words(ws), tlb}
                  <> (SolveFast.Add{fb, tlb} <> inner),
                G, S, n, nodup, inf, g, kids, sum, best,
                SolveFast.dummy_zero(), False{}, False{}),
              SolveFast.step(1n+p, gs, inner, G, S, n, nodup, inf, g, kd, sd,
                best, SolveFast.dummy_zero(),
                SolveFast.skippable(best, Nat.add(sd, tlb)), False{}),
              SolveFast.step(1n+p, gs, inner, G, S, n, nodup, inf, g, kd, sd,
                best, SolveFast.dummy_zero(), True{}, False{}),
              Equal.trans(SolveRef.Best,
                SolveFast.step(1n+p, gs,
                  SolveFast.ClassItem{fb, ws, Groups.len_words(ws), tlb}
                    <> (SolveFast.Add{fb, tlb} <> inner),
                  G, S, n, nodup, inf, g, kids, sum, best,
                  SolveFast.dummy_zero(), False{}, False{}),
                SolveFast.step(1n+p, gs, inner, G, S, n, nodup, inf, g, kf, sf,
                  best, SolveFast.dummy_zero(),
                  SolveFast.skippable(best, Nat.add(sf, tlb)), False{}),
                SolveFast.step(1n+p, gs, inner, G, S, n, nodup, inf, g, kd, sd,
                  best, SolveFast.dummy_zero(),
                  SolveFast.skippable(best, Nat.add(sd, tlb)), False{}),
                e1, e2),
              e3),
            e4),
          e4b)
      +kr : +List<Tree.Child> =
        Tree.Child{fb, Eval.Eval.tree_of(ref_c)} <> kids
      +sr : Nat = SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(ref_c))
      +cut_le_ref : {Nat.is_le(cut, Eval.Eval.cost_of(ref_c)) == True{} : Bool} =
        FC.FC.le_of_lt_false(Eval.Eval.cost_of(ref_c), cut, hge_cut)
      +sub_le_ref : {Nat.is_le(Nat.sub(B, Nat.add(sum, tlb)),
                       Eval.Eval.cost_of(ref_c)) == True{} : Bool} =
        NatProof.Nat.is_le_eq_l(Eval.Eval.cost_of(ref_c), cut,
          Nat.sub(B, Nat.add(sum, tlb)), cut_eq, cut_le_ref)
      +le_r : {Nat.is_le(B, Nat.add(sr, tlb)) == True{} : Bool} =
        FC.FC.dead_cut_ge(inf, sum, Eval.Eval.cost_of(ref_c), tlb, B, hbest,
          st_le, sub_le_ref)
      +feq_rest : {Eval.Eval.finish_ks(inf, g, S,
                     Eval.Eval.items(p, G, S, g, restg, kr, sr, inf), best)
                   == best : SolveRef.Best} =
        FLB.FS.finish_skip_eq(p, inf, G, S, g, restg, kr, sr, best, bt, hz,
          hbest, le_r)
      +wk : {Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg,
               kids, sum, inf)
             == Eval.Eval.items(p, G, S, g, restg, kr, sr, inf) : Eval.KS} =
        Eval.Eval.with_kid_eq(fb, kids, sum, inf, ref_c,
          ka => sa => Eval.Eval.items(p, G, S, g, restg, ka, sa, inf))
      +feq : {Eval.Eval.finish_ks(inf, g, S,
                Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg,
                  kids, sum, inf), best)
              == best : SolveRef.Best} =
        Equal.trans(SolveRef.Best,
          Eval.Eval.finish_ks(inf, g, S,
            Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg,
              kids, sum, inf), best),
          Eval.Eval.finish_ks(inf, g, S,
            Eval.Eval.items(p, G, S, g, restg, kr, sr, inf), best),
          best,
          Equal.cong(Eval.KS, SolveRef.Best,
            ks => Eval.Eval.finish_ks(inf, g, S, ks, best),
            Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg,
              kids, sum, inf),
            Eval.Eval.items(p, G, S, g, restg, kr, sr, inf),
            wk),
          feq_rest)
      +rhs_eq : {SolveFast.step(1n+p, gs, Nil{}, G, S, n, nodup, inf, Nil{},
                   Nil{}, 0n, best, SolveFast.dummy_zero(), False{},
                   SolveFast.is_floor_hit(nodup, n, best))
                 == SolveFast.step(1n+p, gs, Nil{}, G, S, n, nodup, inf, Nil{},
                      Nil{}, 0n,
                      Eval.Eval.finish_ks(inf, g, S,
                        Eval.Eval.items(p, G, S, g,
                          Groups.Group{fb, ws} <> restg, kids, sum, inf),
                        best),
                      SolveFast.dummy_zero(), False{},
                      SolveFast.is_floor_hit(nodup, n,
                        Eval.Eval.finish_ks(inf, g, S,
                          Eval.Eval.items(p, G, S, g,
                            Groups.Group{fb, ws} <> restg, kids, sum, inf),
                          best)))
                 : SolveRef.Best} =
        Equal.cong(SolveRef.Best, SolveRef.Best,
          b => SolveFast.step(1n+p, gs, Nil{}, G, S, n, nodup, inf, Nil{},
                 Nil{}, 0n, b, SolveFast.dummy_zero(), False{},
                 SolveFast.is_floor_hit(nodup, n, b)),
          best,
          Eval.Eval.finish_ks(inf, g, S,
            Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg,
              kids, sum, inf), best),
          Equal.sym(SolveRef.Best,
            Eval.Eval.finish_ks(inf, g, S,
              Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg,
                kids, sum, inf), best),
            best, feq))
      Equal.trans(SolveRef.Best,
        SolveFast.step(1n+p, gs,
          SolveFast.ClassItem{fb, ws, Groups.len_words(ws), tlb}
            <> (SolveFast.Add{fb, tlb} <> inner),
          G, S, n, nodup, inf, g, kids, sum, best,
          SolveFast.dummy_zero(), False{}, False{}),
        SolveFast.step(1n+p, gs, Nil{}, G, S, n, nodup, inf, Nil{}, Nil{}, 0n,
          best, SolveFast.dummy_zero(), False{},
          SolveFast.is_floor_hit(nodup, n, best)),
        SolveFast.step(1n+p, gs, Nil{}, G, S, n, nodup, inf, Nil{}, Nil{}, 0n,
          Eval.Eval.finish_ks(inf, g, S,
            Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg,
              kids, sum, inf),
            best),
          SolveFast.dummy_zero(), False{},
          SolveFast.is_floor_hit(nodup, n,
            Eval.Eval.finish_ks(inf, g, S,
              Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg,
                kids, sum, inf),
              best))),
        lhs_eq, rhs_eq)

# Step a live singleton `OneItem{fb, w}` directly into `Node{w, []}` of cost 1.
def FE.live_groups_one(+p: Nat, +gs: +List<+List<Nat>>, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +nodup: Bool, +inf: Nat, +g: +List<Nat>,
    +fb: +List<Feedback.Color>, +w: +List<Nat>,
    +restg: +List<Groups.Group>, +kids: +List<Tree.Child>, +sum: Nat,
    +best: SolveRef.Best,
    +ble: {Nat.is_le(1n, p) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +win: {Tree.member_word(w, G) == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    +alive: {Nat.is_lt(
               Nat.add(sum,
                 SolveFast.lower_bound(Groups.len_words(S),
                   Groups.Group{fb, w <> Nil{}} <> restg)),
               Eval.Eval.cost_of(best)) == True{} : Bool},
    rec_live: {Nat.is_lt(
                 Nat.add(
                   SolveRef.sat_add(inf, sum,
                     Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, w <> Nil{}))),
                   SolveFast.lower_bound(Groups.len_words(S), restg)),
                 Eval.Eval.cost_of(best)) == True{} : Bool} ->
              {SolveFast.step(1n+p, gs,
                 List.append(&2, SolveFast.Item,
                   SolveFast.group_items(Groups.len_words(S), restg),
                   SolveFast.End{} <> Nil{}),
                 G, S, Groups.len_words(S), nodup, inf, g,
                 Tree.Child{fb, Eval.Eval.tree_of(
                   FS.FS.ref_run_at(p, inf, G, w <> Nil{}))} <> kids,
                 SolveRef.sat_add(inf, sum,
                   Eval.Eval.cost_of(
                     FS.FS.ref_run_at(p, inf, G, w <> Nil{}))),
                 best, SolveFast.dummy_zero(), False{}, False{})
               == SolveFast.step(1n+p, gs, Nil{}, G, S, Groups.len_words(S),
                    nodup, inf, Nil{}, Nil{}, 0n,
                    Eval.Eval.finish_ks(inf, g, S,
                      Eval.Eval.items(p, G, S, g, restg,
                        Tree.Child{fb, Eval.Eval.tree_of(
                          FS.FS.ref_run_at(p, inf, G, w <> Nil{}))} <> kids,
                        SolveRef.sat_add(inf, sum,
                          Eval.Eval.cost_of(
                            FS.FS.ref_run_at(p, inf, G, w <> Nil{}))),
                        inf),
                      best),
                    SolveFast.dummy_zero(), False{},
                    SolveFast.is_floor_hit(nodup, Groups.len_words(S),
                      Eval.Eval.finish_ks(inf, g, S,
                        Eval.Eval.items(p, G, S, g, restg,
                          Tree.Child{fb, Eval.Eval.tree_of(
                            FS.FS.ref_run_at(p, inf, G, w <> Nil{}))} <> kids,
                          SolveRef.sat_add(inf, sum,
                            Eval.Eval.cost_of(
                              FS.FS.ref_run_at(p, inf, G, w <> Nil{}))),
                          inf),
                        best)))
               : SolveRef.Best}) ->
  {SolveFast.step(1n+p, gs,
     SolveFast.OneItem{fb, w}
       <> List.append(&2, SolveFast.Item,
            SolveFast.group_items(Groups.len_words(S), restg),
            SolveFast.End{} <> Nil{}),
     G, S, Groups.len_words(S), nodup, inf, g, kids, sum, best,
     SolveFast.dummy_zero(), False{}, False{})
   == SolveFast.step(1n+p, gs, Nil{}, G, S, Groups.len_words(S), nodup, inf,
        Nil{}, Nil{}, 0n,
        Eval.Eval.finish_ks(inf, g, S,
          Eval.Eval.items(p, G, S, g,
            Groups.Group{fb, w <> Nil{}} <> restg, kids, sum, inf),
          best),
        SolveFast.dummy_zero(), False{},
        SolveFast.is_floor_hit(nodup, Groups.len_words(S),
          Eval.Eval.finish_ks(inf, g, S,
            Eval.Eval.items(p, G, S, g,
              Groups.Group{fb, w <> Nil{}} <> restg, kids, sum, inf),
            best)))
   : SolveRef.Best}:
  +n : Nat = Groups.len_words(S)
  +tlb : Nat = SolveFast.lower_bound(n, restg)
  +inner : +List<SolveFast.Item> =
    List.append(&2, SolveFast.Item, SolveFast.group_items(n, restg),
      SolveFast.End{} <> Nil{})
  +b1 : SolveRef.Best = SolveRef.Best{Tree.Node{w, Nil{}}, 1n}
  +ref_c : SolveRef.Best = FS.FS.ref_run_at(p, inf, G, w <> Nil{})
  +eone : {b1 == ref_c : SolveRef.Best} =
    FO.FO.ref_run_one_eq(p, inf, G, w, ble, h1, win)
  +kr : +List<Tree.Child> = Tree.Child{fb, Eval.Eval.tree_of(ref_c)} <> kids
  +sr : Nat = SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(ref_c))
  +alive1 : {Nat.is_lt(Nat.add(SolveRef.sat_add(inf, sum, 1n), tlb),
               Eval.Eval.cost_of(best)) == True{} : Bool} =
    FC.FC.alive_one(inf, sum, tlb, Eval.Eval.cost_of(best), hbest, alive)
  +alive2 : {Nat.is_lt(Nat.add(sr, tlb), Eval.Eval.cost_of(best))
             == True{} : Bool} =
    Equal.trans(Bool,
      Nat.is_lt(Nat.add(sr, tlb), Eval.Eval.cost_of(best)),
      Nat.is_lt(Nat.add(SolveRef.sat_add(inf, sum, 1n), tlb),
        Eval.Eval.cost_of(best)),
      True{},
      Equal.cong(SolveRef.Best, Bool,
        c => Nat.is_lt(
               Nat.add(SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(c)), tlb),
               Eval.Eval.cost_of(best)),
        ref_c, b1,
        Equal.sym(SolveRef.Best, b1, ref_c, eone)),
      alive1)
  +e1 : {SolveFast.step(1n+p, gs, SolveFast.OneItem{fb, w} <> inner,
           G, S, n, nodup, inf, g, kids, sum, best,
           SolveFast.dummy_zero(), False{}, False{})
         == SolveFast.step(1n+p, gs, inner, G, S, n, nodup, inf, g,
              Tree.Child{fb, Tree.Node{w, Nil{}}} <> kids,
              SolveRef.sat_add(inf, sum, 1n), best,
              SolveFast.dummy_zero(), False{}, False{})
         : SolveRef.Best} =
    FS.FS.one_live(p, gs, G, S, n, nodup, inf, g, fb, w, inner, kids, sum, best)
  +e2 : {SolveFast.step(1n+p, gs, inner, G, S, n, nodup, inf, g,
           Tree.Child{fb, Tree.Node{w, Nil{}}} <> kids,
           SolveRef.sat_add(inf, sum, 1n), best,
           SolveFast.dummy_zero(), False{}, False{})
         == SolveFast.step(1n+p, gs, inner, G, S, n, nodup, inf, g, kr, sr,
              best, SolveFast.dummy_zero(), False{}, False{})
         : SolveRef.Best} =
    Equal.cong(SolveRef.Best, SolveRef.Best,
      c => SolveFast.step(1n+p, gs, inner, G, S, n, nodup, inf, g,
             Tree.Child{fb, Eval.Eval.tree_of(c)} <> kids,
             SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(c)),
             best, SolveFast.dummy_zero(), False{}, False{}),
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
  +e4 : {SolveFast.step(1n+p, gs, Nil{}, G, S, n, nodup, inf, Nil{}, Nil{}, 0n,
           Eval.Eval.finish_ks(inf, g, S,
             Eval.Eval.items(p, G, S, g, restg, kr, sr, inf), best),
           SolveFast.dummy_zero(), False{},
           SolveFast.is_floor_hit(nodup, n,
             Eval.Eval.finish_ks(inf, g, S,
               Eval.Eval.items(p, G, S, g, restg, kr, sr, inf), best)))
         == SolveFast.step(1n+p, gs, Nil{}, G, S, n, nodup, inf, Nil{}, Nil{},
              0n,
              Eval.Eval.finish_ks(inf, g, S,
                Eval.Eval.items(p, G, S, g,
                  Groups.Group{fb, w <> Nil{}} <> restg, kids, sum, inf),
                best),
              SolveFast.dummy_zero(), False{},
              SolveFast.is_floor_hit(nodup, n,
                Eval.Eval.finish_ks(inf, g, S,
                  Eval.Eval.items(p, G, S, g,
                    Groups.Group{fb, w <> Nil{}} <> restg, kids, sum, inf),
                  best)))
         : SolveRef.Best} =
    Equal.cong(Eval.KS, SolveRef.Best,
      ks => SolveFast.step(1n+p, gs, Nil{}, G, S, n, nodup, inf, Nil{}, Nil{},
              0n, Eval.Eval.finish_ks(inf, g, S, ks, best),
              SolveFast.dummy_zero(), False{},
              SolveFast.is_floor_hit(nodup, n,
                Eval.Eval.finish_ks(inf, g, S, ks, best))),
      Eval.Eval.items(p, G, S, g, restg, kr, sr, inf),
      Eval.Eval.items(p, G, S, g, Groups.Group{fb, w <> Nil{}} <> restg,
        kids, sum, inf),
      wk)
  Equal.trans(SolveRef.Best,
    SolveFast.step(1n+p, gs, SolveFast.OneItem{fb, w} <> inner,
      G, S, n, nodup, inf, g, kids, sum, best,
      SolveFast.dummy_zero(), False{}, False{}),
    SolveFast.step(1n+p, gs, inner, G, S, n, nodup, inf, g, kr, sr, best,
      SolveFast.dummy_zero(), False{}, False{}),
    SolveFast.step(1n+p, gs, Nil{}, G, S, n, nodup, inf, Nil{}, Nil{}, 0n,
      Eval.Eval.finish_ks(inf, g, S,
        Eval.Eval.items(p, G, S, g, Groups.Group{fb, w <> Nil{}} <> restg,
          kids, sum, inf),
        best),
      SolveFast.dummy_zero(), False{},
      SolveFast.is_floor_hit(nodup, n,
        Eval.Eval.finish_ks(inf, g, S,
          Eval.Eval.items(p, G, S, g, Groups.Group{fb, w <> Nil{}} <> restg,
            kids, sum, inf),
          best))),
    Equal.trans(SolveRef.Best,
      SolveFast.step(1n+p, gs, SolveFast.OneItem{fb, w} <> inner,
        G, S, n, nodup, inf, g, kids, sum, best,
        SolveFast.dummy_zero(), False{}, False{}),
      SolveFast.step(1n+p, gs, inner, G, S, n, nodup, inf, g,
        Tree.Child{fb, Tree.Node{w, Nil{}}} <> kids,
        SolveRef.sat_add(inf, sum, 1n), best,
        SolveFast.dummy_zero(), False{}, False{}),
      SolveFast.step(1n+p, gs, inner, G, S, n, nodup, inf, g, kr, sr, best,
        SolveFast.dummy_zero(), False{}, False{}),
      e1, e2),
    Equal.trans(SolveRef.Best,
      SolveFast.step(1n+p, gs, inner, G, S, n, nodup, inf, g, kr, sr, best,
        SolveFast.dummy_zero(), False{}, False{}),
      SolveFast.step(1n+p, gs, Nil{}, G, S, n, nodup, inf, Nil{}, Nil{}, 0n,
        Eval.Eval.finish_ks(inf, g, S,
          Eval.Eval.items(p, G, S, g, restg, kr, sr, inf), best),
        SolveFast.dummy_zero(), False{},
        SolveFast.is_floor_hit(nodup, n,
          Eval.Eval.finish_ks(inf, g, S,
            Eval.Eval.items(p, G, S, g, restg, kr, sr, inf), best))),
      SolveFast.step(1n+p, gs, Nil{}, G, S, n, nodup, inf, Nil{}, Nil{}, 0n,
        Eval.Eval.finish_ks(inf, g, S,
          Eval.Eval.items(p, G, S, g, Groups.Group{fb, w <> Nil{}} <> restg,
            kids, sum, inf),
          best),
        SolveFast.dummy_zero(), False{},
        SolveFast.is_floor_hit(nodup, n,
          Eval.Eval.finish_ks(inf, g, S,
            Eval.Eval.items(p, G, S, g, Groups.Group{fb, w <> Nil{}} <> restg,
              kids, sum, inf),
            best))),
      rec_live(alive2), e4))

# Stepping the remaining class items of a live block agrees with `Eval.finish_ks`
# on `Eval.items`, maintaining `sum + lower_bound(|S|, groups) < cost_of(best)`.
def FE.live_groups_eq(+p: Nat, +gs: +List<+List<Nat>>, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +nodup: Bool, +inf: Nat, +g: +List<Nat>,
    +groups: +List<Groups.Group>, +kids: +List<Tree.Child>, +sum: Nat,
    +best: SolveRef.Best,
    bounds: MV.MV.Bounds(p, MV.MV.next_groups(groups)),
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +ag: {FO.FO.all_in_jobs_b(MV.MV.next_groups(groups), G) == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    +hd: {SolveFast.is_floor_hit(nodup, Groups.len_words(S), best)
          == False{} : Bool},
    +alive: {Nat.is_lt(
               Nat.add(sum, SolveFast.lower_bound(Groups.len_words(S), groups)),
               Eval.Eval.cost_of(best)) == True{} : Bool},
    ec: FE.EClass(p, inf, G, nodup, groups)) ->
  {SolveFast.step(1n+p, gs,
     List.append(&2, SolveFast.Item,
       SolveFast.group_items(Groups.len_words(S), groups),
       SolveFast.End{} <> Nil{}),
     G, S, Groups.len_words(S), nodup, inf, g, kids, sum, best,
     SolveFast.dummy_zero(), False{}, False{})
   == SolveFast.step(1n+p, gs, Nil{}, G, S, Groups.len_words(S), nodup, inf,
        Nil{}, Nil{}, 0n,
        Eval.Eval.finish_ks(inf, g, S,
          Eval.Eval.items(p, G, S, g, groups, kids, sum, inf), best),
        SolveFast.dummy_zero(), False{},
        SolveFast.is_floor_hit(nodup, Groups.len_words(S),
          Eval.Eval.finish_ks(inf, g, S,
            Eval.Eval.items(p, G, S, g, groups, kids, sum, inf), best)))
   : SolveRef.Best}:
  match groups:
    case Nil{}:
      FS.FS.end_step(p, gs, G, S, Groups.len_words(S), nodup, inf, g, kids,
        sum, best, SolveFast.dummy_zero(), Nil{}, False{})
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
              +tlb : Nat = SolveFast.lower_bound(Groups.len_words(S), restg)
              MV.MV.use_pair(
                {SolveFast.step(1n+p, gs,
                   List.append(&2, SolveFast.Item,
                     SolveFast.group_items(Groups.len_words(S),
                       Groups.Group{fb, Nil{}} <> restg),
                     SolveFast.End{} <> Nil{}),
                   G, S, Groups.len_words(S), nodup, inf, g, kids, sum, best,
                   SolveFast.dummy_zero(), False{}, False{})
                 == SolveFast.step(1n+p, gs, Nil{}, G, S, Groups.len_words(S),
                      nodup, inf, Nil{}, Nil{}, 0n,
                      Eval.Eval.finish_ks(inf, g, S,
                        Eval.Eval.items(p, G, S, g,
                          Groups.Group{fb, Nil{}} <> restg, kids, sum, inf),
                        best),
                      SolveFast.dummy_zero(), False{},
                      SolveFast.is_floor_hit(nodup, Groups.len_words(S),
                        Eval.Eval.finish_ks(inf, g, S,
                          Eval.Eval.items(p, G, S, g,
                            Groups.Group{fb, Nil{}} <> restg, kids, sum, inf),
                          best)))
                 : SolveRef.Best},
                MV.MV.Bounds(p, MV.MV.next_groups(restg)),
                MV.MV.Bounds(p, MV.MV.next_groups(restg)),
                FE.bounds_copy(p, MV.MV.next_groups(restg), bt),
                bt1 => bt2 =>
                  FE.live_group_cutoff_go(p, gs, G, S, nodup, inf, g, fb, Nil{},
                    restg, kids, sum, best, ble, bt2, hz, hbest, hd, alive, eh,
                    Nat.is_lt(
                      Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, Nil{})),
                      FS.FS.child_cutoff(best, sum, tlb)),
                    {==},
                    alive2 =>
                      FE.live_groups_eq(p, gs, G, S, nodup, inf, g, restg,
                        Tree.Child{fb, Eval.Eval.tree_of(
                          FS.FS.ref_run_at(p, inf, G, Nil{}))} <> kids,
                        SolveRef.sat_add(inf, sum,
                          Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, Nil{}))),
                        best, bt1, hz, h1, ag_rest, hbest, hd, alive2, et)))
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
                  FE.live_groups_one(p, gs, G, S, nodup, inf, g, fb, w, restg,
                    kids, sum, best, ble, h1, win, hbest, alive,
                    alive2 =>
                      FE.live_groups_eq(p, gs, G, S, nodup, inf, g, restg,
                        Tree.Child{fb, Eval.Eval.tree_of(
                          FS.FS.ref_run_at(p, inf, G, w <> Nil{}))} <> kids,
                        SolveRef.sat_add(inf, sum,
                          Eval.Eval.cost_of(
                            FS.FS.ref_run_at(p, inf, G, w <> Nil{}))),
                        best, bt, hz, h1, ag_rest, hbest, hd, alive2, et))
                case Con{+w2, +wt2}:
                  (+ble, bt) = bounds
                  (eh, et) = ec
                  +ws2 : +List<+List<Nat>> = w <> (w2 <> wt2)
                  +ag_rest : {FO.FO.all_in_jobs_b(MV.MV.next_groups(restg), G)
                              == True{} : Bool} =
                    Logic.Proof.and_true_r(FO.FO.all_in_ref(ws2, G),
                      FO.FO.all_in_jobs_b(MV.MV.next_groups(restg), G), ag)
                  +tlb : Nat = SolveFast.lower_bound(Groups.len_words(S), restg)
                  MV.MV.use_pair(
                    {SolveFast.step(1n+p, gs,
                       List.append(&2, SolveFast.Item,
                         SolveFast.group_items(Groups.len_words(S),
                           Groups.Group{fb, ws2} <> restg),
                         SolveFast.End{} <> Nil{}),
                       G, S, Groups.len_words(S), nodup, inf, g, kids, sum,
                       best, SolveFast.dummy_zero(), False{}, False{})
                     == SolveFast.step(1n+p, gs, Nil{}, G, S,
                          Groups.len_words(S), nodup, inf, Nil{}, Nil{}, 0n,
                          Eval.Eval.finish_ks(inf, g, S,
                            Eval.Eval.items(p, G, S, g,
                              Groups.Group{fb, ws2} <> restg, kids, sum, inf),
                            best),
                          SolveFast.dummy_zero(), False{},
                          SolveFast.is_floor_hit(nodup, Groups.len_words(S),
                            Eval.Eval.finish_ks(inf, g, S,
                              Eval.Eval.items(p, G, S, g,
                                Groups.Group{fb, ws2} <> restg, kids, sum, inf),
                              best)))
                     : SolveRef.Best},
                    MV.MV.Bounds(p, MV.MV.next_groups(restg)),
                    MV.MV.Bounds(p, MV.MV.next_groups(restg)),
                    FE.bounds_copy(p, MV.MV.next_groups(restg), bt),
                    bt1 => bt2 =>
                      FE.live_group_cutoff_go(p, gs, G, S, nodup, inf, g, fb,
                        ws2, restg, kids, sum, best, ble, bt2, hz, hbest, hd,
                        alive, eh,
                        Nat.is_lt(
                          Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, ws2)),
                          FS.FS.child_cutoff(best, sum, tlb)),
                        {==},
                        alive2 =>
                          FE.live_groups_eq(p, gs, G, S, nodup, inf, g, restg,
                            Tree.Child{fb, Eval.Eval.tree_of(
                              FS.FS.ref_run_at(p, inf, G, ws2))} <> kids,
                            SolveRef.sat_add(inf, sum,
                              Eval.Eval.cost_of(
                                FS.FS.ref_run_at(p, inf, G, ws2))),
                            best, bt1, hz, h1, ag_rest, hbest, hd, alive2, et)))

# Rewrite `step(..., Nil{}, ..., best, ..., False{})` to use
# `is_floor_hit(nodup, n, best2)` when `best2 == best`.
def FE.keep_best_step(+p: Nat, +gs: +List<+List<Nat>>, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +nodup: Bool, +inf: Nat, +best: SolveRef.Best,
    +best2: SolveRef.Best,
    +hd: {SolveFast.is_floor_hit(nodup, Groups.len_words(S), best)
          == False{} : Bool},
    +eqb: {best2 == best : SolveRef.Best}) ->
  {SolveFast.step(1n+p, gs, Nil{}, G, S, Groups.len_words(S), nodup, inf,
     Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{}, False{})
   == SolveFast.step(1n+p, gs, Nil{}, G, S, Groups.len_words(S), nodup, inf,
        Nil{}, Nil{}, 0n, best2, SolveFast.dummy_zero(), False{},
        SolveFast.is_floor_hit(nodup, Groups.len_words(S), best2))
   : SolveRef.Best}:
  +n : Nat = Groups.len_words(S)
  Equal.trans(SolveRef.Best,
    SolveFast.step(1n+p, gs, Nil{}, G, S, n, nodup, inf, Nil{}, Nil{}, 0n,
      best, SolveFast.dummy_zero(), False{}, False{}),
    SolveFast.step(1n+p, gs, Nil{}, G, S, n, nodup, inf, Nil{}, Nil{}, 0n,
      best, SolveFast.dummy_zero(), False{},
      SolveFast.is_floor_hit(nodup, n, best)),
    SolveFast.step(1n+p, gs, Nil{}, G, S, n, nodup, inf, Nil{}, Nil{}, 0n,
      best2, SolveFast.dummy_zero(), False{},
      SolveFast.is_floor_hit(nodup, n, best2)),
    Equal.cong(Bool, SolveRef.Best,
      dn => SolveFast.step(1n+p, gs, Nil{}, G, S, n, nodup, inf, Nil{}, Nil{},
              0n, best, SolveFast.dummy_zero(), False{}, dn),
      False{}, SolveFast.is_floor_hit(nodup, n, best),
      Equal.sym(Bool, SolveFast.is_floor_hit(nodup, n, best), False{}, hd)),
    Equal.cong(SolveRef.Best, SolveRef.Best,
      b => SolveFast.step(1n+p, gs, Nil{}, G, S, n, nodup, inf, Nil{}, Nil{},
             0n, b, SolveFast.dummy_zero(), False{},
             SolveFast.is_floor_hit(nodup, n, b)),
      best, best2, Equal.sym(SolveRef.Best, best2, best, eqb)))

# Stepping `schedule_fguess_lb` on a usable guess agrees with `Eval.block`.
def FE.schedule_fguess_lb_step(+p: Nat, +gs: +List<+List<Nat>>,
    +G: +List<+List<Nat>>, +S: +List<+List<Nat>>, +nodup: Bool, +inf: Nat,
    +g: +List<Nat>, +fgroups: +List<SolveFast.FGroup>, +best: SolveRef.Best,
    skip: Bool,
    +esk: {skip == SolveFast.skippable(best,
             SolveFast.fgroups_lb(nodup, Groups.len_words(S), fgroups)) : Bool},
    +lok: {FN.FN.fgroups_lens_ok(fgroups) == True{} : Bool},
    +us: {Groups.groups_smaller(S, FN.FN.fgroups_to_groups(fgroups))
          == True{} : Bool},
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +ag: {FO.FO.all_in_jobs_b(
            MV.MV.next_groups(FN.FN.fgroups_to_groups(fgroups)), G)
          == True{} : Bool},
    +ng: {FN.FN.nodup_ok_jobs(nodup,
            MV.MV.next_groups(FN.FN.fgroups_to_groups(fgroups)))
          == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    +hd: {SolveFast.is_floor_hit(nodup, Groups.len_words(S), best)
          == False{} : Bool},
    ec: FE.EClass(p, inf, G, nodup, FN.FN.fgroups_to_groups(fgroups))) ->
  {SolveFast.step(1n+p, gs,
     SolveFast.schedule_fguess_lb(nodup, g, fgroups, Groups.len_words(S), skip),
     G, S, Groups.len_words(S), nodup, inf, Nil{}, Nil{}, 0n, best,
     SolveFast.dummy_zero(), False{}, False{})
   == SolveFast.step(1n+p, gs, Nil{}, G, S, Groups.len_words(S), nodup, inf,
        Nil{}, Nil{}, 0n,
        Eval.Eval.block(p, G, S, g, inf, FN.FN.fgroups_to_groups(fgroups), best),
        SolveFast.dummy_zero(), False{},
        SolveFast.is_floor_hit(nodup, Groups.len_words(S),
          Eval.Eval.block(p, G, S, g, inf, FN.FN.fgroups_to_groups(fgroups),
            best)))
   : SolveRef.Best}:
  match skip:
    case True{}:
      +n : Nat = Groups.len_words(S)
      +groups : +List<Groups.Group> = FN.FN.fgroups_to_groups(fgroups)
      +elb : {SolveFast.fgroups_lb(nodup, n, fgroups)
              == SolveFast.lower_bound(n, groups) : Nat} =
        FN.FN.fgroups_lb_eq(nodup, n, fgroups, lok, ng)
      +eskp : {SolveFast.skippable(best, SolveFast.lower_bound(n, groups))
               == True{} : Bool} =
        Equal.trans(Bool,
          SolveFast.skippable(best, SolveFast.lower_bound(n, groups)),
          SolveFast.skippable(best, SolveFast.fgroups_lb(nodup, n, fgroups)),
          True{},
          Equal.cong(Nat, Bool, x => SolveFast.skippable(best, x),
            SolveFast.lower_bound(n, groups),
            SolveFast.fgroups_lb(nodup, n, fgroups),
            Equal.sym(Nat, SolveFast.fgroups_lb(nodup, n, fgroups),
              SolveFast.lower_bound(n, groups), elb)),
          Equal.sym(Bool, True{},
            SolveFast.skippable(best, SolveFast.fgroups_lb(nodup, n, fgroups)),
            esk))
      +le : {Nat.is_le(Eval.Eval.cost_of(best),
               SolveFast.lower_bound(n, groups)) == True{} : Bool} =
        FLB.FS.skippable_to_le(best, SolveFast.lower_bound(n, groups), eskp)
      +beq : {Eval.Eval.block(p, G, S, g, inf, groups, best) == best
              : SolveRef.Best} =
        FLB.FS.block_skip_eq(p, inf, G, S, g, groups, best, us, ele, hz,
          hbest, le)
      FE.keep_best_step(p, gs, G, S, nodup, inf, best,
        Eval.Eval.block(p, G, S, g, inf, groups, best), hd, beq)
    case False{}:
      +n : Nat = Groups.len_words(S)
      +groups : +List<Groups.Group> = FN.FN.fgroups_to_groups(fgroups)
      +lb : Nat = SolveFast.lower_bound(n, groups)
      +elb : {SolveFast.fgroups_lb(nodup, n, fgroups) == lb : Nat} =
        FN.FN.fgroups_lb_eq(nodup, n, fgroups, lok, ng)
      +eskp : {SolveFast.skippable(best, lb) == False{} : Bool} =
        Equal.trans(Bool,
          SolveFast.skippable(best, lb),
          SolveFast.skippable(best, SolveFast.fgroups_lb(nodup, n, fgroups)),
          False{},
          Equal.cong(Nat, Bool, x => SolveFast.skippable(best, x),
            lb, SolveFast.fgroups_lb(nodup, n, fgroups),
            Equal.sym(Nat, SolveFast.fgroups_lb(nodup, n, fgroups), lb, elb)),
          Equal.sym(Bool, False{},
            SolveFast.skippable(best, SolveFast.fgroups_lb(nodup, n, fgroups)),
            esk))
      +alive0 : {Nat.is_lt(lb, Eval.Eval.cost_of(best)) == True{} : Bool} =
        FE.lt_of_skippable_false(best, lb, eskp)
      +body : +List<SolveFast.Item> =
        List.append(&2, SolveFast.Item, SolveFast.group_items(n, groups),
          SolveFast.End{} <> Nil{})
      +e0 : {SolveFast.step(1n+p, gs,
               SolveFast.schedule_guess_ib(g,
                 SolveFast.fgroup_items_build(nodup, n, fgroups,
                   SolveFast.End{} <> Nil{})),
               G, S, n, nodup, inf, Nil{}, Nil{}, 0n, best,
               SolveFast.dummy_zero(), False{}, False{})
             == SolveFast.step(1n+p, gs, SolveFast.Begin{g} <> body, G, S, n,
                  nodup, inf, Nil{}, Nil{}, 0n, best,
                  SolveFast.dummy_zero(), False{}, False{})
             : SolveRef.Best} =
        Equal.cong(SolveFast.ItemsBound, SolveRef.Best,
          ib => SolveFast.step(1n+p, gs, SolveFast.schedule_guess_ib(g, ib),
                  G, S, n, nodup, inf, Nil{}, Nil{}, 0n, best,
                  SolveFast.dummy_zero(), False{}, False{}),
          SolveFast.fgroup_items_build(nodup, n, fgroups,
            SolveFast.End{} <> Nil{}),
          SolveFast.ItemsBound{lb, body},
          FN.FN.fgroup_items_build_eq(nodup, n, fgroups,
            SolveFast.End{} <> Nil{}, lok, ng))
      +e1 : {SolveFast.step(1n+p, gs, SolveFast.Begin{g} <> body, G, S, n,
               nodup, inf, Nil{}, Nil{}, 0n, best,
               SolveFast.dummy_zero(), False{}, False{})
             == SolveFast.step(1n+p, gs, body, G, S, n, nodup, inf, g, Nil{},
                  0n, best, SolveFast.dummy_zero(), False{}, False{})
             : SolveRef.Best} =
        FS.FS.begin_succ(p, gs, G, S, n, nodup, inf, Nil{}, g, Nil{}, 0n, best,
          SolveFast.dummy_zero(), False{}, False{}, body)
      bounds : MV.MV.Bounds(p, MV.MV.next_groups(groups)) =
        MV.MV.group_bounds(p, S, groups, ele,
          GM.GM.groups_smaller_sound(S, groups, us))
      +e2 : {SolveFast.step(1n+p, gs, body, G, S, n, nodup, inf, g, Nil{}, 0n,
               best, SolveFast.dummy_zero(), False{}, False{})
             == SolveFast.step(1n+p, gs, Nil{}, G, S, n, nodup, inf, Nil{},
                  Nil{}, 0n, Eval.Eval.block(p, G, S, g, inf, groups, best),
                  SolveFast.dummy_zero(), False{},
                  SolveFast.is_floor_hit(nodup, n,
                    Eval.Eval.block(p, G, S, g, inf, groups, best)))
             : SolveRef.Best} =
        FE.live_groups_eq(p, gs, G, S, nodup, inf, g, groups, Nil{}, 0n, best,
          bounds, hz, h1, ag, hbest, hd, alive0, ec)
      Equal.trans(SolveRef.Best,
        SolveFast.step(1n+p, gs,
          SolveFast.schedule_guess_ib(g,
            SolveFast.fgroup_items_build(nodup, n, fgroups,
              SolveFast.End{} <> Nil{})),
          G, S, n, nodup, inf, Nil{}, Nil{}, 0n, best,
          SolveFast.dummy_zero(), False{}, False{}),
        SolveFast.step(1n+p, gs, body, G, S, n, nodup, inf, g, Nil{}, 0n, best,
          SolveFast.dummy_zero(), False{}, False{}),
        SolveFast.step(1n+p, gs, Nil{}, G, S, n, nodup, inf, Nil{}, Nil{}, 0n,
          Eval.Eval.block(p, G, S, g, inf, groups, best),
          SolveFast.dummy_zero(), False{},
          SolveFast.is_floor_hit(nodup, n,
            Eval.Eval.block(p, G, S, g, inf, groups, best))),
        Equal.trans(SolveRef.Best,
          SolveFast.step(1n+p, gs,
            SolveFast.schedule_guess_ib(g,
              SolveFast.fgroup_items_build(nodup, n, fgroups,
                SolveFast.End{} <> Nil{})),
            G, S, n, nodup, inf, Nil{}, Nil{}, 0n, best,
            SolveFast.dummy_zero(), False{}, False{}),
          SolveFast.step(1n+p, gs, SolveFast.Begin{g} <> body, G, S, n, nodup,
            inf, Nil{}, Nil{}, 0n, best,
            SolveFast.dummy_zero(), False{}, False{}),
          SolveFast.step(1n+p, gs, body, G, S, n, nodup, inf, g, Nil{}, 0n,
            best, SolveFast.dummy_zero(), False{}, False{}),
          e0, e1),
        e2)

# Stepping `schedule_fguess` agrees with `Eval.guess_bool`.
def FE.schedule_fguess_step(+p: Nat, +gs: +List<+List<Nat>>,
    +G: +List<+List<Nat>>, +S: +List<+List<Nat>>, +nodup: Bool, +inf: Nat,
    +g: +List<Nat>, +fgroups: +List<SolveFast.FGroup>, +best: SolveRef.Best,
    usable: Bool,
    +eus: {usable == Groups.groups_smaller(S, FN.FN.fgroups_to_groups(fgroups))
           : Bool},
    +lok: {FN.FN.fgroups_lens_ok(fgroups) == True{} : Bool},
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +ag: {FO.FO.all_in_jobs_b(
            MV.MV.next_groups(FN.FN.fgroups_to_groups(fgroups)), G)
          == True{} : Bool},
    +ng: {FN.FN.nodup_ok_jobs(nodup,
            MV.MV.next_groups(FN.FN.fgroups_to_groups(fgroups)))
          == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    +hd: {SolveFast.is_floor_hit(nodup, Groups.len_words(S), best)
          == False{} : Bool},
    ecif: FE.EClassIf(usable, p, inf, G, nodup,
            FN.FN.fgroups_to_groups(fgroups))) ->
  {SolveFast.step(1n+p, gs,
     SolveFast.schedule_fguess(nodup, g, fgroups, Groups.len_words(S), best,
       usable),
     G, S, Groups.len_words(S), nodup, inf, Nil{}, Nil{}, 0n, best,
     SolveFast.dummy_zero(), False{}, False{})
   == SolveFast.step(1n+p, gs, Nil{}, G, S, Groups.len_words(S), nodup, inf,
        Nil{}, Nil{}, 0n,
        Eval.Eval.guess_bool(p, G, S, g, FN.FN.fgroups_to_groups(fgroups), inf,
          usable, best),
        SolveFast.dummy_zero(), False{},
        SolveFast.is_floor_hit(nodup, Groups.len_words(S),
          Eval.Eval.guess_bool(p, G, S, g, FN.FN.fgroups_to_groups(fgroups),
            inf, usable, best)))
   : SolveRef.Best}:
  match usable:
    case False{}:
      FE.keep_best_step(p, gs, G, S, nodup, inf, best, best, hd, {==})
    case True{}:
      +n : Nat = Groups.len_words(S)
      +us : {Groups.groups_smaller(S, FN.FN.fgroups_to_groups(fgroups))
             == True{} : Bool} =
        Equal.sym(Bool, True{},
          Groups.groups_smaller(S, FN.FN.fgroups_to_groups(fgroups)), eus)
      FE.schedule_fguess_lb_step(p, gs, G, S, nodup, inf, g, fgroups, best,
        SolveFast.skippable(best, SolveFast.fgroups_lb(nodup, n, fgroups)),
        {==}, lok, us, ele, hz, h1, ag, ng, hbest, hd, ecif)

# Stepping `schedule_one_guess` on `[w]` agrees with `Eval.guess`.
def FE.schedule_one_lb_step(+p: Nat, +gs: +List<+List<Nat>>,
    +G: +List<+List<Nat>>, +w: +List<Nat>, +nodup: Bool, +inf: Nat,
    +g: +List<Nat>, +best: SolveRef.Best, skip: Bool,
    +esk: {skip == SolveFast.skippable(best, 1n) : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    +hd: {SolveFast.is_floor_hit(nodup, 1n, best) == False{} : Bool}) ->
  {SolveFast.step(1n+p, gs, SolveFast.schedule_one_lb(g, skip),
     G, w <> Nil{}, 1n, nodup, inf, Nil{}, Nil{}, 0n, best,
     SolveFast.dummy_zero(), False{}, False{})
   == SolveFast.step(1n+p, gs, Nil{}, G, w <> Nil{}, 1n, nodup, inf,
        Nil{}, Nil{}, 0n,
        SolveRef.finish_guess(inf, g, Nil{}, 0n, 1n, best),
        SolveFast.dummy_zero(), False{},
        SolveFast.is_floor_hit(nodup, 1n,
          SolveRef.finish_guess(inf, g, Nil{}, 0n, 1n, best)))
   : SolveRef.Best}:
  match skip:
    case True{}:
      +le : {Nat.is_le(Eval.Eval.cost_of(best), 1n) == True{} : Bool} =
        FLB.FS.skippable_to_le(best, 1n,
          Equal.sym(Bool, True{}, SolveFast.skippable(best, 1n), esk))
      +beq : {Eval.Eval.block(p, G, w <> Nil{}, g, inf, Nil{}, best) == best
              : SolveRef.Best} =
        FLB.FS.block_skip_eq(p, inf, G, w <> Nil{}, g, Nil{}, best, {==},
          NatProof.Nat.is_le_zero_l(p), hz, hbest, le)
      FE.keep_best_step(p, gs, G, w <> Nil{}, nodup, inf, best,
        SolveRef.finish_guess(inf, g, Nil{}, 0n, 1n, best), hd, beq)
    case False{}:
      Equal.trans(SolveRef.Best,
        SolveFast.step(1n+p, gs, SolveFast.Begin{g} <> (SolveFast.End{} <> Nil{}),
          G, w <> Nil{}, 1n, nodup, inf, Nil{}, Nil{}, 0n, best,
          SolveFast.dummy_zero(), False{}, False{}),
        SolveFast.step(1n+p, gs, SolveFast.End{} <> Nil{}, G, w <> Nil{}, 1n,
          nodup, inf, g, Nil{}, 0n, best,
          SolveFast.dummy_zero(), False{}, False{}),
        SolveFast.step(1n+p, gs, Nil{}, G, w <> Nil{}, 1n, nodup, inf,
          Nil{}, Nil{}, 0n,
          SolveRef.finish_guess(inf, g, Nil{}, 0n, 1n, best),
          SolveFast.dummy_zero(), False{},
          SolveFast.is_floor_hit(nodup, 1n,
            SolveRef.finish_guess(inf, g, Nil{}, 0n, 1n, best))),
        FS.FS.begin_succ(p, gs, G, w <> Nil{}, 1n, nodup, inf, Nil{}, g, Nil{},
          0n, best, SolveFast.dummy_zero(), False{}, False{},
          SolveFast.End{} <> Nil{}),
        FS.FS.end_step(p, gs, G, w <> Nil{}, 1n, nodup, inf, g, Nil{}, 0n,
          best, SolveFast.dummy_zero(), Nil{}, False{}))

def FE.schedule_one_step(+p: Nat, +gs: +List<+List<Nat>>,
    +G: +List<+List<Nat>>, +w: +List<Nat>, +nodup: Bool, +inf: Nat,
    +g: +List<Nat>, +best: SolveRef.Best, same: Bool,
    +es: {same == Feedback.word_eq(g, w) : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    +hd: {SolveFast.is_floor_hit(nodup, 1n, best) == False{} : Bool}) ->
  {SolveFast.step(1n+p, gs, SolveFast.schedule_one_guess(g, best, same),
     G, w <> Nil{}, 1n, nodup, inf, Nil{}, Nil{}, 0n, best,
     SolveFast.dummy_zero(), False{}, False{})
   == SolveFast.step(1n+p, gs, Nil{}, G, w <> Nil{}, 1n, nodup, inf,
        Nil{}, Nil{}, 0n,
        Eval.Eval.guess(p, G, w <> Nil{}, g, inf, best),
        SolveFast.dummy_zero(), False{},
        SolveFast.is_floor_hit(nodup, 1n,
          Eval.Eval.guess(p, G, w <> Nil{}, g, inf, best)))
   : SolveRef.Best}:
  match same:
    case True{}:
      +eg : {Eval.Eval.guess(p, G, w <> Nil{}, g, inf, best)
             == Feedback.Bool.case(SolveRef.Best, Feedback.word_eq(g, w),
                  SolveRef.finish_guess(inf, g, Nil{}, 0n, 1n, best), best)
             : SolveRef.Best} =
        FO.FO.eval_guess_one(p, G, w, g, inf, best, Feedback.word_eq(g, w))
      +eg2 : {Eval.Eval.guess(p, G, w <> Nil{}, g, inf, best)
              == SolveRef.finish_guess(inf, g, Nil{}, 0n, 1n, best)
              : SolveRef.Best} =
        Equal.trans(SolveRef.Best,
          Eval.Eval.guess(p, G, w <> Nil{}, g, inf, best),
          Feedback.Bool.case(SolveRef.Best, Feedback.word_eq(g, w),
            SolveRef.finish_guess(inf, g, Nil{}, 0n, 1n, best), best),
          SolveRef.finish_guess(inf, g, Nil{}, 0n, 1n, best),
          eg,
          Equal.cong(Bool, SolveRef.Best,
            b => Feedback.Bool.case(SolveRef.Best, b,
                   SolveRef.finish_guess(inf, g, Nil{}, 0n, 1n, best), best),
            Feedback.word_eq(g, w), True{},
            Equal.sym(Bool, True{}, Feedback.word_eq(g, w), es)))
      Equal.trans(SolveRef.Best,
        SolveFast.step(1n+p, gs,
          SolveFast.schedule_one_lb(g, SolveFast.skippable(best, 1n)),
          G, w <> Nil{}, 1n, nodup, inf, Nil{}, Nil{}, 0n, best,
          SolveFast.dummy_zero(), False{}, False{}),
        SolveFast.step(1n+p, gs, Nil{}, G, w <> Nil{}, 1n, nodup, inf,
          Nil{}, Nil{}, 0n,
          SolveRef.finish_guess(inf, g, Nil{}, 0n, 1n, best),
          SolveFast.dummy_zero(), False{},
          SolveFast.is_floor_hit(nodup, 1n,
            SolveRef.finish_guess(inf, g, Nil{}, 0n, 1n, best))),
        SolveFast.step(1n+p, gs, Nil{}, G, w <> Nil{}, 1n, nodup, inf,
          Nil{}, Nil{}, 0n,
          Eval.Eval.guess(p, G, w <> Nil{}, g, inf, best),
          SolveFast.dummy_zero(), False{},
          SolveFast.is_floor_hit(nodup, 1n,
            Eval.Eval.guess(p, G, w <> Nil{}, g, inf, best))),
        FE.schedule_one_lb_step(p, gs, G, w, nodup, inf, g, best,
          SolveFast.skippable(best, 1n), {==}, hz, hbest, hd),
        Equal.cong(SolveRef.Best, SolveRef.Best,
          b => SolveFast.step(1n+p, gs, Nil{}, G, w <> Nil{}, 1n, nodup, inf,
                 Nil{}, Nil{}, 0n, b, SolveFast.dummy_zero(), False{},
                 SolveFast.is_floor_hit(nodup, 1n, b)),
          SolveRef.finish_guess(inf, g, Nil{}, 0n, 1n, best),
          Eval.Eval.guess(p, G, w <> Nil{}, g, inf, best),
          Equal.sym(SolveRef.Best,
            Eval.Eval.guess(p, G, w <> Nil{}, g, inf, best),
            SolveRef.finish_guess(inf, g, Nil{}, 0n, 1n, best), eg2)))
    case False{}:
      +eg : {Eval.Eval.guess(p, G, w <> Nil{}, g, inf, best)
             == Feedback.Bool.case(SolveRef.Best, Feedback.word_eq(g, w),
                  SolveRef.finish_guess(inf, g, Nil{}, 0n, 1n, best), best)
             : SolveRef.Best} =
        FO.FO.eval_guess_one(p, G, w, g, inf, best, Feedback.word_eq(g, w))
      +eg2 : {Eval.Eval.guess(p, G, w <> Nil{}, g, inf, best) == best
              : SolveRef.Best} =
        Equal.trans(SolveRef.Best,
          Eval.Eval.guess(p, G, w <> Nil{}, g, inf, best),
          Feedback.Bool.case(SolveRef.Best, Feedback.word_eq(g, w),
            SolveRef.finish_guess(inf, g, Nil{}, 0n, 1n, best), best),
          best,
          eg,
          Equal.cong(Bool, SolveRef.Best,
            b => Feedback.Bool.case(SolveRef.Best, b,
                   SolveRef.finish_guess(inf, g, Nil{}, 0n, 1n, best), best),
            Feedback.word_eq(g, w), False{},
            Equal.sym(Bool, False{}, Feedback.word_eq(g, w), es)))
      FE.keep_best_step(p, gs, G, w <> Nil{}, nodup, inf, best,
        Eval.Eval.guess(p, G, w <> Nil{}, g, inf, best), hd, eg2)

def FE.eclass_if_transport(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +nodup: Bool,
    +g1: +List<Groups.Group>, +g2: +List<Groups.Group>,
    e: {g1 == g2 : +List<Groups.Group>},
    ecif: FE.EClassIf(Groups.groups_smaller(S, g1), p, inf, G, nodup, g1)) ->
  FE.EClassIf(Groups.groups_smaller(S, g2), p, inf, G, nodup, g2):
  %e : FE.EClassIf(Groups.groups_smaller(S, _), p, inf, G, nodup, _)
  ecif

# Stepping `guess_body` agrees with `Eval.guess` on any `S`.
def FE.guess_body_fgroup_step(+p: Nat, +gs: +List<+List<Nat>>,
    +G: +List<+List<Nat>>, +S: +List<+List<Nat>>, +nodup: Bool, +inf: Nat,
    +g: +List<Nat>, +best: SolveRef.Best,
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +ai: {FO.FO.all_in_ref(S, G) == True{} : Bool},
    +nd: {FN.FN.nodup_ok(nodup, S) == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    +hd: {SolveFast.is_floor_hit(nodup, Groups.len_words(S), best)
          == False{} : Bool},
    ecif: FE.EClassIf(
            Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
            p, inf, G, nodup, Groups.groups_build(g, S, Nil{}))) ->
  {SolveFast.step(1n+p, gs,
     SolveFast.schedule_fguess(nodup, g, SolveFast.fgroups_build_fast(g, S, Nil{}),
       Groups.len_words(S), best,
       SolveFast.fgroups_smaller(Groups.len_words(S),
         SolveFast.fgroups_build_fast(g, S, Nil{}))),
     G, S, Groups.len_words(S), nodup, inf, Nil{}, Nil{}, 0n, best,
     SolveFast.dummy_zero(), False{}, False{})
   == SolveFast.step(1n+p, gs, Nil{}, G, S, Groups.len_words(S), nodup, inf,
        Nil{}, Nil{}, 0n,
        Eval.Eval.guess(p, G, S, g, inf, best),
        SolveFast.dummy_zero(), False{},
        SolveFast.is_floor_hit(nodup, Groups.len_words(S),
          Eval.Eval.guess(p, G, S, g, inf, best)))
   : SolveRef.Best}:
  +n : Nat = Groups.len_words(S)
  +fg : +List<SolveFast.FGroup> = SolveFast.fgroups_build_fast(g, S, Nil{})
  +fg_g : +List<Groups.Group> = FN.FN.fgroups_to_groups(fg)
  +groups : +List<Groups.Group> = Groups.groups_build(g, S, Nil{})
  +egrp : {fg_g == groups : +List<Groups.Group>} =
    FN.FN.fgroups_build_eq(g, S, Nil{})
  +lok : {FN.FN.fgroups_lens_ok(fg) == True{} : Bool} =
    FN.FN.fgroups_build_lens_ok(g, S, Nil{}, {==})
  +ag0 : {FO.FO.all_in_jobs_b(MV.MV.next_groups(groups), G) == True{} : Bool} =
    FO.FO.all_in_next_groups(groups, S, G,
      CoverGroups.Cover.all_subseq_nil(g, S), ai)
  +ag : {FO.FO.all_in_jobs_b(MV.MV.next_groups(fg_g), G) == True{} : Bool} =
    Equal.trans(Bool,
      FO.FO.all_in_jobs_b(MV.MV.next_groups(fg_g), G),
      FO.FO.all_in_jobs_b(MV.MV.next_groups(groups), G),
      True{},
      Equal.cong(+List<Groups.Group>, Bool,
        grp => FO.FO.all_in_jobs_b(MV.MV.next_groups(grp), G),
        fg_g, groups, egrp),
      ag0)
  +ng0 : {FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(groups))
          == True{} : Bool} =
    FN.FN.nodup_ok_next_groups(nodup, groups, S,
      CoverGroups.Cover.all_subseq_nil(g, S), nd)
  +ng : {FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(fg_g)) == True{} : Bool} =
    Equal.trans(Bool,
      FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(fg_g)),
      FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(groups)),
      True{},
      Equal.cong(+List<Groups.Group>, Bool,
        grp => FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(grp)),
        fg_g, groups, egrp),
      ng0)
  ecif_fg : FE.EClassIf(Groups.groups_smaller(S, fg_g), p, inf, G, nodup, fg_g) =
    FE.eclass_if_transport(p, inf, G, S, nodup, groups, fg_g,
      Equal.sym(+List<Groups.Group>, fg_g, groups, egrp), ecif)
  +e0 : {SolveFast.step(1n+p, gs,
           SolveFast.schedule_fguess(nodup, g, fg, n, best,
             SolveFast.fgroups_smaller(n, fg)),
           G, S, n, nodup, inf, Nil{}, Nil{}, 0n, best,
           SolveFast.dummy_zero(), False{}, False{})
         == SolveFast.step(1n+p, gs,
              SolveFast.schedule_fguess(nodup, g, fg, n, best,
                Groups.groups_smaller(S, fg_g)),
              G, S, n, nodup, inf, Nil{}, Nil{}, 0n, best,
              SolveFast.dummy_zero(), False{}, False{})
         : SolveRef.Best} =
    Equal.cong(Bool, SolveRef.Best,
      u => SolveFast.step(1n+p, gs,
             SolveFast.schedule_fguess(nodup, g, fg, n, best, u),
             G, S, n, nodup, inf, Nil{}, Nil{}, 0n, best,
             SolveFast.dummy_zero(), False{}, False{}),
      SolveFast.fgroups_smaller(n, fg), Groups.groups_smaller(S, fg_g),
      FN.FN.fgroups_smaller_eq(S, fg, lok))
  +e1 : {SolveFast.step(1n+p, gs,
           SolveFast.schedule_fguess(nodup, g, fg, n, best,
             Groups.groups_smaller(S, fg_g)),
           G, S, n, nodup, inf, Nil{}, Nil{}, 0n, best,
           SolveFast.dummy_zero(), False{}, False{})
         == SolveFast.step(1n+p, gs, Nil{}, G, S, n, nodup, inf, Nil{}, Nil{},
              0n,
              Eval.Eval.guess_bool(p, G, S, g, fg_g, inf,
                Groups.groups_smaller(S, fg_g), best),
              SolveFast.dummy_zero(), False{},
              SolveFast.is_floor_hit(nodup, n,
                Eval.Eval.guess_bool(p, G, S, g, fg_g, inf,
                  Groups.groups_smaller(S, fg_g), best)))
         : SolveRef.Best} =
    FE.schedule_fguess_step(p, gs, G, S, nodup, inf, g, fg, best,
      Groups.groups_smaller(S, fg_g), {==}, lok, ele, hz, h1, ag, ng, hbest,
      hd, ecif_fg)
  +e2 : {SolveFast.step(1n+p, gs, Nil{}, G, S, n, nodup, inf, Nil{}, Nil{}, 0n,
           Eval.Eval.guess_bool(p, G, S, g, fg_g, inf,
             Groups.groups_smaller(S, fg_g), best),
           SolveFast.dummy_zero(), False{},
           SolveFast.is_floor_hit(nodup, n,
             Eval.Eval.guess_bool(p, G, S, g, fg_g, inf,
               Groups.groups_smaller(S, fg_g), best)))
         == SolveFast.step(1n+p, gs, Nil{}, G, S, n, nodup, inf, Nil{}, Nil{},
              0n, Eval.Eval.guess(p, G, S, g, inf, best),
              SolveFast.dummy_zero(), False{},
              SolveFast.is_floor_hit(nodup, n,
                Eval.Eval.guess(p, G, S, g, inf, best)))
         : SolveRef.Best} =
    Equal.cong(+List<Groups.Group>, SolveRef.Best,
      grp => SolveFast.step(1n+p, gs, Nil{}, G, S, n, nodup, inf, Nil{}, Nil{},
               0n,
               Eval.Eval.guess_bool(p, G, S, g, grp, inf,
                 Groups.groups_smaller(S, grp), best),
               SolveFast.dummy_zero(), False{},
               SolveFast.is_floor_hit(nodup, n,
                 Eval.Eval.guess_bool(p, G, S, g, grp, inf,
                   Groups.groups_smaller(S, grp), best))),
      fg_g, groups, egrp)
  Equal.trans(SolveRef.Best,
    SolveFast.step(1n+p, gs,
      SolveFast.schedule_fguess(nodup, g, fg, n, best,
        SolveFast.fgroups_smaller(n, fg)),
      G, S, n, nodup, inf, Nil{}, Nil{}, 0n, best,
      SolveFast.dummy_zero(), False{}, False{}),
    SolveFast.step(1n+p, gs, Nil{}, G, S, n, nodup, inf, Nil{}, Nil{}, 0n,
      Eval.Eval.guess_bool(p, G, S, g, fg_g, inf,
        Groups.groups_smaller(S, fg_g), best),
      SolveFast.dummy_zero(), False{},
      SolveFast.is_floor_hit(nodup, n,
        Eval.Eval.guess_bool(p, G, S, g, fg_g, inf,
          Groups.groups_smaller(S, fg_g), best))),
    SolveFast.step(1n+p, gs, Nil{}, G, S, n, nodup, inf, Nil{}, Nil{}, 0n,
      Eval.Eval.guess(p, G, S, g, inf, best),
      SolveFast.dummy_zero(), False{},
      SolveFast.is_floor_hit(nodup, n,
        Eval.Eval.guess(p, G, S, g, inf, best))),
    Equal.trans(SolveRef.Best,
      SolveFast.step(1n+p, gs,
        SolveFast.schedule_fguess(nodup, g, fg, n, best,
          SolveFast.fgroups_smaller(n, fg)),
        G, S, n, nodup, inf, Nil{}, Nil{}, 0n, best,
        SolveFast.dummy_zero(), False{}, False{}),
      SolveFast.step(1n+p, gs,
        SolveFast.schedule_fguess(nodup, g, fg, n, best,
          Groups.groups_smaller(S, fg_g)),
        G, S, n, nodup, inf, Nil{}, Nil{}, 0n, best,
        SolveFast.dummy_zero(), False{}, False{}),
      SolveFast.step(1n+p, gs, Nil{}, G, S, n, nodup, inf, Nil{}, Nil{}, 0n,
        Eval.Eval.guess_bool(p, G, S, g, fg_g, inf,
          Groups.groups_smaller(S, fg_g), best),
        SolveFast.dummy_zero(), False{},
        SolveFast.is_floor_hit(nodup, n,
          Eval.Eval.guess_bool(p, G, S, g, fg_g, inf,
            Groups.groups_smaller(S, fg_g), best))),
      e0, e1),
    e2)

def FE.guess_body_step(+p: Nat, +gs: +List<+List<Nat>>,
    +G: +List<+List<Nat>>, +S: +List<+List<Nat>>, +nodup: Bool, +inf: Nat,
    +g: +List<Nat>, +best: SolveRef.Best,
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +ai: {FO.FO.all_in_ref(S, G) == True{} : Bool},
    +nd: {FN.FN.nodup_ok(nodup, S) == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    +hd: {SolveFast.is_floor_hit(nodup, Groups.len_words(S), best)
          == False{} : Bool},
    ecif: FE.EClassIf(
            Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
            p, inf, G, nodup, Groups.groups_build(g, S, Nil{}))) ->
  {SolveFast.step(1n+p, gs,
     SolveFast.guess_body(nodup, g, S, Groups.len_words(S), best),
     G, S, Groups.len_words(S), nodup, inf, Nil{}, Nil{}, 0n, best,
     SolveFast.dummy_zero(), False{}, False{})
   == SolveFast.step(1n+p, gs, Nil{}, G, S, Groups.len_words(S), nodup, inf,
        Nil{}, Nil{}, 0n,
        Eval.Eval.guess(p, G, S, g, inf, best),
        SolveFast.dummy_zero(), False{},
        SolveFast.is_floor_hit(nodup, Groups.len_words(S),
          Eval.Eval.guess(p, G, S, g, inf, best)))
   : SolveRef.Best}:
  match S:
    case Nil{}:
      FE.guess_body_fgroup_step(p, gs, G, Nil{}, nodup, inf, g, best, ele, hz,
        h1, ai, nd, hbest, hd, ecif)
    case Con{+w, +t}:
      match t:
        case Nil{}:
          Equal.trans(SolveRef.Best,
            SolveFast.step(1n+p, gs,
              SolveFast.schedule_one_guess(g, best,
                SolveFast.word_eq_fast(g, w)),
              G, w <> Nil{}, 1n, nodup, inf, Nil{}, Nil{}, 0n, best,
              SolveFast.dummy_zero(), False{}, False{}),
            SolveFast.step(1n+p, gs,
              SolveFast.schedule_one_guess(g, best, Feedback.word_eq(g, w)),
              G, w <> Nil{}, 1n, nodup, inf, Nil{}, Nil{}, 0n, best,
              SolveFast.dummy_zero(), False{}, False{}),
            SolveFast.step(1n+p, gs, Nil{}, G, w <> Nil{}, 1n, nodup, inf,
              Nil{}, Nil{}, 0n,
              Eval.Eval.guess(p, G, w <> Nil{}, g, inf, best),
              SolveFast.dummy_zero(), False{},
              SolveFast.is_floor_hit(nodup, 1n,
                Eval.Eval.guess(p, G, w <> Nil{}, g, inf, best))),
            Equal.cong(Bool, SolveRef.Best,
              b => SolveFast.step(1n+p, gs,
                     SolveFast.schedule_one_guess(g, best, b),
                     G, w <> Nil{}, 1n, nodup, inf, Nil{}, Nil{}, 0n, best,
                     SolveFast.dummy_zero(), False{}, False{}),
              SolveFast.word_eq_fast(g, w), Feedback.word_eq(g, w),
              FG.FG.word_eq_fast_eq(g, w)),
            FE.schedule_one_step(p, gs, G, w, nodup, inf, g, best,
              Feedback.word_eq(g, w), {==}, hz, hbest, hd))
        case Con{+w2, +t2}:
          FE.guess_body_fgroup_step(p, gs, G, w <> (w2 <> t2), nodup, inf, g,
            best, ele, hz, h1, ai, nd, hbest, hd, ecif)

# Step `guess_items` in duplicate-free mode (checking `best_cost <= 2*n` and
# `member_word_fast(g, S)`) and general mode (checking `pre_lb`).
def FE.guess_items_mem_step(+p: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +inf: Nat, +g: +List<Nat>, +t: +List<+List<Nat>>,
    +best: SolveRef.Best, in_s: Bool,
    +ein: {in_s == SolveFast.member_word_fast(g, S) : Bool},
    +ele2n: {SolveFast.skippable(best,
               Nat.add(Groups.len_words(S), Groups.len_words(S)))
             == True{} : Bool},
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +ai: {FO.FO.all_in_ref(S, G) == True{} : Bool},
    +nd: {FN.FN.no_dup_ref(S) == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    +hd: {SolveFast.is_floor_hit(True{}, Groups.len_words(S), best)
          == False{} : Bool},
    ecif: FE.EClassIf(
            Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
            p, inf, G, True{}, Groups.groups_build(g, S, Nil{}))) ->
  {SolveFast.step(1n+p, t,
     SolveFast.guess_items_mem(g, S, Groups.len_words(S), best, in_s),
     G, S, Groups.len_words(S), True{}, inf, Nil{}, Nil{}, 0n, best,
     SolveFast.dummy_zero(), False{}, False{})
   == SolveFast.step(1n+p, t, Nil{}, G, S, Groups.len_words(S), True{}, inf,
        Nil{}, Nil{}, 0n,
        Eval.Eval.guess(p, G, S, g, inf, best),
        SolveFast.dummy_zero(), False{},
        SolveFast.is_floor_hit(True{}, Groups.len_words(S),
          Eval.Eval.guess(p, G, S, g, inf, best)))
   : SolveRef.Best}:
  match in_s:
    case True{}:
      FE.guess_body_step(p, t, G, S, True{}, inf, g, best, ele, hz, h1, ai, nd,
        hbest, hd, ecif)
    case False{}:
      +n : Nat = Groups.len_words(S)
      +nm : {Tree.member_word(g, S) == False{} : Bool} =
        Equal.trans(Bool, Tree.member_word(g, S),
          SolveFast.member_word_fast(g, S), False{},
          Equal.sym(Bool, SolveFast.member_word_fast(g, S),
            Tree.member_word(g, S), FO.FO.member_word_fast_eq(g, S)),
          Equal.sym(Bool, False{}, SolveFast.member_word_fast(g, S), ein))
      +le2n : {Nat.is_le(Eval.Eval.cost_of(best), Nat.add(n, n))
               == True{} : Bool} =
        FLB.FS.skippable_to_le(best, Nat.add(n, n), ele2n)
      +le : {Nat.is_le(Eval.Eval.cost_of(best), SolveFast.pre_lb(n, g, S))
             == True{} : Bool} =
        NatProof.Nat.is_le_eq_r(Eval.Eval.cost_of(best), Nat.add(n, n),
          SolveFast.pre_lb(n, g, S),
          Equal.sym(Nat, SolveFast.pre_lb(n, g, S), Nat.add(n, n),
            FN.FN.pre_lb_of_not_member(g, S, nm)),
          le2n)
      +geq : {Eval.Eval.guess(p, G, S, g, inf, best) == best : SolveRef.Best} =
        FLB.FS.pre_guess_skip_eq(p, inf, G, S, g, best, ele, hz, hbest, le)
      FE.keep_best_step(p, t, G, S, True{}, inf, best,
        Eval.Eval.guess(p, G, S, g, inf, best), hd, geq)

def FE.guess_items_nodup_step(+p: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +inf: Nat, +g: +List<Nat>, +t: +List<+List<Nat>>,
    +best: SolveRef.Best, le_2n: Bool,
    +e2n: {le_2n == SolveFast.skippable(best,
             Nat.add(Groups.len_words(S), Groups.len_words(S))) : Bool},
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +ai: {FO.FO.all_in_ref(S, G) == True{} : Bool},
    +nd: {FN.FN.no_dup_ref(S) == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    +hd: {SolveFast.is_floor_hit(True{}, Groups.len_words(S), best)
          == False{} : Bool},
    ecif: FE.EClassIf(
            Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
            p, inf, G, True{}, Groups.groups_build(g, S, Nil{}))) ->
  {SolveFast.step(1n+p, t,
     SolveFast.guess_items_nodup(g, S, Groups.len_words(S), best, le_2n),
     G, S, Groups.len_words(S), True{}, inf, Nil{}, Nil{}, 0n, best,
     SolveFast.dummy_zero(), False{}, False{})
   == SolveFast.step(1n+p, t, Nil{}, G, S, Groups.len_words(S), True{}, inf,
        Nil{}, Nil{}, 0n,
        Eval.Eval.guess(p, G, S, g, inf, best),
        SolveFast.dummy_zero(), False{},
        SolveFast.is_floor_hit(True{}, Groups.len_words(S),
          Eval.Eval.guess(p, G, S, g, inf, best)))
   : SolveRef.Best}:
  match le_2n:
    case False{}:
      FE.guess_body_step(p, t, G, S, True{}, inf, g, best, ele, hz, h1, ai, nd,
        hbest, hd, ecif)
    case True{}:
      +n : Nat = Groups.len_words(S)
      FE.guess_items_mem_step(p, G, S, inf, g, t, best,
        SolveFast.member_word_fast(g, S), {==},
        Equal.sym(Bool, True{}, SolveFast.skippable(best, Nat.add(n, n)), e2n),
        ele, hz, h1, ai, nd, hbest, hd, ecif)

def FE.guess_items_dup_step(+p: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +inf: Nat, +g: +List<Nat>, +t: +List<+List<Nat>>,
    +best: SolveRef.Best, pre_skip: Bool,
    +ep: {pre_skip == SolveFast.skippable(best,
            SolveFast.pre_lb(Groups.len_words(S), g, S)) : Bool},
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +ai: {FO.FO.all_in_ref(S, G) == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    ecif: FE.EClassIf(
            Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
            p, inf, G, False{}, Groups.groups_build(g, S, Nil{}))) ->
  {SolveFast.step(1n+p, t,
     SolveFast.guess_items_go(False{}, g, S, Groups.len_words(S), best,
       pre_skip),
     G, S, Groups.len_words(S), False{}, inf, Nil{}, Nil{}, 0n, best,
     SolveFast.dummy_zero(), False{}, False{})
   == SolveFast.step(1n+p, t, Nil{}, G, S, Groups.len_words(S), False{}, inf,
        Nil{}, Nil{}, 0n,
        Eval.Eval.guess(p, G, S, g, inf, best),
        SolveFast.dummy_zero(), False{}, False{})
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
      FE.keep_best_step(p, t, G, S, False{}, inf, best,
        Eval.Eval.guess(p, G, S, g, inf, best), {==}, geq)
    case False{}:
      FE.guess_body_step(p, t, G, S, False{}, inf, g, best, ele, hz, h1, ai,
        {==}, hbest, {==}, ecif)

def FE.guess_pop_step(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +nodup: Bool, +inf: Nat, +g: +List<Nat>, +t: +List<+List<Nat>>,
    +best: SolveRef.Best,
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +ai: {FO.FO.all_in_ref(S, G) == True{} : Bool},
    +nd: {FN.FN.nodup_ok(nodup, S) == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    +hd: {SolveFast.is_floor_hit(nodup, Groups.len_words(S), best)
          == False{} : Bool},
    ecif: FE.EClassIf(
            Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
            p, inf, G, nodup, Groups.groups_build(g, S, Nil{}))) ->
  {SolveFast.step(1n+p, t,
     SolveFast.guess_items(nodup, g, S, Groups.len_words(S), best),
     G, S, Groups.len_words(S), nodup, inf, Nil{}, Nil{}, 0n, best,
     SolveFast.dummy_zero(), False{}, False{})
   == SolveFast.step(1n+p, t, Nil{}, G, S, Groups.len_words(S), nodup, inf,
        Nil{}, Nil{}, 0n,
        Eval.Eval.guess(p, G, S, g, inf, best),
        SolveFast.dummy_zero(), False{},
        SolveFast.is_floor_hit(nodup, Groups.len_words(S),
          Eval.Eval.guess(p, G, S, g, inf, best)))
   : SolveRef.Best}:
  match nodup:
    case True{}:
      +n : Nat = Groups.len_words(S)
      FE.guess_items_nodup_step(p, G, S, inf, g, t, best,
        SolveFast.skippable(best, Nat.add(n, n)), {==}, ele, hz, h1, ai, nd,
        hbest, hd, ecif)
    case False{}:
      FE.guess_items_dup_step(p, G, S, inf, g, t, best,
        SolveFast.skippable(best, SolveFast.pre_lb(Groups.len_words(S), g, S)),
        {==}, ele, hz, h1, ai, hbest, ecif)

# When `is_floor_hit(nodup, |S|, best) == True{}`, `nodup` must be `True{}` and
# `Eval.guesses` leaves `best` unchanged on all remaining guesses.
def FE.floor_hit_eval(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +nodup: Bool, +inf: Nat, +gs: +List<+List<Nat>>, +best: SolveRef.Best,
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +nd: {FN.FN.nodup_ok(nodup, S) == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    +ht: {SolveFast.is_floor_hit(nodup, Groups.len_words(S), best)
          == True{} : Bool}) ->
  {Eval.Eval.guesses(1n+p, G, S, inf, gs, best) == best : SolveRef.Best}:
  match nodup:
    case False{}:
      Empty.absurd(
        {Eval.Eval.guesses(1n+p, G, S, inf, gs, best) == best : SolveRef.Best},
        Logic.Proof.false_ne_true(ht))
    case True{}:
      +n : Nat = Groups.len_words(S)
      +hfl : {Nat.is_le(Eval.Eval.cost_of(best),
                Nat.sub(Nat.add(n, n), 1n)) == True{} : Bool} =
        FLB.FS.skippable_to_le(best, Nat.sub(Nat.add(n, n), 1n), ht)
      FN.FN.guesses_floor_skip(p, inf, G, S, gs, best, nd, ele, hz, hbest, hfl)

# Dispatch on `done = is_floor_hit(nodup, |S|, best)` at a non-empty guess list.
def FE.guesses_step_cons(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +nodup: Bool, +inf: Nat, +g: +List<Nat>, +t: +List<+List<Nat>>,
    +best: SolveRef.Best, dn: Bool,
    +edn: {dn == SolveFast.is_floor_hit(nodup, Groups.len_words(S), best)
           : Bool},
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +ai: {FO.FO.all_in_ref(S, G) == True{} : Bool},
    +nd: {FN.FN.nodup_ok(nodup, S) == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    ecif: FE.EClassIf(
            Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
            p, inf, G, nodup, Groups.groups_build(g, S, Nil{})),
    rec: {SolveFast.step(1n+p, t, Nil{}, G, S, Groups.len_words(S), nodup, inf,
            Nil{}, Nil{}, 0n, Eval.Eval.guess(p, G, S, g, inf, best),
            SolveFast.dummy_zero(), False{},
            SolveFast.is_floor_hit(nodup, Groups.len_words(S),
              Eval.Eval.guess(p, G, S, g, inf, best)))
          == Eval.Eval.guesses(1n+p, G, S, inf, t,
               Eval.Eval.guess(p, G, S, g, inf, best))
          : SolveRef.Best}) ->
  {SolveFast.step(1n+p, g <> t, Nil{}, G, S, Groups.len_words(S), nodup, inf,
     Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{}, dn)
   == Eval.Eval.guesses(1n+p, G, S, inf, g <> t, best) : SolveRef.Best}:
  match dn:
    case True{}:
      +ht : {SolveFast.is_floor_hit(nodup, Groups.len_words(S), best)
             == True{} : Bool} =
        Equal.sym(Bool, True{},
          SolveFast.is_floor_hit(nodup, Groups.len_words(S), best), edn)
      Equal.trans(SolveRef.Best,
        SolveFast.step(1n+p, g <> t, Nil{}, G, S, Groups.len_words(S), nodup,
          inf, Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{}, True{}),
        best,
        Eval.Eval.guesses(1n+p, G, S, inf, g <> t, best),
        FS.FS.done_exit(p, g <> t, G, S, Groups.len_words(S), nodup, inf, best),
        Equal.sym(SolveRef.Best,
          Eval.Eval.guesses(1n+p, G, S, inf, g <> t, best), best,
          FE.floor_hit_eval(p, G, S, nodup, inf, g <> t, best, ele, hz, nd,
            hbest, ht)))
    case False{}:
      +n : Nat = Groups.len_words(S)
      +hd : {SolveFast.is_floor_hit(nodup, n, best) == False{} : Bool} =
        Equal.sym(Bool, False{}, SolveFast.is_floor_hit(nodup, n, best), edn)
      +next_best : SolveRef.Best = Eval.Eval.guess(p, G, S, g, inf, best)
      +e1 : {SolveFast.step(1n+p, t,
               SolveFast.guess_items(nodup, g, S, n, best),
               G, S, n, nodup, inf, Nil{}, Nil{}, 0n, best,
               SolveFast.dummy_zero(), False{}, False{})
             == SolveFast.step(1n+p, t, Nil{}, G, S, n, nodup, inf,
                  Nil{}, Nil{}, 0n, next_best,
                  SolveFast.dummy_zero(), False{},
                  SolveFast.is_floor_hit(nodup, n, next_best))
             : SolveRef.Best} =
        FE.guess_pop_step(p, G, S, nodup, inf, g, t, best, ele, hz, h1, ai,
          nd, hbest, hd, ecif)
      Equal.trans(SolveRef.Best,
        SolveFast.step(1n+p, g <> t, Nil{}, G, S, n, nodup, inf,
          Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{}, False{}),
        SolveFast.step(1n+p, t, Nil{}, G, S, n, nodup, inf,
          Nil{}, Nil{}, 0n, next_best, SolveFast.dummy_zero(), False{},
          SolveFast.is_floor_hit(nodup, n, next_best)),
        Eval.Eval.guesses(1n+p, G, S, inf, g <> t, best),
        Equal.trans(SolveRef.Best,
          SolveFast.step(1n+p, g <> t, Nil{}, G, S, n, nodup, inf,
            Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{},
            False{}),
          SolveFast.step(1n+p, t,
            SolveFast.guess_items(nodup, g, S, n, best),
            G, S, n, nodup, inf, Nil{}, Nil{}, 0n, best,
            SolveFast.dummy_zero(), False{}, False{}),
          SolveFast.step(1n+p, t, Nil{}, G, S, n, nodup, inf,
            Nil{}, Nil{}, 0n, next_best, SolveFast.dummy_zero(), False{},
            SolveFast.is_floor_hit(nodup, n, next_best)),
          FS.FS.pop_guess_succ(p, g, t, G, S, n, nodup, inf, best),
          e1),
        rec)

# Folding the pruned schedule over a guess list at positive fuel equals
# `Eval.guesses`.
def FE.guesses_step(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +nodup: Bool, +inf: Nat, +gs: +List<+List<Nat>>, +best: SolveRef.Best,
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +ai: {FO.FO.all_in_ref(S, G) == True{} : Bool},
    +nd: {FN.FN.nodup_ok(nodup, S) == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    f: FE.EByGs(p, inf, G, S, nodup, gs)) ->
  {SolveFast.step(1n+p, gs, Nil{}, G, S, Groups.len_words(S), nodup, inf,
     Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{},
     SolveFast.is_floor_hit(nodup, Groups.len_words(S), best))
   == Eval.Eval.guesses(1n+p, G, S, inf, gs, best) : SolveRef.Best}:
  match gs:
    case Nil{}:
      {==}
    case Con{+g, +t}:
      (ecif, ft) = f
      FE.guesses_step_cons(p, G, S, nodup, inf, g, t, best,
        SolveFast.is_floor_hit(nodup, Groups.len_words(S), best), {==},
        ele, hz, h1, ai, nd, hbest, ecif,
        FE.guesses_step(p, G, S, nodup, inf, t,
          Eval.Eval.guess(p, G, S, g, inf, best), ele, hz, h1, ai, nd,
          NatProof.Nat.is_le_trans(
            Eval.Eval.cost_of(Eval.Eval.guess(p, G, S, g, inf, best)),
            Eval.Eval.cost_of(best), inf,
            Fold.OQ.guess_cost_le_acc(p, G, S, g, inf, best), hbest),
          ft))

# One job at positive fuel `1+p`: `FS.run_from` equals `Eval.guesses` for any
# starting accumulator `best0` with `cost_of(best0) <= inf`.
def FE.ejob_succ(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +nodup: Bool,
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +ai: {FO.FO.all_in_ref(S, G) == True{} : Bool},
    +nd: {FN.FN.nodup_ok(nodup, S) == True{} : Bool},
    f: FE.EByGs(p, inf, G, S, nodup, G)) ->
  FE.EJob(1n+p, inf, G, S, nodup):
  best0 => hb0 =>
    FE.guesses_step(p, G, S, nodup, inf, G, best0, ele, hz, h1, ai, nd, hb0, f)

def FE.zero_guess_step(+G: +List<+List<Nat>>, +nodup: Bool, +inf: Nat,
    +g: +List<Nat>, +rest: +List<+List<Nat>>, +best: SolveRef.Best,
    +dn: Bool) ->
  {SolveFast.step(0n, g <> rest, Nil{}, G, Nil{}, 0n, nodup, inf,
     Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{}, dn)
   == SolveFast.step(0n, rest, Nil{}, G, Nil{}, 0n, nodup, inf,
        Nil{}, Nil{}, 0n,
        SolveRef.finish_guess(inf, g, Nil{}, 0n, 0n, best),
        SolveFast.dummy_zero(), False{}, False{})
   : SolveRef.Best}:
  match rest:
    case Nil{}:
      {==}
    case Con{gh, gt}:
      {==}

# Zero fuel on the empty candidate list: `SolveFast` folds the guesses with
# cost zero, matching `Eval.guesses(0n, ...)`.
def FE.guesses_zero(+G: +List<+List<Nat>>, +nodup: Bool, +inf: Nat,
    +gs: +List<+List<Nat>>, +best: SolveRef.Best, +dn: Bool) ->
  {SolveFast.step(0n, gs, Nil{}, G, Nil{}, 0n, nodup, inf,
     Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{}, dn)
   == Eval.Eval.guesses(0n, G, Nil{}, inf, gs, best) : SolveRef.Best}:
  match gs:
    case Nil{}:
      {==}
    case Con{+g, +rest}:
      +next_best : SolveRef.Best =
        SolveRef.finish_guess(inf, g, Nil{}, 0n, 0n, best)
      Equal.trans(SolveRef.Best,
        SolveFast.step(0n, g <> rest, Nil{}, G, Nil{}, 0n, nodup, inf,
          Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{}, dn),
        SolveFast.step(0n, rest, Nil{}, G, Nil{}, 0n, nodup, inf,
          Nil{}, Nil{}, 0n, next_best, SolveFast.dummy_zero(), False{},
          False{}),
        Eval.Eval.guesses(0n, G, Nil{}, inf, g <> rest, best),
        FE.zero_guess_step(G, nodup, inf, g, rest, best, dn),
        FE.guesses_zero(G, nodup, inf, rest, next_best, False{}))

def FE.ejob_nil_at(+inf: Nat, +G: +List<+List<Nat>>, +nodup: Bool,
    +best0: SolveRef.Best) ->
  {FS.FS.run_from(0n, inf, G, Nil{}, nodup, best0)
   == Eval.Eval.guesses(0n, G, Nil{}, inf, G, best0) : SolveRef.Best}:
  FE.guesses_zero(G, nodup, inf, G, best0,
    SolveFast.is_floor_hit(nodup, 0n, best0))

def FE.ejob_nil(+inf: Nat, +G: +List<+List<Nat>>, +nodup: Bool) ->
  FE.EJob(0n, inf, G, Nil{}, nodup):
  best0 => hb0 => FE.ejob_nil_at(inf, G, nodup, best0)

def FE.ejob_transport(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S1: +List<+List<Nat>>, +S2: +List<+List<Nat>>, +nodup: Bool,
    e: {S1 == S2 : +List<+List<Nat>>},
    j: FE.EJob(fuel, inf, G, S1, nodup)) -> FE.EJob(fuel, inf, G, S2, nodup):
  %e : FE.EJob(fuel, inf, G, _, nodup)
  j

def FE.ejob_zero(+inf: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +nodup: Bool,
    le: {Nat.is_le(Groups.len_words(S), 0n) == True{} : Bool}) ->
  FE.EJob(0n, inf, G, S, nodup):
  +eS : {S == Nil{} : +List<+List<Nat>>} =
    MV.MV.nil_of_len_zero(S,
      NatProof.Nat.eq_zero_of_le_zero(Groups.len_words(S), le))
  FE.ejob_transport(0n, inf, G, Nil{}, S, nodup,
    Equal.sym(+List<+List<Nat>>, S, Nil{}, eS), FE.ejob_nil(inf, G, nodup))

def FE.eflat_zero(+inf: Nat, +G: +List<+List<Nat>>, +nodup: Bool,
    +jobs: +List<+List<+List<Nat>>>,
    bounds: MV.MV.Bounds(0n, jobs)) -> FE.EFlat(0n, inf, G, nodup, jobs):
  match jobs:
    case Nil{}:
      Unit{}
    case Con{S, t}:
      (ble, bt) = bounds
      Tuple{FE.ejob_zero(inf, G, S, nodup, ble),
            FE.eflat_zero(inf, G, nodup, t, bt)}

def FE.eflat_step(+inf: Nat, +p: Nat, +G: +List<+List<Nat>>, +nodup: Bool,
    +jobs: +List<+List<+List<Nat>>>,
    bounds: MV.MV.Bounds(1n+p, jobs),
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +aj: {FO.FO.all_in_jobs_b(jobs, G) == True{} : Bool},
    +nj: {FN.FN.nodup_ok_jobs(nodup, jobs) == True{} : Bool},
    f: FE.EFlat(p, inf, G, nodup, MV.MV.next_jobs(G, jobs))) ->
  FE.EFlat(1n+p, inf, G, nodup, jobs):
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
      +nd : {FN.FN.nodup_ok(nodup, S) == True{} : Bool} =
        Logic.Proof.and_true_l(FN.FN.nodup_ok(nodup, S),
          FN.FN.nodup_ok_jobs(nodup, t), nj)
      +nt : {FN.FN.nodup_ok_jobs(nodup, t) == True{} : Bool} =
        Logic.Proof.and_true_r(FN.FN.nodup_ok(nodup, S),
          FN.FN.nodup_ok_jobs(nodup, t), nj)
      MV.MV.use_pair(FE.EFlat(1n+p, inf, G, nodup, S <> t),
        FE.EFlat(p, inf, G, nodup, MV.MV.next_guess(G, S)),
        FE.EFlat(p, inf, G, nodup, MV.MV.next_jobs(G, t)),
        FE.eflat_append(p, inf, G, nodup, MV.MV.next_guess(G, S),
          MV.MV.next_jobs(G, t), f),
        fS => ft =>
          Tuple{FE.ejob_succ(p, inf, G, S, nodup, ble, hz, h1, ai, nd,
                  FE.eby_gs(p, inf, G, S, nodup, G, fS)),
                FE.eflat_step(inf, p, G, nodup, t, bt, hz, h1, at, nt, ft)})

# The fuel induction over all jobs at a level.
def FE.eflat(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>, +nodup: Bool,
    +jobs: +List<+List<+List<Nat>>>,
    bounds: MV.MV.Bounds(fuel, jobs),
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +aj: {FO.FO.all_in_jobs_b(jobs, G) == True{} : Bool},
    +nj: {FN.FN.nodup_ok_jobs(nodup, jobs) == True{} : Bool}) ->
  FE.EFlat(fuel, inf, G, nodup, jobs):
  match fuel:
    case 0n:
      FE.eflat_zero(inf, G, nodup, jobs, bounds)
    case 1n+p:
      MV.MV.use_pair(FE.EFlat(1n+p, inf, G, nodup, jobs),
        MV.MV.Bounds(1n+p, jobs), MV.MV.Bounds(1n+p, jobs),
        FE.bounds_copy(1n+p, jobs, bounds),
        b1 => b2 =>
          FE.eflat_step(inf, p, G, nodup, jobs, b1, hz, h1, aj, nj,
            FE.eflat(p, inf, G, nodup, MV.MV.next_jobs(G, jobs),
              MV.MV.next_bounds(p, G, jobs, b2), hz, h1,
              FO.FO.all_in_next_jobs(G, jobs, aj),
              FN.FN.nodup_ok_next_jobs(nodup, G, jobs, nj))))

# The top-level equality of the pruned and reference search states.
def FE.main_eq(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +nodup: Bool,
    +le: {Nat.is_le(Groups.len_words(S), fuel) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +ai: {FO.FO.all_in_ref(S, G) == True{} : Bool},
    +nd: {FN.FN.nodup_ok(nodup, S) == True{} : Bool}) ->
  {FS.FS.run_at(fuel, inf, G, S, nodup) == FS.FS.ref_run_at(fuel, inf, G, S)
   : SolveRef.Best}:
  +aj : {FO.FO.all_in_jobs_b(S <> Nil{}, G) == True{} : Bool} =
    FO.FO.bool_and_intro(FO.FO.all_in_ref(S, G), True{}, ai, {==})
  +nj : {FN.FN.nodup_ok_jobs(nodup, S <> Nil{}) == True{} : Bool} =
    FO.FO.bool_and_intro(FN.FN.nodup_ok(nodup, S), True{}, nd, {==})
  +ej : {FS.FS.run_at(fuel, inf, G, S, nodup)
         == Eval.Eval.guesses(fuel, G, S, inf, G, SolveFast.dummy_inf(inf))
         : SolveRef.Best} =
    MV.MV.use_pair(
      {FS.FS.run_at(fuel, inf, G, S, nodup)
       == Eval.Eval.guesses(fuel, G, S, inf, G, SolveFast.dummy_inf(inf))
       : SolveRef.Best},
      FE.EJob(fuel, inf, G, S, nodup), FE.EFlat(fuel, inf, G, nodup, Nil{}),
      FE.eflat(fuel, inf, G, nodup, S <> Nil{}, Tuple{le, Unit{}}, hz, h1,
        aj, nj),
      j => u => j(SolveFast.dummy_inf(inf), NatProof.Nat.is_le_refl(inf)))
  Equal.trans(SolveRef.Best,
    FS.FS.run_at(fuel, inf, G, S, nodup),
    Eval.Eval.guesses(fuel, G, S, inf, G, Eval.Eval.dummy_inf(inf)),
    FS.FS.ref_run_at(fuel, inf, G, S),
    ej,
    FC.FC.ref_run_guesses_eq(fuel, inf, G, S, le))

def FE.nodup_ok_of_fast(+cs: +List<+List<Nat>>, nd: Bool,
    +end: {nd == SolveFast.no_dup_fast(cs) : Bool}) ->
  {FN.FN.nodup_ok(nd, cs) == True{} : Bool}:
  match nd:
    case False{}:
      {==}
    case True{}:
      Equal.trans(Bool, FN.FN.no_dup_ref(cs),
        SolveFast.no_dup_fast(cs), True{},
        Equal.sym(Bool, SolveFast.no_dup_fast(cs), FN.FN.no_dup_ref(cs),
          FN.FN.no_dup_fast_eq(cs)),
        Equal.sym(Bool, True{}, SolveFast.no_dup_fast(cs), end))

def FE.solve_fast_valid_eq(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +ai: {FO.FO.all_in_ref(C, G) == True{} : Bool}) ->
  {SolveFast.solve_fast_valid(G, C) == SolveRef.solve(G, C)
   : Maybe<Tree.Tree>}:
  match C:
    case Nil{}:
      +ez : {FS.FS.run_at(0n, 1n, G, Nil{}, True{})
             == FS.FS.ref_run_at(0n, 1n, G, Nil{}) : SolveRef.Best} =
        Equal.trans(SolveRef.Best,
          FS.FS.run_at(0n, 1n, G, Nil{}, True{}),
          Eval.Eval.guesses(0n, G, Nil{}, 1n, G, Eval.Eval.dummy_inf(1n)),
          FS.FS.ref_run_at(0n, 1n, G, Nil{}),
          FE.guesses_zero(G, True{}, 1n, G, Eval.Eval.dummy_inf(1n),
            SolveFast.is_floor_hit(True{}, 0n, Eval.Eval.dummy_inf(1n))),
          FC.FC.ref_run_guesses_eq(0n, 1n, G, Nil{}, {==}))
      Equal.cong(SolveRef.Best, Maybe<Tree.Tree>,
        b => SolveRef.best_to_maybe(1n, b),
        FS.FS.run_at(0n, 1n, G, Nil{}, True{}),
        FS.FS.ref_run_at(0n, 1n, G, Nil{}),
        ez)
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
          +nd : Bool = SolveFast.no_dup_fast(cs)
          +hz : {Nat.is_lt(0n, inf) == True{} : Bool} =
            Ind.OQ.zero_lt_succ_add(Nat.mul(n, n))
          +h1 : {Nat.is_lt(1n, inf) == True{} : Bool} =
            FO.FO.one_lt_inf_ge2(w, w2, t2)
          +le : {Nat.is_le(Groups.len_words(cs), n) == True{} : Bool} =
            NatProof.Nat.is_le_refl(n)
          +hnd : {FN.FN.nodup_ok(nd, cs) == True{} : Bool} =
            FE.nodup_ok_of_fast(cs, nd, {==})
          Equal.cong(SolveRef.Best, Maybe<Tree.Tree>,
            b => SolveRef.best_to_maybe(inf, b),
            FS.FS.run_at(n, inf, G, cs, nd),
            FS.FS.ref_run_at(n, inf, G, cs),
            FE.main_eq(n, inf, G, cs, nd, le, hz, h1, ai, hnd))

def FE.solve_fast_checked_eq(ok: Bool, +G: +List<+List<Nat>>,
    +C: +List<+List<Nat>>,
    +eok: {ok == SolveFast.all_in_fast(C, G) : Bool}) ->
  {SolveFast.solve_fast_checked(ok, G, C) == SolveRef.solve(G, C)
   : Maybe<Tree.Tree>}:
  match ok:
    case False{}:
      +ef : {FO.FO.all_in_ref(C, G) == False{} : Bool} =
        Equal.trans(Bool, FO.FO.all_in_ref(C, G),
          SolveFast.all_in_fast(C, G), False{},
          Equal.sym(Bool, SolveFast.all_in_fast(C, G), FO.FO.all_in_ref(C, G),
            FO.FO.all_in_fast_eq(C, G)),
          Equal.sym(Bool, False{}, SolveFast.all_in_fast(C, G), eok))
      FO.FO.solve_ref_none_of_all_in_false(G, C, ef)
    case True{}:
      +ai : {FO.FO.all_in_ref(C, G) == True{} : Bool} =
        Equal.trans(Bool, FO.FO.all_in_ref(C, G),
          SolveFast.all_in_fast(C, G), True{},
          Equal.sym(Bool, SolveFast.all_in_fast(C, G), FO.FO.all_in_ref(C, G),
            FO.FO.all_in_fast_eq(C, G)),
          Equal.sym(Bool, True{}, SolveFast.all_in_fast(C, G), eok))
      FE.solve_fast_valid_eq(G, C, ai)

# The pruned solver returns the reference tree for every input.
def FE.solve_fast_eq(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>) ->
  {SolveFast.solve_fast(G, C) == SolveRef.solve(G, C) : Maybe<Tree.Tree>}:
  FE.solve_fast_checked_eq(SolveFast.all_in_fast(C, G), G, C, {==})
