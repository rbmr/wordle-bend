# Direct validity and optimality of the bound-pruned solver (`src/solve_fast.bend`).
#
# Rather than proving tree-for-tree equality with `SolveRef.solve`, this module
# proves directly by fuel induction over the staged guess queue that for every
# candidate subset `S` and cutoff accumulator `best0` with `cost_of(best0) <= inf`:
# 1. `FVal.FV.best_ok_b(cost_of(best0), G, S, res) == True{}` (either the result
#    did not beat `best0`, or its tree is valid for `(G, S)` with `Tree.cost <= cost`),
# 2. `cost_of(res) <= cost_of(best0)`, and
# 3. `cost_of(res) <= cost_of(FS.ref_run_at(fuel, inf, G, S))`.
#
# Combined with `OQStrongProof.F2.optimal_and_finite` (completeness and
# optimality of `SolveRef` against any valid tree `T2`), this proves both
# `Laws.solve_valid` and `Laws.solve_optimal` directly for `SolveFast.solve`.
import Base
import ../src/solve_fast.bend as SolveFast
import ../src/solve_ref.bend as SolveRef
import ../src/tree.bend as Tree
import ../src/groups.bend as Groups
import ../src/feedback.bend as Feedback
import ./logic.bend as Logic
import ./nat.bend as NatProof
import ./feedback.bend as FbProof
import ./eval.bend as Eval
import ./sat.bend as Sat
import ./groupsmeasure.bend as GM
import ./classbound_nat.bend as CBN
import ./optimalvalue.bend as OV
import ./optfold.bend as Fold
import ./optcost.bend as OC
import ./optstrong.bend as OQStrong
import ./mainvalid.bend as MV
import ./lb_size.bend as LBProof
import ./cover_groups.bend as CoverGroups
import ./array.bend as Arr
import ./fast_step.bend as FS
import ./fast_better.bend as FB
import ./fast_groups.bend as FG
import ./fast_lb.bend as FLB
import ./fast_cutoff.bend as FC
import ./fast_one.bend as FO
import ./fast_nodup.bend as FN
import ./fast_hist5.bend as FH
import ./fast_valid.bend as FVal

# ---------------------------------------------------------------------------
# Job-level specification and fuel-induction structures
# ---------------------------------------------------------------------------

def FOpt.job_res_b(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +limit: Nat, +res: SolveRef.Best) -> Bool:
  Bool.and(FVal.FV.best_ok_b(limit, G, S, res),
    Bool.and(Nat.is_le(Eval.Eval.cost_of(res), limit),
             Nat.is_le(Eval.Eval.cost_of(res),
               Eval.Eval.cost_of(FS.FS.ref_run_at(fuel, inf, G, S)))))

def FOpt.EJob(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +nodup: Bool) -> Type:
  @best0: SolveRef.Best ->
  {Nat.is_le(Eval.Eval.cost_of(best0), inf) == True{} : Bool} ->
  {FOpt.job_res_b(fuel, inf, G, S, Eval.Eval.cost_of(best0),
     FS.FS.run_child_from(fuel, inf, G, S, nodup, best0)) == True{} : Bool}

def FOpt.EFlat(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>, +nodup: Bool,
    jobs: +List<+List<+List<Nat>>>) -> Type:
  match jobs:
    case Nil{}:
      Unit
    case Con{S, t}:
      FOpt.EJob(fuel, inf, G, S, nodup) & FOpt.EFlat(fuel, inf, G, nodup, t)

def FOpt.EClass(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>, +nodup: Bool,
    +groups: +List<Groups.Group>) -> Type:
  match groups:
    case Nil{}:
      Unit
    case Con{gp, rest}:
      match gp:
        case Groups.Group{fb, ws}:
          FOpt.EJob(p, inf, G, ws, nodup) & FOpt.EClass(p, inf, G, nodup, rest)

def FOpt.EClassIf(b: Bool, +p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +nodup: Bool, +groups: +List<Groups.Group>) -> Type:
  match b:
    case True{}:
      FOpt.EClass(p, inf, G, nodup, groups)
    case False{}:
      Unit

def FOpt.EByGs(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +nodup: Bool, gs: +List<+List<Nat>>) -> Type:
  match gs:
    case Nil{}:
      Unit
    case Con{g, t}:
      FOpt.EClassIf(
        Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
        p, inf, G, nodup, Groups.groups_build(g, S, Nil{}))
      & FOpt.EByGs(p, inf, G, S, nodup, t)

# Next-level jobs include both stage-1 (`S`) and stage-2 (`G`) guess lists so
# each stage consumes its own linear `EByGs` witness without duplicating functions.
def FOpt.next_jobs(+G: +List<+List<Nat>>, +jobs: +List<+List<+List<Nat>>>) ->
  +List<+List<+List<Nat>>>:
  match jobs:
    case Nil{}:
      Nil{}
    case Con{S, t}:
      List.append(&2, +List<+List<Nat>>,
        List.append(&2, +List<+List<Nat>>,
          MV.MV.next_guess(S, S), MV.MV.next_guess(G, S)),
        FOpt.next_jobs(G, t))

def FOpt.bounds_copy(+fuel: Nat, +jobs: +List<+List<+List<Nat>>>,
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
        FOpt.bounds_copy(fuel, t, bt),
        b1 => b2 => Tuple{Tuple{ble, b1}, Tuple{ble, b2}})

def FOpt.next_bounds(+p: Nat, +G: +List<+List<Nat>>,
    +jobs: +List<+List<+List<Nat>>>,
    bounds: MV.MV.Bounds(1n+p, jobs)) ->
  MV.MV.Bounds(p, FOpt.next_jobs(G, jobs)):
  match jobs:
    case Nil{}:
      Unit{}
    case Con{+S, +t}:
      (+ble, bt) = bounds
      MV.MV.bounds_append_build(p,
        List.append(&2, +List<+List<Nat>>,
          MV.MV.next_guess(S, S), MV.MV.next_guess(G, S)),
        FOpt.next_jobs(G, t),
        MV.MV.bounds_append_build(p,
          MV.MV.next_guess(S, S), MV.MV.next_guess(G, S),
          MV.MV.any_bounds(p, S, S, ble),
          MV.MV.any_bounds(p, G, S, ble)),
        FOpt.next_bounds(p, G, t, bt))

def FOpt.all_in_next_jobs(+G: +List<+List<Nat>>,
    +jobs: +List<+List<+List<Nat>>>,
    +aj: {FO.FO.all_in_jobs_b(jobs, G) == True{} : Bool}) ->
  {FO.FO.all_in_jobs_b(FOpt.next_jobs(G, jobs), G) == True{} : Bool}:
  match jobs:
    case Nil{}:
      {==}
    case Con{+S, +t}:
      +ai : {FO.FO.all_in_ref(S, G) == True{} : Bool} =
        Logic.Proof.and_true_l(FO.FO.all_in_ref(S, G),
          FO.FO.all_in_jobs_b(t, G), aj)
      +at : {FO.FO.all_in_jobs_b(t, G) == True{} : Bool} =
        Logic.Proof.and_true_r(FO.FO.all_in_ref(S, G),
          FO.FO.all_in_jobs_b(t, G), aj)
      FO.FO.all_in_jobs_append(
        List.append(&2, +List<+List<Nat>>,
          MV.MV.next_guess(S, S), MV.MV.next_guess(G, S)),
        FOpt.next_jobs(G, t), G,
        FO.FO.all_in_jobs_append(MV.MV.next_guess(S, S), MV.MV.next_guess(G, S), G,
          FO.FO.all_in_next_guess(S, S, G, ai),
          FO.FO.all_in_next_guess(G, S, G, ai)),
        FOpt.all_in_next_jobs(G, t, at))

def FOpt.nodup_ok_next_jobs(+nodup: Bool, +G: +List<+List<Nat>>,
    +jobs: +List<+List<+List<Nat>>>,
    +nj: {FN.FN.nodup_ok_jobs(nodup, jobs) == True{} : Bool}) ->
  {FN.FN.nodup_ok_jobs(nodup, FOpt.next_jobs(G, jobs)) == True{} : Bool}:
  match jobs:
    case Nil{}:
      {==}
    case Con{+S, +t}:
      +nd : {FN.FN.nodup_ok(nodup, S) == True{} : Bool} =
        Logic.Proof.and_true_l(FN.FN.nodup_ok(nodup, S),
          FN.FN.nodup_ok_jobs(nodup, t), nj)
      +nt : {FN.FN.nodup_ok_jobs(nodup, t) == True{} : Bool} =
        Logic.Proof.and_true_r(FN.FN.nodup_ok(nodup, S),
          FN.FN.nodup_ok_jobs(nodup, t), nj)
      FN.FN.nodup_ok_jobs_append(nodup,
        List.append(&2, +List<+List<Nat>>,
          MV.MV.next_guess(S, S), MV.MV.next_guess(G, S)),
        FOpt.next_jobs(G, t),
        FN.FN.nodup_ok_jobs_append(nodup,
          MV.MV.next_guess(S, S), MV.MV.next_guess(G, S),
          FN.FN.nodup_ok_next_guess(nodup, S, S, nd),
          FN.FN.nodup_ok_next_guess(nodup, G, S, nd)),
        FOpt.nodup_ok_next_jobs(nodup, G, t, nt))

def FOpt.eflat_append(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +nodup: Bool, +xs: +List<+List<+List<Nat>>>, +ys: +List<+List<+List<Nat>>>,
    f: FOpt.EFlat(fuel, inf, G, nodup,
         List.append(&2, +List<+List<Nat>>, xs, ys))) ->
  FOpt.EFlat(fuel, inf, G, nodup, xs) & FOpt.EFlat(fuel, inf, G, nodup, ys):
  match xs:
    case Nil{}:
      Tuple{Unit{}, f}
    case Con{S, t}:
      (j, fr) = f
      MV.MV.use_pair(
        FOpt.EFlat(fuel, inf, G, nodup, S <> t)
        & FOpt.EFlat(fuel, inf, G, nodup, ys),
        FOpt.EFlat(fuel, inf, G, nodup, t),
        FOpt.EFlat(fuel, inf, G, nodup, ys),
        FOpt.eflat_append(fuel, inf, G, nodup, t, ys, fr),
        ft => fys => Tuple{Tuple{j, ft}, fys})

def FOpt.eclass_of_flat(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +nodup: Bool, +groups: +List<Groups.Group>,
    f: FOpt.EFlat(p, inf, G, nodup, MV.MV.next_groups(groups))) ->
  FOpt.EClass(p, inf, G, nodup, groups):
  match groups:
    case Nil{}:
      Unit{}
    case Con{gp, t}:
      match gp:
        case Groups.Group{fb, ws}:
          (j, fr) = f
          (j, FOpt.eclass_of_flat(p, inf, G, nodup, t, fr))

def FOpt.eclass_if(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>, +nodup: Bool,
    +groups: +List<Groups.Group>, b: Bool,
    f: FOpt.EFlat(p, inf, G, nodup, MV.MV.classes_b(b, groups))) ->
  FOpt.EClassIf(b, p, inf, G, nodup, groups):
  match b:
    case True{}:
      FOpt.eclass_of_flat(p, inf, G, nodup, groups, f)
    case False{}:
      Unit{}

def FOpt.eby_gs(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +nodup: Bool, +gs: +List<+List<Nat>>,
    f: FOpt.EFlat(p, inf, G, nodup, MV.MV.next_guess(gs, S))) ->
  FOpt.EByGs(p, inf, G, S, nodup, gs):
  match gs:
    case Nil{}:
      Unit{}
    case Con{g, t}:
      MV.MV.use_pair(FOpt.EByGs(p, inf, G, S, nodup, g <> t),
        FOpt.EFlat(p, inf, G, nodup, MV.MV.classes(g, S)),
        FOpt.EFlat(p, inf, G, nodup, MV.MV.next_guess(t, S)),
        FOpt.eflat_append(p, inf, G, nodup, MV.MV.classes(g, S),
          MV.MV.next_guess(t, S), f),
        fg => ft =>
          Tuple{FOpt.eclass_if(p, inf, G, nodup, Groups.groups_build(g, S, Nil{}),
                  Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
                  fg),
                FOpt.eby_gs(p, inf, G, S, nodup, t, ft)})

# ---------------------------------------------------------------------------
# Single-guess step specification (`FOpt.StepRes`) and combinators
# ---------------------------------------------------------------------------

def FOpt.skippable_false_of_lt(+best: SolveRef.Best, +x: Nat,
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

def FOpt.skippable_true_of_le(+best: SolveRef.Best, +x: Nat,
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

def FOpt.lt_of_skippable_false(+best: SolveRef.Best, +x: Nat,
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

def FOpt.StepRes(+p: Nat, +gs: SolveFast.GList, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +nodup: Bool, +floor: Nat, +inf: Nat,
    +g: +List<Nat>, +cs: +List<SolveFast.Item>, +kids: +List<Tree.Child>,
    +sum: Nat, +best: SolveRef.Best, -gres: SolveFast.GuessRes,
    +limit: Nat, +target: Nat) -> Type:
  &best2: SolveRef.Best ->
    {SolveFast.step(1n+p, gs, 0n, cs,
       SolveFast.glist_of(G, SolveFast.GEnd{}), S, Groups.len_words(S),
       nodup, floor, inf, g, kids, sum, best, SolveFast.dummy_zero(),
       False{}, False{}, gres)
     == SolveFast.step(1n+p, gs, 0n, Nil{},
          SolveFast.glist_of(G, SolveFast.GEnd{}), S, Groups.len_words(S),
          nodup, floor, inf, Nil{}, Nil{}, 0n, best2, SolveFast.dummy_zero(),
          False{}, SolveFast.is_floor_hit(nodup, floor, best2), gres)
     : SolveRef.Best}
    & {FVal.FV.best_ok_b(limit, G, S, best2) == True{} : Bool}
    & {Nat.is_le(Eval.Eval.cost_of(best2), Eval.Eval.cost_of(best))
       == True{} : Bool}
    & {Nat.is_le(Eval.Eval.cost_of(best2), target) == True{} : Bool}

def FOpt.step_res_pre(+p: Nat, +gs: SolveFast.GList, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +nodup: Bool, +floor: Nat, +inf: Nat,
    +g1: +List<Nat>, +cs1: +List<SolveFast.Item>, +k1: +List<Tree.Child>,
    +s1: Nat, +g2: +List<Nat>, +cs2: +List<SolveFast.Item>,
    +k2: +List<Tree.Child>, +s2: Nat, +best: SolveRef.Best,
    -gres: SolveFast.GuessRes, +limit: Nat, +t1: Nat, +t2: Nat,
    +estep: {SolveFast.step(1n+p, gs, 0n, cs1,
               SolveFast.glist_of(G, SolveFast.GEnd{}), S, Groups.len_words(S),
               nodup, floor, inf, g1, k1, s1, best, SolveFast.dummy_zero(),
               False{}, False{}, gres)
             == SolveFast.step(1n+p, gs, 0n, cs2,
                  SolveFast.glist_of(G, SolveFast.GEnd{}), S,
                  Groups.len_words(S), nodup, floor, inf, g2, k2, s2, best,
                  SolveFast.dummy_zero(), False{}, False{}, gres)
             : SolveRef.Best},
    +ht: {Nat.is_le(t1, t2) == True{} : Bool},
    r: FOpt.StepRes(p, gs, G, S, nodup, floor, inf, g2, cs2, k2, s2, best,
         gres, limit, t1)) ->
  FOpt.StepRes(p, gs, G, S, nodup, floor, inf, g1, cs1, k1, s1, best, gres,
    limit, t2):
  match r:
    case Tuple{+best2, p1}:
      match p1:
        case Tuple{+eq2, p2}:
          match p2:
            case Tuple{+hok2, p3}:
              match p3:
                case Tuple{+hleb, hlet}:
                  +n : Nat = Groups.len_words(S)
                  +gG : SolveFast.GList = SolveFast.glist_of(G, SolveFast.GEnd{})
                  Tuple{best2,
                    Tuple{
                      Equal.trans(SolveRef.Best,
                        SolveFast.step(1n+p, gs, 0n, cs1, gG, S, n, nodup,
                          floor, inf, g1, k1, s1, best, SolveFast.dummy_zero(),
                          False{}, False{}, gres),
                        SolveFast.step(1n+p, gs, 0n, cs2, gG, S, n, nodup,
                          floor, inf, g2, k2, s2, best, SolveFast.dummy_zero(),
                          False{}, False{}, gres),
                        SolveFast.step(1n+p, gs, 0n, Nil{}, gG, S, n, nodup,
                          floor, inf, Nil{}, Nil{}, 0n, best2,
                          SolveFast.dummy_zero(), False{},
                          SolveFast.is_floor_hit(nodup, floor, best2), gres),
                        estep, eq2),
                      Tuple{hok2,
                        Tuple{hleb,
                          NatProof.Nat.is_le_trans(Eval.Eval.cost_of(best2),
                            t1, t2, hlet, ht)}}}}

def FOpt.step_res_keep(+p: Nat, +gs: SolveFast.GList, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +nodup: Bool, +floor: Nat, +inf: Nat,
    +best: SolveRef.Best, -gres: SolveFast.GuessRes, +limit: Nat, +target: Nat,
    +hok: {FVal.FV.best_ok_b(limit, G, S, best) == True{} : Bool},
    +hd: {SolveFast.is_floor_hit(nodup, floor, best) == False{} : Bool},
    +ht: {Nat.is_le(Eval.Eval.cost_of(best), target) == True{} : Bool}) ->
  FOpt.StepRes(p, gs, G, S, nodup, floor, inf, Nil{}, Nil{}, Nil{}, 0n, best,
    gres, limit, target):
  +n : Nat = Groups.len_words(S)
  +gG : SolveFast.GList = SolveFast.glist_of(G, SolveFast.GEnd{})
  Tuple{best,
    Tuple{
      Equal.cong(Bool, SolveRef.Best,
        dn => SolveFast.step(1n+p, gs, 0n, Nil{}, gG, S, n, nodup, floor, inf,
                Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{}, dn,
                gres),
        False{}, SolveFast.is_floor_hit(nodup, floor, best),
        Equal.sym(Bool, SolveFast.is_floor_hit(nodup, floor, best),
          False{}, hd)),
      Tuple{hok, Tuple{NatProof.Nat.is_le_refl(Eval.Eval.cost_of(best)), ht}}}}

# ---------------------------------------------------------------------------
# Stepping a live block: `End`, `OneItem`, `TwoItem`, and `ClassItem` + `Add`
# ---------------------------------------------------------------------------

def FOpt.live_group_class_go(-gres: SolveFast.GuessRes, +p: Nat,
    +gs: SolveFast.GList, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +nodup: Bool, +floor: Nat, +inf: Nat, +g: +List<Nat>,
    +fb: +List<Feedback.Color>, +ws: +List<+List<Nat>>,
    +restg: +List<Groups.Group>, +done_rev: +List<Groups.Group>,
    +kids: +List<Tree.Child>, +sum: Nat, +sum_ref: Nat, +best: SolveRef.Best,
    +limit: Nat,
    bt: MV.MV.Bounds(p, MV.MV.next_groups(restg)),
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    +hok: {FVal.FV.best_ok_b(limit, G, S, best) == True{} : Bool},
    +hd: {SolveFast.is_floor_hit(nodup, floor, best) == False{} : Bool},
    +alive: {Nat.is_lt(
               Nat.add(sum,
                 SolveFast.lower_bound(Groups.len_words(S),
                   Groups.Group{fb, ws} <> restg)),
               Eval.Eval.cost_of(best)) == True{} : Bool},
    +hsum_le: {Nat.is_le(sum, sum_ref) == True{} : Bool},
    +hm: {FVal.FV.kids_match_b(G, done_rev, kids) == True{} : Bool},
    +hcs: {Nat.is_le(FVal.FV.kids_cost_sum(done_rev, kids), sum)
           == True{} : Bool},
    +hsearch: {FOpt.job_res_b(p, inf, G, ws,
                 FS.FS.child_cutoff(best, sum,
                   SolveFast.lower_bound(Groups.len_words(S), restg)),
                 FS.FS.run_child_from(p, inf, G, ws, nodup,
                   SolveFast.dummy_inf(FS.FS.child_cutoff(best, sum,
                     SolveFast.lower_bound(Groups.len_words(S), restg)))))
               == True{} : Bool},
    lt_cut: Bool,
    +elt: {lt_cut == Nat.is_lt(
             Eval.Eval.cost_of(
               FS.FS.run_child_from(p, inf, G, ws, nodup,
                 SolveFast.dummy_inf(FS.FS.child_cutoff(best, sum,
                   SolveFast.lower_bound(Groups.len_words(S), restg))))),
             FS.FS.child_cutoff(best, sum,
               SolveFast.lower_bound(Groups.len_words(S), restg))) : Bool},
    rec_live:
      {Nat.is_lt(
         Nat.add(
           SolveRef.sat_add(inf, sum,
             Eval.Eval.cost_of(
               FS.FS.run_child_from(p, inf, G, ws, nodup,
                 SolveFast.dummy_inf(FS.FS.child_cutoff(best, sum,
                   SolveFast.lower_bound(Groups.len_words(S), restg)))))),
           SolveFast.lower_bound(Groups.len_words(S), restg)),
         Eval.Eval.cost_of(best)) == True{} : Bool} ->
      {Nat.is_le(
         SolveRef.sat_add(inf, sum,
           Eval.Eval.cost_of(
             FS.FS.run_child_from(p, inf, G, ws, nodup,
               SolveFast.dummy_inf(FS.FS.child_cutoff(best, sum,
                 SolveFast.lower_bound(Groups.len_words(S), restg)))))),
         SolveRef.sat_add(inf, sum_ref,
           Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, ws))))
       == True{} : Bool} ->
      {FVal.FV.kids_match_b(G, Groups.Group{fb, ws} <> done_rev,
         Tree.Child{fb, Eval.Eval.tree_of(
           FS.FS.run_child_from(p, inf, G, ws, nodup,
             SolveFast.dummy_inf(FS.FS.child_cutoff(best, sum,
               SolveFast.lower_bound(Groups.len_words(S), restg)))))} <> kids)
       == True{} : Bool} ->
      {Nat.is_le(
         FVal.FV.kids_cost_sum(Groups.Group{fb, ws} <> done_rev,
           Tree.Child{fb, Eval.Eval.tree_of(
             FS.FS.run_child_from(p, inf, G, ws, nodup,
               SolveFast.dummy_inf(FS.FS.child_cutoff(best, sum,
                 SolveFast.lower_bound(Groups.len_words(S), restg)))))} <> kids),
         SolveRef.sat_add(inf, sum,
           Eval.Eval.cost_of(
             FS.FS.run_child_from(p, inf, G, ws, nodup,
               SolveFast.dummy_inf(FS.FS.child_cutoff(best, sum,
                 SolveFast.lower_bound(Groups.len_words(S), restg)))))))
       == True{} : Bool} ->
      FOpt.StepRes(p, gs, G, S, nodup, floor, inf, g,
        List.append(&2, SolveFast.Item,
          SolveFast.group_items(nodup, Groups.len_words(S), restg),
          SolveFast.End{} <> Nil{}),
        Tree.Child{fb, Eval.Eval.tree_of(
          FS.FS.run_child_from(p, inf, G, ws, nodup,
            SolveFast.dummy_inf(FS.FS.child_cutoff(best, sum,
              SolveFast.lower_bound(Groups.len_words(S), restg)))))} <> kids,
        SolveRef.sat_add(inf, sum,
          Eval.Eval.cost_of(
            FS.FS.run_child_from(p, inf, G, ws, nodup,
              SolveFast.dummy_inf(FS.FS.child_cutoff(best, sum,
                SolveFast.lower_bound(Groups.len_words(S), restg)))))),
        best, gres, limit,
        Fold.OQ.ks_cost(inf, S,
          Eval.Eval.items(p, G, S, g, restg, Nil{},
            SolveRef.sat_add(inf, sum_ref,
              Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, ws))), inf)))) ->
  FOpt.StepRes(p, gs, G, S, nodup, floor, inf, g,
    SolveFast.ClassItem{fb, ws, Groups.len_words(ws),
      SolveFast.lower_bound(Groups.len_words(S), restg)}
    <> (SolveFast.Add{fb, SolveFast.lower_bound(Groups.len_words(S), restg)}
        <> List.append(&2, SolveFast.Item,
             SolveFast.group_items(nodup, Groups.len_words(S), restg),
             SolveFast.End{} <> Nil{})),
    kids, sum, best, gres, limit,
    Fold.OQ.ks_cost(inf, S,
      Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg,
        Nil{}, sum_ref, inf))):
  match lt_cut:
    case True{}:
      +n : Nat = Groups.len_words(S)
      +gG : SolveFast.GList = SolveFast.glist_of(G, SolveFast.GEnd{})
      +tlb : Nat = SolveFast.lower_bound(n, restg)
      +B : Nat = Eval.Eval.cost_of(best)
      +cut : Nat = FS.FS.child_cutoff(best, sum, tlb)
      +search : SolveRef.Best =
        FS.FS.run_child_from(p, inf, G, ws, nodup, SolveFast.dummy_inf(cut))
      +ref_c : SolveRef.Best = FS.FS.ref_run_at(p, inf, G, ws)
      +inner : +List<SolveFast.Item> =
        List.append(&2, SolveFast.Item, SolveFast.group_items(nodup, n, restg),
          SolveFast.End{} <> Nil{})
      +cs1 : +List<SolveFast.Item> =
        SolveFast.ClassItem{fb, ws, Groups.len_words(ws), tlb}
        <> (SolveFast.Add{fb, tlb} <> inner)
      +cut_eq : {cut == Nat.sub(B, Nat.add(sum, tlb)) : Nat} =
        Equal.cong(Nat, Nat, x => Nat.sub(x, Nat.add(sum, tlb)),
          SolveFast.best_cost(best), B, FLB.FS.best_cost_eq(best))
      +st_le : {Nat.is_le(Nat.add(sum, tlb), B) == True{} : Bool} =
        FC.FC.sum_tail_le(sum, SolveFast.class_lb(ws), tlb, B, alive)
      +hok_c : {FVal.FV.best_ok_b(cut, G, ws, search) == True{} : Bool} =
        Logic.Proof.and_true_l(FVal.FV.best_ok_b(cut, G, ws, search),
          Bool.and(Nat.is_le(Eval.Eval.cost_of(search), cut),
            Nat.is_le(Eval.Eval.cost_of(search), Eval.Eval.cost_of(ref_c))),
          hsearch)
      +hr_c : {Bool.and(Nat.is_le(Eval.Eval.cost_of(search), cut),
                 Nat.is_le(Eval.Eval.cost_of(search), Eval.Eval.cost_of(ref_c)))
               == True{} : Bool} =
        Logic.Proof.and_true_r(FVal.FV.best_ok_b(cut, G, ws, search),
          Bool.and(Nat.is_le(Eval.Eval.cost_of(search), cut),
            Nat.is_le(Eval.Eval.cost_of(search), Eval.Eval.cost_of(ref_c))),
          hsearch)
      +hle_ref : {Nat.is_le(Eval.Eval.cost_of(search), Eval.Eval.cost_of(ref_c))
                  == True{} : Bool} =
        Logic.Proof.and_true_r(Nat.is_le(Eval.Eval.cost_of(search), cut),
          Nat.is_le(Eval.Eval.cost_of(search), Eval.Eval.cost_of(ref_c)), hr_c)
      +kf : +List<Tree.Child> = Tree.Child{fb, Eval.Eval.tree_of(search)} <> kids
      +sf : Nat = SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(search))
      +sr : Nat = SolveRef.sat_add(inf, sum_ref, Eval.Eval.cost_of(ref_c))
      +e_ca : {SolveFast.step(1n+p, gs, 0n, cs1, gG, S, n, nodup, floor, inf, g,
                 kids, sum, best, SolveFast.dummy_zero(), False{}, False{}, gres)
               == SolveFast.step(1n+p, gs, 0n, inner, gG, S, n, nodup, floor, inf,
                    g, kf, sf, best, SolveFast.dummy_zero(),
                    SolveFast.skippable(best, Nat.add(sf, tlb)), False{}, gres)
               : SolveRef.Best} =
        FS.FS.class_add_live(p, gs, G, S, n, nodup, floor, inf, g, fb, ws, tlb,
          inner, kids, sum, best, gres)
      +ek_step : {Fold.OQ.ks_cost(inf, S,
                    Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg,
                      Nil{}, sum_ref, inf))
                  == Fold.OQ.ks_cost(inf, S,
                       Eval.Eval.items(p, G, S, g, restg, Nil{}, sr, inf)) : Nat} =
        FVal.FV.ks_cost_items_step(p, inf, G, S, g, fb, ws, restg, sum_ref)
      +hlt_cut : {Nat.is_lt(Eval.Eval.cost_of(search), cut) == True{} : Bool} =
        Equal.sym(Bool, True{}, Nat.is_lt(Eval.Eval.cost_of(search), cut), elt)
      +hlt_sub : {Nat.is_lt(Eval.Eval.cost_of(search),
                    Nat.sub(B, Nat.add(sum, tlb))) == True{} : Bool} =
        Equal.trans(Bool,
          Nat.is_lt(Eval.Eval.cost_of(search), Nat.sub(B, Nat.add(sum, tlb))),
          Nat.is_lt(Eval.Eval.cost_of(search), cut), True{},
          Equal.cong(Nat, Bool, x => Nat.is_lt(Eval.Eval.cost_of(search), x),
            Nat.sub(B, Nat.add(sum, tlb)), cut,
            Equal.sym(Nat, cut, Nat.sub(B, Nat.add(sum, tlb)), cut_eq)),
          hlt_cut)
      +alive2 : {Nat.is_lt(Nat.add(sf, tlb), B) == True{} : Bool} =
        FC.FC.alive_cut_lt(inf, sum, Eval.Eval.cost_of(search), tlb, B, hbest,
          st_le, hlt_sub)
      +sk_f : {SolveFast.skippable(best, Nat.add(sf, tlb)) == False{} : Bool} =
        FOpt.skippable_false_of_lt(best, Nat.add(sf, tlb), alive2)
      +e_step : {SolveFast.step(1n+p, gs, 0n, cs1, gG, S, n, nodup, floor, inf,
                   g, kids, sum, best, SolveFast.dummy_zero(), False{},
                   False{}, gres)
                 == SolveFast.step(1n+p, gs, 0n, inner, gG, S, n, nodup, floor,
                      inf, g, kf, sf, best, SolveFast.dummy_zero(), False{},
                      False{}, gres) : SolveRef.Best} =
        Equal.trans(SolveRef.Best,
          SolveFast.step(1n+p, gs, 0n, cs1, gG, S, n, nodup, floor, inf, g,
            kids, sum, best, SolveFast.dummy_zero(), False{}, False{}, gres),
          SolveFast.step(1n+p, gs, 0n, inner, gG, S, n, nodup, floor, inf, g,
            kf, sf, best, SolveFast.dummy_zero(),
            SolveFast.skippable(best, Nat.add(sf, tlb)), False{}, gres),
          SolveFast.step(1n+p, gs, 0n, inner, gG, S, n, nodup, floor, inf, g,
            kf, sf, best, SolveFast.dummy_zero(), False{}, False{}, gres),
          e_ca,
          Equal.cong(Bool, SolveRef.Best,
            sk => SolveFast.step(1n+p, gs, 0n, inner, gG, S, n, nodup, floor,
                    inf, g, kf, sf, best, SolveFast.dummy_zero(), sk, False{},
                    gres),
            SolveFast.skippable(best, Nat.add(sf, tlb)), False{}, sk_f))
      +lt_add_b : {Nat.is_lt(
                     Nat.add(Nat.add(sum, Eval.Eval.cost_of(search)), tlb), B)
                   == True{} : Bool} =
        CBN.CB.lt_eq_l(B,
          Nat.add(Nat.add(sum, tlb), Eval.Eval.cost_of(search)),
          Nat.add(Nat.add(sum, Eval.Eval.cost_of(search)), tlb),
          Equal.sym(Nat,
            Nat.add(Nat.add(sum, Eval.Eval.cost_of(search)), tlb),
            Nat.add(Nat.add(sum, tlb), Eval.Eval.cost_of(search)),
            FC.FC.regroup_sum(sum, Eval.Eval.cost_of(search), tlb)),
          Equal.trans(Bool,
            Nat.is_lt(Nat.add(Nat.add(sum, tlb), Eval.Eval.cost_of(search)), B),
            Nat.is_lt(Nat.add(Nat.add(sum, tlb), Eval.Eval.cost_of(search)),
              Nat.add(Nat.add(sum, tlb), Nat.sub(B, Nat.add(sum, tlb)))),
            True{},
            Equal.cong(Nat, Bool,
              x => Nat.is_lt(
                     Nat.add(Nat.add(sum, tlb), Eval.Eval.cost_of(search)), x),
              B, Nat.add(Nat.add(sum, tlb), Nat.sub(B, Nat.add(sum, tlb))),
              Equal.sym(Nat,
                Nat.add(Nat.add(sum, tlb), Nat.sub(B, Nat.add(sum, tlb))), B,
                FC.FC.add_sub_of_le(B, Nat.add(sum, tlb), st_le))),
            FC.FC.lt_add_l(Nat.add(sum, tlb), Eval.Eval.cost_of(search),
              Nat.sub(B, Nat.add(sum, tlb)), hlt_sub)))
      +esf : {sf == Nat.add(sum, Eval.Eval.cost_of(search)) : Nat} =
        FC.FC.sat_add_lt_eq(inf, sum, Eval.Eval.cost_of(search), tlb, B, hbest,
          lt_add_b)
      +hlt_inf : {Nat.is_lt(Nat.add(sum, Eval.Eval.cost_of(search)), inf)
                  == True{} : Bool} =
        NatProof.Nat.is_lt_le_trans(
          Nat.add(sum, Eval.Eval.cost_of(search)), B, inf,
          NatProof.Nat.is_le_lt_trans(
            Nat.add(sum, Eval.Eval.cost_of(search)),
            Nat.add(Nat.add(sum, Eval.Eval.cost_of(search)), tlb), B,
            CBN.CB.is_le_add_self_r(
              Nat.add(sum, Eval.Eval.cost_of(search)), tlb),
            lt_add_b),
          hbest)
      +hsum_le2 : {Nat.is_le(sf, sr) == True{} : Bool} =
        Fold.OQ.le_cong_l(sf, Nat.add(sum, Eval.Eval.cost_of(search)), sr, esf,
          FVal.FV.le_sat_add_of_lt_inf(inf, sum, sum_ref,
            Eval.Eval.cost_of(search), Eval.Eval.cost_of(ref_c),
            hsum_le, hle_ref, hlt_inf))
      +hext : {Bool.and(FVal.FV.valid_b(Eval.Eval.tree_of(search), G, ws),
                 Nat.is_le(Tree.cost(Eval.Eval.tree_of(search), ws),
                   Eval.Eval.cost_of(search))) == True{} : Bool} =
        FVal.FV.best_ok_extract(cut, G, ws, search, hok_c, hlt_cut)
      +hv_c : {FVal.FV.valid_b(Eval.Eval.tree_of(search), G, ws)
               == True{} : Bool} =
        Logic.Proof.and_true_l(
          FVal.FV.valid_b(Eval.Eval.tree_of(search), G, ws),
          Nat.is_le(Tree.cost(Eval.Eval.tree_of(search), ws),
            Eval.Eval.cost_of(search)), hext)
      +hc_c : {Nat.is_le(Tree.cost(Eval.Eval.tree_of(search), ws),
                 Eval.Eval.cost_of(search)) == True{} : Bool} =
        Logic.Proof.and_true_r(
          FVal.FV.valid_b(Eval.Eval.tree_of(search), G, ws),
          Nat.is_le(Tree.cost(Eval.Eval.tree_of(search), ws),
            Eval.Eval.cost_of(search)), hext)
      +hm2 : {FVal.FV.kids_match_b(G, Groups.Group{fb, ws} <> done_rev, kf)
              == True{} : Bool} =
        FO.FO.bool_and_intro(Feedback.feedback_eq(fb, fb),
          Bool.and(FVal.FV.valid_b(Eval.Eval.tree_of(search), G, ws),
            FVal.FV.kids_match_b(G, done_rev, kids)),
          FbProof.FbPrf.feedback_eq_refl(fb),
          FO.FO.bool_and_intro(
            FVal.FV.valid_b(Eval.Eval.tree_of(search), G, ws),
            FVal.FV.kids_match_b(G, done_rev, kids), hv_c, hm))
      +hcs2 : {Nat.is_le(
                 FVal.FV.kids_cost_sum(Groups.Group{fb, ws} <> done_rev, kf),
                 sf) == True{} : Bool} =
        Fold.OQ.le_cong_r(
          Nat.add(Tree.cost(Eval.Eval.tree_of(search), ws),
            FVal.FV.kids_cost_sum(done_rev, kids)),
          Nat.add(sum, Eval.Eval.cost_of(search)), sf,
          Equal.sym(Nat, sf, Nat.add(sum, Eval.Eval.cost_of(search)), esf),
          Fold.OQ.le_cong_r(
            Nat.add(Tree.cost(Eval.Eval.tree_of(search), ws),
              FVal.FV.kids_cost_sum(done_rev, kids)),
            Nat.add(Eval.Eval.cost_of(search), sum),
            Nat.add(sum, Eval.Eval.cost_of(search)),
            NatProof.NatPrf.add_comm(Eval.Eval.cost_of(search), sum),
            CBN.CB.is_le_add(Tree.cost(Eval.Eval.tree_of(search), ws),
              Eval.Eval.cost_of(search),
              FVal.FV.kids_cost_sum(done_rev, kids), sum, hc_c, hcs)))
      FOpt.step_res_pre(p, gs, G, S, nodup, floor, inf, g, cs1, kids, sum,
        g, inner, kf, sf, best, gres, limit,
        Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g, restg, Nil{}, sr, inf)),
        Fold.OQ.ks_cost(inf, S,
          Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg,
            Nil{}, sum_ref, inf)),
        e_step,
        NatProof.Nat.is_le_eq_r(
          Fold.OQ.ks_cost(inf, S,
            Eval.Eval.items(p, G, S, g, restg, Nil{}, sr, inf)),
          Fold.OQ.ks_cost(inf, S,
            Eval.Eval.items(p, G, S, g, restg, Nil{}, sr, inf)),
          Fold.OQ.ks_cost(inf, S,
            Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg,
              Nil{}, sum_ref, inf)),
          Equal.sym(Nat,
            Fold.OQ.ks_cost(inf, S,
              Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg,
                Nil{}, sum_ref, inf)),
            Fold.OQ.ks_cost(inf, S,
              Eval.Eval.items(p, G, S, g, restg, Nil{}, sr, inf)), ek_step),
          NatProof.Nat.is_le_refl(
            Fold.OQ.ks_cost(inf, S,
              Eval.Eval.items(p, G, S, g, restg, Nil{}, sr, inf)))),
        rec_live(alive2, hsum_le2, hm2, hcs2))
    case False{}:
      +n : Nat = Groups.len_words(S)
      +gG : SolveFast.GList = SolveFast.glist_of(G, SolveFast.GEnd{})
      +tlb : Nat = SolveFast.lower_bound(n, restg)
      +B : Nat = Eval.Eval.cost_of(best)
      +cut : Nat = FS.FS.child_cutoff(best, sum, tlb)
      +search : SolveRef.Best =
        FS.FS.run_child_from(p, inf, G, ws, nodup, SolveFast.dummy_inf(cut))
      +ref_c : SolveRef.Best = FS.FS.ref_run_at(p, inf, G, ws)
      +inner : +List<SolveFast.Item> =
        List.append(&2, SolveFast.Item, SolveFast.group_items(nodup, n, restg),
          SolveFast.End{} <> Nil{})
      +cs1 : +List<SolveFast.Item> =
        SolveFast.ClassItem{fb, ws, Groups.len_words(ws), tlb}
        <> (SolveFast.Add{fb, tlb} <> inner)
      +cut_eq : {cut == Nat.sub(B, Nat.add(sum, tlb)) : Nat} =
        Equal.cong(Nat, Nat, x => Nat.sub(x, Nat.add(sum, tlb)),
          SolveFast.best_cost(best), B, FLB.FS.best_cost_eq(best))
      +st_le : {Nat.is_le(Nat.add(sum, tlb), B) == True{} : Bool} =
        FC.FC.sum_tail_le(sum, SolveFast.class_lb(ws), tlb, B, alive)
      +hr_c : {Bool.and(Nat.is_le(Eval.Eval.cost_of(search), cut),
                 Nat.is_le(Eval.Eval.cost_of(search), Eval.Eval.cost_of(ref_c)))
               == True{} : Bool} =
        Logic.Proof.and_true_r(FVal.FV.best_ok_b(cut, G, ws, search),
          Bool.and(Nat.is_le(Eval.Eval.cost_of(search), cut),
            Nat.is_le(Eval.Eval.cost_of(search), Eval.Eval.cost_of(ref_c))),
          hsearch)
      +hle_ref : {Nat.is_le(Eval.Eval.cost_of(search), Eval.Eval.cost_of(ref_c))
                  == True{} : Bool} =
        Logic.Proof.and_true_r(Nat.is_le(Eval.Eval.cost_of(search), cut),
          Nat.is_le(Eval.Eval.cost_of(search), Eval.Eval.cost_of(ref_c)), hr_c)
      +kf : +List<Tree.Child> = Tree.Child{fb, Eval.Eval.tree_of(search)} <> kids
      +sf : Nat = SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(search))
      +sr : Nat = SolveRef.sat_add(inf, sum_ref, Eval.Eval.cost_of(ref_c))
      +e_ca : {SolveFast.step(1n+p, gs, 0n, cs1, gG, S, n, nodup, floor, inf, g,
                 kids, sum, best, SolveFast.dummy_zero(), False{}, False{}, gres)
               == SolveFast.step(1n+p, gs, 0n, inner, gG, S, n, nodup, floor, inf,
                    g, kf, sf, best, SolveFast.dummy_zero(),
                    SolveFast.skippable(best, Nat.add(sf, tlb)), False{}, gres)
               : SolveRef.Best} =
        FS.FS.class_add_live(p, gs, G, S, n, nodup, floor, inf, g, fb, ws, tlb,
          inner, kids, sum, best, gres)
      +ek_step : {Fold.OQ.ks_cost(inf, S,
                    Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg,
                      Nil{}, sum_ref, inf))
                  == Fold.OQ.ks_cost(inf, S,
                       Eval.Eval.items(p, G, S, g, restg, Nil{}, sr, inf)) : Nat} =
        FVal.FV.ks_cost_items_step(p, inf, G, S, g, fb, ws, restg, sum_ref)
      +hge_cut : {Nat.is_le(cut, Eval.Eval.cost_of(search)) == True{} : Bool} =
        FC.FC.le_of_lt_false(Eval.Eval.cost_of(search), cut,
          Equal.sym(Bool, False{}, Nat.is_lt(Eval.Eval.cost_of(search), cut), elt))
      +sub_le_s : {Nat.is_le(Nat.sub(B, Nat.add(sum, tlb)),
                     Eval.Eval.cost_of(search)) == True{} : Bool} =
        NatProof.Nat.is_le_eq_l(Eval.Eval.cost_of(search), cut,
          Nat.sub(B, Nat.add(sum, tlb)), cut_eq, hge_cut)
      +le_f : {Nat.is_le(B, Nat.add(sf, tlb)) == True{} : Bool} =
        FC.FC.dead_cut_ge(inf, sum, Eval.Eval.cost_of(search), tlb, B, hbest,
          st_le, sub_le_s)
      +sk_t : {SolveFast.skippable(best, Nat.add(sf, tlb)) == True{} : Bool} =
        FOpt.skippable_true_of_le(best, Nat.add(sf, tlb), le_f)
      +e_dead : {SolveFast.step(1n+p, gs, 0n, cs1, gG, S, n, nodup, floor, inf,
                   g, kids, sum, best, SolveFast.dummy_zero(), False{},
                   False{}, gres)
                 == SolveFast.step(1n+p, gs, 0n, Nil{}, gG, S, n, nodup, floor,
                      inf, Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(),
                      False{}, False{}, gres) : SolveRef.Best} =
        Equal.trans(SolveRef.Best,
          SolveFast.step(1n+p, gs, 0n, cs1, gG, S, n, nodup, floor, inf, g,
            kids, sum, best, SolveFast.dummy_zero(), False{}, False{}, gres),
          SolveFast.step(1n+p, gs, 0n, inner, gG, S, n, nodup, floor, inf, g,
            kf, sf, best, SolveFast.dummy_zero(), True{}, False{}, gres),
          SolveFast.step(1n+p, gs, 0n, Nil{}, gG, S, n, nodup, floor, inf,
            Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{}, False{},
            gres),
          Equal.trans(SolveRef.Best,
            SolveFast.step(1n+p, gs, 0n, cs1, gG, S, n, nodup, floor, inf, g,
              kids, sum, best, SolveFast.dummy_zero(), False{}, False{}, gres),
            SolveFast.step(1n+p, gs, 0n, inner, gG, S, n, nodup, floor, inf, g,
              kf, sf, best, SolveFast.dummy_zero(),
              SolveFast.skippable(best, Nat.add(sf, tlb)), False{}, gres),
            SolveFast.step(1n+p, gs, 0n, inner, gG, S, n, nodup, floor, inf, g,
              kf, sf, best, SolveFast.dummy_zero(), True{}, False{}, gres),
            e_ca,
            Equal.cong(Bool, SolveRef.Best,
              sk => SolveFast.step(1n+p, gs, 0n, inner, gG, S, n, nodup, floor,
                      inf, g, kf, sf, best, SolveFast.dummy_zero(), sk,
                      False{}, gres),
              SolveFast.skippable(best, Nat.add(sf, tlb)), True{}, sk_t)),
          FS.FS.block_dead(p, gs, gG, S, n, nodup, floor, inf, g, restg, kf, sf,
            best, Nil{}, gres))
      +sub_le_r : {Nat.is_le(Nat.sub(B, Nat.add(sum, tlb)),
                     Eval.Eval.cost_of(ref_c)) == True{} : Bool} =
        NatProof.Nat.is_le_trans(Nat.sub(B, Nat.add(sum, tlb)),
          Eval.Eval.cost_of(search), Eval.Eval.cost_of(ref_c),
          sub_le_s, hle_ref)
      +le_plain_s : {Nat.is_le(B,
                       Nat.add(Nat.add(sum, Eval.Eval.cost_of(ref_c)), tlb))
                     == True{} : Bool} =
        NatProof.Nat.is_le_eq_r(B,
          Nat.add(Nat.add(sum, tlb), Eval.Eval.cost_of(ref_c)),
          Nat.add(Nat.add(sum, Eval.Eval.cost_of(ref_c)), tlb),
          Equal.sym(Nat,
            Nat.add(Nat.add(sum, Eval.Eval.cost_of(ref_c)), tlb),
            Nat.add(Nat.add(sum, tlb), Eval.Eval.cost_of(ref_c)),
            FC.FC.regroup_sum(sum, Eval.Eval.cost_of(ref_c), tlb)),
          NatProof.Nat.is_le_eq_l(
            Nat.add(Nat.add(sum, tlb), Eval.Eval.cost_of(ref_c)),
            Nat.add(Nat.add(sum, tlb), Nat.sub(B, Nat.add(sum, tlb))), B,
            FC.FC.add_sub_of_le(B, Nat.add(sum, tlb), st_le),
            NatProof.Nat.is_le_add_l(Nat.sub(B, Nat.add(sum, tlb)),
              Eval.Eval.cost_of(ref_c), Nat.add(sum, tlb), sub_le_r)))
      +le_plain_r : {Nat.is_le(B,
                       Nat.add(Nat.add(sum_ref, Eval.Eval.cost_of(ref_c)), tlb))
                     == True{} : Bool} =
        NatProof.Nat.is_le_trans(B,
          Nat.add(Nat.add(sum, Eval.Eval.cost_of(ref_c)), tlb),
          Nat.add(Nat.add(sum_ref, Eval.Eval.cost_of(ref_c)), tlb),
          le_plain_s,
          NatProof.Nat.is_le_add_r(
            Nat.add(sum, Eval.Eval.cost_of(ref_c)),
            Nat.add(sum_ref, Eval.Eval.cost_of(ref_c)), tlb,
            NatProof.Nat.is_le_add_r(sum, sum_ref, Eval.Eval.cost_of(ref_c),
              hsum_le)))
      +le_r : {Nat.is_le(B, Nat.add(sr, tlb)) == True{} : Bool} =
        FC.FC.le_sat_add_r(inf, sum_ref, Eval.Eval.cost_of(ref_c), tlb, B,
          hbest, le_plain_r)
      +ks_r : Eval.KS = Eval.Eval.items(p, G, S, g, restg, Nil{}, sr, inf)
      +feq_r : {Eval.Eval.finish_ks(inf, g, S, ks_r, best) == best
                : SolveRef.Best} =
        FLB.FS.finish_skip_eq(p, inf, G, S, g, restg, Nil{}, sr, best, bt, hz,
          hbest, le_r)
      +hb_le_r : {Nat.is_le(B, Fold.OQ.ks_cost(inf, S, ks_r)) == True{} : Bool} =
        Fold.OQ.le_cong_l(B,
          Eval.Eval.cost_of(
            SolveRef.better(Fold.OQ.ks_cost(inf, S, ks_r),
              Fold.OQ.ks_tree(g, ks_r), best)),
          Fold.OQ.ks_cost(inf, S, ks_r),
          Equal.trans(Nat, B,
            Eval.Eval.cost_of(Eval.Eval.finish_ks(inf, g, S, ks_r, best)),
            Eval.Eval.cost_of(
              SolveRef.better(Fold.OQ.ks_cost(inf, S, ks_r),
                Fold.OQ.ks_tree(g, ks_r), best)),
            Equal.cong(SolveRef.Best, Nat, Eval.Eval.cost_of, best,
              Eval.Eval.finish_ks(inf, g, S, ks_r, best),
              Equal.sym(SolveRef.Best,
                Eval.Eval.finish_ks(inf, g, S, ks_r, best), best, feq_r)),
            Fold.OQ.block_cost_eq(inf, g, S, ks_r, best)),
          Fold.OQ.better_le_cand(Fold.OQ.ks_cost(inf, S, ks_r),
            Fold.OQ.ks_tree(g, ks_r), best))
      +hb_le_full : {Nat.is_le(B,
                       Fold.OQ.ks_cost(inf, S,
                         Eval.Eval.items(p, G, S, g,
                           Groups.Group{fb, ws} <> restg, Nil{}, sum_ref, inf)))
                     == True{} : Bool} =
        Fold.OQ.le_cong_r(B, Fold.OQ.ks_cost(inf, S, ks_r),
          Fold.OQ.ks_cost(inf, S,
            Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg,
              Nil{}, sum_ref, inf)),
          Equal.sym(Nat,
            Fold.OQ.ks_cost(inf, S,
              Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg,
                Nil{}, sum_ref, inf)),
            Fold.OQ.ks_cost(inf, S, ks_r), ek_step),
          hb_le_r)
      FOpt.step_res_pre(p, gs, G, S, nodup, floor, inf, g, cs1, kids, sum,
        Nil{}, Nil{}, Nil{}, 0n, best, gres, limit,
        Fold.OQ.ks_cost(inf, S,
          Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg,
            Nil{}, sum_ref, inf)),
        Fold.OQ.ks_cost(inf, S,
          Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg,
            Nil{}, sum_ref, inf)),
        e_dead,
        NatProof.Nat.is_le_refl(
          Fold.OQ.ks_cost(inf, S,
            Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg,
              Nil{}, sum_ref, inf))),
        FOpt.step_res_keep(p, gs, G, S, nodup, floor, inf, best, gres, limit,
          Fold.OQ.ks_cost(inf, S,
            Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg,
              Nil{}, sum_ref, inf)),
          hok, hd, hb_le_full))

def FOpt.live_group_class(-gres: SolveFast.GuessRes, +p: Nat,
    +gs: SolveFast.GList, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +nodup: Bool, +floor: Nat, +inf: Nat, +g: +List<Nat>,
    +fb: +List<Feedback.Color>, +ws: +List<+List<Nat>>,
    +restg: +List<Groups.Group>, +done_rev: +List<Groups.Group>,
    +kids: +List<Tree.Child>, +sum: Nat, +sum_ref: Nat, +best: SolveRef.Best,
    +limit: Nat,
    bt: MV.MV.Bounds(p, MV.MV.next_groups(restg)),
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    +hok: {FVal.FV.best_ok_b(limit, G, S, best) == True{} : Bool},
    +hd: {SolveFast.is_floor_hit(nodup, floor, best) == False{} : Bool},
    +alive: {Nat.is_lt(
               Nat.add(sum,
                 SolveFast.lower_bound(Groups.len_words(S),
                   Groups.Group{fb, ws} <> restg)),
               Eval.Eval.cost_of(best)) == True{} : Bool},
    +hsum_le: {Nat.is_le(sum, sum_ref) == True{} : Bool},
    +hm: {FVal.FV.kids_match_b(G, done_rev, kids) == True{} : Bool},
    +hcs: {Nat.is_le(FVal.FV.kids_cost_sum(done_rev, kids), sum)
           == True{} : Bool},
    eh: FOpt.EJob(p, inf, G, ws, nodup),
    rec_live:
      {Nat.is_lt(
         Nat.add(
           SolveRef.sat_add(inf, sum,
             Eval.Eval.cost_of(
               FS.FS.run_child_from(p, inf, G, ws, nodup,
                 SolveFast.dummy_inf(FS.FS.child_cutoff(best, sum,
                   SolveFast.lower_bound(Groups.len_words(S), restg)))))),
           SolveFast.lower_bound(Groups.len_words(S), restg)),
         Eval.Eval.cost_of(best)) == True{} : Bool} ->
      {Nat.is_le(
         SolveRef.sat_add(inf, sum,
           Eval.Eval.cost_of(
             FS.FS.run_child_from(p, inf, G, ws, nodup,
               SolveFast.dummy_inf(FS.FS.child_cutoff(best, sum,
                 SolveFast.lower_bound(Groups.len_words(S), restg)))))),
         SolveRef.sat_add(inf, sum_ref,
           Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, ws))))
       == True{} : Bool} ->
      {FVal.FV.kids_match_b(G, Groups.Group{fb, ws} <> done_rev,
         Tree.Child{fb, Eval.Eval.tree_of(
           FS.FS.run_child_from(p, inf, G, ws, nodup,
             SolveFast.dummy_inf(FS.FS.child_cutoff(best, sum,
               SolveFast.lower_bound(Groups.len_words(S), restg)))))} <> kids)
       == True{} : Bool} ->
      {Nat.is_le(
         FVal.FV.kids_cost_sum(Groups.Group{fb, ws} <> done_rev,
           Tree.Child{fb, Eval.Eval.tree_of(
             FS.FS.run_child_from(p, inf, G, ws, nodup,
               SolveFast.dummy_inf(FS.FS.child_cutoff(best, sum,
                 SolveFast.lower_bound(Groups.len_words(S), restg)))))} <> kids),
         SolveRef.sat_add(inf, sum,
           Eval.Eval.cost_of(
             FS.FS.run_child_from(p, inf, G, ws, nodup,
               SolveFast.dummy_inf(FS.FS.child_cutoff(best, sum,
                 SolveFast.lower_bound(Groups.len_words(S), restg)))))))
       == True{} : Bool} ->
      FOpt.StepRes(p, gs, G, S, nodup, floor, inf, g,
        List.append(&2, SolveFast.Item,
          SolveFast.group_items(nodup, Groups.len_words(S), restg),
          SolveFast.End{} <> Nil{}),
        Tree.Child{fb, Eval.Eval.tree_of(
          FS.FS.run_child_from(p, inf, G, ws, nodup,
            SolveFast.dummy_inf(FS.FS.child_cutoff(best, sum,
              SolveFast.lower_bound(Groups.len_words(S), restg)))))} <> kids,
        SolveRef.sat_add(inf, sum,
          Eval.Eval.cost_of(
            FS.FS.run_child_from(p, inf, G, ws, nodup,
              SolveFast.dummy_inf(FS.FS.child_cutoff(best, sum,
                SolveFast.lower_bound(Groups.len_words(S), restg)))))),
        best, gres, limit,
        Fold.OQ.ks_cost(inf, S,
          Eval.Eval.items(p, G, S, g, restg, Nil{},
            SolveRef.sat_add(inf, sum_ref,
              Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, ws))), inf)))) ->
  FOpt.StepRes(p, gs, G, S, nodup, floor, inf, g,
    SolveFast.ClassItem{fb, ws, Groups.len_words(ws),
      SolveFast.lower_bound(Groups.len_words(S), restg)}
    <> (SolveFast.Add{fb, SolveFast.lower_bound(Groups.len_words(S), restg)}
        <> List.append(&2, SolveFast.Item,
             SolveFast.group_items(nodup, Groups.len_words(S), restg),
             SolveFast.End{} <> Nil{})),
    kids, sum, best, gres, limit,
    Fold.OQ.ks_cost(inf, S,
      Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg,
        Nil{}, sum_ref, inf))):
  +n : Nat = Groups.len_words(S)
  +tlb : Nat = SolveFast.lower_bound(n, restg)
  +B : Nat = Eval.Eval.cost_of(best)
  +cut : Nat = FS.FS.child_cutoff(best, sum, tlb)
  +cut_eq : {cut == Nat.sub(B, Nat.add(sum, tlb)) : Nat} =
    Equal.cong(Nat, Nat, x => Nat.sub(x, Nat.add(sum, tlb)),
      SolveFast.best_cost(best), B, FLB.FS.best_cost_eq(best))
  +cut_le_inf : {Nat.is_le(cut, inf) == True{} : Bool} =
    NatProof.Nat.is_le_trans(cut, B, inf,
      NatProof.Nat.is_le_eq_l(B, Nat.sub(B, Nat.add(sum, tlb)), cut,
        Equal.sym(Nat, cut, Nat.sub(B, Nat.add(sum, tlb)), cut_eq),
        FC.FC.sub_le_self(B, Nat.add(sum, tlb))),
      hbest)
  +hsearch = eh(SolveFast.dummy_inf(cut), cut_le_inf)
  +search = FS.FS.run_child_from(p, inf, G, ws, nodup, SolveFast.dummy_inf(cut))
  FOpt.live_group_class_go(gres, p, gs, G, S, nodup, floor, inf, g, fb, ws,
    restg, done_rev, kids, sum, sum_ref, best, limit, bt, hz, hbest, hok, hd,
    alive, hsum_le, hm, hcs, hsearch,
    Nat.is_lt(Eval.Eval.cost_of(search), cut), {==}, rec_live)

def FOpt.live_group_one(-gres: SolveFast.GuessRes, +p: Nat,
    +gs: SolveFast.GList, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +nodup: Bool, +floor: Nat, +inf: Nat, +g: +List<Nat>,
    +fb: +List<Feedback.Color>, +w: +List<Nat>,
    +restg: +List<Groups.Group>, +done_rev: +List<Groups.Group>,
    +kids: +List<Tree.Child>, +sum: Nat, +sum_ref: Nat, +best: SolveRef.Best,
    +limit: Nat,
    +ble: {Nat.is_le(1n, p) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +win: {Tree.member_word(w, G) == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    +alive: {Nat.is_lt(
               Nat.add(sum,
                 SolveFast.lower_bound(Groups.len_words(S),
                   Groups.Group{fb, w <> Nil{}} <> restg)),
               Eval.Eval.cost_of(best)) == True{} : Bool},
    +hsum_le: {Nat.is_le(sum, sum_ref) == True{} : Bool},
    +hm: {FVal.FV.kids_match_b(G, done_rev, kids) == True{} : Bool},
    +hcs: {Nat.is_le(FVal.FV.kids_cost_sum(done_rev, kids), sum)
           == True{} : Bool},
    rec_live:
      {Nat.is_lt(
         Nat.add(SolveRef.sat_add(inf, sum, 1n),
           SolveFast.lower_bound(Groups.len_words(S), restg)),
         Eval.Eval.cost_of(best)) == True{} : Bool} ->
      {Nat.is_le(SolveRef.sat_add(inf, sum, 1n),
         SolveRef.sat_add(inf, sum_ref,
           Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, w <> Nil{}))))
       == True{} : Bool} ->
      {FVal.FV.kids_match_b(G, Groups.Group{fb, w <> Nil{}} <> done_rev,
         Tree.Child{fb, Tree.Node{w, Nil{}}} <> kids) == True{} : Bool} ->
      {Nat.is_le(
         FVal.FV.kids_cost_sum(Groups.Group{fb, w <> Nil{}} <> done_rev,
           Tree.Child{fb, Tree.Node{w, Nil{}}} <> kids),
         SolveRef.sat_add(inf, sum, 1n)) == True{} : Bool} ->
      FOpt.StepRes(p, gs, G, S, nodup, floor, inf, g,
        List.append(&2, SolveFast.Item,
          SolveFast.group_items(nodup, Groups.len_words(S), restg),
          SolveFast.End{} <> Nil{}),
        Tree.Child{fb, Tree.Node{w, Nil{}}} <> kids,
        SolveRef.sat_add(inf, sum, 1n), best, gres, limit,
        Fold.OQ.ks_cost(inf, S,
          Eval.Eval.items(p, G, S, g, restg, Nil{},
            SolveRef.sat_add(inf, sum_ref,
              Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, w <> Nil{}))),
            inf)))) ->
  FOpt.StepRes(p, gs, G, S, nodup, floor, inf, g,
    SolveFast.OneItem{fb, w}
    <> List.append(&2, SolveFast.Item,
         SolveFast.group_items(nodup, Groups.len_words(S), restg),
         SolveFast.End{} <> Nil{}),
    kids, sum, best, gres, limit,
    Fold.OQ.ks_cost(inf, S,
      Eval.Eval.items(p, G, S, g, Groups.Group{fb, w <> Nil{}} <> restg,
        Nil{}, sum_ref, inf))):
  +n : Nat = Groups.len_words(S)
  +gG : SolveFast.GList = SolveFast.glist_of(G, SolveFast.GEnd{})
  +tlb : Nat = SolveFast.lower_bound(n, restg)
  +B : Nat = Eval.Eval.cost_of(best)
  +inner : +List<SolveFast.Item> =
    List.append(&2, SolveFast.Item, SolveFast.group_items(nodup, n, restg),
      SolveFast.End{} <> Nil{})
  +ws1 : +List<+List<Nat>> = w <> Nil{}
  +ref_c : SolveRef.Best = FS.FS.ref_run_at(p, inf, G, ws1)
  +e1_clb : {SolveFast.class_lb(ws1) == 1n : Nat} =
    Equal.sym(Nat, 1n, SolveFast.class_lb(ws1),
      FN.FN.class_lb_nodup_eq(ws1, {==}))
  +alive_1 : {Nat.is_lt(Nat.add(sum, Nat.add(1n, tlb)), B) == True{} : Bool} =
    CBN.CB.lt_eq_l(B,
      Nat.add(sum, Nat.add(SolveFast.class_lb(ws1), tlb)),
      Nat.add(sum, Nat.add(1n, tlb)),
      Equal.cong(Nat, Nat, x => Nat.add(sum, Nat.add(x, tlb)),
        SolveFast.class_lb(ws1), 1n, e1_clb),
      alive)
  +alive2 : {Nat.is_lt(Nat.add(SolveRef.sat_add(inf, sum, 1n), tlb), B)
             == True{} : Bool} =
    FC.FC.alive_one(inf, sum, tlb, B, hbest, alive_1)
  +es1 : {SolveRef.sat_add(inf, sum, 1n) == Nat.add(sum, 1n) : Nat} =
    FVal.FV.sat_add_1_eq(inf, sum, tlb, B, hbest, alive_1)
  +e_ref1 : {1n == Eval.Eval.cost_of(ref_c) : Nat} =
    Equal.cong(SolveRef.Best, Nat, Eval.Eval.cost_of,
      SolveRef.Best{Tree.Node{w, Nil{}}, 1n}, ref_c,
      FO.FO.ref_run_one_eq(p, inf, G, w, ble, h1, win))
  +h1_le_ref : {Nat.is_le(1n, Eval.Eval.cost_of(ref_c)) == True{} : Bool} =
    NatProof.Nat.is_le_eq_r(1n, 1n, Eval.Eval.cost_of(ref_c), e_ref1, {==})
  +hlt_inf : {Nat.is_lt(Nat.add(sum, 1n), inf) == True{} : Bool} =
    NatProof.Nat.is_lt_le_trans(Nat.add(sum, 1n), B, inf,
      NatProof.Nat.is_le_lt_trans(Nat.add(sum, 1n),
        Nat.add(SolveRef.sat_add(inf, sum, 1n), tlb), B,
        NatProof.Nat.is_le_eq_l(Nat.add(SolveRef.sat_add(inf, sum, 1n), tlb),
          SolveRef.sat_add(inf, sum, 1n), Nat.add(sum, 1n), es1,
          CBN.CB.is_le_add_self_r(SolveRef.sat_add(inf, sum, 1n), tlb)),
        alive2),
      hbest)
  +sr : Nat = SolveRef.sat_add(inf, sum_ref, Eval.Eval.cost_of(ref_c))
  +hsum_le2 : {Nat.is_le(SolveRef.sat_add(inf, sum, 1n), sr) == True{} : Bool} =
    Fold.OQ.le_cong_l(SolveRef.sat_add(inf, sum, 1n), Nat.add(sum, 1n), sr, es1,
      FVal.FV.le_sat_add_of_lt_inf(inf, sum, sum_ref, 1n,
        Eval.Eval.cost_of(ref_c), hsum_le, h1_le_ref, hlt_inf))
  +hm2 : {FVal.FV.kids_match_b(G, Groups.Group{fb, ws1} <> done_rev,
            Tree.Child{fb, Tree.Node{w, Nil{}}} <> kids) == True{} : Bool} =
    FO.FO.bool_and_intro(Feedback.feedback_eq(fb, fb),
      Bool.and(FVal.FV.valid_b(Tree.Node{w, Nil{}}, G, ws1),
        FVal.FV.kids_match_b(G, done_rev, kids)),
      FbProof.FbPrf.feedback_eq_refl(fb),
      FO.FO.bool_and_intro(FVal.FV.valid_b(Tree.Node{w, Nil{}}, G, ws1),
        FVal.FV.kids_match_b(G, done_rev, kids),
        FVal.FV.one_tree_valid_b(w, G, win), hm))
  +hc1 : {Nat.is_le(Tree.cost(Tree.Node{w, Nil{}}, ws1), 1n) == True{} : Bool} =
    Fold.OQ.le_cong_l(Tree.cost(Tree.Node{w, Nil{}}, ws1), 1n, 1n,
      FVal.FV.one_tree_cost(w), {==})
  +hcs2 : {Nat.is_le(
             FVal.FV.kids_cost_sum(Groups.Group{fb, ws1} <> done_rev,
               Tree.Child{fb, Tree.Node{w, Nil{}}} <> kids),
             SolveRef.sat_add(inf, sum, 1n)) == True{} : Bool} =
    Fold.OQ.le_cong_r(
      Nat.add(Tree.cost(Tree.Node{w, Nil{}}, ws1),
        FVal.FV.kids_cost_sum(done_rev, kids)),
      Nat.add(sum, 1n), SolveRef.sat_add(inf, sum, 1n),
      Equal.sym(Nat, SolveRef.sat_add(inf, sum, 1n), Nat.add(sum, 1n), es1),
      Fold.OQ.le_cong_r(
        Nat.add(Tree.cost(Tree.Node{w, Nil{}}, ws1),
          FVal.FV.kids_cost_sum(done_rev, kids)),
        Nat.add(1n, sum), Nat.add(sum, 1n),
        NatProof.NatPrf.add_comm(1n, sum),
        CBN.CB.is_le_add(Tree.cost(Tree.Node{w, Nil{}}, ws1), 1n,
          FVal.FV.kids_cost_sum(done_rev, kids), sum, hc1, hcs)))
  +ek_step : {Fold.OQ.ks_cost(inf, S,
                Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws1} <> restg,
                  Nil{}, sum_ref, inf))
              == Fold.OQ.ks_cost(inf, S,
                   Eval.Eval.items(p, G, S, g, restg, Nil{}, sr, inf)) : Nat} =
    FVal.FV.ks_cost_items_step(p, inf, G, S, g, fb, ws1, restg, sum_ref)
  FOpt.step_res_pre(p, gs, G, S, nodup, floor, inf, g,
    SolveFast.OneItem{fb, w} <> inner, kids, sum,
    g, inner, Tree.Child{fb, Tree.Node{w, Nil{}}} <> kids,
    SolveRef.sat_add(inf, sum, 1n), best, gres, limit,
    Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g, restg, Nil{}, sr, inf)),
    Fold.OQ.ks_cost(inf, S,
      Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws1} <> restg,
        Nil{}, sum_ref, inf)),
    FS.FS.one_live(p, gs, gG, S, n, nodup, floor, inf, g, fb, w, inner, kids,
      sum, best, gres),
    NatProof.Nat.is_le_eq_r(
      Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g, restg, Nil{}, sr, inf)),
      Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g, restg, Nil{}, sr, inf)),
      Fold.OQ.ks_cost(inf, S,
        Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws1} <> restg,
          Nil{}, sum_ref, inf)),
      Equal.sym(Nat,
        Fold.OQ.ks_cost(inf, S,
          Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws1} <> restg,
            Nil{}, sum_ref, inf)),
        Fold.OQ.ks_cost(inf, S,
          Eval.Eval.items(p, G, S, g, restg, Nil{}, sr, inf)), ek_step),
      NatProof.Nat.is_le_refl(
        Fold.OQ.ks_cost(inf, S,
          Eval.Eval.items(p, G, S, g, restg, Nil{}, sr, inf)))),
    rec_live(alive2, hsum_le2, hm2, hcs2))

def FOpt.live_group_two(-gres: SolveFast.GuessRes, +p: Nat,
    +gs: SolveFast.GList, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +floor: Nat, +inf: Nat, +g: +List<Nat>, +fb: +List<Feedback.Color>,
    +w1: +List<Nat>, +w2: +List<Nat>, +restg: +List<Groups.Group>,
    +done_rev: +List<Groups.Group>, +kids: +List<Tree.Child>, +sum: Nat,
    +sum_ref: Nat, +best: SolveRef.Best, +limit: Nat,
    +ble: {Nat.is_le(2n, p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h3: {Nat.is_lt(3n, inf) == True{} : Bool},
    +w1in: {Tree.member_word(w1, G) == True{} : Bool},
    +w2in: {Tree.member_word(w2, G) == True{} : Bool},
    +nd2: {FN.FN.no_dup_ref(w1 <> (w2 <> Nil{})) == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    +alive: {Nat.is_lt(
               Nat.add(sum,
                 SolveFast.lower_bound(Groups.len_words(S),
                   Groups.Group{fb, w1 <> (w2 <> Nil{})} <> restg)),
               Eval.Eval.cost_of(best)) == True{} : Bool},
    +hsum_le: {Nat.is_le(sum, sum_ref) == True{} : Bool},
    +hm: {FVal.FV.kids_match_b(G, done_rev, kids) == True{} : Bool},
    +hcs: {Nat.is_le(FVal.FV.kids_cost_sum(done_rev, kids), sum)
           == True{} : Bool},
    rec_live:
      {Nat.is_lt(
         Nat.add(SolveRef.sat_add(inf, sum, 3n),
           SolveFast.lower_bound(Groups.len_words(S), restg)),
         Eval.Eval.cost_of(best)) == True{} : Bool} ->
      {Nat.is_le(SolveRef.sat_add(inf, sum, 3n),
         SolveRef.sat_add(inf, sum_ref,
           Eval.Eval.cost_of(
             FS.FS.ref_run_at(p, inf, G, w1 <> (w2 <> Nil{})))))
       == True{} : Bool} ->
      {FVal.FV.kids_match_b(G, Groups.Group{fb, w1 <> (w2 <> Nil{})} <> done_rev,
         Tree.Child{fb, SolveFast.two_tree(w1, w2)} <> kids)
       == True{} : Bool} ->
      {Nat.is_le(
         FVal.FV.kids_cost_sum(Groups.Group{fb, w1 <> (w2 <> Nil{})} <> done_rev,
           Tree.Child{fb, SolveFast.two_tree(w1, w2)} <> kids),
         SolveRef.sat_add(inf, sum, 3n)) == True{} : Bool} ->
      FOpt.StepRes(p, gs, G, S, True{}, floor, inf, g,
        List.append(&2, SolveFast.Item,
          SolveFast.group_items(True{}, Groups.len_words(S), restg),
          SolveFast.End{} <> Nil{}),
        Tree.Child{fb, SolveFast.two_tree(w1, w2)} <> kids,
        SolveRef.sat_add(inf, sum, 3n), best, gres, limit,
        Fold.OQ.ks_cost(inf, S,
          Eval.Eval.items(p, G, S, g, restg, Nil{},
            SolveRef.sat_add(inf, sum_ref,
              Eval.Eval.cost_of(
                FS.FS.ref_run_at(p, inf, G, w1 <> (w2 <> Nil{})))),
            inf)))) ->
  FOpt.StepRes(p, gs, G, S, True{}, floor, inf, g,
    SolveFast.TwoItem{fb, w1, w2}
    <> List.append(&2, SolveFast.Item,
         SolveFast.group_items(True{}, Groups.len_words(S), restg),
         SolveFast.End{} <> Nil{}),
    kids, sum, best, gres, limit,
    Fold.OQ.ks_cost(inf, S,
      Eval.Eval.items(p, G, S, g, Groups.Group{fb, w1 <> (w2 <> Nil{})} <> restg,
        Nil{}, sum_ref, inf))):
  +n : Nat = Groups.len_words(S)
  +gG : SolveFast.GList = SolveFast.glist_of(G, SolveFast.GEnd{})
  +tlb : Nat = SolveFast.lower_bound(n, restg)
  +B : Nat = Eval.Eval.cost_of(best)
  +inner : +List<SolveFast.Item> =
    List.append(&2, SolveFast.Item, SolveFast.group_items(True{}, n, restg),
      SolveFast.End{} <> Nil{})
  +ws2 : +List<+List<Nat>> = w1 <> (w2 <> Nil{})
  +ref_c : SolveRef.Best = FS.FS.ref_run_at(p, inf, G, ws2)
  +hne : {Feedback.word_eq(w1, w2) == False{} : Bool} =
    FVal.FV.word_eq_false_of_no_dup_two(w1, w2, nd2)
  +e3_clb : {SolveFast.class_lb(ws2) == 3n : Nat} =
    Equal.sym(Nat, 3n, SolveFast.class_lb(ws2),
      FN.FN.class_lb_nodup_eq(ws2, nd2))
  +alive_3 : {Nat.is_lt(Nat.add(sum, Nat.add(3n, tlb)), B) == True{} : Bool} =
    CBN.CB.lt_eq_l(B,
      Nat.add(sum, Nat.add(SolveFast.class_lb(ws2), tlb)),
      Nat.add(sum, Nat.add(3n, tlb)),
      Equal.cong(Nat, Nat, x => Nat.add(sum, Nat.add(x, tlb)),
        SolveFast.class_lb(ws2), 3n, e3_clb),
      alive)
  +alive2 : {Nat.is_lt(Nat.add(SolveRef.sat_add(inf, sum, 3n), tlb), B)
             == True{} : Bool} =
    FVal.FV.alive_two(inf, sum, tlb, B, hbest, alive_3)
  +es3 : {SolveRef.sat_add(inf, sum, 3n) == Nat.add(sum, 3n) : Nat} =
    FVal.FV.sat_add_3_eq(inf, sum, tlb, B, hbest, alive_3)
  +h3_le_ref : {Nat.is_le(3n, Eval.Eval.cost_of(ref_c)) == True{} : Bool} =
    FVal.FV.three_le_ref_two(p, inf, G, w1, w2, ble, hz, h3, nd2)
  +hlt_inf : {Nat.is_lt(Nat.add(sum, 3n), inf) == True{} : Bool} =
    NatProof.Nat.is_lt_le_trans(Nat.add(sum, 3n), B, inf,
      NatProof.Nat.is_le_lt_trans(Nat.add(sum, 3n),
        Nat.add(SolveRef.sat_add(inf, sum, 3n), tlb), B,
        NatProof.Nat.is_le_eq_l(Nat.add(SolveRef.sat_add(inf, sum, 3n), tlb),
          SolveRef.sat_add(inf, sum, 3n), Nat.add(sum, 3n), es3,
          CBN.CB.is_le_add_self_r(SolveRef.sat_add(inf, sum, 3n), tlb)),
        alive2),
      hbest)
  +sr : Nat = SolveRef.sat_add(inf, sum_ref, Eval.Eval.cost_of(ref_c))
  +hsum_le2 : {Nat.is_le(SolveRef.sat_add(inf, sum, 3n), sr) == True{} : Bool} =
    Fold.OQ.le_cong_l(SolveRef.sat_add(inf, sum, 3n), Nat.add(sum, 3n), sr, es3,
      FVal.FV.le_sat_add_of_lt_inf(inf, sum, sum_ref, 3n,
        Eval.Eval.cost_of(ref_c), hsum_le, h3_le_ref, hlt_inf))
  +hm2 : {FVal.FV.kids_match_b(G, Groups.Group{fb, ws2} <> done_rev,
            Tree.Child{fb, SolveFast.two_tree(w1, w2)} <> kids)
          == True{} : Bool} =
    FO.FO.bool_and_intro(Feedback.feedback_eq(fb, fb),
      Bool.and(FVal.FV.valid_b(SolveFast.two_tree(w1, w2), G, ws2),
        FVal.FV.kids_match_b(G, done_rev, kids)),
      FbProof.FbPrf.feedback_eq_refl(fb),
      FO.FO.bool_and_intro(
        FVal.FV.valid_b(SolveFast.two_tree(w1, w2), G, ws2),
        FVal.FV.kids_match_b(G, done_rev, kids),
        FVal.FV.two_tree_valid_b(w1, w2, G, w1in, w2in, hne), hm))
  +hc3 : {Nat.is_le(Tree.cost(SolveFast.two_tree(w1, w2), ws2), 3n)
          == True{} : Bool} =
    Fold.OQ.le_cong_l(Tree.cost(SolveFast.two_tree(w1, w2), ws2), 3n, 3n,
      FVal.FV.two_tree_cost(w1, w2, hne), {==})
  +hcs2 : {Nat.is_le(
             FVal.FV.kids_cost_sum(Groups.Group{fb, ws2} <> done_rev,
               Tree.Child{fb, SolveFast.two_tree(w1, w2)} <> kids),
             SolveRef.sat_add(inf, sum, 3n)) == True{} : Bool} =
    Fold.OQ.le_cong_r(
      Nat.add(Tree.cost(SolveFast.two_tree(w1, w2), ws2),
        FVal.FV.kids_cost_sum(done_rev, kids)),
      Nat.add(sum, 3n), SolveRef.sat_add(inf, sum, 3n),
      Equal.sym(Nat, SolveRef.sat_add(inf, sum, 3n), Nat.add(sum, 3n), es3),
      Fold.OQ.le_cong_r(
        Nat.add(Tree.cost(SolveFast.two_tree(w1, w2), ws2),
          FVal.FV.kids_cost_sum(done_rev, kids)),
        Nat.add(3n, sum), Nat.add(sum, 3n),
        NatProof.NatPrf.add_comm(3n, sum),
        CBN.CB.is_le_add(Tree.cost(SolveFast.two_tree(w1, w2), ws2), 3n,
          FVal.FV.kids_cost_sum(done_rev, kids), sum, hc3, hcs)))
  +ek_step : {Fold.OQ.ks_cost(inf, S,
                Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws2} <> restg,
                  Nil{}, sum_ref, inf))
              == Fold.OQ.ks_cost(inf, S,
                   Eval.Eval.items(p, G, S, g, restg, Nil{}, sr, inf)) : Nat} =
    FVal.FV.ks_cost_items_step(p, inf, G, S, g, fb, ws2, restg, sum_ref)
  FOpt.step_res_pre(p, gs, G, S, True{}, floor, inf, g,
    SolveFast.TwoItem{fb, w1, w2} <> inner, kids, sum,
    g, inner, Tree.Child{fb, SolveFast.two_tree(w1, w2)} <> kids,
    SolveRef.sat_add(inf, sum, 3n), best, gres, limit,
    Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g, restg, Nil{}, sr, inf)),
    Fold.OQ.ks_cost(inf, S,
      Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws2} <> restg,
        Nil{}, sum_ref, inf)),
    FS.FS.two_live(p, gs, gG, S, n, True{}, floor, inf, g, fb, w1, w2, inner,
      kids, sum, best, gres),
    NatProof.Nat.is_le_eq_r(
      Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g, restg, Nil{}, sr, inf)),
      Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g, restg, Nil{}, sr, inf)),
      Fold.OQ.ks_cost(inf, S,
        Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws2} <> restg,
          Nil{}, sum_ref, inf)),
      Equal.sym(Nat,
        Fold.OQ.ks_cost(inf, S,
          Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws2} <> restg,
            Nil{}, sum_ref, inf)),
        Fold.OQ.ks_cost(inf, S,
          Eval.Eval.items(p, G, S, g, restg, Nil{}, sr, inf)), ek_step),
      NatProof.Nat.is_le_refl(
        Fold.OQ.ks_cost(inf, S,
          Eval.Eval.items(p, G, S, g, restg, Nil{}, sr, inf)))),
    rec_live(alive2, hsum_le2, hm2, hcs2))

def FOpt.live_group_end(-gres: SolveFast.GuessRes, +p: Nat,
    +gs: SolveFast.GList, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +nodup: Bool, +floor: Nat, +inf: Nat, +g: +List<Nat>,
    +done_rev: +List<Groups.Group>, +kids: +List<Tree.Child>, +sum: Nat,
    +sum_ref: Nat, +best: SolveRef.Best, +limit: Nat,
    +wg: {Tree.member_word(g, G) == True{} : Bool},
    +esplit: {FVal.FV.rev_groups(done_rev, Nil{})
              == Groups.groups_build(g, S, Nil{}) : +List<Groups.Group>},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    +hok: {FVal.FV.best_ok_b(limit, G, S, best) == True{} : Bool},
    +alive: {Nat.is_lt(Nat.add(sum, Groups.len_words(S)),
               Eval.Eval.cost_of(best)) == True{} : Bool},
    +hsum_le: {Nat.is_le(sum, sum_ref) == True{} : Bool},
    +hm: {FVal.FV.kids_match_b(G, done_rev, kids) == True{} : Bool},
    +hcs: {Nat.is_le(FVal.FV.kids_cost_sum(done_rev, kids), sum)
           == True{} : Bool}) ->
  FOpt.StepRes(p, gs, G, S, nodup, floor, inf, g,
    SolveFast.End{} <> Nil{}, kids, sum, best, gres, limit,
    Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g, Nil{}, Nil{}, sum_ref, inf))):
  +n : Nat = Groups.len_words(S)
  +gG : SolveFast.GList = SolveFast.glist_of(G, SolveFast.GEnd{})
  +B : Nat = Eval.Eval.cost_of(best)
  +candCost : Nat = SolveRef.sat_add(inf, n, sum)
  +candTree : Tree.Tree = Tree.Node{g, SolveRef.rev_kids(kids, Nil{})}
  +best2 : SolveRef.Best = SolveRef.finish_guess(inf, g, kids, sum, n, best)
  +hlt_ns : {Nat.is_lt(Nat.add(n, sum), B) == True{} : Bool} =
    CBN.CB.lt_eq_l(B, Nat.add(sum, n), Nat.add(n, sum),
      NatProof.NatPrf.add_comm(sum, n), alive)
  +hlt_inf : {Nat.is_lt(Nat.add(n, sum), inf) == True{} : Bool} =
    NatProof.Nat.is_lt_le_trans(Nat.add(n, sum), B, inf, hlt_ns, hbest)
  +esat : {candCost == Nat.add(n, sum) : Nat} =
    FC.FC.sat_add_lt_eq(inf, n, sum, 0n, B, hbest,
      CBN.CB.lt_eq_l(B, Nat.add(n, sum), Nat.add(Nat.add(n, sum), 0n),
        Equal.sym(Nat, Nat.add(Nat.add(n, sum), 0n), Nat.add(n, sum),
          NatProof.NatPrf.add_zero(Nat.add(n, sum))),
        hlt_ns))
  +hend : {Bool.and(FVal.FV.valid_b(candTree, G, S),
             Nat.is_le(Tree.cost(candTree, S), Nat.add(n, sum)))
           == True{} : Bool} =
    FVal.FV.end_node_ok(G, S, g, done_rev, kids, sum, wg, esplit, hm, hcs)
  +hvalid : {FVal.FV.valid_b(candTree, G, S) == True{} : Bool} =
    Logic.Proof.and_true_l(FVal.FV.valid_b(candTree, G, S),
      Nat.is_le(Tree.cost(candTree, S), Nat.add(n, sum)), hend)
  +hcost : {Nat.is_le(Tree.cost(candTree, S), candCost) == True{} : Bool} =
    Fold.OQ.le_cong_r(Tree.cost(candTree, S), Nat.add(n, sum), candCost,
      Equal.sym(Nat, candCost, Nat.add(n, sum), esat),
      Logic.Proof.and_true_r(FVal.FV.valid_b(candTree, G, S),
        Nat.is_le(Tree.cost(candTree, S), Nat.add(n, sum)), hend))
  +hcand_le_ref : {Nat.is_le(candCost, SolveRef.sat_add(inf, n, sum_ref))
                   == True{} : Bool} =
    Fold.OQ.le_cong_l(candCost, Nat.add(n, sum),
      SolveRef.sat_add(inf, n, sum_ref), esat,
      FVal.FV.le_sat_add_of_lt_inf(inf, n, n, sum, sum_ref,
        NatProof.Nat.is_le_refl(n), hsum_le, hlt_inf))
  Tuple{best2,
    Tuple{
      FS.FS.end_step(p, gs, gG, S, n, nodup, floor, inf, g, kids, sum, best,
        SolveFast.dummy_zero(), Nil{}, False{}, gres),
      Tuple{
        FVal.FV.best_ok_better(limit, G, S, candCost, candTree, best,
          hvalid, hcost, hok),
        Tuple{
          Fold.OQ.better_le_best(candCost, candTree, best),
          NatProof.Nat.is_le_trans(Eval.Eval.cost_of(best2), candCost,
            SolveRef.sat_add(inf, n, sum_ref),
            Fold.OQ.better_le_cand(candCost, candTree, best),
            hcand_le_ref)}}}}

def FOpt.live_group_two_or_class(nodup: Bool, -gres: SolveFast.GuessRes,
    +p: Nat, +gs: SolveFast.GList, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +floor: Nat, +inf: Nat, +g: +List<Nat>, +fb: +List<Feedback.Color>,
    +w: +List<Nat>, +w2: +List<Nat>, +restg: +List<Groups.Group>,
    +done_rev: +List<Groups.Group>, +kids: +List<Tree.Child>, +sum: Nat,
    +sum_ref: Nat, +best: SolveRef.Best, +limit: Nat,
    bounds: MV.MV.Bounds(p,
              MV.MV.next_groups(Groups.Group{fb, w <> (w2 <> Nil{})} <> restg)),
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h3: {Nat.is_lt(3n, inf) == True{} : Bool},
    +ag: {FO.FO.all_in_jobs_b(
            MV.MV.next_groups(Groups.Group{fb, w <> (w2 <> Nil{})} <> restg), G)
          == True{} : Bool},
    +ng: {FN.FN.nodup_ok_jobs(nodup,
            MV.MV.next_groups(Groups.Group{fb, w <> (w2 <> Nil{})} <> restg))
          == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    +hok: {FVal.FV.best_ok_b(limit, G, S, best) == True{} : Bool},
    +hd: {SolveFast.is_floor_hit(nodup, floor, best) == False{} : Bool},
    +alive: {Nat.is_lt(
               Nat.add(sum,
                 SolveFast.lower_bound(Groups.len_words(S),
                   Groups.Group{fb, w <> (w2 <> Nil{})} <> restg)),
               Eval.Eval.cost_of(best)) == True{} : Bool},
    +hsum_le: {Nat.is_le(sum, sum_ref) == True{} : Bool},
    +hm: {FVal.FV.kids_match_b(G, done_rev, kids) == True{} : Bool},
    +hcs: {Nat.is_le(FVal.FV.kids_cost_sum(done_rev, kids), sum)
           == True{} : Bool},
    ec: FOpt.EClass(p, inf, G, nodup,
          Groups.Group{fb, w <> (w2 <> Nil{})} <> restg),
    rec_two:
      @nd: {nodup == True{} : Bool} ->
      MV.MV.Bounds(p, MV.MV.next_groups(restg)) ->
      FOpt.EClass(p, inf, G, True{}, restg) ->
      {FO.FO.all_in_jobs_b(MV.MV.next_groups(restg), G) == True{} : Bool} ->
      {FN.FN.nodup_ok_jobs(True{}, MV.MV.next_groups(restg)) == True{} : Bool} ->
      {Nat.is_lt(
         Nat.add(SolveRef.sat_add(inf, sum, 3n),
           SolveFast.lower_bound(Groups.len_words(S), restg)),
         Eval.Eval.cost_of(best)) == True{} : Bool} ->
      {Nat.is_le(SolveRef.sat_add(inf, sum, 3n),
         SolveRef.sat_add(inf, sum_ref,
           Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, w <> (w2 <> Nil{})))))
       == True{} : Bool} ->
      {FVal.FV.kids_match_b(G, Groups.Group{fb, w <> (w2 <> Nil{})} <> done_rev,
         Tree.Child{fb, SolveFast.two_tree(w, w2)} <> kids) == True{} : Bool} ->
      {Nat.is_le(
         FVal.FV.kids_cost_sum(Groups.Group{fb, w <> (w2 <> Nil{})} <> done_rev,
           Tree.Child{fb, SolveFast.two_tree(w, w2)} <> kids),
         SolveRef.sat_add(inf, sum, 3n)) == True{} : Bool} ->
      FOpt.StepRes(p, gs, G, S, True{}, floor, inf, g,
        List.append(&2, SolveFast.Item,
          SolveFast.group_items(True{}, Groups.len_words(S), restg),
          SolveFast.End{} <> Nil{}),
        Tree.Child{fb, SolveFast.two_tree(w, w2)} <> kids,
        SolveRef.sat_add(inf, sum, 3n), best, gres, limit,
        Fold.OQ.ks_cost(inf, S,
          Eval.Eval.items(p, G, S, g, restg, Nil{},
            SolveRef.sat_add(inf, sum_ref,
              Eval.Eval.cost_of(
                FS.FS.ref_run_at(p, inf, G, w <> (w2 <> Nil{})))), inf))),
    rec_cls:
      MV.MV.Bounds(p, MV.MV.next_groups(restg)) ->
      FOpt.EClass(p, inf, G, False{}, restg) ->
      {FO.FO.all_in_jobs_b(MV.MV.next_groups(restg), G) == True{} : Bool} ->
      {FN.FN.nodup_ok_jobs(False{}, MV.MV.next_groups(restg)) == True{} : Bool} ->
      {Nat.is_lt(
         Nat.add(
           SolveRef.sat_add(inf, sum,
             Eval.Eval.cost_of(
               FS.FS.run_child_from(p, inf, G, w <> (w2 <> Nil{}), False{},
                 SolveFast.dummy_inf(FS.FS.child_cutoff(best, sum,
                   SolveFast.lower_bound(Groups.len_words(S), restg)))))),
           SolveFast.lower_bound(Groups.len_words(S), restg)),
         Eval.Eval.cost_of(best)) == True{} : Bool} ->
      {Nat.is_le(
         SolveRef.sat_add(inf, sum,
           Eval.Eval.cost_of(
             FS.FS.run_child_from(p, inf, G, w <> (w2 <> Nil{}), False{},
               SolveFast.dummy_inf(FS.FS.child_cutoff(best, sum,
                 SolveFast.lower_bound(Groups.len_words(S), restg)))))),
         SolveRef.sat_add(inf, sum_ref,
           Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, w <> (w2 <> Nil{})))))
       == True{} : Bool} ->
      {FVal.FV.kids_match_b(G, Groups.Group{fb, w <> (w2 <> Nil{})} <> done_rev,
         Tree.Child{fb, Eval.Eval.tree_of(
           FS.FS.run_child_from(p, inf, G, w <> (w2 <> Nil{}), False{},
             SolveFast.dummy_inf(FS.FS.child_cutoff(best, sum,
               SolveFast.lower_bound(Groups.len_words(S), restg)))))} <> kids)
       == True{} : Bool} ->
      {Nat.is_le(
         FVal.FV.kids_cost_sum(Groups.Group{fb, w <> (w2 <> Nil{})} <> done_rev,
           Tree.Child{fb, Eval.Eval.tree_of(
             FS.FS.run_child_from(p, inf, G, w <> (w2 <> Nil{}), False{},
               SolveFast.dummy_inf(FS.FS.child_cutoff(best, sum,
                 SolveFast.lower_bound(Groups.len_words(S), restg)))))} <> kids),
         SolveRef.sat_add(inf, sum,
           Eval.Eval.cost_of(
             FS.FS.run_child_from(p, inf, G, w <> (w2 <> Nil{}), False{},
               SolveFast.dummy_inf(FS.FS.child_cutoff(best, sum,
                 SolveFast.lower_bound(Groups.len_words(S), restg)))))))
       == True{} : Bool} ->
      FOpt.StepRes(p, gs, G, S, False{}, floor, inf, g,
        List.append(&2, SolveFast.Item,
          SolveFast.group_items(False{}, Groups.len_words(S), restg),
          SolveFast.End{} <> Nil{}),
        Tree.Child{fb, Eval.Eval.tree_of(
          FS.FS.run_child_from(p, inf, G, w <> (w2 <> Nil{}), False{},
            SolveFast.dummy_inf(FS.FS.child_cutoff(best, sum,
              SolveFast.lower_bound(Groups.len_words(S), restg)))))} <> kids,
        SolveRef.sat_add(inf, sum,
          Eval.Eval.cost_of(
            FS.FS.run_child_from(p, inf, G, w <> (w2 <> Nil{}), False{},
              SolveFast.dummy_inf(FS.FS.child_cutoff(best, sum,
                SolveFast.lower_bound(Groups.len_words(S), restg)))))),
        best, gres, limit,
        Fold.OQ.ks_cost(inf, S,
          Eval.Eval.items(p, G, S, g, restg, Nil{},
            SolveRef.sat_add(inf, sum_ref,
              Eval.Eval.cost_of(
                FS.FS.ref_run_at(p, inf, G, w <> (w2 <> Nil{})))), inf)))) ->
  FOpt.StepRes(p, gs, G, S, nodup, floor, inf, g,
    List.append(&2, SolveFast.Item,
      SolveFast.group_items(nodup, Groups.len_words(S),
        Groups.Group{fb, w <> (w2 <> Nil{})} <> restg),
      SolveFast.End{} <> Nil{}),
    kids, sum, best, gres, limit,
    Fold.OQ.ks_cost(inf, S,
      Eval.Eval.items(p, G, S, g, Groups.Group{fb, w <> (w2 <> Nil{})} <> restg,
        Nil{}, sum_ref, inf))):
  match nodup:
    case True{}:
      (+ble, bt) = bounds
      (eh, et) = ec
      +ws2 : +List<+List<Nat>> = w <> (w2 <> Nil{})
      +ai_ws : {FO.FO.all_in_ref(ws2, G) == True{} : Bool} =
        Logic.Proof.and_true_l(FO.FO.all_in_ref(ws2, G),
          FO.FO.all_in_jobs_b(MV.MV.next_groups(restg), G), ag)
      +ag_rest : {FO.FO.all_in_jobs_b(MV.MV.next_groups(restg), G)
                  == True{} : Bool} =
        Logic.Proof.and_true_r(FO.FO.all_in_ref(ws2, G),
          FO.FO.all_in_jobs_b(MV.MV.next_groups(restg), G), ag)
      +nd2 : {FN.FN.no_dup_ref(ws2) == True{} : Bool} =
        Logic.Proof.and_true_l(FN.FN.no_dup_ref(ws2),
          FN.FN.nodup_ok_jobs(True{}, MV.MV.next_groups(restg)), ng)
      +ng_rest : {FN.FN.nodup_ok_jobs(True{}, MV.MV.next_groups(restg))
                  == True{} : Bool} =
        Logic.Proof.and_true_r(FN.FN.no_dup_ref(ws2),
          FN.FN.nodup_ok_jobs(True{}, MV.MV.next_groups(restg)), ng)
      +w1in : {Tree.member_word(w, G) == True{} : Bool} =
        FO.FO.all_in_head(w, w2 <> Nil{}, G, ai_ws)
      +w2in : {Tree.member_word(w2, G) == True{} : Bool} =
        FO.FO.all_in_head(w2, Nil{}, G,
          FO.FO.all_in_tail(w, w2 <> Nil{}, G, ai_ws))
      FOpt.live_group_two(gres, p, gs, G, S, floor, inf, g, fb, w, w2, restg,
        done_rev, kids, sum, sum_ref, best, limit, ble, hz, h3, w1in, w2in, nd2,
        hbest, alive, hsum_le, hm, hcs,
        alive2 => hsum2 => hm2 => hcs2 =>
          rec_two({==}, bt, et, ag_rest, ng_rest, alive2, hsum2, hm2, hcs2))
    case False{}:
      (+ble, bt) = bounds
      (eh, et) = ec
      +ws2 : +List<+List<Nat>> = w <> (w2 <> Nil{})
      +ag_rest : {FO.FO.all_in_jobs_b(MV.MV.next_groups(restg), G)
                  == True{} : Bool} =
        Logic.Proof.and_true_r(FO.FO.all_in_ref(ws2, G),
          FO.FO.all_in_jobs_b(MV.MV.next_groups(restg), G), ag)
      +ng_rest : {FN.FN.nodup_ok_jobs(False{}, MV.MV.next_groups(restg))
                  == True{} : Bool} =
        Logic.Proof.and_true_r(True{},
          FN.FN.nodup_ok_jobs(False{}, MV.MV.next_groups(restg)), ng)
      MV.MV.use_pair(
        FOpt.StepRes(p, gs, G, S, False{}, floor, inf, g,
          List.append(&2, SolveFast.Item,
            SolveFast.group_items(False{}, Groups.len_words(S),
              Groups.Group{fb, ws2} <> restg),
            SolveFast.End{} <> Nil{}),
          kids, sum, best, gres, limit,
          Fold.OQ.ks_cost(inf, S,
            Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws2} <> restg,
              Nil{}, sum_ref, inf))),
        MV.MV.Bounds(p, MV.MV.next_groups(restg)),
        MV.MV.Bounds(p, MV.MV.next_groups(restg)),
        FOpt.bounds_copy(p, MV.MV.next_groups(restg), bt),
        bt1 => bt2 =>
          FOpt.live_group_class(gres, p, gs, G, S, False{}, floor, inf, g, fb,
            ws2, restg, done_rev, kids, sum, sum_ref, best, limit, bt2, hz,
            hbest, hok, hd, alive, hsum_le, hm, hcs, eh,
            alive2 => hsum2 => hm2 => hcs2 =>
              rec_cls(bt1, et, ag_rest, ng_rest, alive2, hsum2, hm2, hcs2)))

def FOpt.live_groups_ok(-gres: SolveFast.GuessRes, +groups: +List<Groups.Group>,
    +p: Nat, +gs: SolveFast.GList, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +nodup: Bool, +floor: Nat, +inf: Nat, +g: +List<Nat>,
    +done_rev: +List<Groups.Group>,
    +kids: +List<Tree.Child>, +sum: Nat, +sum_ref: Nat, +best: SolveRef.Best,
    +limit: Nat,
    bounds: MV.MV.Bounds(p, MV.MV.next_groups(groups)),
    +wg: {Tree.member_word(g, G) == True{} : Bool},
    +esplit: {FVal.FV.rev_groups(done_rev, groups)
              == Groups.groups_build(g, S, Nil{}) : +List<Groups.Group>},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +h3: {Nat.is_lt(3n, inf) == True{} : Bool},
    +ag: {FO.FO.all_in_jobs_b(MV.MV.next_groups(groups), G) == True{} : Bool},
    +ng: {FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(groups))
          == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    +hok: {FVal.FV.best_ok_b(limit, G, S, best) == True{} : Bool},
    +hd: {SolveFast.is_floor_hit(nodup, floor, best) == False{} : Bool},
    +alive: {Nat.is_lt(
               Nat.add(sum, SolveFast.lower_bound(Groups.len_words(S), groups)),
               Eval.Eval.cost_of(best)) == True{} : Bool},
    +hsum_le: {Nat.is_le(sum, sum_ref) == True{} : Bool},
    +hm: {FVal.FV.kids_match_b(G, done_rev, kids) == True{} : Bool},
    +hcs: {Nat.is_le(FVal.FV.kids_cost_sum(done_rev, kids), sum)
           == True{} : Bool},
    ec: FOpt.EClass(p, inf, G, nodup, groups)) ->
  FOpt.StepRes(p, gs, G, S, nodup, floor, inf, g,
    List.append(&2, SolveFast.Item,
      SolveFast.group_items(nodup, Groups.len_words(S), groups),
      SolveFast.End{} <> Nil{}),
    kids, sum, best, gres, limit,
    Fold.OQ.ks_cost(inf, S,
      Eval.Eval.items(p, G, S, g, groups, Nil{}, sum_ref, inf))):
  match groups:
    case Nil{}:
      FOpt.live_group_end(gres, p, gs, G, S, nodup, floor, inf, g, done_rev,
        kids, sum, sum_ref, best, limit, wg, esplit, hbest, hok, alive,
        hsum_le, hm, hcs)
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
              +ng_rest : {FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(restg))
                          == True{} : Bool} =
                Logic.Proof.and_true_r(FN.FN.nodup_ok(nodup, Nil{}),
                  FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(restg)), ng)
              +tlb : Nat = SolveFast.lower_bound(Groups.len_words(S), restg)
              +search : SolveRef.Best =
                FS.FS.run_child_from(p, inf, G, Nil{}, nodup,
                  SolveFast.dummy_inf(FS.FS.child_cutoff(best, sum, tlb)))
              +sr : Nat =
                SolveRef.sat_add(inf, sum_ref,
                  Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, Nil{})))
              MV.MV.use_pair(
                FOpt.StepRes(p, gs, G, S, nodup, floor, inf, g,
                  List.append(&2, SolveFast.Item,
                    SolveFast.group_items(nodup, Groups.len_words(S),
                      Groups.Group{fb, Nil{}} <> restg),
                    SolveFast.End{} <> Nil{}),
                  kids, sum, best, gres, limit,
                  Fold.OQ.ks_cost(inf, S,
                    Eval.Eval.items(p, G, S, g,
                      Groups.Group{fb, Nil{}} <> restg, Nil{}, sum_ref, inf))),
                MV.MV.Bounds(p, MV.MV.next_groups(restg)),
                MV.MV.Bounds(p, MV.MV.next_groups(restg)),
                FOpt.bounds_copy(p, MV.MV.next_groups(restg), bt),
                bt1 => bt2 =>
                  FOpt.live_group_class(gres, p, gs, G, S, nodup, floor, inf, g,
                    fb, Nil{}, restg, done_rev, kids, sum, sum_ref, best, limit,
                    bt2, hz, hbest, hok, hd, alive, hsum_le, hm, hcs, eh,
                    alive2 => hsum2 => hm2 => hcs2 =>
                      FOpt.live_groups_ok(gres, restg, p, gs, G, S, nodup, floor, inf,
                        g, Groups.Group{fb, Nil{}} <> done_rev,
                        Tree.Child{fb, Eval.Eval.tree_of(search)} <> kids,
                        SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(search)),
                        sr, best, limit, bt1, wg, esplit, hz, h1, h3, ag_rest,
                        ng_rest, hbest, hok, hd, alive2, hsum2, hm2, hcs2, et)))
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
                  +ng_rest : {FN.FN.nodup_ok_jobs(nodup,
                                MV.MV.next_groups(restg)) == True{} : Bool} =
                    Logic.Proof.and_true_r(FN.FN.nodup_ok(nodup, w <> Nil{}),
                      FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(restg)), ng)
                  +win : {Tree.member_word(w, G) == True{} : Bool} =
                    FO.FO.all_in_head(w, Nil{}, G, ai_ws)
                  +sr : Nat =
                    SolveRef.sat_add(inf, sum_ref,
                      Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, w <> Nil{})))
                  FOpt.live_group_one(gres, p, gs, G, S, nodup, floor, inf, g,
                    fb, w, restg, done_rev, kids, sum, sum_ref, best, limit,
                    ble, h1, win, hbest, alive, hsum_le, hm, hcs,
                    alive2 => hsum2 => hm2 => hcs2 =>
                      FOpt.live_groups_ok(gres, restg, p, gs, G, S, nodup, floor, inf,
                        g, Groups.Group{fb, w <> Nil{}} <> done_rev,
                        Tree.Child{fb, Tree.Node{w, Nil{}}} <> kids,
                        SolveRef.sat_add(inf, sum, 1n), sr, best, limit, bt, wg,
                        esplit, hz, h1, h3, ag_rest, ng_rest, hbest, hok, hd,
                        alive2, hsum2, hm2, hcs2, et))
                case Con{+w2, +wt2}:
                  match wt2:
                    case Nil{}:
                      +ws2 : +List<+List<Nat>> = w <> (w2 <> Nil{})
                      +tlb : Nat =
                        SolveFast.lower_bound(Groups.len_words(S), restg)
                      +search : SolveRef.Best =
                        FS.FS.run_child_from(p, inf, G, ws2, False{},
                          SolveFast.dummy_inf(
                            FS.FS.child_cutoff(best, sum, tlb)))
                      +sr : Nat =
                        SolveRef.sat_add(inf, sum_ref,
                          Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, ws2)))
                      FOpt.live_group_two_or_class(nodup, gres, p, gs, G, S,
                        floor, inf, g, fb, w, w2, restg, done_rev, kids, sum,
                        sum_ref, best, limit, bounds, hz, h3, ag, ng, hbest,
                        hok, hd, alive, hsum_le, hm, hcs, ec,
                        end => bt => et => ag_rest => ng_rest =>
                        alive2 => hsum2 => hm2 => hcs2 =>
                          FOpt.live_groups_ok(gres, restg, p, gs, G, S, True{},
                            floor, inf, g,
                            Groups.Group{fb, ws2} <> done_rev,
                            Tree.Child{fb, SolveFast.two_tree(w, w2)} <> kids,
                            SolveRef.sat_add(inf, sum, 3n), sr, best, limit,
                            bt, wg, esplit, hz, h1, h3, ag_rest, ng_rest,
                            hbest, hok,
                            Equal.trans(Bool,
                              SolveFast.is_floor_hit(True{}, floor, best),
                              SolveFast.is_floor_hit(nodup, floor, best),
                              False{},
                              Equal.cong(Bool, Bool,
                                nd0 => SolveFast.is_floor_hit(nd0, floor, best),
                                True{}, nodup,
                                Equal.sym(Bool, nodup, True{}, end)),
                              hd),
                            alive2, hsum2, hm2, hcs2, et),
                        bt1 => et => ag_rest => ng_rest =>
                        alive2 => hsum2 => hm2 => hcs2 =>
                          FOpt.live_groups_ok(gres, restg, p, gs, G, S, False{},
                            floor, inf, g,
                            Groups.Group{fb, ws2} <> done_rev,
                            Tree.Child{fb, Eval.Eval.tree_of(search)} <> kids,
                            SolveRef.sat_add(inf, sum,
                              Eval.Eval.cost_of(search)),
                            sr, best, limit, bt1, wg, esplit, hz, h1, h3,
                            ag_rest, ng_rest, hbest, hok, {==}, alive2, hsum2,
                            hm2, hcs2, et))
                    case Con{+w3, +wt3}:
                      (+ble, bt) = bounds
                      (eh, et) = ec
                      +ws3 : +List<+List<Nat>> = w <> (w2 <> (w3 <> wt3))
                      +ag_rest : {FO.FO.all_in_jobs_b(
                                    MV.MV.next_groups(restg), G)
                                  == True{} : Bool} =
                        Logic.Proof.and_true_r(FO.FO.all_in_ref(ws3, G),
                          FO.FO.all_in_jobs_b(MV.MV.next_groups(restg), G), ag)
                      +ng_rest : {FN.FN.nodup_ok_jobs(nodup,
                                    MV.MV.next_groups(restg)) == True{} : Bool} =
                        Logic.Proof.and_true_r(FN.FN.nodup_ok(nodup, ws3),
                          FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(restg)),
                          ng)
                      +tlb : Nat =
                        SolveFast.lower_bound(Groups.len_words(S), restg)
                      +search : SolveRef.Best =
                        FS.FS.run_child_from(p, inf, G, ws3, nodup,
                          SolveFast.dummy_inf(
                            FS.FS.child_cutoff(best, sum, tlb)))
                      +sr : Nat =
                        SolveRef.sat_add(inf, sum_ref,
                          Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, ws3)))
                      MV.MV.use_pair(
                        FOpt.StepRes(p, gs, G, S, nodup, floor, inf, g,
                          List.append(&2, SolveFast.Item,
                            SolveFast.group_items(nodup, Groups.len_words(S),
                              Groups.Group{fb, ws3} <> restg),
                            SolveFast.End{} <> Nil{}),
                          kids, sum, best, gres, limit,
                          Fold.OQ.ks_cost(inf, S,
                            Eval.Eval.items(p, G, S, g,
                              Groups.Group{fb, ws3} <> restg,
                              Nil{}, sum_ref, inf))),
                        MV.MV.Bounds(p, MV.MV.next_groups(restg)),
                        MV.MV.Bounds(p, MV.MV.next_groups(restg)),
                        FOpt.bounds_copy(p, MV.MV.next_groups(restg), bt),
                        bt1 => bt2 =>
                          FOpt.live_group_class(gres, p, gs, G, S, nodup, floor,
                            inf, g, fb, ws3, restg, done_rev, kids, sum,
                            sum_ref, best, limit, bt2, hz, hbest, hok, hd,
                            alive, hsum_le, hm, hcs, eh,
                            alive2 => hsum2 => hm2 => hcs2 =>
                              FOpt.live_groups_ok(gres, restg, p, gs, G, S, nodup,
                                floor, inf, g,
                                Groups.Group{fb, ws3} <> done_rev,
                                Tree.Child{fb, Eval.Eval.tree_of(search)}
                                  <> kids,
                                SolveRef.sat_add(inf, sum,
                                  Eval.Eval.cost_of(search)),
                                sr, best, limit, bt1, wg, esplit, hz, h1, h3,
                                ag_rest, ng_rest, hbest, hok, hd, alive2,
                                hsum2, hm2, hcs2, et)))

# ---------------------------------------------------------------------------
# Stepping one guess (`schedule_fguess`, `schedule_one_guess`, `guess_items`)
# ---------------------------------------------------------------------------

def FOpt.step_res_to_block(+p: Nat, +gs: SolveFast.GList, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +nodup: Bool, +floor: Nat, +inf: Nat,
    +g: +List<Nat>, +groups: +List<Groups.Group>, +cs: +List<SolveFast.Item>,
    +best: SolveRef.Best, -gres: SolveFast.GuessRes, +limit: Nat,
    r: FOpt.StepRes(p, gs, G, S, nodup, floor, inf, Nil{}, cs, Nil{}, 0n,
         best, gres, limit,
         Fold.OQ.ks_cost(inf, S,
           Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf)))) ->
  FOpt.StepRes(p, gs, G, S, nodup, floor, inf, Nil{}, cs, Nil{}, 0n,
    best, gres, limit,
    Eval.Eval.cost_of(Eval.Eval.block(p, G, S, g, inf, groups, best))):
  match r:
    case Tuple{+best2, p1}:
      match p1:
        case Tuple{+eq2, p2}:
          match p2:
            case Tuple{+hok2, p3}:
              match p3:
                case Tuple{+hleb, hlecc}:
                  +ks : Eval.KS =
                    Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf)
                  +cc : Nat = Fold.OQ.ks_cost(inf, S, ks)
                  +ct : Tree.Tree = Fold.OQ.ks_tree(g, ks)
                  +hlet : {Nat.is_le(Eval.Eval.cost_of(best2),
                             Eval.Eval.cost_of(
                               Eval.Eval.block(p, G, S, g, inf, groups, best)))
                           == True{} : Bool} =
                    Fold.OQ.le_cong_r(Eval.Eval.cost_of(best2),
                      Eval.Eval.cost_of(SolveRef.better(cc, ct, best)),
                      Eval.Eval.cost_of(
                        Eval.Eval.block(p, G, S, g, inf, groups, best)),
                      Equal.sym(Nat,
                        Eval.Eval.cost_of(
                          Eval.Eval.block(p, G, S, g, inf, groups, best)),
                        Eval.Eval.cost_of(SolveRef.better(cc, ct, best)),
                        Fold.OQ.block_cost_eq(inf, g, S, ks, best)),
                      FVal.FV.le_better_of_le_both(Eval.Eval.cost_of(best2),
                        cc, ct, best, hlecc, hleb))
                  Tuple{best2, Tuple{eq2, Tuple{hok2, Tuple{hleb, hlet}}}}

def FOpt.schedule_fguess_lb_ok(-gres: SolveFast.GuessRes, +p: Nat,
    +gs: SolveFast.GList, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +nodup: Bool, +floor: Nat, +inf: Nat, +g: +List<Nat>,
    +fgroups: +List<SolveFast.FGroup>, +best: SolveRef.Best, +limit: Nat,
    skip: Bool,
    +esk: {skip == SolveFast.skippable(best,
             SolveFast.fgroups_lb(nodup, Groups.len_words(S), fgroups)) : Bool},
    +wg: {Tree.member_word(g, G) == True{} : Bool},
    +egrp: {FN.FN.fgroups_to_groups(fgroups) == Groups.groups_build(g, S, Nil{})
            : +List<Groups.Group>},
    +lok: {FN.FN.fgroups_lens_ok(fgroups) == True{} : Bool},
    +us: {Groups.groups_smaller(S, FN.FN.fgroups_to_groups(fgroups))
          == True{} : Bool},
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +h3: {Nat.is_lt(3n, inf) == True{} : Bool},
    +ag: {FO.FO.all_in_jobs_b(
            MV.MV.next_groups(FN.FN.fgroups_to_groups(fgroups)), G)
          == True{} : Bool},
    +ng: {FN.FN.nodup_ok_jobs(nodup,
            MV.MV.next_groups(FN.FN.fgroups_to_groups(fgroups)))
          == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    +hok: {FVal.FV.best_ok_b(limit, G, S, best) == True{} : Bool},
    +hd: {SolveFast.is_floor_hit(nodup, floor, best) == False{} : Bool},
    ec: FOpt.EClass(p, inf, G, nodup, FN.FN.fgroups_to_groups(fgroups))) ->
  FOpt.StepRes(p, gs, G, S, nodup, floor, inf, Nil{},
    SolveFast.schedule_fguess_lb(nodup, g, fgroups, Groups.len_words(S), skip),
    Nil{}, 0n, best, gres, limit,
    Eval.Eval.cost_of(
      Eval.Eval.block(p, G, S, g, inf, FN.FN.fgroups_to_groups(fgroups), best))):
  match skip:
    case True{}:
      +n : Nat = Groups.len_words(S)
      +groups : +List<Groups.Group> = FN.FN.fgroups_to_groups(fgroups)
      +lb : Nat = SolveFast.lower_bound(n, groups)
      +elb : {SolveFast.fgroups_lb(nodup, n, fgroups) == lb : Nat} =
        FN.FN.fgroups_lb_eq(nodup, n, fgroups, lok, ng)
      +eskp : {SolveFast.skippable(best, lb) == True{} : Bool} =
        Equal.trans(Bool,
          SolveFast.skippable(best, lb),
          SolveFast.skippable(best, SolveFast.fgroups_lb(nodup, n, fgroups)),
          True{},
          Equal.cong(Nat, Bool, x => SolveFast.skippable(best, x),
            lb, SolveFast.fgroups_lb(nodup, n, fgroups),
            Equal.sym(Nat, SolveFast.fgroups_lb(nodup, n, fgroups), lb, elb)),
          Equal.sym(Bool, True{},
            SolveFast.skippable(best, SolveFast.fgroups_lb(nodup, n, fgroups)),
            esk))
      +beq : {Eval.Eval.block(p, G, S, g, inf, groups, best) == best
              : SolveRef.Best} =
        FLB.FS.block_skip_eq(p, inf, G, S, g, groups, best, us, ele, hz, hbest,
          FLB.FS.skippable_to_le(best, lb, eskp))
      FOpt.step_res_keep(p, gs, G, S, nodup, floor, inf, best, gres, limit,
        Eval.Eval.cost_of(Eval.Eval.block(p, G, S, g, inf, groups, best)),
        hok, hd,
        NatProof.Nat.is_le_eq_r(Eval.Eval.cost_of(best),
          Eval.Eval.cost_of(best),
          Eval.Eval.cost_of(Eval.Eval.block(p, G, S, g, inf, groups, best)),
          Equal.cong(SolveRef.Best, Nat, Eval.Eval.cost_of, best,
            Eval.Eval.block(p, G, S, g, inf, groups, best),
            Equal.sym(SolveRef.Best,
              Eval.Eval.block(p, G, S, g, inf, groups, best), best, beq)),
          NatProof.Nat.is_le_refl(Eval.Eval.cost_of(best))))
    case False{}:
      +n : Nat = Groups.len_words(S)
      +gG : SolveFast.GList = SolveFast.glist_of(G, SolveFast.GEnd{})
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
        FOpt.lt_of_skippable_false(best, lb, eskp)
      +body : +List<SolveFast.Item> =
        List.append(&2, SolveFast.Item, SolveFast.group_items(nodup, n, groups),
          SolveFast.End{} <> Nil{})
      +cs_in : +List<SolveFast.Item> =
        SolveFast.schedule_guess_ib(g,
          SolveFast.fgroup_items_build(nodup, n, fgroups,
            SolveFast.End{} <> Nil{}))
      +e_pre : {SolveFast.step(1n+p, gs, 0n, cs_in, gG, S, n, nodup, floor, inf,
                  Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{},
                  False{}, gres)
                == SolveFast.step(1n+p, gs, 0n, body, gG, S, n, nodup, floor,
                     inf, g, Nil{}, 0n, best, SolveFast.dummy_zero(), False{},
                     False{}, gres) : SolveRef.Best} =
        Equal.trans(SolveRef.Best,
          SolveFast.step(1n+p, gs, 0n, cs_in, gG, S, n, nodup, floor, inf,
            Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{}, False{},
            gres),
          SolveFast.step(1n+p, gs, 0n, SolveFast.Begin{g} <> body, gG, S, n,
            nodup, floor, inf, Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(),
            False{}, False{}, gres),
          SolveFast.step(1n+p, gs, 0n, body, gG, S, n, nodup, floor, inf, g,
            Nil{}, 0n, best, SolveFast.dummy_zero(), False{}, False{}, gres),
          Equal.cong(SolveFast.ItemsBound, SolveRef.Best,
            ib => SolveFast.step(1n+p, gs, 0n, SolveFast.schedule_guess_ib(g, ib),
                    gG, S, n, nodup, floor, inf, Nil{}, Nil{}, 0n, best,
                    SolveFast.dummy_zero(), False{}, False{}, gres),
            SolveFast.fgroup_items_build(nodup, n, fgroups,
              SolveFast.End{} <> Nil{}),
            SolveFast.ItemsBound{lb, body},
            FN.FN.fgroup_items_build_eq(nodup, n, fgroups,
              SolveFast.End{} <> Nil{}, lok, ng)),
          FS.FS.begin_succ(p, gs, gG, S, n, nodup, floor, inf, Nil{}, g, Nil{},
            0n, best, SolveFast.dummy_zero(), False{}, False{}, body, gres))
      bounds : MV.MV.Bounds(p, MV.MV.next_groups(groups)) =
        MV.MV.group_bounds(p, S, groups, ele,
          GM.GM.groups_smaller_sound(S, groups, us))
      +ks_c : Nat =
        Fold.OQ.ks_cost(inf, S,
          Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf))
      FOpt.step_res_to_block(p, gs, G, S, nodup, floor, inf, g, groups, cs_in,
        best, gres, limit,
        FOpt.step_res_pre(p, gs, G, S, nodup, floor, inf, Nil{}, cs_in, Nil{},
          0n, g, body, Nil{}, 0n, best, gres, limit, ks_c, ks_c, e_pre,
          NatProof.Nat.is_le_refl(ks_c),
          FOpt.live_groups_ok(gres, groups, p, gs, G, S, nodup, floor, inf, g,
            Nil{}, Nil{}, 0n, 0n, best, limit, bounds, wg, egrp, hz, h1, h3,
            ag, ng, hbest, hok, hd, alive0, {==}, {==}, {==}, ec)))

def FOpt.schedule_fguess_ok(-gres: SolveFast.GuessRes, +p: Nat,
    +gs: SolveFast.GList, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +nodup: Bool, +floor: Nat, +inf: Nat, +g: +List<Nat>,
    +fgroups: +List<SolveFast.FGroup>, +best: SolveRef.Best, +limit: Nat,
    usable: Bool,
    +eus: {usable == Groups.groups_smaller(S, FN.FN.fgroups_to_groups(fgroups))
           : Bool},
    +wg: {Tree.member_word(g, G) == True{} : Bool},
    +egrp: {FN.FN.fgroups_to_groups(fgroups) == Groups.groups_build(g, S, Nil{})
            : +List<Groups.Group>},
    +lok: {FN.FN.fgroups_lens_ok(fgroups) == True{} : Bool},
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +h3: {Nat.is_lt(3n, inf) == True{} : Bool},
    +ag: {FO.FO.all_in_jobs_b(
            MV.MV.next_groups(FN.FN.fgroups_to_groups(fgroups)), G)
          == True{} : Bool},
    +ng: {FN.FN.nodup_ok_jobs(nodup,
            MV.MV.next_groups(FN.FN.fgroups_to_groups(fgroups)))
          == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    +hok: {FVal.FV.best_ok_b(limit, G, S, best) == True{} : Bool},
    +hd: {SolveFast.is_floor_hit(nodup, floor, best) == False{} : Bool},
    ecif: FOpt.EClassIf(usable, p, inf, G, nodup,
            FN.FN.fgroups_to_groups(fgroups))) ->
  FOpt.StepRes(p, gs, G, S, nodup, floor, inf, Nil{},
    SolveFast.schedule_fguess(nodup, g, fgroups, Groups.len_words(S), best,
      usable),
    Nil{}, 0n, best, gres, limit,
    Eval.Eval.cost_of(Eval.Eval.guess_bool(p, G, S, g,
      FN.FN.fgroups_to_groups(fgroups), inf, usable, best))):
  match usable:
    case False{}:
      FOpt.step_res_keep(p, gs, G, S, nodup, floor, inf, best, gres, limit,
        Eval.Eval.cost_of(best), hok, hd,
        NatProof.Nat.is_le_refl(Eval.Eval.cost_of(best)))
    case True{}:
      +n : Nat = Groups.len_words(S)
      +us : {Groups.groups_smaller(S, FN.FN.fgroups_to_groups(fgroups))
             == True{} : Bool} =
        Equal.sym(Bool, True{},
          Groups.groups_smaller(S, FN.FN.fgroups_to_groups(fgroups)), eus)
      FOpt.schedule_fguess_lb_ok(gres, p, gs, G, S, nodup, floor, inf, g,
        fgroups, best, limit,
        SolveFast.skippable(best, SolveFast.fgroups_lb(nodup, n, fgroups)),
        {==}, wg, egrp, lok, us, ele, hz, h1, h3, ag, ng, hbest, hok, hd, ecif)

def FOpt.eclass_if_transport(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +nodup: Bool,
    +g1: +List<Groups.Group>, +g2: +List<Groups.Group>,
    e: {g1 == g2 : +List<Groups.Group>},
    ecif: FOpt.EClassIf(Groups.groups_smaller(S, g1), p, inf, G, nodup, g1)) ->
  FOpt.EClassIf(Groups.groups_smaller(S, g2), p, inf, G, nodup, g2):
  %e : FOpt.EClassIf(Groups.groups_smaller(S, _), p, inf, G, nodup, _)
  ecif

def FOpt.guess_body_fgroup_ok(-gres: SolveFast.GuessRes, +p: Nat,
    +gs: SolveFast.GList, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +nodup: Bool, +floor: Nat, +inf: Nat, +g: +List<Nat>,
    +best: SolveRef.Best, +limit: Nat,
    +wg: {Tree.member_word(g, G) == True{} : Bool},
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +h3: {Nat.is_lt(3n, inf) == True{} : Bool},
    +ai: {FO.FO.all_in_ref(S, G) == True{} : Bool},
    +nd: {FN.FN.nodup_ok(nodup, S) == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    +hok: {FVal.FV.best_ok_b(limit, G, S, best) == True{} : Bool},
    +hd: {SolveFast.is_floor_hit(nodup, floor, best) == False{} : Bool},
    ecif: FOpt.EClassIf(
            Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
            p, inf, G, nodup, Groups.groups_build(g, S, Nil{}))) ->
  FOpt.StepRes(p, gs, G, S, nodup, floor, inf, Nil{},
    SolveFast.schedule_fguess(nodup, g, SolveFast.fgroups_build_fast(g, S, Nil{}),
      Groups.len_words(S), best,
      SolveFast.fgroups_smaller(Groups.len_words(S),
        SolveFast.fgroups_build_fast(g, S, Nil{}))),
    Nil{}, 0n, best, gres, limit,
    Eval.Eval.cost_of(Eval.Eval.guess(p, G, S, g, inf, best))):
  +n : Nat = Groups.len_words(S)
  +gG : SolveFast.GList = SolveFast.glist_of(G, SolveFast.GEnd{})
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
      FO.FO.all_in_jobs_b(MV.MV.next_groups(groups), G), True{},
      Equal.cong(+List<Groups.Group>, Bool,
        grp => FO.FO.all_in_jobs_b(MV.MV.next_groups(grp), G),
        fg_g, groups, egrp), ag0)
  +ng0 : {FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(groups))
          == True{} : Bool} =
    FN.FN.nodup_ok_next_groups(nodup, groups, S,
      CoverGroups.Cover.all_subseq_nil(g, S), nd)
  +ng : {FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(fg_g)) == True{} : Bool} =
    Equal.trans(Bool,
      FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(fg_g)),
      FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(groups)), True{},
      Equal.cong(+List<Groups.Group>, Bool,
        grp => FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(grp)),
        fg_g, groups, egrp), ng0)
  ecif_fg : FOpt.EClassIf(Groups.groups_smaller(S, fg_g), p, inf, G, nodup, fg_g) =
    FOpt.eclass_if_transport(p, inf, G, S, nodup, groups, fg_g,
      Equal.sym(+List<Groups.Group>, fg_g, groups, egrp), ecif)
  +cs1 : +List<SolveFast.Item> =
    SolveFast.schedule_fguess(nodup, g, fg, n, best,
      SolveFast.fgroups_smaller(n, fg))
  +cs2 : +List<SolveFast.Item> =
    SolveFast.schedule_fguess(nodup, g, fg, n, best,
      Groups.groups_smaller(S, fg_g))
  +e_cs : {SolveFast.step(1n+p, gs, 0n, cs1, gG, S, n, nodup, floor, inf,
             Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{}, False{},
             gres)
           == SolveFast.step(1n+p, gs, 0n, cs2, gG, S, n, nodup, floor, inf,
                Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{},
                False{}, gres) : SolveRef.Best} =
    Equal.cong(Bool, SolveRef.Best,
      u => SolveFast.step(1n+p, gs, 0n,
             SolveFast.schedule_fguess(nodup, g, fg, n, best, u),
             gG, S, n, nodup, floor, inf, Nil{}, Nil{}, 0n, best,
             SolveFast.dummy_zero(), False{}, False{}, gres),
      SolveFast.fgroups_smaller(n, fg), Groups.groups_smaller(S, fg_g),
      FN.FN.fgroups_smaller_eq(S, fg, lok))
  +t1 : Nat =
    Eval.Eval.cost_of(Eval.Eval.guess_bool(p, G, S, g, fg_g, inf,
      Groups.groups_smaller(S, fg_g), best))
  +t2 : Nat = Eval.Eval.cost_of(Eval.Eval.guess(p, G, S, g, inf, best))
  +et : {t1 == t2 : Nat} =
    Equal.cong(+List<Groups.Group>, Nat,
      grp => Eval.Eval.cost_of(Eval.Eval.guess_bool(p, G, S, g, grp, inf,
               Groups.groups_smaller(S, grp), best)),
      fg_g, groups, egrp)
  FOpt.step_res_pre(p, gs, G, S, nodup, floor, inf, Nil{}, cs1, Nil{}, 0n,
    Nil{}, cs2, Nil{}, 0n, best, gres, limit, t1, t2, e_cs,
    NatProof.Nat.is_le_eq_r(t1, t1, t2, et, NatProof.Nat.is_le_refl(t1)),
    FOpt.schedule_fguess_ok(gres, p, gs, G, S, nodup, floor, inf, g, fg, best,
      limit, Groups.groups_smaller(S, fg_g), {==}, wg, egrp, lok, ele, hz, h1,
      h3, ag, ng, hbest, hok, hd, ecif_fg))

def FOpt.schedule_one_lb_ok(-gres: SolveFast.GuessRes, +p: Nat,
    +gs: SolveFast.GList, +G: +List<+List<Nat>>, +w: +List<Nat>,
    +nodup: Bool, +floor: Nat, +inf: Nat, +g: +List<Nat>,
    +best: SolveRef.Best, +limit: Nat, skip: Bool,
    +esk: {skip == SolveFast.skippable(best, 1n) : Bool},
    +wg: {Tree.member_word(g, G) == True{} : Bool},
    +heq: {Feedback.word_eq(g, w) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    +hok: {FVal.FV.best_ok_b(limit, G, w <> Nil{}, best) == True{} : Bool},
    +hd: {SolveFast.is_floor_hit(nodup, floor, best) == False{} : Bool}) ->
  FOpt.StepRes(p, gs, G, w <> Nil{}, nodup, floor, inf, Nil{},
    SolveFast.schedule_one_lb(g, skip), Nil{}, 0n, best, gres, limit,
    Eval.Eval.cost_of(SolveRef.finish_guess(inf, g, Nil{}, 0n, 1n, best))):
  match skip:
    case True{}:
      +le : {Nat.is_le(Eval.Eval.cost_of(best), 1n) == True{} : Bool} =
        FLB.FS.skippable_to_le(best, 1n,
          Equal.sym(Bool, True{}, SolveFast.skippable(best, 1n), esk))
      +beq : {Eval.Eval.block(p, G, w <> Nil{}, g, inf, Nil{}, best) == best
              : SolveRef.Best} =
        FLB.FS.block_skip_eq(p, inf, G, w <> Nil{}, g, Nil{}, best, {==},
          NatProof.Nat.is_le_zero_l(p), hz, hbest, le)
      FOpt.step_res_keep(p, gs, G, w <> Nil{}, nodup, floor, inf, best, gres,
        limit,
        Eval.Eval.cost_of(SolveRef.finish_guess(inf, g, Nil{}, 0n, 1n, best)),
        hok, hd,
        NatProof.Nat.is_le_eq_r(Eval.Eval.cost_of(best),
          Eval.Eval.cost_of(best),
          Eval.Eval.cost_of(SolveRef.finish_guess(inf, g, Nil{}, 0n, 1n, best)),
          Equal.cong(SolveRef.Best, Nat, Eval.Eval.cost_of, best,
            SolveRef.finish_guess(inf, g, Nil{}, 0n, 1n, best),
            Equal.sym(SolveRef.Best,
              SolveRef.finish_guess(inf, g, Nil{}, 0n, 1n, best), best, beq)),
          NatProof.Nat.is_le_refl(Eval.Eval.cost_of(best))))
    case False{}:
      +gG : SolveFast.GList = SolveFast.glist_of(G, SolveFast.GEnd{})
      +best2 : SolveRef.Best = SolveRef.finish_guess(inf, g, Nil{}, 0n, 1n, best)
      +candCost : Nat = SolveRef.sat_add(inf, 1n, 0n)
      +es1 : {candCost == 1n : Nat} = FO.FO.sat_add_one_zero(inf, h1)
      +hd_gw : {Maybe.is_some(&1, Nat, Tree.depth(Tree.Node{g, Nil{}}, w))
                == True{} : Bool} =
        Equal.cong(Maybe<Nat>, Bool, m => Maybe.is_some(&1, Nat, m),
          Tree.depth(Tree.Node{g, Nil{}}, w), Some{1n},
          FVal.FV.depth_eq_word(g, w, Nil{}, heq))
      +hval : {FVal.FV.valid_b(Tree.Node{g, Nil{}}, G, w <> Nil{})
               == True{} : Bool} =
        FO.FO.bool_and_intro(FVal.FV.tree_in_b(Tree.Node{g, Nil{}}, G),
          FVal.FV.all_have_depth_b(Tree.Node{g, Nil{}}, w <> Nil{}),
          FO.FO.bool_and_intro(Tree.member_word(g, G), True{}, wg, {==}),
          FO.FO.bool_and_intro(
            Maybe.is_some(&1, Nat, Tree.depth(Tree.Node{g, Nil{}}, w)),
            True{}, hd_gw, {==}))
      +ec1 : {Tree.cost(Tree.Node{g, Nil{}}, w <> Nil{}) == 1n : Nat} =
        Equal.cong(Maybe<Nat>, Nat,
          m => Nat.add(Maybe.default(&1, Nat, m, 0n), 0n),
          Tree.depth(Tree.Node{g, Nil{}}, w), Some{1n},
          FVal.FV.depth_eq_word(g, w, Nil{}, heq))
      +hcost : {Nat.is_le(Tree.cost(Tree.Node{g, Nil{}}, w <> Nil{}), candCost)
                == True{} : Bool} =
        Fold.OQ.le_cong_l(Tree.cost(Tree.Node{g, Nil{}}, w <> Nil{}), 1n,
          candCost, ec1,
          NatProof.Nat.is_le_eq_r(1n, 1n, candCost,
            Equal.sym(Nat, candCost, 1n, es1), {==}))
      Tuple{best2,
        Tuple{
          Equal.trans(SolveRef.Best,
            SolveFast.step(1n+p, gs, 0n,
              SolveFast.Begin{g} <> (SolveFast.End{} <> Nil{}),
              gG, w <> Nil{}, 1n, nodup, floor, inf, Nil{}, Nil{}, 0n, best,
              SolveFast.dummy_zero(), False{}, False{}, gres),
            SolveFast.step(1n+p, gs, 0n, SolveFast.End{} <> Nil{}, gG,
              w <> Nil{}, 1n, nodup, floor, inf, g, Nil{}, 0n, best,
              SolveFast.dummy_zero(), False{}, False{}, gres),
            SolveFast.step(1n+p, gs, 0n, Nil{}, gG, w <> Nil{}, 1n, nodup,
              floor, inf, Nil{}, Nil{}, 0n, best2, SolveFast.dummy_zero(),
              False{}, SolveFast.is_floor_hit(nodup, floor, best2), gres),
            FS.FS.begin_succ(p, gs, gG, w <> Nil{}, 1n, nodup, floor, inf,
              Nil{}, g, Nil{}, 0n, best, SolveFast.dummy_zero(), False{},
              False{}, SolveFast.End{} <> Nil{}, gres),
            FS.FS.end_step(p, gs, gG, w <> Nil{}, 1n, nodup, floor, inf, g,
              Nil{}, 0n, best, SolveFast.dummy_zero(), Nil{}, False{}, gres)),
          Tuple{
            FVal.FV.best_ok_better(limit, G, w <> Nil{}, candCost,
              Tree.Node{g, Nil{}}, best, hval, hcost, hok),
            Tuple{
              Fold.OQ.better_le_best(candCost, Tree.Node{g, Nil{}}, best),
              NatProof.Nat.is_le_refl(Eval.Eval.cost_of(best2))}}}}

def FOpt.schedule_one_ok(-gres: SolveFast.GuessRes, +p: Nat,
    +gs: SolveFast.GList, +G: +List<+List<Nat>>, +w: +List<Nat>,
    +nodup: Bool, +floor: Nat, +inf: Nat, +g: +List<Nat>,
    +best: SolveRef.Best, +limit: Nat, same: Bool,
    +es: {same == Feedback.word_eq(g, w) : Bool},
    +wg: {Tree.member_word(g, G) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    +hok: {FVal.FV.best_ok_b(limit, G, w <> Nil{}, best) == True{} : Bool},
    +hd: {SolveFast.is_floor_hit(nodup, floor, best) == False{} : Bool}) ->
  FOpt.StepRes(p, gs, G, w <> Nil{}, nodup, floor, inf, Nil{},
    SolveFast.schedule_one_guess(g, best, same), Nil{}, 0n, best, gres, limit,
    Eval.Eval.cost_of(Eval.Eval.guess(p, G, w <> Nil{}, g, inf, best))):
  match same:
    case True{}:
      +eg : {Eval.Eval.guess(p, G, w <> Nil{}, g, inf, best)
             == Feedback.Bool.case(SolveRef.Best, Feedback.word_eq(g, w),
                  SolveRef.finish_guess(inf, g, Nil{}, 0n, 1n, best), best)
             : SolveRef.Best} =
        FO.FO.eval_guess_one(p, G, w, g, inf, best, Feedback.word_eq(g, w))
      +heq : {Feedback.word_eq(g, w) == True{} : Bool} =
        Equal.sym(Bool, True{}, Feedback.word_eq(g, w), es)
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
            Feedback.word_eq(g, w), True{}, heq))
      +t1 : Nat =
        Eval.Eval.cost_of(SolveRef.finish_guess(inf, g, Nil{}, 0n, 1n, best))
      +t2 : Nat =
        Eval.Eval.cost_of(Eval.Eval.guess(p, G, w <> Nil{}, g, inf, best))
      FOpt.step_res_pre(p, gs, G, w <> Nil{}, nodup, floor, inf, Nil{},
        SolveFast.schedule_one_lb(g, SolveFast.skippable(best, 1n)), Nil{}, 0n,
        Nil{}, SolveFast.schedule_one_lb(g, SolveFast.skippable(best, 1n)),
        Nil{}, 0n, best, gres, limit, t1, t2, {==},
        NatProof.Nat.is_le_eq_r(t1, t1, t2,
          Equal.cong(SolveRef.Best, Nat, Eval.Eval.cost_of,
            SolveRef.finish_guess(inf, g, Nil{}, 0n, 1n, best),
            Eval.Eval.guess(p, G, w <> Nil{}, g, inf, best),
            Equal.sym(SolveRef.Best,
              Eval.Eval.guess(p, G, w <> Nil{}, g, inf, best),
              SolveRef.finish_guess(inf, g, Nil{}, 0n, 1n, best), eg2)),
          NatProof.Nat.is_le_refl(t1)),
        FOpt.schedule_one_lb_ok(gres, p, gs, G, w, nodup, floor, inf, g, best,
          limit, SolveFast.skippable(best, 1n), {==}, wg, heq, hz, h1, hbest,
          hok, hd))
    case False{}:
      +eg : {Eval.Eval.guess(p, G, w <> Nil{}, g, inf, best)
             == Feedback.Bool.case(SolveRef.Best, Feedback.word_eq(g, w),
                  SolveRef.finish_guess(inf, g, Nil{}, 0n, 1n, best), best)
             : SolveRef.Best} =
        FO.FO.eval_guess_one(p, G, w, g, inf, best, Feedback.word_eq(g, w))
      +hne : {Feedback.word_eq(g, w) == False{} : Bool} =
        Equal.sym(Bool, False{}, Feedback.word_eq(g, w), es)
      +eg2 : {Eval.Eval.guess(p, G, w <> Nil{}, g, inf, best) == best
              : SolveRef.Best} =
        Equal.trans(SolveRef.Best,
          Eval.Eval.guess(p, G, w <> Nil{}, g, inf, best),
          Feedback.Bool.case(SolveRef.Best, Feedback.word_eq(g, w),
            SolveRef.finish_guess(inf, g, Nil{}, 0n, 1n, best), best),
          best, eg,
          Equal.cong(Bool, SolveRef.Best,
            b => Feedback.Bool.case(SolveRef.Best, b,
                   SolveRef.finish_guess(inf, g, Nil{}, 0n, 1n, best), best),
            Feedback.word_eq(g, w), False{}, hne))
      FOpt.step_res_keep(p, gs, G, w <> Nil{}, nodup, floor, inf, best, gres,
        limit,
        Eval.Eval.cost_of(Eval.Eval.guess(p, G, w <> Nil{}, g, inf, best)),
        hok, hd,
        NatProof.Nat.is_le_eq_r(Eval.Eval.cost_of(best),
          Eval.Eval.cost_of(best),
          Eval.Eval.cost_of(Eval.Eval.guess(p, G, w <> Nil{}, g, inf, best)),
          Equal.cong(SolveRef.Best, Nat, Eval.Eval.cost_of, best,
            Eval.Eval.guess(p, G, w <> Nil{}, g, inf, best),
            Equal.sym(SolveRef.Best,
              Eval.Eval.guess(p, G, w <> Nil{}, g, inf, best), best, eg2)),
          NatProof.Nat.is_le_refl(Eval.Eval.cost_of(best))))

def FOpt.guess_body_ok(-gres: SolveFast.GuessRes, +p: Nat,
    +gs: SolveFast.GList, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +nodup: Bool, +floor: Nat, +inf: Nat, +g: +List<Nat>,
    +best: SolveRef.Best, +limit: Nat,
    +wg: {Tree.member_word(g, G) == True{} : Bool},
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +h3: {Nat.is_lt(3n, inf) == True{} : Bool},
    +ai: {FO.FO.all_in_ref(S, G) == True{} : Bool},
    +nd: {FN.FN.nodup_ok(nodup, S) == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    +hok: {FVal.FV.best_ok_b(limit, G, S, best) == True{} : Bool},
    +hd: {SolveFast.is_floor_hit(nodup, floor, best) == False{} : Bool},
    ecif: FOpt.EClassIf(
            Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
            p, inf, G, nodup, Groups.groups_build(g, S, Nil{}))) ->
  FOpt.StepRes(p, gs, G, S, nodup, floor, inf, Nil{},
    SolveFast.guess_body(nodup, g, S, Groups.len_words(S), best),
    Nil{}, 0n, best, gres, limit,
    Eval.Eval.cost_of(Eval.Eval.guess(p, G, S, g, inf, best))):
  match S:
    case Nil{}:
      FOpt.guess_body_fgroup_ok(gres, p, gs, G, Nil{}, nodup, floor, inf, g,
        best, limit, wg, ele, hz, h1, h3, ai, nd, hbest, hok, hd, ecif)
    case Con{+w, +t}:
      match t:
        case Nil{}:
          +gG : SolveFast.GList = SolveFast.glist_of(G, SolveFast.GEnd{})
          +t2 : Nat =
            Eval.Eval.cost_of(Eval.Eval.guess(p, G, w <> Nil{}, g, inf, best))
          FOpt.step_res_pre(p, gs, G, w <> Nil{}, nodup, floor, inf, Nil{},
            SolveFast.schedule_one_guess(g, best, SolveFast.word_eq_fast(g, w)),
            Nil{}, 0n, Nil{},
            SolveFast.schedule_one_guess(g, best, Feedback.word_eq(g, w)),
            Nil{}, 0n, best, gres, limit, t2, t2,
            Equal.cong(Bool, SolveRef.Best,
              b => SolveFast.step(1n+p, gs, 0n,
                     SolveFast.schedule_one_guess(g, best, b), gG, w <> Nil{},
                     1n, nodup, floor, inf, Nil{}, Nil{}, 0n, best,
                     SolveFast.dummy_zero(), False{}, False{}, gres),
              SolveFast.word_eq_fast(g, w), Feedback.word_eq(g, w),
              FG.FG.word_eq_fast_eq(g, w)),
            NatProof.Nat.is_le_refl(t2),
            FOpt.schedule_one_ok(gres, p, gs, G, w, nodup, floor, inf, g, best,
              limit, Feedback.word_eq(g, w), {==}, wg, hz, h1, hbest, hok, hd))
        case Con{+w2, +t2}:
          FOpt.guess_body_fgroup_ok(gres, p, gs, G, w <> (w2 <> t2), nodup,
            floor, inf, g, best, limit, wg, ele, hz, h1, h3, ai, nd, hbest,
            hok, hd, ecif)

def FOpt.guess_items_mem_ok(-gres: SolveFast.GuessRes, +p: Nat,
    +gs: SolveFast.GList, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +floor: Nat, +inf: Nat, +g: +List<Nat>, +best: SolveRef.Best, +limit: Nat,
    in_s: Bool, +ein: {in_s == SolveFast.member_word_fast(g, S) : Bool},
    +ele2n: {SolveFast.skippable(best,
               Nat.add(Groups.len_words(S), Groups.len_words(S)))
             == True{} : Bool},
    +wg: {Tree.member_word(g, G) == True{} : Bool},
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +h3: {Nat.is_lt(3n, inf) == True{} : Bool},
    +ai: {FO.FO.all_in_ref(S, G) == True{} : Bool},
    +nd: {FN.FN.no_dup_ref(S) == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    +hok: {FVal.FV.best_ok_b(limit, G, S, best) == True{} : Bool},
    +hd: {SolveFast.is_floor_hit(True{}, floor, best) == False{} : Bool},
    ecif: FOpt.EClassIf(
            Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
            p, inf, G, True{}, Groups.groups_build(g, S, Nil{}))) ->
  FOpt.StepRes(p, gs, G, S, True{}, floor, inf, Nil{},
    SolveFast.guess_items_mem(g, S, Groups.len_words(S), best, in_s),
    Nil{}, 0n, best, gres, limit,
    Eval.Eval.cost_of(Eval.Eval.guess(p, G, S, g, inf, best))):
  match in_s:
    case True{}:
      FOpt.guess_body_ok(gres, p, gs, G, S, True{}, floor, inf, g, best, limit,
        wg, ele, hz, h1, h3, ai, nd, hbest, hok, hd, ecif)
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
      FOpt.step_res_keep(p, gs, G, S, True{}, floor, inf, best, gres, limit,
        Eval.Eval.cost_of(Eval.Eval.guess(p, G, S, g, inf, best)), hok, hd,
        NatProof.Nat.is_le_eq_r(Eval.Eval.cost_of(best),
          Eval.Eval.cost_of(best),
          Eval.Eval.cost_of(Eval.Eval.guess(p, G, S, g, inf, best)),
          Equal.cong(SolveRef.Best, Nat, Eval.Eval.cost_of, best,
            Eval.Eval.guess(p, G, S, g, inf, best),
            Equal.sym(SolveRef.Best, Eval.Eval.guess(p, G, S, g, inf, best),
              best, geq)),
          NatProof.Nat.is_le_refl(Eval.Eval.cost_of(best))))

def FOpt.guess_items_nodup_ok(-gres: SolveFast.GuessRes, +p: Nat,
    +gs: SolveFast.GList, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +floor: Nat, +inf: Nat, +g: +List<Nat>, +best: SolveRef.Best, +limit: Nat,
    le_2n: Bool,
    +e2n: {le_2n == SolveFast.skippable(best,
             Nat.add(Groups.len_words(S), Groups.len_words(S))) : Bool},
    +wg: {Tree.member_word(g, G) == True{} : Bool},
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +h3: {Nat.is_lt(3n, inf) == True{} : Bool},
    +ai: {FO.FO.all_in_ref(S, G) == True{} : Bool},
    +nd: {FN.FN.no_dup_ref(S) == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    +hok: {FVal.FV.best_ok_b(limit, G, S, best) == True{} : Bool},
    +hd: {SolveFast.is_floor_hit(True{}, floor, best) == False{} : Bool},
    ecif: FOpt.EClassIf(
            Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
            p, inf, G, True{}, Groups.groups_build(g, S, Nil{}))) ->
  FOpt.StepRes(p, gs, G, S, True{}, floor, inf, Nil{},
    SolveFast.guess_items_nodup(g, S, Groups.len_words(S), best, le_2n),
    Nil{}, 0n, best, gres, limit,
    Eval.Eval.cost_of(Eval.Eval.guess(p, G, S, g, inf, best))):
  match le_2n:
    case False{}:
      FOpt.guess_body_ok(gres, p, gs, G, S, True{}, floor, inf, g, best, limit,
        wg, ele, hz, h1, h3, ai, nd, hbest, hok, hd, ecif)
    case True{}:
      +n : Nat = Groups.len_words(S)
      FOpt.guess_items_mem_ok(gres, p, gs, G, S, floor, inf, g, best, limit,
        SolveFast.member_word_fast(g, S), {==},
        Equal.sym(Bool, True{}, SolveFast.skippable(best, Nat.add(n, n)), e2n),
        wg, ele, hz, h1, h3, ai, nd, hbest, hok, hd, ecif)

def FOpt.guess_items_dup_ok(-gres: SolveFast.GuessRes, +p: Nat,
    +gs: SolveFast.GList, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +floor: Nat, +inf: Nat, +g: +List<Nat>, +best: SolveRef.Best, +limit: Nat,
    pre_skip: Bool,
    +ep: {pre_skip == SolveFast.skippable(best,
            SolveFast.pre_lb(Groups.len_words(S), g, S)) : Bool},
    +wg: {Tree.member_word(g, G) == True{} : Bool},
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +h3: {Nat.is_lt(3n, inf) == True{} : Bool},
    +ai: {FO.FO.all_in_ref(S, G) == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    +hok: {FVal.FV.best_ok_b(limit, G, S, best) == True{} : Bool},
    ecif: FOpt.EClassIf(
            Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
            p, inf, G, False{}, Groups.groups_build(g, S, Nil{}))) ->
  FOpt.StepRes(p, gs, G, S, False{}, floor, inf, Nil{},
    SolveFast.guess_items_go(False{}, g, S, Groups.len_words(S), best,
      pre_skip),
    Nil{}, 0n, best, gres, limit,
    Eval.Eval.cost_of(Eval.Eval.guess(p, G, S, g, inf, best))):
  match pre_skip:
    case True{}:
      +le : {Nat.is_le(Eval.Eval.cost_of(best),
               SolveFast.pre_lb(Groups.len_words(S), g, S)) == True{} : Bool} =
        FLB.FS.skippable_to_le(best,
          SolveFast.pre_lb(Groups.len_words(S), g, S),
          Equal.sym(Bool, True{},
            SolveFast.skippable(best,
              SolveFast.pre_lb(Groups.len_words(S), g, S)), ep))
      +geq : {Eval.Eval.guess(p, G, S, g, inf, best) == best : SolveRef.Best} =
        FLB.FS.pre_guess_skip_eq(p, inf, G, S, g, best, ele, hz, hbest, le)
      FOpt.step_res_keep(p, gs, G, S, False{}, floor, inf, best, gres, limit,
        Eval.Eval.cost_of(Eval.Eval.guess(p, G, S, g, inf, best)), hok, {==},
        NatProof.Nat.is_le_eq_r(Eval.Eval.cost_of(best),
          Eval.Eval.cost_of(best),
          Eval.Eval.cost_of(Eval.Eval.guess(p, G, S, g, inf, best)),
          Equal.cong(SolveRef.Best, Nat, Eval.Eval.cost_of, best,
            Eval.Eval.guess(p, G, S, g, inf, best),
            Equal.sym(SolveRef.Best, Eval.Eval.guess(p, G, S, g, inf, best),
              best, geq)),
          NatProof.Nat.is_le_refl(Eval.Eval.cost_of(best))))
    case False{}:
      FOpt.guess_body_ok(gres, p, gs, G, S, False{}, floor, inf, g, best, limit,
        wg, ele, hz, h1, h3, ai, {==}, hbest, hok, {==}, ecif)

def FOpt.guess_items_ok(-gres: SolveFast.GuessRes, +p: Nat,
    +gs: SolveFast.GList, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +nodup: Bool, +floor: Nat, +inf: Nat, +g: +List<Nat>,
    +best: SolveRef.Best, +limit: Nat,
    +wg: {Tree.member_word(g, G) == True{} : Bool},
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +h3: {Nat.is_lt(3n, inf) == True{} : Bool},
    +ai: {FO.FO.all_in_ref(S, G) == True{} : Bool},
    +nd: {FN.FN.nodup_ok(nodup, S) == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    +hok: {FVal.FV.best_ok_b(limit, G, S, best) == True{} : Bool},
    +hd: {SolveFast.is_floor_hit(nodup, floor, best) == False{} : Bool},
    ecif: FOpt.EClassIf(
            Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
            p, inf, G, nodup, Groups.groups_build(g, S, Nil{}))) ->
  FOpt.StepRes(p, gs, G, S, nodup, floor, inf, Nil{},
    SolveFast.guess_items(nodup, g, S, Groups.len_words(S), best),
    Nil{}, 0n, best, gres, limit,
    Eval.Eval.cost_of(Eval.Eval.guess(p, G, S, g, inf, best))):
  match nodup:
    case True{}:
      +n : Nat = Groups.len_words(S)
      FOpt.guess_items_nodup_ok(gres, p, gs, G, S, floor, inf, g, best, limit,
        SolveFast.skippable(best, Nat.add(n, n)), {==}, wg, ele, hz, h1, h3,
        ai, nd, hbest, hok, hd, ecif)
    case False{}:
      FOpt.guess_items_dup_ok(gres, p, gs, G, S, floor, inf, g, best, limit,
        SolveFast.skippable(best, SolveFast.pre_lb(Groups.len_words(S), g, S)),
        {==}, wg, ele, hz, h1, h3, ai, hbest, hok, ecif)

# ---------------------------------------------------------------------------
# Staged `GList` walk with `FloorMode` and reusable `Buf5`
# ---------------------------------------------------------------------------

type FOpt.FloorMode is Data:
  FloorInit{}
  FloorAfterS{}

def FOpt.floor_val(mode: FOpt.FloorMode, +n: Nat) -> Nat:
  match mode:
    case FloorInit{}:
      SolveFast.init_floor(n)
    case FloorAfterS{}:
      Nat.add(n, n)

def FOpt.floor_inv(mode: FOpt.FloorMode, +p: Nat, +inf: Nat,
    +G: +List<+List<Nat>>, +S: +List<+List<Nat>>, +best: SolveRef.Best) -> Bool:
  match mode:
    case FloorInit{}:
      True{}
    case FloorAfterS{}:
      Nat.is_le(Eval.Eval.cost_of(best),
        Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, S,
          Eval.Eval.dummy_inf(inf))))

def FOpt.floor_inv_mono(mode: FOpt.FloorMode, +p: Nat, +inf: Nat,
    +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +b1: SolveRef.Best, +b2: SolveRef.Best,
    +hle: {Nat.is_le(Eval.Eval.cost_of(b2), Eval.Eval.cost_of(b1))
           == True{} : Bool},
    +hi: {FOpt.floor_inv(mode, p, inf, G, S, b1) == True{} : Bool}) ->
  {FOpt.floor_inv(mode, p, inf, G, S, b2) == True{} : Bool}:
  match mode:
    case FloorInit{}:
      {==}
    case FloorAfterS{}:
      NatProof.Nat.is_le_trans(Eval.Eval.cost_of(b2), Eval.Eval.cost_of(b1),
        Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, S,
          Eval.Eval.dummy_inf(inf))),
        hle, hi)

def FOpt.floor_hit_le_ref(mode: FOpt.FloorMode, +p: Nat, +inf: Nat,
    +G: +List<+List<Nat>>, +S: +List<+List<Nat>>, +nodup: Bool,
    +best: SolveRef.Best,
    +nd: {FN.FN.nodup_ok(nodup, S) == True{} : Bool},
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    +hinv: {FOpt.floor_inv(mode, p, inf, G, S, best) == True{} : Bool},
    +ht: {SolveFast.is_floor_hit(nodup,
            FOpt.floor_val(mode, Groups.len_words(S)), best)
          == True{} : Bool}) ->
  {Nat.is_le(Eval.Eval.cost_of(best),
             Eval.Eval.cost_of(FS.FS.ref_run_at(1n+p, inf, G, S)))
   == True{} : Bool}:
  match mode:
    case FloorInit{}:
      match nodup:
        case False{}:
          Empty.absurd(
            {Nat.is_le(Eval.Eval.cost_of(best),
               Eval.Eval.cost_of(FS.FS.ref_run_at(1n+p, inf, G, S)))
             == True{} : Bool},
            Logic.Proof.false_ne_true(ht))
        case True{}:
          FVal.FV.floor_init_le_ref(p, inf, G, S, best, nd, ele, hz, hbest,
            FLB.FS.skippable_to_le(best,
              SolveFast.init_floor(Groups.len_words(S)), ht))
    case FloorAfterS{}:
      match nodup:
        case False{}:
          Empty.absurd(
            {Nat.is_le(Eval.Eval.cost_of(best),
               Eval.Eval.cost_of(FS.FS.ref_run_at(1n+p, inf, G, S)))
             == True{} : Bool},
            Logic.Proof.false_ne_true(ht))
        case True{}:
          FVal.FV.after_s_floor_le(p, inf, G, S, best, ele, hz, hbest,
            FLB.FS.skippable_to_le(best,
              Nat.add(Groups.len_words(S), Groups.len_words(S)), ht),
            hinv)

def FOpt.walk_pop_unpack(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +nodup: Bool, +mode: FOpt.FloorMode, +inf: Nat, +g: +List<Nat>,
    +t: +List<+List<Nat>>, +tail: SolveFast.GList, +best: SolveRef.Best,
    +limit: Nat, +items: +List<SolveFast.Item>, buf2: SolveFast.Buf5,
    +hbuf2: FH.FH.BufOk(buf2),
    +e_unp: {SolveFast.step(1n+p, SolveFast.glist_of(t, tail), 1n, Nil{},
               SolveFast.glist_of(G, SolveFast.GEnd{}), S, Groups.len_words(S),
               nodup, FOpt.floor_val(mode, Groups.len_words(S)), inf, Nil{},
               Nil{}, 0n, best, SolveFast.dummy_zero(), False{}, False{},
               SolveFast.GuessRes{items, buf2})
             == SolveFast.step(1n+p, SolveFast.glist_of(t, tail), 0n,
                  SolveFast.guess_items(nodup, g, S, Groups.len_words(S), best),
                  SolveFast.glist_of(G, SolveFast.GEnd{}), S,
                  Groups.len_words(S), nodup,
                  FOpt.floor_val(mode, Groups.len_words(S)), inf, Nil{}, Nil{},
                  0n, best, SolveFast.dummy_zero(), False{}, False{},
                  SolveFast.GuessRes{Nil{}, buf2}) : SolveRef.Best},
    r_step: FOpt.StepRes(p, SolveFast.glist_of(t, tail), G, S, nodup,
              FOpt.floor_val(mode, Groups.len_words(S)), inf, Nil{},
              SolveFast.guess_items(nodup, g, S, Groups.len_words(S), best),
              Nil{}, 0n, best, SolveFast.GuessRes{Nil{}, buf2}, limit,
              Eval.Eval.cost_of(Eval.Eval.guess(p, G, S, g, inf, best))),
    rec: @best2: SolveRef.Best -> @buf2: SolveFast.Buf5 -> FH.FH.BufOk(buf2) ->
         {FVal.FV.best_ok_b(limit, G, S, best2) == True{} : Bool} ->
         {Nat.is_le(Eval.Eval.cost_of(best2), Eval.Eval.cost_of(best))
          == True{} : Bool} ->
         {Nat.is_le(Eval.Eval.cost_of(best2),
            Eval.Eval.cost_of(Eval.Eval.guess(p, G, S, g, inf, best)))
          == True{} : Bool} ->
         {FOpt.job_res_b(1n+p, inf, G, S, limit,
            SolveFast.step(1n+p, SolveFast.glist_of(t, tail), 0n, Nil{},
              SolveFast.glist_of(G, SolveFast.GEnd{}), S, Groups.len_words(S),
              nodup, FOpt.floor_val(mode, Groups.len_words(S)), inf,
              Nil{}, Nil{}, 0n, best2, SolveFast.dummy_zero(), False{},
              SolveFast.is_floor_hit(nodup,
                FOpt.floor_val(mode, Groups.len_words(S)), best2),
              SolveFast.GuessRes{Nil{}, buf2})) == True{} : Bool}) ->
  {FOpt.job_res_b(1n+p, inf, G, S, limit,
     SolveFast.step(1n+p, SolveFast.glist_of(t, tail), 1n, Nil{},
       SolveFast.glist_of(G, SolveFast.GEnd{}), S, Groups.len_words(S),
       nodup, FOpt.floor_val(mode, Groups.len_words(S)), inf,
       Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{}, False{},
       SolveFast.GuessRes{items, buf2})) == True{} : Bool}:
  match r_step:
    case Tuple{+best2, p1}:
      match p1:
        case Tuple{+e_step, p2}:
          match p2:
            case Tuple{+hok2, p3}:
              match p3:
                case Tuple{+hleb, hleg}:
                  +n : Nat = Groups.len_words(S)
                  +fl : Nat = FOpt.floor_val(mode, n)
                  +gG : SolveFast.GList = SolveFast.glist_of(G, SolveFast.GEnd{})
                  +gt : SolveFast.GList = SolveFast.glist_of(t, tail)
                  +e_tot : {SolveFast.step(1n+p, gt, 1n, Nil{}, gG, S, n,
                              nodup, fl, inf, Nil{}, Nil{}, 0n, best,
                              SolveFast.dummy_zero(), False{}, False{},
                              SolveFast.GuessRes{items, buf2})
                            == SolveFast.step(1n+p, gt, 0n, Nil{}, gG, S, n,
                                 nodup, fl, inf, Nil{}, Nil{}, 0n, best2,
                                 SolveFast.dummy_zero(), False{},
                                 SolveFast.is_floor_hit(nodup, fl, best2),
                                 SolveFast.GuessRes{Nil{}, buf2})
                            : SolveRef.Best} =
                    Equal.trans(SolveRef.Best,
                      SolveFast.step(1n+p, gt, 1n, Nil{}, gG, S, n, nodup,
                        fl, inf, Nil{}, Nil{}, 0n, best,
                        SolveFast.dummy_zero(), False{}, False{},
                        SolveFast.GuessRes{items, buf2}),
                      SolveFast.step(1n+p, gt, 0n,
                        SolveFast.guess_items(nodup, g, S, n, best), gG, S,
                        n, nodup, fl, inf, Nil{}, Nil{}, 0n, best,
                        SolveFast.dummy_zero(), False{}, False{},
                        SolveFast.GuessRes{Nil{}, buf2}),
                      SolveFast.step(1n+p, gt, 0n, Nil{}, gG, S, n, nodup,
                        fl, inf, Nil{}, Nil{}, 0n, best2,
                        SolveFast.dummy_zero(), False{},
                        SolveFast.is_floor_hit(nodup, fl, best2),
                        SolveFast.GuessRes{Nil{}, buf2}),
                      e_unp, e_step)
                  Equal.trans(Bool,
                    FOpt.job_res_b(1n+p, inf, G, S, limit,
                      SolveFast.step(1n+p, gt, 1n, Nil{}, gG, S, n, nodup,
                        fl, inf, Nil{}, Nil{}, 0n, best,
                        SolveFast.dummy_zero(), False{}, False{},
                        SolveFast.GuessRes{items, buf2})),
                    FOpt.job_res_b(1n+p, inf, G, S, limit,
                      SolveFast.step(1n+p, gt, 0n, Nil{}, gG, S, n, nodup,
                        fl, inf, Nil{}, Nil{}, 0n, best2,
                        SolveFast.dummy_zero(), False{},
                        SolveFast.is_floor_hit(nodup, fl, best2),
                        SolveFast.GuessRes{Nil{}, buf2})),
                    True{},
                    Equal.cong(SolveRef.Best, Bool,
                      x => FOpt.job_res_b(1n+p, inf, G, S, limit, x),
                      SolveFast.step(1n+p, gt, 1n, Nil{}, gG, S, n, nodup,
                        fl, inf, Nil{}, Nil{}, 0n, best,
                        SolveFast.dummy_zero(), False{}, False{},
                        SolveFast.GuessRes{items, buf2}),
                      SolveFast.step(1n+p, gt, 0n, Nil{}, gG, S, n, nodup,
                        fl, inf, Nil{}, Nil{}, 0n, best2,
                        SolveFast.dummy_zero(), False{},
                        SolveFast.is_floor_hit(nodup, fl, best2),
                        SolveFast.GuessRes{Nil{}, buf2}),
                      e_tot),
                    rec(best2, buf2, hbuf2, hok2, hleb, hleg))

def FOpt.walk_pop_go(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +nodup: Bool, +mode: FOpt.FloorMode, +inf: Nat, +g: +List<Nat>,
    +t: +List<+List<Nat>>, +tail: SolveFast.GList, +best: SolveRef.Best,
    +limit: Nat, r: SolveFast.GuessRes,
    +hr: FH.FH.GuessResSpec(
           SolveFast.guess_items(nodup, g, S, Groups.len_words(S), best), r),
    +wg: {Tree.member_word(g, G) == True{} : Bool},
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +h3: {Nat.is_lt(3n, inf) == True{} : Bool},
    +ai: {FO.FO.all_in_ref(S, G) == True{} : Bool},
    +nd: {FN.FN.nodup_ok(nodup, S) == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    +hok: {FVal.FV.best_ok_b(limit, G, S, best) == True{} : Bool},
    +hd: {SolveFast.is_floor_hit(nodup,
            FOpt.floor_val(mode, Groups.len_words(S)), best) == False{} : Bool},
    ecif: FOpt.EClassIf(
            Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
            p, inf, G, nodup, Groups.groups_build(g, S, Nil{})),
    rec: @best2: SolveRef.Best -> @buf2: SolveFast.Buf5 -> FH.FH.BufOk(buf2) ->
         {FVal.FV.best_ok_b(limit, G, S, best2) == True{} : Bool} ->
         {Nat.is_le(Eval.Eval.cost_of(best2), Eval.Eval.cost_of(best))
          == True{} : Bool} ->
         {Nat.is_le(Eval.Eval.cost_of(best2),
            Eval.Eval.cost_of(Eval.Eval.guess(p, G, S, g, inf, best)))
          == True{} : Bool} ->
         {FOpt.job_res_b(1n+p, inf, G, S, limit,
            SolveFast.step(1n+p, SolveFast.glist_of(t, tail), 0n, Nil{},
              SolveFast.glist_of(G, SolveFast.GEnd{}), S, Groups.len_words(S),
              nodup, FOpt.floor_val(mode, Groups.len_words(S)), inf,
              Nil{}, Nil{}, 0n, best2, SolveFast.dummy_zero(), False{},
              SolveFast.is_floor_hit(nodup,
                FOpt.floor_val(mode, Groups.len_words(S)), best2),
              SolveFast.GuessRes{Nil{}, buf2})) == True{} : Bool}) ->
  {FOpt.job_res_b(1n+p, inf, G, S, limit,
     SolveFast.step(1n+p, SolveFast.glist_of(t, tail), 1n, Nil{},
       SolveFast.glist_of(G, SolveFast.GEnd{}), S, Groups.len_words(S),
       nodup, FOpt.floor_val(mode, Groups.len_words(S)), inf,
       Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{}, False{}, r))
   == True{} : Bool}:
  match r:
    case SolveFast.GuessRes{+items, buf2}:
      +n : Nat = Groups.len_words(S)
      +fl : Nat = FOpt.floor_val(mode, n)
      +gG : SolveFast.GList = SolveFast.glist_of(G, SolveFast.GEnd{})
      +gt : SolveFast.GList = SolveFast.glist_of(t, tail)
      +eitems : {items == SolveFast.guess_items(nodup, g, S, n, best)
                 : +List<SolveFast.Item>} =
        Arr.Arr.dpair_l(
          {items == SolveFast.guess_items(nodup, g, S, n, best)
           : +List<SolveFast.Item>},
          FH.FH.BufOk(buf2), hr)
      +hbuf2 : FH.FH.BufOk(buf2) =
        Arr.Arr.dpair_r(
          {items == SolveFast.guess_items(nodup, g, S, n, best)
           : +List<SolveFast.Item>},
          FH.FH.BufOk(buf2), hr)
      +e_unp : {SolveFast.step(1n+p, gt, 1n, Nil{}, gG, S, n, nodup, fl, inf,
                  Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{},
                  False{}, SolveFast.GuessRes{items, buf2})
                == SolveFast.step(1n+p, gt, 0n,
                     SolveFast.guess_items(nodup, g, S, n, best),
                     gG, S, n, nodup, fl, inf, Nil{}, Nil{}, 0n, best,
                     SolveFast.dummy_zero(), False{}, False{},
                     SolveFast.GuessRes{Nil{}, buf2}) : SolveRef.Best} =
        Equal.trans(SolveRef.Best,
          SolveFast.step(1n+p, gt, 1n, Nil{}, gG, S, n, nodup, fl, inf,
            Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{}, False{},
            SolveFast.GuessRes{items, buf2}),
          SolveFast.step(1n+p, gt, 0n, items, gG, S, n, nodup, fl, inf,
            Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{}, False{},
            SolveFast.GuessRes{Nil{}, buf2}),
          SolveFast.step(1n+p, gt, 0n,
            SolveFast.guess_items(nodup, g, S, n, best), gG, S, n, nodup, fl,
            inf, Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{},
            False{}, SolveFast.GuessRes{Nil{}, buf2}),
          FS.FS.unpack_gres_succ(p, gt, gG, S, n, nodup, fl, inf, best, items,
            buf2),
          Equal.cong(+List<SolveFast.Item>, SolveRef.Best,
            cs => SolveFast.step(1n+p, gt, 0n, cs, gG, S, n, nodup, fl, inf,
                    Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{},
                    False{}, SolveFast.GuessRes{Nil{}, buf2}),
            items, SolveFast.guess_items(nodup, g, S, n, best), eitems))
      FOpt.walk_pop_unpack(p, G, S, nodup, mode, inf, g, t, tail, best, limit,
        items, buf2, hbuf2, e_unp,
        FOpt.guess_items_ok(SolveFast.GuessRes{Nil{}, buf2}, p, gt, G, S,
          nodup, fl, inf, g, best, limit, wg, ele, hz, h1, h3, ai, nd,
          hbest, hok, hd, ecif),
        rec)

def FOpt.walk_pop_dup(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +nodup: Bool, +mode: FOpt.FloorMode, +inf: Nat, +g: +List<Nat>,
    +t: +List<+List<Nat>>, +tail: SolveFast.GList, +best: SolveRef.Best,
    +limit: Nat, -buf: SolveFast.Buf5, +hbuf: FH.FH.BufOk(buf),
    dp: &b1: SolveFast.Buf5 -> &b2: SolveFast.Buf5 ->
        {b1 == buf : SolveFast.Buf5} & {b2 == b1 : SolveFast.Buf5},
    +wg: {Tree.member_word(g, G) == True{} : Bool},
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +h3: {Nat.is_lt(3n, inf) == True{} : Bool},
    +ai: {FO.FO.all_in_ref(S, G) == True{} : Bool},
    +nd: {FN.FN.nodup_ok(nodup, S) == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    +hok: {FVal.FV.best_ok_b(limit, G, S, best) == True{} : Bool},
    +hd: {SolveFast.is_floor_hit(nodup,
            FOpt.floor_val(mode, Groups.len_words(S)), best) == False{} : Bool},
    ecif: FOpt.EClassIf(
            Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
            p, inf, G, nodup, Groups.groups_build(g, S, Nil{})),
    rec: @best2: SolveRef.Best -> @buf2: SolveFast.Buf5 -> FH.FH.BufOk(buf2) ->
         {FVal.FV.best_ok_b(limit, G, S, best2) == True{} : Bool} ->
         {Nat.is_le(Eval.Eval.cost_of(best2), Eval.Eval.cost_of(best))
          == True{} : Bool} ->
         {Nat.is_le(Eval.Eval.cost_of(best2),
            Eval.Eval.cost_of(Eval.Eval.guess(p, G, S, g, inf, best)))
          == True{} : Bool} ->
         {FOpt.job_res_b(1n+p, inf, G, S, limit,
            SolveFast.step(1n+p, SolveFast.glist_of(t, tail), 0n, Nil{},
              SolveFast.glist_of(G, SolveFast.GEnd{}), S, Groups.len_words(S),
              nodup, FOpt.floor_val(mode, Groups.len_words(S)), inf,
              Nil{}, Nil{}, 0n, best2, SolveFast.dummy_zero(), False{},
              SolveFast.is_floor_hit(nodup,
                FOpt.floor_val(mode, Groups.len_words(S)), best2),
              SolveFast.GuessRes{Nil{}, buf2})) == True{} : Bool}) ->
  {FOpt.job_res_b(1n+p, inf, G, S, limit,
     SolveFast.step(1n+p, SolveFast.glist_of(t, tail), 1n, Nil{},
       SolveFast.glist_of(G, SolveFast.GEnd{}), S, Groups.len_words(S),
       nodup, FOpt.floor_val(mode, Groups.len_words(S)), inf,
       Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{}, False{},
       SolveFast.guess_items_buf(nodup, g, S, Groups.len_words(S), best, buf)))
   == True{} : Bool}:
  (b1, dp2) = dp
  (b2, pe) = dp2
  (eb1, eb2) = pe
  +eb1_c : {b1 == buf : SolveFast.Buf5} = eb1
  +eb2_c : {b2 == b1 : SolveFast.Buf5} = eb2
  +n : Nat = Groups.len_words(S)
  +fl : Nat = FOpt.floor_val(mode, n)
  +gG : SolveFast.GList = SolveFast.glist_of(G, SolveFast.GEnd{})
  +eb2_buf : {b2 == buf : SolveFast.Buf5} =
    Equal.trans(SolveFast.Buf5, b2, b1, buf, eb2_c, eb1_c)
  +hbuf2 : FH.FH.BufOk(b2) =
    FH.FH.buf_ok_transport(buf, b2,
      Equal.sym(SolveFast.Buf5, b2, buf, eb2_buf), hbuf)
  +hr2 : FH.FH.GuessResSpec(SolveFast.guess_items(nodup, g, S, n, best),
           SolveFast.guess_items_buf(nodup, g, S, n, best, b2)) =
    FH.FH.guess_items_buf_spec(nodup, g, S, n, best, b2, {==}, nd, hbuf2)
  +er : {SolveFast.guess_items_buf(nodup, g, S, n, best, b2)
         == SolveFast.guess_items_buf(nodup, g, S, n, best, b1)
         : SolveFast.GuessRes} =
    Equal.cong(SolveFast.Buf5, SolveFast.GuessRes,
      b => SolveFast.guess_items_buf(nodup, g, S, n, best, b), b2, b1, eb2_c)
  +hr1 : FH.FH.GuessResSpec(SolveFast.guess_items(nodup, g, S, n, best),
           SolveFast.guess_items_buf(nodup, g, S, n, best, b1)) =
    %er : FH.FH.GuessResSpec(SolveFast.guess_items(nodup, g, S, n, best), _)
    hr2
  %eb1_c : {FOpt.job_res_b(1n+p, inf, G, S, limit,
            SolveFast.step(1n+p, SolveFast.glist_of(t, tail), 1n, Nil{}, gG, S,
              n, nodup, fl, inf, Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(),
              False{}, False{}, SolveFast.guess_items_buf(nodup, g, S, n, best, _)))
          == True{} : Bool}
  FOpt.walk_pop_go(p, G, S, nodup, mode, inf, g, t, tail, best, limit,
    SolveFast.guess_items_buf(nodup, g, S, n, best, b1), hr1,
    wg, ele, hz, h1, h3, ai, nd, hbest, hok, hd, ecif, rec)

def FOpt.walk_cons(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +nodup: Bool, +mode: FOpt.FloorMode, +inf: Nat, +g: +List<Nat>,
    +t: +List<+List<Nat>>, +tail: SolveFast.GList, +best: SolveRef.Best,
    +limit: Nat, buf: SolveFast.Buf5, +hbuf: FH.FH.BufOk(buf), dn: Bool,
    +edn: {dn == SolveFast.is_floor_hit(nodup,
                   FOpt.floor_val(mode, Groups.len_words(S)), best) : Bool},
    +wg: {Tree.member_word(g, G) == True{} : Bool},
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +h3: {Nat.is_lt(3n, inf) == True{} : Bool},
    +ai: {FO.FO.all_in_ref(S, G) == True{} : Bool},
    +nd: {FN.FN.nodup_ok(nodup, S) == True{} : Bool},
    +hbest_lim: {Nat.is_le(Eval.Eval.cost_of(best), limit) == True{} : Bool},
    +hlim_inf: {Nat.is_le(limit, inf) == True{} : Bool},
    +hok: {FVal.FV.best_ok_b(limit, G, S, best) == True{} : Bool},
    +hinv: {FOpt.floor_inv(mode, p, inf, G, S, best) == True{} : Bool},
    ecif: FOpt.EClassIf(
            Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
            p, inf, G, nodup, Groups.groups_build(g, S, Nil{})),
    rec: @best2: SolveRef.Best -> @buf2: SolveFast.Buf5 -> FH.FH.BufOk(buf2) ->
         {FVal.FV.best_ok_b(limit, G, S, best2) == True{} : Bool} ->
         {Nat.is_le(Eval.Eval.cost_of(best2), Eval.Eval.cost_of(best))
          == True{} : Bool} ->
         {Nat.is_le(Eval.Eval.cost_of(best2),
            Eval.Eval.cost_of(Eval.Eval.guess(p, G, S, g, inf, best)))
          == True{} : Bool} ->
         {FOpt.job_res_b(1n+p, inf, G, S, limit,
            SolveFast.step(1n+p, SolveFast.glist_of(t, tail), 0n, Nil{},
              SolveFast.glist_of(G, SolveFast.GEnd{}), S, Groups.len_words(S),
              nodup, FOpt.floor_val(mode, Groups.len_words(S)), inf,
              Nil{}, Nil{}, 0n, best2, SolveFast.dummy_zero(), False{},
              SolveFast.is_floor_hit(nodup,
                FOpt.floor_val(mode, Groups.len_words(S)), best2),
              SolveFast.GuessRes{Nil{}, buf2})) == True{} : Bool}) ->
  {FOpt.job_res_b(1n+p, inf, G, S, limit,
     SolveFast.step(1n+p, SolveFast.GTry{g, SolveFast.glist_of(t, tail)},
       0n, Nil{}, SolveFast.glist_of(G, SolveFast.GEnd{}), S,
       Groups.len_words(S), nodup, FOpt.floor_val(mode, Groups.len_words(S)),
       inf, Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{}, dn,
       SolveFast.GuessRes{Nil{}, buf})) == True{} : Bool}:
  match dn:
    case True{}:
      +n : Nat = Groups.len_words(S)
      +fl : Nat = FOpt.floor_val(mode, n)
      +gG : SolveFast.GList = SolveFast.glist_of(G, SolveFast.GEnd{})
      +gt : SolveFast.GList = SolveFast.glist_of(t, tail)
      +hbest : {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool} =
        NatProof.Nat.is_le_trans(Eval.Eval.cost_of(best), limit, inf,
          hbest_lim, hlim_inf)
      +ht : {SolveFast.is_floor_hit(nodup, fl, best) == True{} : Bool} =
        Equal.sym(Bool, True{}, SolveFast.is_floor_hit(nodup, fl, best), edn)
      +hjr : {FOpt.job_res_b(1n+p, inf, G, S, limit, best) == True{} : Bool} =
        FO.FO.bool_and_intro(FVal.FV.best_ok_b(limit, G, S, best),
          Bool.and(Nat.is_le(Eval.Eval.cost_of(best), limit),
            Nat.is_le(Eval.Eval.cost_of(best),
              Eval.Eval.cost_of(FS.FS.ref_run_at(1n+p, inf, G, S)))),
          hok,
          FO.FO.bool_and_intro(Nat.is_le(Eval.Eval.cost_of(best), limit),
            Nat.is_le(Eval.Eval.cost_of(best),
              Eval.Eval.cost_of(FS.FS.ref_run_at(1n+p, inf, G, S))),
            hbest_lim,
            FOpt.floor_hit_le_ref(mode, p, inf, G, S, nodup, best, nd, ele, hz,
              hbest, hinv, ht)))
      Equal.trans(Bool,
        FOpt.job_res_b(1n+p, inf, G, S, limit,
          SolveFast.step(1n+p, SolveFast.GTry{g, gt}, 0n, Nil{}, gG, S, n,
            nodup, fl, inf, Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(),
            False{}, True{}, SolveFast.GuessRes{Nil{}, buf})),
        FOpt.job_res_b(1n+p, inf, G, S, limit, best), True{},
        Equal.cong(SolveRef.Best, Bool,
          x => FOpt.job_res_b(1n+p, inf, G, S, limit, x),
          SolveFast.step(1n+p, SolveFast.GTry{g, gt}, 0n, Nil{}, gG, S, n,
            nodup, fl, inf, Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(),
            False{}, True{}, SolveFast.GuessRes{Nil{}, buf}),
          best,
          FS.FS.done_exit(p, SolveFast.GTry{g, gt}, gG, S, n, nodup, fl, inf,
            best, SolveFast.GuessRes{Nil{}, buf})),
        hjr)
    case False{}:
      +n : Nat = Groups.len_words(S)
      +fl : Nat = FOpt.floor_val(mode, n)
      +gG : SolveFast.GList = SolveFast.glist_of(G, SolveFast.GEnd{})
      +gt : SolveFast.GList = SolveFast.glist_of(t, tail)
      +hbest : {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool} =
        NatProof.Nat.is_le_trans(Eval.Eval.cost_of(best), limit, inf,
          hbest_lim, hlim_inf)
      +hd : {SolveFast.is_floor_hit(nodup, fl, best) == False{} : Bool} =
        Equal.sym(Bool, False{}, SolveFast.is_floor_hit(nodup, fl, best), edn)
      Equal.trans(Bool,
        FOpt.job_res_b(1n+p, inf, G, S, limit,
          SolveFast.step(1n+p, SolveFast.GTry{g, gt}, 0n, Nil{}, gG, S, n,
            nodup, fl, inf, Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(),
            False{}, False{}, SolveFast.GuessRes{Nil{}, buf})),
        FOpt.job_res_b(1n+p, inf, G, S, limit,
          SolveFast.step(1n+p, gt, 1n, Nil{}, gG, S, n, nodup, fl, inf,
            Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{}, False{},
            SolveFast.guess_items_buf(nodup, g, S, n, best, buf))),
        True{},
        Equal.cong(SolveRef.Best, Bool,
          x => FOpt.job_res_b(1n+p, inf, G, S, limit, x),
          SolveFast.step(1n+p, SolveFast.GTry{g, gt}, 0n, Nil{}, gG, S, n,
            nodup, fl, inf, Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(),
            False{}, False{}, SolveFast.GuessRes{Nil{}, buf}),
          SolveFast.step(1n+p, gt, 1n, Nil{}, gG, S, n, nodup, fl, inf,
            Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{}, False{},
            SolveFast.guess_items_buf(nodup, g, S, n, best, buf)),
          FS.FS.pop_guess_succ(p, g, gt, gG, S, n, nodup, fl, inf, best, buf)),
        FOpt.walk_pop_dup(p, G, S, nodup, mode, inf, g, t, tail, best, limit,
          buf, hbuf, FH.FH.buf_dup(buf), wg, ele, hz, h1, h3, ai, nd, hbest,
          hok, hd, ecif, rec))

def FOpt.glist_walk(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +nodup: Bool, +mode: FOpt.FloorMode, +inf: Nat, +ws: +List<+List<Nat>>,
    +tail: SolveFast.GList, +best: SolveRef.Best, +limit: Nat,
    buf: SolveFast.Buf5, +hbuf: FH.FH.BufOk(buf),
    +hg_in: {FO.FO.all_in_ref(ws, G) == True{} : Bool},
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +h3: {Nat.is_lt(3n, inf) == True{} : Bool},
    +ai: {FO.FO.all_in_ref(S, G) == True{} : Bool},
    +nd: {FN.FN.nodup_ok(nodup, S) == True{} : Bool},
    +hbest_lim: {Nat.is_le(Eval.Eval.cost_of(best), limit) == True{} : Bool},
    +hlim_inf: {Nat.is_le(limit, inf) == True{} : Bool},
    +hok: {FVal.FV.best_ok_b(limit, G, S, best) == True{} : Bool},
    +hinv: {FOpt.floor_inv(mode, p, inf, G, S, best) == True{} : Bool},
    f: FOpt.EByGs(p, inf, G, S, nodup, ws),
    k_tail:
      @best_end: SolveRef.Best -> @buf_end: SolveFast.Buf5 ->
      FH.FH.BufOk(buf_end) ->
      {FVal.FV.best_ok_b(limit, G, S, best_end) == True{} : Bool} ->
      {Nat.is_le(Eval.Eval.cost_of(best_end), Eval.Eval.cost_of(best))
       == True{} : Bool} ->
      {Nat.is_le(Eval.Eval.cost_of(best_end),
         Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, ws, best)))
       == True{} : Bool} ->
      {FOpt.job_res_b(1n+p, inf, G, S, limit,
         SolveFast.step(1n+p, tail, 0n, Nil{},
           SolveFast.glist_of(G, SolveFast.GEnd{}), S, Groups.len_words(S),
           nodup, FOpt.floor_val(mode, Groups.len_words(S)), inf,
           Nil{}, Nil{}, 0n, best_end, SolveFast.dummy_zero(), False{},
           SolveFast.is_floor_hit(nodup,
             FOpt.floor_val(mode, Groups.len_words(S)), best_end),
           SolveFast.GuessRes{Nil{}, buf_end})) == True{} : Bool}) ->
  {FOpt.job_res_b(1n+p, inf, G, S, limit,
     SolveFast.step(1n+p, SolveFast.glist_of(ws, tail), 0n, Nil{},
       SolveFast.glist_of(G, SolveFast.GEnd{}), S, Groups.len_words(S),
       nodup, FOpt.floor_val(mode, Groups.len_words(S)), inf,
       Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{},
       SolveFast.is_floor_hit(nodup,
         FOpt.floor_val(mode, Groups.len_words(S)), best),
       SolveFast.GuessRes{Nil{}, buf})) == True{} : Bool}:
  match ws:
    case Nil{}:
      k_tail(best, buf, hbuf, hok,
        NatProof.Nat.is_le_refl(Eval.Eval.cost_of(best)),
        NatProof.Nat.is_le_refl(Eval.Eval.cost_of(best)))
    case Con{+g, +t}:
      (ecif, ft) = f
      +wg : {Tree.member_word(g, G) == True{} : Bool} =
        FO.FO.all_in_head(g, t, G, hg_in)
      +ht_in : {FO.FO.all_in_ref(t, G) == True{} : Bool} =
        FO.FO.all_in_tail(g, t, G, hg_in)
      FOpt.walk_cons(p, G, S, nodup, mode, inf, g, t, tail, best, limit, buf,
        hbuf,
        SolveFast.is_floor_hit(nodup,
          FOpt.floor_val(mode, Groups.len_words(S)), best), {==},
        wg, ele, hz, h1, h3, ai, nd, hbest_lim, hlim_inf, hok, hinv, ecif,
        +best2 => buf2 => hbuf2 => +hok2 => +hleb => +hleg =>
          FOpt.glist_walk(p, G, S, nodup, mode, inf, t, tail, best2, limit,
            buf2, hbuf2, ht_in, ele, hz, h1, h3, ai, nd,
            NatProof.Nat.is_le_trans(Eval.Eval.cost_of(best2),
              Eval.Eval.cost_of(best), limit, hleb, hbest_lim),
            hlim_inf, hok2,
            FOpt.floor_inv_mono(mode, p, inf, G, S, best, best2, hleb, hinv),
            ft,
            +best_end => buf_end => hbuf_end => +hok_end => +hle_b2 => +hle_t =>
              k_tail(best_end, buf_end, hbuf_end, hok_end,
                NatProof.Nat.is_le_trans(Eval.Eval.cost_of(best_end),
                  Eval.Eval.cost_of(best2), Eval.Eval.cost_of(best),
                  hle_b2, hleb),
                NatProof.Nat.is_le_trans(Eval.Eval.cost_of(best_end),
                  Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, t, best2)),
                  Eval.Eval.cost_of(
                    Eval.Eval.guesses(1n+p, G, S, inf, t,
                      Eval.Eval.guess(p, G, S, g, inf, best))),
                  hle_t,
                  FVal.FV.eval_guesses_mono(p, G, S, inf, t, best2,
                    Eval.Eval.guess(p, G, S, g, inf, best), hleg)))))

# ---------------------------------------------------------------------------
# Crossing `GThen` and running `run_child_from` / `run_root_from`
# ---------------------------------------------------------------------------

def FOpt.walk_gthen_after(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +best_mid: SolveRef.Best, +limit: Nat,
    buf2: SolveFast.Buf5, +hbuf2: FH.FH.BufOk(buf2),
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +h3: {Nat.is_lt(3n, inf) == True{} : Bool},
    +ai: {FO.FO.all_in_ref(S, G) == True{} : Bool},
    +nd: {FN.FN.no_dup_ref(S) == True{} : Bool},
    +hmid_lim: {Nat.is_le(Eval.Eval.cost_of(best_mid), limit) == True{} : Bool},
    +hlim_inf: {Nat.is_le(limit, inf) == True{} : Bool},
    +hok_mid: {FVal.FV.best_ok_b(limit, G, S, best_mid) == True{} : Bool},
    +hle_s: {Nat.is_le(Eval.Eval.cost_of(best_mid),
               Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, S,
                 Eval.Eval.dummy_inf(inf)))) == True{} : Bool},
    fG: FOpt.EByGs(p, inf, G, S, True{}, G)) ->
  {FOpt.job_res_b(1n+p, inf, G, S, limit,
     SolveFast.step(1n+p, SolveFast.glist_of(G, SolveFast.GEnd{}), 0n, Nil{},
       SolveFast.glist_of(G, SolveFast.GEnd{}), S, Groups.len_words(S),
       True{}, Nat.add(Groups.len_words(S), Groups.len_words(S)), inf,
       Nil{}, Nil{}, 0n, best_mid, SolveFast.dummy_zero(), False{},
       SolveFast.is_floor_hit(True{},
         Nat.add(Groups.len_words(S), Groups.len_words(S)), best_mid),
       SolveFast.GuessRes{Nil{}, buf2})) == True{} : Bool}:
  +hmid_inf : {Nat.is_le(Eval.Eval.cost_of(best_mid), inf) == True{} : Bool} =
    NatProof.Nat.is_le_trans(Eval.Eval.cost_of(best_mid), limit, inf,
      hmid_lim, hlim_inf)
  FOpt.glist_walk(p, G, S, True{}, FloorAfterS{}, inf, G,
    SolveFast.GEnd{}, best_mid, limit, buf2, hbuf2,
    FVal.FV.all_in_ref_self(G), ele, hz, h1, h3, ai, nd,
    hmid_lim, hlim_inf, hok_mid, hle_s, fG,
    +best_end => buf_end => hbuf_end => +hok_end => +hle_mid => +hle_g =>
      +hg_le_ref : {Nat.is_le(
                      Eval.Eval.cost_of(
                        Eval.Eval.guesses(1n+p, G, S, inf, G, best_mid)),
                      Eval.Eval.cost_of(
                        FS.FS.ref_run_at(1n+p, inf, G, S)))
                    == True{} : Bool} =
        Fold.OQ.le_cong_l(
          Eval.Eval.cost_of(
            Eval.Eval.guesses(1n+p, G, S, inf, G, best_mid)),
          Eval.Eval.cost_of(
            FC.FC.better_best(
              FS.FS.ref_run_at(1n+p, inf, G, S), best_mid)),
          Eval.Eval.cost_of(FS.FS.ref_run_at(1n+p, inf, G, S)),
          Equal.cong(SolveRef.Best, Nat, Eval.Eval.cost_of,
            Eval.Eval.guesses(1n+p, G, S, inf, G, best_mid),
            FC.FC.better_best(
              FS.FS.ref_run_at(1n+p, inf, G, S), best_mid),
            FC.FC.eval_guesses_from(1n+p, inf, G, S, best_mid, ele,
              hmid_inf)),
          FVal.FV.better_best_le_l(
            FS.FS.ref_run_at(1n+p, inf, G, S), best_mid))
      FO.FO.bool_and_intro(FVal.FV.best_ok_b(limit, G, S, best_end),
        Bool.and(Nat.is_le(Eval.Eval.cost_of(best_end), limit),
          Nat.is_le(Eval.Eval.cost_of(best_end),
            Eval.Eval.cost_of(FS.FS.ref_run_at(1n+p, inf, G, S)))),
        hok_end,
        FO.FO.bool_and_intro(
          Nat.is_le(Eval.Eval.cost_of(best_end), limit),
          Nat.is_le(Eval.Eval.cost_of(best_end),
            Eval.Eval.cost_of(FS.FS.ref_run_at(1n+p, inf, G, S))),
          NatProof.Nat.is_le_trans(Eval.Eval.cost_of(best_end),
            Eval.Eval.cost_of(best_mid), limit, hle_mid, hmid_lim),
          NatProof.Nat.is_le_trans(Eval.Eval.cost_of(best_end),
            Eval.Eval.cost_of(
              Eval.Eval.guesses(1n+p, G, S, inf, G, best_mid)),
            Eval.Eval.cost_of(FS.FS.ref_run_at(1n+p, inf, G, S)),
            hle_g, hg_le_ref))))

def FOpt.walk_gthen_false(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +best_mid: SolveRef.Best, +limit: Nat,
    buf_mid: SolveFast.Buf5, +hbuf_mid: FH.FH.BufOk(buf_mid),
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +h3: {Nat.is_lt(3n, inf) == True{} : Bool},
    +ai: {FO.FO.all_in_ref(S, G) == True{} : Bool},
    +nd: {FN.FN.no_dup_ref(S) == True{} : Bool},
    +hmid_lim: {Nat.is_le(Eval.Eval.cost_of(best_mid), limit) == True{} : Bool},
    +hlim_inf: {Nat.is_le(limit, inf) == True{} : Bool},
    +hok_mid: {FVal.FV.best_ok_b(limit, G, S, best_mid) == True{} : Bool},
    +hle_s: {Nat.is_le(Eval.Eval.cost_of(best_mid),
               Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, S,
                 Eval.Eval.dummy_inf(inf)))) == True{} : Bool},
    fG: FOpt.EByGs(p, inf, G, S, True{}, G)) ->
  {FOpt.job_res_b(1n+p, inf, G, S, limit,
     SolveFast.step(1n+p,
       SolveFast.GThen{SolveFast.glist_of(G, SolveFast.GEnd{})}, 0n, Nil{},
       SolveFast.glist_of(G, SolveFast.GEnd{}), S, Groups.len_words(S),
       True{}, SolveFast.init_floor(Groups.len_words(S)), inf,
       Nil{}, Nil{}, 0n, best_mid, SolveFast.dummy_zero(), False{}, False{},
       SolveFast.GuessRes{Nil{}, buf_mid})) == True{} : Bool}:
  match buf_mid:
    case SolveFast.NoBuf{}:
      +n : Nat = Groups.len_words(S)
      +fl : Nat = SolveFast.init_floor(n)
      +gG : SolveFast.GList = SolveFast.glist_of(G, SolveFast.GEnd{})
      Equal.trans(Bool,
        FOpt.job_res_b(1n+p, inf, G, S, limit,
          SolveFast.step(1n+p, SolveFast.GThen{gG}, 0n, Nil{}, gG, S, n,
            True{}, fl, inf, Nil{}, Nil{}, 0n, best_mid,
            SolveFast.dummy_zero(), False{}, False{},
            SolveFast.GuessRes{Nil{}, SolveFast.NoBuf{}})),
        FOpt.job_res_b(1n+p, inf, G, S, limit,
          SolveFast.step(1n+p, gG, 0n, Nil{}, gG, S, n, True{},
            Nat.add(n, n), inf, Nil{}, Nil{}, 0n, best_mid,
            SolveFast.dummy_zero(), False{},
            SolveFast.is_floor_hit(True{}, Nat.add(n, n), best_mid),
            SolveFast.GuessRes{Nil{}, SolveFast.mk_buf(True{}, n, best_mid)})),
        True{},
        Equal.cong(SolveRef.Best, Bool,
          x => FOpt.job_res_b(1n+p, inf, G, S, limit, x),
          SolveFast.step(1n+p, SolveFast.GThen{gG}, 0n, Nil{}, gG, S, n,
            True{}, fl, inf, Nil{}, Nil{}, 0n, best_mid,
            SolveFast.dummy_zero(), False{}, False{},
            SolveFast.GuessRes{Nil{}, SolveFast.NoBuf{}}),
          SolveFast.step(1n+p, gG, 0n, Nil{}, gG, S, n, True{},
            Nat.add(n, n), inf, Nil{}, Nil{}, 0n, best_mid,
            SolveFast.dummy_zero(), False{},
            SolveFast.is_floor_hit(True{}, Nat.add(n, n), best_mid),
            SolveFast.GuessRes{Nil{}, SolveFast.mk_buf(True{}, n, best_mid)}),
          FS.FS.gthen_step(p, gG, gG, S, n, True{}, fl, inf, best_mid,
            SolveFast.GuessRes{Nil{}, SolveFast.NoBuf{}})),
        FOpt.walk_gthen_after(p, inf, G, S, best_mid, limit,
          SolveFast.mk_buf(True{}, n, best_mid),
          FH.FH.mk_buf_ok(True{}, n, best_mid),
          ele, hz, h1, h3, ai, nd, hmid_lim, hlim_inf, hok_mid, hle_s, fG))
    case SolveFast.Buf5{seen, bkts, +gen}:
      +n : Nat = Groups.len_words(S)
      +fl : Nat = SolveFast.init_floor(n)
      +gG : SolveFast.GList = SolveFast.glist_of(G, SolveFast.GEnd{})
      Equal.trans(Bool,
        FOpt.job_res_b(1n+p, inf, G, S, limit,
          SolveFast.step(1n+p, SolveFast.GThen{gG}, 0n, Nil{}, gG, S, n,
            True{}, fl, inf, Nil{}, Nil{}, 0n, best_mid,
            SolveFast.dummy_zero(), False{}, False{},
            SolveFast.GuessRes{Nil{}, SolveFast.Buf5{seen, bkts, gen}})),
        FOpt.job_res_b(1n+p, inf, G, S, limit,
          SolveFast.step(1n+p, gG, 0n, Nil{}, gG, S, n, True{},
            Nat.add(n, n), inf, Nil{}, Nil{}, 0n, best_mid,
            SolveFast.dummy_zero(), False{},
            SolveFast.is_floor_hit(True{}, Nat.add(n, n), best_mid),
            SolveFast.GuessRes{Nil{}, SolveFast.Buf5{seen, bkts, gen}})),
        True{},
        Equal.cong(SolveRef.Best, Bool,
          x => FOpt.job_res_b(1n+p, inf, G, S, limit, x),
          SolveFast.step(1n+p, SolveFast.GThen{gG}, 0n, Nil{}, gG, S, n,
            True{}, fl, inf, Nil{}, Nil{}, 0n, best_mid,
            SolveFast.dummy_zero(), False{}, False{},
            SolveFast.GuessRes{Nil{}, SolveFast.Buf5{seen, bkts, gen}}),
          SolveFast.step(1n+p, gG, 0n, Nil{}, gG, S, n, True{},
            Nat.add(n, n), inf, Nil{}, Nil{}, 0n, best_mid,
            SolveFast.dummy_zero(), False{},
            SolveFast.is_floor_hit(True{}, Nat.add(n, n), best_mid),
            SolveFast.GuessRes{Nil{}, SolveFast.Buf5{seen, bkts, gen}}),
          FS.FS.gthen_step(p, gG, gG, S, n, True{}, fl, inf, best_mid,
            SolveFast.GuessRes{Nil{}, SolveFast.Buf5{seen, bkts, gen}})),
        FOpt.walk_gthen_after(p, inf, G, S, best_mid, limit,
          SolveFast.Buf5{seen, bkts, gen}, hbuf_mid,
          ele, hz, h1, h3, ai, nd, hmid_lim, hlim_inf, hok_mid, hle_s, fG))

def FOpt.walk_gthen(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +best_mid: SolveRef.Best, +limit: Nat,
    buf_mid: SolveFast.Buf5, +hbuf_mid: FH.FH.BufOk(buf_mid), dn: Bool,
    +edn: {dn == SolveFast.is_floor_hit(True{},
                   SolveFast.init_floor(Groups.len_words(S)), best_mid) : Bool},
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +h3: {Nat.is_lt(3n, inf) == True{} : Bool},
    +ai: {FO.FO.all_in_ref(S, G) == True{} : Bool},
    +nd: {FN.FN.no_dup_ref(S) == True{} : Bool},
    +hmid_lim: {Nat.is_le(Eval.Eval.cost_of(best_mid), limit) == True{} : Bool},
    +hlim_inf: {Nat.is_le(limit, inf) == True{} : Bool},
    +hok_mid: {FVal.FV.best_ok_b(limit, G, S, best_mid) == True{} : Bool},
    +hle_s: {Nat.is_le(Eval.Eval.cost_of(best_mid),
               Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, S,
                 Eval.Eval.dummy_inf(inf)))) == True{} : Bool},
    fG: FOpt.EByGs(p, inf, G, S, True{}, G)) ->
  {FOpt.job_res_b(1n+p, inf, G, S, limit,
     SolveFast.step(1n+p,
       SolveFast.GThen{SolveFast.glist_of(G, SolveFast.GEnd{})}, 0n, Nil{},
       SolveFast.glist_of(G, SolveFast.GEnd{}), S, Groups.len_words(S),
       True{}, SolveFast.init_floor(Groups.len_words(S)), inf,
       Nil{}, Nil{}, 0n, best_mid, SolveFast.dummy_zero(), False{}, dn,
       SolveFast.GuessRes{Nil{}, buf_mid})) == True{} : Bool}:
  match dn:
    case True{}:
      +n : Nat = Groups.len_words(S)
      +fl : Nat = SolveFast.init_floor(n)
      +gG : SolveFast.GList = SolveFast.glist_of(G, SolveFast.GEnd{})
      +hmid_inf : {Nat.is_le(Eval.Eval.cost_of(best_mid), inf) == True{} : Bool} =
        NatProof.Nat.is_le_trans(Eval.Eval.cost_of(best_mid), limit, inf,
          hmid_lim, hlim_inf)
      +ht : {SolveFast.is_floor_hit(True{}, fl, best_mid) == True{} : Bool} =
        Equal.sym(Bool, True{},
          SolveFast.is_floor_hit(True{}, fl, best_mid), edn)
      +hjr : {FOpt.job_res_b(1n+p, inf, G, S, limit, best_mid)
              == True{} : Bool} =
        FO.FO.bool_and_intro(FVal.FV.best_ok_b(limit, G, S, best_mid),
          Bool.and(Nat.is_le(Eval.Eval.cost_of(best_mid), limit),
            Nat.is_le(Eval.Eval.cost_of(best_mid),
              Eval.Eval.cost_of(FS.FS.ref_run_at(1n+p, inf, G, S)))),
          hok_mid,
          FO.FO.bool_and_intro(Nat.is_le(Eval.Eval.cost_of(best_mid), limit),
            Nat.is_le(Eval.Eval.cost_of(best_mid),
              Eval.Eval.cost_of(FS.FS.ref_run_at(1n+p, inf, G, S))),
            hmid_lim,
            FVal.FV.floor_init_le_ref(p, inf, G, S, best_mid, nd, ele, hz,
              hmid_inf, FLB.FS.skippable_to_le(best_mid, fl, ht))))
      Equal.trans(Bool,
        FOpt.job_res_b(1n+p, inf, G, S, limit,
          SolveFast.step(1n+p, SolveFast.GThen{gG}, 0n, Nil{}, gG, S, n,
            True{}, fl, inf, Nil{}, Nil{}, 0n, best_mid,
            SolveFast.dummy_zero(), False{}, True{},
            SolveFast.GuessRes{Nil{}, buf_mid})),
        FOpt.job_res_b(1n+p, inf, G, S, limit, best_mid), True{},
        Equal.cong(SolveRef.Best, Bool,
          x => FOpt.job_res_b(1n+p, inf, G, S, limit, x),
          SolveFast.step(1n+p, SolveFast.GThen{gG}, 0n, Nil{}, gG, S, n,
            True{}, fl, inf, Nil{}, Nil{}, 0n, best_mid,
            SolveFast.dummy_zero(), False{}, True{},
            SolveFast.GuessRes{Nil{}, buf_mid}),
          best_mid,
          FS.FS.done_exit(p, SolveFast.GThen{gG}, gG, S, n, True{}, fl, inf,
            best_mid, SolveFast.GuessRes{Nil{}, buf_mid})),
        hjr)
    case False{}:
      FOpt.walk_gthen_false(p, inf, G, S, best_mid, limit, buf_mid, hbuf_mid,
        ele, hz, h1, h3, ai, nd, hmid_lim, hlim_inf, hok_mid, hle_s, fG)

def FOpt.ejob_succ_nodup(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +best0: SolveRef.Best, le_2n: Bool,
    +e2n: {le_2n == SolveFast.skippable(best0,
             Nat.add(Groups.len_words(S), Groups.len_words(S))) : Bool},
    +hb0: {Nat.is_le(Eval.Eval.cost_of(best0), inf) == True{} : Bool},
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +h3: {Nat.is_lt(3n, inf) == True{} : Bool},
    +ai: {FO.FO.all_in_ref(S, G) == True{} : Bool},
    +nd: {FN.FN.no_dup_ref(S) == True{} : Bool},
    fS: FOpt.EByGs(p, inf, G, S, True{}, S),
    fG: FOpt.EByGs(p, inf, G, S, True{}, G)) ->
  {FOpt.job_res_b(1n+p, inf, G, S, Eval.Eval.cost_of(best0),
     SolveFast.step(1n+p,
       SolveFast.child_glist_nodup(S, SolveFast.glist_of(G, SolveFast.GEnd{}),
         le_2n),
       0n, Nil{}, SolveFast.glist_of(G, SolveFast.GEnd{}), S,
       Groups.len_words(S), True{}, SolveFast.init_floor(Groups.len_words(S)),
       inf, Nil{}, Nil{}, 0n, best0, SolveFast.dummy_zero(), False{},
       SolveFast.is_floor_hit(True{}, SolveFast.init_floor(Groups.len_words(S)),
         best0),
       SolveFast.GuessRes{Nil{},
         SolveFast.mk_buf_init(True{}, Groups.len_words(S), best0)}))
   == True{} : Bool}:
  match le_2n:
    case True{}:
      +n : Nat = Groups.len_words(S)
      +limit : Nat = Eval.Eval.cost_of(best0)
      +hok0 : {FVal.FV.best_ok_b(limit, G, S, best0) == True{} : Bool} =
        FVal.FV.best_ok_init(limit, G, S, best0, Nat.ge_refl(limit))
      +h2n0 : {Nat.is_le(limit, Nat.add(n, n)) == True{} : Bool} =
        FLB.FS.skippable_to_le(best0, Nat.add(n, n),
          Equal.sym(Bool, True{},
            SolveFast.skippable(best0, Nat.add(n, n)), e2n))
      FOpt.glist_walk(p, G, S, True{}, FloorInit{}, inf, S,
        SolveFast.GEnd{}, best0, limit,
        SolveFast.mk_buf_init(True{}, n, best0),
        FH.FH.mk_buf_init_ok(True{}, n, best0),
        ai, ele, hz, h1, h3, ai, nd, NatProof.Nat.is_le_refl(limit), hb0,
        hok0, {==}, fS,
        +best_end => buf_end => hbuf_end => +hok_end => +hle_b0 => +hle_s =>
          +h2n_end : {Nat.is_le(Eval.Eval.cost_of(best_end), Nat.add(n, n))
                      == True{} : Bool} =
            NatProof.Nat.is_le_trans(Eval.Eval.cost_of(best_end), limit,
              Nat.add(n, n), hle_b0, h2n0)
          +hs_inf : {Nat.is_le(Eval.Eval.cost_of(best_end),
                       Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, S,
                         Eval.Eval.dummy_inf(inf)))) == True{} : Bool} =
            NatProof.Nat.is_le_trans(Eval.Eval.cost_of(best_end),
              Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, S, best0)),
              Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, S,
                Eval.Eval.dummy_inf(inf))),
              hle_s,
              FVal.FV.eval_guesses_le_from_inf(1n+p, inf, G, S, S, best0, hb0))
          +hle_ref : {Nat.is_le(Eval.Eval.cost_of(best_end),
                        Eval.Eval.cost_of(FS.FS.ref_run_at(1n+p, inf, G, S)))
                      == True{} : Bool} =
            FVal.FV.after_s_floor_le(p, inf, G, S, best_end, ele, hz,
              NatProof.Nat.is_le_trans(Eval.Eval.cost_of(best_end), limit, inf,
                hle_b0, hb0),
              h2n_end, hs_inf)
          FO.FO.bool_and_intro(FVal.FV.best_ok_b(limit, G, S, best_end),
            Bool.and(Nat.is_le(Eval.Eval.cost_of(best_end), limit),
              Nat.is_le(Eval.Eval.cost_of(best_end),
                Eval.Eval.cost_of(FS.FS.ref_run_at(1n+p, inf, G, S)))),
            hok_end,
            FO.FO.bool_and_intro(Nat.is_le(Eval.Eval.cost_of(best_end), limit),
              Nat.is_le(Eval.Eval.cost_of(best_end),
                Eval.Eval.cost_of(FS.FS.ref_run_at(1n+p, inf, G, S))),
              hle_b0, hle_ref)))
    case False{}:
      +n : Nat = Groups.len_words(S)
      +limit : Nat = Eval.Eval.cost_of(best0)
      +hok0 : {FVal.FV.best_ok_b(limit, G, S, best0) == True{} : Bool} =
        FVal.FV.best_ok_init(limit, G, S, best0, Nat.ge_refl(limit))
      FOpt.glist_walk(p, G, S, True{}, FloorInit{}, inf, S,
        SolveFast.GThen{SolveFast.glist_of(G, SolveFast.GEnd{})}, best0, limit,
        SolveFast.mk_buf_init(True{}, n, best0),
        FH.FH.mk_buf_init_ok(True{}, n, best0),
        ai, ele, hz, h1, h3, ai, nd, NatProof.Nat.is_le_refl(limit), hb0,
        hok0, {==}, fS,
        +best_mid => buf_mid => hbuf_mid => +hok_mid => +hle_b0 => +hle_s =>
          +hs_inf : {Nat.is_le(Eval.Eval.cost_of(best_mid),
                       Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, S,
                         Eval.Eval.dummy_inf(inf)))) == True{} : Bool} =
            NatProof.Nat.is_le_trans(Eval.Eval.cost_of(best_mid),
              Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, S, best0)),
              Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, S,
                Eval.Eval.dummy_inf(inf))),
              hle_s,
              FVal.FV.eval_guesses_le_from_inf(1n+p, inf, G, S, S, best0, hb0))
          FOpt.walk_gthen(p, inf, G, S, best_mid, limit, buf_mid, hbuf_mid,
            SolveFast.is_floor_hit(True{}, SolveFast.init_floor(n), best_mid),
            {==}, ele, hz, h1, h3, ai, nd, hle_b0, hb0, hok_mid, hs_inf, fG))

def FOpt.ejob_succ_direct(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +nodup: Bool, +best0: SolveRef.Best,
    buf0: SolveFast.Buf5, +hbuf0: FH.FH.BufOk(buf0),
    +hb0: {Nat.is_le(Eval.Eval.cost_of(best0), inf) == True{} : Bool},
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +h3: {Nat.is_lt(3n, inf) == True{} : Bool},
    +ai: {FO.FO.all_in_ref(S, G) == True{} : Bool},
    +nd: {FN.FN.nodup_ok(nodup, S) == True{} : Bool},
    fG: FOpt.EByGs(p, inf, G, S, nodup, G)) ->
  {FOpt.job_res_b(1n+p, inf, G, S, Eval.Eval.cost_of(best0),
     SolveFast.step(1n+p, SolveFast.glist_of(G, SolveFast.GEnd{}), 0n, Nil{},
       SolveFast.glist_of(G, SolveFast.GEnd{}), S, Groups.len_words(S),
       nodup, SolveFast.init_floor(Groups.len_words(S)), inf,
       Nil{}, Nil{}, 0n, best0, SolveFast.dummy_zero(), False{},
       SolveFast.is_floor_hit(nodup, SolveFast.init_floor(Groups.len_words(S)),
         best0),
       SolveFast.GuessRes{Nil{}, buf0})) == True{} : Bool}:
  +limit : Nat = Eval.Eval.cost_of(best0)
  +hok0 : {FVal.FV.best_ok_b(limit, G, S, best0) == True{} : Bool} =
    FVal.FV.best_ok_init(limit, G, S, best0, Nat.ge_refl(limit))
  FOpt.glist_walk(p, G, S, nodup, FloorInit{}, inf, G, SolveFast.GEnd{},
    best0, limit, buf0, hbuf0, FVal.FV.all_in_ref_self(G), ele, hz, h1, h3,
    ai, nd, NatProof.Nat.is_le_refl(limit), hb0, hok0, {==}, fG,
    +best_end => buf_end => hbuf_end => +hok_end => +hle_b0 => +hle_g =>
      +hg_le_ref : {Nat.is_le(
                      Eval.Eval.cost_of(
                        Eval.Eval.guesses(1n+p, G, S, inf, G, best0)),
                      Eval.Eval.cost_of(FS.FS.ref_run_at(1n+p, inf, G, S)))
                    == True{} : Bool} =
        Fold.OQ.le_cong_l(
          Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, G, best0)),
          Eval.Eval.cost_of(
            FC.FC.better_best(FS.FS.ref_run_at(1n+p, inf, G, S), best0)),
          Eval.Eval.cost_of(FS.FS.ref_run_at(1n+p, inf, G, S)),
          Equal.cong(SolveRef.Best, Nat, Eval.Eval.cost_of,
            Eval.Eval.guesses(1n+p, G, S, inf, G, best0),
            FC.FC.better_best(FS.FS.ref_run_at(1n+p, inf, G, S), best0),
            FC.FC.eval_guesses_from(1n+p, inf, G, S, best0, ele, hb0)),
          FVal.FV.better_best_le_l(FS.FS.ref_run_at(1n+p, inf, G, S), best0))
      FO.FO.bool_and_intro(FVal.FV.best_ok_b(limit, G, S, best_end),
        Bool.and(Nat.is_le(Eval.Eval.cost_of(best_end), limit),
          Nat.is_le(Eval.Eval.cost_of(best_end),
            Eval.Eval.cost_of(FS.FS.ref_run_at(1n+p, inf, G, S)))),
        hok_end,
        FO.FO.bool_and_intro(Nat.is_le(Eval.Eval.cost_of(best_end), limit),
          Nat.is_le(Eval.Eval.cost_of(best_end),
            Eval.Eval.cost_of(FS.FS.ref_run_at(1n+p, inf, G, S))),
          hle_b0,
          NatProof.Nat.is_le_trans(Eval.Eval.cost_of(best_end),
            Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, G, best0)),
            Eval.Eval.cost_of(FS.FS.ref_run_at(1n+p, inf, G, S)),
            hle_g, hg_le_ref))))

def FOpt.ejob_succ_at(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +nodup: Bool, +best0: SolveRef.Best,
    +hb0: {Nat.is_le(Eval.Eval.cost_of(best0), inf) == True{} : Bool},
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +h3: {Nat.is_lt(3n, inf) == True{} : Bool},
    +ai: {FO.FO.all_in_ref(S, G) == True{} : Bool},
    +nd: {FN.FN.nodup_ok(nodup, S) == True{} : Bool},
    fS: FOpt.EByGs(p, inf, G, S, nodup, S),
    fG: FOpt.EByGs(p, inf, G, S, nodup, G)) ->
  {FOpt.job_res_b(1n+p, inf, G, S, Eval.Eval.cost_of(best0),
     FS.FS.run_child_from(1n+p, inf, G, S, nodup, best0)) == True{} : Bool}:
  match nodup:
    case True{}:
      +n : Nat = Groups.len_words(S)
      FOpt.ejob_succ_nodup(p, inf, G, S, best0,
        SolveFast.skippable(best0, Nat.add(n, n)), {==}, hb0, ele, hz, h1, h3,
        ai, nd, fS, fG)
    case False{}:
      +n : Nat = Groups.len_words(S)
      FOpt.ejob_succ_direct(p, inf, G, S, False{}, best0,
        SolveFast.mk_buf_init(False{}, n, best0),
        FH.FH.mk_buf_init_ok(False{}, n, best0),
        hb0, ele, hz, h1, h3, ai, {==}, fG)

def FOpt.ejob_succ(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +nodup: Bool,
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +h3: {Nat.is_lt(3n, inf) == True{} : Bool},
    +ai: {FO.FO.all_in_ref(S, G) == True{} : Bool},
    +nd: {FN.FN.nodup_ok(nodup, S) == True{} : Bool},
    fS: FOpt.EByGs(p, inf, G, S, nodup, S),
    fG: FOpt.EByGs(p, inf, G, S, nodup, G)) ->
  FOpt.EJob(1n+p, inf, G, S, nodup):
  +best0 => +hb0 =>
    FOpt.ejob_succ_at(p, inf, G, S, nodup, best0, hb0, ele, hz, h1, h3, ai, nd,
      fS, fG)

# ---------------------------------------------------------------------------
# Fuel 0 base case and fuel induction (`FOpt.eflat`)
# ---------------------------------------------------------------------------

def FOpt.zero_guess_step(+gG: SolveFast.GList, +nodup: Bool, +fl: Nat,
    +inf: Nat, +g: +List<Nat>, +rest: +List<+List<Nat>>, +best: SolveRef.Best,
    +dn: Bool, -gres: SolveFast.GuessRes) ->
  {SolveFast.step(0n, SolveFast.GTry{g, SolveFast.glist_of(rest, SolveFast.GEnd{})},
     0n, Nil{}, gG, Nil{}, 0n, nodup, fl, inf, Nil{}, Nil{}, 0n, best,
     SolveFast.dummy_zero(), False{}, dn, gres)
   == SolveFast.step(0n, SolveFast.glist_of(rest, SolveFast.GEnd{}), 0n, Nil{},
        gG, Nil{}, 0n, nodup, fl, inf, Nil{}, Nil{}, 0n,
        SolveRef.finish_guess(inf, g, Nil{}, 0n, 0n, best),
        SolveFast.dummy_zero(), False{}, False{}, gres) : SolveRef.Best}:
  match rest:
    case Nil{}:
      {==}
    case Con{gh, gt}:
      {==}

def FOpt.guesses_zero_eq(+G: +List<+List<Nat>>, +nodup: Bool, +fl: Nat,
    +inf: Nat, +gs: +List<+List<Nat>>, +best: SolveRef.Best, +dn: Bool,
    -gres: SolveFast.GuessRes) ->
  {SolveFast.step(0n, SolveFast.glist_of(gs, SolveFast.GEnd{}), 0n, Nil{},
     SolveFast.glist_of(G, SolveFast.GEnd{}), Nil{}, 0n, nodup, fl, inf,
     Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{}, dn, gres)
   == Eval.Eval.guesses(0n, G, Nil{}, inf, gs, best) : SolveRef.Best}:
  match gs:
    case Nil{}:
      {==}
    case Con{+g, +rest}:
      +gG : SolveFast.GList = SolveFast.glist_of(G, SolveFast.GEnd{})
      +next_best : SolveRef.Best =
        SolveRef.finish_guess(inf, g, Nil{}, 0n, 0n, best)
      Equal.trans(SolveRef.Best,
        SolveFast.step(0n,
          SolveFast.GTry{g, SolveFast.glist_of(rest, SolveFast.GEnd{})},
          0n, Nil{}, gG, Nil{}, 0n, nodup, fl, inf, Nil{}, Nil{}, 0n, best,
          SolveFast.dummy_zero(), False{}, dn, gres),
        SolveFast.step(0n, SolveFast.glist_of(rest, SolveFast.GEnd{}), 0n,
          Nil{}, gG, Nil{}, 0n, nodup, fl, inf, Nil{}, Nil{}, 0n, next_best,
          SolveFast.dummy_zero(), False{}, False{}, gres),
        Eval.Eval.guesses(0n, G, Nil{}, inf, g <> rest, best),
        FOpt.zero_guess_step(gG, nodup, fl, inf, g, rest, best, dn, gres),
        FOpt.guesses_zero_eq(G, nodup, fl, inf, rest, next_best, False{}, gres))

def FOpt.guesses_zero_ok(+inf: Nat, +G: +List<+List<Nat>>,
    +ws: +List<+List<Nat>>, +best: SolveRef.Best, +limit: Nat,
    +hg_in: {FO.FO.all_in_ref(ws, G) == True{} : Bool},
    +hok: {FVal.FV.best_ok_b(limit, G, Nil{}, best) == True{} : Bool}) ->
  {FVal.FV.best_ok_b(limit, G, Nil{},
     Eval.Eval.guesses(0n, G, Nil{}, inf, ws, best)) == True{} : Bool}:
  match ws:
    case Nil{}:
      hok
    case Con{+g, +rest}:
      +wg : {Tree.member_word(g, G) == True{} : Bool} =
        FO.FO.all_in_head(g, rest, G, hg_in)
      FOpt.guesses_zero_ok(inf, G, rest,
        SolveRef.finish_guess(inf, g, Nil{}, 0n, 0n, best), limit,
        FO.FO.all_in_tail(g, rest, G, hg_in),
        FVal.FV.best_ok_better(limit, G, Nil{}, SolveRef.sat_add(inf, 0n, 0n),
          Tree.Node{g, Nil{}}, best,
          FO.FO.bool_and_intro(
            FVal.FV.tree_in_b(Tree.Node{g, Nil{}}, G), True{},
            FO.FO.bool_and_intro(Tree.member_word(g, G), True{}, wg, {==}),
            {==}),
          NatProof.Nat.is_le_zero_l(SolveRef.sat_add(inf, 0n, 0n)), hok))

def FOpt.ejob_nil_guesses(+inf: Nat, +G: +List<+List<Nat>>, +best0: SolveRef.Best,
    +hb0: {Nat.is_le(Eval.Eval.cost_of(best0), inf) == True{} : Bool}) ->
  {FOpt.job_res_b(0n, inf, G, Nil{}, Eval.Eval.cost_of(best0),
     Eval.Eval.guesses(0n, G, Nil{}, inf, G, best0)) == True{} : Bool}:
  +limit : Nat = Eval.Eval.cost_of(best0)
  +hok0 : {FVal.FV.best_ok_b(limit, G, Nil{}, best0) == True{} : Bool} =
    FVal.FV.best_ok_init(limit, G, Nil{}, best0, Nat.ge_refl(limit))
  +ef : {Eval.Eval.guesses(0n, G, Nil{}, inf, G, best0)
         == FC.FC.better_best(FS.FS.ref_run_at(0n, inf, G, Nil{}), best0)
         : SolveRef.Best} =
    FC.FC.eval_guesses_from(0n, inf, G, Nil{}, best0, {==}, hb0)
  FO.FO.bool_and_intro(
    FVal.FV.best_ok_b(limit, G, Nil{},
      Eval.Eval.guesses(0n, G, Nil{}, inf, G, best0)),
    Bool.and(
      Nat.is_le(Eval.Eval.cost_of(Eval.Eval.guesses(0n, G, Nil{}, inf, G, best0)),
        limit),
      Nat.is_le(Eval.Eval.cost_of(Eval.Eval.guesses(0n, G, Nil{}, inf, G, best0)),
        Eval.Eval.cost_of(FS.FS.ref_run_at(0n, inf, G, Nil{})))),
    FOpt.guesses_zero_ok(inf, G, G, best0, limit, FVal.FV.all_in_ref_self(G),
      hok0),
    FO.FO.bool_and_intro(
      Nat.is_le(Eval.Eval.cost_of(Eval.Eval.guesses(0n, G, Nil{}, inf, G, best0)),
        limit),
      Nat.is_le(Eval.Eval.cost_of(Eval.Eval.guesses(0n, G, Nil{}, inf, G, best0)),
        Eval.Eval.cost_of(FS.FS.ref_run_at(0n, inf, G, Nil{}))),
      Fold.OQ.le_cong_l(
        Eval.Eval.cost_of(Eval.Eval.guesses(0n, G, Nil{}, inf, G, best0)),
        Eval.Eval.cost_of(
          FC.FC.better_best(FS.FS.ref_run_at(0n, inf, G, Nil{}), best0)),
        limit,
        Equal.cong(SolveRef.Best, Nat, Eval.Eval.cost_of,
          Eval.Eval.guesses(0n, G, Nil{}, inf, G, best0),
          FC.FC.better_best(FS.FS.ref_run_at(0n, inf, G, Nil{}), best0), ef),
        FVal.FV.better_best_le_r(FS.FS.ref_run_at(0n, inf, G, Nil{}), best0)),
      Fold.OQ.le_cong_l(
        Eval.Eval.cost_of(Eval.Eval.guesses(0n, G, Nil{}, inf, G, best0)),
        Eval.Eval.cost_of(
          FC.FC.better_best(FS.FS.ref_run_at(0n, inf, G, Nil{}), best0)),
        Eval.Eval.cost_of(FS.FS.ref_run_at(0n, inf, G, Nil{})),
        Equal.cong(SolveRef.Best, Nat, Eval.Eval.cost_of,
          Eval.Eval.guesses(0n, G, Nil{}, inf, G, best0),
          FC.FC.better_best(FS.FS.ref_run_at(0n, inf, G, Nil{}), best0), ef),
        FVal.FV.better_best_le_l(FS.FS.ref_run_at(0n, inf, G, Nil{}), best0))))

def FOpt.ejob_nil_nodup(+inf: Nat, +G: +List<+List<Nat>>, +best0: SolveRef.Best,
    le0: Bool, +ele0: {le0 == SolveFast.skippable(best0, 0n) : Bool},
    +hb0: {Nat.is_le(Eval.Eval.cost_of(best0), inf) == True{} : Bool}) ->
  {FOpt.job_res_b(0n, inf, G, Nil{}, Eval.Eval.cost_of(best0),
     SolveFast.step(0n,
       SolveFast.child_glist_nodup(Nil{},
         SolveFast.glist_of(G, SolveFast.GEnd{}), le0),
       0n, Nil{}, SolveFast.glist_of(G, SolveFast.GEnd{}), Nil{}, 0n, True{},
       0n, inf, Nil{}, Nil{}, 0n, best0, SolveFast.dummy_zero(), False{},
       SolveFast.is_floor_hit(True{}, 0n, best0),
       SolveFast.GuessRes{Nil{}, SolveFast.mk_buf_init(True{}, 0n, best0)}))
   == True{} : Bool}:
  match le0:
    case True{}:
      +limit : Nat = Eval.Eval.cost_of(best0)
      +h0 : {limit == 0n : Nat} =
        NatProof.Nat.eq_zero_of_le_zero(limit,
          FLB.FS.skippable_to_le(best0, 0n,
            Equal.sym(Bool, True{}, SolveFast.skippable(best0, 0n), ele0)))
      FO.FO.bool_and_intro(FVal.FV.best_ok_b(limit, G, Nil{}, best0),
        Bool.and(Nat.is_le(limit, limit),
          Nat.is_le(limit,
            Eval.Eval.cost_of(FS.FS.ref_run_at(0n, inf, G, Nil{})))),
        FVal.FV.best_ok_init(limit, G, Nil{}, best0, Nat.ge_refl(limit)),
        FO.FO.bool_and_intro(Nat.is_le(limit, limit),
          Nat.is_le(limit,
            Eval.Eval.cost_of(FS.FS.ref_run_at(0n, inf, G, Nil{}))),
          NatProof.Nat.is_le_refl(limit),
          Fold.OQ.le_cong_l(limit, 0n,
            Eval.Eval.cost_of(FS.FS.ref_run_at(0n, inf, G, Nil{})), h0,
            NatProof.Nat.is_le_zero_l(
              Eval.Eval.cost_of(FS.FS.ref_run_at(0n, inf, G, Nil{}))))))
    case False{}:
      +limit : Nat = Eval.Eval.cost_of(best0)
      +gG : SolveFast.GList = SolveFast.glist_of(G, SolveFast.GEnd{})
      Equal.trans(Bool,
        FOpt.job_res_b(0n, inf, G, Nil{}, limit,
          SolveFast.step(0n, gG, 0n, Nil{}, gG, Nil{}, 0n, True{}, 0n, inf,
            Nil{}, Nil{}, 0n, best0, SolveFast.dummy_zero(), False{}, False{},
            SolveFast.GuessRes{Nil{}, SolveFast.mk_buf_init(True{}, 0n, best0)})),
        FOpt.job_res_b(0n, inf, G, Nil{}, limit,
          Eval.Eval.guesses(0n, G, Nil{}, inf, G, best0)),
        True{},
        Equal.cong(SolveRef.Best, Bool,
          x => FOpt.job_res_b(0n, inf, G, Nil{}, limit, x),
          SolveFast.step(0n, gG, 0n, Nil{}, gG, Nil{}, 0n, True{}, 0n, inf,
            Nil{}, Nil{}, 0n, best0, SolveFast.dummy_zero(), False{}, False{},
            SolveFast.GuessRes{Nil{}, SolveFast.mk_buf_init(True{}, 0n, best0)}),
          Eval.Eval.guesses(0n, G, Nil{}, inf, G, best0),
          FOpt.guesses_zero_eq(G, True{}, 0n, inf, G, best0, False{},
            SolveFast.GuessRes{Nil{}, SolveFast.mk_buf_init(True{}, 0n, best0)})),
        FOpt.ejob_nil_guesses(inf, G, best0, hb0))

def FOpt.ejob_nil(+inf: Nat, +G: +List<+List<Nat>>, +nodup: Bool) ->
  FOpt.EJob(0n, inf, G, Nil{}, nodup):
  match nodup:
    case True{}:
      +best0 => +hb0 =>
        FOpt.ejob_nil_nodup(inf, G, best0, SolveFast.skippable(best0, 0n),
          {==}, hb0)
    case False{}:
      +best0 => +hb0 =>
        +gG : SolveFast.GList = SolveFast.glist_of(G, SolveFast.GEnd{})
        Equal.trans(Bool,
          FOpt.job_res_b(0n, inf, G, Nil{}, Eval.Eval.cost_of(best0),
            SolveFast.step(0n, gG, 0n, Nil{}, gG, Nil{}, 0n, False{}, 0n, inf,
              Nil{}, Nil{}, 0n, best0, SolveFast.dummy_zero(), False{}, False{},
              SolveFast.GuessRes{Nil{}, SolveFast.mk_buf_init(False{}, 0n, best0)})),
          FOpt.job_res_b(0n, inf, G, Nil{}, Eval.Eval.cost_of(best0),
            Eval.Eval.guesses(0n, G, Nil{}, inf, G, best0)),
          True{},
          Equal.cong(SolveRef.Best, Bool,
            x => FOpt.job_res_b(0n, inf, G, Nil{}, Eval.Eval.cost_of(best0), x),
            SolveFast.step(0n, gG, 0n, Nil{}, gG, Nil{}, 0n, False{}, 0n, inf,
              Nil{}, Nil{}, 0n, best0, SolveFast.dummy_zero(), False{}, False{},
              SolveFast.GuessRes{Nil{}, SolveFast.mk_buf_init(False{}, 0n, best0)}),
            Eval.Eval.guesses(0n, G, Nil{}, inf, G, best0),
            FOpt.guesses_zero_eq(G, False{}, 0n, inf, G, best0, False{},
              SolveFast.GuessRes{Nil{}, SolveFast.mk_buf_init(False{}, 0n, best0)})),
          FOpt.ejob_nil_guesses(inf, G, best0, hb0))

def FOpt.ejob_transport(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S1: +List<+List<Nat>>, +S2: +List<+List<Nat>>, +nodup: Bool,
    e: {S1 == S2 : +List<+List<Nat>>},
    j: FOpt.EJob(fuel, inf, G, S1, nodup)) -> FOpt.EJob(fuel, inf, G, S2, nodup):
  %e : FOpt.EJob(fuel, inf, G, _, nodup)
  j

def FOpt.ejob_zero(+inf: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +nodup: Bool,
    le: {Nat.is_le(Groups.len_words(S), 0n) == True{} : Bool}) ->
  FOpt.EJob(0n, inf, G, S, nodup):
  +eS : {S == Nil{} : +List<+List<Nat>>} =
    MV.MV.nil_of_len_zero(S,
      NatProof.Nat.eq_zero_of_le_zero(Groups.len_words(S), le))
  FOpt.ejob_transport(0n, inf, G, Nil{}, S, nodup,
    Equal.sym(+List<+List<Nat>>, S, Nil{}, eS), FOpt.ejob_nil(inf, G, nodup))

def FOpt.eflat_zero(+inf: Nat, +G: +List<+List<Nat>>, +nodup: Bool,
    +jobs: +List<+List<+List<Nat>>>,
    bounds: MV.MV.Bounds(0n, jobs)) -> FOpt.EFlat(0n, inf, G, nodup, jobs):
  match jobs:
    case Nil{}:
      Unit{}
    case Con{S, t}:
      (ble, bt) = bounds
      Tuple{FOpt.ejob_zero(inf, G, S, nodup, ble),
            FOpt.eflat_zero(inf, G, nodup, t, bt)}

def FOpt.eflat_step(+inf: Nat, +p: Nat, +G: +List<+List<Nat>>, +nodup: Bool,
    +jobs: +List<+List<+List<Nat>>>,
    bounds: MV.MV.Bounds(1n+p, jobs),
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +h3: {Nat.is_lt(3n, inf) == True{} : Bool},
    +aj: {FO.FO.all_in_jobs_b(jobs, G) == True{} : Bool},
    +nj: {FN.FN.nodup_ok_jobs(nodup, jobs) == True{} : Bool},
    f: FOpt.EFlat(p, inf, G, nodup, FOpt.next_jobs(G, jobs))) ->
  FOpt.EFlat(1n+p, inf, G, nodup, jobs):
  match jobs:
    case Nil{}:
      Unit{}
    case Con{+S, +t}:
      (+ble, bt) = bounds
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
      MV.MV.use_pair(FOpt.EFlat(1n+p, inf, G, nodup, S <> t),
        FOpt.EFlat(p, inf, G, nodup,
          List.append(&2, +List<+List<Nat>>,
            MV.MV.next_guess(S, S), MV.MV.next_guess(G, S))),
        FOpt.EFlat(p, inf, G, nodup, FOpt.next_jobs(G, t)),
        FOpt.eflat_append(p, inf, G, nodup,
          List.append(&2, +List<+List<Nat>>,
            MV.MV.next_guess(S, S), MV.MV.next_guess(G, S)),
          FOpt.next_jobs(G, t), f),
        fSG => ft =>
          MV.MV.use_pair(FOpt.EFlat(1n+p, inf, G, nodup, S <> t),
            FOpt.EFlat(p, inf, G, nodup, MV.MV.next_guess(S, S)),
            FOpt.EFlat(p, inf, G, nodup, MV.MV.next_guess(G, S)),
            FOpt.eflat_append(p, inf, G, nodup,
              MV.MV.next_guess(S, S), MV.MV.next_guess(G, S), fSG),
            fS => fG =>
              Tuple{FOpt.ejob_succ(p, inf, G, S, nodup, ble, hz, h1, h3, ai, nd,
                      FOpt.eby_gs(p, inf, G, S, nodup, S, fS),
                      FOpt.eby_gs(p, inf, G, S, nodup, G, fG)),
                    FOpt.eflat_step(inf, p, G, nodup, t, bt, hz, h1, h3, at,
                      nt, ft)}))

def FOpt.eflat(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>, +nodup: Bool,
    +jobs: +List<+List<+List<Nat>>>,
    bounds: MV.MV.Bounds(fuel, jobs),
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +h3: {Nat.is_lt(3n, inf) == True{} : Bool},
    +aj: {FO.FO.all_in_jobs_b(jobs, G) == True{} : Bool},
    +nj: {FN.FN.nodup_ok_jobs(nodup, jobs) == True{} : Bool}) ->
  FOpt.EFlat(fuel, inf, G, nodup, jobs):
  match fuel:
    case 0n:
      FOpt.eflat_zero(inf, G, nodup, jobs, bounds)
    case 1n+p:
      MV.MV.use_pair(FOpt.EFlat(1n+p, inf, G, nodup, jobs),
        MV.MV.Bounds(1n+p, jobs), MV.MV.Bounds(1n+p, jobs),
        FOpt.bounds_copy(1n+p, jobs, bounds),
        b1 => b2 =>
          FOpt.eflat_step(inf, p, G, nodup, jobs, b1, hz, h1, h3, aj, nj,
            FOpt.eflat(p, inf, G, nodup, FOpt.next_jobs(G, jobs),
              FOpt.next_bounds(p, G, jobs, b2), hz, h1, h3,
              FOpt.all_in_next_jobs(G, jobs, aj),
              FOpt.nodup_ok_next_jobs(nodup, G, jobs, nj))))

# ---------------------------------------------------------------------------
# Root search result and top-level `FOpt.solve_valid` / `FOpt.solve_optimal`
# ---------------------------------------------------------------------------

def FOpt.nodup_ok_of_fast_go(+S: +List<+List<Nat>>, b: Bool,
    +eb: {b == SolveFast.no_dup_fast(S) : Bool}) ->
  {FN.FN.nodup_ok(b, S) == True{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Equal.trans(Bool, FN.FN.no_dup_ref(S), SolveFast.no_dup_fast(S), True{},
        Equal.sym(Bool, SolveFast.no_dup_fast(S), FN.FN.no_dup_ref(S),
          FN.FN.no_dup_fast_eq(S)),
        Equal.sym(Bool, True{}, SolveFast.no_dup_fast(S), eb))

def FOpt.nodup_ok_of_fast(+S: +List<+List<Nat>>) ->
  {FN.FN.nodup_ok(SolveFast.no_dup_fast(S), S) == True{} : Bool}:
  FOpt.nodup_ok_of_fast_go(S, SolveFast.no_dup_fast(S), {==})

def FOpt.root_ge3_ok(+G: +List<+List<Nat>>, +w: +List<Nat>, +w2: +List<Nat>,
    +w3: +List<Nat>, +t3: +List<+List<Nat>>,
    +ai: {FO.FO.all_in_ref(w <> (w2 <> (w3 <> t3)), G) == True{} : Bool}) ->
  {FOpt.job_res_b(
     Groups.len_words(w <> (w2 <> (w3 <> t3))),
     SolveRef.inf_of(Groups.len_words(w <> (w2 <> (w3 <> t3)))),
     G, w <> (w2 <> (w3 <> t3)),
     SolveRef.inf_of(Groups.len_words(w <> (w2 <> (w3 <> t3)))),
     FS.FS.run_root_from(
       Groups.len_words(w <> (w2 <> (w3 <> t3))),
       SolveRef.inf_of(Groups.len_words(w <> (w2 <> (w3 <> t3)))),
       G, w <> (w2 <> (w3 <> t3)),
       SolveFast.no_dup_fast(w <> (w2 <> (w3 <> t3))),
       SolveFast.dummy_inf(
         SolveRef.inf_of(Groups.len_words(w <> (w2 <> (w3 <> t3)))))))
   == True{} : Bool}:
  +cs : +List<+List<Nat>> = w <> (w2 <> (w3 <> t3))
  +p : Nat = Groups.len_words(w2 <> (w3 <> t3))
  +n : Nat = Groups.len_words(cs)
  +inf : Nat = SolveRef.inf_of(n)
  +nd : Bool = SolveFast.no_dup_fast(cs)
  +hnd : {FN.FN.nodup_ok(nd, cs) == True{} : Bool} = FOpt.nodup_ok_of_fast(cs)
  +aj : {FO.FO.all_in_jobs_b(cs <> Nil{}, G) == True{} : Bool} =
    FO.FO.bool_and_intro(FO.FO.all_in_ref(cs, G), True{}, ai, {==})
  +nj : {FN.FN.nodup_ok_jobs(nd, cs <> Nil{}) == True{} : Bool} =
    FO.FO.bool_and_intro(FN.FN.nodup_ok(nd, cs), True{}, hnd, {==})
  +h3_le_n : {Nat.is_le(3n, n) == True{} : Bool} =
    NatProof.Nat.is_le_zero_l(Groups.len_words(t3))
  +h9_le_sq : {Nat.is_le(9n, Nat.mul(n, n)) == True{} : Bool} =
    NatProof.Nat.is_le_trans(9n, Nat.mul(3n, n), Nat.mul(n, n),
      CBN.CB.is_le_mul_r(3n, n, 3n, h3_le_n),
      CBN.CB.is_le_mul_l(3n, n, n, h3_le_n))
  +h3 : {Nat.is_lt(3n, inf) == True{} : Bool} =
    NatProof.Nat.is_le_lt_trans(3n, Nat.mul(n, n), inf,
      NatProof.Nat.is_le_trans(3n, 9n, Nat.mul(n, n), {==}, h9_le_sq),
      CBN.CB.lt_add_one(Nat.mul(n, n)))
  +h1 : {Nat.is_lt(1n, inf) == True{} : Bool} =
    NatProof.Nat.is_le_lt_trans(1n, 3n, inf, {==}, h3)
  +hz : {Nat.is_lt(0n, inf) == True{} : Bool} =
    NatProof.Nat.is_le_lt_trans(0n, 3n, inf, {==}, h3)
  bounds : MV.MV.Bounds(1n+p, cs <> Nil{}) =
    Tuple{NatProof.Nat.is_le_refl(n), Unit{}}
  ff : FOpt.EFlat(p, inf, G, nd, FOpt.next_jobs(G, cs <> Nil{})) =
    FOpt.eflat(p, inf, G, nd, FOpt.next_jobs(G, cs <> Nil{}),
      FOpt.next_bounds(p, G, cs <> Nil{}, bounds), hz, h1, h3,
      FOpt.all_in_next_jobs(G, cs <> Nil{}, aj),
      FOpt.nodup_ok_next_jobs(nd, G, cs <> Nil{}, nj))
  MV.MV.use_pair(
    {FOpt.job_res_b(n, inf, G, cs, inf,
       FS.FS.run_root_from(n, inf, G, cs, nd, SolveFast.dummy_inf(inf)))
     == True{} : Bool},
    FOpt.EFlat(p, inf, G, nd,
      List.append(&2, +List<+List<Nat>>,
        MV.MV.next_guess(cs, cs), MV.MV.next_guess(G, cs))),
    FOpt.EFlat(p, inf, G, nd, FOpt.next_jobs(G, Nil{})),
    FOpt.eflat_append(p, inf, G, nd,
      List.append(&2, +List<+List<Nat>>,
        MV.MV.next_guess(cs, cs), MV.MV.next_guess(G, cs)),
      FOpt.next_jobs(G, Nil{}), ff),
    fSG => fNil =>
      MV.MV.use_pair(
        {FOpt.job_res_b(n, inf, G, cs, inf,
           FS.FS.run_root_from(n, inf, G, cs, nd, SolveFast.dummy_inf(inf)))
         == True{} : Bool},
        FOpt.EFlat(p, inf, G, nd, MV.MV.next_guess(cs, cs)),
        FOpt.EFlat(p, inf, G, nd, MV.MV.next_guess(G, cs)),
        FOpt.eflat_append(p, inf, G, nd,
          MV.MV.next_guess(cs, cs), MV.MV.next_guess(G, cs), fSG),
        fS => fG =>
          FOpt.ejob_succ_direct(p, inf, G, cs, nd, SolveFast.dummy_inf(inf),
            SolveFast.mk_buf(nd, n, SolveFast.dummy_inf(inf)),
            FH.FH.mk_buf_ok(nd, n, SolveFast.dummy_inf(inf)),
            NatProof.Nat.is_le_refl(inf), NatProof.Nat.is_le_refl(n),
            hz, h1, h3, ai, hnd,
            FOpt.eby_gs(p, inf, G, cs, nd, G, fG))))

def FOpt.some_inj(+T1: Tree.Tree, +T2: Tree.Tree,
    e: {Some{T1} == Some{T2} : Maybe<Tree.Tree>}) -> {T1 == T2 : Tree.Tree}:
  Equal.cong(Maybe<Tree.Tree>, Tree.Tree,
    m => MV.MV.from_some(m, Tree.Node{Nil{}, Nil{}}), Some{T1}, Some{T2}, e)

def FOpt.valid_from_best_maybe_go(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +inf: Nat, +tree: Tree.Tree, +cost: Nat, +T: Tree.Tree, b: Bool,
    +eb: {b == Nat.is_ge(cost, inf) : Bool},
    +hok: {FVal.FV.best_ok_b(inf, G, C, SolveRef.Best{tree, cost})
           == True{} : Bool},
    e: {Feedback.Bool.case(Maybe<Tree.Tree>, b, None{}, Some{tree}) == Some{T}
        : Maybe<Tree.Tree>}) -> Tree.Valid(T, G, C):
  match b:
    case True{}:
      Empty.absurd(Tree.Valid(T, G, C), MV.MV.none_ne_some(Tree.Tree, T, e))
    case False{}:
      +hlt : {Nat.is_lt(cost, inf) == True{} : Bool} =
        Sat.SB.lt_of_ge_false(cost, inf,
          Equal.sym(Bool, False{}, Nat.is_ge(cost, inf), eb))
      +hext : {Bool.and(FVal.FV.valid_b(tree, G, C),
                 Nat.is_le(Tree.cost(tree, C), cost)) == True{} : Bool} =
        FVal.FV.best_ok_extract(inf, G, C, SolveRef.Best{tree, cost}, hok, hlt)
      +hval : {FVal.FV.valid_b(tree, G, C) == True{} : Bool} =
        Logic.Proof.and_true_l(FVal.FV.valid_b(tree, G, C),
          Nat.is_le(Tree.cost(tree, C), cost), hext)
      +et : {tree == T : Tree.Tree} = FOpt.some_inj(tree, T, e)
      %et : Tree.Valid(_, G, C)
      FVal.FV.valid_of_b(tree, G, C, hval)

def FOpt.valid_from_best_maybe(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +inf: Nat, best: SolveRef.Best, +T: Tree.Tree,
    +hok: {FVal.FV.best_ok_b(inf, G, C, best) == True{} : Bool},
    e: {SolveRef.best_to_maybe(inf, best) == Some{T} : Maybe<Tree.Tree>}) ->
  Tree.Valid(T, G, C):
  match best:
    case SolveRef.Best{+tree, +cost}:
      FOpt.valid_from_best_maybe_go(G, C, inf, tree, cost, T,
        Nat.is_ge(cost, inf), {==}, hok, e)

def FOpt.solve_fast_nil_eq(+G: +List<+List<Nat>>) ->
  {SolveFast.solve_fast_valid(G, Nil{}) == SolveRef.solve(G, Nil{})
   : Maybe<Tree.Tree>}:
  +gG : SolveFast.GList = SolveFast.glist_of(G, SolveFast.GEnd{})
  +b0 : SolveRef.Best = SolveFast.dummy_inf(1n)
  +eb : {SolveFast.step(0n, gG, 0n, Nil{}, gG, Nil{}, 0n, True{}, 0n, 1n,
           Nil{}, Nil{}, 0n, b0, SolveFast.dummy_zero(), False{},
           SolveFast.is_floor_hit(True{}, 0n, b0),
           SolveFast.GuessRes{Nil{}, SolveFast.mk_buf(True{}, 0n, b0)})
         == MV.MV.solve_best(G, Nil{}) : SolveRef.Best} =
    Equal.trans(SolveRef.Best,
      SolveFast.step(0n, gG, 0n, Nil{}, gG, Nil{}, 0n, True{}, 0n, 1n,
        Nil{}, Nil{}, 0n, b0, SolveFast.dummy_zero(), False{},
        SolveFast.is_floor_hit(True{}, 0n, b0),
        SolveFast.GuessRes{Nil{}, SolveFast.mk_buf(True{}, 0n, b0)}),
      Eval.Eval.guesses(0n, G, Nil{}, 1n, G, b0),
      MV.MV.solve_best(G, Nil{}),
      FOpt.guesses_zero_eq(G, True{}, 0n, 1n, G, b0,
        SolveFast.is_floor_hit(True{}, 0n, b0),
        SolveFast.GuessRes{Nil{}, SolveFast.mk_buf(True{}, 0n, b0)}),
      Equal.sym(SolveRef.Best, MV.MV.solve_best(G, Nil{}),
        Eval.Eval.guesses(0n, G, Nil{}, 1n, G, b0),
        Eval.Eval.guesses_zero(G, 1n, G, b0)))
  Equal.cong(SolveRef.Best, Maybe<Tree.Tree>,
    b => SolveRef.best_to_maybe(1n, b),
    SolveFast.step(0n, gG, 0n, Nil{}, gG, Nil{}, 0n, True{}, 0n, 1n,
      Nil{}, Nil{}, 0n, b0, SolveFast.dummy_zero(), False{},
      SolveFast.is_floor_hit(True{}, 0n, b0),
      SolveFast.GuessRes{Nil{}, SolveFast.mk_buf(True{}, 0n, b0)}),
    MV.MV.solve_best(G, Nil{}), eb)

def FOpt.solve_valid_two(+G: +List<+List<Nat>>, +w: +List<Nat>, +w2: +List<Nat>,
    +T: Tree.Tree, same: Bool,
    +es: {same == SolveFast.word_eq_fast(w, w2) : Bool},
    +w1in: {Tree.member_word(w, G) == True{} : Bool},
    +w2in: {Tree.member_word(w2, G) == True{} : Bool},
    e: {SolveFast.solve_fast_two(w, w2, same) == Some{T} : Maybe<Tree.Tree>}) ->
  Tree.Valid(T, G, w <> (w2 <> Nil{})):
  match same:
    case True{}:
      +heq : {Feedback.word_eq(w, w2) == True{} : Bool} =
        Equal.trans(Bool, Feedback.word_eq(w, w2),
          SolveFast.word_eq_fast(w, w2), True{},
          Equal.sym(Bool, SolveFast.word_eq_fast(w, w2),
            Feedback.word_eq(w, w2), FG.FG.word_eq_fast_eq(w, w2)),
          Equal.sym(Bool, True{}, SolveFast.word_eq_fast(w, w2), es))
      +et : {Tree.Node{w, Nil{}} == T : Tree.Tree} =
        FOpt.some_inj(Tree.Node{w, Nil{}}, T, e)
      %et : Tree.Valid(_, G, w <> (w2 <> Nil{}))
      FVal.FV.valid_of_b(Tree.Node{w, Nil{}}, G, w <> (w2 <> Nil{}),
        FVal.FV.two_same_valid_b(w, w2, G, w1in, heq))
    case False{}:
      +hne : {Feedback.word_eq(w, w2) == False{} : Bool} =
        Equal.trans(Bool, Feedback.word_eq(w, w2),
          SolveFast.word_eq_fast(w, w2), False{},
          Equal.sym(Bool, SolveFast.word_eq_fast(w, w2),
            Feedback.word_eq(w, w2), FG.FG.word_eq_fast_eq(w, w2)),
          Equal.sym(Bool, False{}, SolveFast.word_eq_fast(w, w2), es))
      +et : {SolveFast.two_tree(w, w2) == T : Tree.Tree} =
        FOpt.some_inj(SolveFast.two_tree(w, w2), T, e)
      %et : Tree.Valid(_, G, w <> (w2 <> Nil{}))
      FVal.FV.valid_of_b(SolveFast.two_tree(w, w2), G, w <> (w2 <> Nil{}),
        FVal.FV.two_tree_valid_b(w, w2, G, w1in, w2in, hne))

def FOpt.solve_valid_all_in(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +T: Tree.Tree, +ai: {FO.FO.all_in_ref(C, G) == True{} : Bool},
    e: {SolveFast.solve_fast_valid(G, C) == Some{T} : Maybe<Tree.Tree>}) ->
  Tree.Valid(T, G, C):
  match C:
    case Nil{}:
      MV.MV.solve_valid(G, Nil{}, T,
        Equal.trans(Maybe<Tree.Tree>, SolveRef.solve(G, Nil{}),
          SolveFast.solve_fast_valid(G, Nil{}), Some{T},
          Equal.sym(Maybe<Tree.Tree>, SolveFast.solve_fast_valid(G, Nil{}),
            SolveRef.solve(G, Nil{}), FOpt.solve_fast_nil_eq(G)), e))
    case Con{+w, +t}:
      match t:
        case Nil{}:
          +win : {Tree.member_word(w, G) == True{} : Bool} =
            FO.FO.all_in_head(w, Nil{}, G, ai)
          +et : {Tree.Node{w, Nil{}} == T : Tree.Tree} =
            FOpt.some_inj(Tree.Node{w, Nil{}}, T, e)
          %et : Tree.Valid(_, G, w <> Nil{})
          FVal.FV.valid_of_b(Tree.Node{w, Nil{}}, G, w <> Nil{},
            FVal.FV.one_tree_valid_b(w, G, win))
        case Con{+w2, +t2}:
          match t2:
            case Nil{}:
              +w1in : {Tree.member_word(w, G) == True{} : Bool} =
                FO.FO.all_in_head(w, w2 <> Nil{}, G, ai)
              +w2in : {Tree.member_word(w2, G) == True{} : Bool} =
                FO.FO.all_in_head(w2, Nil{}, G,
                  FO.FO.all_in_tail(w, w2 <> Nil{}, G, ai))
              FOpt.solve_valid_two(G, w, w2, T,
                SolveFast.word_eq_fast(w, w2), {==}, w1in, w2in, e)
            case Con{+w3, +t3}:
              +cs : +List<+List<Nat>> = w <> (w2 <> (w3 <> t3))
              +n : Nat = Groups.len_words(cs)
              +inf : Nat = SolveRef.inf_of(n)
              +nd : Bool = SolveFast.no_dup_fast(cs)
              +res : SolveRef.Best =
                FS.FS.run_root_from(n, inf, G, cs, nd,
                  SolveFast.dummy_inf(inf))
              +hjr : {FOpt.job_res_b(n, inf, G, cs, inf, res)
                      == True{} : Bool} =
                FOpt.root_ge3_ok(G, w, w2, w3, t3, ai)
              +hok : {FVal.FV.best_ok_b(inf, G, cs, res) == True{} : Bool} =
                Logic.Proof.and_true_l(FVal.FV.best_ok_b(inf, G, cs, res),
                  Bool.and(Nat.is_le(Eval.Eval.cost_of(res), inf),
                    Nat.is_le(Eval.Eval.cost_of(res),
                      Eval.Eval.cost_of(FS.FS.ref_run_at(n, inf, G, cs)))),
                  hjr)
              FOpt.valid_from_best_maybe(G, cs, inf, res, T, hok, e)

def FOpt.solve_valid_checked(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +T: Tree.Tree, ok: Bool, +eok: {ok == SolveFast.all_in_fast(C, G) : Bool},
    e: {SolveFast.solve_fast_checked(ok, G, C) == Some{T} : Maybe<Tree.Tree>}) ->
  Tree.Valid(T, G, C):
  match ok:
    case False{}:
      Empty.absurd(Tree.Valid(T, G, C), MV.MV.none_ne_some(Tree.Tree, T, e))
    case True{}:
      +ai : {FO.FO.all_in_ref(C, G) == True{} : Bool} =
        Equal.trans(Bool, FO.FO.all_in_ref(C, G), SolveFast.all_in_fast(C, G),
          True{},
          Equal.sym(Bool, SolveFast.all_in_fast(C, G), FO.FO.all_in_ref(C, G),
            FO.FO.all_in_fast_eq(C, G)),
          Equal.sym(Bool, True{}, SolveFast.all_in_fast(C, G), eok))
      FOpt.solve_valid_all_in(G, C, T, ai, e)

def FOpt.solve_valid(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +T: Tree.Tree,
    e: {SolveFast.solve(G, C) == Some{T} : Maybe<Tree.Tree>}) ->
  Tree.Valid(T, G, C):
  FOpt.solve_valid_checked(G, C, T, SolveFast.all_in_fast(C, G), {==}, e)

def FOpt.solve_opt_two(+G: +List<+List<Nat>>, +w: +List<Nat>, +w2: +List<Nat>,
    +T2: Tree.Tree, v: Tree.Valid(T2, G, w <> (w2 <> Nil{})), same: Bool,
    +es: {same == SolveFast.word_eq_fast(w, w2) : Bool}) ->
  Exists(Tree.Tree, T =>
    {SolveFast.solve_fast_two(w, w2, same) == Some{T} : Maybe<Tree.Tree>}
    & {Nat.is_le(Tree.cost(T, w <> (w2 <> Nil{})),
         Tree.cost(T2, w <> (w2 <> Nil{}))) == True{} : Bool}):
  match same:
    case True{}:
      +ws2 : +List<+List<Nat>> = w <> (w2 <> Nil{})
      +heq : {Feedback.word_eq(w, w2) == True{} : Bool} =
        Equal.trans(Bool, Feedback.word_eq(w, w2),
          SolveFast.word_eq_fast(w, w2), True{},
          Equal.sym(Bool, SolveFast.word_eq_fast(w, w2),
            Feedback.word_eq(w, w2), FG.FG.word_eq_fast_eq(w, w2)),
          Equal.sym(Bool, True{}, SolveFast.word_eq_fast(w, w2), es))
      (Tree.Node{w, Nil{}},
       ({==},
        Fold.OQ.le_cong_l(Tree.cost(Tree.Node{w, Nil{}}, ws2), 2n,
          Tree.cost(T2, ws2), FVal.FV.two_same_cost(w, w2, heq),
          LBProof.LB.valid_cost_ge_size(T2, G, ws2, v))))
    case False{}:
      +ws2 : +List<+List<Nat>> = w <> (w2 <> Nil{})
      +hne : {Feedback.word_eq(w, w2) == False{} : Bool} =
        Equal.trans(Bool, Feedback.word_eq(w, w2),
          SolveFast.word_eq_fast(w, w2), False{},
          Equal.sym(Bool, SolveFast.word_eq_fast(w, w2),
            Feedback.word_eq(w, w2), FG.FG.word_eq_fast_eq(w, w2)),
          Equal.sym(Bool, False{}, SolveFast.word_eq_fast(w, w2), es))
      +nd2 : {FN.FN.no_dup_ref(ws2) == True{} : Bool} =
        FVal.FV.no_dup_two_of_word_eq_false(w, w2, hne)
      (SolveFast.two_tree(w, w2),
       ({==},
        Fold.OQ.le_cong_l(Tree.cost(SolveFast.two_tree(w, w2), ws2),
          SolveFast.class_lb(ws2), Tree.cost(T2, ws2),
          Equal.trans(Nat, Tree.cost(SolveFast.two_tree(w, w2), ws2), 3n,
            SolveFast.class_lb(ws2),
            FVal.FV.two_tree_cost(w, w2, hne),
            FN.FN.class_lb_nodup_eq(ws2, nd2)),
          FLB.FS.valid_cost_ge_class_lb(T2, G, ws2, v))))

def FOpt.solve_opt_all_in(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +T2: Tree.Tree, +ai: {FO.FO.all_in_ref(C, G) == True{} : Bool},
    v: Tree.Valid(T2, G, C)) ->
  Exists(Tree.Tree, T =>
    {SolveFast.solve_fast_valid(G, C) == Some{T} : Maybe<Tree.Tree>}
    & {Nat.is_le(Tree.cost(T, C), Tree.cost(T2, C)) == True{} : Bool}):
  match C:
    case Nil{}:
      +inf : Nat = SolveRef.inf_of(0n)
      OQStrong.F2.use_pair(
        Exists(Tree.Tree, T =>
          {SolveFast.solve_fast_valid(G, Nil{}) == Some{T}
           : Maybe<Tree.Tree>}
          & {Nat.is_le(Tree.cost(T, Nil{}), Tree.cost(T2, Nil{}))
             == True{} : Bool}),
        {Nat.is_le(Eval.Eval.cost_of(MV.MV.solve_best(G, Nil{})),
           Tree.cost(T2, Nil{})) == True{} : Bool},
        {Nat.is_lt(Eval.Eval.cost_of(MV.MV.solve_best(G, Nil{})), inf)
         == True{} : Bool},
        OQStrong.F2.optimal_and_finite(G, Nil{}, T2, v),
        opt => fin =>
          +fin2 : {Nat.is_lt(Eval.Eval.cost_of(MV.MV.solve_best(G, Nil{})),
                     inf) == True{} : Bool} = fin
          +es_ref : {SolveRef.solve(G, Nil{})
                     == Some{Eval.Eval.tree_of(MV.MV.solve_best(G, Nil{}))}
                     : Maybe<Tree.Tree>} =
            OC.OC.best_to_maybe_fin(inf, MV.MV.solve_best(G, Nil{}), fin2)
          (Eval.Eval.tree_of(MV.MV.solve_best(G, Nil{})),
           (Equal.trans(Maybe<Tree.Tree>,
              SolveFast.solve_fast_valid(G, Nil{}),
              SolveRef.solve(G, Nil{}),
              Some{Eval.Eval.tree_of(MV.MV.solve_best(G, Nil{}))},
              FOpt.solve_fast_nil_eq(G), es_ref),
            {==})))
    case Con{+w, +t}:
      match t:
        case Nil{}:
          (Tree.Node{w, Nil{}},
           ({==},
            Fold.OQ.le_cong_l(Tree.cost(Tree.Node{w, Nil{}}, w <> Nil{}),
              1n, Tree.cost(T2, w <> Nil{}), FVal.FV.one_tree_cost(w),
              LBProof.LB.valid_cost_ge_size(T2, G, w <> Nil{}, v))))
        case Con{+w2, +t2}:
          match t2:
            case Nil{}:
              FOpt.solve_opt_two(G, w, w2, T2, v,
                SolveFast.word_eq_fast(w, w2), {==})
            case Con{+w3, +t3}:
              +cs : +List<+List<Nat>> = w <> (w2 <> (w3 <> t3))
              +n : Nat = Groups.len_words(cs)
              +inf : Nat = SolveRef.inf_of(n)
              +nd : Bool = SolveFast.no_dup_fast(cs)
              +res : SolveRef.Best =
                FS.FS.run_root_from(n, inf, G, cs, nd,
                  SolveFast.dummy_inf(inf))
              +hjr : {FOpt.job_res_b(n, inf, G, cs, inf, res)
                      == True{} : Bool} =
                FOpt.root_ge3_ok(G, w, w2, w3, t3, ai)
              +hok : {FVal.FV.best_ok_b(inf, G, cs, res) == True{} : Bool} =
                Logic.Proof.and_true_l(FVal.FV.best_ok_b(inf, G, cs, res),
                  Bool.and(Nat.is_le(Eval.Eval.cost_of(res), inf),
                    Nat.is_le(Eval.Eval.cost_of(res),
                      Eval.Eval.cost_of(FS.FS.ref_run_at(n, inf, G, cs)))),
                  hjr)
              +hjr_r : {Bool.and(Nat.is_le(Eval.Eval.cost_of(res), inf),
                          Nat.is_le(Eval.Eval.cost_of(res),
                            Eval.Eval.cost_of(
                              FS.FS.ref_run_at(n, inf, G, cs))))
                        == True{} : Bool} =
                Logic.Proof.and_true_r(FVal.FV.best_ok_b(inf, G, cs, res),
                  Bool.and(Nat.is_le(Eval.Eval.cost_of(res), inf),
                    Nat.is_le(Eval.Eval.cost_of(res),
                      Eval.Eval.cost_of(FS.FS.ref_run_at(n, inf, G, cs)))),
                  hjr)
              +hle_ref : {Nat.is_le(Eval.Eval.cost_of(res),
                            Eval.Eval.cost_of(MV.MV.solve_best(G, cs)))
                          == True{} : Bool} =
                Logic.Proof.and_true_r(
                  Nat.is_le(Eval.Eval.cost_of(res), inf),
                  Nat.is_le(Eval.Eval.cost_of(res),
                    Eval.Eval.cost_of(FS.FS.ref_run_at(n, inf, G, cs))),
                  hjr_r)
              OQStrong.F2.use_pair(
                Exists(Tree.Tree, T =>
                  {SolveRef.best_to_maybe(inf, res) == Some{T}
                   : Maybe<Tree.Tree>}
                  & {Nat.is_le(Tree.cost(T, cs), Tree.cost(T2, cs))
                     == True{} : Bool}),
                {Nat.is_le(Eval.Eval.cost_of(MV.MV.solve_best(G, cs)),
                   Tree.cost(T2, cs)) == True{} : Bool},
                {Nat.is_lt(Eval.Eval.cost_of(MV.MV.solve_best(G, cs)), inf)
                 == True{} : Bool},
                OQStrong.F2.optimal_and_finite(G, cs, T2, v),
                opt => fin =>
                  +fin_res : {Nat.is_lt(Eval.Eval.cost_of(res), inf)
                              == True{} : Bool} =
                    NatProof.Nat.is_le_lt_trans(Eval.Eval.cost_of(res),
                      Eval.Eval.cost_of(MV.MV.solve_best(G, cs)), inf,
                      hle_ref, fin)
                  +es : {SolveRef.best_to_maybe(inf, res)
                         == Some{Eval.Eval.tree_of(res)}
                         : Maybe<Tree.Tree>} =
                    OC.OC.best_to_maybe_fin(inf, res, fin_res)
                  +hext : {Bool.and(
                             FVal.FV.valid_b(Eval.Eval.tree_of(res), G, cs),
                             Nat.is_le(
                               Tree.cost(Eval.Eval.tree_of(res), cs),
                               Eval.Eval.cost_of(res))) == True{} : Bool} =
                    FVal.FV.best_ok_extract(inf, G, cs, res, hok, fin_res)
                  +hcost : {Nat.is_le(
                              Tree.cost(Eval.Eval.tree_of(res), cs),
                              Eval.Eval.cost_of(res)) == True{} : Bool} =
                    Logic.Proof.and_true_r(
                      FVal.FV.valid_b(Eval.Eval.tree_of(res), G, cs),
                      Nat.is_le(Tree.cost(Eval.Eval.tree_of(res), cs),
                        Eval.Eval.cost_of(res)), hext)
                  +hle : {Nat.is_le(Tree.cost(Eval.Eval.tree_of(res), cs),
                            Tree.cost(T2, cs)) == True{} : Bool} =
                    NatProof.Nat.is_le_trans(
                      Tree.cost(Eval.Eval.tree_of(res), cs),
                      Eval.Eval.cost_of(res), Tree.cost(T2, cs), hcost,
                      NatProof.Nat.is_le_trans(Eval.Eval.cost_of(res),
                        Eval.Eval.cost_of(MV.MV.solve_best(G, cs)),
                        Tree.cost(T2, cs), hle_ref, opt))
                  (Eval.Eval.tree_of(res), (es, hle)))

def FOpt.solve_opt_checked(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +T2: Tree.Tree, ok: Bool, +eok: {ok == SolveFast.all_in_fast(C, G) : Bool},
    v: Tree.Valid(T2, G, C)) ->
  Exists(Tree.Tree, T =>
    {SolveFast.solve_fast_checked(ok, G, C) == Some{T} : Maybe<Tree.Tree>}
    & {Nat.is_le(Tree.cost(T, C), Tree.cost(T2, C)) == True{} : Bool}):
  match ok:
    case False{}:
      +ef : {FO.FO.all_in_ref(C, G) == False{} : Bool} =
        Equal.trans(Bool, FO.FO.all_in_ref(C, G), SolveFast.all_in_fast(C, G),
          False{},
          Equal.sym(Bool, SolveFast.all_in_fast(C, G), FO.FO.all_in_ref(C, G),
            FO.FO.all_in_fast_eq(C, G)),
          Equal.sym(Bool, False{}, SolveFast.all_in_fast(C, G), eok))
      Empty.absurd(
        Exists(Tree.Tree, T =>
          {None{} == Some{T} : Maybe<Tree.Tree>}
          & {Nat.is_le(Tree.cost(T, C), Tree.cost(T2, C)) == True{} : Bool}),
        FO.FO.no_valid_of_valid(G, C, T2, v, ef))
    case True{}:
      +ai : {FO.FO.all_in_ref(C, G) == True{} : Bool} =
        Equal.trans(Bool, FO.FO.all_in_ref(C, G), SolveFast.all_in_fast(C, G),
          True{},
          Equal.sym(Bool, SolveFast.all_in_fast(C, G), FO.FO.all_in_ref(C, G),
            FO.FO.all_in_fast_eq(C, G)),
          Equal.sym(Bool, True{}, SolveFast.all_in_fast(C, G), eok))
      FOpt.solve_opt_all_in(G, C, T2, ai, v)

def FOpt.solve_optimal(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +T2: Tree.Tree, v: Tree.Valid(T2, G, C)) ->
  Exists(Tree.Tree, T =>
    {SolveFast.solve(G, C) == Some{T} : Maybe<Tree.Tree>}
    & {Nat.is_le(Tree.cost(T, C), Tree.cost(T2, C)) == True{} : Bool}):
  FOpt.solve_opt_checked(G, C, T2, SolveFast.all_in_fast(C, G), {==}, v)
