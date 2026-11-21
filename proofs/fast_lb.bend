# Soundness of the guess lower bound for the pruned search.
#
# For a guess `g` and its feedback groups over a candidate list `S`, the pruned
# search in `src/solve_fast.bend` skips the guess when the best cost so far is
# at most `lower_bound(|S|, groups) = |S| + class_words(groups)`.
#
# When the reference class fold produces a finite candidate cost `< inf`, every
# class search at fuel `p` also has a finite cost `< inf`. By the validity
# invariant (`mainvalid.bend`), the cost correspondence (`optcost.bend`) and the
# size lower bound (`lb_size.bend`), each class cost is at least its word count,
# so `lower_bound(|S|, groups)` is at most the guess's candidate cost and
# `better` keeps the accumulator. When the candidate cost is not below `inf`,
# `better` also keeps any accumulator whose cost is at most `inf`.
import Base
import ../src/solve_fast.bend as SolveFast
import ../src/solve_ref.bend as SolveRef
import ../src/tree.bend as Tree
import ../src/groups.bend as Groups
import ../src/feedback.bend as Feedback
import ./logic.bend as Logic
import ./nat.bend as NatProof
import ./eval.bend as Eval
import ./sat.bend as Sat
import ./bestok.bend as BO
import ./groupsmeasure.bend as GM
import ./solvevalid.bend as SV
import ./mainvalid.bend as MV
import ./classbound_nat.bend as CBN
import ./classbound_sum.bend as CBS
import ./optimalvalue.bend as OV
import ./optfold.bend as Fold
import ./optnode.bend as Node
import ./optcost.bend as OC
import ./lb_size.bend as LBProof
import ./fast_step.bend as FStep
import ./fast_better.bend as FB
import ./par_elt.bend as ParElt

# Extract a single job's cost correspondence from `OC.c_flat`.
def FS.child_cost_ok(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +ws: +List<+List<Nat>>,
    +ble: {Nat.is_le(Groups.len_words(ws), p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool}) ->
  OC.OC.CJob(p, inf, G, ws):
  MV.MV.use_pair(OC.OC.CJob(p, inf, G, ws),
    OC.OC.CJob(p, inf, G, ws), OC.OC.CFlat(p, inf, G, Nil{}),
    OC.OC.c_flat(p, inf, G, ws <> Nil{}, Tuple{ble, Unit{}}, hz),
    j => u => j)

# A finite child search at fuel `p` costs at least the number of words in the
# class.
def FS.child_size_le(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +ws: +List<+List<Nat>>,
    +ble: {Nat.is_le(Groups.len_words(ws), p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +clt: {Nat.is_lt(Sat.SB.child_cost(p, G, ws, inf), inf) == True{} : Bool}) ->
  {Nat.is_le(Groups.len_words(ws), Sat.SB.child_cost(p, G, ws, inf))
   == True{} : Bool}:
  +cr : SolveRef.Best = FStep.FS.ref_run_at(p, inf, G, ws)
  ok : BO.BO.BestOK(inf, cr, G, ws) = MV.MV.main_ok(p, inf, G, ws, ble)
  v : Tree.Valid(Eval.Eval.tree_of(cr), G, ws) =
    SV.SV.valid_of_ok_lt(inf, cr, G, ws, clt, ok)
  +le1 : {Nat.is_le(Groups.len_words(ws),
            Tree.cost(Eval.Eval.tree_of(cr), ws)) == True{} : Bool} =
    LBProof.LB.valid_cost_ge_size(Eval.Eval.tree_of(cr), G, ws, v)
  cok : OC.OC.CJob(p, inf, G, ws) = FS.child_cost_ok(p, inf, G, ws, ble, hz)
  +le2 : {Nat.is_le(Tree.cost(Eval.Eval.tree_of(cr), ws),
            Sat.SB.child_cost(p, G, ws, inf)) == True{} : Bool} =
    cok(clt)
  NatProof.Nat.is_le_trans(Groups.len_words(ws),
    Tree.cost(Eval.Eval.tree_of(cr), ws),
    Sat.SB.child_cost(p, G, ws, inf), le1, le2)

# Summing the word counts over a list of finite classes sits below the plain
# sum of the class costs.
def FS.classes_size_le(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +groups: +List<Groups.Group>,
    bounds: MV.MV.Bounds(p, MV.MV.next_groups(groups)),
    all: CBS.CU.AllLt(inf, Sat.SB.child_costs(p, G, groups, inf)),
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool}) ->
  {Nat.is_le(SolveFast.class_words(groups),
             CBN.CB.sum(Sat.SB.child_costs(p, G, groups, inf))) == True{} : Bool}:
  match groups:
    case Nil{}:
      NatProof.Nat.is_le_refl(0n)
    case Con{gp, rest}:
      match gp:
        case Groups.Group{fb, ws}:
          (ble, bt) = bounds
          (clt, at) = all
          +hd : {Nat.is_le(Groups.len_words(ws),
                   Sat.SB.child_cost(p, G, ws, inf)) == True{} : Bool} =
            FS.child_size_le(p, inf, G, ws, ble, hz, clt)
          +tl : {Nat.is_le(SolveFast.class_words(rest),
                   CBN.CB.sum(Sat.SB.child_costs(p, G, rest, inf)))
                 == True{} : Bool} =
            FS.classes_size_le(p, inf, G, rest, bt, at, hz)
          CBN.CB.is_le_add(Groups.len_words(ws),
            Sat.SB.child_cost(p, G, ws, inf),
            SolveFast.class_words(rest),
            CBN.CB.sum(Sat.SB.child_costs(p, G, rest, inf)), hd, tl)

# Finish the lower-bound comparison once the finite saturating fold is unpacked.
def FS.lb_le_ks_finish(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +g: +List<Nat>, +groups: +List<Groups.Group>,
    bounds: MV.MV.Bounds(p, MV.MV.next_groups(groups)),
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +eSat: {Nat.is_lt(SolveRef.sat_add(inf, Groups.len_words(S),
              Sat.SB.ks_sum(Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf))),
              inf) == True{} : Bool},
    +es: {Nat.is_lt(Sat.SB.ks_sum(
            Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf)), inf)
          == True{} : Bool},
    all: CBS.CU.AllLt(inf, Sat.SB.child_costs(p, G, groups, inf)),
    +plain: {OV.OV.sumL(inf, Sat.SB.child_costs(p, G, groups, inf), 0n)
             == Nat.add(0n, CBN.CB.sum(Sat.SB.child_costs(p, G, groups, inf)))
             : Nat}) ->
  {Nat.is_le(SolveFast.lower_bound(Groups.len_words(S), groups),
             Fold.OQ.ks_cost(inf, S,
               Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf)))
   == True{} : Bool}:
  +items : Eval.KS = Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf)
  +cs : +List<Nat> = Sat.SB.child_costs(p, G, groups, inf)
  +sum_eq : {Sat.SB.ks_sum(items) == CBN.CB.sum(cs) : Nat} =
    Equal.trans(Nat, Sat.SB.ks_sum(items), OV.OV.sumL(inf, cs, 0n),
      CBN.CB.sum(cs),
      OV.OV.sum_fold(p, G, S, g, groups, Nil{}, 0n, inf),
      Equal.trans(Nat, OV.OV.sumL(inf, cs, 0n),
        Nat.add(0n, CBN.CB.sum(cs)), CBN.CB.sum(cs), plain, {==}))
  +n_lt : {Nat.is_lt(Groups.len_words(S), inf) == True{} : Bool} =
    Sat.SB.sat_add_lt_l(inf, Groups.len_words(S), Sat.SB.ks_sum(items), eSat)
  +sat_eq : {SolveRef.sat_add(inf, Groups.len_words(S), Sat.SB.ks_sum(items))
             == Nat.add(Groups.len_words(S), CBN.CB.sum(cs)) : Nat} =
    Equal.trans(Nat,
      SolveRef.sat_add(inf, Groups.len_words(S), Sat.SB.ks_sum(items)),
      Nat.add(Groups.len_words(S), Sat.SB.ks_sum(items)),
      Nat.add(Groups.len_words(S), CBN.CB.sum(cs)),
      OV.OV.sat_fin(inf, Groups.len_words(S), Sat.SB.ks_sum(items),
        OV.OV.ge_false_of_lt(Groups.len_words(S), inf, n_lt),
        OV.OV.ge_false_of_lt(Sat.SB.ks_sum(items), inf, es)),
      Equal.cong(Nat, Nat, x => Nat.add(Groups.len_words(S), x),
        Sat.SB.ks_sum(items), CBN.CB.sum(cs), sum_eq))
  +kc_eq : {Fold.OQ.ks_cost(inf, S, items)
            == Nat.add(Groups.len_words(S), CBN.CB.sum(cs)) : Nat} =
    Equal.trans(Nat, Fold.OQ.ks_cost(inf, S, items),
      SolveRef.sat_add(inf, Groups.len_words(S), Sat.SB.ks_sum(items)),
      Nat.add(Groups.len_words(S), CBN.CB.sum(cs)),
      Node.OQ.ks_cost_unfold(inf, S, items), sat_eq)
  +cw_le : {Nat.is_le(SolveFast.class_words(groups), CBN.CB.sum(cs))
            == True{} : Bool} =
    FS.classes_size_le(p, inf, G, groups, bounds, all, hz)
  +lb_le : {Nat.is_le(SolveFast.lower_bound(Groups.len_words(S), groups),
                      Nat.add(Groups.len_words(S), CBN.CB.sum(cs)))
            == True{} : Bool} =
    NatProof.Nat.is_le_add_l(SolveFast.class_words(groups),
      CBN.CB.sum(cs), Groups.len_words(S), cw_le)
  Fold.OQ.le_cong_r(
    SolveFast.lower_bound(Groups.len_words(S), groups),
    Nat.add(Groups.len_words(S), CBN.CB.sum(cs)),
    Fold.OQ.ks_cost(inf, S, items),
    Equal.sym(Nat, Fold.OQ.ks_cost(inf, S, items),
      Nat.add(Groups.len_words(S), CBN.CB.sum(cs)), kc_eq),
    lb_le)

# When the guess's candidate cost is below infinity, the saturating class sum
# is a plain sum and `lower_bound(|S|, groups)` is at most the candidate cost.
def FS.lb_le_ks_cost(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +g: +List<Nat>, +groups: +List<Groups.Group>,
    bounds: MV.MV.Bounds(p, MV.MV.next_groups(groups)),
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +lt: {Nat.is_lt(Fold.OQ.ks_cost(inf, S,
            Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf)), inf)
          == True{} : Bool}) ->
  {Nat.is_le(SolveFast.lower_bound(Groups.len_words(S), groups),
             Fold.OQ.ks_cost(inf, S,
               Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf)))
   == True{} : Bool}:
  +items : Eval.KS = Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf)
  +cs : +List<Nat> = Sat.SB.child_costs(p, G, groups, inf)
  +eSat : {Nat.is_lt(SolveRef.sat_add(inf, Groups.len_words(S),
             Sat.SB.ks_sum(items)), inf) == True{} : Bool} =
    CBN.CB.lt_eq_l(inf, Fold.OQ.ks_cost(inf, S, items),
      SolveRef.sat_add(inf, Groups.len_words(S), Sat.SB.ks_sum(items)),
      Node.OQ.ks_cost_unfold(inf, S, items), lt)
  +es : {Nat.is_lt(Sat.SB.ks_sum(items), inf) == True{} : Bool} =
    Sat.SB.sat_add_lt_r(inf, Groups.len_words(S), Sat.SB.ks_sum(items), eSat)
  +esL : {Nat.is_lt(OV.OV.sumL(inf, cs, 0n), inf) == True{} : Bool} =
    CBN.CB.lt_eq_l(inf, Sat.SB.ks_sum(items), OV.OV.sumL(inf, cs, 0n),
      OV.OV.sum_fold(p, G, S, g, groups, Nil{}, 0n, inf), es)
  OC.OC.use_pair(
    {Nat.is_le(SolveFast.lower_bound(Groups.len_words(S), groups),
       Fold.OQ.ks_cost(inf, S, items)) == True{} : Bool},
    {Nat.is_lt(Nat.add(0n, CBN.CB.sum(cs)), inf) == True{} : Bool},
    CBS.CU.AllLt(inf, cs)
    & {OV.OV.sumL(inf, cs, 0n) == Nat.add(0n, CBN.CB.sum(cs)) : Nat}
    & {Nat.is_lt(0n, inf) == True{} : Bool},
    OC.OC.plain_both(inf, cs, 0n, esL),
    tot => r =>
      OC.OC.use_pair(
        {Nat.is_le(SolveFast.lower_bound(Groups.len_words(S), groups),
           Fold.OQ.ks_cost(inf, S, items)) == True{} : Bool},
        CBS.CU.AllLt(inf, cs),
        {OV.OV.sumL(inf, cs, 0n) == Nat.add(0n, CBN.CB.sum(cs)) : Nat}
        & {Nat.is_lt(0n, inf) == True{} : Bool},
        r,
        all => r2 =>
          OC.OC.use_pair(
            {Nat.is_le(SolveFast.lower_bound(Groups.len_words(S), groups),
               Fold.OQ.ks_cost(inf, S, items)) == True{} : Bool},
            {OV.OV.sumL(inf, cs, 0n) == Nat.add(0n, CBN.CB.sum(cs)) : Nat},
            {Nat.is_lt(0n, inf) == True{} : Bool},
            r2,
            plain => zlt =>
              FS.lb_le_ks_finish(p, inf, G, S, g, groups, bounds, hz,
                eSat, es, all, plain))))

# `SolveFast.best_cost` and `Eval.cost_of` read the same cost field.
def FS.best_cost_eq(best: SolveRef.Best) ->
  {SolveFast.best_cost(best) == Eval.Eval.cost_of(best) : Nat}:
  match best:
    case SolveRef.Best{tree, cost}:
      {==}

def FS.skippable_to_le(+best: SolveRef.Best, +lb: Nat,
    +e: {SolveFast.skippable(best, lb) == True{} : Bool}) ->
  {Nat.is_le(Eval.Eval.cost_of(best), lb) == True{} : Bool}:
  Fold.OQ.le_cong_l(Eval.Eval.cost_of(best), SolveFast.best_cost(best), lb,
    Equal.sym(Nat, SolveFast.best_cost(best), Eval.Eval.cost_of(best),
      FS.best_cost_eq(best)),
    e)
def FS.better_inf_keep(+cc: Nat, +ct: Tree.Tree, best: SolveRef.Best,
    +inf: Nat, +nf: {Nat.is_lt(cc, inf) == False{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool}) ->
  {SolveRef.better(cc, ct, best) == best : SolveRef.Best}:
  match best:
    case SolveRef.Best{+ta, +ca}:
      Equal.trans(SolveRef.Best,
        SolveRef.better(cc, ct, SolveRef.Best{ta, ca}),
        ParElt.ParElt.pick(ct, cc, ta, ca, Nat.is_lt(cc, ca)),
        SolveRef.Best{ta, ca},
        ParElt.ParElt.pick_better(cc, ct, ta, ca, Nat.is_lt(cc, ca), {==}),
        ParElt.ParElt.pick_acc(cc, ct, ta, ca, inf, Nat.is_lt(cc, ca),
          {==}, nf, hbest))

# `better` keeps `best` when `cost_of(best) <= lb`: either the candidate cost is
# finite (and at least `lb`) or it is at least `inf` (and loses to `best`).
def FS.better_skip_case(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +g: +List<Nat>, +groups: +List<Groups.Group>,
    +best: SolveRef.Best,
    bounds: MV.MV.Bounds(p, MV.MV.next_groups(groups)),
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    +le: {Nat.is_le(Eval.Eval.cost_of(best),
            SolveFast.lower_bound(Groups.len_words(S), groups)) == True{} : Bool},
    b: Bool,
    +eb: {b == Nat.is_lt(Fold.OQ.ks_cost(inf, S,
            Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf)), inf) : Bool}) ->
  {SolveRef.better(
     Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf)),
     Fold.OQ.ks_tree(g, Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf)),
     best)
   == best : SolveRef.Best}:
  match b:
    case True{}:
      +items : Eval.KS = Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf)
      +cc : Nat = Fold.OQ.ks_cost(inf, S, items)
      +ct : Tree.Tree = Fold.OQ.ks_tree(g, items)
      +lt : {Nat.is_lt(cc, inf) == True{} : Bool} =
        Equal.sym(Bool, True{}, Nat.is_lt(cc, inf), eb)
      +bl : {Nat.is_le(SolveFast.lower_bound(Groups.len_words(S), groups), cc)
             == True{} : Bool} =
        FS.lb_le_ks_cost(p, inf, G, S, g, groups, bounds, hz, lt)
      FB.FS.keep(cc, ct, best,
        SolveFast.lower_bound(Groups.len_words(S), groups), le, bl)
    case False{}:
      +items : Eval.KS = Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf)
      +cc : Nat = Fold.OQ.ks_cost(inf, S, items)
      +ct : Tree.Tree = Fold.OQ.ks_tree(g, items)
      +nf : {Nat.is_lt(cc, inf) == False{} : Bool} =
        Equal.sym(Bool, False{}, Nat.is_lt(cc, inf), eb)
      FS.better_inf_keep(cc, ct, best, inf, nf, hbest)

# A skipped usable block leaves the reference accumulator unchanged.
def FS.block_skip_eq(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +g: +List<Nat>, +groups: +List<Groups.Group>,
    +best: SolveRef.Best,
    +us: {Groups.groups_smaller(S, groups) == True{} : Bool},
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    +le: {Nat.is_le(Eval.Eval.cost_of(best),
            SolveFast.lower_bound(Groups.len_words(S), groups)) == True{} : Bool}) ->
  {Eval.Eval.block(p, G, S, g, inf, groups, best) == best : SolveRef.Best}:
  +items : Eval.KS = Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf)
  +cc : Nat = Fold.OQ.ks_cost(inf, S, items)
  +ct : Tree.Tree = Fold.OQ.ks_tree(g, items)
  bounds : MV.MV.Bounds(p, MV.MV.next_groups(groups)) =
    MV.MV.group_bounds(p, S, groups, ele,
      GM.GM.groups_smaller_sound(S, groups, us))
  Equal.trans(SolveRef.Best,
    Eval.Eval.block(p, G, S, g, inf, groups, best),
    SolveRef.better(cc, ct, best),
    best,
    Fold.OQ.block_eq(inf, g, S, items, best),
    FS.better_skip_case(p, inf, G, S, g, groups, best, bounds, hz, hbest, le,
      Nat.is_lt(cc, inf), {==}))
