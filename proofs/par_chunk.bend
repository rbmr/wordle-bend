# The seeded, presorted, chunked root of the bound-pruned solver.
#
# `src/solve_k.bend` first runs `Greedy.root_prepare` (`src/greedy.bend`) to
# presort usable root guesses by their Pass-1 depth-two lower bound and seed an
# initial valid upper bound `b0` from greedy(lb) rollouts. For `d = 0` (`k <= 1`),
# it runs `SolveFast.step` directly on the root buffer from `b0`. For `d >= 1`
# (`k >= 2`), it deals the sorted root guesses round-robin (`deal_even` /
# `deal_odd`) into `2^d <= k` chunks, evaluates every chunk from `b0` with the
# full guess list available at every child node, and folds the results with
# `SolveRef.better`.
#
# This module proves that every chunk result is valid and at most the reference
# fold over its own guesses, and by pointwise optimality over all usable root
# guesses in `G` that the final folded root result is valid and costs at most
# the reference solver for every chunk count `k`.
#
# The walk functions are the ones of `proofs/fast_opt.bend`, with the reference
# guess list as an explicit parameter `gs` instead of the whole child guess
# list `G`. Every proof term below mirrors the original; only the third
# conjunct of the job specification changes.
import Base
import ../src/solve_fast.bend as SolveFast
import ../src/solve_ref.bend as SolveRef
import ../src/tree.bend as Tree
import ../src/groups.bend as Groups
import ../src/feedback.bend as Feedback
import ../src/solve_k.bend as SolveK
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
import ./cover_list.bend as CoverList
import ./cover_groups.bend as CoverGroups
import ./array.bend as Arr
import ./fast_step.bend as FS
import ./fast_better.bend as FB
import ./fast_groups.bend as FG
import ./fast_lb.bend as FLB
import ./fast_cutoff.bend as FC
import ./fast_one.bend as FO
import ./fast_nodup.bend as FN
import ./fast_perm.bend as FP
import ./fast_tbl.bend as FT
import ./fast_three.bend as FT3
import ./fast_hist5.bend as FH
import ./fast_tight.bend as FTight
import ./fast_valid.bend as FVal
import ./fast_opt.bend as FOpt
import ./par_fold.bend as ParFold
import ./par_list.bend as ParList
import ../src/greedy.bend as Greedy
import ./optguess.bend as OQGuess
import ./par_elt.bend as ParElt
import ./greedy.bend as GR

# ---------------------------------------------------------------------------
# The chunk job specification
# ---------------------------------------------------------------------------

# Like `FOpt.FOpt.job_res_b`, but the third conjunct bounds the result by the
# reference fold over the chunk `gs` instead of the whole guess list `G`.
def P.job_res_gs_b(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +gs: +List<+List<Nat>>, +S: +List<+List<Nat>>, +limit: Nat,
    +res: SolveRef.Best) -> Bool:
  Bool.and(FVal.FV.best_ok_b(limit, G, S, res),
    Bool.and(Nat.is_le(Eval.Eval.cost_of(res), limit),
             Nat.is_le(Eval.Eval.cost_of(res),
               Eval.Eval.cost_of(Eval.Eval.guesses(fuel, G, S, inf, gs,
                 Eval.Eval.dummy_inf(inf))))))

def P.ChunkSpec(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +gs: +List<+List<Nat>>, +C_root: +List<+List<Nat>>, +n_root: Nat,
    +has_buf: Bool, +nodup: Bool, +S: +List<+List<Nat>>, +limit: Nat,
    sr: SolveFast.StepRes) -> Data:
  match sr:
    case SolveFast.StepRes{res, buf2}:
      Arr.Arr.DPair<
        {P.job_res_gs_b(fuel, inf, G, gs, S, limit, res) == True{} : Bool},
        FH.FH.BufOk(G, C_root, n_root, has_buf, nodup, buf2)>

def P.chunk_spec_transport(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +gs: +List<+List<Nat>>, +C_root: +List<+List<Nat>>, +n_root: Nat,
    +has_buf: Bool, +nodup: Bool, +S: +List<+List<Nat>>, +limit: Nat,
    -sr1: SolveFast.StepRes, -sr2: SolveFast.StepRes,
    +esr: {sr1 == sr2 : SolveFast.StepRes},
    +h: P.ChunkSpec(fuel, inf, G, gs, C_root, n_root, has_buf, nodup, S,
          limit, sr1)) ->
  P.ChunkSpec(fuel, inf, G, gs, C_root, n_root, has_buf, nodup, S, limit, sr2):
  %esr : P.ChunkSpec(fuel, inf, G, gs, C_root, n_root, has_buf, nodup, S,
           limit, _)
  h

def P.chunk_spec_gs(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +gs1: +List<+List<Nat>>, +gs2: +List<+List<Nat>>,
    +C_root: +List<+List<Nat>>, +n_root: Nat, +has_buf: Bool, +nodup: Bool,
    +S: +List<+List<Nat>>, +limit: Nat, sr: SolveFast.StepRes,
    +e: {gs1 == gs2 : +List<+List<Nat>>},
    h: P.ChunkSpec(fuel, inf, G, gs1, C_root, n_root, has_buf, nodup, S,
         limit, sr)) ->
  P.ChunkSpec(fuel, inf, G, gs2, C_root, n_root, has_buf, nodup, S, limit,
    sr):
  %e : P.ChunkSpec(fuel, inf, G, _, C_root, n_root, has_buf, nodup, S,
         limit, sr)
  h

# ---------------------------------------------------------------------------
# Floor exit bounds the chunk reference fold
# ---------------------------------------------------------------------------

# If the reference fold over `gs` leaves `best` unchanged, then `best` is at
# most the fold over `gs` from the neutral accumulator.
def P.fixed_le_evals(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +gs: +List<+List<Nat>>, +best: SolveRef.Best,
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    +efix: {Eval.Eval.guesses(fuel, G, S, inf, gs, best) == best
            : SolveRef.Best}) ->
  {Nat.is_le(Eval.Eval.cost_of(best),
     Eval.Eval.cost_of(Eval.Eval.guesses(fuel, G, S, inf, gs,
       Eval.Eval.dummy_inf(inf)))) == True{} : Bool}:
  +d : SolveRef.Best = Eval.Eval.dummy_inf(inf)
  +r : SolveRef.Best = Eval.Eval.guesses(fuel, G, S, inf, gs, d)
  +eb : {best == FC.FC.better_best(r, best) : SolveRef.Best} =
    Equal.trans(SolveRef.Best,
      best,
      Eval.Eval.guesses(fuel, G, S, inf, gs, best),
      FC.FC.better_best(r, best),
      Equal.sym(SolveRef.Best,
        Eval.Eval.guesses(fuel, G, S, inf, gs, best), best, efix),
      Equal.trans(SolveRef.Best,
        Eval.Eval.guesses(fuel, G, S, inf, gs, best),
        Eval.Eval.guesses(fuel, G, S, inf, gs,
          FC.FC.better_best(d, best)),
        FC.FC.better_best(
          Eval.Eval.guesses(fuel, G, S, inf, gs, d), best),
        Equal.cong(SolveRef.Best, SolveRef.Best,
          a => Eval.Eval.guesses(fuel, G, S, inf, gs, a),
          best, FC.FC.better_best(d, best),
          Equal.sym(SolveRef.Best,
            FC.FC.better_best(d, best), best,
            FC.FC.better_dummy_inf(inf, best, hbest))),
        FC.FC.eval_guesses_better(fuel, G, S, inf, gs, d, best)))
  Fold.OQ.le_cong_l(Eval.Eval.cost_of(best),
    Eval.Eval.cost_of(FC.FC.better_best(r, best)),
    Eval.Eval.cost_of(r),
    Equal.cong(SolveRef.Best, Nat, Eval.Eval.cost_of, best,
      FC.FC.better_best(r, best), eb),
    FVal.FV.better_best_le_l(r, best))

def P.floor_hit_le_evals(mode: FOpt.FOpt.FloorMode, +p: Nat, +inf: Nat,
    +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +gs: +List<+List<Nat>>, +nodup: Bool, +best: SolveRef.Best,
    +nd: {FN.FN.nodup_ok(nodup, S) == True{} : Bool},
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    +hinv: {FOpt.FOpt.floor_inv(mode, p, inf, G, S, best) == True{} : Bool},
    +ht: {SolveFast.is_floor_hit(nodup,
            FOpt.FOpt.floor_val(mode, Groups.len_words(S)), best)
          == True{} : Bool}) ->
  {Nat.is_le(Eval.Eval.cost_of(best),
     Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, gs,
       Eval.Eval.dummy_inf(inf)))) == True{} : Bool}:
  match mode:
    case FOpt.FloorInit{}:
      match nodup:
        case False{}:
          Empty.absurd(
            {Nat.is_le(Eval.Eval.cost_of(best),
               Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, gs,
                 Eval.Eval.dummy_inf(inf)))) == True{} : Bool},
            Logic.Proof.false_ne_true(ht))
        case True{}:
          P.fixed_le_evals(1n+p, inf, G, S, gs, best, hbest,
            FN.FN.guesses_floor_skip(p, inf, G, S, gs, best, nd, ele, hz,
              hbest,
              FLB.FS.skippable_to_le(best,
                SolveFast.init_floor(Groups.len_words(S)), ht)))
    case FOpt.FloorAfterS{}:
      match nodup:
        case False{}:
          Empty.absurd(
            {Nat.is_le(Eval.Eval.cost_of(best),
               Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, gs,
                 Eval.Eval.dummy_inf(inf)))) == True{} : Bool},
            Logic.Proof.false_ne_true(ht))
        case True{}:
          P.fixed_le_evals(1n+p, inf, G, S, gs, best, hbest,
            FVal.FV.after_s_guesses_skip(p, inf, G, S, gs, best, ele, hz,
              hbest,
              FLB.FS.skippable_to_le(best,
                Nat.add(Groups.len_words(S), Groups.len_words(S)), ht),
              hinv))

# `better` picks one of its two inputs, so the accumulator invariant transfers.
def P.best_ok_better_go(+limit: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, cand: SolveRef.Best, best: SolveRef.Best, lt: Bool,
    +e: {lt == Nat.is_lt(Eval.Eval.cost_of(cand), Eval.Eval.cost_of(best))
         : Bool},
    +hokc: {FVal.FV.best_ok_b(limit, G, S, cand) == True{} : Bool},
    +hokb: {FVal.FV.best_ok_b(limit, G, S, best) == True{} : Bool}) ->
  {FVal.FV.best_ok_b(limit, G, S,
     Feedback.Bool.case(SolveRef.Best, lt, cand, best)) == True{} : Bool}:
  match lt:
    case True{}:
      hokc
    case False{}:
      hokb

def P.best_ok_better(+limit: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, cand: SolveRef.Best, best: SolveRef.Best,
    +hokc: {FVal.FV.best_ok_b(limit, G, S, cand) == True{} : Bool},
    +hokb: {FVal.FV.best_ok_b(limit, G, S, best) == True{} : Bool}) ->
  {FVal.FV.best_ok_b(limit, G, S, FC.FC.better_best(cand, best))
   == True{} : Bool}:
  match cand:
    case SolveRef.Best{+ctree, +ccost}:
      match best:
        case SolveRef.Best{+btree, +bcost}:
          P.best_ok_better_go(limit, G, S,
            SolveRef.Best{ctree, ccost}, SolveRef.Best{btree, bcost},
            Nat.is_lt(ccost, bcost), {==}, hokc, hokb)

# ---------------------------------------------------------------------------
# Cloned staged walks with a chunk reference list
# ---------------------------------------------------------------------------

def P.walk_pop_unpack(+p: Nat, +G: +List<+List<Nat>>,
    +gs: +List<+List<Nat>>,
    +C_root: +List<+List<Nat>>, +n_root: Nat, +has_buf: Bool,
    +rwsG: +List<FT.FT.RowWord>, +cwS: +List<SolveFast.CWord>,
    +S: +List<+List<Nat>>, +nodup: Bool, +mode: FOpt.FOpt.FloorMode, +inf: Nat,
    +g: +List<Nat>, +t: +List<FT.FT.RowWord>, +tail: SolveFast.GList,
    +best: SolveRef.Best, +limit: Nat, +items: +List<SolveFast.Item>,
    -buf2: SolveFast.Buf5,
    r_step: FOpt.FOpt.StepRes(p, FT.FT.glist_of_rws(t, tail), G, C_root, n_root,
              has_buf, FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS, S,
              nodup, FOpt.FOpt.floor_val(mode, Groups.len_words(S)), inf, Nil{},
              items, Nil{}, 0n, best, buf2, limit,
              Eval.Eval.cost_of(Eval.Eval.guess(p, G, S, g, inf, best))),
    rec: @best2: SolveRef.Best -> @buf3: SolveFast.Buf5 ->
         FH.FH.BufOk(G, C_root, n_root, has_buf, nodup, buf3) ->
         {FVal.FV.best_ok_b(limit, G, S, best2) == True{} : Bool} ->
         {Nat.is_le(Eval.Eval.cost_of(best2), Eval.Eval.cost_of(best))
          == True{} : Bool} ->
         {Nat.is_le(Eval.Eval.cost_of(best2),
            Eval.Eval.cost_of(Eval.Eval.guess(p, G, S, g, inf, best)))
          == True{} : Bool} ->
         P.ChunkSpec(1n+p, inf, G, gs, C_root, n_root, has_buf, nodup, S, limit,
           SolveFast.step(1n+p, FT.FT.glist_of_rws(t, tail), 0n, Nil{},
             FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS,
             Groups.len_words(S), nodup,
             FOpt.FOpt.floor_val(mode, Groups.len_words(S)), inf,
             Nil{}, Nil{}, 0n, best2, SolveFast.dummy_step_zero(), False{},
             SolveFast.is_floor_hit(nodup,
               FOpt.FOpt.floor_val(mode, Groups.len_words(S)), best2),
             SolveFast.GuessRes{Nil{}, buf3}))) ->
  P.ChunkSpec(1n+p, inf, G, gs, C_root, n_root, has_buf, nodup, S, limit,
    SolveFast.step(1n+p, FT.FT.glist_of_rws(t, tail), 1n, Nil{},
      FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS, Groups.len_words(S),
      nodup, FOpt.FOpt.floor_val(mode, Groups.len_words(S)), inf,
      Nil{}, Nil{}, 0n, best, SolveFast.dummy_step_zero(), False{}, False{},
      SolveFast.GuessRes{items, buf2})):
  match r_step:
    case Tuple{+best2, p0}:
      match p0:
        case Tuple{buf3, p1}:
          match p1:
            case Tuple{+e_step, p2}:
              match p2:
                case Tuple{+hbuf3, p3}:
                  match p3:
                    case Tuple{+hok2, p4}:
                      match p4:
                        case Tuple{+hleb, hleg}:
                          +n : Nat = Groups.len_words(S)
                          +fl : Nat = FOpt.FOpt.floor_val(mode, n)
                          +gG : SolveFast.GList =
                            FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{})
                          +gt : SolveFast.GList = FT.FT.glist_of_rws(t, tail)
                          +e_tot : {SolveFast.step(1n+p, gt, 1n, Nil{}, gG, cwS,
                                      n, nodup, fl, inf, Nil{}, Nil{}, 0n, best,
                                      SolveFast.dummy_step_zero(), False{},
                                      False{}, SolveFast.GuessRes{items, buf2})
                                    == SolveFast.step(1n+p, gt, 0n, Nil{}, gG,
                                         cwS, n, nodup, fl, inf, Nil{}, Nil{},
                                         0n, best2, SolveFast.dummy_step_zero(),
                                         False{},
                                         SolveFast.is_floor_hit(nodup, fl, best2),
                                         SolveFast.GuessRes{Nil{}, buf3})
                                    : SolveFast.StepRes} =
                            Equal.trans(SolveFast.StepRes,
                              SolveFast.step(1n+p, gt, 1n, Nil{}, gG, cwS, n,
                                nodup, fl, inf, Nil{}, Nil{}, 0n, best,
                                SolveFast.dummy_step_zero(), False{}, False{},
                                SolveFast.GuessRes{items, buf2}),
                              SolveFast.step(1n+p, gt, 0n, items, gG, cwS, n,
                                nodup, fl, inf, Nil{}, Nil{}, 0n, best,
                                SolveFast.dummy_step_zero(), False{}, False{},
                                SolveFast.GuessRes{Nil{}, buf2}),
                              SolveFast.step(1n+p, gt, 0n, Nil{}, gG, cwS, n,
                                nodup, fl, inf, Nil{}, Nil{}, 0n, best2,
                                SolveFast.dummy_step_zero(), False{},
                                SolveFast.is_floor_hit(nodup, fl, best2),
                                SolveFast.GuessRes{Nil{}, buf3}),
                              FS.FS.unpack_gres_succ(p, gt, gG, cwS, n, nodup,
                                fl, inf, best, items, buf2),
                              e_step)
                          P.chunk_spec_transport(1n+p, inf, G, gs, C_root,
                            n_root, has_buf, nodup, S, limit,
                            SolveFast.step(1n+p, gt, 0n, Nil{}, gG, cwS, n,
                              nodup, fl, inf, Nil{}, Nil{}, 0n, best2,
                              SolveFast.dummy_step_zero(), False{},
                              SolveFast.is_floor_hit(nodup, fl, best2),
                              SolveFast.GuessRes{Nil{}, buf3}),
                            SolveFast.step(1n+p, gt, 1n, Nil{}, gG, cwS, n,
                              nodup, fl, inf, Nil{}, Nil{}, 0n, best,
                              SolveFast.dummy_step_zero(), False{}, False{},
                              SolveFast.GuessRes{items, buf2}),
                            Equal.sym(SolveFast.StepRes,
                              SolveFast.step(1n+p, gt, 1n, Nil{}, gG, cwS, n,
                                nodup, fl, inf, Nil{}, Nil{}, 0n, best,
                                SolveFast.dummy_step_zero(), False{}, False{},
                                SolveFast.GuessRes{items, buf2}),
                              SolveFast.step(1n+p, gt, 0n, Nil{}, gG, cwS, n,
                                nodup, fl, inf, Nil{}, Nil{}, 0n, best2,
                                SolveFast.dummy_step_zero(), False{},
                                SolveFast.is_floor_hit(nodup, fl, best2),
                                SolveFast.GuessRes{Nil{}, buf3}), e_tot),
                            rec(best2, buf3, hbuf3, hok2, hleb, hleg))

def P.walk_pop_go(+p: Nat, +G: +List<+List<Nat>>,
    +gs: +List<+List<Nat>>,
    +C_root: +List<+List<Nat>>, +n_root: Nat, +has_buf: Bool,
    +rwsG: +List<FT.FT.RowWord>, +cwS: +List<SolveFast.CWord>,
    +S: +List<+List<Nat>>, +nodup: Bool, +mode: FOpt.FOpt.FloorMode, +inf: Nat,
    +g: +List<Nat>, +t: +List<FT.FT.RowWord>, +tail: SolveFast.GList,
    +best: SolveRef.Best, +limit: Nat, r: SolveFast.GuessRes,
    +hr: FH.FH.GuessSpec(G, C_root, n_root, has_buf, nodup, g, S,
           Groups.len_words(S), FOpt.FOpt.floor_val(mode, Groups.len_words(S)),
           best, r),
    +erwsG: {FT.FT.rws_words(rwsG) == G : +List<+List<Nat>>},
    +hrwsG: {FH.FH.rws_ok_if(has_buf, G, n_root, rwsG) == True{} : Bool},
    +wg: {Tree.member_word(g, G) == True{} : Bool},
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +h3: {Nat.is_lt(3n, inf) == True{} : Bool},
    +h6: {Nat.is_lt(6n, inf) == True{} : Bool},
    +ai: {FO.FO.all_in_ref(S, G) == True{} : Bool},
    +nd: {FN.FN.nodup_ok(nodup, S) == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    +hok: {FVal.FV.best_ok_b(limit, G, S, best) == True{} : Bool},
    +hd: {SolveFast.is_floor_hit(nodup,
            FOpt.FOpt.floor_val(mode, Groups.len_words(S)), best) == False{} : Bool},
    +hinv: {FOpt.FOpt.floor_inv(mode, p, inf, G, S, best) == True{} : Bool},
    ecif: FOpt.FOpt.EClassIf(
            Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
            p, inf, G, C_root, n_root, has_buf, nodup,
            Groups.groups_build(g, S, Nil{})),
    rec: @best2: SolveRef.Best -> @buf3: SolveFast.Buf5 ->
         FH.FH.BufOk(G, C_root, n_root, has_buf, nodup, buf3) ->
         {FVal.FV.best_ok_b(limit, G, S, best2) == True{} : Bool} ->
         {Nat.is_le(Eval.Eval.cost_of(best2), Eval.Eval.cost_of(best))
          == True{} : Bool} ->
         {Nat.is_le(Eval.Eval.cost_of(best2),
            Eval.Eval.cost_of(Eval.Eval.guess(p, G, S, g, inf, best)))
          == True{} : Bool} ->
         P.ChunkSpec(1n+p, inf, G, gs, C_root, n_root, has_buf, nodup, S, limit,
           SolveFast.step(1n+p, FT.FT.glist_of_rws(t, tail), 0n, Nil{},
             FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS,
             Groups.len_words(S), nodup,
             FOpt.FOpt.floor_val(mode, Groups.len_words(S)), inf,
             Nil{}, Nil{}, 0n, best2, SolveFast.dummy_step_zero(), False{},
             SolveFast.is_floor_hit(nodup,
               FOpt.FOpt.floor_val(mode, Groups.len_words(S)), best2),
             SolveFast.GuessRes{Nil{}, buf3}))) ->
  P.ChunkSpec(1n+p, inf, G, gs, C_root, n_root, has_buf, nodup, S, limit,
    SolveFast.step(1n+p, FT.FT.glist_of_rws(t, tail), 1n, Nil{},
      FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS, Groups.len_words(S),
      nodup, FOpt.FOpt.floor_val(mode, Groups.len_words(S)), inf,
      Nil{}, Nil{}, 0n, best, SolveFast.dummy_step_zero(), False{}, False{}, r)):
  match r:
    case SolveFast.GuessRes{+items, buf2}:
      +n : Nat = Groups.len_words(S)
      +fl : Nat = FOpt.FOpt.floor_val(mode, n)
      +gt : SolveFast.GList = FT.FT.glist_of_rws(t, tail)
      +gw = Arr.Arr.dpair_l(
              FH.FH.GuessWit<G, C_root, n_root, has_buf, nodup, g, S, n, fl,
                best, items>,
              FH.FH.BufOk(G, C_root, n_root, has_buf, nodup, buf2), hr)
      +hbuf2 = Arr.Arr.dpair_r(
                 FH.FH.GuessWit<G, C_root, n_root, has_buf, nodup, g, S, n, fl,
                   best, items>,
                 FH.FH.BufOk(G, C_root, n_root, has_buf, nodup, buf2), hr)
      P.walk_pop_unpack(p, G, gs, C_root, n_root, has_buf, rwsG, cwS, S, nodup,
        mode, inf, g, t, tail, best, limit, items, buf2,
        FOpt.FOpt.guess_case_ok(p, gt, G, C_root, n_root, has_buf, rwsG, cwS, S,
          nodup, mode, inf, g, items, best, buf2, limit, hbuf2, gw, erwsG,
          hrwsG, wg, ele, hz, h1, h3, h6, ai, nd, hbest, hok, hd, hinv, ecif),
        rec)

def P.walk_pop_dup(+p: Nat, +G: +List<+List<Nat>>,
    +gs: +List<+List<Nat>>,
    +C_root: +List<+List<Nat>>, +n_root: Nat, +has_buf: Bool,
    +rwsG: +List<FT.FT.RowWord>, +cwS: +List<SolveFast.CWord>,
    +S: +List<+List<Nat>>, +nodup: Bool, +mode: FOpt.FOpt.FloorMode, +inf: Nat,
    +row: U32, +g: +List<Nat>, +t: +List<FT.FT.RowWord>, +tail: SolveFast.GList,
    +best: SolveRef.Best, +limit: Nat, -buf: SolveFast.Buf5,
    +hbuf: FH.FH.BufOk(G, C_root, n_root, has_buf, nodup, buf),
    dp: &b1: SolveFast.Buf5 -> &b2: SolveFast.Buf5 ->
        {b1 == buf : SolveFast.Buf5} & {b2 == b1 : SolveFast.Buf5},
    +erwsG: {FT.FT.rws_words(rwsG) == G : +List<+List<Nat>>},
    +hrwsG: {FH.FH.rws_ok_if(has_buf, G, n_root, rwsG) == True{} : Bool},
    +ecwS: {SolveFast.cwords_words(cwS) == S : +List<+List<Nat>>},
    +hcwS: {FH.FH.cwords_ok_if(has_buf, G, C_root, n_root, cwS) == True{} : Bool},
    +hrow: {FH.FH.gentry_ok_if(has_buf, G, n_root, row, g) == True{} : Bool},
    +wg: {Tree.member_word(g, G) == True{} : Bool},
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +h3: {Nat.is_lt(3n, inf) == True{} : Bool},
    +h6: {Nat.is_lt(6n, inf) == True{} : Bool},
    +ai: {FO.FO.all_in_ref(S, G) == True{} : Bool},
    +nd: {FN.FN.nodup_ok(nodup, S) == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    +hok: {FVal.FV.best_ok_b(limit, G, S, best) == True{} : Bool},
    +hd: {SolveFast.is_floor_hit(nodup,
            FOpt.FOpt.floor_val(mode, Groups.len_words(S)), best) == False{} : Bool},
    +hinv: {FOpt.FOpt.floor_inv(mode, p, inf, G, S, best) == True{} : Bool},
    ecif: FOpt.FOpt.EClassIf(
            Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
            p, inf, G, C_root, n_root, has_buf, nodup,
            Groups.groups_build(g, S, Nil{})),
    rec: @best2: SolveRef.Best -> @buf3: SolveFast.Buf5 ->
         FH.FH.BufOk(G, C_root, n_root, has_buf, nodup, buf3) ->
         {FVal.FV.best_ok_b(limit, G, S, best2) == True{} : Bool} ->
         {Nat.is_le(Eval.Eval.cost_of(best2), Eval.Eval.cost_of(best))
          == True{} : Bool} ->
         {Nat.is_le(Eval.Eval.cost_of(best2),
            Eval.Eval.cost_of(Eval.Eval.guess(p, G, S, g, inf, best)))
          == True{} : Bool} ->
         P.ChunkSpec(1n+p, inf, G, gs, C_root, n_root, has_buf, nodup, S, limit,
           SolveFast.step(1n+p, FT.FT.glist_of_rws(t, tail), 0n, Nil{},
             FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS,
             Groups.len_words(S), nodup,
             FOpt.FOpt.floor_val(mode, Groups.len_words(S)), inf,
             Nil{}, Nil{}, 0n, best2, SolveFast.dummy_step_zero(), False{},
             SolveFast.is_floor_hit(nodup,
               FOpt.FOpt.floor_val(mode, Groups.len_words(S)), best2),
             SolveFast.GuessRes{Nil{}, buf3}))) ->
  P.ChunkSpec(1n+p, inf, G, gs, C_root, n_root, has_buf, nodup, S, limit,
    SolveFast.step(1n+p, FT.FT.glist_of_rws(t, tail), 1n, Nil{},
      FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS, Groups.len_words(S),
      nodup, FOpt.FOpt.floor_val(mode, Groups.len_words(S)), inf,
      Nil{}, Nil{}, 0n, best, SolveFast.dummy_step_zero(), False{}, False{},
      SolveFast.guess_items_buf(nodup, row, g,
        FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS, Groups.len_words(S),
        FOpt.FOpt.floor_val(mode, Groups.len_words(S)), best, buf))):
  (b1, dp2) = dp
  (b2, pe) = dp2
  (+eb1, +eb2) = pe
  +n : Nat = Groups.len_words(S)
  +fl : Nat = FOpt.FOpt.floor_val(mode, n)
  +gG : SolveFast.GList = FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{})
  +gt : SolveFast.GList = FT.FT.glist_of_rws(t, tail)
  +eb2_buf : {b2 == buf : SolveFast.Buf5} =
    Equal.trans(SolveFast.Buf5, b2, b1, buf, eb2, eb1)
  +hbuf2 = FH.FH.buf_ok_transport(G, C_root, n_root, has_buf, nodup, buf, b2,
             Equal.sym(SolveFast.Buf5, b2, buf, eb2_buf), hbuf)
  +en : {n == Groups.len_words(SolveFast.cwords_words(cwS)) : Nat} =
    Equal.cong(+List<+List<Nat>>, Nat, l => Groups.len_words(l),
      S, SolveFast.cwords_words(cwS),
      Equal.sym(+List<+List<Nat>>, SolveFast.cwords_words(cwS), S, ecwS))
  +hnd_cw : {FN.FN.nodup_ok(nodup, SolveFast.cwords_words(cwS)) == True{} : Bool} =
    Equal.trans(Bool, FN.FN.nodup_ok(nodup, SolveFast.cwords_words(cwS)),
      FN.FN.nodup_ok(nodup, S), True{},
      Equal.cong(+List<+List<Nat>>, Bool, l => FN.FN.nodup_ok(nodup, l),
        SolveFast.cwords_words(cwS), S, ecwS), nd)
  +hr2_cw = FTight.FTight.guess_items_buf_spec(rwsG, G, C_root, n_root, has_buf,
              nodup, row, g, cwS, n, fl, best, b2, erwsG, hrwsG, en, hnd_cw,
              hrow, hcwS, hbuf2)
  +hr2 : FH.FH.GuessSpec(G, C_root, n_root, has_buf, nodup, g, S, n, fl, best,
           SolveFast.guess_items_buf(nodup, row, g, gG, cwS, n, fl, best, b2)) =
    %ecwS : FH.FH.GuessSpec(G, C_root, n_root, has_buf, nodup, g, _, n, fl,
              best,
              SolveFast.guess_items_buf(nodup, row, g, gG, cwS, n, fl, best, b2))
    hr2_cw
  +er : {SolveFast.guess_items_buf(nodup, row, g, gG, cwS, n, fl, best, b2)
         == SolveFast.guess_items_buf(nodup, row, g, gG, cwS, n, fl, best, b1)
         : SolveFast.GuessRes} =
    Equal.cong(SolveFast.Buf5, SolveFast.GuessRes,
      b => SolveFast.guess_items_buf(nodup, row, g, gG, cwS, n, fl, best, b),
      b2, b1, eb2)
  +hr1 : FH.FH.GuessSpec(G, C_root, n_root, has_buf, nodup, g, S, n, fl, best,
           SolveFast.guess_items_buf(nodup, row, g, gG, cwS, n, fl, best, b1)) =
    %er : FH.FH.GuessSpec(G, C_root, n_root, has_buf, nodup, g, S, n, fl, best, _)
    hr2
  %eb1 : P.ChunkSpec(1n+p, inf, G, gs, C_root, n_root, has_buf, nodup, S, limit,
           SolveFast.step(1n+p, gt, 1n, Nil{}, gG, cwS, n, nodup, fl, inf,
             Nil{}, Nil{}, 0n, best, SolveFast.dummy_step_zero(), False{},
             False{},
             SolveFast.guess_items_buf(nodup, row, g, gG, cwS, n, fl, best, _)))
  P.walk_pop_go(p, G, gs, C_root, n_root, has_buf, rwsG, cwS, S, nodup, mode,
    inf, g, t, tail, best, limit,
    SolveFast.guess_items_buf(nodup, row, g, gG, cwS, n, fl, best, b1), hr1,
    erwsG, hrwsG, wg, ele, hz, h1, h3, h6, ai, nd, hbest, hok, hd, hinv, ecif,
    rec)

def P.walk_cons(+p: Nat, +G: +List<+List<Nat>>,
    +gs: +List<+List<Nat>>,
    +C_root: +List<+List<Nat>>, +n_root: Nat, +has_buf: Bool,
    +rwsG: +List<FT.FT.RowWord>, +cwS: +List<SolveFast.CWord>,
    +S: +List<+List<Nat>>, +nodup: Bool, +mode: FOpt.FOpt.FloorMode, +inf: Nat,
    +row: U32, +g: +List<Nat>, +t: +List<FT.FT.RowWord>, +tail: SolveFast.GList,
    +best: SolveRef.Best, +limit: Nat, buf: SolveFast.Buf5,
    +hbuf: FH.FH.BufOk(G, C_root, n_root, has_buf, nodup, buf), dn: Bool,
    +edn: {dn == SolveFast.is_floor_hit(nodup,
                   FOpt.FOpt.floor_val(mode, Groups.len_words(S)), best) : Bool},
    +erwsG: {FT.FT.rws_words(rwsG) == G : +List<+List<Nat>>},
    +hrwsG: {FH.FH.rws_ok_if(has_buf, G, n_root, rwsG) == True{} : Bool},
    +ecwS: {SolveFast.cwords_words(cwS) == S : +List<+List<Nat>>},
    +hcwS: {FH.FH.cwords_ok_if(has_buf, G, C_root, n_root, cwS) == True{} : Bool},
    +hrow: {FH.FH.gentry_ok_if(has_buf, G, n_root, row, g) == True{} : Bool},
    +wg: {Tree.member_word(g, G) == True{} : Bool},
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +h3: {Nat.is_lt(3n, inf) == True{} : Bool},
    +h6: {Nat.is_lt(6n, inf) == True{} : Bool},
    +ai: {FO.FO.all_in_ref(S, G) == True{} : Bool},
    +nd: {FN.FN.nodup_ok(nodup, S) == True{} : Bool},
    +hbest_lim: {Nat.is_le(Eval.Eval.cost_of(best), limit) == True{} : Bool},
    +hlim_inf: {Nat.is_le(limit, inf) == True{} : Bool},
    +hok: {FVal.FV.best_ok_b(limit, G, S, best) == True{} : Bool},
    +hinv: {FOpt.FOpt.floor_inv(mode, p, inf, G, S, best) == True{} : Bool},
    ecif: FOpt.FOpt.EClassIf(
            Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
            p, inf, G, C_root, n_root, has_buf, nodup,
            Groups.groups_build(g, S, Nil{})),
    rec: @best2: SolveRef.Best -> @buf3: SolveFast.Buf5 ->
         FH.FH.BufOk(G, C_root, n_root, has_buf, nodup, buf3) ->
         {FVal.FV.best_ok_b(limit, G, S, best2) == True{} : Bool} ->
         {Nat.is_le(Eval.Eval.cost_of(best2), Eval.Eval.cost_of(best))
          == True{} : Bool} ->
         {Nat.is_le(Eval.Eval.cost_of(best2),
            Eval.Eval.cost_of(Eval.Eval.guess(p, G, S, g, inf, best)))
          == True{} : Bool} ->
         P.ChunkSpec(1n+p, inf, G, gs, C_root, n_root, has_buf, nodup, S, limit,
           SolveFast.step(1n+p, FT.FT.glist_of_rws(t, tail), 0n, Nil{},
             FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS,
             Groups.len_words(S), nodup,
             FOpt.FOpt.floor_val(mode, Groups.len_words(S)), inf,
             Nil{}, Nil{}, 0n, best2, SolveFast.dummy_step_zero(), False{},
             SolveFast.is_floor_hit(nodup,
               FOpt.FOpt.floor_val(mode, Groups.len_words(S)), best2),
             SolveFast.GuessRes{Nil{}, buf3}))) ->
  P.ChunkSpec(1n+p, inf, G, gs, C_root, n_root, has_buf, nodup, S, limit,
    SolveFast.step(1n+p,
      SolveFast.GTry{row, g, FT.FT.glist_of_rws(t, tail)},
      0n, Nil{}, FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS,
      Groups.len_words(S), nodup, FOpt.FOpt.floor_val(mode, Groups.len_words(S)),
      inf, Nil{}, Nil{}, 0n, best, SolveFast.dummy_step_zero(), False{}, dn,
      SolveFast.GuessRes{Nil{}, buf})):
  match dn:
    case True{}:
      +n : Nat = Groups.len_words(S)
      +fl : Nat = FOpt.FOpt.floor_val(mode, n)
      +gG : SolveFast.GList = FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{})
      +gt : SolveFast.GList = FT.FT.glist_of_rws(t, tail)
      +hbest = NatProof.Nat.is_le_trans(Eval.Eval.cost_of(best), limit, inf,
                 hbest_lim, hlim_inf)
      +ht = Equal.sym(Bool, True{}, SolveFast.is_floor_hit(nodup, fl, best), edn)
      +hjr : {P.job_res_gs_b(1n+p, inf, G, gs, S, limit, best) == True{} : Bool} =
        FO.FO.bool_and_intro(FVal.FV.best_ok_b(limit, G, S, best),
          Bool.and(Nat.is_le(Eval.Eval.cost_of(best), limit),
            Nat.is_le(Eval.Eval.cost_of(best),
              Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, gs, Eval.Eval.dummy_inf(inf))))),
          hok,
          FO.FO.bool_and_intro(Nat.is_le(Eval.Eval.cost_of(best), limit),
            Nat.is_le(Eval.Eval.cost_of(best),
              Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, gs, Eval.Eval.dummy_inf(inf)))),
            hbest_lim,
            P.floor_hit_le_evals(mode, p, inf, G, S, gs, nodup, best, nd, ele, hz,
              hbest, hinv, ht)))
      P.chunk_spec_transport(1n+p, inf, G, gs, C_root, n_root, has_buf, nodup,
        S, limit, SolveFast.StepRes{best, buf},
        SolveFast.step(1n+p, SolveFast.GTry{row, g, gt}, 0n, Nil{}, gG, cwS, n,
          nodup, fl, inf, Nil{}, Nil{}, 0n, best, SolveFast.dummy_step_zero(),
          False{}, True{}, SolveFast.GuessRes{Nil{}, buf}),
        Equal.sym(SolveFast.StepRes,
          SolveFast.step(1n+p, SolveFast.GTry{row, g, gt}, 0n, Nil{}, gG, cwS,
            n, nodup, fl, inf, Nil{}, Nil{}, 0n, best,
            SolveFast.dummy_step_zero(), False{}, True{},
            SolveFast.GuessRes{Nil{}, buf}),
          SolveFast.StepRes{best, buf},
          FS.FS.done_exit(p, SolveFast.GTry{row, g, gt}, gG, cwS, n, nodup, fl,
            inf, best, SolveFast.GuessRes{Nil{}, buf})),
        Arr.DPair{hjr, hbuf})
    case False{}:
      +n : Nat = Groups.len_words(S)
      +fl : Nat = FOpt.FOpt.floor_val(mode, n)
      +gG : SolveFast.GList = FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{})
      +gt : SolveFast.GList = FT.FT.glist_of_rws(t, tail)
      +hbest = NatProof.Nat.is_le_trans(Eval.Eval.cost_of(best), limit, inf,
                 hbest_lim, hlim_inf)
      +hd = Equal.sym(Bool, False{}, SolveFast.is_floor_hit(nodup, fl, best), edn)
      P.chunk_spec_transport(1n+p, inf, G, gs, C_root, n_root, has_buf, nodup,
        S, limit,
        SolveFast.step(1n+p, gt, 1n, Nil{}, gG, cwS, n, nodup, fl, inf, Nil{},
          Nil{}, 0n, best, SolveFast.dummy_step_zero(), False{}, False{},
          SolveFast.guess_items_buf(nodup, row, g, gG, cwS, n, fl, best, buf)),
        SolveFast.step(1n+p, SolveFast.GTry{row, g, gt}, 0n, Nil{}, gG, cwS, n,
          nodup, fl, inf, Nil{}, Nil{}, 0n, best, SolveFast.dummy_step_zero(),
          False{}, False{}, SolveFast.GuessRes{Nil{}, buf}),
        Equal.sym(SolveFast.StepRes,
          SolveFast.step(1n+p, SolveFast.GTry{row, g, gt}, 0n, Nil{}, gG, cwS,
            n, nodup, fl, inf, Nil{}, Nil{}, 0n, best,
            SolveFast.dummy_step_zero(), False{}, False{},
            SolveFast.GuessRes{Nil{}, buf}),
          SolveFast.step(1n+p, gt, 1n, Nil{}, gG, cwS, n, nodup, fl, inf,
            Nil{}, Nil{}, 0n, best, SolveFast.dummy_step_zero(), False{},
            False{},
            SolveFast.guess_items_buf(nodup, row, g, gG, cwS, n, fl, best, buf)),
          FS.FS.pop_guess_succ(p, row, g, gt, gG, cwS, n, nodup, fl, inf, best,
            buf)),
        P.walk_pop_dup(p, G, gs, C_root, n_root, has_buf, rwsG, cwS, S, nodup,
          mode, inf, row, g, t, tail, best, limit, buf, hbuf,
          FH.FH.buf_dup(buf), erwsG, hrwsG, ecwS, hcwS, hrow, wg, ele, hz, h1,
          h3, h6, ai, nd, hbest, hok, hd, hinv, ecif, rec))

def P.glist_walk(+rws: +List<FT.FT.RowWord>, +p: Nat,
    +G: +List<+List<Nat>>, +gs: +List<+List<Nat>>,
    +C_root: +List<+List<Nat>>, +n_root: Nat,
    +has_buf: Bool, +rwsG: +List<FT.FT.RowWord>, +cwS: +List<SolveFast.CWord>,
    +S: +List<+List<Nat>>, +nodup: Bool, +mode: FOpt.FOpt.FloorMode, +inf: Nat,
    +tail: SolveFast.GList, +best: SolveRef.Best, +limit: Nat,
    buf: SolveFast.Buf5,
    +hbuf: FH.FH.BufOk(G, C_root, n_root, has_buf, nodup, buf),
    +erwsG: {FT.FT.rws_words(rwsG) == G : +List<+List<Nat>>},
    +hrwsG: {FH.FH.rws_ok_if(has_buf, G, n_root, rwsG) == True{} : Bool},
    +ecwS: {SolveFast.cwords_words(cwS) == S : +List<+List<Nat>>},
    +hcwS: {FH.FH.cwords_ok_if(has_buf, G, C_root, n_root, cwS) == True{} : Bool},
    +hg_in: {FO.FO.all_in_ref(FT.FT.rws_words(rws), G) == True{} : Bool},
    +hrws: {FH.FH.rws_ok_if(has_buf, G, n_root, rws) == True{} : Bool},
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +h3: {Nat.is_lt(3n, inf) == True{} : Bool},
    +h6: {Nat.is_lt(6n, inf) == True{} : Bool},
    +ai: {FO.FO.all_in_ref(S, G) == True{} : Bool},
    +nd: {FN.FN.nodup_ok(nodup, S) == True{} : Bool},
    +hbest_lim: {Nat.is_le(Eval.Eval.cost_of(best), limit) == True{} : Bool},
    +hlim_inf: {Nat.is_le(limit, inf) == True{} : Bool},
    +hok: {FVal.FV.best_ok_b(limit, G, S, best) == True{} : Bool},
    +hinv: {FOpt.FOpt.floor_inv(mode, p, inf, G, S, best) == True{} : Bool},
    f: FOpt.FOpt.EByGs(p, inf, G, C_root, n_root, has_buf, S, nodup,
         FT.FT.rws_words(rws)),
    k_tail:
      @best_end: SolveRef.Best -> @buf_end: SolveFast.Buf5 ->
      FH.FH.BufOk(G, C_root, n_root, has_buf, nodup, buf_end) ->
      {FVal.FV.best_ok_b(limit, G, S, best_end) == True{} : Bool} ->
      {Nat.is_le(Eval.Eval.cost_of(best_end), Eval.Eval.cost_of(best))
       == True{} : Bool} ->
      {Nat.is_le(Eval.Eval.cost_of(best_end),
         Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf,
           FT.FT.rws_words(rws), best))) == True{} : Bool} ->
      P.ChunkSpec(1n+p, inf, G, gs, C_root, n_root, has_buf, nodup, S, limit,
        SolveFast.step(1n+p, tail, 0n, Nil{},
          FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS, Groups.len_words(S),
          nodup, FOpt.FOpt.floor_val(mode, Groups.len_words(S)), inf,
          Nil{}, Nil{}, 0n, best_end, SolveFast.dummy_step_zero(), False{},
          SolveFast.is_floor_hit(nodup,
            FOpt.FOpt.floor_val(mode, Groups.len_words(S)), best_end),
          SolveFast.GuessRes{Nil{}, buf_end}))) ->
  P.ChunkSpec(1n+p, inf, G, gs, C_root, n_root, has_buf, nodup, S, limit,
    SolveFast.step(1n+p, FT.FT.glist_of_rws(rws, tail), 0n, Nil{},
      FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS, Groups.len_words(S),
      nodup, FOpt.FOpt.floor_val(mode, Groups.len_words(S)), inf,
      Nil{}, Nil{}, 0n, best, SolveFast.dummy_step_zero(), False{},
      SolveFast.is_floor_hit(nodup,
        FOpt.FOpt.floor_val(mode, Groups.len_words(S)), best),
      SolveFast.GuessRes{Nil{}, buf})):
  match rws:
    case Nil{}:
      k_tail(best, buf, hbuf, hok,
        NatProof.Nat.is_le_refl(Eval.Eval.cost_of(best)),
        NatProof.Nat.is_le_refl(Eval.Eval.cost_of(best)))
    case Con{rw, t}:
      match rw:
        case FT.RowWord{+row, +g}:
          (ecif, ft) = f
          +wg = FO.FO.all_in_head(g, FT.FT.rws_words(t), G, hg_in)
          +ht_in = FO.FO.all_in_tail(g, FT.FT.rws_words(t), G, hg_in)
          +hrow = FOpt.FOpt.rws_ok_if_head(has_buf, G, n_root, row, g, t, hrws)
          +ht_ok = FOpt.FOpt.rws_ok_if_tail(has_buf, G, n_root, row, g, t, hrws)
          P.walk_cons(p, G, gs, C_root, n_root, has_buf, rwsG, cwS, S, nodup,
            mode, inf, row, g, t, tail, best, limit, buf, hbuf,
            SolveFast.is_floor_hit(nodup,
              FOpt.FOpt.floor_val(mode, Groups.len_words(S)), best), {==},
            erwsG, hrwsG, ecwS, hcwS, hrow, wg, ele, hz, h1, h3, h6, ai, nd,
            hbest_lim, hlim_inf, hok, hinv, ecif,
            +best2 => buf2 => +hbuf2 => +hok2 => +hleb => +hleg =>
              P.glist_walk(t, p, G, gs, C_root, n_root, has_buf, rwsG, cwS, S,
                nodup, mode, inf, tail, best2, limit, buf2, hbuf2, erwsG, hrwsG,
                ecwS, hcwS, ht_in, ht_ok, ele, hz, h1, h3, h6, ai, nd,
                NatProof.Nat.is_le_trans(Eval.Eval.cost_of(best2),
                  Eval.Eval.cost_of(best), limit, hleb, hbest_lim),
                hlim_inf, hok2,
                FOpt.FOpt.floor_inv_mono(mode, p, inf, G, S, best, best2, hleb, hinv),
                ft,
                +best_end => buf_end => +hbuf_end => +hok_end => +hle_b2 => +hle_t =>
                  k_tail(best_end, buf_end, hbuf_end, hok_end,
                    NatProof.Nat.is_le_trans(Eval.Eval.cost_of(best_end),
                      Eval.Eval.cost_of(best2), Eval.Eval.cost_of(best),
                      hle_b2, hleb),
                    NatProof.Nat.is_le_trans(Eval.Eval.cost_of(best_end),
                      Eval.Eval.cost_of(
                        Eval.Eval.guesses(1n+p, G, S, inf, FT.FT.rws_words(t),
                          best2)),
                      Eval.Eval.cost_of(
                        Eval.Eval.guesses(1n+p, G, S, inf, FT.FT.rws_words(t),
                          Eval.Eval.guess(p, G, S, g, inf, best))),
                      hle_t,
                      FVal.FV.eval_guesses_mono(p, G, S, inf,
                        FT.FT.rws_words(t), best2,
                        Eval.Eval.guess(p, G, S, g, inf, best), hleg)))))

# ---------------------------------------------------------------------------
# The chunk leaf: one `step` over any valid root guess list
# ---------------------------------------------------------------------------

def P.job_res_gs_of_spec(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +gs: +List<+List<Nat>>, +C_root: +List<+List<Nat>>, +n_root: Nat,
    +has_buf: Bool, +nodup: Bool, +S: +List<+List<Nat>>, +limit: Nat,
    sr: SolveFast.StepRes,
    +hspec: P.ChunkSpec(fuel, inf, G, gs, C_root, n_root, has_buf, nodup, S,
              limit, sr)) ->
  {P.job_res_gs_b(fuel, inf, G, gs, S, limit,
     SolveFast.step_res_best(sr)) == True{} : Bool}:
  match sr:
    case SolveFast.StepRes{res, buf2}:
      Arr.Arr.dpair_l(
        {P.job_res_gs_b(fuel, inf, G, gs, S, limit, res) == True{} : Bool},
        FH.FH.BufOk(G, C_root, n_root, has_buf, nodup, buf2), hspec)

def P.chunk_direct(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +gs: +List<+List<Nat>>, +cs: +List<+List<Nat>>, +has_buf: Bool,
    +rws: +List<FT.FT.RowWord>, +rwsG: +List<FT.FT.RowWord>,
    +cwS: +List<SolveFast.CWord>, +nodup: Bool, +b0: SolveRef.Best,
    buf0: SolveFast.Buf5,
    +erwsG: {FT.FT.rws_words(rwsG) == G : +List<+List<Nat>>},
    +hrwsG: {FH.FH.rws_ok_if(has_buf, G, Groups.len_words(cs), rwsG)
             == True{} : Bool},
    +ecwS: {SolveFast.cwords_words(cwS) == cs : +List<+List<Nat>>},
    +hcwS: {FH.FH.cwords_ok_if(has_buf, G, cs, Groups.len_words(cs), cwS)
            == True{} : Bool},
    +erws: {FT.FT.rws_words(rws) == gs : +List<+List<Nat>>},
    +hrws: {FH.FH.rws_ok_if(has_buf, G, Groups.len_words(cs), rws)
            == True{} : Bool},
    +hg_in: {FO.FO.all_in_ref(gs, G) == True{} : Bool},
    +ele: {Nat.is_le(Groups.len_words(cs), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +h3: {Nat.is_lt(3n, inf) == True{} : Bool},
    +h6: {Nat.is_lt(6n, inf) == True{} : Bool},
    +ai: {FO.FO.all_in_ref(cs, G) == True{} : Bool},
    +hnd: {FN.FN.nodup_ok(nodup, cs) == True{} : Bool},
    +hbest0: {Nat.is_le(Eval.Eval.cost_of(b0), inf) == True{} : Bool},
    +hok0: {FVal.FV.best_ok_b(inf, G, cs, b0) == True{} : Bool},
    +hbuf0: FH.FH.BufOk(G, cs, Groups.len_words(cs), has_buf, nodup, buf0),
    fgs: FOpt.FOpt.EByGs(p, inf, G, cs, Groups.len_words(cs), has_buf, cs,
          nodup, gs)) ->
  P.ChunkSpec(1n+p, inf, G, gs, cs, Groups.len_words(cs), has_buf, nodup, cs,
    inf,
    SolveFast.step(1n+p, FT.FT.glist_of_rws(rws, SolveFast.GEnd{}), 0n, Nil{},
      FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS, Groups.len_words(cs),
      nodup, SolveFast.init_floor(Groups.len_words(cs)), inf,
      Nil{}, Nil{}, 0n, b0, SolveFast.dummy_step_zero(), False{},
      SolveFast.is_floor_hit(nodup,
        SolveFast.init_floor(Groups.len_words(cs)), b0),
      SolveFast.GuessRes{Nil{}, buf0})):
  +n : Nat = Groups.len_words(cs)
  fgs_rws : FOpt.FOpt.EByGs(p, inf, G, cs, n, has_buf, cs, nodup,
                FT.FT.rws_words(rws)) =
    FOpt.FOpt.eby_gs_transport(p, inf, G, cs, n, has_buf, cs, nodup,
      gs, FT.FT.rws_words(rws),
      Equal.sym(+List<+List<Nat>>, FT.FT.rws_words(rws), gs, erws), fgs)
  +hg_in2 : {FO.FO.all_in_ref(FT.FT.rws_words(rws), G) == True{} : Bool} =
    Equal.trans(Bool, FO.FO.all_in_ref(FT.FT.rws_words(rws), G),
      FO.FO.all_in_ref(gs, G), True{},
      Equal.cong(+List<+List<Nat>>, Bool, l => FO.FO.all_in_ref(l, G),
        FT.FT.rws_words(rws), gs, erws), hg_in)
  P.glist_walk(rws, p, G, gs, cs, n, has_buf, rwsG, cwS, cs, nodup,
    FOpt.FloorInit{}, inf, SolveFast.GEnd{}, b0, inf, buf0, hbuf0,
    erwsG, hrwsG, ecwS, hcwS, hg_in2, hrws, ele, hz, h1, h3, h6, ai, hnd,
    hbest0, NatProof.Nat.is_le_refl(inf), hok0, {==}, fgs_rws,
    +best_end => buf_end => +hbuf_end => +hok_end => +hle_b0 => +hle_rws =>
      +hle_gs : {Nat.is_le(Eval.Eval.cost_of(best_end),
                    Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, cs, inf, gs,
                      b0))) == True{} : Bool} =
        Fold.OQ.le_cong_r(Eval.Eval.cost_of(best_end),
          Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, cs, inf,
            FT.FT.rws_words(rws), b0)),
          Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, cs, inf, gs, b0)),
          Equal.cong(+List<+List<Nat>>, Nat,
            l => Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, cs, inf, l, b0)),
            FT.FT.rws_words(rws), gs, erws), hle_rws)
      +hle_inf : {Nat.is_le(Eval.Eval.cost_of(best_end), inf)
                  == True{} : Bool} =
        NatProof.Nat.is_le_trans(Eval.Eval.cost_of(best_end),
          Eval.Eval.cost_of(b0), inf, hle_b0, hbest0)
      +hle_dummy : {Nat.is_le(Eval.Eval.cost_of(best_end),
                     Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, cs, inf, gs,
                       Eval.Eval.dummy_inf(inf)))) == True{} : Bool} =
        NatProof.Nat.is_le_trans(Eval.Eval.cost_of(best_end),
          Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, cs, inf, gs, b0)),
          Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, cs, inf, gs,
            Eval.Eval.dummy_inf(inf))),
          hle_gs,
          FVal.FV.eval_guesses_le_from_inf(1n+p, inf, G, cs, gs, b0, hbest0))
      +hjr : {P.job_res_gs_b(1n+p, inf, G, gs, cs, inf, best_end)
              == True{} : Bool} =
        FO.FO.bool_and_intro(FVal.FV.best_ok_b(inf, G, cs, best_end),
          Bool.and(Nat.is_le(Eval.Eval.cost_of(best_end), inf),
            Nat.is_le(Eval.Eval.cost_of(best_end),
              Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, cs, inf, gs,
                Eval.Eval.dummy_inf(inf))))),
          hok_end,
          FO.FO.bool_and_intro(Nat.is_le(Eval.Eval.cost_of(best_end), inf),
            Nat.is_le(Eval.Eval.cost_of(best_end),
              Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, cs, inf, gs,
                Eval.Eval.dummy_inf(inf)))),
            hle_inf, hle_dummy))
      Arr.DPair{hjr, hbuf_end})


# ---------------------------------------------------------------------------
# Fold and accumulator helpers
# ---------------------------------------------------------------------------

def P.or_true_l(+a: Bool, +b: Bool, +ha: {a == True{} : Bool}) ->
  {Bool.or(a, b) == True{} : Bool}:
  Equal.cong(Bool, Bool, x => Bool.or(x, b), a, True{}, ha)

def P.or_true_r(a: Bool, +b: Bool, +hb: {b == True{} : Bool}) ->
  {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      hb

def P.fold_unfold(+r: SolveRef.Best, +rest: +List<SolveRef.Best>,
    +best: SolveRef.Best) ->
  {SolveK.fold_results(r <> rest, best)
   == SolveK.fold_results(rest, FC.FC.better_best(r, best)) : SolveRef.Best}:
  match r:
    case SolveRef.Best{+tree, +cost}:
      {==}

def P.fold_single(+r: SolveRef.Best, +best: SolveRef.Best) ->
  {SolveK.fold_results(r <> Nil{}, best)
   == FC.FC.better_best(r, best) : SolveRef.Best}:
  match r:
    case SolveRef.Best{+tree, +cost}:
      {==}

def P.fold_le_best(+rs: +List<SolveRef.Best>, +best: SolveRef.Best) ->
  {Nat.is_le(Eval.Eval.cost_of(SolveK.fold_results(rs, best)),
     Eval.Eval.cost_of(best)) == True{} : Bool}:
  match rs:
    case Nil{}:
      NatProof.Nat.is_le_refl(Eval.Eval.cost_of(best))
    case Con{+r, +t}:
      +e = P.fold_unfold(r, t, best)
      +ih = NatProof.Nat.is_le_trans(
              Eval.Eval.cost_of(SolveK.fold_results(t,
                FC.FC.better_best(r, best))),
              Eval.Eval.cost_of(FC.FC.better_best(r, best)),
              Eval.Eval.cost_of(best),
              P.fold_le_best(t, FC.FC.better_best(r, best)),
              FVal.FV.better_best_le_r(r, best))
      Fold.OQ.le_cong_l(Eval.Eval.cost_of(SolveK.fold_results(r <> t, best)),
        Eval.Eval.cost_of(SolveK.fold_results(t, FC.FC.better_best(r, best))),
        Eval.Eval.cost_of(best),
        Equal.cong(SolveRef.Best, Nat, Eval.Eval.cost_of,
          SolveK.fold_results(r <> t, best),
          SolveK.fold_results(t, FC.FC.better_best(r, best)), e),
        ih)

def P.fold_append(+xs: +List<SolveRef.Best>, +ys: +List<SolveRef.Best>,
    +best: SolveRef.Best) ->
  {SolveK.fold_results(List.append(&2, SolveRef.Best, xs, ys), best)
   == SolveK.fold_results(ys, SolveK.fold_results(xs, best))
   : SolveRef.Best}:
  match xs:
    case Nil{}:
      {==}
    case Con{+r, +t}:
      +e1 = P.fold_unfold(r, List.append(&2, SolveRef.Best, t, ys), best)
      +e2 = P.fold_unfold(r, t, best)
      +e3 = Equal.cong(SolveRef.Best, SolveRef.Best,
              a => SolveK.fold_results(ys, a),
              SolveK.fold_results(r <> t, best),
              SolveK.fold_results(t, FC.FC.better_best(r, best)), e2)
      Equal.trans(SolveRef.Best,
        SolveK.fold_results(r <> List.append(&2, SolveRef.Best, t, ys), best),
        SolveK.fold_results(List.append(&2, SolveRef.Best, t, ys),
          FC.FC.better_best(r, best)),
        SolveK.fold_results(ys, SolveK.fold_results(r <> t, best)),
        e1,
        Equal.trans(SolveRef.Best,
          SolveK.fold_results(List.append(&2, SolveRef.Best, t, ys),
            FC.FC.better_best(r, best)),
          SolveK.fold_results(ys,
            SolveK.fold_results(t, FC.FC.better_best(r, best))),
          SolveK.fold_results(ys, SolveK.fold_results(r <> t, best)),
          P.fold_append(t, ys, FC.FC.better_best(r, best)),
          Equal.sym(SolveRef.Best,
            SolveK.fold_results(ys, SolveK.fold_results(r <> t, best)),
            SolveK.fold_results(ys,
              SolveK.fold_results(t, FC.FC.better_best(r, best))), e3)))

def P.elt_ok_better(+limit: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +a: SolveRef.Best, +b: SolveRef.Best,
    +ha: {GR.GR.elt_ok(limit, G, S, a) == True{} : Bool},
    +hb: {GR.GR.elt_ok(limit, G, S, b) == True{} : Bool}) ->
  {GR.GR.elt_ok(limit, G, S, FC.FC.better_best(a, b)) == True{} : Bool}:
  +hoka = Logic.Proof.and_true_l(FVal.FV.best_ok_b(limit, G, S, a),
            Nat.is_le(Eval.Eval.cost_of(a), limit), ha)
  +hca = Logic.Proof.and_true_r(FVal.FV.best_ok_b(limit, G, S, a),
           Nat.is_le(Eval.Eval.cost_of(a), limit), ha)
  +hokb = Logic.Proof.and_true_l(FVal.FV.best_ok_b(limit, G, S, b),
            Nat.is_le(Eval.Eval.cost_of(b), limit), hb)
  FO.FO.bool_and_intro(
    FVal.FV.best_ok_b(limit, G, S, FC.FC.better_best(a, b)),
    Nat.is_le(Eval.Eval.cost_of(FC.FC.better_best(a, b)), limit),
    P.best_ok_better(limit, G, S, a, b, hoka, hokb),
    NatProof.Nat.is_le_trans(Eval.Eval.cost_of(FC.FC.better_best(a, b)),
      Eval.Eval.cost_of(a), limit, FVal.FV.better_best_le_l(a, b), hca))

def P.ok_list(+limit: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +rs: +List<SolveRef.Best>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case Con{r, t}:
      Bool.and(GR.GR.elt_ok(limit, G, S, r), P.ok_list(limit, G, S, t))

def P.ok_list_append(+limit: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +xs: +List<SolveRef.Best>,
    +ys: +List<SolveRef.Best>,
    +hx: {P.ok_list(limit, G, S, xs) == True{} : Bool},
    +hy: {P.ok_list(limit, G, S, ys) == True{} : Bool}) ->
  {P.ok_list(limit, G, S, List.append(&2, SolveRef.Best, xs, ys))
   == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case Con{+r, +t}:
      +hr = Logic.Proof.and_true_l(GR.GR.elt_ok(limit, G, S, r),
              P.ok_list(limit, G, S, t), hx)
      +ht = Logic.Proof.and_true_r(GR.GR.elt_ok(limit, G, S, r),
              P.ok_list(limit, G, S, t), hx)
      FO.FO.bool_and_intro(GR.GR.elt_ok(limit, G, S, r),
        P.ok_list(limit, G, S, List.append(&2, SolveRef.Best, t, ys)),
        hr, P.ok_list_append(limit, G, S, t, ys, ht, hy))

def P.ok_list_fold(+limit: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +rs: +List<SolveRef.Best>,
    +best: SolveRef.Best,
    +h: {P.ok_list(limit, G, S, rs) == True{} : Bool},
    +hb: {GR.GR.elt_ok(limit, G, S, best) == True{} : Bool}) ->
  {GR.GR.elt_ok(limit, G, S, SolveK.fold_results(rs, best)) == True{} : Bool}:
  match rs:
    case Nil{}:
      hb
    case Con{+r, +t}:
      match r:
        case SolveRef.Best{+tree, +cost}:
          +hr = Logic.Proof.and_true_l(
                  GR.GR.elt_ok(limit, G, S, SolveRef.Best{tree, cost}),
                  P.ok_list(limit, G, S, t), h)
          +ht = Logic.Proof.and_true_r(
                  GR.GR.elt_ok(limit, G, S, SolveRef.Best{tree, cost}),
                  P.ok_list(limit, G, S, t), h)
          P.ok_list_fold(limit, G, S, t,
            FC.FC.better_best(SolveRef.Best{tree, cost}, best), ht,
            P.elt_ok_better(limit, G, S, SolveRef.Best{tree, cost}, best,
              hr, hb))

def P.elt_ok_of_job_res(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +gs: +List<+List<Nat>>, +S: +List<+List<Nat>>, +res: SolveRef.Best,
    +h: {P.job_res_gs_b(fuel, inf, G, gs, S, inf, res) == True{} : Bool}) ->
  {GR.GR.elt_ok(inf, G, S, res) == True{} : Bool}:
  +hok = Logic.Proof.and_true_l(FVal.FV.best_ok_b(inf, G, S, res),
           Bool.and(Nat.is_le(Eval.Eval.cost_of(res), inf),
             Nat.is_le(Eval.Eval.cost_of(res),
               Eval.Eval.cost_of(Eval.Eval.guesses(fuel, G, S, inf, gs,
                 Eval.Eval.dummy_inf(inf))))), h)
  +hr = Logic.Proof.and_true_r(FVal.FV.best_ok_b(inf, G, S, res),
          Bool.and(Nat.is_le(Eval.Eval.cost_of(res), inf),
            Nat.is_le(Eval.Eval.cost_of(res),
              Eval.Eval.cost_of(Eval.Eval.guesses(fuel, G, S, inf, gs,
                Eval.Eval.dummy_inf(inf))))), h)
  +hle = Logic.Proof.and_true_l(Nat.is_le(Eval.Eval.cost_of(res), inf),
           Nat.is_le(Eval.Eval.cost_of(res),
             Eval.Eval.cost_of(Eval.Eval.guesses(fuel, G, S, inf, gs,
               Eval.Eval.dummy_inf(inf)))), hr)
  FO.FO.bool_and_intro(FVal.FV.best_ok_b(inf, G, S, res),
    Nat.is_le(Eval.Eval.cost_of(res), inf), hok, hle)

def P.le_gs_of_job_res(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +gs: +List<+List<Nat>>, +S: +List<+List<Nat>>, +res: SolveRef.Best,
    +h: {P.job_res_gs_b(fuel, inf, G, gs, S, inf, res) == True{} : Bool}) ->
  {Nat.is_le(Eval.Eval.cost_of(res),
     Eval.Eval.cost_of(Eval.Eval.guesses(fuel, G, S, inf, gs,
       Eval.Eval.dummy_inf(inf)))) == True{} : Bool}:
  +hr = Logic.Proof.and_true_r(FVal.FV.best_ok_b(inf, G, S, res),
          Bool.and(Nat.is_le(Eval.Eval.cost_of(res), inf),
            Nat.is_le(Eval.Eval.cost_of(res),
              Eval.Eval.cost_of(Eval.Eval.guesses(fuel, G, S, inf, gs,
                Eval.Eval.dummy_inf(inf))))), h)
  Logic.Proof.and_true_r(Nat.is_le(Eval.Eval.cost_of(res), inf),
    Nat.is_le(Eval.Eval.cost_of(res),
      Eval.Eval.cost_of(Eval.Eval.guesses(fuel, G, S, inf, gs,
        Eval.Eval.dummy_inf(inf)))), hr)

# ---------------------------------------------------------------------------
# `SolveK.chunk_best` over any valid `RootGuess` list and valid initial bound
# ---------------------------------------------------------------------------

def P.chunk_best_rgs(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +cs: +List<+List<Nat>>, +nd: Bool, +has_buf: Bool,
    +rgs: +List<Greedy.RootGuess>, +b0: SolveRef.Best, buf0: SolveFast.Buf5,
    +en: {Groups.len_words(cs) == 1n+p : Nat},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +h3: {Nat.is_lt(3n, inf) == True{} : Bool},
    +h6: {Nat.is_lt(6n, inf) == True{} : Bool},
    +ai: {FO.FO.all_in_ref(cs, G) == True{} : Bool},
    +hnd: {FN.FN.nodup_ok(nd, cs) == True{} : Bool},
    +hrgs: {GR.GR.rgs_ok_b(has_buf, G, Groups.len_words(cs), rgs) == True{} : Bool},
    +hb0: {GR.GR.elt_ok(inf, G, cs, b0) == True{} : Bool},
    +hbuf0: FH.FH.BufOk(G, cs, Groups.len_words(cs), has_buf, nd, buf0)) ->
  {P.job_res_gs_b(1n+p, inf, G, GR.GR.rgs_words(rgs), cs, inf,
     SolveK.chunk_best(1n+p, rgs, SolveFast.glist_of_guesses(G, 0, 1),
       SolveFast.build_cwords(cs, G, 0, U32.from_nat(Groups.len_words(G))),
       Groups.len_words(cs), nd, SolveFast.init_floor(Groups.len_words(cs)),
       inf, b0, buf0)) == True{} : Bool}:
  +n : Nat = Groups.len_words(cs)
  +gs : +List<+List<Nat>> = GR.GR.rgs_words(rgs)
  +rws : +List<FT.FT.RowWord> = GR.GR.rgs_to_rws(rgs)
  +rwsG : +List<FT.FT.RowWord> = FT.FT.guesses_to_rws(G, 0, 1)
  +cwS : +List<SolveFast.CWord> =
    SolveFast.build_cwords(cs, G, 0, U32.from_nat(Groups.len_words(G)))
  +erws = GR.GR.rgs_to_rws_words(rgs)
  +hrws = GR.GR.rgs_ok_to_rws(has_buf, G, n, rgs, hrgs)
  +hg_in = GR.GR.rgs_ok_to_all_in(has_buf, G, n, rgs, hrgs)
  +erwsG = FT.FT.guesses_to_rws_words(G, 0, 1)
  +hrwsG = FOpt.FOpt.guesses_to_rws_ok_if(has_buf, G, n)
  +ecwS = FT.FT.build_cwords_words(cs, G, 0, U32.from_nat(Groups.len_words(G)))
  +hcwS = FOpt.FOpt.build_cwords_ok_if(has_buf, G, cs, n, ai)
  +ele : {Nat.is_le(n, 1n+p) == True{} : Bool} =
    Fold.OQ.le_cong_l(n, 1n+p, 1n+p, en, NatProof.Nat.is_le_refl(1n+p))
  +hok0 = Logic.Proof.and_true_l(FVal.FV.best_ok_b(inf, G, cs, b0),
            Nat.is_le(Eval.Eval.cost_of(b0), inf), hb0)
  +hbest0 = Logic.Proof.and_true_r(FVal.FV.best_ok_b(inf, G, cs, b0),
              Nat.is_le(Eval.Eval.cost_of(b0), inf), hb0)
  +eg_rgs = Equal.sym(SolveFast.GList, Greedy.glist_of_rgs(rgs),
              FT.FT.glist_of_rws(rws, SolveFast.GEnd{}), GR.GR.glist_of_rgs_eq(rgs))
  +eg_G = Equal.sym(SolveFast.GList, SolveFast.glist_of_guesses(G, 0, 1),
            FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}),
            FT.FT.glist_of_guesses_eq(G, 0, 1))
  GR.GR.with_dup_buf(
    {P.job_res_gs_b(1n+p, inf, G, gs, cs, inf,
       SolveK.chunk_best(1n+p, rgs, SolveFast.glist_of_guesses(G, 0, 1),
         cwS, n, nd, SolveFast.init_floor(n), inf, b0, buf0)) == True{} : Bool},
    buf0,
    b1 => b2 => +eb1 => +eb2 =>
    +hbuf1 = FH.FH.buf_ok_transport(G, cs, n, has_buf, nd, buf0, b1,
               Equal.sym(SolveFast.Buf5, b1, buf0, eb1), hbuf0)
    fseg : FOpt.FOpt.EFlat(p, inf, G, cs, n, has_buf, nd,
              MV.MV.next_guess(gs, cs)) =
      FOpt.FOpt.eflat(p, inf, G, cs, n, has_buf, nd,
        MV.MV.next_guess(gs, cs), MV.MV.any_bounds(p, gs, cs, ele),
        hz, h1, h3, h6, FO.FO.all_in_next_guess(gs, cs, G, ai),
        FN.FN.nodup_ok_next_guess(nd, gs, cs, hnd))
    fgs : FOpt.FOpt.EByGs(p, inf, G, cs, n, has_buf, cs, nd, gs) =
      FOpt.FOpt.eby_gs(p, inf, G, cs, n, has_buf, cs, nd, gs, fseg)
    +hspec1 = P.chunk_direct(p, inf, G, gs, cs, has_buf, rws, rwsG, cwS, nd,
                b0, b1, erwsG, hrwsG, ecwS, hcwS, erws, hrws, hg_in, ele, hz,
                h1, h3, h6, ai, hnd, hbest0, hok0, hbuf1, fgs)
    +eb12 : {b1 == b2 : SolveFast.Buf5} =
      Equal.trans(SolveFast.Buf5, b1, buf0, b2, eb1,
        Equal.sym(SolveFast.Buf5, b2, buf0, eb2))
    +hspec2 : P.ChunkSpec(1n+p, inf, G, gs, cs, n, has_buf, nd, cs, inf,
                SolveFast.step(1n+p, FT.FT.glist_of_rws(rws, SolveFast.GEnd{}),
                  0n, Nil{}, FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS,
                  n, nd, SolveFast.init_floor(n), inf, Nil{}, Nil{}, 0n, b0,
                  SolveFast.dummy_step_zero(), False{},
                  SolveFast.is_floor_hit(nd, SolveFast.init_floor(n), b0),
                  SolveFast.GuessRes{Nil{}, b2})) =
      %eb12 : P.ChunkSpec(1n+p, inf, G, gs, cs, n, has_buf, nd, cs, inf,
                SolveFast.step(1n+p, FT.FT.glist_of_rws(rws, SolveFast.GEnd{}),
                  0n, Nil{}, FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS,
                  n, nd, SolveFast.init_floor(n), inf, Nil{}, Nil{}, 0n, b0,
                  SolveFast.dummy_step_zero(), False{},
                  SolveFast.is_floor_hit(nd, SolveFast.init_floor(n), b0),
                  SolveFast.GuessRes{Nil{}, _}))
      hspec1
    +hjr2 = P.job_res_gs_of_spec(1n+p, inf, G, gs, cs, n, has_buf, nd, cs, inf,
              SolveFast.step(1n+p, FT.FT.glist_of_rws(rws, SolveFast.GEnd{}),
                0n, Nil{}, FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS,
                n, nd, SolveFast.init_floor(n), inf, Nil{}, Nil{}, 0n, b0,
                SolveFast.dummy_step_zero(), False{},
                SolveFast.is_floor_hit(nd, SolveFast.init_floor(n), b0),
                SolveFast.GuessRes{Nil{}, b2}), hspec2)
    %eg_rgs :
      {P.job_res_gs_b(1n+p, inf, G, gs, cs, inf,
         SolveFast.step_res_best(
           SolveFast.step(1n+p, _, 0n, Nil{},
             SolveFast.glist_of_guesses(G, 0, 1), cwS, n, nd,
             SolveFast.init_floor(n), inf, Nil{}, Nil{}, 0n, b0,
             SolveFast.dummy_step_zero(), False{},
             SolveFast.is_floor_hit(nd, SolveFast.init_floor(n), b0),
             SolveFast.GuessRes{Nil{}, buf0}))) == True{} : Bool}
    %eg_G :
      {P.job_res_gs_b(1n+p, inf, G, gs, cs, inf,
         SolveFast.step_res_best(
           SolveFast.step(1n+p, FT.FT.glist_of_rws(rws, SolveFast.GEnd{}),
             0n, Nil{}, _, cwS, n, nd, SolveFast.init_floor(n), inf, Nil{},
             Nil{}, 0n, b0, SolveFast.dummy_step_zero(), False{},
             SolveFast.is_floor_hit(nd, SolveFast.init_floor(n), b0),
             SolveFast.GuessRes{Nil{}, buf0}))) == True{} : Bool}
    %eb2 :
      {P.job_res_gs_b(1n+p, inf, G, gs, cs, inf,
         SolveFast.step_res_best(
           SolveFast.step(1n+p, FT.FT.glist_of_rws(rws, SolveFast.GEnd{}),
             0n, Nil{}, FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS, n, nd,
             SolveFast.init_floor(n), inf, Nil{}, Nil{}, 0n, b0,
             SolveFast.dummy_step_zero(), False{},
             SolveFast.is_floor_hit(nd, SolveFast.init_floor(n), b0),
             SolveFast.GuessRes{Nil{}, _}))) == True{} : Bool}
    hjr2)

# ---------------------------------------------------------------------------
# Round-robin splitting (`deal_even` / `deal_odd`) and `par_chunks`
# ---------------------------------------------------------------------------

def P.deal_even_ok(+has_buf: Bool, +G: +List<+List<Nat>>, +n_root: Nat,
    +xs: +List<Greedy.RootGuess>,
    +h: {GR.GR.rgs_ok_b(has_buf, G, n_root, xs) == True{} : Bool}) ->
  {GR.GR.rgs_ok_b(has_buf, G, n_root, SolveK.deal_even(xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      match t:
        case Nil{}:
          h
        case Con{+y, +rest}:
          +hx = Logic.Proof.and_true_l(GR.GR.rg_ok_b(has_buf, G, n_root, x),
                  GR.GR.rgs_ok_b(has_buf, G, n_root, y <> rest), h)
          +ht = Logic.Proof.and_true_r(GR.GR.rg_ok_b(has_buf, G, n_root, x),
                  GR.GR.rgs_ok_b(has_buf, G, n_root, y <> rest), h)
          +hr = Logic.Proof.and_true_r(GR.GR.rg_ok_b(has_buf, G, n_root, y),
                  GR.GR.rgs_ok_b(has_buf, G, n_root, rest), ht)
          FO.FO.bool_and_intro(GR.GR.rg_ok_b(has_buf, G, n_root, x),
            GR.GR.rgs_ok_b(has_buf, G, n_root, SolveK.deal_even(rest)),
            hx, P.deal_even_ok(has_buf, G, n_root, rest, hr))

def P.deal_odd_ok(+has_buf: Bool, +G: +List<+List<Nat>>, +n_root: Nat,
    +xs: +List<Greedy.RootGuess>,
    +h: {GR.GR.rgs_ok_b(has_buf, G, n_root, xs) == True{} : Bool}) ->
  {GR.GR.rgs_ok_b(has_buf, G, n_root, SolveK.deal_odd(xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      match t:
        case Nil{}:
          {==}
        case Con{+y, +rest}:
          +ht = Logic.Proof.and_true_r(GR.GR.rg_ok_b(has_buf, G, n_root, x),
                  GR.GR.rgs_ok_b(has_buf, G, n_root, y <> rest), h)
          +hy = Logic.Proof.and_true_l(GR.GR.rg_ok_b(has_buf, G, n_root, y),
                  GR.GR.rgs_ok_b(has_buf, G, n_root, rest), ht)
          +hr = Logic.Proof.and_true_r(GR.GR.rg_ok_b(has_buf, G, n_root, y),
                  GR.GR.rgs_ok_b(has_buf, G, n_root, rest), ht)
          FO.FO.bool_and_intro(GR.GR.rg_ok_b(has_buf, G, n_root, y),
            GR.GR.rgs_ok_b(has_buf, G, n_root, SolveK.deal_odd(rest)),
            hy, P.deal_odd_ok(has_buf, G, n_root, rest, hr))

def P.or_cons_mono(+w: +List<Nat>, +gx: +List<Nat>, +gy: +List<Nat>,
    +ls: +List<+List<Nat>>, +rs: +List<+List<Nat>>, ml: Bool,
    +eml: {ml == Tree.member_word(w, ls) : Bool},
    +hor: {Bool.or(ml, Tree.member_word(w, rs)) == True{} : Bool}) ->
  {Bool.or(Tree.member_word(w, gx <> ls), Tree.member_word(w, gy <> rs))
   == True{} : Bool}:
  match ml:
    case True{}:
      P.or_true_l(Tree.member_word(w, gx <> ls), Tree.member_word(w, gy <> rs),
        FN.FN.member_cons_r(w, gx, ls,
          Equal.sym(Bool, True{}, Tree.member_word(w, ls), eml)))
    case False{}:
      P.or_true_r(Tree.member_word(w, gx <> ls), Tree.member_word(w, gy <> rs),
        FN.FN.member_cons_r(w, gy, rs, hor))

def P.deal_mem(+w: +List<Nat>, +xs: +List<Greedy.RootGuess>,
    +hm: {Tree.member_word(w, GR.GR.rgs_words(xs)) == True{} : Bool}) ->
  {Bool.or(Tree.member_word(w, GR.GR.rgs_words(SolveK.deal_even(xs))),
           Tree.member_word(w, GR.GR.rgs_words(SolveK.deal_odd(xs))))
   == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd(
        {Bool.or(Tree.member_word(w, Nil{}), Tree.member_word(w, Nil{}))
         == True{} : Bool},
        Logic.Proof.false_ne_true(hm))
    case Con{+x, +t}:
      match x:
        case Greedy.RootGuess{+rx, +gx}:
          match t:
            case Nil{}:
              P.or_true_l(
                Tree.member_word(w, gx <> Nil{}), False{}, hm)
            case Con{+y, +rest}:
              match y:
                case Greedy.RootGuess{+ry, +gy}:
                  GR.GR.member_cons_split(
                    {Bool.or(
                       Tree.member_word(w,
                         gx <> GR.GR.rgs_words(SolveK.deal_even(rest))),
                       Tree.member_word(w,
                         gy <> GR.GR.rgs_words(SolveK.deal_odd(rest))))
                     == True{} : Bool},
                    w, gx, gy <> GR.GR.rgs_words(rest), hm,
                    +ewx =>
                      +eqx : {Feedback.word_eq(w, gx) == True{} : Bool} =
                        Equal.trans(Bool, Feedback.word_eq(w, gx),
                          Feedback.word_eq(gx, gx), True{},
                          Equal.cong(+List<Nat>, Bool,
                            z => Feedback.word_eq(z, gx), w, gx, ewx),
                          FbProof.FbPrf.word_eq_refl(gx))
                      P.or_true_l(
                        Tree.member_word(w,
                          gx <> GR.GR.rgs_words(SolveK.deal_even(rest))),
                        Tree.member_word(w,
                          gy <> GR.GR.rgs_words(SolveK.deal_odd(rest))),
                        GR.GR.member_cons_l(w, gx,
                          GR.GR.rgs_words(SolveK.deal_even(rest)), eqx)),
                    +hm2 =>
                      GR.GR.member_cons_split(
                        {Bool.or(
                           Tree.member_word(w,
                             gx <> GR.GR.rgs_words(SolveK.deal_even(rest))),
                           Tree.member_word(w,
                             gy <> GR.GR.rgs_words(SolveK.deal_odd(rest))))
                         == True{} : Bool},
                        w, gy, GR.GR.rgs_words(rest), hm2,
                        +ewy =>
                          +eqy : {Feedback.word_eq(w, gy) == True{} : Bool} =
                            Equal.trans(Bool, Feedback.word_eq(w, gy),
                              Feedback.word_eq(gy, gy), True{},
                              Equal.cong(+List<Nat>, Bool,
                                z => Feedback.word_eq(z, gy), w, gy, ewy),
                              FbProof.FbPrf.word_eq_refl(gy))
                          P.or_true_r(
                            Tree.member_word(w,
                              gx <> GR.GR.rgs_words(SolveK.deal_even(rest))),
                            Tree.member_word(w,
                              gy <> GR.GR.rgs_words(SolveK.deal_odd(rest))),
                            GR.GR.member_cons_l(w, gy,
                              GR.GR.rgs_words(SolveK.deal_odd(rest)), eqy)),
                        +hm3 =>
                          P.or_cons_mono(w, gx, gy,
                            GR.GR.rgs_words(SolveK.deal_even(rest)),
                            GR.GR.rgs_words(SolveK.deal_odd(rest)),
                            Tree.member_word(w,
                              GR.GR.rgs_words(SolveK.deal_even(rest))),
                            {==}, P.deal_mem(w, rest, hm3))))

def P.par_chunks_ok(+d: Nat, +rgs: +List<Greedy.RootGuess>, +p: Nat,
    +inf: Nat, +G: +List<+List<Nat>>, +cs: +List<+List<Nat>>, +nd: Bool,
    +b0: SolveRef.Best,
    +en: {Groups.len_words(cs) == 1n+p : Nat},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +h3: {Nat.is_lt(3n, inf) == True{} : Bool},
    +h6: {Nat.is_lt(6n, inf) == True{} : Bool},
    +ai: {FO.FO.all_in_ref(cs, G) == True{} : Bool},
    +hnd: {FN.FN.nodup_ok(nd, cs) == True{} : Bool},
    +hrgs: {GR.GR.rgs_ok_b(FH.FH.mk_buf_has(nd, G, cs, Groups.len_words(cs)), G,
              Groups.len_words(cs), rgs) == True{} : Bool},
    +hb0: {GR.GR.elt_ok(inf, G, cs, b0) == True{} : Bool}) ->
  {P.ok_list(inf, G, cs,
     SolveK.par_chunks(d, rgs, 1n+p, G, SolveFast.glist_of_guesses(G, 0, 1),
       SolveFast.build_cwords(cs, G, 0, U32.from_nat(Groups.len_words(G))),
       cs, Groups.len_words(cs), nd, SolveFast.init_floor(Groups.len_words(cs)),
       inf, b0)) == True{} : Bool}:
  match d:
    case 0n:
      +n : Nat = Groups.len_words(cs)
      +hjr = P.chunk_best_rgs(p, inf, G, cs, nd, FH.FH.mk_buf_has(nd, G, cs, n),
               rgs, b0, SolveFast.mk_buf_tbl(nd, G, cs, n), en, hz, h1, h3, h6,
               ai, hnd, hrgs, hb0, FH.FH.mk_buf_tbl_ok(nd, G, cs, n, {==}))
      +helt = P.elt_ok_of_job_res(1n+p, inf, G, GR.GR.rgs_words(rgs), cs,
                SolveK.chunk_best(1n+p, rgs, SolveFast.glist_of_guesses(G, 0, 1),
                  SolveFast.build_cwords(cs, G, 0,
                    U32.from_nat(Groups.len_words(G))),
                  n, nd, SolveFast.init_floor(n), inf, b0,
                  SolveFast.mk_buf_tbl(nd, G, cs, n)), hjr)
      FO.FO.bool_and_intro(
        GR.GR.elt_ok(inf, G, cs,
          SolveK.chunk_best(1n+p, rgs, SolveFast.glist_of_guesses(G, 0, 1),
            SolveFast.build_cwords(cs, G, 0, U32.from_nat(Groups.len_words(G))),
            n, nd, SolveFast.init_floor(n), inf, b0,
            SolveFast.mk_buf_tbl(nd, G, cs, n))),
        True{}, helt, {==})
    case 1n+dp:
      match rgs:
        case Nil{}:
          {==}
        case Con{+w, +rest}:
          match rest:
            case Nil{}:
              +n : Nat = Groups.len_words(cs)
              +hjr = P.chunk_best_rgs(p, inf, G, cs, nd,
                       FH.FH.mk_buf_has(nd, G, cs, n), w <> Nil{}, b0,
                       SolveFast.mk_buf_tbl(nd, G, cs, n), en, hz, h1, h3, h6,
                       ai, hnd, hrgs, hb0,
                       FH.FH.mk_buf_tbl_ok(nd, G, cs, n, {==}))
              +helt = P.elt_ok_of_job_res(1n+p, inf, G,
                        GR.GR.rgs_words(w <> Nil{}), cs,
                        SolveK.chunk_best(1n+p, w <> Nil{},
                          SolveFast.glist_of_guesses(G, 0, 1),
                          SolveFast.build_cwords(cs, G, 0,
                            U32.from_nat(Groups.len_words(G))),
                          n, nd, SolveFast.init_floor(n), inf, b0,
                          SolveFast.mk_buf_tbl(nd, G, cs, n)), hjr)
              FO.FO.bool_and_intro(
                GR.GR.elt_ok(inf, G, cs,
                  SolveK.chunk_best(1n+p, w <> Nil{},
                    SolveFast.glist_of_guesses(G, 0, 1),
                    SolveFast.build_cwords(cs, G, 0,
                      U32.from_nat(Groups.len_words(G))),
                    n, nd, SolveFast.init_floor(n), inf, b0,
                    SolveFast.mk_buf_tbl(nd, G, cs, n))),
                True{}, helt, {==})
            case Con{+w2, +rest2}:
              +rgs0 : +List<Greedy.RootGuess> = w <> (w2 <> rest2)
              +n : Nat = Groups.len_words(cs)
              +hb = FH.FH.mk_buf_has(nd, G, cs, n)
              P.ok_list_append(inf, G, cs,
                SolveK.par_chunks(dp, SolveK.deal_even(rgs0), 1n+p, G,
                  SolveFast.glist_of_guesses(G, 0, 1),
                  SolveFast.build_cwords(cs, G, 0,
                    U32.from_nat(Groups.len_words(G))),
                  cs, n, nd, SolveFast.init_floor(n), inf, b0),
                SolveK.par_chunks(dp, SolveK.deal_odd(rgs0), 1n+p, G,
                  SolveFast.glist_of_guesses(G, 0, 1),
                  SolveFast.build_cwords(cs, G, 0,
                    U32.from_nat(Groups.len_words(G))),
                  cs, n, nd, SolveFast.init_floor(n), inf, b0),
                P.par_chunks_ok(dp, SolveK.deal_even(rgs0), p, inf, G, cs, nd,
                  b0, en, hz, h1, h3, h6, ai, hnd,
                  P.deal_even_ok(hb, G, n, rgs0, hrgs), hb0),
                P.par_chunks_ok(dp, SolveK.deal_odd(rgs0), p, inf, G, cs, nd,
                  b0, en, hz, h1, h3, h6, ai, hnd,
                  P.deal_odd_ok(hb, G, n, rgs0, hrgs), hb0))

def P.par_chunks_cand_split(+ra: +List<SolveRef.Best>,
    +rb: +List<SolveRef.Best>, +acc: SolveRef.Best, +cand_cost: Nat,
    +m_even: Bool, +m_odd: Bool,
    +hor: {Bool.or(m_even, m_odd) == True{} : Bool},
    kl: {m_even == True{} : Bool} ->
        {Nat.is_le(Eval.Eval.cost_of(SolveK.fold_results(ra, acc)), cand_cost)
         == True{} : Bool},
    kr: {m_odd == True{} : Bool} ->
        {Nat.is_le(Eval.Eval.cost_of(
           SolveK.fold_results(rb, SolveK.fold_results(ra, acc))), cand_cost)
         == True{} : Bool}) ->
  {Nat.is_le(
     Eval.Eval.cost_of(
       SolveK.fold_results(List.append(&2, SolveRef.Best, ra, rb), acc)),
     cand_cost) == True{} : Bool}:
  match m_even:
    case True{}:
      Fold.OQ.le_cong_l(
        Eval.Eval.cost_of(
          SolveK.fold_results(List.append(&2, SolveRef.Best, ra, rb), acc)),
        Eval.Eval.cost_of(
          SolveK.fold_results(rb, SolveK.fold_results(ra, acc))),
        cand_cost,
        Equal.cong(SolveRef.Best, Nat, Eval.Eval.cost_of,
          SolveK.fold_results(List.append(&2, SolveRef.Best, ra, rb), acc),
          SolveK.fold_results(rb, SolveK.fold_results(ra, acc)),
          P.fold_append(ra, rb, acc)),
        NatProof.Nat.is_le_trans(
          Eval.Eval.cost_of(
            SolveK.fold_results(rb, SolveK.fold_results(ra, acc))),
          Eval.Eval.cost_of(SolveK.fold_results(ra, acc)),
          cand_cost,
          P.fold_le_best(rb, SolveK.fold_results(ra, acc)),
          kl({==})))
    case False{}:
      Fold.OQ.le_cong_l(
        Eval.Eval.cost_of(
          SolveK.fold_results(List.append(&2, SolveRef.Best, ra, rb), acc)),
        Eval.Eval.cost_of(
          SolveK.fold_results(rb, SolveK.fold_results(ra, acc))),
        cand_cost,
        Equal.cong(SolveRef.Best, Nat, Eval.Eval.cost_of,
          SolveK.fold_results(List.append(&2, SolveRef.Best, ra, rb), acc),
          SolveK.fold_results(rb, SolveK.fold_results(ra, acc)),
          P.fold_append(ra, rb, acc)),
        kr(hor))

def P.par_chunks_cand_le(+d: Nat, +rgs: +List<Greedy.RootGuess>, +p: Nat,
    +inf: Nat, +G: +List<+List<Nat>>, +cs: +List<+List<Nat>>, +nd: Bool,
    +b0: SolveRef.Best, +acc: SolveRef.Best, +g: +List<Nat>,
    +en: {Groups.len_words(cs) == 1n+p : Nat},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +h3: {Nat.is_lt(3n, inf) == True{} : Bool},
    +h6: {Nat.is_lt(6n, inf) == True{} : Bool},
    +ai: {FO.FO.all_in_ref(cs, G) == True{} : Bool},
    +hnd: {FN.FN.nodup_ok(nd, cs) == True{} : Bool},
    +hrgs: {GR.GR.rgs_ok_b(FH.FH.mk_buf_has(nd, G, cs, Groups.len_words(cs)), G,
              Groups.len_words(cs), rgs) == True{} : Bool},
    +hb0: {GR.GR.elt_ok(inf, G, cs, b0) == True{} : Bool},
    +hm: {Tree.member_word(g, GR.GR.rgs_words(rgs)) == True{} : Bool},
    +hus: {Groups.groups_smaller(cs, Groups.groups_build(g, cs, Nil{}))
           == True{} : Bool}) ->
  {Nat.is_le(
     Eval.Eval.cost_of(
       SolveK.fold_results(
         SolveK.par_chunks(d, rgs, 1n+p, G,
           SolveFast.glist_of_guesses(G, 0, 1),
           SolveFast.build_cwords(cs, G, 0, U32.from_nat(Groups.len_words(G))),
           cs, Groups.len_words(cs), nd,
           SolveFast.init_floor(Groups.len_words(cs)), inf, b0),
         acc)),
     Fold.OQ.ks_cost(inf, cs,
       Eval.Eval.items(p, G, cs, g, Groups.groups_build(g, cs, Nil{}),
         Nil{}, 0n, inf))) == True{} : Bool}:
  match d:
    case 0n:
      +n : Nat = Groups.len_words(cs)
      +r = SolveK.chunk_best(1n+p, rgs, SolveFast.glist_of_guesses(G, 0, 1),
             SolveFast.build_cwords(cs, G, 0, U32.from_nat(Groups.len_words(G))),
             n, nd, SolveFast.init_floor(n), inf, b0,
             SolveFast.mk_buf_tbl(nd, G, cs, n))
      +hjr = P.chunk_best_rgs(p, inf, G, cs, nd, FH.FH.mk_buf_has(nd, G, cs, n),
               rgs, b0, SolveFast.mk_buf_tbl(nd, G, cs, n), en, hz, h1, h3, h6,
               ai, hnd, hrgs, hb0, FH.FH.mk_buf_tbl_ok(nd, G, cs, n, {==}))
      +hle_gs = P.le_gs_of_job_res(1n+p, inf, G, GR.GR.rgs_words(rgs), cs, r, hjr)
      +hle_c = NatProof.Nat.is_le_trans(
                 Eval.Eval.cost_of(r),
                 Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, cs, inf,
                   GR.GR.rgs_words(rgs), Eval.Eval.dummy_inf(inf))),
                 Fold.OQ.ks_cost(inf, cs,
                   Eval.Eval.items(p, G, cs, g,
                     Groups.groups_build(g, cs, Nil{}), Nil{}, 0n, inf)),
                 hle_gs,
                 OQGuess.OQ.guesses_le_cand(p, G, cs, inf, GR.GR.rgs_words(rgs),
                   g, Eval.Eval.dummy_inf(inf), hm, hus))
      Fold.OQ.le_cong_l(
        Eval.Eval.cost_of(SolveK.fold_results(r <> Nil{}, acc)),
        Eval.Eval.cost_of(FC.FC.better_best(r, acc)),
        Fold.OQ.ks_cost(inf, cs,
          Eval.Eval.items(p, G, cs, g, Groups.groups_build(g, cs, Nil{}),
            Nil{}, 0n, inf)),
        Equal.cong(SolveRef.Best, Nat, Eval.Eval.cost_of,
          SolveK.fold_results(r <> Nil{}, acc), FC.FC.better_best(r, acc),
          P.fold_single(r, acc)),
        NatProof.Nat.is_le_trans(Eval.Eval.cost_of(FC.FC.better_best(r, acc)),
          Eval.Eval.cost_of(r),
          Fold.OQ.ks_cost(inf, cs,
            Eval.Eval.items(p, G, cs, g, Groups.groups_build(g, cs, Nil{}),
              Nil{}, 0n, inf)),
          FVal.FV.better_best_le_l(r, acc), hle_c))
    case 1n+dp:
      match rgs:
        case Nil{}:
          Empty.absurd(
            {Nat.is_le(Eval.Eval.cost_of(acc),
               Fold.OQ.ks_cost(inf, cs,
                 Eval.Eval.items(p, G, cs, g,
                   Groups.groups_build(g, cs, Nil{}), Nil{}, 0n, inf)))
             == True{} : Bool},
            Logic.Proof.false_ne_true(hm))
        case Con{+w, +rest}:
          match rest:
            case Nil{}:
              +n : Nat = Groups.len_words(cs)
              +r = SolveK.chunk_best(1n+p, w <> Nil{},
                     SolveFast.glist_of_guesses(G, 0, 1),
                     SolveFast.build_cwords(cs, G, 0,
                       U32.from_nat(Groups.len_words(G))),
                     n, nd, SolveFast.init_floor(n), inf, b0,
                     SolveFast.mk_buf_tbl(nd, G, cs, n))
              +hjr = P.chunk_best_rgs(p, inf, G, cs, nd,
                       FH.FH.mk_buf_has(nd, G, cs, n), w <> Nil{}, b0,
                       SolveFast.mk_buf_tbl(nd, G, cs, n), en, hz, h1, h3, h6,
                       ai, hnd, hrgs, hb0,
                       FH.FH.mk_buf_tbl_ok(nd, G, cs, n, {==}))
              +hle_gs = P.le_gs_of_job_res(1n+p, inf, G,
                          GR.GR.rgs_words(w <> Nil{}), cs, r, hjr)
              +hle_c = NatProof.Nat.is_le_trans(
                         Eval.Eval.cost_of(r),
                         Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, cs, inf,
                           GR.GR.rgs_words(w <> Nil{}), Eval.Eval.dummy_inf(inf))),
                         Fold.OQ.ks_cost(inf, cs,
                           Eval.Eval.items(p, G, cs, g,
                             Groups.groups_build(g, cs, Nil{}), Nil{}, 0n, inf)),
                         hle_gs,
                         OQGuess.OQ.guesses_le_cand(p, G, cs, inf,
                           GR.GR.rgs_words(w <> Nil{}), g,
                           Eval.Eval.dummy_inf(inf), hm, hus))
              Fold.OQ.le_cong_l(
                Eval.Eval.cost_of(SolveK.fold_results(r <> Nil{}, acc)),
                Eval.Eval.cost_of(FC.FC.better_best(r, acc)),
                Fold.OQ.ks_cost(inf, cs,
                  Eval.Eval.items(p, G, cs, g,
                    Groups.groups_build(g, cs, Nil{}), Nil{}, 0n, inf)),
                Equal.cong(SolveRef.Best, Nat, Eval.Eval.cost_of,
                  SolveK.fold_results(r <> Nil{}, acc),
                  FC.FC.better_best(r, acc), P.fold_single(r, acc)),
                NatProof.Nat.is_le_trans(
                  Eval.Eval.cost_of(FC.FC.better_best(r, acc)),
                  Eval.Eval.cost_of(r),
                  Fold.OQ.ks_cost(inf, cs,
                    Eval.Eval.items(p, G, cs, g,
                      Groups.groups_build(g, cs, Nil{}), Nil{}, 0n, inf)),
                  FVal.FV.better_best_le_l(r, acc), hle_c))
            case Con{+w2, +rest2}:
              +rgs0 : +List<Greedy.RootGuess> = w <> (w2 <> rest2)
              +n : Nat = Groups.len_words(cs)
              +hb = FH.FH.mk_buf_has(nd, G, cs, n)
              +ra = SolveK.par_chunks(dp, SolveK.deal_even(rgs0), 1n+p, G,
                      SolveFast.glist_of_guesses(G, 0, 1),
                      SolveFast.build_cwords(cs, G, 0,
                        U32.from_nat(Groups.len_words(G))),
                      cs, n, nd, SolveFast.init_floor(n), inf, b0)
              +rb = SolveK.par_chunks(dp, SolveK.deal_odd(rgs0), 1n+p, G,
                      SolveFast.glist_of_guesses(G, 0, 1),
                      SolveFast.build_cwords(cs, G, 0,
                        U32.from_nat(Groups.len_words(G))),
                      cs, n, nd, SolveFast.init_floor(n), inf, b0)
              P.par_chunks_cand_split(ra, rb, acc,
                Fold.OQ.ks_cost(inf, cs,
                  Eval.Eval.items(p, G, cs, g,
                    Groups.groups_build(g, cs, Nil{}), Nil{}, 0n, inf)),
                Tree.member_word(g, GR.GR.rgs_words(SolveK.deal_even(rgs0))),
                Tree.member_word(g, GR.GR.rgs_words(SolveK.deal_odd(rgs0))),
                P.deal_mem(g, rgs0, hm),
                +hme =>
                  P.par_chunks_cand_le(dp, SolveK.deal_even(rgs0), p, inf, G,
                    cs, nd, b0, acc, g, en, hz, h1, h3, h6, ai, hnd,
                    P.deal_even_ok(hb, G, n, rgs0, hrgs), hb0, hme, hus),
                +hmo =>
                  P.par_chunks_cand_le(dp, SolveK.deal_odd(rgs0), p, inf, G,
                    cs, nd, b0, SolveK.fold_results(ra, acc), g, en, hz, h1,
                    h3, h6, ai, hnd, P.deal_odd_ok(hb, G, n, rgs0, hrgs),
                    hb0, hmo, hus))

# ---------------------------------------------------------------------------
# Pointwise optimality: any bound <= every usable candidate in `G` beats `ref`
# ---------------------------------------------------------------------------

def P.guess_fixed_go(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +cs: +List<+List<Nat>>, +g: +List<Nat>, +best: SolveRef.Best, us: Bool,
    +eus: {us == Groups.groups_smaller(cs, Groups.groups_build(g, cs, Nil{}))
           : Bool},
    hle: {Groups.groups_smaller(cs, Groups.groups_build(g, cs, Nil{}))
          == True{} : Bool} ->
         {Nat.is_le(Eval.Eval.cost_of(best),
            Fold.OQ.ks_cost(inf, cs,
              Eval.Eval.items(p, G, cs, g, Groups.groups_build(g, cs, Nil{}),
                Nil{}, 0n, inf))) == True{} : Bool}) ->
  {Eval.Eval.guess_bool(p, G, cs, g, Groups.groups_build(g, cs, Nil{}), inf,
     us, best) == best : SolveRef.Best}:
  match best:
    case SolveRef.Best{+bt, +bc}:
      match us:
        case False{}:
          {==}
        case True{}:
          +grps = Groups.groups_build(g, cs, Nil{})
          +its = Eval.Eval.items(p, G, cs, g, grps, Nil{}, 0n, inf)
          +cc = Fold.OQ.ks_cost(inf, cs, its)
          +ct = Fold.OQ.ks_tree(g, its)
          +hus : {Groups.groups_smaller(cs, grps) == True{} : Bool} =
            Equal.sym(Bool, True{}, Groups.groups_smaller(cs, grps), eus)
          +hc = hle(hus)
          +enlt : {False{} == Nat.is_lt(cc, bc) : Bool} =
            Equal.sym(Bool, Nat.is_lt(cc, bc), False{},
              ParElt.ParElt.not_lt_of_le(bc, cc, hc))
          Equal.trans(SolveRef.Best,
            Eval.Eval.guess_bool(p, G, cs, g, grps, inf, True{},
              SolveRef.Best{bt, bc}),
            SolveRef.better(cc, ct, SolveRef.Best{bt, bc}),
            SolveRef.Best{bt, bc},
            Fold.OQ.block_eq(inf, g, cs, its, SolveRef.Best{bt, bc}),
            ParElt.ParElt.pick_better(cc, ct, bt, bc, False{}, enlt))

def P.guesses_fixed_of_rgs_bound(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +cs: +List<+List<Nat>>, +ws: +List<+List<Nat>>, +rem: +List<+List<Nat>>,
    +best: SolveRef.Best,
    +hle_ws: {Nat.is_le(Eval.Eval.cost_of(best),
                Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, cs, inf, ws,
                  Eval.Eval.dummy_inf(inf)))) == True{} : Bool},
    +hcov: {GR.GR.all_usable_in(cs, rem, ws) == True{} : Bool}) ->
  {Eval.Eval.guesses(1n+p, G, cs, inf, rem, best) == best : SolveRef.Best}:
  match rem:
    case Nil{}:
      {==}
    case Con{+g, +t}:
      +us = Groups.groups_smaller(cs, Groups.groups_build(g, cs, Nil{}))
      +hg = Logic.Proof.and_true_l(
              Feedback.Bool.case(Bool, us, Tree.member_word(g, ws), True{}),
              GR.GR.all_usable_in(cs, t, ws), hcov)
      +ht = Logic.Proof.and_true_r(
              Feedback.Bool.case(Bool, us, Tree.member_word(g, ws), True{}),
              GR.GR.all_usable_in(cs, t, ws), hcov)
      +efg : {Eval.Eval.guess(p, G, cs, g, inf, best) == best : SolveRef.Best} =
        P.guess_fixed_go(p, inf, G, cs, g, best, us, {==},
          +hus =>
            +hm = GR.GR.all_usable_in_mem_go(cs, g, ws, us, {==}, hus, hg)
            NatProof.Nat.is_le_trans(
              Eval.Eval.cost_of(best),
              Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, cs, inf, ws,
                Eval.Eval.dummy_inf(inf))),
              Fold.OQ.ks_cost(inf, cs,
                Eval.Eval.items(p, G, cs, g, Groups.groups_build(g, cs, Nil{}),
                  Nil{}, 0n, inf)),
              hle_ws,
              OQGuess.OQ.guesses_le_cand(p, G, cs, inf, ws, g,
                Eval.Eval.dummy_inf(inf), hm, hus)))
      Equal.trans(SolveRef.Best,
        Eval.Eval.guesses(1n+p, G, cs, inf, t,
          Eval.Eval.guess(p, G, cs, g, inf, best)),
        Eval.Eval.guesses(1n+p, G, cs, inf, t, best),
        best,
        Equal.cong(SolveRef.Best, SolveRef.Best,
          b => Eval.Eval.guesses(1n+p, G, cs, inf, t, b),
          Eval.Eval.guess(p, G, cs, g, inf, best), best, efg),
        P.guesses_fixed_of_rgs_bound(p, inf, G, cs, ws, t, best, hle_ws, ht))

def P.guesses_fixed_of_par_chunks(+d: Nat, +rgs: +List<Greedy.RootGuess>,
    +p: Nat, +inf: Nat, +G: +List<+List<Nat>>, +cs: +List<+List<Nat>>,
    +nd: Bool, +b0: SolveRef.Best, +rem: +List<+List<Nat>>,
    +en: {Groups.len_words(cs) == 1n+p : Nat},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +h3: {Nat.is_lt(3n, inf) == True{} : Bool},
    +h6: {Nat.is_lt(6n, inf) == True{} : Bool},
    +ai: {FO.FO.all_in_ref(cs, G) == True{} : Bool},
    +hnd: {FN.FN.nodup_ok(nd, cs) == True{} : Bool},
    +hrgs: {GR.GR.rgs_ok_b(FH.FH.mk_buf_has(nd, G, cs, Groups.len_words(cs)), G,
              Groups.len_words(cs), rgs) == True{} : Bool},
    +hb0: {GR.GR.elt_ok(inf, G, cs, b0) == True{} : Bool},
    +hcov: {GR.GR.all_usable_in(cs, rem, GR.GR.rgs_words(rgs)) == True{} : Bool}) ->
  {Eval.Eval.guesses(1n+p, G, cs, inf, rem,
     SolveK.fold_results(
       SolveK.par_chunks(d, rgs, 1n+p, G,
         SolveFast.glist_of_guesses(G, 0, 1),
         SolveFast.build_cwords(cs, G, 0, U32.from_nat(Groups.len_words(G))),
         cs, Groups.len_words(cs), nd,
         SolveFast.init_floor(Groups.len_words(cs)), inf, b0),
       b0))
   == SolveK.fold_results(
        SolveK.par_chunks(d, rgs, 1n+p, G,
          SolveFast.glist_of_guesses(G, 0, 1),
          SolveFast.build_cwords(cs, G, 0, U32.from_nat(Groups.len_words(G))),
          cs, Groups.len_words(cs), nd,
          SolveFast.init_floor(Groups.len_words(cs)), inf, b0),
        b0) : SolveRef.Best}:
  match rem:
    case Nil{}:
      {==}
    case Con{+g, +t}:
      +n : Nat = Groups.len_words(cs)
      +best = SolveK.fold_results(
                SolveK.par_chunks(d, rgs, 1n+p, G,
                  SolveFast.glist_of_guesses(G, 0, 1),
                  SolveFast.build_cwords(cs, G, 0,
                    U32.from_nat(Groups.len_words(G))),
                  cs, n, nd, SolveFast.init_floor(n), inf, b0),
                b0)
      +us = Groups.groups_smaller(cs, Groups.groups_build(g, cs, Nil{}))
      +hg = Logic.Proof.and_true_l(
              Feedback.Bool.case(Bool, us,
                Tree.member_word(g, GR.GR.rgs_words(rgs)), True{}),
              GR.GR.all_usable_in(cs, t, GR.GR.rgs_words(rgs)), hcov)
      +ht = Logic.Proof.and_true_r(
              Feedback.Bool.case(Bool, us,
                Tree.member_word(g, GR.GR.rgs_words(rgs)), True{}),
              GR.GR.all_usable_in(cs, t, GR.GR.rgs_words(rgs)), hcov)
      +efg : {Eval.Eval.guess(p, G, cs, g, inf, best) == best : SolveRef.Best} =
        P.guess_fixed_go(p, inf, G, cs, g, best, us, {==},
          +hus =>
            +hm = GR.GR.all_usable_in_mem_go(cs, g, GR.GR.rgs_words(rgs), us, {==},
                    hus, hg)
            P.par_chunks_cand_le(d, rgs, p, inf, G, cs, nd, b0, b0, g, en, hz,
              h1, h3, h6, ai, hnd, hrgs, hb0, hm, hus))
      Equal.trans(SolveRef.Best,
        Eval.Eval.guesses(1n+p, G, cs, inf, t,
          Eval.Eval.guess(p, G, cs, g, inf, best)),
        Eval.Eval.guesses(1n+p, G, cs, inf, t, best),
        best,
        Equal.cong(SolveRef.Best, SolveRef.Best,
          b => Eval.Eval.guesses(1n+p, G, cs, inf, t, b),
          Eval.Eval.guess(p, G, cs, g, inf, best), best, efg),
        P.guesses_fixed_of_par_chunks(d, rgs, p, inf, G, cs, nd, b0, t, en,
          hz, h1, h3, h6, ai, hnd, hrgs, hb0, ht))

# ---------------------------------------------------------------------------
# Root bounds (`inf > 6`, `ref_p`, `after_prep`, `solve_chunked`)
# ---------------------------------------------------------------------------

def P.inf_gt6(+cs: +List<+List<Nat>>,
    +h3_le_n: {Nat.is_le(3n, Groups.len_words(cs)) == True{} : Bool}) ->
  {Nat.is_lt(6n, SolveRef.inf_of(Groups.len_words(cs))) == True{} : Bool}:
  +n : Nat = Groups.len_words(cs)
  +h9_le_sq : {Nat.is_le(9n, Nat.mul(n, n)) == True{} : Bool} =
    NatProof.Nat.is_le_trans(9n, Nat.mul(3n, n), Nat.mul(n, n),
      CBN.CB.is_le_mul_r(3n, n, 3n, h3_le_n),
      CBN.CB.is_le_mul_l(3n, n, n, h3_le_n))
  NatProof.Nat.is_le_lt_trans(6n, Nat.mul(n, n), SolveRef.inf_of(n),
    NatProof.Nat.is_le_trans(6n, 9n, Nat.mul(n, n), {==}, h9_le_sq),
    CBN.CB.lt_add_one(Nat.mul(n, n)))

def P.inf_gt3(+cs: +List<+List<Nat>>,
    +h3_le_n: {Nat.is_le(3n, Groups.len_words(cs)) == True{} : Bool}) ->
  {Nat.is_lt(3n, SolveRef.inf_of(Groups.len_words(cs))) == True{} : Bool}:
  NatProof.Nat.is_le_lt_trans(3n, 6n, SolveRef.inf_of(Groups.len_words(cs)),
    {==}, P.inf_gt6(cs, h3_le_n))

def P.inf_gt1(+cs: +List<+List<Nat>>,
    +h3_le_n: {Nat.is_le(3n, Groups.len_words(cs)) == True{} : Bool}) ->
  {Nat.is_lt(1n, SolveRef.inf_of(Groups.len_words(cs))) == True{} : Bool}:
  NatProof.Nat.is_le_lt_trans(1n, 6n, SolveRef.inf_of(Groups.len_words(cs)),
    {==}, P.inf_gt6(cs, h3_le_n))

def P.inf_gt0(+cs: +List<+List<Nat>>,
    +h3_le_n: {Nat.is_le(3n, Groups.len_words(cs)) == True{} : Bool}) ->
  {Nat.is_lt(0n, SolveRef.inf_of(Groups.len_words(cs))) == True{} : Bool}:
  NatProof.Nat.is_le_lt_trans(0n, 6n, SolveRef.inf_of(Groups.len_words(cs)),
    {==}, P.inf_gt6(cs, h3_le_n))

def P.ref_p(+G: +List<+List<Nat>>, +cs: +List<+List<Nat>>, +p: Nat) ->
    SolveRef.Best:
  SolveRef.step(1n+p, SolveRef.mk_schedule(G, cs), G, cs,
    SolveRef.inf_of(Groups.len_words(cs)), Nil{}, Nil{}, 0n,
    Eval.Eval.dummy_inf(SolveRef.inf_of(Groups.len_words(cs))),
    Eval.Eval.dummy_zero())

def P.opt_from_best(+G: +List<+List<Nat>>, +cs: +List<+List<Nat>>, +p: Nat,
    +T2: Tree.Tree, +best: SolveRef.Best,
    +helt: {GR.GR.elt_ok(SolveRef.inf_of(Groups.len_words(cs)), G, cs, best)
            == True{} : Bool},
    +efix: {Eval.Eval.guesses(1n+p, G, cs,
              SolveRef.inf_of(Groups.len_words(cs)), G, best)
            == best : SolveRef.Best},
    +opt: {Nat.is_le(Eval.Eval.cost_of(P.ref_p(G, cs, p)), Tree.cost(T2, cs))
           == True{} : Bool},
    +fin: {Nat.is_lt(Eval.Eval.cost_of(P.ref_p(G, cs, p)),
             SolveRef.inf_of(Groups.len_words(cs))) == True{} : Bool}) ->
  Exists(Tree.Tree, T =>
    {SolveRef.best_to_maybe(SolveRef.inf_of(Groups.len_words(cs)), best)
     == Some{T} : Maybe<Tree.Tree>}
    & {Nat.is_le(Tree.cost(T, cs), Tree.cost(T2, cs)) == True{} : Bool}):
  +inf : Nat = SolveRef.inf_of(Groups.len_words(cs))
  +hok = Logic.Proof.and_true_l(FVal.FV.best_ok_b(inf, G, cs, best),
           Nat.is_le(Eval.Eval.cost_of(best), inf), helt)
  +hbest = Logic.Proof.and_true_r(FVal.FV.best_ok_b(inf, G, cs, best),
             Nat.is_le(Eval.Eval.cost_of(best), inf), helt)
  +hle_ev = P.fixed_le_evals(1n+p, inf, G, cs, G, best, hbest, efix)
  +egs : {Eval.Eval.guesses(1n+p, G, cs, inf, G, Eval.Eval.dummy_inf(inf))
          == P.ref_p(G, cs, p) : SolveRef.Best} =
    Equal.sym(SolveRef.Best, P.ref_p(G, cs, p),
      Eval.Eval.guesses(1n+p, G, cs, inf, G, Eval.Eval.dummy_inf(inf)),
      Eval.Eval.guesses_step(p, G, cs, inf, G, Eval.Eval.dummy_inf(inf)))
  +hle_ref : {Nat.is_le(Eval.Eval.cost_of(best),
                Eval.Eval.cost_of(P.ref_p(G, cs, p))) == True{} : Bool} =
    Fold.OQ.le_cong_r(Eval.Eval.cost_of(best),
      Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, cs, inf, G,
        Eval.Eval.dummy_inf(inf))),
      Eval.Eval.cost_of(P.ref_p(G, cs, p)),
      Equal.cong(SolveRef.Best, Nat, Eval.Eval.cost_of,
        Eval.Eval.guesses(1n+p, G, cs, inf, G, Eval.Eval.dummy_inf(inf)),
        P.ref_p(G, cs, p), egs),
      hle_ev)
  +fin_best = NatProof.Nat.is_le_lt_trans(Eval.Eval.cost_of(best),
                Eval.Eval.cost_of(P.ref_p(G, cs, p)), inf, hle_ref, fin)
  +es = OC.OC.best_to_maybe_fin(inf, best, fin_best)
  +hext = FVal.FV.best_ok_extract(inf, G, cs, best, hok, fin_best)
  +hcost_t = Logic.Proof.and_true_r(
               FVal.FV.valid_b(Eval.Eval.tree_of(best), G, cs),
               Nat.is_le(Tree.cost(Eval.Eval.tree_of(best), cs),
                 Eval.Eval.cost_of(best)), hext)
  +hle = NatProof.Nat.is_le_trans(Tree.cost(Eval.Eval.tree_of(best), cs),
           Eval.Eval.cost_of(best), Tree.cost(T2, cs), hcost_t,
           NatProof.Nat.is_le_trans(Eval.Eval.cost_of(best),
             Eval.Eval.cost_of(P.ref_p(G, cs, p)), Tree.cost(T2, cs),
             hle_ref, opt))
  (Eval.Eval.tree_of(best), (es, hle))

def P.valid_from_job_res(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +gs: +List<+List<Nat>>, +cs: +List<+List<Nat>>, +best: SolveRef.Best,
    +T: Tree.Tree,
    +hjr: {P.job_res_gs_b(1n+p, inf, G, gs, cs, inf, best) == True{} : Bool},
    e: {SolveRef.best_to_maybe(inf, best) == Some{T} : Maybe<Tree.Tree>}) ->
  Tree.Valid(T, G, cs):
  +hok = Logic.Proof.and_true_l(
           FVal.FV.best_ok_b(inf, G, cs, best),
           Bool.and(Nat.is_le(Eval.Eval.cost_of(best), inf),
             Nat.is_le(Eval.Eval.cost_of(best),
               Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, cs, inf, gs,
                 Eval.Eval.dummy_inf(inf))))),
           hjr)
  FOpt.FOpt.valid_from_best_maybe(G, cs, inf, best, T, hok, e)

def P.opt_from_job_res(+p: Nat, +G: +List<+List<Nat>>,
    +gs: +List<+List<Nat>>, +cs: +List<+List<Nat>>, +best: SolveRef.Best,
    +T2: Tree.Tree,
    +hjr: {P.job_res_gs_b(1n+p, SolveRef.inf_of(Groups.len_words(cs)), G, gs,
             cs, SolveRef.inf_of(Groups.len_words(cs)), best) == True{} : Bool},
    +hcov: {GR.GR.all_usable_in(cs, G, gs) == True{} : Bool},
    +opt: {Nat.is_le(Eval.Eval.cost_of(P.ref_p(G, cs, p)), Tree.cost(T2, cs))
           == True{} : Bool},
    +fin: {Nat.is_lt(Eval.Eval.cost_of(P.ref_p(G, cs, p)),
             SolveRef.inf_of(Groups.len_words(cs))) == True{} : Bool}) ->
  Exists(Tree.Tree, T =>
    {SolveRef.best_to_maybe(SolveRef.inf_of(Groups.len_words(cs)), best)
     == Some{T} : Maybe<Tree.Tree>}
    & {Nat.is_le(Tree.cost(T, cs), Tree.cost(T2, cs)) == True{} : Bool}):
  +inf : Nat = SolveRef.inf_of(Groups.len_words(cs))
  +helt = P.elt_ok_of_job_res(1n+p, inf, G, gs, cs, best, hjr)
  +hle_ws = P.le_gs_of_job_res(1n+p, inf, G, gs, cs, best, hjr)
  +efix = P.guesses_fixed_of_rgs_bound(p, inf, G, cs, gs, G, best, hle_ws, hcov)
  P.opt_from_best(G, cs, p, T2, best, helt, efix, opt, fin)

def P.after_prep_valid(+d: Nat, +p: Nat, +G: +List<+List<Nat>>,
    +cs: +List<+List<Nat>>, +nd: Bool, pr: Greedy.RootPrepRes, +T: Tree.Tree,
    +en: {Groups.len_words(cs) == 1n+p : Nat},
    +h3n: {Nat.is_le(3n, Groups.len_words(cs)) == True{} : Bool},
    +ai: {FO.FO.all_in_ref(cs, G) == True{} : Bool},
    +hnd: {FN.FN.nodup_ok(nd, cs) == True{} : Bool},
    +hpr: GR.GR.RootPrepSpec(SolveRef.inf_of(Groups.len_words(cs)), G, cs,
            FH.FH.mk_buf_has(nd, G, cs, Groups.len_words(cs)), nd, pr),
    e: {SolveK.after_prep(d, G, SolveFast.glist_of_guesses(G, 0, 1),
          SolveFast.build_cwords(cs, G, 0, U32.from_nat(Groups.len_words(G))),
          cs, Groups.len_words(cs), nd,
          SolveFast.init_floor(Groups.len_words(cs)),
          SolveRef.inf_of(Groups.len_words(cs)), pr)
        == Some{T} : Maybe<Tree.Tree>}) ->
  Tree.Valid(T, G, cs):
  match d:
    case 0n:
      match pr:
        case Greedy.RootPrepRes{+b0, +rgs, buf0}:
          +n : Nat = Groups.len_words(cs)
          +inf : Nat = SolveRef.inf_of(n)
          +has_buf : Bool = FH.FH.mk_buf_has(nd, G, cs, n)
          +gG = SolveFast.glist_of_guesses(G, 0, 1)
          +cwS = SolveFast.build_cwords(cs, G, 0,
                   U32.from_nat(Groups.len_words(G)))
          +fl = SolveFast.init_floor(n)
          +hb0 = Arr.Arr.dpair_l({GR.GR.elt_ok(inf, G, cs, b0) == True{} : Bool},
                   Arr.Arr.DPair<{GR.GR.rgs_ok_b(has_buf, G, n, rgs) == True{} : Bool},
                     Arr.Arr.DPair<FH.FH.BufOk(G, cs, n, has_buf, nd, buf0),
                       {GR.GR.all_usable_in(cs, G, GR.GR.rgs_words(rgs)) == True{} : Bool}>>,
                   hpr)
          +r1 = Arr.Arr.dpair_r({GR.GR.elt_ok(inf, G, cs, b0) == True{} : Bool},
                  Arr.Arr.DPair<{GR.GR.rgs_ok_b(has_buf, G, n, rgs) == True{} : Bool},
                    Arr.Arr.DPair<FH.FH.BufOk(G, cs, n, has_buf, nd, buf0),
                      {GR.GR.all_usable_in(cs, G, GR.GR.rgs_words(rgs)) == True{} : Bool}>>,
                  hpr)
          +hrgs = Arr.Arr.dpair_l({GR.GR.rgs_ok_b(has_buf, G, n, rgs) == True{} : Bool},
                    Arr.Arr.DPair<FH.FH.BufOk(G, cs, n, has_buf, nd, buf0),
                      {GR.GR.all_usable_in(cs, G, GR.GR.rgs_words(rgs)) == True{} : Bool}>,
                    r1)
          +r2 = Arr.Arr.dpair_r({GR.GR.rgs_ok_b(has_buf, G, n, rgs) == True{} : Bool},
                  Arr.Arr.DPair<FH.FH.BufOk(G, cs, n, has_buf, nd, buf0),
                    {GR.GR.all_usable_in(cs, G, GR.GR.rgs_words(rgs)) == True{} : Bool}>,
                  r1)
          +hbuf0 = Arr.Arr.dpair_l(FH.FH.BufOk(G, cs, n, has_buf, nd, buf0),
                     {GR.GR.all_usable_in(cs, G, GR.GR.rgs_words(rgs)) == True{} : Bool},
                     r2)
          GR.GR.with_dup_buf(Tree.Valid(T, G, cs), buf0,
            b1 => b2 => +eb1 => +eb2 =>
            +hbuf1 = FH.FH.buf_ok_transport(G, cs, n, has_buf, nd, buf0, b1,
                       Equal.sym(SolveFast.Buf5, b1, buf0, eb1), hbuf0)
            +hjr_p = P.chunk_best_rgs(p, inf, G, cs, nd, has_buf, rgs, b0, b1,
                       en, P.inf_gt0(cs, h3n), P.inf_gt1(cs, h3n),
                       P.inf_gt3(cs, h3n), P.inf_gt6(cs, h3n), ai, hnd, hrgs,
                       hb0, hbuf1)
            +eb12 : {b1 == b2 : SolveFast.Buf5} =
              Equal.trans(SolveFast.Buf5, b1, buf0, b2, eb1,
                Equal.sym(SolveFast.Buf5, b2, buf0, eb2))
            +hjr2 : {P.job_res_gs_b(1n+p, inf, G, GR.GR.rgs_words(rgs), cs, inf,
                       SolveK.chunk_best(n, rgs, gG, cwS, n, nd, fl, inf, b0, b2))
                     == True{} : Bool} =
              %Equal.sym(Nat, n, 1n+p, en) :
                {P.job_res_gs_b(1n+p, inf, G, GR.GR.rgs_words(rgs), cs, inf,
                   SolveK.chunk_best(_, rgs, gG, cwS, n, nd, fl, inf, b0, b2))
                 == True{} : Bool}
              %eb12 :
                {P.job_res_gs_b(1n+p, inf, G, GR.GR.rgs_words(rgs), cs, inf,
                   SolveK.chunk_best(1n+p, rgs, gG, cwS, n, nd, fl, inf, b0, _))
                 == True{} : Bool}
              hjr_p
            +e2 : {SolveRef.best_to_maybe(inf,
                     SolveK.chunk_best(n, rgs, gG, cwS, n, nd, fl, inf, b0, b2))
                   == Some{T} : Maybe<Tree.Tree>} =
              %Equal.sym(SolveFast.Buf5, b2, buf0, eb2) :
                {SolveRef.best_to_maybe(inf,
                   SolveK.chunk_best(n, rgs, gG, cwS, n, nd, fl, inf, b0, _))
                 == Some{T} : Maybe<Tree.Tree>}
              e
            P.valid_from_job_res(p, inf, G, GR.GR.rgs_words(rgs), cs,
              SolveK.chunk_best(n, rgs, gG, cwS, n, nd, fl, inf, b0, b2),
              T, hjr2, e2))
    case 1n+dp:
      match pr:
        case Greedy.RootPrepRes{+b0, +rgs, buf0}:
          +n : Nat = Groups.len_words(cs)
          +inf : Nat = SolveRef.inf_of(n)
          +has_buf : Bool = FH.FH.mk_buf_has(nd, G, cs, n)
          +gG = SolveFast.glist_of_guesses(G, 0, 1)
          +cwS = SolveFast.build_cwords(cs, G, 0,
                   U32.from_nat(Groups.len_words(G)))
          +fl = SolveFast.init_floor(n)
          +hb0 = Arr.Arr.dpair_l({GR.GR.elt_ok(inf, G, cs, b0) == True{} : Bool},
                   Arr.Arr.DPair<{GR.GR.rgs_ok_b(has_buf, G, n, rgs) == True{} : Bool},
                     Arr.Arr.DPair<FH.FH.BufOk(G, cs, n, has_buf, nd, buf0),
                       {GR.GR.all_usable_in(cs, G, GR.GR.rgs_words(rgs)) == True{} : Bool}>>,
                   hpr)
          +r1 = Arr.Arr.dpair_r({GR.GR.elt_ok(inf, G, cs, b0) == True{} : Bool},
                  Arr.Arr.DPair<{GR.GR.rgs_ok_b(has_buf, G, n, rgs) == True{} : Bool},
                    Arr.Arr.DPair<FH.FH.BufOk(G, cs, n, has_buf, nd, buf0),
                      {GR.GR.all_usable_in(cs, G, GR.GR.rgs_words(rgs)) == True{} : Bool}>>,
                  hpr)
          +hrgs = Arr.Arr.dpair_l({GR.GR.rgs_ok_b(has_buf, G, n, rgs) == True{} : Bool},
                    Arr.Arr.DPair<FH.FH.BufOk(G, cs, n, has_buf, nd, buf0),
                      {GR.GR.all_usable_in(cs, G, GR.GR.rgs_words(rgs)) == True{} : Bool}>,
                    r1)
          +hokl_p = P.par_chunks_ok(1n+dp, rgs, p, inf, G, cs, nd, b0, en,
                      P.inf_gt0(cs, h3n), P.inf_gt1(cs, h3n),
                      P.inf_gt3(cs, h3n), P.inf_gt6(cs, h3n), ai, hnd, hrgs, hb0)
          +rs = SolveK.par_chunks(1n+dp, rgs, n, G, gG, cwS, cs, n, nd, fl, inf, b0)
          +hokl : {P.ok_list(inf, G, cs, rs) == True{} : Bool} =
            %Equal.sym(Nat, n, 1n+p, en) :
              {P.ok_list(inf, G, cs,
                 SolveK.par_chunks(1n+dp, rgs, _, G, gG, cwS, cs, n, nd, fl,
                   inf, b0)) == True{} : Bool}
            hokl_p
          +hf = P.ok_list_fold(inf, G, cs, rs, b0, hokl, hb0)
          +hok = Logic.Proof.and_true_l(
                   FVal.FV.best_ok_b(inf, G, cs, SolveK.fold_results(rs, b0)),
                   Nat.is_le(Eval.Eval.cost_of(SolveK.fold_results(rs, b0)), inf),
                   hf)
          FOpt.FOpt.valid_from_best_maybe(G, cs, inf,
            SolveK.fold_results(rs, b0), T, hok, e)

def P.after_prep_optimal(+d: Nat, +p: Nat, +G: +List<+List<Nat>>,
    +cs: +List<+List<Nat>>, +nd: Bool, pr: Greedy.RootPrepRes, +T2: Tree.Tree,
    +en: {Groups.len_words(cs) == 1n+p : Nat},
    +h3n: {Nat.is_le(3n, Groups.len_words(cs)) == True{} : Bool},
    +ai: {FO.FO.all_in_ref(cs, G) == True{} : Bool},
    +hnd: {FN.FN.nodup_ok(nd, cs) == True{} : Bool},
    +hpr: GR.GR.RootPrepSpec(SolveRef.inf_of(Groups.len_words(cs)), G, cs,
            FH.FH.mk_buf_has(nd, G, cs, Groups.len_words(cs)), nd, pr),
    +opt: {Nat.is_le(Eval.Eval.cost_of(P.ref_p(G, cs, p)), Tree.cost(T2, cs))
           == True{} : Bool},
    +fin: {Nat.is_lt(Eval.Eval.cost_of(P.ref_p(G, cs, p)),
             SolveRef.inf_of(Groups.len_words(cs))) == True{} : Bool}) ->
  Exists(Tree.Tree, T =>
    {SolveK.after_prep(d, G, SolveFast.glist_of_guesses(G, 0, 1),
       SolveFast.build_cwords(cs, G, 0, U32.from_nat(Groups.len_words(G))),
       cs, Groups.len_words(cs), nd,
       SolveFast.init_floor(Groups.len_words(cs)),
       SolveRef.inf_of(Groups.len_words(cs)), pr)
     == Some{T} : Maybe<Tree.Tree>}
    & {Nat.is_le(Tree.cost(T, cs), Tree.cost(T2, cs)) == True{} : Bool}):
  match d:
    case 0n:
      match pr:
        case Greedy.RootPrepRes{+b0, +rgs, buf0}:
          +n : Nat = Groups.len_words(cs)
          +inf : Nat = SolveRef.inf_of(n)
          +has_buf : Bool = FH.FH.mk_buf_has(nd, G, cs, n)
          +gG = SolveFast.glist_of_guesses(G, 0, 1)
          +cwS = SolveFast.build_cwords(cs, G, 0,
                   U32.from_nat(Groups.len_words(G)))
          +fl = SolveFast.init_floor(n)
          +hb0 = Arr.Arr.dpair_l({GR.GR.elt_ok(inf, G, cs, b0) == True{} : Bool},
                   Arr.Arr.DPair<{GR.GR.rgs_ok_b(has_buf, G, n, rgs) == True{} : Bool},
                     Arr.Arr.DPair<FH.FH.BufOk(G, cs, n, has_buf, nd, buf0),
                       {GR.GR.all_usable_in(cs, G, GR.GR.rgs_words(rgs)) == True{} : Bool}>>,
                   hpr)
          +r1 = Arr.Arr.dpair_r({GR.GR.elt_ok(inf, G, cs, b0) == True{} : Bool},
                  Arr.Arr.DPair<{GR.GR.rgs_ok_b(has_buf, G, n, rgs) == True{} : Bool},
                    Arr.Arr.DPair<FH.FH.BufOk(G, cs, n, has_buf, nd, buf0),
                      {GR.GR.all_usable_in(cs, G, GR.GR.rgs_words(rgs)) == True{} : Bool}>>,
                  hpr)
          +hrgs = Arr.Arr.dpair_l({GR.GR.rgs_ok_b(has_buf, G, n, rgs) == True{} : Bool},
                    Arr.Arr.DPair<FH.FH.BufOk(G, cs, n, has_buf, nd, buf0),
                      {GR.GR.all_usable_in(cs, G, GR.GR.rgs_words(rgs)) == True{} : Bool}>,
                    r1)
          +r2 = Arr.Arr.dpair_r({GR.GR.rgs_ok_b(has_buf, G, n, rgs) == True{} : Bool},
                  Arr.Arr.DPair<FH.FH.BufOk(G, cs, n, has_buf, nd, buf0),
                    {GR.GR.all_usable_in(cs, G, GR.GR.rgs_words(rgs)) == True{} : Bool}>,
                  r1)
          +hbuf0 = Arr.Arr.dpair_l(FH.FH.BufOk(G, cs, n, has_buf, nd, buf0),
                     {GR.GR.all_usable_in(cs, G, GR.GR.rgs_words(rgs)) == True{} : Bool},
                     r2)
          +hcov = Arr.Arr.dpair_r(FH.FH.BufOk(G, cs, n, has_buf, nd, buf0),
                    {GR.GR.all_usable_in(cs, G, GR.GR.rgs_words(rgs)) == True{} : Bool},
                    r2)
          GR.GR.with_dup_buf(
            Exists(Tree.Tree, T =>
              {SolveRef.best_to_maybe(inf,
                 SolveK.chunk_best(n, rgs, gG, cwS, n, nd, fl, inf, b0, buf0))
               == Some{T} : Maybe<Tree.Tree>}
              & {Nat.is_le(Tree.cost(T, cs), Tree.cost(T2, cs))
                 == True{} : Bool}),
            buf0,
            b1 => b2 => +eb1 => +eb2 =>
            +hbuf1 = FH.FH.buf_ok_transport(G, cs, n, has_buf, nd, buf0, b1,
                       Equal.sym(SolveFast.Buf5, b1, buf0, eb1), hbuf0)
            +hjr_p = P.chunk_best_rgs(p, inf, G, cs, nd, has_buf, rgs, b0, b1,
                       en, P.inf_gt0(cs, h3n), P.inf_gt1(cs, h3n),
                       P.inf_gt3(cs, h3n), P.inf_gt6(cs, h3n), ai, hnd, hrgs,
                       hb0, hbuf1)
            +eb12 : {b1 == b2 : SolveFast.Buf5} =
              Equal.trans(SolveFast.Buf5, b1, buf0, b2, eb1,
                Equal.sym(SolveFast.Buf5, b2, buf0, eb2))
            +hjr2 : {P.job_res_gs_b(1n+p, inf, G, GR.GR.rgs_words(rgs), cs, inf,
                       SolveK.chunk_best(n, rgs, gG, cwS, n, nd, fl, inf, b0, b2))
                     == True{} : Bool} =
              %Equal.sym(Nat, n, 1n+p, en) :
                {P.job_res_gs_b(1n+p, inf, G, GR.GR.rgs_words(rgs), cs, inf,
                   SolveK.chunk_best(_, rgs, gG, cwS, n, nd, fl, inf, b0, b2))
                 == True{} : Bool}
              %eb12 :
                {P.job_res_gs_b(1n+p, inf, G, GR.GR.rgs_words(rgs), cs, inf,
                   SolveK.chunk_best(1n+p, rgs, gG, cwS, n, nd, fl, inf, b0, _))
                 == True{} : Bool}
              hjr_p
            %eb2 :
              Exists(Tree.Tree, T =>
                {SolveRef.best_to_maybe(inf,
                   SolveK.chunk_best(n, rgs, gG, cwS, n, nd, fl, inf, b0, _))
                 == Some{T} : Maybe<Tree.Tree>}
                & {Nat.is_le(Tree.cost(T, cs), Tree.cost(T2, cs))
                   == True{} : Bool})
            P.opt_from_job_res(p, G, GR.GR.rgs_words(rgs), cs,
              SolveK.chunk_best(n, rgs, gG, cwS, n, nd, fl, inf, b0, b2),
              T2, hjr2, hcov, opt, fin))
    case 1n+dp:
      match pr:
        case Greedy.RootPrepRes{+b0, +rgs, buf0}:
          +n : Nat = Groups.len_words(cs)
          +inf : Nat = SolveRef.inf_of(n)
          +has_buf : Bool = FH.FH.mk_buf_has(nd, G, cs, n)
          +gG = SolveFast.glist_of_guesses(G, 0, 1)
          +cwS = SolveFast.build_cwords(cs, G, 0,
                   U32.from_nat(Groups.len_words(G)))
          +fl = SolveFast.init_floor(n)
          +hb0 = Arr.Arr.dpair_l({GR.GR.elt_ok(inf, G, cs, b0) == True{} : Bool},
                   Arr.Arr.DPair<{GR.GR.rgs_ok_b(has_buf, G, n, rgs) == True{} : Bool},
                     Arr.Arr.DPair<FH.FH.BufOk(G, cs, n, has_buf, nd, buf0),
                       {GR.GR.all_usable_in(cs, G, GR.GR.rgs_words(rgs)) == True{} : Bool}>>,
                   hpr)
          +r1 = Arr.Arr.dpair_r({GR.GR.elt_ok(inf, G, cs, b0) == True{} : Bool},
                  Arr.Arr.DPair<{GR.GR.rgs_ok_b(has_buf, G, n, rgs) == True{} : Bool},
                    Arr.Arr.DPair<FH.FH.BufOk(G, cs, n, has_buf, nd, buf0),
                      {GR.GR.all_usable_in(cs, G, GR.GR.rgs_words(rgs)) == True{} : Bool}>>,
                  hpr)
          +hrgs = Arr.Arr.dpair_l({GR.GR.rgs_ok_b(has_buf, G, n, rgs) == True{} : Bool},
                    Arr.Arr.DPair<FH.FH.BufOk(G, cs, n, has_buf, nd, buf0),
                      {GR.GR.all_usable_in(cs, G, GR.GR.rgs_words(rgs)) == True{} : Bool}>,
                    r1)
          +r2 = Arr.Arr.dpair_r({GR.GR.rgs_ok_b(has_buf, G, n, rgs) == True{} : Bool},
                  Arr.Arr.DPair<FH.FH.BufOk(G, cs, n, has_buf, nd, buf0),
                    {GR.GR.all_usable_in(cs, G, GR.GR.rgs_words(rgs)) == True{} : Bool}>,
                  r1)
          +hcov = Arr.Arr.dpair_r(FH.FH.BufOk(G, cs, n, has_buf, nd, buf0),
                    {GR.GR.all_usable_in(cs, G, GR.GR.rgs_words(rgs)) == True{} : Bool},
                    r2)
          +hokl_p = P.par_chunks_ok(1n+dp, rgs, p, inf, G, cs, nd, b0, en,
                      P.inf_gt0(cs, h3n), P.inf_gt1(cs, h3n),
                      P.inf_gt3(cs, h3n), P.inf_gt6(cs, h3n), ai, hnd, hrgs, hb0)
          +rs = SolveK.par_chunks(1n+dp, rgs, n, G, gG, cwS, cs, n, nd, fl, inf, b0)
          +hokl : {P.ok_list(inf, G, cs, rs) == True{} : Bool} =
            %Equal.sym(Nat, n, 1n+p, en) :
              {P.ok_list(inf, G, cs,
                 SolveK.par_chunks(1n+dp, rgs, _, G, gG, cwS, cs, n, nd, fl,
                   inf, b0)) == True{} : Bool}
            hokl_p
          +helt = P.ok_list_fold(inf, G, cs, rs, b0, hokl, hb0)
          +efix_p = P.guesses_fixed_of_par_chunks(1n+dp, rgs, p, inf, G, cs,
                      nd, b0, G, en, P.inf_gt0(cs, h3n), P.inf_gt1(cs, h3n),
                      P.inf_gt3(cs, h3n), P.inf_gt6(cs, h3n), ai, hnd, hrgs,
                      hb0, hcov)
          +efix : {Eval.Eval.guesses(1n+p, G, cs, inf, G,
                     SolveK.fold_results(rs, b0))
                   == SolveK.fold_results(rs, b0) : SolveRef.Best} =
            %Equal.sym(Nat, n, 1n+p, en) :
              {Eval.Eval.guesses(1n+p, G, cs, inf, G,
                 SolveK.fold_results(
                   SolveK.par_chunks(1n+dp, rgs, _, G, gG, cwS, cs, n, nd, fl,
                     inf, b0), b0))
               == SolveK.fold_results(
                    SolveK.par_chunks(1n+dp, rgs, _, G, gG, cwS, cs, n, nd, fl,
                      inf, b0), b0) : SolveRef.Best}
            efix_p
          P.opt_from_best(G, cs, p, T2, SolveK.fold_results(rs, b0), helt,
            efix, opt, fin)

def P.solve_chunked_valid(+G: +List<+List<Nat>>, +cs: +List<+List<Nat>>,
    +d: Nat, +p: Nat, +T: Tree.Tree,
    +en: {Groups.len_words(cs) == 1n+p : Nat},
    +h3n: {Nat.is_le(3n, Groups.len_words(cs)) == True{} : Bool},
    +ai: {FO.FO.all_in_ref(cs, G) == True{} : Bool},
    e: {SolveK.solve_chunked(G, cs, d) == Some{T} : Maybe<Tree.Tree>}) ->
  Tree.Valid(T, G, cs):
  +n : Nat = Groups.len_words(cs)
  +inf : Nat = SolveRef.inf_of(n)
  +nd : Bool = SolveFast.no_dup_fast(cs)
  +has_buf : Bool = FH.FH.mk_buf_has(nd, G, cs, n)
  +gG = SolveFast.glist_of_guesses(G, 0, 1)
  +cwS = SolveFast.build_cwords(cs, G, 0, U32.from_nat(Groups.len_words(G)))
  +ecwS = FT.FT.build_cwords_words(cs, G, 0, U32.from_nat(Groups.len_words(G)))
  +hcwS = FOpt.FOpt.build_cwords_ok_if(has_buf, G, cs, n, ai)
  +hnd = FOpt.FOpt.nodup_ok_of_fast(cs)
  +hpr = GR.GR.root_prepare_spec(p, inf, G, cs, nd, has_buf, gG, cwS,
           SolveFast.mk_buf_tbl(nd, G, cs, n), en, {==}, ecwS, hcwS, ai, hnd,
           FH.FH.mk_buf_tbl_ok(nd, G, cs, n, {==}))
  P.after_prep_valid(d, p, G, cs, nd,
    Greedy.root_prepare(G, gG, cwS, n, inf, SolveFast.mk_buf_tbl(nd, G, cs, n)),
    T, en, h3n, ai, hnd, hpr, e)

def P.solve_chunked_optimal(+G: +List<+List<Nat>>, +cs: +List<+List<Nat>>,
    +d: Nat, +p: Nat, +T2: Tree.Tree,
    +en: {Groups.len_words(cs) == 1n+p : Nat},
    +h3n: {Nat.is_le(3n, Groups.len_words(cs)) == True{} : Bool},
    +ai: {FO.FO.all_in_ref(cs, G) == True{} : Bool},
    +opt: {Nat.is_le(Eval.Eval.cost_of(P.ref_p(G, cs, p)), Tree.cost(T2, cs))
           == True{} : Bool},
    +fin: {Nat.is_lt(Eval.Eval.cost_of(P.ref_p(G, cs, p)),
             SolveRef.inf_of(Groups.len_words(cs))) == True{} : Bool}) ->
  Exists(Tree.Tree, T =>
    {SolveK.solve_chunked(G, cs, d) == Some{T} : Maybe<Tree.Tree>}
    & {Nat.is_le(Tree.cost(T, cs), Tree.cost(T2, cs)) == True{} : Bool}):
  +n : Nat = Groups.len_words(cs)
  +inf : Nat = SolveRef.inf_of(n)
  +nd : Bool = SolveFast.no_dup_fast(cs)
  +has_buf : Bool = FH.FH.mk_buf_has(nd, G, cs, n)
  +gG = SolveFast.glist_of_guesses(G, 0, 1)
  +cwS = SolveFast.build_cwords(cs, G, 0, U32.from_nat(Groups.len_words(G)))
  +ecwS = FT.FT.build_cwords_words(cs, G, 0, U32.from_nat(Groups.len_words(G)))
  +hcwS = FOpt.FOpt.build_cwords_ok_if(has_buf, G, cs, n, ai)
  +hnd = FOpt.FOpt.nodup_ok_of_fast(cs)
  +hpr = GR.GR.root_prepare_spec(p, inf, G, cs, nd, has_buf, gG, cwS,
           SolveFast.mk_buf_tbl(nd, G, cs, n), en, {==}, ecwS, hcwS, ai, hnd,
           FH.FH.mk_buf_tbl_ok(nd, G, cs, n, {==}))
  P.after_prep_optimal(d, p, G, cs, nd,
    Greedy.root_prepare(G, gG, cwS, n, inf, SolveFast.mk_buf_tbl(nd, G, cs, n)),
    T2, en, h3n, ai, hnd, hpr, opt, fin)

# ---------------------------------------------------------------------------
# Validity and optimality of `SolveK.solve_k` for every chunk count
# ---------------------------------------------------------------------------

def P.solve_small_valid(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +d: Nat, +T: Tree.Tree,
    +ai: {FO.FO.all_in_ref(C, G) == True{} : Bool},
    e: {SolveK.solve_small(G, C, d) == Some{T} : Maybe<Tree.Tree>}) ->
  Tree.Valid(T, G, C):
  match C:
    case Nil{}:
      FOpt.FOpt.solve_valid_all_in(G, Nil{}, T, ai, e)
    case Con{w, t}:
      match t:
        case Nil{}:
          FOpt.FOpt.solve_valid_all_in(G, w <> Nil{}, T, ai, e)
        case Con{w2, t2}:
          match t2:
            case Nil{}:
              FOpt.FOpt.solve_valid_all_in(G, w <> (w2 <> Nil{}), T, ai, e)
            case Con{w3, t3}:
              +cs : +List<+List<Nat>> = w <> (w2 <> (w3 <> t3))
              +p : Nat = Groups.len_words(w2 <> (w3 <> t3))
              +en : {Groups.len_words(cs) == 1n+p : Nat} = {==}
              +h3n : {Nat.is_le(3n, Groups.len_words(cs)) == True{} : Bool} =
                NatProof.Nat.is_le_zero_l(Groups.len_words(t3))
              P.solve_chunked_valid(G, cs, d, p, T, en, h3n, ai, e)

def P.solve_small_optimal(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +d: Nat, +T2: Tree.Tree,
    +ai: {FO.FO.all_in_ref(C, G) == True{} : Bool},
    v: Tree.Valid(T2, G, C)) ->
  Exists(Tree.Tree, T =>
    {SolveK.solve_small(G, C, d) == Some{T} : Maybe<Tree.Tree>}
    & {Nat.is_le(Tree.cost(T, C), Tree.cost(T2, C)) == True{} : Bool}):
  match C:
    case Nil{}:
      FOpt.FOpt.solve_opt_all_in(G, Nil{}, T2, ai, v)
    case Con{w, t}:
      match t:
        case Nil{}:
          FOpt.FOpt.solve_opt_all_in(G, w <> Nil{}, T2, ai, v)
        case Con{w2, t2}:
          match t2:
            case Nil{}:
              FOpt.FOpt.solve_opt_all_in(G, w <> (w2 <> Nil{}), T2, ai, v)
            case Con{w3, t3}:
              +cs : +List<+List<Nat>> = w <> (w2 <> (w3 <> t3))
              +p : Nat = Groups.len_words(w2 <> (w3 <> t3))
              +en : {Groups.len_words(cs) == 1n+p : Nat} = {==}
              +h3n : {Nat.is_le(3n, Groups.len_words(cs)) == True{} : Bool} =
                NatProof.Nat.is_le_zero_l(Groups.len_words(t3))
              OQStrong.F2.use_pair(
                Exists(Tree.Tree, T =>
                  {SolveK.solve_chunked(G, cs, d) == Some{T}
                   : Maybe<Tree.Tree>}
                  & {Nat.is_le(Tree.cost(T, cs), Tree.cost(T2, cs))
                     == True{} : Bool}),
                {Nat.is_le(Eval.Eval.cost_of(MV.MV.solve_best(G, cs)),
                   Tree.cost(T2, cs)) == True{} : Bool},
                {Nat.is_lt(Eval.Eval.cost_of(MV.MV.solve_best(G, cs)),
                   SolveRef.inf_of(Groups.len_words(cs)))
                 == True{} : Bool},
                OQStrong.F2.optimal_and_finite(G, cs, T2, v),
                opt => fin =>
                  P.solve_chunked_optimal(G, cs, d, p, T2, en, h3n, ai,
                    opt, fin))

def P.solve_k_checked_valid(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +d: Nat, ok: Bool,
    +eok: {ok == SolveFast.all_in_fast(C, G) : Bool}, +T: Tree.Tree,
    e: {SolveK.solve_k_checked(G, C, d, ok) == Some{T}
        : Maybe<Tree.Tree>}) ->
  Tree.Valid(T, G, C):
  match ok:
    case False{}:
      Empty.absurd(Tree.Valid(T, G, C),
        MV.MV.none_ne_some(Tree.Tree, T, e))
    case True{}:
      +ai : {FO.FO.all_in_ref(C, G) == True{} : Bool} =
        Equal.trans(Bool, FO.FO.all_in_ref(C, G), SolveFast.all_in_fast(C, G),
          True{},
          Equal.sym(Bool, SolveFast.all_in_fast(C, G), FO.FO.all_in_ref(C, G),
            FO.FO.all_in_fast_eq(C, G)),
          Equal.sym(Bool, True{}, SolveFast.all_in_fast(C, G), eok))
      P.solve_small_valid(G, C, d, T, ai, e)

def P.solve_k_checked_optimal(+G: +List<+List<Nat>>,
    +C: +List<+List<Nat>>, +d: Nat, ok: Bool,
    +eok: {ok == SolveFast.all_in_fast(C, G) : Bool}, +T2: Tree.Tree,
    v: Tree.Valid(T2, G, C)) ->
  Exists(Tree.Tree, T =>
    {SolveK.solve_k_checked(G, C, d, ok) == Some{T} : Maybe<Tree.Tree>}
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
      P.solve_small_optimal(G, C, d, T2, ai, v)

def P.solve_k_valid(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +k: Nat, +T: Tree.Tree,
    e: {SolveK.solve_k(G, C, k) == Some{T} : Maybe<Tree.Tree>}) ->
  Tree.Valid(T, G, C):
  P.solve_k_checked_valid(G, C, SolveK.depth_of(k),
    SolveFast.all_in_fast(C, G), {==}, T, e)

def P.solve_k_optimal(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +k: Nat, +T2: Tree.Tree, v: Tree.Valid(T2, G, C)) ->
  Exists(Tree.Tree, T =>
    {SolveK.solve_k(G, C, k) == Some{T} : Maybe<Tree.Tree>}
    & {Nat.is_le(Tree.cost(T, C), Tree.cost(T2, C)) == True{} : Bool}):
  P.solve_k_checked_optimal(G, C, SolveK.depth_of(k),
    SolveFast.all_in_fast(C, G), {==}, T2, v)
