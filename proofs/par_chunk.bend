# The chunked root of the bound-pruned solver.
#
# `src/solve_k.bend` splits the root guess list into contiguous chunks and runs
# the fast search machine (`SolveFast.step`) on each chunk from the neutral
# accumulator, with the full guess list still used at every child node. This
# module proves that every chunk result is valid and at most the reference fold
# over its own guesses, and that folding the chunk results in guess order is at
# most the reference fold over the whole root guess list.
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
import ./fast_valid.bend as FVal
import ./fast_opt.bend as FOpt
import ./par_fold.bend as ParFold
import ./cap_walk.bend as CAP
import ./par_list.bend as ParList

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
      SolveFast.guess_items_buf(nodup, row, g, cwS, Groups.len_words(S),
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
  +hr2_cw = FH.FH.guess_items_buf_spec(G, C_root, CAP.CW.hook(G, C_root), n_root, has_buf, nodup, row,
              g, cwS, n, fl, best, b2, en, hnd_cw, hrow, hcwS, hbuf2)
  +hr2 : FH.FH.GuessSpec(G, C_root, n_root, has_buf, nodup, g, S, n, fl, best,
           SolveFast.guess_items_buf(nodup, row, g, cwS, n, fl, best, b2)) =
    %ecwS : FH.FH.GuessSpec(G, C_root, n_root, has_buf, nodup, g, _, n, fl,
              best,
              SolveFast.guess_items_buf(nodup, row, g, cwS, n, fl, best, b2))
    hr2_cw
  +er : {SolveFast.guess_items_buf(nodup, row, g, cwS, n, fl, best, b2)
         == SolveFast.guess_items_buf(nodup, row, g, cwS, n, fl, best, b1)
         : SolveFast.GuessRes} =
    Equal.cong(SolveFast.Buf5, SolveFast.GuessRes,
      b => SolveFast.guess_items_buf(nodup, row, g, cwS, n, fl, best, b),
      b2, b1, eb2)
  +hr1 : FH.FH.GuessSpec(G, C_root, n_root, has_buf, nodup, g, S, n, fl, best,
           SolveFast.guess_items_buf(nodup, row, g, cwS, n, fl, best, b1)) =
    %er : FH.FH.GuessSpec(G, C_root, n_root, has_buf, nodup, g, S, n, fl, best, _)
    hr2
  %eb1 : P.ChunkSpec(1n+p, inf, G, gs, C_root, n_root, has_buf, nodup, S, limit,
           SolveFast.step(1n+p, gt, 1n, Nil{}, gG, cwS, n, nodup, fl, inf,
             Nil{}, Nil{}, 0n, best, SolveFast.dummy_step_zero(), False{},
             False{},
             SolveFast.guess_items_buf(nodup, row, g, cwS, n, fl, best, _)))
  P.walk_pop_go(p, G, gs, C_root, n_root, has_buf, rwsG, cwS, S, nodup, mode,
    inf, g, t, tail, best, limit,
    SolveFast.guess_items_buf(nodup, row, g, cwS, n, fl, best, b1), hr1,
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
          SolveFast.guess_items_buf(nodup, row, g, cwS, n, fl, best, buf)),
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
            SolveFast.guess_items_buf(nodup, row, g, cwS, n, fl, best, buf)),
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
# Split bookkeeping: prefixes, tails, and contiguous segments
# ---------------------------------------------------------------------------

# `half_go` is at most its argument.
def P.half_go_le(fuel: Nat, +n: Nat) ->
  {Nat.is_le(SolveK.half_go(fuel, n), n) == True{} : Bool}:
  match fuel:
    case 0n:
      NatProof.Nat.is_le_zero_l(n)
    case 1n++p:
      match n:
        case 0n:
          {==}
        case 1n+q:
          match q:
            case 0n:
              {==}
            case 1n++r:
              +ih : {Nat.is_le(SolveK.half_go(p, r), r) == True{} : Bool} =
                P.half_go_le(p, r)
              +h1 : {Nat.is_le(Nat.add(1n, SolveK.half_go(p, r)),
                                Nat.add(1n, r)) == True{} : Bool} =
                NatProof.Nat.is_le_add_l(SolveK.half_go(p, r), r, 1n, ih)
              NatProof.Nat.is_le_trans(Nat.add(1n, SolveK.half_go(p, r)),
                Nat.add(1n, r), Nat.add(1n, Nat.add(1n, r)), h1,
                NatProof.Nat.is_le_add_self_l(1n, r))

def P.half_le(+n: Nat) ->
  {Nat.is_le(SolveK.half(n), n) == True{} : Bool}:
  P.half_go_le(n, n)

# `take` of an in-range length has that length.
def P.len_take_le(+xs: +List<+List<Nat>>, +k: Nat,
    +h: {Nat.is_le(k, Groups.len_words(xs)) == True{} : Bool}) ->
  {Groups.len_words(List.take(&2, +List<Nat>, xs, k)) == k : Nat}:
  match xs k:
    case Nil{} _:
      +hk : {k == 0n : Nat} = NatProof.Nat.eq_zero_of_le_zero(k, h)
      Equal.trans(Nat,
        Groups.len_words(List.take(&2, +List<Nat>, Nil{}, k)), 0n, k,
        {==}, Equal.sym(Nat, k, 0n, hk))
    case Con{w, t} 0n:
      {==}
    case Con{w, t} 1n+p:
      +hp : {Nat.is_le(p, Groups.len_words(t)) == True{} : Bool} =
        NatProof.Nat.is_le_succ_inv(p, Groups.len_words(t), h)
      +ih : {Groups.len_words(List.take(&2, +List<Nat>, t, p)) == p : Nat} =
        P.len_take_le(t, p, hp)
      Equal.cong(Nat, Nat, x => Nat.add(1n, x),
        Groups.len_words(List.take(&2, +List<Nat>, t, p)), p, ih)

# Appending `rest` to the guess list keeps `has_grow_go`.
def P.has_grow_go_append(+G: +List<+List<Nat>>, +rest: +List<+List<Nat>>,
    +n: Nat, +row: U32, +g: +List<Nat>, +cur: Nat,
    +h: {FT.FT.has_grow_go(G, n, row, g, cur) == True{} : Bool}) ->
  {FT.FT.has_grow_go(List.append(&2, +List<Nat>, G, rest), n, row, g, cur)
   == True{} : Bool}:
  match G:
    case Nil{}:
      Empty.absurd(
        {FT.FT.has_grow_go(List.append(&2, +List<Nat>, Nil{}, rest), n, row,
           g, cur) == True{} : Bool},
        Logic.Proof.false_ne_true(h))
    case Con{h0, t}:
      +cond : Bool = Bool.and(U32.is_eq(row, U32.from_nat(cur)),
        Feedback.word_eq(g, h0))
      FT.FT.bool_or_elim_go(
        {FT.FT.has_grow_go(List.append(&2, +List<Nat>, h0 <> t, rest), n, row,
           g, cur) == True{} : Bool},
        cond, FT.FT.has_grow_go(t, n, row, g, 1n+cur), h,
        +hc => FOpt.FOpt.bool_or_l(cond,
          FT.FT.has_grow_go(List.append(&2, +List<Nat>, t, rest), n, row, g,
            1n+cur), hc),
        +ht => FVal.FV.bool_or_r(cond,
          FT.FT.has_grow_go(List.append(&2, +List<Nat>, t, rest), n, row, g,
            1n+cur),
          P.has_grow_go_append(t, rest, n, row, g, 1n+cur, ht)))

# Appending `rest` to the guess list keeps `rws_ok_b`.
def P.rws_ok_b_append(+G: +List<+List<Nat>>, +rest: +List<+List<Nat>>,
    +n: Nat, +rws: +List<FT.FT.RowWord>,
    +h: {FT.FT.rws_ok_b(G, n, rws) == True{} : Bool}) ->
  {FT.FT.rws_ok_b(List.append(&2, +List<Nat>, G, rest), n, rws)
   == True{} : Bool}:
  match rws:
    case Nil{}:
      {==}
    case Con{rw, t}:
      match rw:
        case FT.RowWord{+r, +w}:
          FO.FO.bool_and_intro(
            FT.FT.gentry_ok_b(List.append(&2, +List<Nat>, G, rest), n, r, w),
            FT.FT.rws_ok_b(List.append(&2, +List<Nat>, G, rest), n, t),
            P.has_grow_go_append(G, rest, n, r, w, 0n,
              Logic.Proof.and_true_l(FT.FT.gentry_ok_b(G, n, r, w),
                FT.FT.rws_ok_b(G, n, t), h)),
            P.rws_ok_b_append(G, rest, n, t,
              Logic.Proof.and_true_r(FT.FT.gentry_ok_b(G, n, r, w),
                FT.FT.rws_ok_b(G, n, t), h)))

# A subsequence relation for the segment inside the whole guess list.
def P.subseq_self(+xs: +List<+List<Nat>>) -> CoverList.Cover.Subseq(xs, xs):
  match xs:
    case Nil{}:
      Unit{}
    case Con{h, t}:
      Inl{({==}, P.subseq_self(t))}

def P.subseq_cons_r(+h: +List<Nat>, +xs: +List<+List<Nat>>,
    +ys: +List<+List<Nat>>, p: CoverList.Cover.Subseq(xs, ys)) ->
  CoverList.Cover.Subseq(xs, List.append(&2, +List<Nat>, ys, h <> Nil{})):
  match xs ys:
    case Nil{} _:
      Unit{}
    case Con{h0, t} Nil{}:
      match p:
    case Con{h0, t} Con{y, r}:
      match p:
        case Inl{q}:
          (e, pt) = q
          Inl{(e, P.subseq_cons_r(h, t, r, pt))}
        case Inr{q}:
          Inr{P.subseq_cons_r(h, xs, r, q)}

def P.subseq_append_r(+xs: +List<+List<Nat>>, +zs: +List<+List<Nat>>,
    +ys: +List<+List<Nat>>, p: CoverList.Cover.Subseq(xs, ys)) ->
  CoverList.Cover.Subseq(xs, List.append(&2, +List<Nat>, ys, zs)):
  match zs:
    case Nil{}:
      +e : {ys == List.append(&2, +List<Nat>, ys, Nil{}) : +List<+List<Nat>>} =
        Equal.sym(+List<+List<Nat>>, List.append(&2, +List<Nat>, ys, Nil{}), ys,
          FN.FN.list_append_nil(ys))
      %e : CoverList.Cover.Subseq(xs, _)
      p
    case Con{w, t}:
      +e : {List.append(&2, +List<Nat>,
              List.append(&2, +List<Nat>, ys, w <> Nil{}), t)
            == List.append(&2, +List<Nat>, ys, w <> t)
            : +List<+List<Nat>>} =
        FN.FN.list_append_assoc(ys, w <> Nil{}, t)
      %e : CoverList.Cover.Subseq(xs, _)
      P.subseq_append_r(xs, t, List.append(&2, +List<Nat>, ys, w <> Nil{}),
        P.subseq_cons_r(w, xs, ys, p))

def P.subseq_prepend(+xs: +List<+List<Nat>>, +pre: +List<+List<Nat>>) ->
  CoverList.Cover.Subseq(xs, List.append(&2, +List<Nat>, pre, xs)):
  match xs pre:
    case Nil{} _:
      Unit{}
    case Con{xh, xt} Nil{}:
      P.subseq_self(xs)
    case Con{xh, xt} Con{h, t}:
      Inr{P.subseq_prepend(xs, t)}

def P.subseq_mid(+pre: +List<+List<Nat>>, +seg: +List<+List<Nat>>,
    +post: +List<+List<Nat>>) ->
  CoverList.Cover.Subseq(seg,
    List.append(&2, +List<Nat>,
      List.append(&2, +List<Nat>, pre, seg), post)):
  P.subseq_append_r(seg, post, List.append(&2, +List<Nat>, pre, seg),
    P.subseq_prepend(seg, pre))

def P.all_in_seg(+pre: +List<+List<Nat>>, +seg: +List<+List<Nat>>,
    +post: +List<+List<Nat>>, +G: +List<+List<Nat>>,
    +eG: {List.append(&2, +List<Nat>,
            List.append(&2, +List<Nat>, pre, seg), post) == G
          : +List<+List<Nat>>}) ->
  {FO.FO.all_in_ref(seg, G) == True{} : Bool}:
  sub : CoverList.Cover.Subseq(seg,
    List.append(&2, +List<Nat>,
      List.append(&2, +List<Nat>, pre, seg), post)) =
    P.subseq_mid(pre, seg, post)
  +GX : +List<+List<Nat>> = List.append(&2, +List<Nat>,
    List.append(&2, +List<Nat>, pre, seg), post)
  +ai : {FO.FO.all_in_ref(GX, GX) == True{} : Bool} =
    FVal.FV.all_in_ref_self(GX)
  +a : {FO.FO.all_in_ref(seg, GX) == True{} : Bool} =
    FO.FO.all_in_of_subseq(seg, GX, GX, sub, ai)
  %eG : {FO.FO.all_in_ref(seg, _) == True{} : Bool}
  a

# The rows of a segment, as a transparent definition (a local `+` binding is
# opaque in type indices).
def P.rws_of(+seg: +List<+List<Nat>>, +off: U32) -> +List<FT.FT.RowWord>:
  FT.FT.guesses_to_rws(seg, off, 1)

# The chunk rows are valid against the whole guess list.
def P.chunk_rws_ok(+n: Nat, +G: +List<+List<Nat>>, +cs: +List<+List<Nat>>,
    +has_buf: Bool, +pre: +List<+List<Nat>>, +seg: +List<+List<Nat>>,
    +post: +List<+List<Nat>>, +off: U32,
    +eG : {G == List.append(&2, +List<Nat>,
             List.append(&2, +List<Nat>, pre, seg), post)
           : +List<+List<Nat>>},
    +eoff: {U32.from_nat(Groups.len_words(pre)) == off : U32}) ->
  {FH.FH.rws_ok_if(has_buf, G, n, P.rws_of(seg, off)) == True{} : Bool}:
  match has_buf:
    case False{}:
      {==}
    case True{}:
      +hbase : {FT.FT.rws_ok_b(
                 List.append(&2, +List<Nat>, pre, seg), n,
                 FT.FT.guesses_to_rws(seg, U32.from_nat(
                   Groups.len_words(pre)), 1))
                == True{} : Bool} =
        FT.FT.guesses_to_rws_ok_go(seg, pre, n)
      +elist : {FT.FT.guesses_to_rws(seg, U32.from_nat(
                    Groups.len_words(pre)), 1)
                 == FT.FT.guesses_to_rws(seg, off, 1)
                 : +List<FT.FT.RowWord>} =
        Equal.cong(U32, +List<FT.FT.RowWord>,
          u => FT.FT.guesses_to_rws(seg, u, 1),
          U32.from_nat(Groups.len_words(pre)), off, eoff)
      +hbase_off : {FT.FT.rws_ok_b(
                      List.append(&2, +List<Nat>, pre, seg), n,
                      P.rws_of(seg, off))
                    == True{} : Bool} =
        %elist : {FT.FT.rws_ok_b(List.append(&2, +List<Nat>, pre, seg), n,
                    _) == True{} : Bool}
        hbase
      +happ : {FT.FT.rws_ok_b(
                 List.append(&2, +List<Nat>,
                   List.append(&2, +List<Nat>, pre, seg), post), n,
                 P.rws_of(seg, off))
               == True{} : Bool} =
        P.rws_ok_b_append(List.append(&2, +List<Nat>, pre, seg), post, n,
          P.rws_of(seg, off), hbase_off)
      +eall : {List.append(&2, +List<Nat>,
                 List.append(&2, +List<Nat>, pre, seg), post) == G
               : +List<+List<Nat>>} =
        Equal.sym(+List<+List<Nat>>, G,
          List.append(&2, +List<Nat>,
            List.append(&2, +List<Nat>, pre, seg), post), eG)
      %eall : {FT.FT.rws_ok_b(_, n, P.rws_of(seg, off)) == True{} : Bool}
      happ

# ---------------------------------------------------------------------------
# The chunk leaf: one `step` over a contiguous segment of the root guess list
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

def P.chunk_leaf(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +cs: +List<+List<Nat>>, +nd: Bool, +has_buf: Bool,
    +rwsG: +List<FT.FT.RowWord>,
    +cwS: +List<SolveFast.CWord>,
    +pre: +List<+List<Nat>>, +seg: +List<+List<Nat>>,
    +post: +List<+List<Nat>>, +off: U32,
    -buf0: SolveFast.Buf5,
    +hbuf0: FH.FH.BufOk(G, cs, Groups.len_words(cs), has_buf, nd, buf0),
    dp: &b1: SolveFast.Buf5 -> &b2: SolveFast.Buf5 ->
        {b1 == buf0 : SolveFast.Buf5} & {b2 == b1 : SolveFast.Buf5},
    +erwsG: {FT.FT.rws_words(rwsG) == G : +List<+List<Nat>>},
    +hrwsG: {FH.FH.rws_ok_if(has_buf, G, Groups.len_words(cs), rwsG)
             == True{} : Bool},
    +ecwS: {SolveFast.cwords_words(cwS) == cs : +List<+List<Nat>>},
    +hcwS: {FH.FH.cwords_ok_if(has_buf, G, cs, Groups.len_words(cs), cwS)
            == True{} : Bool},
    +eG : {G == List.append(&2, +List<Nat>,
             List.append(&2, +List<Nat>, pre, seg), post)
           : +List<+List<Nat>>},
    +eoff: {U32.from_nat(Groups.len_words(pre)) == off : U32},
    +ele: {Nat.is_le(Groups.len_words(cs), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +h3: {Nat.is_lt(3n, inf) == True{} : Bool},
    +h6: {Nat.is_lt(6n, inf) == True{} : Bool},
    +ai: {FO.FO.all_in_ref(cs, G) == True{} : Bool},
    +hnd: {FN.FN.nodup_ok(nd, cs) == True{} : Bool}) ->
  {P.job_res_gs_b(1n+p, inf, G, seg, cs, inf,
     SolveFast.step_res_best(
       SolveFast.step(1n+p, SolveFast.glist_of_guesses(seg, off, 1), 0n,
         Nil{}, FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS,
         Groups.len_words(cs), nd,
         SolveFast.init_floor(Groups.len_words(cs)), inf,
         Nil{}, Nil{}, 0n, SolveFast.dummy_inf(inf),
         SolveFast.dummy_step_zero(), False{},
         SolveFast.is_floor_hit(nd, SolveFast.init_floor(Groups.len_words(cs)),
           SolveFast.dummy_inf(inf)),
         SolveFast.GuessRes{Nil{}, buf0}))) == True{} : Bool}:
  (b1, d2) = dp
  (b2, pe) = d2
  (+eb1, +eb2) = pe
  +n : Nat = Groups.len_words(cs)
  +erws : {FT.FT.rws_words(P.rws_of(seg, off)) == seg
           : +List<+List<Nat>>} =
    FT.FT.guesses_to_rws_words(seg, off, 1)
  +b0 : SolveRef.Best = SolveFast.dummy_inf(inf)
  +hbest0 : {Nat.is_le(Eval.Eval.cost_of(b0), inf) == True{} : Bool} =
    NatProof.Nat.is_le_refl(inf)
  +hok0 : {FVal.FV.best_ok_b(inf, G, cs, b0) == True{} : Bool} =
    FVal.FV.best_ok_init(inf, G, cs, b0, Nat.ge_refl(inf))
  +eb2_0 : {b2 == buf0 : SolveFast.Buf5} =
    Equal.trans(SolveFast.Buf5, b2, b1, buf0, eb2, eb1)
  +hbuf2 = FH.FH.buf_ok_transport(G, cs, n, has_buf, nd, buf0, b2,
              Equal.sym(SolveFast.Buf5, b2, buf0, eb2_0), hbuf0)
  +seg_in : {FO.FO.all_in_ref(seg, G) == True{} : Bool} =
    P.all_in_seg(pre, seg, post, G, Equal.sym(+List<+List<Nat>>, G, List.append(&2, +List<Nat>, List.append(&2, +List<Nat>, pre, seg), post), eG))
  fseg : FOpt.FOpt.EFlat(p, inf, G, cs, n, has_buf, nd,
            MV.MV.next_guess(seg, cs)) =
    FOpt.FOpt.eflat(p, inf, G, cs, n, has_buf, nd,
      MV.MV.next_guess(seg, cs), MV.MV.any_bounds(p, seg, cs, ele),
      hz, h1, h3, h6, FO.FO.all_in_next_guess(seg, cs, G, ai),
      FN.FN.nodup_ok_next_guess(nd, seg, cs, hnd))
  fgs : FOpt.FOpt.EByGs(p, inf, G, cs, n, has_buf, cs, nd, seg) =
    FOpt.FOpt.eby_gs(p, inf, G, cs, n, has_buf, cs, nd, seg, fseg)
  +hrws : {FH.FH.rws_ok_if(has_buf, G, n, P.rws_of(seg, off))
           == True{} : Bool} =
    P.chunk_rws_ok(n, G, cs, has_buf, pre, seg, post, off, eG, eoff)
  +esg : {SolveFast.step(1n+p, FT.FT.glist_of_rws(P.rws_of(seg, off), SolveFast.GEnd{}), 0n, Nil{}, FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS, n, nd,
        SolveFast.init_floor(n), inf, Nil{}, Nil{}, 0n, b0,
        SolveFast.dummy_step_zero(), False{},
        SolveFast.is_floor_hit(nd, SolveFast.init_floor(n), b0),
        SolveFast.GuessRes{Nil{}, b2})
           == SolveFast.step(1n+p, FT.FT.glist_of_rws(P.rws_of(seg, off), SolveFast.GEnd{}), 0n, Nil{}, FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS, n, nd,
        SolveFast.init_floor(n), inf, Nil{}, Nil{}, 0n, b0,
        SolveFast.dummy_step_zero(), False{},
        SolveFast.is_floor_hit(nd, SolveFast.init_floor(n), b0),
        SolveFast.GuessRes{Nil{}, b2})
           : SolveFast.StepRes} =
    Equal.cong(SolveFast.GList, SolveFast.StepRes,
      gl => SolveFast.step(1n+p,
              FT.FT.glist_of_rws(P.rws_of(seg, off), SolveFast.GEnd{}), 0n,
              Nil{}, gl, cwS, n, nd,
              SolveFast.init_floor(n), inf, Nil{}, Nil{}, 0n, b0,
              SolveFast.dummy_step_zero(), False{},
              SolveFast.is_floor_hit(nd, SolveFast.init_floor(n), b0),
              SolveFast.GuessRes{Nil{}, b2}),
      FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), {==})
  +hspec : P.ChunkSpec(1n+p, inf, G, seg, cs, n, has_buf, nd, cs, inf,
            SolveFast.step(1n+p, FT.FT.glist_of_rws(P.rws_of(seg, off), SolveFast.GEnd{}), 0n, Nil{}, FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS, n, nd,
        SolveFast.init_floor(n), inf, Nil{}, Nil{}, 0n, b0,
        SolveFast.dummy_step_zero(), False{},
        SolveFast.is_floor_hit(nd, SolveFast.init_floor(n), b0),
        SolveFast.GuessRes{Nil{}, b2})) =
    P.chunk_spec_transport(1n+p, inf, G, seg, cs, n, has_buf, nd, cs, inf,
      SolveFast.step(1n+p, FT.FT.glist_of_rws(P.rws_of(seg, off), SolveFast.GEnd{}), 0n, Nil{}, FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS, n, nd,
        SolveFast.init_floor(n), inf, Nil{}, Nil{}, 0n, b0,
        SolveFast.dummy_step_zero(), False{},
        SolveFast.is_floor_hit(nd, SolveFast.init_floor(n), b0),
        SolveFast.GuessRes{Nil{}, b2}),
      SolveFast.step(1n+p, FT.FT.glist_of_rws(P.rws_of(seg, off), SolveFast.GEnd{}), 0n, Nil{}, FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS, n, nd,
        SolveFast.init_floor(n), inf, Nil{}, Nil{}, 0n, b0,
        SolveFast.dummy_step_zero(), False{},
        SolveFast.is_floor_hit(nd, SolveFast.init_floor(n), b0),
        SolveFast.GuessRes{Nil{}, b2}),
      esg,
      P.chunk_direct(p, inf, G, seg, cs, has_buf, P.rws_of(seg, off), rwsG, cwS, nd, b0, b2,
        erwsG, hrwsG, ecwS, hcwS, erws, hrws, seg_in, ele, hz, h1, h3, h6, ai,
        hnd, hbest0, hok0, hbuf2, fgs))
  +esr : {SolveFast.step(1n+p, FT.FT.glist_of_rws(P.rws_of(seg, off), SolveFast.GEnd{}), 0n, Nil{}, FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS, n, nd,
        SolveFast.init_floor(n), inf, Nil{}, Nil{}, 0n, b0,
        SolveFast.dummy_step_zero(), False{},
        SolveFast.is_floor_hit(nd, SolveFast.init_floor(n), b0),
        SolveFast.GuessRes{Nil{}, b2})
           == SolveFast.step(1n+p, SolveFast.glist_of_guesses(seg, off, 1), 0n, Nil{}, FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS, n, nd,
        SolveFast.init_floor(n), inf, Nil{}, Nil{}, 0n, b0,
        SolveFast.dummy_step_zero(), False{},
        SolveFast.is_floor_hit(nd, SolveFast.init_floor(n), b0),
        SolveFast.GuessRes{Nil{}, b1})
           : SolveFast.StepRes} =
    Equal.trans(SolveFast.StepRes,
      SolveFast.step(1n+p, FT.FT.glist_of_rws(P.rws_of(seg, off), SolveFast.GEnd{}), 0n, Nil{}, FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS, n, nd,
        SolveFast.init_floor(n), inf, Nil{}, Nil{}, 0n, b0,
        SolveFast.dummy_step_zero(), False{},
        SolveFast.is_floor_hit(nd, SolveFast.init_floor(n), b0),
        SolveFast.GuessRes{Nil{}, b2}),
      SolveFast.step(1n+p, FT.FT.glist_of_rws(P.rws_of(seg, off), SolveFast.GEnd{}), 0n, Nil{}, FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS, n, nd,
        SolveFast.init_floor(n), inf, Nil{}, Nil{}, 0n, b0,
        SolveFast.dummy_step_zero(), False{},
        SolveFast.is_floor_hit(nd, SolveFast.init_floor(n), b0),
        SolveFast.GuessRes{Nil{}, b1}),
      SolveFast.step(1n+p, SolveFast.glist_of_guesses(seg, off, 1), 0n, Nil{}, FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS, n, nd,
        SolveFast.init_floor(n), inf, Nil{}, Nil{}, 0n, b0,
        SolveFast.dummy_step_zero(), False{},
        SolveFast.is_floor_hit(nd, SolveFast.init_floor(n), b0),
        SolveFast.GuessRes{Nil{}, b1}),
      Equal.cong(SolveFast.Buf5, SolveFast.StepRes,
        b => SolveFast.step(1n+p, FT.FT.glist_of_rws(P.rws_of(seg, off), SolveFast.GEnd{}), 0n, Nil{}, FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS, n, nd,
        SolveFast.init_floor(n), inf, Nil{}, Nil{}, 0n, b0,
        SolveFast.dummy_step_zero(), False{},
        SolveFast.is_floor_hit(nd, SolveFast.init_floor(n), b0),
        SolveFast.GuessRes{Nil{}, b}),
        b2, b1, eb2),
      Equal.trans(SolveFast.StepRes,
        SolveFast.step(1n+p, FT.FT.glist_of_rws(P.rws_of(seg, off), SolveFast.GEnd{}), 0n, Nil{}, FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS, n, nd,
        SolveFast.init_floor(n), inf, Nil{}, Nil{}, 0n, b0,
        SolveFast.dummy_step_zero(), False{},
        SolveFast.is_floor_hit(nd, SolveFast.init_floor(n), b0),
        SolveFast.GuessRes{Nil{}, b1}),
        SolveFast.step(1n+p, SolveFast.glist_of_guesses(seg, off, 1), 0n, Nil{}, FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS, n, nd,
        SolveFast.init_floor(n), inf, Nil{}, Nil{}, 0n, b0,
        SolveFast.dummy_step_zero(), False{},
        SolveFast.is_floor_hit(nd, SolveFast.init_floor(n), b0),
        SolveFast.GuessRes{Nil{}, b1}),
        SolveFast.step(1n+p, SolveFast.glist_of_guesses(seg, off, 1), 0n, Nil{}, FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS, n, nd,
        SolveFast.init_floor(n), inf, Nil{}, Nil{}, 0n, b0,
        SolveFast.dummy_step_zero(), False{},
        SolveFast.is_floor_hit(nd, SolveFast.init_floor(n), b0),
        SolveFast.GuessRes{Nil{}, b1}),
        Equal.cong(SolveFast.GList, SolveFast.StepRes,
        gl => SolveFast.step(1n+p, gl, 0n, Nil{}, FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS, n, nd,
        SolveFast.init_floor(n), inf, Nil{}, Nil{}, 0n, b0,
        SolveFast.dummy_step_zero(), False{},
        SolveFast.is_floor_hit(nd, SolveFast.init_floor(n), b0),
        SolveFast.GuessRes{Nil{}, b1}),
        FT.FT.glist_of_rws(P.rws_of(seg, off), SolveFast.GEnd{}), SolveFast.glist_of_guesses(seg, off, 1),
        Equal.sym(SolveFast.GList, SolveFast.glist_of_guesses(seg, off, 1), FT.FT.glist_of_rws(P.rws_of(seg, off), SolveFast.GEnd{}),
          FT.FT.glist_of_guesses_eq(seg, off, 1))),
        Equal.cong(SolveFast.GList, SolveFast.StepRes,
        gl => SolveFast.step(1n+p, SolveFast.glist_of_guesses(seg, off, 1), 0n, Nil{}, gl, cwS, n, nd,
        SolveFast.init_floor(n), inf, Nil{}, Nil{}, 0n, b0,
        SolveFast.dummy_step_zero(), False{},
        SolveFast.is_floor_hit(nd, SolveFast.init_floor(n), b0),
        SolveFast.GuessRes{Nil{}, b1}),
        FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), {==})))
  +hspec2 : P.ChunkSpec(1n+p, inf, G, seg, cs, n, has_buf, nd, cs, inf,
              SolveFast.step(1n+p, SolveFast.glist_of_guesses(seg, off, 1), 0n,
                Nil{}, FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS, n, nd,
                SolveFast.init_floor(n), inf, Nil{}, Nil{}, 0n, b0,
                SolveFast.dummy_step_zero(), False{},
                SolveFast.is_floor_hit(nd, SolveFast.init_floor(n), b0),
                SolveFast.GuessRes{Nil{}, b1})) =
    P.chunk_spec_transport(1n+p, inf, G, seg, cs, n, has_buf, nd, cs, inf,
      SolveFast.step(1n+p, FT.FT.glist_of_rws(P.rws_of(seg, off), SolveFast.GEnd{}), 0n,
        Nil{}, FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS, n, nd,
        SolveFast.init_floor(n), inf, Nil{}, Nil{}, 0n, b0,
        SolveFast.dummy_step_zero(), False{},
        SolveFast.is_floor_hit(nd, SolveFast.init_floor(n), b0),
        SolveFast.GuessRes{Nil{}, b2}),
      SolveFast.step(1n+p, SolveFast.glist_of_guesses(seg, off, 1), 0n, Nil{}, FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS, n, nd,
        SolveFast.init_floor(n), inf, Nil{}, Nil{}, 0n, b0,
        SolveFast.dummy_step_zero(), False{},
        SolveFast.is_floor_hit(nd, SolveFast.init_floor(n), b0),
        SolveFast.GuessRes{Nil{}, b1}),
      esr, hspec)
  +hfinal : {P.job_res_gs_b(1n+p, inf, G, seg, cs, inf,
      SolveFast.step_res_best(
        SolveFast.step(1n+p, SolveFast.glist_of_guesses(seg, off, 1), 0n, Nil{},
          FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS, n, nd,
          SolveFast.init_floor(n), inf, Nil{}, Nil{}, 0n, b0,
          SolveFast.dummy_step_zero(), False{},
          SolveFast.is_floor_hit(nd, SolveFast.init_floor(n), b0),
          SolveFast.GuessRes{Nil{}, b1}))) == True{} : Bool} =
    P.job_res_gs_of_spec(1n+p, inf, G, seg, cs, n, has_buf, nd, cs, inf,
      SolveFast.step(1n+p, SolveFast.glist_of_guesses(seg, off, 1), 0n, Nil{},
        FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS, n, nd,
        SolveFast.init_floor(n), inf, Nil{}, Nil{}, 0n, b0,
        SolveFast.dummy_step_zero(), False{},
        SolveFast.is_floor_hit(nd, SolveFast.init_floor(n), b0),
        SolveFast.GuessRes{Nil{}, b1}), hspec2)
  +esr2 : {SolveFast.step(1n+p, SolveFast.glist_of_guesses(seg, off, 1), 0n,
              Nil{}, FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS, n, nd,
              SolveFast.init_floor(n), inf, Nil{}, Nil{}, 0n, b0,
              SolveFast.dummy_step_zero(), False{},
              SolveFast.is_floor_hit(nd, SolveFast.init_floor(n), b0),
              SolveFast.GuessRes{Nil{}, b1})
            == SolveFast.step(1n+p, SolveFast.glist_of_guesses(seg, off, 1), 0n,
                 Nil{}, FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS, n, nd,
                 SolveFast.init_floor(n), inf, Nil{}, Nil{}, 0n, b0,
                 SolveFast.dummy_step_zero(), False{},
                 SolveFast.is_floor_hit(nd, SolveFast.init_floor(n), b0),
                 SolveFast.GuessRes{Nil{}, buf0})
            : SolveFast.StepRes} =
    Equal.cong(SolveFast.Buf5, SolveFast.StepRes,
      b => SolveFast.step(1n+p, SolveFast.glist_of_guesses(seg, off, 1), 0n,
             Nil{}, FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS, n,
             nd, SolveFast.init_floor(n), inf, Nil{}, Nil{}, 0n, b0,
             SolveFast.dummy_step_zero(), False{},
             SolveFast.is_floor_hit(nd, SolveFast.init_floor(n), b0),
             SolveFast.GuessRes{Nil{}, b}),
      b1, buf0, eb1)
  %esr2 : {P.job_res_gs_b(1n+p, inf, G, seg, cs, inf,
              SolveFast.step_res_best(_)) == True{} : Bool}
  hfinal

# ---------------------------------------------------------------------------
# Fold composition
# ---------------------------------------------------------------------------

# `Eval.guesses` over a concatenation is the two folds in order.
def P.guesses_append(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +inf: Nat, +xs: +List<+List<Nat>>, +ys: +List<+List<Nat>>,
    +best: SolveRef.Best) ->
  {Eval.Eval.guesses(1n+p, G, S, inf,
      List.append(&2, +List<Nat>, xs, ys), best)
   == Eval.Eval.guesses(1n+p, G, S, inf, ys,
        Eval.Eval.guesses(1n+p, G, S, inf, xs, best)) : SolveRef.Best}:
  match xs:
    case Nil{}:
      {==}
    case Con{g, t}:
      P.guesses_append(p, G, S, inf, t, ys,
        Eval.Eval.guess(p, G, S, g, inf, best))

# `Eval.guesses` from `best` is `better` of the neutral fold and `best`.
def P.guesses_as_better(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +inf: Nat, +gs: +List<+List<Nat>>, +best: SolveRef.Best,
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool}) ->
  {Eval.Eval.guesses(1n+p, G, S, inf, gs, best)
   == FC.FC.better_best(
        Eval.Eval.guesses(1n+p, G, S, inf, gs, Eval.Eval.dummy_inf(inf)), best)
   : SolveRef.Best}:
  +d : SolveRef.Best = Eval.Eval.dummy_inf(inf)
  Equal.trans(SolveRef.Best,
    Eval.Eval.guesses(1n+p, G, S, inf, gs, best),
    Eval.Eval.guesses(1n+p, G, S, inf, gs, FC.FC.better_best(d, best)),
    FC.FC.better_best(Eval.Eval.guesses(1n+p, G, S, inf, gs, d), best),
    Equal.cong(SolveRef.Best, SolveRef.Best,
      a => Eval.Eval.guesses(1n+p, G, S, inf, gs, a),
      best, FC.FC.better_best(d, best),
      Equal.sym(SolveRef.Best, FC.FC.better_best(d, best), best,
        FC.FC.better_dummy_inf(inf, best, hbest))),
    FC.FC.eval_guesses_better(1n+p, G, S, inf, gs, d, best))

# `better` is monotone in both costs.
def P.better_mono_le_go(+a1: SolveRef.Best, +a2: SolveRef.Best,
    +b1: SolveRef.Best, +b2: SolveRef.Best, c: Bool,
    +ec: {c == Nat.is_lt(Eval.Eval.cost_of(a2), Eval.Eval.cost_of(b2)) : Bool},
    +h1: {Nat.is_le(Eval.Eval.cost_of(a1), Eval.Eval.cost_of(a2))
          == True{} : Bool},
    +h2: {Nat.is_le(Eval.Eval.cost_of(b1), Eval.Eval.cost_of(b2))
          == True{} : Bool}) ->
  {Nat.is_le(Eval.Eval.cost_of(FC.FC.better_best(a1, b1)),
     Eval.Eval.cost_of(Feedback.Bool.case(SolveRef.Best, c, a2, b2)))
   == True{} : Bool}:
  match c:
    case True{}:
      NatProof.Nat.is_le_trans(Eval.Eval.cost_of(FC.FC.better_best(a1, b1)),
        Eval.Eval.cost_of(a1), Eval.Eval.cost_of(a2),
        FVal.FV.better_best_le_l(a1, b1), h1)
    case False{}:
      NatProof.Nat.is_le_trans(Eval.Eval.cost_of(FC.FC.better_best(a1, b1)),
        Eval.Eval.cost_of(b1), Eval.Eval.cost_of(b2),
        FVal.FV.better_best_le_r(a1, b1), h2)

def P.better_mono_le(+a1: SolveRef.Best, +a2: SolveRef.Best,
    +b1: SolveRef.Best, +b2: SolveRef.Best,
    +h1: {Nat.is_le(Eval.Eval.cost_of(a1), Eval.Eval.cost_of(a2))
          == True{} : Bool},
    +h2: {Nat.is_le(Eval.Eval.cost_of(b1), Eval.Eval.cost_of(b2))
          == True{} : Bool}) ->
  {Nat.is_le(Eval.Eval.cost_of(FC.FC.better_best(a1, b1)),
     Eval.Eval.cost_of(FC.FC.better_best(a2, b2))) == True{} : Bool}:
  match a2:
    case SolveRef.Best{+ta2, +ca2}:
      match b2:
        case SolveRef.Best{+tb2, +cb2}:
          P.better_mono_le_go(a1, SolveRef.Best{ta2, ca2}, b1,
            SolveRef.Best{tb2, cb2}, Nat.is_lt(ca2, cb2), {==}, h1, h2)

# Unfolding one fold step.
def P.fold_unfold(+r: SolveRef.Best, +rest: +List<SolveRef.Best>,
    +best: SolveRef.Best) ->
  {SolveK.fold_results(r <> rest, best)
   == SolveK.fold_results(rest, FC.FC.better_best(r, best)) : SolveRef.Best}:
  match r:
    case SolveRef.Best{+tree, +cost}:
      {==}

# Folding never increases the accumulator cost.
def P.fold_le_best(+rs: +List<SolveRef.Best>, +best: SolveRef.Best) ->
  {Nat.is_le(Eval.Eval.cost_of(SolveK.fold_results(rs, best)),
     Eval.Eval.cost_of(best)) == True{} : Bool}:
  match rs:
    case Nil{}:
      NatProof.Nat.is_le_refl(Eval.Eval.cost_of(best))
    case Con{r, t}:
      +e : {SolveK.fold_results(r <> t, best)
            == SolveK.fold_results(t, FC.FC.better_best(r, best))
            : SolveRef.Best} =
        P.fold_unfold(r, t, best)
      +ih : {Nat.is_le(
               Eval.Eval.cost_of(SolveK.fold_results(t,
                 FC.FC.better_best(r, best))),
               Eval.Eval.cost_of(best)) == True{} : Bool} =
        NatProof.Nat.is_le_trans(
          Eval.Eval.cost_of(SolveK.fold_results(t,
            FC.FC.better_best(r, best))),
          Eval.Eval.cost_of(FC.FC.better_best(r, best)),
          Eval.Eval.cost_of(best),
          P.fold_le_best(t, FC.FC.better_best(r, best)),
          FVal.FV.better_best_le_r(r, best))
      Fold.OQ.le_cong_l(Eval.Eval.cost_of(SolveK.fold_results(r <> t, best)),
        Eval.Eval.cost_of(SolveK.fold_results(t,
          FC.FC.better_best(r, best))),
        Eval.Eval.cost_of(best),
        Equal.cong(SolveRef.Best, Nat, Eval.Eval.cost_of,
          SolveK.fold_results(r <> t, best),
          SolveK.fold_results(t, FC.FC.better_best(r, best)), e),
        ih)

# Folding a concatenation is folding the halves in order.
def P.fold_append(+xs: +List<SolveRef.Best>, +ys: +List<SolveRef.Best>,
    +best: SolveRef.Best) ->
  {SolveK.fold_results(List.append(&2, SolveRef.Best, xs, ys), best)
   == SolveK.fold_results(ys, SolveK.fold_results(xs, best))
   : SolveRef.Best}:
  match xs:
    case Nil{}:
      {==}
    case Con{r, t}:
      +e1 : {SolveK.fold_results(List.append(&2, SolveRef.Best, [r], List.append(&2, SolveRef.Best, t, ys)), best)
             == SolveK.fold_results(List.append(&2, SolveRef.Best, t, ys), FC.FC.better_best(r, best))
             : SolveRef.Best} =
        P.fold_unfold(r, List.append(&2, SolveRef.Best, t, ys), best)
      +e2 : {SolveK.fold_results(List.append(&2, SolveRef.Best, [r], t), best)
             == SolveK.fold_results(t, FC.FC.better_best(r, best))
             : SolveRef.Best} =
        P.fold_unfold(r, t, best)
      +e3 : {SolveK.fold_results(ys, SolveK.fold_results(List.append(&2, SolveRef.Best, [r], t), best))
             == SolveK.fold_results(ys,
                  SolveK.fold_results(t, FC.FC.better_best(r, best)))
             : SolveRef.Best} =
        Equal.cong(SolveRef.Best, SolveRef.Best,
          a => SolveK.fold_results(ys, a),
          SolveK.fold_results(List.append(&2, SolveRef.Best, [r], t), best),
          SolveK.fold_results(t, FC.FC.better_best(r, best)), e2)
      Equal.trans(SolveRef.Best,
        SolveK.fold_results(List.append(&2, SolveRef.Best, [r], List.append(&2, SolveRef.Best, t, ys)), best),
        SolveK.fold_results(List.append(&2, SolveRef.Best, t, ys), FC.FC.better_best(r, best)),
        SolveK.fold_results(ys, SolveK.fold_results(List.append(&2, SolveRef.Best, [r], t), best)),
        e1,
        Equal.trans(SolveRef.Best,
          SolveK.fold_results(List.append(&2, SolveRef.Best, t, ys), FC.FC.better_best(r, best)),
          SolveK.fold_results(ys,
            SolveK.fold_results(t, FC.FC.better_best(r, best))),
          SolveK.fold_results(ys, SolveK.fold_results(List.append(&2, SolveRef.Best, [r], t), best)),
          P.fold_append(t, ys, FC.FC.better_best(r, best)),
          Equal.sym(SolveRef.Best,
            SolveK.fold_results(ys, SolveK.fold_results(List.append(&2, SolveRef.Best, [r], t), best)),
            SolveK.fold_results(ys,
              SolveK.fold_results(t, FC.FC.better_best(r, best))), e3)))


# ---------------------------------------------------------------------------
# Chunk results as `SolveK.chunk_best`
# ---------------------------------------------------------------------------

# Transporting a chunk job result along an equality of results (the shape of
# `P.chunk_spec_transport`, for the bare result).
def P.job_res_gs_b_transport(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +gs: +List<+List<Nat>>, +S: +List<+List<Nat>>, +limit: Nat,
    -r1: SolveRef.Best, -r2: SolveRef.Best,
    +e: {r1 == r2 : SolveRef.Best},
    +h: {P.job_res_gs_b(fuel, inf, G, gs, S, limit, r1) == True{}
        : Bool}) ->
  {P.job_res_gs_b(fuel, inf, G, gs, S, limit, r2) == True{} : Bool}:
  %e : {P.job_res_gs_b(fuel, inf, G, gs, S, limit, _) == True{} : Bool}
  h

# The chunk leaf on the term `par_chunks` actually calls: `SolveK.chunk_best`
# over the segment, with the root-allocated table buffer.
def P.chunk_best_leaf(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +cs: +List<+List<Nat>>, +nd: Bool,
    +pre: +List<+List<Nat>>, +seg: +List<+List<Nat>>,
    +post: +List<+List<Nat>>, +off: U32,
    +eG : {G == List.append(&2, +List<Nat>,
             List.append(&2, +List<Nat>, pre, seg), post)
           : +List<+List<Nat>>},
    +eoff: {U32.from_nat(Groups.len_words(pre)) == off : U32},
    +ele: {Nat.is_le(Groups.len_words(cs), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +h3: {Nat.is_lt(3n, inf) == True{} : Bool},
    +h6: {Nat.is_lt(6n, inf) == True{} : Bool},
    +ai: {FO.FO.all_in_ref(cs, G) == True{} : Bool},
    +hnd: {FN.FN.nodup_ok(nd, cs) == True{} : Bool}) ->
  {P.job_res_gs_b(1n+p, inf, G, seg, cs, inf,
     SolveK.chunk_best(1n+p, seg, off, G, SolveFast.glist_of_guesses(G, 0, 1),
       SolveFast.build_cwords(cs, G, 0, U32.from_nat(Groups.len_words(G))),
       cs, Groups.len_words(cs), nd,
       SolveFast.init_floor(Groups.len_words(cs)), inf,
       SolveFast.mk_buf_tbl(nd, G, cs, Groups.len_words(cs))))
   == True{} : Bool}:
  +n : Nat = Groups.len_words(cs)
  +rwsG : +List<FT.FT.RowWord> = FT.FT.guesses_to_rws(G, 0, 1)
  +cwS : +List<SolveFast.CWord> =
    SolveFast.build_cwords(cs, G, 0, U32.from_nat(Groups.len_words(G)))
  +has_buf : Bool = FH.FH.mk_buf_has(nd, G, cs, n)
  +erwsG : {FT.FT.rws_words(rwsG) == G : +List<+List<Nat>>} =
    FT.FT.guesses_to_rws_words(G, 0, 1)
  +hrwsG : {FH.FH.rws_ok_if(has_buf, G, n, rwsG) == True{} : Bool} =
    FOpt.FOpt.guesses_to_rws_ok_if(has_buf, G, n)
  +ecwS : {SolveFast.cwords_words(cwS) == cs : +List<+List<Nat>>} =
    FT.FT.build_cwords_words(cs, G, 0, U32.from_nat(Groups.len_words(G)))
  +hcwS : {FH.FH.cwords_ok_if(has_buf, G, cs, n, cwS) == True{} : Bool} =
    FOpt.FOpt.build_cwords_ok_if(has_buf, G, cs, n, ai)
  +egG : {SolveFast.glist_of_guesses(G, 0, 1)
          == FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}) : SolveFast.GList} =
    FT.FT.glist_of_guesses_eq(G, 0, 1)
  +econc : {SolveK.chunk_best(1n+p, seg, off, G,
               SolveFast.glist_of_guesses(G, 0, 1), cwS, cs, n, nd,
               SolveFast.init_floor(n), inf, SolveFast.mk_buf_tbl(nd, G, cs, n))
             == SolveK.chunk_best(1n+p, seg, off, G,
                  FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS, cs, n, nd,
                  SolveFast.init_floor(n), inf,
                  SolveFast.mk_buf_tbl(nd, G, cs, n))
             : SolveRef.Best} =
    Equal.cong(SolveFast.GList, SolveRef.Best,
      gl => SolveK.chunk_best(1n+p, seg, off, G, gl, cwS, cs, n, nd,
              SolveFast.init_floor(n), inf, SolveFast.mk_buf_tbl(nd, G, cs, n)),
      SolveFast.glist_of_guesses(G, 0, 1),
      FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), egG)
  P.job_res_gs_b_transport(1n+p, inf, G, seg, cs, inf,
    SolveK.chunk_best(1n+p, seg, off, G,
      FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS, cs, n, nd,
      SolveFast.init_floor(n), inf, SolveFast.mk_buf_tbl(nd, G, cs, n)),
    SolveK.chunk_best(1n+p, seg, off, G,
      SolveFast.glist_of_guesses(G, 0, 1), cwS, cs, n, nd,
      SolveFast.init_floor(n), inf, SolveFast.mk_buf_tbl(nd, G, cs, n)),
    Equal.sym(SolveRef.Best,
      SolveK.chunk_best(1n+p, seg, off, G,
        SolveFast.glist_of_guesses(G, 0, 1), cwS, cs, n, nd,
        SolveFast.init_floor(n), inf, SolveFast.mk_buf_tbl(nd, G, cs, n)),
      SolveK.chunk_best(1n+p, seg, off, G,
        FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS, cs, n, nd,
        SolveFast.init_floor(n), inf, SolveFast.mk_buf_tbl(nd, G, cs, n)),
      econc),
    P.chunk_leaf(p, inf, G, cs, nd, has_buf, rwsG, cwS, pre, seg, post, off,
      SolveFast.mk_buf_tbl(nd, G, cs, n),
      FH.FH.mk_buf_tbl_ok(nd, G, cs, n, {==}),
      FH.FH.buf_dup(SolveFast.mk_buf_tbl(nd, G, cs, n)),
      erwsG, hrwsG, ecwS, hcwS, eG, eoff, ele, hz, h1, h3, h6, ai, hnd))

# ---------------------------------------------------------------------------
# Per-chunk results: validity and finite cost
# ---------------------------------------------------------------------------

# One chunk result is acceptable when it is valid at the cutoff, and its cost
# is below the cutoff.
def P.elt_ok(+limit: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +r: SolveRef.Best) -> Bool:
  Bool.and(FVal.FV.best_ok_b(limit, G, S, r),
    Nat.is_le(Eval.Eval.cost_of(r), limit))

def P.elt_ok_better(+limit: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +a: SolveRef.Best, +b: SolveRef.Best,
    +ha: {P.elt_ok(limit, G, S, a) == True{} : Bool},
    +hb: {P.elt_ok(limit, G, S, b) == True{} : Bool}) ->
  {P.elt_ok(limit, G, S, FC.FC.better_best(a, b)) == True{} : Bool}:
  +hoka = Logic.Proof.and_true_l(FVal.FV.best_ok_b(limit, G, S, a),
            Nat.is_le(Eval.Eval.cost_of(a), limit), ha)
  +hca = Logic.Proof.and_true_r(FVal.FV.best_ok_b(limit, G, S, a),
           Nat.is_le(Eval.Eval.cost_of(a), limit), ha)
  +hokb = Logic.Proof.and_true_l(FVal.FV.best_ok_b(limit, G, S, b),
            Nat.is_le(Eval.Eval.cost_of(b), limit), hb)
  FO.FO.bool_and_intro(FVal.FV.best_ok_b(limit, G, S,
      FC.FC.better_best(a, b)),
    Nat.is_le(Eval.Eval.cost_of(FC.FC.better_best(a, b)), limit),
    P.best_ok_better(limit, G, S, a, b, hoka, hokb),
    NatProof.Nat.is_le_trans(Eval.Eval.cost_of(FC.FC.better_best(a, b)),
      Eval.Eval.cost_of(a), limit, FVal.FV.better_best_le_l(a, b), hca))

# Every result of the list is acceptable.
def P.ok_list(+limit: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +rs: +List<SolveRef.Best>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case Con{r, t}:
      Bool.and(P.elt_ok(limit, G, S, r), P.ok_list(limit, G, S, t))

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
    case Con{r, t}:
      +hr = Logic.Proof.and_true_l(P.elt_ok(limit, G, S, r),
              P.ok_list(limit, G, S, t), hx)
      +ht = Logic.Proof.and_true_r(P.elt_ok(limit, G, S, r),
              P.ok_list(limit, G, S, t), hx)
      FO.FO.bool_and_intro(P.elt_ok(limit, G, S, r),
        P.ok_list(limit, G, S, List.append(&2, SolveRef.Best, t, ys)),
        hr, P.ok_list_append(limit, G, S, t, ys, ht, hy))

# Folding acceptable results keeps the accumulator acceptable.
def P.ok_list_fold(+limit: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +rs: +List<SolveRef.Best>,
    +best: SolveRef.Best,
    +h: {P.ok_list(limit, G, S, rs) == True{} : Bool},
    +hb: {P.elt_ok(limit, G, S, best) == True{} : Bool}) ->
  {P.elt_ok(limit, G, S, SolveK.fold_results(rs, best)) == True{} : Bool}:
  match rs:
    case Nil{}:
      hb
    case Con{r, t}:
      match r:
        case SolveRef.Best{+tree, +cost}:
          +hr = Logic.Proof.and_true_l(
                  P.elt_ok(limit, G, S, SolveRef.Best{tree, cost}),
                  P.ok_list(limit, G, S, t), h)
          +ht = Logic.Proof.and_true_r(
                  P.elt_ok(limit, G, S, SolveRef.Best{tree, cost}),
                  P.ok_list(limit, G, S, t), h)
          P.ok_list_fold(limit, G, S, t,
            FC.FC.better_best(SolveRef.Best{tree, cost}, best), ht,
            P.elt_ok_better(limit, G, S, SolveRef.Best{tree, cost}, best,
              hr, hb))

# The neutral accumulator is acceptable at a positive cutoff.
def P.elt_ok_dummy_inf(+limit: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>,
    +hge: {Nat.is_ge(limit, limit) == True{} : Bool}) ->
  {P.elt_ok(limit, G, S, Eval.Eval.dummy_inf(limit)) == True{} : Bool}:
  FO.FO.bool_and_intro(
    FVal.FV.best_ok_b(limit, G, S, Eval.Eval.dummy_inf(limit)),
    Nat.is_le(Eval.Eval.cost_of(Eval.Eval.dummy_inf(limit)), limit),
    FVal.FV.best_ok_init(limit, G, S, Eval.Eval.dummy_inf(limit), hge),
    NatProof.Nat.is_le_refl(limit))

# Folding a singleton result list is one `better` step.
def P.fold_single(+r: SolveRef.Best, +best: SolveRef.Best) ->
  {SolveK.fold_results(r <> Nil{}, best)
   == FC.FC.better_best(r, best) : SolveRef.Best}:
  match r:
    case SolveRef.Best{+tree, +cost}:
      {==}

# A chunk job result bounds the fold of its singleton list by the reference
# fold over the segment, from any accumulator below the cutoff.
def P.single_le(+p: Nat, +G: +List<+List<Nat>>, +cs: +List<+List<Nat>>,
    +inf: Nat, +seg: +List<+List<Nat>>, +acc: SolveRef.Best,
    +r: SolveRef.Best,
    +hjr: {P.job_res_gs_b(1n+p, inf, G, seg, cs, inf, r) == True{} : Bool},
    +hacc: {Nat.is_le(Eval.Eval.cost_of(acc), inf) == True{} : Bool}) ->
  {Nat.is_le(Eval.Eval.cost_of(SolveK.fold_results(r <> Nil{}, acc)),
     Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, cs, inf, seg, acc)))
   == True{} : Bool}:
  +hb2 = Logic.Proof.and_true_r(FVal.FV.best_ok_b(inf, G, cs, r),
           Bool.and(Nat.is_le(Eval.Eval.cost_of(r), inf),
             Nat.is_le(Eval.Eval.cost_of(r),
               Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, cs, inf, seg,
                 Eval.Eval.dummy_inf(inf))))), hjr)
  +hcost = Logic.Proof.and_true_r(Nat.is_le(Eval.Eval.cost_of(r), inf),
             Nat.is_le(Eval.Eval.cost_of(r),
               Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, cs, inf, seg,
                 Eval.Eval.dummy_inf(inf)))), hb2)
  +eab : {Eval.Eval.guesses(1n+p, G, cs, inf, seg, acc)
          == FC.FC.better_best(
               Eval.Eval.guesses(1n+p, G, cs, inf, seg,
                 Eval.Eval.dummy_inf(inf)), acc) : SolveRef.Best} =
    P.guesses_as_better(p, G, cs, inf, seg, acc, hacc)
  +emon = P.better_mono_le(r,
            Eval.Eval.guesses(1n+p, G, cs, inf, seg,
              Eval.Eval.dummy_inf(inf)),
            acc, acc, hcost, NatProof.Nat.is_le_refl(Eval.Eval.cost_of(acc)))
  +hmain = Fold.OQ.le_cong_r(
             Eval.Eval.cost_of(FC.FC.better_best(r, acc)),
             Eval.Eval.cost_of(FC.FC.better_best(
               Eval.Eval.guesses(1n+p, G, cs, inf, seg,
                 Eval.Eval.dummy_inf(inf)), acc)),
             Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, cs, inf, seg, acc)),
             Equal.cong(SolveRef.Best, Nat, Eval.Eval.cost_of,
               FC.FC.better_best(Eval.Eval.guesses(1n+p, G, cs, inf, seg,
                 Eval.Eval.dummy_inf(inf)), acc),
               Eval.Eval.guesses(1n+p, G, cs, inf, seg, acc),
               Equal.sym(SolveRef.Best,
                 Eval.Eval.guesses(1n+p, G, cs, inf, seg, acc),
                 FC.FC.better_best(Eval.Eval.guesses(1n+p, G, cs, inf, seg,
                   Eval.Eval.dummy_inf(inf)), acc), eab)),
             emon)
  Fold.OQ.le_cong_l(
    Eval.Eval.cost_of(SolveK.fold_results(r <> Nil{}, acc)),
    Eval.Eval.cost_of(FC.FC.better_best(r, acc)),
    Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, cs, inf, seg, acc)),
    Equal.cong(SolveRef.Best, Nat, Eval.Eval.cost_of,
      SolveK.fold_results(r <> Nil{}, acc), FC.FC.better_best(r, acc),
      P.fold_single(r, acc)),
    hmain)

# The split of a segment, as transparent definitions so the type indices of
# the induction below can mention them.
def P.half_of(+xs: +List<+List<Nat>>) -> Nat:
  SolveK.half(Groups.len_words(xs))

def P.left_of(+xs: +List<+List<Nat>>) -> +List<+List<Nat>>:
  List.take(&2, +List<Nat>, xs, P.half_of(xs))

def P.right_of(+xs: +List<+List<Nat>>) -> +List<+List<Nat>>:
  List.drop(&2, +List<Nat>, xs, P.half_of(xs))

def P.off_next(+off: U32, +xs: +List<+List<Nat>>) -> U32:
  U32.add(off, U32.from_nat(P.half_of(xs)))

def P.split_back(+xs: +List<+List<Nat>>) ->
  {List.append(&2, +List<Nat>, P.left_of(xs), P.right_of(xs)) == xs
   : +List<+List<Nat>>}:
  ParList.ParList.take_drop(xs, P.half_of(xs))

def P.half_of_le(+xs: +List<+List<Nat>>) ->
  {Nat.is_le(P.half_of(xs), Groups.len_words(xs)) == True{} : Bool}:
  P.half_le(Groups.len_words(xs))

def P.len_left(+xs: +List<+List<Nat>>) ->
  {Groups.len_words(P.left_of(xs)) == P.half_of(xs) : Nat}:
  P.len_take_le(xs, P.half_of(xs), P.half_of_le(xs))

def P.eG1(+pre: +List<+List<Nat>>, +seg: +List<+List<Nat>>,
    +post: +List<+List<Nat>>) ->
  {List.append(&2, +List<Nat>,
     List.append(&2, +List<Nat>, pre, seg), post)
   == List.append(&2, +List<Nat>,
        List.append(&2, +List<Nat>, pre,
          List.append(&2, +List<Nat>, P.left_of(seg), P.right_of(seg))),
        post) : +List<+List<Nat>>}:
  Equal.cong(+List<+List<Nat>>, +List<+List<Nat>>,
    l => List.append(&2, +List<Nat>,
      List.append(&2, +List<Nat>, pre, l), post),
    seg, List.append(&2, +List<Nat>, P.left_of(seg), P.right_of(seg)),
    Equal.sym(+List<+List<Nat>>,
      List.append(&2, +List<Nat>, P.left_of(seg), P.right_of(seg)), seg,
      P.split_back(seg)))

def P.eG2(+pre: +List<+List<Nat>>, +seg: +List<+List<Nat>>,
    +post: +List<+List<Nat>>) ->
  {List.append(&2, +List<Nat>,
     List.append(&2, +List<Nat>, pre,
       List.append(&2, +List<Nat>, P.left_of(seg), P.right_of(seg))),
     post)
   == List.append(&2, +List<Nat>,
        List.append(&2, +List<Nat>,
          List.append(&2, +List<Nat>, pre, P.left_of(seg)),
          P.right_of(seg)),
        post) : +List<+List<Nat>>}:
  Equal.cong(+List<+List<Nat>>, +List<+List<Nat>>,
    l => List.append(&2, +List<Nat>, l, post),
    List.append(&2, +List<Nat>, pre,
      List.append(&2, +List<Nat>, P.left_of(seg), P.right_of(seg))),
    List.append(&2, +List<Nat>,
      List.append(&2, +List<Nat>, pre, P.left_of(seg)),
      P.right_of(seg)),
    Equal.sym(+List<+List<Nat>>,
      List.append(&2, +List<Nat>,
        List.append(&2, +List<Nat>, pre, P.left_of(seg)),
        P.right_of(seg)),
      List.append(&2, +List<Nat>, pre,
        List.append(&2, +List<Nat>, P.left_of(seg), P.right_of(seg))),
      FN.FN.list_append_assoc(pre, P.left_of(seg), P.right_of(seg))))

def P.eG3(+pre: +List<+List<Nat>>, +seg: +List<+List<Nat>>,
    +post: +List<+List<Nat>>) ->
  {List.append(&2, +List<Nat>,
     List.append(&2, +List<Nat>,
       List.append(&2, +List<Nat>, pre, P.left_of(seg)), P.right_of(seg)),
     post)
   == List.append(&2, +List<Nat>,
        List.append(&2, +List<Nat>, pre, P.left_of(seg)),
        List.append(&2, +List<Nat>, P.right_of(seg), post))
   : +List<+List<Nat>>}:
  FN.FN.list_append_assoc(
    List.append(&2, +List<Nat>, pre, P.left_of(seg)), P.right_of(seg), post)

# The left child keeps the prefix, taking the right half into its suffix.
def P.eG_left(+pre: +List<+List<Nat>>, +seg: +List<+List<Nat>>,
    +post: +List<+List<Nat>>, +G: +List<+List<Nat>>,
    +eG : {G == List.append(&2, +List<Nat>,
             List.append(&2, +List<Nat>, pre, seg), post)
           : +List<+List<Nat>>}) ->
  {G == List.append(&2, +List<Nat>,
         List.append(&2, +List<Nat>, pre, P.left_of(seg)),
         List.append(&2, +List<Nat>, P.right_of(seg), post))
   : +List<+List<Nat>>}:
  Equal.trans(+List<+List<Nat>>, G,
    List.append(&2, +List<Nat>,
      List.append(&2, +List<Nat>, pre, seg), post),
    List.append(&2, +List<Nat>,
      List.append(&2, +List<Nat>, pre, P.left_of(seg)),
      List.append(&2, +List<Nat>, P.right_of(seg), post)),
    eG,
    Equal.trans(+List<+List<Nat>>,
      List.append(&2, +List<Nat>,
        List.append(&2, +List<Nat>, pre, seg), post),
      List.append(&2, +List<Nat>,
        List.append(&2, +List<Nat>,
          List.append(&2, +List<Nat>, pre, P.left_of(seg)),
          P.right_of(seg)),
        post),
      List.append(&2, +List<Nat>,
        List.append(&2, +List<Nat>, pre, P.left_of(seg)),
        List.append(&2, +List<Nat>, P.right_of(seg), post)),
      Equal.trans(+List<+List<Nat>>,
        List.append(&2, +List<Nat>,
          List.append(&2, +List<Nat>, pre, seg), post),
        List.append(&2, +List<Nat>,
          List.append(&2, +List<Nat>, pre,
            List.append(&2, +List<Nat>, P.left_of(seg), P.right_of(seg))),
          post),
        List.append(&2, +List<Nat>,
          List.append(&2, +List<Nat>,
            List.append(&2, +List<Nat>, pre, P.left_of(seg)),
            P.right_of(seg)),
          post),
        P.eG1(pre, seg, post), P.eG2(pre, seg, post)),
      P.eG3(pre, seg, post)))

# The right child takes the left half into its prefix.
def P.eG_right(+pre: +List<+List<Nat>>, +seg: +List<+List<Nat>>,
    +post: +List<+List<Nat>>, +G: +List<+List<Nat>>,
    +eG : {G == List.append(&2, +List<Nat>,
             List.append(&2, +List<Nat>, pre, seg), post)
           : +List<+List<Nat>>}) ->
  {G == List.append(&2, +List<Nat>,
         List.append(&2, +List<Nat>,
           List.append(&2, +List<Nat>, pre, P.left_of(seg)),
           P.right_of(seg)),
         post) : +List<+List<Nat>>}:
  Equal.trans(+List<+List<Nat>>, G,
    List.append(&2, +List<Nat>,
      List.append(&2, +List<Nat>, pre, seg), post),
    List.append(&2, +List<Nat>,
      List.append(&2, +List<Nat>,
        List.append(&2, +List<Nat>, pre, P.left_of(seg)),
        P.right_of(seg)),
      post),
    eG,
    Equal.trans(+List<+List<Nat>>,
      List.append(&2, +List<Nat>,
        List.append(&2, +List<Nat>, pre, seg), post),
      List.append(&2, +List<Nat>,
        List.append(&2, +List<Nat>, pre,
          List.append(&2, +List<Nat>, P.left_of(seg), P.right_of(seg))),
        post),
      List.append(&2, +List<Nat>,
        List.append(&2, +List<Nat>,
          List.append(&2, +List<Nat>, pre, P.left_of(seg)),
          P.right_of(seg)),
        post),
      P.eG1(pre, seg, post), P.eG2(pre, seg, post)))

# The right child's offset is the left child's length added to the prefix
# offset.
def P.eoff_right(+pre: +List<+List<Nat>>, +seg: +List<+List<Nat>>,
    +off: U32,
    +eoff: {U32.from_nat(Groups.len_words(pre)) == off : U32}) ->
  {U32.from_nat(Groups.len_words(
      List.append(&2, +List<Nat>, pre, P.left_of(seg))))
   == P.off_next(off, seg) : U32}:
  Equal.trans(U32,
    U32.from_nat(Groups.len_words(
      List.append(&2, +List<Nat>, pre, P.left_of(seg)))),
    U32.from_nat(Nat.add(Groups.len_words(pre), P.half_of(seg))),
    U32.add(off, U32.from_nat(P.half_of(seg))),
    Equal.cong(Nat, U32, x => U32.from_nat(x),
      Groups.len_words(List.append(&2, +List<Nat>, pre, P.left_of(seg))),
      Nat.add(Groups.len_words(pre), P.half_of(seg)),
      Equal.trans(Nat,
        Groups.len_words(List.append(&2, +List<Nat>, pre, P.left_of(seg))),
        Nat.add(Groups.len_words(pre), Groups.len_words(P.left_of(seg))),
        Nat.add(Groups.len_words(pre), P.half_of(seg)),
        FT.FT.len_words_append(pre, P.left_of(seg)),
        Equal.cong(Nat, Nat, x => Nat.add(Groups.len_words(pre), x),
          Groups.len_words(P.left_of(seg)), P.half_of(seg),
          P.len_left(seg)))),
    Equal.trans(U32,
      U32.from_nat(Nat.add(Groups.len_words(pre), P.half_of(seg))),
      U32.add(U32.from_nat(Groups.len_words(pre)),
        U32.from_nat(P.half_of(seg))),
      U32.add(off, U32.from_nat(P.half_of(seg))),
      Equal.sym(U32,
        U32.add(U32.from_nat(Groups.len_words(pre)),
          U32.from_nat(P.half_of(seg))),
        U32.from_nat(Nat.add(Groups.len_words(pre), P.half_of(seg))),
        FT.FT.u32_add_from_nat(Groups.len_words(pre), P.half_of(seg))),
      Equal.cong(U32, U32, x => U32.add(x, U32.from_nat(P.half_of(seg))),
        U32.from_nat(Groups.len_words(pre)), off, eoff)))

# ---------------------------------------------------------------------------
# The chunked root: cost bound and validity of every chunk result
# ---------------------------------------------------------------------------

def P.par_cost(+d: Nat, +seg: +List<+List<Nat>>, +off: U32, +p: Nat,
    +G: +List<+List<Nat>>, +cs: +List<+List<Nat>>, +nd: Bool, +inf: Nat,
    +pre: +List<+List<Nat>>, +post: +List<+List<Nat>>,
    +acc: SolveRef.Best,
    +en: {Groups.len_words(cs) == 1n+p : Nat},
    +eG : {G == List.append(&2, +List<Nat>,
             List.append(&2, +List<Nat>, pre, seg), post)
           : +List<+List<Nat>>},
    +eoff: {U32.from_nat(Groups.len_words(pre)) == off : U32},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +h3: {Nat.is_lt(3n, inf) == True{} : Bool},
    +h6: {Nat.is_lt(6n, inf) == True{} : Bool},
    +ai: {FO.FO.all_in_ref(cs, G) == True{} : Bool},
    +hnd: {FN.FN.nodup_ok(nd, cs) == True{} : Bool},
    +hacc: {Nat.is_le(Eval.Eval.cost_of(acc), inf) == True{} : Bool}) ->
  {Nat.is_le(
     Eval.Eval.cost_of(SolveK.fold_results(
       SolveK.par_chunks(d, seg, off, 1n+p, G,
         SolveFast.glist_of_guesses(G, 0, 1),
         SolveFast.build_cwords(cs, G, 0, U32.from_nat(Groups.len_words(G))),
         cs, Groups.len_words(cs), nd,
         SolveFast.init_floor(Groups.len_words(cs)), inf), acc)),
     Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, cs, inf, seg, acc)))
   == True{} : Bool}:
  match d:
    case 0n:
      +n : Nat = Groups.len_words(cs)
      +ele : {Nat.is_le(n, 1n+p) == True{} : Bool} =
        Fold.OQ.le_cong_l(n, 1n+p, 1n+p, en,
          NatProof.Nat.is_le_refl(1n+p))
      P.single_le(p, G, cs, inf, seg, acc,
        SolveK.chunk_best(1n+p, seg, off, G,
          SolveFast.glist_of_guesses(G, 0, 1),
          SolveFast.build_cwords(cs, G, 0, U32.from_nat(Groups.len_words(G))),
          cs, n, nd, SolveFast.init_floor(n), inf,
          SolveFast.mk_buf_tbl(nd, G, cs, n)),
        P.chunk_best_leaf(p, inf, G, cs, nd, pre, seg, post, off, eG, eoff,
          ele, hz, h1, h3, h6, ai, hnd), hacc)
    case 1n+dc:
      match seg:
        case Nil{}:
          NatProof.Nat.is_le_refl(Eval.Eval.cost_of(acc))
        case Con{w, rest}:
          match rest:
            case Nil{}:
              +n : Nat = Groups.len_words(cs)
              +ele : {Nat.is_le(n, 1n+p) == True{} : Bool} =
                Fold.OQ.le_cong_l(n, 1n+p, 1n+p, en,
                  NatProof.Nat.is_le_refl(1n+p))
              P.single_le(p, G, cs, inf, seg, acc,
                SolveK.chunk_best(1n+p, seg, off, G,
                  SolveFast.glist_of_guesses(G, 0, 1),
                  SolveFast.build_cwords(cs, G, 0,
                    U32.from_nat(Groups.len_words(G))),
                  cs, n, nd, SolveFast.init_floor(n), inf,
                  SolveFast.mk_buf_tbl(nd, G, cs, n)),
                P.chunk_best_leaf(p, inf, G, cs, nd, pre, seg, post, off, eG,
                  eoff, ele, hz, h1, h3, h6, ai, hnd), hacc)
            case Con{w2, rest2}:
              +n : Nat = Groups.len_words(cs)
              +ele : {Nat.is_le(n, 1n+p) == True{} : Bool} =
                Fold.OQ.le_cong_l(n, 1n+p, 1n+p, en,
                  NatProof.Nat.is_le_refl(1n+p))
              +off2 : U32 = P.off_next(off, seg)
              +e1 : {List.append(&2, +List<Nat>,
                        List.append(&2, +List<Nat>, pre, seg), post)
                     == List.append(&2, +List<Nat>,
                          List.append(&2, +List<Nat>, pre,
                            List.append(&2, +List<Nat>, P.left_of(seg),
                              P.right_of(seg))),
                          post) : +List<+List<Nat>>} =
                Equal.cong(+List<+List<Nat>>, +List<+List<Nat>>,
                  l => List.append(&2, +List<Nat>,
                    List.append(&2, +List<Nat>, pre, l), post),
                  seg,
                  List.append(&2, +List<Nat>, P.left_of(seg),
                    P.right_of(seg)),
                  Equal.sym(+List<+List<Nat>>,
                    List.append(&2, +List<Nat>, P.left_of(seg),
                      P.right_of(seg)), seg, P.split_back(seg)))
              +e2 : {List.append(&2, +List<Nat>,
                        List.append(&2, +List<Nat>, pre,
                          List.append(&2, +List<Nat>, P.left_of(seg),
                            P.right_of(seg))),
                        post)
                     == List.append(&2, +List<Nat>,
                          List.append(&2, +List<Nat>,
                            List.append(&2, +List<Nat>, pre, P.left_of(seg)),
                            P.right_of(seg)),
                          post) : +List<+List<Nat>>} =
                Equal.cong(+List<+List<Nat>>, +List<+List<Nat>>,
                  l => List.append(&2, +List<Nat>, l, post),
                  List.append(&2, +List<Nat>, pre,
                    List.append(&2, +List<Nat>, P.left_of(seg),
                      P.right_of(seg))),
                  List.append(&2, +List<Nat>,
                    List.append(&2, +List<Nat>, pre, P.left_of(seg)),
                    P.right_of(seg)),
                  Equal.sym(+List<+List<Nat>>,
                    List.append(&2, +List<Nat>,
                      List.append(&2, +List<Nat>, pre, P.left_of(seg)),
                      P.right_of(seg)),
                    List.append(&2, +List<Nat>, pre,
                      List.append(&2, +List<Nat>, P.left_of(seg),
                        P.right_of(seg))),
                    FN.FN.list_append_assoc(pre, P.left_of(seg),
                      P.right_of(seg))))
              +e3 : {List.append(&2, +List<Nat>,
                        List.append(&2, +List<Nat>,
                          List.append(&2, +List<Nat>, pre, P.left_of(seg)),
                          P.right_of(seg)),
                        post)
                     == List.append(&2, +List<Nat>,
                          List.append(&2, +List<Nat>, pre, P.left_of(seg)),
                          List.append(&2, +List<Nat>, P.right_of(seg), post))
                     : +List<+List<Nat>>} =
                FN.FN.list_append_assoc(
                  List.append(&2, +List<Nat>, pre, P.left_of(seg)),
                  P.right_of(seg), post)
              +eGl : {G == List.append(&2, +List<Nat>,
                         List.append(&2, +List<Nat>, pre, P.left_of(seg)),
                         List.append(&2, +List<Nat>, P.right_of(seg), post))
                      : +List<+List<Nat>>} =
                Equal.trans(+List<+List<Nat>>, G,
                  List.append(&2, +List<Nat>,
                    List.append(&2, +List<Nat>, pre, seg), post),
                  List.append(&2, +List<Nat>,
                    List.append(&2, +List<Nat>, pre, P.left_of(seg)),
                    List.append(&2, +List<Nat>, P.right_of(seg), post)),
                  eG,
                  Equal.trans(+List<+List<Nat>>,
                    List.append(&2, +List<Nat>,
                      List.append(&2, +List<Nat>, pre, seg), post),
                    List.append(&2, +List<Nat>,
                      List.append(&2, +List<Nat>,
                        List.append(&2, +List<Nat>, pre, P.left_of(seg)),
                        P.right_of(seg)),
                      post),
                    List.append(&2, +List<Nat>,
                      List.append(&2, +List<Nat>, pre, P.left_of(seg)),
                      List.append(&2, +List<Nat>, P.right_of(seg), post)),
                    Equal.trans(+List<+List<Nat>>,
                      List.append(&2, +List<Nat>,
                        List.append(&2, +List<Nat>, pre, seg), post),
                      List.append(&2, +List<Nat>,
                        List.append(&2, +List<Nat>, pre,
                          List.append(&2, +List<Nat>, P.left_of(seg),
                            P.right_of(seg))),
                        post),
                      List.append(&2, +List<Nat>,
                        List.append(&2, +List<Nat>,
                          List.append(&2, +List<Nat>, pre, P.left_of(seg)),
                          P.right_of(seg)),
                        post),
                      e1, e2),
                    e3))
              +eGr : {G == List.append(&2, +List<Nat>,
                         List.append(&2, +List<Nat>,
                           List.append(&2, +List<Nat>, pre, P.left_of(seg)),
                           P.right_of(seg)),
                         post) : +List<+List<Nat>>} =
                Equal.trans(+List<+List<Nat>>, G,
                  List.append(&2, +List<Nat>,
                    List.append(&2, +List<Nat>, pre, seg), post),
                  List.append(&2, +List<Nat>,
                    List.append(&2, +List<Nat>,
                      List.append(&2, +List<Nat>, pre, P.left_of(seg)),
                      P.right_of(seg)),
                    post),
                  eG,
                  Equal.trans(+List<+List<Nat>>,
                    List.append(&2, +List<Nat>,
                      List.append(&2, +List<Nat>, pre, seg), post),
                    List.append(&2, +List<Nat>,
                      List.append(&2, +List<Nat>, pre,
                        List.append(&2, +List<Nat>, P.left_of(seg),
                          P.right_of(seg))),
                      post),
                    List.append(&2, +List<Nat>,
                      List.append(&2, +List<Nat>,
                        List.append(&2, +List<Nat>, pre, P.left_of(seg)),
                        P.right_of(seg)),
                      post),
                    e1, e2))
              +eL1 : {Groups.len_words(
                        List.append(&2, +List<Nat>, pre, P.left_of(seg)))
                      == Nat.add(Groups.len_words(pre), P.half_of(seg))
                      : Nat} =
                Equal.trans(Nat,
                  Groups.len_words(
                    List.append(&2, +List<Nat>, pre, P.left_of(seg))),
                  Nat.add(Groups.len_words(pre),
                    Groups.len_words(P.left_of(seg))),
                  Nat.add(Groups.len_words(pre), P.half_of(seg)),
                  FT.FT.len_words_append(pre, P.left_of(seg)),
                  Equal.cong(Nat, Nat,
                    x => Nat.add(Groups.len_words(pre), x),
                    Groups.len_words(P.left_of(seg)), P.half_of(seg),
                    P.len_left(seg)))
              +eL2 : {U32.from_nat(Groups.len_words(
                         List.append(&2, +List<Nat>, pre, P.left_of(seg))))
                      == U32.add(U32.from_nat(Groups.len_words(pre)),
                           U32.from_nat(P.half_of(seg))) : U32} =
                Equal.trans(U32,
                  U32.from_nat(Groups.len_words(
                    List.append(&2, +List<Nat>, pre, P.left_of(seg)))),
                  U32.from_nat(Nat.add(Groups.len_words(pre),
                    P.half_of(seg))),
                  U32.add(U32.from_nat(Groups.len_words(pre)),
                    U32.from_nat(P.half_of(seg))),
                  Equal.cong(Nat, U32, x => U32.from_nat(x),
                    Groups.len_words(
                      List.append(&2, +List<Nat>, pre, P.left_of(seg))),
                    Nat.add(Groups.len_words(pre), P.half_of(seg)), eL1),
                  Equal.sym(U32,
                    U32.add(U32.from_nat(Groups.len_words(pre)),
                      U32.from_nat(P.half_of(seg))),
                    U32.from_nat(Nat.add(Groups.len_words(pre),
                      P.half_of(seg))),
                    FT.FT.u32_add_from_nat(Groups.len_words(pre),
                      P.half_of(seg))))
              +eoff2 : {U32.from_nat(Groups.len_words(
                          List.append(&2, +List<Nat>, pre, P.left_of(seg))))
                        == off2 : U32} =
                Equal.trans(U32,
                  U32.from_nat(Groups.len_words(
                    List.append(&2, +List<Nat>, pre, P.left_of(seg)))),
                  U32.add(U32.from_nat(Groups.len_words(pre)),
                    U32.from_nat(P.half_of(seg))),
                  U32.add(off, U32.from_nat(P.half_of(seg))),
                  eL2,
                  Equal.cong(U32, U32,
                    x => U32.add(x, U32.from_nat(P.half_of(seg))),
                    U32.from_nat(Groups.len_words(pre)), off, eoff))
              +ihl : {Nat.is_le(
                        Eval.Eval.cost_of(SolveK.fold_results(
                          SolveK.par_chunks(dc, P.left_of(seg), off, 1n+p, G,
                            SolveFast.glist_of_guesses(G, 0, 1),
                            SolveFast.build_cwords(cs, G, 0,
                              U32.from_nat(Groups.len_words(G))),
                            cs, n, nd, SolveFast.init_floor(n), inf), acc)),
                        Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, cs, inf,
                          P.left_of(seg), acc))) == True{} : Bool} =
                P.par_cost(dc, P.left_of(seg), off, p, G, cs, nd, inf, pre,
                  List.append(&2, +List<Nat>, P.right_of(seg), post), acc, en,
                  eGl, eoff, hz, h1, h3, h6, ai, hnd, hacc)
              +hacc2 : {Nat.is_le(
                          Eval.Eval.cost_of(SolveK.fold_results(
                            SolveK.par_chunks(dc, P.left_of(seg), off, 1n+p, G,
                              SolveFast.glist_of_guesses(G, 0, 1),
                              SolveFast.build_cwords(cs, G, 0,
                                U32.from_nat(Groups.len_words(G))),
                              cs, n, nd, SolveFast.init_floor(n), inf), acc)),
                          inf) == True{} : Bool} =
                NatProof.Nat.is_le_trans(
                  Eval.Eval.cost_of(SolveK.fold_results(
                    SolveK.par_chunks(dc, P.left_of(seg), off, 1n+p, G,
                      SolveFast.glist_of_guesses(G, 0, 1),
                      SolveFast.build_cwords(cs, G, 0,
                        U32.from_nat(Groups.len_words(G))),
                      cs, n, nd, SolveFast.init_floor(n), inf), acc)),
                  Eval.Eval.cost_of(acc), inf,
                  P.fold_le_best(
                    SolveK.par_chunks(dc, P.left_of(seg), off, 1n+p, G,
                      SolveFast.glist_of_guesses(G, 0, 1),
                      SolveFast.build_cwords(cs, G, 0,
                        U32.from_nat(Groups.len_words(G))),
                      cs, n, nd, SolveFast.init_floor(n), inf), acc),
                  hacc)
              +ihr : {Nat.is_le(
                        Eval.Eval.cost_of(SolveK.fold_results(
                          SolveK.par_chunks(dc, P.right_of(seg), off2, 1n+p, G,
                            SolveFast.glist_of_guesses(G, 0, 1),
                            SolveFast.build_cwords(cs, G, 0,
                              U32.from_nat(Groups.len_words(G))),
                            cs, n, nd, SolveFast.init_floor(n), inf),
                          SolveK.fold_results(
                            SolveK.par_chunks(dc, P.left_of(seg), off, 1n+p, G,
                              SolveFast.glist_of_guesses(G, 0, 1),
                              SolveFast.build_cwords(cs, G, 0,
                                U32.from_nat(Groups.len_words(G))),
                              cs, n, nd, SolveFast.init_floor(n), inf), acc))),
                        Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, cs, inf,
                          P.right_of(seg),
                          SolveK.fold_results(
                            SolveK.par_chunks(dc, P.left_of(seg), off, 1n+p, G,
                              SolveFast.glist_of_guesses(G, 0, 1),
                              SolveFast.build_cwords(cs, G, 0,
                                U32.from_nat(Groups.len_words(G))),
                              cs, n, nd, SolveFast.init_floor(n), inf), acc))))
                        == True{} : Bool} =
                P.par_cost(dc, P.right_of(seg), off2, p, G, cs, nd, inf,
                  List.append(&2, +List<Nat>, pre, P.left_of(seg)), post,
                  SolveK.fold_results(
                    SolveK.par_chunks(dc, P.left_of(seg), off, 1n+p, G,
                      SolveFast.glist_of_guesses(G, 0, 1),
                      SolveFast.build_cwords(cs, G, 0,
                        U32.from_nat(Groups.len_words(G))),
                      cs, n, nd, SolveFast.init_floor(n), inf), acc),
                  en, eGr, eoff2, hz, h1, h3, h6, ai, hnd, hacc2)
              +emon : {Nat.is_le(
                         Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, cs, inf,
                           P.right_of(seg),
                           SolveK.fold_results(
                             SolveK.par_chunks(dc, P.left_of(seg), off, 1n+p, G,
                               SolveFast.glist_of_guesses(G, 0, 1),
                               SolveFast.build_cwords(cs, G, 0,
                                 U32.from_nat(Groups.len_words(G))),
                               cs, n, nd, SolveFast.init_floor(n), inf), acc))),
                         Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, cs, inf,
                           P.right_of(seg),
                           Eval.Eval.guesses(1n+p, G, cs, inf, P.left_of(seg),
                             acc))))
                       == True{} : Bool} =
                FVal.FV.eval_guesses_mono(p, G, cs, inf, P.right_of(seg),
                  SolveK.fold_results(
                    SolveK.par_chunks(dc, P.left_of(seg), off, 1n+p, G,
                      SolveFast.glist_of_guesses(G, 0, 1),
                      SolveFast.build_cwords(cs, G, 0,
                        U32.from_nat(Groups.len_words(G))),
                      cs, n, nd, SolveFast.init_floor(n), inf), acc),
                  Eval.Eval.guesses(1n+p, G, cs, inf, P.left_of(seg), acc), ihl)
              +eapp : {Eval.Eval.guesses(1n+p, G, cs, inf,
                         List.append(&2, +List<Nat>, P.left_of(seg),
                           P.right_of(seg)), acc)
                       == Eval.Eval.guesses(1n+p, G, cs, inf, P.right_of(seg),
                            Eval.Eval.guesses(1n+p, G, cs, inf,
                              P.left_of(seg), acc))
                       : SolveRef.Best} =
                P.guesses_append(p, G, cs, inf, P.left_of(seg),
                  P.right_of(seg), acc)
              +eapp2 : {Eval.Eval.guesses(1n+p, G, cs, inf, seg, acc)
                        == Eval.Eval.guesses(1n+p, G, cs, inf, P.right_of(seg),
                             Eval.Eval.guesses(1n+p, G, cs, inf,
                               P.left_of(seg), acc))
                        : SolveRef.Best} =
                Equal.trans(SolveRef.Best,
                  Eval.Eval.guesses(1n+p, G, cs, inf, seg, acc),
                  Eval.Eval.guesses(1n+p, G, cs, inf,
                    List.append(&2, +List<Nat>, P.left_of(seg),
                      P.right_of(seg)), acc),
                  Eval.Eval.guesses(1n+p, G, cs, inf, P.right_of(seg),
                    Eval.Eval.guesses(1n+p, G, cs, inf, P.left_of(seg), acc)),
                  Equal.cong(+List<+List<Nat>>, SolveRef.Best,
                    l => Eval.Eval.guesses(1n+p, G, cs, inf, l, acc),
                    seg,
                    List.append(&2, +List<Nat>, P.left_of(seg),
                      P.right_of(seg)),
                    Equal.sym(+List<+List<Nat>>,
                      List.append(&2, +List<Nat>, P.left_of(seg),
                        P.right_of(seg)), seg, P.split_back(seg))),
                  eapp)
              +hmain2 : {Nat.is_le(
                           Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, cs,
                             inf, P.right_of(seg),
                             SolveK.fold_results(
                               SolveK.par_chunks(dc, P.left_of(seg), off, 1n+p,
                                 G, SolveFast.glist_of_guesses(G, 0, 1),
                                 SolveFast.build_cwords(cs, G, 0,
                                   U32.from_nat(Groups.len_words(G))),
                                 cs, n, nd, SolveFast.init_floor(n), inf),
                               acc))),
                           Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, cs,
                             inf, seg, acc))) == True{} : Bool} =
                Fold.OQ.le_cong_r(
                  Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, cs, inf,
                    P.right_of(seg),
                    SolveK.fold_results(
                      SolveK.par_chunks(dc, P.left_of(seg), off, 1n+p, G,
                        SolveFast.glist_of_guesses(G, 0, 1),
                        SolveFast.build_cwords(cs, G, 0,
                          U32.from_nat(Groups.len_words(G))),
                        cs, n, nd, SolveFast.init_floor(n), inf), acc))),
                  Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, cs, inf,
                    P.right_of(seg),
                    Eval.Eval.guesses(1n+p, G, cs, inf, P.left_of(seg), acc))),
                  Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, cs, inf, seg,
                    acc)),
                  Equal.cong(SolveRef.Best, Nat, Eval.Eval.cost_of,
                    Eval.Eval.guesses(1n+p, G, cs, inf, P.right_of(seg),
                      Eval.Eval.guesses(1n+p, G, cs, inf, P.left_of(seg),
                        acc)),
                    Eval.Eval.guesses(1n+p, G, cs, inf, seg, acc),
                    Equal.sym(SolveRef.Best,
                      Eval.Eval.guesses(1n+p, G, cs, inf, seg, acc),
                      Eval.Eval.guesses(1n+p, G, cs, inf, P.right_of(seg),
                        Eval.Eval.guesses(1n+p, G, cs, inf, P.left_of(seg),
                          acc)), eapp2)),
                  emon)
              +hmain : {Nat.is_le(
                          Eval.Eval.cost_of(SolveK.fold_results(
                            SolveK.par_chunks(dc, P.right_of(seg), off2, 1n+p,
                              G, SolveFast.glist_of_guesses(G, 0, 1),
                              SolveFast.build_cwords(cs, G, 0,
                                U32.from_nat(Groups.len_words(G))),
                              cs, n, nd, SolveFast.init_floor(n), inf),
                            SolveK.fold_results(
                              SolveK.par_chunks(dc, P.left_of(seg), off, 1n+p,
                                G, SolveFast.glist_of_guesses(G, 0, 1),
                                SolveFast.build_cwords(cs, G, 0,
                                  U32.from_nat(Groups.len_words(G))),
                                cs, n, nd, SolveFast.init_floor(n), inf), acc))),
                          Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, cs,
                            inf, seg, acc))) == True{} : Bool} =
                NatProof.Nat.is_le_trans(
                  Eval.Eval.cost_of(SolveK.fold_results(
                    SolveK.par_chunks(dc, P.right_of(seg), off2, 1n+p, G,
                      SolveFast.glist_of_guesses(G, 0, 1),
                      SolveFast.build_cwords(cs, G, 0,
                        U32.from_nat(Groups.len_words(G))),
                      cs, n, nd, SolveFast.init_floor(n), inf),
                    SolveK.fold_results(
                      SolveK.par_chunks(dc, P.left_of(seg), off, 1n+p, G,
                        SolveFast.glist_of_guesses(G, 0, 1),
                        SolveFast.build_cwords(cs, G, 0,
                          U32.from_nat(Groups.len_words(G))),
                        cs, n, nd, SolveFast.init_floor(n), inf), acc))),
                  Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, cs, inf,
                    P.right_of(seg),
                    SolveK.fold_results(
                      SolveK.par_chunks(dc, P.left_of(seg), off, 1n+p, G,
                        SolveFast.glist_of_guesses(G, 0, 1),
                        SolveFast.build_cwords(cs, G, 0,
                          U32.from_nat(Groups.len_words(G))),
                        cs, n, nd, SolveFast.init_floor(n), inf), acc))),
                  Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, cs, inf, seg,
                    acc)),
                  ihr, hmain2)
              Fold.OQ.le_cong_l(
                Eval.Eval.cost_of(SolveK.fold_results(
                  List.append(&2, SolveRef.Best,
                    SolveK.par_chunks(dc, P.left_of(seg), off, 1n+p, G,
                      SolveFast.glist_of_guesses(G, 0, 1),
                      SolveFast.build_cwords(cs, G, 0,
                        U32.from_nat(Groups.len_words(G))),
                      cs, n, nd, SolveFast.init_floor(n), inf),
                    SolveK.par_chunks(dc, P.right_of(seg), off2, 1n+p, G,
                      SolveFast.glist_of_guesses(G, 0, 1),
                      SolveFast.build_cwords(cs, G, 0,
                        U32.from_nat(Groups.len_words(G))),
                      cs, n, nd, SolveFast.init_floor(n), inf)), acc)),
                Eval.Eval.cost_of(SolveK.fold_results(
                  SolveK.par_chunks(dc, P.right_of(seg), off2, 1n+p, G,
                    SolveFast.glist_of_guesses(G, 0, 1),
                    SolveFast.build_cwords(cs, G, 0,
                      U32.from_nat(Groups.len_words(G))),
                    cs, n, nd, SolveFast.init_floor(n), inf),
                  SolveK.fold_results(
                    SolveK.par_chunks(dc, P.left_of(seg), off, 1n+p, G,
                      SolveFast.glist_of_guesses(G, 0, 1),
                      SolveFast.build_cwords(cs, G, 0,
                        U32.from_nat(Groups.len_words(G))),
                      cs, n, nd, SolveFast.init_floor(n), inf), acc))),
                Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, cs, inf, seg,
                  acc)),
                Equal.cong(SolveRef.Best, Nat, Eval.Eval.cost_of,
                  SolveK.fold_results(
                    List.append(&2, SolveRef.Best,
                      SolveK.par_chunks(dc, P.left_of(seg), off, 1n+p, G,
                        SolveFast.glist_of_guesses(G, 0, 1),
                        SolveFast.build_cwords(cs, G, 0,
                          U32.from_nat(Groups.len_words(G))),
                        cs, n, nd, SolveFast.init_floor(n), inf),
                      SolveK.par_chunks(dc, P.right_of(seg), off2, 1n+p, G,
                        SolveFast.glist_of_guesses(G, 0, 1),
                        SolveFast.build_cwords(cs, G, 0,
                          U32.from_nat(Groups.len_words(G))),
                        cs, n, nd, SolveFast.init_floor(n), inf)), acc),
                  SolveK.fold_results(
                    SolveK.par_chunks(dc, P.right_of(seg), off2, 1n+p, G,
                      SolveFast.glist_of_guesses(G, 0, 1),
                      SolveFast.build_cwords(cs, G, 0,
                        U32.from_nat(Groups.len_words(G))),
                      cs, n, nd, SolveFast.init_floor(n), inf),
                    SolveK.fold_results(
                      SolveK.par_chunks(dc, P.left_of(seg), off, 1n+p, G,
                        SolveFast.glist_of_guesses(G, 0, 1),
                        SolveFast.build_cwords(cs, G, 0,
                          U32.from_nat(Groups.len_words(G))),
                        cs, n, nd, SolveFast.init_floor(n), inf), acc)),
                  P.fold_append(
                    SolveK.par_chunks(dc, P.left_of(seg), off, 1n+p, G,
                      SolveFast.glist_of_guesses(G, 0, 1),
                      SolveFast.build_cwords(cs, G, 0,
                        U32.from_nat(Groups.len_words(G))),
                      cs, n, nd, SolveFast.init_floor(n), inf),
                    SolveK.par_chunks(dc, P.right_of(seg), off2, 1n+p, G,
                      SolveFast.glist_of_guesses(G, 0, 1),
                      SolveFast.build_cwords(cs, G, 0,
                        U32.from_nat(Groups.len_words(G))),
                      cs, n, nd, SolveFast.init_floor(n), inf), acc)),
                hmain)

# Every result `par_chunks` returns is valid at the cutoff and costs at most
# the cutoff.
def P.par_ok(+d: Nat, +seg: +List<+List<Nat>>, +off: U32, +p: Nat,
    +G: +List<+List<Nat>>, +cs: +List<+List<Nat>>, +nd: Bool, +inf: Nat,
    +pre: +List<+List<Nat>>, +post: +List<+List<Nat>>,
    +en: {Groups.len_words(cs) == 1n+p : Nat},
    +eG : {G == List.append(&2, +List<Nat>,
             List.append(&2, +List<Nat>, pre, seg), post)
           : +List<+List<Nat>>},
    +eoff: {U32.from_nat(Groups.len_words(pre)) == off : U32},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +h3: {Nat.is_lt(3n, inf) == True{} : Bool},
    +h6: {Nat.is_lt(6n, inf) == True{} : Bool},
    +ai: {FO.FO.all_in_ref(cs, G) == True{} : Bool},
    +hnd: {FN.FN.nodup_ok(nd, cs) == True{} : Bool}) ->
  {P.ok_list(inf, G, cs,
     SolveK.par_chunks(d, seg, off, 1n+p, G,
       SolveFast.glist_of_guesses(G, 0, 1),
       SolveFast.build_cwords(cs, G, 0, U32.from_nat(Groups.len_words(G))),
       cs, Groups.len_words(cs), nd,
       SolveFast.init_floor(Groups.len_words(cs)), inf))
   == True{} : Bool}:
  match d:
    case 0n:
      +n : Nat = Groups.len_words(cs)
      +ele : {Nat.is_le(n, 1n+p) == True{} : Bool} =
        Fold.OQ.le_cong_l(n, 1n+p, 1n+p, en,
          NatProof.Nat.is_le_refl(1n+p))
      +hs : {P.job_res_gs_b(1n+p, inf, G, seg, cs, inf,
               SolveK.chunk_best(1n+p, seg, off, G,
                 SolveFast.glist_of_guesses(G, 0, 1),
                 SolveFast.build_cwords(cs, G, 0,
                   U32.from_nat(Groups.len_words(G))),
                 cs, n, nd, SolveFast.init_floor(n), inf,
                 SolveFast.mk_buf_tbl(nd, G, cs, n)))
             == True{} : Bool} =
        P.chunk_best_leaf(p, inf, G, cs, nd, pre, seg, post, off, eG, eoff,
          ele, hz, h1, h3, h6, ai, hnd)
      FO.FO.bool_and_intro(
        P.elt_ok(inf, G, cs,
          SolveK.chunk_best(1n+p, seg, off, G,
            SolveFast.glist_of_guesses(G, 0, 1),
            SolveFast.build_cwords(cs, G, 0, U32.from_nat(Groups.len_words(G))),
            cs, n, nd, SolveFast.init_floor(n), inf,
            SolveFast.mk_buf_tbl(nd, G, cs, n))),
        True{},
        FO.FO.bool_and_intro(
          FVal.FV.best_ok_b(inf, G, cs,
            SolveK.chunk_best(1n+p, seg, off, G,
              SolveFast.glist_of_guesses(G, 0, 1),
              SolveFast.build_cwords(cs, G, 0,
                U32.from_nat(Groups.len_words(G))),
              cs, n, nd, SolveFast.init_floor(n), inf,
              SolveFast.mk_buf_tbl(nd, G, cs, n))),
          Nat.is_le(Eval.Eval.cost_of(
            SolveK.chunk_best(1n+p, seg, off, G,
              SolveFast.glist_of_guesses(G, 0, 1),
              SolveFast.build_cwords(cs, G, 0,
                U32.from_nat(Groups.len_words(G))),
              cs, n, nd, SolveFast.init_floor(n), inf,
              SolveFast.mk_buf_tbl(nd, G, cs, n))), inf),
          Logic.Proof.and_true_l(FVal.FV.best_ok_b(inf, G, cs,
              SolveK.chunk_best(1n+p, seg, off, G,
                SolveFast.glist_of_guesses(G, 0, 1),
                SolveFast.build_cwords(cs, G, 0,
                  U32.from_nat(Groups.len_words(G))),
                cs, n, nd, SolveFast.init_floor(n), inf,
                SolveFast.mk_buf_tbl(nd, G, cs, n))),
            Bool.and(Nat.is_le(Eval.Eval.cost_of(
                SolveK.chunk_best(1n+p, seg, off, G,
                  SolveFast.glist_of_guesses(G, 0, 1),
                  SolveFast.build_cwords(cs, G, 0,
                    U32.from_nat(Groups.len_words(G))),
                  cs, n, nd, SolveFast.init_floor(n), inf,
                  SolveFast.mk_buf_tbl(nd, G, cs, n))), inf),
              Nat.is_le(Eval.Eval.cost_of(
                  SolveK.chunk_best(1n+p, seg, off, G,
                    SolveFast.glist_of_guesses(G, 0, 1),
                    SolveFast.build_cwords(cs, G, 0,
                      U32.from_nat(Groups.len_words(G))),
                    cs, n, nd, SolveFast.init_floor(n), inf,
                    SolveFast.mk_buf_tbl(nd, G, cs, n))),
                Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, cs, inf, seg,
                  Eval.Eval.dummy_inf(inf))))),
            hs),
          Logic.Proof.and_true_l(Nat.is_le(Eval.Eval.cost_of(
              SolveK.chunk_best(1n+p, seg, off, G,
                SolveFast.glist_of_guesses(G, 0, 1),
                SolveFast.build_cwords(cs, G, 0,
                  U32.from_nat(Groups.len_words(G))),
                cs, n, nd, SolveFast.init_floor(n), inf,
                SolveFast.mk_buf_tbl(nd, G, cs, n))), inf),
            Nat.is_le(Eval.Eval.cost_of(
                SolveK.chunk_best(1n+p, seg, off, G,
                  SolveFast.glist_of_guesses(G, 0, 1),
                  SolveFast.build_cwords(cs, G, 0,
                    U32.from_nat(Groups.len_words(G))),
                  cs, n, nd, SolveFast.init_floor(n), inf,
                  SolveFast.mk_buf_tbl(nd, G, cs, n))),
              Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, cs, inf, seg,
                Eval.Eval.dummy_inf(inf)))),
            Logic.Proof.and_true_r(FVal.FV.best_ok_b(inf, G, cs,
                SolveK.chunk_best(1n+p, seg, off, G,
                  SolveFast.glist_of_guesses(G, 0, 1),
                  SolveFast.build_cwords(cs, G, 0,
                    U32.from_nat(Groups.len_words(G))),
                  cs, n, nd, SolveFast.init_floor(n), inf,
                  SolveFast.mk_buf_tbl(nd, G, cs, n))),
              Bool.and(Nat.is_le(Eval.Eval.cost_of(
                  SolveK.chunk_best(1n+p, seg, off, G,
                    SolveFast.glist_of_guesses(G, 0, 1),
                    SolveFast.build_cwords(cs, G, 0,
                      U32.from_nat(Groups.len_words(G))),
                    cs, n, nd, SolveFast.init_floor(n), inf,
                    SolveFast.mk_buf_tbl(nd, G, cs, n))), inf),
                Nat.is_le(Eval.Eval.cost_of(
                    SolveK.chunk_best(1n+p, seg, off, G,
                      SolveFast.glist_of_guesses(G, 0, 1),
                      SolveFast.build_cwords(cs, G, 0,
                        U32.from_nat(Groups.len_words(G))),
                      cs, n, nd, SolveFast.init_floor(n), inf,
                      SolveFast.mk_buf_tbl(nd, G, cs, n))),
                  Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, cs, inf, seg,
                    Eval.Eval.dummy_inf(inf))))),
              hs))),
        {==})
    case 1n+dc:
      match seg:
        case Nil{}:
          {==}
        case Con{w, rest}:
          match rest:
            case Nil{}:
              +n : Nat = Groups.len_words(cs)
              +ele : {Nat.is_le(n, 1n+p) == True{} : Bool} =
                Fold.OQ.le_cong_l(n, 1n+p, 1n+p, en,
                  NatProof.Nat.is_le_refl(1n+p))
              +hs : {P.job_res_gs_b(1n+p, inf, G, seg, cs, inf,
                       SolveK.chunk_best(1n+p, seg, off, G,
                         SolveFast.glist_of_guesses(G, 0, 1),
                         SolveFast.build_cwords(cs, G, 0,
                           U32.from_nat(Groups.len_words(G))),
                         cs, n, nd, SolveFast.init_floor(n), inf,
                         SolveFast.mk_buf_tbl(nd, G, cs, n)))
                     == True{} : Bool} =
                P.chunk_best_leaf(p, inf, G, cs, nd, pre, seg, post, off, eG,
                  eoff, ele, hz, h1, h3, h6, ai, hnd)
              FO.FO.bool_and_intro(
                P.elt_ok(inf, G, cs,
                  SolveK.chunk_best(1n+p, seg, off, G,
                    SolveFast.glist_of_guesses(G, 0, 1),
                    SolveFast.build_cwords(cs, G, 0,
                      U32.from_nat(Groups.len_words(G))),
                    cs, n, nd, SolveFast.init_floor(n), inf,
                    SolveFast.mk_buf_tbl(nd, G, cs, n))),
                True{},
                FO.FO.bool_and_intro(
                  FVal.FV.best_ok_b(inf, G, cs,
                    SolveK.chunk_best(1n+p, seg, off, G,
                      SolveFast.glist_of_guesses(G, 0, 1),
                      SolveFast.build_cwords(cs, G, 0,
                        U32.from_nat(Groups.len_words(G))),
                      cs, n, nd, SolveFast.init_floor(n), inf,
                      SolveFast.mk_buf_tbl(nd, G, cs, n))),
                  Nat.is_le(Eval.Eval.cost_of(
                    SolveK.chunk_best(1n+p, seg, off, G,
                      SolveFast.glist_of_guesses(G, 0, 1),
                      SolveFast.build_cwords(cs, G, 0,
                        U32.from_nat(Groups.len_words(G))),
                      cs, n, nd, SolveFast.init_floor(n), inf,
                      SolveFast.mk_buf_tbl(nd, G, cs, n))), inf),
                  Logic.Proof.and_true_l(FVal.FV.best_ok_b(inf, G, cs,
                      SolveK.chunk_best(1n+p, seg, off, G,
                        SolveFast.glist_of_guesses(G, 0, 1),
                        SolveFast.build_cwords(cs, G, 0,
                          U32.from_nat(Groups.len_words(G))),
                        cs, n, nd, SolveFast.init_floor(n), inf,
                        SolveFast.mk_buf_tbl(nd, G, cs, n))),
                    Bool.and(Nat.is_le(Eval.Eval.cost_of(
                        SolveK.chunk_best(1n+p, seg, off, G,
                          SolveFast.glist_of_guesses(G, 0, 1),
                          SolveFast.build_cwords(cs, G, 0,
                            U32.from_nat(Groups.len_words(G))),
                          cs, n, nd, SolveFast.init_floor(n), inf,
                          SolveFast.mk_buf_tbl(nd, G, cs, n))), inf),
                      Nat.is_le(Eval.Eval.cost_of(
                          SolveK.chunk_best(1n+p, seg, off, G,
                            SolveFast.glist_of_guesses(G, 0, 1),
                            SolveFast.build_cwords(cs, G, 0,
                              U32.from_nat(Groups.len_words(G))),
                            cs, n, nd, SolveFast.init_floor(n), inf,
                            SolveFast.mk_buf_tbl(nd, G, cs, n))),
                        Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, cs, inf,
                          seg, Eval.Eval.dummy_inf(inf))))),
                    hs),
                  Logic.Proof.and_true_l(Nat.is_le(Eval.Eval.cost_of(
                      SolveK.chunk_best(1n+p, seg, off, G,
                        SolveFast.glist_of_guesses(G, 0, 1),
                        SolveFast.build_cwords(cs, G, 0,
                          U32.from_nat(Groups.len_words(G))),
                        cs, n, nd, SolveFast.init_floor(n), inf,
                        SolveFast.mk_buf_tbl(nd, G, cs, n))), inf),
                    Nat.is_le(Eval.Eval.cost_of(
                        SolveK.chunk_best(1n+p, seg, off, G,
                          SolveFast.glist_of_guesses(G, 0, 1),
                          SolveFast.build_cwords(cs, G, 0,
                            U32.from_nat(Groups.len_words(G))),
                          cs, n, nd, SolveFast.init_floor(n), inf,
                          SolveFast.mk_buf_tbl(nd, G, cs, n))),
                      Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, cs, inf,
                        seg, Eval.Eval.dummy_inf(inf)))),
                    Logic.Proof.and_true_r(FVal.FV.best_ok_b(inf, G, cs,
                        SolveK.chunk_best(1n+p, seg, off, G,
                          SolveFast.glist_of_guesses(G, 0, 1),
                          SolveFast.build_cwords(cs, G, 0,
                            U32.from_nat(Groups.len_words(G))),
                          cs, n, nd, SolveFast.init_floor(n), inf,
                          SolveFast.mk_buf_tbl(nd, G, cs, n))),
                      Bool.and(Nat.is_le(Eval.Eval.cost_of(
                          SolveK.chunk_best(1n+p, seg, off, G,
                            SolveFast.glist_of_guesses(G, 0, 1),
                            SolveFast.build_cwords(cs, G, 0,
                              U32.from_nat(Groups.len_words(G))),
                            cs, n, nd, SolveFast.init_floor(n), inf,
                            SolveFast.mk_buf_tbl(nd, G, cs, n))), inf),
                        Nat.is_le(Eval.Eval.cost_of(
                            SolveK.chunk_best(1n+p, seg, off, G,
                              SolveFast.glist_of_guesses(G, 0, 1),
                              SolveFast.build_cwords(cs, G, 0,
                                U32.from_nat(Groups.len_words(G))),
                              cs, n, nd, SolveFast.init_floor(n), inf,
                              SolveFast.mk_buf_tbl(nd, G, cs, n))),
                          Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, cs,
                            inf, seg, Eval.Eval.dummy_inf(inf))))),
                      hs))),
                {==})
            case Con{w2, rest2}:
              +n : Nat = Groups.len_words(cs)
              +ele : {Nat.is_le(n, 1n+p) == True{} : Bool} =
                Fold.OQ.le_cong_l(n, 1n+p, 1n+p, en,
                  NatProof.Nat.is_le_refl(1n+p))
              +okl : {P.ok_list(inf, G, cs,
                        SolveK.par_chunks(dc, P.left_of(seg), off, 1n+p, G,
                          SolveFast.glist_of_guesses(G, 0, 1),
                          SolveFast.build_cwords(cs, G, 0,
                            U32.from_nat(Groups.len_words(G))),
                          cs, n, nd, SolveFast.init_floor(n), inf))
                      == True{} : Bool} =
                P.par_ok(dc, P.left_of(seg), off, p, G, cs, nd, inf, pre,
                  List.append(&2, +List<Nat>, P.right_of(seg), post), en,
                  P.eG_left(pre, seg, post, G, eG), eoff, hz, h1, h3, h6, ai,
                  hnd)
              +okr : {P.ok_list(inf, G, cs,
                        SolveK.par_chunks(dc, P.right_of(seg),
                          P.off_next(off, seg), 1n+p, G,
                          SolveFast.glist_of_guesses(G, 0, 1),
                          SolveFast.build_cwords(cs, G, 0,
                            U32.from_nat(Groups.len_words(G))),
                          cs, n, nd, SolveFast.init_floor(n), inf))
                      == True{} : Bool} =
                P.par_ok(dc, P.right_of(seg), P.off_next(off, seg), p, G, cs,
                  nd, inf,
                  List.append(&2, +List<Nat>, pre, P.left_of(seg)), post, en,
                  P.eG_right(pre, seg, post, G, eG),
                  P.eoff_right(pre, seg, off, eoff), hz, h1, h3, h6, ai, hnd)
              P.ok_list_append(inf, G, cs,
                SolveK.par_chunks(dc, P.left_of(seg), off, 1n+p, G,
                  SolveFast.glist_of_guesses(G, 0, 1),
                  SolveFast.build_cwords(cs, G, 0,
                    U32.from_nat(Groups.len_words(G))),
                  cs, n, nd, SolveFast.init_floor(n), inf),
                SolveK.par_chunks(dc, P.right_of(seg),
                  P.off_next(off, seg), 1n+p, G,
                  SolveFast.glist_of_guesses(G, 0, 1),
                  SolveFast.build_cwords(cs, G, 0,
                    U32.from_nat(Groups.len_words(G))),
                  cs, n, nd, SolveFast.init_floor(n), inf),
                okl, okr)

# ---------------------------------------------------------------------------
# The chunked root entry point
# ---------------------------------------------------------------------------

# The chunk result list of `solve_chunked`, as a transparent definition.
def P.root_rs(+G: +List<+List<Nat>>, +cs: +List<+List<Nat>>, +d: Nat) ->
    +List<SolveRef.Best>:
  SolveK.par_chunks(d, G, 0, Groups.len_words(cs), G,
    SolveFast.glist_of_guesses(G, 0, 1),
    SolveFast.build_cwords(cs, G, 0, U32.from_nat(Groups.len_words(G))),
    cs, Groups.len_words(cs), SolveFast.no_dup_fast(cs),
    SolveFast.init_floor(Groups.len_words(cs)),
    SolveRef.inf_of(Groups.len_words(cs)))

# The folded root result of `solve_chunked`.
def P.root_best(+G: +List<+List<Nat>>, +cs: +List<+List<Nat>>, +d: Nat) ->
    SolveRef.Best:
  SolveK.fold_results(P.root_rs(G, cs, d),
    SolveFast.dummy_inf(SolveRef.inf_of(Groups.len_words(cs))))

# The infinity bound the chunked root needs: at least three candidates put
# `6` below `inf_of n`.
def P.inf_gt6(+cs: +List<+List<Nat>>, +h3_le_n:
    {Nat.is_le(3n, Groups.len_words(cs)) == True{} : Bool}) ->
  {Nat.is_lt(6n, SolveRef.inf_of(Groups.len_words(cs))) == True{} : Bool}:
  +n : Nat = Groups.len_words(cs)
  +h9_le_sq : {Nat.is_le(9n, Nat.mul(n, n)) == True{} : Bool} =
    NatProof.Nat.is_le_trans(9n, Nat.mul(3n, n), Nat.mul(n, n),
      CBN.CB.is_le_mul_r(3n, n, 3n, h3_le_n),
      CBN.CB.is_le_mul_l(3n, n, n, h3_le_n))
  NatProof.Nat.is_le_lt_trans(6n, Nat.mul(n, n), SolveRef.inf_of(n),
    NatProof.Nat.is_le_trans(6n, 9n, Nat.mul(n, n), {==}, h9_le_sq),
    CBN.CB.lt_add_one(Nat.mul(n, n)))

def P.inf_gt3(+cs: +List<+List<Nat>>, +h3_le_n:
    {Nat.is_le(3n, Groups.len_words(cs)) == True{} : Bool}) ->
  {Nat.is_lt(3n, SolveRef.inf_of(Groups.len_words(cs))) == True{} : Bool}:
  NatProof.Nat.is_le_lt_trans(3n, 6n, SolveRef.inf_of(Groups.len_words(cs)),
    {==}, P.inf_gt6(cs, h3_le_n))

def P.inf_gt1(+cs: +List<+List<Nat>>, +h3_le_n:
    {Nat.is_le(3n, Groups.len_words(cs)) == True{} : Bool}) ->
  {Nat.is_lt(1n, SolveRef.inf_of(Groups.len_words(cs))) == True{} : Bool}:
  NatProof.Nat.is_le_lt_trans(1n, 6n, SolveRef.inf_of(Groups.len_words(cs)),
    {==}, P.inf_gt6(cs, h3_le_n))

def P.inf_gt0(+cs: +List<+List<Nat>>, +h3_le_n:
    {Nat.is_le(3n, Groups.len_words(cs)) == True{} : Bool}) ->
  {Nat.is_lt(0n, SolveRef.inf_of(Groups.len_words(cs))) == True{} : Bool}:
  NatProof.Nat.is_le_lt_trans(0n, 6n, SolveRef.inf_of(Groups.len_words(cs)),
    {==}, P.inf_gt6(cs, h3_le_n))

def P.nodup_cs(+cs: +List<+List<Nat>>) ->
  {FN.FN.nodup_ok(SolveFast.no_dup_fast(cs), cs) == True{} : Bool}:
  FOpt.FOpt.nodup_ok_of_fast(cs)

# The same result list with the fuel written as the positive successor the
# chunk lemmas are stated at.
def P.par_rs_p(+G: +List<+List<Nat>>, +cs: +List<+List<Nat>>, +p: Nat,
    +d: Nat) -> +List<SolveRef.Best>:
  SolveK.par_chunks(d, G, 0, 1n+p, G,
    SolveFast.glist_of_guesses(G, 0, 1),
    SolveFast.build_cwords(cs, G, 0, U32.from_nat(Groups.len_words(G))),
    cs, Groups.len_words(cs), SolveFast.no_dup_fast(cs),
    SolveFast.init_floor(Groups.len_words(cs)),
    SolveRef.inf_of(Groups.len_words(cs)))

def P.par_rs_eq(+G: +List<+List<Nat>>, +cs: +List<+List<Nat>>, +p: Nat,
    +d: Nat, +en: {Groups.len_words(cs) == 1n+p : Nat}) ->
  {P.par_rs_p(G, cs, p, d) == P.root_rs(G, cs, d) : +List<SolveRef.Best>}:
  Equal.cong(Nat, +List<SolveRef.Best>,
    f => SolveK.par_chunks(d, G, 0, f, G,
      SolveFast.glist_of_guesses(G, 0, 1),
      SolveFast.build_cwords(cs, G, 0, U32.from_nat(Groups.len_words(G))),
      cs, Groups.len_words(cs), SolveFast.no_dup_fast(cs),
      SolveFast.init_floor(Groups.len_words(cs)),
      SolveRef.inf_of(Groups.len_words(cs))),
    1n+p, Groups.len_words(cs), Equal.sym(Nat, Groups.len_words(cs), 1n+p, en))

def P.ok_list_transport(+limit: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, -rs1: +List<SolveRef.Best>,
    -rs2: +List<SolveRef.Best>,
    +e: {rs1 == rs2 : +List<SolveRef.Best>},
    +h: {P.ok_list(limit, G, S, rs1) == True{} : Bool}) ->
  {P.ok_list(limit, G, S, rs2) == True{} : Bool}:
  %e : {P.ok_list(limit, G, S, _) == True{} : Bool}
  h

def P.eG_nil(+G: +List<+List<Nat>>) ->
  {G == List.append(&2, +List<Nat>,
         List.append(&2, +List<Nat>, Nil{}, G), Nil{})
   : +List<+List<Nat>>}:
  Equal.sym(+List<+List<Nat>>, List.append(&2, +List<Nat>, G, Nil{}), G,
    FN.FN.list_append_nil(G))

# The folded chunk result is valid.
def P.root_ok(+G: +List<+List<Nat>>, +cs: +List<+List<Nat>>, +p: Nat,
    +d: Nat, +en: {Groups.len_words(cs) == 1n+p : Nat},
    +h3n : {Nat.is_le(3n, Groups.len_words(cs)) == True{} : Bool},
    +ai: {FO.FO.all_in_ref(cs, G) == True{} : Bool}) ->
  {FVal.FV.best_ok_b(SolveRef.inf_of(Groups.len_words(cs)), G, cs,
     P.root_best(G, cs, d)) == True{} : Bool}:
  +n : Nat = Groups.len_words(cs)
  +inf : Nat = SolveRef.inf_of(n)
  +nd : Bool = SolveFast.no_dup_fast(cs)
  +hz = P.inf_gt0(cs, h3n)
  +h1 = P.inf_gt1(cs, h3n)
  +h3 = P.inf_gt3(cs, h3n)
  +h6 = P.inf_gt6(cs, h3n)
  +hnd = P.nodup_cs(cs)
  +hokl_p = P.par_ok(d, G, 0, p, G, cs, nd, inf, Nil{}, Nil{}, en,
              P.eG_nil(G), {==}, hz, h1, h3, h6, ai, hnd)
  +hokl = P.ok_list_transport(inf, G, cs, P.par_rs_p(G, cs, p, d),
            P.root_rs(G, cs, d), P.par_rs_eq(G, cs, p, d, en), hokl_p)
  +helt = P.elt_ok_dummy_inf(inf, G, cs, Nat.ge_refl(inf))
  +hf = P.ok_list_fold(inf, G, cs, P.root_rs(G, cs, d),
          SolveFast.dummy_inf(inf), hokl, helt)
  Logic.Proof.and_true_l(
    FVal.FV.best_ok_b(inf, G, cs, P.root_best(G, cs, d)),
    Nat.is_le(Eval.Eval.cost_of(P.root_best(G, cs, d)), inf), hf)

# The folded chunk result costs at most the reference fold over the root guess
# list.
def P.root_cost(+G: +List<+List<Nat>>, +cs: +List<+List<Nat>>, +p: Nat,
    +d: Nat, +en: {Groups.len_words(cs) == 1n+p : Nat},
    +h3n : {Nat.is_le(3n, Groups.len_words(cs)) == True{} : Bool},
    +ai: {FO.FO.all_in_ref(cs, G) == True{} : Bool}) ->
  {Nat.is_le(Eval.Eval.cost_of(P.root_best(G, cs, d)),
     Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, cs,
       SolveRef.inf_of(Groups.len_words(cs)), G,
       Eval.Eval.dummy_inf(SolveRef.inf_of(Groups.len_words(cs))))))
   == True{} : Bool}:
  +n : Nat = Groups.len_words(cs)
  +inf : Nat = SolveRef.inf_of(n)
  +nd : Bool = SolveFast.no_dup_fast(cs)
  +hz = P.inf_gt0(cs, h3n)
  +h1 = P.inf_gt1(cs, h3n)
  +h3 = P.inf_gt3(cs, h3n)
  +h6 = P.inf_gt6(cs, h3n)
  +hnd = P.nodup_cs(cs)
  +hcost_p = P.par_cost(d, G, 0, p, G, cs, nd, inf, Nil{}, Nil{},
                SolveFast.dummy_inf(inf), en, P.eG_nil(G), {==}, hz, h1, h3,
                h6, ai, hnd, NatProof.Nat.is_le_refl(inf))
  +efold : {SolveK.fold_results(P.par_rs_p(G, cs, p, d),
                SolveFast.dummy_inf(inf)) == P.root_best(G, cs, d)
            : SolveRef.Best} =
    Equal.cong(+List<SolveRef.Best>, SolveRef.Best,
      rs => SolveK.fold_results(rs, SolveFast.dummy_inf(inf)),
      P.par_rs_p(G, cs, p, d), P.root_rs(G, cs, d),
      P.par_rs_eq(G, cs, p, d, en))
  Fold.OQ.le_cong_l(
    Eval.Eval.cost_of(P.root_best(G, cs, d)),
    Eval.Eval.cost_of(SolveK.fold_results(P.par_rs_p(G, cs, p, d),
      SolveFast.dummy_inf(inf))),
    Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, cs, inf, G,
      Eval.Eval.dummy_inf(inf))),
    Equal.cong(SolveRef.Best, Nat, Eval.Eval.cost_of,
      P.root_best(G, cs, d),
      SolveK.fold_results(P.par_rs_p(G, cs, p, d),
        SolveFast.dummy_inf(inf)),
      Equal.sym(SolveRef.Best,
        SolveK.fold_results(P.par_rs_p(G, cs, p, d),
          SolveFast.dummy_inf(inf)),
        P.root_best(G, cs, d), efold)),
    hcost_p)

# The reference search over the root guess list at the positive fuel.
def P.ref_p(+G: +List<+List<Nat>>, +cs: +List<+List<Nat>>, +p: Nat) ->
    SolveRef.Best:
  SolveRef.step(1n+p, SolveRef.mk_schedule(G, cs), G, cs,
    SolveRef.inf_of(Groups.len_words(cs)), Nil{}, Nil{}, 0n,
    Eval.Eval.dummy_inf(SolveRef.inf_of(Groups.len_words(cs))),
    Eval.Eval.dummy_zero())

def P.root_le_ref(+G: +List<+List<Nat>>, +cs: +List<+List<Nat>>, +p: Nat,
    +d: Nat, +en: {Groups.len_words(cs) == 1n+p : Nat},
    +h3n : {Nat.is_le(3n, Groups.len_words(cs)) == True{} : Bool},
    +ai: {FO.FO.all_in_ref(cs, G) == True{} : Bool}) ->
  {Nat.is_le(Eval.Eval.cost_of(P.root_best(G, cs, d)),
     Eval.Eval.cost_of(P.ref_p(G, cs, p))) == True{} : Bool}:
  +inf : Nat = SolveRef.inf_of(Groups.len_words(cs))
  +hcost = P.root_cost(G, cs, p, d, en, h3n, ai)
  +egs : {Eval.Eval.guesses(1n+p, G, cs, inf, G,
            Eval.Eval.dummy_inf(inf)) == P.ref_p(G, cs, p)
          : SolveRef.Best} =
    Equal.sym(SolveRef.Best, P.ref_p(G, cs, p),
      Eval.Eval.guesses(1n+p, G, cs, inf, G, Eval.Eval.dummy_inf(inf)),
      Eval.Eval.guesses_step(p, G, cs, inf, G, Eval.Eval.dummy_inf(inf)))
  Fold.OQ.le_cong_r(
    Eval.Eval.cost_of(P.root_best(G, cs, d)),
    Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, cs, inf, G,
      Eval.Eval.dummy_inf(inf))),
    Eval.Eval.cost_of(P.ref_p(G, cs, p)),
    Equal.cong(SolveRef.Best, Nat, Eval.Eval.cost_of,
      Eval.Eval.guesses(1n+p, G, cs, inf, G, Eval.Eval.dummy_inf(inf)),
      P.ref_p(G, cs, p), egs),
    hcost)

# The chunked root is optimal, given the reference comparison and finiteness.
def P.solve_chunked_optimal(+G: +List<+List<Nat>>,
    +cs: +List<+List<Nat>>, +d: Nat, +p: Nat, +T2: Tree.Tree,
    +en: {Groups.len_words(cs) == 1n+p : Nat},
    +h3n : {Nat.is_le(3n, Groups.len_words(cs)) == True{} : Bool},
    +ai: {FO.FO.all_in_ref(cs, G) == True{} : Bool},
    +opt: {Nat.is_le(Eval.Eval.cost_of(P.ref_p(G, cs, p)),
             Tree.cost(T2, cs)) == True{} : Bool},
    +fin: {Nat.is_lt(Eval.Eval.cost_of(P.ref_p(G, cs, p)),
             SolveRef.inf_of(Groups.len_words(cs))) == True{} : Bool}) ->
  Exists(Tree.Tree, T =>
    {SolveK.solve_chunked(G, cs, d) == Some{T} : Maybe<Tree.Tree>}
    & {Nat.is_le(Tree.cost(T, cs), Tree.cost(T2, cs)) == True{} : Bool}):
  +n : Nat = Groups.len_words(cs)
  +inf : Nat = SolveRef.inf_of(n)
  +hok = P.root_ok(G, cs, p, d, en, h3n, ai)
  +hle_ref = P.root_le_ref(G, cs, p, d, en, h3n, ai)
  +fin_fold : {Nat.is_lt(Eval.Eval.cost_of(P.root_best(G, cs, d)), inf)
               == True{} : Bool} =
    NatProof.Nat.is_le_lt_trans(Eval.Eval.cost_of(P.root_best(G, cs, d)),
      Eval.Eval.cost_of(P.ref_p(G, cs, p)), inf, hle_ref, fin)
  +es = OC.OC.best_to_maybe_fin(inf, P.root_best(G, cs, d), fin_fold)
  +hext = FVal.FV.best_ok_extract(inf, G, cs, P.root_best(G, cs, d), hok,
            fin_fold)
  +hcost_tree = Logic.Proof.and_true_r(
                  FVal.FV.valid_b(Eval.Eval.tree_of(P.root_best(G, cs, d)),
                    G, cs),
                  Nat.is_le(Tree.cost(
                      Eval.Eval.tree_of(P.root_best(G, cs, d)), cs),
                    Eval.Eval.cost_of(P.root_best(G, cs, d))), hext)
  +hle = NatProof.Nat.is_le_trans(
           Tree.cost(Eval.Eval.tree_of(P.root_best(G, cs, d)), cs),
           Eval.Eval.cost_of(P.root_best(G, cs, d)), Tree.cost(T2, cs),
           hcost_tree,
           NatProof.Nat.is_le_trans(Eval.Eval.cost_of(P.root_best(G, cs, d)),
             Eval.Eval.cost_of(P.ref_p(G, cs, p)), Tree.cost(T2, cs),
             hle_ref, opt))
  (Eval.Eval.tree_of(P.root_best(G, cs, d)), (es, hle))

# Transporting the accumulator invariant along an equality of results.
def P.best_ok_transport(+limit: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, -r1: SolveRef.Best, -r2: SolveRef.Best,
    +e: {r1 == r2 : SolveRef.Best},
    +h: {FVal.FV.best_ok_b(limit, G, S, r1) == True{} : Bool}) ->
  {FVal.FV.best_ok_b(limit, G, S, r2) == True{} : Bool}:
  %e : {FVal.FV.best_ok_b(limit, G, S, _) == True{} : Bool}
  h

# The chunked root is valid.
def P.solve_chunked_valid(+G: +List<+List<Nat>>, +cs: +List<+List<Nat>>,
    +d: Nat, +p: Nat, +T: Tree.Tree,
    +en: {Groups.len_words(cs) == 1n+p : Nat},
    +h3n : {Nat.is_le(3n, Groups.len_words(cs)) == True{} : Bool},
    +ai: {FO.FO.all_in_ref(cs, G) == True{} : Bool},
    e: {SolveK.solve_chunked(G, cs, d) == Some{T} : Maybe<Tree.Tree>}) ->
  Tree.Valid(T, G, cs):
  +inf : Nat = SolveRef.inf_of(Groups.len_words(cs))
  +hok = P.root_ok(G, cs, p, d, en, h3n, ai)
  +hok_fold : {FVal.FV.best_ok_b(inf, G, cs,
      SolveK.fold_results(
        SolveK.par_chunks(d, G, 0, Groups.len_words(cs), G,
          SolveFast.glist_of_guesses(G, 0, 1),
          SolveFast.build_cwords(cs, G, 0, U32.from_nat(Groups.len_words(G))),
          cs, Groups.len_words(cs), SolveFast.no_dup_fast(cs),
          SolveFast.init_floor(Groups.len_words(cs)),
          SolveRef.inf_of(Groups.len_words(cs))),
        SolveFast.dummy_inf(SolveRef.inf_of(Groups.len_words(cs)))))
    == True{} : Bool} =
    P.best_ok_transport(inf, G, cs, P.root_best(G, cs, d),
      SolveK.fold_results(
        SolveK.par_chunks(d, G, 0, Groups.len_words(cs), G,
          SolveFast.glist_of_guesses(G, 0, 1),
          SolveFast.build_cwords(cs, G, 0, U32.from_nat(Groups.len_words(G))),
          cs, Groups.len_words(cs), SolveFast.no_dup_fast(cs),
          SolveFast.init_floor(Groups.len_words(cs)),
          SolveRef.inf_of(Groups.len_words(cs))),
        SolveFast.dummy_inf(SolveRef.inf_of(Groups.len_words(cs)))),
      {==}, hok)
  FOpt.FOpt.valid_from_best_maybe(G, cs, inf,
    SolveK.fold_results(
      SolveK.par_chunks(d, G, 0, Groups.len_words(cs), G,
        SolveFast.glist_of_guesses(G, 0, 1),
        SolveFast.build_cwords(cs, G, 0, U32.from_nat(Groups.len_words(G))),
        cs, Groups.len_words(cs), SolveFast.no_dup_fast(cs),
        SolveFast.init_floor(Groups.len_words(cs)),
        SolveRef.inf_of(Groups.len_words(cs))),
      SolveFast.dummy_inf(SolveRef.inf_of(Groups.len_words(cs)))),
    T, hok_fold, e)

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
              +h3n : {Nat.is_le(3n, Groups.len_words(cs)) == True{}
                      : Bool} =
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
              +h3n : {Nat.is_le(3n, Groups.len_words(cs)) == True{}
                      : Bool} =
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
  match k:
    case 0n:
      FOpt.FOpt.solve_valid(G, C, T, e)
    case 1n+p:
      match p:
        case 0n:
          FOpt.FOpt.solve_valid(G, C, T, e)
        case 1n+q:
          P.solve_k_checked_valid(G, C, SolveK.depth_of(1n+p),
            SolveFast.all_in_fast(C, G), {==}, T, e)

def P.solve_k_optimal(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +k: Nat, +T2: Tree.Tree, v: Tree.Valid(T2, G, C)) ->
  Exists(Tree.Tree, T =>
    {SolveK.solve_k(G, C, k) == Some{T} : Maybe<Tree.Tree>}
    & {Nat.is_le(Tree.cost(T, C), Tree.cost(T2, C)) == True{} : Bool}):
  match k:
    case 0n:
      FOpt.FOpt.solve_optimal(G, C, T2, v)
    case 1n+p:
      match p:
        case 0n:
          FOpt.FOpt.solve_optimal(G, C, T2, v)
        case 1n+q:
          P.solve_k_checked_optimal(G, C, SolveK.depth_of(1n+p),
            SolveFast.all_in_fast(C, G), {==}, T2, v)
