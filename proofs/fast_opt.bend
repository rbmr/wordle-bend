# Direct validity and optimality of the bound-pruned solver (`src/solve_fast.bend`).
#
# Rather than proving tree-for-tree equality with `SolveRef.solve`, this module
# proves directly by fuel induction over the staged guess queue that for every
# candidate subset `S` (represented as `CWord`s), cutoff accumulator `best0`
# with `cost_of(best0) <= inf`, and valid root-threaded buffer `buf0`:
# 1. `FVal.FV.best_ok_b(cost_of(best0), G, S, res) == True{}` (either the result
#    did not beat `best0`, or its tree is valid for `(G, S)` with `Tree.cost <= cost`),
# 2. `cost_of(res) <= cost_of(best0)`,
# 3. `cost_of(res) <= cost_of(FS.ref_run_at(fuel, inf, G, S))`, and
# 4. the returned buffer `buf2` preserves `FH.BufOk`.
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
import ./fast_perm.bend as FP
import ./fast_tbl.bend as FT
import ./fast_three.bend as FT3
import ./fast_lb2.bend as LB2
import ./fast_hist5.bend as FH
import ./fast_tight.bend as FTight
import ./fast_valid.bend as FVal

# ---------------------------------------------------------------------------
# Small arithmetic, list, and `sat_add` helpers
# ---------------------------------------------------------------------------

def FOpt.nat_pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def FOpt.nat_succ_disc(n: Nat) -> Type:
  match n:
    case 0n:
      Empty
    case 1n+p:
      Unit

def FOpt.nat_ne_succ(x: Nat, e: {x == 1n+x : Nat}) -> Empty:
  match x:
    case 0n:
      +es = Equal.sym(Nat, 0n, 1n, e)
      %es : FOpt.nat_succ_disc(_)
      Unit{}
    case 1n+p:
      FOpt.nat_ne_succ(p,
        Equal.cong(Nat, Nat, FOpt.nat_pred, 1n+p, 1n+(1n+p), e))

def FOpt.init_floor_ne_2n(+w: +List<Nat>, +t: +List<+List<Nat>>,
    e: {SolveFast.init_floor(Groups.len_words(w <> t))
        == Nat.add(Groups.len_words(w <> t), Groups.len_words(w <> t))
        : Nat}) -> Empty:
  +k : Nat = Groups.len_words(t)
  +m : Nat = Nat.add(k, 1n+k)
  +e1 : {SolveFast.init_floor(1n+k) == m : Nat} =
    FLB.FS.sub_zero(m)
  +e2 : {m == 1n+m : Nat} =
    Equal.trans(Nat, m, SolveFast.init_floor(1n+k), 1n+m,
      Equal.sym(Nat, SolveFast.init_floor(1n+k), m, e1), e)
  FOpt.nat_ne_succ(m, e2)

def FOpt.list_disc(+xs: +List<+List<Nat>>) -> Type:
  match xs:
    case Nil{}:
      Empty
    case Con{_, _}:
      Unit

def FOpt.list_con_ne_nil(+h: +List<Nat>, +t: +List<+List<Nat>>,
    +e: {h <> t == Nil{} : +List<+List<Nat>>}) -> Empty:
  %e : FOpt.list_disc(_)
  Unit{}

def FOpt.cwords_nil_of_words_nil(cwS: +List<SolveFast.CWord>,
    e: {SolveFast.cwords_words(cwS) == Nil{} : +List<+List<Nat>>}) ->
  {cwS == Nil{} : +List<SolveFast.CWord>}:
  match cwS:
    case Nil{}:
      {==}
    case Con{cw, t}:
      match cw:
        case SolveFast.CWord{ci, grow, w}:
          Empty.absurd({SolveFast.CWord{ci, grow, w} <> t == Nil{}
                        : +List<SolveFast.CWord>},
            FOpt.list_con_ne_nil(w, SolveFast.cwords_words(t), e))

def FOpt.lt_sub_of_add_lt(a: Nat, +b: Nat, c: Nat,
    +hlt: {Nat.is_lt(Nat.add(a, b), c) == True{} : Bool}) ->
  {Nat.is_lt(b, Nat.sub(c, a)) == True{} : Bool}:
  match a c:
    case 0n 0n:
      hlt
    case 0n 1n+cp:
      hlt
    case 1n+ap 0n:
      Empty.absurd({Nat.is_lt(b, 0n) == True{} : Bool},
        Logic.Proof.false_ne_true(hlt))
    case 1n+ap 1n+cp:
      FOpt.lt_sub_of_add_lt(ap, b, cp, hlt)

def FOpt.bool_case_same(b: Bool, +x: Nat) ->
  {Feedback.Bool.case(Nat, b, x, x) == x : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def FOpt.sat_add_ge_r(+inf: Nat, +a: Nat, +b: Nat,
    +hge: {Nat.is_ge(b, inf) == True{} : Bool}) ->
  {SolveRef.sat_add(inf, a, b) == inf : Nat}:
  Equal.trans(Nat,
    SolveRef.sat_add(inf, a, b),
    Feedback.Bool.case(Nat, Nat.is_ge(a, inf), inf, inf),
    inf,
    Equal.cong(Bool, Nat,
      gb => Feedback.Bool.case(Nat, Nat.is_ge(a, inf), inf,
              Feedback.Bool.case(Nat, gb, inf, Nat.add(a, b))),
      Nat.is_ge(b, inf), True{}, hge),
    FOpt.bool_case_same(Nat.is_ge(a, inf), inf))

def FOpt.rws_ok_if_head(has_buf: Bool, +G: +List<+List<Nat>>, +n_root: Nat,
    +row: U32, +g: +List<Nat>, +rest: +List<FT.FT.RowWord>,
    +h: {FH.FH.rws_ok_if(has_buf, G, n_root, FT.RowWord{row, g} <> rest)
         == True{} : Bool}) ->
  {FH.FH.gentry_ok_if(has_buf, G, n_root, row, g) == True{} : Bool}:
  match has_buf:
    case False{}:
      {==}
    case True{}:
      Logic.Proof.and_true_l(FT.FT.gentry_ok_b(G, n_root, row, g),
        FT.FT.rws_ok_b(G, n_root, rest), h)

def FOpt.rws_ok_if_tail(has_buf: Bool, +G: +List<+List<Nat>>, +n_root: Nat,
    +row: U32, +g: +List<Nat>, +rest: +List<FT.FT.RowWord>,
    +h: {FH.FH.rws_ok_if(has_buf, G, n_root, FT.RowWord{row, g} <> rest)
         == True{} : Bool}) ->
  {FH.FH.rws_ok_if(has_buf, G, n_root, rest) == True{} : Bool}:
  match has_buf:
    case False{}:
      {==}
    case True{}:
      Logic.Proof.and_true_r(FT.FT.gentry_ok_b(G, n_root, row, g),
        FT.FT.rws_ok_b(G, n_root, rest), h)

def FOpt.cwords_to_rws_ok_if(has_buf: Bool, +G: +List<+List<Nat>>,
    +C_root: +List<+List<Nat>>, +n_root: Nat, +cs: +List<SolveFast.CWord>,
    +h: {FH.FH.cwords_ok_if(has_buf, G, C_root, n_root, cs) == True{} : Bool}) ->
  {FH.FH.rws_ok_if(has_buf, G, n_root, FT.FT.cwords_to_rws(cs))
   == True{} : Bool}:
  match has_buf:
    case False{}:
      {==}
    case True{}:
      FT.FT.cwords_to_rws_ok(G, C_root, n_root, cs, h)

def FOpt.guesses_to_rws_ok_if(has_buf: Bool, +G: +List<+List<Nat>>,
    +n_root: Nat) ->
  {FH.FH.rws_ok_if(has_buf, G, n_root,
     FT.FT.guesses_to_rws(G, 0, 1)) == True{} : Bool}:
  match has_buf:
    case False{}:
      {==}
    case True{}:
      FT.FT.guesses_to_rws_ok(G, n_root)

def FOpt.build_cwords_ok_if(has_buf: Bool, +G: +List<+List<Nat>>,
    +C: +List<+List<Nat>>, +n_root: Nat,
    +ai: {FO.FO.all_in_ref(C, G) == True{} : Bool}) ->
  {FH.FH.cwords_ok_if(has_buf, G, C, n_root,
     SolveFast.build_cwords(C, G, 0,
       U32.from_nat(Groups.len_words(G)))) == True{} : Bool}:
  match has_buf:
    case False{}:
      {==}
    case True{}:
      FT.FT.build_cwords_ok(C, G, n_root, ai)

# ---------------------------------------------------------------------------
# Job-level specification and fuel-induction structures
# ---------------------------------------------------------------------------

def FOpt.job_res_b(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +limit: Nat, +res: SolveRef.Best) -> Bool:
  Bool.and(FVal.FV.best_ok_b(limit, G, S, res),
    Bool.and(Nat.is_le(Eval.Eval.cost_of(res), limit),
             Nat.is_le(Eval.Eval.cost_of(res),
               Eval.Eval.cost_of(FS.FS.ref_run_at(fuel, inf, G, S)))))

def FOpt.JobResSpec(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +C_root: +List<+List<Nat>>, +n_root: Nat, +has_buf: Bool, +nodup: Bool,
    +S: +List<+List<Nat>>, +limit: Nat, sr: SolveFast.StepRes) -> Data:
  match sr:
    case SolveFast.StepRes{res, buf2}:
      Arr.Arr.DPair<
        {FOpt.job_res_b(fuel, inf, G, S, limit, res) == True{} : Bool},
        FH.FH.BufOk(G, C_root, n_root, has_buf, nodup, buf2)>

def FOpt.job_res_spec_transport(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +C_root: +List<+List<Nat>>, +n_root: Nat, +has_buf: Bool, +nodup: Bool,
    +S: +List<+List<Nat>>, +limit: Nat,
    -sr1: SolveFast.StepRes, -sr2: SolveFast.StepRes,
    +esr: {sr1 == sr2 : SolveFast.StepRes},
    +h: FOpt.JobResSpec(fuel, inf, G, C_root, n_root, has_buf, nodup, S,
          limit, sr1)) ->
  FOpt.JobResSpec(fuel, inf, G, C_root, n_root, has_buf, nodup, S, limit, sr2):
  %esr : FOpt.JobResSpec(fuel, inf, G, C_root, n_root, has_buf, nodup, S,
           limit, _)
  h

def FOpt.EJob(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +C_root: +List<+List<Nat>>, +n_root: Nat, +has_buf: Bool,
    +S: +List<+List<Nat>>, +nodup: Bool) -> Type:
  @rwsG: +List<FT.FT.RowWord> ->
  @cwS: +List<SolveFast.CWord> ->
  @best0: SolveRef.Best ->
  @buf0: SolveFast.Buf5 ->
  {FT.FT.rws_words(rwsG) == G : +List<+List<Nat>>} ->
  {FH.FH.rws_ok_if(has_buf, G, n_root, rwsG) == True{} : Bool} ->
  {SolveFast.cwords_words(cwS) == S : +List<+List<Nat>>} ->
  {FH.FH.cwords_ok_if(has_buf, G, C_root, n_root, cwS) == True{} : Bool} ->
  {Nat.is_le(Eval.Eval.cost_of(best0), inf) == True{} : Bool} ->
  FH.FH.BufOk(G, C_root, n_root, has_buf, nodup, buf0) ->
  FOpt.JobResSpec(fuel, inf, G, C_root, n_root, has_buf, nodup, S,
    Eval.Eval.cost_of(best0),
    FS.FS.run_child_from(fuel, inf,
      FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS, nodup, best0, buf0))

def FOpt.EFlat(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +C_root: +List<+List<Nat>>, +n_root: Nat, +has_buf: Bool, +nodup: Bool,
    jobs: +List<+List<+List<Nat>>>) -> Type:
  match jobs:
    case Nil{}:
      Unit
    case Con{S, t}:
      FOpt.EJob(fuel, inf, G, C_root, n_root, has_buf, S, nodup)
      & FOpt.EFlat(fuel, inf, G, C_root, n_root, has_buf, nodup, t)

def FOpt.EClass(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +C_root: +List<+List<Nat>>, +n_root: Nat, +has_buf: Bool, +nodup: Bool,
    +groups: +List<Groups.Group>) -> Type:
  match groups:
    case Nil{}:
      Unit
    case Con{gp, rest}:
      match gp:
        case Groups.Group{fb, ws}:
          FOpt.EJob(p, inf, G, C_root, n_root, has_buf, ws, nodup)
          & FOpt.EClass(p, inf, G, C_root, n_root, has_buf, nodup, rest)

def FOpt.EClassIf(b: Bool, +p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +C_root: +List<+List<Nat>>, +n_root: Nat, +has_buf: Bool, +nodup: Bool,
    +groups: +List<Groups.Group>) -> Type:
  match b:
    case True{}:
      FOpt.EClass(p, inf, G, C_root, n_root, has_buf, nodup, groups)
    case False{}:
      Unit

def FOpt.EByGs(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +C_root: +List<+List<Nat>>, +n_root: Nat, +has_buf: Bool,
    +S: +List<+List<Nat>>, +nodup: Bool, gs: +List<+List<Nat>>) -> Type:
  match gs:
    case Nil{}:
      Unit
    case Con{g, t}:
      FOpt.EClassIf(
        Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
        p, inf, G, C_root, n_root, has_buf, nodup,
        Groups.groups_build(g, S, Nil{}))
      & FOpt.EByGs(p, inf, G, C_root, n_root, has_buf, S, nodup, t)

def FOpt.eclass_of_if_true(+b: Bool, +p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +C_root: +List<+List<Nat>>, +n_root: Nat, +has_buf: Bool, +nodup: Bool,
    +groups: +List<Groups.Group>,
    +eb: {b == True{} : Bool},
    ecif: FOpt.EClassIf(b, p, inf, G, C_root, n_root, has_buf, nodup, groups)) ->
  FOpt.EClass(p, inf, G, C_root, n_root, has_buf, nodup, groups):
  %eb : FOpt.EClassIf(_, p, inf, G, C_root, n_root, has_buf, nodup, groups)
  ecif

def FOpt.eby_gs_transport(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +C_root: +List<+List<Nat>>, +n_root: Nat, +has_buf: Bool,
    +S: +List<+List<Nat>>, +nodup: Bool,
    +gs1: +List<+List<Nat>>, +gs2: +List<+List<Nat>>,
    +e: {gs1 == gs2 : +List<+List<Nat>>},
    f: FOpt.EByGs(p, inf, G, C_root, n_root, has_buf, S, nodup, gs1)) ->
  FOpt.EByGs(p, inf, G, C_root, n_root, has_buf, S, nodup, gs2):
  %e : FOpt.EByGs(p, inf, G, C_root, n_root, has_buf, S, nodup, _)
  f

def FOpt.eclass_skip_go(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +C_root: +List<+List<Nat>>, +n_root: Nat, +has_buf: Bool, +nodup: Bool,
    +fx: +List<Feedback.Color>, +wx: +List<+List<Nat>>,
    +tx: +List<Groups.Group>, +ty: +List<Groups.Group>,
    ec: FOpt.EClass(p, inf, G, C_root, n_root, has_buf, nodup,
          Groups.Group{fx, wx} <> tx),
    f: FOpt.EClass(p, inf, G, C_root, n_root, has_buf, nodup, tx) ->
       FOpt.EClass(p, inf, G, C_root, n_root, has_buf, nodup, ty)) ->
  FOpt.EClass(p, inf, G, C_root, n_root, has_buf, nodup,
    Groups.Group{fx, wx} <> ty):
  (eh, et) = ec
  Tuple{eh, f(et)}

def FOpt.eclass_swap_go(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +C_root: +List<+List<Nat>>, +n_root: Nat, +has_buf: Bool, +nodup: Bool,
    +fa: +List<Feedback.Color>, +wa: +List<+List<Nat>>,
    +fb: +List<Feedback.Color>, +wb: +List<+List<Nat>>,
    +tx: +List<Groups.Group>,
    ec: FOpt.EClass(p, inf, G, C_root, n_root, has_buf, nodup,
          Groups.Group{fa, wa} <> (Groups.Group{fb, wb} <> tx))) ->
  FOpt.EClass(p, inf, G, C_root, n_root, has_buf, nodup,
    Groups.Group{fb, wb} <> (Groups.Group{fa, wa} <> tx)):
  (ea, r1) = ec
  (eb, et) = r1
  Tuple{eb, Tuple{ea, et}}

def FOpt.eclass_perm(perm: FP.FP.Perm, +p: Nat, +inf: Nat,
    +G: +List<+List<Nat>>, +C_root: +List<+List<Nat>>, +n_root: Nat,
    +has_buf: Bool, +nodup: Bool,
    +xs: +List<Groups.Group>, +ys: +List<Groups.Group>,
    +ok: FP.FP.PermOk(perm, xs, ys),
    ec: FOpt.EClass(p, inf, G, C_root, n_root, has_buf, nodup, xs)) ->
  FOpt.EClass(p, inf, G, C_root, n_root, has_buf, nodup, ys):
  match perm:
    case FP.PRefl{}:
      %ok : FOpt.EClass(p, inf, G, C_root, n_root, has_buf, nodup, _)
      ec
    case FP.PSkip{pr}:
      match xs:
        case Nil{}:
          Empty.absurd(
            FOpt.EClass(p, inf, G, C_root, n_root, has_buf, nodup, ys), ok)
        case Con{hx, tx}:
          match hx:
            case Groups.Group{+fx, +wx}:
              match ys:
                case Nil{}:
                  Empty.absurd(Unit, ok)
                case Con{hy, ty}:
                  +eh = Arr.Arr.dpair_l(
                          {Groups.Group{fx, wx} == hy : Groups.Group},
                          FP.FP.PermOk(pr, tx, ty), ok)
                  +et = Arr.Arr.dpair_r(
                          {Groups.Group{fx, wx} == hy : Groups.Group},
                          FP.FP.PermOk(pr, tx, ty), ok)
                  %eh : FOpt.EClass(p, inf, G, C_root, n_root, has_buf, nodup,
                          _ <> ty)
                  FOpt.eclass_skip_go(p, inf, G, C_root, n_root, has_buf, nodup,
                    fx, wx, tx, ty, ec,
                    et0 => FOpt.eclass_perm(pr, p, inf, G, C_root, n_root,
                             has_buf, nodup, tx, ty, et, et0))
    case FP.PSwap{}:
      match xs:
        case Nil{}:
          Empty.absurd(
            FOpt.EClass(p, inf, G, C_root, n_root, has_buf, nodup, ys), ok)
        case Con{a, t1}:
          match a:
            case Groups.Group{+fa, +wa}:
              match t1:
                case Nil{}:
                  Empty.absurd(
                    FOpt.EClass(p, inf, G, C_root, n_root, has_buf, nodup, ys),
                    ok)
                case Con{b, tx}:
                  match b:
                    case Groups.Group{+fb2, +wb}:
                      match ys:
                        case Nil{}:
                          Empty.absurd(Unit, ok)
                        case Con{c, t2}:
                          match t2:
                            case Nil{}:
                              Empty.absurd(
                                FOpt.EClass(p, inf, G, C_root, n_root, has_buf,
                                  nodup, c <> Nil{}), ok)
                            case Con{d, ty}:
                              +ead = Arr.Arr.dpair_l(
                                       {Groups.Group{fa, wa} == d : Groups.Group},
                                       Arr.Arr.DPair<
                                         {Groups.Group{fb2, wb} == c : Groups.Group},
                                         {tx == ty : +List<Groups.Group>}>, ok)
                              +r1 = Arr.Arr.dpair_r(
                                      {Groups.Group{fa, wa} == d : Groups.Group},
                                      Arr.Arr.DPair<
                                        {Groups.Group{fb2, wb} == c : Groups.Group},
                                        {tx == ty : +List<Groups.Group>}>, ok)
                              +ebc = Arr.Arr.dpair_l(
                                       {Groups.Group{fb2, wb} == c : Groups.Group},
                                       {tx == ty : +List<Groups.Group>}, r1)
                              +et = Arr.Arr.dpair_r(
                                      {Groups.Group{fb2, wb} == c : Groups.Group},
                                      {tx == ty : +List<Groups.Group>}, r1)
                              %ead : FOpt.EClass(p, inf, G, C_root, n_root,
                                       has_buf, nodup, c <> (_ <> ty))
                              %ebc : FOpt.EClass(p, inf, G, C_root, n_root,
                                       has_buf, nodup,
                                       _ <> (Groups.Group{fa, wa} <> ty))
                              %et : FOpt.EClass(p, inf, G, C_root, n_root,
                                      has_buf, nodup,
                                      Groups.Group{fb2, wb}
                                      <> (Groups.Group{fa, wa} <> _))
                              FOpt.eclass_swap_go(p, inf, G, C_root, n_root,
                                has_buf, nodup, fa, wa, fb2, wb, tx, ec)
    case FP.PTrans{+mid, p1, p2}:
      +ok1 = Arr.Arr.dpair_l(FP.FP.PermOk(p1, xs, mid),
               FP.FP.PermOk(p2, mid, ys), ok)
      +ok2 = Arr.Arr.dpair_r(FP.FP.PermOk(p1, xs, mid),
               FP.FP.PermOk(p2, mid, ys), ok)
      FOpt.eclass_perm(p2, p, inf, G, C_root, n_root, has_buf, nodup,
        mid, ys, ok2,
        FOpt.eclass_perm(p1, p, inf, G, C_root, n_root, has_buf, nodup,
          xs, mid, ok1, ec))

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
    +C_root: +List<+List<Nat>>, +n_root: Nat, +has_buf: Bool, +nodup: Bool,
    +xs: +List<+List<+List<Nat>>>, +ys: +List<+List<+List<Nat>>>,
    f: FOpt.EFlat(fuel, inf, G, C_root, n_root, has_buf, nodup,
         List.append(&2, +List<+List<Nat>>, xs, ys))) ->
  FOpt.EFlat(fuel, inf, G, C_root, n_root, has_buf, nodup, xs)
  & FOpt.EFlat(fuel, inf, G, C_root, n_root, has_buf, nodup, ys):
  match xs:
    case Nil{}:
      Tuple{Unit{}, f}
    case Con{S, t}:
      (j, fr) = f
      MV.MV.use_pair(
        FOpt.EFlat(fuel, inf, G, C_root, n_root, has_buf, nodup, S <> t)
        & FOpt.EFlat(fuel, inf, G, C_root, n_root, has_buf, nodup, ys),
        FOpt.EFlat(fuel, inf, G, C_root, n_root, has_buf, nodup, t),
        FOpt.EFlat(fuel, inf, G, C_root, n_root, has_buf, nodup, ys),
        FOpt.eflat_append(fuel, inf, G, C_root, n_root, has_buf, nodup, t, ys, fr),
        ft => fys => Tuple{Tuple{j, ft}, fys})

def FOpt.eclass_of_flat(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +C_root: +List<+List<Nat>>, +n_root: Nat, +has_buf: Bool, +nodup: Bool,
    +groups: +List<Groups.Group>,
    f: FOpt.EFlat(p, inf, G, C_root, n_root, has_buf, nodup,
         MV.MV.next_groups(groups))) ->
  FOpt.EClass(p, inf, G, C_root, n_root, has_buf, nodup, groups):
  match groups:
    case Nil{}:
      Unit{}
    case Con{gp, t}:
      match gp:
        case Groups.Group{fb, ws}:
          (j, fr) = f
          (j, FOpt.eclass_of_flat(p, inf, G, C_root, n_root, has_buf, nodup, t, fr))

def FOpt.eclass_if(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +C_root: +List<+List<Nat>>, +n_root: Nat, +has_buf: Bool, +nodup: Bool,
    +groups: +List<Groups.Group>, b: Bool,
    f: FOpt.EFlat(p, inf, G, C_root, n_root, has_buf, nodup,
         MV.MV.classes_b(b, groups))) ->
  FOpt.EClassIf(b, p, inf, G, C_root, n_root, has_buf, nodup, groups):
  match b:
    case True{}:
      FOpt.eclass_of_flat(p, inf, G, C_root, n_root, has_buf, nodup, groups, f)
    case False{}:
      Unit{}

def FOpt.eby_gs(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +C_root: +List<+List<Nat>>, +n_root: Nat, +has_buf: Bool,
    +S: +List<+List<Nat>>, +nodup: Bool, +gs: +List<+List<Nat>>,
    f: FOpt.EFlat(p, inf, G, C_root, n_root, has_buf, nodup,
         MV.MV.next_guess(gs, S))) ->
  FOpt.EByGs(p, inf, G, C_root, n_root, has_buf, S, nodup, gs):
  match gs:
    case Nil{}:
      Unit{}
    case Con{g, t}:
      MV.MV.use_pair(FOpt.EByGs(p, inf, G, C_root, n_root, has_buf, S, nodup, g <> t),
        FOpt.EFlat(p, inf, G, C_root, n_root, has_buf, nodup, MV.MV.classes(g, S)),
        FOpt.EFlat(p, inf, G, C_root, n_root, has_buf, nodup, MV.MV.next_guess(t, S)),
        FOpt.eflat_append(p, inf, G, C_root, n_root, has_buf, nodup,
          MV.MV.classes(g, S), MV.MV.next_guess(t, S), f),
        fg => ft =>
          Tuple{FOpt.eclass_if(p, inf, G, C_root, n_root, has_buf, nodup,
                  Groups.groups_build(g, S, Nil{}),
                  Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
                  fg),
                FOpt.eby_gs(p, inf, G, C_root, n_root, has_buf, S, nodup, t, ft)})

# ---------------------------------------------------------------------------
# Dead-body skipping and `FH.body_lb` lower-bound soundness
# ---------------------------------------------------------------------------

def FOpt.body_dead(+groups: +List<Groups.Group>, +body: +List<SolveFast.Item>,
    +p: Nat, +gs: SolveFast.GList, +G: +List<+List<Nat>>,
    +C_root: +List<+List<Nat>>, +n_root: Nat, +has_buf: Bool,
    +gG: SolveFast.GList, +cwS: +List<SolveFast.CWord>, +n: Nat,
    +nodup: Bool, +floor: Nat, +inf: Nat, +g: +List<Nat>,
    +kids: +List<Tree.Child>, +sum: Nat, +best: SolveRef.Best,
    -gres: SolveFast.GuessRes,
    +hbm: FH.FH.BodyMatch(G, C_root, n_root, has_buf, nodup, n, groups, body)) ->
  {SolveFast.step(1n+p, gs, 0n, body, gG, cwS, n, nodup, floor, inf, g,
     kids, sum, best, SolveFast.dummy_step_zero(), True{}, False{}, gres)
   == SolveFast.step(1n+p, gs, 0n, Nil{}, gG, cwS, n, nodup, floor, inf,
        Nil{}, Nil{}, 0n, best, SolveFast.dummy_step_zero(), False{}, False{},
        gres) : SolveFast.StepRes}:
  match groups:
    case Nil{}:
      %Equal.sym(+List<SolveFast.Item>, body, SolveFast.End{} <> Nil{}, hbm) :
        {SolveFast.step(1n+p, gs, 0n, _, gG, cwS, n, nodup, floor, inf, g,
           kids, sum, best, SolveFast.dummy_step_zero(), True{}, False{}, gres)
         == SolveFast.step(1n+p, gs, 0n, Nil{}, gG, cwS, n, nodup, floor, inf,
              Nil{}, Nil{}, 0n, best, SolveFast.dummy_step_zero(), False{},
              False{}, gres) : SolveFast.StepRes}
      FS.FS.end_step(p, gs, gG, cwS, n, nodup, floor, inf, g, kids, sum, best,
        SolveFast.dummy_step_zero(), Nil{}, True{}, gres)
    case Con{gp, restg}:
      match gp:
        case Groups.Group{+fb, +ws}:
          match body:
            case Nil{}:
              Empty.absurd(
                {SolveFast.step(1n+p, gs, 0n, Nil{}, gG, cwS, n, nodup, floor,
                   inf, g, kids, sum, best, SolveFast.dummy_step_zero(), True{},
                   False{}, gres)
                 == SolveFast.step(1n+p, gs, 0n, Nil{}, gG, cwS, n, nodup,
                      floor, inf, Nil{}, Nil{}, 0n, best,
                      SolveFast.dummy_step_zero(), False{}, False{}, gres)
                 : SolveFast.StepRes}, hbm)
            case Con{it, restb}:
              match it:
                case SolveFast.Begin{g2}:
                  Empty.absurd(
                    {SolveFast.step(1n+p, gs, 0n, SolveFast.Begin{g2} <> restb,
                       gG, cwS, n, nodup, floor, inf, g, kids, sum, best,
                       SolveFast.dummy_step_zero(), True{}, False{}, gres)
                     == SolveFast.step(1n+p, gs, 0n, Nil{}, gG, cwS, n, nodup,
                          floor, inf, Nil{}, Nil{}, 0n, best,
                          SolveFast.dummy_step_zero(), False{}, False{}, gres)
                     : SolveFast.StepRes}, hbm)
                case SolveFast.OneItem{+f, +w}:
                  +r1 = Arr.Arr.dpair_r({f == fb : +List<Feedback.Color>},
                          Arr.Arr.DPair<{ws == w <> Nil{} : +List<+List<Nat>>},
                            FH.FH.BodyMatch(G, C_root, n_root, has_buf, nodup,
                              n, restg, restb)>, hbm)
                  +hbm2 = Arr.Arr.dpair_r({ws == w <> Nil{} : +List<+List<Nat>>},
                            FH.FH.BodyMatch(G, C_root, n_root, has_buf, nodup,
                              n, restg, restb), r1)
                  Equal.trans(SolveFast.StepRes,
                    SolveFast.step(1n+p, gs, 0n, SolveFast.OneItem{f, w} <> restb,
                      gG, cwS, n, nodup, floor, inf, g, kids, sum, best,
                      SolveFast.dummy_step_zero(), True{}, False{}, gres),
                    SolveFast.step(1n+p, gs, 0n, restb, gG, cwS, n, nodup, floor,
                      inf, g, kids, sum, best, SolveFast.dummy_step_zero(),
                      True{}, False{}, gres),
                    SolveFast.step(1n+p, gs, 0n, Nil{}, gG, cwS, n, nodup, floor,
                      inf, Nil{}, Nil{}, 0n, best, SolveFast.dummy_step_zero(),
                      False{}, False{}, gres),
                    FS.FS.one_dead(p, gs, gG, cwS, n, nodup, floor, inf, g, f, w,
                      restb, kids, sum, best, gres),
                    FOpt.body_dead(restg, restb, p, gs, G, C_root, n_root,
                      has_buf, gG, cwS, n, nodup, floor, inf, g, kids, sum, best,
                      gres, hbm2))
                case SolveFast.TwoItem{+f, +w1, +w2}:
                  +r1 = Arr.Arr.dpair_r({nodup == True{} : Bool},
                          Arr.Arr.DPair<{f == fb : +List<Feedback.Color>},
                            Arr.Arr.DPair<
                              {ws == w1 <> (w2 <> Nil{}) : +List<+List<Nat>>},
                              FH.FH.BodyMatch(G, C_root, n_root, has_buf, nodup,
                                n, restg, restb)>>, hbm)
                  +r2 = Arr.Arr.dpair_r({f == fb : +List<Feedback.Color>},
                          Arr.Arr.DPair<
                            {ws == w1 <> (w2 <> Nil{}) : +List<+List<Nat>>},
                            FH.FH.BodyMatch(G, C_root, n_root, has_buf, nodup,
                              n, restg, restb)>, r1)
                  +hbm2 = Arr.Arr.dpair_r(
                            {ws == w1 <> (w2 <> Nil{}) : +List<+List<Nat>>},
                            FH.FH.BodyMatch(G, C_root, n_root, has_buf, nodup,
                              n, restg, restb), r2)
                  Equal.trans(SolveFast.StepRes,
                    SolveFast.step(1n+p, gs, 0n,
                      SolveFast.TwoItem{f, w1, w2} <> restb, gG, cwS, n, nodup,
                      floor, inf, g, kids, sum, best,
                      SolveFast.dummy_step_zero(), True{}, False{}, gres),
                    SolveFast.step(1n+p, gs, 0n, restb, gG, cwS, n, nodup, floor,
                      inf, g, kids, sum, best, SolveFast.dummy_step_zero(),
                      True{}, False{}, gres),
                    SolveFast.step(1n+p, gs, 0n, Nil{}, gG, cwS, n, nodup, floor,
                      inf, Nil{}, Nil{}, 0n, best, SolveFast.dummy_step_zero(),
                      False{}, False{}, gres),
                    FS.FS.two_dead(p, gs, gG, cwS, n, nodup, floor, inf, g, f,
                      w1, w2, restb, kids, sum, best, gres),
                    FOpt.body_dead(restg, restb, p, gs, G, C_root, n_root,
                      has_buf, gG, cwS, n, nodup, floor, inf, g, kids, sum, best,
                      gres, hbm2))
                case SolveFast.DoneItem{+f, +tr, +c}:
                  +r1 = Arr.Arr.dpair_r({nodup == True{} : Bool},
                          Arr.Arr.DPair<{f == fb : +List<Feedback.Color>},
                            Arr.Arr.DPair<
                              {FH.FH.done_ws_ok_b(G, ws, tr, c) == True{} : Bool},
                              FH.FH.BodyMatch(G, C_root, n_root, has_buf, nodup,
                                n, restg, restb)>>, hbm)
                  +r2 = Arr.Arr.dpair_r({f == fb : +List<Feedback.Color>},
                          Arr.Arr.DPair<
                            {FH.FH.done_ws_ok_b(G, ws, tr, c) == True{} : Bool},
                            FH.FH.BodyMatch(G, C_root, n_root, has_buf, nodup,
                              n, restg, restb)>, r1)
                  +hbm2 = Arr.Arr.dpair_r(
                            {FH.FH.done_ws_ok_b(G, ws, tr, c) == True{} : Bool},
                            FH.FH.BodyMatch(G, C_root, n_root, has_buf, nodup,
                              n, restg, restb), r2)
                  Equal.trans(SolveFast.StepRes,
                    SolveFast.step(1n+p, gs, 0n,
                      SolveFast.DoneItem{f, tr, c} <> restb, gG, cwS, n, nodup,
                      floor, inf, g, kids, sum, best,
                      SolveFast.dummy_step_zero(), True{}, False{}, gres),
                    SolveFast.step(1n+p, gs, 0n, restb, gG, cwS, n, nodup, floor,
                      inf, g, kids, sum, best, SolveFast.dummy_step_zero(),
                      True{}, False{}, gres),
                    SolveFast.step(1n+p, gs, 0n, Nil{}, gG, cwS, n, nodup, floor,
                      inf, Nil{}, Nil{}, 0n, best, SolveFast.dummy_step_zero(),
                      False{}, False{}, gres),
                    FS.FS.done_dead(p, gs, gG, cwS, n, nodup, floor, inf, g, f,
                      tr, c, restb, kids, sum, best, gres),
                    FOpt.body_dead(restg, restb, p, gs, G, C_root, n_root,
                      has_buf, gG, cwS, n, nodup, floor, inf, g, kids, sum, best,
                      gres, hbm2))
                case SolveFast.ClassItem{+f, +cws, +wlen, +tlb}:
                  match restb:
                    case Nil{}:
                      Empty.absurd(
                        {SolveFast.step(1n+p, gs, 0n,
                           SolveFast.ClassItem{f, cws, wlen, tlb} <> Nil{},
                           gG, cwS, n, nodup, floor, inf, g, kids, sum, best,
                           SolveFast.dummy_step_zero(), True{}, False{}, gres)
                         == SolveFast.step(1n+p, gs, 0n, Nil{}, gG, cwS, n,
                              nodup, floor, inf, Nil{}, Nil{}, 0n, best,
                              SolveFast.dummy_step_zero(), False{}, False{},
                              gres) : SolveFast.StepRes}, hbm)
                    case Con{it2, restb2}:
                      match it2:
                        case SolveFast.Add{+f2, +tlb2}:
                          +r1 = Arr.Arr.dpair_r({f == fb : +List<Feedback.Color>},
                                  Arr.Arr.DPair<{f2 == fb : +List<Feedback.Color>},
                                    Arr.Arr.DPair<
                                      {SolveFast.cwords_words(cws) == ws
                                       : +List<+List<Nat>>},
                                      Arr.Arr.DPair<{wlen == Groups.len_words(ws) : Nat},
                                        Arr.Arr.DPair<
                                          {FH.FH.cwords_ok_if(has_buf, G, C_root, n_root, cws)
                                           == True{} : Bool},
                                          Arr.Arr.DPair<
                                            {FH.FH.tail_lb_ok_b(G, nodup, n, restb2, tlb)
                                             == True{} : Bool},
                                            Arr.Arr.DPair<{tlb2 == tlb : Nat},
                                              FH.FH.BodyMatch(G, C_root, n_root,
                                                has_buf, nodup, n, restg, restb2)>>>>>>,
                                  hbm)
                          +r2 = Arr.Arr.dpair_r({f2 == fb : +List<Feedback.Color>},
                                  Arr.Arr.DPair<
                                    {SolveFast.cwords_words(cws) == ws
                                     : +List<+List<Nat>>},
                                    Arr.Arr.DPair<{wlen == Groups.len_words(ws) : Nat},
                                      Arr.Arr.DPair<
                                        {FH.FH.cwords_ok_if(has_buf, G, C_root, n_root, cws)
                                         == True{} : Bool},
                                        Arr.Arr.DPair<
                                          {FH.FH.tail_lb_ok_b(G, nodup, n, restb2, tlb)
                                           == True{} : Bool},
                                          Arr.Arr.DPair<{tlb2 == tlb : Nat},
                                            FH.FH.BodyMatch(G, C_root, n_root,
                                              has_buf, nodup, n, restg, restb2)>>>>>,
                                  r1)
                          +r3 = Arr.Arr.dpair_r(
                                  {SolveFast.cwords_words(cws) == ws
                                   : +List<+List<Nat>>},
                                  Arr.Arr.DPair<{wlen == Groups.len_words(ws) : Nat},
                                    Arr.Arr.DPair<
                                      {FH.FH.cwords_ok_if(has_buf, G, C_root, n_root, cws)
                                       == True{} : Bool},
                                      Arr.Arr.DPair<
                                        {FH.FH.tail_lb_ok_b(G, nodup, n, restb2, tlb)
                                         == True{} : Bool},
                                        Arr.Arr.DPair<{tlb2 == tlb : Nat},
                                          FH.FH.BodyMatch(G, C_root, n_root,
                                            has_buf, nodup, n, restg, restb2)>>>>,
                                  r2)
                          +r4 = Arr.Arr.dpair_r({wlen == Groups.len_words(ws) : Nat},
                                  Arr.Arr.DPair<
                                    {FH.FH.cwords_ok_if(has_buf, G, C_root, n_root, cws)
                                     == True{} : Bool},
                                    Arr.Arr.DPair<
                                      {FH.FH.tail_lb_ok_b(G, nodup, n, restb2, tlb)
                                       == True{} : Bool},
                                      Arr.Arr.DPair<{tlb2 == tlb : Nat},
                                        FH.FH.BodyMatch(G, C_root, n_root,
                                          has_buf, nodup, n, restg, restb2)>>>,
                                  r3)
                          +r5 = Arr.Arr.dpair_r(
                                  {FH.FH.cwords_ok_if(has_buf, G, C_root, n_root, cws)
                                   == True{} : Bool},
                                  Arr.Arr.DPair<
                                    {FH.FH.tail_lb_ok_b(G, nodup, n, restb2, tlb)
                                     == True{} : Bool},
                                    Arr.Arr.DPair<{tlb2 == tlb : Nat},
                                      FH.FH.BodyMatch(G, C_root, n_root,
                                        has_buf, nodup, n, restg, restb2)>>,
                                  r4)
                          +r6 = Arr.Arr.dpair_r(
                                  {FH.FH.tail_lb_ok_b(G, nodup, n, restb2, tlb)
                                   == True{} : Bool},
                                  Arr.Arr.DPair<{tlb2 == tlb : Nat},
                                    FH.FH.BodyMatch(G, C_root, n_root,
                                      has_buf, nodup, n, restg, restb2)>,
                                  r5)
                          +hbm2 = Arr.Arr.dpair_r({tlb2 == tlb : Nat},
                                    FH.FH.BodyMatch(G, C_root, n_root,
                                      has_buf, nodup, n, restg, restb2), r6)
                          Equal.trans(SolveFast.StepRes,
                            SolveFast.step(1n+p, gs, 0n,
                              SolveFast.ClassItem{f, cws, wlen, tlb}
                              <> (SolveFast.Add{f2, tlb2} <> restb2),
                              gG, cwS, n, nodup, floor, inf, g, kids, sum, best,
                              SolveFast.dummy_step_zero(), True{}, False{}, gres),
                            SolveFast.step(1n+p, gs, 0n,
                              SolveFast.Add{f2, tlb2} <> restb2,
                              gG, cwS, n, nodup, floor, inf, g, kids, sum, best,
                              SolveFast.dummy_step_zero(), True{}, False{}, gres),
                            SolveFast.step(1n+p, gs, 0n, Nil{}, gG, cwS, n,
                              nodup, floor, inf, Nil{}, Nil{}, 0n, best,
                              SolveFast.dummy_step_zero(), False{}, False{}, gres),
                            FS.FS.class_dead(p, gs, gG, cwS, n, nodup, floor,
                              inf, g, f, cws, wlen, tlb,
                              SolveFast.Add{f2, tlb2} <> restb2, kids, sum,
                              best, gres),
                            Equal.trans(SolveFast.StepRes,
                              SolveFast.step(1n+p, gs, 0n,
                                SolveFast.Add{f2, tlb2} <> restb2,
                                gG, cwS, n, nodup, floor, inf, g, kids, sum,
                                best, SolveFast.dummy_step_zero(), True{},
                                False{}, gres),
                              SolveFast.step(1n+p, gs, 0n, restb2, gG, cwS, n,
                                nodup, floor, inf, g, kids, sum, best,
                                SolveFast.dummy_step_zero(), True{}, False{},
                                gres),
                              SolveFast.step(1n+p, gs, 0n, Nil{}, gG, cwS, n,
                                nodup, floor, inf, Nil{}, Nil{}, 0n, best,
                                SolveFast.dummy_step_zero(), False{}, False{},
                                gres),
                              FS.FS.add_dead(p, gs, gG, cwS, n, nodup, floor,
                                inf, g, f2, tlb2, restb2, kids, sum, best,
                                SolveFast.dummy_zero(), SolveFast.NoBuf{}, gres),
                              FOpt.body_dead(restg, restb2, p, gs, G, C_root,
                                n_root, has_buf, gG, cwS, n, nodup, floor, inf,
                                g, kids, sum, best, gres, hbm2)))
                        case SolveFast.Begin{g2}:
                          Empty.absurd(
                            {SolveFast.step(1n+p, gs, 0n,
                               SolveFast.ClassItem{f, cws, wlen, tlb}
                               <> (SolveFast.Begin{g2} <> restb2),
                               gG, cwS, n, nodup, floor, inf, g, kids, sum,
                               best, SolveFast.dummy_step_zero(), True{},
                               False{}, gres)
                             == SolveFast.step(1n+p, gs, 0n, Nil{}, gG, cwS, n,
                                  nodup, floor, inf, Nil{}, Nil{}, 0n, best,
                                  SolveFast.dummy_step_zero(), False{}, False{},
                                  gres) : SolveFast.StepRes}, hbm)
                        case SolveFast.ClassItem{fa, ca, la, ta}:
                          Empty.absurd(
                            {SolveFast.step(1n+p, gs, 0n,
                               SolveFast.ClassItem{f, cws, wlen, tlb}
                               <> (SolveFast.ClassItem{fa, ca, la, ta} <> restb2),
                               gG, cwS, n, nodup, floor, inf, g, kids, sum,
                               best, SolveFast.dummy_step_zero(), True{},
                               False{}, gres)
                             == SolveFast.step(1n+p, gs, 0n, Nil{}, gG, cwS, n,
                                  nodup, floor, inf, Nil{}, Nil{}, 0n, best,
                                  SolveFast.dummy_step_zero(), False{}, False{},
                                  gres) : SolveFast.StepRes}, hbm)
                        case SolveFast.OneItem{fa, wa}:
                          Empty.absurd(
                            {SolveFast.step(1n+p, gs, 0n,
                               SolveFast.ClassItem{f, cws, wlen, tlb}
                               <> (SolveFast.OneItem{fa, wa} <> restb2),
                               gG, cwS, n, nodup, floor, inf, g, kids, sum,
                               best, SolveFast.dummy_step_zero(), True{},
                               False{}, gres)
                             == SolveFast.step(1n+p, gs, 0n, Nil{}, gG, cwS, n,
                                  nodup, floor, inf, Nil{}, Nil{}, 0n, best,
                                  SolveFast.dummy_step_zero(), False{}, False{},
                                  gres) : SolveFast.StepRes}, hbm)
                        case SolveFast.TwoItem{fa, wa1, wa2}:
                          Empty.absurd(
                            {SolveFast.step(1n+p, gs, 0n,
                               SolveFast.ClassItem{f, cws, wlen, tlb}
                               <> (SolveFast.TwoItem{fa, wa1, wa2} <> restb2),
                               gG, cwS, n, nodup, floor, inf, g, kids, sum,
                               best, SolveFast.dummy_step_zero(), True{},
                               False{}, gres)
                             == SolveFast.step(1n+p, gs, 0n, Nil{}, gG, cwS, n,
                                  nodup, floor, inf, Nil{}, Nil{}, 0n, best,
                                  SolveFast.dummy_step_zero(), False{}, False{},
                                  gres) : SolveFast.StepRes}, hbm)
                        case SolveFast.DoneItem{fa, tra, ca}:
                          Empty.absurd(
                            {SolveFast.step(1n+p, gs, 0n,
                               SolveFast.ClassItem{f, cws, wlen, tlb}
                               <> (SolveFast.DoneItem{fa, tra, ca} <> restb2),
                               gG, cwS, n, nodup, floor, inf, g, kids, sum,
                               best, SolveFast.dummy_step_zero(), True{},
                               False{}, gres)
                             == SolveFast.step(1n+p, gs, 0n, Nil{}, gG, cwS, n,
                                  nodup, floor, inf, Nil{}, Nil{}, 0n, best,
                                  SolveFast.dummy_step_zero(), False{}, False{},
                                  gres) : SolveFast.StepRes}, hbm)
                        case SolveFast.End{}:
                          Empty.absurd(
                            {SolveFast.step(1n+p, gs, 0n,
                               SolveFast.ClassItem{f, cws, wlen, tlb}
                               <> (SolveFast.End{} <> restb2),
                               gG, cwS, n, nodup, floor, inf, g, kids, sum,
                               best, SolveFast.dummy_step_zero(), True{},
                               False{}, gres)
                             == SolveFast.step(1n+p, gs, 0n, Nil{}, gG, cwS, n,
                                  nodup, floor, inf, Nil{}, Nil{}, 0n, best,
                                  SolveFast.dummy_step_zero(), False{}, False{},
                                  gres) : SolveFast.StepRes}, hbm)
                case SolveFast.Add{f2, tlb2}:
                  Empty.absurd(
                    {SolveFast.step(1n+p, gs, 0n,
                       SolveFast.Add{f2, tlb2} <> restb, gG, cwS, n, nodup,
                       floor, inf, g, kids, sum, best,
                       SolveFast.dummy_step_zero(), True{}, False{}, gres)
                     == SolveFast.step(1n+p, gs, 0n, Nil{}, gG, cwS, n, nodup,
                          floor, inf, Nil{}, Nil{}, 0n, best,
                          SolveFast.dummy_step_zero(), False{}, False{}, gres)
                     : SolveFast.StepRes}, hbm)
                case SolveFast.End{}:
                  Empty.absurd(
                    {SolveFast.step(1n+p, gs, 0n, SolveFast.End{} <> restb,
                       gG, cwS, n, nodup, floor, inf, g, kids, sum, best,
                       SolveFast.dummy_step_zero(), True{}, False{}, gres)
                     == SolveFast.step(1n+p, gs, 0n, Nil{}, gG, cwS, n, nodup,
                          floor, inf, Nil{}, Nil{}, 0n, best,
                          SolveFast.dummy_step_zero(), False{}, False{}, gres)
                     : SolveFast.StepRes}, hbm)

# Helper: advancing `B <= sum_ref + (c_lb + tlb)` across one child search
# `ref_c = Eval.cost_of(FS.ref_run_at(p, inf, G, ws))` when `c_lb <= ref_c`
# holds whenever `ref_c < inf`.
def FOpt.body_lb_step_go(+inf: Nat, +B: Nat, +sum_ref: Nat, +c_lb: Nat,
    +tlb: Nat, +ref_c: Nat, lt_inf: Bool,
    +elt: {lt_inf == Nat.is_lt(ref_c, inf) : Bool},
    +hB: {Nat.is_le(B, inf) == True{} : Bool},
    +hcur: {Nat.is_le(B, Nat.add(sum_ref, Nat.add(c_lb, tlb))) == True{} : Bool},
    hle_if: {Nat.is_lt(ref_c, inf) == True{} : Bool} ->
            {Nat.is_le(c_lb, ref_c) == True{} : Bool}) ->
  {Nat.is_le(B, Nat.add(SolveRef.sat_add(inf, sum_ref, ref_c), tlb))
   == True{} : Bool}:
  match lt_inf:
    case False{}:
      +hge : {Nat.is_ge(ref_c, inf) == True{} : Bool} =
        FVal.FV.ge_of_le(inf, ref_c,
          FC.FC.le_of_lt_false(ref_c, inf,
            Equal.sym(Bool, False{}, Nat.is_lt(ref_c, inf), elt)))
      +esat : {SolveRef.sat_add(inf, sum_ref, ref_c) == inf : Nat} =
        FOpt.sat_add_ge_r(inf, sum_ref, ref_c, hge)
      Fold.OQ.le_cong_r(B, Nat.add(inf, tlb),
        Nat.add(SolveRef.sat_add(inf, sum_ref, ref_c), tlb),
        Equal.cong(Nat, Nat, x => Nat.add(x, tlb), inf,
          SolveRef.sat_add(inf, sum_ref, ref_c),
          Equal.sym(Nat, SolveRef.sat_add(inf, sum_ref, ref_c), inf, esat)),
        NatProof.Nat.is_le_trans(B, inf, Nat.add(inf, tlb),
          hB, CBN.CB.is_le_add_self_r(inf, tlb)))
    case True{}:
      +hlt : {Nat.is_lt(ref_c, inf) == True{} : Bool} =
        Equal.sym(Bool, True{}, Nat.is_lt(ref_c, inf), elt)
      +hc : {Nat.is_le(c_lb, ref_c) == True{} : Bool} = hle_if(hlt)
      +hplain : {Nat.is_le(B, Nat.add(Nat.add(sum_ref, ref_c), tlb))
                 == True{} : Bool} =
        NatProof.Nat.is_le_trans(B,
          Nat.add(Nat.add(sum_ref, c_lb), tlb),
          Nat.add(Nat.add(sum_ref, ref_c), tlb),
          Fold.OQ.le_cong_r(B, Nat.add(sum_ref, Nat.add(c_lb, tlb)),
            Nat.add(Nat.add(sum_ref, c_lb), tlb),
            Equal.sym(Nat, Nat.add(Nat.add(sum_ref, c_lb), tlb),
              Nat.add(sum_ref, Nat.add(c_lb, tlb)),
              NatProof.NatPrf.add_assoc(sum_ref, c_lb, tlb)), hcur),
          NatProof.Nat.is_le_add_r(Nat.add(sum_ref, c_lb),
            Nat.add(sum_ref, ref_c), tlb,
            NatProof.Nat.is_le_add_l(c_lb, ref_c, sum_ref, hc)))
      FC.FC.le_sat_add_r(inf, sum_ref, ref_c, tlb, B, hB, hplain)

def FOpt.done_ws_le_ref(+ws: +List<+List<Nat>>, +p: Nat, +inf: Nat,
    +G: +List<+List<Nat>>, +tr: Tree.Tree, +c: Nat,
    +ble: {Nat.is_le(Groups.len_words(ws), p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h6: {Nat.is_lt(6n, inf) == True{} : Bool},
    +nd: {FN.FN.no_dup_ref(ws) == True{} : Bool},
    +hdws: {FH.FH.done_ws_ok_b(G, ws, tr, c) == True{} : Bool}) ->
  {Nat.is_le(c, Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, ws)))
   == True{} : Bool}:
  match ws:
    case Nil{}:
      Empty.absurd(
        {Nat.is_le(c, Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, Nil{})))
         == True{} : Bool}, Logic.Proof.false_ne_true(hdws))
    case Con{+w1, +t1}:
      match t1:
        case Nil{}:
          Empty.absurd(
            {Nat.is_le(c, Eval.Eval.cost_of(
               FS.FS.ref_run_at(p, inf, G, w1 <> Nil{}))) == True{} : Bool},
            Logic.Proof.false_ne_true(hdws))
        case Con{+w2, +t2}:
          match t2:
            case Nil{}:
              Empty.absurd(
                {Nat.is_le(c, Eval.Eval.cost_of(
                   FS.FS.ref_run_at(p, inf, G, w1 <> (w2 <> Nil{}))))
                 == True{} : Bool},
                Logic.Proof.false_ne_true(hdws))
            case Con{+w3, +t3}:
              match t3:
                case Nil{}:
                  FT3.FT3.done_three_le_ref(p, inf, G, w1, w2, w3, tr, c,
                    ble, hz, h6, nd, hdws)
                case Con{+w4, +t4}:
                  Empty.absurd(
                    {Nat.is_le(c, Eval.Eval.cost_of(
                       FS.FS.ref_run_at(p, inf, G,
                         w1 <> (w2 <> (w3 <> (w4 <> t4)))))) == True{} : Bool},
                    Logic.Proof.false_ne_true(hdws))

def FOpt.done_ws_valid_cost(+ws: +List<+List<Nat>>, +G: +List<+List<Nat>>,
    +tr: Tree.Tree, +c: Nat,
    +hdws: {FH.FH.done_ws_ok_b(G, ws, tr, c) == True{} : Bool}) ->
  {Bool.and(FVal.FV.valid_b(tr, G, ws), Nat.is_le(Tree.cost(tr, ws), c))
   == True{} : Bool}:
  match ws:
    case Nil{}:
      Empty.absurd(
        {Bool.and(FVal.FV.valid_b(tr, G, Nil{}), Nat.is_le(Tree.cost(tr, Nil{}), c))
         == True{} : Bool}, Logic.Proof.false_ne_true(hdws))
    case Con{+w1, +t1}:
      match t1:
        case Nil{}:
          Empty.absurd(
            {Bool.and(FVal.FV.valid_b(tr, G, w1 <> Nil{}),
               Nat.is_le(Tree.cost(tr, w1 <> Nil{}), c)) == True{} : Bool},
            Logic.Proof.false_ne_true(hdws))
        case Con{+w2, +t2}:
          match t2:
            case Nil{}:
              Empty.absurd(
                {Bool.and(FVal.FV.valid_b(tr, G, w1 <> (w2 <> Nil{})),
                   Nat.is_le(Tree.cost(tr, w1 <> (w2 <> Nil{})), c))
                 == True{} : Bool},
                Logic.Proof.false_ne_true(hdws))
            case Con{+w3, +t3}:
              match t3:
                case Nil{}:
                  +ws3 : +List<+List<Nat>> = w1 <> (w2 <> (w3 <> Nil{}))
                  FO.FO.bool_and_intro(FVal.FV.valid_b(tr, G, ws3),
                    Nat.is_le(Tree.cost(tr, ws3), c),
                    FT3.FT3.done_three_valid_b(G, w1, w2, w3, tr, c, hdws),
                    FT3.FT3.done_three_cost_le(G, w1, w2, w3, tr, c, hdws))
                case Con{+w4, +t4}:
                  +ws4 : +List<+List<Nat>> = w1 <> (w2 <> (w3 <> (w4 <> t4)))
                  Empty.absurd(
                    {Bool.and(FVal.FV.valid_b(tr, G, ws4),
                       Nat.is_le(Tree.cost(tr, ws4), c)) == True{} : Bool},
                    Logic.Proof.false_ne_true(hdws))

def FOpt.add_sub_eq(b: Nat, a: Nat,
    +h: {Nat.is_le(b, a) == True{} : Bool}) ->
  {Nat.add(b, Nat.sub(a, b)) == a : Nat}:
  match b a:
    case 0n _:
      FLB.FS.sub_zero(a)
    case 1n+bp 0n:
      Empty.absurd({Nat.add(1n+bp, Nat.sub(0n, 1n+bp)) == 0n : Nat},
        Logic.Proof.false_ne_true(h))
    case 1n+bp 1n+ap:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(bp, Nat.sub(ap, bp)), ap,
        FOpt.add_sub_eq(bp, ap, h))

def FOpt.add_sub_eq_r(+b: Nat, +a: Nat,
    +h: {Nat.is_le(b, a) == True{} : Bool}) ->
  {Nat.add(Nat.sub(a, b), b) == a : Nat}:
  Equal.trans(Nat, Nat.add(Nat.sub(a, b), b), Nat.add(b, Nat.sub(a, b)), a,
    NatProof.NatPrf.add_comm(Nat.sub(a, b), b), FOpt.add_sub_eq(b, a, h))

# Direct lower-bound theorem for `FH.tail_lb_ok_b`: whenever `B <= inf` and
# `B <= sum_ref + tlb_in` with `FH.tail_lb_ok_b(G, nodup, |S|, body, tlb_in)`
# for a body matching `groups`,
# `B <= Fold.OQ.ks_cost(inf, S, Eval.items(p, G, S, g, groups, Nil{}, sum_ref, inf))`.
def FOpt.body_lb_le_ks_cost(+groups: +List<Groups.Group>,
    +body: +List<SolveFast.Item>, +p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +C_root: +List<+List<Nat>>, +n_root: Nat, +has_buf: Bool,
    +S: +List<+List<Nat>>, +nodup: Bool, +g: +List<Nat>, +sum_ref: Nat,
    +B: Nat, +tlb_in: Nat,
    bounds: MV.MV.Bounds(p, MV.MV.next_groups(groups)),
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h3: {Nat.is_lt(3n, inf) == True{} : Bool},
    +h6: {Nat.is_lt(6n, inf) == True{} : Bool},
    +ng: {FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(groups))
          == True{} : Bool},
    +hB: {Nat.is_le(B, inf) == True{} : Bool},
    +hbm: FH.FH.BodyMatch(G, C_root, n_root, has_buf, nodup,
            Groups.len_words(S), groups, body),
    +htlb: {FH.FH.tail_lb_ok_b(G, nodup, Groups.len_words(S), body, tlb_in)
            == True{} : Bool},
    +hcur: {Nat.is_le(B, Nat.add(sum_ref, tlb_in)) == True{} : Bool}) ->
  {Nat.is_le(B, Fold.OQ.ks_cost(inf, S,
     Eval.Eval.items(p, G, S, g, groups, Nil{}, sum_ref, inf)))
   == True{} : Bool}:
  match groups:
    case Nil{}:
      +n : Nat = Groups.len_words(S)
      +heq_n : {Nat.is_eq(tlb_in, n) == True{} : Bool} =
        Equal.trans(Bool, Nat.is_eq(tlb_in, n),
          FH.FH.tail_lb_ok_b(G, nodup, n, body, tlb_in), True{},
          Equal.cong(+List<SolveFast.Item>, Bool,
            b => FH.FH.tail_lb_ok_b(G, nodup, n, b, tlb_in),
            SolveFast.End{} <> Nil{}, body,
            Equal.sym(+List<SolveFast.Item>, body, SolveFast.End{} <> Nil{},
              hbm)), htlb)
      +elb : {tlb_in == n : Nat} = NatProof.NatPrf.is_eq_true(tlb_in, n, heq_n)
      +hplain : {Nat.is_le(B, Nat.add(Nat.add(n, sum_ref), 0n)) == True{} : Bool} =
        Fold.OQ.le_cong_r(B, Nat.add(sum_ref, n),
          Nat.add(Nat.add(n, sum_ref), 0n),
          Equal.trans(Nat, Nat.add(sum_ref, n), Nat.add(n, sum_ref),
            Nat.add(Nat.add(n, sum_ref), 0n),
            NatProof.NatPrf.add_comm(sum_ref, n),
            Equal.sym(Nat, Nat.add(Nat.add(n, sum_ref), 0n), Nat.add(n, sum_ref),
              NatProof.NatPrf.add_zero(Nat.add(n, sum_ref)))),
          Fold.OQ.le_cong_r(B, Nat.add(sum_ref, tlb_in), Nat.add(sum_ref, n),
            Equal.cong(Nat, Nat, x => Nat.add(sum_ref, x), tlb_in, n, elb),
            hcur))
      Fold.OQ.le_cong_r(B, Nat.add(SolveRef.sat_add(inf, n, sum_ref), 0n),
        SolveRef.sat_add(inf, n, sum_ref),
        NatProof.NatPrf.add_zero(SolveRef.sat_add(inf, n, sum_ref)),
        FC.FC.le_sat_add_r(inf, n, sum_ref, 0n, B, hB, hplain))
    case Con{gp, restg}:
      match gp:
        case Groups.Group{+fb, +ws}:
          match body:
            case Nil{}:
              Empty.absurd(
                {Nat.is_le(B, Fold.OQ.ks_cost(inf, S,
                   Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg,
                     Nil{}, sum_ref, inf))) == True{} : Bool}, hbm)
            case Con{it, restb}:
              match it:
                case SolveFast.Begin{g2}:
                  Empty.absurd(
                    {Nat.is_le(B, Fold.OQ.ks_cost(inf, S,
                       Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg,
                         Nil{}, sum_ref, inf))) == True{} : Bool}, hbm)
                case SolveFast.OneItem{+f, +w}:
                  (+ble, bt) = bounds
                  +n : Nat = Groups.len_words(S)
                  +r1 = Arr.Arr.dpair_r({f == fb : +List<Feedback.Color>},
                          Arr.Arr.DPair<{ws == w <> Nil{} : +List<+List<Nat>>},
                            FH.FH.BodyMatch(G, C_root, n_root, has_buf, nodup,
                              n, restg, restb)>, hbm)
                  +ews = Arr.Arr.dpair_l({ws == w <> Nil{} : +List<+List<Nat>>},
                           FH.FH.BodyMatch(G, C_root, n_root, has_buf, nodup,
                             n, restg, restb), r1)
                  +hbm2 = Arr.Arr.dpair_r({ws == w <> Nil{} : +List<+List<Nat>>},
                            FH.FH.BodyMatch(G, C_root, n_root, has_buf, nodup,
                              n, restg, restb), r1)
                  +ngt = Logic.Proof.and_true_r(FN.FN.nodup_ok(nodup, ws),
                           FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(restg)),
                           ng)
                  +hle1 = Logic.Proof.and_true_l(Nat.is_le(1n, tlb_in),
                            FH.FH.tail_lb_ok_b(G, nodup, n, restb,
                              Nat.sub(tlb_in, 1n)), htlb)
                  +htlb2 = Logic.Proof.and_true_r(Nat.is_le(1n, tlb_in),
                             FH.FH.tail_lb_ok_b(G, nodup, n, restb,
                               Nat.sub(tlb_in, 1n)), htlb)
                  +hcur1 : {Nat.is_le(B,
                              Nat.add(sum_ref, Nat.add(1n, Nat.sub(tlb_in, 1n))))
                            == True{} : Bool} =
                    Fold.OQ.le_cong_r(B, Nat.add(sum_ref, tlb_in),
                      Nat.add(sum_ref, Nat.add(1n, Nat.sub(tlb_in, 1n))),
                      Equal.cong(Nat, Nat, x => Nat.add(sum_ref, x), tlb_in,
                        Nat.add(1n, Nat.sub(tlb_in, 1n)),
                        Equal.sym(Nat, Nat.add(1n, Nat.sub(tlb_in, 1n)), tlb_in,
                          FOpt.add_sub_eq(1n, tlb_in, hle1))), hcur)
                  +ref_c : Nat = Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, ws))
                  +sr : Nat = SolveRef.sat_add(inf, sum_ref, ref_c)
                  +hcur2 : {Nat.is_le(B, Nat.add(sr, Nat.sub(tlb_in, 1n)))
                            == True{} : Bool} =
                    FOpt.body_lb_step_go(inf, B, sum_ref, 1n,
                      Nat.sub(tlb_in, 1n), ref_c,
                      Nat.is_lt(ref_c, inf), {==}, hB, hcur1,
                      +hlt =>
                        +eclb : {1n == SolveFast.class_lb(ws) : Nat} =
                          Equal.trans(Nat, 1n, SolveFast.class_lb(w <> Nil{}),
                            SolveFast.class_lb(ws),
                            FN.FN.class_lb_nodup_eq(w <> Nil{}, {==}),
                            Equal.cong(+List<+List<Nat>>, Nat,
                              l => SolveFast.class_lb(l), w <> Nil{}, ws,
                              Equal.sym(+List<+List<Nat>>, ws, w <> Nil{}, ews)))
                        Fold.OQ.le_cong_l(1n, SolveFast.class_lb(ws), ref_c,
                          eclb, FLB.FS.child_size_le(p, inf, G, ws, ble, hz, hlt)))
                  Fold.OQ.le_cong_r(B,
                    Fold.OQ.ks_cost(inf, S,
                      Eval.Eval.items(p, G, S, g, restg, Nil{}, sr, inf)),
                    Fold.OQ.ks_cost(inf, S,
                      Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg,
                        Nil{}, sum_ref, inf)),
                    Equal.sym(Nat,
                      Fold.OQ.ks_cost(inf, S,
                        Eval.Eval.items(p, G, S, g,
                          Groups.Group{fb, ws} <> restg, Nil{}, sum_ref, inf)),
                      Fold.OQ.ks_cost(inf, S,
                        Eval.Eval.items(p, G, S, g, restg, Nil{}, sr, inf)),
                      FVal.FV.ks_cost_items_step(p, inf, G, S, g, fb, ws, restg,
                        sum_ref)),
                    FOpt.body_lb_le_ks_cost(restg, restb, p, inf, G, C_root,
                      n_root, has_buf, S, nodup, g, sr, B, Nat.sub(tlb_in, 1n),
                      bt, hz, h3, h6, ngt, hB, hbm2, htlb2, hcur2))
                case SolveFast.TwoItem{+f, +w1, +w2}:
                  (+ble, bt) = bounds
                  +n : Nat = Groups.len_words(S)
                  +end = Arr.Arr.dpair_l({nodup == True{} : Bool},
                           Arr.Arr.DPair<{f == fb : +List<Feedback.Color>},
                             Arr.Arr.DPair<
                               {ws == w1 <> (w2 <> Nil{}) : +List<+List<Nat>>},
                               FH.FH.BodyMatch(G, C_root, n_root, has_buf, nodup,
                                 n, restg, restb)>>, hbm)
                  +r1 = Arr.Arr.dpair_r({nodup == True{} : Bool},
                          Arr.Arr.DPair<{f == fb : +List<Feedback.Color>},
                            Arr.Arr.DPair<
                              {ws == w1 <> (w2 <> Nil{}) : +List<+List<Nat>>},
                              FH.FH.BodyMatch(G, C_root, n_root, has_buf, nodup,
                                n, restg, restb)>>, hbm)
                  +r2 = Arr.Arr.dpair_r({f == fb : +List<Feedback.Color>},
                          Arr.Arr.DPair<
                            {ws == w1 <> (w2 <> Nil{}) : +List<+List<Nat>>},
                            FH.FH.BodyMatch(G, C_root, n_root, has_buf, nodup,
                              n, restg, restb)>, r1)
                  +ews = Arr.Arr.dpair_l(
                           {ws == w1 <> (w2 <> Nil{}) : +List<+List<Nat>>},
                           FH.FH.BodyMatch(G, C_root, n_root, has_buf, nodup,
                             n, restg, restb), r2)
                  +hbm2 = Arr.Arr.dpair_r(
                            {ws == w1 <> (w2 <> Nil{}) : +List<+List<Nat>>},
                            FH.FH.BodyMatch(G, C_root, n_root, has_buf, nodup,
                              n, restg, restb), r2)
                  +ndh0 = Logic.Proof.and_true_l(FN.FN.nodup_ok(nodup, ws),
                            FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(restg)),
                            ng)
                  +ngt = Logic.Proof.and_true_r(FN.FN.nodup_ok(nodup, ws),
                           FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(restg)),
                           ng)
                  +ws2 : +List<+List<Nat>> = w1 <> (w2 <> Nil{})
                  +nd2 : {FN.FN.no_dup_ref(ws2) == True{} : Bool} =
                    Equal.trans(Bool, FN.FN.no_dup_ref(ws2),
                      FN.FN.nodup_ok(nodup, ws), True{},
                      Equal.trans(Bool, FN.FN.no_dup_ref(ws2),
                        FN.FN.nodup_ok(True{}, ws), FN.FN.nodup_ok(nodup, ws),
                        Equal.cong(+List<+List<Nat>>, Bool,
                          l => FN.FN.no_dup_ref(l), ws2, ws,
                          Equal.sym(+List<+List<Nat>>, ws, ws2, ews)),
                        Equal.cong(Bool, Bool, b => FN.FN.nodup_ok(b, ws),
                          True{}, nodup, Equal.sym(Bool, nodup, True{}, end))),
                      ndh0)
                  +ble2 : {Nat.is_le(2n, p) == True{} : Bool} =
                    Equal.trans(Bool, Nat.is_le(2n, p),
                      Nat.is_le(Groups.len_words(ws), p), True{},
                      Equal.cong(+List<+List<Nat>>, Bool,
                        l => Nat.is_le(Groups.len_words(l), p), ws2, ws,
                        Equal.sym(+List<+List<Nat>>, ws, ws2, ews)), ble)
                  +hle3 = Logic.Proof.and_true_l(Nat.is_le(3n, tlb_in),
                            FH.FH.tail_lb_ok_b(G, nodup, n, restb,
                              Nat.sub(tlb_in, 3n)), htlb)
                  +htlb2 = Logic.Proof.and_true_r(Nat.is_le(3n, tlb_in),
                             FH.FH.tail_lb_ok_b(G, nodup, n, restb,
                               Nat.sub(tlb_in, 3n)), htlb)
                  +hcur1 : {Nat.is_le(B,
                              Nat.add(sum_ref, Nat.add(3n, Nat.sub(tlb_in, 3n))))
                            == True{} : Bool} =
                    Fold.OQ.le_cong_r(B, Nat.add(sum_ref, tlb_in),
                      Nat.add(sum_ref, Nat.add(3n, Nat.sub(tlb_in, 3n))),
                      Equal.cong(Nat, Nat, x => Nat.add(sum_ref, x), tlb_in,
                        Nat.add(3n, Nat.sub(tlb_in, 3n)),
                        Equal.sym(Nat, Nat.add(3n, Nat.sub(tlb_in, 3n)), tlb_in,
                          FOpt.add_sub_eq(3n, tlb_in, hle3))), hcur)
                  +ref_c : Nat = Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, ws))
                  +sr : Nat = SolveRef.sat_add(inf, sum_ref, ref_c)
                  +hcur2 : {Nat.is_le(B, Nat.add(sr, Nat.sub(tlb_in, 3n)))
                            == True{} : Bool} =
                    FOpt.body_lb_step_go(inf, B, sum_ref, 3n,
                      Nat.sub(tlb_in, 3n), ref_c,
                      Nat.is_lt(ref_c, inf), {==}, hB, hcur1,
                      +hlt =>
                        Fold.OQ.le_cong_r(3n,
                          Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, ws2)),
                          ref_c,
                          Equal.cong(+List<+List<Nat>>, Nat,
                            l => Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, l)),
                            ws2, ws, Equal.sym(+List<+List<Nat>>, ws, ws2, ews)),
                          FVal.FV.three_le_ref_two(p, inf, G, w1, w2, ble2, hz,
                            h3, nd2)))
                  Fold.OQ.le_cong_r(B,
                    Fold.OQ.ks_cost(inf, S,
                      Eval.Eval.items(p, G, S, g, restg, Nil{}, sr, inf)),
                    Fold.OQ.ks_cost(inf, S,
                      Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg,
                        Nil{}, sum_ref, inf)),
                    Equal.sym(Nat,
                      Fold.OQ.ks_cost(inf, S,
                        Eval.Eval.items(p, G, S, g,
                          Groups.Group{fb, ws} <> restg, Nil{}, sum_ref, inf)),
                      Fold.OQ.ks_cost(inf, S,
                        Eval.Eval.items(p, G, S, g, restg, Nil{}, sr, inf)),
                      FVal.FV.ks_cost_items_step(p, inf, G, S, g, fb, ws, restg,
                        sum_ref)),
                    FOpt.body_lb_le_ks_cost(restg, restb, p, inf, G, C_root,
                      n_root, has_buf, S, nodup, g, sr, B, Nat.sub(tlb_in, 3n),
                      bt, hz, h3, h6, ngt, hB, hbm2, htlb2, hcur2))
                case SolveFast.DoneItem{+f, +tr, +c}:
                  (+ble, bt) = bounds
                  +n : Nat = Groups.len_words(S)
                  +end = Arr.Arr.dpair_l({nodup == True{} : Bool},
                           Arr.Arr.DPair<{f == fb : +List<Feedback.Color>},
                             Arr.Arr.DPair<
                               {FH.FH.done_ws_ok_b(G, ws, tr, c) == True{} : Bool},
                               FH.FH.BodyMatch(G, C_root, n_root, has_buf, nodup,
                                 n, restg, restb)>>, hbm)
                  +r1 = Arr.Arr.dpair_r({nodup == True{} : Bool},
                          Arr.Arr.DPair<{f == fb : +List<Feedback.Color>},
                            Arr.Arr.DPair<
                              {FH.FH.done_ws_ok_b(G, ws, tr, c) == True{} : Bool},
                              FH.FH.BodyMatch(G, C_root, n_root, has_buf, nodup,
                                n, restg, restb)>>, hbm)
                  +r2 = Arr.Arr.dpair_r({f == fb : +List<Feedback.Color>},
                          Arr.Arr.DPair<
                            {FH.FH.done_ws_ok_b(G, ws, tr, c) == True{} : Bool},
                            FH.FH.BodyMatch(G, C_root, n_root, has_buf, nodup,
                              n, restg, restb)>, r1)
                  +hdws = Arr.Arr.dpair_l(
                            {FH.FH.done_ws_ok_b(G, ws, tr, c) == True{} : Bool},
                            FH.FH.BodyMatch(G, C_root, n_root, has_buf, nodup,
                              n, restg, restb), r2)
                  +hbm2 = Arr.Arr.dpair_r(
                            {FH.FH.done_ws_ok_b(G, ws, tr, c) == True{} : Bool},
                            FH.FH.BodyMatch(G, C_root, n_root, has_buf, nodup,
                              n, restg, restb), r2)
                  +ndh0 = Logic.Proof.and_true_l(FN.FN.nodup_ok(nodup, ws),
                            FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(restg)),
                            ng)
                  +ngt = Logic.Proof.and_true_r(FN.FN.nodup_ok(nodup, ws),
                           FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(restg)),
                           ng)
                  +ndh : {FN.FN.no_dup_ref(ws) == True{} : Bool} =
                    Equal.trans(Bool, FN.FN.no_dup_ref(ws),
                      FN.FN.nodup_ok(nodup, ws), True{},
                      Equal.cong(Bool, Bool, b => FN.FN.nodup_ok(b, ws),
                        True{}, nodup, Equal.sym(Bool, nodup, True{}, end)),
                      ndh0)
                  +hlec = Logic.Proof.and_true_l(Nat.is_le(c, tlb_in),
                            FH.FH.tail_lb_ok_b(G, nodup, n, restb,
                              Nat.sub(tlb_in, c)), htlb)
                  +htlb2 = Logic.Proof.and_true_r(Nat.is_le(c, tlb_in),
                             FH.FH.tail_lb_ok_b(G, nodup, n, restb,
                               Nat.sub(tlb_in, c)), htlb)
                  +hcur1 : {Nat.is_le(B,
                              Nat.add(sum_ref, Nat.add(c, Nat.sub(tlb_in, c))))
                            == True{} : Bool} =
                    Fold.OQ.le_cong_r(B, Nat.add(sum_ref, tlb_in),
                      Nat.add(sum_ref, Nat.add(c, Nat.sub(tlb_in, c))),
                      Equal.cong(Nat, Nat, x => Nat.add(sum_ref, x), tlb_in,
                        Nat.add(c, Nat.sub(tlb_in, c)),
                        Equal.sym(Nat, Nat.add(c, Nat.sub(tlb_in, c)), tlb_in,
                          FOpt.add_sub_eq(c, tlb_in, hlec))), hcur)
                  +ref_c : Nat = Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, ws))
                  +sr : Nat = SolveRef.sat_add(inf, sum_ref, ref_c)
                  +hcur2 : {Nat.is_le(B, Nat.add(sr, Nat.sub(tlb_in, c)))
                            == True{} : Bool} =
                    FOpt.body_lb_step_go(inf, B, sum_ref, c,
                      Nat.sub(tlb_in, c), ref_c,
                      Nat.is_lt(ref_c, inf), {==}, hB, hcur1,
                      +hlt => FOpt.done_ws_le_ref(ws, p, inf, G, tr, c, ble,
                                hz, h6, ndh, hdws))
                  Fold.OQ.le_cong_r(B,
                    Fold.OQ.ks_cost(inf, S,
                      Eval.Eval.items(p, G, S, g, restg, Nil{}, sr, inf)),
                    Fold.OQ.ks_cost(inf, S,
                      Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg,
                        Nil{}, sum_ref, inf)),
                    Equal.sym(Nat,
                      Fold.OQ.ks_cost(inf, S,
                        Eval.Eval.items(p, G, S, g,
                          Groups.Group{fb, ws} <> restg, Nil{}, sum_ref, inf)),
                      Fold.OQ.ks_cost(inf, S,
                        Eval.Eval.items(p, G, S, g, restg, Nil{}, sr, inf)),
                      FVal.FV.ks_cost_items_step(p, inf, G, S, g, fb, ws, restg,
                        sum_ref)),
                    FOpt.body_lb_le_ks_cost(restg, restb, p, inf, G, C_root,
                      n_root, has_buf, S, nodup, g, sr, B, Nat.sub(tlb_in, c),
                      bt, hz, h3, h6, ngt, hB, hbm2, htlb2, hcur2))
                case SolveFast.ClassItem{+f, +cws, +wlen, +tlb}:
                  match restb:
                    case Nil{}:
                      Empty.absurd(
                        {Nat.is_le(B, Fold.OQ.ks_cost(inf, S,
                           Eval.Eval.items(p, G, S, g,
                             Groups.Group{fb, ws} <> restg, Nil{}, sum_ref, inf)))
                         == True{} : Bool}, hbm)
                    case Con{it2, restb2}:
                      match it2:
                        case SolveFast.Add{+f2, +tlb2}:
                          (+ble, bt) = bounds
                          +n : Nat = Groups.len_words(S)
                          +r1 = Arr.Arr.dpair_r({f == fb : +List<Feedback.Color>},
                                  Arr.Arr.DPair<{f2 == fb : +List<Feedback.Color>},
                                    Arr.Arr.DPair<
                                      {SolveFast.cwords_words(cws) == ws
                                       : +List<+List<Nat>>},
                                      Arr.Arr.DPair<{wlen == Groups.len_words(ws) : Nat},
                                        Arr.Arr.DPair<
                                          {FH.FH.cwords_ok_if(has_buf, G, C_root, n_root, cws)
                                           == True{} : Bool},
                                          Arr.Arr.DPair<
                                            {FH.FH.tail_lb_ok_b(G, nodup, n, restb2, tlb)
                                             == True{} : Bool},
                                            Arr.Arr.DPair<{tlb2 == tlb : Nat},
                                              FH.FH.BodyMatch(G, C_root, n_root,
                                                has_buf, nodup, n, restg, restb2)>>>>>>,
                                  hbm)
                          +r2 = Arr.Arr.dpair_r({f2 == fb : +List<Feedback.Color>},
                                  Arr.Arr.DPair<
                                    {SolveFast.cwords_words(cws) == ws
                                     : +List<+List<Nat>>},
                                    Arr.Arr.DPair<{wlen == Groups.len_words(ws) : Nat},
                                      Arr.Arr.DPair<
                                        {FH.FH.cwords_ok_if(has_buf, G, C_root, n_root, cws)
                                         == True{} : Bool},
                                        Arr.Arr.DPair<
                                          {FH.FH.tail_lb_ok_b(G, nodup, n, restb2, tlb)
                                           == True{} : Bool},
                                          Arr.Arr.DPair<{tlb2 == tlb : Nat},
                                            FH.FH.BodyMatch(G, C_root, n_root,
                                              has_buf, nodup, n, restg, restb2)>>>>>,
                                  r1)
                          +ecws = Arr.Arr.dpair_l(
                                    {SolveFast.cwords_words(cws) == ws
                                     : +List<+List<Nat>>},
                                    Arr.Arr.DPair<{wlen == Groups.len_words(ws) : Nat},
                                      Arr.Arr.DPair<
                                        {FH.FH.cwords_ok_if(has_buf, G, C_root, n_root, cws)
                                         == True{} : Bool},
                                        Arr.Arr.DPair<
                                          {FH.FH.tail_lb_ok_b(G, nodup, n, restb2, tlb)
                                           == True{} : Bool},
                                          Arr.Arr.DPair<{tlb2 == tlb : Nat},
                                            FH.FH.BodyMatch(G, C_root, n_root,
                                              has_buf, nodup, n, restg, restb2)>>>>,
                                    r2)
                          +r3 = Arr.Arr.dpair_r(
                                  {SolveFast.cwords_words(cws) == ws
                                   : +List<+List<Nat>>},
                                  Arr.Arr.DPair<{wlen == Groups.len_words(ws) : Nat},
                                    Arr.Arr.DPair<
                                      {FH.FH.cwords_ok_if(has_buf, G, C_root, n_root, cws)
                                       == True{} : Bool},
                                      Arr.Arr.DPair<
                                        {FH.FH.tail_lb_ok_b(G, nodup, n, restb2, tlb)
                                         == True{} : Bool},
                                        Arr.Arr.DPair<{tlb2 == tlb : Nat},
                                          FH.FH.BodyMatch(G, C_root, n_root,
                                            has_buf, nodup, n, restg, restb2)>>>>,
                                  r2)
                          +r4 = Arr.Arr.dpair_r({wlen == Groups.len_words(ws) : Nat},
                                  Arr.Arr.DPair<
                                    {FH.FH.cwords_ok_if(has_buf, G, C_root, n_root, cws)
                                     == True{} : Bool},
                                    Arr.Arr.DPair<
                                      {FH.FH.tail_lb_ok_b(G, nodup, n, restb2, tlb)
                                       == True{} : Bool},
                                      Arr.Arr.DPair<{tlb2 == tlb : Nat},
                                        FH.FH.BodyMatch(G, C_root, n_root,
                                          has_buf, nodup, n, restg, restb2)>>>,
                                  r3)
                          +r5 = Arr.Arr.dpair_r(
                                  {FH.FH.cwords_ok_if(has_buf, G, C_root, n_root, cws)
                                   == True{} : Bool},
                                  Arr.Arr.DPair<
                                    {FH.FH.tail_lb_ok_b(G, nodup, n, restb2, tlb)
                                     == True{} : Bool},
                                    Arr.Arr.DPair<{tlb2 == tlb : Nat},
                                      FH.FH.BodyMatch(G, C_root, n_root,
                                        has_buf, nodup, n, restg, restb2)>>,
                                  r4)
                          +htlb_sub = Arr.Arr.dpair_l(
                                        {FH.FH.tail_lb_ok_b(G, nodup, n, restb2, tlb)
                                         == True{} : Bool},
                                        Arr.Arr.DPair<{tlb2 == tlb : Nat},
                                          FH.FH.BodyMatch(G, C_root, n_root,
                                            has_buf, nodup, n, restg, restb2)>,
                                        r5)
                          +r6 = Arr.Arr.dpair_r(
                                  {FH.FH.tail_lb_ok_b(G, nodup, n, restb2, tlb)
                                   == True{} : Bool},
                                  Arr.Arr.DPair<{tlb2 == tlb : Nat},
                                    FH.FH.BodyMatch(G, C_root, n_root,
                                      has_buf, nodup, n, restg, restb2)>,
                                  r5)
                          +hbm2 = Arr.Arr.dpair_r({tlb2 == tlb : Nat},
                                    FH.FH.BodyMatch(G, C_root, n_root,
                                      has_buf, nodup, n, restg, restb2), r6)
                          +ngt = Logic.Proof.and_true_r(FN.FN.nodup_ok(nodup, ws),
                                   FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(restg)),
                                   ng)
                          +c_lb : Nat = Nat.sub(tlb_in, tlb)
                          +hle_t = Logic.Proof.and_true_l(Nat.is_le(tlb, tlb_in),
                                     LB2.LB2.clb_ok_b(G, nodup,
                                       SolveFast.cwords_words(cws), c_lb), htlb)
                          +hclb_cw = Logic.Proof.and_true_r(Nat.is_le(tlb, tlb_in),
                                       LB2.LB2.clb_ok_b(G, nodup,
                                         SolveFast.cwords_words(cws), c_lb), htlb)
                          +hclb : {LB2.LB2.clb_ok_b(G, nodup, ws, c_lb)
                                   == True{} : Bool} =
                            Equal.trans(Bool, LB2.LB2.clb_ok_b(G, nodup, ws, c_lb),
                              LB2.LB2.clb_ok_b(G, nodup,
                                SolveFast.cwords_words(cws), c_lb), True{},
                              Equal.cong(+List<+List<Nat>>, Bool,
                                l => LB2.LB2.clb_ok_b(G, nodup, l, c_lb),
                                ws, SolveFast.cwords_words(cws),
                                Equal.sym(+List<+List<Nat>>,
                                  SolveFast.cwords_words(cws), ws, ecws)),
                              hclb_cw)
                          +hcur1 : {Nat.is_le(B,
                                      Nat.add(sum_ref, Nat.add(c_lb, tlb)))
                                    == True{} : Bool} =
                            Fold.OQ.le_cong_r(B, Nat.add(sum_ref, tlb_in),
                              Nat.add(sum_ref, Nat.add(c_lb, tlb)),
                              Equal.cong(Nat, Nat, x => Nat.add(sum_ref, x),
                                tlb_in, Nat.add(c_lb, tlb),
                                Equal.sym(Nat, Nat.add(c_lb, tlb), tlb_in,
                                  FOpt.add_sub_eq_r(tlb, tlb_in, hle_t))), hcur)
                          +ref_c : Nat = Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, ws))
                          +sr : Nat = SolveRef.sat_add(inf, sum_ref, ref_c)
                          +hcur2 : {Nat.is_le(B, Nat.add(sr, tlb))
                                    == True{} : Bool} =
                            FOpt.body_lb_step_go(inf, B, sum_ref, c_lb, tlb,
                              ref_c, Nat.is_lt(ref_c, inf), {==}, hB, hcur1,
                              +hlt =>
                                LB2.LB2.child_lb_le_ref(p, inf, G, nodup, ws,
                                  c_lb, ble, hz, hlt, hclb))
                          Fold.OQ.le_cong_r(B,
                            Fold.OQ.ks_cost(inf, S,
                              Eval.Eval.items(p, G, S, g, restg, Nil{}, sr, inf)),
                            Fold.OQ.ks_cost(inf, S,
                              Eval.Eval.items(p, G, S, g,
                                Groups.Group{fb, ws} <> restg, Nil{}, sum_ref, inf)),
                            Equal.sym(Nat,
                              Fold.OQ.ks_cost(inf, S,
                                Eval.Eval.items(p, G, S, g,
                                  Groups.Group{fb, ws} <> restg, Nil{}, sum_ref, inf)),
                              Fold.OQ.ks_cost(inf, S,
                                Eval.Eval.items(p, G, S, g, restg, Nil{}, sr, inf)),
                              FVal.FV.ks_cost_items_step(p, inf, G, S, g, fb, ws,
                                restg, sum_ref)),
                            FOpt.body_lb_le_ks_cost(restg, restb2, p, inf, G,
                              C_root, n_root, has_buf, S, nodup, g, sr, B, tlb,
                              bt, hz, h3, h6, ngt, hB, hbm2, htlb_sub, hcur2))
                        case SolveFast.Begin{g2}:
                          Empty.absurd(
                            {Nat.is_le(B, Fold.OQ.ks_cost(inf, S,
                               Eval.Eval.items(p, G, S, g,
                                 Groups.Group{fb, ws} <> restg, Nil{}, sum_ref, inf)))
                             == True{} : Bool}, hbm)
                        case SolveFast.ClassItem{fa, ca, la, ta}:
                          Empty.absurd(
                            {Nat.is_le(B, Fold.OQ.ks_cost(inf, S,
                               Eval.Eval.items(p, G, S, g,
                                 Groups.Group{fb, ws} <> restg, Nil{}, sum_ref, inf)))
                             == True{} : Bool}, hbm)
                        case SolveFast.OneItem{fa, wa}:
                          Empty.absurd(
                            {Nat.is_le(B, Fold.OQ.ks_cost(inf, S,
                               Eval.Eval.items(p, G, S, g,
                                 Groups.Group{fb, ws} <> restg, Nil{}, sum_ref, inf)))
                             == True{} : Bool}, hbm)
                        case SolveFast.TwoItem{fa, wa1, wa2}:
                          Empty.absurd(
                            {Nat.is_le(B, Fold.OQ.ks_cost(inf, S,
                               Eval.Eval.items(p, G, S, g,
                                 Groups.Group{fb, ws} <> restg, Nil{}, sum_ref, inf)))
                             == True{} : Bool}, hbm)
                        case SolveFast.DoneItem{fa, tra, ca}:
                          Empty.absurd(
                            {Nat.is_le(B, Fold.OQ.ks_cost(inf, S,
                               Eval.Eval.items(p, G, S, g,
                                 Groups.Group{fb, ws} <> restg, Nil{}, sum_ref, inf)))
                             == True{} : Bool}, hbm)
                        case SolveFast.End{}:
                          Empty.absurd(
                            {Nat.is_le(B, Fold.OQ.ks_cost(inf, S,
                               Eval.Eval.items(p, G, S, g,
                                 Groups.Group{fb, ws} <> restg, Nil{}, sum_ref, inf)))
                             == True{} : Bool}, hbm)
                case SolveFast.Add{f2, tlb2}:
                  Empty.absurd(
                    {Nat.is_le(B, Fold.OQ.ks_cost(inf, S,
                       Eval.Eval.items(p, G, S, g,
                         Groups.Group{fb, ws} <> restg, Nil{}, sum_ref, inf)))
                     == True{} : Bool}, hbm)
                case SolveFast.End{}:
                  Empty.absurd(
                    {Nat.is_le(B, Fold.OQ.ks_cost(inf, S,
                       Eval.Eval.items(p, G, S, g,
                         Groups.Group{fb, ws} <> restg, Nil{}, sum_ref, inf)))
                     == True{} : Bool}, hbm)

# ---------------------------------------------------------------------------
# Single-guess step specification (`FOpt.StepRes`) and live-block invariants
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

def FOpt.sum_ref_ge(+B: Nat, +sum: Nat, +sum_ref: Nat) -> Bool:
  Bool.or(Nat.is_le(B, sum_ref), Nat.is_le(sum, sum_ref))

def FOpt.kids_inv(+B: Nat, +G: +List<+List<Nat>>,
    +done_rev: +List<Groups.Group>, +kids: +List<Tree.Child>, +sum: Nat) -> Bool:
  Bool.or(Nat.is_le(B, sum),
    Bool.and(FVal.FV.kids_match_b(G, done_rev, kids),
             Nat.is_le(FVal.FV.kids_cost_sum(done_rev, kids), sum)))

def FOpt.bool_or_l(a: Bool, b: Bool, +ha: {a == True{} : Bool}) ->
  {Bool.or(a, b) == True{} : Bool}:
  Equal.cong(Bool, Bool, x => Bool.or(x, b), a, True{}, ha)

def FOpt.bool_or_elim_r(+a: Bool, +b: Bool,
    +hor: {Bool.or(a, b) == True{} : Bool},
    +haf: {a == False{} : Bool}) -> {b == True{} : Bool}:
  Equal.trans(Bool, b, Bool.or(a, b), True{},
    Equal.sym(Bool, Bool.or(a, b), b,
      Equal.cong(Bool, Bool, x => Bool.or(x, b), a, False{}, haf)),
    hor)

def FOpt.sum_ref_ge_step_go(+inf: Nat, +B: Nat, +sum: Nat, +sum_ref: Nat,
    +k: Nat, +ref_c: Nat, le_sr: Bool,
    +ele: {le_sr == Nat.is_le(B, SolveRef.sat_add(inf, sum_ref, ref_c)) : Bool},
    +hB: {Nat.is_le(B, inf) == True{} : Bool},
    +hk: {Nat.is_le(k, ref_c) == True{} : Bool},
    +hprev: {FOpt.sum_ref_ge(B, sum, sum_ref) == True{} : Bool}) ->
  {FOpt.sum_ref_ge(B, SolveRef.sat_add(inf, sum, k),
     SolveRef.sat_add(inf, sum_ref, ref_c)) == True{} : Bool}:
  match le_sr:
    case True{}:
      +sr : Nat = SolveRef.sat_add(inf, sum_ref, ref_c)
      FOpt.bool_or_l(Nat.is_le(B, sr),
        Nat.is_le(SolveRef.sat_add(inf, sum, k), sr),
        Equal.sym(Bool, True{}, Nat.is_le(B, sr), ele))
    case False{}:
      +sf : Nat = SolveRef.sat_add(inf, sum, k)
      +sr : Nat = SolveRef.sat_add(inf, sum_ref, ref_c)
      +hlt_B : {Nat.is_lt(sr, B) == True{} : Bool} =
        FC.FC.lt_of_le_false(B, sr,
          Equal.sym(Bool, False{}, Nat.is_le(B, sr), ele))
      +hlt_inf : {Nat.is_lt(sr, inf) == True{} : Bool} =
        NatProof.Nat.is_lt_le_trans(sr, B, inf, hlt_B, hB)
      +hsumr_lt : {Nat.is_lt(sum_ref, inf) == True{} : Bool} =
        Sat.SB.sat_add_lt_l(inf, sum_ref, ref_c, hlt_inf)
      +href_lt : {Nat.is_lt(ref_c, inf) == True{} : Bool} =
        Sat.SB.sat_add_lt_r(inf, sum_ref, ref_c, hlt_inf)
      +esr : {sr == Nat.add(sum_ref, ref_c) : Nat} =
        OV.OV.sat_fin(inf, sum_ref, ref_c,
          OV.OV.ge_false_of_lt(sum_ref, inf, hsumr_lt),
          OV.OV.ge_false_of_lt(ref_c, inf, href_lt))
      +hsumr_lt_B : {Nat.is_lt(sum_ref, B) == True{} : Bool} =
        NatProof.Nat.is_le_lt_trans(sum_ref, sr, B,
          Fold.OQ.le_cong_r(sum_ref, Nat.add(sum_ref, ref_c), sr,
            Equal.sym(Nat, sr, Nat.add(sum_ref, ref_c), esr),
            CBN.CB.is_le_add_self_r(sum_ref, ref_c)),
          hlt_B)
      +hsum_le : {Nat.is_le(sum, sum_ref) == True{} : Bool} =
        FOpt.bool_or_elim_r(Nat.is_le(B, sum_ref), Nat.is_le(sum, sum_ref),
          hprev, FC.FC.le_false_of_lt(B, sum_ref, hsumr_lt_B))
      +hsum_lt : {Nat.is_lt(sum, inf) == True{} : Bool} =
        NatProof.Nat.is_le_lt_trans(sum, sum_ref, inf, hsum_le, hsumr_lt)
      +hk_lt : {Nat.is_lt(k, inf) == True{} : Bool} =
        NatProof.Nat.is_le_lt_trans(k, ref_c, inf, hk, href_lt)
      +esf : {sf == Nat.add(sum, k) : Nat} =
        OV.OV.sat_fin(inf, sum, k,
          OV.OV.ge_false_of_lt(sum, inf, hsum_lt),
          OV.OV.ge_false_of_lt(k, inf, hk_lt))
      +hle_sf : {Nat.is_le(sf, sr) == True{} : Bool} =
        Fold.OQ.le_cong_l(sf, Nat.add(sum, k), sr, esf,
          Fold.OQ.le_cong_r(Nat.add(sum, k), Nat.add(sum_ref, ref_c), sr,
            Equal.sym(Nat, sr, Nat.add(sum_ref, ref_c), esr),
            CBN.CB.is_le_add(sum, sum_ref, k, ref_c, hsum_le, hk)))
      FVal.FV.bool_or_r(Nat.is_le(B, sr), Nat.is_le(sf, sr), hle_sf)

def FOpt.sum_ref_ge_step(+inf: Nat, +B: Nat, +sum: Nat, +sum_ref: Nat,
    +k: Nat, +ref_c: Nat,
    +hB: {Nat.is_le(B, inf) == True{} : Bool},
    +hk: {Nat.is_le(k, ref_c) == True{} : Bool},
    +hprev: {FOpt.sum_ref_ge(B, sum, sum_ref) == True{} : Bool}) ->
  {FOpt.sum_ref_ge(B, SolveRef.sat_add(inf, sum, k),
     SolveRef.sat_add(inf, sum_ref, ref_c)) == True{} : Bool}:
  FOpt.sum_ref_ge_step_go(inf, B, sum, sum_ref, k, ref_c,
    Nat.is_le(B, SolveRef.sat_add(inf, sum_ref, ref_c)), {==}, hB, hk, hprev)

def FOpt.sum_ref_ge_end_go(+inf: Nat, +B: Nat, +n: Nat, +sum: Nat,
    +sum_ref: Nat, le_rc: Bool,
    +ele: {le_rc == Nat.is_le(B, SolveRef.sat_add(inf, n, sum_ref)) : Bool},
    +hB: {Nat.is_le(B, inf) == True{} : Bool},
    +hprev: {FOpt.sum_ref_ge(B, sum, sum_ref) == True{} : Bool}) ->
  {Bool.or(Nat.is_le(B, SolveRef.sat_add(inf, n, sum_ref)),
           Nat.is_le(SolveRef.sat_add(inf, n, sum),
             SolveRef.sat_add(inf, n, sum_ref))) == True{} : Bool}:
  match le_rc:
    case True{}:
      +rc : Nat = SolveRef.sat_add(inf, n, sum_ref)
      FOpt.bool_or_l(Nat.is_le(B, rc),
        Nat.is_le(SolveRef.sat_add(inf, n, sum), rc),
        Equal.sym(Bool, True{}, Nat.is_le(B, rc), ele))
    case False{}:
      +cc : Nat = SolveRef.sat_add(inf, n, sum)
      +rc : Nat = SolveRef.sat_add(inf, n, sum_ref)
      +hlt_B : {Nat.is_lt(rc, B) == True{} : Bool} =
        FC.FC.lt_of_le_false(B, rc,
          Equal.sym(Bool, False{}, Nat.is_le(B, rc), ele))
      +hlt_inf : {Nat.is_lt(rc, inf) == True{} : Bool} =
        NatProof.Nat.is_lt_le_trans(rc, B, inf, hlt_B, hB)
      +hn_lt : {Nat.is_lt(n, inf) == True{} : Bool} =
        Sat.SB.sat_add_lt_l(inf, n, sum_ref, hlt_inf)
      +hsumr_lt : {Nat.is_lt(sum_ref, inf) == True{} : Bool} =
        Sat.SB.sat_add_lt_r(inf, n, sum_ref, hlt_inf)
      +erc : {rc == Nat.add(n, sum_ref) : Nat} =
        OV.OV.sat_fin(inf, n, sum_ref,
          OV.OV.ge_false_of_lt(n, inf, hn_lt),
          OV.OV.ge_false_of_lt(sum_ref, inf, hsumr_lt))
      +hsumr_lt_B : {Nat.is_lt(sum_ref, B) == True{} : Bool} =
        NatProof.Nat.is_le_lt_trans(sum_ref, rc, B,
          Fold.OQ.le_cong_r(sum_ref, Nat.add(n, sum_ref), rc,
            Equal.sym(Nat, rc, Nat.add(n, sum_ref), erc),
            Fold.OQ.le_cong_r(sum_ref, Nat.add(sum_ref, n), Nat.add(n, sum_ref),
              NatProof.NatPrf.add_comm(sum_ref, n),
              CBN.CB.is_le_add_self_r(sum_ref, n))),
          hlt_B)
      +hsum_le : {Nat.is_le(sum, sum_ref) == True{} : Bool} =
        FOpt.bool_or_elim_r(Nat.is_le(B, sum_ref), Nat.is_le(sum, sum_ref),
          hprev, FC.FC.le_false_of_lt(B, sum_ref, hsumr_lt_B))
      +hsum_lt : {Nat.is_lt(sum, inf) == True{} : Bool} =
        NatProof.Nat.is_le_lt_trans(sum, sum_ref, inf, hsum_le, hsumr_lt)
      +ecc : {cc == Nat.add(n, sum) : Nat} =
        OV.OV.sat_fin(inf, n, sum,
          OV.OV.ge_false_of_lt(n, inf, hn_lt),
          OV.OV.ge_false_of_lt(sum, inf, hsum_lt))
      +hle_cc : {Nat.is_le(cc, rc) == True{} : Bool} =
        Fold.OQ.le_cong_l(cc, Nat.add(n, sum), rc, ecc,
          Fold.OQ.le_cong_r(Nat.add(n, sum), Nat.add(n, sum_ref), rc,
            Equal.sym(Nat, rc, Nat.add(n, sum_ref), erc),
            NatProof.Nat.is_le_add_l(sum, sum_ref, n, hsum_le)))
      FVal.FV.bool_or_r(Nat.is_le(B, rc), Nat.is_le(cc, rc), hle_cc)

def FOpt.kids_inv_step_go(+inf: Nat, +B: Nat, +G: +List<+List<Nat>>,
    +fb: +List<Feedback.Color>, +f: +List<Feedback.Color>,
    +ws: +List<+List<Nat>>, +tr: Tree.Tree, +k: Nat,
    +done_rev: +List<Groups.Group>, +kids: +List<Tree.Child>, +sum: Nat,
    lt_sf: Bool,
    +elt: {lt_sf == Nat.is_lt(SolveRef.sat_add(inf, sum, k), B) : Bool},
    +ef: {f == fb : +List<Feedback.Color>},
    +hB: {Nat.is_le(B, inf) == True{} : Bool},
    +hval: {FVal.FV.valid_b(tr, G, ws) == True{} : Bool},
    +hcost: {Nat.is_le(Tree.cost(tr, ws), k) == True{} : Bool},
    +hkids: {FOpt.kids_inv(B, G, done_rev, kids, sum) == True{} : Bool}) ->
  {FOpt.kids_inv(B, G, Groups.Group{fb, ws} <> done_rev,
     Tree.Child{f, tr} <> kids, SolveRef.sat_add(inf, sum, k)) == True{} : Bool}:
  match lt_sf:
    case False{}:
      +sf : Nat = SolveRef.sat_add(inf, sum, k)
      +hge : {Nat.is_le(B, sf) == True{} : Bool} =
        FC.FC.le_of_lt_false(sf, B,
          Equal.sym(Bool, False{}, Nat.is_lt(sf, B), elt))
      FOpt.bool_or_l(Nat.is_le(B, sf),
        Bool.and(
          FVal.FV.kids_match_b(G, Groups.Group{fb, ws} <> done_rev,
            Tree.Child{f, tr} <> kids),
          Nat.is_le(
            FVal.FV.kids_cost_sum(Groups.Group{fb, ws} <> done_rev,
              Tree.Child{f, tr} <> kids), sf)), hge)
    case True{}:
      +sf : Nat = SolveRef.sat_add(inf, sum, k)
      +hlt_B : {Nat.is_lt(sf, B) == True{} : Bool} =
        Equal.sym(Bool, True{}, Nat.is_lt(sf, B), elt)
      +hlt_inf : {Nat.is_lt(sf, inf) == True{} : Bool} =
        NatProof.Nat.is_lt_le_trans(sf, B, inf, hlt_B, hB)
      +hsum_lt_inf : {Nat.is_lt(sum, inf) == True{} : Bool} =
        Sat.SB.sat_add_lt_l(inf, sum, k, hlt_inf)
      +hk_lt_inf : {Nat.is_lt(k, inf) == True{} : Bool} =
        Sat.SB.sat_add_lt_r(inf, sum, k, hlt_inf)
      +esf : {sf == Nat.add(sum, k) : Nat} =
        OV.OV.sat_fin(inf, sum, k,
          OV.OV.ge_false_of_lt(sum, inf, hsum_lt_inf),
          OV.OV.ge_false_of_lt(k, inf, hk_lt_inf))
      +hsum_lt_B : {Nat.is_lt(sum, B) == True{} : Bool} =
        NatProof.Nat.is_le_lt_trans(sum, sf, B,
          Fold.OQ.le_cong_r(sum, Nat.add(sum, k), sf,
            Equal.sym(Nat, sf, Nat.add(sum, k), esf),
            CBN.CB.is_le_add_self_r(sum, k)), hlt_B)
      +hpair : {Bool.and(FVal.FV.kids_match_b(G, done_rev, kids),
                  Nat.is_le(FVal.FV.kids_cost_sum(done_rev, kids), sum))
                == True{} : Bool} =
        FOpt.bool_or_elim_r(Nat.is_le(B, sum),
          Bool.and(FVal.FV.kids_match_b(G, done_rev, kids),
            Nat.is_le(FVal.FV.kids_cost_sum(done_rev, kids), sum)),
          hkids, FC.FC.le_false_of_lt(B, sum, hsum_lt_B))
      +hm = Logic.Proof.and_true_l(FVal.FV.kids_match_b(G, done_rev, kids),
              Nat.is_le(FVal.FV.kids_cost_sum(done_rev, kids), sum), hpair)
      +hcs = Logic.Proof.and_true_r(FVal.FV.kids_match_b(G, done_rev, kids),
               Nat.is_le(FVal.FV.kids_cost_sum(done_rev, kids), sum), hpair)
      +hfbeq : {Feedback.feedback_eq(fb, f) == True{} : Bool} =
        Equal.trans(Bool, Feedback.feedback_eq(fb, f),
          Feedback.feedback_eq(fb, fb), True{},
          Equal.cong(+List<Feedback.Color>, Bool,
            x => Feedback.feedback_eq(fb, x), f, fb, ef),
          FbProof.FbPrf.feedback_eq_refl(fb))
      +hm2 : {FVal.FV.kids_match_b(G, Groups.Group{fb, ws} <> done_rev,
                Tree.Child{f, tr} <> kids) == True{} : Bool} =
        FO.FO.bool_and_intro(Feedback.feedback_eq(fb, f),
          Bool.and(FVal.FV.valid_b(tr, G, ws),
            FVal.FV.kids_match_b(G, done_rev, kids)),
          hfbeq,
          FO.FO.bool_and_intro(FVal.FV.valid_b(tr, G, ws),
            FVal.FV.kids_match_b(G, done_rev, kids), hval, hm))
      +hcs2 : {Nat.is_le(
                 FVal.FV.kids_cost_sum(Groups.Group{fb, ws} <> done_rev,
                   Tree.Child{f, tr} <> kids), sf) == True{} : Bool} =
        Fold.OQ.le_cong_r(
          Nat.add(Tree.cost(tr, ws), FVal.FV.kids_cost_sum(done_rev, kids)),
          Nat.add(sum, k), sf,
          Equal.sym(Nat, sf, Nat.add(sum, k), esf),
          Fold.OQ.le_cong_r(
            Nat.add(Tree.cost(tr, ws), FVal.FV.kids_cost_sum(done_rev, kids)),
            Nat.add(k, sum), Nat.add(sum, k),
            NatProof.NatPrf.add_comm(k, sum),
            CBN.CB.is_le_add(Tree.cost(tr, ws), k,
              FVal.FV.kids_cost_sum(done_rev, kids), sum, hcost, hcs)))
      FVal.FV.bool_or_r(Nat.is_le(B, sf),
        Bool.and(
          FVal.FV.kids_match_b(G, Groups.Group{fb, ws} <> done_rev,
            Tree.Child{f, tr} <> kids),
          Nat.is_le(
            FVal.FV.kids_cost_sum(Groups.Group{fb, ws} <> done_rev,
              Tree.Child{f, tr} <> kids), sf)),
        FO.FO.bool_and_intro(
          FVal.FV.kids_match_b(G, Groups.Group{fb, ws} <> done_rev,
            Tree.Child{f, tr} <> kids),
          Nat.is_le(
            FVal.FV.kids_cost_sum(Groups.Group{fb, ws} <> done_rev,
              Tree.Child{f, tr} <> kids), sf), hm2, hcs2))

def FOpt.kids_inv_step(+inf: Nat, +B: Nat, +G: +List<+List<Nat>>,
    +fb: +List<Feedback.Color>, +f: +List<Feedback.Color>,
    +ws: +List<+List<Nat>>, +tr: Tree.Tree, +k: Nat,
    +done_rev: +List<Groups.Group>, +kids: +List<Tree.Child>, +sum: Nat,
    +ef: {f == fb : +List<Feedback.Color>},
    +hB: {Nat.is_le(B, inf) == True{} : Bool},
    +hval: {FVal.FV.valid_b(tr, G, ws) == True{} : Bool},
    +hcost: {Nat.is_le(Tree.cost(tr, ws), k) == True{} : Bool},
    +hkids: {FOpt.kids_inv(B, G, done_rev, kids, sum) == True{} : Bool}) ->
  {FOpt.kids_inv(B, G, Groups.Group{fb, ws} <> done_rev,
     Tree.Child{f, tr} <> kids, SolveRef.sat_add(inf, sum, k)) == True{} : Bool}:
  FOpt.kids_inv_step_go(inf, B, G, fb, f, ws, tr, k, done_rev, kids, sum,
    Nat.is_lt(SolveRef.sat_add(inf, sum, k), B), {==}, ef, hB, hval, hcost,
    hkids)

def FOpt.StepRes(+p: Nat, +gs: SolveFast.GList, +G: +List<+List<Nat>>,
    +C_root: +List<+List<Nat>>, +n_root: Nat, +has_buf: Bool,
    +gG: SolveFast.GList, +cwS: +List<SolveFast.CWord>, +S: +List<+List<Nat>>,
    +nodup: Bool, +floor: Nat, +inf: Nat,
    +g: +List<Nat>, +cs: +List<SolveFast.Item>, +kids: +List<Tree.Child>,
    +sum: Nat, +best: SolveRef.Best, -buf: SolveFast.Buf5,
    +limit: Nat, +target: Nat) -> Type:
  &best2: SolveRef.Best ->
  &buf2: SolveFast.Buf5 ->
    {SolveFast.step(1n+p, gs, 0n, cs, gG, cwS, Groups.len_words(S),
       nodup, floor, inf, g, kids, sum, best, SolveFast.dummy_step_zero(),
       False{}, False{}, SolveFast.GuessRes{Nil{}, buf})
     == SolveFast.step(1n+p, gs, 0n, Nil{}, gG, cwS, Groups.len_words(S),
          nodup, floor, inf, Nil{}, Nil{}, 0n, best2,
          SolveFast.dummy_step_zero(), False{},
          SolveFast.is_floor_hit(nodup, floor, best2),
          SolveFast.GuessRes{Nil{}, buf2})
     : SolveFast.StepRes}
    & FH.FH.BufOk(G, C_root, n_root, has_buf, nodup, buf2)
    & {FVal.FV.best_ok_b(limit, G, S, best2) == True{} : Bool}
    & {Nat.is_le(Eval.Eval.cost_of(best2), Eval.Eval.cost_of(best))
       == True{} : Bool}
    & {Nat.is_le(Eval.Eval.cost_of(best2), target) == True{} : Bool}

def FOpt.step_res_pre(+p: Nat, +gs: SolveFast.GList, +G: +List<+List<Nat>>,
    +C_root: +List<+List<Nat>>, +n_root: Nat, +has_buf: Bool,
    +gG: SolveFast.GList, +cwS: +List<SolveFast.CWord>, +S: +List<+List<Nat>>,
    +nodup: Bool, +floor: Nat, +inf: Nat,
    +g1: +List<Nat>, +cs1: +List<SolveFast.Item>, +k1: +List<Tree.Child>,
    +s1: Nat, -b1: SolveFast.Buf5,
    +g2: +List<Nat>, +cs2: +List<SolveFast.Item>, +k2: +List<Tree.Child>,
    +s2: Nat, -b2: SolveFast.Buf5,
    +best: SolveRef.Best, +limit: Nat, +t1: Nat, +t2: Nat,
    +estep: {SolveFast.step(1n+p, gs, 0n, cs1, gG, cwS, Groups.len_words(S),
               nodup, floor, inf, g1, k1, s1, best, SolveFast.dummy_step_zero(),
               False{}, False{}, SolveFast.GuessRes{Nil{}, b1})
             == SolveFast.step(1n+p, gs, 0n, cs2, gG, cwS, Groups.len_words(S),
                  nodup, floor, inf, g2, k2, s2, best,
                  SolveFast.dummy_step_zero(), False{}, False{},
                  SolveFast.GuessRes{Nil{}, b2})
             : SolveFast.StepRes},
    +ht: {Nat.is_le(t1, t2) == True{} : Bool},
    r: FOpt.StepRes(p, gs, G, C_root, n_root, has_buf, gG, cwS, S, nodup,
         floor, inf, g2, cs2, k2, s2, best, b2, limit, t1)) ->
  FOpt.StepRes(p, gs, G, C_root, n_root, has_buf, gG, cwS, S, nodup,
    floor, inf, g1, cs1, k1, s1, best, b1, limit, t2):
  match r:
    case Tuple{+best2, p0}:
      match p0:
        case Tuple{buf2, p1}:
          match p1:
            case Tuple{+eq2, p2}:
              match p2:
                case Tuple{+hbuf2, p3}:
                  match p3:
                    case Tuple{+hok2, p4}:
                      match p4:
                        case Tuple{+hleb, hlet}:
                          +n : Nat = Groups.len_words(S)
                          Tuple{best2,
                            Tuple{buf2,
                              Tuple{
                                Equal.trans(SolveFast.StepRes,
                                  SolveFast.step(1n+p, gs, 0n, cs1, gG, cwS, n,
                                    nodup, floor, inf, g1, k1, s1, best,
                                    SolveFast.dummy_step_zero(), False{},
                                    False{}, SolveFast.GuessRes{Nil{}, b1}),
                                  SolveFast.step(1n+p, gs, 0n, cs2, gG, cwS, n,
                                    nodup, floor, inf, g2, k2, s2, best,
                                    SolveFast.dummy_step_zero(), False{},
                                    False{}, SolveFast.GuessRes{Nil{}, b2}),
                                  SolveFast.step(1n+p, gs, 0n, Nil{}, gG, cwS, n,
                                    nodup, floor, inf, Nil{}, Nil{}, 0n, best2,
                                    SolveFast.dummy_step_zero(), False{},
                                    SolveFast.is_floor_hit(nodup, floor, best2),
                                    SolveFast.GuessRes{Nil{}, buf2}),
                                  estep, eq2),
                                Tuple{hbuf2,
                                  Tuple{hok2,
                                    Tuple{hleb,
                                      NatProof.Nat.is_le_trans(
                                        Eval.Eval.cost_of(best2), t1, t2,
                                        hlet, ht)}}}}}}

def FOpt.step_res_keep(+p: Nat, +gs: SolveFast.GList, +G: +List<+List<Nat>>,
    +C_root: +List<+List<Nat>>, +n_root: Nat, +has_buf: Bool,
    +gG: SolveFast.GList, +cwS: +List<SolveFast.CWord>, +S: +List<+List<Nat>>,
    +nodup: Bool, +floor: Nat, +inf: Nat,
    +best: SolveRef.Best, buf: SolveFast.Buf5, +limit: Nat, +target: Nat,
    +hbuf: FH.FH.BufOk(G, C_root, n_root, has_buf, nodup, buf),
    +hok: {FVal.FV.best_ok_b(limit, G, S, best) == True{} : Bool},
    +hd: {SolveFast.is_floor_hit(nodup, floor, best) == False{} : Bool},
    +ht: {Nat.is_le(Eval.Eval.cost_of(best), target) == True{} : Bool}) ->
  FOpt.StepRes(p, gs, G, C_root, n_root, has_buf, gG, cwS, S, nodup,
    floor, inf, Nil{}, Nil{}, Nil{}, 0n, best, buf, limit, target):
  +n : Nat = Groups.len_words(S)
  Tuple{best,
    Tuple{buf,
      Tuple{
        Equal.cong(Bool, SolveFast.StepRes,
          dn => SolveFast.step(1n+p, gs, 0n, Nil{}, gG, cwS, n, nodup, floor,
                  inf, Nil{}, Nil{}, 0n, best, SolveFast.dummy_step_zero(),
                  False{}, dn, SolveFast.GuessRes{Nil{}, buf}),
          False{}, SolveFast.is_floor_hit(nodup, floor, best),
          Equal.sym(Bool, SolveFast.is_floor_hit(nodup, floor, best),
            False{}, hd)),
        Tuple{hbuf,
          Tuple{hok,
            Tuple{NatProof.Nat.is_le_refl(Eval.Eval.cost_of(best)), ht}}}}}}

# ---------------------------------------------------------------------------
# Stepping a live block (`End`, `OneItem`, `TwoItem`, `DoneItem`, `ClassItem`+`Add`)
# ---------------------------------------------------------------------------

def FOpt.live_group_end_ok(+G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +inf: Nat, +g: +List<Nat>, +done_rev: +List<Groups.Group>,
    +kids: +List<Tree.Child>, +sum: Nat, +best: SolveRef.Best, +limit: Nat,
    lt_cand: Bool,
    +elt: {lt_cand == Nat.is_lt(SolveRef.sat_add(inf, Groups.len_words(S), sum),
                        Eval.Eval.cost_of(best)) : Bool},
    +wg: {Tree.member_word(g, G) == True{} : Bool},
    +perm: FP.FP.Perm,
    +hperm: FP.FP.PermOk(perm, Groups.groups_build(g, S, Nil{}),
              FVal.FV.rev_groups(done_rev, Nil{})),
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    +hok: {FVal.FV.best_ok_b(limit, G, S, best) == True{} : Bool},
    +hkids: {FOpt.kids_inv(Eval.Eval.cost_of(best), G, done_rev, kids, sum)
             == True{} : Bool}) ->
  {FVal.FV.best_ok_b(limit, G, S,
     SolveRef.finish_guess(inf, g, kids, sum, Groups.len_words(S), best))
   == True{} : Bool}:
  match lt_cand:
    case False{}:
      +n : Nat = Groups.len_words(S)
      +cc : Nat = SolveRef.sat_add(inf, n, sum)
      +ct : Tree.Tree = Tree.Node{g, SolveRef.rev_kids(kids, Nil{})}
      +hge : {Nat.is_le(Eval.Eval.cost_of(best), cc) == True{} : Bool} =
        FC.FC.le_of_lt_false(cc, Eval.Eval.cost_of(best),
          Equal.sym(Bool, False{}, Nat.is_lt(cc, Eval.Eval.cost_of(best)), elt))
      +eb : {SolveRef.better(cc, ct, best) == best : SolveRef.Best} =
        FB.FS.keep(cc, ct, best, Eval.Eval.cost_of(best),
          NatProof.Nat.is_le_refl(Eval.Eval.cost_of(best)), hge)
      Equal.trans(Bool,
        FVal.FV.best_ok_b(limit, G, S, SolveRef.better(cc, ct, best)),
        FVal.FV.best_ok_b(limit, G, S, best), True{},
        Equal.cong(SolveRef.Best, Bool,
          b => FVal.FV.best_ok_b(limit, G, S, b),
          SolveRef.better(cc, ct, best), best, eb),
        hok)
    case True{}:
      +n : Nat = Groups.len_words(S)
      +B : Nat = Eval.Eval.cost_of(best)
      +cc : Nat = SolveRef.sat_add(inf, n, sum)
      +ct : Tree.Tree = Tree.Node{g, SolveRef.rev_kids(kids, Nil{})}
      +hlt_B : {Nat.is_lt(cc, B) == True{} : Bool} =
        Equal.sym(Bool, True{}, Nat.is_lt(cc, B), elt)
      +hlt_inf : {Nat.is_lt(cc, inf) == True{} : Bool} =
        NatProof.Nat.is_lt_le_trans(cc, B, inf, hlt_B, hbest)
      +hn_lt : {Nat.is_lt(n, inf) == True{} : Bool} =
        Sat.SB.sat_add_lt_l(inf, n, sum, hlt_inf)
      +hsum_lt_inf : {Nat.is_lt(sum, inf) == True{} : Bool} =
        Sat.SB.sat_add_lt_r(inf, n, sum, hlt_inf)
      +ecc : {cc == Nat.add(n, sum) : Nat} =
        OV.OV.sat_fin(inf, n, sum,
          OV.OV.ge_false_of_lt(n, inf, hn_lt),
          OV.OV.ge_false_of_lt(sum, inf, hsum_lt_inf))
      +hsum_lt_B : {Nat.is_lt(sum, B) == True{} : Bool} =
        NatProof.Nat.is_le_lt_trans(sum, cc, B,
          Fold.OQ.le_cong_r(sum, Nat.add(n, sum), cc,
            Equal.sym(Nat, cc, Nat.add(n, sum), ecc),
            Fold.OQ.le_cong_r(sum, Nat.add(sum, n), Nat.add(n, sum),
              NatProof.NatPrf.add_comm(sum, n),
              CBN.CB.is_le_add_self_r(sum, n))),
          hlt_B)
      +hpair : {Bool.and(FVal.FV.kids_match_b(G, done_rev, kids),
                  Nat.is_le(FVal.FV.kids_cost_sum(done_rev, kids), sum))
                == True{} : Bool} =
        FOpt.bool_or_elim_r(Nat.is_le(B, sum),
          Bool.and(FVal.FV.kids_match_b(G, done_rev, kids),
            Nat.is_le(FVal.FV.kids_cost_sum(done_rev, kids), sum)),
          hkids, FC.FC.le_false_of_lt(B, sum, hsum_lt_B))
      +hm = Logic.Proof.and_true_l(FVal.FV.kids_match_b(G, done_rev, kids),
              Nat.is_le(FVal.FV.kids_cost_sum(done_rev, kids), sum), hpair)
      +hcs = Logic.Proof.and_true_r(FVal.FV.kids_match_b(G, done_rev, kids),
               Nat.is_le(FVal.FV.kids_cost_sum(done_rev, kids), sum), hpair)
      +hend : {Bool.and(FVal.FV.valid_b(ct, G, S),
                 Nat.is_le(Tree.cost(ct, S), Nat.add(n, sum)))
               == True{} : Bool} =
        FVal.FV.end_node_ok_perm(G, S, g, done_rev, kids, sum, wg, perm, hperm,
          hm, hcs)
      +hvalid = Logic.Proof.and_true_l(FVal.FV.valid_b(ct, G, S),
                  Nat.is_le(Tree.cost(ct, S), Nat.add(n, sum)), hend)
      +hcost : {Nat.is_le(Tree.cost(ct, S), cc) == True{} : Bool} =
        Fold.OQ.le_cong_r(Tree.cost(ct, S), Nat.add(n, sum), cc,
          Equal.sym(Nat, cc, Nat.add(n, sum), ecc),
          Logic.Proof.and_true_r(FVal.FV.valid_b(ct, G, S),
            Nat.is_le(Tree.cost(ct, S), Nat.add(n, sum)), hend))
      FVal.FV.best_ok_better(limit, G, S, cc, ct, best, hvalid, hcost, hok)

def FOpt.better_le_ref_end(+cc: Nat, +ct: Tree.Tree, +best: SolveRef.Best,
    +rc: Nat, le_rc: Bool,
    +ele: {le_rc == Nat.is_le(Eval.Eval.cost_of(best), rc) : Bool},
    +hor: {Bool.or(Nat.is_le(Eval.Eval.cost_of(best), rc),
                   Nat.is_le(cc, rc)) == True{} : Bool}) ->
  {Nat.is_le(Eval.Eval.cost_of(SolveRef.better(cc, ct, best)), rc)
   == True{} : Bool}:
  match le_rc:
    case True{}:
      NatProof.Nat.is_le_trans(
        Eval.Eval.cost_of(SolveRef.better(cc, ct, best)),
        Eval.Eval.cost_of(best), rc,
        Fold.OQ.better_le_best(cc, ct, best),
        Equal.sym(Bool, True{}, Nat.is_le(Eval.Eval.cost_of(best), rc), ele))
    case False{}:
      +hcc : {Nat.is_le(cc, rc) == True{} : Bool} =
        FOpt.bool_or_elim_r(Nat.is_le(Eval.Eval.cost_of(best), rc),
          Nat.is_le(cc, rc), hor,
          Equal.sym(Bool, False{}, Nat.is_le(Eval.Eval.cost_of(best), rc), ele))
      NatProof.Nat.is_le_trans(
        Eval.Eval.cost_of(SolveRef.better(cc, ct, best)), cc, rc,
        Fold.OQ.better_le_cand(cc, ct, best), hcc)

def FOpt.live_group_end(+p: Nat, +gs: SolveFast.GList, +G: +List<+List<Nat>>,
    +C_root: +List<+List<Nat>>, +n_root: Nat, +has_buf: Bool,
    +gG: SolveFast.GList, +cwS: +List<SolveFast.CWord>, +S: +List<+List<Nat>>,
    +nodup: Bool, +floor: Nat, +inf: Nat, +g: +List<Nat>,
    +done_rev: +List<Groups.Group>, +kids: +List<Tree.Child>, +sum: Nat,
    +sum_ref: Nat, +best: SolveRef.Best, buf: SolveFast.Buf5, +limit: Nat,
    +hbuf: FH.FH.BufOk(G, C_root, n_root, has_buf, nodup, buf),
    +wg: {Tree.member_word(g, G) == True{} : Bool},
    +perm: FP.FP.Perm,
    +hperm: FP.FP.PermOk(perm, Groups.groups_build(g, S, Nil{}),
              FVal.FV.rev_groups(done_rev, Nil{})),
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    +hok: {FVal.FV.best_ok_b(limit, G, S, best) == True{} : Bool},
    +hsum_ge: {FOpt.sum_ref_ge(Eval.Eval.cost_of(best), sum, sum_ref)
               == True{} : Bool},
    +hkids: {FOpt.kids_inv(Eval.Eval.cost_of(best), G, done_rev, kids, sum)
             == True{} : Bool}) ->
  FOpt.StepRes(p, gs, G, C_root, n_root, has_buf, gG, cwS, S, nodup, floor, inf,
    g, SolveFast.End{} <> Nil{}, kids, sum, best, buf, limit,
    Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g, Nil{}, Nil{}, sum_ref, inf))):
  +n : Nat = Groups.len_words(S)
  +B : Nat = Eval.Eval.cost_of(best)
  +cc : Nat = SolveRef.sat_add(inf, n, sum)
  +rc : Nat = SolveRef.sat_add(inf, n, sum_ref)
  +ct : Tree.Tree = Tree.Node{g, SolveRef.rev_kids(kids, Nil{})}
  +best2 : SolveRef.Best = SolveRef.finish_guess(inf, g, kids, sum, n, best)
  +hor : {Bool.or(Nat.is_le(B, rc), Nat.is_le(cc, rc)) == True{} : Bool} =
    FOpt.sum_ref_ge_end_go(inf, B, n, sum, sum_ref, Nat.is_le(B, rc), {==},
      hbest, hsum_ge)
  Tuple{best2,
    Tuple{buf,
      Tuple{
        FS.FS.end_step(p, gs, gG, cwS, n, nodup, floor, inf, g, kids, sum, best,
          SolveFast.dummy_step_zero(), Nil{}, False{},
          SolveFast.GuessRes{Nil{}, buf}),
        Tuple{hbuf,
          Tuple{
            FOpt.live_group_end_ok(G, S, inf, g, done_rev, kids, sum, best,
              limit, Nat.is_lt(cc, B), {==}, wg, perm, hperm, hbest, hok, hkids),
            Tuple{
              Fold.OQ.better_le_best(cc, ct, best),
              FOpt.better_le_ref_end(cc, ct, best, rc, Nat.is_le(B, rc), {==},
                hor)}}}}}}

# Shared helper for `OneItem`, `TwoItem`, and `DoneItem` (cost `k`, tree `tr`).
def FOpt.live_group_leaf(+p: Nat, +gs: SolveFast.GList, +G: +List<+List<Nat>>,
    +C_root: +List<+List<Nat>>, +n_root: Nat, +has_buf: Bool,
    +gG: SolveFast.GList, +cwS: +List<SolveFast.CWord>, +S: +List<+List<Nat>>,
    +nodup: Bool, +floor: Nat, +inf: Nat, +g: +List<Nat>,
    +fb: +List<Feedback.Color>, +f: +List<Feedback.Color>,
    +ws: +List<+List<Nat>>, +restg: +List<Groups.Group>,
    +it: SolveFast.Item, +restb: +List<SolveFast.Item>,
    +tr: Tree.Tree, +k: Nat,
    +done_rev: +List<Groups.Group>, +kids: +List<Tree.Child>, +sum: Nat,
    +sum_ref: Nat, +best: SolveRef.Best, buf: SolveFast.Buf5, +limit: Nat,
    +hbuf: FH.FH.BufOk(G, C_root, n_root, has_buf, nodup, buf),
    +estep: {SolveFast.step(1n+p, gs, 0n, it <> restb, gG, cwS,
               Groups.len_words(S), nodup, floor, inf, g, kids, sum, best,
               SolveFast.dummy_step_zero(), False{}, False{},
               SolveFast.GuessRes{Nil{}, buf})
             == SolveFast.step(1n+p, gs, 0n, restb, gG, cwS,
                  Groups.len_words(S), nodup, floor, inf, g,
                  Tree.Child{f, tr} <> kids, SolveRef.sat_add(inf, sum, k),
                  best, SolveFast.dummy_step_zero(), False{}, False{},
                  SolveFast.GuessRes{Nil{}, buf}) : SolveFast.StepRes},
    +ef: {f == fb : +List<Feedback.Color>},
    +hB: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    +hval: {FVal.FV.valid_b(tr, G, ws) == True{} : Bool},
    +hcost: {Nat.is_le(Tree.cost(tr, ws), k) == True{} : Bool},
    +hk_ref: {Nat.is_le(k, Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, ws)))
              == True{} : Bool},
    +hsum_ge: {FOpt.sum_ref_ge(Eval.Eval.cost_of(best), sum, sum_ref)
               == True{} : Bool},
    +hkids: {FOpt.kids_inv(Eval.Eval.cost_of(best), G, done_rev, kids, sum)
             == True{} : Bool},
    rec_live:
      @buf_in: SolveFast.Buf5 ->
      FH.FH.BufOk(G, C_root, n_root, has_buf, nodup, buf_in) ->
      {FOpt.sum_ref_ge(Eval.Eval.cost_of(best),
         SolveRef.sat_add(inf, sum, k),
         SolveRef.sat_add(inf, sum_ref,
           Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, ws)))) == True{} : Bool} ->
      {FOpt.kids_inv(Eval.Eval.cost_of(best), G,
         Groups.Group{fb, ws} <> done_rev,
         Tree.Child{f, tr} <> kids,
         SolveRef.sat_add(inf, sum, k)) == True{} : Bool} ->
      FOpt.StepRes(p, gs, G, C_root, n_root, has_buf, gG, cwS, S, nodup,
        floor, inf, g, restb, Tree.Child{f, tr} <> kids,
        SolveRef.sat_add(inf, sum, k), best, buf_in, limit,
        Fold.OQ.ks_cost(inf, S,
          Eval.Eval.items(p, G, S, g, restg, Nil{},
            SolveRef.sat_add(inf, sum_ref,
              Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, ws))), inf)))) ->
  FOpt.StepRes(p, gs, G, C_root, n_root, has_buf, gG, cwS, S, nodup,
    floor, inf, g, it <> restb, kids, sum, best, buf, limit,
    Fold.OQ.ks_cost(inf, S,
      Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg, Nil{},
        sum_ref, inf))):
  +B : Nat = Eval.Eval.cost_of(best)
  +ref_c : Nat = Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, ws))
  +sf : Nat = SolveRef.sat_add(inf, sum, k)
  +sr : Nat = SolveRef.sat_add(inf, sum_ref, ref_c)
  +hsum2 = FOpt.sum_ref_ge_step(inf, B, sum, sum_ref, k, ref_c, hB, hk_ref,
             hsum_ge)
  +hkids2 = FOpt.kids_inv_step(inf, B, G, fb, f, ws, tr, k, done_rev, kids,
              sum, ef, hB, hval, hcost, hkids)
  +ek_step = FVal.FV.ks_cost_items_step(p, inf, G, S, g, fb, ws, restg, sum_ref)
  FOpt.step_res_pre(p, gs, G, C_root, n_root, has_buf, gG, cwS, S, nodup,
    floor, inf, g, it <> restb, kids, sum, buf,
    g, restb, Tree.Child{f, tr} <> kids, sf, buf,
    best, limit,
    Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g, restg, Nil{}, sr, inf)),
    Fold.OQ.ks_cost(inf, S,
      Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg, Nil{},
        sum_ref, inf)),
    estep,
    NatProof.Nat.is_le_eq_r(
      Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g, restg, Nil{}, sr, inf)),
      Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g, restg, Nil{}, sr, inf)),
      Fold.OQ.ks_cost(inf, S,
        Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg, Nil{},
          sum_ref, inf)),
      Equal.sym(Nat,
        Fold.OQ.ks_cost(inf, S,
          Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg, Nil{},
            sum_ref, inf)),
        Fold.OQ.ks_cost(inf, S,
          Eval.Eval.items(p, G, S, g, restg, Nil{}, sr, inf)), ek_step),
      NatProof.Nat.is_le_refl(
        Fold.OQ.ks_cost(inf, S,
          Eval.Eval.items(p, G, S, g, restg, Nil{}, sr, inf)))),
    rec_live(buf, hbuf, hsum2, hkids2))

def FOpt.le_sr_tlb_of_ge(+B: Nat, +sf: Nat, +sr: Nat, +tlb: Nat, le_sr: Bool,
    +ele: {le_sr == Nat.is_le(B, sr) : Bool},
    +hge_sf: {Nat.is_le(B, Nat.add(sf, tlb)) == True{} : Bool},
    +hsum2: {FOpt.sum_ref_ge(B, sf, sr) == True{} : Bool}) ->
  {Nat.is_le(B, Nat.add(sr, tlb)) == True{} : Bool}:
  match le_sr:
    case True{}:
      NatProof.Nat.is_le_trans(B, sr, Nat.add(sr, tlb),
        Equal.sym(Bool, True{}, Nat.is_le(B, sr), ele),
        CBN.CB.is_le_add_self_r(sr, tlb))
    case False{}:
      +hsf_le : {Nat.is_le(sf, sr) == True{} : Bool} =
        FOpt.bool_or_elim_r(Nat.is_le(B, sr), Nat.is_le(sf, sr), hsum2,
          Equal.sym(Bool, False{}, Nat.is_le(B, sr), ele))
      NatProof.Nat.is_le_trans(B, Nat.add(sf, tlb), Nat.add(sr, tlb),
        hge_sf, NatProof.Nat.is_le_add_r(sf, sr, tlb, hsf_le))

def FOpt.live_group_class_sk(+p: Nat, +gs: SolveFast.GList,
    +G: +List<+List<Nat>>, +C_root: +List<+List<Nat>>, +n_root: Nat,
    +has_buf: Bool, +gG: SolveFast.GList, +cwS: +List<SolveFast.CWord>,
    +S: +List<+List<Nat>>, +nodup: Bool, +floor: Nat, +inf: Nat,
    +g: +List<Nat>, +fb: +List<Feedback.Color>, +f: +List<Feedback.Color>,
    +f2: +List<Feedback.Color>, +ws: +List<+List<Nat>>,
    +cws: +List<SolveFast.CWord>, +wlen: Nat, +tlb: Nat, +tlb2: Nat,
    +restg: +List<Groups.Group>, +restb2: +List<SolveFast.Item>,
    +done_rev: +List<Groups.Group>, +kids: +List<Tree.Child>, +sum: Nat,
    +sum_ref: Nat, +best: SolveRef.Best, -b1a: SolveFast.Buf5,
    +search: SolveRef.Best, buf2: SolveFast.Buf5, +limit: Nat,
    sk: Bool,
    +esk: {sk == SolveFast.skippable(best,
                   Nat.add(SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(search)),
                     tlb)) : Bool},
    bt: MV.MV.Bounds(p, MV.MV.next_groups(restg)),
    +ef2: {f2 == fb : +List<Feedback.Color>},
    +etlb: {FH.FH.tail_lb_ok_b(G, nodup, Groups.len_words(S), restb2, tlb)
            == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h3: {Nat.is_lt(3n, inf) == True{} : Bool},
    +h6: {Nat.is_lt(6n, inf) == True{} : Bool},
    +ngt: {FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(restg)) == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    +hok: {FVal.FV.best_ok_b(limit, G, S, best) == True{} : Bool},
    +hd: {SolveFast.is_floor_hit(nodup, floor, best) == False{} : Bool},
    +hsum_ge: {FOpt.sum_ref_ge(Eval.Eval.cost_of(best), sum, sum_ref)
               == True{} : Bool},
    +hkids: {FOpt.kids_inv(Eval.Eval.cost_of(best), G, done_rev, kids, sum)
             == True{} : Bool},
    +hbm2: FH.FH.BodyMatch(G, C_root, n_root, has_buf, nodup,
             Groups.len_words(S), restg, restb2),
    +hbuf2: FH.FH.BufOk(G, C_root, n_root, has_buf, nodup, buf2),
    +hsearch: {FOpt.job_res_b(p, inf, G, ws,
                 FS.FS.child_cutoff(best, sum, tlb), search) == True{} : Bool},
    +e_step_sk: {SolveFast.step(1n+p, gs, 0n,
                   SolveFast.ClassItem{f, cws, wlen, tlb}
                   <> (SolveFast.Add{f2, tlb2} <> restb2),
                   gG, cwS, Groups.len_words(S), nodup, floor, inf, g, kids,
                   sum, best, SolveFast.dummy_step_zero(), False{}, False{},
                   SolveFast.GuessRes{Nil{}, b1a})
                 == SolveFast.step(1n+p, gs, 0n, restb2, gG, cwS,
                      Groups.len_words(S), nodup, floor, inf, g,
                      Tree.Child{f2, Eval.Eval.tree_of(search)} <> kids,
                      SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(search)),
                      best, SolveFast.dummy_step_zero(),
                      SolveFast.skippable(best,
                        Nat.add(SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(search)),
                          tlb)),
                      False{}, SolveFast.GuessRes{Nil{}, buf2})
                 : SolveFast.StepRes},
    rec_live:
      @search_in: SolveRef.Best ->
      @buf_in: SolveFast.Buf5 ->
      FH.FH.BufOk(G, C_root, n_root, has_buf, nodup, buf_in) ->
      {FOpt.sum_ref_ge(Eval.Eval.cost_of(best),
         SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(search_in)),
         SolveRef.sat_add(inf, sum_ref,
           Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, ws)))) == True{} : Bool} ->
      {FOpt.kids_inv(Eval.Eval.cost_of(best), G,
         Groups.Group{fb, ws} <> done_rev,
         Tree.Child{f2, Eval.Eval.tree_of(search_in)} <> kids,
         SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(search_in))) == True{} : Bool} ->
      FOpt.StepRes(p, gs, G, C_root, n_root, has_buf, gG, cwS, S, nodup,
        floor, inf, g, restb2,
        Tree.Child{f2, Eval.Eval.tree_of(search_in)} <> kids,
        SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(search_in)),
        best, buf_in, limit,
        Fold.OQ.ks_cost(inf, S,
          Eval.Eval.items(p, G, S, g, restg, Nil{},
            SolveRef.sat_add(inf, sum_ref,
              Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, ws))), inf)))) ->
  FOpt.StepRes(p, gs, G, C_root, n_root, has_buf, gG, cwS, S, nodup, floor, inf,
    g, SolveFast.ClassItem{f, cws, wlen, tlb}
       <> (SolveFast.Add{f2, tlb2} <> restb2),
    kids, sum, best, b1a, limit,
    Fold.OQ.ks_cost(inf, S,
      Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg,
        Nil{}, sum_ref, inf))):
  match sk:
    case False{}:
      +n : Nat = Groups.len_words(S)
      +B : Nat = Eval.Eval.cost_of(best)
      +cut : Nat = FS.FS.child_cutoff(best, sum, tlb)
      +ref_c : Nat = Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, ws))
      +sc : Nat = Eval.Eval.cost_of(search)
      +sf : Nat = SolveRef.sat_add(inf, sum, sc)
      +sr : Nat = SolveRef.sat_add(inf, sum_ref, ref_c)
      +cs1 : +List<SolveFast.Item> =
        SolveFast.ClassItem{f, cws, wlen, tlb}
        <> (SolveFast.Add{f2, tlb2} <> restb2)
      +kf : +List<Tree.Child> = Tree.Child{f2, Eval.Eval.tree_of(search)} <> kids
      +hok_c = Logic.Proof.and_true_l(FVal.FV.best_ok_b(cut, G, ws, search),
                 Bool.and(Nat.is_le(sc, cut), Nat.is_le(sc, ref_c)), hsearch)
      +hr_c = Logic.Proof.and_true_r(FVal.FV.best_ok_b(cut, G, ws, search),
                Bool.and(Nat.is_le(sc, cut), Nat.is_le(sc, ref_c)), hsearch)
      +hle_ref = Logic.Proof.and_true_r(Nat.is_le(sc, cut), Nat.is_le(sc, ref_c),
                   hr_c)
      +esk_f : {SolveFast.skippable(best, Nat.add(sf, tlb)) == False{} : Bool} =
        Equal.sym(Bool, False{}, SolveFast.skippable(best, Nat.add(sf, tlb)), esk)
      +hlt_sft : {Nat.is_lt(Nat.add(sf, tlb), B) == True{} : Bool} =
        FOpt.lt_of_skippable_false(best, Nat.add(sf, tlb), esk_f)
      +hlt_sf_B : {Nat.is_lt(sf, B) == True{} : Bool} =
        NatProof.Nat.is_le_lt_trans(sf, Nat.add(sf, tlb), B,
          CBN.CB.is_le_add_self_r(sf, tlb), hlt_sft)
      +hlt_sf_inf : {Nat.is_lt(sf, inf) == True{} : Bool} =
        NatProof.Nat.is_lt_le_trans(sf, B, inf, hlt_sf_B, hbest)
      +esf : {sf == Nat.add(sum, sc) : Nat} =
        OV.OV.sat_fin(inf, sum, sc,
          OV.OV.ge_false_of_lt(sum, inf, Sat.SB.sat_add_lt_l(inf, sum, sc, hlt_sf_inf)),
          OV.OV.ge_false_of_lt(sc, inf, Sat.SB.sat_add_lt_r(inf, sum, sc, hlt_sf_inf)))
      +hlt_reg : {Nat.is_lt(Nat.add(Nat.add(sum, tlb), sc), B) == True{} : Bool} =
        CBN.CB.lt_eq_l(B, Nat.add(sf, tlb), Nat.add(Nat.add(sum, tlb), sc),
          Equal.trans(Nat, Nat.add(sf, tlb), Nat.add(Nat.add(sum, sc), tlb),
            Nat.add(Nat.add(sum, tlb), sc),
            Equal.cong(Nat, Nat, x => Nat.add(x, tlb), sf, Nat.add(sum, sc), esf),
            FC.FC.regroup_sum(sum, sc, tlb)), hlt_sft)
      +hlt_sub : {Nat.is_lt(sc, Nat.sub(B, Nat.add(sum, tlb))) == True{} : Bool} =
        FOpt.lt_sub_of_add_lt(Nat.add(sum, tlb), sc, B, hlt_reg)
      +cut_eq : {cut == Nat.sub(B, Nat.add(sum, tlb)) : Nat} =
        Equal.cong(Nat, Nat, x => Nat.sub(x, Nat.add(sum, tlb)),
          SolveFast.best_cost(best), B, FLB.FS.best_cost_eq(best))
      +hlt_cut : {Nat.is_lt(sc, cut) == True{} : Bool} =
        Equal.trans(Bool, Nat.is_lt(sc, cut),
          Nat.is_lt(sc, Nat.sub(B, Nat.add(sum, tlb))), True{},
          Equal.cong(Nat, Bool, x => Nat.is_lt(sc, x),
            cut, Nat.sub(B, Nat.add(sum, tlb)), cut_eq), hlt_sub)
      +hext = FVal.FV.best_ok_extract(cut, G, ws, search, hok_c, hlt_cut)
      +hv_c = Logic.Proof.and_true_l(
                FVal.FV.valid_b(Eval.Eval.tree_of(search), G, ws),
                Nat.is_le(Tree.cost(Eval.Eval.tree_of(search), ws), sc), hext)
      +hc_c = Logic.Proof.and_true_r(
                FVal.FV.valid_b(Eval.Eval.tree_of(search), G, ws),
                Nat.is_le(Tree.cost(Eval.Eval.tree_of(search), ws), sc), hext)
      +hsum2 = FOpt.sum_ref_ge_step(inf, B, sum, sum_ref, sc, ref_c, hbest,
                 hle_ref, hsum_ge)
      +hkids2 = FOpt.kids_inv_step(inf, B, G, fb, f2, ws,
                  Eval.Eval.tree_of(search), sc, done_rev, kids, sum, ef2,
                  hbest, hv_c, hc_c, hkids)
      +e_step : {SolveFast.step(1n+p, gs, 0n, cs1, gG, cwS, n, nodup, floor,
                   inf, g, kids, sum, best, SolveFast.dummy_step_zero(), False{},
                   False{}, SolveFast.GuessRes{Nil{}, b1a})
                 == SolveFast.step(1n+p, gs, 0n, restb2, gG, cwS, n, nodup,
                      floor, inf, g, kf, sf, best, SolveFast.dummy_step_zero(),
                      False{}, False{}, SolveFast.GuessRes{Nil{}, buf2})
                 : SolveFast.StepRes} =
        Equal.trans(SolveFast.StepRes,
          SolveFast.step(1n+p, gs, 0n, cs1, gG, cwS, n, nodup, floor, inf, g,
            kids, sum, best, SolveFast.dummy_step_zero(), False{}, False{},
            SolveFast.GuessRes{Nil{}, b1a}),
          SolveFast.step(1n+p, gs, 0n, restb2, gG, cwS, n, nodup, floor, inf, g,
            kf, sf, best, SolveFast.dummy_step_zero(),
            SolveFast.skippable(best, Nat.add(sf, tlb)), False{},
            SolveFast.GuessRes{Nil{}, buf2}),
          SolveFast.step(1n+p, gs, 0n, restb2, gG, cwS, n, nodup, floor, inf, g,
            kf, sf, best, SolveFast.dummy_step_zero(), False{}, False{},
            SolveFast.GuessRes{Nil{}, buf2}),
          e_step_sk,
          Equal.cong(Bool, SolveFast.StepRes,
            sk0 => SolveFast.step(1n+p, gs, 0n, restb2, gG, cwS, n, nodup,
                     floor, inf, g, kf, sf, best, SolveFast.dummy_step_zero(),
                     sk0, False{}, SolveFast.GuessRes{Nil{}, buf2}),
            SolveFast.skippable(best, Nat.add(sf, tlb)), False{}, esk_f))
      +ek_step = FVal.FV.ks_cost_items_step(p, inf, G, S, g, fb, ws, restg, sum_ref)
      FOpt.step_res_pre(p, gs, G, C_root, n_root, has_buf, gG, cwS, S, nodup,
        floor, inf, g, cs1, kids, sum, b1a, g, restb2, kf, sf, buf2, best, limit,
        Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g, restg, Nil{}, sr, inf)),
        Fold.OQ.ks_cost(inf, S,
          Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg, Nil{},
            sum_ref, inf)),
        e_step,
        NatProof.Nat.is_le_eq_r(
          Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g, restg, Nil{}, sr, inf)),
          Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g, restg, Nil{}, sr, inf)),
          Fold.OQ.ks_cost(inf, S,
            Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg, Nil{},
              sum_ref, inf)),
          Equal.sym(Nat,
            Fold.OQ.ks_cost(inf, S,
              Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg, Nil{},
                sum_ref, inf)),
            Fold.OQ.ks_cost(inf, S,
              Eval.Eval.items(p, G, S, g, restg, Nil{}, sr, inf)), ek_step),
          NatProof.Nat.is_le_refl(
            Fold.OQ.ks_cost(inf, S,
              Eval.Eval.items(p, G, S, g, restg, Nil{}, sr, inf)))),
        rec_live(search, buf2, hbuf2, hsum2, hkids2))
    case True{}:
      +n : Nat = Groups.len_words(S)
      +B : Nat = Eval.Eval.cost_of(best)
      +cut : Nat = FS.FS.child_cutoff(best, sum, tlb)
      +ref_c : Nat = Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, ws))
      +sc : Nat = Eval.Eval.cost_of(search)
      +sf : Nat = SolveRef.sat_add(inf, sum, sc)
      +sr : Nat = SolveRef.sat_add(inf, sum_ref, ref_c)
      +cs1 : +List<SolveFast.Item> =
        SolveFast.ClassItem{f, cws, wlen, tlb}
        <> (SolveFast.Add{f2, tlb2} <> restb2)
      +kf : +List<Tree.Child> = Tree.Child{f2, Eval.Eval.tree_of(search)} <> kids
      +hr_c = Logic.Proof.and_true_r(FVal.FV.best_ok_b(cut, G, ws, search),
                Bool.and(Nat.is_le(sc, cut), Nat.is_le(sc, ref_c)), hsearch)
      +hle_ref = Logic.Proof.and_true_r(Nat.is_le(sc, cut), Nat.is_le(sc, ref_c),
                   hr_c)
      +esk_t : {SolveFast.skippable(best, Nat.add(sf, tlb)) == True{} : Bool} =
        Equal.sym(Bool, True{}, SolveFast.skippable(best, Nat.add(sf, tlb)), esk)
      +hge_sf : {Nat.is_le(B, Nat.add(sf, tlb)) == True{} : Bool} =
        FLB.FS.skippable_to_le(best, Nat.add(sf, tlb), esk_t)
      +hsum2 = FOpt.sum_ref_ge_step(inf, B, sum, sum_ref, sc, ref_c, hbest,
                 hle_ref, hsum_ge)
      +hge_sr_tlb : {Nat.is_le(B, Nat.add(sr, tlb)) == True{} : Bool} =
        FOpt.le_sr_tlb_of_ge(B, sf, sr, tlb, Nat.is_le(B, sr), {==}, hge_sf,
          hsum2)
      +hb_le_r : {Nat.is_le(B, Fold.OQ.ks_cost(inf, S,
                    Eval.Eval.items(p, G, S, g, restg, Nil{}, sr, inf)))
                  == True{} : Bool} =
        FOpt.body_lb_le_ks_cost(restg, restb2, p, inf, G, C_root, n_root,
          has_buf, S, nodup, g, sr, B, tlb, bt, hz, h3, h6, ngt, hbest, hbm2,
          etlb, hge_sr_tlb)
      +ek_step = FVal.FV.ks_cost_items_step(p, inf, G, S, g, fb, ws, restg, sum_ref)
      +hb_le_full : {Nat.is_le(B, Fold.OQ.ks_cost(inf, S,
                       Eval.Eval.items(p, G, S, g,
                         Groups.Group{fb, ws} <> restg, Nil{}, sum_ref, inf)))
                     == True{} : Bool} =
        Fold.OQ.le_cong_r(B,
          Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g, restg, Nil{}, sr, inf)),
          Fold.OQ.ks_cost(inf, S,
            Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg, Nil{},
              sum_ref, inf)),
          Equal.sym(Nat,
            Fold.OQ.ks_cost(inf, S,
              Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg, Nil{},
                sum_ref, inf)),
            Fold.OQ.ks_cost(inf, S,
              Eval.Eval.items(p, G, S, g, restg, Nil{}, sr, inf)), ek_step),
          hb_le_r)
      +e_dead : {SolveFast.step(1n+p, gs, 0n, cs1, gG, cwS, n, nodup, floor,
                   inf, g, kids, sum, best, SolveFast.dummy_step_zero(), False{},
                   False{}, SolveFast.GuessRes{Nil{}, b1a})
                 == SolveFast.step(1n+p, gs, 0n, Nil{}, gG, cwS, n, nodup,
                      floor, inf, Nil{}, Nil{}, 0n, best,
                      SolveFast.dummy_step_zero(), False{}, False{},
                      SolveFast.GuessRes{Nil{}, buf2}) : SolveFast.StepRes} =
        Equal.trans(SolveFast.StepRes,
          SolveFast.step(1n+p, gs, 0n, cs1, gG, cwS, n, nodup, floor, inf, g,
            kids, sum, best, SolveFast.dummy_step_zero(), False{}, False{},
            SolveFast.GuessRes{Nil{}, b1a}),
          SolveFast.step(1n+p, gs, 0n, restb2, gG, cwS, n, nodup, floor, inf, g,
            kf, sf, best, SolveFast.dummy_step_zero(), True{}, False{},
            SolveFast.GuessRes{Nil{}, buf2}),
          SolveFast.step(1n+p, gs, 0n, Nil{}, gG, cwS, n, nodup, floor, inf,
            Nil{}, Nil{}, 0n, best, SolveFast.dummy_step_zero(), False{},
            False{}, SolveFast.GuessRes{Nil{}, buf2}),
          Equal.trans(SolveFast.StepRes,
            SolveFast.step(1n+p, gs, 0n, cs1, gG, cwS, n, nodup, floor, inf, g,
              kids, sum, best, SolveFast.dummy_step_zero(), False{}, False{},
              SolveFast.GuessRes{Nil{}, b1a}),
            SolveFast.step(1n+p, gs, 0n, restb2, gG, cwS, n, nodup, floor, inf,
              g, kf, sf, best, SolveFast.dummy_step_zero(),
              SolveFast.skippable(best, Nat.add(sf, tlb)), False{},
              SolveFast.GuessRes{Nil{}, buf2}),
            SolveFast.step(1n+p, gs, 0n, restb2, gG, cwS, n, nodup, floor, inf,
              g, kf, sf, best, SolveFast.dummy_step_zero(), True{}, False{},
              SolveFast.GuessRes{Nil{}, buf2}),
            e_step_sk,
            Equal.cong(Bool, SolveFast.StepRes,
              sk0 => SolveFast.step(1n+p, gs, 0n, restb2, gG, cwS, n, nodup,
                       floor, inf, g, kf, sf, best, SolveFast.dummy_step_zero(),
                       sk0, False{}, SolveFast.GuessRes{Nil{}, buf2}),
              SolveFast.skippable(best, Nat.add(sf, tlb)), True{}, esk_t)),
          FOpt.body_dead(restg, restb2, p, gs, G, C_root, n_root, has_buf, gG,
            cwS, n, nodup, floor, inf, g, kf, sf, best,
            SolveFast.GuessRes{Nil{}, buf2}, hbm2))
      FOpt.step_res_pre(p, gs, G, C_root, n_root, has_buf, gG, cwS, S, nodup,
        floor, inf, g, cs1, kids, sum, b1a, Nil{}, Nil{}, Nil{}, 0n, buf2,
        best, limit,
        Fold.OQ.ks_cost(inf, S,
          Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg, Nil{},
            sum_ref, inf)),
        Fold.OQ.ks_cost(inf, S,
          Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg, Nil{},
            sum_ref, inf)),
        e_dead,
        NatProof.Nat.is_le_refl(
          Fold.OQ.ks_cost(inf, S,
            Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg, Nil{},
              sum_ref, inf))),
        FOpt.step_res_keep(p, gs, G, C_root, n_root, has_buf, gG, cwS, S, nodup,
          floor, inf, best, buf2, limit,
          Fold.OQ.ks_cost(inf, S,
            Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg, Nil{},
              sum_ref, inf)),
          hbuf2, hok, hd, hb_le_full))

def FOpt.live_group_class_sr(+p: Nat, +gs: SolveFast.GList,
    +G: +List<+List<Nat>>, +C_root: +List<+List<Nat>>, +n_root: Nat,
    +has_buf: Bool, +gG: SolveFast.GList, +cwS: +List<SolveFast.CWord>,
    +S: +List<+List<Nat>>, +nodup: Bool, +floor: Nat, +inf: Nat,
    +g: +List<Nat>, +fb: +List<Feedback.Color>, +f: +List<Feedback.Color>,
    +f2: +List<Feedback.Color>, +ws: +List<+List<Nat>>,
    +cws: +List<SolveFast.CWord>, +wlen: Nat, +tlb: Nat, +tlb2: Nat,
    +restg: +List<Groups.Group>, +restb2: +List<SolveFast.Item>,
    +done_rev: +List<Groups.Group>, +kids: +List<Tree.Child>, +sum: Nat,
    +sum_ref: Nat, +best: SolveRef.Best, -b1a: SolveFast.Buf5, +limit: Nat,
    sr: SolveFast.StepRes,
    +hspec: FOpt.JobResSpec(p, inf, G, C_root, n_root, has_buf, nodup, ws,
              FS.FS.child_cutoff(best, sum, tlb), sr),
    +e_ca: {SolveFast.step(1n+p, gs, 0n,
              SolveFast.ClassItem{f, cws, wlen, tlb}
              <> (SolveFast.Add{f2, tlb2} <> restb2),
              gG, cwS, Groups.len_words(S), nodup, floor, inf, g, kids, sum,
              best, SolveFast.dummy_step_zero(), False{}, False{},
              SolveFast.GuessRes{Nil{}, b1a})
            == FS.FS.after_child_res(p, gs, gG, cwS, Groups.len_words(S), nodup,
                 floor, inf, g, f2, tlb, restb2, kids, sum, best, sr)
            : SolveFast.StepRes},
    bt: MV.MV.Bounds(p, MV.MV.next_groups(restg)),
    +ef2: {f2 == fb : +List<Feedback.Color>},
    +etlb: {FH.FH.tail_lb_ok_b(G, nodup, Groups.len_words(S), restb2, tlb)
            == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h3: {Nat.is_lt(3n, inf) == True{} : Bool},
    +h6: {Nat.is_lt(6n, inf) == True{} : Bool},
    +ngt: {FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(restg)) == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    +hok: {FVal.FV.best_ok_b(limit, G, S, best) == True{} : Bool},
    +hd: {SolveFast.is_floor_hit(nodup, floor, best) == False{} : Bool},
    +hsum_ge: {FOpt.sum_ref_ge(Eval.Eval.cost_of(best), sum, sum_ref)
               == True{} : Bool},
    +hkids: {FOpt.kids_inv(Eval.Eval.cost_of(best), G, done_rev, kids, sum)
             == True{} : Bool},
    +hbm2: FH.FH.BodyMatch(G, C_root, n_root, has_buf, nodup,
             Groups.len_words(S), restg, restb2),
    rec_live:
      @search_in: SolveRef.Best ->
      @buf_in: SolveFast.Buf5 ->
      FH.FH.BufOk(G, C_root, n_root, has_buf, nodup, buf_in) ->
      {FOpt.sum_ref_ge(Eval.Eval.cost_of(best),
         SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(search_in)),
         SolveRef.sat_add(inf, sum_ref,
           Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, ws)))) == True{} : Bool} ->
      {FOpt.kids_inv(Eval.Eval.cost_of(best), G,
         Groups.Group{fb, ws} <> done_rev,
         Tree.Child{f2, Eval.Eval.tree_of(search_in)} <> kids,
         SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(search_in))) == True{} : Bool} ->
      FOpt.StepRes(p, gs, G, C_root, n_root, has_buf, gG, cwS, S, nodup,
        floor, inf, g, restb2,
        Tree.Child{f2, Eval.Eval.tree_of(search_in)} <> kids,
        SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(search_in)),
        best, buf_in, limit,
        Fold.OQ.ks_cost(inf, S,
          Eval.Eval.items(p, G, S, g, restg, Nil{},
            SolveRef.sat_add(inf, sum_ref,
              Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, ws))), inf)))) ->
  FOpt.StepRes(p, gs, G, C_root, n_root, has_buf, gG, cwS, S, nodup, floor, inf,
    g, SolveFast.ClassItem{f, cws, wlen, tlb}
       <> (SolveFast.Add{f2, tlb2} <> restb2),
    kids, sum, best, b1a, limit,
    Fold.OQ.ks_cost(inf, S,
      Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg,
        Nil{}, sum_ref, inf))):
  match sr:
    case SolveFast.StepRes{+search, buf2}:
      +n : Nat = Groups.len_words(S)
      +cut : Nat = FS.FS.child_cutoff(best, sum, tlb)
      +cs1 : +List<SolveFast.Item> =
        SolveFast.ClassItem{f, cws, wlen, tlb}
        <> (SolveFast.Add{f2, tlb2} <> restb2)
      +hsearch = Arr.Arr.dpair_l(
                   {FOpt.job_res_b(p, inf, G, ws, cut, search) == True{} : Bool},
                   FH.FH.BufOk(G, C_root, n_root, has_buf, nodup, buf2), hspec)
      +hbuf2 = Arr.Arr.dpair_r(
                 {FOpt.job_res_b(p, inf, G, ws, cut, search) == True{} : Bool},
                 FH.FH.BufOk(G, C_root, n_root, has_buf, nodup, buf2), hspec)
      +sf : Nat = SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(search))
      +e_step_sk : {SolveFast.step(1n+p, gs, 0n, cs1, gG, cwS, n, nodup, floor,
                      inf, g, kids, sum, best, SolveFast.dummy_step_zero(),
                      False{}, False{}, SolveFast.GuessRes{Nil{}, b1a})
                    == SolveFast.step(1n+p, gs, 0n, restb2, gG, cwS, n, nodup,
                         floor, inf, g,
                         Tree.Child{f2, Eval.Eval.tree_of(search)} <> kids, sf,
                         best, SolveFast.dummy_step_zero(),
                         SolveFast.skippable(best, Nat.add(sf, tlb)), False{},
                         SolveFast.GuessRes{Nil{}, buf2}) : SolveFast.StepRes} =
        Equal.trans(SolveFast.StepRes,
          SolveFast.step(1n+p, gs, 0n, cs1, gG, cwS, n, nodup, floor, inf, g,
            kids, sum, best, SolveFast.dummy_step_zero(), False{}, False{},
            SolveFast.GuessRes{Nil{}, b1a}),
          FS.FS.after_child_res(p, gs, gG, cwS, n, nodup, floor, inf, g, f2,
            tlb, restb2, kids, sum, best, SolveFast.StepRes{search, buf2}),
          SolveFast.step(1n+p, gs, 0n, restb2, gG, cwS, n, nodup, floor, inf, g,
            Tree.Child{f2, Eval.Eval.tree_of(search)} <> kids, sf, best,
            SolveFast.dummy_step_zero(),
            SolveFast.skippable(best, Nat.add(sf, tlb)), False{},
            SolveFast.GuessRes{Nil{}, buf2}),
          e_ca,
          FS.FS.after_child_res_eq(p, gs, gG, cwS, n, nodup, floor, inf, g, f2,
            tlb, restb2, kids, sum, best, search, buf2))
      FOpt.live_group_class_sk(p, gs, G, C_root, n_root, has_buf, gG, cwS, S,
        nodup, floor, inf, g, fb, f, f2, ws, cws, wlen, tlb, tlb2, restg,
        restb2, done_rev, kids, sum, sum_ref, best, b1a, search, buf2, limit,
        SolveFast.skippable(best, Nat.add(sf, tlb)), {==}, bt, ef2, etlb,
        hz, h3, h6, ngt, hbest, hok, hd, hsum_ge, hkids, hbm2, hbuf2, hsearch,
        e_step_sk, rec_live)

def FOpt.live_group_class_dup2(+p: Nat, +gs: SolveFast.GList,
    +G: +List<+List<Nat>>, +C_root: +List<+List<Nat>>, +n_root: Nat,
    +has_buf: Bool, +rwsG: +List<FT.FT.RowWord>, +cwS: +List<SolveFast.CWord>,
    +S: +List<+List<Nat>>, +nodup: Bool, +floor: Nat, +inf: Nat,
    +g: +List<Nat>, +fb: +List<Feedback.Color>, +f: +List<Feedback.Color>,
    +f2: +List<Feedback.Color>, +ws: +List<+List<Nat>>,
    +cws: +List<SolveFast.CWord>, +wlen: Nat, +tlb: Nat, +tlb2: Nat,
    +restg: +List<Groups.Group>, +restb2: +List<SolveFast.Item>,
    +done_rev: +List<Groups.Group>, +kids: +List<Tree.Child>, +sum: Nat,
    +sum_ref: Nat, +best: SolveRef.Best, -b1: SolveFast.Buf5, +limit: Nat,
    +hspec1: FOpt.JobResSpec(p, inf, G, C_root, n_root, has_buf, nodup, ws,
               FS.FS.child_cutoff(best, sum, tlb),
               FS.FS.run_child_from(p, inf,
                 FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cws, nodup,
                 SolveFast.dummy_inf(FS.FS.child_cutoff(best, sum, tlb)), b1)),
    dp2: &b1a: SolveFast.Buf5 -> &b1b: SolveFast.Buf5 ->
         {b1a == b1 : SolveFast.Buf5} & {b1b == b1a : SolveFast.Buf5},
    bt: MV.MV.Bounds(p, MV.MV.next_groups(restg)),
    +ef: {f == fb : +List<Feedback.Color>},
    +ef2: {f2 == fb : +List<Feedback.Color>},
    +ecws: {SolveFast.cwords_words(cws) == ws : +List<+List<Nat>>},
    +elen: {wlen == Groups.len_words(ws) : Nat},
    +etlb: {FH.FH.tail_lb_ok_b(G, nodup, Groups.len_words(S), restb2, tlb)
            == True{} : Bool},
    +etlb2: {tlb2 == tlb : Nat},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h3: {Nat.is_lt(3n, inf) == True{} : Bool},
    +h6: {Nat.is_lt(6n, inf) == True{} : Bool},
    +ngt: {FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(restg)) == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    +hok: {FVal.FV.best_ok_b(limit, G, S, best) == True{} : Bool},
    +hd: {SolveFast.is_floor_hit(nodup, floor, best) == False{} : Bool},
    +hsum_ge: {FOpt.sum_ref_ge(Eval.Eval.cost_of(best), sum, sum_ref)
               == True{} : Bool},
    +hkids: {FOpt.kids_inv(Eval.Eval.cost_of(best), G, done_rev, kids, sum)
             == True{} : Bool},
    +hbm2: FH.FH.BodyMatch(G, C_root, n_root, has_buf, nodup,
             Groups.len_words(S), restg, restb2),
    rec_live:
      @search_in: SolveRef.Best ->
      @buf_in: SolveFast.Buf5 ->
      FH.FH.BufOk(G, C_root, n_root, has_buf, nodup, buf_in) ->
      {FOpt.sum_ref_ge(Eval.Eval.cost_of(best),
         SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(search_in)),
         SolveRef.sat_add(inf, sum_ref,
           Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, ws)))) == True{} : Bool} ->
      {FOpt.kids_inv(Eval.Eval.cost_of(best), G,
         Groups.Group{fb, ws} <> done_rev,
         Tree.Child{f2, Eval.Eval.tree_of(search_in)} <> kids,
         SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(search_in))) == True{} : Bool} ->
      FOpt.StepRes(p, gs, G, C_root, n_root, has_buf,
        FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS, S, nodup,
        floor, inf, g, restb2,
        Tree.Child{f2, Eval.Eval.tree_of(search_in)} <> kids,
        SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(search_in)),
        best, buf_in, limit,
        Fold.OQ.ks_cost(inf, S,
          Eval.Eval.items(p, G, S, g, restg, Nil{},
            SolveRef.sat_add(inf, sum_ref,
              Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, ws))), inf)))) ->
  FOpt.StepRes(p, gs, G, C_root, n_root, has_buf,
    FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS, S, nodup, floor, inf,
    g, SolveFast.ClassItem{f, cws, wlen, tlb}
       <> (SolveFast.Add{f2, tlb2} <> restb2),
    kids, sum, best, b1, limit,
    Fold.OQ.ks_cost(inf, S,
      Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg,
        Nil{}, sum_ref, inf))):
  (b1a, d2) = dp2
  (b1b, pe) = d2
  (+eb1a, +eb1b) = pe
  +gG : SolveFast.GList = FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{})
  +n : Nat = Groups.len_words(S)
  +cut : Nat = FS.FS.child_cutoff(best, sum, tlb)
  +ewlen : {wlen == Groups.len_words(SolveFast.cwords_words(cws)) : Nat} =
    Equal.trans(Nat, wlen, Groups.len_words(ws),
      Groups.len_words(SolveFast.cwords_words(cws)), elen,
      Equal.cong(+List<+List<Nat>>, Nat, l => Groups.len_words(l),
        ws, SolveFast.cwords_words(cws),
        Equal.sym(+List<+List<Nat>>, SolveFast.cwords_words(cws), ws, ecws)))
  +hspec1a = FOpt.job_res_spec_transport(p, inf, G, C_root, n_root, has_buf,
               nodup, ws, cut,
               FS.FS.run_child_from(p, inf, gG, cws, nodup,
                 SolveFast.dummy_inf(cut), b1),
               FS.FS.run_child_from(p, inf, gG, cws, nodup,
                 SolveFast.dummy_inf(cut), b1a),
               Equal.cong(SolveFast.Buf5, SolveFast.StepRes,
                 b => FS.FS.run_child_from(p, inf, gG, cws, nodup,
                        SolveFast.dummy_inf(cut), b),
                 b1, b1a, Equal.sym(SolveFast.Buf5, b1a, b1, eb1a)),
               hspec1)
  +e_ca_b : {SolveFast.step(1n+p, gs, 0n,
               SolveFast.ClassItem{f2, cws,
                 Groups.len_words(SolveFast.cwords_words(cws)), tlb}
               <> (SolveFast.Add{f2, tlb} <> restb2),
               gG, cwS, n, nodup, floor, inf, g, kids, sum, best,
               SolveFast.dummy_step_zero(), False{}, False{},
               SolveFast.GuessRes{Nil{}, b1b})
             == FS.FS.after_child_res(p, gs, gG, cwS, n, nodup, floor, inf, g,
                  f2, tlb, restb2, kids, sum, best,
                  FS.FS.run_child_from(p, inf, gG, cws, nodup,
                    SolveFast.dummy_inf(cut), b1b)) : SolveFast.StepRes} =
    FS.FS.class_add_live(p, gs, gG, cwS, n, nodup, floor, inf, g, f2, cws, tlb,
      restb2, kids, sum, best, b1b)
  +ef12 : {f == f2 : +List<Feedback.Color>} =
    Equal.trans(+List<Feedback.Color>, f, fb, f2, ef,
      Equal.sym(+List<Feedback.Color>, f2, fb, ef2))
  +e_cs_eq : {SolveFast.ClassItem{f, cws, wlen, tlb}
              <> (SolveFast.Add{f2, tlb2} <> restb2)
              == SolveFast.ClassItem{f2, cws,
                   Groups.len_words(SolveFast.cwords_words(cws)), tlb}
                 <> (SolveFast.Add{f2, tlb} <> restb2)
              : +List<SolveFast.Item>} =
    Equal.trans(+List<SolveFast.Item>,
      SolveFast.ClassItem{f, cws, wlen, tlb}
      <> (SolveFast.Add{f2, tlb2} <> restb2),
      SolveFast.ClassItem{f2, cws, wlen, tlb}
      <> (SolveFast.Add{f2, tlb2} <> restb2),
      SolveFast.ClassItem{f2, cws,
        Groups.len_words(SolveFast.cwords_words(cws)), tlb}
      <> (SolveFast.Add{f2, tlb} <> restb2),
      Equal.cong(+List<Feedback.Color>, +List<SolveFast.Item>,
        fx => SolveFast.ClassItem{fx, cws, wlen, tlb}
              <> (SolveFast.Add{f2, tlb2} <> restb2),
        f, f2, ef12),
      Equal.trans(+List<SolveFast.Item>,
        SolveFast.ClassItem{f2, cws, wlen, tlb}
        <> (SolveFast.Add{f2, tlb2} <> restb2),
        SolveFast.ClassItem{f2, cws,
          Groups.len_words(SolveFast.cwords_words(cws)), tlb}
        <> (SolveFast.Add{f2, tlb2} <> restb2),
        SolveFast.ClassItem{f2, cws,
          Groups.len_words(SolveFast.cwords_words(cws)), tlb}
        <> (SolveFast.Add{f2, tlb} <> restb2),
        Equal.cong(Nat, +List<SolveFast.Item>,
          wl => SolveFast.ClassItem{f2, cws, wl, tlb}
                <> (SolveFast.Add{f2, tlb2} <> restb2),
          wlen, Groups.len_words(SolveFast.cwords_words(cws)), ewlen),
        Equal.cong(Nat, +List<SolveFast.Item>,
          t0 => SolveFast.ClassItem{f2, cws,
                  Groups.len_words(SolveFast.cwords_words(cws)), tlb}
                <> (SolveFast.Add{f2, t0} <> restb2),
          tlb2, tlb, etlb2)))
  +e_ca_a0 : {SolveFast.step(1n+p, gs, 0n,
                SolveFast.ClassItem{f2, cws,
                  Groups.len_words(SolveFast.cwords_words(cws)), tlb}
                <> (SolveFast.Add{f2, tlb} <> restb2),
                gG, cwS, n, nodup, floor, inf, g, kids, sum, best,
                SolveFast.dummy_step_zero(), False{}, False{},
                SolveFast.GuessRes{Nil{}, b1a})
              == FS.FS.after_child_res(p, gs, gG, cwS, n, nodup, floor, inf, g,
                   f2, tlb, restb2, kids, sum, best,
                   FS.FS.run_child_from(p, inf, gG, cws, nodup,
                     SolveFast.dummy_inf(cut), b1a)) : SolveFast.StepRes} =
    %eb1b : {SolveFast.step(1n+p, gs, 0n,
               SolveFast.ClassItem{f2, cws,
                 Groups.len_words(SolveFast.cwords_words(cws)), tlb}
               <> (SolveFast.Add{f2, tlb} <> restb2),
               gG, cwS, n, nodup, floor, inf, g, kids, sum, best,
               SolveFast.dummy_step_zero(), False{}, False{},
               SolveFast.GuessRes{Nil{}, _})
             == FS.FS.after_child_res(p, gs, gG, cwS, n, nodup, floor, inf, g,
                  f2, tlb, restb2, kids, sum, best,
                  FS.FS.run_child_from(p, inf, gG, cws, nodup,
                    SolveFast.dummy_inf(cut), _)) : SolveFast.StepRes}
    e_ca_b
  +e_ca : {SolveFast.step(1n+p, gs, 0n,
             SolveFast.ClassItem{f, cws, wlen, tlb}
             <> (SolveFast.Add{f2, tlb2} <> restb2),
             gG, cwS, n, nodup, floor, inf, g, kids, sum, best,
             SolveFast.dummy_step_zero(), False{}, False{},
             SolveFast.GuessRes{Nil{}, b1a})
           == FS.FS.after_child_res(p, gs, gG, cwS, n, nodup, floor, inf, g,
                f2, tlb, restb2, kids, sum, best,
                FS.FS.run_child_from(p, inf, gG, cws, nodup,
                  SolveFast.dummy_inf(cut), b1a)) : SolveFast.StepRes} =
    Equal.trans(SolveFast.StepRes,
      SolveFast.step(1n+p, gs, 0n,
        SolveFast.ClassItem{f, cws, wlen, tlb}
        <> (SolveFast.Add{f2, tlb2} <> restb2),
        gG, cwS, n, nodup, floor, inf, g, kids, sum, best,
        SolveFast.dummy_step_zero(), False{}, False{},
        SolveFast.GuessRes{Nil{}, b1a}),
      SolveFast.step(1n+p, gs, 0n,
        SolveFast.ClassItem{f2, cws,
          Groups.len_words(SolveFast.cwords_words(cws)), tlb}
        <> (SolveFast.Add{f2, tlb} <> restb2),
        gG, cwS, n, nodup, floor, inf, g, kids, sum, best,
        SolveFast.dummy_step_zero(), False{}, False{},
        SolveFast.GuessRes{Nil{}, b1a}),
      FS.FS.after_child_res(p, gs, gG, cwS, n, nodup, floor, inf, g, f2, tlb,
        restb2, kids, sum, best,
        FS.FS.run_child_from(p, inf, gG, cws, nodup,
          SolveFast.dummy_inf(cut), b1a)),
      Equal.cong(+List<SolveFast.Item>, SolveFast.StepRes,
        cs => SolveFast.step(1n+p, gs, 0n, cs, gG, cwS, n, nodup, floor, inf,
                g, kids, sum, best, SolveFast.dummy_step_zero(), False{},
                False{}, SolveFast.GuessRes{Nil{}, b1a}),
        SolveFast.ClassItem{f, cws, wlen, tlb}
        <> (SolveFast.Add{f2, tlb2} <> restb2),
        SolveFast.ClassItem{f2, cws,
          Groups.len_words(SolveFast.cwords_words(cws)), tlb}
        <> (SolveFast.Add{f2, tlb} <> restb2), e_cs_eq),
      e_ca_a0)
  %eb1a : FOpt.StepRes(p, gs, G, C_root, n_root, has_buf, gG, cwS, S, nodup,
            floor, inf, g,
            SolveFast.ClassItem{f, cws, wlen, tlb}
            <> (SolveFast.Add{f2, tlb2} <> restb2),
            kids, sum, best, _, limit,
            Fold.OQ.ks_cost(inf, S,
              Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg,
                Nil{}, sum_ref, inf)))
  FOpt.live_group_class_sr(p, gs, G, C_root, n_root, has_buf, gG, cwS, S,
    nodup, floor, inf, g, fb, f, f2, ws, cws, wlen, tlb, tlb2, restg, restb2,
    done_rev, kids, sum, sum_ref, best, b1a, limit,
    FS.FS.run_child_from(p, inf, gG, cws, nodup, SolveFast.dummy_inf(cut), b1a),
    hspec1a, e_ca, bt, ef2, etlb, hz, h3, h6, ngt, hbest, hok, hd, hsum_ge,
    hkids, hbm2, rec_live)

def FOpt.live_group_class_dup1(+p: Nat, +gs: SolveFast.GList,
    +G: +List<+List<Nat>>, +C_root: +List<+List<Nat>>, +n_root: Nat,
    +has_buf: Bool, +rwsG: +List<FT.FT.RowWord>, +cwS: +List<SolveFast.CWord>,
    +S: +List<+List<Nat>>, +nodup: Bool, +floor: Nat, +inf: Nat,
    +g: +List<Nat>, +fb: +List<Feedback.Color>, +f: +List<Feedback.Color>,
    +f2: +List<Feedback.Color>, +ws: +List<+List<Nat>>,
    +cws: +List<SolveFast.CWord>, +wlen: Nat, +tlb: Nat, +tlb2: Nat,
    +restg: +List<Groups.Group>, +restb2: +List<SolveFast.Item>,
    +done_rev: +List<Groups.Group>, +kids: +List<Tree.Child>, +sum: Nat,
    +sum_ref: Nat, +best: SolveRef.Best, -buf: SolveFast.Buf5, +limit: Nat,
    +hbuf: FH.FH.BufOk(G, C_root, n_root, has_buf, nodup, buf),
    dp1: &b1: SolveFast.Buf5 -> &b2: SolveFast.Buf5 ->
         {b1 == buf : SolveFast.Buf5} & {b2 == b1 : SolveFast.Buf5},
    bt: MV.MV.Bounds(p, MV.MV.next_groups(restg)),
    +erwsG: {FT.FT.rws_words(rwsG) == G : +List<+List<Nat>>},
    +hrwsG: {FH.FH.rws_ok_if(has_buf, G, n_root, rwsG) == True{} : Bool},
    +ef: {f == fb : +List<Feedback.Color>},
    +ef2: {f2 == fb : +List<Feedback.Color>},
    +ecws: {SolveFast.cwords_words(cws) == ws : +List<+List<Nat>>},
    +elen: {wlen == Groups.len_words(ws) : Nat},
    +hcws: {FH.FH.cwords_ok_if(has_buf, G, C_root, n_root, cws) == True{} : Bool},
    +etlb: {FH.FH.tail_lb_ok_b(G, nodup, Groups.len_words(S), restb2, tlb)
            == True{} : Bool},
    +etlb2: {tlb2 == tlb : Nat},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h3: {Nat.is_lt(3n, inf) == True{} : Bool},
    +h6: {Nat.is_lt(6n, inf) == True{} : Bool},
    +ngt: {FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(restg)) == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    +hok: {FVal.FV.best_ok_b(limit, G, S, best) == True{} : Bool},
    +hd: {SolveFast.is_floor_hit(nodup, floor, best) == False{} : Bool},
    +hsum_ge: {FOpt.sum_ref_ge(Eval.Eval.cost_of(best), sum, sum_ref)
               == True{} : Bool},
    +hkids: {FOpt.kids_inv(Eval.Eval.cost_of(best), G, done_rev, kids, sum)
             == True{} : Bool},
    +hbm2: FH.FH.BodyMatch(G, C_root, n_root, has_buf, nodup,
             Groups.len_words(S), restg, restb2),
    eh: FOpt.EJob(p, inf, G, C_root, n_root, has_buf, ws, nodup),
    rec_live:
      @search_in: SolveRef.Best ->
      @buf_in: SolveFast.Buf5 ->
      FH.FH.BufOk(G, C_root, n_root, has_buf, nodup, buf_in) ->
      {FOpt.sum_ref_ge(Eval.Eval.cost_of(best),
         SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(search_in)),
         SolveRef.sat_add(inf, sum_ref,
           Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, ws)))) == True{} : Bool} ->
      {FOpt.kids_inv(Eval.Eval.cost_of(best), G,
         Groups.Group{fb, ws} <> done_rev,
         Tree.Child{f2, Eval.Eval.tree_of(search_in)} <> kids,
         SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(search_in))) == True{} : Bool} ->
      FOpt.StepRes(p, gs, G, C_root, n_root, has_buf,
        FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS, S, nodup,
        floor, inf, g, restb2,
        Tree.Child{f2, Eval.Eval.tree_of(search_in)} <> kids,
        SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(search_in)),
        best, buf_in, limit,
        Fold.OQ.ks_cost(inf, S,
          Eval.Eval.items(p, G, S, g, restg, Nil{},
            SolveRef.sat_add(inf, sum_ref,
              Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, ws))), inf)))) ->
  FOpt.StepRes(p, gs, G, C_root, n_root, has_buf,
    FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS, S, nodup, floor, inf,
    g, SolveFast.ClassItem{f, cws, wlen, tlb}
       <> (SolveFast.Add{f2, tlb2} <> restb2),
    kids, sum, best, buf, limit,
    Fold.OQ.ks_cost(inf, S,
      Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg,
        Nil{}, sum_ref, inf))):
  (b1, d2) = dp1
  (b2, pe) = d2
  (+eb1, +eb2) = pe
  +gG : SolveFast.GList = FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{})
  +B : Nat = Eval.Eval.cost_of(best)
  +cut : Nat = FS.FS.child_cutoff(best, sum, tlb)
  +cut_eq : {cut == Nat.sub(B, Nat.add(sum, tlb)) : Nat} =
    Equal.cong(Nat, Nat, x => Nat.sub(x, Nat.add(sum, tlb)),
      SolveFast.best_cost(best), B, FLB.FS.best_cost_eq(best))
  +cut_le_inf : {Nat.is_le(cut, inf) == True{} : Bool} =
    NatProof.Nat.is_le_trans(cut, B, inf,
      NatProof.Nat.is_le_eq_l(B, Nat.sub(B, Nat.add(sum, tlb)), cut,
        Equal.sym(Nat, cut, Nat.sub(B, Nat.add(sum, tlb)), cut_eq),
        FC.FC.sub_le_self(B, Nat.add(sum, tlb))), hbest)
  +eb2_buf : {b2 == buf : SolveFast.Buf5} =
    Equal.trans(SolveFast.Buf5, b2, b1, buf, eb2, eb1)
  +hbuf2 = FH.FH.buf_ok_transport(G, C_root, n_root, has_buf, nodup, buf, b2,
             Equal.sym(SolveFast.Buf5, b2, buf, eb2_buf), hbuf)
  +hspec2 = eh(rwsG, cws, SolveFast.dummy_inf(cut), b2, erwsG, hrwsG, ecws,
              hcws, cut_le_inf, hbuf2)
  +hspec1 = FOpt.job_res_spec_transport(p, inf, G, C_root, n_root, has_buf,
              nodup, ws, cut,
              FS.FS.run_child_from(p, inf, gG, cws, nodup,
                SolveFast.dummy_inf(cut), b2),
              FS.FS.run_child_from(p, inf, gG, cws, nodup,
                SolveFast.dummy_inf(cut), b1),
              Equal.cong(SolveFast.Buf5, SolveFast.StepRes,
                b => FS.FS.run_child_from(p, inf, gG, cws, nodup,
                       SolveFast.dummy_inf(cut), b),
                b2, b1, eb2), hspec2)
  %eb1 : FOpt.StepRes(p, gs, G, C_root, n_root, has_buf, gG, cwS, S, nodup,
           floor, inf, g,
           SolveFast.ClassItem{f, cws, wlen, tlb}
           <> (SolveFast.Add{f2, tlb2} <> restb2),
           kids, sum, best, _, limit,
           Fold.OQ.ks_cost(inf, S,
             Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg,
               Nil{}, sum_ref, inf)))
  FOpt.live_group_class_dup2(p, gs, G, C_root, n_root, has_buf, rwsG, cwS, S,
    nodup, floor, inf, g, fb, f, f2, ws, cws, wlen, tlb, tlb2, restg, restb2,
    done_rev, kids, sum, sum_ref, best, b1, limit, hspec1, FH.FH.buf_dup(b1),
    bt, ef, ef2, ecws, elen, etlb, etlb2, hz, h3, h6, ngt, hbest, hok, hd,
    hsum_ge, hkids, hbm2, rec_live)

def FOpt.live_groups_ok(+groups: +List<Groups.Group>,
    +body: +List<SolveFast.Item>, +p: Nat, +gs: SolveFast.GList,
    +G: +List<+List<Nat>>, +C_root: +List<+List<Nat>>, +n_root: Nat,
    +has_buf: Bool, +rwsG: +List<FT.FT.RowWord>, +cwS: +List<SolveFast.CWord>,
    +S: +List<+List<Nat>>, +nodup: Bool, +floor: Nat, +inf: Nat,
    +g: +List<Nat>, +done_rev: +List<Groups.Group>,
    +kids: +List<Tree.Child>, +sum: Nat, +sum_ref: Nat, +best: SolveRef.Best,
    buf: SolveFast.Buf5, +limit: Nat,
    +hbuf: FH.FH.BufOk(G, C_root, n_root, has_buf, nodup, buf),
    bounds: MV.MV.Bounds(p, MV.MV.next_groups(groups)),
    +erwsG: {FT.FT.rws_words(rwsG) == G : +List<+List<Nat>>},
    +hrwsG: {FH.FH.rws_ok_if(has_buf, G, n_root, rwsG) == True{} : Bool},
    +wg: {Tree.member_word(g, G) == True{} : Bool},
    +perm: FP.FP.Perm,
    +hperm: FP.FP.PermOk(perm, Groups.groups_build(g, S, Nil{}),
              FVal.FV.rev_groups(done_rev, groups)),
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +h3: {Nat.is_lt(3n, inf) == True{} : Bool},
    +h6: {Nat.is_lt(6n, inf) == True{} : Bool},
    +ag: {FO.FO.all_in_jobs_b(MV.MV.next_groups(groups), G) == True{} : Bool},
    +ng: {FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(groups))
          == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    +hok: {FVal.FV.best_ok_b(limit, G, S, best) == True{} : Bool},
    +hd: {SolveFast.is_floor_hit(nodup, floor, best) == False{} : Bool},
    +hsum_ge: {FOpt.sum_ref_ge(Eval.Eval.cost_of(best), sum, sum_ref)
               == True{} : Bool},
    +hkids: {FOpt.kids_inv(Eval.Eval.cost_of(best), G, done_rev, kids, sum)
             == True{} : Bool},
    +hbm: FH.FH.BodyMatch(G, C_root, n_root, has_buf, nodup,
            Groups.len_words(S), groups, body),
    ec: FOpt.EClass(p, inf, G, C_root, n_root, has_buf, nodup, groups)) ->
  FOpt.StepRes(p, gs, G, C_root, n_root, has_buf,
    FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS, S, nodup, floor, inf,
    g, body, kids, sum, best, buf, limit,
    Fold.OQ.ks_cost(inf, S,
      Eval.Eval.items(p, G, S, g, groups, Nil{}, sum_ref, inf))):
  match groups:
    case Nil{}:
      +gG : SolveFast.GList = FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{})
      %Equal.sym(+List<SolveFast.Item>, body, SolveFast.End{} <> Nil{}, hbm) :
        FOpt.StepRes(p, gs, G, C_root, n_root, has_buf, gG, cwS, S, nodup,
          floor, inf, g, _, kids, sum, best, buf, limit,
          Fold.OQ.ks_cost(inf, S,
            Eval.Eval.items(p, G, S, g, Nil{}, Nil{}, sum_ref, inf)))
      FOpt.live_group_end(p, gs, G, C_root, n_root, has_buf, gG, cwS, S, nodup,
        floor, inf, g, done_rev, kids, sum, sum_ref, best, buf, limit, hbuf, wg,
        perm, hperm, hbest, hok, hsum_ge, hkids)
    case Con{gp, restg}:
      match gp:
        case Groups.Group{+fb, +ws}:
          match body:
            case Nil{}:
              +gG : SolveFast.GList = FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{})
              Empty.absurd(
                FOpt.StepRes(p, gs, G, C_root, n_root, has_buf, gG, cwS, S,
                  nodup, floor, inf, g, Nil{}, kids, sum, best, buf, limit,
                  Fold.OQ.ks_cost(inf, S,
                    Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg,
                      Nil{}, sum_ref, inf))), hbm)
            case Con{it, restb}:
              match it:
                case SolveFast.Begin{g2}:
                  +gG : SolveFast.GList = FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{})
                  Empty.absurd(
                    FOpt.StepRes(p, gs, G, C_root, n_root, has_buf, gG, cwS, S,
                      nodup, floor, inf, g, SolveFast.Begin{g2} <> restb,
                      kids, sum, best, buf, limit,
                      Fold.OQ.ks_cost(inf, S,
                        Eval.Eval.items(p, G, S, g,
                          Groups.Group{fb, ws} <> restg, Nil{}, sum_ref, inf))),
                    hbm)
                case SolveFast.OneItem{+f, +w}:
                  (+ble, bt) = bounds
                  (eh, et) = ec
                  +n : Nat = Groups.len_words(S)
                  +gG : SolveFast.GList = FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{})
                  +ef = Arr.Arr.dpair_l({f == fb : +List<Feedback.Color>},
                          Arr.Arr.DPair<{ws == w <> Nil{} : +List<+List<Nat>>},
                            FH.FH.BodyMatch(G, C_root, n_root, has_buf, nodup,
                              n, restg, restb)>, hbm)
                  +r1 = Arr.Arr.dpair_r({f == fb : +List<Feedback.Color>},
                          Arr.Arr.DPair<{ws == w <> Nil{} : +List<+List<Nat>>},
                            FH.FH.BodyMatch(G, C_root, n_root, has_buf, nodup,
                              n, restg, restb)>, hbm)
                  +ews = Arr.Arr.dpair_l({ws == w <> Nil{} : +List<+List<Nat>>},
                           FH.FH.BodyMatch(G, C_root, n_root, has_buf, nodup,
                             n, restg, restb), r1)
                  +hbm2 = Arr.Arr.dpair_r({ws == w <> Nil{} : +List<+List<Nat>>},
                            FH.FH.BodyMatch(G, C_root, n_root, has_buf, nodup,
                              n, restg, restb), r1)
                  +ai_ws = Logic.Proof.and_true_l(FO.FO.all_in_ref(ws, G),
                             FO.FO.all_in_jobs_b(MV.MV.next_groups(restg), G), ag)
                  +ag_rest = Logic.Proof.and_true_r(FO.FO.all_in_ref(ws, G),
                               FO.FO.all_in_jobs_b(MV.MV.next_groups(restg), G), ag)
                  +ng_rest = Logic.Proof.and_true_r(FN.FN.nodup_ok(nodup, ws),
                               FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(restg)),
                               ng)
                  +ai1 : {FO.FO.all_in_ref(w <> Nil{}, G) == True{} : Bool} =
                    Equal.trans(Bool, FO.FO.all_in_ref(w <> Nil{}, G),
                      FO.FO.all_in_ref(ws, G), True{},
                      Equal.cong(+List<+List<Nat>>, Bool,
                        l => FO.FO.all_in_ref(l, G), w <> Nil{}, ws,
                        Equal.sym(+List<+List<Nat>>, ws, w <> Nil{}, ews)),
                      ai_ws)
                  +win = FO.FO.all_in_head(w, Nil{}, G, ai1)
                  +ble1 : {Nat.is_le(1n, p) == True{} : Bool} =
                    Equal.trans(Bool, Nat.is_le(1n, p),
                      Nat.is_le(Groups.len_words(ws), p), True{},
                      Equal.cong(+List<+List<Nat>>, Bool,
                        l => Nat.is_le(Groups.len_words(l), p), w <> Nil{}, ws,
                        Equal.sym(+List<+List<Nat>>, ws, w <> Nil{}, ews)), ble)
                  +hval : {FVal.FV.valid_b(Tree.Node{w, Nil{}}, G, ws)
                           == True{} : Bool} =
                    Equal.trans(Bool, FVal.FV.valid_b(Tree.Node{w, Nil{}}, G, ws),
                      FVal.FV.valid_b(Tree.Node{w, Nil{}}, G, w <> Nil{}), True{},
                      Equal.cong(+List<+List<Nat>>, Bool,
                        l => FVal.FV.valid_b(Tree.Node{w, Nil{}}, G, l),
                        ws, w <> Nil{}, ews),
                      FVal.FV.one_tree_valid_b(w, G, win))
                  +hcost : {Nat.is_le(Tree.cost(Tree.Node{w, Nil{}}, ws), 1n)
                            == True{} : Bool} =
                    Fold.OQ.le_cong_l(Tree.cost(Tree.Node{w, Nil{}}, ws), 1n, 1n,
                      Equal.trans(Nat, Tree.cost(Tree.Node{w, Nil{}}, ws),
                        Tree.cost(Tree.Node{w, Nil{}}, w <> Nil{}), 1n,
                        Equal.cong(+List<+List<Nat>>, Nat,
                          l => Tree.cost(Tree.Node{w, Nil{}}, l),
                          ws, w <> Nil{}, ews),
                        FVal.FV.one_tree_cost(w)), {==})
                  +e_ref1 : {1n == Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, ws))
                             : Nat} =
                    Equal.trans(Nat, 1n,
                      Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, w <> Nil{})),
                      Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, ws)),
                      Equal.cong(SolveRef.Best, Nat, Eval.Eval.cost_of,
                        SolveRef.Best{Tree.Node{w, Nil{}}, 1n},
                        FS.FS.ref_run_at(p, inf, G, w <> Nil{}),
                        FO.FO.ref_run_one_eq(p, inf, G, w, ble1, h1, win)),
                      Equal.cong(+List<+List<Nat>>, Nat,
                        l => Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, l)),
                        w <> Nil{}, ws,
                        Equal.sym(+List<+List<Nat>>, ws, w <> Nil{}, ews)))
                  +h1_ref : {Nat.is_le(1n,
                               Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, ws)))
                             == True{} : Bool} =
                    NatProof.Nat.is_le_eq_r(1n, 1n,
                      Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, ws)),
                      e_ref1, {==})
                  +sr : Nat =
                    SolveRef.sat_add(inf, sum_ref,
                      Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, ws)))
                  FOpt.live_group_leaf(p, gs, G, C_root, n_root, has_buf, gG,
                    cwS, S, nodup, floor, inf, g, fb, f, ws, restg,
                    SolveFast.OneItem{f, w}, restb, Tree.Node{w, Nil{}}, 1n,
                    done_rev, kids, sum, sum_ref, best, buf, limit, hbuf,
                    FS.FS.one_live(p, gs, gG, cwS, n, nodup, floor, inf, g, f,
                      w, restb, kids, sum, best, SolveFast.GuessRes{Nil{}, buf}),
                    ef, hbest, hval, hcost, h1_ref, hsum_ge, hkids,
                    buf_in => +hbuf_in => +hsum2 => +hkids2 =>
                      FOpt.live_groups_ok(restg, restb, p, gs, G, C_root, n_root,
                        has_buf, rwsG, cwS, S, nodup, floor, inf, g,
                        Groups.Group{fb, ws} <> done_rev,
                        Tree.Child{f, Tree.Node{w, Nil{}}} <> kids,
                        SolveRef.sat_add(inf, sum, 1n), sr, best, buf_in, limit,
                        hbuf_in, bt, erwsG, hrwsG, wg, perm, hperm, hz, h1, h3, h6,
                        ag_rest, ng_rest, hbest, hok, hd, hsum2, hkids2, hbm2,
                        et))
                case SolveFast.TwoItem{+f, +w1, +w2}:
                  (+ble, bt) = bounds
                  (eh, et) = ec
                  +n : Nat = Groups.len_words(S)
                  +gG : SolveFast.GList = FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{})
                  +ws2 : +List<+List<Nat>> = w1 <> (w2 <> Nil{})
                  +end = Arr.Arr.dpair_l({nodup == True{} : Bool},
                           Arr.Arr.DPair<{f == fb : +List<Feedback.Color>},
                             Arr.Arr.DPair<{ws == ws2 : +List<+List<Nat>>},
                               FH.FH.BodyMatch(G, C_root, n_root, has_buf, nodup,
                                 n, restg, restb)>>, hbm)
                  +r1 = Arr.Arr.dpair_r({nodup == True{} : Bool},
                          Arr.Arr.DPair<{f == fb : +List<Feedback.Color>},
                            Arr.Arr.DPair<{ws == ws2 : +List<+List<Nat>>},
                              FH.FH.BodyMatch(G, C_root, n_root, has_buf, nodup,
                                n, restg, restb)>>, hbm)
                  +ef = Arr.Arr.dpair_l({f == fb : +List<Feedback.Color>},
                          Arr.Arr.DPair<{ws == ws2 : +List<+List<Nat>>},
                            FH.FH.BodyMatch(G, C_root, n_root, has_buf, nodup,
                              n, restg, restb)>, r1)
                  +r2 = Arr.Arr.dpair_r({f == fb : +List<Feedback.Color>},
                          Arr.Arr.DPair<{ws == ws2 : +List<+List<Nat>>},
                            FH.FH.BodyMatch(G, C_root, n_root, has_buf, nodup,
                              n, restg, restb)>, r1)
                  +ews = Arr.Arr.dpair_l({ws == ws2 : +List<+List<Nat>>},
                           FH.FH.BodyMatch(G, C_root, n_root, has_buf, nodup,
                             n, restg, restb), r2)
                  +hbm2 = Arr.Arr.dpair_r({ws == ws2 : +List<+List<Nat>>},
                            FH.FH.BodyMatch(G, C_root, n_root, has_buf, nodup,
                              n, restg, restb), r2)
                  +ai_ws = Logic.Proof.and_true_l(FO.FO.all_in_ref(ws, G),
                             FO.FO.all_in_jobs_b(MV.MV.next_groups(restg), G), ag)
                  +ag_rest = Logic.Proof.and_true_r(FO.FO.all_in_ref(ws, G),
                               FO.FO.all_in_jobs_b(MV.MV.next_groups(restg), G), ag)
                  +ndh0 = Logic.Proof.and_true_l(FN.FN.nodup_ok(nodup, ws),
                            FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(restg)),
                            ng)
                  +ng_rest = Logic.Proof.and_true_r(FN.FN.nodup_ok(nodup, ws),
                               FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(restg)),
                               ng)
                  +ai2 : {FO.FO.all_in_ref(ws2, G) == True{} : Bool} =
                    Equal.trans(Bool, FO.FO.all_in_ref(ws2, G),
                      FO.FO.all_in_ref(ws, G), True{},
                      Equal.cong(+List<+List<Nat>>, Bool,
                        l => FO.FO.all_in_ref(l, G), ws2, ws,
                        Equal.sym(+List<+List<Nat>>, ws, ws2, ews)), ai_ws)
                  +w1in = FO.FO.all_in_head(w1, w2 <> Nil{}, G, ai2)
                  +w2in = FO.FO.all_in_head(w2, Nil{}, G,
                            FO.FO.all_in_tail(w1, w2 <> Nil{}, G, ai2))
                  +nd2 : {FN.FN.no_dup_ref(ws2) == True{} : Bool} =
                    Equal.trans(Bool, FN.FN.no_dup_ref(ws2),
                      FN.FN.nodup_ok(nodup, ws), True{},
                      Equal.trans(Bool, FN.FN.no_dup_ref(ws2),
                        FN.FN.nodup_ok(True{}, ws), FN.FN.nodup_ok(nodup, ws),
                        Equal.cong(+List<+List<Nat>>, Bool,
                          l => FN.FN.no_dup_ref(l), ws2, ws,
                          Equal.sym(+List<+List<Nat>>, ws, ws2, ews)),
                        Equal.cong(Bool, Bool, b => FN.FN.nodup_ok(b, ws),
                          True{}, nodup, Equal.sym(Bool, nodup, True{}, end))),
                      ndh0)
                  +hne = FVal.FV.word_eq_false_of_no_dup_two(w1, w2, nd2)
                  +ble2 : {Nat.is_le(2n, p) == True{} : Bool} =
                    Equal.trans(Bool, Nat.is_le(2n, p),
                      Nat.is_le(Groups.len_words(ws), p), True{},
                      Equal.cong(+List<+List<Nat>>, Bool,
                        l => Nat.is_le(Groups.len_words(l), p), ws2, ws,
                        Equal.sym(+List<+List<Nat>>, ws, ws2, ews)), ble)
                  +hval : {FVal.FV.valid_b(SolveFast.two_tree(w1, w2), G, ws)
                           == True{} : Bool} =
                    Equal.trans(Bool,
                      FVal.FV.valid_b(SolveFast.two_tree(w1, w2), G, ws),
                      FVal.FV.valid_b(SolveFast.two_tree(w1, w2), G, ws2), True{},
                      Equal.cong(+List<+List<Nat>>, Bool,
                        l => FVal.FV.valid_b(SolveFast.two_tree(w1, w2), G, l),
                        ws, ws2, ews),
                      FVal.FV.two_tree_valid_b(w1, w2, G, w1in, w2in, hne))
                  +hcost : {Nat.is_le(Tree.cost(SolveFast.two_tree(w1, w2), ws), 3n)
                            == True{} : Bool} =
                    Fold.OQ.le_cong_l(Tree.cost(SolveFast.two_tree(w1, w2), ws),
                      3n, 3n,
                      Equal.trans(Nat, Tree.cost(SolveFast.two_tree(w1, w2), ws),
                        Tree.cost(SolveFast.two_tree(w1, w2), ws2), 3n,
                        Equal.cong(+List<+List<Nat>>, Nat,
                          l => Tree.cost(SolveFast.two_tree(w1, w2), l),
                          ws, ws2, ews),
                        FVal.FV.two_tree_cost(w1, w2, hne)), {==})
                  +h3_ref : {Nat.is_le(3n,
                               Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, ws)))
                             == True{} : Bool} =
                    Fold.OQ.le_cong_r(3n,
                      Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, ws2)),
                      Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, ws)),
                      Equal.cong(+List<+List<Nat>>, Nat,
                        l => Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, l)),
                        ws2, ws, Equal.sym(+List<+List<Nat>>, ws, ws2, ews)),
                      FVal.FV.three_le_ref_two(p, inf, G, w1, w2, ble2, hz, h3,
                        nd2))
                  +sr : Nat =
                    SolveRef.sat_add(inf, sum_ref,
                      Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, ws)))
                  FOpt.live_group_leaf(p, gs, G, C_root, n_root, has_buf, gG,
                    cwS, S, nodup, floor, inf, g, fb, f, ws, restg,
                    SolveFast.TwoItem{f, w1, w2}, restb,
                    SolveFast.two_tree(w1, w2), 3n,
                    done_rev, kids, sum, sum_ref, best, buf, limit, hbuf,
                    FS.FS.two_live(p, gs, gG, cwS, n, nodup, floor, inf, g, f,
                      w1, w2, restb, kids, sum, best,
                      SolveFast.GuessRes{Nil{}, buf}),
                    ef, hbest, hval, hcost, h3_ref, hsum_ge, hkids,
                    buf_in => +hbuf_in => +hsum2 => +hkids2 =>
                      FOpt.live_groups_ok(restg, restb, p, gs, G, C_root, n_root,
                        has_buf, rwsG, cwS, S, nodup, floor, inf, g,
                        Groups.Group{fb, ws} <> done_rev,
                        Tree.Child{f, SolveFast.two_tree(w1, w2)} <> kids,
                        SolveRef.sat_add(inf, sum, 3n), sr, best, buf_in, limit,
                        hbuf_in, bt, erwsG, hrwsG, wg, perm, hperm, hz, h1, h3, h6,
                        ag_rest, ng_rest, hbest, hok, hd, hsum2, hkids2, hbm2,
                        et))
                case SolveFast.DoneItem{+f, +tr, +c}:
                  (+ble, bt) = bounds
                  (eh, et) = ec
                  +n : Nat = Groups.len_words(S)
                  +gG : SolveFast.GList = FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{})
                  +end = Arr.Arr.dpair_l({nodup == True{} : Bool},
                           Arr.Arr.DPair<{f == fb : +List<Feedback.Color>},
                             Arr.Arr.DPair<
                               {FH.FH.done_ws_ok_b(G, ws, tr, c) == True{} : Bool},
                               FH.FH.BodyMatch(G, C_root, n_root, has_buf, nodup,
                                 n, restg, restb)>>, hbm)
                  +r1 = Arr.Arr.dpair_r({nodup == True{} : Bool},
                          Arr.Arr.DPair<{f == fb : +List<Feedback.Color>},
                            Arr.Arr.DPair<
                              {FH.FH.done_ws_ok_b(G, ws, tr, c) == True{} : Bool},
                              FH.FH.BodyMatch(G, C_root, n_root, has_buf, nodup,
                                n, restg, restb)>>, hbm)
                  +ef = Arr.Arr.dpair_l({f == fb : +List<Feedback.Color>},
                          Arr.Arr.DPair<
                            {FH.FH.done_ws_ok_b(G, ws, tr, c) == True{} : Bool},
                            FH.FH.BodyMatch(G, C_root, n_root, has_buf, nodup,
                              n, restg, restb)>, r1)
                  +r2 = Arr.Arr.dpair_r({f == fb : +List<Feedback.Color>},
                          Arr.Arr.DPair<
                            {FH.FH.done_ws_ok_b(G, ws, tr, c) == True{} : Bool},
                            FH.FH.BodyMatch(G, C_root, n_root, has_buf, nodup,
                              n, restg, restb)>, r1)
                  +hdws = Arr.Arr.dpair_l(
                            {FH.FH.done_ws_ok_b(G, ws, tr, c) == True{} : Bool},
                            FH.FH.BodyMatch(G, C_root, n_root, has_buf, nodup,
                              n, restg, restb), r2)
                  +hbm2 = Arr.Arr.dpair_r(
                            {FH.FH.done_ws_ok_b(G, ws, tr, c) == True{} : Bool},
                            FH.FH.BodyMatch(G, C_root, n_root, has_buf, nodup,
                              n, restg, restb), r2)
                  +ag_rest = Logic.Proof.and_true_r(FO.FO.all_in_ref(ws, G),
                               FO.FO.all_in_jobs_b(MV.MV.next_groups(restg), G), ag)
                  +ndh0 = Logic.Proof.and_true_l(FN.FN.nodup_ok(nodup, ws),
                            FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(restg)),
                            ng)
                  +ng_rest = Logic.Proof.and_true_r(FN.FN.nodup_ok(nodup, ws),
                               FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(restg)),
                               ng)
                  +ndh : {FN.FN.no_dup_ref(ws) == True{} : Bool} =
                    Equal.trans(Bool, FN.FN.no_dup_ref(ws),
                      FN.FN.nodup_ok(nodup, ws), True{},
                      Equal.cong(Bool, Bool, b => FN.FN.nodup_ok(b, ws),
                        True{}, nodup, Equal.sym(Bool, nodup, True{}, end)),
                      ndh0)
                  +hvc = FOpt.done_ws_valid_cost(ws, G, tr, c, hdws)
                  +hval = Logic.Proof.and_true_l(FVal.FV.valid_b(tr, G, ws),
                            Nat.is_le(Tree.cost(tr, ws), c), hvc)
                  +hcost = Logic.Proof.and_true_r(FVal.FV.valid_b(tr, G, ws),
                             Nat.is_le(Tree.cost(tr, ws), c), hvc)
                  +hc_ref = FOpt.done_ws_le_ref(ws, p, inf, G, tr, c, ble, hz,
                              h6, ndh, hdws)
                  +sr : Nat =
                    SolveRef.sat_add(inf, sum_ref,
                      Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, ws)))
                  FOpt.live_group_leaf(p, gs, G, C_root, n_root, has_buf, gG,
                    cwS, S, nodup, floor, inf, g, fb, f, ws, restg,
                    SolveFast.DoneItem{f, tr, c}, restb, tr, c,
                    done_rev, kids, sum, sum_ref, best, buf, limit, hbuf,
                    FS.FS.done_live(p, gs, gG, cwS, n, nodup, floor, inf, g, f,
                      tr, c, restb, kids, sum, best,
                      SolveFast.GuessRes{Nil{}, buf}),
                    ef, hbest, hval, hcost, hc_ref, hsum_ge, hkids,
                    buf_in => +hbuf_in => +hsum2 => +hkids2 =>
                      FOpt.live_groups_ok(restg, restb, p, gs, G, C_root, n_root,
                        has_buf, rwsG, cwS, S, nodup, floor, inf, g,
                        Groups.Group{fb, ws} <> done_rev,
                        Tree.Child{f, tr} <> kids,
                        SolveRef.sat_add(inf, sum, c), sr, best, buf_in, limit,
                        hbuf_in, bt, erwsG, hrwsG, wg, perm, hperm, hz, h1, h3, h6,
                        ag_rest, ng_rest, hbest, hok, hd, hsum2, hkids2, hbm2,
                        et))
                case SolveFast.ClassItem{+f, +cws, +wlen, +tlb}:
                  match restb:
                    case Nil{}:
                      +gG : SolveFast.GList = FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{})
                      Empty.absurd(
                        FOpt.StepRes(p, gs, G, C_root, n_root, has_buf, gG, cwS,
                          S, nodup, floor, inf, g,
                          SolveFast.ClassItem{f, cws, wlen, tlb} <> Nil{},
                          kids, sum, best, buf, limit,
                          Fold.OQ.ks_cost(inf, S,
                            Eval.Eval.items(p, G, S, g,
                              Groups.Group{fb, ws} <> restg, Nil{}, sum_ref, inf))),
                        hbm)
                    case Con{it2, restb2}:
                      match it2:
                        case SolveFast.Add{+f2, +tlb2}:
                          (+ble, bt) = bounds
                          (eh, et) = ec
                          +n : Nat = Groups.len_words(S)
                          +gG : SolveFast.GList = FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{})
                          +ef = Arr.Arr.dpair_l({f == fb : +List<Feedback.Color>},
                                  Arr.Arr.DPair<{f2 == fb : +List<Feedback.Color>},
                                    Arr.Arr.DPair<
                                      {SolveFast.cwords_words(cws) == ws
                                       : +List<+List<Nat>>},
                                      Arr.Arr.DPair<{wlen == Groups.len_words(ws) : Nat},
                                        Arr.Arr.DPair<
                                          {FH.FH.cwords_ok_if(has_buf, G, C_root, n_root, cws)
                                           == True{} : Bool},
                                          Arr.Arr.DPair<
                                            {FH.FH.tail_lb_ok_b(G, nodup, n, restb2, tlb)
                                             == True{} : Bool},
                                            Arr.Arr.DPair<{tlb2 == tlb : Nat},
                                              FH.FH.BodyMatch(G, C_root, n_root,
                                                has_buf, nodup, n, restg, restb2)>>>>>>,
                                  hbm)
                          +r1 = Arr.Arr.dpair_r({f == fb : +List<Feedback.Color>},
                                  Arr.Arr.DPair<{f2 == fb : +List<Feedback.Color>},
                                    Arr.Arr.DPair<
                                      {SolveFast.cwords_words(cws) == ws
                                       : +List<+List<Nat>>},
                                      Arr.Arr.DPair<{wlen == Groups.len_words(ws) : Nat},
                                        Arr.Arr.DPair<
                                          {FH.FH.cwords_ok_if(has_buf, G, C_root, n_root, cws)
                                           == True{} : Bool},
                                          Arr.Arr.DPair<
                                            {FH.FH.tail_lb_ok_b(G, nodup, n, restb2, tlb)
                                             == True{} : Bool},
                                            Arr.Arr.DPair<{tlb2 == tlb : Nat},
                                              FH.FH.BodyMatch(G, C_root, n_root,
                                                has_buf, nodup, n, restg, restb2)>>>>>>,
                                  hbm)
                          +ef2 = Arr.Arr.dpair_l({f2 == fb : +List<Feedback.Color>},
                                   Arr.Arr.DPair<
                                     {SolveFast.cwords_words(cws) == ws
                                      : +List<+List<Nat>>},
                                     Arr.Arr.DPair<{wlen == Groups.len_words(ws) : Nat},
                                       Arr.Arr.DPair<
                                         {FH.FH.cwords_ok_if(has_buf, G, C_root, n_root, cws)
                                          == True{} : Bool},
                                         Arr.Arr.DPair<
                                           {FH.FH.tail_lb_ok_b(G, nodup, n, restb2, tlb)
                                            == True{} : Bool},
                                           Arr.Arr.DPair<{tlb2 == tlb : Nat},
                                             FH.FH.BodyMatch(G, C_root, n_root,
                                               has_buf, nodup, n, restg, restb2)>>>>>,
                                   r1)
                          +r2 = Arr.Arr.dpair_r({f2 == fb : +List<Feedback.Color>},
                                  Arr.Arr.DPair<
                                    {SolveFast.cwords_words(cws) == ws
                                     : +List<+List<Nat>>},
                                    Arr.Arr.DPair<{wlen == Groups.len_words(ws) : Nat},
                                      Arr.Arr.DPair<
                                        {FH.FH.cwords_ok_if(has_buf, G, C_root, n_root, cws)
                                         == True{} : Bool},
                                        Arr.Arr.DPair<
                                          {FH.FH.tail_lb_ok_b(G, nodup, n, restb2, tlb)
                                           == True{} : Bool},
                                          Arr.Arr.DPair<{tlb2 == tlb : Nat},
                                            FH.FH.BodyMatch(G, C_root, n_root,
                                              has_buf, nodup, n, restg, restb2)>>>>>,
                                  r1)
                          +ecws = Arr.Arr.dpair_l(
                                    {SolveFast.cwords_words(cws) == ws
                                     : +List<+List<Nat>>},
                                    Arr.Arr.DPair<{wlen == Groups.len_words(ws) : Nat},
                                      Arr.Arr.DPair<
                                        {FH.FH.cwords_ok_if(has_buf, G, C_root, n_root, cws)
                                         == True{} : Bool},
                                        Arr.Arr.DPair<
                                          {FH.FH.tail_lb_ok_b(G, nodup, n, restb2, tlb)
                                           == True{} : Bool},
                                          Arr.Arr.DPair<{tlb2 == tlb : Nat},
                                            FH.FH.BodyMatch(G, C_root, n_root,
                                              has_buf, nodup, n, restg, restb2)>>>>,
                                    r2)
                          +r3 = Arr.Arr.dpair_r(
                                  {SolveFast.cwords_words(cws) == ws
                                   : +List<+List<Nat>>},
                                  Arr.Arr.DPair<{wlen == Groups.len_words(ws) : Nat},
                                    Arr.Arr.DPair<
                                      {FH.FH.cwords_ok_if(has_buf, G, C_root, n_root, cws)
                                       == True{} : Bool},
                                      Arr.Arr.DPair<
                                        {FH.FH.tail_lb_ok_b(G, nodup, n, restb2, tlb)
                                         == True{} : Bool},
                                        Arr.Arr.DPair<{tlb2 == tlb : Nat},
                                          FH.FH.BodyMatch(G, C_root, n_root,
                                            has_buf, nodup, n, restg, restb2)>>>>,
                                  r2)
                          +elen = Arr.Arr.dpair_l({wlen == Groups.len_words(ws) : Nat},
                                    Arr.Arr.DPair<
                                      {FH.FH.cwords_ok_if(has_buf, G, C_root, n_root, cws)
                                       == True{} : Bool},
                                      Arr.Arr.DPair<
                                        {FH.FH.tail_lb_ok_b(G, nodup, n, restb2, tlb)
                                         == True{} : Bool},
                                        Arr.Arr.DPair<{tlb2 == tlb : Nat},
                                          FH.FH.BodyMatch(G, C_root, n_root,
                                            has_buf, nodup, n, restg, restb2)>>>,
                                    r3)
                          +r4 = Arr.Arr.dpair_r({wlen == Groups.len_words(ws) : Nat},
                                  Arr.Arr.DPair<
                                    {FH.FH.cwords_ok_if(has_buf, G, C_root, n_root, cws)
                                     == True{} : Bool},
                                    Arr.Arr.DPair<
                                      {FH.FH.tail_lb_ok_b(G, nodup, n, restb2, tlb)
                                       == True{} : Bool},
                                      Arr.Arr.DPair<{tlb2 == tlb : Nat},
                                        FH.FH.BodyMatch(G, C_root, n_root,
                                          has_buf, nodup, n, restg, restb2)>>>,
                                  r3)
                          +hcws = Arr.Arr.dpair_l(
                                    {FH.FH.cwords_ok_if(has_buf, G, C_root, n_root, cws)
                                     == True{} : Bool},
                                    Arr.Arr.DPair<
                                      {FH.FH.tail_lb_ok_b(G, nodup, n, restb2, tlb)
                                       == True{} : Bool},
                                      Arr.Arr.DPair<{tlb2 == tlb : Nat},
                                        FH.FH.BodyMatch(G, C_root, n_root,
                                          has_buf, nodup, n, restg, restb2)>>,
                                    r4)
                          +r5 = Arr.Arr.dpair_r(
                                  {FH.FH.cwords_ok_if(has_buf, G, C_root, n_root, cws)
                                   == True{} : Bool},
                                  Arr.Arr.DPair<
                                    {FH.FH.tail_lb_ok_b(G, nodup, n, restb2, tlb)
                                     == True{} : Bool},
                                    Arr.Arr.DPair<{tlb2 == tlb : Nat},
                                      FH.FH.BodyMatch(G, C_root, n_root,
                                        has_buf, nodup, n, restg, restb2)>>,
                                  r4)
                          +etlb = Arr.Arr.dpair_l(
                                    {FH.FH.tail_lb_ok_b(G, nodup, n, restb2, tlb)
                                     == True{} : Bool},
                                    Arr.Arr.DPair<{tlb2 == tlb : Nat},
                                      FH.FH.BodyMatch(G, C_root, n_root,
                                        has_buf, nodup, n, restg, restb2)>,
                                    r5)
                          +r6 = Arr.Arr.dpair_r(
                                  {FH.FH.tail_lb_ok_b(G, nodup, n, restb2, tlb)
                                   == True{} : Bool},
                                  Arr.Arr.DPair<{tlb2 == tlb : Nat},
                                    FH.FH.BodyMatch(G, C_root, n_root,
                                      has_buf, nodup, n, restg, restb2)>,
                                  r5)
                          +etlb2 = Arr.Arr.dpair_l({tlb2 == tlb : Nat},
                                     FH.FH.BodyMatch(G, C_root, n_root,
                                       has_buf, nodup, n, restg, restb2), r6)
                          +hbm2 = Arr.Arr.dpair_r({tlb2 == tlb : Nat},
                                    FH.FH.BodyMatch(G, C_root, n_root,
                                      has_buf, nodup, n, restg, restb2), r6)
                          +ag_rest = Logic.Proof.and_true_r(FO.FO.all_in_ref(ws, G),
                                       FO.FO.all_in_jobs_b(MV.MV.next_groups(restg), G),
                                       ag)
                          +ng_rest = Logic.Proof.and_true_r(FN.FN.nodup_ok(nodup, ws),
                                       FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(restg)),
                                       ng)
                          +sr : Nat =
                            SolveRef.sat_add(inf, sum_ref,
                              Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, ws)))
                          MV.MV.use_pair(
                            FOpt.StepRes(p, gs, G, C_root, n_root, has_buf, gG,
                              cwS, S, nodup, floor, inf, g,
                              SolveFast.ClassItem{f, cws, wlen, tlb}
                              <> (SolveFast.Add{f2, tlb2} <> restb2),
                              kids, sum, best, buf, limit,
                              Fold.OQ.ks_cost(inf, S,
                                Eval.Eval.items(p, G, S, g,
                                  Groups.Group{fb, ws} <> restg, Nil{}, sum_ref,
                                  inf))),
                            MV.MV.Bounds(p, MV.MV.next_groups(restg)),
                            MV.MV.Bounds(p, MV.MV.next_groups(restg)),
                            FOpt.bounds_copy(p, MV.MV.next_groups(restg), bt),
                            bt1 => bt2 =>
                              FOpt.live_group_class_dup1(p, gs, G, C_root,
                                n_root, has_buf, rwsG, cwS, S, nodup, floor,
                                inf, g, fb, f, f2, ws, cws, wlen, tlb, tlb2,
                                restg, restb2, done_rev, kids, sum, sum_ref,
                                best, buf, limit, hbuf, FH.FH.buf_dup(buf),
                                bt2, erwsG, hrwsG, ef, ef2, ecws, elen, hcws,
                                etlb, etlb2, hz, h3, h6, ng_rest, hbest, hok,
                                hd, hsum_ge, hkids, hbm2, eh,
                                +search_in => buf_in => +hbuf_in => +hsum2 => +hkids2 =>
                                  FOpt.live_groups_ok(restg, restb2, p, gs, G,
                                    C_root, n_root, has_buf, rwsG, cwS, S, nodup,
                                    floor, inf, g,
                                    Groups.Group{fb, ws} <> done_rev,
                                    Tree.Child{f2, Eval.Eval.tree_of(search_in)}
                                      <> kids,
                                    SolveRef.sat_add(inf, sum,
                                      Eval.Eval.cost_of(search_in)),
                                    sr, best, buf_in, limit, hbuf_in, bt1, erwsG,
                                    hrwsG, wg, perm, hperm, hz, h1, h3, h6,
                                    ag_rest, ng_rest, hbest, hok, hd, hsum2,
                                    hkids2, hbm2, et)))
                        case SolveFast.Begin{g2}:
                          +gG : SolveFast.GList = FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{})
                          Empty.absurd(
                            FOpt.StepRes(p, gs, G, C_root, n_root, has_buf, gG,
                              cwS, S, nodup, floor, inf, g,
                              SolveFast.ClassItem{f, cws, wlen, tlb}
                              <> (SolveFast.Begin{g2} <> restb2),
                              kids, sum, best, buf, limit,
                              Fold.OQ.ks_cost(inf, S,
                                Eval.Eval.items(p, G, S, g,
                                  Groups.Group{fb, ws} <> restg, Nil{},
                                  sum_ref, inf))), hbm)
                        case SolveFast.ClassItem{fa, ca, la, ta}:
                          +gG : SolveFast.GList = FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{})
                          Empty.absurd(
                            FOpt.StepRes(p, gs, G, C_root, n_root, has_buf, gG,
                              cwS, S, nodup, floor, inf, g,
                              SolveFast.ClassItem{f, cws, wlen, tlb}
                              <> (SolveFast.ClassItem{fa, ca, la, ta} <> restb2),
                              kids, sum, best, buf, limit,
                              Fold.OQ.ks_cost(inf, S,
                                Eval.Eval.items(p, G, S, g,
                                  Groups.Group{fb, ws} <> restg, Nil{},
                                  sum_ref, inf))), hbm)
                        case SolveFast.OneItem{fa, wa}:
                          +gG : SolveFast.GList = FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{})
                          Empty.absurd(
                            FOpt.StepRes(p, gs, G, C_root, n_root, has_buf, gG,
                              cwS, S, nodup, floor, inf, g,
                              SolveFast.ClassItem{f, cws, wlen, tlb}
                              <> (SolveFast.OneItem{fa, wa} <> restb2),
                              kids, sum, best, buf, limit,
                              Fold.OQ.ks_cost(inf, S,
                                Eval.Eval.items(p, G, S, g,
                                  Groups.Group{fb, ws} <> restg, Nil{},
                                  sum_ref, inf))), hbm)
                        case SolveFast.TwoItem{fa, wa1, wa2}:
                          +gG : SolveFast.GList = FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{})
                          Empty.absurd(
                            FOpt.StepRes(p, gs, G, C_root, n_root, has_buf, gG,
                              cwS, S, nodup, floor, inf, g,
                              SolveFast.ClassItem{f, cws, wlen, tlb}
                              <> (SolveFast.TwoItem{fa, wa1, wa2} <> restb2),
                              kids, sum, best, buf, limit,
                              Fold.OQ.ks_cost(inf, S,
                                Eval.Eval.items(p, G, S, g,
                                  Groups.Group{fb, ws} <> restg, Nil{},
                                  sum_ref, inf))), hbm)
                        case SolveFast.DoneItem{fa, tra, ca}:
                          +gG : SolveFast.GList = FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{})
                          Empty.absurd(
                            FOpt.StepRes(p, gs, G, C_root, n_root, has_buf, gG,
                              cwS, S, nodup, floor, inf, g,
                              SolveFast.ClassItem{f, cws, wlen, tlb}
                              <> (SolveFast.DoneItem{fa, tra, ca} <> restb2),
                              kids, sum, best, buf, limit,
                              Fold.OQ.ks_cost(inf, S,
                                Eval.Eval.items(p, G, S, g,
                                  Groups.Group{fb, ws} <> restg, Nil{},
                                  sum_ref, inf))), hbm)
                        case SolveFast.End{}:
                          +gG : SolveFast.GList = FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{})
                          Empty.absurd(
                            FOpt.StepRes(p, gs, G, C_root, n_root, has_buf, gG,
                              cwS, S, nodup, floor, inf, g,
                              SolveFast.ClassItem{f, cws, wlen, tlb}
                              <> (SolveFast.End{} <> restb2),
                              kids, sum, best, buf, limit,
                              Fold.OQ.ks_cost(inf, S,
                                Eval.Eval.items(p, G, S, g,
                                  Groups.Group{fb, ws} <> restg, Nil{},
                                  sum_ref, inf))), hbm)
                case SolveFast.Add{f2, tlb2}:
                  +gG : SolveFast.GList = FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{})
                  Empty.absurd(
                    FOpt.StepRes(p, gs, G, C_root, n_root, has_buf, gG, cwS, S,
                      nodup, floor, inf, g, SolveFast.Add{f2, tlb2} <> restb,
                      kids, sum, best, buf, limit,
                      Fold.OQ.ks_cost(inf, S,
                        Eval.Eval.items(p, G, S, g,
                          Groups.Group{fb, ws} <> restg, Nil{}, sum_ref, inf))),
                    hbm)
                case SolveFast.End{}:
                  +gG : SolveFast.GList = FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{})
                  Empty.absurd(
                    FOpt.StepRes(p, gs, G, C_root, n_root, has_buf, gG, cwS, S,
                      nodup, floor, inf, g, SolveFast.End{} <> restb,
                      kids, sum, best, buf, limit,
                      Fold.OQ.ks_cost(inf, S,
                        Eval.Eval.items(p, G, S, g,
                          Groups.Group{fb, ws} <> restg, Nil{}, sum_ref, inf))),
                    hbm)

# ---------------------------------------------------------------------------
# Staged `GList` walk with `FloorMode` and 5-case semantic `FH.GuessWit`
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

def FOpt.guess_skip_lb_eq(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +g: +List<Nat>, +best: SolveRef.Best,
    us: Bool,
    +eus: {us == Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{}))
           : Bool},
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    +hle: {Nat.is_le(Eval.Eval.cost_of(best),
             SolveFast.lower_bound(Groups.len_words(S),
               Groups.groups_build(g, S, Nil{}))) == True{} : Bool}) ->
  {Eval.Eval.guess_bool(p, G, S, g, Groups.groups_build(g, S, Nil{}), inf, us,
     best) == best : SolveRef.Best}:
  match us:
    case False{}:
      {==}
    case True{}:
      FLB.FS.block_skip_eq(p, inf, G, S, g, Groups.groups_build(g, S, Nil{}),
        best,
        Equal.sym(Bool, True{},
          Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})), eus),
        ele, hz, hbest, hle)

def FOpt.guess_skip_self_eq(mode: FOpt.FloorMode, +p: Nat, +inf: Nat,
    +G: +List<+List<Nat>>, +S: +List<+List<Nat>>, +g: +List<Nat>,
    +best: SolveRef.Best,
    +efl: {FOpt.floor_val(mode, Groups.len_words(S))
           == Nat.add(Groups.len_words(S), Groups.len_words(S)) : Nat},
    +hmem: {Tree.member_word(g, S) == True{} : Bool},
    +hinv: {FOpt.floor_inv(mode, p, inf, G, S, best) == True{} : Bool}) ->
  {Eval.Eval.guess(p, G, S, g, inf, best) == best : SolveRef.Best}:
  match mode:
    case FloorInit{}:
      match S:
        case Nil{}:
          Empty.absurd(
            {Eval.Eval.guess(p, G, Nil{}, g, inf, best) == best : SolveRef.Best},
            Logic.Proof.false_ne_true(hmem))
        case Con{+w, +t}:
          Empty.absurd(
            {Eval.Eval.guess(p, G, w <> t, g, inf, best) == best : SolveRef.Best},
            FOpt.init_floor_ne_2n(w, t, efl))
    case FloorAfterS{}:
      FVal.FV.after_s_guess_skip_in_us(p, inf, G, S, g, best, hmem, hinv,
        Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})), {==})

def FOpt.step_res_to_guess_perm(+p: Nat, +gs: SolveFast.GList,
    +G: +List<+List<Nat>>, +C_root: +List<+List<Nat>>, +n_root: Nat,
    +has_buf: Bool, +gG: SolveFast.GList, +cwS: +List<SolveFast.CWord>,
    +S: +List<+List<Nat>>, +nodup: Bool, +floor: Nat, +inf: Nat,
    +g: +List<Nat>, +ord: +List<Groups.Group>, +cs: +List<SolveFast.Item>,
    +best: SolveRef.Best, -buf: SolveFast.Buf5, +limit: Nat,
    +perm: FP.FP.Perm,
    +hperm: FP.FP.PermOk(perm, Groups.groups_build(g, S, Nil{}), ord),
    +hus: {Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{}))
           == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    r: FOpt.StepRes(p, gs, G, C_root, n_root, has_buf, gG, cwS, S, nodup,
         floor, inf, Nil{}, cs, Nil{}, 0n, best, buf, limit,
         Fold.OQ.ks_cost(inf, S,
           Eval.Eval.items(p, G, S, g, ord, Nil{}, 0n, inf)))) ->
  FOpt.StepRes(p, gs, G, C_root, n_root, has_buf, gG, cwS, S, nodup,
    floor, inf, Nil{}, cs, Nil{}, 0n, best, buf, limit,
    Eval.Eval.cost_of(Eval.Eval.guess(p, G, S, g, inf, best))):
  match r:
    case Tuple{+best2, p0}:
      match p0:
        case Tuple{buf2, p1}:
          match p1:
            case Tuple{+eq2, p2}:
              match p2:
                case Tuple{+hbuf2, p3}:
                  match p3:
                    case Tuple{+hok2, p4}:
                      match p4:
                        case Tuple{+hleb, hle_ord}:
                          +full : +List<Groups.Group> =
                            Groups.groups_build(g, S, Nil{})
                          +ks : Eval.KS =
                            Eval.Eval.items(p, G, S, g, full, Nil{}, 0n, inf)
                          +cc : Nat = Fold.OQ.ks_cost(inf, S, ks)
                          +ct : Tree.Tree = Fold.OQ.ks_tree(g, ks)
                          +hb2_inf : {Nat.is_le(Eval.Eval.cost_of(best2), inf)
                                      == True{} : Bool} =
                            NatProof.Nat.is_le_trans(Eval.Eval.cost_of(best2),
                              Eval.Eval.cost_of(best), inf, hleb, hbest)
                          +hle_cc : {Nat.is_le(Eval.Eval.cost_of(best2), cc)
                                     == True{} : Bool} =
                            FP.FP.ks_cost_le_of_perm(perm, p, inf, G, S, g,
                              full, ord, Eval.Eval.cost_of(best2), hperm,
                              hb2_inf, hle_ord)
                          +eg_blk : {Eval.Eval.guess(p, G, S, g, inf, best)
                                     == Eval.Eval.block(p, G, S, g, inf, full, best)
                                     : SolveRef.Best} =
                            Equal.cong(Bool, SolveRef.Best,
                              u => Eval.Eval.guess_bool(p, G, S, g, full, inf, u,
                                     best),
                              Groups.groups_smaller(S, full), True{}, hus)
                          +hlet : {Nat.is_le(Eval.Eval.cost_of(best2),
                                     Eval.Eval.cost_of(
                                       Eval.Eval.guess(p, G, S, g, inf, best)))
                                   == True{} : Bool} =
                            Fold.OQ.le_cong_r(Eval.Eval.cost_of(best2),
                              Eval.Eval.cost_of(SolveRef.better(cc, ct, best)),
                              Eval.Eval.cost_of(
                                Eval.Eval.guess(p, G, S, g, inf, best)),
                              Equal.trans(Nat,
                                Eval.Eval.cost_of(SolveRef.better(cc, ct, best)),
                                Eval.Eval.cost_of(
                                  Eval.Eval.block(p, G, S, g, inf, full, best)),
                                Eval.Eval.cost_of(
                                  Eval.Eval.guess(p, G, S, g, inf, best)),
                                Equal.sym(Nat,
                                  Eval.Eval.cost_of(
                                    Eval.Eval.block(p, G, S, g, inf, full, best)),
                                  Eval.Eval.cost_of(SolveRef.better(cc, ct, best)),
                                  Fold.OQ.block_cost_eq(inf, g, S, ks, best)),
                                Equal.cong(SolveRef.Best, Nat, Eval.Eval.cost_of,
                                  Eval.Eval.block(p, G, S, g, inf, full, best),
                                  Eval.Eval.guess(p, G, S, g, inf, best),
                                  Equal.sym(SolveRef.Best,
                                    Eval.Eval.guess(p, G, S, g, inf, best),
                                    Eval.Eval.block(p, G, S, g, inf, full, best),
                                    eg_blk))),
                              FVal.FV.le_better_of_le_both(
                                Eval.Eval.cost_of(best2), cc, ct, best,
                                hle_cc, hleb))
                          Tuple{best2, Tuple{buf2,
                            Tuple{eq2, Tuple{hbuf2,
                              Tuple{hok2, Tuple{hleb, hlet}}}}}}

def FOpt.guess_case_ok(+p: Nat, +gs: SolveFast.GList, +G: +List<+List<Nat>>,
    +C_root: +List<+List<Nat>>, +n_root: Nat, +has_buf: Bool,
    +rwsG: +List<FT.FT.RowWord>, +cwS: +List<SolveFast.CWord>,
    +S: +List<+List<Nat>>, +nodup: Bool, +mode: FOpt.FloorMode, +inf: Nat,
    +g: +List<Nat>, +items: +List<SolveFast.Item>, +best: SolveRef.Best,
    buf: SolveFast.Buf5, +limit: Nat,
    +hbuf: FH.FH.BufOk(G, C_root, n_root, has_buf, nodup, buf),
    +gw: FH.FH.GuessWit<G, C_root, n_root, has_buf, nodup, g, S,
           Groups.len_words(S), FOpt.floor_val(mode, Groups.len_words(S)),
           best, items>,
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
            FOpt.floor_val(mode, Groups.len_words(S)), best) == False{} : Bool},
    +hinv: {FOpt.floor_inv(mode, p, inf, G, S, best) == True{} : Bool},
    ecif: FOpt.EClassIf(
            Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
            p, inf, G, C_root, n_root, has_buf, nodup,
            Groups.groups_build(g, S, Nil{}))) ->
  FOpt.StepRes(p, gs, G, C_root, n_root, has_buf,
    FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS, S, nodup,
    FOpt.floor_val(mode, Groups.len_words(S)), inf, Nil{}, items, Nil{}, 0n,
    best, buf, limit,
    Eval.Eval.cost_of(Eval.Eval.guess(p, G, S, g, inf, best))):
  match gw:
    case FH.GWit{gc, hgc}:
      match gc:
        case FH.GCSkipSelf{}:
          +n : Nat = Groups.len_words(S)
          +fl : Nat = FOpt.floor_val(mode, n)
          +gG : SolveFast.GList = FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{})
          +eits = Arr.Arr.dpair_l({items == Nil{} : +List<SolveFast.Item>},
                    Arr.Arr.DPair<{nodup == True{} : Bool},
                      Arr.Arr.DPair<{fl == Nat.add(n, n) : Nat},
                        {Tree.member_word(g, S) == True{} : Bool}>>, hgc)
          +r1 = Arr.Arr.dpair_r({items == Nil{} : +List<SolveFast.Item>},
                  Arr.Arr.DPair<{nodup == True{} : Bool},
                    Arr.Arr.DPair<{fl == Nat.add(n, n) : Nat},
                      {Tree.member_word(g, S) == True{} : Bool}>>, hgc)
          +r2 = Arr.Arr.dpair_r({nodup == True{} : Bool},
                  Arr.Arr.DPair<{fl == Nat.add(n, n) : Nat},
                    {Tree.member_word(g, S) == True{} : Bool}>, r1)
          +efl = Arr.Arr.dpair_l({fl == Nat.add(n, n) : Nat},
                   {Tree.member_word(g, S) == True{} : Bool}, r2)
          +hmem = Arr.Arr.dpair_r({fl == Nat.add(n, n) : Nat},
                    {Tree.member_word(g, S) == True{} : Bool}, r2)
          +geq = FOpt.guess_skip_self_eq(mode, p, inf, G, S, g, best, efl, hmem,
                   hinv)
          %Equal.sym(+List<SolveFast.Item>, items, Nil{}, eits) :
            FOpt.StepRes(p, gs, G, C_root, n_root, has_buf, gG, cwS, S, nodup,
              fl, inf, Nil{}, _, Nil{}, 0n, best, buf, limit,
              Eval.Eval.cost_of(Eval.Eval.guess(p, G, S, g, inf, best)))
          FOpt.step_res_keep(p, gs, G, C_root, n_root, has_buf, gG, cwS, S,
            nodup, fl, inf, best, buf, limit,
            Eval.Eval.cost_of(Eval.Eval.guess(p, G, S, g, inf, best)),
            hbuf, hok, hd,
            NatProof.Nat.is_le_eq_r(Eval.Eval.cost_of(best),
              Eval.Eval.cost_of(best),
              Eval.Eval.cost_of(Eval.Eval.guess(p, G, S, g, inf, best)),
              Equal.cong(SolveRef.Best, Nat, Eval.Eval.cost_of, best,
                Eval.Eval.guess(p, G, S, g, inf, best),
                Equal.sym(SolveRef.Best,
                  Eval.Eval.guess(p, G, S, g, inf, best), best, geq)),
              NatProof.Nat.is_le_refl(Eval.Eval.cost_of(best))))
        case FH.GCSkipUnusable{}:
          +n : Nat = Groups.len_words(S)
          +fl : Nat = FOpt.floor_val(mode, n)
          +gG : SolveFast.GList = FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{})
          +full : +List<Groups.Group> = Groups.groups_build(g, S, Nil{})
          +eits = Arr.Arr.dpair_l({items == Nil{} : +List<SolveFast.Item>},
                    {Groups.groups_smaller(S, full) == False{} : Bool}, hgc)
          +husf = Arr.Arr.dpair_r({items == Nil{} : +List<SolveFast.Item>},
                    {Groups.groups_smaller(S, full) == False{} : Bool}, hgc)
          +geq : {Eval.Eval.guess(p, G, S, g, inf, best) == best : SolveRef.Best} =
            Equal.cong(Bool, SolveRef.Best,
              u => Eval.Eval.guess_bool(p, G, S, g, full, inf, u, best),
              Groups.groups_smaller(S, full), False{}, husf)
          %Equal.sym(+List<SolveFast.Item>, items, Nil{}, eits) :
            FOpt.StepRes(p, gs, G, C_root, n_root, has_buf, gG, cwS, S, nodup,
              fl, inf, Nil{}, _, Nil{}, 0n, best, buf, limit,
              Eval.Eval.cost_of(Eval.Eval.guess(p, G, S, g, inf, best)))
          FOpt.step_res_keep(p, gs, G, C_root, n_root, has_buf, gG, cwS, S,
            nodup, fl, inf, best, buf, limit,
            Eval.Eval.cost_of(Eval.Eval.guess(p, G, S, g, inf, best)),
            hbuf, hok, hd,
            NatProof.Nat.is_le_eq_r(Eval.Eval.cost_of(best),
              Eval.Eval.cost_of(best),
              Eval.Eval.cost_of(Eval.Eval.guess(p, G, S, g, inf, best)),
              Equal.cong(SolveRef.Best, Nat, Eval.Eval.cost_of, best,
                Eval.Eval.guess(p, G, S, g, inf, best),
                Equal.sym(SolveRef.Best,
                  Eval.Eval.guess(p, G, S, g, inf, best), best, geq)),
              NatProof.Nat.is_le_refl(Eval.Eval.cost_of(best))))
        case FH.GCSkipPre{}:
          +n : Nat = Groups.len_words(S)
          +fl : Nat = FOpt.floor_val(mode, n)
          +gG : SolveFast.GList = FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{})
          +eits = Arr.Arr.dpair_l({items == Nil{} : +List<SolveFast.Item>},
                    {Nat.is_le(Eval.Eval.cost_of(best),
                       SolveFast.pre_lb(n, g, S)) == True{} : Bool}, hgc)
          +hle = Arr.Arr.dpair_r({items == Nil{} : +List<SolveFast.Item>},
                   {Nat.is_le(Eval.Eval.cost_of(best),
                      SolveFast.pre_lb(n, g, S)) == True{} : Bool}, hgc)
          +geq = FLB.FS.pre_guess_skip_eq(p, inf, G, S, g, best, ele, hz, hbest,
                   hle)
          %Equal.sym(+List<SolveFast.Item>, items, Nil{}, eits) :
            FOpt.StepRes(p, gs, G, C_root, n_root, has_buf, gG, cwS, S, nodup,
              fl, inf, Nil{}, _, Nil{}, 0n, best, buf, limit,
              Eval.Eval.cost_of(Eval.Eval.guess(p, G, S, g, inf, best)))
          FOpt.step_res_keep(p, gs, G, C_root, n_root, has_buf, gG, cwS, S,
            nodup, fl, inf, best, buf, limit,
            Eval.Eval.cost_of(Eval.Eval.guess(p, G, S, g, inf, best)),
            hbuf, hok, hd,
            NatProof.Nat.is_le_eq_r(Eval.Eval.cost_of(best),
              Eval.Eval.cost_of(best),
              Eval.Eval.cost_of(Eval.Eval.guess(p, G, S, g, inf, best)),
              Equal.cong(SolveRef.Best, Nat, Eval.Eval.cost_of, best,
                Eval.Eval.guess(p, G, S, g, inf, best),
                Equal.sym(SolveRef.Best,
                  Eval.Eval.guess(p, G, S, g, inf, best), best, geq)),
              NatProof.Nat.is_le_refl(Eval.Eval.cost_of(best))))
        case FH.GCSkipLb{}:
          +n : Nat = Groups.len_words(S)
          +fl : Nat = FOpt.floor_val(mode, n)
          +gG : SolveFast.GList = FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{})
          +full : +List<Groups.Group> = Groups.groups_build(g, S, Nil{})
          +eits = Arr.Arr.dpair_l({items == Nil{} : +List<SolveFast.Item>},
                    {Nat.is_le(Eval.Eval.cost_of(best),
                       SolveFast.lower_bound(n, full)) == True{} : Bool}, hgc)
          +hle = Arr.Arr.dpair_r({items == Nil{} : +List<SolveFast.Item>},
                   {Nat.is_le(Eval.Eval.cost_of(best),
                      SolveFast.lower_bound(n, full)) == True{} : Bool}, hgc)
          +geq = FOpt.guess_skip_lb_eq(p, inf, G, S, g, best,
                   Groups.groups_smaller(S, full), {==}, ele, hz, hbest, hle)
          %Equal.sym(+List<SolveFast.Item>, items, Nil{}, eits) :
            FOpt.StepRes(p, gs, G, C_root, n_root, has_buf, gG, cwS, S, nodup,
              fl, inf, Nil{}, _, Nil{}, 0n, best, buf, limit,
              Eval.Eval.cost_of(Eval.Eval.guess(p, G, S, g, inf, best)))
          FOpt.step_res_keep(p, gs, G, C_root, n_root, has_buf, gG, cwS, S,
            nodup, fl, inf, best, buf, limit,
            Eval.Eval.cost_of(Eval.Eval.guess(p, G, S, g, inf, best)),
            hbuf, hok, hd,
            NatProof.Nat.is_le_eq_r(Eval.Eval.cost_of(best),
              Eval.Eval.cost_of(best),
              Eval.Eval.cost_of(Eval.Eval.guess(p, G, S, g, inf, best)),
              Equal.cong(SolveRef.Best, Nat, Eval.Eval.cost_of, best,
                Eval.Eval.guess(p, G, S, g, inf, best),
                Equal.sym(SolveRef.Best,
                  Eval.Eval.guess(p, G, S, g, inf, best), best, geq)),
              NatProof.Nat.is_le_refl(Eval.Eval.cost_of(best))))
        case FH.GCSkipBody{+ord, +body, +tot, +perm}:
          +n : Nat = Groups.len_words(S)
          +fl : Nat = FOpt.floor_val(mode, n)
          +gG : SolveFast.GList = FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{})
          +full : +List<Groups.Group> = Groups.groups_build(g, S, Nil{})
          +eits = Arr.Arr.dpair_l({items == Nil{} : +List<SolveFast.Item>},
                    Arr.Arr.DPair<{Groups.groups_smaller(S, full) == True{} : Bool},
                      Arr.Arr.DPair<FP.FP.PermOk(perm, full, ord),
                        Arr.Arr.DPair<
                          FH.FH.BodyMatch(G, C_root, n_root, has_buf, nodup, n,
                            ord, body),
                          Arr.Arr.DPair<
                            {FH.FH.tail_lb_ok_b(G, nodup, n, body, tot)
                             == True{} : Bool},
                            {Nat.is_le(Eval.Eval.cost_of(best), tot)
                             == True{} : Bool}>>>>, hgc)
          +r1 = Arr.Arr.dpair_r({items == Nil{} : +List<SolveFast.Item>},
                  Arr.Arr.DPair<{Groups.groups_smaller(S, full) == True{} : Bool},
                    Arr.Arr.DPair<FP.FP.PermOk(perm, full, ord),
                      Arr.Arr.DPair<
                        FH.FH.BodyMatch(G, C_root, n_root, has_buf, nodup, n,
                          ord, body),
                        Arr.Arr.DPair<
                          {FH.FH.tail_lb_ok_b(G, nodup, n, body, tot)
                           == True{} : Bool},
                          {Nat.is_le(Eval.Eval.cost_of(best), tot)
                           == True{} : Bool}>>>>, hgc)
          +hus = Arr.Arr.dpair_l({Groups.groups_smaller(S, full) == True{} : Bool},
                   Arr.Arr.DPair<FP.FP.PermOk(perm, full, ord),
                     Arr.Arr.DPair<
                       FH.FH.BodyMatch(G, C_root, n_root, has_buf, nodup, n,
                         ord, body),
                       Arr.Arr.DPair<
                         {FH.FH.tail_lb_ok_b(G, nodup, n, body, tot)
                          == True{} : Bool},
                         {Nat.is_le(Eval.Eval.cost_of(best), tot)
                          == True{} : Bool}>>>, r1)
          +r2 = Arr.Arr.dpair_r({Groups.groups_smaller(S, full) == True{} : Bool},
                  Arr.Arr.DPair<FP.FP.PermOk(perm, full, ord),
                    Arr.Arr.DPair<
                      FH.FH.BodyMatch(G, C_root, n_root, has_buf, nodup, n,
                        ord, body),
                      Arr.Arr.DPair<
                        {FH.FH.tail_lb_ok_b(G, nodup, n, body, tot)
                         == True{} : Bool},
                        {Nat.is_le(Eval.Eval.cost_of(best), tot)
                         == True{} : Bool}>>>, r1)
          +hperm = Arr.Arr.dpair_l(FP.FP.PermOk(perm, full, ord),
                     Arr.Arr.DPair<
                       FH.FH.BodyMatch(G, C_root, n_root, has_buf, nodup, n,
                         ord, body),
                       Arr.Arr.DPair<
                         {FH.FH.tail_lb_ok_b(G, nodup, n, body, tot)
                          == True{} : Bool},
                         {Nat.is_le(Eval.Eval.cost_of(best), tot)
                          == True{} : Bool}>>, r2)
          +r3 = Arr.Arr.dpair_r(FP.FP.PermOk(perm, full, ord),
                  Arr.Arr.DPair<
                    FH.FH.BodyMatch(G, C_root, n_root, has_buf, nodup, n,
                      ord, body),
                    Arr.Arr.DPair<
                      {FH.FH.tail_lb_ok_b(G, nodup, n, body, tot)
                       == True{} : Bool},
                      {Nat.is_le(Eval.Eval.cost_of(best), tot)
                       == True{} : Bool}>>, r2)
          +hbm = Arr.Arr.dpair_l(
                   FH.FH.BodyMatch(G, C_root, n_root, has_buf, nodup, n,
                     ord, body),
                   Arr.Arr.DPair<
                     {FH.FH.tail_lb_ok_b(G, nodup, n, body, tot)
                      == True{} : Bool},
                     {Nat.is_le(Eval.Eval.cost_of(best), tot)
                      == True{} : Bool}>, r3)
          +r4 = Arr.Arr.dpair_r(
                  FH.FH.BodyMatch(G, C_root, n_root, has_buf, nodup, n,
                    ord, body),
                  Arr.Arr.DPair<
                    {FH.FH.tail_lb_ok_b(G, nodup, n, body, tot)
                     == True{} : Bool},
                    {Nat.is_le(Eval.Eval.cost_of(best), tot)
                     == True{} : Bool}>, r3)
          +htlb = Arr.Arr.dpair_l(
                    {FH.FH.tail_lb_ok_b(G, nodup, n, body, tot) == True{} : Bool},
                    {Nat.is_le(Eval.Eval.cost_of(best), tot) == True{} : Bool},
                    r4)
          +hle_tot = Arr.Arr.dpair_r(
                       {FH.FH.tail_lb_ok_b(G, nodup, n, body, tot) == True{} : Bool},
                       {Nat.is_le(Eval.Eval.cost_of(best), tot) == True{} : Bool},
                       r4)
          bounds_full : MV.MV.Bounds(p, MV.MV.next_groups(full)) =
            MV.MV.group_bounds(p, S, full, ele,
              GM.GM.groups_smaller_sound(S, full, hus))
          bounds_ord : MV.MV.Bounds(p, MV.MV.next_groups(ord)) =
            FP.FP.bounds_perm(perm, p, full, ord, hperm, bounds_full)
          +ng_full = FN.FN.nodup_ok_next_groups(nodup, full, S,
                       CoverGroups.Cover.all_subseq_nil(g, S), nd)
          +ng_ord : {FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(ord))
                     == True{} : Bool} =
            Equal.trans(Bool, FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(ord)),
              FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(full)), True{},
              Equal.sym(Bool,
                FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(full)),
                FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(ord)),
                FP.FP.nodup_ok_jobs_perm(perm, nodup, full, ord, hperm)),
              ng_full)
          +hle_ord : {Nat.is_le(Eval.Eval.cost_of(best),
                        Fold.OQ.ks_cost(inf, S,
                          Eval.Eval.items(p, G, S, g, ord, Nil{}, 0n, inf)))
                      == True{} : Bool} =
            FOpt.body_lb_le_ks_cost(ord, body, p, inf, G, C_root, n_root,
              has_buf, S, nodup, g, 0n, Eval.Eval.cost_of(best), tot,
              bounds_ord, hz, h3, h6, ng_ord, hbest, hbm, htlb, hle_tot)
          +ks = Eval.Eval.items(p, G, S, g, full, Nil{}, 0n, inf)
          +cc : Nat = Fold.OQ.ks_cost(inf, S, ks)
          +ct : Tree.Tree = Fold.OQ.ks_tree(g, ks)
          +hle_cc : {Nat.is_le(Eval.Eval.cost_of(best), cc) == True{} : Bool} =
            FP.FP.ks_cost_le_of_perm(perm, p, inf, G, S, g, full, ord,
              Eval.Eval.cost_of(best), hperm, hbest, hle_ord)
          +eg_blk : {Eval.Eval.guess(p, G, S, g, inf, best)
                     == Eval.Eval.block(p, G, S, g, inf, full, best)
                     : SolveRef.Best} =
            Equal.cong(Bool, SolveRef.Best,
              u => Eval.Eval.guess_bool(p, G, S, g, full, inf, u, best),
              Groups.groups_smaller(S, full), True{}, hus)
          +hlet : {Nat.is_le(Eval.Eval.cost_of(best),
                     Eval.Eval.cost_of(Eval.Eval.guess(p, G, S, g, inf, best)))
                   == True{} : Bool} =
            Fold.OQ.le_cong_r(Eval.Eval.cost_of(best),
              Eval.Eval.cost_of(SolveRef.better(cc, ct, best)),
              Eval.Eval.cost_of(Eval.Eval.guess(p, G, S, g, inf, best)),
              Equal.trans(Nat,
                Eval.Eval.cost_of(SolveRef.better(cc, ct, best)),
                Eval.Eval.cost_of(Eval.Eval.block(p, G, S, g, inf, full, best)),
                Eval.Eval.cost_of(Eval.Eval.guess(p, G, S, g, inf, best)),
                Equal.sym(Nat,
                  Eval.Eval.cost_of(
                    Eval.Eval.block(p, G, S, g, inf, full, best)),
                  Eval.Eval.cost_of(SolveRef.better(cc, ct, best)),
                  Fold.OQ.block_cost_eq(inf, g, S, ks, best)),
                Equal.cong(SolveRef.Best, Nat, Eval.Eval.cost_of,
                  Eval.Eval.block(p, G, S, g, inf, full, best),
                  Eval.Eval.guess(p, G, S, g, inf, best),
                  Equal.sym(SolveRef.Best,
                    Eval.Eval.guess(p, G, S, g, inf, best),
                    Eval.Eval.block(p, G, S, g, inf, full, best), eg_blk))),
              FVal.FV.le_better_of_le_both(Eval.Eval.cost_of(best), cc, ct,
                best, hle_cc, NatProof.Nat.is_le_refl(Eval.Eval.cost_of(best))))
          %Equal.sym(+List<SolveFast.Item>, items, Nil{}, eits) :
            FOpt.StepRes(p, gs, G, C_root, n_root, has_buf, gG, cwS, S, nodup,
              fl, inf, Nil{}, _, Nil{}, 0n, best, buf, limit,
              Eval.Eval.cost_of(Eval.Eval.guess(p, G, S, g, inf, best)))
          FOpt.step_res_keep(p, gs, G, C_root, n_root, has_buf, gG, cwS, S,
            nodup, fl, inf, best, buf, limit,
            Eval.Eval.cost_of(Eval.Eval.guess(p, G, S, g, inf, best)),
            hbuf, hok, hd, hlet)
        case FH.GCLive{+ord, +body, +perm}:
          +n : Nat = Groups.len_words(S)
          +fl : Nat = FOpt.floor_val(mode, n)
          +gG : SolveFast.GList = FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{})
          +full : +List<Groups.Group> = Groups.groups_build(g, S, Nil{})
          +eits = Arr.Arr.dpair_l(
                    {items == SolveFast.Begin{g} <> body : +List<SolveFast.Item>},
                    Arr.Arr.DPair<{Groups.groups_smaller(S, full) == True{} : Bool},
                      Arr.Arr.DPair<FP.FP.PermOk(perm, full, ord),
                        FH.FH.BodyMatch(G, C_root, n_root, has_buf, nodup, n,
                          ord, body)>>, hgc)
          +r1 = Arr.Arr.dpair_r(
                  {items == SolveFast.Begin{g} <> body : +List<SolveFast.Item>},
                  Arr.Arr.DPair<{Groups.groups_smaller(S, full) == True{} : Bool},
                    Arr.Arr.DPair<FP.FP.PermOk(perm, full, ord),
                      FH.FH.BodyMatch(G, C_root, n_root, has_buf, nodup, n,
                        ord, body)>>, hgc)
          +hus = Arr.Arr.dpair_l({Groups.groups_smaller(S, full) == True{} : Bool},
                   Arr.Arr.DPair<FP.FP.PermOk(perm, full, ord),
                     FH.FH.BodyMatch(G, C_root, n_root, has_buf, nodup, n,
                       ord, body)>, r1)
          +r2 = Arr.Arr.dpair_r({Groups.groups_smaller(S, full) == True{} : Bool},
                  Arr.Arr.DPair<FP.FP.PermOk(perm, full, ord),
                    FH.FH.BodyMatch(G, C_root, n_root, has_buf, nodup, n,
                      ord, body)>, r1)
          +hperm = Arr.Arr.dpair_l(FP.FP.PermOk(perm, full, ord),
                     FH.FH.BodyMatch(G, C_root, n_root, has_buf, nodup, n,
                       ord, body), r2)
          +hbm = Arr.Arr.dpair_r(FP.FP.PermOk(perm, full, ord),
                   FH.FH.BodyMatch(G, C_root, n_root, has_buf, nodup, n,
                     ord, body), r2)
          ec_full : FOpt.EClass(p, inf, G, C_root, n_root, has_buf, nodup, full) =
            FOpt.eclass_of_if_true(Groups.groups_smaller(S, full), p, inf, G,
              C_root, n_root, has_buf, nodup, full, hus, ecif)
          ec_ord : FOpt.EClass(p, inf, G, C_root, n_root, has_buf, nodup, ord) =
            FOpt.eclass_perm(perm, p, inf, G, C_root, n_root, has_buf, nodup,
              full, ord, hperm, ec_full)
          bounds_full : MV.MV.Bounds(p, MV.MV.next_groups(full)) =
            MV.MV.group_bounds(p, S, full, ele,
              GM.GM.groups_smaller_sound(S, full, hus))
          bounds_ord : MV.MV.Bounds(p, MV.MV.next_groups(ord)) =
            FP.FP.bounds_perm(perm, p, full, ord, hperm, bounds_full)
          +ag_full = FO.FO.all_in_next_groups(full, S, G,
                       CoverGroups.Cover.all_subseq_nil(g, S), ai)
          +ag_ord : {FO.FO.all_in_jobs_b(MV.MV.next_groups(ord), G)
                     == True{} : Bool} =
            Equal.trans(Bool, FO.FO.all_in_jobs_b(MV.MV.next_groups(ord), G),
              FO.FO.all_in_jobs_b(MV.MV.next_groups(full), G), True{},
              Equal.sym(Bool, FO.FO.all_in_jobs_b(MV.MV.next_groups(full), G),
                FO.FO.all_in_jobs_b(MV.MV.next_groups(ord), G),
                FP.FP.all_in_jobs_perm(perm, G, full, ord, hperm)), ag_full)
          +ng_full = FN.FN.nodup_ok_next_groups(nodup, full, S,
                       CoverGroups.Cover.all_subseq_nil(g, S), nd)
          +ng_ord : {FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(ord))
                     == True{} : Bool} =
            Equal.trans(Bool, FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(ord)),
              FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(full)), True{},
              Equal.sym(Bool,
                FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(full)),
                FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(ord)),
                FP.FP.nodup_ok_jobs_perm(perm, nodup, full, ord, hperm)), ng_full)
          +ks_c : Nat =
            Fold.OQ.ks_cost(inf, S,
              Eval.Eval.items(p, G, S, g, ord, Nil{}, 0n, inf))
          +e_pre : {SolveFast.step(1n+p, gs, 0n, items, gG, cwS, n, nodup, fl,
                      inf, Nil{}, Nil{}, 0n, best, SolveFast.dummy_step_zero(),
                      False{}, False{}, SolveFast.GuessRes{Nil{}, buf})
                    == SolveFast.step(1n+p, gs, 0n, body, gG, cwS, n, nodup, fl,
                         inf, g, Nil{}, 0n, best, SolveFast.dummy_step_zero(),
                         False{}, False{}, SolveFast.GuessRes{Nil{}, buf})
                    : SolveFast.StepRes} =
            Equal.trans(SolveFast.StepRes,
              SolveFast.step(1n+p, gs, 0n, items, gG, cwS, n, nodup, fl, inf,
                Nil{}, Nil{}, 0n, best, SolveFast.dummy_step_zero(), False{},
                False{}, SolveFast.GuessRes{Nil{}, buf}),
              SolveFast.step(1n+p, gs, 0n, SolveFast.Begin{g} <> body, gG, cwS,
                n, nodup, fl, inf, Nil{}, Nil{}, 0n, best,
                SolveFast.dummy_step_zero(), False{}, False{},
                SolveFast.GuessRes{Nil{}, buf}),
              SolveFast.step(1n+p, gs, 0n, body, gG, cwS, n, nodup, fl, inf, g,
                Nil{}, 0n, best, SolveFast.dummy_step_zero(), False{}, False{},
                SolveFast.GuessRes{Nil{}, buf}),
              Equal.cong(+List<SolveFast.Item>, SolveFast.StepRes,
                cs => SolveFast.step(1n+p, gs, 0n, cs, gG, cwS, n, nodup, fl,
                        inf, Nil{}, Nil{}, 0n, best,
                        SolveFast.dummy_step_zero(), False{}, False{},
                        SolveFast.GuessRes{Nil{}, buf}),
                items, SolveFast.Begin{g} <> body, eits),
              FS.FS.begin_succ(p, gs, gG, cwS, n, nodup, fl, inf, Nil{}, g,
                Nil{}, 0n, best, SolveFast.dummy_step_zero(), False{}, False{},
                body, SolveFast.GuessRes{Nil{}, buf}))
          FOpt.step_res_to_guess_perm(p, gs, G, C_root, n_root, has_buf, gG,
            cwS, S, nodup, fl, inf, g, ord, items, best, buf, limit, perm,
            hperm, hus, hbest,
            FOpt.step_res_pre(p, gs, G, C_root, n_root, has_buf, gG, cwS, S,
              nodup, fl, inf, Nil{}, items, Nil{}, 0n, buf,
              g, body, Nil{}, 0n, buf, best, limit, ks_c, ks_c, e_pre,
              NatProof.Nat.is_le_refl(ks_c),
              FOpt.live_groups_ok(ord, body, p, gs, G, C_root, n_root, has_buf,
                rwsG, cwS, S, nodup, fl, inf, g, Nil{}, Nil{}, 0n, 0n, best,
                buf, limit, hbuf, bounds_ord, erwsG, hrwsG, wg, perm, hperm,
                hz, h1, h3, h6, ag_ord, ng_ord, hbest, hok, hd,
                FVal.FV.bool_or_r(Nat.is_le(Eval.Eval.cost_of(best), 0n),
                  True{}, {==}),
                FVal.FV.bool_or_r(Nat.is_le(Eval.Eval.cost_of(best), 0n),
                  True{}, {==}),
                hbm, ec_ord)))

def FOpt.walk_pop_unpack(+p: Nat, +G: +List<+List<Nat>>,
    +C_root: +List<+List<Nat>>, +n_root: Nat, +has_buf: Bool,
    +rwsG: +List<FT.FT.RowWord>, +cwS: +List<SolveFast.CWord>,
    +S: +List<+List<Nat>>, +nodup: Bool, +mode: FOpt.FloorMode, +inf: Nat,
    +g: +List<Nat>, +t: +List<FT.FT.RowWord>, +tail: SolveFast.GList,
    +best: SolveRef.Best, +limit: Nat, +items: +List<SolveFast.Item>,
    -buf2: SolveFast.Buf5,
    r_step: FOpt.StepRes(p, FT.FT.glist_of_rws(t, tail), G, C_root, n_root,
              has_buf, FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS, S,
              nodup, FOpt.floor_val(mode, Groups.len_words(S)), inf, Nil{},
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
         FOpt.JobResSpec(1n+p, inf, G, C_root, n_root, has_buf, nodup, S, limit,
           SolveFast.step(1n+p, FT.FT.glist_of_rws(t, tail), 0n, Nil{},
             FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS,
             Groups.len_words(S), nodup,
             FOpt.floor_val(mode, Groups.len_words(S)), inf,
             Nil{}, Nil{}, 0n, best2, SolveFast.dummy_step_zero(), False{},
             SolveFast.is_floor_hit(nodup,
               FOpt.floor_val(mode, Groups.len_words(S)), best2),
             SolveFast.GuessRes{Nil{}, buf3}))) ->
  FOpt.JobResSpec(1n+p, inf, G, C_root, n_root, has_buf, nodup, S, limit,
    SolveFast.step(1n+p, FT.FT.glist_of_rws(t, tail), 1n, Nil{},
      FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS, Groups.len_words(S),
      nodup, FOpt.floor_val(mode, Groups.len_words(S)), inf,
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
                          +fl : Nat = FOpt.floor_val(mode, n)
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
                          FOpt.job_res_spec_transport(1n+p, inf, G, C_root,
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

def FOpt.walk_pop_go(+p: Nat, +G: +List<+List<Nat>>,
    +C_root: +List<+List<Nat>>, +n_root: Nat, +has_buf: Bool,
    +rwsG: +List<FT.FT.RowWord>, +cwS: +List<SolveFast.CWord>,
    +S: +List<+List<Nat>>, +nodup: Bool, +mode: FOpt.FloorMode, +inf: Nat,
    +g: +List<Nat>, +t: +List<FT.FT.RowWord>, +tail: SolveFast.GList,
    +best: SolveRef.Best, +limit: Nat, r: SolveFast.GuessRes,
    +hr: FH.FH.GuessSpec(G, C_root, n_root, has_buf, nodup, g, S,
           Groups.len_words(S), FOpt.floor_val(mode, Groups.len_words(S)),
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
            FOpt.floor_val(mode, Groups.len_words(S)), best) == False{} : Bool},
    +hinv: {FOpt.floor_inv(mode, p, inf, G, S, best) == True{} : Bool},
    ecif: FOpt.EClassIf(
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
         FOpt.JobResSpec(1n+p, inf, G, C_root, n_root, has_buf, nodup, S, limit,
           SolveFast.step(1n+p, FT.FT.glist_of_rws(t, tail), 0n, Nil{},
             FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS,
             Groups.len_words(S), nodup,
             FOpt.floor_val(mode, Groups.len_words(S)), inf,
             Nil{}, Nil{}, 0n, best2, SolveFast.dummy_step_zero(), False{},
             SolveFast.is_floor_hit(nodup,
               FOpt.floor_val(mode, Groups.len_words(S)), best2),
             SolveFast.GuessRes{Nil{}, buf3}))) ->
  FOpt.JobResSpec(1n+p, inf, G, C_root, n_root, has_buf, nodup, S, limit,
    SolveFast.step(1n+p, FT.FT.glist_of_rws(t, tail), 1n, Nil{},
      FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS, Groups.len_words(S),
      nodup, FOpt.floor_val(mode, Groups.len_words(S)), inf,
      Nil{}, Nil{}, 0n, best, SolveFast.dummy_step_zero(), False{}, False{}, r)):
  match r:
    case SolveFast.GuessRes{+items, buf2}:
      +n : Nat = Groups.len_words(S)
      +fl : Nat = FOpt.floor_val(mode, n)
      +gt : SolveFast.GList = FT.FT.glist_of_rws(t, tail)
      +gw = Arr.Arr.dpair_l(
              FH.FH.GuessWit<G, C_root, n_root, has_buf, nodup, g, S, n, fl,
                best, items>,
              FH.FH.BufOk(G, C_root, n_root, has_buf, nodup, buf2), hr)
      +hbuf2 = Arr.Arr.dpair_r(
                 FH.FH.GuessWit<G, C_root, n_root, has_buf, nodup, g, S, n, fl,
                   best, items>,
                 FH.FH.BufOk(G, C_root, n_root, has_buf, nodup, buf2), hr)
      FOpt.walk_pop_unpack(p, G, C_root, n_root, has_buf, rwsG, cwS, S, nodup,
        mode, inf, g, t, tail, best, limit, items, buf2,
        FOpt.guess_case_ok(p, gt, G, C_root, n_root, has_buf, rwsG, cwS, S,
          nodup, mode, inf, g, items, best, buf2, limit, hbuf2, gw, erwsG,
          hrwsG, wg, ele, hz, h1, h3, h6, ai, nd, hbest, hok, hd, hinv, ecif),
        rec)

def FOpt.walk_pop_dup(+p: Nat, +G: +List<+List<Nat>>,
    +C_root: +List<+List<Nat>>, +n_root: Nat, +has_buf: Bool,
    +rwsG: +List<FT.FT.RowWord>, +cwS: +List<SolveFast.CWord>,
    +S: +List<+List<Nat>>, +nodup: Bool, +mode: FOpt.FloorMode, +inf: Nat,
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
            FOpt.floor_val(mode, Groups.len_words(S)), best) == False{} : Bool},
    +hinv: {FOpt.floor_inv(mode, p, inf, G, S, best) == True{} : Bool},
    ecif: FOpt.EClassIf(
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
         FOpt.JobResSpec(1n+p, inf, G, C_root, n_root, has_buf, nodup, S, limit,
           SolveFast.step(1n+p, FT.FT.glist_of_rws(t, tail), 0n, Nil{},
             FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS,
             Groups.len_words(S), nodup,
             FOpt.floor_val(mode, Groups.len_words(S)), inf,
             Nil{}, Nil{}, 0n, best2, SolveFast.dummy_step_zero(), False{},
             SolveFast.is_floor_hit(nodup,
               FOpt.floor_val(mode, Groups.len_words(S)), best2),
             SolveFast.GuessRes{Nil{}, buf3}))) ->
  FOpt.JobResSpec(1n+p, inf, G, C_root, n_root, has_buf, nodup, S, limit,
    SolveFast.step(1n+p, FT.FT.glist_of_rws(t, tail), 1n, Nil{},
      FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS, Groups.len_words(S),
      nodup, FOpt.floor_val(mode, Groups.len_words(S)), inf,
      Nil{}, Nil{}, 0n, best, SolveFast.dummy_step_zero(), False{}, False{},
      SolveFast.guess_items_buf(nodup, row, g,
        FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS, Groups.len_words(S),
        FOpt.floor_val(mode, Groups.len_words(S)), best, buf))):
  (b1, dp2) = dp
  (b2, pe) = dp2
  (+eb1, +eb2) = pe
  +n : Nat = Groups.len_words(S)
  +fl : Nat = FOpt.floor_val(mode, n)
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
  %eb1 : FOpt.JobResSpec(1n+p, inf, G, C_root, n_root, has_buf, nodup, S, limit,
           SolveFast.step(1n+p, gt, 1n, Nil{}, gG, cwS, n, nodup, fl, inf,
             Nil{}, Nil{}, 0n, best, SolveFast.dummy_step_zero(), False{},
             False{},
             SolveFast.guess_items_buf(nodup, row, g, gG, cwS, n, fl, best, _)))
  FOpt.walk_pop_go(p, G, C_root, n_root, has_buf, rwsG, cwS, S, nodup, mode,
    inf, g, t, tail, best, limit,
    SolveFast.guess_items_buf(nodup, row, g, gG, cwS, n, fl, best, b1), hr1,
    erwsG, hrwsG, wg, ele, hz, h1, h3, h6, ai, nd, hbest, hok, hd, hinv, ecif,
    rec)

def FOpt.walk_cons(+p: Nat, +G: +List<+List<Nat>>,
    +C_root: +List<+List<Nat>>, +n_root: Nat, +has_buf: Bool,
    +rwsG: +List<FT.FT.RowWord>, +cwS: +List<SolveFast.CWord>,
    +S: +List<+List<Nat>>, +nodup: Bool, +mode: FOpt.FloorMode, +inf: Nat,
    +row: U32, +g: +List<Nat>, +t: +List<FT.FT.RowWord>, +tail: SolveFast.GList,
    +best: SolveRef.Best, +limit: Nat, buf: SolveFast.Buf5,
    +hbuf: FH.FH.BufOk(G, C_root, n_root, has_buf, nodup, buf), dn: Bool,
    +edn: {dn == SolveFast.is_floor_hit(nodup,
                   FOpt.floor_val(mode, Groups.len_words(S)), best) : Bool},
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
    +hinv: {FOpt.floor_inv(mode, p, inf, G, S, best) == True{} : Bool},
    ecif: FOpt.EClassIf(
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
         FOpt.JobResSpec(1n+p, inf, G, C_root, n_root, has_buf, nodup, S, limit,
           SolveFast.step(1n+p, FT.FT.glist_of_rws(t, tail), 0n, Nil{},
             FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS,
             Groups.len_words(S), nodup,
             FOpt.floor_val(mode, Groups.len_words(S)), inf,
             Nil{}, Nil{}, 0n, best2, SolveFast.dummy_step_zero(), False{},
             SolveFast.is_floor_hit(nodup,
               FOpt.floor_val(mode, Groups.len_words(S)), best2),
             SolveFast.GuessRes{Nil{}, buf3}))) ->
  FOpt.JobResSpec(1n+p, inf, G, C_root, n_root, has_buf, nodup, S, limit,
    SolveFast.step(1n+p,
      SolveFast.GTry{row, g, FT.FT.glist_of_rws(t, tail)},
      0n, Nil{}, FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS,
      Groups.len_words(S), nodup, FOpt.floor_val(mode, Groups.len_words(S)),
      inf, Nil{}, Nil{}, 0n, best, SolveFast.dummy_step_zero(), False{}, dn,
      SolveFast.GuessRes{Nil{}, buf})):
  match dn:
    case True{}:
      +n : Nat = Groups.len_words(S)
      +fl : Nat = FOpt.floor_val(mode, n)
      +gG : SolveFast.GList = FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{})
      +gt : SolveFast.GList = FT.FT.glist_of_rws(t, tail)
      +hbest = NatProof.Nat.is_le_trans(Eval.Eval.cost_of(best), limit, inf,
                 hbest_lim, hlim_inf)
      +ht = Equal.sym(Bool, True{}, SolveFast.is_floor_hit(nodup, fl, best), edn)
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
      FOpt.job_res_spec_transport(1n+p, inf, G, C_root, n_root, has_buf, nodup,
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
      +fl : Nat = FOpt.floor_val(mode, n)
      +gG : SolveFast.GList = FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{})
      +gt : SolveFast.GList = FT.FT.glist_of_rws(t, tail)
      +hbest = NatProof.Nat.is_le_trans(Eval.Eval.cost_of(best), limit, inf,
                 hbest_lim, hlim_inf)
      +hd = Equal.sym(Bool, False{}, SolveFast.is_floor_hit(nodup, fl, best), edn)
      FOpt.job_res_spec_transport(1n+p, inf, G, C_root, n_root, has_buf, nodup,
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
        FOpt.walk_pop_dup(p, G, C_root, n_root, has_buf, rwsG, cwS, S, nodup,
          mode, inf, row, g, t, tail, best, limit, buf, hbuf,
          FH.FH.buf_dup(buf), erwsG, hrwsG, ecwS, hcwS, hrow, wg, ele, hz, h1,
          h3, h6, ai, nd, hbest, hok, hd, hinv, ecif, rec))

def FOpt.glist_walk(+rws: +List<FT.FT.RowWord>, +p: Nat,
    +G: +List<+List<Nat>>, +C_root: +List<+List<Nat>>, +n_root: Nat,
    +has_buf: Bool, +rwsG: +List<FT.FT.RowWord>, +cwS: +List<SolveFast.CWord>,
    +S: +List<+List<Nat>>, +nodup: Bool, +mode: FOpt.FloorMode, +inf: Nat,
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
    +hinv: {FOpt.floor_inv(mode, p, inf, G, S, best) == True{} : Bool},
    f: FOpt.EByGs(p, inf, G, C_root, n_root, has_buf, S, nodup,
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
      FOpt.JobResSpec(1n+p, inf, G, C_root, n_root, has_buf, nodup, S, limit,
        SolveFast.step(1n+p, tail, 0n, Nil{},
          FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS, Groups.len_words(S),
          nodup, FOpt.floor_val(mode, Groups.len_words(S)), inf,
          Nil{}, Nil{}, 0n, best_end, SolveFast.dummy_step_zero(), False{},
          SolveFast.is_floor_hit(nodup,
            FOpt.floor_val(mode, Groups.len_words(S)), best_end),
          SolveFast.GuessRes{Nil{}, buf_end}))) ->
  FOpt.JobResSpec(1n+p, inf, G, C_root, n_root, has_buf, nodup, S, limit,
    SolveFast.step(1n+p, FT.FT.glist_of_rws(rws, tail), 0n, Nil{},
      FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS, Groups.len_words(S),
      nodup, FOpt.floor_val(mode, Groups.len_words(S)), inf,
      Nil{}, Nil{}, 0n, best, SolveFast.dummy_step_zero(), False{},
      SolveFast.is_floor_hit(nodup,
        FOpt.floor_val(mode, Groups.len_words(S)), best),
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
          +hrow = FOpt.rws_ok_if_head(has_buf, G, n_root, row, g, t, hrws)
          +ht_ok = FOpt.rws_ok_if_tail(has_buf, G, n_root, row, g, t, hrws)
          FOpt.walk_cons(p, G, C_root, n_root, has_buf, rwsG, cwS, S, nodup,
            mode, inf, row, g, t, tail, best, limit, buf, hbuf,
            SolveFast.is_floor_hit(nodup,
              FOpt.floor_val(mode, Groups.len_words(S)), best), {==},
            erwsG, hrwsG, ecwS, hcwS, hrow, wg, ele, hz, h1, h3, h6, ai, nd,
            hbest_lim, hlim_inf, hok, hinv, ecif,
            +best2 => buf2 => +hbuf2 => +hok2 => +hleb => +hleg =>
              FOpt.glist_walk(t, p, G, C_root, n_root, has_buf, rwsG, cwS, S,
                nodup, mode, inf, tail, best2, limit, buf2, hbuf2, erwsG, hrwsG,
                ecwS, hcwS, ht_in, ht_ok, ele, hz, h1, h3, h6, ai, nd,
                NatProof.Nat.is_le_trans(Eval.Eval.cost_of(best2),
                  Eval.Eval.cost_of(best), limit, hleb, hbest_lim),
                hlim_inf, hok2,
                FOpt.floor_inv_mono(mode, p, inf, G, S, best, best2, hleb, hinv),
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
# Crossing `GThen` and running `run_child_from` / `run_root_from`
# ---------------------------------------------------------------------------

def FOpt.walk_gthen_after(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +C_root: +List<+List<Nat>>, +n_root: Nat, +has_buf: Bool,
    +rwsG: +List<FT.FT.RowWord>, +cwS: +List<SolveFast.CWord>,
    +S: +List<+List<Nat>>, +best_mid: SolveRef.Best, +limit: Nat,
    buf2: SolveFast.Buf5,
    +hbuf2: FH.FH.BufOk(G, C_root, n_root, has_buf, True{}, buf2),
    +erwsG: {FT.FT.rws_words(rwsG) == G : +List<+List<Nat>>},
    +hrwsG: {FH.FH.rws_ok_if(has_buf, G, n_root, rwsG) == True{} : Bool},
    +ecwS: {SolveFast.cwords_words(cwS) == S : +List<+List<Nat>>},
    +hcwS: {FH.FH.cwords_ok_if(has_buf, G, C_root, n_root, cwS) == True{} : Bool},
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +h3: {Nat.is_lt(3n, inf) == True{} : Bool},
    +h6: {Nat.is_lt(6n, inf) == True{} : Bool},
    +ai: {FO.FO.all_in_ref(S, G) == True{} : Bool},
    +nd: {FN.FN.no_dup_ref(S) == True{} : Bool},
    +hmid_lim: {Nat.is_le(Eval.Eval.cost_of(best_mid), limit) == True{} : Bool},
    +hlim_inf: {Nat.is_le(limit, inf) == True{} : Bool},
    +hok_mid: {FVal.FV.best_ok_b(limit, G, S, best_mid) == True{} : Bool},
    +hle_s: {Nat.is_le(Eval.Eval.cost_of(best_mid),
               Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, S,
                 Eval.Eval.dummy_inf(inf)))) == True{} : Bool},
    fG: FOpt.EByGs(p, inf, G, C_root, n_root, has_buf, S, True{}, G)) ->
  FOpt.JobResSpec(1n+p, inf, G, C_root, n_root, has_buf, True{}, S, limit,
    SolveFast.step(1n+p, FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), 0n, Nil{},
      FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS, Groups.len_words(S),
      True{}, Nat.add(Groups.len_words(S), Groups.len_words(S)), inf,
      Nil{}, Nil{}, 0n, best_mid, SolveFast.dummy_step_zero(), False{},
      SolveFast.is_floor_hit(True{},
        Nat.add(Groups.len_words(S), Groups.len_words(S)), best_mid),
      SolveFast.GuessRes{Nil{}, buf2})):
  +hmid_inf = NatProof.Nat.is_le_trans(Eval.Eval.cost_of(best_mid), limit, inf,
                hmid_lim, hlim_inf)
  +hg_in : {FO.FO.all_in_ref(FT.FT.rws_words(rwsG), G) == True{} : Bool} =
    Equal.trans(Bool, FO.FO.all_in_ref(FT.FT.rws_words(rwsG), G),
      FO.FO.all_in_ref(G, G), True{},
      Equal.cong(+List<+List<Nat>>, Bool, l => FO.FO.all_in_ref(l, G),
        FT.FT.rws_words(rwsG), G, erwsG),
      FVal.FV.all_in_ref_self(G))
  fG_rws : FOpt.EByGs(p, inf, G, C_root, n_root, has_buf, S, True{},
             FT.FT.rws_words(rwsG)) =
    FOpt.eby_gs_transport(p, inf, G, C_root, n_root, has_buf, S, True{},
      G, FT.FT.rws_words(rwsG),
      Equal.sym(+List<+List<Nat>>, FT.FT.rws_words(rwsG), G, erwsG), fG)
  FOpt.glist_walk(rwsG, p, G, C_root, n_root, has_buf, rwsG, cwS, S, True{},
    FloorAfterS{}, inf, SolveFast.GEnd{}, best_mid, limit, buf2, hbuf2,
    erwsG, hrwsG, ecwS, hcwS, hg_in, hrwsG, ele, hz, h1, h3, h6, ai, nd,
    hmid_lim, hlim_inf, hok_mid, hle_s, fG_rws,
    +best_end => buf_end => +hbuf_end => +hok_end => +hle_mid => +hle_rws =>
      +hle_g : {Nat.is_le(Eval.Eval.cost_of(best_end),
                  Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, G,
                    best_mid))) == True{} : Bool} =
        Fold.OQ.le_cong_r(Eval.Eval.cost_of(best_end),
          Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf,
            FT.FT.rws_words(rwsG), best_mid)),
          Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, G, best_mid)),
          Equal.cong(+List<+List<Nat>>, Nat,
            l => Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, l, best_mid)),
            FT.FT.rws_words(rwsG), G, erwsG), hle_rws)
      +hg_le_ref : {Nat.is_le(
                      Eval.Eval.cost_of(
                        Eval.Eval.guesses(1n+p, G, S, inf, G, best_mid)),
                      Eval.Eval.cost_of(FS.FS.ref_run_at(1n+p, inf, G, S)))
                    == True{} : Bool} =
        Fold.OQ.le_cong_l(
          Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, G, best_mid)),
          Eval.Eval.cost_of(
            FC.FC.better_best(FS.FS.ref_run_at(1n+p, inf, G, S), best_mid)),
          Eval.Eval.cost_of(FS.FS.ref_run_at(1n+p, inf, G, S)),
          Equal.cong(SolveRef.Best, Nat, Eval.Eval.cost_of,
            Eval.Eval.guesses(1n+p, G, S, inf, G, best_mid),
            FC.FC.better_best(FS.FS.ref_run_at(1n+p, inf, G, S), best_mid),
            FC.FC.eval_guesses_from(1n+p, inf, G, S, best_mid, ele, hmid_inf)),
          FVal.FV.better_best_le_l(FS.FS.ref_run_at(1n+p, inf, G, S), best_mid))
      +hjr : {FOpt.job_res_b(1n+p, inf, G, S, limit, best_end) == True{} : Bool} =
        FO.FO.bool_and_intro(FVal.FV.best_ok_b(limit, G, S, best_end),
          Bool.and(Nat.is_le(Eval.Eval.cost_of(best_end), limit),
            Nat.is_le(Eval.Eval.cost_of(best_end),
              Eval.Eval.cost_of(FS.FS.ref_run_at(1n+p, inf, G, S)))),
          hok_end,
          FO.FO.bool_and_intro(Nat.is_le(Eval.Eval.cost_of(best_end), limit),
            Nat.is_le(Eval.Eval.cost_of(best_end),
              Eval.Eval.cost_of(FS.FS.ref_run_at(1n+p, inf, G, S))),
            NatProof.Nat.is_le_trans(Eval.Eval.cost_of(best_end),
              Eval.Eval.cost_of(best_mid), limit, hle_mid, hmid_lim),
            NatProof.Nat.is_le_trans(Eval.Eval.cost_of(best_end),
              Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, G, best_mid)),
              Eval.Eval.cost_of(FS.FS.ref_run_at(1n+p, inf, G, S)),
              hle_g, hg_le_ref)))
      Arr.DPair{hjr, hbuf_end})

def FOpt.walk_gthen(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +C_root: +List<+List<Nat>>, +n_root: Nat, +has_buf: Bool,
    +rwsG: +List<FT.FT.RowWord>, +cwS: +List<SolveFast.CWord>,
    +S: +List<+List<Nat>>, +best_mid: SolveRef.Best, +limit: Nat,
    buf_mid: SolveFast.Buf5,
    +hbuf_mid: FH.FH.BufOk(G, C_root, n_root, has_buf, True{}, buf_mid),
    dn: Bool,
    +edn: {dn == SolveFast.is_floor_hit(True{},
                   SolveFast.init_floor(Groups.len_words(S)), best_mid) : Bool},
    +erwsG: {FT.FT.rws_words(rwsG) == G : +List<+List<Nat>>},
    +hrwsG: {FH.FH.rws_ok_if(has_buf, G, n_root, rwsG) == True{} : Bool},
    +ecwS: {SolveFast.cwords_words(cwS) == S : +List<+List<Nat>>},
    +hcwS: {FH.FH.cwords_ok_if(has_buf, G, C_root, n_root, cwS) == True{} : Bool},
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +h3: {Nat.is_lt(3n, inf) == True{} : Bool},
    +h6: {Nat.is_lt(6n, inf) == True{} : Bool},
    +ai: {FO.FO.all_in_ref(S, G) == True{} : Bool},
    +nd: {FN.FN.no_dup_ref(S) == True{} : Bool},
    +hmid_lim: {Nat.is_le(Eval.Eval.cost_of(best_mid), limit) == True{} : Bool},
    +hlim_inf: {Nat.is_le(limit, inf) == True{} : Bool},
    +hok_mid: {FVal.FV.best_ok_b(limit, G, S, best_mid) == True{} : Bool},
    +hle_s: {Nat.is_le(Eval.Eval.cost_of(best_mid),
               Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, S,
                 Eval.Eval.dummy_inf(inf)))) == True{} : Bool},
    fG: FOpt.EByGs(p, inf, G, C_root, n_root, has_buf, S, True{}, G)) ->
  FOpt.JobResSpec(1n+p, inf, G, C_root, n_root, has_buf, True{}, S, limit,
    SolveFast.step(1n+p,
      SolveFast.GThen{FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{})}, 0n, Nil{},
      FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS, Groups.len_words(S),
      True{}, SolveFast.init_floor(Groups.len_words(S)), inf,
      Nil{}, Nil{}, 0n, best_mid, SolveFast.dummy_step_zero(), False{}, dn,
      SolveFast.GuessRes{Nil{}, buf_mid})):
  match dn:
    case True{}:
      +n : Nat = Groups.len_words(S)
      +fl : Nat = SolveFast.init_floor(n)
      +gG : SolveFast.GList = FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{})
      +hmid_inf = NatProof.Nat.is_le_trans(Eval.Eval.cost_of(best_mid), limit,
                    inf, hmid_lim, hlim_inf)
      +ht = Equal.sym(Bool, True{},
              SolveFast.is_floor_hit(True{}, fl, best_mid), edn)
      +hjr : {FOpt.job_res_b(1n+p, inf, G, S, limit, best_mid) == True{} : Bool} =
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
      FOpt.job_res_spec_transport(1n+p, inf, G, C_root, n_root, has_buf, True{},
        S, limit, SolveFast.StepRes{best_mid, buf_mid},
        SolveFast.step(1n+p, SolveFast.GThen{gG}, 0n, Nil{}, gG, cwS, n,
          True{}, fl, inf, Nil{}, Nil{}, 0n, best_mid,
          SolveFast.dummy_step_zero(), False{}, True{},
          SolveFast.GuessRes{Nil{}, buf_mid}),
        Equal.sym(SolveFast.StepRes,
          SolveFast.step(1n+p, SolveFast.GThen{gG}, 0n, Nil{}, gG, cwS, n,
            True{}, fl, inf, Nil{}, Nil{}, 0n, best_mid,
            SolveFast.dummy_step_zero(), False{}, True{},
            SolveFast.GuessRes{Nil{}, buf_mid}),
          SolveFast.StepRes{best_mid, buf_mid},
          FS.FS.done_exit(p, SolveFast.GThen{gG}, gG, cwS, n, True{}, fl, inf,
            best_mid, SolveFast.GuessRes{Nil{}, buf_mid})),
        Arr.DPair{hjr, hbuf_mid})
    case False{}:
      +n : Nat = Groups.len_words(S)
      +fl : Nat = SolveFast.init_floor(n)
      +gG : SolveFast.GList = FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{})
      FOpt.job_res_spec_transport(1n+p, inf, G, C_root, n_root, has_buf, True{},
        S, limit,
        SolveFast.step(1n+p, gG, 0n, Nil{}, gG, cwS, n, True{}, Nat.add(n, n),
          inf, Nil{}, Nil{}, 0n, best_mid, SolveFast.dummy_step_zero(), False{},
          SolveFast.is_floor_hit(True{}, Nat.add(n, n), best_mid),
          SolveFast.GuessRes{Nil{}, buf_mid}),
        SolveFast.step(1n+p, SolveFast.GThen{gG}, 0n, Nil{}, gG, cwS, n,
          True{}, fl, inf, Nil{}, Nil{}, 0n, best_mid,
          SolveFast.dummy_step_zero(), False{}, False{},
          SolveFast.GuessRes{Nil{}, buf_mid}),
        Equal.sym(SolveFast.StepRes,
          SolveFast.step(1n+p, SolveFast.GThen{gG}, 0n, Nil{}, gG, cwS, n,
            True{}, fl, inf, Nil{}, Nil{}, 0n, best_mid,
            SolveFast.dummy_step_zero(), False{}, False{},
            SolveFast.GuessRes{Nil{}, buf_mid}),
          SolveFast.step(1n+p, gG, 0n, Nil{}, gG, cwS, n, True{}, Nat.add(n, n),
            inf, Nil{}, Nil{}, 0n, best_mid, SolveFast.dummy_step_zero(),
            False{}, SolveFast.is_floor_hit(True{}, Nat.add(n, n), best_mid),
            SolveFast.GuessRes{Nil{}, buf_mid}),
          FS.FS.gthen_step(p, gG, gG, cwS, n, True{}, fl, inf, best_mid,
            SolveFast.GuessRes{Nil{}, buf_mid})),
        FOpt.walk_gthen_after(p, inf, G, C_root, n_root, has_buf, rwsG, cwS, S,
          best_mid, limit, buf_mid, hbuf_mid, erwsG, hrwsG, ecwS, hcwS, ele,
          hz, h1, h3, h6, ai, nd, hmid_lim, hlim_inf, hok_mid, hle_s, fG))

def FOpt.ejob_succ_nodup(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +C_root: +List<+List<Nat>>, +n_root: Nat, +has_buf: Bool,
    +rwsG: +List<FT.FT.RowWord>, +cwS: +List<SolveFast.CWord>,
    +S: +List<+List<Nat>>, +best0: SolveRef.Best, buf0: SolveFast.Buf5,
    le_2n: Bool,
    +e2n: {le_2n == SolveFast.skippable(best0,
             Nat.add(Groups.len_words(S), Groups.len_words(S))) : Bool},
    +erwsG: {FT.FT.rws_words(rwsG) == G : +List<+List<Nat>>},
    +hrwsG: {FH.FH.rws_ok_if(has_buf, G, n_root, rwsG) == True{} : Bool},
    +ecwS: {SolveFast.cwords_words(cwS) == S : +List<+List<Nat>>},
    +hcwS: {FH.FH.cwords_ok_if(has_buf, G, C_root, n_root, cwS) == True{} : Bool},
    +hb0: {Nat.is_le(Eval.Eval.cost_of(best0), inf) == True{} : Bool},
    +hbuf0: FH.FH.BufOk(G, C_root, n_root, has_buf, True{}, buf0),
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +h3: {Nat.is_lt(3n, inf) == True{} : Bool},
    +h6: {Nat.is_lt(6n, inf) == True{} : Bool},
    +ai: {FO.FO.all_in_ref(S, G) == True{} : Bool},
    +nd: {FN.FN.no_dup_ref(S) == True{} : Bool},
    fS: FOpt.EByGs(p, inf, G, C_root, n_root, has_buf, S, True{}, S),
    fG: FOpt.EByGs(p, inf, G, C_root, n_root, has_buf, S, True{}, G)) ->
  FOpt.JobResSpec(1n+p, inf, G, C_root, n_root, has_buf, True{}, S,
    Eval.Eval.cost_of(best0),
    SolveFast.step(1n+p,
      SolveFast.child_glist_nodup(cwS,
        FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), le_2n),
      0n, Nil{}, FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS,
      Groups.len_words(S), True{}, SolveFast.init_floor(Groups.len_words(S)),
      inf, Nil{}, Nil{}, 0n, best0, SolveFast.dummy_step_zero(), False{},
      SolveFast.is_floor_hit(True{}, SolveFast.init_floor(Groups.len_words(S)),
        best0),
      SolveFast.GuessRes{Nil{}, buf0})):
  match le_2n:
    case True{}:
      +n : Nat = Groups.len_words(S)
      +limit : Nat = Eval.Eval.cost_of(best0)
      +gG : SolveFast.GList = FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{})
      +rwsS : +List<FT.FT.RowWord> = FT.FT.cwords_to_rws(cwS)
      +erwsS : {FT.FT.rws_words(rwsS) == S : +List<+List<Nat>>} =
        Equal.trans(+List<+List<Nat>>, FT.FT.rws_words(rwsS),
          SolveFast.cwords_words(cwS), S,
          FT.FT.cwords_to_rws_words(cwS), ecwS)
      +hrwsS = FOpt.cwords_to_rws_ok_if(has_buf, G, C_root, n_root, cwS, hcwS)
      +hs_in : {FO.FO.all_in_ref(FT.FT.rws_words(rwsS), G) == True{} : Bool} =
        Equal.trans(Bool, FO.FO.all_in_ref(FT.FT.rws_words(rwsS), G),
          FO.FO.all_in_ref(S, G), True{},
          Equal.cong(+List<+List<Nat>>, Bool, l => FO.FO.all_in_ref(l, G),
            FT.FT.rws_words(rwsS), S, erwsS), ai)
      fS_rws : FOpt.EByGs(p, inf, G, C_root, n_root, has_buf, S, True{},
                 FT.FT.rws_words(rwsS)) =
        FOpt.eby_gs_transport(p, inf, G, C_root, n_root, has_buf, S, True{},
          S, FT.FT.rws_words(rwsS),
          Equal.sym(+List<+List<Nat>>, FT.FT.rws_words(rwsS), S, erwsS), fS)
      +hok0 = FVal.FV.best_ok_init(limit, G, S, best0, Nat.ge_refl(limit))
      +h2n0 = FLB.FS.skippable_to_le(best0, Nat.add(n, n),
                Equal.sym(Bool, True{},
                  SolveFast.skippable(best0, Nat.add(n, n)), e2n))
      %Equal.sym(SolveFast.GList,
         SolveFast.glist_of_cwords(cwS, SolveFast.GEnd{}),
         FT.FT.glist_of_rws(rwsS, SolveFast.GEnd{}),
         FT.FT.glist_of_cwords_eq(cwS, SolveFast.GEnd{})) :
        FOpt.JobResSpec(1n+p, inf, G, C_root, n_root, has_buf, True{}, S, limit,
          SolveFast.step(1n+p, _, 0n, Nil{}, gG, cwS, n, True{},
            SolveFast.init_floor(n), inf, Nil{}, Nil{}, 0n, best0,
            SolveFast.dummy_step_zero(), False{},
            SolveFast.is_floor_hit(True{}, SolveFast.init_floor(n), best0),
            SolveFast.GuessRes{Nil{}, buf0}))
      FOpt.glist_walk(rwsS, p, G, C_root, n_root, has_buf, rwsG, cwS, S, True{},
        FloorInit{}, inf, SolveFast.GEnd{}, best0, limit, buf0, hbuf0,
        erwsG, hrwsG, ecwS, hcwS, hs_in, hrwsS, ele, hz, h1, h3, h6, ai, nd,
        NatProof.Nat.is_le_refl(limit), hb0, hok0, {==}, fS_rws,
        +best_end => buf_end => +hbuf_end => +hok_end => +hle_b0 => +hle_rws =>
          +hle_s : {Nat.is_le(Eval.Eval.cost_of(best_end),
                      Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, S,
                        best0))) == True{} : Bool} =
            Fold.OQ.le_cong_r(Eval.Eval.cost_of(best_end),
              Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf,
                FT.FT.rws_words(rwsS), best0)),
              Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, S, best0)),
              Equal.cong(+List<+List<Nat>>, Nat,
                l => Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, l, best0)),
                FT.FT.rws_words(rwsS), S, erwsS), hle_rws)
          +h2n_end = NatProof.Nat.is_le_trans(Eval.Eval.cost_of(best_end),
                       limit, Nat.add(n, n), hle_b0, h2n0)
          +hs_inf = NatProof.Nat.is_le_trans(Eval.Eval.cost_of(best_end),
                      Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, S, best0)),
                      Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, S,
                        Eval.Eval.dummy_inf(inf))),
                      hle_s,
                      FVal.FV.eval_guesses_le_from_inf(1n+p, inf, G, S, S, best0, hb0))
          +hle_ref = FVal.FV.after_s_floor_le(p, inf, G, S, best_end, ele, hz,
                       NatProof.Nat.is_le_trans(Eval.Eval.cost_of(best_end),
                         limit, inf, hle_b0, hb0), h2n_end, hs_inf)
          +hjr : {FOpt.job_res_b(1n+p, inf, G, S, limit, best_end) == True{} : Bool} =
            FO.FO.bool_and_intro(FVal.FV.best_ok_b(limit, G, S, best_end),
              Bool.and(Nat.is_le(Eval.Eval.cost_of(best_end), limit),
                Nat.is_le(Eval.Eval.cost_of(best_end),
                  Eval.Eval.cost_of(FS.FS.ref_run_at(1n+p, inf, G, S)))),
              hok_end,
              FO.FO.bool_and_intro(Nat.is_le(Eval.Eval.cost_of(best_end), limit),
                Nat.is_le(Eval.Eval.cost_of(best_end),
                  Eval.Eval.cost_of(FS.FS.ref_run_at(1n+p, inf, G, S))),
                hle_b0, hle_ref))
          Arr.DPair{hjr, hbuf_end})
    case False{}:
      +n : Nat = Groups.len_words(S)
      +limit : Nat = Eval.Eval.cost_of(best0)
      +gG : SolveFast.GList = FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{})
      +rwsS : +List<FT.FT.RowWord> = FT.FT.cwords_to_rws(cwS)
      +erwsS : {FT.FT.rws_words(rwsS) == S : +List<+List<Nat>>} =
        Equal.trans(+List<+List<Nat>>, FT.FT.rws_words(rwsS),
          SolveFast.cwords_words(cwS), S,
          FT.FT.cwords_to_rws_words(cwS), ecwS)
      +hrwsS = FOpt.cwords_to_rws_ok_if(has_buf, G, C_root, n_root, cwS, hcwS)
      +hs_in : {FO.FO.all_in_ref(FT.FT.rws_words(rwsS), G) == True{} : Bool} =
        Equal.trans(Bool, FO.FO.all_in_ref(FT.FT.rws_words(rwsS), G),
          FO.FO.all_in_ref(S, G), True{},
          Equal.cong(+List<+List<Nat>>, Bool, l => FO.FO.all_in_ref(l, G),
            FT.FT.rws_words(rwsS), S, erwsS), ai)
      fS_rws : FOpt.EByGs(p, inf, G, C_root, n_root, has_buf, S, True{},
                 FT.FT.rws_words(rwsS)) =
        FOpt.eby_gs_transport(p, inf, G, C_root, n_root, has_buf, S, True{},
          S, FT.FT.rws_words(rwsS),
          Equal.sym(+List<+List<Nat>>, FT.FT.rws_words(rwsS), S, erwsS), fS)
      +hok0 = FVal.FV.best_ok_init(limit, G, S, best0, Nat.ge_refl(limit))
      %Equal.sym(SolveFast.GList,
         SolveFast.glist_of_cwords(cwS, SolveFast.GThen{gG}),
         FT.FT.glist_of_rws(rwsS, SolveFast.GThen{gG}),
         FT.FT.glist_of_cwords_eq(cwS, SolveFast.GThen{gG})) :
        FOpt.JobResSpec(1n+p, inf, G, C_root, n_root, has_buf, True{}, S, limit,
          SolveFast.step(1n+p, _, 0n, Nil{}, gG, cwS, n, True{},
            SolveFast.init_floor(n), inf, Nil{}, Nil{}, 0n, best0,
            SolveFast.dummy_step_zero(), False{},
            SolveFast.is_floor_hit(True{}, SolveFast.init_floor(n), best0),
            SolveFast.GuessRes{Nil{}, buf0}))
      FOpt.glist_walk(rwsS, p, G, C_root, n_root, has_buf, rwsG, cwS, S, True{},
        FloorInit{}, inf, SolveFast.GThen{gG}, best0, limit, buf0, hbuf0,
        erwsG, hrwsG, ecwS, hcwS, hs_in, hrwsS, ele, hz, h1, h3, h6, ai, nd,
        NatProof.Nat.is_le_refl(limit), hb0, hok0, {==}, fS_rws,
        +best_mid => buf_mid => +hbuf_mid => +hok_mid => +hle_b0 => +hle_rws =>
          +hle_s : {Nat.is_le(Eval.Eval.cost_of(best_mid),
                      Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, S,
                        best0))) == True{} : Bool} =
            Fold.OQ.le_cong_r(Eval.Eval.cost_of(best_mid),
              Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf,
                FT.FT.rws_words(rwsS), best0)),
              Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, S, best0)),
              Equal.cong(+List<+List<Nat>>, Nat,
                l => Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, l, best0)),
                FT.FT.rws_words(rwsS), S, erwsS), hle_rws)
          +hs_inf = NatProof.Nat.is_le_trans(Eval.Eval.cost_of(best_mid),
                      Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, S, best0)),
                      Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, S,
                        Eval.Eval.dummy_inf(inf))),
                      hle_s,
                      FVal.FV.eval_guesses_le_from_inf(1n+p, inf, G, S, S, best0, hb0))
          FOpt.walk_gthen(p, inf, G, C_root, n_root, has_buf, rwsG, cwS, S,
            best_mid, limit, buf_mid, hbuf_mid,
            SolveFast.is_floor_hit(True{}, SolveFast.init_floor(n), best_mid),
            {==}, erwsG, hrwsG, ecwS, hcwS, ele, hz, h1, h3, h6, ai, nd,
            hle_b0, hb0, hok_mid, hs_inf, fG))

def FOpt.ejob_succ_direct(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +C_root: +List<+List<Nat>>, +n_root: Nat, +has_buf: Bool,
    +rwsG: +List<FT.FT.RowWord>, +cwS: +List<SolveFast.CWord>,
    +S: +List<+List<Nat>>, +nodup: Bool, +best0: SolveRef.Best,
    buf0: SolveFast.Buf5,
    +erwsG: {FT.FT.rws_words(rwsG) == G : +List<+List<Nat>>},
    +hrwsG: {FH.FH.rws_ok_if(has_buf, G, n_root, rwsG) == True{} : Bool},
    +ecwS: {SolveFast.cwords_words(cwS) == S : +List<+List<Nat>>},
    +hcwS: {FH.FH.cwords_ok_if(has_buf, G, C_root, n_root, cwS) == True{} : Bool},
    +hb0: {Nat.is_le(Eval.Eval.cost_of(best0), inf) == True{} : Bool},
    +hbuf0: FH.FH.BufOk(G, C_root, n_root, has_buf, nodup, buf0),
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +h3: {Nat.is_lt(3n, inf) == True{} : Bool},
    +h6: {Nat.is_lt(6n, inf) == True{} : Bool},
    +ai: {FO.FO.all_in_ref(S, G) == True{} : Bool},
    +nd: {FN.FN.nodup_ok(nodup, S) == True{} : Bool},
    fG: FOpt.EByGs(p, inf, G, C_root, n_root, has_buf, S, nodup, G)) ->
  FOpt.JobResSpec(1n+p, inf, G, C_root, n_root, has_buf, nodup, S,
    Eval.Eval.cost_of(best0),
    SolveFast.step(1n+p, FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), 0n, Nil{},
      FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS, Groups.len_words(S),
      nodup, SolveFast.init_floor(Groups.len_words(S)), inf,
      Nil{}, Nil{}, 0n, best0, SolveFast.dummy_step_zero(), False{},
      SolveFast.is_floor_hit(nodup, SolveFast.init_floor(Groups.len_words(S)),
        best0),
      SolveFast.GuessRes{Nil{}, buf0})):
  +limit : Nat = Eval.Eval.cost_of(best0)
  +hok0 = FVal.FV.best_ok_init(limit, G, S, best0, Nat.ge_refl(limit))
  +hg_in : {FO.FO.all_in_ref(FT.FT.rws_words(rwsG), G) == True{} : Bool} =
    Equal.trans(Bool, FO.FO.all_in_ref(FT.FT.rws_words(rwsG), G),
      FO.FO.all_in_ref(G, G), True{},
      Equal.cong(+List<+List<Nat>>, Bool, l => FO.FO.all_in_ref(l, G),
        FT.FT.rws_words(rwsG), G, erwsG),
      FVal.FV.all_in_ref_self(G))
  fG_rws : FOpt.EByGs(p, inf, G, C_root, n_root, has_buf, S, nodup,
             FT.FT.rws_words(rwsG)) =
    FOpt.eby_gs_transport(p, inf, G, C_root, n_root, has_buf, S, nodup,
      G, FT.FT.rws_words(rwsG),
      Equal.sym(+List<+List<Nat>>, FT.FT.rws_words(rwsG), G, erwsG), fG)
  FOpt.glist_walk(rwsG, p, G, C_root, n_root, has_buf, rwsG, cwS, S, nodup,
    FloorInit{}, inf, SolveFast.GEnd{}, best0, limit, buf0, hbuf0,
    erwsG, hrwsG, ecwS, hcwS, hg_in, hrwsG, ele, hz, h1, h3, h6, ai, nd,
    NatProof.Nat.is_le_refl(limit), hb0, hok0, {==}, fG_rws,
    +best_end => buf_end => +hbuf_end => +hok_end => +hle_b0 => +hle_rws =>
      +hle_g : {Nat.is_le(Eval.Eval.cost_of(best_end),
                  Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, G,
                    best0))) == True{} : Bool} =
        Fold.OQ.le_cong_r(Eval.Eval.cost_of(best_end),
          Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf,
            FT.FT.rws_words(rwsG), best0)),
          Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, G, best0)),
          Equal.cong(+List<+List<Nat>>, Nat,
            l => Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, l, best0)),
            FT.FT.rws_words(rwsG), G, erwsG), hle_rws)
      +hg_le_ref : {Nat.is_le(
                      Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, G, best0)),
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
      +hjr : {FOpt.job_res_b(1n+p, inf, G, S, limit, best_end) == True{} : Bool} =
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
              hle_g, hg_le_ref)))
      Arr.DPair{hjr, hbuf_end})

def FOpt.ejob_succ_at(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +C_root: +List<+List<Nat>>, +n_root: Nat, +has_buf: Bool,
    +rwsG: +List<FT.FT.RowWord>, +cwS: +List<SolveFast.CWord>,
    +S: +List<+List<Nat>>, +nodup: Bool, +best0: SolveRef.Best,
    buf0: SolveFast.Buf5,
    +erwsG: {FT.FT.rws_words(rwsG) == G : +List<+List<Nat>>},
    +hrwsG: {FH.FH.rws_ok_if(has_buf, G, n_root, rwsG) == True{} : Bool},
    +ecwS: {SolveFast.cwords_words(cwS) == S : +List<+List<Nat>>},
    +hcwS: {FH.FH.cwords_ok_if(has_buf, G, C_root, n_root, cwS) == True{} : Bool},
    +hb0: {Nat.is_le(Eval.Eval.cost_of(best0), inf) == True{} : Bool},
    +hbuf0: FH.FH.BufOk(G, C_root, n_root, has_buf, nodup, buf0),
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +h3: {Nat.is_lt(3n, inf) == True{} : Bool},
    +h6: {Nat.is_lt(6n, inf) == True{} : Bool},
    +ai: {FO.FO.all_in_ref(S, G) == True{} : Bool},
    +nd: {FN.FN.nodup_ok(nodup, S) == True{} : Bool},
    fS: FOpt.EByGs(p, inf, G, C_root, n_root, has_buf, S, nodup, S),
    fG: FOpt.EByGs(p, inf, G, C_root, n_root, has_buf, S, nodup, G)) ->
  FOpt.JobResSpec(1n+p, inf, G, C_root, n_root, has_buf, nodup, S,
    Eval.Eval.cost_of(best0),
    FS.FS.run_child_from(1n+p, inf,
      FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS, nodup, best0, buf0)):
  match nodup:
    case True{}:
      +n : Nat = Groups.len_words(S)
      +gG : SolveFast.GList = FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{})
      %Equal.sym(+List<+List<Nat>>, SolveFast.cwords_words(cwS), S, ecwS) :
        FOpt.JobResSpec(1n+p, inf, G, C_root, n_root, has_buf, True{}, S,
          Eval.Eval.cost_of(best0),
          SolveFast.step(1n+p,
            SolveFast.child_glist(True{}, cwS, Groups.len_words(_), best0, gG),
            0n, Nil{}, gG, cwS, Groups.len_words(_), True{},
            SolveFast.init_floor(Groups.len_words(_)), inf, Nil{}, Nil{}, 0n,
            best0, SolveFast.dummy_step_zero(), False{},
            SolveFast.is_floor_hit(True{},
              SolveFast.init_floor(Groups.len_words(_)), best0),
            SolveFast.GuessRes{Nil{}, buf0}))
      FOpt.ejob_succ_nodup(p, inf, G, C_root, n_root, has_buf, rwsG, cwS, S,
        best0, buf0, SolveFast.skippable(best0, Nat.add(n, n)), {==},
        erwsG, hrwsG, ecwS, hcwS, hb0, hbuf0, ele, hz, h1, h3, h6, ai, nd,
        fS, fG)
    case False{}:
      +gG : SolveFast.GList = FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{})
      %Equal.sym(+List<+List<Nat>>, SolveFast.cwords_words(cwS), S, ecwS) :
        FOpt.JobResSpec(1n+p, inf, G, C_root, n_root, has_buf, False{}, S,
          Eval.Eval.cost_of(best0),
          SolveFast.step(1n+p, gG, 0n, Nil{}, gG, cwS, Groups.len_words(_),
            False{}, SolveFast.init_floor(Groups.len_words(_)), inf,
            Nil{}, Nil{}, 0n, best0, SolveFast.dummy_step_zero(), False{},
            SolveFast.is_floor_hit(False{},
              SolveFast.init_floor(Groups.len_words(_)), best0),
            SolveFast.GuessRes{Nil{}, buf0}))
      FOpt.ejob_succ_direct(p, inf, G, C_root, n_root, has_buf, rwsG, cwS, S,
        False{}, best0, buf0, erwsG, hrwsG, ecwS, hcwS, hb0, hbuf0, ele, hz,
        h1, h3, h6, ai, {==}, fG)

def FOpt.ejob_succ(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +C_root: +List<+List<Nat>>, +n_root: Nat, +has_buf: Bool,
    +S: +List<+List<Nat>>, +nodup: Bool,
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +h3: {Nat.is_lt(3n, inf) == True{} : Bool},
    +h6: {Nat.is_lt(6n, inf) == True{} : Bool},
    +ai: {FO.FO.all_in_ref(S, G) == True{} : Bool},
    +nd: {FN.FN.nodup_ok(nodup, S) == True{} : Bool},
    fS: FOpt.EByGs(p, inf, G, C_root, n_root, has_buf, S, nodup, S),
    fG: FOpt.EByGs(p, inf, G, C_root, n_root, has_buf, S, nodup, G)) ->
  FOpt.EJob(1n+p, inf, G, C_root, n_root, has_buf, S, nodup):
  +rwsG => +cwS => +best0 => buf0 => +erwsG => +hrwsG => +ecwS => +hcwS =>
  +hb0 => +hbuf0 =>
    FOpt.ejob_succ_at(p, inf, G, C_root, n_root, has_buf, rwsG, cwS, S, nodup,
      best0, buf0, erwsG, hrwsG, ecwS, hcwS, hb0, hbuf0, ele, hz, h1, h3, h6,
      ai, nd, fS, fG)

# ---------------------------------------------------------------------------
# Fuel 0 base case and fuel induction (`FOpt.eflat`)
# ---------------------------------------------------------------------------

def FOpt.zero_guess_step_rws(+gG: SolveFast.GList, +nodup: Bool, +fl: Nat,
    +inf: Nat, +row: U32, +g: +List<Nat>, +rest: +List<FT.FT.RowWord>,
    +best: SolveRef.Best, +dn: Bool, -gres: SolveFast.GuessRes) ->
  {SolveFast.step(0n,
     SolveFast.GTry{row, g, FT.FT.glist_of_rws(rest, SolveFast.GEnd{})}, 0n,
     Nil{}, gG, Nil{}, 0n, nodup, fl, inf, Nil{}, Nil{}, 0n, best,
     SolveFast.dummy_step_zero(), False{}, dn, gres)
   == SolveFast.step(0n, FT.FT.glist_of_rws(rest, SolveFast.GEnd{}), 0n, Nil{},
        gG, Nil{}, 0n, nodup, fl, inf, Nil{}, Nil{}, 0n,
        SolveRef.finish_guess(inf, g, Nil{}, 0n, 0n, best),
        SolveFast.dummy_step_zero(), False{}, False{}, gres)
   : SolveFast.StepRes}:
  match rest:
    case Nil{}:
      {==}
    case Con{rw, rt}:
      match rw:
        case FT.RowWord{rh, gh}:
          {==}

def FOpt.zero_guess_step_words(+gG: SolveFast.GList, +nodup: Bool, +fl: Nat,
    +inf: Nat, +row: U32, +g: +List<Nat>, +rest: +List<+List<Nat>>,
    +best: SolveRef.Best, +dn: Bool, -gres: SolveFast.GuessRes) ->
  {SolveFast.step(0n,
     SolveFast.GTry{row, g, SolveFast.glist_of_words(rest, SolveFast.GEnd{})},
     0n, Nil{}, gG, Nil{}, 0n, nodup, fl, inf, Nil{}, Nil{}, 0n, best,
     SolveFast.dummy_step_zero(), False{}, dn, gres)
   == SolveFast.step(0n, SolveFast.glist_of_words(rest, SolveFast.GEnd{}), 0n,
        Nil{}, gG, Nil{}, 0n, nodup, fl, inf, Nil{}, Nil{}, 0n,
        SolveRef.finish_guess(inf, g, Nil{}, 0n, 0n, best),
        SolveFast.dummy_step_zero(), False{}, False{}, gres)
   : SolveFast.StepRes}:
  match rest:
    case Nil{}:
      {==}
    case Con{gh, rt}:
      {==}

def FOpt.guesses_zero_eq(+rws: +List<FT.FT.RowWord>, +G: +List<+List<Nat>>,
    +gG: SolveFast.GList, +nodup: Bool, +fl: Nat, +inf: Nat,
    +best: SolveRef.Best, +dn: Bool, -buf: SolveFast.Buf5) ->
  {SolveFast.step(0n, FT.FT.glist_of_rws(rws, SolveFast.GEnd{}), 0n, Nil{}, gG,
     Nil{}, 0n, nodup, fl, inf, Nil{}, Nil{}, 0n, best,
     SolveFast.dummy_step_zero(), False{}, dn, SolveFast.GuessRes{Nil{}, buf})
   == SolveFast.StepRes{
        Eval.Eval.guesses(0n, G, Nil{}, inf, FT.FT.rws_words(rws), best), buf}
   : SolveFast.StepRes}:
  match rws:
    case Nil{}:
      {==}
    case Con{rw, rest}:
      match rw:
        case FT.RowWord{+row, +g}:
          +next_best : SolveRef.Best =
            SolveRef.finish_guess(inf, g, Nil{}, 0n, 0n, best)
          Equal.trans(SolveFast.StepRes,
            SolveFast.step(0n,
              SolveFast.GTry{row, g, FT.FT.glist_of_rws(rest, SolveFast.GEnd{})},
              0n, Nil{}, gG, Nil{}, 0n, nodup, fl, inf, Nil{}, Nil{}, 0n, best,
              SolveFast.dummy_step_zero(), False{}, dn,
              SolveFast.GuessRes{Nil{}, buf}),
            SolveFast.step(0n, FT.FT.glist_of_rws(rest, SolveFast.GEnd{}), 0n,
              Nil{}, gG, Nil{}, 0n, nodup, fl, inf, Nil{}, Nil{}, 0n, next_best,
              SolveFast.dummy_step_zero(), False{}, False{},
              SolveFast.GuessRes{Nil{}, buf}),
            SolveFast.StepRes{
              Eval.Eval.guesses(0n, G, Nil{}, inf,
                g <> FT.FT.rws_words(rest), best), buf},
            FOpt.zero_guess_step_rws(gG, nodup, fl, inf, row, g, rest, best, dn,
              SolveFast.GuessRes{Nil{}, buf}),
            FOpt.guesses_zero_eq(rest, G, gG, nodup, fl, inf, next_best,
              False{}, buf))

def FOpt.guesses_zero_words_eq(+gs: +List<+List<Nat>>, +G: +List<+List<Nat>>,
    +gG: SolveFast.GList, +nodup: Bool, +fl: Nat, +inf: Nat,
    +best: SolveRef.Best, +dn: Bool, -buf: SolveFast.Buf5) ->
  {SolveFast.step(0n, SolveFast.glist_of_words(gs, SolveFast.GEnd{}), 0n, Nil{},
     gG, Nil{}, 0n, nodup, fl, inf, Nil{}, Nil{}, 0n, best,
     SolveFast.dummy_step_zero(), False{}, dn, SolveFast.GuessRes{Nil{}, buf})
   == SolveFast.StepRes{Eval.Eval.guesses(0n, G, Nil{}, inf, gs, best), buf}
   : SolveFast.StepRes}:
  match gs:
    case Nil{}:
      {==}
    case Con{+g, +rest}:
      +next_best : SolveRef.Best =
        SolveRef.finish_guess(inf, g, Nil{}, 0n, 0n, best)
      Equal.trans(SolveFast.StepRes,
        SolveFast.step(0n,
          SolveFast.GTry{0, g, SolveFast.glist_of_words(rest, SolveFast.GEnd{})},
          0n, Nil{}, gG, Nil{}, 0n, nodup, fl, inf, Nil{}, Nil{}, 0n, best,
          SolveFast.dummy_step_zero(), False{}, dn,
          SolveFast.GuessRes{Nil{}, buf}),
        SolveFast.step(0n, SolveFast.glist_of_words(rest, SolveFast.GEnd{}), 0n,
          Nil{}, gG, Nil{}, 0n, nodup, fl, inf, Nil{}, Nil{}, 0n, next_best,
          SolveFast.dummy_step_zero(), False{}, False{},
          SolveFast.GuessRes{Nil{}, buf}),
        SolveFast.StepRes{Eval.Eval.guesses(0n, G, Nil{}, inf, g <> rest, best),
          buf},
        FOpt.zero_guess_step_words(gG, nodup, fl, inf, 0, g, rest, best, dn,
          SolveFast.GuessRes{Nil{}, buf}),
        FOpt.guesses_zero_words_eq(rest, G, gG, nodup, fl, inf, next_best,
          False{}, buf))

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
      +wg = FO.FO.all_in_head(g, rest, G, hg_in)
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
  +hok0 = FVal.FV.best_ok_init(limit, G, Nil{}, best0, Nat.ge_refl(limit))
  +ef = FC.FC.eval_guesses_from(0n, inf, G, Nil{}, best0, {==}, hb0)
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

def FOpt.ejob_nil_nodup(+inf: Nat, +G: +List<+List<Nat>>,
    +C_root: +List<+List<Nat>>, +n_root: Nat, +has_buf: Bool,
    +rwsG: +List<FT.FT.RowWord>, +best0: SolveRef.Best, -buf0: SolveFast.Buf5,
    le0: Bool, +ele0: {le0 == SolveFast.skippable(best0, 0n) : Bool},
    +erwsG: {FT.FT.rws_words(rwsG) == G : +List<+List<Nat>>},
    +hb0: {Nat.is_le(Eval.Eval.cost_of(best0), inf) == True{} : Bool},
    +hbuf0: FH.FH.BufOk(G, C_root, n_root, has_buf, True{}, buf0)) ->
  FOpt.JobResSpec(0n, inf, G, C_root, n_root, has_buf, True{}, Nil{},
    Eval.Eval.cost_of(best0),
    SolveFast.step(0n,
      SolveFast.child_glist_nodup(Nil{},
        FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), le0),
      0n, Nil{}, FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), Nil{}, 0n, True{},
      0n, inf, Nil{}, Nil{}, 0n, best0, SolveFast.dummy_step_zero(), False{},
      SolveFast.is_floor_hit(True{}, 0n, best0),
      SolveFast.GuessRes{Nil{}, buf0})):
  match le0:
    case True{}:
      +limit : Nat = Eval.Eval.cost_of(best0)
      +h0 = NatProof.Nat.eq_zero_of_le_zero(limit,
              FLB.FS.skippable_to_le(best0, 0n,
                Equal.sym(Bool, True{}, SolveFast.skippable(best0, 0n), ele0)))
      +hjr : {FOpt.job_res_b(0n, inf, G, Nil{}, limit, best0) == True{} : Bool} =
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
      Arr.DPair{hjr, hbuf0}
    case False{}:
      +limit : Nat = Eval.Eval.cost_of(best0)
      +gG : SolveFast.GList = FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{})
      +eq1 : {SolveFast.step(0n, gG, 0n, Nil{}, gG, Nil{}, 0n, True{}, 0n, inf,
                Nil{}, Nil{}, 0n, best0, SolveFast.dummy_step_zero(), False{},
                False{}, SolveFast.GuessRes{Nil{}, buf0})
              == SolveFast.StepRes{
                   Eval.Eval.guesses(0n, G, Nil{}, inf, G, best0), buf0}
              : SolveFast.StepRes} =
        Equal.trans(SolveFast.StepRes,
          SolveFast.step(0n, gG, 0n, Nil{}, gG, Nil{}, 0n, True{}, 0n, inf,
            Nil{}, Nil{}, 0n, best0, SolveFast.dummy_step_zero(), False{},
            False{}, SolveFast.GuessRes{Nil{}, buf0}),
          SolveFast.StepRes{
            Eval.Eval.guesses(0n, G, Nil{}, inf, FT.FT.rws_words(rwsG), best0),
            buf0},
          SolveFast.StepRes{
            Eval.Eval.guesses(0n, G, Nil{}, inf, G, best0), buf0},
          FOpt.guesses_zero_eq(rwsG, G, gG, True{}, 0n, inf, best0, False{},
            buf0),
          Equal.cong(+List<+List<Nat>>, SolveFast.StepRes,
            l => SolveFast.StepRes{Eval.Eval.guesses(0n, G, Nil{}, inf, l, best0),
                   buf0},
            FT.FT.rws_words(rwsG), G, erwsG))
      FOpt.job_res_spec_transport(0n, inf, G, C_root, n_root, has_buf, True{},
        Nil{}, limit,
        SolveFast.StepRes{Eval.Eval.guesses(0n, G, Nil{}, inf, G, best0), buf0},
        SolveFast.step(0n, gG, 0n, Nil{}, gG, Nil{}, 0n, True{}, 0n, inf,
          Nil{}, Nil{}, 0n, best0, SolveFast.dummy_step_zero(), False{},
          False{}, SolveFast.GuessRes{Nil{}, buf0}),
        Equal.sym(SolveFast.StepRes,
          SolveFast.step(0n, gG, 0n, Nil{}, gG, Nil{}, 0n, True{}, 0n, inf,
            Nil{}, Nil{}, 0n, best0, SolveFast.dummy_step_zero(), False{},
            False{}, SolveFast.GuessRes{Nil{}, buf0}),
          SolveFast.StepRes{Eval.Eval.guesses(0n, G, Nil{}, inf, G, best0), buf0},
          eq1),
        Arr.DPair{FOpt.ejob_nil_guesses(inf, G, best0, hb0), hbuf0})

def FOpt.ejob_nil(+inf: Nat, +G: +List<+List<Nat>>,
    +C_root: +List<+List<Nat>>, +n_root: Nat, +has_buf: Bool, +nodup: Bool) ->
  FOpt.EJob(0n, inf, G, C_root, n_root, has_buf, Nil{}, nodup):
  match nodup:
    case True{}:
      +rwsG => +cwS => +best0 => buf0 => +erwsG => +hrwsG => +ecwS => +hcwS =>
      +hb0 => +hbuf0 =>
        +ecw_nil = FOpt.cwords_nil_of_words_nil(cwS, ecwS)
        %Equal.sym(+List<SolveFast.CWord>, cwS, Nil{}, ecw_nil) :
          FOpt.JobResSpec(0n, inf, G, C_root, n_root, has_buf, True{}, Nil{},
            Eval.Eval.cost_of(best0),
            FS.FS.run_child_from(0n, inf,
              FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), _, True{}, best0,
              buf0))
        FOpt.ejob_nil_nodup(inf, G, C_root, n_root, has_buf, rwsG, best0, buf0,
          SolveFast.skippable(best0, 0n), {==}, erwsG, hb0, hbuf0)
    case False{}:
      +rwsG => +cwS => +best0 => buf0 => +erwsG => +hrwsG => +ecwS => +hcwS =>
      +hb0 => +hbuf0 =>
        +ecw_nil = FOpt.cwords_nil_of_words_nil(cwS, ecwS)
        +gG : SolveFast.GList = FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{})
        +eq1 : {SolveFast.step(0n, gG, 0n, Nil{}, gG, Nil{}, 0n, False{}, 0n,
                  inf, Nil{}, Nil{}, 0n, best0, SolveFast.dummy_step_zero(),
                  False{}, False{}, SolveFast.GuessRes{Nil{}, buf0})
                == SolveFast.StepRes{
                     Eval.Eval.guesses(0n, G, Nil{}, inf, G, best0), buf0}
                : SolveFast.StepRes} =
          Equal.trans(SolveFast.StepRes,
            SolveFast.step(0n, gG, 0n, Nil{}, gG, Nil{}, 0n, False{}, 0n, inf,
              Nil{}, Nil{}, 0n, best0, SolveFast.dummy_step_zero(), False{},
              False{}, SolveFast.GuessRes{Nil{}, buf0}),
            SolveFast.StepRes{
              Eval.Eval.guesses(0n, G, Nil{}, inf, FT.FT.rws_words(rwsG), best0),
              buf0},
            SolveFast.StepRes{
              Eval.Eval.guesses(0n, G, Nil{}, inf, G, best0), buf0},
            FOpt.guesses_zero_eq(rwsG, G, gG, False{}, 0n, inf, best0, False{},
              buf0),
            Equal.cong(+List<+List<Nat>>, SolveFast.StepRes,
              l => SolveFast.StepRes{Eval.Eval.guesses(0n, G, Nil{}, inf, l, best0),
                     buf0},
              FT.FT.rws_words(rwsG), G, erwsG))
        %Equal.sym(+List<SolveFast.CWord>, cwS, Nil{}, ecw_nil) :
          FOpt.JobResSpec(0n, inf, G, C_root, n_root, has_buf, False{}, Nil{},
            Eval.Eval.cost_of(best0),
            FS.FS.run_child_from(0n, inf, gG, _, False{}, best0, buf0))
        FOpt.job_res_spec_transport(0n, inf, G, C_root, n_root, has_buf,
          False{}, Nil{}, Eval.Eval.cost_of(best0),
          SolveFast.StepRes{Eval.Eval.guesses(0n, G, Nil{}, inf, G, best0), buf0},
          SolveFast.step(0n, gG, 0n, Nil{}, gG, Nil{}, 0n, False{}, 0n, inf,
            Nil{}, Nil{}, 0n, best0, SolveFast.dummy_step_zero(), False{},
            False{}, SolveFast.GuessRes{Nil{}, buf0}),
          Equal.sym(SolveFast.StepRes,
            SolveFast.step(0n, gG, 0n, Nil{}, gG, Nil{}, 0n, False{}, 0n, inf,
              Nil{}, Nil{}, 0n, best0, SolveFast.dummy_step_zero(), False{},
              False{}, SolveFast.GuessRes{Nil{}, buf0}),
            SolveFast.StepRes{
              Eval.Eval.guesses(0n, G, Nil{}, inf, G, best0), buf0}, eq1),
          Arr.DPair{FOpt.ejob_nil_guesses(inf, G, best0, hb0), hbuf0})

def FOpt.ejob_transport(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +C_root: +List<+List<Nat>>, +n_root: Nat, +has_buf: Bool,
    +S1: +List<+List<Nat>>, +S2: +List<+List<Nat>>, +nodup: Bool,
    e: {S1 == S2 : +List<+List<Nat>>},
    j: FOpt.EJob(fuel, inf, G, C_root, n_root, has_buf, S1, nodup)) ->
  FOpt.EJob(fuel, inf, G, C_root, n_root, has_buf, S2, nodup):
  %e : FOpt.EJob(fuel, inf, G, C_root, n_root, has_buf, _, nodup)
  j

def FOpt.ejob_zero(+inf: Nat, +G: +List<+List<Nat>>,
    +C_root: +List<+List<Nat>>, +n_root: Nat, +has_buf: Bool,
    +S: +List<+List<Nat>>, +nodup: Bool,
    le: {Nat.is_le(Groups.len_words(S), 0n) == True{} : Bool}) ->
  FOpt.EJob(0n, inf, G, C_root, n_root, has_buf, S, nodup):
  +eS = MV.MV.nil_of_len_zero(S,
          NatProof.Nat.eq_zero_of_le_zero(Groups.len_words(S), le))
  FOpt.ejob_transport(0n, inf, G, C_root, n_root, has_buf, Nil{}, S, nodup,
    Equal.sym(+List<+List<Nat>>, S, Nil{}, eS),
    FOpt.ejob_nil(inf, G, C_root, n_root, has_buf, nodup))

def FOpt.eflat_zero(+inf: Nat, +G: +List<+List<Nat>>,
    +C_root: +List<+List<Nat>>, +n_root: Nat, +has_buf: Bool, +nodup: Bool,
    +jobs: +List<+List<+List<Nat>>>,
    bounds: MV.MV.Bounds(0n, jobs)) ->
  FOpt.EFlat(0n, inf, G, C_root, n_root, has_buf, nodup, jobs):
  match jobs:
    case Nil{}:
      Unit{}
    case Con{S, t}:
      (ble, bt) = bounds
      Tuple{FOpt.ejob_zero(inf, G, C_root, n_root, has_buf, S, nodup, ble),
            FOpt.eflat_zero(inf, G, C_root, n_root, has_buf, nodup, t, bt)}

def FOpt.eflat_step(+inf: Nat, +p: Nat, +G: +List<+List<Nat>>,
    +C_root: +List<+List<Nat>>, +n_root: Nat, +has_buf: Bool, +nodup: Bool,
    +jobs: +List<+List<+List<Nat>>>,
    bounds: MV.MV.Bounds(1n+p, jobs),
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +h3: {Nat.is_lt(3n, inf) == True{} : Bool},
    +h6: {Nat.is_lt(6n, inf) == True{} : Bool},
    +aj: {FO.FO.all_in_jobs_b(jobs, G) == True{} : Bool},
    +nj: {FN.FN.nodup_ok_jobs(nodup, jobs) == True{} : Bool},
    f: FOpt.EFlat(p, inf, G, C_root, n_root, has_buf, nodup,
         FOpt.next_jobs(G, jobs))) ->
  FOpt.EFlat(1n+p, inf, G, C_root, n_root, has_buf, nodup, jobs):
  match jobs:
    case Nil{}:
      Unit{}
    case Con{+S, +t}:
      (+ble, bt) = bounds
      +ai = Logic.Proof.and_true_l(FO.FO.all_in_ref(S, G),
              FO.FO.all_in_jobs_b(t, G), aj)
      +at = Logic.Proof.and_true_r(FO.FO.all_in_ref(S, G),
              FO.FO.all_in_jobs_b(t, G), aj)
      +nd = Logic.Proof.and_true_l(FN.FN.nodup_ok(nodup, S),
              FN.FN.nodup_ok_jobs(nodup, t), nj)
      +nt = Logic.Proof.and_true_r(FN.FN.nodup_ok(nodup, S),
              FN.FN.nodup_ok_jobs(nodup, t), nj)
      MV.MV.use_pair(
        FOpt.EFlat(1n+p, inf, G, C_root, n_root, has_buf, nodup, S <> t),
        FOpt.EFlat(p, inf, G, C_root, n_root, has_buf, nodup,
          List.append(&2, +List<+List<Nat>>,
            MV.MV.next_guess(S, S), MV.MV.next_guess(G, S))),
        FOpt.EFlat(p, inf, G, C_root, n_root, has_buf, nodup,
          FOpt.next_jobs(G, t)),
        FOpt.eflat_append(p, inf, G, C_root, n_root, has_buf, nodup,
          List.append(&2, +List<+List<Nat>>,
            MV.MV.next_guess(S, S), MV.MV.next_guess(G, S)),
          FOpt.next_jobs(G, t), f),
        fSG => ft =>
          MV.MV.use_pair(
            FOpt.EFlat(1n+p, inf, G, C_root, n_root, has_buf, nodup, S <> t),
            FOpt.EFlat(p, inf, G, C_root, n_root, has_buf, nodup,
              MV.MV.next_guess(S, S)),
            FOpt.EFlat(p, inf, G, C_root, n_root, has_buf, nodup,
              MV.MV.next_guess(G, S)),
            FOpt.eflat_append(p, inf, G, C_root, n_root, has_buf, nodup,
              MV.MV.next_guess(S, S), MV.MV.next_guess(G, S), fSG),
            fS => fG =>
              Tuple{FOpt.ejob_succ(p, inf, G, C_root, n_root, has_buf, S, nodup,
                      ble, hz, h1, h3, h6, ai, nd,
                      FOpt.eby_gs(p, inf, G, C_root, n_root, has_buf, S, nodup,
                        S, fS),
                      FOpt.eby_gs(p, inf, G, C_root, n_root, has_buf, S, nodup,
                        G, fG)),
                    FOpt.eflat_step(inf, p, G, C_root, n_root, has_buf, nodup,
                      t, bt, hz, h1, h3, h6, at, nt, ft)}))

def FOpt.eflat(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +C_root: +List<+List<Nat>>, +n_root: Nat, +has_buf: Bool, +nodup: Bool,
    +jobs: +List<+List<+List<Nat>>>,
    bounds: MV.MV.Bounds(fuel, jobs),
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +h3: {Nat.is_lt(3n, inf) == True{} : Bool},
    +h6: {Nat.is_lt(6n, inf) == True{} : Bool},
    +aj: {FO.FO.all_in_jobs_b(jobs, G) == True{} : Bool},
    +nj: {FN.FN.nodup_ok_jobs(nodup, jobs) == True{} : Bool}) ->
  FOpt.EFlat(fuel, inf, G, C_root, n_root, has_buf, nodup, jobs):
  match fuel:
    case 0n:
      FOpt.eflat_zero(inf, G, C_root, n_root, has_buf, nodup, jobs, bounds)
    case 1n+p:
      MV.MV.use_pair(
        FOpt.EFlat(1n+p, inf, G, C_root, n_root, has_buf, nodup, jobs),
        MV.MV.Bounds(1n+p, jobs), MV.MV.Bounds(1n+p, jobs),
        FOpt.bounds_copy(1n+p, jobs, bounds),
        b1 => b2 =>
          FOpt.eflat_step(inf, p, G, C_root, n_root, has_buf, nodup, jobs, b1,
            hz, h1, h3, h6, aj, nj,
            FOpt.eflat(p, inf, G, C_root, n_root, has_buf, nodup,
              FOpt.next_jobs(G, jobs), FOpt.next_bounds(p, G, jobs, b2),
              hz, h1, h3, h6, FOpt.all_in_next_jobs(G, jobs, aj),
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

def FOpt.job_res_of_spec(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +C_root: +List<+List<Nat>>, +n_root: Nat, +has_buf: Bool, +nodup: Bool,
    +S: +List<+List<Nat>>, +limit: Nat, sr: SolveFast.StepRes,
    +hspec: FOpt.JobResSpec(fuel, inf, G, C_root, n_root, has_buf, nodup, S,
              limit, sr)) ->
  {FOpt.job_res_b(fuel, inf, G, S, limit, SolveFast.step_res_best(sr))
   == True{} : Bool}:
  match sr:
    case SolveFast.StepRes{res, buf2}:
      Arr.Arr.dpair_l(
        {FOpt.job_res_b(fuel, inf, G, S, limit, res) == True{} : Bool},
        FH.FH.BufOk(G, C_root, n_root, has_buf, nodup, buf2), hspec)

def FOpt.root_ge3_dup(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +cs: +List<+List<Nat>>, +nd: Bool, +has_buf: Bool,
    +rwsG: +List<FT.FT.RowWord>, +cwS: +List<SolveFast.CWord>,
    -buf0: SolveFast.Buf5,
    +hbuf0: FH.FH.BufOk(G, cs, Groups.len_words(cs), has_buf, nd, buf0),
    dp: &b1: SolveFast.Buf5 -> &b2: SolveFast.Buf5 ->
        {b1 == buf0 : SolveFast.Buf5} & {b2 == b1 : SolveFast.Buf5},
    +en: {Groups.len_words(cs) == 1n+p : Nat},
    +erwsG: {FT.FT.rws_words(rwsG) == G : +List<+List<Nat>>},
    +hrwsG: {FH.FH.rws_ok_if(has_buf, G, Groups.len_words(cs), rwsG)
             == True{} : Bool},
    +ecwS: {SolveFast.cwords_words(cwS) == cs : +List<+List<Nat>>},
    +hcwS: {FH.FH.cwords_ok_if(has_buf, G, cs, Groups.len_words(cs), cwS)
            == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +h3: {Nat.is_lt(3n, inf) == True{} : Bool},
    +h6: {Nat.is_lt(6n, inf) == True{} : Bool},
    +ai: {FO.FO.all_in_ref(cs, G) == True{} : Bool},
    +hnd: {FN.FN.nodup_ok(nd, cs) == True{} : Bool},
    fG: FOpt.EByGs(p, inf, G, cs, Groups.len_words(cs), has_buf, cs, nd, G)) ->
  {FOpt.job_res_b(1n+p, inf, G, cs, inf,
     SolveFast.step_res_best(
       SolveFast.step(1n+p, FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), 0n,
         Nil{}, FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS,
         Groups.len_words(cs), nd, SolveFast.init_floor(Groups.len_words(cs)),
         inf, Nil{}, Nil{}, 0n, SolveFast.dummy_inf(inf),
         SolveFast.dummy_step_zero(), False{},
         SolveFast.is_floor_hit(nd, SolveFast.init_floor(Groups.len_words(cs)),
           SolveFast.dummy_inf(inf)),
         SolveFast.GuessRes{Nil{}, buf0}))) == True{} : Bool}:
  (b1, d2) = dp
  (b2, pe) = d2
  (+eb1, +eb2) = pe
  +n : Nat = Groups.len_words(cs)
  +gG : SolveFast.GList = FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{})
  +b0 : SolveRef.Best = SolveFast.dummy_inf(inf)
  +fl : Nat = SolveFast.init_floor(n)
  +ele : {Nat.is_le(n, 1n+p) == True{} : Bool} =
    Fold.OQ.le_cong_l(n, 1n+p, 1n+p, en, NatProof.Nat.is_le_refl(1n+p))
  +eb2_0 : {b2 == buf0 : SolveFast.Buf5} =
    Equal.trans(SolveFast.Buf5, b2, b1, buf0, eb2, eb1)
  +hbuf2 = FH.FH.buf_ok_transport(G, cs, n, has_buf, nd, buf0, b2,
             Equal.sym(SolveFast.Buf5, b2, buf0, eb2_0), hbuf0)
  +hspec2 = FOpt.ejob_succ_direct(p, inf, G, cs, n, has_buf, rwsG, cwS, cs, nd,
              b0, b2, erwsG, hrwsG, ecwS, hcwS, NatProof.Nat.is_le_refl(inf),
              hbuf2, ele, hz, h1, h3, h6, ai, hnd, fG)
  +hspec1 = FOpt.job_res_spec_transport(1n+p, inf, G, cs, n, has_buf, nd, cs,
              inf,
              SolveFast.step(1n+p, gG, 0n, Nil{}, gG, cwS, n, nd, fl, inf,
                Nil{}, Nil{}, 0n, b0, SolveFast.dummy_step_zero(), False{},
                SolveFast.is_floor_hit(nd, fl, b0),
                SolveFast.GuessRes{Nil{}, b2}),
              SolveFast.step(1n+p, gG, 0n, Nil{}, gG, cwS, n, nd, fl, inf,
                Nil{}, Nil{}, 0n, b0, SolveFast.dummy_step_zero(), False{},
                SolveFast.is_floor_hit(nd, fl, b0),
                SolveFast.GuessRes{Nil{}, b1}),
              Equal.cong(SolveFast.Buf5, SolveFast.StepRes,
                b => SolveFast.step(1n+p, gG, 0n, Nil{}, gG, cwS, n, nd, fl,
                       inf, Nil{}, Nil{}, 0n, b0, SolveFast.dummy_step_zero(),
                       False{}, SolveFast.is_floor_hit(nd, fl, b0),
                       SolveFast.GuessRes{Nil{}, b}), b2, b1, eb2),
              hspec2)
  %eb1 : {FOpt.job_res_b(1n+p, inf, G, cs, inf,
            SolveFast.step_res_best(
              SolveFast.step(1n+p, gG, 0n, Nil{}, gG, cwS, n, nd, fl, inf,
                Nil{}, Nil{}, 0n, b0, SolveFast.dummy_step_zero(), False{},
                SolveFast.is_floor_hit(nd, fl, b0),
                SolveFast.GuessRes{Nil{}, _}))) == True{} : Bool}
  FOpt.job_res_of_spec(1n+p, inf, G, cs, n, has_buf, nd, cs, inf,
    SolveFast.step(1n+p, gG, 0n, Nil{}, gG, cwS, n, nd, fl, inf,
      Nil{}, Nil{}, 0n, b0, SolveFast.dummy_step_zero(), False{},
      SolveFast.is_floor_hit(nd, fl, b0), SolveFast.GuessRes{Nil{}, b1}),
    hspec1)

def FOpt.root_ge3_ok(+G: +List<+List<Nat>>, +w: +List<Nat>, +w2: +List<Nat>,
    +w3: +List<Nat>, +t3: +List<+List<Nat>>,
    +ai: {FO.FO.all_in_ref(w <> (w2 <> (w3 <> t3)), G) == True{} : Bool}) ->
  {FOpt.job_res_b(
     Groups.len_words(w <> (w2 <> (w3 <> t3))),
     SolveRef.inf_of(Groups.len_words(w <> (w2 <> (w3 <> t3)))),
     G, w <> (w2 <> (w3 <> t3)),
     SolveRef.inf_of(Groups.len_words(w <> (w2 <> (w3 <> t3)))),
     SolveFast.step_res_best(
       SolveFast.step(
         Groups.len_words(w <> (w2 <> (w3 <> t3))),
         SolveFast.glist_of_guesses(G, 0, 1),
         0n, Nil{},
         SolveFast.glist_of_guesses(G, 0, 1),
         SolveFast.build_cwords(w <> (w2 <> (w3 <> t3)), G, 0,
           U32.from_nat(Groups.len_words(G))),
         Groups.len_words(w <> (w2 <> (w3 <> t3))),
         SolveFast.no_dup_fast(w <> (w2 <> (w3 <> t3))),
         SolveFast.init_floor(Groups.len_words(w <> (w2 <> (w3 <> t3)))),
         SolveRef.inf_of(Groups.len_words(w <> (w2 <> (w3 <> t3)))),
         Nil{}, Nil{}, 0n,
         SolveFast.dummy_inf(
           SolveRef.inf_of(Groups.len_words(w <> (w2 <> (w3 <> t3))))),
         SolveFast.dummy_step_zero(), False{},
         SolveFast.is_floor_hit(
           SolveFast.no_dup_fast(w <> (w2 <> (w3 <> t3))),
           SolveFast.init_floor(Groups.len_words(w <> (w2 <> (w3 <> t3)))),
           SolveFast.dummy_inf(
             SolveRef.inf_of(Groups.len_words(w <> (w2 <> (w3 <> t3)))))),
         SolveFast.GuessRes{Nil{},
           SolveFast.mk_buf_tbl(
             SolveFast.no_dup_fast(w <> (w2 <> (w3 <> t3))),
             G, w <> (w2 <> (w3 <> t3)),
             Groups.len_words(w <> (w2 <> (w3 <> t3))))})))
   == True{} : Bool}:
  +cs : +List<+List<Nat>> = w <> (w2 <> (w3 <> t3))
  +p : Nat = Groups.len_words(w2 <> (w3 <> t3))
  +n : Nat = Groups.len_words(cs)
  +gcount : U32 = U32.from_nat(Groups.len_words(G))
  +inf : Nat = SolveRef.inf_of(n)
  +nd : Bool = SolveFast.no_dup_fast(cs)
  +has_buf : Bool = FH.FH.mk_buf_has(nd, G, cs, n)
  +hnd = FOpt.nodup_ok_of_fast(cs)
  +aj = FO.FO.bool_and_intro(FO.FO.all_in_ref(cs, G), True{}, ai, {==})
  +nj = FO.FO.bool_and_intro(FN.FN.nodup_ok(nd, cs), True{}, hnd, {==})
  +h3_le_n : {Nat.is_le(3n, n) == True{} : Bool} =
    NatProof.Nat.is_le_zero_l(Groups.len_words(t3))
  +h9_le_sq : {Nat.is_le(9n, Nat.mul(n, n)) == True{} : Bool} =
    NatProof.Nat.is_le_trans(9n, Nat.mul(3n, n), Nat.mul(n, n),
      CBN.CB.is_le_mul_r(3n, n, 3n, h3_le_n),
      CBN.CB.is_le_mul_l(3n, n, n, h3_le_n))
  +h6 : {Nat.is_lt(6n, inf) == True{} : Bool} =
    NatProof.Nat.is_le_lt_trans(6n, Nat.mul(n, n), inf,
      NatProof.Nat.is_le_trans(6n, 9n, Nat.mul(n, n), {==}, h9_le_sq),
      CBN.CB.lt_add_one(Nat.mul(n, n)))
  +h3 : {Nat.is_lt(3n, inf) == True{} : Bool} =
    NatProof.Nat.is_le_lt_trans(3n, 6n, inf, {==}, h6)
  +h1 : {Nat.is_lt(1n, inf) == True{} : Bool} =
    NatProof.Nat.is_le_lt_trans(1n, 6n, inf, {==}, h6)
  +hz : {Nat.is_lt(0n, inf) == True{} : Bool} =
    NatProof.Nat.is_le_lt_trans(0n, 6n, inf, {==}, h6)
  +rwsG : +List<FT.FT.RowWord> = FT.FT.guesses_to_rws(G, 0, 1)
  +cwS : +List<SolveFast.CWord> = SolveFast.build_cwords(cs, G, 0, gcount)
  +egG = FT.FT.glist_of_guesses_eq(G, 0, 1)
  +erwsG = FT.FT.guesses_to_rws_words(G, 0, 1)
  +hrwsG = FOpt.guesses_to_rws_ok_if(has_buf, G, n)
  +ecwS = FT.FT.build_cwords_words(cs, G, 0, gcount)
  +hcwS = FOpt.build_cwords_ok_if(has_buf, G, cs, n, ai)
  bounds : MV.MV.Bounds(1n+p, cs <> Nil{}) =
    Tuple{NatProof.Nat.is_le_refl(n), Unit{}}
  ff : FOpt.EFlat(p, inf, G, cs, n, has_buf, nd, FOpt.next_jobs(G, cs <> Nil{})) =
    FOpt.eflat(p, inf, G, cs, n, has_buf, nd, FOpt.next_jobs(G, cs <> Nil{}),
      FOpt.next_bounds(p, G, cs <> Nil{}, bounds), hz, h1, h3, h6,
      FOpt.all_in_next_jobs(G, cs <> Nil{}, aj),
      FOpt.nodup_ok_next_jobs(nd, G, cs <> Nil{}, nj))
  %Equal.sym(SolveFast.GList,
     SolveFast.glist_of_guesses(G, 0, 1),
     FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), egG) :
    {FOpt.job_res_b(n, inf, G, cs, inf,
       SolveFast.step_res_best(
         SolveFast.step(n, _, 0n, Nil{}, _, cwS, n, nd,
           SolveFast.init_floor(n), inf, Nil{}, Nil{}, 0n,
           SolveFast.dummy_inf(inf), SolveFast.dummy_step_zero(), False{},
           SolveFast.is_floor_hit(nd, SolveFast.init_floor(n),
             SolveFast.dummy_inf(inf)),
           SolveFast.GuessRes{Nil{}, SolveFast.mk_buf_tbl(nd, G, cs, n)})))
     == True{} : Bool}
  MV.MV.use_pair(
    {FOpt.job_res_b(n, inf, G, cs, inf,
       SolveFast.step_res_best(
         SolveFast.step(n, FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), 0n,
           Nil{}, FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS, n, nd,
           SolveFast.init_floor(n), inf, Nil{}, Nil{}, 0n,
           SolveFast.dummy_inf(inf), SolveFast.dummy_step_zero(), False{},
           SolveFast.is_floor_hit(nd, SolveFast.init_floor(n),
             SolveFast.dummy_inf(inf)),
           SolveFast.GuessRes{Nil{}, SolveFast.mk_buf_tbl(nd, G, cs, n)})))
     == True{} : Bool},
    FOpt.EFlat(p, inf, G, cs, n, has_buf, nd,
      List.append(&2, +List<+List<Nat>>,
        MV.MV.next_guess(cs, cs), MV.MV.next_guess(G, cs))),
    FOpt.EFlat(p, inf, G, cs, n, has_buf, nd, FOpt.next_jobs(G, Nil{})),
    FOpt.eflat_append(p, inf, G, cs, n, has_buf, nd,
      List.append(&2, +List<+List<Nat>>,
        MV.MV.next_guess(cs, cs), MV.MV.next_guess(G, cs)),
      FOpt.next_jobs(G, Nil{}), ff),
    fSG => fNil =>
      MV.MV.use_pair(
        {FOpt.job_res_b(n, inf, G, cs, inf,
           SolveFast.step_res_best(
             SolveFast.step(n, FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), 0n,
               Nil{}, FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), cwS, n, nd,
               SolveFast.init_floor(n), inf, Nil{}, Nil{}, 0n,
               SolveFast.dummy_inf(inf), SolveFast.dummy_step_zero(), False{},
               SolveFast.is_floor_hit(nd, SolveFast.init_floor(n),
                 SolveFast.dummy_inf(inf)),
               SolveFast.GuessRes{Nil{}, SolveFast.mk_buf_tbl(nd, G, cs, n)})))
         == True{} : Bool},
        FOpt.EFlat(p, inf, G, cs, n, has_buf, nd, MV.MV.next_guess(cs, cs)),
        FOpt.EFlat(p, inf, G, cs, n, has_buf, nd, MV.MV.next_guess(G, cs)),
        FOpt.eflat_append(p, inf, G, cs, n, has_buf, nd,
          MV.MV.next_guess(cs, cs), MV.MV.next_guess(G, cs), fSG),
        fS => fG =>
          FOpt.root_ge3_dup(p, inf, G, cs, nd, has_buf, rwsG, cwS,
            SolveFast.mk_buf_tbl(nd, G, cs, n),
            FH.FH.mk_buf_tbl_ok(nd, G, cs, n, {==}),
            FH.FH.buf_dup(SolveFast.mk_buf_tbl(nd, G, cs, n)),
            {==}, erwsG, hrwsG, ecwS, hcwS, hz, h1, h3, h6, ai, hnd,
            FOpt.eby_gs(p, inf, G, cs, n, has_buf, cs, nd, G, fG))))

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
      +hlt = Sat.SB.lt_of_ge_false(cost, inf,
               Equal.sym(Bool, False{}, Nat.is_ge(cost, inf), eb))
      +hext = FVal.FV.best_ok_extract(inf, G, C, SolveRef.Best{tree, cost},
                hok, hlt)
      +hval = Logic.Proof.and_true_l(FVal.FV.valid_b(tree, G, C),
                Nat.is_le(Tree.cost(tree, C), cost), hext)
      +et = FOpt.some_inj(tree, T, e)
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
  +gG : SolveFast.GList = SolveFast.glist_of_words(G, SolveFast.GEnd{})
  +b0 : SolveRef.Best = SolveFast.dummy_inf(1n)
  +eb : {SolveFast.step_res_best(
           SolveFast.step(0n, gG, 0n, Nil{}, gG, Nil{}, 0n, True{}, 0n, 1n,
             Nil{}, Nil{}, 0n, b0, SolveFast.dummy_step_zero(), False{},
             SolveFast.is_floor_hit(True{}, 0n, b0),
             SolveFast.GuessRes{Nil{}, SolveFast.NoBuf{}}))
         == MV.MV.solve_best(G, Nil{}) : SolveRef.Best} =
    Equal.trans(SolveRef.Best,
      SolveFast.step_res_best(
        SolveFast.step(0n, gG, 0n, Nil{}, gG, Nil{}, 0n, True{}, 0n, 1n,
          Nil{}, Nil{}, 0n, b0, SolveFast.dummy_step_zero(), False{},
          SolveFast.is_floor_hit(True{}, 0n, b0),
          SolveFast.GuessRes{Nil{}, SolveFast.NoBuf{}})),
      Eval.Eval.guesses(0n, G, Nil{}, 1n, G, b0),
      MV.MV.solve_best(G, Nil{}),
      Equal.cong(SolveFast.StepRes, SolveRef.Best, SolveFast.step_res_best,
        SolveFast.step(0n, gG, 0n, Nil{}, gG, Nil{}, 0n, True{}, 0n, 1n,
          Nil{}, Nil{}, 0n, b0, SolveFast.dummy_step_zero(), False{},
          SolveFast.is_floor_hit(True{}, 0n, b0),
          SolveFast.GuessRes{Nil{}, SolveFast.NoBuf{}}),
        SolveFast.StepRes{Eval.Eval.guesses(0n, G, Nil{}, 1n, G, b0),
          SolveFast.NoBuf{}},
        FOpt.guesses_zero_words_eq(G, G, gG, True{}, 0n, 1n, b0,
          SolveFast.is_floor_hit(True{}, 0n, b0), SolveFast.NoBuf{})),
      Equal.sym(SolveRef.Best, MV.MV.solve_best(G, Nil{}),
        Eval.Eval.guesses(0n, G, Nil{}, 1n, G, b0),
        Eval.Eval.guesses_zero(G, 1n, G, b0)))
  Equal.cong(SolveRef.Best, Maybe<Tree.Tree>,
    b => SolveRef.best_to_maybe(1n, b),
    SolveFast.step_res_best(
      SolveFast.step(0n, gG, 0n, Nil{}, gG, Nil{}, 0n, True{}, 0n, 1n,
        Nil{}, Nil{}, 0n, b0, SolveFast.dummy_step_zero(), False{},
        SolveFast.is_floor_hit(True{}, 0n, b0),
        SolveFast.GuessRes{Nil{}, SolveFast.NoBuf{}})),
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
      +et = FOpt.some_inj(Tree.Node{w, Nil{}}, T, e)
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
      +et = FOpt.some_inj(SolveFast.two_tree(w, w2), T, e)
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
          +win = FO.FO.all_in_head(w, Nil{}, G, ai)
          +et = FOpt.some_inj(Tree.Node{w, Nil{}}, T, e)
          %et : Tree.Valid(_, G, w <> Nil{})
          FVal.FV.valid_of_b(Tree.Node{w, Nil{}}, G, w <> Nil{},
            FVal.FV.one_tree_valid_b(w, G, win))
        case Con{+w2, +t2}:
          match t2:
            case Nil{}:
              +w1in = FO.FO.all_in_head(w, w2 <> Nil{}, G, ai)
              +w2in = FO.FO.all_in_head(w2, Nil{}, G,
                        FO.FO.all_in_tail(w, w2 <> Nil{}, G, ai))
              FOpt.solve_valid_two(G, w, w2, T,
                SolveFast.word_eq_fast(w, w2), {==}, w1in, w2in, e)
            case Con{+w3, +t3}:
              +cs : +List<+List<Nat>> = w <> (w2 <> (w3 <> t3))
              +n : Nat = Groups.len_words(cs)
              +gcount : U32 = U32.from_nat(Groups.len_words(G))
              +inf : Nat = SolveRef.inf_of(n)
              +nd : Bool = SolveFast.no_dup_fast(cs)
              +gG : SolveFast.GList = SolveFast.glist_of_guesses(G, 0, 1)
              +res : SolveRef.Best =
                SolveFast.step_res_best(
                  SolveFast.step(n, gG, 0n, Nil{}, gG,
                    SolveFast.build_cwords(cs, G, 0, gcount), n, nd,
                    SolveFast.init_floor(n), inf, Nil{}, Nil{}, 0n,
                    SolveFast.dummy_inf(inf), SolveFast.dummy_step_zero(),
                    False{},
                    SolveFast.is_floor_hit(nd, SolveFast.init_floor(n),
                      SolveFast.dummy_inf(inf)),
                    SolveFast.GuessRes{Nil{},
                      SolveFast.mk_buf_tbl(nd, G, cs, n)}))
              +hjr = FOpt.root_ge3_ok(G, w, w2, w3, t3, ai)
              +hok = Logic.Proof.and_true_l(FVal.FV.best_ok_b(inf, G, cs, res),
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
      +nd2 = FVal.FV.no_dup_two_of_word_eq_false(w, w2, hne)
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
          {SolveFast.solve_fast_valid(G, Nil{}) == Some{T} : Maybe<Tree.Tree>}
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
          +es_ref = OC.OC.best_to_maybe_fin(inf, MV.MV.solve_best(G, Nil{}),
                      fin2)
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
              +gcount : U32 = U32.from_nat(Groups.len_words(G))
              +inf : Nat = SolveRef.inf_of(n)
              +nd : Bool = SolveFast.no_dup_fast(cs)
              +gG : SolveFast.GList = SolveFast.glist_of_guesses(G, 0, 1)
              +res : SolveRef.Best =
                SolveFast.step_res_best(
                  SolveFast.step(n, gG, 0n, Nil{}, gG,
                    SolveFast.build_cwords(cs, G, 0, gcount), n, nd,
                    SolveFast.init_floor(n), inf, Nil{}, Nil{}, 0n,
                    SolveFast.dummy_inf(inf), SolveFast.dummy_step_zero(),
                    False{},
                    SolveFast.is_floor_hit(nd, SolveFast.init_floor(n),
                      SolveFast.dummy_inf(inf)),
                    SolveFast.GuessRes{Nil{},
                      SolveFast.mk_buf_tbl(nd, G, cs, n)}))
              +hjr = FOpt.root_ge3_ok(G, w, w2, w3, t3, ai)
              +hok = Logic.Proof.and_true_l(FVal.FV.best_ok_b(inf, G, cs, res),
                       Bool.and(Nat.is_le(Eval.Eval.cost_of(res), inf),
                         Nat.is_le(Eval.Eval.cost_of(res),
                           Eval.Eval.cost_of(FS.FS.ref_run_at(n, inf, G, cs)))),
                       hjr)
              +hjr_r = Logic.Proof.and_true_r(FVal.FV.best_ok_b(inf, G, cs, res),
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
                  +fin_res = NatProof.Nat.is_le_lt_trans(
                               Eval.Eval.cost_of(res),
                               Eval.Eval.cost_of(MV.MV.solve_best(G, cs)),
                               inf, hle_ref, fin)
                  +es = OC.OC.best_to_maybe_fin(inf, res, fin_res)
                  +hext = FVal.FV.best_ok_extract(inf, G, cs, res, hok, fin_res)
                  +hcost = Logic.Proof.and_true_r(
                             FVal.FV.valid_b(Eval.Eval.tree_of(res), G, cs),
                             Nat.is_le(Tree.cost(Eval.Eval.tree_of(res), cs),
                               Eval.Eval.cost_of(res)), hext)
                  +hle = NatProof.Nat.is_le_trans(
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
