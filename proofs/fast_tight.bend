# Correctness of sibling-level depth-two lookahead tightening
# (`SolveFast.scan_lb2_step`, `SolveFast.tighten_bigs_go`,
# `SolveFast.run_drain5_tight`, and `SolveFast.guess_items_buf`).
#
# Main theorems:
# 1. `FTight.scan_lb2_full`: scanning candidate guesses `ws` followed by
#    `glist_G` with `SolveFast.scan_lb2_step` preserves `FH.SeenTree` and `tbl`,
#    and certifies `LB2.all_usable_ge(G, ws, new_clb) == True{}` unconditionally
#    (for any initial cap `cap`).
# 2. `FTight.tighten_bigs_go_spec`: tightening a list of `BigClass` items either
#    prunes with a valid tightened witness list whose lower-bound sum reaches
#    `b_cost`, or returns an updated `BigClass` list preserving `FH.bigs_ok_b`,
#    `FH.bigs_groups`, and the running total lower bound.
# 3. `FTight.guess_items_buf_spec`: full 6-case `FH.GuessSpec` (including
#    `FH.GCSkipBody` for sibling-tightening prunes) and `FH.BufOk` preservation
#    for `SolveFast.guess_items_buf`.
import Base
import ../src/feedback.bend as Feedback
import ../src/tree.bend as Tree
import ../src/groups.bend as Groups
import ../src/solve_ref.bend as SolveRef
import ../src/solve_fast.bend as SolveFast
import ./logic.bend as Logic
import ./nat.bend as NatProof
import ./eval.bend as Eval
import ./mainvalid.bend as MV
import ./cover_groups.bend as CoverGroups
import ./fast_groups.bend as FG
import ./fast_lb.bend as FLB
import ./fast_one.bend as FO
import ./fast_nodup.bend as FN
import ./array.bend as Arr
import ./fast_perm.bend as FP
import ./fast_tbl.bend as FT
import ./fast_lb2.bend as LB2
import ./fast_hist5.bend as FH

# ---------------------------------------------------------------------------
# Small Nat and List helpers
# ---------------------------------------------------------------------------

def FTight.le_of_lt_false(a: Nat, b: Nat,
    +h: {Nat.is_lt(a, b) == False{} : Bool}) ->
  {Nat.is_le(b, a) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      Empty.absurd({Nat.is_le(1n+bp, 0n) == True{} : Bool},
        Logic.Proof.false_ne_true(Equal.sym(Bool, True{}, False{}, h)))
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      FTight.le_of_lt_false(ap, bp, h)

def FTight.list_append_assoc(-T: Data, +xs: +List<T>, +ys: +List<T>,
    +zs: +List<T>) ->
  {List.append(&2, T, List.append(&2, T, xs, ys), zs)
   == List.append(&2, T, xs, List.append(&2, T, ys, zs)) : +List<T>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Equal.cong(+List<T>, +List<T>, l => h <> l,
        List.append(&2, T, List.append(&2, T, t, ys), zs),
        List.append(&2, T, t, List.append(&2, T, ys, zs)),
        FTight.list_append_assoc(T, t, ys, zs))

def FTight.add_swap_l(+a: Nat, +b: Nat, +c: Nat) ->
  {Nat.add(a, Nat.add(b, c)) == Nat.add(b, Nat.add(a, c)) : Nat}:
  Equal.trans(Nat,
    Nat.add(a, Nat.add(b, c)),
    Nat.add(Nat.add(a, b), c),
    Nat.add(b, Nat.add(a, c)),
    Equal.sym(Nat, Nat.add(Nat.add(a, b), c), Nat.add(a, Nat.add(b, c)),
      NatProof.NatPrf.add_assoc(a, b, c)),
    Equal.trans(Nat,
      Nat.add(Nat.add(a, b), c),
      Nat.add(Nat.add(b, a), c),
      Nat.add(b, Nat.add(a, c)),
      Equal.cong(Nat, Nat, x => Nat.add(x, c), Nat.add(a, b), Nat.add(b, a),
        NatProof.NatPrf.add_comm(a, b)),
      NatProof.NatPrf.add_assoc(b, a, c)))

def FTight.bigs_lb_sum_add(+bs: +List<SolveFast.BigClass>, +acc: Nat) ->
  {SolveFast.bigs_lb_sum(bs, acc)
   == Nat.add(SolveFast.bigs_lb_sum(bs, 0n), acc) : Nat}:
  match bs:
    case Nil{}:
      {==}
    case Con{bc, +rest}:
      match bc:
        case SolveFast.BigClass{fb, ws, len, +clb}:
          +s = SolveFast.bigs_lb_sum(rest, 0n)
          +e1 : {SolveFast.bigs_lb_sum(rest, Nat.add(clb, acc))
                 == Nat.add(s, Nat.add(clb, acc)) : Nat} =
            FTight.bigs_lb_sum_add(rest, Nat.add(clb, acc))
          +e2 : {SolveFast.bigs_lb_sum(rest, Nat.add(clb, 0n))
                 == Nat.add(s, clb) : Nat} =
            Equal.trans(Nat,
              SolveFast.bigs_lb_sum(rest, Nat.add(clb, 0n)),
              Nat.add(s, Nat.add(clb, 0n)),
              Nat.add(s, clb),
              FTight.bigs_lb_sum_add(rest, Nat.add(clb, 0n)),
              Equal.cong(Nat, Nat, x => Nat.add(s, x), Nat.add(clb, 0n), clb,
                NatProof.NatPrf.add_zero(clb)))
          +e3 : {Nat.add(SolveFast.bigs_lb_sum(rest, Nat.add(clb, 0n)), acc)
                 == Nat.add(s, Nat.add(clb, acc)) : Nat} =
            Equal.trans(Nat,
              Nat.add(SolveFast.bigs_lb_sum(rest, Nat.add(clb, 0n)), acc),
              Nat.add(Nat.add(s, clb), acc),
              Nat.add(s, Nat.add(clb, acc)),
              Equal.cong(Nat, Nat, x => Nat.add(x, acc),
                SolveFast.bigs_lb_sum(rest, Nat.add(clb, 0n)),
                Nat.add(s, clb), e2),
              NatProof.NatPrf.add_assoc(s, clb, acc))
          Equal.trans(Nat,
            SolveFast.bigs_lb_sum(rest, Nat.add(clb, acc)),
            Nat.add(s, Nat.add(clb, acc)),
            Nat.add(SolveFast.bigs_lb_sum(rest, Nat.add(clb, 0n)), acc),
            e1,
            Equal.sym(Nat,
              Nat.add(SolveFast.bigs_lb_sum(rest, Nat.add(clb, 0n)), acc),
              Nat.add(s, Nat.add(clb, acc)), e3))

def FTight.bigs_lb_sum_cons(+fb: +List<Feedback.Color>,
    +ws: +List<SolveFast.CWord>, +len: Nat, +clb: Nat,
    +rest: +List<SolveFast.BigClass>) ->
  {SolveFast.bigs_lb_sum(SolveFast.BigClass{fb, ws, len, clb} <> rest, 0n)
   == Nat.add(SolveFast.bigs_lb_sum(rest, 0n), clb) : Nat}:
  Equal.trans(Nat,
    SolveFast.bigs_lb_sum(rest, Nat.add(clb, 0n)),
    Nat.add(SolveFast.bigs_lb_sum(rest, 0n), Nat.add(clb, 0n)),
    Nat.add(SolveFast.bigs_lb_sum(rest, 0n), clb),
    FTight.bigs_lb_sum_add(rest, Nat.add(clb, 0n)),
    Equal.cong(Nat, Nat, x => Nat.add(SolveFast.bigs_lb_sum(rest, 0n), x),
      Nat.add(clb, 0n), clb, NatProof.NatPrf.add_zero(clb)))

# ---------------------------------------------------------------------------
# Section 1: Soundness of `SolveFast.scan_lb2_step`
# ---------------------------------------------------------------------------

def FTight.LB2Spec(+gs_cov: +List<+List<Nat>>, +ws: +List<+List<Nat>>,
    +cur0: Nat, -tbl0: Array<U32>, lr: SolveFast.LB2Res) -> Data:
  match lr:
    case SolveFast.LB2Res{new_clb, seen2, tbl2, gen2, hit}:
      Arr.Arr.DPair<
        FH.FH.SeenTree(10n, 0, seen2, gen2, Nil{}),
        Arr.Arr.DPair<
          {tbl2 == tbl0 : Array<U32>},
          Arr.Arr.DPair<
            {Nat.is_le(new_clb, cur0) == True{} : Bool},
            {LB2.LB2.all_usable_ge(gs_cov, ws, new_clb) == True{} : Bool}>>>

def FTight.lb2_spec_transport(+gs_cov: +List<+List<Nat>>,
    +ws: +List<+List<Nat>>, +cur0: Nat, -tbl0: Array<U32>,
    -r1: SolveFast.LB2Res, -r2: SolveFast.LB2Res,
    +er: {r1 == r2 : SolveFast.LB2Res},
    +h: FTight.LB2Spec(gs_cov, ws, cur0, tbl0, r1)) ->
  FTight.LB2Spec(gs_cov, ws, cur0, tbl0, r2):
  %er : FTight.LB2Spec(gs_cov, ws, cur0, tbl0, _)
  h

def FTight.lb2_spec_transport_tbl(+gs_cov: +List<+List<Nat>>,
    +ws: +List<+List<Nat>>, +cur0: Nat, -t1: Array<U32>, -t2: Array<U32>,
    -r: SolveFast.LB2Res, +et: {t1 == t2 : Array<U32>},
    +h: FTight.LB2Spec(gs_cov, ws, cur0, t1, r)) ->
  FTight.LB2Spec(gs_cov, ws, cur0, t2, r):
  %et : FTight.LB2Spec(gs_cov, ws, cur0, _, r)
  h

def FTight.LB2OneSpec(+g: +List<Nat>, +ws: +List<+List<Nat>>,
    +cur0: Nat, +floor: Nat, -tbl0: Array<U32>,
    lr: SolveFast.LB2Res) -> Data:
  match lr:
    case SolveFast.LB2Res{cur2, seen2, tbl2, gen2, hit2}:
      Arr.Arr.DPair<
        FH.FH.SeenTree(10n, 0, seen2, gen2, Nil{}),
        Arr.Arr.DPair<
          {tbl2 == tbl0 : Array<U32>},
          Arr.Arr.DPair<
            {hit2 == Nat.is_le(cur2, floor) : Bool},
            Arr.Arr.DPair<
              {Nat.is_le(cur2, cur0) == True{} : Bool},
              {LB2.LB2.all_usable_ge(g <> Nil{}, ws, cur2) == True{} : Bool}>>>>

def FTight.lb2_one_transport(+g: +List<Nat>, +ws: +List<+List<Nat>>,
    +cur0: Nat, +floor: Nat, -tbl0: Array<U32>,
    -r1: SolveFast.LB2Res, -r2: SolveFast.LB2Res,
    +er: {r1 == r2 : SolveFast.LB2Res},
    +h: FTight.LB2OneSpec(g, ws, cur0, floor, tbl0, r1)) ->
  FTight.LB2OneSpec(g, ws, cur0, floor, tbl0, r2):
  %er : FTight.LB2OneSpec(g, ws, cur0, floor, tbl0, _)
  h

def FTight.Stage2WS(skip_self: Bool, +ws: +List<+List<Nat>>,
    +cur: Nat) -> Data:
  match skip_self:
    case True{}:
      {LB2.LB2.all_usable_ge(ws, ws, cur) == True{} : Bool}
    case False{}:
      Unit

def FTight.lb2_pruned_all_usable_s2_mem(+g: +List<Nat>,
    +ws: +List<+List<Nat>>, +cur: Nat,
    +hmem: {Tree.member_word(g, ws) == True{} : Bool},
    +hws: {LB2.LB2.all_usable_ge(ws, ws, cur) == True{} : Bool},
    us: Bool,
    +eus: {us == Groups.groups_smaller(ws, Groups.groups_build(g, ws, Nil{}))
           : Bool}) ->
  {Feedback.Bool.case(Bool, us,
     Nat.is_le(cur, SolveFast.lower_bound(Groups.len_words(ws),
                      Groups.groups_build(g, ws, Nil{}))),
     True{}) == True{} : Bool}:
  match us:
    case False{}:
      {==}
    case True{}:
      +hus : {Groups.groups_smaller(ws, Groups.groups_build(g, ws, Nil{}))
              == True{} : Bool} =
        Equal.sym(Bool, True{},
          Groups.groups_smaller(ws, Groups.groups_build(g, ws, Nil{})), eus)
      LB2.LB2.all_usable_ge_at(ws, ws, cur, g, hmem, hws, hus)

def FTight.lb2_pruned_all_usable(+g: +List<Nat>, +ws: +List<+List<Nat>>,
    +len: Nat, +cur: Nat, skip_self: Bool,
    +elen: {len == Groups.len_words(ws) : Nat},
    +hnd: {FN.FN.no_dup_ref(ws) == True{} : Bool},
    +hs2: FTight.Stage2WS(skip_self, ws, cur),
    mem: Bool, +emem: {mem == Tree.member_word(g, ws) : Bool},
    +hpr: {FH.FH.pruned_reason(g, ws, Nil{},
             SolveFast.lb2_bgt(len, cur, skip_self), skip_self)
           == True{} : Bool}) ->
  {LB2.LB2.all_usable_ge(g <> Nil{}, ws, cur) == True{} : Bool}:
  match skip_self:
    case False{}:
      +fg = SolveFast.fgroups_build_fast(g, ws, Nil{})
      +gb = Groups.groups_build(g, ws, Nil{})
      +hsk = FH.FH.pruned_skippable_true(g, ws, len, SolveFast.dummy_inf(cur),
               elen, hnd, hpr)
      +hle1 : {Nat.is_le(cur, SolveFast.lower_bound(len, gb)) == True{} : Bool} =
        NatProof.Nat.is_le_eq_r(cur, SolveFast.fgroups_lb_nodup(fg, len),
          SolveFast.lower_bound(len, gb),
          FH.FH.fgroups_lb_nodup_eq_lb(g, ws, len, hnd), hsk)
      +hle : {Nat.is_le(cur, SolveFast.lower_bound(Groups.len_words(ws), gb))
              == True{} : Bool} =
        NatProof.Nat.is_le_eq_r(cur, SolveFast.lower_bound(len, gb),
          SolveFast.lower_bound(Groups.len_words(ws), gb),
          Equal.cong(Nat, Nat, x => SolveFast.lower_bound(x, gb),
            len, Groups.len_words(ws), elen), hle1)
      FH.FH.bool_and_intro(
        Feedback.Bool.case(Bool, Groups.groups_smaller(ws, gb),
          Nat.is_le(cur, SolveFast.lower_bound(Groups.len_words(ws), gb)),
          True{}),
        True{},
        LB2.LB2.usable_case_of_le(Groups.groups_smaller(ws, gb), cur,
          SolveFast.lower_bound(Groups.len_words(ws), gb), hle),
        {==})
    case True{}:
      match mem:
        case True{}:
          +gb = Groups.groups_build(g, ws, Nil{})
          +hmem : {Tree.member_word(g, ws) == True{} : Bool} =
            Equal.sym(Bool, True{}, Tree.member_word(g, ws), emem)
          FH.FH.bool_and_intro(
            Feedback.Bool.case(Bool, Groups.groups_smaller(ws, gb),
              Nat.is_le(cur, SolveFast.lower_bound(Groups.len_words(ws), gb)),
              True{}),
            True{},
            FTight.lb2_pruned_all_usable_s2_mem(g, ws, cur, hmem, hs2,
              Groups.groups_smaller(ws, gb), {==}),
            {==})
        case False{}:
          +fg = SolveFast.fgroups_build_fast(g, ws, Nil{})
          +gb = Groups.groups_build(g, ws, Nil{})
          +b0 = SolveFast.lb2_bgt(len, cur, True{})
          +hnm : {Tree.member_word(g, ws) == False{} : Bool} =
            Equal.sym(Bool, False{}, Tree.member_word(g, ws), emem)
          +hpr2 : {Nat.is_le(
                     Nat.add(1n, Nat.add(b0, FH.FH.fgroups_count(fg))),
                     FH.FH.fgroups_total(fg)) == True{} : Bool} =
            Equal.trans(Bool,
              Nat.is_le(Nat.add(1n, Nat.add(b0, FH.FH.fgroups_count(fg))),
                FH.FH.fgroups_total(fg)),
              Bool.or(Tree.member_word(g, ws),
                Nat.is_le(Nat.add(1n, Nat.add(b0, FH.FH.fgroups_count(fg))),
                  FH.FH.fgroups_total(fg))), True{},
              Equal.cong(Bool, Bool,
                x => Bool.or(x,
                       Nat.is_le(
                         Nat.add(1n, Nat.add(b0, FH.FH.fgroups_count(fg))),
                         FH.FH.fgroups_total(fg))),
                False{}, Tree.member_word(g, ws), emem), hpr)
          +hsk = FH.FH.pruned_skippable_stage2(g, ws, len,
                   SolveFast.dummy_inf(cur), elen, hnm, hpr2)
          +hle1 : {Nat.is_le(cur, SolveFast.lower_bound(len, gb))
                   == True{} : Bool} =
            NatProof.Nat.is_le_eq_r(cur, SolveFast.fgroups_lb_nodup(fg, len),
              SolveFast.lower_bound(len, gb),
              FH.FH.fgroups_lb_nodup_eq_lb(g, ws, len, hnd), hsk)
          +hle : {Nat.is_le(cur, SolveFast.lower_bound(Groups.len_words(ws), gb))
                  == True{} : Bool} =
            NatProof.Nat.is_le_eq_r(cur, SolveFast.lower_bound(len, gb),
              SolveFast.lower_bound(Groups.len_words(ws), gb),
              Equal.cong(Nat, Nat, x => SolveFast.lower_bound(x, gb),
                len, Groups.len_words(ws), elen), hle1)
          FH.FH.bool_and_intro(
            Feedback.Bool.case(Bool, Groups.groups_smaller(ws, gb),
              Nat.is_le(cur, SolveFast.lower_bound(Groups.len_words(ws), gb)),
              True{}),
            True{},
            LB2.LB2.usable_case_of_le(Groups.groups_smaller(ws, gb), cur,
              SolveFast.lower_bound(Groups.len_words(ws), gb), hle),
            {==})

def FTight.lb2_pick_min_le_cur(+lb: Nat, +cur: Nat, lt: Bool,
    +elt: {lt == Nat.is_lt(lb, cur) : Bool}) ->
  {Nat.is_le(SolveFast.lb2_pick_min(lb, cur, lt), cur) == True{} : Bool}:
  match lt:
    case True{}:
      NatProof.Nat.is_le_of_lt(lb, cur,
        Equal.sym(Bool, True{}, Nat.is_lt(lb, cur), elt))
    case False{}:
      NatProof.Nat.is_le_refl(cur)

def FTight.lb2_pick_min_le_lb(+lb: Nat, +cur: Nat, lt: Bool,
    +elt: {lt == Nat.is_lt(lb, cur) : Bool}) ->
  {Nat.is_le(SolveFast.lb2_pick_min(lb, cur, lt), lb) == True{} : Bool}:
  match lt:
    case True{}:
      NatProof.Nat.is_le_refl(lb)
    case False{}:
      FTight.le_of_lt_false(lb, cur,
        Equal.sym(Bool, False{}, Nat.is_lt(lb, cur), elt))

def FTight.lb2_hist_usable_spec(+g: +List<Nat>, +ws: +List<+List<Nat>>,
    +len: Nat, +cur: Nat, +floor: Nat, +m: Nat, +k: Nat,
    -seen2: Array<Nat>, -tbl0: Array<U32>, -tbl2: Array<U32>, +gen2: Nat,
    usable: Bool,
    +eus: {usable == Groups.groups_smaller(ws, Groups.groups_build(g, ws, Nil{}))
           : Bool},
    +elen: {len == Groups.len_words(ws) : Nat},
    +hnd: {FN.FN.no_dup_ref(ws) == True{} : Bool},
    +hwf: {FH.FH.fgroups_wf(SolveFast.fgroups_build_fast(g, ws, Nil{}))
           == True{} : Bool},
    +hm: {m == FH.FH.fgroups_total(SolveFast.fgroups_build_fast(g, ws, Nil{}))
          : Nat},
    +hk: {k == FH.FH.fgroups_count(SolveFast.fgroups_build_fast(g, ws, Nil{}))
          : Nat},
    +hs2: FH.FH.SeenTree(10n, 0, seen2, gen2, Nil{}),
    +et2: {tbl2 == tbl0 : Array<U32>}) ->
  FTight.LB2OneSpec(g, ws, cur, floor, tbl0,
    SolveFast.lb2_hist_usable(len, cur, floor, m, k, seen2, tbl2, gen2,
      usable)):
  match usable:
    case False{}:
      +gb = Groups.groups_build(g, ws, Nil{})
      +hf : {Groups.groups_smaller(ws, gb) == False{} : Bool} =
        Equal.sym(Bool, False{}, Groups.groups_smaller(ws, gb), eus)
      +hall : {LB2.LB2.all_usable_ge(g <> Nil{}, ws, cur) == True{} : Bool} =
        FH.FH.bool_and_intro(
          Feedback.Bool.case(Bool, Groups.groups_smaller(ws, gb),
            Nat.is_le(cur, SolveFast.lower_bound(Groups.len_words(ws), gb)),
            True{}),
          True{},
          Equal.cong(Bool, Bool,
            u => Feedback.Bool.case(Bool, u,
                   Nat.is_le(cur,
                     SolveFast.lower_bound(Groups.len_words(ws), gb)),
                   True{}),
            Groups.groups_smaller(ws, gb), False{}, hf),
          {==})
      Arr.DPair{hs2, Arr.DPair{et2, Arr.DPair{{==},
        Arr.DPair{NatProof.Nat.is_le_refl(cur), hall}}}}
    case True{}:
      +fg = SolveFast.fgroups_build_fast(g, ws, Nil{})
      +gb = Groups.groups_build(g, ws, Nil{})
      +lb = Nat.sub(Nat.add(len, Nat.add(m, m)), k)
      +hpos = FH.FH.fgroups_pos_of_wf(fg, hwf)
      +elb_fg : {SolveFast.fgroups_lb_nodup(fg, len) == lb : Nat} =
        Equal.trans(Nat,
          SolveFast.fgroups_lb_nodup(fg, len),
          Nat.sub(
            Nat.add(len, Nat.add(FH.FH.fgroups_total(fg), FH.FH.fgroups_total(fg))),
            FH.FH.fgroups_count(fg)),
          lb,
          FH.FH.fgroups_lb_nodup_formula(len, fg, hpos),
          Equal.trans(Nat,
            Nat.sub(
              Nat.add(len, Nat.add(FH.FH.fgroups_total(fg), FH.FH.fgroups_total(fg))),
              FH.FH.fgroups_count(fg)),
            Nat.sub(Nat.add(len, Nat.add(m, m)), FH.FH.fgroups_count(fg)),
            lb,
            Equal.cong(Nat, Nat,
              x => Nat.sub(Nat.add(len, Nat.add(x, x)), FH.FH.fgroups_count(fg)),
              FH.FH.fgroups_total(fg), m,
              Equal.sym(Nat, m, FH.FH.fgroups_total(fg), hm)),
            Equal.cong(Nat, Nat, y => Nat.sub(Nat.add(len, Nat.add(m, m)), y),
              FH.FH.fgroups_count(fg), k,
              Equal.sym(Nat, k, FH.FH.fgroups_count(fg), hk))))
      +elb : {lb == SolveFast.lower_bound(Groups.len_words(ws), gb) : Nat} =
        Equal.trans(Nat, lb, SolveFast.lower_bound(len, gb),
          SolveFast.lower_bound(Groups.len_words(ws), gb),
          Equal.trans(Nat, lb, SolveFast.fgroups_lb_nodup(fg, len),
            SolveFast.lower_bound(len, gb),
            Equal.sym(Nat, SolveFast.fgroups_lb_nodup(fg, len), lb, elb_fg),
            FH.FH.fgroups_lb_nodup_eq_lb(g, ws, len, hnd)),
          Equal.cong(Nat, Nat, x => SolveFast.lower_bound(x, gb),
            len, Groups.len_words(ws), elen))
      +cur2 = SolveFast.lb2_pick_min(lb, cur, Nat.is_lt(lb, cur))
      +hle_cur : {Nat.is_le(cur2, cur) == True{} : Bool} =
        FTight.lb2_pick_min_le_cur(lb, cur, Nat.is_lt(lb, cur), {==})
      +hle_lb : {Nat.is_le(cur2, lb) == True{} : Bool} =
        FTight.lb2_pick_min_le_lb(lb, cur, Nat.is_lt(lb, cur), {==})
      +hle_v : {Nat.is_le(cur2, SolveFast.lower_bound(Groups.len_words(ws), gb))
                == True{} : Bool} =
        NatProof.Nat.is_le_eq_r(cur2, lb,
          SolveFast.lower_bound(Groups.len_words(ws), gb), elb, hle_lb)
      +hall : {LB2.LB2.all_usable_ge(g <> Nil{}, ws, cur2) == True{} : Bool} =
        FH.FH.bool_and_intro(
          Feedback.Bool.case(Bool, Groups.groups_smaller(ws, gb),
            Nat.is_le(cur2, SolveFast.lower_bound(Groups.len_words(ws), gb)),
            True{}),
          True{},
          LB2.LB2.usable_case_of_le(Groups.groups_smaller(ws, gb), cur2,
            SolveFast.lower_bound(Groups.len_words(ws), gb), hle_v),
          {==})
      Arr.DPair{hs2, Arr.DPair{et2, Arr.DPair{{==}, Arr.DPair{hle_cur, hall}}}}

def FTight.lb2_hist_ok_dup(+g: +List<Nat>, +ws: +List<+List<Nat>>,
    +len: Nat, +cur: Nat, +floor: Nat, +skip_self: Bool,
    -seen2: Array<Nat>, -tbl0: Array<U32>, -tbl2: Array<U32>,
    +gen: Nat, +m: Nat, +k: Nat, +b: Nat,
    +hge1: {Nat.is_le(1n, len) == True{} : Bool},
    +elen: {len == Groups.len_words(ws) : Nat},
    +hnd: {FN.FN.no_dup_ref(ws) == True{} : Bool},
    +hhr: FH.FH.HistSpec(g, ws, Nil{}, gen,
            SolveFast.lb2_bgt(len, cur, skip_self), skip_self, tbl0,
            SolveFast.Hist5Ok{seen2, tbl2, m, k, b}),
    dp: &s1: Array<Nat> -> &s2: Array<Nat> ->
        {s1 == seen2 : Array<Nat>} & {s2 == s1 : Array<Nat>}) ->
  FTight.LB2OneSpec(g, ws, cur, floor, tbl0,
    SolveFast.lb2_hist_usable(len, cur, floor, m, k, seen2, tbl2,
      Nat.add(1n, gen), Bool.or(Nat.is_lt(m, len), Nat.is_le(2n, k)))):
  (s1, dp2) = dp
  (s2, pe) = dp2
  (+es1, +es2) = pe
  +fg = SolveFast.fgroups_build_fast(g, ws, Nil{})
  +budget0 = SolveFast.lb2_bgt(len, cur, skip_self)
  +hs2 = Arr.Arr.dpair_l(
           FH.FH.SeenTree(10n, 0, seen2, gen, fg),
           Arr.Arr.DPair<{tbl2 == tbl0 : Array<U32>},
             Arr.Arr.DPair<{FH.FH.fgroups_wf(fg) == True{} : Bool},
               Arr.Arr.DPair<{m == FH.FH.fgroups_total(fg) : Nat},
                 Arr.Arr.DPair<{k == FH.FH.fgroups_count(fg) : Nat},
                   Arr.Arr.DPair<
                     {Nat.add(b, m) == Nat.add(budget0, k) : Nat},
                     {Nat.is_le(m, Nat.add(Groups.len_words(ws), 0n))
                      == True{} : Bool}>>>>>, hhr)
  +r1 = Arr.Arr.dpair_r(
          FH.FH.SeenTree(10n, 0, seen2, gen, fg),
          Arr.Arr.DPair<{tbl2 == tbl0 : Array<U32>},
            Arr.Arr.DPair<{FH.FH.fgroups_wf(fg) == True{} : Bool},
              Arr.Arr.DPair<{m == FH.FH.fgroups_total(fg) : Nat},
                Arr.Arr.DPair<{k == FH.FH.fgroups_count(fg) : Nat},
                  Arr.Arr.DPair<
                    {Nat.add(b, m) == Nat.add(budget0, k) : Nat},
                    {Nat.is_le(m, Nat.add(Groups.len_words(ws), 0n))
                     == True{} : Bool}>>>>>, hhr)
  +et20 = Arr.Arr.dpair_l({tbl2 == tbl0 : Array<U32>},
            Arr.Arr.DPair<{FH.FH.fgroups_wf(fg) == True{} : Bool},
              Arr.Arr.DPair<{m == FH.FH.fgroups_total(fg) : Nat},
                Arr.Arr.DPair<{k == FH.FH.fgroups_count(fg) : Nat},
                  Arr.Arr.DPair<
                    {Nat.add(b, m) == Nat.add(budget0, k) : Nat},
                    {Nat.is_le(m, Nat.add(Groups.len_words(ws), 0n))
                     == True{} : Bool}>>>>, r1)
  +r2 = Arr.Arr.dpair_r({tbl2 == tbl0 : Array<U32>},
          Arr.Arr.DPair<{FH.FH.fgroups_wf(fg) == True{} : Bool},
            Arr.Arr.DPair<{m == FH.FH.fgroups_total(fg) : Nat},
              Arr.Arr.DPair<{k == FH.FH.fgroups_count(fg) : Nat},
                Arr.Arr.DPair<
                  {Nat.add(b, m) == Nat.add(budget0, k) : Nat},
                  {Nat.is_le(m, Nat.add(Groups.len_words(ws), 0n))
                   == True{} : Bool}>>>>, r1)
  +hwf = Arr.Arr.dpair_l({FH.FH.fgroups_wf(fg) == True{} : Bool},
           Arr.Arr.DPair<{m == FH.FH.fgroups_total(fg) : Nat},
             Arr.Arr.DPair<{k == FH.FH.fgroups_count(fg) : Nat},
               Arr.Arr.DPair<
                 {Nat.add(b, m) == Nat.add(budget0, k) : Nat},
                 {Nat.is_le(m, Nat.add(Groups.len_words(ws), 0n))
                  == True{} : Bool}>>>, r2)
  +r3 = Arr.Arr.dpair_r({FH.FH.fgroups_wf(fg) == True{} : Bool},
          Arr.Arr.DPair<{m == FH.FH.fgroups_total(fg) : Nat},
            Arr.Arr.DPair<{k == FH.FH.fgroups_count(fg) : Nat},
              Arr.Arr.DPair<
                {Nat.add(b, m) == Nat.add(budget0, k) : Nat},
                {Nat.is_le(m, Nat.add(Groups.len_words(ws), 0n))
                 == True{} : Bool}>>>, r2)
  +hm = Arr.Arr.dpair_l({m == FH.FH.fgroups_total(fg) : Nat},
          Arr.Arr.DPair<{k == FH.FH.fgroups_count(fg) : Nat},
            Arr.Arr.DPair<
              {Nat.add(b, m) == Nat.add(budget0, k) : Nat},
              {Nat.is_le(m, Nat.add(Groups.len_words(ws), 0n))
               == True{} : Bool}>>, r3)
  +r4 = Arr.Arr.dpair_r({m == FH.FH.fgroups_total(fg) : Nat},
          Arr.Arr.DPair<{k == FH.FH.fgroups_count(fg) : Nat},
            Arr.Arr.DPair<
              {Nat.add(b, m) == Nat.add(budget0, k) : Nat},
              {Nat.is_le(m, Nat.add(Groups.len_words(ws), 0n))
               == True{} : Bool}>>, r3)
  +hk = Arr.Arr.dpair_l({k == FH.FH.fgroups_count(fg) : Nat},
          Arr.Arr.DPair<
            {Nat.add(b, m) == Nat.add(budget0, k) : Nat},
            {Nat.is_le(m, Nat.add(Groups.len_words(ws), 0n))
             == True{} : Bool}>, r4)
  +r5 = Arr.Arr.dpair_r({k == FH.FH.fgroups_count(fg) : Nat},
          Arr.Arr.DPair<
            {Nat.add(b, m) == Nat.add(budget0, k) : Nat},
            {Nat.is_le(m, Nat.add(Groups.len_words(ws), 0n))
             == True{} : Bool}>, r4)
  +hle0 = Arr.Arr.dpair_r(
            {Nat.add(b, m) == Nat.add(budget0, k) : Nat},
            {Nat.is_le(m, Nat.add(Groups.len_words(ws), 0n)) == True{} : Bool},
            r5)
  +es2_seen : {s2 == seen2 : Array<Nat>} =
    Equal.trans(Array<Nat>, s2, s1, seen2, es2, es1)
  +hs_s2 = FH.FH.seen_tree_transport(10n, 0, seen2, s2, gen, fg,
             Equal.sym(Array<Nat>, s2, seen2, es2_seen), hs2)
  +hbump = FH.FH.seen_tree_transport(10n, 0, s2, seen2, Nat.add(1n, gen), Nil{},
             es2_seen, FH.FH.seen_tree_bump(10n, 0, s2, gen, fg, hs_s2))
  +hle_n : {Nat.is_le(FH.FH.fgroups_total(fg), len) == True{} : Bool} =
    NatProof.Nat.is_le_eq_r(FH.FH.fgroups_total(fg),
      Nat.add(Groups.len_words(ws), 0n), len,
      Equal.trans(Nat, Nat.add(Groups.len_words(ws), 0n), Groups.len_words(ws),
        len, NatProof.NatPrf.add_zero(Groups.len_words(ws)),
        Equal.sym(Nat, len, Groups.len_words(ws), elen)),
      NatProof.Nat.is_le_eq_l(Nat.add(Groups.len_words(ws), 0n), m,
        FH.FH.fgroups_total(fg), hm, hle0))
  +eus_fg : {SolveFast.fgroups_smaller(len, fg)
             == Bool.or(Nat.is_lt(m, len), Nat.is_le(2n, k)) : Bool} =
    Equal.trans(Bool,
      SolveFast.fgroups_smaller(len, fg),
      Bool.or(Nat.is_lt(FH.FH.fgroups_total(fg), len),
        Nat.is_le(2n, FH.FH.fgroups_count(fg))),
      Bool.or(Nat.is_lt(m, len), Nat.is_le(2n, k)),
      FH.FH.fgroups_smaller_formula(len, fg, FH.FH.fgroups_pos_of_wf(fg, hwf),
        hge1, hle_n),
      Equal.trans(Bool,
        Bool.or(Nat.is_lt(FH.FH.fgroups_total(fg), len),
          Nat.is_le(2n, FH.FH.fgroups_count(fg))),
        Bool.or(Nat.is_lt(m, len), Nat.is_le(2n, FH.FH.fgroups_count(fg))),
        Bool.or(Nat.is_lt(m, len), Nat.is_le(2n, k)),
        Equal.cong(Nat, Bool,
          x => Bool.or(Nat.is_lt(x, len),
                 Nat.is_le(2n, FH.FH.fgroups_count(fg))),
          FH.FH.fgroups_total(fg), m,
          Equal.sym(Nat, m, FH.FH.fgroups_total(fg), hm)),
        Equal.cong(Nat, Bool,
          y => Bool.or(Nat.is_lt(m, len), Nat.is_le(2n, y)),
          FH.FH.fgroups_count(fg), k,
          Equal.sym(Nat, k, FH.FH.fgroups_count(fg), hk))))
  +eus_g : {SolveFast.fgroups_smaller(len, fg)
            == Groups.groups_smaller(ws, Groups.groups_build(g, ws, Nil{}))
            : Bool} =
    Equal.trans(Bool,
      SolveFast.fgroups_smaller(len, fg),
      SolveFast.fgroups_smaller(Groups.len_words(ws), fg),
      Groups.groups_smaller(ws, Groups.groups_build(g, ws, Nil{})),
      Equal.cong(Nat, Bool, x => SolveFast.fgroups_smaller(x, fg),
        len, Groups.len_words(ws), elen),
      Equal.trans(Bool,
        SolveFast.fgroups_smaller(Groups.len_words(ws), fg),
        Groups.groups_smaller(ws, FN.FN.fgroups_to_groups(fg)),
        Groups.groups_smaller(ws, Groups.groups_build(g, ws, Nil{})),
        FN.FN.fgroups_smaller_eq(ws, fg,
          FN.FN.fgroups_build_lens_ok(g, ws, Nil{}, {==})),
        Equal.cong(+List<Groups.Group>, Bool, gs => Groups.groups_smaller(ws, gs),
          FN.FN.fgroups_to_groups(fg), Groups.groups_build(g, ws, Nil{}),
          FN.FN.fgroups_build_eq(g, ws, Nil{}))))
  +eus : {Bool.or(Nat.is_lt(m, len), Nat.is_le(2n, k))
          == Groups.groups_smaller(ws, Groups.groups_build(g, ws, Nil{}))
          : Bool} =
    Equal.trans(Bool,
      Bool.or(Nat.is_lt(m, len), Nat.is_le(2n, k)),
      SolveFast.fgroups_smaller(len, fg),
      Groups.groups_smaller(ws, Groups.groups_build(g, ws, Nil{})),
      Equal.sym(Bool, SolveFast.fgroups_smaller(len, fg),
        Bool.or(Nat.is_lt(m, len), Nat.is_le(2n, k)), eus_fg), eus_g)
  FTight.lb2_hist_usable_spec(g, ws, len, cur, floor, m, k, seen2, tbl0, tbl2,
    Nat.add(1n, gen), Bool.or(Nat.is_lt(m, len), Nat.is_le(2n, k)), eus, elen,
    hnd, hwf, hm, hk, hbump, et20)

def FTight.lb2_hist_res_spec(+g: +List<Nat>, +ws: +List<+List<Nat>>,
    +len: Nat, +cur: Nat, +floor: Nat, +gen: Nat, +skip_self: Bool,
    -tbl0: Array<U32>, hr: SolveFast.Hist5Res,
    +hge1: {Nat.is_le(1n, len) == True{} : Bool},
    +elen: {len == Groups.len_words(ws) : Nat},
    +hnd: {FN.FN.no_dup_ref(ws) == True{} : Bool},
    +hs2: FTight.Stage2WS(skip_self, ws, cur),
    +hhr: FH.FH.HistSpec(g, ws, Nil{}, gen,
            SolveFast.lb2_bgt(len, cur, skip_self), skip_self, tbl0, hr)) ->
  FTight.LB2OneSpec(g, ws, cur, floor, tbl0,
    SolveFast.lb2_hist_res(len, cur, floor, gen, hr)):
  match hr:
    case SolveFast.Hist5Pruned{seen2, tbl2}:
      +b0 = SolveFast.lb2_bgt(len, cur, skip_self)
      +hs_out = Arr.Arr.dpair_l(
                  FH.FH.SeenTree(10n, 0, seen2, Nat.add(1n, gen), Nil{}),
                  Arr.Arr.DPair<{tbl2 == tbl0 : Array<U32>},
                    {FH.FH.pruned_reason(g, ws, Nil{}, b0, skip_self)
                     == True{} : Bool}>, hhr)
      +hr1 = Arr.Arr.dpair_r(
               FH.FH.SeenTree(10n, 0, seen2, Nat.add(1n, gen), Nil{}),
               Arr.Arr.DPair<{tbl2 == tbl0 : Array<U32>},
                 {FH.FH.pruned_reason(g, ws, Nil{}, b0, skip_self)
                  == True{} : Bool}>, hhr)
      +et2 = Arr.Arr.dpair_l({tbl2 == tbl0 : Array<U32>},
               {FH.FH.pruned_reason(g, ws, Nil{}, b0, skip_self)
                == True{} : Bool}, hr1)
      +hpr = Arr.Arr.dpair_r({tbl2 == tbl0 : Array<U32>},
               {FH.FH.pruned_reason(g, ws, Nil{}, b0, skip_self)
                == True{} : Bool}, hr1)
      +hall = FTight.lb2_pruned_all_usable(g, ws, len, cur, skip_self, elen,
                hnd, hs2, Tree.member_word(g, ws), {==}, hpr)
      Arr.DPair{hs_out, Arr.DPair{et2, Arr.DPair{{==},
        Arr.DPair{NatProof.Nat.is_le_refl(cur), hall}}}}
    case SolveFast.Hist5Ok{seen2, tbl2, +m, +k, +b}:
      FTight.lb2_hist_ok_dup(g, ws, len, cur, floor, skip_self, seen2, tbl0,
        tbl2, gen, m, k, b, hge1, elen, hnd, hhr, Arr.Arr.dup(Nat, seen2))

# Running one `lb2_hist_res(..., hist5_go(...))` step with linear array dup.
def FTight.lb2_one_step_dup(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +row: U32, +g: +List<Nat>, +ws: +List<SolveFast.CWord>,
    +len: Nat, +cur: Nat, +floor: Nat, +skip_self: Bool,
    -seen: Array<Nat>, -tbl: Array<U32>, +gen: Nat,
    +hge1: {Nat.is_le(1n, len) == True{} : Bool},
    +elen: {len == Groups.len_words(SolveFast.cwords_words(ws)) : Nat},
    +hnd: {FN.FN.no_dup_ref(SolveFast.cwords_words(ws)) == True{} : Bool},
    +hrow: {FT.FT.gentry_ok_b(G, n_root, row, g) == True{} : Bool},
    +hws: {FT.FT.cwords_ok_b(G, C, n_root, ws) == True{} : Bool},
    +hs2: FTight.Stage2WS(skip_self, SolveFast.cwords_words(ws), cur),
    +hs: FH.FH.SeenTree(10n, 0, seen, gen, Nil{}),
    +htbl: FT.FT.TblOk(G, C, n_root, tbl),
    dps: &s1: Array<Nat> -> &s2: Array<Nat> ->
         {s1 == seen : Array<Nat>} & {s2 == s1 : Array<Nat>},
    dpt: &t1: Array<U32> -> &t2: Array<U32> ->
         {t1 == tbl : Array<U32>} & {t2 == t1 : Array<U32>}) ->
  FTight.LB2OneSpec(g, SolveFast.cwords_words(ws), cur, floor, tbl,
    SolveFast.lb2_hist_res(len, cur, floor, gen,
      SolveFast.hist5_go(row, ws, gen, skip_self,
        SolveFast.Hist5Ok{seen, tbl, 0n, 0n,
          SolveFast.lb2_bgt(len, cur, skip_self)}))):
  (s1, dps2) = dps
  (s2, pes) = dps2
  (+es1, +es2) = pes
  (t1, dpt2) = dpt
  (t2, pet) = dpt2
  (+et1, +et2) = pet
  +ws_w = SolveFast.cwords_words(ws)
  +bgt = SolveFast.lb2_bgt(len, cur, skip_self)
  +es2_s : {s2 == seen : Array<Nat>} = Equal.trans(Array<Nat>, s2, s1, seen, es2, es1)
  +et2_t : {t2 == tbl : Array<U32>} = Equal.trans(Array<U32>, t2, t1, tbl, et2, et1)
  +hs_s2 = FH.FH.seen_tree_transport(10n, 0, seen, s2, gen, Nil{},
             Equal.sym(Array<Nat>, s2, seen, es2_s), hs)
  +ht_t2 = FT.FT.tbl_ok_transport(G, C, n_root, tbl, t2,
             Equal.sym(Array<U32>, t2, tbl, et2_t), htbl)
  +hhr2 = FH.FH.hist5_go_spec(ws, G, C, n_root, row, g, Nil{}, s2, t2, gen,
            0n, 0n, bgt, bgt, skip_self, ht_t2, hrow, hws, {==}, {==}, {==},
            {==}, hs_s2)
  +hhr_t0 = FH.FH.hist_spec_transport_tbl(g, ws_w, Nil{}, gen, bgt, skip_self,
              t2, tbl,
              SolveFast.hist5_go(row, ws, gen, skip_self,
                SolveFast.Hist5Ok{s2, t2, 0n, 0n, bgt}), et2_t, hhr2)
  +eq_12 : {SolveFast.hist5_go(row, ws, gen, skip_self,
              SolveFast.Hist5Ok{s2, t2, 0n, 0n, bgt})
            == SolveFast.hist5_go(row, ws, gen, skip_self,
                 SolveFast.Hist5Ok{s1, t1, 0n, 0n, bgt})
            : SolveFast.Hist5Res} =
    Equal.trans(SolveFast.Hist5Res,
      SolveFast.hist5_go(row, ws, gen, skip_self,
        SolveFast.Hist5Ok{s2, t2, 0n, 0n, bgt}),
      SolveFast.hist5_go(row, ws, gen, skip_self,
        SolveFast.Hist5Ok{s1, t2, 0n, 0n, bgt}),
      SolveFast.hist5_go(row, ws, gen, skip_self,
        SolveFast.Hist5Ok{s1, t1, 0n, 0n, bgt}),
      Equal.cong(Array<Nat>, SolveFast.Hist5Res,
        x => SolveFast.hist5_go(row, ws, gen, skip_self,
               SolveFast.Hist5Ok{x, t2, 0n, 0n, bgt}), s2, s1, es2),
      Equal.cong(Array<U32>, SolveFast.Hist5Res,
        y => SolveFast.hist5_go(row, ws, gen, skip_self,
               SolveFast.Hist5Ok{s1, y, 0n, 0n, bgt}), t2, t1, et2))
  +hhr1 = FH.FH.hist_spec_transport(g, ws_w, Nil{}, gen, bgt, skip_self, tbl,
            SolveFast.hist5_go(row, ws, gen, skip_self,
              SolveFast.Hist5Ok{s2, t2, 0n, 0n, bgt}),
            SolveFast.hist5_go(row, ws, gen, skip_self,
              SolveFast.Hist5Ok{s1, t1, 0n, 0n, bgt}), eq_12, hhr_t0)
  %es1 : FTight.LB2OneSpec(g, ws_w, cur, floor, tbl,
           SolveFast.lb2_hist_res(len, cur, floor, gen,
             SolveFast.hist5_go(row, ws, gen, skip_self,
               SolveFast.Hist5Ok{_, tbl, 0n, 0n, bgt})))
  %et1 : FTight.LB2OneSpec(g, ws_w, cur, floor, tbl,
           SolveFast.lb2_hist_res(len, cur, floor, gen,
             SolveFast.hist5_go(row, ws, gen, skip_self,
               SolveFast.Hist5Ok{s1, _, 0n, 0n, bgt})))
  FTight.lb2_hist_res_spec(g, ws_w, len, cur, floor, gen, skip_self, tbl,
    SolveFast.hist5_go(row, ws, gen, skip_self,
      SolveFast.Hist5Ok{s1, t1, 0n, 0n, bgt}),
    hge1, elen, hnd, hs2, hhr1)

def FTight.lb2_spec_cons(+g: +List<Nat>, +gs_rest: +List<+List<Nat>>,
    +ws: +List<+List<Nat>>, +cur: Nat, +cur2: Nat, -tbl0: Array<U32>,
    lr: SolveFast.LB2Res,
    +hle_c: {Nat.is_le(cur2, cur) == True{} : Bool},
    +hg_ok: {LB2.LB2.all_usable_ge(g <> Nil{}, ws, cur2) == True{} : Bool},
    +hrec: FTight.LB2Spec(gs_rest, ws, cur2, tbl0, lr)) ->
  FTight.LB2Spec(g <> gs_rest, ws, cur, tbl0, lr):
  match lr:
    case SolveFast.LB2Res{+new_clb, seen3, tbl3, +gen3, +hit3}:
      +hs3 = Arr.Arr.dpair_l(FH.FH.SeenTree(10n, 0, seen3, gen3, Nil{}),
               Arr.Arr.DPair<{tbl3 == tbl0 : Array<U32>},
                 Arr.Arr.DPair<{Nat.is_le(new_clb, cur2) == True{} : Bool},
                   {LB2.LB2.all_usable_ge(gs_rest, ws, new_clb)
                    == True{} : Bool}>>, hrec)
      +r1 = Arr.Arr.dpair_r(FH.FH.SeenTree(10n, 0, seen3, gen3, Nil{}),
              Arr.Arr.DPair<{tbl3 == tbl0 : Array<U32>},
                Arr.Arr.DPair<{Nat.is_le(new_clb, cur2) == True{} : Bool},
                  {LB2.LB2.all_usable_ge(gs_rest, ws, new_clb)
                   == True{} : Bool}>>, hrec)
      +et3 = Arr.Arr.dpair_l({tbl3 == tbl0 : Array<U32>},
               Arr.Arr.DPair<{Nat.is_le(new_clb, cur2) == True{} : Bool},
                 {LB2.LB2.all_usable_ge(gs_rest, ws, new_clb)
                  == True{} : Bool}>, r1)
      +r2 = Arr.Arr.dpair_r({tbl3 == tbl0 : Array<U32>},
              Arr.Arr.DPair<{Nat.is_le(new_clb, cur2) == True{} : Bool},
                {LB2.LB2.all_usable_ge(gs_rest, ws, new_clb)
                 == True{} : Bool}>, r1)
      +hle_nc = Arr.Arr.dpair_l({Nat.is_le(new_clb, cur2) == True{} : Bool},
                  {LB2.LB2.all_usable_ge(gs_rest, ws, new_clb)
                   == True{} : Bool}, r2)
      +hrest = Arr.Arr.dpair_r({Nat.is_le(new_clb, cur2) == True{} : Bool},
                 {LB2.LB2.all_usable_ge(gs_rest, ws, new_clb)
                  == True{} : Bool}, r2)
      +hg_new = LB2.LB2.all_usable_ge_mono(g <> Nil{}, ws, cur2, new_clb,
                  hle_nc, hg_ok)
      +hall = LB2.LB2.all_usable_ge_append(g <> Nil{}, gs_rest, ws, new_clb,
                hg_new, hrest)
      Arr.DPair{hs3, Arr.DPair{et3, Arr.DPair{
        NatProof.Nat.is_le_trans(new_clb, cur2, cur, hle_nc, hle_c), hall}}}

def FTight.scan_lb2_stage2_cont_dup(+g: +List<Nat>, +rest: +List<FT.FT.RowWord>,
    +G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n_root: Nat,
    +ws: +List<SolveFast.CWord>, +len: Nat, +cur: Nat, +cur2: Nat,
    -seen2: Array<Nat>, -tbl0: Array<U32>, -tbl2: Array<U32>,
    +gen2: Nat, +hit2: Bool,
    +et2: {tbl2 == tbl0 : Array<U32>},
    +ehit2: {hit2 == Nat.is_le(cur2, Nat.add(len, len)) : Bool},
    +hle_c: {Nat.is_le(cur2, cur) == True{} : Bool},
    +hg_ok: {LB2.LB2.all_usable_ge(g <> Nil{}, SolveFast.cwords_words(ws), cur2)
             == True{} : Bool},
    +hws_all2: {LB2.LB2.all_usable_ge(SolveFast.cwords_words(ws),
                  SolveFast.cwords_words(ws), cur2) == True{} : Bool},
    +hs2: FH.FH.SeenTree(10n, 0, seen2, gen2, Nil{}),
    +htbl2: FT.FT.TblOk(G, C, n_root, tbl2),
    dps: &s1: Array<Nat> -> &s2: Array<Nat> ->
         {s1 == seen2 : Array<Nat>} & {s2 == s1 : Array<Nat>},
    dpt: &t1: Array<U32> -> &t2: Array<U32> ->
         {t1 == tbl2 : Array<U32>} & {t2 == t1 : Array<U32>},
    rec: @cur3: Nat -> @seen3: Array<Nat> -> @tbl3: Array<U32> ->
         @gen3: Nat -> @hit3: Bool ->
         {hit3 == Nat.is_le(cur3, Nat.add(len, len)) : Bool} ->
         {LB2.LB2.all_usable_ge(SolveFast.cwords_words(ws),
            SolveFast.cwords_words(ws), cur3) == True{} : Bool} ->
         FH.FH.SeenTree(10n, 0, seen3, gen3, Nil{}) ->
         FT.FT.TblOk(G, C, n_root, tbl3) ->
         FTight.LB2Spec(FT.FT.rws_words(rest), SolveFast.cwords_words(ws),
           cur3, tbl3,
           SolveFast.scan_lb2_step(FT.FT.glist_of_rws(rest, SolveFast.GEnd{}),
             ws, len, Nat.add(len, len), True{},
             SolveFast.LB2Res{cur3, seen3, tbl3, gen3, hit3}))) ->
  FTight.LB2Spec(g <> FT.FT.rws_words(rest), SolveFast.cwords_words(ws),
    cur, tbl0,
    SolveFast.scan_lb2_step(FT.FT.glist_of_rws(rest, SolveFast.GEnd{}),
      ws, len, Nat.add(len, len), True{},
      SolveFast.LB2Res{cur2, seen2, tbl2, gen2, hit2})):
  (s1, dps2) = dps
  (s2, pes) = dps2
  (+es1, +es2) = pes
  (t1, dpt2) = dpt
  (t2, pet) = dpt2
  (+et1, +et2a) = pet
  +ws_w = SolveFast.cwords_words(ws)
  +fl2 = Nat.add(len, len)
  +grest = FT.FT.glist_of_rws(rest, SolveFast.GEnd{})
  +es2_s : {s2 == seen2 : Array<Nat>} = Equal.trans(Array<Nat>, s2, s1, seen2, es2, es1)
  +et2_t : {t2 == tbl2 : Array<U32>} = Equal.trans(Array<U32>, t2, t1, tbl2, et2a, et1)
  +et2_t0 : {t2 == tbl0 : Array<U32>} = Equal.trans(Array<U32>, t2, tbl2, tbl0, et2_t, et2)
  +hs_s2 = FH.FH.seen_tree_transport(10n, 0, seen2, s2, gen2, Nil{},
             Equal.sym(Array<Nat>, s2, seen2, es2_s), hs2)
  +ht_t2 = FT.FT.tbl_ok_transport(G, C, n_root, tbl2, t2,
             Equal.sym(Array<U32>, t2, tbl2, et2_t), htbl2)
  +hrec2 = rec(cur2, s2, t2, gen2, hit2, ehit2, hws_all2, hs_s2, ht_t2)
  +hrec_t0 = FTight.lb2_spec_transport_tbl(FT.FT.rws_words(rest), ws_w, cur2,
               t2, tbl0,
               SolveFast.scan_lb2_step(grest, ws, len, fl2, True{},
                 SolveFast.LB2Res{cur2, s2, t2, gen2, hit2}), et2_t0, hrec2)
  +eq_12 : {SolveFast.scan_lb2_step(grest, ws, len, fl2, True{},
              SolveFast.LB2Res{cur2, s2, t2, gen2, hit2})
            == SolveFast.scan_lb2_step(grest, ws, len, fl2, True{},
                 SolveFast.LB2Res{cur2, s1, t1, gen2, hit2})
            : SolveFast.LB2Res} =
    Equal.trans(SolveFast.LB2Res,
      SolveFast.scan_lb2_step(grest, ws, len, fl2, True{},
        SolveFast.LB2Res{cur2, s2, t2, gen2, hit2}),
      SolveFast.scan_lb2_step(grest, ws, len, fl2, True{},
        SolveFast.LB2Res{cur2, s1, t2, gen2, hit2}),
      SolveFast.scan_lb2_step(grest, ws, len, fl2, True{},
        SolveFast.LB2Res{cur2, s1, t1, gen2, hit2}),
      Equal.cong(Array<Nat>, SolveFast.LB2Res,
        x => SolveFast.scan_lb2_step(grest, ws, len, fl2, True{},
               SolveFast.LB2Res{cur2, x, t2, gen2, hit2}), s2, s1, es2),
      Equal.cong(Array<U32>, SolveFast.LB2Res,
        y => SolveFast.scan_lb2_step(grest, ws, len, fl2, True{},
               SolveFast.LB2Res{cur2, s1, y, gen2, hit2}), t2, t1, et2a))
  +hrec1 = FTight.lb2_spec_transport(FT.FT.rws_words(rest), ws_w, cur2, tbl0,
             SolveFast.scan_lb2_step(grest, ws, len, fl2, True{},
               SolveFast.LB2Res{cur2, s2, t2, gen2, hit2}),
             SolveFast.scan_lb2_step(grest, ws, len, fl2, True{},
               SolveFast.LB2Res{cur2, s1, t1, gen2, hit2}), eq_12, hrec_t0)
  %es1 : FTight.LB2Spec(g <> FT.FT.rws_words(rest), ws_w, cur, tbl0,
           SolveFast.scan_lb2_step(grest, ws, len, fl2, True{},
             SolveFast.LB2Res{cur2, _, tbl2, gen2, hit2}))
  %et1 : FTight.LB2Spec(g <> FT.FT.rws_words(rest), ws_w, cur, tbl0,
           SolveFast.scan_lb2_step(grest, ws, len, fl2, True{},
             SolveFast.LB2Res{cur2, s1, _, gen2, hit2}))
  FTight.lb2_spec_cons(g, FT.FT.rws_words(rest), ws_w, cur, cur2, tbl0,
    SolveFast.scan_lb2_step(grest, ws, len, fl2, True{},
      SolveFast.LB2Res{cur2, s1, t1, gen2, hit2}),
    hle_c, hg_ok, hrec1)

# Stage-2 continuation: unpack `lr1` and combine with recursive call on `rest`.
def FTight.scan_lb2_stage2_cont(+g: +List<Nat>, +rest: +List<FT.FT.RowWord>,
    +G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n_root: Nat,
    +ws: +List<SolveFast.CWord>, +len: Nat, +cur: Nat, -tbl0: Array<U32>,
    lr1: SolveFast.LB2Res,
    +htbl0: FT.FT.TblOk(G, C, n_root, tbl0),
    +hws_all: {LB2.LB2.all_usable_ge(SolveFast.cwords_words(ws),
                 SolveFast.cwords_words(ws), cur) == True{} : Bool},
    +h1: FTight.LB2OneSpec(g, SolveFast.cwords_words(ws), cur,
           Nat.add(len, len), tbl0, lr1),
    rec: @cur2: Nat -> @seen2: Array<Nat> -> @tbl2: Array<U32> ->
         @gen2: Nat -> @hit2: Bool ->
         {hit2 == Nat.is_le(cur2, Nat.add(len, len)) : Bool} ->
         {LB2.LB2.all_usable_ge(SolveFast.cwords_words(ws),
            SolveFast.cwords_words(ws), cur2) == True{} : Bool} ->
         FH.FH.SeenTree(10n, 0, seen2, gen2, Nil{}) ->
         FT.FT.TblOk(G, C, n_root, tbl2) ->
         FTight.LB2Spec(FT.FT.rws_words(rest), SolveFast.cwords_words(ws),
           cur2, tbl2,
           SolveFast.scan_lb2_step(FT.FT.glist_of_rws(rest, SolveFast.GEnd{}),
             ws, len, Nat.add(len, len), True{},
             SolveFast.LB2Res{cur2, seen2, tbl2, gen2, hit2}))) ->
  FTight.LB2Spec(g <> FT.FT.rws_words(rest), SolveFast.cwords_words(ws),
    cur, tbl0,
    SolveFast.scan_lb2_step(FT.FT.glist_of_rws(rest, SolveFast.GEnd{}),
      ws, len, Nat.add(len, len), True{}, lr1)):
  match lr1:
    case SolveFast.LB2Res{+cur2, seen2, tbl2, +gen2, +hit2}:
      +ws_w = SolveFast.cwords_words(ws)
      +fl2 = Nat.add(len, len)
      +hs2 = Arr.Arr.dpair_l(FH.FH.SeenTree(10n, 0, seen2, gen2, Nil{}),
               Arr.Arr.DPair<{tbl2 == tbl0 : Array<U32>},
                 Arr.Arr.DPair<{hit2 == Nat.is_le(cur2, fl2) : Bool},
                   Arr.Arr.DPair<{Nat.is_le(cur2, cur) == True{} : Bool},
                     {LB2.LB2.all_usable_ge(g <> Nil{}, ws_w, cur2)
                      == True{} : Bool}>>>, h1)
      +r1 = Arr.Arr.dpair_r(FH.FH.SeenTree(10n, 0, seen2, gen2, Nil{}),
              Arr.Arr.DPair<{tbl2 == tbl0 : Array<U32>},
                Arr.Arr.DPair<{hit2 == Nat.is_le(cur2, fl2) : Bool},
                  Arr.Arr.DPair<{Nat.is_le(cur2, cur) == True{} : Bool},
                    {LB2.LB2.all_usable_ge(g <> Nil{}, ws_w, cur2)
                     == True{} : Bool}>>>, h1)
      +et2 = Arr.Arr.dpair_l({tbl2 == tbl0 : Array<U32>},
               Arr.Arr.DPair<{hit2 == Nat.is_le(cur2, fl2) : Bool},
                 Arr.Arr.DPair<{Nat.is_le(cur2, cur) == True{} : Bool},
                   {LB2.LB2.all_usable_ge(g <> Nil{}, ws_w, cur2)
                    == True{} : Bool}>>, r1)
      +r2 = Arr.Arr.dpair_r({tbl2 == tbl0 : Array<U32>},
              Arr.Arr.DPair<{hit2 == Nat.is_le(cur2, fl2) : Bool},
                Arr.Arr.DPair<{Nat.is_le(cur2, cur) == True{} : Bool},
                  {LB2.LB2.all_usable_ge(g <> Nil{}, ws_w, cur2)
                   == True{} : Bool}>>, r1)
      +ehit2 = Arr.Arr.dpair_l({hit2 == Nat.is_le(cur2, fl2) : Bool},
                 Arr.Arr.DPair<{Nat.is_le(cur2, cur) == True{} : Bool},
                   {LB2.LB2.all_usable_ge(g <> Nil{}, ws_w, cur2)
                    == True{} : Bool}>, r2)
      +r3 = Arr.Arr.dpair_r({hit2 == Nat.is_le(cur2, fl2) : Bool},
              Arr.Arr.DPair<{Nat.is_le(cur2, cur) == True{} : Bool},
                {LB2.LB2.all_usable_ge(g <> Nil{}, ws_w, cur2)
                 == True{} : Bool}>, r2)
      +hle_c = Arr.Arr.dpair_l({Nat.is_le(cur2, cur) == True{} : Bool},
                 {LB2.LB2.all_usable_ge(g <> Nil{}, ws_w, cur2)
                  == True{} : Bool}, r3)
      +hg_ok = Arr.Arr.dpair_r({Nat.is_le(cur2, cur) == True{} : Bool},
                 {LB2.LB2.all_usable_ge(g <> Nil{}, ws_w, cur2)
                  == True{} : Bool}, r3)
      +htbl2 = FT.FT.tbl_ok_transport(G, C, n_root, tbl0, tbl2,
                 Equal.sym(Array<U32>, tbl2, tbl0, et2), htbl0)
      +hws_all2 = LB2.LB2.all_usable_ge_mono(ws_w, ws_w, cur, cur2, hle_c,
                    hws_all)
      FTight.scan_lb2_stage2_cont_dup(g, rest, G, C, n_root, ws, len, cur,
        cur2, seen2, tbl0, tbl2, gen2, hit2, et2, ehit2, hle_c, hg_ok,
        hws_all2, hs2, htbl2, Arr.Arr.dup(Nat, seen2), Arr.Arr.dup(U32, tbl2),
        rec)

# Duplication wrapper for stage 2 step.
def FTight.scan_lb2_stage2_dup(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +row: U32, +g: +List<Nat>, +rest: +List<FT.FT.RowWord>,
    +ws: +List<SolveFast.CWord>, +len: Nat, +cur: Nat,
    -seen: Array<Nat>, -tbl: Array<U32>, +gen: Nat,
    +hge1: {Nat.is_le(1n, len) == True{} : Bool},
    +elen: {len == Groups.len_words(SolveFast.cwords_words(ws)) : Nat},
    +hnd: {FN.FN.no_dup_ref(SolveFast.cwords_words(ws)) == True{} : Bool},
    +hrow: {FT.FT.gentry_ok_b(G, n_root, row, g) == True{} : Bool},
    +hws: {FT.FT.cwords_ok_b(G, C, n_root, ws) == True{} : Bool},
    +hws_all: {LB2.LB2.all_usable_ge(SolveFast.cwords_words(ws),
                 SolveFast.cwords_words(ws), cur) == True{} : Bool},
    +hs: FH.FH.SeenTree(10n, 0, seen, gen, Nil{}),
    +htbl: FT.FT.TblOk(G, C, n_root, tbl),
    dps: &s1: Array<Nat> -> &s2: Array<Nat> ->
         {s1 == seen : Array<Nat>} & {s2 == s1 : Array<Nat>},
    dpt: &t1: Array<U32> -> &t2: Array<U32> ->
         {t1 == tbl : Array<U32>} & {t2 == t1 : Array<U32>},
    rec: @cur2: Nat -> @seen2: Array<Nat> -> @tbl2: Array<U32> ->
         @gen2: Nat -> @hit2: Bool ->
         {hit2 == Nat.is_le(cur2, Nat.add(len, len)) : Bool} ->
         {LB2.LB2.all_usable_ge(SolveFast.cwords_words(ws),
            SolveFast.cwords_words(ws), cur2) == True{} : Bool} ->
         FH.FH.SeenTree(10n, 0, seen2, gen2, Nil{}) ->
         FT.FT.TblOk(G, C, n_root, tbl2) ->
         FTight.LB2Spec(FT.FT.rws_words(rest), SolveFast.cwords_words(ws),
           cur2, tbl2,
           SolveFast.scan_lb2_step(FT.FT.glist_of_rws(rest, SolveFast.GEnd{}),
             ws, len, Nat.add(len, len), True{},
             SolveFast.LB2Res{cur2, seen2, tbl2, gen2, hit2}))) ->
  FTight.LB2Spec(g <> FT.FT.rws_words(rest), SolveFast.cwords_words(ws),
    cur, tbl,
    SolveFast.scan_lb2_step(FT.FT.glist_of_rws(rest, SolveFast.GEnd{}),
      ws, len, Nat.add(len, len), True{},
      SolveFast.lb2_hist_res(len, cur, Nat.add(len, len), gen,
        SolveFast.hist5_go(row, ws, gen, True{},
          SolveFast.Hist5Ok{seen, tbl, 0n, 0n,
            SolveFast.lb2_bgt(len, cur, True{})})))) :
  (s1, dps2) = dps
  (s2, pes) = dps2
  (+es1, +es2) = pes
  (t1, dpt2) = dpt
  (t2, pet) = dpt2
  (+et1, +et2) = pet
  +ws_w = SolveFast.cwords_words(ws)
  +fl2 = Nat.add(len, len)
  +bgt = SolveFast.lb2_bgt(len, cur, True{})
  +es2_s : {s2 == seen : Array<Nat>} = Equal.trans(Array<Nat>, s2, s1, seen, es2, es1)
  +et2_t : {t2 == tbl : Array<U32>} = Equal.trans(Array<U32>, t2, t1, tbl, et2, et1)
  +hs_s2 = FH.FH.seen_tree_transport(10n, 0, seen, s2, gen, Nil{},
             Equal.sym(Array<Nat>, s2, seen, es2_s), hs)
  +ht_t2 = FT.FT.tbl_ok_transport(G, C, n_root, tbl, t2,
             Equal.sym(Array<U32>, t2, tbl, et2_t), htbl)
  +h1_s2 = FTight.lb2_one_step_dup(G, C, n_root, row, g, ws, len, cur, fl2,
             True{}, s2, t2, gen, hge1, elen, hnd, hrow, hws, hws_all, hs_s2,
             ht_t2, Arr.Arr.dup(Nat, s2), Arr.Arr.dup(U32, t2))
  +h1_t0 : FTight.LB2OneSpec(g, ws_w, cur, fl2, tbl,
             SolveFast.lb2_hist_res(len, cur, fl2, gen,
               SolveFast.hist5_go(row, ws, gen, True{},
                 SolveFast.Hist5Ok{s2, t2, 0n, 0n, bgt}))) =
    %et2_t : FTight.LB2OneSpec(g, ws_w, cur, fl2, _,
               SolveFast.lb2_hist_res(len, cur, fl2, gen,
                 SolveFast.hist5_go(row, ws, gen, True{},
                   SolveFast.Hist5Ok{s2, t2, 0n, 0n, bgt})))
    h1_s2
  +eq_12 : {SolveFast.lb2_hist_res(len, cur, fl2, gen,
              SolveFast.hist5_go(row, ws, gen, True{},
                SolveFast.Hist5Ok{s2, t2, 0n, 0n, bgt}))
            == SolveFast.lb2_hist_res(len, cur, fl2, gen,
                 SolveFast.hist5_go(row, ws, gen, True{},
                   SolveFast.Hist5Ok{s1, t1, 0n, 0n, bgt}))
            : SolveFast.LB2Res} =
    Equal.trans(SolveFast.LB2Res,
      SolveFast.lb2_hist_res(len, cur, fl2, gen,
        SolveFast.hist5_go(row, ws, gen, True{},
          SolveFast.Hist5Ok{s2, t2, 0n, 0n, bgt})),
      SolveFast.lb2_hist_res(len, cur, fl2, gen,
        SolveFast.hist5_go(row, ws, gen, True{},
          SolveFast.Hist5Ok{s1, t2, 0n, 0n, bgt})),
      SolveFast.lb2_hist_res(len, cur, fl2, gen,
        SolveFast.hist5_go(row, ws, gen, True{},
          SolveFast.Hist5Ok{s1, t1, 0n, 0n, bgt})),
      Equal.cong(Array<Nat>, SolveFast.LB2Res,
        x => SolveFast.lb2_hist_res(len, cur, fl2, gen,
               SolveFast.hist5_go(row, ws, gen, True{},
                 SolveFast.Hist5Ok{x, t2, 0n, 0n, bgt})), s2, s1, es2),
      Equal.cong(Array<U32>, SolveFast.LB2Res,
        y => SolveFast.lb2_hist_res(len, cur, fl2, gen,
               SolveFast.hist5_go(row, ws, gen, True{},
                 SolveFast.Hist5Ok{s1, y, 0n, 0n, bgt})), t2, t1, et2))
  +h1_s1 = FTight.lb2_one_transport(g, ws_w, cur, fl2, tbl,
             SolveFast.lb2_hist_res(len, cur, fl2, gen,
               SolveFast.hist5_go(row, ws, gen, True{},
                 SolveFast.Hist5Ok{s2, t2, 0n, 0n, bgt})),
             SolveFast.lb2_hist_res(len, cur, fl2, gen,
               SolveFast.hist5_go(row, ws, gen, True{},
                 SolveFast.Hist5Ok{s1, t1, 0n, 0n, bgt})), eq_12, h1_t0)
  %es1 : FTight.LB2Spec(g <> FT.FT.rws_words(rest), ws_w, cur, tbl,
           SolveFast.scan_lb2_step(FT.FT.glist_of_rws(rest, SolveFast.GEnd{}),
             ws, len, fl2, True{},
             SolveFast.lb2_hist_res(len, cur, fl2, gen,
               SolveFast.hist5_go(row, ws, gen, True{},
                 SolveFast.Hist5Ok{_, tbl, 0n, 0n, bgt}))))
  %et1 : FTight.LB2Spec(g <> FT.FT.rws_words(rest), ws_w, cur, tbl,
           SolveFast.scan_lb2_step(FT.FT.glist_of_rws(rest, SolveFast.GEnd{}),
             ws, len, fl2, True{},
             SolveFast.lb2_hist_res(len, cur, fl2, gen,
               SolveFast.hist5_go(row, ws, gen, True{},
                 SolveFast.Hist5Ok{s1, _, 0n, 0n, bgt}))))
  FTight.scan_lb2_stage2_cont(g, rest, G, C, n_root, ws, len, cur, tbl,
    SolveFast.lb2_hist_res(len, cur, fl2, gen,
      SolveFast.hist5_go(row, ws, gen, True{},
        SolveFast.Hist5Ok{s1, t1, 0n, 0n, bgt})),
    htbl, hws_all, h1_s1, rec)

# Stage 2 of `scan_lb2_step`: scanning `rws` (full guess list `G`) with
# `floor = 2*len` and `skip_self = True{}` once `ws` has been covered.
def FTight.scan_lb2_stage2(+rws: +List<FT.FT.RowWord>, +G: +List<+List<Nat>>,
    +C: +List<+List<Nat>>, +n_root: Nat, +ws: +List<SolveFast.CWord>,
    +len: Nat, +cur: Nat, seen: Array<Nat>, tbl: Array<U32>, +gen: Nat,
    hit: Bool,
    +ehit: {hit == Nat.is_le(cur, Nat.add(len, len)) : Bool},
    +hge1: {Nat.is_le(1n, len) == True{} : Bool},
    +elen: {len == Groups.len_words(SolveFast.cwords_words(ws)) : Nat},
    +hnd: {FN.FN.no_dup_ref(SolveFast.cwords_words(ws)) == True{} : Bool},
    +hws: {FT.FT.cwords_ok_b(G, C, n_root, ws) == True{} : Bool},
    +hrws: {FT.FT.rws_ok_b(G, n_root, rws) == True{} : Bool},
    +hws_all: {LB2.LB2.all_usable_ge(SolveFast.cwords_words(ws),
                 SolveFast.cwords_words(ws), cur) == True{} : Bool},
    +hs: FH.FH.SeenTree(10n, 0, seen, gen, Nil{}),
    +htbl: FT.FT.TblOk(G, C, n_root, tbl)) ->
  FTight.LB2Spec(FT.FT.rws_words(rws), SolveFast.cwords_words(ws), cur, tbl,
    SolveFast.scan_lb2_step(FT.FT.glist_of_rws(rws, SolveFast.GEnd{}),
      ws, len, Nat.add(len, len), True{},
      SolveFast.LB2Res{cur, seen, tbl, gen, hit})):
  match rws:
    case Nil{}:
      Arr.DPair{hs, Arr.DPair{{==},
        Arr.DPair{NatProof.Nat.is_le_refl(cur), {==}}}}
    case Con{rw, +rest}:
      match rw:
        case FT.RowWord{+row, +g}:
          match hit:
            case True{}:
              +ws_w = SolveFast.cwords_words(ws)
              +hle1 : {Nat.is_le(cur, Nat.add(len, len)) == True{} : Bool} =
                Equal.sym(Bool, True{}, Nat.is_le(cur, Nat.add(len, len)), ehit)
              +hle2n : {Nat.is_le(cur, Nat.add(Groups.len_words(ws_w),
                          Groups.len_words(ws_w))) == True{} : Bool} =
                NatProof.Nat.is_le_eq_r(cur, Nat.add(len, len),
                  Nat.add(Groups.len_words(ws_w), Groups.len_words(ws_w)),
                  Equal.cong(Nat, Nat, x => Nat.add(x, x), len,
                    Groups.len_words(ws_w), elen), hle1)
              +hall = LB2.LB2.all_usable_ge_of_le_2n(g <> FT.FT.rws_words(rest),
                        ws_w, cur, hnd, hws_all, hle2n)
              Arr.DPair{hs, Arr.DPair{{==},
                Arr.DPair{NatProof.Nat.is_le_refl(cur), hall}}}
            case False{}:
              +hrow = Logic.Proof.and_true_l(FT.FT.gentry_ok_b(G, n_root, row, g),
                        FT.FT.rws_ok_b(G, n_root, rest), hrws)
              +hrest = Logic.Proof.and_true_r(FT.FT.gentry_ok_b(G, n_root, row, g),
                         FT.FT.rws_ok_b(G, n_root, rest), hrws)
              FTight.scan_lb2_stage2_dup(G, C, n_root, row, g, rest, ws, len,
                cur, seen, tbl, gen, hge1, elen, hnd, hrow, hws, hws_all, hs,
                htbl, Arr.Arr.dup(Nat, seen), Arr.Arr.dup(U32, tbl),
                +cur2 => seen2 => tbl2 => +gen2 => hit2 => +ehit2 =>
                +hws_all2 => +hs2 => +htbl2 =>
                  FTight.scan_lb2_stage2(rest, G, C, n_root, ws, len, cur2,
                    seen2, tbl2, gen2, hit2, ehit2, hge1, elen, hnd, hws,
                    hrest, hws_all2, hs2, htbl2))

def FTight.lb2_spec_weaken_cur(+gs_cov: +List<+List<Nat>>,
    +ws: +List<+List<Nat>>, +cur: Nat, +cur2: Nat, -tbl0: Array<U32>,
    lr: SolveFast.LB2Res,
    +hle_c: {Nat.is_le(cur2, cur) == True{} : Bool},
    +hrec: FTight.LB2Spec(gs_cov, ws, cur2, tbl0, lr)) ->
  FTight.LB2Spec(gs_cov, ws, cur, tbl0, lr):
  match lr:
    case SolveFast.LB2Res{+new_clb, seen3, tbl3, +gen3, +hit3}:
      +hs3 = Arr.Arr.dpair_l(FH.FH.SeenTree(10n, 0, seen3, gen3, Nil{}),
               Arr.Arr.DPair<{tbl3 == tbl0 : Array<U32>},
                 Arr.Arr.DPair<{Nat.is_le(new_clb, cur2) == True{} : Bool},
                   {LB2.LB2.all_usable_ge(gs_cov, ws, new_clb)
                    == True{} : Bool}>>, hrec)
      +r1 = Arr.Arr.dpair_r(FH.FH.SeenTree(10n, 0, seen3, gen3, Nil{}),
              Arr.Arr.DPair<{tbl3 == tbl0 : Array<U32>},
                Arr.Arr.DPair<{Nat.is_le(new_clb, cur2) == True{} : Bool},
                  {LB2.LB2.all_usable_ge(gs_cov, ws, new_clb)
                   == True{} : Bool}>>, hrec)
      +et3 = Arr.Arr.dpair_l({tbl3 == tbl0 : Array<U32>},
               Arr.Arr.DPair<{Nat.is_le(new_clb, cur2) == True{} : Bool},
                 {LB2.LB2.all_usable_ge(gs_cov, ws, new_clb)
                  == True{} : Bool}>, r1)
      +r2 = Arr.Arr.dpair_r({tbl3 == tbl0 : Array<U32>},
              Arr.Arr.DPair<{Nat.is_le(new_clb, cur2) == True{} : Bool},
                {LB2.LB2.all_usable_ge(gs_cov, ws, new_clb)
                 == True{} : Bool}>, r1)
      +hle_nc = Arr.Arr.dpair_l({Nat.is_le(new_clb, cur2) == True{} : Bool},
                  {LB2.LB2.all_usable_ge(gs_cov, ws, new_clb)
                   == True{} : Bool}, r2)
      +hall = Arr.Arr.dpair_r({Nat.is_le(new_clb, cur2) == True{} : Bool},
                {LB2.LB2.all_usable_ge(gs_cov, ws, new_clb)
                 == True{} : Bool}, r2)
      Arr.DPair{hs3, Arr.DPair{et3, Arr.DPair{
        NatProof.Nat.is_le_trans(new_clb, cur2, cur, hle_nc, hle_c), hall}}}

def FTight.scan_lb2_stage1_cont_dup(+g: +List<Nat>, +rest: +List<FT.FT.RowWord>,
    +rwsG: +List<FT.FT.RowWord>, +G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +ws: +List<SolveFast.CWord>, +ws_pre: +List<+List<Nat>>,
    +len: Nat, +cur: Nat, +cur2: Nat, -seen2: Array<Nat>, -tbl0: Array<U32>,
    -tbl2: Array<U32>, +gen2: Nat, +hit2: Bool,
    +et2: {tbl2 == tbl0 : Array<U32>},
    +ehit2: {hit2 == Nat.is_le(cur2, SolveFast.init_floor(len)) : Bool},
    +hle_c: {Nat.is_le(cur2, cur) == True{} : Bool},
    +hpre2: {LB2.LB2.all_usable_ge(
               List.append(&2, +List<Nat>, ws_pre, g <> Nil{}),
               SolveFast.cwords_words(ws), cur2) == True{} : Bool},
    +hs2: FH.FH.SeenTree(10n, 0, seen2, gen2, Nil{}),
    +htbl2: FT.FT.TblOk(G, C, n_root, tbl2),
    dps: &s1: Array<Nat> -> &s2: Array<Nat> ->
         {s1 == seen2 : Array<Nat>} & {s2 == s1 : Array<Nat>},
    dpt: &t1: Array<U32> -> &t2: Array<U32> ->
         {t1 == tbl2 : Array<U32>} & {t2 == t1 : Array<U32>},
    rec: @cur3: Nat -> @seen3: Array<Nat> -> @tbl3: Array<U32> ->
         @gen3: Nat -> @hit3: Bool ->
         {hit3 == Nat.is_le(cur3, SolveFast.init_floor(len)) : Bool} ->
         {LB2.LB2.all_usable_ge(
            List.append(&2, +List<Nat>, ws_pre, g <> Nil{}),
            SolveFast.cwords_words(ws), cur3) == True{} : Bool} ->
         FH.FH.SeenTree(10n, 0, seen3, gen3, Nil{}) ->
         FT.FT.TblOk(G, C, n_root, tbl3) ->
         FTight.LB2Spec(G, SolveFast.cwords_words(ws), cur3, tbl3,
           SolveFast.scan_lb2_step(
             FT.FT.glist_of_rws(rest,
               SolveFast.GThen{FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{})}),
             ws, len, SolveFast.init_floor(len), False{},
             SolveFast.LB2Res{cur3, seen3, tbl3, gen3, hit3}))) ->
  FTight.LB2Spec(G, SolveFast.cwords_words(ws), cur, tbl0,
    SolveFast.scan_lb2_step(
      FT.FT.glist_of_rws(rest,
        SolveFast.GThen{FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{})}),
      ws, len, SolveFast.init_floor(len), False{},
      SolveFast.LB2Res{cur2, seen2, tbl2, gen2, hit2})):
  (s1, dps2) = dps
  (s2, pes) = dps2
  (+es1, +es2) = pes
  (t1, dpt2) = dpt
  (t2, pet) = dpt2
  (+et1, +et2a) = pet
  +ws_w = SolveFast.cwords_words(ws)
  +fl = SolveFast.init_floor(len)
  +grest = FT.FT.glist_of_rws(rest,
             SolveFast.GThen{FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{})})
  +es2_s : {s2 == seen2 : Array<Nat>} = Equal.trans(Array<Nat>, s2, s1, seen2, es2, es1)
  +et2_t : {t2 == tbl2 : Array<U32>} = Equal.trans(Array<U32>, t2, t1, tbl2, et2a, et1)
  +et2_t0 : {t2 == tbl0 : Array<U32>} = Equal.trans(Array<U32>, t2, tbl2, tbl0, et2_t, et2)
  +hs_s2 = FH.FH.seen_tree_transport(10n, 0, seen2, s2, gen2, Nil{},
             Equal.sym(Array<Nat>, s2, seen2, es2_s), hs2)
  +ht_t2 = FT.FT.tbl_ok_transport(G, C, n_root, tbl2, t2,
             Equal.sym(Array<U32>, t2, tbl2, et2_t), htbl2)
  +hrec2 = rec(cur2, s2, t2, gen2, hit2, ehit2, hpre2, hs_s2, ht_t2)
  +hrec_t0 = FTight.lb2_spec_transport_tbl(G, ws_w, cur2, t2, tbl0,
               SolveFast.scan_lb2_step(grest, ws, len, fl, False{},
                 SolveFast.LB2Res{cur2, s2, t2, gen2, hit2}), et2_t0, hrec2)
  +eq_12 : {SolveFast.scan_lb2_step(grest, ws, len, fl, False{},
              SolveFast.LB2Res{cur2, s2, t2, gen2, hit2})
            == SolveFast.scan_lb2_step(grest, ws, len, fl, False{},
                 SolveFast.LB2Res{cur2, s1, t1, gen2, hit2})
            : SolveFast.LB2Res} =
    Equal.trans(SolveFast.LB2Res,
      SolveFast.scan_lb2_step(grest, ws, len, fl, False{},
        SolveFast.LB2Res{cur2, s2, t2, gen2, hit2}),
      SolveFast.scan_lb2_step(grest, ws, len, fl, False{},
        SolveFast.LB2Res{cur2, s1, t2, gen2, hit2}),
      SolveFast.scan_lb2_step(grest, ws, len, fl, False{},
        SolveFast.LB2Res{cur2, s1, t1, gen2, hit2}),
      Equal.cong(Array<Nat>, SolveFast.LB2Res,
        x => SolveFast.scan_lb2_step(grest, ws, len, fl, False{},
               SolveFast.LB2Res{cur2, x, t2, gen2, hit2}), s2, s1, es2),
      Equal.cong(Array<U32>, SolveFast.LB2Res,
        y => SolveFast.scan_lb2_step(grest, ws, len, fl, False{},
               SolveFast.LB2Res{cur2, s1, y, gen2, hit2}), t2, t1, et2a))
  +hrec1 = FTight.lb2_spec_transport(G, ws_w, cur2, tbl0,
             SolveFast.scan_lb2_step(grest, ws, len, fl, False{},
               SolveFast.LB2Res{cur2, s2, t2, gen2, hit2}),
             SolveFast.scan_lb2_step(grest, ws, len, fl, False{},
               SolveFast.LB2Res{cur2, s1, t1, gen2, hit2}), eq_12, hrec_t0)
  %es1 : FTight.LB2Spec(G, ws_w, cur, tbl0,
           SolveFast.scan_lb2_step(grest, ws, len, fl, False{},
             SolveFast.LB2Res{cur2, _, tbl2, gen2, hit2}))
  %et1 : FTight.LB2Spec(G, ws_w, cur, tbl0,
           SolveFast.scan_lb2_step(grest, ws, len, fl, False{},
             SolveFast.LB2Res{cur2, s1, _, gen2, hit2}))
  FTight.lb2_spec_weaken_cur(G, ws_w, cur, cur2, tbl0,
    SolveFast.scan_lb2_step(grest, ws, len, fl, False{},
      SolveFast.LB2Res{cur2, s1, t1, gen2, hit2}),
    hle_c, hrec1)

def FTight.scan_lb2_stage1_cont(+g: +List<Nat>, +rest: +List<FT.FT.RowWord>,
    +rwsG: +List<FT.FT.RowWord>, +G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +ws: +List<SolveFast.CWord>, +ws_pre: +List<+List<Nat>>,
    +len: Nat, +cur: Nat, -tbl0: Array<U32>, lr1: SolveFast.LB2Res,
    +htbl0: FT.FT.TblOk(G, C, n_root, tbl0),
    +hpre: {LB2.LB2.all_usable_ge(ws_pre, SolveFast.cwords_words(ws), cur)
            == True{} : Bool},
    +h1: FTight.LB2OneSpec(g, SolveFast.cwords_words(ws), cur,
           SolveFast.init_floor(len), tbl0, lr1),
    rec: @cur2: Nat -> @seen2: Array<Nat> -> @tbl2: Array<U32> ->
         @gen2: Nat -> @hit2: Bool ->
         {hit2 == Nat.is_le(cur2, SolveFast.init_floor(len)) : Bool} ->
         {LB2.LB2.all_usable_ge(
            List.append(&2, +List<Nat>, ws_pre, g <> Nil{}),
            SolveFast.cwords_words(ws), cur2) == True{} : Bool} ->
         FH.FH.SeenTree(10n, 0, seen2, gen2, Nil{}) ->
         FT.FT.TblOk(G, C, n_root, tbl2) ->
         FTight.LB2Spec(G, SolveFast.cwords_words(ws), cur2, tbl2,
           SolveFast.scan_lb2_step(
             FT.FT.glist_of_rws(rest,
               SolveFast.GThen{FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{})}),
             ws, len, SolveFast.init_floor(len), False{},
             SolveFast.LB2Res{cur2, seen2, tbl2, gen2, hit2}))) ->
  FTight.LB2Spec(G, SolveFast.cwords_words(ws), cur, tbl0,
    SolveFast.scan_lb2_step(
      FT.FT.glist_of_rws(rest,
        SolveFast.GThen{FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{})}),
      ws, len, SolveFast.init_floor(len), False{}, lr1)):
  match lr1:
    case SolveFast.LB2Res{+cur2, seen2, tbl2, +gen2, +hit2}:
      +ws_w = SolveFast.cwords_words(ws)
      +fl = SolveFast.init_floor(len)
      +hs2 = Arr.Arr.dpair_l(FH.FH.SeenTree(10n, 0, seen2, gen2, Nil{}),
               Arr.Arr.DPair<{tbl2 == tbl0 : Array<U32>},
                 Arr.Arr.DPair<{hit2 == Nat.is_le(cur2, fl) : Bool},
                   Arr.Arr.DPair<{Nat.is_le(cur2, cur) == True{} : Bool},
                     {LB2.LB2.all_usable_ge(g <> Nil{}, ws_w, cur2)
                      == True{} : Bool}>>>, h1)
      +r1 = Arr.Arr.dpair_r(FH.FH.SeenTree(10n, 0, seen2, gen2, Nil{}),
              Arr.Arr.DPair<{tbl2 == tbl0 : Array<U32>},
                Arr.Arr.DPair<{hit2 == Nat.is_le(cur2, fl) : Bool},
                  Arr.Arr.DPair<{Nat.is_le(cur2, cur) == True{} : Bool},
                    {LB2.LB2.all_usable_ge(g <> Nil{}, ws_w, cur2)
                     == True{} : Bool}>>>, h1)
      +et2 = Arr.Arr.dpair_l({tbl2 == tbl0 : Array<U32>},
               Arr.Arr.DPair<{hit2 == Nat.is_le(cur2, fl) : Bool},
                 Arr.Arr.DPair<{Nat.is_le(cur2, cur) == True{} : Bool},
                   {LB2.LB2.all_usable_ge(g <> Nil{}, ws_w, cur2)
                    == True{} : Bool}>>, r1)
      +r2 = Arr.Arr.dpair_r({tbl2 == tbl0 : Array<U32>},
              Arr.Arr.DPair<{hit2 == Nat.is_le(cur2, fl) : Bool},
                Arr.Arr.DPair<{Nat.is_le(cur2, cur) == True{} : Bool},
                  {LB2.LB2.all_usable_ge(g <> Nil{}, ws_w, cur2)
                   == True{} : Bool}>>, r1)
      +ehit2 = Arr.Arr.dpair_l({hit2 == Nat.is_le(cur2, fl) : Bool},
                 Arr.Arr.DPair<{Nat.is_le(cur2, cur) == True{} : Bool},
                   {LB2.LB2.all_usable_ge(g <> Nil{}, ws_w, cur2)
                    == True{} : Bool}>, r2)
      +r3 = Arr.Arr.dpair_r({hit2 == Nat.is_le(cur2, fl) : Bool},
              Arr.Arr.DPair<{Nat.is_le(cur2, cur) == True{} : Bool},
                {LB2.LB2.all_usable_ge(g <> Nil{}, ws_w, cur2)
                 == True{} : Bool}>, r2)
      +hle_c = Arr.Arr.dpair_l({Nat.is_le(cur2, cur) == True{} : Bool},
                 {LB2.LB2.all_usable_ge(g <> Nil{}, ws_w, cur2)
                  == True{} : Bool}, r3)
      +hg_ok = Arr.Arr.dpair_r({Nat.is_le(cur2, cur) == True{} : Bool},
                 {LB2.LB2.all_usable_ge(g <> Nil{}, ws_w, cur2)
                  == True{} : Bool}, r3)
      +htbl2 = FT.FT.tbl_ok_transport(G, C, n_root, tbl0, tbl2,
                 Equal.sym(Array<U32>, tbl2, tbl0, et2), htbl0)
      +hpre2 = LB2.LB2.all_usable_ge_append(ws_pre, g <> Nil{}, ws_w, cur2,
                 LB2.LB2.all_usable_ge_mono(ws_pre, ws_w, cur, cur2, hle_c,
                   hpre), hg_ok)
      FTight.scan_lb2_stage1_cont_dup(g, rest, rwsG, G, C, n_root, ws, ws_pre,
        len, cur, cur2, seen2, tbl0, tbl2, gen2, hit2, et2, ehit2, hle_c,
        hpre2, hs2, htbl2, Arr.Arr.dup(Nat, seen2), Arr.Arr.dup(U32, tbl2),
        rec)

def FTight.scan_lb2_stage1_dup(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +row: U32, +g: +List<Nat>, +rest: +List<FT.FT.RowWord>,
    +rwsG: +List<FT.FT.RowWord>, +ws: +List<SolveFast.CWord>,
    +ws_pre: +List<+List<Nat>>, +len: Nat, +cur: Nat,
    -seen: Array<Nat>, -tbl: Array<U32>, +gen: Nat,
    +hge1: {Nat.is_le(1n, len) == True{} : Bool},
    +elen: {len == Groups.len_words(SolveFast.cwords_words(ws)) : Nat},
    +hnd: {FN.FN.no_dup_ref(SolveFast.cwords_words(ws)) == True{} : Bool},
    +hrow: {FT.FT.gentry_ok_b(G, n_root, row, g) == True{} : Bool},
    +hws: {FT.FT.cwords_ok_b(G, C, n_root, ws) == True{} : Bool},
    +hpre: {LB2.LB2.all_usable_ge(ws_pre, SolveFast.cwords_words(ws), cur)
            == True{} : Bool},
    +hs: FH.FH.SeenTree(10n, 0, seen, gen, Nil{}),
    +htbl: FT.FT.TblOk(G, C, n_root, tbl),
    dps: &s1: Array<Nat> -> &s2: Array<Nat> ->
         {s1 == seen : Array<Nat>} & {s2 == s1 : Array<Nat>},
    dpt: &t1: Array<U32> -> &t2: Array<U32> ->
         {t1 == tbl : Array<U32>} & {t2 == t1 : Array<U32>},
    rec: @cur2: Nat -> @seen2: Array<Nat> -> @tbl2: Array<U32> ->
         @gen2: Nat -> @hit2: Bool ->
         {hit2 == Nat.is_le(cur2, SolveFast.init_floor(len)) : Bool} ->
         {LB2.LB2.all_usable_ge(
            List.append(&2, +List<Nat>, ws_pre, g <> Nil{}),
            SolveFast.cwords_words(ws), cur2) == True{} : Bool} ->
         FH.FH.SeenTree(10n, 0, seen2, gen2, Nil{}) ->
         FT.FT.TblOk(G, C, n_root, tbl2) ->
         FTight.LB2Spec(G, SolveFast.cwords_words(ws), cur2, tbl2,
           SolveFast.scan_lb2_step(
             FT.FT.glist_of_rws(rest,
               SolveFast.GThen{FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{})}),
             ws, len, SolveFast.init_floor(len), False{},
             SolveFast.LB2Res{cur2, seen2, tbl2, gen2, hit2}))) ->
  FTight.LB2Spec(G, SolveFast.cwords_words(ws), cur, tbl,
    SolveFast.scan_lb2_step(
      FT.FT.glist_of_rws(rest,
        SolveFast.GThen{FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{})}),
      ws, len, SolveFast.init_floor(len), False{},
      SolveFast.lb2_hist_res(len, cur, SolveFast.init_floor(len), gen,
        SolveFast.hist5_go(row, ws, gen, False{},
          SolveFast.Hist5Ok{seen, tbl, 0n, 0n,
            SolveFast.lb2_bgt(len, cur, False{})})))) :
  (s1, dps2) = dps
  (s2, pes) = dps2
  (+es1, +es2) = pes
  (t1, dpt2) = dpt
  (t2, pet) = dpt2
  (+et1, +et2) = pet
  +ws_w = SolveFast.cwords_words(ws)
  +fl = SolveFast.init_floor(len)
  +bgt = SolveFast.lb2_bgt(len, cur, False{})
  +tailG : SolveFast.GList =
    SolveFast.GThen{FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{})}
  +es2_s : {s2 == seen : Array<Nat>} = Equal.trans(Array<Nat>, s2, s1, seen, es2, es1)
  +et2_t : {t2 == tbl : Array<U32>} = Equal.trans(Array<U32>, t2, t1, tbl, et2, et1)
  +hs_s2 = FH.FH.seen_tree_transport(10n, 0, seen, s2, gen, Nil{},
             Equal.sym(Array<Nat>, s2, seen, es2_s), hs)
  +ht_t2 = FT.FT.tbl_ok_transport(G, C, n_root, tbl, t2,
             Equal.sym(Array<U32>, t2, tbl, et2_t), htbl)
  +h1_s2 = FTight.lb2_one_step_dup(G, C, n_root, row, g, ws, len, cur, fl,
             False{}, s2, t2, gen, hge1, elen, hnd, hrow, hws, Unit{}, hs_s2,
             ht_t2, Arr.Arr.dup(Nat, s2), Arr.Arr.dup(U32, t2))
  +h1_t0 : FTight.LB2OneSpec(g, ws_w, cur, fl, tbl,
             SolveFast.lb2_hist_res(len, cur, fl, gen,
               SolveFast.hist5_go(row, ws, gen, False{},
                 SolveFast.Hist5Ok{s2, t2, 0n, 0n, bgt}))) =
    %et2_t : FTight.LB2OneSpec(g, ws_w, cur, fl, _,
               SolveFast.lb2_hist_res(len, cur, fl, gen,
                 SolveFast.hist5_go(row, ws, gen, False{},
                   SolveFast.Hist5Ok{s2, t2, 0n, 0n, bgt})))
    h1_s2
  +eq_12 : {SolveFast.lb2_hist_res(len, cur, fl, gen,
              SolveFast.hist5_go(row, ws, gen, False{},
                SolveFast.Hist5Ok{s2, t2, 0n, 0n, bgt}))
            == SolveFast.lb2_hist_res(len, cur, fl, gen,
                 SolveFast.hist5_go(row, ws, gen, False{},
                   SolveFast.Hist5Ok{s1, t1, 0n, 0n, bgt}))
            : SolveFast.LB2Res} =
    Equal.trans(SolveFast.LB2Res,
      SolveFast.lb2_hist_res(len, cur, fl, gen,
        SolveFast.hist5_go(row, ws, gen, False{},
          SolveFast.Hist5Ok{s2, t2, 0n, 0n, bgt})),
      SolveFast.lb2_hist_res(len, cur, fl, gen,
        SolveFast.hist5_go(row, ws, gen, False{},
          SolveFast.Hist5Ok{s1, t2, 0n, 0n, bgt})),
      SolveFast.lb2_hist_res(len, cur, fl, gen,
        SolveFast.hist5_go(row, ws, gen, False{},
          SolveFast.Hist5Ok{s1, t1, 0n, 0n, bgt})),
      Equal.cong(Array<Nat>, SolveFast.LB2Res,
        x => SolveFast.lb2_hist_res(len, cur, fl, gen,
               SolveFast.hist5_go(row, ws, gen, False{},
                 SolveFast.Hist5Ok{x, t2, 0n, 0n, bgt})), s2, s1, es2),
      Equal.cong(Array<U32>, SolveFast.LB2Res,
        y => SolveFast.lb2_hist_res(len, cur, fl, gen,
               SolveFast.hist5_go(row, ws, gen, False{},
                 SolveFast.Hist5Ok{s1, y, 0n, 0n, bgt})), t2, t1, et2))
  +h1_s1 = FTight.lb2_one_transport(g, ws_w, cur, fl, tbl,
             SolveFast.lb2_hist_res(len, cur, fl, gen,
               SolveFast.hist5_go(row, ws, gen, False{},
                 SolveFast.Hist5Ok{s2, t2, 0n, 0n, bgt})),
             SolveFast.lb2_hist_res(len, cur, fl, gen,
               SolveFast.hist5_go(row, ws, gen, False{},
                 SolveFast.Hist5Ok{s1, t1, 0n, 0n, bgt})), eq_12, h1_t0)
  %es1 : FTight.LB2Spec(G, ws_w, cur, tbl,
           SolveFast.scan_lb2_step(FT.FT.glist_of_rws(rest, tailG),
             ws, len, fl, False{},
             SolveFast.lb2_hist_res(len, cur, fl, gen,
               SolveFast.hist5_go(row, ws, gen, False{},
                 SolveFast.Hist5Ok{_, tbl, 0n, 0n, bgt}))))
  %et1 : FTight.LB2Spec(G, ws_w, cur, tbl,
           SolveFast.scan_lb2_step(FT.FT.glist_of_rws(rest, tailG),
             ws, len, fl, False{},
             SolveFast.lb2_hist_res(len, cur, fl, gen,
               SolveFast.hist5_go(row, ws, gen, False{},
                 SolveFast.Hist5Ok{s1, _, 0n, 0n, bgt}))))
  FTight.scan_lb2_stage1_cont(g, rest, rwsG, G, C, n_root, ws, ws_pre, len,
    cur, tbl,
    SolveFast.lb2_hist_res(len, cur, fl, gen,
      SolveFast.hist5_go(row, ws, gen, False{},
        SolveFast.Hist5Ok{s1, t1, 0n, 0n, bgt})),
    htbl, hpre, h1_s1, rec)

# Stage 1 of `scan_lb2_step`: scanning candidate guesses `rws_rem` followed by
# `GThen{glist_G}` with `floor = init_floor(len)` and `skip_self = False{}`.
def FTight.scan_lb2_stage1(+rws_rem: +List<FT.FT.RowWord>,
    +rwsG: +List<FT.FT.RowWord>, +G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +ws: +List<SolveFast.CWord>, +ws_pre: +List<+List<Nat>>,
    +len: Nat, +cur: Nat, seen: Array<Nat>, tbl: Array<U32>, +gen: Nat,
    hit: Bool,
    +ewsp: {List.append(&2, +List<Nat>, ws_pre, FT.FT.rws_words(rws_rem))
            == SolveFast.cwords_words(ws) : +List<+List<Nat>>},
    +hpre: {LB2.LB2.all_usable_ge(ws_pre, SolveFast.cwords_words(ws), cur)
            == True{} : Bool},
    +erwsG: {FT.FT.rws_words(rwsG) == G : +List<+List<Nat>>},
    +hrwsG: {FT.FT.rws_ok_b(G, n_root, rwsG) == True{} : Bool},
    +ehit: {hit == Nat.is_le(cur, SolveFast.init_floor(len)) : Bool},
    +hge1: {Nat.is_le(1n, len) == True{} : Bool},
    +elen: {len == Groups.len_words(SolveFast.cwords_words(ws)) : Nat},
    +hnd: {FN.FN.no_dup_ref(SolveFast.cwords_words(ws)) == True{} : Bool},
    +hws: {FT.FT.cwords_ok_b(G, C, n_root, ws) == True{} : Bool},
    +hrws: {FT.FT.rws_ok_b(G, n_root, rws_rem) == True{} : Bool},
    +hs: FH.FH.SeenTree(10n, 0, seen, gen, Nil{}),
    +htbl: FT.FT.TblOk(G, C, n_root, tbl)) ->
  FTight.LB2Spec(G, SolveFast.cwords_words(ws), cur, tbl,
    SolveFast.scan_lb2_step(
      FT.FT.glist_of_rws(rws_rem,
        SolveFast.GThen{FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{})}),
      ws, len, SolveFast.init_floor(len), False{},
      SolveFast.LB2Res{cur, seen, tbl, gen, hit})):
  match rws_rem:
    case Nil{}:
      match hit:
        case True{}:
          +ws_w = SolveFast.cwords_words(ws)
          +hle1 : {Nat.is_le(cur, SolveFast.init_floor(len)) == True{} : Bool} =
            Equal.sym(Bool, True{}, Nat.is_le(cur, SolveFast.init_floor(len)),
              ehit)
          +hle_fl : {Nat.is_le(cur, SolveFast.init_floor(Groups.len_words(ws_w)))
                     == True{} : Bool} =
            NatProof.Nat.is_le_eq_r(cur, SolveFast.init_floor(len),
              SolveFast.init_floor(Groups.len_words(ws_w)),
              Equal.cong(Nat, Nat, x => SolveFast.init_floor(x), len,
                Groups.len_words(ws_w), elen), hle1)
          +hall = LB2.LB2.all_usable_ge_of_le_floor(G, ws_w, cur, hnd, hle_fl)
          Arr.DPair{hs, Arr.DPair{{==},
            Arr.DPair{NatProof.Nat.is_le_refl(cur), hall}}}
        case False{}:
          +ws_w = SolveFast.cwords_words(ws)
          +epre_ws : {ws_pre == ws_w : +List<+List<Nat>>} =
            Equal.trans(+List<+List<Nat>>, ws_pre,
              List.append(&2, +List<Nat>, ws_pre, Nil{}), ws_w,
              Equal.sym(+List<+List<Nat>>,
                List.append(&2, +List<Nat>, ws_pre, Nil{}), ws_pre,
                FH.FH.list_append_nil(+List<Nat>, ws_pre)), ewsp)
          +hws_all : {LB2.LB2.all_usable_ge(ws_w, ws_w, cur) == True{} : Bool} =
            Equal.trans(Bool, LB2.LB2.all_usable_ge(ws_w, ws_w, cur),
              LB2.LB2.all_usable_ge(ws_pre, ws_w, cur), True{},
              Equal.cong(+List<+List<Nat>>, Bool,
                l => LB2.LB2.all_usable_ge(l, ws_w, cur), ws_w, ws_pre,
                Equal.sym(+List<+List<Nat>>, ws_pre, ws_w, epre_ws)), hpre)
          +hs2 = FTight.scan_lb2_stage2(rwsG, G, C, n_root, ws, len, cur, seen,
                   tbl, gen, Nat.is_le(cur, Nat.add(len, len)), {==}, hge1,
                   elen, hnd, hws, hrwsG, hws_all, hs, htbl)
          %erwsG : FTight.LB2Spec(_, ws_w, cur, tbl,
                     SolveFast.scan_lb2_step(
                       FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}),
                       ws, len, Nat.add(len, len), True{},
                       SolveFast.LB2Res{cur, seen, tbl, gen,
                         Nat.is_le(cur, Nat.add(len, len))}))
          hs2
    case Con{rw, +rest}:
      match rw:
        case FT.RowWord{+row, +g}:
          match hit:
            case True{}:
              +ws_w = SolveFast.cwords_words(ws)
              +hle1 : {Nat.is_le(cur, SolveFast.init_floor(len))
                       == True{} : Bool} =
                Equal.sym(Bool, True{},
                  Nat.is_le(cur, SolveFast.init_floor(len)), ehit)
              +hle_fl : {Nat.is_le(cur,
                           SolveFast.init_floor(Groups.len_words(ws_w)))
                         == True{} : Bool} =
                NatProof.Nat.is_le_eq_r(cur, SolveFast.init_floor(len),
                  SolveFast.init_floor(Groups.len_words(ws_w)),
                  Equal.cong(Nat, Nat, x => SolveFast.init_floor(x), len,
                    Groups.len_words(ws_w), elen), hle1)
              +hall = LB2.LB2.all_usable_ge_of_le_floor(G, ws_w, cur, hnd,
                        hle_fl)
              Arr.DPair{hs, Arr.DPair{{==},
                Arr.DPair{NatProof.Nat.is_le_refl(cur), hall}}}
            case False{}:
              +hrow = Logic.Proof.and_true_l(FT.FT.gentry_ok_b(G, n_root, row, g),
                        FT.FT.rws_ok_b(G, n_root, rest), hrws)
              +hrest = Logic.Proof.and_true_r(FT.FT.gentry_ok_b(G, n_root, row, g),
                         FT.FT.rws_ok_b(G, n_root, rest), hrws)
              +ws_pre2 : +List<+List<Nat>> =
                List.append(&2, +List<Nat>, ws_pre, g <> Nil{})
              +ewsp2 : {List.append(&2, +List<Nat>, ws_pre2,
                          FT.FT.rws_words(rest))
                        == SolveFast.cwords_words(ws) : +List<+List<Nat>>} =
                Equal.trans(+List<+List<Nat>>,
                  List.append(&2, +List<Nat>, ws_pre2, FT.FT.rws_words(rest)),
                  List.append(&2, +List<Nat>, ws_pre, g <> FT.FT.rws_words(rest)),
                  SolveFast.cwords_words(ws),
                  FTight.list_append_assoc(+List<Nat>, ws_pre, g <> Nil{},
                    FT.FT.rws_words(rest)), ewsp)
              FTight.scan_lb2_stage1_dup(G, C, n_root, row, g, rest, rwsG, ws,
                ws_pre, len, cur, seen, tbl, gen, hge1, elen, hnd, hrow, hws,
                hpre, hs, htbl, Arr.Arr.dup(Nat, seen), Arr.Arr.dup(U32, tbl),
                +cur2 => seen2 => tbl2 => +gen2 => hit2 => +ehit2 => +hpre2 =>
                +hs2 => +htbl2 =>
                  FTight.scan_lb2_stage1(rest, rwsG, G, C, n_root, ws, ws_pre2,
                    len, cur2, seen2, tbl2, gen2, hit2, ewsp2, hpre2, erwsG,
                    hrwsG, ehit2, hge1, elen, hnd, hws, hrest, hs2, htbl2))

def FTight.scan_lb2_full(+rwsG: +List<FT.FT.RowWord>, +G: +List<+List<Nat>>,
    +C: +List<+List<Nat>>, +n_root: Nat, +ws: +List<SolveFast.CWord>,
    +len: Nat, +cap: Nat, seen: Array<Nat>, tbl: Array<U32>, +gen: Nat,
    +erwsG: {FT.FT.rws_words(rwsG) == G : +List<+List<Nat>>},
    +hrwsG: {FT.FT.rws_ok_b(G, n_root, rwsG) == True{} : Bool},
    +hge1: {Nat.is_le(1n, len) == True{} : Bool},
    +elen: {len == Groups.len_words(SolveFast.cwords_words(ws)) : Nat},
    +hnd: {FN.FN.no_dup_ref(SolveFast.cwords_words(ws)) == True{} : Bool},
    +hws: {FT.FT.cwords_ok_b(G, C, n_root, ws) == True{} : Bool},
    +hs: FH.FH.SeenTree(10n, 0, seen, gen, Nil{}),
    +htbl: FT.FT.TblOk(G, C, n_root, tbl)) ->
  FTight.LB2Spec(G, SolveFast.cwords_words(ws), cap, tbl,
    SolveFast.scan_lb2_step(
      SolveFast.glist_of_cwords(ws,
        SolveFast.GThen{FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{})}),
      ws, len, SolveFast.init_floor(len), False{},
      SolveFast.LB2Res{cap, seen, tbl, gen,
        Nat.is_le(cap, SolveFast.init_floor(len))})):
  +tailG : SolveFast.GList =
    SolveFast.GThen{FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{})}
  +fl = SolveFast.init_floor(len)
  +h1 = FTight.scan_lb2_stage1(FT.FT.cwords_to_rws(ws), rwsG, G, C, n_root,
          ws, Nil{}, len, cap, seen, tbl, gen, Nat.is_le(cap, fl),
          FT.FT.cwords_to_rws_words(ws), {==}, erwsG, hrwsG, {==}, hge1, elen,
          hnd, hws, FT.FT.cwords_to_rws_ok(G, C, n_root, ws, hws), hs, htbl)
  %Equal.sym(SolveFast.GList,
     SolveFast.glist_of_cwords(ws, tailG),
     FT.FT.glist_of_rws(FT.FT.cwords_to_rws(ws), tailG),
     FT.FT.glist_of_cwords_eq(ws, tailG)) :
    FTight.LB2Spec(G, SolveFast.cwords_words(ws), cap, tbl,
      SolveFast.scan_lb2_step(_, ws, len, fl, False{},
        SolveFast.LB2Res{cap, seen, tbl, gen, Nat.is_le(cap, fl)}))
  h1

# ---------------------------------------------------------------------------
# Section 2: Soundness of `SolveFast.tighten_bigs_go`
# ---------------------------------------------------------------------------

type FTight.TightPruneWit<+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +bs: +List<SolveFast.BigClass>, +extra_lb: Nat,
    +b_cost: Nat> is Data:
  TPWit{bs_wit: +List<SolveFast.BigClass>,
        egrps: {FH.FH.bigs_groups(bs_wit) == FH.FH.bigs_groups(bs)
                : +List<Groups.Group>},
        hok: {FH.FH.bigs_ok_b(G, C, n_root, bs_wit) == True{} : Bool},
        hle: {Nat.is_le(b_cost,
                Nat.add(SolveFast.bigs_lb_sum(bs_wit, 0n), extra_lb))
              == True{} : Bool}}

def FTight.TightSpec(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +bs: +List<SolveFast.BigClass>, +extra_lb: Nat,
    +b_cost: Nat, -tbl0: Array<U32>, tr: SolveFast.TightRes) -> Data:
  match tr:
    case SolveFast.TightPruned{seen2, tbl2, gen2}:
      Arr.Arr.DPair<
        FH.FH.SeenTree(10n, 0, seen2, gen2, Nil{}),
        Arr.Arr.DPair<
          {tbl2 == tbl0 : Array<U32>},
          FTight.TightPruneWit<G, C, n_root, bs, extra_lb, b_cost>>>
    case SolveFast.TightOk{tot2, bs2, seen2, tbl2, gen2}:
      Arr.Arr.DPair<
        FH.FH.SeenTree(10n, 0, seen2, gen2, Nil{}),
        Arr.Arr.DPair<
          {tbl2 == tbl0 : Array<U32>},
          Arr.Arr.DPair<
            {FH.FH.bigs_groups(bs2) == FH.FH.bigs_groups(bs)
             : +List<Groups.Group>},
            Arr.Arr.DPair<
              {FH.FH.bigs_ok_b(G, C, n_root, bs2) == True{} : Bool},
              {tot2 == Nat.add(SolveFast.bigs_lb_sum(bs2, 0n), extra_lb)
               : Nat}>>>>

def FTight.tight_spec_transport(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +bs: +List<SolveFast.BigClass>, +extra_lb: Nat,
    +b_cost: Nat, -tbl0: Array<U32>,
    -r1: SolveFast.TightRes, -r2: SolveFast.TightRes,
    +er: {r1 == r2 : SolveFast.TightRes},
    +h: FTight.TightSpec(G, C, n_root, bs, extra_lb, b_cost, tbl0, r1)) ->
  FTight.TightSpec(G, C, n_root, bs, extra_lb, b_cost, tbl0, r2):
  %er : FTight.TightSpec(G, C, n_root, bs, extra_lb, b_cost, tbl0, _)
  h

def FTight.tight_spec_transport_tbl(+G: +List<+List<Nat>>,
    +C: +List<+List<Nat>>, +n_root: Nat, +bs: +List<SolveFast.BigClass>,
    +extra_lb: Nat, +b_cost: Nat, -t1: Array<U32>, -t2: Array<U32>,
    -r: SolveFast.TightRes, +et: {t1 == t2 : Array<U32>},
    +h: FTight.TightSpec(G, C, n_root, bs, extra_lb, b_cost, t1, r)) ->
  FTight.TightSpec(G, C, n_root, bs, extra_lb, b_cost, t2, r):
  %et : FTight.TightSpec(G, C, n_root, bs, extra_lb, b_cost, _, r)
  h

def FTight.tighten_one_check_spec(+G: +List<+List<Nat>>,
    +C: +List<+List<Nat>>, +n_root: Nat,
    +fb: +List<Feedback.Color>, +ws: +List<SolveFast.CWord>,
    +len: Nat, +old_clb: Nat, +new_clb: Nat, +new_tot: Nat,
    +rest: +List<SolveFast.BigClass>, +rest2: +List<SolveFast.BigClass>,
    +extra_lb: Nat, +b_cost: Nat, -seen2: Array<Nat>, -tbl0: Array<U32>,
    -tbl2: Array<U32>, +gen2: Nat, pruned: Bool,
    +epr: {pruned == Nat.is_le(b_cost, new_tot) : Bool},
    +hs2: FH.FH.SeenTree(10n, 0, seen2, gen2, Nil{}),
    +et2: {tbl2 == tbl0 : Array<U32>},
    +egrps: {FH.FH.bigs_groups(rest2) == FH.FH.bigs_groups(rest)
             : +List<Groups.Group>},
    +hbc_new: {FH.FH.big_ok_b(G, C, n_root,
                 SolveFast.BigClass{fb, ws, len, new_clb}) == True{} : Bool},
    +hrest2: {FH.FH.bigs_ok_b(G, C, n_root, rest2) == True{} : Bool},
    +etot: {new_tot == Nat.add(
              SolveFast.bigs_lb_sum(
                SolveFast.BigClass{fb, ws, len, new_clb} <> rest2, 0n),
              extra_lb) : Nat}) ->
  FTight.TightSpec(G, C, n_root,
    SolveFast.BigClass{fb, ws, len, old_clb} <> rest, extra_lb, b_cost, tbl0,
    SolveFast.tighten_one_check(fb, ws, len, new_clb, new_tot, rest2, seen2,
      tbl2, gen2, pruned)):
  match pruned:
    case True{}:
      +bc_new : SolveFast.BigClass = SolveFast.BigClass{fb, ws, len, new_clb}
      +bs_new : +List<SolveFast.BigClass> = bc_new <> rest2
      +egrps_all : {FH.FH.bigs_groups(bs_new)
                    == Groups.Group{fb, SolveFast.cwords_words(ws)}
                       <> FH.FH.bigs_groups(rest) : +List<Groups.Group>} =
        Equal.cong(+List<Groups.Group>, +List<Groups.Group>,
          l => Groups.Group{fb, SolveFast.cwords_words(ws)} <> l,
          FH.FH.bigs_groups(rest2), FH.FH.bigs_groups(rest), egrps)
      +hok_all : {FH.FH.bigs_ok_b(G, C, n_root, bs_new) == True{} : Bool} =
        FH.FH.bool_and_intro(FH.FH.big_ok_b(G, C, n_root, bc_new),
          FH.FH.bigs_ok_b(G, C, n_root, rest2), hbc_new, hrest2)
      +hle1 : {Nat.is_le(b_cost, new_tot) == True{} : Bool} =
        Equal.sym(Bool, True{}, Nat.is_le(b_cost, new_tot), epr)
      +hle : {Nat.is_le(b_cost,
                Nat.add(SolveFast.bigs_lb_sum(bs_new, 0n), extra_lb))
              == True{} : Bool} =
        NatProof.Nat.is_le_eq_r(b_cost, new_tot,
          Nat.add(SolveFast.bigs_lb_sum(bs_new, 0n), extra_lb), etot, hle1)
      Arr.DPair{hs2, Arr.DPair{et2, TPWit{bs_new, egrps_all, hok_all, hle}}}
    case False{}:
      +bc_new : SolveFast.BigClass = SolveFast.BigClass{fb, ws, len, new_clb}
      +bs_new : +List<SolveFast.BigClass> = bc_new <> rest2
      +egrps_all : {FH.FH.bigs_groups(bs_new)
                    == Groups.Group{fb, SolveFast.cwords_words(ws)}
                       <> FH.FH.bigs_groups(rest) : +List<Groups.Group>} =
        Equal.cong(+List<Groups.Group>, +List<Groups.Group>,
          l => Groups.Group{fb, SolveFast.cwords_words(ws)} <> l,
          FH.FH.bigs_groups(rest2), FH.FH.bigs_groups(rest), egrps)
      +hok_all : {FH.FH.bigs_ok_b(G, C, n_root, bs_new) == True{} : Bool} =
        FH.FH.bool_and_intro(FH.FH.big_ok_b(G, C, n_root, bc_new),
          FH.FH.bigs_ok_b(G, C, n_root, rest2), hbc_new, hrest2)
      Arr.DPair{hs2, Arr.DPair{et2,
        Arr.DPair{egrps_all, Arr.DPair{hok_all, etot}}}}

def FTight.tighten_one_finish_spec(+G: +List<+List<Nat>>,
    +C: +List<+List<Nat>>, +n_root: Nat,
    +fb: +List<Feedback.Color>, +ws: +List<SolveFast.CWord>,
    +len: Nat, +old_clb: Nat, +base_lb: Nat, +b_cost: Nat, +cap: Nat,
    +rest: +List<SolveFast.BigClass>, +rest2: +List<SolveFast.BigClass>,
    +extra_lb: Nat, -tbl0: Array<U32>, lr: SolveFast.LB2Res,
    +hcws: {FT.FT.cwords_ok_b(G, C, n_root, ws) == True{} : Bool},
    +elen_b: {Nat.is_eq(len, Groups.len_words(SolveFast.cwords_words(ws)))
              == True{} : Bool},
    +hnd: {FN.FN.no_dup_ref(SolveFast.cwords_words(ws)) == True{} : Bool},
    +egrps: {FH.FH.bigs_groups(rest2) == FH.FH.bigs_groups(rest)
             : +List<Groups.Group>},
    +hrest2: {FH.FH.bigs_ok_b(G, C, n_root, rest2) == True{} : Bool},
    +ebase: {base_lb == Nat.add(SolveFast.bigs_lb_sum(rest2, 0n), extra_lb)
             : Nat},
    +hlr: FTight.LB2Spec(G, SolveFast.cwords_words(ws), cap, tbl0, lr)) ->
  FTight.TightSpec(G, C, n_root,
    SolveFast.BigClass{fb, ws, len, old_clb} <> rest, extra_lb, b_cost, tbl0,
    SolveFast.tighten_one_finish(fb, ws, len, base_lb, b_cost, rest2, lr)):
  match lr:
    case SolveFast.LB2Res{+new_clb, seen2, tbl2, +gen2, hit}:
      +ws_w = SolveFast.cwords_words(ws)
      +hs2 = Arr.Arr.dpair_l(FH.FH.SeenTree(10n, 0, seen2, gen2, Nil{}),
               Arr.Arr.DPair<{tbl2 == tbl0 : Array<U32>},
                 Arr.Arr.DPair<{Nat.is_le(new_clb, cap) == True{} : Bool},
                   {LB2.LB2.all_usable_ge(G, ws_w, new_clb)
                    == True{} : Bool}>>, hlr)
      +r1 = Arr.Arr.dpair_r(FH.FH.SeenTree(10n, 0, seen2, gen2, Nil{}),
              Arr.Arr.DPair<{tbl2 == tbl0 : Array<U32>},
                Arr.Arr.DPair<{Nat.is_le(new_clb, cap) == True{} : Bool},
                  {LB2.LB2.all_usable_ge(G, ws_w, new_clb)
                   == True{} : Bool}>>, hlr)
      +et2 = Arr.Arr.dpair_l({tbl2 == tbl0 : Array<U32>},
               Arr.Arr.DPair<{Nat.is_le(new_clb, cap) == True{} : Bool},
                 {LB2.LB2.all_usable_ge(G, ws_w, new_clb)
                  == True{} : Bool}>, r1)
      +r2 = Arr.Arr.dpair_r({tbl2 == tbl0 : Array<U32>},
              Arr.Arr.DPair<{Nat.is_le(new_clb, cap) == True{} : Bool},
                {LB2.LB2.all_usable_ge(G, ws_w, new_clb)
                 == True{} : Bool}>, r1)
      +hall = Arr.Arr.dpair_r({Nat.is_le(new_clb, cap) == True{} : Bool},
                {LB2.LB2.all_usable_ge(G, ws_w, new_clb) == True{} : Bool}, r2)
      +hclb = LB2.LB2.clb_ok_of_all_usable(G, ws_w, new_clb, hall)
      +hbc_new : {FH.FH.big_ok_b(G, C, n_root,
                    SolveFast.BigClass{fb, ws, len, new_clb}) == True{} : Bool} =
        FH.FH.bool_and_intro(FT.FT.cwords_ok_b(G, C, n_root, ws),
          Bool.and(Nat.is_eq(len, Groups.len_words(ws_w)),
            Bool.and(FN.FN.no_dup_ref(ws_w),
              LB2.LB2.clb_ok_b(G, True{}, ws_w, new_clb))),
          hcws,
          FH.FH.bool_and_intro(Nat.is_eq(len, Groups.len_words(ws_w)),
            Bool.and(FN.FN.no_dup_ref(ws_w),
              LB2.LB2.clb_ok_b(G, True{}, ws_w, new_clb)),
            elen_b,
            FH.FH.bool_and_intro(FN.FN.no_dup_ref(ws_w),
              LB2.LB2.clb_ok_b(G, True{}, ws_w, new_clb), hnd, hclb)))
      +s2 = SolveFast.bigs_lb_sum(rest2, 0n)
      +new_tot = Nat.add(new_clb, base_lb)
      +etot : {new_tot == Nat.add(
                 SolveFast.bigs_lb_sum(
                   SolveFast.BigClass{fb, ws, len, new_clb} <> rest2, 0n),
                 extra_lb) : Nat} =
        Equal.trans(Nat,
          Nat.add(new_clb, base_lb),
          Nat.add(new_clb, Nat.add(s2, extra_lb)),
          Nat.add(
            SolveFast.bigs_lb_sum(
              SolveFast.BigClass{fb, ws, len, new_clb} <> rest2, 0n),
            extra_lb),
          Equal.cong(Nat, Nat, x => Nat.add(new_clb, x),
            base_lb, Nat.add(s2, extra_lb), ebase),
          Equal.trans(Nat,
            Nat.add(new_clb, Nat.add(s2, extra_lb)),
            Nat.add(Nat.add(s2, new_clb), extra_lb),
            Nat.add(
              SolveFast.bigs_lb_sum(
                SolveFast.BigClass{fb, ws, len, new_clb} <> rest2, 0n),
              extra_lb),
            Equal.trans(Nat,
              Nat.add(new_clb, Nat.add(s2, extra_lb)),
              Nat.add(Nat.add(new_clb, s2), extra_lb),
              Nat.add(Nat.add(s2, new_clb), extra_lb),
              Equal.sym(Nat, Nat.add(Nat.add(new_clb, s2), extra_lb),
                Nat.add(new_clb, Nat.add(s2, extra_lb)),
                NatProof.NatPrf.add_assoc(new_clb, s2, extra_lb)),
              Equal.cong(Nat, Nat, x => Nat.add(x, extra_lb),
                Nat.add(new_clb, s2), Nat.add(s2, new_clb),
                NatProof.NatPrf.add_comm(new_clb, s2))),
            Equal.cong(Nat, Nat, x => Nat.add(x, extra_lb),
              Nat.add(s2, new_clb),
              SolveFast.bigs_lb_sum(
                SolveFast.BigClass{fb, ws, len, new_clb} <> rest2, 0n),
              Equal.sym(Nat,
                SolveFast.bigs_lb_sum(
                  SolveFast.BigClass{fb, ws, len, new_clb} <> rest2, 0n),
                Nat.add(s2, new_clb),
                FTight.bigs_lb_sum_cons(fb, ws, len, new_clb, rest2)))))
      FTight.tighten_one_check_spec(G, C, n_root, fb, ws, len, old_clb,
        new_clb, new_tot, rest, rest2, extra_lb, b_cost, seen2, tbl0, tbl2,
        gen2, Nat.is_le(b_cost, new_tot), {==}, hs2, et2, egrps, hbc_new,
        hrest2, etot)

def FTight.tighten_one_scan_dup(+rwsG: +List<FT.FT.RowWord>,
    +G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n_root: Nat,
    +fb: +List<Feedback.Color>, +ws: +List<SolveFast.CWord>,
    +len: Nat, +old_clb: Nat, +base_lb: Nat, +b_cost: Nat, +cap: Nat,
    +rest: +List<SolveFast.BigClass>, +rest2: +List<SolveFast.BigClass>,
    +extra_lb: Nat, -seen: Array<Nat>, -tbl: Array<U32>, +gen: Nat,
    +erwsG: {FT.FT.rws_words(rwsG) == G : +List<+List<Nat>>},
    +hrwsG: {FT.FT.rws_ok_b(G, n_root, rwsG) == True{} : Bool},
    +hge1: {Nat.is_le(1n, len) == True{} : Bool},
    +hcws: {FT.FT.cwords_ok_b(G, C, n_root, ws) == True{} : Bool},
    +elen_b: {Nat.is_eq(len, Groups.len_words(SolveFast.cwords_words(ws)))
              == True{} : Bool},
    +hnd: {FN.FN.no_dup_ref(SolveFast.cwords_words(ws)) == True{} : Bool},
    +egrps: {FH.FH.bigs_groups(rest2) == FH.FH.bigs_groups(rest)
             : +List<Groups.Group>},
    +hrest2: {FH.FH.bigs_ok_b(G, C, n_root, rest2) == True{} : Bool},
    +ebase: {base_lb == Nat.add(SolveFast.bigs_lb_sum(rest2, 0n), extra_lb)
             : Nat},
    +hs: FH.FH.SeenTree(10n, 0, seen, gen, Nil{}),
    +htbl: FT.FT.TblOk(G, C, n_root, tbl),
    dps: &s1: Array<Nat> -> &s2: Array<Nat> ->
         {s1 == seen : Array<Nat>} & {s2 == s1 : Array<Nat>},
    dpt: &t1: Array<U32> -> &t2: Array<U32> ->
         {t1 == tbl : Array<U32>} & {t2 == t1 : Array<U32>}) ->
  FTight.TightSpec(G, C, n_root,
    SolveFast.BigClass{fb, ws, len, old_clb} <> rest, extra_lb, b_cost, tbl,
    SolveFast.tighten_one_finish(fb, ws, len, base_lb, b_cost, rest2,
      SolveFast.scan_lb2_step(
        SolveFast.glist_of_cwords(ws,
          SolveFast.GThen{FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{})}),
        ws, len, SolveFast.init_floor(len), False{},
        SolveFast.LB2Res{cap, seen, tbl, gen,
          Nat.is_le(cap, SolveFast.init_floor(len))}))) :
  (s1, dps2) = dps
  (s2, pes) = dps2
  (+es1, +es2) = pes
  (t1, dpt2) = dpt
  (t2, pet) = dpt2
  (+et1, +et2) = pet
  +ws_w = SolveFast.cwords_words(ws)
  +fl = SolveFast.init_floor(len)
  +g_in = SolveFast.glist_of_cwords(ws,
            SolveFast.GThen{FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{})})
  +elen = NatProof.NatPrf.is_eq_true(len, Groups.len_words(ws_w), elen_b)
  +es2_s : {s2 == seen : Array<Nat>} = Equal.trans(Array<Nat>, s2, s1, seen, es2, es1)
  +et2_t : {t2 == tbl : Array<U32>} = Equal.trans(Array<U32>, t2, t1, tbl, et2, et1)
  +hs_s2 = FH.FH.seen_tree_transport(10n, 0, seen, s2, gen, Nil{},
             Equal.sym(Array<Nat>, s2, seen, es2_s), hs)
  +ht_t2 = FT.FT.tbl_ok_transport(G, C, n_root, tbl, t2,
             Equal.sym(Array<U32>, t2, tbl, et2_t), htbl)
  +hlr2 = FTight.scan_lb2_full(rwsG, G, C, n_root, ws, len, cap, s2, t2, gen,
            erwsG, hrwsG, hge1, elen, hnd, hcws, hs_s2, ht_t2)
  +hlr_t0 = FTight.lb2_spec_transport_tbl(G, ws_w, cap, t2, tbl,
              SolveFast.scan_lb2_step(g_in, ws, len, fl, False{},
                SolveFast.LB2Res{cap, s2, t2, gen, Nat.is_le(cap, fl)}),
              et2_t, hlr2)
  +eq_12 : {SolveFast.scan_lb2_step(g_in, ws, len, fl, False{},
              SolveFast.LB2Res{cap, s2, t2, gen, Nat.is_le(cap, fl)})
            == SolveFast.scan_lb2_step(g_in, ws, len, fl, False{},
                 SolveFast.LB2Res{cap, s1, t1, gen, Nat.is_le(cap, fl)})
            : SolveFast.LB2Res} =
    Equal.trans(SolveFast.LB2Res,
      SolveFast.scan_lb2_step(g_in, ws, len, fl, False{},
        SolveFast.LB2Res{cap, s2, t2, gen, Nat.is_le(cap, fl)}),
      SolveFast.scan_lb2_step(g_in, ws, len, fl, False{},
        SolveFast.LB2Res{cap, s1, t2, gen, Nat.is_le(cap, fl)}),
      SolveFast.scan_lb2_step(g_in, ws, len, fl, False{},
        SolveFast.LB2Res{cap, s1, t1, gen, Nat.is_le(cap, fl)}),
      Equal.cong(Array<Nat>, SolveFast.LB2Res,
        x => SolveFast.scan_lb2_step(g_in, ws, len, fl, False{},
               SolveFast.LB2Res{cap, x, t2, gen, Nat.is_le(cap, fl)}),
        s2, s1, es2),
      Equal.cong(Array<U32>, SolveFast.LB2Res,
        y => SolveFast.scan_lb2_step(g_in, ws, len, fl, False{},
               SolveFast.LB2Res{cap, s1, y, gen, Nat.is_le(cap, fl)}),
        t2, t1, et2))
  +hlr1 = FTight.lb2_spec_transport(G, ws_w, cap, tbl,
            SolveFast.scan_lb2_step(g_in, ws, len, fl, False{},
              SolveFast.LB2Res{cap, s2, t2, gen, Nat.is_le(cap, fl)}),
            SolveFast.scan_lb2_step(g_in, ws, len, fl, False{},
              SolveFast.LB2Res{cap, s1, t1, gen, Nat.is_le(cap, fl)}),
            eq_12, hlr_t0)
  %es1 : FTight.TightSpec(G, C, n_root,
           SolveFast.BigClass{fb, ws, len, old_clb} <> rest, extra_lb, b_cost,
           tbl,
           SolveFast.tighten_one_finish(fb, ws, len, base_lb, b_cost, rest2,
             SolveFast.scan_lb2_step(g_in, ws, len, fl, False{},
               SolveFast.LB2Res{cap, _, tbl, gen, Nat.is_le(cap, fl)})))
  %et1 : FTight.TightSpec(G, C, n_root,
           SolveFast.BigClass{fb, ws, len, old_clb} <> rest, extra_lb, b_cost,
           tbl,
           SolveFast.tighten_one_finish(fb, ws, len, base_lb, b_cost, rest2,
             SolveFast.scan_lb2_step(g_in, ws, len, fl, False{},
               SolveFast.LB2Res{cap, s1, _, gen, Nat.is_le(cap, fl)})))
  FTight.tighten_one_finish_spec(G, C, n_root, fb, ws, len, old_clb, base_lb,
    b_cost, cap, rest, rest2, extra_lb, tbl,
    SolveFast.scan_lb2_step(g_in, ws, len, fl, False{},
      SolveFast.LB2Res{cap, s1, t1, gen, Nat.is_le(cap, fl)}),
    hcws, elen_b, hnd, egrps, hrest2, ebase, hlr1)

def FTight.tighten_one_spec(+rwsG: +List<FT.FT.RowWord>,
    +G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n_root: Nat,
    +fb: +List<Feedback.Color>, +ws: +List<SolveFast.CWord>,
    +len: Nat, +old_clb: Nat, +tot2: Nat, +b_cost: Nat,
    +rest: +List<SolveFast.BigClass>, +rest2: +List<SolveFast.BigClass>,
    +extra_lb: Nat, seen: Array<Nat>, tbl: Array<U32>, +gen: Nat,
    do_scan: Bool, +ed: {do_scan == Nat.is_le(8n, len) : Bool},
    +erwsG: {FT.FT.rws_words(rwsG) == G : +List<+List<Nat>>},
    +hrwsG: {FT.FT.rws_ok_b(G, n_root, rwsG) == True{} : Bool},
    +hbc: {FH.FH.big_ok_b(G, C, n_root,
             SolveFast.BigClass{fb, ws, len, old_clb}) == True{} : Bool},
    +egrps: {FH.FH.bigs_groups(rest2) == FH.FH.bigs_groups(rest)
             : +List<Groups.Group>},
    +hrest2: {FH.FH.bigs_ok_b(G, C, n_root, rest2) == True{} : Bool},
    +etot2: {tot2 == Nat.add(SolveFast.bigs_lb_sum(rest2, 0n),
                       Nat.add(old_clb, extra_lb)) : Nat},
    +hs: FH.FH.SeenTree(10n, 0, seen, gen, Nil{}),
    +htbl: FT.FT.TblOk(G, C, n_root, tbl)) ->
  FTight.TightSpec(G, C, n_root,
    SolveFast.BigClass{fb, ws, len, old_clb} <> rest, extra_lb, b_cost, tbl,
    SolveFast.tighten_one(FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}),
      fb, ws, len, old_clb, tot2, b_cost, rest2, seen, tbl, gen, do_scan)):
  match do_scan:
    case False{}:
      +bc_old : SolveFast.BigClass = SolveFast.BigClass{fb, ws, len, old_clb}
      +bs_old : +List<SolveFast.BigClass> = bc_old <> rest2
      +s2 = SolveFast.bigs_lb_sum(rest2, 0n)
      +egrps_all : {FH.FH.bigs_groups(bs_old)
                    == Groups.Group{fb, SolveFast.cwords_words(ws)}
                       <> FH.FH.bigs_groups(rest) : +List<Groups.Group>} =
        Equal.cong(+List<Groups.Group>, +List<Groups.Group>,
          l => Groups.Group{fb, SolveFast.cwords_words(ws)} <> l,
          FH.FH.bigs_groups(rest2), FH.FH.bigs_groups(rest), egrps)
      +hok_all : {FH.FH.bigs_ok_b(G, C, n_root, bs_old) == True{} : Bool} =
        FH.FH.bool_and_intro(FH.FH.big_ok_b(G, C, n_root, bc_old),
          FH.FH.bigs_ok_b(G, C, n_root, rest2), hbc, hrest2)
      +etot_old : {tot2 == Nat.add(SolveFast.bigs_lb_sum(bs_old, 0n), extra_lb)
                   : Nat} =
        Equal.trans(Nat, tot2, Nat.add(s2, Nat.add(old_clb, extra_lb)),
          Nat.add(SolveFast.bigs_lb_sum(bs_old, 0n), extra_lb), etot2,
          Equal.trans(Nat,
            Nat.add(s2, Nat.add(old_clb, extra_lb)),
            Nat.add(Nat.add(s2, old_clb), extra_lb),
            Nat.add(SolveFast.bigs_lb_sum(bs_old, 0n), extra_lb),
            Equal.sym(Nat, Nat.add(Nat.add(s2, old_clb), extra_lb),
              Nat.add(s2, Nat.add(old_clb, extra_lb)),
              NatProof.NatPrf.add_assoc(s2, old_clb, extra_lb)),
            Equal.cong(Nat, Nat, x => Nat.add(x, extra_lb),
              Nat.add(s2, old_clb), SolveFast.bigs_lb_sum(bs_old, 0n),
              Equal.sym(Nat, SolveFast.bigs_lb_sum(bs_old, 0n),
                Nat.add(s2, old_clb),
                FTight.bigs_lb_sum_cons(fb, ws, len, old_clb, rest2)))))
      Arr.DPair{hs, Arr.DPair{{==},
        Arr.DPair{egrps_all, Arr.DPair{hok_all, etot_old}}}}
    case True{}:
      +ws_w = SolveFast.cwords_words(ws)
      +hge8 : {Nat.is_le(8n, len) == True{} : Bool} =
        Equal.sym(Bool, True{}, Nat.is_le(8n, len), ed)
      +hge1 : {Nat.is_le(1n, len) == True{} : Bool} =
        NatProof.Nat.is_le_trans(1n, 8n, len, {==}, hge8)
      +hcws = Logic.Proof.and_true_l(FT.FT.cwords_ok_b(G, C, n_root, ws),
                Bool.and(Nat.is_eq(len, Groups.len_words(ws_w)),
                  Bool.and(FN.FN.no_dup_ref(ws_w),
                    LB2.LB2.clb_ok_b(G, True{}, ws_w, old_clb))), hbc)
      +hr1 = Logic.Proof.and_true_r(FT.FT.cwords_ok_b(G, C, n_root, ws),
               Bool.and(Nat.is_eq(len, Groups.len_words(ws_w)),
                 Bool.and(FN.FN.no_dup_ref(ws_w),
                   LB2.LB2.clb_ok_b(G, True{}, ws_w, old_clb))), hbc)
      +elen_b = Logic.Proof.and_true_l(Nat.is_eq(len, Groups.len_words(ws_w)),
                  Bool.and(FN.FN.no_dup_ref(ws_w),
                    LB2.LB2.clb_ok_b(G, True{}, ws_w, old_clb)), hr1)
      +hr2 = Logic.Proof.and_true_r(Nat.is_eq(len, Groups.len_words(ws_w)),
               Bool.and(FN.FN.no_dup_ref(ws_w),
                 LB2.LB2.clb_ok_b(G, True{}, ws_w, old_clb)), hr1)
      +hnd = Logic.Proof.and_true_l(FN.FN.no_dup_ref(ws_w),
               LB2.LB2.clb_ok_b(G, True{}, ws_w, old_clb), hr2)
      +s2 = SolveFast.bigs_lb_sum(rest2, 0n)
      +etot_sw : {tot2 == Nat.add(old_clb, Nat.add(s2, extra_lb)) : Nat} =
        Equal.trans(Nat, tot2, Nat.add(s2, Nat.add(old_clb, extra_lb)),
          Nat.add(old_clb, Nat.add(s2, extra_lb)), etot2,
          FTight.add_swap_l(s2, old_clb, extra_lb))
      +ebase : {Nat.sub(tot2, old_clb) == Nat.add(s2, extra_lb) : Nat} =
        Equal.trans(Nat,
          Nat.sub(tot2, old_clb),
          Nat.sub(Nat.add(old_clb, Nat.add(s2, extra_lb)), old_clb),
          Nat.add(s2, extra_lb),
          Equal.cong(Nat, Nat, x => Nat.sub(x, old_clb),
            tot2, Nat.add(old_clb, Nat.add(s2, extra_lb)), etot_sw),
          FLB.FS.add_sub_cancel_l(old_clb, Nat.add(s2, extra_lb)))
      +cap = Nat.add(old_clb, Nat.sub(b_cost, tot2))
      FTight.tighten_one_scan_dup(rwsG, G, C, n_root, fb, ws, len, old_clb,
        Nat.sub(tot2, old_clb), b_cost, cap, rest, rest2, extra_lb, seen, tbl,
        gen, erwsG, hrwsG, hge1, hcws, elen_b, hnd, egrps, hrest2, ebase, hs,
        htbl, Arr.Arr.dup(Nat, seen), Arr.Arr.dup(U32, tbl))

def FTight.tight_prune_lift(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +fb: +List<Feedback.Color>, +ws: +List<SolveFast.CWord>,
    +len: Nat, +clb: Nat, +rest: +List<SolveFast.BigClass>, +extra_lb: Nat,
    +b_cost: Nat,
    +hbc: {FH.FH.big_ok_b(G, C, n_root,
             SolveFast.BigClass{fb, ws, len, clb}) == True{} : Bool},
    pw: FTight.TightPruneWit<G, C, n_root, rest, Nat.add(clb, extra_lb),
          b_cost>) ->
  FTight.TightPruneWit<G, C, n_root,
    SolveFast.BigClass{fb, ws, len, clb} <> rest, extra_lb, b_cost>:
  match pw:
    case TPWit{+rest_wit, +egrps, +hok_r, +hle_r}:
      +bc1 : SolveFast.BigClass = SolveFast.BigClass{fb, ws, len, clb}
      +bs_wit : +List<SolveFast.BigClass> = bc1 <> rest_wit
      +sw = SolveFast.bigs_lb_sum(rest_wit, 0n)
      +egrps_all : {FH.FH.bigs_groups(bs_wit)
                    == Groups.Group{fb, SolveFast.cwords_words(ws)}
                       <> FH.FH.bigs_groups(rest) : +List<Groups.Group>} =
        Equal.cong(+List<Groups.Group>, +List<Groups.Group>,
          l => Groups.Group{fb, SolveFast.cwords_words(ws)} <> l,
          FH.FH.bigs_groups(rest_wit), FH.FH.bigs_groups(rest), egrps)
      +hok_all : {FH.FH.bigs_ok_b(G, C, n_root, bs_wit) == True{} : Bool} =
        FH.FH.bool_and_intro(FH.FH.big_ok_b(G, C, n_root, bc1),
          FH.FH.bigs_ok_b(G, C, n_root, rest_wit), hbc, hok_r)
      +esum : {Nat.add(sw, Nat.add(clb, extra_lb))
               == Nat.add(SolveFast.bigs_lb_sum(bs_wit, 0n), extra_lb)
               : Nat} =
        Equal.trans(Nat,
          Nat.add(sw, Nat.add(clb, extra_lb)),
          Nat.add(Nat.add(sw, clb), extra_lb),
          Nat.add(SolveFast.bigs_lb_sum(bs_wit, 0n), extra_lb),
          Equal.sym(Nat, Nat.add(Nat.add(sw, clb), extra_lb),
            Nat.add(sw, Nat.add(clb, extra_lb)),
            NatProof.NatPrf.add_assoc(sw, clb, extra_lb)),
          Equal.cong(Nat, Nat, x => Nat.add(x, extra_lb),
            Nat.add(sw, clb), SolveFast.bigs_lb_sum(bs_wit, 0n),
            Equal.sym(Nat, SolveFast.bigs_lb_sum(bs_wit, 0n),
              Nat.add(sw, clb),
              FTight.bigs_lb_sum_cons(fb, ws, len, clb, rest_wit))))
      +hle_all = NatProof.Nat.is_le_eq_r(b_cost,
                   Nat.add(sw, Nat.add(clb, extra_lb)),
                   Nat.add(SolveFast.bigs_lb_sum(bs_wit, 0n), extra_lb),
                   esum, hle_r)
      TPWit{bs_wit, egrps_all, hok_all, hle_all}

def FTight.tighten_bigs_step_spec(+rwsG: +List<FT.FT.RowWord>,
    +G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n_root: Nat,
    +fb: +List<Feedback.Color>, +ws: +List<SolveFast.CWord>,
    +len: Nat, +clb: Nat, +rest: +List<SolveFast.BigClass>,
    +extra_lb: Nat, +b_cost: Nat, -tbl0: Array<U32>, tr: SolveFast.TightRes,
    +erwsG: {FT.FT.rws_words(rwsG) == G : +List<+List<Nat>>},
    +hrwsG: {FT.FT.rws_ok_b(G, n_root, rwsG) == True{} : Bool},
    +hbc: {FH.FH.big_ok_b(G, C, n_root,
             SolveFast.BigClass{fb, ws, len, clb}) == True{} : Bool},
    +htbl0: FT.FT.TblOk(G, C, n_root, tbl0),
    +htr: FTight.TightSpec(G, C, n_root, rest, Nat.add(clb, extra_lb), b_cost,
            tbl0, tr)) ->
  FTight.TightSpec(G, C, n_root,
    SolveFast.BigClass{fb, ws, len, clb} <> rest, extra_lb, b_cost, tbl0,
    SolveFast.tighten_bigs_step(FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}),
      fb, ws, len, clb, b_cost, tr)):
  match tr:
    case SolveFast.TightPruned{seen2, tbl2, +gen2}:
      +hs2 = Arr.Arr.dpair_l(FH.FH.SeenTree(10n, 0, seen2, gen2, Nil{}),
               Arr.Arr.DPair<{tbl2 == tbl0 : Array<U32>},
                 FTight.TightPruneWit<G, C, n_root, rest,
                   Nat.add(clb, extra_lb), b_cost>>, htr)
      +r1 = Arr.Arr.dpair_r(FH.FH.SeenTree(10n, 0, seen2, gen2, Nil{}),
              Arr.Arr.DPair<{tbl2 == tbl0 : Array<U32>},
                FTight.TightPruneWit<G, C, n_root, rest,
                  Nat.add(clb, extra_lb), b_cost>>, htr)
      +et2 = Arr.Arr.dpair_l({tbl2 == tbl0 : Array<U32>},
               FTight.TightPruneWit<G, C, n_root, rest,
                 Nat.add(clb, extra_lb), b_cost>, r1)
      +pw = Arr.Arr.dpair_r({tbl2 == tbl0 : Array<U32>},
              FTight.TightPruneWit<G, C, n_root, rest,
                Nat.add(clb, extra_lb), b_cost>, r1)
      Arr.DPair{hs2, Arr.DPair{et2,
        FTight.tight_prune_lift(G, C, n_root, fb, ws, len, clb, rest, extra_lb,
          b_cost, hbc, pw)}}
    case SolveFast.TightOk{+tot2, +rest2, seen2, tbl2, +gen2}:
      +hs2 = Arr.Arr.dpair_l(FH.FH.SeenTree(10n, 0, seen2, gen2, Nil{}),
               Arr.Arr.DPair<{tbl2 == tbl0 : Array<U32>},
                 Arr.Arr.DPair<{FH.FH.bigs_groups(rest2)
                                == FH.FH.bigs_groups(rest)
                                : +List<Groups.Group>},
                   Arr.Arr.DPair<
                     {FH.FH.bigs_ok_b(G, C, n_root, rest2) == True{} : Bool},
                     {tot2 == Nat.add(SolveFast.bigs_lb_sum(rest2, 0n),
                                Nat.add(clb, extra_lb)) : Nat}>>>, htr)
      +r1 = Arr.Arr.dpair_r(FH.FH.SeenTree(10n, 0, seen2, gen2, Nil{}),
              Arr.Arr.DPair<{tbl2 == tbl0 : Array<U32>},
                Arr.Arr.DPair<{FH.FH.bigs_groups(rest2)
                               == FH.FH.bigs_groups(rest)
                               : +List<Groups.Group>},
                  Arr.Arr.DPair<
                    {FH.FH.bigs_ok_b(G, C, n_root, rest2) == True{} : Bool},
                    {tot2 == Nat.add(SolveFast.bigs_lb_sum(rest2, 0n),
                               Nat.add(clb, extra_lb)) : Nat}>>>, htr)
      +et2 = Arr.Arr.dpair_l({tbl2 == tbl0 : Array<U32>},
               Arr.Arr.DPair<{FH.FH.bigs_groups(rest2)
                              == FH.FH.bigs_groups(rest)
                              : +List<Groups.Group>},
                 Arr.Arr.DPair<
                   {FH.FH.bigs_ok_b(G, C, n_root, rest2) == True{} : Bool},
                   {tot2 == Nat.add(SolveFast.bigs_lb_sum(rest2, 0n),
                              Nat.add(clb, extra_lb)) : Nat}>>, r1)
      +r2 = Arr.Arr.dpair_r({tbl2 == tbl0 : Array<U32>},
              Arr.Arr.DPair<{FH.FH.bigs_groups(rest2)
                             == FH.FH.bigs_groups(rest)
                             : +List<Groups.Group>},
                Arr.Arr.DPair<
                  {FH.FH.bigs_ok_b(G, C, n_root, rest2) == True{} : Bool},
                  {tot2 == Nat.add(SolveFast.bigs_lb_sum(rest2, 0n),
                             Nat.add(clb, extra_lb)) : Nat}>>, r1)
      +egrps = Arr.Arr.dpair_l(
                 {FH.FH.bigs_groups(rest2) == FH.FH.bigs_groups(rest)
                  : +List<Groups.Group>},
                 Arr.Arr.DPair<
                   {FH.FH.bigs_ok_b(G, C, n_root, rest2) == True{} : Bool},
                   {tot2 == Nat.add(SolveFast.bigs_lb_sum(rest2, 0n),
                              Nat.add(clb, extra_lb)) : Nat}>, r2)
      +r3 = Arr.Arr.dpair_r(
              {FH.FH.bigs_groups(rest2) == FH.FH.bigs_groups(rest)
               : +List<Groups.Group>},
              Arr.Arr.DPair<
                {FH.FH.bigs_ok_b(G, C, n_root, rest2) == True{} : Bool},
                {tot2 == Nat.add(SolveFast.bigs_lb_sum(rest2, 0n),
                           Nat.add(clb, extra_lb)) : Nat}>, r2)
      +hrest2 = Arr.Arr.dpair_l(
                  {FH.FH.bigs_ok_b(G, C, n_root, rest2) == True{} : Bool},
                  {tot2 == Nat.add(SolveFast.bigs_lb_sum(rest2, 0n),
                             Nat.add(clb, extra_lb)) : Nat}, r3)
      +etot2 = Arr.Arr.dpair_r(
                 {FH.FH.bigs_ok_b(G, C, n_root, rest2) == True{} : Bool},
                 {tot2 == Nat.add(SolveFast.bigs_lb_sum(rest2, 0n),
                            Nat.add(clb, extra_lb)) : Nat}, r3)
      +htbl2 = FT.FT.tbl_ok_transport(G, C, n_root, tbl0, tbl2,
                 Equal.sym(Array<U32>, tbl2, tbl0, et2), htbl0)
      +h1 = FTight.tighten_one_spec(rwsG, G, C, n_root, fb, ws, len, clb, tot2,
              b_cost, rest, rest2, extra_lb, seen2, tbl2, gen2,
              Nat.is_le(8n, len), {==}, erwsG, hrwsG, hbc, egrps, hrest2,
              etot2, hs2, htbl2)
      FTight.tight_spec_transport_tbl(G, C, n_root,
        SolveFast.BigClass{fb, ws, len, clb} <> rest, extra_lb, b_cost,
        tbl2, tbl0,
        SolveFast.tighten_one(FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}),
          fb, ws, len, clb, tot2, b_cost, rest2, seen2, tbl2, gen2,
          Nat.is_le(8n, len)), et2, h1)

def FTight.tighten_bigs_cons_dup(+rwsG: +List<FT.FT.RowWord>,
    +G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n_root: Nat,
    +fb: +List<Feedback.Color>, +ws: +List<SolveFast.CWord>,
    +len: Nat, +clb: Nat, +rest: +List<SolveFast.BigClass>,
    +total_lb: Nat, +extra_lb: Nat, +b_cost: Nat,
    -seen: Array<Nat>, -tbl: Array<U32>, +gen: Nat,
    +erwsG: {FT.FT.rws_words(rwsG) == G : +List<+List<Nat>>},
    +hrwsG: {FT.FT.rws_ok_b(G, n_root, rwsG) == True{} : Bool},
    +hbc: {FH.FH.big_ok_b(G, C, n_root,
             SolveFast.BigClass{fb, ws, len, clb}) == True{} : Bool},
    +hs: FH.FH.SeenTree(10n, 0, seen, gen, Nil{}),
    +htbl: FT.FT.TblOk(G, C, n_root, tbl),
    dps: &s1: Array<Nat> -> &s2: Array<Nat> ->
         {s1 == seen : Array<Nat>} & {s2 == s1 : Array<Nat>},
    dpt: &t1: Array<U32> -> &t2: Array<U32> ->
         {t1 == tbl : Array<U32>} & {t2 == t1 : Array<U32>},
    rec: @s2: Array<Nat> -> @t2: Array<U32> ->
         FH.FH.SeenTree(10n, 0, s2, gen, Nil{}) ->
         FT.FT.TblOk(G, C, n_root, t2) ->
         FTight.TightSpec(G, C, n_root, rest, Nat.add(clb, extra_lb), b_cost,
           t2,
           SolveFast.tighten_bigs_go(
             FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}),
             rest, total_lb, b_cost, s2, t2, gen))) ->
  FTight.TightSpec(G, C, n_root,
    SolveFast.BigClass{fb, ws, len, clb} <> rest, extra_lb, b_cost, tbl,
    SolveFast.tighten_bigs_step(FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}),
      fb, ws, len, clb, b_cost,
      SolveFast.tighten_bigs_go(FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}),
        rest, total_lb, b_cost, seen, tbl, gen))):
  (s1, dps2) = dps
  (s2, pes) = dps2
  (+es1, +es2) = pes
  (t1, dpt2) = dpt
  (t2, pet) = dpt2
  (+et1, +et2) = pet
  +gG = FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{})
  +es2_s : {s2 == seen : Array<Nat>} = Equal.trans(Array<Nat>, s2, s1, seen, es2, es1)
  +et2_t : {t2 == tbl : Array<U32>} = Equal.trans(Array<U32>, t2, t1, tbl, et2, et1)
  +hs_s2 = FH.FH.seen_tree_transport(10n, 0, seen, s2, gen, Nil{},
             Equal.sym(Array<Nat>, s2, seen, es2_s), hs)
  +ht_t2 = FT.FT.tbl_ok_transport(G, C, n_root, tbl, t2,
             Equal.sym(Array<U32>, t2, tbl, et2_t), htbl)
  +hrec2 = rec(s2, t2, hs_s2, ht_t2)
  +hrec_t0 = FTight.tight_spec_transport_tbl(G, C, n_root, rest,
               Nat.add(clb, extra_lb), b_cost, t2, tbl,
               SolveFast.tighten_bigs_go(gG, rest, total_lb, b_cost, s2, t2,
                 gen), et2_t, hrec2)
  +eq_12 : {SolveFast.tighten_bigs_go(gG, rest, total_lb, b_cost, s2, t2, gen)
            == SolveFast.tighten_bigs_go(gG, rest, total_lb, b_cost, s1, t1, gen)
            : SolveFast.TightRes} =
    Equal.trans(SolveFast.TightRes,
      SolveFast.tighten_bigs_go(gG, rest, total_lb, b_cost, s2, t2, gen),
      SolveFast.tighten_bigs_go(gG, rest, total_lb, b_cost, s1, t2, gen),
      SolveFast.tighten_bigs_go(gG, rest, total_lb, b_cost, s1, t1, gen),
      Equal.cong(Array<Nat>, SolveFast.TightRes,
        x => SolveFast.tighten_bigs_go(gG, rest, total_lb, b_cost, x, t2, gen),
        s2, s1, es2),
      Equal.cong(Array<U32>, SolveFast.TightRes,
        y => SolveFast.tighten_bigs_go(gG, rest, total_lb, b_cost, s1, y, gen),
        t2, t1, et2))
  +hrec1 = FTight.tight_spec_transport(G, C, n_root, rest,
             Nat.add(clb, extra_lb), b_cost, tbl,
             SolveFast.tighten_bigs_go(gG, rest, total_lb, b_cost, s2, t2, gen),
             SolveFast.tighten_bigs_go(gG, rest, total_lb, b_cost, s1, t1, gen),
             eq_12, hrec_t0)
  %es1 : FTight.TightSpec(G, C, n_root,
           SolveFast.BigClass{fb, ws, len, clb} <> rest, extra_lb, b_cost, tbl,
           SolveFast.tighten_bigs_step(gG, fb, ws, len, clb, b_cost,
             SolveFast.tighten_bigs_go(gG, rest, total_lb, b_cost, _, tbl, gen)))
  %et1 : FTight.TightSpec(G, C, n_root,
           SolveFast.BigClass{fb, ws, len, clb} <> rest, extra_lb, b_cost, tbl,
           SolveFast.tighten_bigs_step(gG, fb, ws, len, clb, b_cost,
             SolveFast.tighten_bigs_go(gG, rest, total_lb, b_cost, s1, _, gen)))
  FTight.tighten_bigs_step_spec(rwsG, G, C, n_root, fb, ws, len, clb, rest,
    extra_lb, b_cost, tbl,
    SolveFast.tighten_bigs_go(gG, rest, total_lb, b_cost, s1, t1, gen),
    erwsG, hrwsG, hbc, htbl, hrec1)

def FTight.tighten_bigs_go_spec(+bs: +List<SolveFast.BigClass>,
    +rwsG: +List<FT.FT.RowWord>, +G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +total_lb: Nat, +extra_lb: Nat, +b_cost: Nat,
    seen: Array<Nat>, tbl: Array<U32>, +gen: Nat,
    +erwsG: {FT.FT.rws_words(rwsG) == G : +List<+List<Nat>>},
    +hrwsG: {FT.FT.rws_ok_b(G, n_root, rwsG) == True{} : Bool},
    +hbs: {FH.FH.bigs_ok_b(G, C, n_root, bs) == True{} : Bool},
    +etot: {total_lb == Nat.add(SolveFast.bigs_lb_sum(bs, 0n), extra_lb) : Nat},
    +hs: FH.FH.SeenTree(10n, 0, seen, gen, Nil{}),
    +htbl: FT.FT.TblOk(G, C, n_root, tbl)) ->
  FTight.TightSpec(G, C, n_root, bs, extra_lb, b_cost, tbl,
    SolveFast.tighten_bigs_go(FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}),
      bs, total_lb, b_cost, seen, tbl, gen)):
  match bs:
    case Nil{}:
      Arr.DPair{hs, Arr.DPair{{==}, Arr.DPair{{==}, Arr.DPair{{==}, etot}}}}
    case Con{bc, +rest}:
      match bc:
        case SolveFast.BigClass{+fb, +ws, +len, +clb}:
          +bc1 : SolveFast.BigClass = SolveFast.BigClass{fb, ws, len, clb}
          +hbc = Logic.Proof.and_true_l(FH.FH.big_ok_b(G, C, n_root, bc1),
                   FH.FH.bigs_ok_b(G, C, n_root, rest), hbs)
          +hrest = Logic.Proof.and_true_r(FH.FH.big_ok_b(G, C, n_root, bc1),
                     FH.FH.bigs_ok_b(G, C, n_root, rest), hbs)
          +sr = SolveFast.bigs_lb_sum(rest, 0n)
          +etot_r : {total_lb == Nat.add(sr, Nat.add(clb, extra_lb)) : Nat} =
            Equal.trans(Nat, total_lb,
              Nat.add(SolveFast.bigs_lb_sum(bc1 <> rest, 0n), extra_lb),
              Nat.add(sr, Nat.add(clb, extra_lb)), etot,
              Equal.trans(Nat,
                Nat.add(SolveFast.bigs_lb_sum(bc1 <> rest, 0n), extra_lb),
                Nat.add(Nat.add(sr, clb), extra_lb),
                Nat.add(sr, Nat.add(clb, extra_lb)),
                Equal.cong(Nat, Nat, x => Nat.add(x, extra_lb),
                  SolveFast.bigs_lb_sum(bc1 <> rest, 0n), Nat.add(sr, clb),
                  FTight.bigs_lb_sum_cons(fb, ws, len, clb, rest)),
                NatProof.NatPrf.add_assoc(sr, clb, extra_lb)))
          FTight.tighten_bigs_cons_dup(rwsG, G, C, n_root, fb, ws, len, clb,
            rest, total_lb, extra_lb, b_cost, seen, tbl, gen, erwsG, hrwsG,
            hbc, hs, htbl, Arr.Arr.dup(Nat, seen), Arr.Arr.dup(U32, tbl),
            s2 => t2 => +hs2 => +ht2 =>
              FTight.tighten_bigs_go_spec(rest, rwsG, G, C, n_root, total_lb,
                Nat.add(clb, extra_lb), b_cost, s2, t2, gen, erwsG, hrwsG,
                hrest, etot_r, hs2, ht2))

# ---------------------------------------------------------------------------
# Section 3: `finish_tight`, `finish_drain5_tight`, and `run_drain5_tight`
# ---------------------------------------------------------------------------

def FTight.mk_perm_full(+g: +List<Nat>, +S: +List<+List<Nat>>,
    +ig: +List<Groups.Group>, +bs_g: +List<Groups.Group>,
    +perm1: FP.FP.Perm,
    +hperm1: FP.FP.PermOk(perm1,
               List.append(&2, Groups.Group,
                 FN.FN.fgroups_to_groups(
                   SolveFast.fgroups_build_fast(g, S, Nil{})), Nil{}),
               List.append(&2, Groups.Group, bs_g, ig))) ->
  FP.FP.PermOk(
    FP.PTrans{
      List.append(&2, Groups.Group,
        FN.FN.fgroups_to_groups(SolveFast.fgroups_build_fast(g, S, Nil{})),
        Nil{}),
      FP.PRefl{},
      FP.PTrans{List.append(&2, Groups.Group, bs_g, ig), perm1,
        FP.FP.perm_sym(FP.FP.perm_rev_append(bs_g, ig))}},
    Groups.groups_build(g, S, Nil{}),
    FP.FP.rev_groups(bs_g, ig)):
  +fg = SolveFast.fgroups_build_fast(g, S, Nil{})
  +ord = FP.FP.rev_groups(bs_g, ig)
  +efg_app : {Groups.groups_build(g, S, Nil{})
              == List.append(&2, Groups.Group,
                   FN.FN.fgroups_to_groups(fg), Nil{})
              : +List<Groups.Group>} =
    Equal.sym(+List<Groups.Group>,
      List.append(&2, Groups.Group, FN.FN.fgroups_to_groups(fg), Nil{}),
      Groups.groups_build(g, S, Nil{}),
      Equal.trans(+List<Groups.Group>,
        List.append(&2, Groups.Group, FN.FN.fgroups_to_groups(fg), Nil{}),
        FN.FN.fgroups_to_groups(fg),
        Groups.groups_build(g, S, Nil{}),
        FH.FH.list_append_nil(Groups.Group, FN.FN.fgroups_to_groups(fg)),
        FN.FN.fgroups_build_eq(g, S, Nil{})))
  +hp_rev = FP.FP.perm_sym_ok(FP.FP.perm_rev_append(bs_g, ig),
              ord, List.append(&2, Groups.Group, bs_g, ig),
              FP.FP.perm_rev_append_ok(bs_g, ig))
  Arr.DPair{efg_app, Arr.DPair{hperm1, hp_rev}}

def FTight.finish_tight_pruned_pw(+G: +List<+List<Nat>>,
    +C: +List<+List<Nat>>, +n_root: Nat, +g: +List<Nat>, +S: +List<+List<Nat>>,
    +n: Nat, +floor: Nat, +best: SolveRef.Best, +rem_lb: Nat,
    +items: +List<SolveFast.Item>, +bigs: +List<SolveFast.BigClass>,
    +ig: +List<Groups.Group>, +perm1: FP.FP.Perm,
    +hus: {Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{}))
           == True{} : Bool},
    +hbm: FH.FH.BodyMatch(G, C, n_root, True{}, True{}, n, ig, items),
    +elb: {FH.FH.tail_lb_ok_b(G, True{}, n, items, rem_lb) == True{} : Bool},
    +hperm1: FP.FP.PermOk(perm1,
               List.append(&2, Groups.Group,
                 FN.FN.fgroups_to_groups(
                   SolveFast.fgroups_build_fast(g, S, Nil{})), Nil{}),
               List.append(&2, Groups.Group, FH.FH.bigs_groups(bigs), ig)),
    pw: FTight.TightPruneWit<G, C, n_root, bigs, rem_lb,
          SolveFast.best_cost(best)>) ->
  FH.FH.GuessWit<G, C, n_root, True{}, True{}, g, S, n, floor, best, Nil{}>:
  match pw:
    case TPWit{+bs_wit, +egrps, +hok_wit, +hle_sum}:
      +fg = SolveFast.fgroups_build_fast(g, S, Nil{})
      +bs_g = FH.FH.bigs_groups(bs_wit)
      +ord = FP.FP.rev_groups(bs_g, ig)
      +body = SolveFast.emit_bigs(bs_wit, rem_lb, items)
      +tot = SolveFast.bigs_lb_sum(bs_wit, rem_lb)
      +hem = FH.FH.emit_bigs_spec(G, C, n_root, n, bs_wit, rem_lb, items,
               ig, hok_wit, hbm, elb)
      +hbm_all = Arr.Arr.dpair_l(
                   FH.FH.BodyMatch(G, C, n_root, True{}, True{}, n, ord,
                     body),
                   {FH.FH.tail_lb_ok_b(G, True{}, n, body, tot)
                    == True{} : Bool}, hem)
      +htlb_all = Arr.Arr.dpair_r(
                    FH.FH.BodyMatch(G, C, n_root, True{}, True{}, n, ord,
                      body),
                    {FH.FH.tail_lb_ok_b(G, True{}, n, body, tot)
                     == True{} : Bool}, hem)
      +hperm1_w : FP.FP.PermOk(perm1,
                    List.append(&2, Groups.Group,
                      FN.FN.fgroups_to_groups(fg), Nil{}),
                    List.append(&2, Groups.Group, bs_g, ig)) =
        %Equal.sym(+List<Groups.Group>, bs_g, FH.FH.bigs_groups(bigs),
           egrps) :
          FP.FP.PermOk(perm1,
            List.append(&2, Groups.Group,
              FN.FN.fgroups_to_groups(fg), Nil{}),
            List.append(&2, Groups.Group, _, ig))
        hperm1
      +p_full : FP.FP.Perm =
        FP.PTrans{
          List.append(&2, Groups.Group, FN.FN.fgroups_to_groups(fg), Nil{}),
          FP.PRefl{},
          FP.PTrans{List.append(&2, Groups.Group, bs_g, ig), perm1,
            FP.FP.perm_sym(FP.FP.perm_rev_append(bs_g, ig))}}
      +hp_full = FTight.mk_perm_full(g, S, ig, bs_g, perm1, hperm1_w)
      +hle_tot_bc : {Nat.is_le(SolveFast.best_cost(best), tot)
                     == True{} : Bool} =
        NatProof.Nat.is_le_eq_r(SolveFast.best_cost(best),
          Nat.add(SolveFast.bigs_lb_sum(bs_wit, 0n), rem_lb), tot,
          Equal.sym(Nat, tot,
            Nat.add(SolveFast.bigs_lb_sum(bs_wit, 0n), rem_lb),
            FTight.bigs_lb_sum_add(bs_wit, rem_lb)), hle_sum)
      +hle_tot = FLB.FS.skippable_to_le(best, tot, hle_tot_bc)
      FH.GWit{FH.GCSkipBody{ord, body, tot, p_full},
        Arr.DPair{{==}, Arr.DPair{hus, Arr.DPair{hp_full,
          Arr.DPair{hbm_all, Arr.DPair{htlb_all, hle_tot}}}}}}

def FTight.finish_tight_spec(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +g: +List<Nat>, +S: +List<+List<Nat>>, +n: Nat, +floor: Nat,
    +best: SolveRef.Best, +rem_lb: Nat, +items: +List<SolveFast.Item>,
    +bigs: +List<SolveFast.BigClass>, +ig: +List<Groups.Group>,
    +perm1: FP.FP.Perm, bkts3: Array<+List<SolveFast.CWord>>,
    -tbl0: Array<U32>, tr: SolveFast.TightRes,
    +hus: {Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{}))
           == True{} : Bool},
    +hb3: FH.FH.BktTree(G, C, n_root, 10n, 0, bkts3, Nil{}),
    +htbl0: FT.FT.TblOk(G, C, n_root, tbl0),
    +hbm: FH.FH.BodyMatch(G, C, n_root, True{}, True{}, n, ig, items),
    +elb: {FH.FH.tail_lb_ok_b(G, True{}, n, items, rem_lb) == True{} : Bool},
    +hperm1: FP.FP.PermOk(perm1,
               List.append(&2, Groups.Group,
                 FN.FN.fgroups_to_groups(
                   SolveFast.fgroups_build_fast(g, S, Nil{})), Nil{}),
               List.append(&2, Groups.Group, FH.FH.bigs_groups(bigs), ig)),
    +htr: FTight.TightSpec(G, C, n_root, bigs, rem_lb,
            SolveFast.best_cost(best), tbl0, tr)) ->
  FH.FH.GuessSpec(G, C, n_root, True{}, True{}, g, S, n, floor, best,
    SolveFast.finish_tight(g, rem_lb, items, bkts3, tr)):
  match tr:
    case SolveFast.TightPruned{seen2, tbl2, +gen2}:
      +hs2 = Arr.Arr.dpair_l(FH.FH.SeenTree(10n, 0, seen2, gen2, Nil{}),
               Arr.Arr.DPair<{tbl2 == tbl0 : Array<U32>},
                 FTight.TightPruneWit<G, C, n_root, bigs, rem_lb,
                   SolveFast.best_cost(best)>>, htr)
      +r1 = Arr.Arr.dpair_r(FH.FH.SeenTree(10n, 0, seen2, gen2, Nil{}),
              Arr.Arr.DPair<{tbl2 == tbl0 : Array<U32>},
                FTight.TightPruneWit<G, C, n_root, bigs, rem_lb,
                  SolveFast.best_cost(best)>>, htr)
      +et2 = Arr.Arr.dpair_l({tbl2 == tbl0 : Array<U32>},
               FTight.TightPruneWit<G, C, n_root, bigs, rem_lb,
                 SolveFast.best_cost(best)>, r1)
      +pw = Arr.Arr.dpair_r({tbl2 == tbl0 : Array<U32>},
              FTight.TightPruneWit<G, C, n_root, bigs, rem_lb,
                SolveFast.best_cost(best)>, r1)
      +htbl2 = FT.FT.tbl_ok_transport(G, C, n_root, tbl0, tbl2,
                 Equal.sym(Array<U32>, tbl2, tbl0, et2), htbl0)
      Arr.DPair{
        FTight.finish_tight_pruned_pw(G, C, n_root, g, S, n, floor, best,
          rem_lb, items, bigs, ig, perm1, hus, hbm, elb, hperm1, pw),
        Arr.DPair{{==}, Arr.DPair{hs2, Arr.DPair{hb3, htbl2}}}}
    case SolveFast.TightOk{+tot2, +bigs2, seen2, tbl2, +gen2}:
      +hs2 = Arr.Arr.dpair_l(FH.FH.SeenTree(10n, 0, seen2, gen2, Nil{}),
               Arr.Arr.DPair<{tbl2 == tbl0 : Array<U32>},
                 Arr.Arr.DPair<{FH.FH.bigs_groups(bigs2)
                                == FH.FH.bigs_groups(bigs)
                                : +List<Groups.Group>},
                   Arr.Arr.DPair<
                     {FH.FH.bigs_ok_b(G, C, n_root, bigs2) == True{} : Bool},
                     {tot2 == Nat.add(SolveFast.bigs_lb_sum(bigs2, 0n), rem_lb)
                      : Nat}>>>, htr)
      +r1 = Arr.Arr.dpair_r(FH.FH.SeenTree(10n, 0, seen2, gen2, Nil{}),
              Arr.Arr.DPair<{tbl2 == tbl0 : Array<U32>},
                Arr.Arr.DPair<{FH.FH.bigs_groups(bigs2)
                               == FH.FH.bigs_groups(bigs)
                               : +List<Groups.Group>},
                  Arr.Arr.DPair<
                    {FH.FH.bigs_ok_b(G, C, n_root, bigs2) == True{} : Bool},
                    {tot2 == Nat.add(SolveFast.bigs_lb_sum(bigs2, 0n), rem_lb)
                     : Nat}>>>, htr)
      +et2 = Arr.Arr.dpair_l({tbl2 == tbl0 : Array<U32>},
               Arr.Arr.DPair<{FH.FH.bigs_groups(bigs2)
                              == FH.FH.bigs_groups(bigs)
                              : +List<Groups.Group>},
                 Arr.Arr.DPair<
                   {FH.FH.bigs_ok_b(G, C, n_root, bigs2) == True{} : Bool},
                   {tot2 == Nat.add(SolveFast.bigs_lb_sum(bigs2, 0n), rem_lb)
                    : Nat}>>, r1)
      +r2 = Arr.Arr.dpair_r({tbl2 == tbl0 : Array<U32>},
              Arr.Arr.DPair<{FH.FH.bigs_groups(bigs2)
                             == FH.FH.bigs_groups(bigs)
                             : +List<Groups.Group>},
                Arr.Arr.DPair<
                  {FH.FH.bigs_ok_b(G, C, n_root, bigs2) == True{} : Bool},
                  {tot2 == Nat.add(SolveFast.bigs_lb_sum(bigs2, 0n), rem_lb)
                   : Nat}>>, r1)
      +egrps = Arr.Arr.dpair_l(
                 {FH.FH.bigs_groups(bigs2) == FH.FH.bigs_groups(bigs)
                  : +List<Groups.Group>},
                 Arr.Arr.DPair<
                   {FH.FH.bigs_ok_b(G, C, n_root, bigs2) == True{} : Bool},
                   {tot2 == Nat.add(SolveFast.bigs_lb_sum(bigs2, 0n), rem_lb)
                    : Nat}>, r2)
      +r3 = Arr.Arr.dpair_r(
              {FH.FH.bigs_groups(bigs2) == FH.FH.bigs_groups(bigs)
               : +List<Groups.Group>},
              Arr.Arr.DPair<
                {FH.FH.bigs_ok_b(G, C, n_root, bigs2) == True{} : Bool},
                {tot2 == Nat.add(SolveFast.bigs_lb_sum(bigs2, 0n), rem_lb)
                 : Nat}>, r2)
      +hok2 = Arr.Arr.dpair_l(
                {FH.FH.bigs_ok_b(G, C, n_root, bigs2) == True{} : Bool},
                {tot2 == Nat.add(SolveFast.bigs_lb_sum(bigs2, 0n), rem_lb)
                 : Nat}, r3)
      +htbl2 = FT.FT.tbl_ok_transport(G, C, n_root, tbl0, tbl2,
                 Equal.sym(Array<U32>, tbl2, tbl0, et2), htbl0)
      +fg = SolveFast.fgroups_build_fast(g, S, Nil{})
      +bs_g = FH.FH.bigs_groups(bigs2)
      +ord = FP.FP.rev_groups(bs_g, ig)
      +body = SolveFast.emit_bigs(bigs2, rem_lb, items)
      +hem = FH.FH.emit_bigs_spec(G, C, n_root, n, bigs2, rem_lb, items, ig,
               hok2, hbm, elb)
      +hbm_all = Arr.Arr.dpair_l(
                   FH.FH.BodyMatch(G, C, n_root, True{}, True{}, n, ord, body),
                   {FH.FH.tail_lb_ok_b(G, True{}, n, body,
                      SolveFast.bigs_lb_sum(bigs2, rem_lb)) == True{} : Bool},
                   hem)
      +hperm1_2 : FP.FP.PermOk(perm1,
                    List.append(&2, Groups.Group,
                      FN.FN.fgroups_to_groups(fg), Nil{}),
                    List.append(&2, Groups.Group, bs_g, ig)) =
        %Equal.sym(+List<Groups.Group>, bs_g, FH.FH.bigs_groups(bigs), egrps) :
          FP.FP.PermOk(perm1,
            List.append(&2, Groups.Group, FN.FN.fgroups_to_groups(fg), Nil{}),
            List.append(&2, Groups.Group, _, ig))
        hperm1
      +p_full : FP.FP.Perm =
        FP.PTrans{
          List.append(&2, Groups.Group, FN.FN.fgroups_to_groups(fg), Nil{}),
          FP.PRefl{},
          FP.PTrans{List.append(&2, Groups.Group, bs_g, ig), perm1,
            FP.FP.perm_sym(FP.FP.perm_rev_append(bs_g, ig))}}
      +hp_full = FTight.mk_perm_full(g, S, ig, bs_g, perm1, hperm1_2)
      Arr.DPair{
        FH.GWit{FH.GCLive{ord, body, p_full},
          Arr.DPair{{==}, Arr.DPair{hus, Arr.DPair{hp_full, hbm_all}}}},
        Arr.DPair{{==}, Arr.DPair{hs2, Arr.DPair{hb3, htbl2}}}}

def FTight.finish_drain5_check_false_dup(+rwsG: +List<FT.FT.RowWord>,
    +G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n_root: Nat,
    +g: +List<Nat>, +S: +List<+List<Nat>>, +n: Nat, +floor: Nat,
    +best: SolveRef.Best, +rem_lb: Nat, +items: +List<SolveFast.Item>,
    +bigs: +List<SolveFast.BigClass>, +ig: +List<Groups.Group>,
    +perm1: FP.FP.Perm, -seen: Array<Nat>, bkts3: Array<+List<SolveFast.CWord>>,
    -tbl3: Array<U32>, +gen2: Nat,
    +erwsG: {FT.FT.rws_words(rwsG) == G : +List<+List<Nat>>},
    +hrwsG: {FT.FT.rws_ok_b(G, n_root, rwsG) == True{} : Bool},
    +hus: {Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{}))
           == True{} : Bool},
    +hs: FH.FH.SeenTree(10n, 0, seen, gen2, Nil{}),
    +hb3: FH.FH.BktTree(G, C, n_root, 10n, 0, bkts3, Nil{}),
    +htbl3: FT.FT.TblOk(G, C, n_root, tbl3),
    +hok_bigs: {FH.FH.bigs_ok_b(G, C, n_root, bigs) == True{} : Bool},
    +hbm: FH.FH.BodyMatch(G, C, n_root, True{}, True{}, n, ig, items),
    +elb: {FH.FH.tail_lb_ok_b(G, True{}, n, items, rem_lb) == True{} : Bool},
    +hperm1: FP.FP.PermOk(perm1,
               List.append(&2, Groups.Group,
                 FN.FN.fgroups_to_groups(
                   SolveFast.fgroups_build_fast(g, S, Nil{})), Nil{}),
               List.append(&2, Groups.Group, FH.FH.bigs_groups(bigs), ig)),
    dps: &s1: Array<Nat> -> &s2: Array<Nat> ->
         {s1 == seen : Array<Nat>} & {s2 == s1 : Array<Nat>},
    dpt: &t1: Array<U32> -> &t2: Array<U32> ->
         {t1 == tbl3 : Array<U32>} & {t2 == t1 : Array<U32>}) ->
  FH.FH.GuessSpec(G, C, n_root, True{}, True{}, g, S, n, floor, best,
    SolveFast.finish_tight(g, rem_lb, items, bkts3,
      SolveFast.tighten_bigs_go(FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}),
        bigs, SolveFast.bigs_lb_sum(bigs, rem_lb), SolveFast.best_cost(best),
        seen, tbl3, gen2))):
  (s1, dps2) = dps
  (s2, pes) = dps2
  (+es1, +es2) = pes
  (t1, dpt2) = dpt
  (t2, pet) = dpt2
  (+et1, +et2) = pet
  +gG = FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{})
  +tot = SolveFast.bigs_lb_sum(bigs, rem_lb)
  +bc = SolveFast.best_cost(best)
  +es2_s : {s2 == seen : Array<Nat>} = Equal.trans(Array<Nat>, s2, s1, seen, es2, es1)
  +et2_t : {t2 == tbl3 : Array<U32>} = Equal.trans(Array<U32>, t2, t1, tbl3, et2, et1)
  +hs_s2 = FH.FH.seen_tree_transport(10n, 0, seen, s2, gen2, Nil{},
             Equal.sym(Array<Nat>, s2, seen, es2_s), hs)
  +ht_t2 = FT.FT.tbl_ok_transport(G, C, n_root, tbl3, t2,
             Equal.sym(Array<U32>, t2, tbl3, et2_t), htbl3)
  +htr2 = FTight.tighten_bigs_go_spec(bigs, rwsG, G, C, n_root, tot, rem_lb,
            bc, s2, t2, gen2, erwsG, hrwsG, hok_bigs,
            FTight.bigs_lb_sum_add(bigs, rem_lb), hs_s2, ht_t2)
  +htr_t0 = FTight.tight_spec_transport_tbl(G, C, n_root, bigs, rem_lb, bc,
              t2, tbl3,
              SolveFast.tighten_bigs_go(gG, bigs, tot, bc, s2, t2, gen2),
              et2_t, htr2)
  +eq_12 : {SolveFast.tighten_bigs_go(gG, bigs, tot, bc, s2, t2, gen2)
            == SolveFast.tighten_bigs_go(gG, bigs, tot, bc, s1, t1, gen2)
            : SolveFast.TightRes} =
    Equal.trans(SolveFast.TightRes,
      SolveFast.tighten_bigs_go(gG, bigs, tot, bc, s2, t2, gen2),
      SolveFast.tighten_bigs_go(gG, bigs, tot, bc, s1, t2, gen2),
      SolveFast.tighten_bigs_go(gG, bigs, tot, bc, s1, t1, gen2),
      Equal.cong(Array<Nat>, SolveFast.TightRes,
        x => SolveFast.tighten_bigs_go(gG, bigs, tot, bc, x, t2, gen2),
        s2, s1, es2),
      Equal.cong(Array<U32>, SolveFast.TightRes,
        y => SolveFast.tighten_bigs_go(gG, bigs, tot, bc, s1, y, gen2),
        t2, t1, et2))
  +htr1 = FTight.tight_spec_transport(G, C, n_root, bigs, rem_lb, bc, tbl3,
            SolveFast.tighten_bigs_go(gG, bigs, tot, bc, s2, t2, gen2),
            SolveFast.tighten_bigs_go(gG, bigs, tot, bc, s1, t1, gen2),
            eq_12, htr_t0)
  %es1 : FH.FH.GuessSpec(G, C, n_root, True{}, True{}, g, S, n, floor, best,
           SolveFast.finish_tight(g, rem_lb, items, bkts3,
             SolveFast.tighten_bigs_go(gG, bigs, tot, bc, _, tbl3, gen2)))
  %et1 : FH.FH.GuessSpec(G, C, n_root, True{}, True{}, g, S, n, floor, best,
           SolveFast.finish_tight(g, rem_lb, items, bkts3,
             SolveFast.tighten_bigs_go(gG, bigs, tot, bc, s1, _, gen2)))
  FTight.finish_tight_spec(G, C, n_root, g, S, n, floor, best, rem_lb, items,
    bigs, ig, perm1, bkts3, tbl3,
    SolveFast.tighten_bigs_go(gG, bigs, tot, bc, s1, t1, gen2),
    hus, hb3, htbl3, hbm, elb, hperm1, htr1)

def FTight.finish_drain5_check_spec(+rwsG: +List<FT.FT.RowWord>,
    +G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n_root: Nat,
    +g: +List<Nat>, +S: +List<+List<Nat>>, +n: Nat, +floor: Nat,
    +best: SolveRef.Best, +rem_lb: Nat, +items: +List<SolveFast.Item>,
    +bigs: +List<SolveFast.BigClass>, +ig: +List<Groups.Group>,
    +perm1: FP.FP.Perm, seen: Array<Nat>, bkts3: Array<+List<SolveFast.CWord>>,
    tbl3: Array<U32>, +gen2: Nat, skip: Bool,
    +esk: {skip == Nat.is_le(SolveFast.best_cost(best),
                     SolveFast.bigs_lb_sum(bigs, rem_lb)) : Bool},
    +erwsG: {FT.FT.rws_words(rwsG) == G : +List<+List<Nat>>},
    +hrwsG: {FT.FT.rws_ok_b(G, n_root, rwsG) == True{} : Bool},
    +hus: {Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{}))
           == True{} : Bool},
    +hs: FH.FH.SeenTree(10n, 0, seen, gen2, Nil{}),
    +hb3: FH.FH.BktTree(G, C, n_root, 10n, 0, bkts3, Nil{}),
    +htbl3: FT.FT.TblOk(G, C, n_root, tbl3),
    +hok_bigs: {FH.FH.bigs_ok_b(G, C, n_root, bigs) == True{} : Bool},
    +hbm: FH.FH.BodyMatch(G, C, n_root, True{}, True{}, n, ig, items),
    +elb: {FH.FH.tail_lb_ok_b(G, True{}, n, items, rem_lb) == True{} : Bool},
    +hperm1: FP.FP.PermOk(perm1,
               List.append(&2, Groups.Group,
                 FN.FN.fgroups_to_groups(
                   SolveFast.fgroups_build_fast(g, S, Nil{})), Nil{}),
               List.append(&2, Groups.Group, FH.FH.bigs_groups(bigs), ig))) ->
  FH.FH.GuessSpec(G, C, n_root, True{}, True{}, g, S, n, floor, best,
    SolveFast.finish_drain5_check(g, FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}),
      SolveFast.best_cost(best), rem_lb, SolveFast.bigs_lb_sum(bigs, rem_lb),
      items, bigs, seen, bkts3, tbl3, gen2, skip)):
  match skip:
    case True{}:
      +fg = SolveFast.fgroups_build_fast(g, S, Nil{})
      +bs_g = FH.FH.bigs_groups(bigs)
      +ord = FP.FP.rev_groups(bs_g, ig)
      +body = SolveFast.emit_bigs(bigs, rem_lb, items)
      +tot = SolveFast.bigs_lb_sum(bigs, rem_lb)
      +hem = FH.FH.emit_bigs_spec(G, C, n_root, n, bigs, rem_lb, items, ig,
               hok_bigs, hbm, elb)
      +hbm_all = Arr.Arr.dpair_l(
                   FH.FH.BodyMatch(G, C, n_root, True{}, True{}, n, ord, body),
                   {FH.FH.tail_lb_ok_b(G, True{}, n, body, tot)
                    == True{} : Bool}, hem)
      +htlb_all = Arr.Arr.dpair_r(
                    FH.FH.BodyMatch(G, C, n_root, True{}, True{}, n, ord, body),
                    {FH.FH.tail_lb_ok_b(G, True{}, n, body, tot)
                     == True{} : Bool}, hem)
      +p_full : FP.FP.Perm =
        FP.PTrans{
          List.append(&2, Groups.Group, FN.FN.fgroups_to_groups(fg), Nil{}),
          FP.PRefl{},
          FP.PTrans{List.append(&2, Groups.Group, bs_g, ig), perm1,
            FP.FP.perm_sym(FP.FP.perm_rev_append(bs_g, ig))}}
      +hp_full = FTight.mk_perm_full(g, S, ig, bs_g, perm1, hperm1)
      +hle_tot = FLB.FS.skippable_to_le(best, tot,
                   Equal.sym(Bool, True{},
                     Nat.is_le(SolveFast.best_cost(best), tot), esk))
      Arr.DPair{
        FH.GWit{FH.GCSkipBody{ord, body, tot, p_full},
          Arr.DPair{{==}, Arr.DPair{hus, Arr.DPair{hp_full,
            Arr.DPair{hbm_all, Arr.DPair{htlb_all, hle_tot}}}}}},
        Arr.DPair{{==}, Arr.DPair{hs, Arr.DPair{hb3, htbl3}}}}
    case False{}:
      FTight.finish_drain5_check_false_dup(rwsG, G, C, n_root, g, S, n, floor,
        best, rem_lb, items, bigs, ig, perm1, seen, bkts3, tbl3, gen2, erwsG,
        hrwsG, hus, hs, hb3, htbl3, hok_bigs, hbm, elb, hperm1,
        Arr.Arr.dup(Nat, seen), Arr.Arr.dup(U32, tbl3))

def FTight.finish_drain5_tight_dw(+rwsG: +List<FT.FT.RowWord>,
    +G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n_root: Nat,
    +g: +List<Nat>, +S: +List<+List<Nat>>, +n: Nat, +floor: Nat,
    +best: SolveRef.Best, seen: Array<Nat>, bkts3: Array<+List<SolveFast.CWord>>,
    tbl3: Array<U32>, +gen2: Nat, +lb3: Nat, +items3: +List<SolveFast.Item>,
    +bigs3: +List<SolveFast.BigClass>,
    +erwsG: {FT.FT.rws_words(rwsG) == G : +List<+List<Nat>>},
    +hrwsG: {FT.FT.rws_ok_b(G, n_root, rwsG) == True{} : Bool},
    +hus: {Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{}))
           == True{} : Bool},
    +hs: FH.FH.SeenTree(10n, 0, seen, gen2, Nil{}),
    +hb3: FH.FH.BktTree(G, C, n_root, 10n, 0, bkts3, Nil{}),
    +htbl3: FT.FT.TblOk(G, C, n_root, tbl3),
    dw: FH.FH.DrainWit<G, C, n_root,
          SolveFast.fgroups_build_fast(g, S, Nil{}), n, Nil{}, Nil{}, lb3,
          items3, bigs3>) ->
  FH.FH.GuessSpec(G, C, n_root, True{}, True{}, g, S, n, floor, best,
    SolveFast.finish_drain5_check(g, FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}),
      SolveFast.best_cost(best), lb3, SolveFast.bigs_lb_sum(bigs3, lb3),
      items3, bigs3, seen, bkts3, tbl3, gen2,
      Nat.is_le(SolveFast.best_cost(best),
        SolveFast.bigs_lb_sum(bigs3, lb3)))):
  match dw:
    case FH.DWit{+ig, +perm1, +hok_bigs, +hbm, +elb, +hperm1}:
      FTight.finish_drain5_check_spec(rwsG, G, C, n_root, g, S, n, floor,
        best, lb3, items3, bigs3, ig, perm1, seen, bkts3, tbl3, gen2,
        Nat.is_le(SolveFast.best_cost(best),
          SolveFast.bigs_lb_sum(bigs3, lb3)), {==}, erwsG, hrwsG, hus, hs,
        hb3, htbl3, hok_bigs, hbm, elb, hperm1)

def FTight.finish_drain5_tight_spec(+rwsG: +List<FT.FT.RowWord>,
    +G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n_root: Nat,
    +g: +List<Nat>, +S: +List<+List<Nat>>, +n: Nat, +floor: Nat,
    +best: SolveRef.Best, seen: Array<Nat>, -tbl0: Array<U32>, +gen2: Nat,
    dr: SolveFast.Drain5State,
    +erwsG: {FT.FT.rws_words(rwsG) == G : +List<+List<Nat>>},
    +hrwsG: {FT.FT.rws_ok_b(G, n_root, rwsG) == True{} : Bool},
    +hus: {Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{}))
           == True{} : Bool},
    +hs: FH.FH.SeenTree(10n, 0, seen, gen2, Nil{}),
    +htbl0: FT.FT.TblOk(G, C, n_root, tbl0),
    +hdr: FH.FH.DrainSpec(G, C, n_root, Nil{},
            SolveFast.fgroups_build_fast(g, S, Nil{}), n, Nil{}, Nil{}, tbl0,
            dr)) ->
  FH.FH.GuessSpec(G, C, n_root, True{}, True{}, g, S, n, floor, best,
    SolveFast.finish_drain5_tight(g, FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}),
      best, seen, gen2, dr)):
  match dr:
    case SolveFast.Drain5State{bkts3, tbl3, +lb3, +items3, +bigs3}:
      +fg = SolveFast.fgroups_build_fast(g, S, Nil{})
      +hb3 = Arr.Arr.dpair_l(
               FH.FH.BktTree(G, C, n_root, 10n, 0, bkts3, Nil{}),
               Arr.Arr.DPair<{tbl3 == tbl0 : Array<U32>},
                 FH.FH.DrainWit<G, C, n_root, fg, n, Nil{}, Nil{}, lb3, items3,
                   bigs3>>, hdr)
      +hr = Arr.Arr.dpair_r(
              FH.FH.BktTree(G, C, n_root, 10n, 0, bkts3, Nil{}),
              Arr.Arr.DPair<{tbl3 == tbl0 : Array<U32>},
                FH.FH.DrainWit<G, C, n_root, fg, n, Nil{}, Nil{}, lb3, items3,
                  bigs3>>, hdr)
      +et3 = Arr.Arr.dpair_l({tbl3 == tbl0 : Array<U32>},
               FH.FH.DrainWit<G, C, n_root, fg, n, Nil{}, Nil{}, lb3, items3,
                 bigs3>, hr)
      +dw = Arr.Arr.dpair_r({tbl3 == tbl0 : Array<U32>},
              FH.FH.DrainWit<G, C, n_root, fg, n, Nil{}, Nil{}, lb3, items3,
                bigs3>, hr)
      +htbl3 = FT.FT.tbl_ok_transport(G, C, n_root, tbl0, tbl3,
                 Equal.sym(Array<U32>, tbl3, tbl0, et3), htbl0)
      FTight.finish_drain5_tight_dw(rwsG, G, C, n_root, g, S, n, floor, best,
        seen, bkts3, tbl3, gen2, lb3, items3, bigs3, erwsG, hrwsG, hus, hs,
        hb3, htbl3, dw)

def FTight.run_drain5_tight_dup(+rwsG: +List<FT.FT.RowWord>,
    +G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n_root: Nat,
    +g: +List<Nat>, +S: +List<+List<Nat>>, +n: Nat, +floor: Nat,
    +best: SolveRef.Best, seen: Array<Nat>, +gen2: Nat,
    -bkts2: Array<+List<SolveFast.CWord>>, -tbl0: Array<U32>, -tbl2: Array<U32>,
    +touched: +List<U32>,
    +erwsG: {FT.FT.rws_words(rwsG) == G : +List<+List<Nat>>},
    +hrwsG: {FT.FT.rws_ok_b(G, n_root, rwsG) == True{} : Bool},
    +hus: {Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{}))
           == True{} : Bool},
    +hnd_s: {FN.FN.no_dup_ref(S) == True{} : Bool},
    +hs: FH.FH.SeenTree(10n, 0, seen, gen2, Nil{}),
    +htbl0: FT.FT.TblOk(G, C, n_root, tbl0),
    +et20: {tbl2 == tbl0 : Array<U32>},
    +hb2: FH.FH.BktTree(G, C, n_root, 10n, 0, bkts2,
            SolveFast.fgroups_build_fast(g, S, Nil{})),
    +etouched: {touched
                == FH.FH.rev_codes(SolveFast.fgroups_build_fast(g, S, Nil{}),
                     Nil{}) : +List<U32>},
    +hwf: {FH.FH.fgroups_wf(SolveFast.fgroups_build_fast(g, S, Nil{}))
           == True{} : Bool},
    dpb: &b1: Array<+List<SolveFast.CWord>> -> &b2: Array<+List<SolveFast.CWord>> ->
         {b1 == bkts2 : Array<+List<SolveFast.CWord>>}
         & {b2 == b1 : Array<+List<SolveFast.CWord>>},
    dpt: &t1: Array<U32> -> &t2: Array<U32> ->
         {t1 == tbl2 : Array<U32>} & {t2 == t1 : Array<U32>}) ->
  FH.FH.GuessSpec(G, C, n_root, True{}, True{}, g, S, n, floor, best,
    SolveFast.finish_drain5_tight(g, FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}),
      best, seen, gen2,
      SolveFast.drain5_go(touched,
        SolveFast.Drain5State{bkts2, tbl2, n, SolveFast.End{} <> Nil{}, Nil{}}))):
  (b1, dpb2) = dpb
  (b2, peb) = dpb2
  (+eb1, +eb2) = peb
  (t1, dpt2) = dpt
  (t2, pet) = dpt2
  (+et1, +et2) = pet
  +gG = FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{})
  +fg = SolveFast.fgroups_build_fast(g, S, Nil{})
  +eb2_bk : {b2 == bkts2 : Array<+List<SolveFast.CWord>>} =
    Equal.trans(Array<+List<SolveFast.CWord>>, b2, b1, bkts2, eb2, eb1)
  +et2_t2 : {t2 == tbl2 : Array<U32>} = Equal.trans(Array<U32>, t2, t1, tbl2, et2, et1)
  +et2_t0 : {t2 == tbl0 : Array<U32>} = Equal.trans(Array<U32>, t2, tbl2, tbl0, et2_t2, et20)
  +hb_b2 = FH.FH.bkt_tree_transport(G, C, n_root, 10n, 0, bkts2, b2, fg,
             Equal.sym(Array<+List<SolveFast.CWord>>, b2, bkts2, eb2_bk), hb2)
  +ht_t2 = FT.FT.tbl_ok_transport(G, C, n_root, tbl0, t2,
             Equal.sym(Array<U32>, t2, tbl0, et2_t0), htbl0)
  +hnd_fg : {FN.FN.nodup_ok_jobs(True{},
               MV.MV.next_groups(FN.FN.fgroups_to_groups(fg))) == True{} : Bool} =
    Equal.trans(Bool,
      FN.FN.nodup_ok_jobs(True{}, MV.MV.next_groups(FN.FN.fgroups_to_groups(fg))),
      FN.FN.nodup_ok_jobs(True{},
        MV.MV.next_groups(Groups.groups_build(g, S, Nil{}))),
      True{},
      Equal.cong(+List<Groups.Group>, Bool,
        gs => FN.FN.nodup_ok_jobs(True{}, MV.MV.next_groups(gs)),
        FN.FN.fgroups_to_groups(fg), Groups.groups_build(g, S, Nil{}),
        FN.FN.fgroups_build_eq(g, S, Nil{})),
      FN.FN.nodup_ok_next_groups(True{}, Groups.groups_build(g, S, Nil{}), S,
        CoverGroups.Cover.all_subseq_nil(g, S), hnd_s))
  +hdr2 = FH.FH.drain5_go_spec(fg, G, C, n_root, Nil{}, n, Nil{}, Nil{}, n,
            SolveFast.End{} <> Nil{}, b2, t2, hwf, FH.FH.disjoint_codes_nil(fg),
            hnd_fg, {==}, {==}, NatProof.NatPrf.is_eq_refl(n), hb_b2, ht_t2)
  +hdr_t0 = FH.FH.drain_spec_transport_tbl(G, C, n_root, Nil{}, fg, n, Nil{},
              Nil{}, t2, tbl0,
              SolveFast.drain5_go(FH.FH.rev_codes(fg, Nil{}),
                SolveFast.Drain5State{b2, t2, n, SolveFast.End{} <> Nil{}, Nil{}}),
              et2_t0, hdr2)
  +eq_12 : {SolveFast.drain5_go(FH.FH.rev_codes(fg, Nil{}),
              SolveFast.Drain5State{b2, t2, n, SolveFast.End{} <> Nil{}, Nil{}})
            == SolveFast.drain5_go(FH.FH.rev_codes(fg, Nil{}),
                 SolveFast.Drain5State{b1, t1, n, SolveFast.End{} <> Nil{}, Nil{}})
            : SolveFast.Drain5State} =
    Equal.trans(SolveFast.Drain5State,
      SolveFast.drain5_go(FH.FH.rev_codes(fg, Nil{}),
        SolveFast.Drain5State{b2, t2, n, SolveFast.End{} <> Nil{}, Nil{}}),
      SolveFast.drain5_go(FH.FH.rev_codes(fg, Nil{}),
        SolveFast.Drain5State{b1, t2, n, SolveFast.End{} <> Nil{}, Nil{}}),
      SolveFast.drain5_go(FH.FH.rev_codes(fg, Nil{}),
        SolveFast.Drain5State{b1, t1, n, SolveFast.End{} <> Nil{}, Nil{}}),
      Equal.cong(Array<+List<SolveFast.CWord>>, SolveFast.Drain5State,
        x => SolveFast.drain5_go(FH.FH.rev_codes(fg, Nil{}),
               SolveFast.Drain5State{x, t2, n, SolveFast.End{} <> Nil{}, Nil{}}),
        b2, b1, eb2),
      Equal.cong(Array<U32>, SolveFast.Drain5State,
        y => SolveFast.drain5_go(FH.FH.rev_codes(fg, Nil{}),
               SolveFast.Drain5State{b1, y, n, SolveFast.End{} <> Nil{}, Nil{}}),
        t2, t1, et2))
  +hdr1 = FH.FH.drain_spec_transport(G, C, n_root, Nil{}, fg, n, Nil{}, Nil{},
            tbl0,
            SolveFast.drain5_go(FH.FH.rev_codes(fg, Nil{}),
              SolveFast.Drain5State{b2, t2, n, SolveFast.End{} <> Nil{}, Nil{}}),
            SolveFast.drain5_go(FH.FH.rev_codes(fg, Nil{}),
              SolveFast.Drain5State{b1, t1, n, SolveFast.End{} <> Nil{}, Nil{}}),
            eq_12, hdr_t0)
  %eb1 : FH.FH.GuessSpec(G, C, n_root, True{}, True{}, g, S, n, floor, best,
           SolveFast.finish_drain5_tight(g, gG, best, seen, gen2,
             SolveFast.drain5_go(touched,
               SolveFast.Drain5State{_, tbl2, n, SolveFast.End{} <> Nil{}, Nil{}})))
  %et1 : FH.FH.GuessSpec(G, C, n_root, True{}, True{}, g, S, n, floor, best,
           SolveFast.finish_drain5_tight(g, gG, best, seen, gen2,
             SolveFast.drain5_go(touched,
               SolveFast.Drain5State{b1, _, n, SolveFast.End{} <> Nil{}, Nil{}})))
  %Equal.sym(+List<U32>, touched, FH.FH.rev_codes(fg, Nil{}), etouched) :
    FH.FH.GuessSpec(G, C, n_root, True{}, True{}, g, S, n, floor, best,
      SolveFast.finish_drain5_tight(g, gG, best, seen, gen2,
        SolveFast.drain5_go(_,
          SolveFast.Drain5State{b1, t1, n, SolveFast.End{} <> Nil{}, Nil{}})))
  FTight.finish_drain5_tight_spec(rwsG, G, C, n_root, g, S, n, floor, best,
    seen, tbl0, gen2,
    SolveFast.drain5_go(FH.FH.rev_codes(fg, Nil{}),
      SolveFast.Drain5State{b1, t1, n, SolveFast.End{} <> Nil{}, Nil{}}),
    erwsG, hrwsG, hus, hs, htbl0, hdr1)

def FTight.run_drain5_tight_spec(+rwsG: +List<FT.FT.RowWord>,
    +G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n_root: Nat,
    +g: +List<Nat>, +S: +List<+List<Nat>>, +n: Nat, +floor: Nat,
    +best: SolveRef.Best, seen: Array<Nat>, -tbl0: Array<U32>, +gen2: Nat,
    fs: SolveFast.Fill5State,
    +erwsG: {FT.FT.rws_words(rwsG) == G : +List<+List<Nat>>},
    +hrwsG: {FT.FT.rws_ok_b(G, n_root, rwsG) == True{} : Bool},
    +hus: {Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{}))
           == True{} : Bool},
    +hnd_s: {FN.FN.no_dup_ref(S) == True{} : Bool},
    +hs: FH.FH.SeenTree(10n, 0, seen, gen2, Nil{}),
    +htbl0: FT.FT.TblOk(G, C, n_root, tbl0),
    +hfs: FH.FH.FillSpec(G, C, n_root,
            SolveFast.fgroups_build_fast(g, S, Nil{}), Nil{}, tbl0, fs)) ->
  FH.FH.GuessSpec(G, C, n_root, True{}, True{}, g, S, n, floor, best,
    SolveFast.run_drain5_tight(g, FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}),
      n, best, seen, gen2, fs)):
  match fs:
    case SolveFast.Fill5State{bkts2, tbl2, +touched}:
      +fg = SolveFast.fgroups_build_fast(g, S, Nil{})
      +hb2 = Arr.Arr.dpair_l(
               FH.FH.BktTree(G, C, n_root, 10n, 0, bkts2, fg),
               Arr.Arr.DPair<{tbl2 == tbl0 : Array<U32>},
                 Arr.Arr.DPair<
                   {touched == FH.FH.rev_codes(fg, Nil{}) : +List<U32>},
                   {FH.FH.fgroups_wf(fg) == True{} : Bool}>>, hfs)
      +r1 = Arr.Arr.dpair_r(
              FH.FH.BktTree(G, C, n_root, 10n, 0, bkts2, fg),
              Arr.Arr.DPair<{tbl2 == tbl0 : Array<U32>},
                Arr.Arr.DPair<
                  {touched == FH.FH.rev_codes(fg, Nil{}) : +List<U32>},
                  {FH.FH.fgroups_wf(fg) == True{} : Bool}>>, hfs)
      +et20 = Arr.Arr.dpair_l({tbl2 == tbl0 : Array<U32>},
                Arr.Arr.DPair<
                  {touched == FH.FH.rev_codes(fg, Nil{}) : +List<U32>},
                  {FH.FH.fgroups_wf(fg) == True{} : Bool}>, r1)
      +r2 = Arr.Arr.dpair_r({tbl2 == tbl0 : Array<U32>},
              Arr.Arr.DPair<
                {touched == FH.FH.rev_codes(fg, Nil{}) : +List<U32>},
                {FH.FH.fgroups_wf(fg) == True{} : Bool}>, r1)
      +et = Arr.Arr.dpair_l(
              {touched == FH.FH.rev_codes(fg, Nil{}) : +List<U32>},
              {FH.FH.fgroups_wf(fg) == True{} : Bool}, r2)
      +hwf = Arr.Arr.dpair_r(
               {touched == FH.FH.rev_codes(fg, Nil{}) : +List<U32>},
               {FH.FH.fgroups_wf(fg) == True{} : Bool}, r2)
      FTight.run_drain5_tight_dup(rwsG, G, C, n_root, g, S, n, floor, best,
        seen, gen2, bkts2, tbl0, tbl2, touched, erwsG, hrwsG, hus, hnd_s, hs,
        htbl0, et20, hb2, et, hwf,
        Arr.Arr.dup(+List<SolveFast.CWord>, bkts2), Arr.Arr.dup(U32, tbl2))

# ---------------------------------------------------------------------------
# Section 4: `schedule5_lb` .. `guess_items_buf_spec`
# ---------------------------------------------------------------------------

def FTight.schedule5_lb_false_dup(+rwsG: +List<FT.FT.RowWord>,
    +G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n_root: Nat,
    +row: U32, +g: +List<Nat>, +S: +List<SolveFast.CWord>,
    +n: Nat, +floor: Nat, +best: SolveRef.Best, seen: Array<Nat>,
    -bkts: Array<+List<SolveFast.CWord>>, -tbl: Array<U32>, +gen2: Nat,
    +erwsG: {FT.FT.rws_words(rwsG) == G : +List<+List<Nat>>},
    +hrwsG: {FT.FT.rws_ok_b(G, n_root, rwsG) == True{} : Bool},
    +hrow: {FT.FT.gentry_ok_b(G, n_root, row, g) == True{} : Bool},
    +hS: {FT.FT.cwords_ok_b(G, C, n_root, S) == True{} : Bool},
    +hus: {Groups.groups_smaller(SolveFast.cwords_words(S),
             Groups.groups_build(g, SolveFast.cwords_words(S), Nil{}))
           == True{} : Bool},
    +hnd_s: {FN.FN.no_dup_ref(SolveFast.cwords_words(S)) == True{} : Bool},
    +hs: FH.FH.SeenTree(10n, 0, seen, gen2, Nil{}),
    +hb: FH.FH.BktTree(G, C, n_root, 10n, 0, bkts, Nil{}),
    +htbl: FT.FT.TblOk(G, C, n_root, tbl),
    dpb: &b1: Array<+List<SolveFast.CWord>> -> &b2: Array<+List<SolveFast.CWord>> ->
         {b1 == bkts : Array<+List<SolveFast.CWord>>}
         & {b2 == b1 : Array<+List<SolveFast.CWord>>},
    dpt: &t1: Array<U32> -> &t2: Array<U32> ->
         {t1 == tbl : Array<U32>} & {t2 == t1 : Array<U32>}) ->
  FH.FH.GuessSpec(G, C, n_root, True{}, True{}, g, SolveFast.cwords_words(S), n,
    floor, best,
    SolveFast.run_drain5_tight(g, FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}),
      n, best, seen, gen2,
      SolveFast.fill5_go(row, S, SolveFast.Fill5State{bkts, tbl, Nil{}}))):
  (b1, dpb2) = dpb
  (b2, peb) = dpb2
  (+eb1, +eb2) = peb
  (t1, dpt2) = dpt
  (t2, pet) = dpt2
  (+et1, +et2) = pet
  +gG = FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{})
  +ws = SolveFast.cwords_words(S)
  +fg = SolveFast.fgroups_build_fast(g, ws, Nil{})
  +eb2_bk : {b2 == bkts : Array<+List<SolveFast.CWord>>} =
    Equal.trans(Array<+List<SolveFast.CWord>>, b2, b1, bkts, eb2, eb1)
  +et2_t : {t2 == tbl : Array<U32>} = Equal.trans(Array<U32>, t2, t1, tbl, et2, et1)
  +hb2 = FH.FH.bkt_tree_transport(G, C, n_root, 10n, 0, bkts, b2, Nil{},
           Equal.sym(Array<+List<SolveFast.CWord>>, b2, bkts, eb2_bk), hb)
  +ht2 = FT.FT.tbl_ok_transport(G, C, n_root, tbl, t2,
           Equal.sym(Array<U32>, t2, tbl, et2_t), htbl)
  +hfs2 = FH.FH.fill5_go_spec(S, G, C, n_root, row, g, Nil{}, b2, t2, Nil{},
            Nil{}, ht2, hrow, hS, {==}, {==}, hb2)
  +hfs_t0 = FH.FH.fill_spec_transport_tbl(G, C, n_root, fg, Nil{}, t2, tbl,
              SolveFast.fill5_go(row, S, SolveFast.Fill5State{b2, t2, Nil{}}),
              et2_t, hfs2)
  +eq_12 : {SolveFast.fill5_go(row, S, SolveFast.Fill5State{b2, t2, Nil{}})
            == SolveFast.fill5_go(row, S, SolveFast.Fill5State{b1, t1, Nil{}})
            : SolveFast.Fill5State} =
    Equal.trans(SolveFast.Fill5State,
      SolveFast.fill5_go(row, S, SolveFast.Fill5State{b2, t2, Nil{}}),
      SolveFast.fill5_go(row, S, SolveFast.Fill5State{b1, t2, Nil{}}),
      SolveFast.fill5_go(row, S, SolveFast.Fill5State{b1, t1, Nil{}}),
      Equal.cong(Array<+List<SolveFast.CWord>>, SolveFast.Fill5State,
        x => SolveFast.fill5_go(row, S, SolveFast.Fill5State{x, t2, Nil{}}),
        b2, b1, eb2),
      Equal.cong(Array<U32>, SolveFast.Fill5State,
        y => SolveFast.fill5_go(row, S, SolveFast.Fill5State{b1, y, Nil{}}),
        t2, t1, et2))
  +hfs1 = FH.FH.fill_spec_transport(G, C, n_root, fg, Nil{}, tbl,
            SolveFast.fill5_go(row, S, SolveFast.Fill5State{b2, t2, Nil{}}),
            SolveFast.fill5_go(row, S, SolveFast.Fill5State{b1, t1, Nil{}}),
            eq_12, hfs_t0)
  %eb1 : FH.FH.GuessSpec(G, C, n_root, True{}, True{}, g, ws, n, floor, best,
           SolveFast.run_drain5_tight(g, gG, n, best, seen, gen2,
             SolveFast.fill5_go(row, S, SolveFast.Fill5State{_, tbl, Nil{}})))
  %et1 : FH.FH.GuessSpec(G, C, n_root, True{}, True{}, g, ws, n, floor, best,
           SolveFast.run_drain5_tight(g, gG, n, best, seen, gen2,
             SolveFast.fill5_go(row, S, SolveFast.Fill5State{b1, _, Nil{}})))
  FTight.run_drain5_tight_spec(rwsG, G, C, n_root, g, ws, n, floor, best, seen,
    tbl, gen2,
    SolveFast.fill5_go(row, S, SolveFast.Fill5State{b1, t1, Nil{}}),
    erwsG, hrwsG, hus, hnd_s, hs, htbl, hfs1)

def FTight.schedule5_lb_spec(+rwsG: +List<FT.FT.RowWord>,
    +G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n_root: Nat,
    +row: U32, +g: +List<Nat>, +S: +List<SolveFast.CWord>,
    +n: Nat, +floor: Nat, +best: SolveRef.Best, seen: Array<Nat>,
    bkts: Array<+List<SolveFast.CWord>>, tbl: Array<U32>, +gen2: Nat,
    +lb: Nat, skip: Bool,
    +esk: {skip == SolveFast.skippable(best, lb) : Bool},
    +elb: {lb == SolveFast.lower_bound(n,
                   Groups.groups_build(g, SolveFast.cwords_words(S), Nil{}))
           : Nat},
    +erwsG: {FT.FT.rws_words(rwsG) == G : +List<+List<Nat>>},
    +hrwsG: {FT.FT.rws_ok_b(G, n_root, rwsG) == True{} : Bool},
    +hrow: {FT.FT.gentry_ok_b(G, n_root, row, g) == True{} : Bool},
    +hS: {FT.FT.cwords_ok_b(G, C, n_root, S) == True{} : Bool},
    +hus: {Groups.groups_smaller(SolveFast.cwords_words(S),
             Groups.groups_build(g, SolveFast.cwords_words(S), Nil{}))
           == True{} : Bool},
    +hnd_s: {FN.FN.no_dup_ref(SolveFast.cwords_words(S)) == True{} : Bool},
    +hs: FH.FH.SeenTree(10n, 0, seen, gen2, Nil{}),
    +hb: FH.FH.BktTree(G, C, n_root, 10n, 0, bkts, Nil{}),
    +htbl: FT.FT.TblOk(G, C, n_root, tbl)) ->
  FH.FH.GuessSpec(G, C, n_root, True{}, True{}, g, SolveFast.cwords_words(S), n,
    floor, best,
    SolveFast.schedule5_lb(row, g, FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}),
      S, n, best, seen, bkts, tbl, gen2, skip)):
  match skip:
    case True{}:
      +ws = SolveFast.cwords_words(S)
      +hle_lb : {Nat.is_le(Eval.Eval.cost_of(best), lb) == True{} : Bool} =
        FLB.FS.skippable_to_le(best, lb,
          Equal.sym(Bool, True{}, SolveFast.skippable(best, lb), esk))
      +hle : {Nat.is_le(Eval.Eval.cost_of(best),
                SolveFast.lower_bound(n, Groups.groups_build(g, ws, Nil{})))
              == True{} : Bool} =
        NatProof.Nat.is_le_eq_r(Eval.Eval.cost_of(best), lb,
          SolveFast.lower_bound(n, Groups.groups_build(g, ws, Nil{})),
          elb, hle_lb)
      Arr.DPair{
        FH.GWit{FH.GCSkipLb{}, Arr.DPair{{==}, hle}},
        Arr.DPair{{==}, Arr.DPair{hs, Arr.DPair{hb, htbl}}}}
    case False{}:
      FTight.schedule5_lb_false_dup(rwsG, G, C, n_root, row, g, S, n, floor,
        best, seen, bkts, tbl, gen2, erwsG, hrwsG, hrow, hS, hus, hnd_s, hs,
        hb, htbl, Arr.Arr.dup(+List<SolveFast.CWord>, bkts),
        Arr.Arr.dup(U32, tbl))

def FTight.schedule5_usable_spec(+rwsG: +List<FT.FT.RowWord>,
    +G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n_root: Nat,
    +row: U32, +g: +List<Nat>, +S: +List<SolveFast.CWord>,
    +n: Nat, +floor: Nat, +best: SolveRef.Best, seen: Array<Nat>,
    bkts: Array<+List<SolveFast.CWord>>, tbl: Array<U32>, +gen2: Nat,
    +m: Nat, +k: Nat, usable: Bool,
    +eus: {usable == Groups.groups_smaller(SolveFast.cwords_words(S),
                       Groups.groups_build(g, SolveFast.cwords_words(S), Nil{}))
           : Bool},
    +erwsG: {FT.FT.rws_words(rwsG) == G : +List<+List<Nat>>},
    +hrwsG: {FT.FT.rws_ok_b(G, n_root, rwsG) == True{} : Bool},
    +hrow: {FT.FT.gentry_ok_b(G, n_root, row, g) == True{} : Bool},
    +hS: {FT.FT.cwords_ok_b(G, C, n_root, S) == True{} : Bool},
    +hnd_s: {FN.FN.no_dup_ref(SolveFast.cwords_words(S)) == True{} : Bool},
    +hwf: {FH.FH.fgroups_wf(
             SolveFast.fgroups_build_fast(g, SolveFast.cwords_words(S), Nil{}))
           == True{} : Bool},
    +hm: {m == FH.FH.fgroups_total(
                 SolveFast.fgroups_build_fast(g, SolveFast.cwords_words(S),
                   Nil{})) : Nat},
    +hk: {k == FH.FH.fgroups_count(
                 SolveFast.fgroups_build_fast(g, SolveFast.cwords_words(S),
                   Nil{})) : Nat},
    +hs: FH.FH.SeenTree(10n, 0, seen, gen2, Nil{}),
    +hb: FH.FH.BktTree(G, C, n_root, 10n, 0, bkts, Nil{}),
    +htbl: FT.FT.TblOk(G, C, n_root, tbl)) ->
  FH.FH.GuessSpec(G, C, n_root, True{}, True{}, g, SolveFast.cwords_words(S), n,
    floor, best,
    SolveFast.schedule5_usable(row, g,
      FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), S, n, best, seen, bkts, tbl,
      gen2, m, k, usable)):
  match usable:
    case False{}:
      +ws = SolveFast.cwords_words(S)
      Arr.DPair{
        FH.GWit{FH.GCSkipUnusable{},
          Arr.DPair{{==},
            Equal.sym(Bool, False{},
              Groups.groups_smaller(ws, Groups.groups_build(g, ws, Nil{})),
              eus)}},
        Arr.DPair{{==}, Arr.DPair{hs, Arr.DPair{hb, htbl}}}}
    case True{}:
      +ws = SolveFast.cwords_words(S)
      +fg = SolveFast.fgroups_build_fast(g, ws, Nil{})
      +lb = Nat.sub(Nat.add(n, Nat.add(m, m)), k)
      +hpos = FH.FH.fgroups_pos_of_wf(fg, hwf)
      +elb_fg : {SolveFast.fgroups_lb_nodup(fg, n) == lb : Nat} =
        Equal.trans(Nat,
          SolveFast.fgroups_lb_nodup(fg, n),
          Nat.sub(
            Nat.add(n, Nat.add(FH.FH.fgroups_total(fg), FH.FH.fgroups_total(fg))),
            FH.FH.fgroups_count(fg)),
          lb,
          FH.FH.fgroups_lb_nodup_formula(n, fg, hpos),
          Equal.trans(Nat,
            Nat.sub(
              Nat.add(n, Nat.add(FH.FH.fgroups_total(fg), FH.FH.fgroups_total(fg))),
              FH.FH.fgroups_count(fg)),
            Nat.sub(Nat.add(n, Nat.add(m, m)), FH.FH.fgroups_count(fg)),
            lb,
            Equal.cong(Nat, Nat,
              x => Nat.sub(Nat.add(n, Nat.add(x, x)), FH.FH.fgroups_count(fg)),
              FH.FH.fgroups_total(fg), m,
              Equal.sym(Nat, m, FH.FH.fgroups_total(fg), hm)),
            Equal.cong(Nat, Nat, y => Nat.sub(Nat.add(n, Nat.add(m, m)), y),
              FH.FH.fgroups_count(fg), k,
              Equal.sym(Nat, k, FH.FH.fgroups_count(fg), hk))))
      +elb : {lb == SolveFast.lower_bound(n, Groups.groups_build(g, ws, Nil{}))
              : Nat} =
        Equal.trans(Nat, lb, SolveFast.fgroups_lb_nodup(fg, n),
          SolveFast.lower_bound(n, Groups.groups_build(g, ws, Nil{})),
          Equal.sym(Nat, SolveFast.fgroups_lb_nodup(fg, n), lb, elb_fg),
          FH.FH.fgroups_lb_nodup_eq_lb(g, ws, n, hnd_s))
      +hus : {Groups.groups_smaller(ws, Groups.groups_build(g, ws, Nil{}))
              == True{} : Bool} =
        Equal.sym(Bool, True{},
          Groups.groups_smaller(ws, Groups.groups_build(g, ws, Nil{})), eus)
      FTight.schedule5_lb_spec(rwsG, G, C, n_root, row, g, S, n, floor, best,
        seen, bkts, tbl, gen2, lb, SolveFast.skippable(best, lb), {==}, elb,
        erwsG, hrwsG, hrow, hS, hus, hnd_s, hs, hb, htbl)

def FTight.schedule5_hist_ok_dup(+rwsG: +List<FT.FT.RowWord>,
    +G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n_root: Nat,
    +row: U32, +g: +List<Nat>, +S: +List<SolveFast.CWord>,
    +n: Nat, +floor: Nat, +best: SolveRef.Best, +skip_self: Bool,
    -seen2: Array<Nat>, bkts: Array<+List<SolveFast.CWord>>,
    -tbl0: Array<U32>, tbl2: Array<U32>, +gen: Nat, +m: Nat, +k: Nat, +b: Nat,
    +erwsG: {FT.FT.rws_words(rwsG) == G : +List<+List<Nat>>},
    +hrwsG: {FT.FT.rws_ok_b(G, n_root, rwsG) == True{} : Bool},
    +hge1: {Nat.is_le(1n, n) == True{} : Bool},
    +en: {n == Groups.len_words(SolveFast.cwords_words(S)) : Nat},
    +hnd_s: {FN.FN.no_dup_ref(SolveFast.cwords_words(S)) == True{} : Bool},
    +hrow: {FT.FT.gentry_ok_b(G, n_root, row, g) == True{} : Bool},
    +hS: {FT.FT.cwords_ok_b(G, C, n_root, S) == True{} : Bool},
    +hb: FH.FH.BktTree(G, C, n_root, 10n, 0, bkts, Nil{}),
    +htbl0: FT.FT.TblOk(G, C, n_root, tbl0),
    +hhr: FH.FH.HistSpec(g, SolveFast.cwords_words(S), Nil{}, gen,
            SolveFast.budget_for(n, best, skip_self), skip_self, tbl0,
            SolveFast.Hist5Ok{seen2, tbl2, m, k, b}),
    dp: &s1: Array<Nat> -> &s2: Array<Nat> ->
        {s1 == seen2 : Array<Nat>} & {s2 == s1 : Array<Nat>}) ->
  FH.FH.GuessSpec(G, C, n_root, True{}, True{}, g, SolveFast.cwords_words(S), n,
    floor, best,
    SolveFast.schedule5_usable(row, g,
      FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), S, n, best, seen2, bkts,
      tbl2, Nat.add(1n, gen), m, k,
      Bool.or(Nat.is_lt(m, n), Nat.is_le(2n, k)))):
  (s1, dp2) = dp
  (s2, pe) = dp2
  (+es1, +es2) = pe
  +ws = SolveFast.cwords_words(S)
  +fg = SolveFast.fgroups_build_fast(g, ws, Nil{})
  +budget0 = SolveFast.budget_for(n, best, skip_self)
  +hs2 = Arr.Arr.dpair_l(
           FH.FH.SeenTree(10n, 0, seen2, gen, fg),
           Arr.Arr.DPair<{tbl2 == tbl0 : Array<U32>},
             Arr.Arr.DPair<{FH.FH.fgroups_wf(fg) == True{} : Bool},
               Arr.Arr.DPair<{m == FH.FH.fgroups_total(fg) : Nat},
                 Arr.Arr.DPair<{k == FH.FH.fgroups_count(fg) : Nat},
                   Arr.Arr.DPair<
                     {Nat.add(b, m) == Nat.add(budget0, k) : Nat},
                     {Nat.is_le(m, Nat.add(Groups.len_words(ws), 0n))
                      == True{} : Bool}>>>>>, hhr)
  +r1 = Arr.Arr.dpair_r(
          FH.FH.SeenTree(10n, 0, seen2, gen, fg),
          Arr.Arr.DPair<{tbl2 == tbl0 : Array<U32>},
            Arr.Arr.DPair<{FH.FH.fgroups_wf(fg) == True{} : Bool},
              Arr.Arr.DPair<{m == FH.FH.fgroups_total(fg) : Nat},
                Arr.Arr.DPair<{k == FH.FH.fgroups_count(fg) : Nat},
                  Arr.Arr.DPair<
                    {Nat.add(b, m) == Nat.add(budget0, k) : Nat},
                    {Nat.is_le(m, Nat.add(Groups.len_words(ws), 0n))
                     == True{} : Bool}>>>>>, hhr)
  +et20 = Arr.Arr.dpair_l({tbl2 == tbl0 : Array<U32>},
            Arr.Arr.DPair<{FH.FH.fgroups_wf(fg) == True{} : Bool},
              Arr.Arr.DPair<{m == FH.FH.fgroups_total(fg) : Nat},
                Arr.Arr.DPair<{k == FH.FH.fgroups_count(fg) : Nat},
                  Arr.Arr.DPair<
                    {Nat.add(b, m) == Nat.add(budget0, k) : Nat},
                    {Nat.is_le(m, Nat.add(Groups.len_words(ws), 0n))
                     == True{} : Bool}>>>>, r1)
  +r2 = Arr.Arr.dpair_r({tbl2 == tbl0 : Array<U32>},
          Arr.Arr.DPair<{FH.FH.fgroups_wf(fg) == True{} : Bool},
            Arr.Arr.DPair<{m == FH.FH.fgroups_total(fg) : Nat},
              Arr.Arr.DPair<{k == FH.FH.fgroups_count(fg) : Nat},
                Arr.Arr.DPair<
                  {Nat.add(b, m) == Nat.add(budget0, k) : Nat},
                  {Nat.is_le(m, Nat.add(Groups.len_words(ws), 0n))
                   == True{} : Bool}>>>>, r1)
  +hwf = Arr.Arr.dpair_l({FH.FH.fgroups_wf(fg) == True{} : Bool},
           Arr.Arr.DPair<{m == FH.FH.fgroups_total(fg) : Nat},
             Arr.Arr.DPair<{k == FH.FH.fgroups_count(fg) : Nat},
               Arr.Arr.DPair<
                 {Nat.add(b, m) == Nat.add(budget0, k) : Nat},
                 {Nat.is_le(m, Nat.add(Groups.len_words(ws), 0n))
                  == True{} : Bool}>>>, r2)
  +r3 = Arr.Arr.dpair_r({FH.FH.fgroups_wf(fg) == True{} : Bool},
          Arr.Arr.DPair<{m == FH.FH.fgroups_total(fg) : Nat},
            Arr.Arr.DPair<{k == FH.FH.fgroups_count(fg) : Nat},
              Arr.Arr.DPair<
                {Nat.add(b, m) == Nat.add(budget0, k) : Nat},
                {Nat.is_le(m, Nat.add(Groups.len_words(ws), 0n))
                 == True{} : Bool}>>>, r2)
  +hm = Arr.Arr.dpair_l({m == FH.FH.fgroups_total(fg) : Nat},
          Arr.Arr.DPair<{k == FH.FH.fgroups_count(fg) : Nat},
            Arr.Arr.DPair<
              {Nat.add(b, m) == Nat.add(budget0, k) : Nat},
              {Nat.is_le(m, Nat.add(Groups.len_words(ws), 0n))
               == True{} : Bool}>>, r3)
  +r4 = Arr.Arr.dpair_r({m == FH.FH.fgroups_total(fg) : Nat},
          Arr.Arr.DPair<{k == FH.FH.fgroups_count(fg) : Nat},
            Arr.Arr.DPair<
              {Nat.add(b, m) == Nat.add(budget0, k) : Nat},
              {Nat.is_le(m, Nat.add(Groups.len_words(ws), 0n))
               == True{} : Bool}>>, r3)
  +hk = Arr.Arr.dpair_l({k == FH.FH.fgroups_count(fg) : Nat},
          Arr.Arr.DPair<
            {Nat.add(b, m) == Nat.add(budget0, k) : Nat},
            {Nat.is_le(m, Nat.add(Groups.len_words(ws), 0n))
             == True{} : Bool}>, r4)
  +r5 = Arr.Arr.dpair_r({k == FH.FH.fgroups_count(fg) : Nat},
          Arr.Arr.DPair<
            {Nat.add(b, m) == Nat.add(budget0, k) : Nat},
            {Nat.is_le(m, Nat.add(Groups.len_words(ws), 0n))
             == True{} : Bool}>, r4)
  +hle0 = Arr.Arr.dpair_r(
            {Nat.add(b, m) == Nat.add(budget0, k) : Nat},
            {Nat.is_le(m, Nat.add(Groups.len_words(ws), 0n)) == True{} : Bool},
            r5)
  +es2_seen : {s2 == seen2 : Array<Nat>} =
    Equal.trans(Array<Nat>, s2, s1, seen2, es2, es1)
  +hs_s2 = FH.FH.seen_tree_transport(10n, 0, seen2, s2, gen, fg,
             Equal.sym(Array<Nat>, s2, seen2, es2_seen), hs2)
  +hbump = FH.FH.seen_tree_transport(10n, 0, s2, s1, Nat.add(1n, gen), Nil{},
             es2, FH.FH.seen_tree_bump(10n, 0, s2, gen, fg, hs_s2))
  +htbl2 = FT.FT.tbl_ok_transport(G, C, n_root, tbl0, tbl2,
             Equal.sym(Array<U32>, tbl2, tbl0, et20), htbl0)
  +hle_n : {Nat.is_le(FH.FH.fgroups_total(fg), n) == True{} : Bool} =
    NatProof.Nat.is_le_eq_r(FH.FH.fgroups_total(fg),
      Nat.add(Groups.len_words(ws), 0n), n,
      Equal.trans(Nat, Nat.add(Groups.len_words(ws), 0n), Groups.len_words(ws),
        n, NatProof.NatPrf.add_zero(Groups.len_words(ws)),
        Equal.sym(Nat, n, Groups.len_words(ws), en)),
      NatProof.Nat.is_le_eq_l(Nat.add(Groups.len_words(ws), 0n), m,
        FH.FH.fgroups_total(fg), hm, hle0))
  +eus_fg : {SolveFast.fgroups_smaller(n, fg)
             == Bool.or(Nat.is_lt(m, n), Nat.is_le(2n, k)) : Bool} =
    Equal.trans(Bool,
      SolveFast.fgroups_smaller(n, fg),
      Bool.or(Nat.is_lt(FH.FH.fgroups_total(fg), n),
        Nat.is_le(2n, FH.FH.fgroups_count(fg))),
      Bool.or(Nat.is_lt(m, n), Nat.is_le(2n, k)),
      FH.FH.fgroups_smaller_formula(n, fg, FH.FH.fgroups_pos_of_wf(fg, hwf),
        hge1, hle_n),
      Equal.trans(Bool,
        Bool.or(Nat.is_lt(FH.FH.fgroups_total(fg), n),
          Nat.is_le(2n, FH.FH.fgroups_count(fg))),
        Bool.or(Nat.is_lt(m, n), Nat.is_le(2n, FH.FH.fgroups_count(fg))),
        Bool.or(Nat.is_lt(m, n), Nat.is_le(2n, k)),
        Equal.cong(Nat, Bool,
          x => Bool.or(Nat.is_lt(x, n), Nat.is_le(2n, FH.FH.fgroups_count(fg))),
          FH.FH.fgroups_total(fg), m,
          Equal.sym(Nat, m, FH.FH.fgroups_total(fg), hm)),
        Equal.cong(Nat, Bool,
          y => Bool.or(Nat.is_lt(m, n), Nat.is_le(2n, y)),
          FH.FH.fgroups_count(fg), k,
          Equal.sym(Nat, k, FH.FH.fgroups_count(fg), hk))))
  +eus_g : {SolveFast.fgroups_smaller(n, fg)
            == Groups.groups_smaller(ws, Groups.groups_build(g, ws, Nil{}))
            : Bool} =
    Equal.trans(Bool,
      SolveFast.fgroups_smaller(n, fg),
      SolveFast.fgroups_smaller(Groups.len_words(ws), fg),
      Groups.groups_smaller(ws, Groups.groups_build(g, ws, Nil{})),
      Equal.cong(Nat, Bool, x => SolveFast.fgroups_smaller(x, fg),
        n, Groups.len_words(ws), en),
      Equal.trans(Bool,
        SolveFast.fgroups_smaller(Groups.len_words(ws), fg),
        Groups.groups_smaller(ws, FN.FN.fgroups_to_groups(fg)),
        Groups.groups_smaller(ws, Groups.groups_build(g, ws, Nil{})),
        FN.FN.fgroups_smaller_eq(ws, fg,
          FN.FN.fgroups_build_lens_ok(g, ws, Nil{}, {==})),
        Equal.cong(+List<Groups.Group>, Bool, gs => Groups.groups_smaller(ws, gs),
          FN.FN.fgroups_to_groups(fg), Groups.groups_build(g, ws, Nil{}),
          FN.FN.fgroups_build_eq(g, ws, Nil{}))))
  +eus : {Bool.or(Nat.is_lt(m, n), Nat.is_le(2n, k))
          == Groups.groups_smaller(ws, Groups.groups_build(g, ws, Nil{}))
          : Bool} =
    Equal.trans(Bool,
      Bool.or(Nat.is_lt(m, n), Nat.is_le(2n, k)),
      SolveFast.fgroups_smaller(n, fg),
      Groups.groups_smaller(ws, Groups.groups_build(g, ws, Nil{})),
      Equal.sym(Bool, SolveFast.fgroups_smaller(n, fg),
        Bool.or(Nat.is_lt(m, n), Nat.is_le(2n, k)), eus_fg), eus_g)
  %es1 : FH.FH.GuessSpec(G, C, n_root, True{}, True{}, g, ws, n, floor, best,
           SolveFast.schedule5_usable(row, g,
             FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), S, n, best, _, bkts,
             tbl2, Nat.add(1n, gen), m, k,
             Bool.or(Nat.is_lt(m, n), Nat.is_le(2n, k))))
  FTight.schedule5_usable_spec(rwsG, G, C, n_root, row, g, S, n, floor, best,
    s1, bkts, tbl2, Nat.add(1n, gen), m, k,
    Bool.or(Nat.is_lt(m, n), Nat.is_le(2n, k)), eus, erwsG, hrwsG, hrow, hS,
    hnd_s, hwf, hm, hk, hbump, hb, htbl2)

def FTight.schedule5_hist_spec(+rwsG: +List<FT.FT.RowWord>,
    +G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n_root: Nat,
    +row: U32, +g: +List<Nat>, +S: +List<SolveFast.CWord>,
    +n: Nat, +floor: Nat, +best: SolveRef.Best, +skip_self: Bool,
    bkts: Array<+List<SolveFast.CWord>>, -tbl0: Array<U32>, +gen: Nat,
    hr: SolveFast.Hist5Res,
    +erwsG: {FT.FT.rws_words(rwsG) == G : +List<+List<Nat>>},
    +hrwsG: {FT.FT.rws_ok_b(G, n_root, rwsG) == True{} : Bool},
    +esk: {skip_self == Nat.is_eq(floor, Nat.add(n, n)) : Bool},
    +hge1: {Nat.is_le(1n, n) == True{} : Bool},
    +en: {n == Groups.len_words(SolveFast.cwords_words(S)) : Nat},
    +hnd_s: {FN.FN.no_dup_ref(SolveFast.cwords_words(S)) == True{} : Bool},
    +hrow: {FT.FT.gentry_ok_b(G, n_root, row, g) == True{} : Bool},
    +hS: {FT.FT.cwords_ok_b(G, C, n_root, S) == True{} : Bool},
    +hb: FH.FH.BktTree(G, C, n_root, 10n, 0, bkts, Nil{}),
    +htbl0: FT.FT.TblOk(G, C, n_root, tbl0),
    +hhr: FH.FH.HistSpec(g, SolveFast.cwords_words(S), Nil{}, gen,
            SolveFast.budget_for(n, best, skip_self), skip_self, tbl0, hr)) ->
  FH.FH.GuessSpec(G, C, n_root, True{}, True{}, g, SolveFast.cwords_words(S), n,
    floor, best,
    SolveFast.schedule5_hist(row, g, FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}),
      S, n, best, bkts, gen, hr)):
  match hr:
    case SolveFast.Hist5Pruned{seen2, tbl2}:
      +ws = SolveFast.cwords_words(S)
      +budget0 = SolveFast.budget_for(n, best, skip_self)
      +hs2 = Arr.Arr.dpair_l(
               FH.FH.SeenTree(10n, 0, seen2, Nat.add(1n, gen), Nil{}),
               Arr.Arr.DPair<{tbl2 == tbl0 : Array<U32>},
                 {FH.FH.pruned_reason(g, ws, Nil{}, budget0, skip_self)
                  == True{} : Bool}>, hhr)
      +hr1 = Arr.Arr.dpair_r(
               FH.FH.SeenTree(10n, 0, seen2, Nat.add(1n, gen), Nil{}),
               Arr.Arr.DPair<{tbl2 == tbl0 : Array<U32>},
                 {FH.FH.pruned_reason(g, ws, Nil{}, budget0, skip_self)
                  == True{} : Bool}>, hhr)
      +et2 = Arr.Arr.dpair_l({tbl2 == tbl0 : Array<U32>},
               {FH.FH.pruned_reason(g, ws, Nil{}, budget0, skip_self)
                == True{} : Bool}, hr1)
      +hpr = Arr.Arr.dpair_r({tbl2 == tbl0 : Array<U32>},
               {FH.FH.pruned_reason(g, ws, Nil{}, budget0, skip_self)
                == True{} : Bool}, hr1)
      +htbl2 = FT.FT.tbl_ok_transport(G, C, n_root, tbl0, tbl2,
                 Equal.sym(Array<U32>, tbl2, tbl0, et2), htbl0)
      Arr.DPair{
        FH.FH.schedule5_pruned_wit(G, C, n_root, g, ws, n, floor, best,
          skip_self, esk, en, hnd_s, Tree.member_word(g, ws), {==}, hpr),
        Arr.DPair{{==}, Arr.DPair{hs2, Arr.DPair{hb, htbl2}}}}
    case SolveFast.Hist5Ok{seen2, tbl2, +m, +k, +b}:
      FTight.schedule5_hist_ok_dup(rwsG, G, C, n_root, row, g, S, n, floor,
        best, skip_self, seen2, bkts, tbl0, tbl2, gen, m, k, b, erwsG, hrwsG,
        hge1, en, hnd_s, hrow, hS, hb, htbl0, hhr, Arr.Arr.dup(Nat, seen2))

def FTight.guess_body_buf5_dup(+rwsG: +List<FT.FT.RowWord>,
    +G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n_root: Nat,
    +row: U32, +g: +List<Nat>, +S: +List<SolveFast.CWord>,
    +n: Nat, +floor: Nat, +best: SolveRef.Best, +skip_self: Bool,
    -seen: Array<Nat>, bkts: Array<+List<SolveFast.CWord>>, -tbl: Array<U32>,
    +gen: Nat,
    +erwsG: {FT.FT.rws_words(rwsG) == G : +List<+List<Nat>>},
    +hrwsG: {FT.FT.rws_ok_b(G, n_root, rwsG) == True{} : Bool},
    +esk: {skip_self == Nat.is_eq(floor, Nat.add(n, n)) : Bool},
    +hge1: {Nat.is_le(1n, n) == True{} : Bool},
    +en: {n == Groups.len_words(SolveFast.cwords_words(S)) : Nat},
    +hnd_s: {FN.FN.no_dup_ref(SolveFast.cwords_words(S)) == True{} : Bool},
    +hrow: {FT.FT.gentry_ok_b(G, n_root, row, g) == True{} : Bool},
    +hS: {FT.FT.cwords_ok_b(G, C, n_root, S) == True{} : Bool},
    +hs: FH.FH.SeenTree(10n, 0, seen, gen, Nil{}),
    +hb: FH.FH.BktTree(G, C, n_root, 10n, 0, bkts, Nil{}),
    +htbl: FT.FT.TblOk(G, C, n_root, tbl),
    dps: &s1: Array<Nat> -> &s2: Array<Nat> ->
         {s1 == seen : Array<Nat>} & {s2 == s1 : Array<Nat>},
    dpt: &t1: Array<U32> -> &t2: Array<U32> ->
         {t1 == tbl : Array<U32>} & {t2 == t1 : Array<U32>}) ->
  FH.FH.GuessSpec(G, C, n_root, True{}, True{}, g, SolveFast.cwords_words(S), n,
    floor, best,
    SolveFast.schedule5_hist(row, g, FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}),
      S, n, best, bkts, gen,
      SolveFast.hist5_go(row, S, gen, skip_self,
        SolveFast.Hist5Ok{seen, tbl, 0n, 0n,
          SolveFast.budget_for(n, best, skip_self)}))):
  (s1, dps2) = dps
  (s2, pes) = dps2
  (+es1, +es2) = pes
  (t1, dpt2) = dpt
  (t2, pet) = dpt2
  (+et1, +et2) = pet
  +gG = FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{})
  +ws = SolveFast.cwords_words(S)
  +budget0 = SolveFast.budget_for(n, best, skip_self)
  +es2_s : {s2 == seen : Array<Nat>} = Equal.trans(Array<Nat>, s2, s1, seen, es2, es1)
  +et2_t : {t2 == tbl : Array<U32>} = Equal.trans(Array<U32>, t2, t1, tbl, et2, et1)
  +hs2 = FH.FH.seen_tree_transport(10n, 0, seen, s2, gen, Nil{},
           Equal.sym(Array<Nat>, s2, seen, es2_s), hs)
  +ht2 = FT.FT.tbl_ok_transport(G, C, n_root, tbl, t2,
           Equal.sym(Array<U32>, t2, tbl, et2_t), htbl)
  +hhr2 = FH.FH.hist5_go_spec(S, G, C, n_root, row, g, Nil{}, s2, t2, gen, 0n,
            0n, budget0, budget0, skip_self, ht2, hrow, hS, {==}, {==}, {==},
            {==}, hs2)
  +hhr_t0 = FH.FH.hist_spec_transport_tbl(g, ws, Nil{}, gen, budget0, skip_self,
              t2, tbl,
              SolveFast.hist5_go(row, S, gen, skip_self,
                SolveFast.Hist5Ok{s2, t2, 0n, 0n, budget0}), et2_t, hhr2)
  +eq_12 : {SolveFast.hist5_go(row, S, gen, skip_self,
              SolveFast.Hist5Ok{s2, t2, 0n, 0n, budget0})
            == SolveFast.hist5_go(row, S, gen, skip_self,
                 SolveFast.Hist5Ok{s1, t1, 0n, 0n, budget0})
            : SolveFast.Hist5Res} =
    Equal.trans(SolveFast.Hist5Res,
      SolveFast.hist5_go(row, S, gen, skip_self,
        SolveFast.Hist5Ok{s2, t2, 0n, 0n, budget0}),
      SolveFast.hist5_go(row, S, gen, skip_self,
        SolveFast.Hist5Ok{s1, t2, 0n, 0n, budget0}),
      SolveFast.hist5_go(row, S, gen, skip_self,
        SolveFast.Hist5Ok{s1, t1, 0n, 0n, budget0}),
      Equal.cong(Array<Nat>, SolveFast.Hist5Res,
        x => SolveFast.hist5_go(row, S, gen, skip_self,
               SolveFast.Hist5Ok{x, t2, 0n, 0n, budget0}), s2, s1, es2),
      Equal.cong(Array<U32>, SolveFast.Hist5Res,
        y => SolveFast.hist5_go(row, S, gen, skip_self,
               SolveFast.Hist5Ok{s1, y, 0n, 0n, budget0}), t2, t1, et2))
  +hhr1 = FH.FH.hist_spec_transport(g, ws, Nil{}, gen, budget0, skip_self, tbl,
            SolveFast.hist5_go(row, S, gen, skip_self,
              SolveFast.Hist5Ok{s2, t2, 0n, 0n, budget0}),
            SolveFast.hist5_go(row, S, gen, skip_self,
              SolveFast.Hist5Ok{s1, t1, 0n, 0n, budget0}), eq_12, hhr_t0)
  %es1 : FH.FH.GuessSpec(G, C, n_root, True{}, True{}, g, ws, n, floor, best,
           SolveFast.schedule5_hist(row, g, gG, S, n, best, bkts, gen,
             SolveFast.hist5_go(row, S, gen, skip_self,
               SolveFast.Hist5Ok{_, tbl, 0n, 0n, budget0})))
  %et1 : FH.FH.GuessSpec(G, C, n_root, True{}, True{}, g, ws, n, floor, best,
           SolveFast.schedule5_hist(row, g, gG, S, n, best, bkts, gen,
             SolveFast.hist5_go(row, S, gen, skip_self,
               SolveFast.Hist5Ok{s1, _, 0n, 0n, budget0})))
  FTight.schedule5_hist_spec(rwsG, G, C, n_root, row, g, S, n, floor, best,
    skip_self, bkts, tbl, gen,
    SolveFast.hist5_go(row, S, gen, skip_self,
      SolveFast.Hist5Ok{s1, t1, 0n, 0n, budget0}),
    erwsG, hrwsG, esk, hge1, en, hnd_s, hrow, hS, hb, htbl, hhr1)

def FTight.guess_body_buf_ge2_spec(+rwsG: +List<FT.FT.RowWord>,
    +G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n_root: Nat,
    has_buf: Bool, +row: U32, +g: +List<Nat>, +S: +List<SolveFast.CWord>,
    +n: Nat, +floor: Nat, +best: SolveRef.Best, +skip_self: Bool,
    buf: SolveFast.Buf5,
    +erwsG: {FT.FT.rws_words(rwsG) == G : +List<+List<Nat>>},
    +hrwsG: {FH.FH.rws_ok_if(has_buf, G, n_root, rwsG) == True{} : Bool},
    +esk: {skip_self == Nat.is_eq(floor, Nat.add(n, n)) : Bool},
    +hge1: {Nat.is_le(1n, n) == True{} : Bool},
    +en: {n == Groups.len_words(SolveFast.cwords_words(S)) : Nat},
    +hnd_s: {FN.FN.no_dup_ref(SolveFast.cwords_words(S)) == True{} : Bool},
    +hrow: {FH.FH.gentry_ok_if(has_buf, G, n_root, row, g) == True{} : Bool},
    +hS: {FH.FH.cwords_ok_if(has_buf, G, C, n_root, S) == True{} : Bool},
    +hbuf: FH.FH.BufOk(G, C, n_root, has_buf, True{}, buf)) ->
  FH.FH.GuessSpec(G, C, n_root, has_buf, True{}, g, SolveFast.cwords_words(S), n,
    floor, best,
    SolveFast.guess_body_buf_ge2(row, g,
      FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), S, n, best, skip_self, buf)):
  match has_buf:
    case False{}:
      match buf:
        case SolveFast.NoBuf{}:
          Arr.DPair{
            FH.FH.schedule_fguess_fast_wit(G, C, n_root, True{}, g,
              SolveFast.cwords_words(S), n, floor, best, en, hnd_s),
            Unit{}}
        case SolveFast.Buf5{s0, k0, t0, g0}:
          Empty.absurd(
            FH.FH.GuessSpec(G, C, n_root, False{}, True{}, g,
              SolveFast.cwords_words(S), n, floor, best,
              SolveFast.guess_body_buf_ge2(row, g,
                FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), S, n, best,
                skip_self, SolveFast.Buf5{s0, k0, t0, g0})), hbuf)
    case True{}:
      match buf:
        case SolveFast.NoBuf{}:
          Empty.absurd(
            FH.FH.GuessSpec(G, C, n_root, True{}, True{}, g,
              SolveFast.cwords_words(S), n, floor, best,
              SolveFast.guess_body_buf_ge2(row, g,
                FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), S, n, best,
                skip_self, SolveFast.NoBuf{})), hbuf)
        case SolveFast.Buf5{seen, bkts, tbl, +gen}:
          +r1 = Arr.Arr.dpair_r({True{} == True{} : Bool},
                  Arr.Arr.DPair<FH.FH.SeenTree(10n, 0, seen, gen, Nil{}),
                    Arr.Arr.DPair<FH.FH.BktTree(G, C, n_root, 10n, 0, bkts, Nil{}),
                      FT.FT.TblOk(G, C, n_root, tbl)>>, hbuf)
          +hs = Arr.Arr.dpair_l(FH.FH.SeenTree(10n, 0, seen, gen, Nil{}),
                  Arr.Arr.DPair<FH.FH.BktTree(G, C, n_root, 10n, 0, bkts, Nil{}),
                    FT.FT.TblOk(G, C, n_root, tbl)>, r1)
          +r2 = Arr.Arr.dpair_r(FH.FH.SeenTree(10n, 0, seen, gen, Nil{}),
                  Arr.Arr.DPair<FH.FH.BktTree(G, C, n_root, 10n, 0, bkts, Nil{}),
                    FT.FT.TblOk(G, C, n_root, tbl)>, r1)
          +hb = Arr.Arr.dpair_l(FH.FH.BktTree(G, C, n_root, 10n, 0, bkts, Nil{}),
                  FT.FT.TblOk(G, C, n_root, tbl), r2)
          +htbl = Arr.Arr.dpair_r(FH.FH.BktTree(G, C, n_root, 10n, 0, bkts, Nil{}),
                    FT.FT.TblOk(G, C, n_root, tbl), r2)
          FTight.guess_body_buf5_dup(rwsG, G, C, n_root, row, g, S, n, floor,
            best, skip_self, seen, bkts, tbl, gen, erwsG, hrwsG, esk, hge1, en,
            hnd_s, hrow, hS, hs, hb, htbl, Arr.Arr.dup(Nat, seen),
            Arr.Arr.dup(U32, tbl))

def FTight.guess_body_buf_spec(+rwsG: +List<FT.FT.RowWord>,
    +G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n_root: Nat,
    +has_buf: Bool, +row: U32, +g: +List<Nat>, +S: +List<SolveFast.CWord>,
    +n: Nat, +floor: Nat, +best: SolveRef.Best, +skip_self: Bool,
    buf: SolveFast.Buf5,
    +erwsG: {FT.FT.rws_words(rwsG) == G : +List<+List<Nat>>},
    +hrwsG: {FH.FH.rws_ok_if(has_buf, G, n_root, rwsG) == True{} : Bool},
    +esk: {skip_self == Nat.is_eq(floor, Nat.add(n, n)) : Bool},
    +en: {n == Groups.len_words(SolveFast.cwords_words(S)) : Nat},
    +hnd_s: {FN.FN.no_dup_ref(SolveFast.cwords_words(S)) == True{} : Bool},
    +hrow: {FH.FH.gentry_ok_if(has_buf, G, n_root, row, g) == True{} : Bool},
    +hS: {FH.FH.cwords_ok_if(has_buf, G, C, n_root, S) == True{} : Bool},
    +hbuf: FH.FH.BufOk(G, C, n_root, has_buf, True{}, buf)) ->
  FH.FH.GuessSpec(G, C, n_root, has_buf, True{}, g, SolveFast.cwords_words(S), n,
    floor, best,
    SolveFast.guess_body_buf(row, g, FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}),
      S, n, best, skip_self, buf)):
  match S:
    case Nil{}:
      %Equal.sym(Nat, n, 0n, en) :
        FH.FH.GuessSpec(G, C, n_root, has_buf, True{}, g, Nil{}, _, floor, best,
          SolveFast.GuessRes{
            SolveFast.schedule_fguess_lb(True{}, g, Nil{}, 0n,
              SolveFast.skippable(best, 0n)), buf})
      Arr.DPair{
        FH.FH.schedule_nil_wit(G, C, n_root, has_buf, True{}, g, floor, best,
          SolveFast.skippable(best, 0n), {==}), hbuf}
    case Con{cw, +t}:
      match cw:
        case SolveFast.CWord{+ci, +grow, +w}:
          match t:
            case Nil{}:
              %Equal.sym(Nat, n, 1n, en) :
                FH.FH.GuessSpec(G, C, n_root, has_buf, True{}, g, w <> Nil{}, _,
                  floor, best,
                  SolveFast.GuessRes{
                    SolveFast.schedule_one_guess(g, best,
                      SolveFast.word_eq_fast(g, w)), buf})
              Arr.DPair{
                FH.FH.schedule_one_wit(G, C, n_root, has_buf, True{}, g, w,
                  floor, best, SolveFast.word_eq_fast(g, w), {==}), hbuf}
            case Con{cw2, +t2}:
              match cw2:
                case SolveFast.CWord{+ci2, +grow2, +w2}:
                  +cw1 : SolveFast.CWord = SolveFast.CWord{ci, grow, w}
                  +cw2a : SolveFast.CWord = SolveFast.CWord{ci2, grow2, w2}
                  +hge1 : {Nat.is_le(1n, n) == True{} : Bool} =
                    Equal.cong(Nat, Bool, x => Nat.is_le(1n, x),
                      n, 1n+(1n+Groups.len_words(SolveFast.cwords_words(t2))),
                      en)
                  FTight.guess_body_buf_ge2_spec(rwsG, G, C, n_root, has_buf,
                    row, g, cw1 <> (cw2a <> t2), n, floor, best, skip_self, buf,
                    erwsG, hrwsG, esk, hge1, en, hnd_s, hrow, hS, hbuf)

def FTight.guess_items_mem_buf_spec(+rwsG: +List<FT.FT.RowWord>,
    +G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n_root: Nat,
    +has_buf: Bool, +row: U32, +g: +List<Nat>, +S: +List<SolveFast.CWord>,
    +n: Nat, +floor: Nat, +best: SolveRef.Best, +skip_self: Bool,
    buf: SolveFast.Buf5, in_s: Bool,
    +ein: {in_s == SolveFast.member_word_fast(g, SolveFast.cwords_words(S))
           : Bool},
    +ele2n: {SolveFast.skippable(best, Nat.add(n, n)) == True{} : Bool},
    +erwsG: {FT.FT.rws_words(rwsG) == G : +List<+List<Nat>>},
    +hrwsG: {FH.FH.rws_ok_if(has_buf, G, n_root, rwsG) == True{} : Bool},
    +esk: {skip_self == Nat.is_eq(floor, Nat.add(n, n)) : Bool},
    +en: {n == Groups.len_words(SolveFast.cwords_words(S)) : Nat},
    +hnd_s: {FN.FN.no_dup_ref(SolveFast.cwords_words(S)) == True{} : Bool},
    +hrow: {FH.FH.gentry_ok_if(has_buf, G, n_root, row, g) == True{} : Bool},
    +hS: {FH.FH.cwords_ok_if(has_buf, G, C, n_root, S) == True{} : Bool},
    +hbuf: FH.FH.BufOk(G, C, n_root, has_buf, True{}, buf)) ->
  FH.FH.GuessSpec(G, C, n_root, has_buf, True{}, g, SolveFast.cwords_words(S), n,
    floor, best,
    SolveFast.guess_items_mem_buf(row, g,
      FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), S, n, best, skip_self, buf,
      in_s)):
  match in_s:
    case True{}:
      FTight.guess_body_buf_spec(rwsG, G, C, n_root, has_buf, row, g, S, n,
        floor, best, skip_self, buf, erwsG, hrwsG, esk, en, hnd_s, hrow, hS,
        hbuf)
    case False{}:
      +ws = SolveFast.cwords_words(S)
      +hnm : {Tree.member_word(g, ws) == False{} : Bool} =
        Equal.trans(Bool, Tree.member_word(g, ws),
          SolveFast.member_word_fast(g, ws), False{},
          Equal.sym(Bool, SolveFast.member_word_fast(g, ws),
            Tree.member_word(g, ws), FO.FO.member_word_fast_eq(g, ws)),
          Equal.sym(Bool, False{}, SolveFast.member_word_fast(g, ws), ein))
      +epre : {Nat.add(n, n) == SolveFast.pre_lb(n, g, ws) : Nat} =
        Equal.cong(Nat, Nat, x => Nat.add(n, x),
          n, SolveFast.keep_fast(g, ws),
          Equal.trans(Nat, n, Groups.len_words(ws), SolveFast.keep_fast(g, ws),
            en,
            Equal.sym(Nat, SolveFast.keep_fast(g, ws), Groups.len_words(ws),
              FN.FN.keep_of_not_member(g, ws, hnm))))
      +hle : {Nat.is_le(Eval.Eval.cost_of(best), SolveFast.pre_lb(n, g, ws))
              == True{} : Bool} =
        NatProof.Nat.is_le_eq_r(Eval.Eval.cost_of(best), Nat.add(n, n),
          SolveFast.pre_lb(n, g, ws), epre,
          FLB.FS.skippable_to_le(best, Nat.add(n, n), ele2n))
      Arr.DPair{FH.GWit{FH.GCSkipPre{}, Arr.DPair{{==}, hle}}, hbuf}

def FTight.guess_items_nodup_buf_spec(+rwsG: +List<FT.FT.RowWord>,
    +G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n_root: Nat,
    +has_buf: Bool, +row: U32, +g: +List<Nat>, +S: +List<SolveFast.CWord>,
    +n: Nat, +floor: Nat, +best: SolveRef.Best, +skip_self: Bool,
    buf: SolveFast.Buf5, le_2n: Bool,
    +e2n: {le_2n == SolveFast.skippable(best, Nat.add(n, n)) : Bool},
    +erwsG: {FT.FT.rws_words(rwsG) == G : +List<+List<Nat>>},
    +hrwsG: {FH.FH.rws_ok_if(has_buf, G, n_root, rwsG) == True{} : Bool},
    +esk: {skip_self == Nat.is_eq(floor, Nat.add(n, n)) : Bool},
    +en: {n == Groups.len_words(SolveFast.cwords_words(S)) : Nat},
    +hnd_s: {FN.FN.no_dup_ref(SolveFast.cwords_words(S)) == True{} : Bool},
    +hrow: {FH.FH.gentry_ok_if(has_buf, G, n_root, row, g) == True{} : Bool},
    +hS: {FH.FH.cwords_ok_if(has_buf, G, C, n_root, S) == True{} : Bool},
    +hbuf: FH.FH.BufOk(G, C, n_root, has_buf, True{}, buf)) ->
  FH.FH.GuessSpec(G, C, n_root, has_buf, True{}, g, SolveFast.cwords_words(S), n,
    floor, best,
    SolveFast.guess_items_nodup_buf(row, g,
      FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), S, n, best, skip_self, buf,
      le_2n)):
  match le_2n:
    case False{}:
      FTight.guess_body_buf_spec(rwsG, G, C, n_root, has_buf, row, g, S, n,
        floor, best, skip_self, buf, erwsG, hrwsG, esk, en, hnd_s, hrow, hS,
        hbuf)
    case True{}:
      FTight.guess_items_mem_buf_spec(rwsG, G, C, n_root, has_buf, row, g, S, n,
        floor, best, skip_self, buf,
        SolveFast.member_word_fast(g, SolveFast.cwords_words(S)), {==},
        Equal.sym(Bool, True{}, SolveFast.skippable(best, Nat.add(n, n)), e2n),
        erwsG, hrwsG, esk, en, hnd_s, hrow, hS, hbuf)

# Main theorem: `guess_items_buf` satisfies the 6-case `FH.GuessSpec` and
# preserves `FH.BufOk`.
def FTight.guess_items_buf_spec(+rwsG: +List<FT.FT.RowWord>,
    +G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n_root: Nat,
    +has_buf: Bool, +nodup: Bool, +row: U32, +g: +List<Nat>,
    +S: +List<SolveFast.CWord>, +n: Nat, +floor: Nat, +best: SolveRef.Best,
    buf: SolveFast.Buf5,
    +erwsG: {FT.FT.rws_words(rwsG) == G : +List<+List<Nat>>},
    +hrwsG: {FH.FH.rws_ok_if(has_buf, G, n_root, rwsG) == True{} : Bool},
    +en: {n == Groups.len_words(SolveFast.cwords_words(S)) : Nat},
    +hnd: {FN.FN.nodup_ok(nodup, SolveFast.cwords_words(S)) == True{} : Bool},
    +hrow: {FH.FH.gentry_ok_if(has_buf, G, n_root, row, g) == True{} : Bool},
    +hS: {FH.FH.cwords_ok_if(has_buf, G, C, n_root, S) == True{} : Bool},
    +hbuf: FH.FH.BufOk(G, C, n_root, has_buf, nodup, buf)) ->
  FH.FH.GuessSpec(G, C, n_root, has_buf, nodup, g, SolveFast.cwords_words(S), n,
    floor, best,
    SolveFast.guess_items_buf(nodup, row, g,
      FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), S, n, floor, best, buf)):
  match nodup:
    case True{}:
      FTight.guess_items_nodup_buf_spec(rwsG, G, C, n_root, has_buf, row, g, S,
        n, floor, best, Nat.is_eq(floor, Nat.add(n, n)), buf,
        SolveFast.skippable(best, Nat.add(n, n)), {==}, erwsG, hrwsG, {==}, en,
        hnd, hrow, hS, hbuf)
    case False{}:
      FH.FH.guess_items_buf_false_spec(G, C, n_root, has_buf, g, S, n, floor,
        best, buf, en, hbuf)
