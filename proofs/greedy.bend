# Soundness of table-backed greedy(lb) upper-bound seeding and root guess
# presorting (`src/greedy.bend`).
#
# Proves for `Greedy.root_prepare`:
# 1. `GR.greedy_phase1_ok` and `GR.gjobs_ok`: every `GreedyOk{tree, cost, buf2}`
#    returned by `Greedy.greedy_step` is a valid decision tree (`FV.valid_b`)
#    whose true cost on `S` is at most `cost`, and preserves `FH.BufOk`.
# 2. `GR.rsort_fill_ok` and `GR.drain_tree_ok`: root Pass-1 bucket sorting
#    returns a list `rgs` of valid, usable `RootGuess` entries containing every
#    usable guess from `G`, while preserving `FH.SeenTree` and `FT.TblOk`.
# 3. `GR.root_prepare_spec`: combines both phases (and the `NoBuf{}` fallback),
#    producing an acceptable initial bound `b0`, a valid root guess list `rgs`
#    covering every usable guess in `G`, and a valid `Buf5`.
import Base
import ../src/feedback.bend as Feedback
import ../src/tree.bend as Tree
import ../src/groups.bend as Groups
import ../src/solve_ref.bend as SolveRef
import ../src/solve_fast.bend as SolveFast
import ../src/greedy.bend as Greedy
import ./logic.bend as Logic
import ./nat.bend as NatProof
import ./feedback.bend as FbProof
import ./eval.bend as Eval
import ./groupsmeasure.bend as GM
import ./classbound_nat.bend as CBN
import ./optfold.bend as Fold
import ./mainvalid.bend as MV
import ./cover_list.bend as CoverList
import ./cover_groups.bend as CoverGroups
import ./array.bend as Arr
import ./fast_one.bend as FO
import ./fast_nodup.bend as FN
import ./fast_perm.bend as FP
import ./fast_tbl.bend as FT
import ./fast_hist5.bend as FH
import ./fast_valid.bend as FVal
import ./fast_opt.bend as FOpt

# ---------------------------------------------------------------------------
# Section 1: `RootGuess` list helpers and word membership
# ---------------------------------------------------------------------------

def GR.rgs_words(+rgs: +List<Greedy.RootGuess>) -> +List<+List<Nat>>:
  match rgs:
    case Nil{}:
      Nil{}
    case Con{rg, rest}:
      match rg:
        case Greedy.RootGuess{row, g}:
          g <> GR.rgs_words(rest)

def GR.rgs_to_rws(+rgs: +List<Greedy.RootGuess>) -> +List<FT.FT.RowWord>:
  match rgs:
    case Nil{}:
      Nil{}
    case Con{rg, rest}:
      match rg:
        case Greedy.RootGuess{row, g}:
          FT.RowWord{row, g} <> GR.rgs_to_rws(rest)

def GR.rgs_to_rws_words(+rgs: +List<Greedy.RootGuess>) ->
  {FT.FT.rws_words(GR.rgs_to_rws(rgs)) == GR.rgs_words(rgs) : +List<+List<Nat>>}:
  match rgs:
    case Nil{}:
      {==}
    case Con{rg, rest}:
      match rg:
        case Greedy.RootGuess{+row, +g}:
          Equal.cong(+List<+List<Nat>>, +List<+List<Nat>>, l => g <> l,
            FT.FT.rws_words(GR.rgs_to_rws(rest)), GR.rgs_words(rest),
            GR.rgs_to_rws_words(rest))

def GR.glist_of_rgs_eq(+rgs: +List<Greedy.RootGuess>) ->
  {Greedy.glist_of_rgs(rgs)
   == FT.FT.glist_of_rws(GR.rgs_to_rws(rgs), SolveFast.GEnd{})
   : SolveFast.GList}:
  match rgs:
    case Nil{}:
      {==}
    case Con{rg, rest}:
      match rg:
        case Greedy.RootGuess{+row, +g}:
          Equal.cong(SolveFast.GList, SolveFast.GList,
            gl => SolveFast.GTry{row, g, gl},
            Greedy.glist_of_rgs(rest),
            FT.FT.glist_of_rws(GR.rgs_to_rws(rest), SolveFast.GEnd{}),
            GR.glist_of_rgs_eq(rest))

def GR.rg_ok_b(+has_buf: Bool, +G: +List<+List<Nat>>, +n_root: Nat,
    +rg: Greedy.RootGuess) -> Bool:
  match rg:
    case Greedy.RootGuess{row, g}:
      Bool.and(FH.FH.gentry_ok_if(has_buf, G, n_root, row, g),
        Tree.member_word(g, G))

def GR.rgs_ok_b(+has_buf: Bool, +G: +List<+List<Nat>>, +n_root: Nat,
    +rgs: +List<Greedy.RootGuess>) -> Bool:
  match rgs:
    case Nil{}:
      True{}
    case Con{rg, rest}:
      Bool.and(GR.rg_ok_b(has_buf, G, n_root, rg),
        GR.rgs_ok_b(has_buf, G, n_root, rest))

def GR.rgs_usable_b(+S: +List<+List<Nat>>,
    +rgs: +List<Greedy.RootGuess>) -> Bool:
  match rgs:
    case Nil{}:
      True{}
    case Con{rg, rest}:
      match rg:
        case Greedy.RootGuess{row, g}:
          Bool.and(Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
            GR.rgs_usable_b(S, rest))

def GR.rgs_ok_to_rws_true(+G: +List<+List<Nat>>, +n_root: Nat,
    +rgs: +List<Greedy.RootGuess>,
    +h: {GR.rgs_ok_b(True{}, G, n_root, rgs) == True{} : Bool}) ->
  {FT.FT.rws_ok_b(G, n_root, GR.rgs_to_rws(rgs)) == True{} : Bool}:
  match rgs:
    case Nil{}:
      {==}
    case Con{rg, rest}:
      match rg:
        case Greedy.RootGuess{+row, +g}:
          +h1 = Logic.Proof.and_true_l(
                  Bool.and(FT.FT.gentry_ok_b(G, n_root, row, g),
                    Tree.member_word(g, G)),
                  GR.rgs_ok_b(True{}, G, n_root, rest), h)
          +hr = Logic.Proof.and_true_r(
                  Bool.and(FT.FT.gentry_ok_b(G, n_root, row, g),
                    Tree.member_word(g, G)),
                  GR.rgs_ok_b(True{}, G, n_root, rest), h)
          +he = Logic.Proof.and_true_l(FT.FT.gentry_ok_b(G, n_root, row, g),
                  Tree.member_word(g, G), h1)
          FO.FO.bool_and_intro(FT.FT.gentry_ok_b(G, n_root, row, g),
            FT.FT.rws_ok_b(G, n_root, GR.rgs_to_rws(rest)), he,
            GR.rgs_ok_to_rws_true(G, n_root, rest, hr))

def GR.rgs_ok_to_rws(has_buf: Bool, +G: +List<+List<Nat>>, +n_root: Nat,
    +rgs: +List<Greedy.RootGuess>,
    +h: {GR.rgs_ok_b(has_buf, G, n_root, rgs) == True{} : Bool}) ->
  {FH.FH.rws_ok_if(has_buf, G, n_root, GR.rgs_to_rws(rgs)) == True{} : Bool}:
  match has_buf:
    case False{}:
      {==}
    case True{}:
      GR.rgs_ok_to_rws_true(G, n_root, rgs, h)

def GR.rgs_ok_to_all_in(+has_buf: Bool, +G: +List<+List<Nat>>, +n_root: Nat,
    +rgs: +List<Greedy.RootGuess>,
    +h: {GR.rgs_ok_b(has_buf, G, n_root, rgs) == True{} : Bool}) ->
  {FO.FO.all_in_ref(GR.rgs_words(rgs), G) == True{} : Bool}:
  match rgs:
    case Nil{}:
      {==}
    case Con{rg, rest}:
      match rg:
        case Greedy.RootGuess{+row, +g}:
          +h1 = Logic.Proof.and_true_l(
                  Bool.and(FH.FH.gentry_ok_if(has_buf, G, n_root, row, g),
                    Tree.member_word(g, G)),
                  GR.rgs_ok_b(has_buf, G, n_root, rest), h)
          +hr = Logic.Proof.and_true_r(
                  Bool.and(FH.FH.gentry_ok_if(has_buf, G, n_root, row, g),
                    Tree.member_word(g, G)),
                  GR.rgs_ok_b(has_buf, G, n_root, rest), h)
          +hm = Logic.Proof.and_true_r(
                  FH.FH.gentry_ok_if(has_buf, G, n_root, row, g),
                  Tree.member_word(g, G), h1)
          FO.FO.bool_and_intro(Tree.member_word(g, G),
            FO.FO.all_in_ref(GR.rgs_words(rest), G), hm,
            GR.rgs_ok_to_all_in(has_buf, G, n_root, rest, hr))

def GR.rgs_of_G_words(+G: +List<+List<Nat>>, +row: U32) ->
  {GR.rgs_words(Greedy.rgs_of_G(G, row)) == G : +List<+List<Nat>>}:
  match G:
    case Nil{}:
      {==}
    case Con{+g, +rest}:
      Equal.cong(+List<+List<Nat>>, +List<+List<Nat>>, l => g <> l,
        GR.rgs_words(Greedy.rgs_of_G(rest, U32.add(row, 1))), rest,
        GR.rgs_of_G_words(rest, U32.add(row, 1)))

def GR.rgs_of_G_ok_go(+G: +List<+List<Nat>>, +rem: +List<+List<Nat>>,
    +n_root: Nat, +row: U32,
    +hai: {FO.FO.all_in_ref(rem, G) == True{} : Bool}) ->
  {GR.rgs_ok_b(False{}, G, n_root, Greedy.rgs_of_G(rem, row))
   == True{} : Bool}:
  match rem:
    case Nil{}:
      {==}
    case Con{+g, +rest}:
      +hg = FO.FO.all_in_head(g, rest, G, hai)
      +hr = FO.FO.all_in_tail(g, rest, G, hai)
      FO.FO.bool_and_intro(Tree.member_word(g, G),
        GR.rgs_ok_b(False{}, G, n_root,
          Greedy.rgs_of_G(rest, U32.add(row, 1))),
        hg, GR.rgs_of_G_ok_go(G, rest, n_root, U32.add(row, 1), hr))

def GR.all_in_sub(+xs: +List<+List<Nat>>, +ys: +List<+List<Nat>>,
    +w: +List<Nat>,
    +h: {FO.FO.all_in_ref(xs, ys) == True{} : Bool}) ->
  {FO.FO.all_in_ref(xs, w <> ys) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +hx = FO.FO.all_in_head(x, t, ys, h)
      +ht = FO.FO.all_in_tail(x, t, ys, h)
      FO.FO.bool_and_intro(Tree.member_word(x, w <> ys),
        FO.FO.all_in_ref(t, w <> ys),
        FN.FN.member_cons_r(x, w, ys, hx),
        GR.all_in_sub(t, ys, w, ht))

def GR.all_in_refl(+G: +List<+List<Nat>>) ->
  {FO.FO.all_in_ref(G, G) == True{} : Bool}:
  match G:
    case Nil{}:
      {==}
    case Con{+w, +t}:
      +hw : {Tree.member_word(w, w <> t) == True{} : Bool} =
        Equal.cong(Bool, Bool,
          b => Feedback.Bool.case(Bool, b, True{}, Tree.member_word(w, t)),
          Feedback.word_eq(w, w), True{}, FbProof.FbPrf.word_eq_refl(w))
      FO.FO.bool_and_intro(Tree.member_word(w, w <> t),
        FO.FO.all_in_ref(t, w <> t), hw,
        GR.all_in_sub(t, t, w, GR.all_in_refl(t)))

def GR.member_cons_l(+w: +List<Nat>, +h: +List<Nat>, +t: +List<+List<Nat>>,
    +e: {Feedback.word_eq(w, h) == True{} : Bool}) ->
  {Tree.member_word(w, h <> t) == True{} : Bool}:
  Equal.cong(Bool, Bool,
    b => Feedback.Bool.case(Bool, b, True{}, Tree.member_word(w, t)),
    Feedback.word_eq(w, h), True{}, e)

def GR.member_cons_split_go(-R: Type, +w: +List<Nat>, +h: +List<Nat>,
    +t: +List<+List<Nat>>, eq: Bool,
    +eeq: {eq == Feedback.word_eq(w, h) : Bool},
    +hm: {Feedback.Bool.case(Bool, eq, True{}, Tree.member_word(w, t))
          == True{} : Bool},
    kl: {w == h : +List<Nat>} -> R,
    kr: {Tree.member_word(w, t) == True{} : Bool} -> R) -> R:
  match eq:
    case True{}:
      kl(CoverList.Cover.word_eq_true(w, h,
        Equal.sym(Bool, True{}, Feedback.word_eq(w, h), eeq)))
    case False{}:
      kr(hm)

def GR.member_cons_split(-R: Type, +w: +List<Nat>, +h: +List<Nat>,
    +t: +List<+List<Nat>>,
    +hm: {Tree.member_word(w, h <> t) == True{} : Bool},
    kl: {w == h : +List<Nat>} -> R,
    kr: {Tree.member_word(w, t) == True{} : Bool} -> R) -> R:
  GR.member_cons_split_go(R, w, h, t, Feedback.word_eq(w, h), {==}, hm, kl, kr)

def GR.nat_is_eq_cases(-R: Type, +a: Nat, +b: Nat, eq: Bool,
    +eeq: {eq == Nat.is_eq(a, b) : Bool},
    kl: {a == b : Nat} -> R,
    kr: {Nat.is_eq(a, b) == False{} : Bool} -> R) -> R:
  match eq:
    case True{}:
      kl(NatProof.NatPrf.is_eq_true(a, b,
        Equal.sym(Bool, True{}, Nat.is_eq(a, b), eeq)))
    case False{}:
      kr(Equal.sym(Bool, False{}, Nat.is_eq(a, b), eeq))

def GR.nat_lt_of_lt_succ_ne(a: Nat, p: Nat,
    +hlt: {Nat.is_lt(a, 1n+p) == True{} : Bool},
    +hne: {Nat.is_eq(a, p) == False{} : Bool}) ->
  {Nat.is_lt(a, p) == True{} : Bool}:
  match a p:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool},
        Logic.Proof.true_ne_false(hne))
    case 0n 1n+pp:
      {==}
    case 1n+ap 0n:
      Empty.absurd({Nat.is_lt(1n+ap, 0n) == True{} : Bool},
        Logic.Proof.false_ne_true(
          Equal.trans(Bool, False{}, Nat.is_lt(ap, 0n), True{},
            Equal.sym(Bool, Nat.is_lt(ap, 0n), False{},
              FT.FT.nat_lt_zero_false(ap)), hlt)))
    case 1n+ap 1n+pp:
      GR.nat_lt_of_lt_succ_ne(ap, pp, hlt, hne)

def GR.with_dup_arr_go(-T: Data, -R: Type, -a: Array<T>,
    dp: &a1: Array<T> -> &a2: Array<T> ->
        {a1 == a : Array<T>} & {a2 == a1 : Array<T>},
    k: @a1: Array<T> -> @a2: Array<T> ->
       {a1 == a : Array<T>} -> {a2 == a : Array<T>} -> R) -> R:
  (a1, dp2) = dp
  (a2, pe) = dp2
  (+ea1, +ea2) = pe
  k(a1, a2, ea1, Equal.trans(Array<T>, a2, a1, a, ea2, ea1))

def GR.with_dup_arr(-T: Data, -R: Type, a: Array<T>,
    k: @a1: Array<T> -> @a2: Array<T> ->
       {a1 == a : Array<T>} -> {a2 == a : Array<T>} -> R) -> R:
  GR.with_dup_arr_go(T, R, a, Arr.Arr.dup(T, a), k)

def GR.with_dup_buf(-R: Type, buf: SolveFast.Buf5,
    k: @b1: SolveFast.Buf5 -> @b2: SolveFast.Buf5 ->
       {b1 == buf : SolveFast.Buf5} -> {b2 == buf : SolveFast.Buf5} -> R) -> R:
  match buf:
    case SolveFast.NoBuf{}:
      k(SolveFast.NoBuf{}, SolveFast.NoBuf{}, {==}, {==})
    case SolveFast.Buf5{seen, bkts, tbl, +gen}:
      GR.with_dup_arr(Nat, R, seen,
        s1 => s2 => +es1 => +es2 =>
        GR.with_dup_arr(+List<SolveFast.CWord>, R, bkts,
          b1 => b2 => +eb1 => +eb2 =>
          GR.with_dup_arr(U32, R, tbl,
            t1 => t2 => +et1 => +et2 =>
            +e1 : {SolveFast.Buf5{s1, b1, t1, gen}
                   == SolveFast.Buf5{seen, bkts, tbl, gen} : SolveFast.Buf5} =
              Equal.trans(SolveFast.Buf5,
                SolveFast.Buf5{s1, b1, t1, gen},
                SolveFast.Buf5{seen, b1, t1, gen},
                SolveFast.Buf5{seen, bkts, tbl, gen},
                Equal.cong(Array<Nat>, SolveFast.Buf5,
                  x => SolveFast.Buf5{x, b1, t1, gen}, s1, seen, es1),
                Equal.trans(SolveFast.Buf5,
                  SolveFast.Buf5{seen, b1, t1, gen},
                  SolveFast.Buf5{seen, bkts, t1, gen},
                  SolveFast.Buf5{seen, bkts, tbl, gen},
                  Equal.cong(Array<+List<SolveFast.CWord>>, SolveFast.Buf5,
                    x => SolveFast.Buf5{seen, x, t1, gen}, b1, bkts, eb1),
                  Equal.cong(Array<U32>, SolveFast.Buf5,
                    x => SolveFast.Buf5{seen, bkts, x, gen}, t1, tbl, et1)))
            +e2 : {SolveFast.Buf5{s2, b2, t2, gen}
                   == SolveFast.Buf5{seen, bkts, tbl, gen} : SolveFast.Buf5} =
              Equal.trans(SolveFast.Buf5,
                SolveFast.Buf5{s2, b2, t2, gen},
                SolveFast.Buf5{seen, b2, t2, gen},
                SolveFast.Buf5{seen, bkts, tbl, gen},
                Equal.cong(Array<Nat>, SolveFast.Buf5,
                  x => SolveFast.Buf5{x, b2, t2, gen}, s2, seen, es2),
                Equal.trans(SolveFast.Buf5,
                  SolveFast.Buf5{seen, b2, t2, gen},
                  SolveFast.Buf5{seen, bkts, t2, gen},
                  SolveFast.Buf5{seen, bkts, tbl, gen},
                  Equal.cong(Array<+List<SolveFast.CWord>>, SolveFast.Buf5,
                    x => SolveFast.Buf5{seen, x, t2, gen}, b2, bkts, eb2),
                  Equal.cong(Array<U32>, SolveFast.Buf5,
                    x => SolveFast.Buf5{seen, bkts, x, gen}, t2, tbl, et2)))
            k(SolveFast.Buf5{s1, b1, t1, gen}, SolveFast.Buf5{s2, b2, t2, gen},
              e1, e2))))

# ---------------------------------------------------------------------------
# Section 2: `Greedy.gpick_loop`, `greedy_expand`, and `greedy_step` soundness
# ---------------------------------------------------------------------------

def GR.glist_ok_b(+G: +List<+List<Nat>>, +n_root: Nat,
    +gs: SolveFast.GList) -> Bool:
  match gs:
    case SolveFast.GEnd{}:
      True{}
    case SolveFast.GThen{rest}:
      GR.glist_ok_b(G, n_root, rest)
    case SolveFast.GTry{row, g, rest}:
      Bool.and(FT.FT.gentry_ok_b(G, n_root, row, g),
        Bool.and(Tree.member_word(g, G), GR.glist_ok_b(G, n_root, rest)))

def GR.glist_of_rws_ok(+G: +List<+List<Nat>>, +n_root: Nat,
    +rws: +List<FT.FT.RowWord>, +tail: SolveFast.GList,
    +hrws: {FT.FT.rws_ok_b(G, n_root, rws) == True{} : Bool},
    +hai: {FO.FO.all_in_ref(FT.FT.rws_words(rws), G) == True{} : Bool},
    +ht: {GR.glist_ok_b(G, n_root, tail) == True{} : Bool}) ->
  {GR.glist_ok_b(G, n_root, FT.FT.glist_of_rws(rws, tail)) == True{} : Bool}:
  match rws:
    case Nil{}:
      ht
    case Con{rw, rest}:
      match rw:
        case FT.RowWord{+row, +g}:
          +h1 = Logic.Proof.and_true_l(FT.FT.gentry_ok_b(G, n_root, row, g),
                  FT.FT.rws_ok_b(G, n_root, rest), hrws)
          +hr = Logic.Proof.and_true_r(FT.FT.gentry_ok_b(G, n_root, row, g),
                  FT.FT.rws_ok_b(G, n_root, rest), hrws)
          +hg = FO.FO.all_in_head(g, FT.FT.rws_words(rest), G, hai)
          +hat = FO.FO.all_in_tail(g, FT.FT.rws_words(rest), G, hai)
          FO.FO.bool_and_intro(FT.FT.gentry_ok_b(G, n_root, row, g),
            Bool.and(Tree.member_word(g, G),
              GR.glist_ok_b(G, n_root, FT.FT.glist_of_rws(rest, tail))),
            h1,
            FO.FO.bool_and_intro(Tree.member_word(g, G),
              GR.glist_ok_b(G, n_root, FT.FT.glist_of_rws(rest, tail)),
              hg, GR.glist_of_rws_ok(G, n_root, rest, tail, hr, hat, ht)))

def GR.glist_of_cwords_ok(+G: +List<+List<Nat>>, +C_root: +List<+List<Nat>>,
    +n_root: Nat, +cs: +List<SolveFast.CWord>, +tail: SolveFast.GList,
    +hcs: {FT.FT.cwords_ok_b(G, C_root, n_root, cs) == True{} : Bool},
    +hai: {FO.FO.all_in_ref(SolveFast.cwords_words(cs), G) == True{} : Bool},
    +ht: {GR.glist_ok_b(G, n_root, tail) == True{} : Bool}) ->
  {GR.glist_ok_b(G, n_root, SolveFast.glist_of_cwords(cs, tail))
   == True{} : Bool}:
  match cs:
    case Nil{}:
      ht
    case Con{cw, rest}:
      match cw:
        case SolveFast.CWord{+ci, +grow, +w}:
          +hcw = Logic.Proof.and_true_l(
                   FT.FT.cword_ok_b(G, C_root, n_root,
                     SolveFast.CWord{ci, grow, w}),
                   FT.FT.cwords_ok_b(G, C_root, n_root, rest), hcs)
          +hrest = Logic.Proof.and_true_r(
                     FT.FT.cword_ok_b(G, C_root, n_root,
                       SolveFast.CWord{ci, grow, w}),
                     FT.FT.cwords_ok_b(G, C_root, n_root, rest), hcs)
          +hgr = Logic.Proof.and_true_r(
                   FT.FT.has_col_go(Groups.len_words(G), C_root, ci, w, 0n),
                   FT.FT.gentry_ok_b(G, n_root, grow, w), hcw)
          +hw = FO.FO.all_in_head(w, SolveFast.cwords_words(rest), G, hai)
          +hat = FO.FO.all_in_tail(w, SolveFast.cwords_words(rest), G, hai)
          FO.FO.bool_and_intro(FT.FT.gentry_ok_b(G, n_root, grow, w),
            Bool.and(Tree.member_word(w, G),
              GR.glist_ok_b(G, n_root, SolveFast.glist_of_cwords(rest, tail))),
            hgr,
            FO.FO.bool_and_intro(Tree.member_word(w, G),
              GR.glist_ok_b(G, n_root, SolveFast.glist_of_cwords(rest, tail)),
              hw,
              GR.glist_of_cwords_ok(G, C_root, n_root, rest, tail, hrest, hat,
                ht)))

def GR.HasOk(+G: +List<+List<Nat>>, +n_root: Nat, +S: +List<+List<Nat>>,
    +has: Bool, +brow: U32, +bg: +List<Nat>) -> Data:
  match has:
    case False{}:
      Unit
    case True{}:
      Arr.Arr.DPair<
        {FT.FT.gentry_ok_b(G, n_root, brow, bg) == True{} : Bool},
        Arr.Arr.DPair<
          {Tree.member_word(bg, G) == True{} : Bool},
          {Groups.groups_smaller(S, Groups.groups_build(bg, S, Nil{}))
           == True{} : Bool}>>

def GR.GPickInv(+G: +List<+List<Nat>>, +C_root: +List<+List<Nat>>, +n_root: Nat,
    +S: +List<+List<Nat>>, st: Greedy.GPickSt) -> Data:
  match st:
    case Greedy.GPickOk{seen, tbl, gen, has, brow, bg, blb, hit}:
      Arr.Arr.DPair<
        FH.FH.SeenTree(10n, 0, seen, gen, Nil{}),
        Arr.Arr.DPair<
          FT.FT.TblOk(G, C_root, n_root, tbl),
          GR.HasOk(G, n_root, S, has, brow, bg)>>

def GR.gpick_inv_transport(+G: +List<+List<Nat>>, +C_root: +List<+List<Nat>>,
    +n_root: Nat, +S: +List<+List<Nat>>,
    -s1: Greedy.GPickSt, -s2: Greedy.GPickSt,
    +e: {s1 == s2 : Greedy.GPickSt},
    +h: GR.GPickInv(G, C_root, n_root, S, s1)) ->
  GR.GPickInv(G, C_root, n_root, S, s2):
  %e : GR.GPickInv(G, C_root, n_root, S, _)
  h

def GR.gpick_cmp_ok(+G: +List<+List<Nat>>, +C_root: +List<+List<Nat>>,
    +n_root: Nat, +S: +List<+List<Nat>>,
    +row: U32, +g: +List<Nat>, +lb: Nat, +fl: Nat,
    seen: Array<Nat>, tbl: Array<U32>, +gen2: Nat,
    +has: Bool, +brow: U32, +bg: +List<Nat>, +blb: Nat, better: Bool,
    +hs: FH.FH.SeenTree(10n, 0, seen, gen2, Nil{}),
    +ht: FT.FT.TblOk(G, C_root, n_root, tbl),
    +hh: GR.HasOk(G, n_root, S, has, brow, bg),
    +hrow: {FT.FT.gentry_ok_b(G, n_root, row, g) == True{} : Bool},
    +hwg: {Tree.member_word(g, G) == True{} : Bool},
    +hus: {Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{}))
           == True{} : Bool}) ->
  GR.GPickInv(G, C_root, n_root, S,
    Greedy.gpick_cmp(row, g, lb, fl, seen, tbl, gen2, has, brow, bg, blb,
      better)):
  match better:
    case True{}:
      Arr.DPair{hs, Arr.DPair{ht, Arr.DPair{hrow, Arr.DPair{hwg, hus}}}}
    case False{}:
      Arr.DPair{hs, Arr.DPair{ht, hh}}

def GR.gpick_usable_ok(+G: +List<+List<Nat>>, +C_root: +List<+List<Nat>>,
    +n_root: Nat, +S: +List<+List<Nat>>,
    +row: U32, +g: +List<Nat>, +n: Nat, +fl: Nat,
    seen: Array<Nat>, tbl: Array<U32>, +gen2: Nat,
    +has: Bool, +brow: U32, +bg: +List<Nat>, +blb: Nat,
    +m: Nat, +k: Nat, usable: Bool,
    +eus: {usable == Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{}))
           : Bool},
    +hs: FH.FH.SeenTree(10n, 0, seen, gen2, Nil{}),
    +ht: FT.FT.TblOk(G, C_root, n_root, tbl),
    +hh: GR.HasOk(G, n_root, S, has, brow, bg),
    +hrow: {FT.FT.gentry_ok_b(G, n_root, row, g) == True{} : Bool},
    +hwg: {Tree.member_word(g, G) == True{} : Bool}) ->
  GR.GPickInv(G, C_root, n_root, S,
    Greedy.gpick_usable(row, g, n, fl, seen, tbl, gen2, has, brow, bg, blb,
      m, k, usable)):
  match usable:
    case False{}:
      Arr.DPair{hs, Arr.DPair{ht, hh}}
    case True{}:
      +lb = Nat.sub(Nat.add(n, Nat.add(m, m)), k)
      +hus : {Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{}))
              == True{} : Bool} =
        Equal.sym(Bool, True{},
          Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})), eus)
      GR.gpick_cmp_ok(G, C_root, n_root, S, row, g, lb, fl, seen, tbl, gen2,
        has, brow, bg, blb, Bool.or(Bool.not(has), Nat.is_lt(lb, blb)),
        hs, ht, hh, hrow, hwg, hus)

# Extract `Bool.or(m < n, 2 <= k) == groups_smaller(ws, groups_build(g, ws, Nil{}))`
# and bump `SeenTree` after `Hist5Ok`.
def GR.usable_eq_of_hist(+g: +List<Nat>, +ws: +List<+List<Nat>>, +n: Nat,
    +m: Nat, +k: Nat,
    +hge1: {Nat.is_le(1n, n) == True{} : Bool},
    +en: {n == Groups.len_words(ws) : Nat},
    +hwf: {FH.FH.fgroups_wf(SolveFast.fgroups_build_fast(g, ws, Nil{}))
           == True{} : Bool},
    +hm: {m == FH.FH.fgroups_total(SolveFast.fgroups_build_fast(g, ws, Nil{}))
          : Nat},
    +hk: {k == FH.FH.fgroups_count(SolveFast.fgroups_build_fast(g, ws, Nil{}))
          : Nat},
    +hle0: {Nat.is_le(m, Nat.add(Groups.len_words(ws), 0n)) == True{} : Bool}) ->
  {Bool.or(Nat.is_lt(m, n), Nat.is_le(2n, k))
   == Groups.groups_smaller(ws, Groups.groups_build(g, ws, Nil{})) : Bool}:
  +fg = SolveFast.fgroups_build_fast(g, ws, Nil{})
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
          FH.FH.fgroups_total(fg), m, Equal.sym(Nat, m, FH.FH.fgroups_total(fg), hm)),
        Equal.cong(Nat, Bool,
          y => Bool.or(Nat.is_lt(m, n), Nat.is_le(2n, y)),
          FH.FH.fgroups_count(fg), k, Equal.sym(Nat, k, FH.FH.fgroups_count(fg), hk))))
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
  Equal.trans(Bool,
    Bool.or(Nat.is_lt(m, n), Nat.is_le(2n, k)),
    SolveFast.fgroups_smaller(n, fg),
    Groups.groups_smaller(ws, Groups.groups_build(g, ws, Nil{})),
    Equal.sym(Bool, SolveFast.fgroups_smaller(n, fg),
      Bool.or(Nat.is_lt(m, n), Nat.is_le(2n, k)), eus_fg), eus_g)

def GR.seen_bump_dup(+gen: Nat, +fg: +List<SolveFast.FGroup>,
    -seen2: Array<Nat>, +hs2: FH.FH.SeenTree(10n, 0, seen2, gen, fg),
    dp: &s1: Array<Nat> -> &s2: Array<Nat> ->
        {s1 == seen2 : Array<Nat>} & {s2 == s1 : Array<Nat>}) ->
  FH.FH.SeenTree(10n, 0, seen2, Nat.add(1n, gen), Nil{}):
  (s1, dp2) = dp
  (s2, pe) = dp2
  (+es1, +es2) = pe
  +es2_seen : {s2 == seen2 : Array<Nat>} =
    Equal.trans(Array<Nat>, s2, s1, seen2, es2, es1)
  +hs_s2 = FH.FH.seen_tree_transport(10n, 0, seen2, s2, gen, fg,
             Equal.sym(Array<Nat>, s2, seen2, es2_seen), hs2)
  FH.FH.seen_tree_transport(10n, 0, s2, seen2, Nat.add(1n, gen), Nil{},
    es2_seen, FH.FH.seen_tree_bump(10n, 0, s2, gen, fg, hs_s2))

def GR.gpick_res_ok_dup2(+G: +List<+List<Nat>>, +C_root: +List<+List<Nat>>,
    +n_root: Nat, +row: U32, +g: +List<Nat>, +ws: +List<+List<Nat>>,
    +n: Nat, +fl: Nat, +gen: Nat,
    +has: Bool, +brow: U32, +bg: +List<Nat>, +blb: Nat,
    -seen2: Array<Nat>, tbl2: Array<U32>, +m: Nat, +k: Nat,
    +eus: {Bool.or(Nat.is_lt(m, n), Nat.is_le(2n, k))
           == Groups.groups_smaller(ws, Groups.groups_build(g, ws, Nil{}))
           : Bool},
    +hs2: FH.FH.SeenTree(10n, 0, seen2, gen, SolveFast.fgroups_build_fast(g, ws, Nil{})),
    +htbl2: FT.FT.TblOk(G, C_root, n_root, tbl2),
    +hh: GR.HasOk(G, n_root, ws, has, brow, bg),
    +hrow: {FT.FT.gentry_ok_b(G, n_root, row, g) == True{} : Bool},
    +hwg: {Tree.member_word(g, G) == True{} : Bool},
    dp: &s1: Array<Nat> -> &s2: Array<Nat> ->
        {s1 == seen2 : Array<Nat>} & {s2 == s1 : Array<Nat>}) ->
  GR.GPickInv(G, C_root, n_root, ws,
    Greedy.gpick_usable(row, g, n, fl, seen2, tbl2, Nat.add(1n, gen),
      has, brow, bg, blb, m, k, Bool.or(Nat.is_lt(m, n), Nat.is_le(2n, k)))):
  (s1, dp2) = dp
  (s2, pe) = dp2
  (+es1, +es2) = pe
  +fg = SolveFast.fgroups_build_fast(g, ws, Nil{})
  +es2_s : {s2 == seen2 : Array<Nat>} =
    Equal.trans(Array<Nat>, s2, s1, seen2, es2, es1)
  +hbump = FH.FH.seen_tree_transport(10n, 0, s2, s1, Nat.add(1n, gen), Nil{},
             es2,
             FH.FH.seen_tree_bump(10n, 0, s2, gen, fg,
               FH.FH.seen_tree_transport(10n, 0, seen2, s2, gen, fg,
                 Equal.sym(Array<Nat>, s2, seen2, es2_s), hs2)))
  %es1 : GR.GPickInv(G, C_root, n_root, ws,
           Greedy.gpick_usable(row, g, n, fl, _, tbl2, Nat.add(1n, gen),
             has, brow, bg, blb, m, k,
             Bool.or(Nat.is_lt(m, n), Nat.is_le(2n, k))))
  GR.gpick_usable_ok(G, C_root, n_root, ws, row, g, n, fl, s1, tbl2,
    Nat.add(1n, gen), has, brow, bg, blb, m, k,
    Bool.or(Nat.is_lt(m, n), Nat.is_le(2n, k)), eus, hbump, htbl2, hh, hrow,
    hwg)

def GR.gpick_res_ok_dup(+G: +List<+List<Nat>>, +C_root: +List<+List<Nat>>,
    +n_root: Nat, +row: U32, +g: +List<Nat>, +ws: +List<+List<Nat>>,
    +n: Nat, +fl: Nat, +gen: Nat, +budget0: Nat, +skip_self: Bool,
    +has: Bool, +brow: U32, +bg: +List<Nat>, +blb: Nat,
    -tbl0: Array<U32>, seen2: Array<Nat>, tbl2: Array<U32>,
    +m: Nat, +k: Nat, +b: Nat,
    +hge1: {Nat.is_le(1n, n) == True{} : Bool},
    +en: {n == Groups.len_words(ws) : Nat},
    +hrow: {FT.FT.gentry_ok_b(G, n_root, row, g) == True{} : Bool},
    +hwg: {Tree.member_word(g, G) == True{} : Bool},
    +htbl0: FT.FT.TblOk(G, C_root, n_root, tbl0),
    +hh: GR.HasOk(G, n_root, ws, has, brow, bg),
    +hhr: FH.FH.HistSpec(g, ws, Nil{}, gen, budget0, skip_self, tbl0,
            SolveFast.Hist5Ok{seen2, tbl2, m, k, b})) ->
  GR.GPickInv(G, C_root, n_root, ws,
    Greedy.gpick_usable(row, g, n, fl, seen2, tbl2, Nat.add(1n, gen),
      has, brow, bg, blb, m, k, Bool.or(Nat.is_lt(m, n), Nat.is_le(2n, k)))):
  +fg = SolveFast.fgroups_build_fast(g, ws, Nil{})
  +hs2 = Arr.Arr.dpair_l(FH.FH.SeenTree(10n, 0, seen2, gen, fg),
           Arr.Arr.DPair<{tbl2 == tbl0 : Array<U32>},
             Arr.Arr.DPair<{FH.FH.fgroups_wf(fg) == True{} : Bool},
               Arr.Arr.DPair<{m == FH.FH.fgroups_total(fg) : Nat},
                 Arr.Arr.DPair<{k == FH.FH.fgroups_count(fg) : Nat},
                   Arr.Arr.DPair<{Nat.add(b, m) == Nat.add(budget0, k) : Nat},
                     {Nat.is_le(m, Nat.add(Groups.len_words(ws), 0n))
                      == True{} : Bool}>>>>>, hhr)
  +r1 = Arr.Arr.dpair_r(FH.FH.SeenTree(10n, 0, seen2, gen, fg),
          Arr.Arr.DPair<{tbl2 == tbl0 : Array<U32>},
            Arr.Arr.DPair<{FH.FH.fgroups_wf(fg) == True{} : Bool},
              Arr.Arr.DPair<{m == FH.FH.fgroups_total(fg) : Nat},
                Arr.Arr.DPair<{k == FH.FH.fgroups_count(fg) : Nat},
                  Arr.Arr.DPair<{Nat.add(b, m) == Nat.add(budget0, k) : Nat},
                    {Nat.is_le(m, Nat.add(Groups.len_words(ws), 0n))
                     == True{} : Bool}>>>>>, hhr)
  +et20 = Arr.Arr.dpair_l({tbl2 == tbl0 : Array<U32>},
            Arr.Arr.DPair<{FH.FH.fgroups_wf(fg) == True{} : Bool},
              Arr.Arr.DPair<{m == FH.FH.fgroups_total(fg) : Nat},
                Arr.Arr.DPair<{k == FH.FH.fgroups_count(fg) : Nat},
                  Arr.Arr.DPair<{Nat.add(b, m) == Nat.add(budget0, k) : Nat},
                    {Nat.is_le(m, Nat.add(Groups.len_words(ws), 0n))
                     == True{} : Bool}>>>>, r1)
  +r2 = Arr.Arr.dpair_r({tbl2 == tbl0 : Array<U32>},
          Arr.Arr.DPair<{FH.FH.fgroups_wf(fg) == True{} : Bool},
            Arr.Arr.DPair<{m == FH.FH.fgroups_total(fg) : Nat},
              Arr.Arr.DPair<{k == FH.FH.fgroups_count(fg) : Nat},
                Arr.Arr.DPair<{Nat.add(b, m) == Nat.add(budget0, k) : Nat},
                  {Nat.is_le(m, Nat.add(Groups.len_words(ws), 0n))
                   == True{} : Bool}>>>>, r1)
  +hwf = Arr.Arr.dpair_l({FH.FH.fgroups_wf(fg) == True{} : Bool},
           Arr.Arr.DPair<{m == FH.FH.fgroups_total(fg) : Nat},
             Arr.Arr.DPair<{k == FH.FH.fgroups_count(fg) : Nat},
               Arr.Arr.DPair<{Nat.add(b, m) == Nat.add(budget0, k) : Nat},
                 {Nat.is_le(m, Nat.add(Groups.len_words(ws), 0n))
                  == True{} : Bool}>>>, r2)
  +r3 = Arr.Arr.dpair_r({FH.FH.fgroups_wf(fg) == True{} : Bool},
          Arr.Arr.DPair<{m == FH.FH.fgroups_total(fg) : Nat},
            Arr.Arr.DPair<{k == FH.FH.fgroups_count(fg) : Nat},
              Arr.Arr.DPair<{Nat.add(b, m) == Nat.add(budget0, k) : Nat},
                {Nat.is_le(m, Nat.add(Groups.len_words(ws), 0n))
                 == True{} : Bool}>>>, r2)
  +hm = Arr.Arr.dpair_l({m == FH.FH.fgroups_total(fg) : Nat},
          Arr.Arr.DPair<{k == FH.FH.fgroups_count(fg) : Nat},
            Arr.Arr.DPair<{Nat.add(b, m) == Nat.add(budget0, k) : Nat},
              {Nat.is_le(m, Nat.add(Groups.len_words(ws), 0n))
               == True{} : Bool}>>, r3)
  +r4 = Arr.Arr.dpair_r({m == FH.FH.fgroups_total(fg) : Nat},
          Arr.Arr.DPair<{k == FH.FH.fgroups_count(fg) : Nat},
            Arr.Arr.DPair<{Nat.add(b, m) == Nat.add(budget0, k) : Nat},
              {Nat.is_le(m, Nat.add(Groups.len_words(ws), 0n))
               == True{} : Bool}>>, r3)
  +hk = Arr.Arr.dpair_l({k == FH.FH.fgroups_count(fg) : Nat},
          Arr.Arr.DPair<{Nat.add(b, m) == Nat.add(budget0, k) : Nat},
            {Nat.is_le(m, Nat.add(Groups.len_words(ws), 0n))
             == True{} : Bool}>, r4)
  +r5 = Arr.Arr.dpair_r({k == FH.FH.fgroups_count(fg) : Nat},
          Arr.Arr.DPair<{Nat.add(b, m) == Nat.add(budget0, k) : Nat},
            {Nat.is_le(m, Nat.add(Groups.len_words(ws), 0n))
             == True{} : Bool}>, r4)
  +hle0 = Arr.Arr.dpair_r({Nat.add(b, m) == Nat.add(budget0, k) : Nat},
            {Nat.is_le(m, Nat.add(Groups.len_words(ws), 0n)) == True{} : Bool},
            r5)
  +htbl2 = FT.FT.tbl_ok_transport(G, C_root, n_root, tbl0, tbl2,
             Equal.sym(Array<U32>, tbl2, tbl0, et20), htbl0)
  +eus = GR.usable_eq_of_hist(g, ws, n, m, k, hge1, en, hwf, hm, hk, hle0)
  GR.gpick_res_ok_dup2(G, C_root, n_root, row, g, ws, n, fl, gen, has, brow, bg,
    blb, seen2, tbl2, m, k, eus, hs2, htbl2, hh, hrow, hwg,
    Arr.Arr.dup(Nat, seen2))

def GR.gpick_res_ok(+G: +List<+List<Nat>>, +C_root: +List<+List<Nat>>,
    +n_root: Nat, +row: U32, +g: +List<Nat>, +ws: +List<+List<Nat>>,
    +n: Nat, +fl: Nat, +gen: Nat, +budget0: Nat, +skip_self: Bool,
    +has: Bool, +brow: U32, +bg: +List<Nat>, +blb: Nat,
    -tbl0: Array<U32>, hr: SolveFast.Hist5Res,
    +hge1: {Nat.is_le(1n, n) == True{} : Bool},
    +en: {n == Groups.len_words(ws) : Nat},
    +hrow: {FT.FT.gentry_ok_b(G, n_root, row, g) == True{} : Bool},
    +hwg: {Tree.member_word(g, G) == True{} : Bool},
    +htbl0: FT.FT.TblOk(G, C_root, n_root, tbl0),
    +hh: GR.HasOk(G, n_root, ws, has, brow, bg),
    +hhr: FH.FH.HistSpec(g, ws, Nil{}, gen, budget0, skip_self, tbl0, hr)) ->
  GR.GPickInv(G, C_root, n_root, ws,
    Greedy.gpick_res(row, g, n, fl, gen, has, brow, bg, blb, hr)):
  match hr:
    case SolveFast.Hist5Pruned{seen2, tbl2}:
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
      +htbl2 = FT.FT.tbl_ok_transport(G, C_root, n_root, tbl0, tbl2,
                 Equal.sym(Array<U32>, tbl2, tbl0, et2), htbl0)
      Arr.DPair{hs2, Arr.DPair{htbl2, hh}}
    case SolveFast.Hist5Ok{seen2, tbl2, +m, +k, +b}:
      GR.gpick_res_ok_dup(G, C_root, n_root, row, g, ws, n, fl, gen, budget0,
        skip_self, has, brow, bg, blb, tbl0, seen2, tbl2, m, k, b, hge1, en,
        hrow, hwg, htbl0, hh, hhr)

def GR.gpick_try_ok(+G: +List<+List<Nat>>, +C_root: +List<+List<Nat>>,
    +n_root: Nat, +row: U32, +g: +List<Nat>, +S: +List<SolveFast.CWord>,
    +n: Nat, +fl: Nat, +skip_self: Bool,
    seen: Array<Nat>, tbl: Array<U32>, +gen: Nat,
    +has: Bool, +brow: U32, +bg: +List<Nat>, +blb: Nat,
    +hge1: {Nat.is_le(1n, n) == True{} : Bool},
    +en: {n == Groups.len_words(SolveFast.cwords_words(S)) : Nat},
    +hS: {FT.FT.cwords_ok_b(G, C_root, n_root, S) == True{} : Bool},
    +hrow: {FT.FT.gentry_ok_b(G, n_root, row, g) == True{} : Bool},
    +hwg: {Tree.member_word(g, G) == True{} : Bool},
    +hs: FH.FH.SeenTree(10n, 0, seen, gen, Nil{}),
    +ht: FT.FT.TblOk(G, C_root, n_root, tbl),
    +hh: GR.HasOk(G, n_root, SolveFast.cwords_words(S), has, brow, bg)) ->
  GR.GPickInv(G, C_root, n_root, SolveFast.cwords_words(S),
    Greedy.gpick_res(row, g, n, fl, gen, has, brow, bg, blb,
      SolveFast.hist5_go(row, S, gen, skip_self,
        SolveFast.Hist5Ok{seen, tbl, 0n, 0n,
          Greedy.gpick_budget(n, has, blb, skip_self)}))):
  +ws = SolveFast.cwords_words(S)
  +bgt = Greedy.gpick_budget(n, has, blb, skip_self)
  GR.with_dup_arr(Nat,
    GR.GPickInv(G, C_root, n_root, ws,
      Greedy.gpick_res(row, g, n, fl, gen, has, brow, bg, blb,
        SolveFast.hist5_go(row, S, gen, skip_self,
          SolveFast.Hist5Ok{seen, tbl, 0n, 0n, bgt}))),
    seen,
    s1 => s2 => +es1 => +es2 =>
    GR.with_dup_arr(U32,
      GR.GPickInv(G, C_root, n_root, ws,
        Greedy.gpick_res(row, g, n, fl, gen, has, brow, bg, blb,
          SolveFast.hist5_go(row, S, gen, skip_self,
            SolveFast.Hist5Ok{seen, tbl, 0n, 0n, bgt}))),
      tbl,
      t1 => t2 => +et1 => +et2 =>
      +hs1 = FH.FH.seen_tree_transport(10n, 0, seen, s1, gen, Nil{},
               Equal.sym(Array<Nat>, s1, seen, es1), hs)
      +ht1 = FT.FT.tbl_ok_transport(G, C_root, n_root, tbl, t1,
               Equal.sym(Array<U32>, t1, tbl, et1), ht)
      +hhr1 = FH.FH.hist5_go_spec(S, G, C_root, n_root, row, g, Nil{}, s1, t1,
                gen, 0n, 0n, bgt, bgt, skip_self, ht1, hrow, hS,
                Equal.trans(Nat, Nat.add(bgt, 0n), bgt, Nat.add(bgt, 0n),
                  NatProof.NatPrf.add_zero(bgt),
                  Equal.sym(Nat, Nat.add(bgt, 0n), bgt,
                    NatProof.NatPrf.add_zero(bgt))),
                {==}, {==}, {==}, hs1)
      +es12 : {s1 == s2 : Array<Nat>} =
        Equal.trans(Array<Nat>, s1, seen, s2, es1,
          Equal.sym(Array<Nat>, s2, seen, es2))
      +et12 : {t1 == t2 : Array<U32>} =
        Equal.trans(Array<U32>, t1, tbl, t2, et1,
          Equal.sym(Array<U32>, t2, tbl, et2))
      +hhr2 : FH.FH.HistSpec(g, ws, Nil{}, gen, bgt, skip_self, t1,
                SolveFast.hist5_go(row, S, gen, skip_self,
                  SolveFast.Hist5Ok{s2, t2, 0n, 0n, bgt})) =
        %es12 : FH.FH.HistSpec(g, ws, Nil{}, gen, bgt, skip_self, t1,
                  SolveFast.hist5_go(row, S, gen, skip_self,
                    SolveFast.Hist5Ok{_, t2, 0n, 0n, bgt}))
        %et12 : FH.FH.HistSpec(g, ws, Nil{}, gen, bgt, skip_self, t1,
                  SolveFast.hist5_go(row, S, gen, skip_self,
                    SolveFast.Hist5Ok{s1, _, 0n, 0n, bgt}))
        hhr1
      +hr2 = GR.gpick_res_ok(G, C_root, n_root, row, g, ws, n, fl, gen, bgt,
               skip_self, has, brow, bg, blb, t1,
               SolveFast.hist5_go(row, S, gen, skip_self,
                 SolveFast.Hist5Ok{s2, t2, 0n, 0n, bgt}),
               hge1, en, hrow, hwg, ht1, hh, hhr2)
      %es2 : GR.GPickInv(G, C_root, n_root, ws,
               Greedy.gpick_res(row, g, n, fl, gen, has, brow, bg, blb,
                 SolveFast.hist5_go(row, S, gen, skip_self,
                   SolveFast.Hist5Ok{_, tbl, 0n, 0n, bgt})))
      %et2 : GR.GPickInv(G, C_root, n_root, ws,
               Greedy.gpick_res(row, g, n, fl, gen, has, brow, bg, blb,
                 SolveFast.hist5_go(row, S, gen, skip_self,
                   SolveFast.Hist5Ok{s2, _, 0n, 0n, bgt})))
      hr2))

def GR.gpick_loop_ok(+gs: SolveFast.GList, +G: +List<+List<Nat>>,
    +C_root: +List<+List<Nat>>, +n_root: Nat, +S: +List<SolveFast.CWord>,
    +n: Nat, +fl: Nat, +skip_self: Bool, st: Greedy.GPickSt,
    +hgs: {GR.glist_ok_b(G, n_root, gs) == True{} : Bool},
    +hge1: {Nat.is_le(1n, n) == True{} : Bool},
    +en: {n == Groups.len_words(SolveFast.cwords_words(S)) : Nat},
    +hS: {FT.FT.cwords_ok_b(G, C_root, n_root, S) == True{} : Bool},
    +hst: GR.GPickInv(G, C_root, n_root, SolveFast.cwords_words(S), st)) ->
  GR.GPickInv(G, C_root, n_root, SolveFast.cwords_words(S),
    Greedy.gpick_loop(gs, S, n, fl, skip_self, st)):
  match gs:
    case SolveFast.GEnd{}:
      hst
    case SolveFast.GThen{rest}:
      match st:
        case Greedy.GPickOk{seen, tbl, +gen, +has, +brow, +bg, +blb, hit}:
          GR.gpick_loop_ok(rest, G, C_root, n_root, S, n, Nat.add(n, n), True{},
            Greedy.GPickOk{seen, tbl, gen, has, brow, bg, blb,
              Bool.and(has, Nat.is_le(blb, Nat.add(n, n)))},
            hgs, hge1, en, hS, hst)
    case SolveFast.GTry{+row, +g, +rest}:
      match st:
        case Greedy.GPickOk{seen, tbl, +gen, +has, +brow, +bg, +blb, hit}:
          match hit:
            case True{}:
              hst
            case False{}:
              +ws = SolveFast.cwords_words(S)
              +bgt = Greedy.gpick_budget(n, has, blb, skip_self)
              +hrow = Logic.Proof.and_true_l(
                        FT.FT.gentry_ok_b(G, n_root, row, g),
                        Bool.and(Tree.member_word(g, G),
                          GR.glist_ok_b(G, n_root, rest)), hgs)
              +hr1 = Logic.Proof.and_true_r(
                       FT.FT.gentry_ok_b(G, n_root, row, g),
                       Bool.and(Tree.member_word(g, G),
                         GR.glist_ok_b(G, n_root, rest)), hgs)
              +hwg = Logic.Proof.and_true_l(Tree.member_word(g, G),
                       GR.glist_ok_b(G, n_root, rest), hr1)
              +hrest = Logic.Proof.and_true_r(Tree.member_word(g, G),
                         GR.glist_ok_b(G, n_root, rest), hr1)
              +hs = Arr.Arr.dpair_l(FH.FH.SeenTree(10n, 0, seen, gen, Nil{}),
                      Arr.Arr.DPair<FT.FT.TblOk(G, C_root, n_root, tbl),
                        GR.HasOk(G, n_root, ws, has, brow, bg)>, hst)
              +hrr = Arr.Arr.dpair_r(FH.FH.SeenTree(10n, 0, seen, gen, Nil{}),
                       Arr.Arr.DPair<FT.FT.TblOk(G, C_root, n_root, tbl),
                         GR.HasOk(G, n_root, ws, has, brow, bg)>, hst)
              +ht = Arr.Arr.dpair_l(FT.FT.TblOk(G, C_root, n_root, tbl),
                      GR.HasOk(G, n_root, ws, has, brow, bg), hrr)
              +hh = Arr.Arr.dpair_r(FT.FT.TblOk(G, C_root, n_root, tbl),
                      GR.HasOk(G, n_root, ws, has, brow, bg), hrr)
              GR.with_dup_arr(Nat,
                GR.GPickInv(G, C_root, n_root, ws,
                  Greedy.gpick_loop(rest, S, n, fl, skip_self,
                    Greedy.gpick_res(row, g, n, fl, gen, has, brow, bg, blb,
                      SolveFast.hist5_go(row, S, gen, skip_self,
                        SolveFast.Hist5Ok{seen, tbl, 0n, 0n, bgt})))),
                seen,
                s1 => s2 => +es1 => +es2 =>
                GR.with_dup_arr(U32,
                  GR.GPickInv(G, C_root, n_root, ws,
                    Greedy.gpick_loop(rest, S, n, fl, skip_self,
                      Greedy.gpick_res(row, g, n, fl, gen, has, brow, bg, blb,
                        SolveFast.hist5_go(row, S, gen, skip_self,
                          SolveFast.Hist5Ok{seen, tbl, 0n, 0n, bgt})))),
                  tbl,
                  t1 => t2 => +et1 => +et2 =>
                  +hs1 = FH.FH.seen_tree_transport(10n, 0, seen, s1, gen, Nil{},
                           Equal.sym(Array<Nat>, s1, seen, es1), hs)
                  +ht1 = FT.FT.tbl_ok_transport(G, C_root, n_root, tbl, t1,
                           Equal.sym(Array<U32>, t1, tbl, et1), ht)
                  +hst1 = GR.gpick_try_ok(G, C_root, n_root, row, g, S, n, fl,
                            skip_self, s1, t1, gen, has, brow, bg, blb, hge1,
                            en, hS, hrow, hwg, hs1, ht1, hh)
                  +es12 : {s1 == s2 : Array<Nat>} =
                    Equal.trans(Array<Nat>, s1, seen, s2, es1,
                      Equal.sym(Array<Nat>, s2, seen, es2))
                  +et12 : {t1 == t2 : Array<U32>} =
                    Equal.trans(Array<U32>, t1, tbl, t2, et1,
                      Equal.sym(Array<U32>, t2, tbl, et2))
                  +hst2 : GR.GPickInv(G, C_root, n_root, ws,
                            Greedy.gpick_res(row, g, n, fl, gen, has, brow, bg,
                              blb, SolveFast.hist5_go(row, S, gen, skip_self,
                                SolveFast.Hist5Ok{s2, t2, 0n, 0n, bgt}))) =
                    %es12 : GR.GPickInv(G, C_root, n_root, ws,
                              Greedy.gpick_res(row, g, n, fl, gen, has, brow, bg,
                                blb, SolveFast.hist5_go(row, S, gen, skip_self,
                                  SolveFast.Hist5Ok{_, t2, 0n, 0n, bgt})))
                    %et12 : GR.GPickInv(G, C_root, n_root, ws,
                              Greedy.gpick_res(row, g, n, fl, gen, has, brow, bg,
                                blb, SolveFast.hist5_go(row, S, gen, skip_self,
                                  SolveFast.Hist5Ok{s1, _, 0n, 0n, bgt})))
                    hst1
                  +hres = GR.gpick_loop_ok(rest, G, C_root, n_root, S, n, fl,
                            skip_self,
                            Greedy.gpick_res(row, g, n, fl, gen, has, brow, bg,
                              blb, SolveFast.hist5_go(row, S, gen, skip_self,
                                SolveFast.Hist5Ok{s2, t2, 0n, 0n, bgt})),
                            hrest, hge1, en, hS, hst2)
                  %es2 : GR.GPickInv(G, C_root, n_root, ws,
                           Greedy.gpick_loop(rest, S, n, fl, skip_self,
                             Greedy.gpick_res(row, g, n, fl, gen, has, brow, bg,
                               blb, SolveFast.hist5_go(row, S, gen, skip_self,
                                 SolveFast.Hist5Ok{_, tbl, 0n, 0n, bgt}))))
                  %et2 : GR.GPickInv(G, C_root, n_root, ws,
                           Greedy.gpick_loop(rest, S, n, fl, skip_self,
                             Greedy.gpick_res(row, g, n, fl, gen, has, brow, bg,
                               blb, SolveFast.hist5_go(row, S, gen, skip_self,
                                 SolveFast.Hist5Ok{s2, _, 0n, 0n, bgt}))))
                  hres))

# Witness returned by `greedy_expand` and `greedy_expand_forced`.
type GR.ExpWit<+G: +List<+List<Nat>>, +C_root: +List<+List<Nat>>, +n_root: Nat,
    +S: +List<+List<Nat>>, +n: Nat, +items: +List<SolveFast.Item>> is Data:
  ExpNil{e: {items == Nil{} : +List<SolveFast.Item>}}
  ExpLive{g: +List<Nat>, ord: +List<Groups.Group>, body: +List<SolveFast.Item>,
          perm: FP.FP.Perm,
          eits: {items == SolveFast.Begin{g} <> body : +List<SolveFast.Item>},
          wg: {Tree.member_word(g, G) == True{} : Bool},
          hus: {Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{}))
                == True{} : Bool},
          hperm: FP.FP.PermOk(perm, Groups.groups_build(g, S, Nil{}), ord),
          hbm: FH.FH.BodyMatch(G, C_root, n_root, True{}, True{}, n, ord, body)}

def GR.ExpSpec(+G: +List<+List<Nat>>, +C_root: +List<+List<Nat>>, +n_root: Nat,
    +S: +List<+List<Nat>>, +n: Nat, gr: SolveFast.GuessRes) -> Data:
  match gr:
    case SolveFast.GuessRes{items, buf2}:
      Arr.Arr.DPair<
        GR.ExpWit<G, C_root, n_root, S, n, items>,
        FH.FH.BufOk(G, C_root, n_root, True{}, True{}, buf2)>

def GR.exp_of_guess_wit(+G: +List<+List<Nat>>, +C_root: +List<+List<Nat>>,
    +n_root: Nat, +g: +List<Nat>, +S: +List<+List<Nat>>, +n: Nat,
    +items: +List<SolveFast.Item>,
    +wg: {Tree.member_word(g, G) == True{} : Bool},
    gw: FH.FH.GuessWit<G, C_root, n_root, True{}, True{}, g, S, n, 0n,
          SolveFast.dummy_inf(0n), items>) ->
  GR.ExpWit<G, C_root, n_root, S, n, items>:
  match gw:
    case FH.GWit{gc, +hgc}:
      match gc:
        case FH.GCSkipSelf{}:
          +eits = Arr.Arr.dpair_l({items == Nil{} : +List<SolveFast.Item>},
                    Arr.Arr.DPair<{True{} == True{} : Bool},
                      Arr.Arr.DPair<{0n == Nat.add(n, n) : Nat},
                        {Tree.member_word(g, S) == True{} : Bool}>>, hgc)
          ExpNil{eits}
        case FH.GCSkipUnusable{}:
          +eits = Arr.Arr.dpair_l({items == Nil{} : +List<SolveFast.Item>},
                    {Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{}))
                     == False{} : Bool}, hgc)
          ExpNil{eits}
        case FH.GCSkipPre{}:
          +eits = Arr.Arr.dpair_l({items == Nil{} : +List<SolveFast.Item>},
                    {Nat.is_le(Eval.Eval.cost_of(SolveFast.dummy_inf(0n)),
                       SolveFast.pre_lb(n, g, S)) == True{} : Bool}, hgc)
          ExpNil{eits}
        case FH.GCSkipLb{}:
          +eits = Arr.Arr.dpair_l({items == Nil{} : +List<SolveFast.Item>},
                    {Nat.is_le(Eval.Eval.cost_of(SolveFast.dummy_inf(0n)),
                       SolveFast.lower_bound(n,
                         Groups.groups_build(g, S, Nil{})))
                     == True{} : Bool}, hgc)
          ExpNil{eits}
        case FH.GCLive{+ord, +body, +perm}:
          +full = Groups.groups_build(g, S, Nil{})
          +eits = Arr.Arr.dpair_l(
                    {items == SolveFast.Begin{g} <> body
                     : +List<SolveFast.Item>},
                    Arr.Arr.DPair<{Groups.groups_smaller(S, full) == True{} : Bool},
                      Arr.Arr.DPair<FP.FP.PermOk(perm, full, ord),
                        FH.FH.BodyMatch(G, C_root, n_root, True{}, True{},
                          n, ord, body)>>, hgc)
          +r1 = Arr.Arr.dpair_r(
                  {items == SolveFast.Begin{g} <> body
                   : +List<SolveFast.Item>},
                  Arr.Arr.DPair<{Groups.groups_smaller(S, full) == True{} : Bool},
                    Arr.Arr.DPair<FP.FP.PermOk(perm, full, ord),
                      FH.FH.BodyMatch(G, C_root, n_root, True{}, True{},
                        n, ord, body)>>, hgc)
          +hus = Arr.Arr.dpair_l(
                   {Groups.groups_smaller(S, full) == True{} : Bool},
                   Arr.Arr.DPair<FP.FP.PermOk(perm, full, ord),
                     FH.FH.BodyMatch(G, C_root, n_root, True{}, True{},
                       n, ord, body)>, r1)
          +r2 = Arr.Arr.dpair_r(
                  {Groups.groups_smaller(S, full) == True{} : Bool},
                  Arr.Arr.DPair<FP.FP.PermOk(perm, full, ord),
                    FH.FH.BodyMatch(G, C_root, n_root, True{}, True{},
                      n, ord, body)>, r1)
          +hperm = Arr.Arr.dpair_l(FP.FP.PermOk(perm, full, ord),
                     FH.FH.BodyMatch(G, C_root, n_root, True{}, True{},
                       n, ord, body), r2)
          +hbm = Arr.Arr.dpair_r(FP.FP.PermOk(perm, full, ord),
                   FH.FH.BodyMatch(G, C_root, n_root, True{}, True{},
                     n, ord, body), r2)
          ExpLive{g, ord, body, perm, eits, wg, hus, hperm, hbm}

def GR.exp_of_guess_spec(+G: +List<+List<Nat>>, +C_root: +List<+List<Nat>>,
    +n_root: Nat, +g: +List<Nat>, +S: +List<+List<Nat>>, +n: Nat,
    +wg: {Tree.member_word(g, G) == True{} : Bool},
    gr: SolveFast.GuessRes,
    +hgs: FH.FH.GuessSpec(G, C_root, n_root, True{}, True{}, g, S, n, 0n,
            SolveFast.dummy_inf(0n), gr)) ->
  GR.ExpSpec(G, C_root, n_root, S, n, gr):
  match gr:
    case SolveFast.GuessRes{+items, buf2}:
      +gw = Arr.Arr.dpair_l(
              FH.FH.GuessWit<G, C_root, n_root, True{}, True{}, g, S, n, 0n,
                SolveFast.dummy_inf(0n), items>,
              FH.FH.BufOk(G, C_root, n_root, True{}, True{}, buf2), hgs)
      +hbuf2 = Arr.Arr.dpair_r(
                 FH.FH.GuessWit<G, C_root, n_root, True{}, True{}, g, S, n, 0n,
                   SolveFast.dummy_inf(0n), items>,
                 FH.FH.BufOk(G, C_root, n_root, True{}, True{}, buf2), hgs)
      Arr.DPair{GR.exp_of_guess_wit(G, C_root, n_root, g, S, n, items, wg, gw),
        hbuf2}

def GR.fill_drain_exp_ok(+G: +List<+List<Nat>>, +C_root: +List<+List<Nat>>,
    +n_root: Nat, +row: U32, +g: +List<Nat>, +S: +List<SolveFast.CWord>,
    +n: Nat, seen: Array<Nat>, bkts: Array<+List<SolveFast.CWord>>,
    tbl: Array<U32>, +gen: Nat,
    +hrow: {FT.FT.gentry_ok_b(G, n_root, row, g) == True{} : Bool},
    +hwg: {Tree.member_word(g, G) == True{} : Bool},
    +hS: {FT.FT.cwords_ok_b(G, C_root, n_root, S) == True{} : Bool},
    +hus: {Groups.groups_smaller(SolveFast.cwords_words(S),
             Groups.groups_build(g, SolveFast.cwords_words(S), Nil{}))
           == True{} : Bool},
    +hnd: {FN.FN.no_dup_ref(SolveFast.cwords_words(S)) == True{} : Bool},
    +hs: FH.FH.SeenTree(10n, 0, seen, gen, Nil{}),
    +hb: FH.FH.BktTree(G, C_root, n_root, 10n, 0, bkts, Nil{}),
    +ht: FT.FT.TblOk(G, C_root, n_root, tbl)) ->
  GR.ExpSpec(G, C_root, n_root, SolveFast.cwords_words(S), n,
    SolveFast.run_drain5(g, n, seen, gen,
      SolveFast.fill5_go(row, S, SolveFast.Fill5State{bkts, tbl, Nil{}}))):
  +ws = SolveFast.cwords_words(S)
  GR.with_dup_arr(+List<SolveFast.CWord>,
    GR.ExpSpec(G, C_root, n_root, ws, n,
      SolveFast.run_drain5(g, n, seen, gen,
        SolveFast.fill5_go(row, S, SolveFast.Fill5State{bkts, tbl, Nil{}}))),
    bkts,
    b_f => br1 => +eb_f => +ebr1 =>
    GR.with_dup_arr(+List<SolveFast.CWord>,
      GR.ExpSpec(G, C_root, n_root, ws, n,
        SolveFast.run_drain5(g, n, seen, gen,
          SolveFast.fill5_go(row, S, SolveFast.Fill5State{bkts, tbl, Nil{}}))),
      br1,
      b_d => b_r => +eb_dr => +eb_rr =>
      GR.with_dup_arr(U32,
        GR.ExpSpec(G, C_root, n_root, ws, n,
          SolveFast.run_drain5(g, n, seen, gen,
            SolveFast.fill5_go(row, S, SolveFast.Fill5State{bkts, tbl, Nil{}}))),
        tbl,
        t_f => tr1 => +et_f => +etr1 =>
        GR.with_dup_arr(U32,
          GR.ExpSpec(G, C_root, n_root, ws, n,
            SolveFast.run_drain5(g, n, seen, gen,
              SolveFast.fill5_go(row, S, SolveFast.Fill5State{bkts, tbl, Nil{}}))),
          tr1,
          t_d => t_r => +et_dr => +et_rr =>
          +eb_d : {b_d == bkts : Array<+List<SolveFast.CWord>>} =
            Equal.trans(Array<+List<SolveFast.CWord>>, b_d, br1, bkts,
              eb_dr, ebr1)
          +eb_r : {b_r == bkts : Array<+List<SolveFast.CWord>>} =
            Equal.trans(Array<+List<SolveFast.CWord>>, b_r, br1, bkts,
              eb_rr, ebr1)
          +et_d : {t_d == tbl : Array<U32>} =
            Equal.trans(Array<U32>, t_d, tr1, tbl, et_dr, etr1)
          +et_r : {t_r == tbl : Array<U32>} =
            Equal.trans(Array<U32>, t_r, tr1, tbl, et_rr, etr1)
          +hb_f = FH.FH.bkt_tree_transport(G, C_root, n_root, 10n, 0, bkts, b_f,
                    Nil{},
                    Equal.sym(Array<+List<SolveFast.CWord>>, b_f, bkts, eb_f),
                    hb)
          +ht_f = FT.FT.tbl_ok_transport(G, C_root, n_root, tbl, t_f,
                    Equal.sym(Array<U32>, t_f, tbl, et_f), ht)
          +hfs_f = FH.FH.fill5_go_spec(S, G, C_root, n_root, row, g, Nil{}, b_f,
                     t_f, Nil{}, Nil{}, ht_f, hrow, hS, {==}, {==}, hb_f)
          +eb_fd : {b_f == b_d : Array<+List<SolveFast.CWord>>} =
            Equal.trans(Array<+List<SolveFast.CWord>>, b_f, bkts, b_d, eb_f,
              Equal.sym(Array<+List<SolveFast.CWord>>, b_d, bkts, eb_d))
          +et_fd : {t_f == t_d : Array<U32>} =
            Equal.trans(Array<U32>, t_f, tbl, t_d, et_f,
              Equal.sym(Array<U32>, t_d, tbl, et_d))
          +hfs_d : FH.FH.FillSpec(G, C_root, n_root,
                     SolveFast.fgroups_build_fast(g, ws, Nil{}), Nil{}, t_f,
                     SolveFast.fill5_go(row, S,
                       SolveFast.Fill5State{b_d, t_d, Nil{}})) =
            %eb_fd : FH.FH.FillSpec(G, C_root, n_root,
                       SolveFast.fgroups_build_fast(g, ws, Nil{}), Nil{}, t_f,
                       SolveFast.fill5_go(row, S,
                         SolveFast.Fill5State{_, t_d, Nil{}}))
            %et_fd : FH.FH.FillSpec(G, C_root, n_root,
                       SolveFast.fgroups_build_fast(g, ws, Nil{}), Nil{}, t_f,
                       SolveFast.fill5_go(row, S,
                         SolveFast.Fill5State{b_f, _, Nil{}}))
            hfs_f
          +hgs_d = FH.FH.run_drain5_spec(G, C_root, n_root, g, ws, n, 0n,
                     SolveFast.dummy_inf(0n), seen, t_f, gen,
                     SolveFast.fill5_go(row, S,
                       SolveFast.Fill5State{b_d, t_d, Nil{}}),
                     hus, hnd, hs, ht_f, hfs_d)
          +eb_dr2 : {b_d == b_r : Array<+List<SolveFast.CWord>>} =
            Equal.trans(Array<+List<SolveFast.CWord>>, b_d, bkts, b_r, eb_d,
              Equal.sym(Array<+List<SolveFast.CWord>>, b_r, bkts, eb_r))
          +et_dr2 : {t_d == t_r : Array<U32>} =
            Equal.trans(Array<U32>, t_d, tbl, t_r, et_d,
              Equal.sym(Array<U32>, t_r, tbl, et_r))
          +hgs_r : FH.FH.GuessSpec(G, C_root, n_root, True{}, True{}, g, ws, n,
                     0n, SolveFast.dummy_inf(0n),
                     SolveFast.run_drain5(g, n, seen, gen,
                       SolveFast.fill5_go(row, S,
                         SolveFast.Fill5State{b_r, t_r, Nil{}}))) =
            %eb_dr2 : FH.FH.GuessSpec(G, C_root, n_root, True{}, True{}, g, ws,
                        n, 0n, SolveFast.dummy_inf(0n),
                        SolveFast.run_drain5(g, n, seen, gen,
                          SolveFast.fill5_go(row, S,
                            SolveFast.Fill5State{_, t_r, Nil{}})))
            %et_dr2 : FH.FH.GuessSpec(G, C_root, n_root, True{}, True{}, g, ws,
                        n, 0n, SolveFast.dummy_inf(0n),
                        SolveFast.run_drain5(g, n, seen, gen,
                          SolveFast.fill5_go(row, S,
                            SolveFast.Fill5State{b_d, _, Nil{}})))
            hgs_d
          +hexp = GR.exp_of_guess_spec(G, C_root, n_root, g, ws, n, hwg,
                    SolveFast.run_drain5(g, n, seen, gen,
                      SolveFast.fill5_go(row, S,
                        SolveFast.Fill5State{b_r, t_r, Nil{}})), hgs_r)
          %eb_r : GR.ExpSpec(G, C_root, n_root, ws, n,
                    SolveFast.run_drain5(g, n, seen, gen,
                      SolveFast.fill5_go(row, S,
                        SolveFast.Fill5State{_, tbl, Nil{}})))
          %et_r : GR.ExpSpec(G, C_root, n_root, ws, n,
                    SolveFast.run_drain5(g, n, seen, gen,
                      SolveFast.fill5_go(row, S,
                        SolveFast.Fill5State{b_r, _, Nil{}})))
          hexp))))

def GR.gpick_split_ok(+G: +List<+List<Nat>>, +C_root: +List<+List<Nat>>,
    +n_root: Nat, +S: +List<SolveFast.CWord>, +n: Nat,
    bkts: Array<+List<SolveFast.CWord>>, st: Greedy.GPickSt,
    +hS: {FT.FT.cwords_ok_b(G, C_root, n_root, S) == True{} : Bool},
    +hnd: {FN.FN.no_dup_ref(SolveFast.cwords_words(S)) == True{} : Bool},
    +hb: FH.FH.BktTree(G, C_root, n_root, 10n, 0, bkts, Nil{}),
    +hst: GR.GPickInv(G, C_root, n_root, SolveFast.cwords_words(S), st)) ->
  GR.ExpSpec(G, C_root, n_root, SolveFast.cwords_words(S), n,
    Greedy.gpick_split(S, n, bkts, st)):
  match st:
    case Greedy.GPickOk{seen, tbl, +gen, +has, +brow, +bg, +blb, hit}:
      match has:
        case False{}:
          +ws = SolveFast.cwords_words(S)
          +hs = Arr.Arr.dpair_l(FH.FH.SeenTree(10n, 0, seen, gen, Nil{}),
                  Arr.Arr.DPair<FT.FT.TblOk(G, C_root, n_root, tbl),
                    GR.HasOk(G, n_root, ws, False{}, brow, bg)>, hst)
          +hrr = Arr.Arr.dpair_r(FH.FH.SeenTree(10n, 0, seen, gen, Nil{}),
                   Arr.Arr.DPair<FT.FT.TblOk(G, C_root, n_root, tbl),
                     GR.HasOk(G, n_root, ws, False{}, brow, bg)>, hst)
          +ht = Arr.Arr.dpair_l(FT.FT.TblOk(G, C_root, n_root, tbl),
                  GR.HasOk(G, n_root, ws, False{}, brow, bg), hrr)
          Arr.DPair{ExpNil{{==}},
            Arr.DPair{{==}, Arr.DPair{hs, Arr.DPair{hb, ht}}}}
        case True{}:
          +ws = SolveFast.cwords_words(S)
          +hs = Arr.Arr.dpair_l(FH.FH.SeenTree(10n, 0, seen, gen, Nil{}),
                  Arr.Arr.DPair<FT.FT.TblOk(G, C_root, n_root, tbl),
                    GR.HasOk(G, n_root, ws, True{}, brow, bg)>, hst)
          +hrr = Arr.Arr.dpair_r(FH.FH.SeenTree(10n, 0, seen, gen, Nil{}),
                   Arr.Arr.DPair<FT.FT.TblOk(G, C_root, n_root, tbl),
                     GR.HasOk(G, n_root, ws, True{}, brow, bg)>, hst)
          +ht = Arr.Arr.dpair_l(FT.FT.TblOk(G, C_root, n_root, tbl),
                  GR.HasOk(G, n_root, ws, True{}, brow, bg), hrr)
          +hh = Arr.Arr.dpair_r(FT.FT.TblOk(G, C_root, n_root, tbl),
                  GR.HasOk(G, n_root, ws, True{}, brow, bg), hrr)
          +hrow = Arr.Arr.dpair_l(
                    {FT.FT.gentry_ok_b(G, n_root, brow, bg) == True{} : Bool},
                    Arr.Arr.DPair<{Tree.member_word(bg, G) == True{} : Bool},
                      {Groups.groups_smaller(ws,
                         Groups.groups_build(bg, ws, Nil{})) == True{} : Bool}>,
                    hh)
          +hhr = Arr.Arr.dpair_r(
                   {FT.FT.gentry_ok_b(G, n_root, brow, bg) == True{} : Bool},
                   Arr.Arr.DPair<{Tree.member_word(bg, G) == True{} : Bool},
                     {Groups.groups_smaller(ws,
                        Groups.groups_build(bg, ws, Nil{})) == True{} : Bool}>,
                   hh)
          +hwg = Arr.Arr.dpair_l({Tree.member_word(bg, G) == True{} : Bool},
                   {Groups.groups_smaller(ws,
                      Groups.groups_build(bg, ws, Nil{})) == True{} : Bool},
                   hhr)
          +hus = Arr.Arr.dpair_r({Tree.member_word(bg, G) == True{} : Bool},
                   {Groups.groups_smaller(ws,
                      Groups.groups_build(bg, ws, Nil{})) == True{} : Bool},
                   hhr)
          GR.fill_drain_exp_ok(G, C_root, n_root, brow, bg, S, n, seen, bkts,
            tbl, gen, hrow, hwg, hS, hus, hnd, hs, hb, ht)

def GR.greedy_expand_spec(+G: +List<+List<Nat>>, +C_root: +List<+List<Nat>>,
    +n_root: Nat, +gG: SolveFast.GList, +S: +List<SolveFast.CWord>, +n: Nat,
    buf: SolveFast.Buf5,
    +hgG: {GR.glist_ok_b(G, n_root, gG) == True{} : Bool},
    +hge1: {Nat.is_le(1n, n) == True{} : Bool},
    +en: {n == Groups.len_words(SolveFast.cwords_words(S)) : Nat},
    +hS: {FT.FT.cwords_ok_b(G, C_root, n_root, S) == True{} : Bool},
    +hai: {FO.FO.all_in_ref(SolveFast.cwords_words(S), G) == True{} : Bool},
    +hnd: {FN.FN.no_dup_ref(SolveFast.cwords_words(S)) == True{} : Bool},
    +hbuf: FH.FH.BufOk(G, C_root, n_root, True{}, True{}, buf)) ->
  GR.ExpSpec(G, C_root, n_root, SolveFast.cwords_words(S), n,
    Greedy.greedy_expand(gG, S, n, buf)):
  match buf:
    case SolveFast.NoBuf{}:
      Empty.absurd(
        GR.ExpSpec(G, C_root, n_root, SolveFast.cwords_words(S), n,
          SolveFast.GuessRes{Nil{}, SolveFast.NoBuf{}}), hbuf)
    case SolveFast.Buf5{seen, bkts, tbl, +gen}:
      +ws = SolveFast.cwords_words(S)
      +r1 = Arr.Arr.dpair_r({True{} == True{} : Bool},
              Arr.Arr.DPair<FH.FH.SeenTree(10n, 0, seen, gen, Nil{}),
                Arr.Arr.DPair<FH.FH.BktTree(G, C_root, n_root, 10n, 0, bkts, Nil{}),
                  FT.FT.TblOk(G, C_root, n_root, tbl)>>, hbuf)
      +hs = Arr.Arr.dpair_l(FH.FH.SeenTree(10n, 0, seen, gen, Nil{}),
              Arr.Arr.DPair<FH.FH.BktTree(G, C_root, n_root, 10n, 0, bkts, Nil{}),
                FT.FT.TblOk(G, C_root, n_root, tbl)>, r1)
      +r2 = Arr.Arr.dpair_r(FH.FH.SeenTree(10n, 0, seen, gen, Nil{}),
              Arr.Arr.DPair<FH.FH.BktTree(G, C_root, n_root, 10n, 0, bkts, Nil{}),
                FT.FT.TblOk(G, C_root, n_root, tbl)>, r1)
      +hb = Arr.Arr.dpair_l(FH.FH.BktTree(G, C_root, n_root, 10n, 0, bkts, Nil{}),
              FT.FT.TblOk(G, C_root, n_root, tbl), r2)
      +ht = Arr.Arr.dpair_r(FH.FH.BktTree(G, C_root, n_root, 10n, 0, bkts, Nil{}),
              FT.FT.TblOk(G, C_root, n_root, tbl), r2)
      +fl = SolveFast.init_floor(n)
      +q = SolveFast.glist_of_cwords(S, SolveFast.GThen{gG})
      +hq = GR.glist_of_cwords_ok(G, C_root, n_root, S, SolveFast.GThen{gG},
              hS, hai, hgG)
      GR.with_dup_arr(Nat,
        GR.ExpSpec(G, C_root, n_root, ws, n,
          Greedy.gpick_split(S, n, bkts,
            Greedy.gpick_loop(q, S, n, fl, False{},
              Greedy.GPickOk{seen, tbl, gen, False{}, 0, Nil{}, 0n, False{}}))),
        seen,
        s1 => s2 => +es1 => +es2 =>
        GR.with_dup_arr(U32,
          GR.ExpSpec(G, C_root, n_root, ws, n,
            Greedy.gpick_split(S, n, bkts,
              Greedy.gpick_loop(q, S, n, fl, False{},
                Greedy.GPickOk{seen, tbl, gen, False{}, 0, Nil{}, 0n, False{}}))),
          tbl,
          t1 => t2 => +et1 => +et2 =>
          +hs1 = FH.FH.seen_tree_transport(10n, 0, seen, s1, gen, Nil{},
                   Equal.sym(Array<Nat>, s1, seen, es1), hs)
          +ht1 = FT.FT.tbl_ok_transport(G, C_root, n_root, tbl, t1,
                   Equal.sym(Array<U32>, t1, tbl, et1), ht)
          +hst0 : GR.GPickInv(G, C_root, n_root, ws,
                    Greedy.GPickOk{s1, t1, gen, False{}, 0, Nil{}, 0n, False{}}) =
            Arr.DPair{hs1, Arr.DPair{ht1, Unit{}}}
          +hl1 = GR.gpick_loop_ok(q, G, C_root, n_root, S, n, fl, False{},
                   Greedy.GPickOk{s1, t1, gen, False{}, 0, Nil{}, 0n, False{}},
                   hq, hge1, en, hS, hst0)
          +es12 : {s1 == s2 : Array<Nat>} =
            Equal.trans(Array<Nat>, s1, seen, s2, es1,
              Equal.sym(Array<Nat>, s2, seen, es2))
          +et12 : {t1 == t2 : Array<U32>} =
            Equal.trans(Array<U32>, t1, tbl, t2, et1,
              Equal.sym(Array<U32>, t2, tbl, et2))
          +hl2 : GR.GPickInv(G, C_root, n_root, ws,
                   Greedy.gpick_loop(q, S, n, fl, False{},
                     Greedy.GPickOk{s2, t2, gen, False{}, 0, Nil{}, 0n, False{}})) =
            %es12 : GR.GPickInv(G, C_root, n_root, ws,
                      Greedy.gpick_loop(q, S, n, fl, False{},
                        Greedy.GPickOk{_, t2, gen, False{}, 0, Nil{}, 0n, False{}}))
            %et12 : GR.GPickInv(G, C_root, n_root, ws,
                      Greedy.gpick_loop(q, S, n, fl, False{},
                        Greedy.GPickOk{s1, _, gen, False{}, 0, Nil{}, 0n, False{}}))
            hl1
          +hsp = GR.gpick_split_ok(G, C_root, n_root, S, n, bkts,
                   Greedy.gpick_loop(q, S, n, fl, False{},
                     Greedy.GPickOk{s2, t2, gen, False{}, 0, Nil{}, 0n, False{}}),
                   hS, hnd, hb, hl2)
          %es2 : GR.ExpSpec(G, C_root, n_root, ws, n,
                   Greedy.gpick_split(S, n, bkts,
                     Greedy.gpick_loop(q, S, n, fl, False{},
                       Greedy.GPickOk{_, tbl, gen, False{}, 0, Nil{}, 0n, False{}})))
          %et2 : GR.ExpSpec(G, C_root, n_root, ws, n,
                   Greedy.gpick_split(S, n, bkts,
                     Greedy.gpick_loop(q, S, n, fl, False{},
                       Greedy.GPickOk{s2, _, gen, False{}, 0, Nil{}, 0n, False{}})))
          hsp))

def GR.greedy_expand_forced_spec(+G: +List<+List<Nat>>,
    +C_root: +List<+List<Nat>>, +n_root: Nat,
    +row: U32, +g: +List<Nat>, +S: +List<SolveFast.CWord>, +n: Nat,
    buf: SolveFast.Buf5,
    +hrow: {FT.FT.gentry_ok_b(G, n_root, row, g) == True{} : Bool},
    +hwg: {Tree.member_word(g, G) == True{} : Bool},
    +hS: {FT.FT.cwords_ok_b(G, C_root, n_root, S) == True{} : Bool},
    +hus: {Groups.groups_smaller(SolveFast.cwords_words(S),
             Groups.groups_build(g, SolveFast.cwords_words(S), Nil{}))
           == True{} : Bool},
    +hnd: {FN.FN.no_dup_ref(SolveFast.cwords_words(S)) == True{} : Bool},
    +hbuf: FH.FH.BufOk(G, C_root, n_root, True{}, True{}, buf)) ->
  GR.ExpSpec(G, C_root, n_root, SolveFast.cwords_words(S), n,
    Greedy.greedy_expand_forced(row, g, S, n, buf)):
  match buf:
    case SolveFast.NoBuf{}:
      Empty.absurd(
        GR.ExpSpec(G, C_root, n_root, SolveFast.cwords_words(S), n,
          SolveFast.GuessRes{Nil{}, SolveFast.NoBuf{}}), hbuf)
    case SolveFast.Buf5{seen, bkts, tbl, +gen}:
      +r1 = Arr.Arr.dpair_r({True{} == True{} : Bool},
              Arr.Arr.DPair<FH.FH.SeenTree(10n, 0, seen, gen, Nil{}),
                Arr.Arr.DPair<FH.FH.BktTree(G, C_root, n_root, 10n, 0, bkts, Nil{}),
                  FT.FT.TblOk(G, C_root, n_root, tbl)>>, hbuf)
      +hs = Arr.Arr.dpair_l(FH.FH.SeenTree(10n, 0, seen, gen, Nil{}),
              Arr.Arr.DPair<FH.FH.BktTree(G, C_root, n_root, 10n, 0, bkts, Nil{}),
                FT.FT.TblOk(G, C_root, n_root, tbl)>, r1)
      +r2 = Arr.Arr.dpair_r(FH.FH.SeenTree(10n, 0, seen, gen, Nil{}),
              Arr.Arr.DPair<FH.FH.BktTree(G, C_root, n_root, 10n, 0, bkts, Nil{}),
                FT.FT.TblOk(G, C_root, n_root, tbl)>, r1)
      +hb = Arr.Arr.dpair_l(FH.FH.BktTree(G, C_root, n_root, 10n, 0, bkts, Nil{}),
              FT.FT.TblOk(G, C_root, n_root, tbl), r2)
      +ht = Arr.Arr.dpair_r(FH.FH.BktTree(G, C_root, n_root, 10n, 0, bkts, Nil{}),
              FT.FT.TblOk(G, C_root, n_root, tbl), r2)
      GR.fill_drain_exp_ok(G, C_root, n_root, row, g, S, n, seen, bkts, tbl,
        gen, hrow, hwg, hS, hus, hnd, hs, hb, ht)

# Specification of `Greedy.greedy_step`: valid tree with cost <= returned cost,
# plus valid threaded `Buf5`.
def GR.GreedySpec(+G: +List<+List<Nat>>, +C_root: +List<+List<Nat>>,
    +n_root: Nat, +S: +List<+List<Nat>>, gr: Greedy.GreedyRes) -> Data:
  match gr:
    case Greedy.GreedyFail{buf2}:
      FH.FH.BufOk(G, C_root, n_root, True{}, True{}, buf2)
    case Greedy.GreedyOk{tree, cost, buf2}:
      Arr.Arr.DPair<
        {Bool.and(FVal.FV.valid_b(tree, G, S),
           Nat.is_le(Tree.cost(tree, S), cost)) == True{} : Bool},
        FH.FH.BufOk(G, C_root, n_root, True{}, True{}, buf2)>

def GR.kids_step_match(+G: +List<+List<Nat>>, +fb: +List<Feedback.Color>,
    +f: +List<Feedback.Color>, +ws: +List<+List<Nat>>, +tr: Tree.Tree,
    +done_rev: +List<Groups.Group>, +kids: +List<Tree.Child>,
    +ef: {f == fb : +List<Feedback.Color>},
    +hv: {FVal.FV.valid_b(tr, G, ws) == True{} : Bool},
    +hm: {FVal.FV.kids_match_b(G, done_rev, kids) == True{} : Bool}) ->
  {FVal.FV.kids_match_b(G, Groups.Group{fb, ws} <> done_rev,
     Tree.Child{f, tr} <> kids) == True{} : Bool}:
  +hfb : {Feedback.feedback_eq(fb, f) == True{} : Bool} =
    Equal.trans(Bool, Feedback.feedback_eq(fb, f), Feedback.feedback_eq(fb, fb),
      True{},
      Equal.cong(+List<Feedback.Color>, Bool, x => Feedback.feedback_eq(fb, x),
        f, fb, ef),
      FbProof.FbPrf.feedback_eq_refl(fb))
  FO.FO.bool_and_intro(Feedback.feedback_eq(fb, f),
    Bool.and(FVal.FV.valid_b(tr, G, ws),
      FVal.FV.kids_match_b(G, done_rev, kids)),
    hfb,
    FO.FO.bool_and_intro(FVal.FV.valid_b(tr, G, ws),
      FVal.FV.kids_match_b(G, done_rev, kids), hv, hm))

def GR.kids_step_cost(+fb: +List<Feedback.Color>, +f: +List<Feedback.Color>,
    +ws: +List<+List<Nat>>, +tr: Tree.Tree, +c: Nat,
    +done_rev: +List<Groups.Group>, +kids: +List<Tree.Child>, +sum: Nat,
    +hc: {Nat.is_le(Tree.cost(tr, ws), c) == True{} : Bool},
    +hcs: {Nat.is_le(FVal.FV.kids_cost_sum(done_rev, kids), sum)
           == True{} : Bool}) ->
  {Nat.is_le(
     FVal.FV.kids_cost_sum(Groups.Group{fb, ws} <> done_rev,
       Tree.Child{f, tr} <> kids),
     Nat.add(sum, c)) == True{} : Bool}:
  NatProof.Nat.is_le_eq_r(
    Nat.add(Tree.cost(tr, ws), FVal.FV.kids_cost_sum(done_rev, kids)),
    Nat.add(c, sum), Nat.add(sum, c), NatProof.NatPrf.add_comm(c, sum),
    FT.FT.nat_add_le_add(Tree.cost(tr, ws), c,
      FVal.FV.kids_cost_sum(done_rev, kids), sum, hc, hcs))

def GR.greedy_add_step(+p: Nat, +G: +List<+List<Nat>>,
    +C_root: +List<+List<Nat>>, +n_root: Nat, +gG: SolveFast.GList,
    +cwS: +List<SolveFast.CWord>, +S: +List<+List<Nat>>, +n: Nat,
    +g: +List<Nat>, +fb: +List<Feedback.Color>, +f2: +List<Feedback.Color>,
    +tlb2: Nat, +ws: +List<+List<Nat>>, +restb: +List<SolveFast.Item>,
    +done_rev: +List<Groups.Group>, +kids: +List<Tree.Child>, +sum: Nat,
    pending: Greedy.GreedyRes,
    +ef2: {f2 == fb : +List<Feedback.Color>},
    +hm: {FVal.FV.kids_match_b(G, done_rev, kids) == True{} : Bool},
    +hcs: {Nat.is_le(FVal.FV.kids_cost_sum(done_rev, kids), sum)
           == True{} : Bool},
    +hpend: GR.GreedySpec(G, C_root, n_root, ws, pending),
    k_cont: @tr: Tree.Tree -> @c: Nat -> @pbuf: SolveFast.Buf5 ->
            FH.FH.BufOk(G, C_root, n_root, True{}, True{}, pbuf) ->
            {FVal.FV.kids_match_b(G, Groups.Group{fb, ws} <> done_rev,
               Tree.Child{f2, tr} <> kids) == True{} : Bool} ->
            {Nat.is_le(
               FVal.FV.kids_cost_sum(Groups.Group{fb, ws} <> done_rev,
                 Tree.Child{f2, tr} <> kids),
               Nat.add(sum, c)) == True{} : Bool} ->
            GR.GreedySpec(G, C_root, n_root, S,
              Greedy.greedy_step(1n+p, 0n, restb, gG, cwS, n, g,
                Tree.Child{f2, tr} <> kids, Nat.add(sum, c),
                Greedy.GreedyFail{SolveFast.NoBuf{}},
                SolveFast.GuessRes{Nil{}, pbuf}))) ->
  GR.GreedySpec(G, C_root, n_root, S,
    Greedy.greedy_step(1n+p, 0n, SolveFast.Add{f2, tlb2} <> restb, gG, cwS, n,
      g, kids, sum, pending, SolveFast.GuessRes{Nil{}, SolveFast.NoBuf{}})):
  match pending:
    case Greedy.GreedyFail{pbuf}:
      hpend
    case Greedy.GreedyOk{+tr, +c, pbuf}:
      +hvc = Arr.Arr.dpair_l(
               {Bool.and(FVal.FV.valid_b(tr, G, ws),
                  Nat.is_le(Tree.cost(tr, ws), c)) == True{} : Bool},
               FH.FH.BufOk(G, C_root, n_root, True{}, True{}, pbuf), hpend)
      +hpbuf = Arr.Arr.dpair_r(
                 {Bool.and(FVal.FV.valid_b(tr, G, ws),
                    Nat.is_le(Tree.cost(tr, ws), c)) == True{} : Bool},
                 FH.FH.BufOk(G, C_root, n_root, True{}, True{}, pbuf), hpend)
      +hv = Logic.Proof.and_true_l(FVal.FV.valid_b(tr, G, ws),
              Nat.is_le(Tree.cost(tr, ws), c), hvc)
      +hc = Logic.Proof.and_true_r(FVal.FV.valid_b(tr, G, ws),
              Nat.is_le(Tree.cost(tr, ws), c), hvc)
      k_cont(tr, c, pbuf, hpbuf,
        GR.kids_step_match(G, fb, f2, ws, tr, done_rev, kids, ef2, hv, hm),
        GR.kids_step_cost(fb, f2, ws, tr, c, done_rev, kids, sum, hc, hcs))

def GR.GJob(+fuel: Nat, +G: +List<+List<Nat>>, +C_root: +List<+List<Nat>>,
    +n_root: Nat, +gG: SolveFast.GList, +ws: +List<+List<Nat>>) -> Type:
  @cws: +List<SolveFast.CWord> -> @wlen: Nat -> @b_in: SolveFast.Buf5 ->
  {SolveFast.cwords_words(cws) == ws : +List<+List<Nat>>} ->
  {wlen == Groups.len_words(ws) : Nat} ->
  {FT.FT.cwords_ok_b(G, C_root, n_root, cws) == True{} : Bool} ->
  FH.FH.BufOk(G, C_root, n_root, True{}, True{}, b_in) ->
  GR.GreedySpec(G, C_root, n_root, ws,
    Greedy.greedy_step(fuel, 2n, Nil{}, gG, cws, wlen, Nil{}, Nil{}, 0n,
      Greedy.GreedyFail{SolveFast.NoBuf{}},
      SolveFast.GuessRes{Nil{}, b_in}))

def GR.GJobs(+fuel: Nat, +G: +List<+List<Nat>>, +C_root: +List<+List<Nat>>,
    +n_root: Nat, +gG: SolveFast.GList, +jobs: +List<+List<+List<Nat>>>) -> Type:
  match jobs:
    case Nil{}:
      Unit
    case Con{ws, rest}:
      GR.GJob(fuel, G, C_root, n_root, gG, ws)
      & GR.GJobs(fuel, G, C_root, n_root, gG, rest)

def GR.gjobs_split(+fuel: Nat, +G: +List<+List<Nat>>,
    +C_root: +List<+List<Nat>>, +n_root: Nat, +gG: SolveFast.GList,
    +xs: +List<+List<+List<Nat>>>, +ys: +List<+List<+List<Nat>>>,
    gj: GR.GJobs(fuel, G, C_root, n_root, gG,
          List.append(&2, +List<+List<Nat>>, xs, ys))) ->
  GR.GJobs(fuel, G, C_root, n_root, gG, xs)
  & GR.GJobs(fuel, G, C_root, n_root, gG, ys):
  match xs:
    case Nil{}:
      (Unit{}, gj)
    case Con{+w, +t}:
      (hw, gt) = gj
      MV.MV.use_pair(
        GR.GJobs(fuel, G, C_root, n_root, gG, w <> t)
        & GR.GJobs(fuel, G, C_root, n_root, gG, ys),
        GR.GJobs(fuel, G, C_root, n_root, gG, t),
        GR.GJobs(fuel, G, C_root, n_root, gG, ys),
        GR.gjobs_split(fuel, G, C_root, n_root, gG, t, ys, gt),
        gx => gy => ((hw, gx), gy))

def GR.gjobs_pick_guess(+p: Nat, +G: +List<+List<Nat>>,
    +C_root: +List<+List<Nat>>, +n_root: Nat, +gG: SolveFast.GList,
    +gs: +List<+List<Nat>>, +S: +List<+List<Nat>>, +g: +List<Nat>,
    +hm: {Tree.member_word(g, gs) == True{} : Bool},
    +hus: {Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{}))
           == True{} : Bool},
    gj: GR.GJobs(p, G, C_root, n_root, gG, MV.MV.next_guess(gs, S))) ->
  GR.GJobs(p, G, C_root, n_root, gG,
    MV.MV.next_groups(Groups.groups_build(g, S, Nil{}))):
  match gs:
    case Nil{}:
      Empty.absurd(
        GR.GJobs(p, G, C_root, n_root, gG,
          MV.MV.next_groups(Groups.groups_build(g, S, Nil{}))),
        Logic.Proof.false_ne_true(hm))
    case Con{+h, +t}:
      MV.MV.use_pair(
        GR.GJobs(p, G, C_root, n_root, gG,
          MV.MV.next_groups(Groups.groups_build(g, S, Nil{}))),
        GR.GJobs(p, G, C_root, n_root, gG, MV.MV.classes(h, S)),
        GR.GJobs(p, G, C_root, n_root, gG, MV.MV.next_guess(t, S)),
        GR.gjobs_split(p, G, C_root, n_root, gG, MV.MV.classes(h, S),
          MV.MV.next_guess(t, S), gj),
        gh => gt =>
          GR.member_cons_split(
            GR.GJobs(p, G, C_root, n_root, gG,
              MV.MV.next_groups(Groups.groups_build(g, S, Nil{}))),
            g, h, t, hm,
            +egh =>
              +ecl : {MV.MV.classes(h, S)
                      == MV.MV.next_groups(Groups.groups_build(g, S, Nil{}))
                      : +List<+List<+List<Nat>>>} =
                Equal.trans(+List<+List<+List<Nat>>>,
                  MV.MV.classes(h, S),
                  MV.MV.classes(g, S),
                  MV.MV.next_groups(Groups.groups_build(g, S, Nil{})),
                  Equal.cong(+List<Nat>, +List<+List<+List<Nat>>>,
                    x => MV.MV.classes(x, S), h, g,
                    Equal.sym(+List<Nat>, g, h, egh)),
                  Equal.cong(Bool, +List<+List<+List<Nat>>>,
                    b => MV.MV.classes_b(b, Groups.groups_build(g, S, Nil{})),
                    Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
                    True{}, hus))
              %ecl : GR.GJobs(p, G, C_root, n_root, gG, _)
              gh,
            +hmt =>
              GR.gjobs_pick_guess(p, G, C_root, n_root, gG, t, S, g, hmt, hus,
                gt)))

def GR.gjobs_skip_go(+p: Nat, +G: +List<+List<Nat>>,
    +C_root: +List<+List<Nat>>, +n_root: Nat, +gG: SolveFast.GList,
    +fx: +List<Feedback.Color>, +wx: +List<+List<Nat>>,
    +tx: +List<Groups.Group>, +ty: +List<Groups.Group>,
    gj: GR.GJobs(p, G, C_root, n_root, gG,
          MV.MV.next_groups(Groups.Group{fx, wx} <> tx)),
    k: GR.GJobs(p, G, C_root, n_root, gG, MV.MV.next_groups(tx)) ->
       GR.GJobs(p, G, C_root, n_root, gG, MV.MV.next_groups(ty))) ->
  GR.GJobs(p, G, C_root, n_root, gG,
    MV.MV.next_groups(Groups.Group{fx, wx} <> ty)):
  (h1, gt) = gj
  (h1, k(gt))

def GR.gjobs_swap_go(+p: Nat, +G: +List<+List<Nat>>,
    +C_root: +List<+List<Nat>>, +n_root: Nat, +gG: SolveFast.GList,
    +fa: +List<Feedback.Color>, +wa: +List<+List<Nat>>,
    +fb2: +List<Feedback.Color>, +wb: +List<+List<Nat>>,
    +tx: +List<Groups.Group>,
    gj: GR.GJobs(p, G, C_root, n_root, gG,
          MV.MV.next_groups(
            Groups.Group{fa, wa} <> (Groups.Group{fb2, wb} <> tx)))) ->
  GR.GJobs(p, G, C_root, n_root, gG,
    MV.MV.next_groups(
      Groups.Group{fb2, wb} <> (Groups.Group{fa, wa} <> tx))):
  (ha, r2) = gj
  (hb, gt) = r2
  (hb, (ha, gt))

def GR.gjobs_perm(perm: FP.FP.Perm, +p: Nat, +G: +List<+List<Nat>>,
    +C_root: +List<+List<Nat>>, +n_root: Nat, +gG: SolveFast.GList,
    +xs: +List<Groups.Group>, +ys: +List<Groups.Group>,
    +ok: FP.FP.PermOk(perm, xs, ys),
    gj: GR.GJobs(p, G, C_root, n_root, gG, MV.MV.next_groups(xs))) ->
  GR.GJobs(p, G, C_root, n_root, gG, MV.MV.next_groups(ys)):
  match perm:
    case FP.PRefl{}:
      %ok : GR.GJobs(p, G, C_root, n_root, gG, MV.MV.next_groups(_))
      gj
    case FP.PSkip{pr}:
      match xs:
        case Nil{}:
          Empty.absurd(
            GR.GJobs(p, G, C_root, n_root, gG, MV.MV.next_groups(ys)), ok)
        case Con{hx, tx}:
          match hx:
            case Groups.Group{+fx, +wx}:
              match ys:
                case Nil{}:
                  Empty.absurd(
                    GR.GJobs(p, G, C_root, n_root, gG, Nil{}), ok)
                case Con{hy, ty}:
                  +eh = Arr.Arr.dpair_l(
                          {Groups.Group{fx, wx} == hy : Groups.Group},
                          FP.FP.PermOk(pr, tx, ty), ok)
                  +et = Arr.Arr.dpair_r(
                          {Groups.Group{fx, wx} == hy : Groups.Group},
                          FP.FP.PermOk(pr, tx, ty), ok)
                  %eh : GR.GJobs(p, G, C_root, n_root, gG,
                          MV.MV.next_groups(_ <> ty))
                  GR.gjobs_skip_go(p, G, C_root, n_root, gG, fx, wx, tx, ty, gj,
                    gt => GR.gjobs_perm(pr, p, G, C_root, n_root, gG, tx, ty,
                            et, gt))
    case FP.PSwap{}:
      match xs:
        case Nil{}:
          Empty.absurd(
            GR.GJobs(p, G, C_root, n_root, gG, MV.MV.next_groups(ys)), ok)
        case Con{a, t1}:
          match a:
            case Groups.Group{+fa, +wa}:
              match t1:
                case Nil{}:
                  Empty.absurd(
                    GR.GJobs(p, G, C_root, n_root, gG, MV.MV.next_groups(ys)),
                    ok)
                case Con{b, tx}:
                  match b:
                    case Groups.Group{+fb2, +wb}:
                      match ys:
                        case Nil{}:
                          Empty.absurd(
                            GR.GJobs(p, G, C_root, n_root, gG, Nil{}), ok)
                        case Con{c, t2}:
                          match t2:
                            case Nil{}:
                              Empty.absurd(
                                GR.GJobs(p, G, C_root, n_root, gG,
                                  MV.MV.next_groups(c <> Nil{})), ok)
                            case Con{d, ty}:
                              +ead = Arr.Arr.dpair_l(
                                       {Groups.Group{fa, wa} == d : Groups.Group},
                                       Arr.Arr.DPair<
                                         {Groups.Group{fb2, wb} == c
                                          : Groups.Group},
                                         {tx == ty : +List<Groups.Group>}>, ok)
                              +r1 = Arr.Arr.dpair_r(
                                      {Groups.Group{fa, wa} == d : Groups.Group},
                                      Arr.Arr.DPair<
                                        {Groups.Group{fb2, wb} == c
                                         : Groups.Group},
                                        {tx == ty : +List<Groups.Group>}>, ok)
                              +ebc = Arr.Arr.dpair_l(
                                       {Groups.Group{fb2, wb} == c
                                        : Groups.Group},
                                       {tx == ty : +List<Groups.Group>}, r1)
                              +et = Arr.Arr.dpair_r(
                                      {Groups.Group{fb2, wb} == c : Groups.Group},
                                      {tx == ty : +List<Groups.Group>}, r1)
                              %ead :
                                GR.GJobs(p, G, C_root, n_root, gG,
                                  MV.MV.next_groups(c <> (_ <> ty)))
                              %ebc :
                                GR.GJobs(p, G, C_root, n_root, gG,
                                  MV.MV.next_groups(
                                    _ <> (Groups.Group{fa, wa} <> ty)))
                              %et :
                                GR.GJobs(p, G, C_root, n_root, gG,
                                  MV.MV.next_groups(
                                    Groups.Group{fb2, wb}
                                    <> (Groups.Group{fa, wa} <> _)))
                              GR.gjobs_swap_go(p, G, C_root, n_root, gG, fa, wa,
                                fb2, wb, tx, gj)
    case FP.PTrans{+mid, p1, p2}:
      +ok1 = Arr.Arr.dpair_l(FP.FP.PermOk(p1, xs, mid),
               FP.FP.PermOk(p2, mid, ys), ok)
      +ok2 = Arr.Arr.dpair_r(FP.FP.PermOk(p1, xs, mid),
               FP.FP.PermOk(p2, mid, ys), ok)
      GR.gjobs_perm(p2, p, G, C_root, n_root, gG, mid, ys, ok2,
        GR.gjobs_perm(p1, p, G, C_root, n_root, gG, xs, mid, ok1, gj))

def GR.greedy_body_ok(+rem: +List<Groups.Group>, +body: +List<SolveFast.Item>,
    +p: Nat, +G: +List<+List<Nat>>, +C_root: +List<+List<Nat>>, +n_root: Nat,
    +gG: SolveFast.GList, +cwS: +List<SolveFast.CWord>, +S: +List<+List<Nat>>,
    +n: Nat, +g: +List<Nat>,
    +done_rev: +List<Groups.Group>, +kids: +List<Tree.Child>, +sum: Nat,
    buf: SolveFast.Buf5, +perm: FP.FP.Perm,
    +en: {n == Groups.len_words(S) : Nat},
    +wg: {Tree.member_word(g, G) == True{} : Bool},
    +hperm: FP.FP.PermOk(perm, Groups.groups_build(g, S, Nil{}),
              FVal.FV.rev_groups(done_rev, rem)),
    +ag: {FO.FO.all_in_jobs_b(MV.MV.next_groups(rem), G) == True{} : Bool},
    +ng: {FN.FN.nodup_ok_jobs(True{}, MV.MV.next_groups(rem)) == True{} : Bool},
    +hm: {FVal.FV.kids_match_b(G, done_rev, kids) == True{} : Bool},
    +hcs: {Nat.is_le(FVal.FV.kids_cost_sum(done_rev, kids), sum)
           == True{} : Bool},
    +hbm: FH.FH.BodyMatch(G, C_root, n_root, True{}, True{}, n, rem, body),
    +hbuf: FH.FH.BufOk(G, C_root, n_root, True{}, True{}, buf),
    gj: GR.GJobs(p, G, C_root, n_root, gG, MV.MV.next_groups(rem))) ->
  GR.GreedySpec(G, C_root, n_root, S,
    Greedy.greedy_step(1n+p, 0n, body, gG, cwS, n, g, kids, sum,
      Greedy.GreedyFail{SolveFast.NoBuf{}}, SolveFast.GuessRes{Nil{}, buf})):
  match rem:
    case Nil{}:
      %Equal.sym(+List<SolveFast.Item>, body, SolveFast.End{} <> Nil{}, hbm) :
        GR.GreedySpec(G, C_root, n_root, S,
          Greedy.greedy_step(1n+p, 0n, _, gG, cwS, n, g, kids, sum,
            Greedy.GreedyFail{SolveFast.NoBuf{}},
            SolveFast.GuessRes{Nil{}, buf}))
      +hok = FVal.FV.end_node_ok_perm(G, S, g, done_rev, kids, sum, wg, perm,
               hperm, hm, hcs)
      +hval = Logic.Proof.and_true_l(
                FVal.FV.valid_b(
                  Tree.Node{g, SolveRef.rev_kids(kids, Nil{})}, G, S),
                Nat.is_le(
                  Tree.cost(Tree.Node{g, SolveRef.rev_kids(kids, Nil{})}, S),
                  Nat.add(Groups.len_words(S), sum)), hok)
      +hcost0 = Logic.Proof.and_true_r(
                  FVal.FV.valid_b(
                    Tree.Node{g, SolveRef.rev_kids(kids, Nil{})}, G, S),
                  Nat.is_le(
                    Tree.cost(Tree.Node{g, SolveRef.rev_kids(kids, Nil{})}, S),
                    Nat.add(Groups.len_words(S), sum)), hok)
      +hcost = NatProof.Nat.is_le_eq_r(
                 Tree.cost(Tree.Node{g, SolveRef.rev_kids(kids, Nil{})}, S),
                 Nat.add(Groups.len_words(S), sum), Nat.add(sum, n),
                 Equal.trans(Nat, Nat.add(Groups.len_words(S), sum),
                   Nat.add(n, sum), Nat.add(sum, n),
                   Equal.cong(Nat, Nat, x => Nat.add(x, sum),
                     Groups.len_words(S), n,
                     Equal.sym(Nat, n, Groups.len_words(S), en)),
                   NatProof.NatPrf.add_comm(n, sum)), hcost0)
      Arr.DPair{
        FO.FO.bool_and_intro(
          FVal.FV.valid_b(Tree.Node{g, SolveRef.rev_kids(kids, Nil{})}, G, S),
          Nat.is_le(Tree.cost(Tree.Node{g, SolveRef.rev_kids(kids, Nil{})}, S),
            Nat.add(sum, n)),
          hval, hcost),
        hbuf}
    case Con{gp, restg}:
      match gp:
        case Groups.Group{+fb, +ws}:
          match body:
            case Nil{}:
              Empty.absurd(
                GR.GreedySpec(G, C_root, n_root, S,
                  Greedy.greedy_step(1n+p, 0n, Nil{}, gG, cwS, n, g, kids, sum,
                    Greedy.GreedyFail{SolveFast.NoBuf{}},
                    SolveFast.GuessRes{Nil{}, buf})), hbm)
            case Con{it, restb}:
              match it:
                case SolveFast.Begin{g2}:
                  Empty.absurd(
                    GR.GreedySpec(G, C_root, n_root, S,
                      Greedy.greedy_step(1n+p, 0n,
                        SolveFast.Begin{g2} <> restb, gG, cwS, n, g, kids, sum,
                        Greedy.GreedyFail{SolveFast.NoBuf{}},
                        SolveFast.GuessRes{Nil{}, buf})), hbm)
                case SolveFast.Add{f2, tlb2}:
                  Empty.absurd(
                    GR.GreedySpec(G, C_root, n_root, S,
                      Greedy.greedy_step(1n+p, 0n,
                        SolveFast.Add{f2, tlb2} <> restb, gG, cwS, n, g, kids,
                        sum, Greedy.GreedyFail{SolveFast.NoBuf{}},
                        SolveFast.GuessRes{Nil{}, buf})), hbm)
                case SolveFast.End{}:
                  Empty.absurd(
                    GR.GreedySpec(G, C_root, n_root, S,
                      Greedy.greedy_step(1n+p, 0n,
                        SolveFast.End{} <> restb, gG, cwS, n, g, kids, sum,
                        Greedy.GreedyFail{SolveFast.NoBuf{}},
                        SolveFast.GuessRes{Nil{}, buf})), hbm)
                case SolveFast.OneItem{+f, +w}:
                  (hjob, gj_r) = gj
                  +ef = Arr.Arr.dpair_l({f == fb : +List<Feedback.Color>},
                          Arr.Arr.DPair<{ws == w <> Nil{} : +List<+List<Nat>>},
                            FH.FH.BodyMatch(G, C_root, n_root, True{}, True{},
                              n, restg, restb)>, hbm)
                  +r1 = Arr.Arr.dpair_r({f == fb : +List<Feedback.Color>},
                          Arr.Arr.DPair<{ws == w <> Nil{} : +List<+List<Nat>>},
                            FH.FH.BodyMatch(G, C_root, n_root, True{}, True{},
                              n, restg, restb)>, hbm)
                  +ews = Arr.Arr.dpair_l({ws == w <> Nil{} : +List<+List<Nat>>},
                           FH.FH.BodyMatch(G, C_root, n_root, True{}, True{},
                             n, restg, restb), r1)
                  +hbm2 = Arr.Arr.dpair_r({ws == w <> Nil{} : +List<+List<Nat>>},
                            FH.FH.BodyMatch(G, C_root, n_root, True{}, True{},
                              n, restg, restb), r1)
                  +ai_ws = Logic.Proof.and_true_l(FO.FO.all_in_ref(ws, G),
                             FO.FO.all_in_jobs_b(MV.MV.next_groups(restg), G),
                             ag)
                  +ag_r = Logic.Proof.and_true_r(FO.FO.all_in_ref(ws, G),
                            FO.FO.all_in_jobs_b(MV.MV.next_groups(restg), G),
                            ag)
                  +ng_r = Logic.Proof.and_true_r(FN.FN.no_dup_ref(ws),
                            FN.FN.nodup_ok_jobs(True{},
                              MV.MV.next_groups(restg)), ng)
                  +ai1 : {FO.FO.all_in_ref(w <> Nil{}, G) == True{} : Bool} =
                    Equal.trans(Bool, FO.FO.all_in_ref(w <> Nil{}, G),
                      FO.FO.all_in_ref(ws, G), True{},
                      Equal.cong(+List<+List<Nat>>, Bool,
                        l => FO.FO.all_in_ref(l, G), w <> Nil{}, ws,
                        Equal.sym(+List<+List<Nat>>, ws, w <> Nil{}, ews)),
                      ai_ws)
                  +win = FO.FO.all_in_head(w, Nil{}, G, ai1)
                  +hv : {FVal.FV.valid_b(Tree.Node{w, Nil{}}, G, ws)
                         == True{} : Bool} =
                    Equal.trans(Bool,
                      FVal.FV.valid_b(Tree.Node{w, Nil{}}, G, ws),
                      FVal.FV.valid_b(Tree.Node{w, Nil{}}, G, w <> Nil{}),
                      True{},
                      Equal.cong(+List<+List<Nat>>, Bool,
                        l => FVal.FV.valid_b(Tree.Node{w, Nil{}}, G, l),
                        ws, w <> Nil{}, ews),
                      FVal.FV.one_tree_valid_b(w, G, win))
                  +hc : {Nat.is_le(Tree.cost(Tree.Node{w, Nil{}}, ws), 1n)
                         == True{} : Bool} =
                    Fold.OQ.le_cong_l(Tree.cost(Tree.Node{w, Nil{}}, ws), 1n, 1n,
                      Equal.trans(Nat, Tree.cost(Tree.Node{w, Nil{}}, ws),
                        Tree.cost(Tree.Node{w, Nil{}}, w <> Nil{}), 1n,
                        Equal.cong(+List<+List<Nat>>, Nat,
                          l => Tree.cost(Tree.Node{w, Nil{}}, l),
                          ws, w <> Nil{}, ews),
                        FVal.FV.one_tree_cost(w)), {==})
                  GR.greedy_body_ok(restg, restb, p, G, C_root, n_root, gG, cwS,
                    S, n, g, Groups.Group{fb, ws} <> done_rev,
                    Tree.Child{f, Tree.Node{w, Nil{}}} <> kids,
                    Nat.add(sum, 1n), buf, perm, en, wg, hperm, ag_r, ng_r,
                    GR.kids_step_match(G, fb, f, ws, Tree.Node{w, Nil{}},
                      done_rev, kids, ef, hv, hm),
                    GR.kids_step_cost(fb, f, ws, Tree.Node{w, Nil{}}, 1n,
                      done_rev, kids, sum, hc, hcs),
                    hbm2, hbuf, gj_r)
                case SolveFast.TwoItem{+f, +w1, +w2}:
                  (hjob, gj_r) = gj
                  +ws2 : +List<+List<Nat>> = w1 <> (w2 <> Nil{})
                  +r0 = Arr.Arr.dpair_r({True{} == True{} : Bool},
                          Arr.Arr.DPair<{f == fb : +List<Feedback.Color>},
                            Arr.Arr.DPair<{ws == ws2 : +List<+List<Nat>>},
                              FH.FH.BodyMatch(G, C_root, n_root, True{}, True{},
                                n, restg, restb)>>, hbm)
                  +ef = Arr.Arr.dpair_l({f == fb : +List<Feedback.Color>},
                          Arr.Arr.DPair<{ws == ws2 : +List<+List<Nat>>},
                            FH.FH.BodyMatch(G, C_root, n_root, True{}, True{},
                              n, restg, restb)>, r0)
                  +r1 = Arr.Arr.dpair_r({f == fb : +List<Feedback.Color>},
                          Arr.Arr.DPair<{ws == ws2 : +List<+List<Nat>>},
                            FH.FH.BodyMatch(G, C_root, n_root, True{}, True{},
                              n, restg, restb)>, r0)
                  +ews = Arr.Arr.dpair_l({ws == ws2 : +List<+List<Nat>>},
                           FH.FH.BodyMatch(G, C_root, n_root, True{}, True{},
                             n, restg, restb), r1)
                  +hbm2 = Arr.Arr.dpair_r({ws == ws2 : +List<+List<Nat>>},
                            FH.FH.BodyMatch(G, C_root, n_root, True{}, True{},
                              n, restg, restb), r1)
                  +ai_ws = Logic.Proof.and_true_l(FO.FO.all_in_ref(ws, G),
                             FO.FO.all_in_jobs_b(MV.MV.next_groups(restg), G),
                             ag)
                  +ag_r = Logic.Proof.and_true_r(FO.FO.all_in_ref(ws, G),
                            FO.FO.all_in_jobs_b(MV.MV.next_groups(restg), G),
                            ag)
                  +nd_ws = Logic.Proof.and_true_l(FN.FN.no_dup_ref(ws),
                             FN.FN.nodup_ok_jobs(True{},
                               MV.MV.next_groups(restg)), ng)
                  +ng_r = Logic.Proof.and_true_r(FN.FN.no_dup_ref(ws),
                            FN.FN.nodup_ok_jobs(True{},
                              MV.MV.next_groups(restg)), ng)
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
                      FN.FN.no_dup_ref(ws), True{},
                      Equal.cong(+List<+List<Nat>>, Bool, l => FN.FN.no_dup_ref(l),
                        ws2, ws, Equal.sym(+List<+List<Nat>>, ws, ws2, ews)),
                      nd_ws)
                  +hne = FVal.FV.word_eq_false_of_no_dup_two(w1, w2, nd2)
                  +tr2 = SolveFast.two_tree(w1, w2)
                  +hv : {FVal.FV.valid_b(tr2, G, ws) == True{} : Bool} =
                    Equal.trans(Bool, FVal.FV.valid_b(tr2, G, ws),
                      FVal.FV.valid_b(tr2, G, ws2), True{},
                      Equal.cong(+List<+List<Nat>>, Bool,
                        l => FVal.FV.valid_b(tr2, G, l), ws, ws2, ews),
                      FVal.FV.two_tree_valid_b(w1, w2, G, w1in, w2in, hne))
                  +hc : {Nat.is_le(Tree.cost(tr2, ws), 3n) == True{} : Bool} =
                    Fold.OQ.le_cong_l(Tree.cost(tr2, ws), 3n, 3n,
                      Equal.trans(Nat, Tree.cost(tr2, ws), Tree.cost(tr2, ws2),
                        3n,
                        Equal.cong(+List<+List<Nat>>, Nat,
                          l => Tree.cost(tr2, l), ws, ws2, ews),
                        FVal.FV.two_tree_cost(w1, w2, hne)), {==})
                  GR.greedy_body_ok(restg, restb, p, G, C_root, n_root, gG, cwS,
                    S, n, g, Groups.Group{fb, ws} <> done_rev,
                    Tree.Child{f, tr2} <> kids, Nat.add(sum, 3n), buf, perm, en,
                    wg, hperm, ag_r, ng_r,
                    GR.kids_step_match(G, fb, f, ws, tr2, done_rev, kids, ef,
                      hv, hm),
                    GR.kids_step_cost(fb, f, ws, tr2, 3n, done_rev, kids, sum,
                      hc, hcs),
                    hbm2, hbuf, gj_r)
                case SolveFast.DoneItem{+f, +tr, +c}:
                  (hjob, gj_r) = gj
                  +r0 = Arr.Arr.dpair_r({True{} == True{} : Bool},
                          Arr.Arr.DPair<{f == fb : +List<Feedback.Color>},
                            Arr.Arr.DPair<
                              {FH.FH.done_ws_ok_b(G, ws, tr, c) == True{} : Bool},
                              FH.FH.BodyMatch(G, C_root, n_root, True{}, True{},
                                n, restg, restb)>>, hbm)
                  +ef = Arr.Arr.dpair_l({f == fb : +List<Feedback.Color>},
                          Arr.Arr.DPair<
                            {FH.FH.done_ws_ok_b(G, ws, tr, c) == True{} : Bool},
                            FH.FH.BodyMatch(G, C_root, n_root, True{}, True{},
                              n, restg, restb)>, r0)
                  +r1 = Arr.Arr.dpair_r({f == fb : +List<Feedback.Color>},
                          Arr.Arr.DPair<
                            {FH.FH.done_ws_ok_b(G, ws, tr, c) == True{} : Bool},
                            FH.FH.BodyMatch(G, C_root, n_root, True{}, True{},
                              n, restg, restb)>, r0)
                  +hdws = Arr.Arr.dpair_l(
                            {FH.FH.done_ws_ok_b(G, ws, tr, c) == True{} : Bool},
                            FH.FH.BodyMatch(G, C_root, n_root, True{}, True{},
                              n, restg, restb), r1)
                  +hbm2 = Arr.Arr.dpair_r(
                            {FH.FH.done_ws_ok_b(G, ws, tr, c) == True{} : Bool},
                            FH.FH.BodyMatch(G, C_root, n_root, True{}, True{},
                              n, restg, restb), r1)
                  +ag_r = Logic.Proof.and_true_r(FO.FO.all_in_ref(ws, G),
                            FO.FO.all_in_jobs_b(MV.MV.next_groups(restg), G),
                            ag)
                  +ng_r = Logic.Proof.and_true_r(FN.FN.no_dup_ref(ws),
                            FN.FN.nodup_ok_jobs(True{},
                              MV.MV.next_groups(restg)), ng)
                  +hvc = FOpt.FOpt.done_ws_valid_cost(ws, G, tr, c, hdws)
                  +hv = Logic.Proof.and_true_l(FVal.FV.valid_b(tr, G, ws),
                          Nat.is_le(Tree.cost(tr, ws), c), hvc)
                  +hc = Logic.Proof.and_true_r(FVal.FV.valid_b(tr, G, ws),
                          Nat.is_le(Tree.cost(tr, ws), c), hvc)
                  GR.greedy_body_ok(restg, restb, p, G, C_root, n_root, gG, cwS,
                    S, n, g, Groups.Group{fb, ws} <> done_rev,
                    Tree.Child{f, tr} <> kids, Nat.add(sum, c), buf, perm, en,
                    wg, hperm, ag_r, ng_r,
                    GR.kids_step_match(G, fb, f, ws, tr, done_rev, kids, ef,
                      hv, hm),
                    GR.kids_step_cost(fb, f, ws, tr, c, done_rev, kids, sum,
                      hc, hcs),
                    hbm2, hbuf, gj_r)
                case SolveFast.ClassItem{+f, +cws, +wlen, +tlb}:
                  match restb:
                    case Nil{}:
                      Empty.absurd(
                        GR.GreedySpec(G, C_root, n_root, S,
                          Greedy.greedy_step(1n+p, 0n,
                            SolveFast.ClassItem{f, cws, wlen, tlb} <> Nil{},
                            gG, cwS, n, g, kids, sum,
                            Greedy.GreedyFail{SolveFast.NoBuf{}},
                            SolveFast.GuessRes{Nil{}, buf})), hbm)
                    case Con{it2, restb2}:
                      match it2:
                        case SolveFast.Begin{g2}:
                          Empty.absurd(
                            GR.GreedySpec(G, C_root, n_root, S,
                              Greedy.greedy_step(1n+p, 0n,
                                SolveFast.ClassItem{f, cws, wlen, tlb}
                                <> (SolveFast.Begin{g2} <> restb2),
                                gG, cwS, n, g, kids, sum,
                                Greedy.GreedyFail{SolveFast.NoBuf{}},
                                SolveFast.GuessRes{Nil{}, buf})), hbm)
                        case SolveFast.ClassItem{fa, cwsa, wla, tlba}:
                          Empty.absurd(
                            GR.GreedySpec(G, C_root, n_root, S,
                              Greedy.greedy_step(1n+p, 0n,
                                SolveFast.ClassItem{f, cws, wlen, tlb}
                                <> (SolveFast.ClassItem{fa, cwsa, wla, tlba}
                                    <> restb2),
                                gG, cwS, n, g, kids, sum,
                                Greedy.GreedyFail{SolveFast.NoBuf{}},
                                SolveFast.GuessRes{Nil{}, buf})), hbm)
                        case SolveFast.OneItem{fa, wa}:
                          Empty.absurd(
                            GR.GreedySpec(G, C_root, n_root, S,
                              Greedy.greedy_step(1n+p, 0n,
                                SolveFast.ClassItem{f, cws, wlen, tlb}
                                <> (SolveFast.OneItem{fa, wa} <> restb2),
                                gG, cwS, n, g, kids, sum,
                                Greedy.GreedyFail{SolveFast.NoBuf{}},
                                SolveFast.GuessRes{Nil{}, buf})), hbm)
                        case SolveFast.TwoItem{fa, wa1, wa2}:
                          Empty.absurd(
                            GR.GreedySpec(G, C_root, n_root, S,
                              Greedy.greedy_step(1n+p, 0n,
                                SolveFast.ClassItem{f, cws, wlen, tlb}
                                <> (SolveFast.TwoItem{fa, wa1, wa2} <> restb2),
                                gG, cwS, n, g, kids, sum,
                                Greedy.GreedyFail{SolveFast.NoBuf{}},
                                SolveFast.GuessRes{Nil{}, buf})), hbm)
                        case SolveFast.DoneItem{fa, tra, ca}:
                          Empty.absurd(
                            GR.GreedySpec(G, C_root, n_root, S,
                              Greedy.greedy_step(1n+p, 0n,
                                SolveFast.ClassItem{f, cws, wlen, tlb}
                                <> (SolveFast.DoneItem{fa, tra, ca} <> restb2),
                                gG, cwS, n, g, kids, sum,
                                Greedy.GreedyFail{SolveFast.NoBuf{}},
                                SolveFast.GuessRes{Nil{}, buf})), hbm)
                        case SolveFast.End{}:
                          Empty.absurd(
                            GR.GreedySpec(G, C_root, n_root, S,
                              Greedy.greedy_step(1n+p, 0n,
                                SolveFast.ClassItem{f, cws, wlen, tlb}
                                <> (SolveFast.End{} <> restb2),
                                gG, cwS, n, g, kids, sum,
                                Greedy.GreedyFail{SolveFast.NoBuf{}},
                                SolveFast.GuessRes{Nil{}, buf})), hbm)
                        case SolveFast.Add{+f2, +tlb2}:
                          (hjob, gj_r) = gj
                          +r1 = Arr.Arr.dpair_r({f == fb : +List<Feedback.Color>},
                                  Arr.Arr.DPair<{f2 == fb : +List<Feedback.Color>},
                                    Arr.Arr.DPair<
                                      {SolveFast.cwords_words(cws) == ws
                                       : +List<+List<Nat>>},
                                      Arr.Arr.DPair<
                                        {wlen == Groups.len_words(ws) : Nat},
                                        Arr.Arr.DPair<
                                          {FT.FT.cwords_ok_b(G, C_root, n_root, cws)
                                           == True{} : Bool},
                                          Arr.Arr.DPair<
                                            {tlb == FH.FH.body_lb(True{}, n, restb2)
                                             : Nat},
                                            Arr.Arr.DPair<{tlb2 == tlb : Nat},
                                              FH.FH.BodyMatch(G, C_root, n_root,
                                                True{}, True{}, n, restg,
                                                restb2)>>>>>>, hbm)
                          +ef2 = Arr.Arr.dpair_l({f2 == fb : +List<Feedback.Color>},
                                   Arr.Arr.DPair<
                                     {SolveFast.cwords_words(cws) == ws
                                      : +List<+List<Nat>>},
                                     Arr.Arr.DPair<
                                       {wlen == Groups.len_words(ws) : Nat},
                                       Arr.Arr.DPair<
                                         {FT.FT.cwords_ok_b(G, C_root, n_root, cws)
                                          == True{} : Bool},
                                         Arr.Arr.DPair<
                                           {tlb == FH.FH.body_lb(True{}, n, restb2)
                                            : Nat},
                                           Arr.Arr.DPair<{tlb2 == tlb : Nat},
                                             FH.FH.BodyMatch(G, C_root, n_root,
                                               True{}, True{}, n, restg,
                                               restb2)>>>>>, r1)
                          +r2 = Arr.Arr.dpair_r({f2 == fb : +List<Feedback.Color>},
                                  Arr.Arr.DPair<
                                    {SolveFast.cwords_words(cws) == ws
                                     : +List<+List<Nat>>},
                                    Arr.Arr.DPair<
                                      {wlen == Groups.len_words(ws) : Nat},
                                      Arr.Arr.DPair<
                                        {FT.FT.cwords_ok_b(G, C_root, n_root, cws)
                                         == True{} : Bool},
                                        Arr.Arr.DPair<
                                          {tlb == FH.FH.body_lb(True{}, n, restb2)
                                           : Nat},
                                          Arr.Arr.DPair<{tlb2 == tlb : Nat},
                                            FH.FH.BodyMatch(G, C_root, n_root,
                                              True{}, True{}, n, restg,
                                              restb2)>>>>>, r1)
                          +ecws = Arr.Arr.dpair_l(
                                    {SolveFast.cwords_words(cws) == ws
                                     : +List<+List<Nat>>},
                                    Arr.Arr.DPair<
                                      {wlen == Groups.len_words(ws) : Nat},
                                      Arr.Arr.DPair<
                                        {FT.FT.cwords_ok_b(G, C_root, n_root, cws)
                                         == True{} : Bool},
                                        Arr.Arr.DPair<
                                          {tlb == FH.FH.body_lb(True{}, n, restb2)
                                           : Nat},
                                          Arr.Arr.DPair<{tlb2 == tlb : Nat},
                                            FH.FH.BodyMatch(G, C_root, n_root,
                                              True{}, True{}, n, restg,
                                              restb2)>>>>, r2)
                          +r3 = Arr.Arr.dpair_r(
                                  {SolveFast.cwords_words(cws) == ws
                                   : +List<+List<Nat>>},
                                  Arr.Arr.DPair<
                                    {wlen == Groups.len_words(ws) : Nat},
                                    Arr.Arr.DPair<
                                      {FT.FT.cwords_ok_b(G, C_root, n_root, cws)
                                       == True{} : Bool},
                                      Arr.Arr.DPair<
                                        {tlb == FH.FH.body_lb(True{}, n, restb2)
                                         : Nat},
                                        Arr.Arr.DPair<{tlb2 == tlb : Nat},
                                          FH.FH.BodyMatch(G, C_root, n_root,
                                            True{}, True{}, n, restg,
                                            restb2)>>>>, r2)
                          +ewlen = Arr.Arr.dpair_l(
                                     {wlen == Groups.len_words(ws) : Nat},
                                     Arr.Arr.DPair<
                                       {FT.FT.cwords_ok_b(G, C_root, n_root, cws)
                                        == True{} : Bool},
                                       Arr.Arr.DPair<
                                         {tlb == FH.FH.body_lb(True{}, n, restb2)
                                          : Nat},
                                         Arr.Arr.DPair<{tlb2 == tlb : Nat},
                                           FH.FH.BodyMatch(G, C_root, n_root,
                                             True{}, True{}, n, restg,
                                             restb2)>>>, r3)
                          +r4 = Arr.Arr.dpair_r(
                                  {wlen == Groups.len_words(ws) : Nat},
                                  Arr.Arr.DPair<
                                    {FT.FT.cwords_ok_b(G, C_root, n_root, cws)
                                     == True{} : Bool},
                                    Arr.Arr.DPair<
                                      {tlb == FH.FH.body_lb(True{}, n, restb2)
                                       : Nat},
                                      Arr.Arr.DPair<{tlb2 == tlb : Nat},
                                        FH.FH.BodyMatch(G, C_root, n_root,
                                          True{}, True{}, n, restg,
                                          restb2)>>>, r3)
                          +hcws = Arr.Arr.dpair_l(
                                    {FT.FT.cwords_ok_b(G, C_root, n_root, cws)
                                     == True{} : Bool},
                                    Arr.Arr.DPair<
                                      {tlb == FH.FH.body_lb(True{}, n, restb2)
                                       : Nat},
                                      Arr.Arr.DPair<{tlb2 == tlb : Nat},
                                        FH.FH.BodyMatch(G, C_root, n_root,
                                          True{}, True{}, n, restg,
                                          restb2)>>, r4)
                          +r5 = Arr.Arr.dpair_r(
                                  {FT.FT.cwords_ok_b(G, C_root, n_root, cws)
                                   == True{} : Bool},
                                  Arr.Arr.DPair<
                                    {tlb == FH.FH.body_lb(True{}, n, restb2)
                                     : Nat},
                                    Arr.Arr.DPair<{tlb2 == tlb : Nat},
                                      FH.FH.BodyMatch(G, C_root, n_root,
                                        True{}, True{}, n, restg,
                                        restb2)>>, r4)
                          +r6 = Arr.Arr.dpair_r(
                                  {tlb == FH.FH.body_lb(True{}, n, restb2)
                                   : Nat},
                                  Arr.Arr.DPair<{tlb2 == tlb : Nat},
                                    FH.FH.BodyMatch(G, C_root, n_root,
                                      True{}, True{}, n, restg, restb2)>, r5)
                          +hbm2 = Arr.Arr.dpair_r({tlb2 == tlb : Nat},
                                    FH.FH.BodyMatch(G, C_root, n_root,
                                      True{}, True{}, n, restg, restb2), r6)
                          +ag_r = Logic.Proof.and_true_r(
                                    FO.FO.all_in_ref(ws, G),
                                    FO.FO.all_in_jobs_b(
                                      MV.MV.next_groups(restg), G), ag)
                          +ng_r = Logic.Proof.and_true_r(FN.FN.no_dup_ref(ws),
                                    FN.FN.nodup_ok_jobs(True{},
                                      MV.MV.next_groups(restg)), ng)
                          GR.with_dup_buf(
                            GR.GreedySpec(G, C_root, n_root, S,
                              Greedy.greedy_step(1n+p, 0n,
                                SolveFast.Add{f2, tlb2} <> restb2, gG, cwS, n,
                                g, kids, sum,
                                Greedy.greedy_step(p, 2n, Nil{}, gG, cws, wlen,
                                  Nil{}, Nil{}, 0n,
                                  Greedy.GreedyFail{SolveFast.NoBuf{}},
                                  SolveFast.GuessRes{Nil{}, buf}),
                                SolveFast.GuessRes{Nil{}, SolveFast.NoBuf{}})),
                            buf,
                            b1 => b2 => +eb1 => +eb2 =>
                            +hbuf1 = FH.FH.buf_ok_transport(G, C_root, n_root,
                                       True{}, True{}, buf, b1,
                                       Equal.sym(SolveFast.Buf5, b1, buf, eb1),
                                       hbuf)
                            +hpend1 = hjob(cws, wlen, b1, ecws, ewlen, hcws,
                                        hbuf1)
                            +eb12 : {b1 == b2 : SolveFast.Buf5} =
                              Equal.trans(SolveFast.Buf5, b1, buf, b2, eb1,
                                Equal.sym(SolveFast.Buf5, b2, buf, eb2))
                            +hpend : GR.GreedySpec(G, C_root, n_root, ws,
                                       Greedy.greedy_step(p, 2n, Nil{}, gG, cws,
                                         wlen, Nil{}, Nil{}, 0n,
                                         Greedy.GreedyFail{SolveFast.NoBuf{}},
                                         SolveFast.GuessRes{Nil{}, b2})) =
                              %eb12 : GR.GreedySpec(G, C_root, n_root, ws,
                                        Greedy.greedy_step(p, 2n, Nil{}, gG,
                                          cws, wlen, Nil{}, Nil{}, 0n,
                                          Greedy.GreedyFail{SolveFast.NoBuf{}},
                                          SolveFast.GuessRes{Nil{}, _}))
                              hpend1
                            %eb2 : GR.GreedySpec(G, C_root, n_root, S,
                                     Greedy.greedy_step(1n+p, 0n,
                                       SolveFast.Add{f2, tlb2} <> restb2, gG,
                                       cwS, n, g, kids, sum,
                                       Greedy.greedy_step(p, 2n, Nil{}, gG, cws,
                                         wlen, Nil{}, Nil{}, 0n,
                                         Greedy.GreedyFail{SolveFast.NoBuf{}},
                                         SolveFast.GuessRes{Nil{}, _}),
                                       SolveFast.GuessRes{Nil{},
                                         SolveFast.NoBuf{}}))
                            GR.greedy_add_step(p, G, C_root, n_root, gG, cwS, S,
                              n, g, fb, f2, tlb2, ws, restb2, done_rev, kids,
                              sum,
                              Greedy.greedy_step(p, 2n, Nil{}, gG, cws, wlen,
                                Nil{}, Nil{}, 0n,
                                Greedy.GreedyFail{SolveFast.NoBuf{}},
                                SolveFast.GuessRes{Nil{}, b2}),
                              ef2, hm, hcs, hpend,
                              +tr => +c => pbuf => +hpbuf => +hm2 => +hcs2 =>
                                GR.greedy_body_ok(restg, restb2, p, G, C_root,
                                  n_root, gG, cwS, S, n, g,
                                  Groups.Group{fb, ws} <> done_rev,
                                  Tree.Child{f2, tr} <> kids, Nat.add(sum, c),
                                  pbuf, perm, en, wg, hperm, ag_r, ng_r,
                                  hm2, hcs2, hbm2, hpbuf, gj_r)))

def GR.greedy_phase1_ew(+p: Nat, +G: +List<+List<Nat>>,
    +C_root: +List<+List<Nat>>, +n_root: Nat, +gG: SolveFast.GList,
    +cwS: +List<SolveFast.CWord>, +S: +List<+List<Nat>>, +n: Nat,
    +items: +List<SolveFast.Item>, buf2: SolveFast.Buf5,
    +en: {n == Groups.len_words(S) : Nat},
    +hai: {FO.FO.all_in_ref(S, G) == True{} : Bool},
    +hnd: {FN.FN.no_dup_ref(S) == True{} : Bool},
    ew: GR.ExpWit<G, C_root, n_root, S, n, items>,
    +hbuf2: FH.FH.BufOk(G, C_root, n_root, True{}, True{}, buf2),
    gj_guess: GR.GJobs(p, G, C_root, n_root, gG, MV.MV.next_guess(G, S))) ->
  GR.GreedySpec(G, C_root, n_root, S,
    Greedy.greedy_step(1n+p, 1n, Nil{}, gG, cwS, n, Nil{}, Nil{}, 0n,
      Greedy.GreedyFail{SolveFast.NoBuf{}},
      SolveFast.GuessRes{items, buf2})):
  match ew:
    case ExpNil{enil}:
      %Equal.sym(+List<SolveFast.Item>, items, Nil{}, enil) :
        GR.GreedySpec(G, C_root, n_root, S,
          Greedy.greedy_step(1n+p, 1n, Nil{}, gG, cwS, n, Nil{}, Nil{}, 0n,
            Greedy.GreedyFail{SolveFast.NoBuf{}},
            SolveFast.GuessRes{_, buf2}))
      hbuf2
    case ExpLive{+g, +ord, +body, +perm, eits, +wg, +hus, +hperm, +hbm}:
      %Equal.sym(+List<SolveFast.Item>, items, SolveFast.Begin{g} <> body,
         eits) :
        GR.GreedySpec(G, C_root, n_root, S,
          Greedy.greedy_step(1n+p, 1n, Nil{}, gG, cwS, n, Nil{}, Nil{}, 0n,
            Greedy.GreedyFail{SolveFast.NoBuf{}},
            SolveFast.GuessRes{_, buf2}))
      +full = Groups.groups_build(g, S, Nil{})
      +ag_full = FO.FO.all_in_next_groups(full, S, G,
                   CoverGroups.Cover.all_subseq_nil(g, S), hai)
      +ag_ord : {FO.FO.all_in_jobs_b(MV.MV.next_groups(ord), G)
                 == True{} : Bool} =
        Equal.trans(Bool,
          FO.FO.all_in_jobs_b(MV.MV.next_groups(ord), G),
          FO.FO.all_in_jobs_b(MV.MV.next_groups(full), G), True{},
          Equal.sym(Bool,
            FO.FO.all_in_jobs_b(MV.MV.next_groups(full), G),
            FO.FO.all_in_jobs_b(MV.MV.next_groups(ord), G),
            FP.FP.all_in_jobs_perm(perm, G, full, ord, hperm)), ag_full)
      +ng_full = FN.FN.nodup_ok_next_groups(True{}, full, S,
                   CoverGroups.Cover.all_subseq_nil(g, S), hnd)
      +ng_ord : {FN.FN.nodup_ok_jobs(True{}, MV.MV.next_groups(ord))
                 == True{} : Bool} =
        Equal.trans(Bool,
          FN.FN.nodup_ok_jobs(True{}, MV.MV.next_groups(ord)),
          FN.FN.nodup_ok_jobs(True{}, MV.MV.next_groups(full)), True{},
          Equal.sym(Bool,
            FN.FN.nodup_ok_jobs(True{}, MV.MV.next_groups(full)),
            FN.FN.nodup_ok_jobs(True{}, MV.MV.next_groups(ord)),
            FP.FP.nodup_ok_jobs_perm(perm, True{}, full, ord, hperm)),
          ng_full)
      gj_full = GR.gjobs_pick_guess(p, G, C_root, n_root, gG, G, S, g, wg, hus,
                  gj_guess)
      gj_ord = GR.gjobs_perm(perm, p, G, C_root, n_root, gG, full, ord, hperm,
                 gj_full)
      GR.greedy_body_ok(ord, body, p, G, C_root, n_root, gG, cwS, S, n, g,
        Nil{}, Nil{}, 0n, buf2, perm, en, wg, hperm, ag_ord, ng_ord, {==},
        {==}, hbm, hbuf2, gj_ord)

def GR.greedy_phase1_ok(+p: Nat, +G: +List<+List<Nat>>,
    +C_root: +List<+List<Nat>>, +n_root: Nat, +gG: SolveFast.GList,
    +cwS: +List<SolveFast.CWord>, +S: +List<+List<Nat>>, +n: Nat,
    gres: SolveFast.GuessRes,
    +en: {n == Groups.len_words(S) : Nat},
    +hai: {FO.FO.all_in_ref(S, G) == True{} : Bool},
    +hnd: {FN.FN.no_dup_ref(S) == True{} : Bool},
    +hgres: GR.ExpSpec(G, C_root, n_root, S, n, gres),
    gj_guess: GR.GJobs(p, G, C_root, n_root, gG, MV.MV.next_guess(G, S))) ->
  GR.GreedySpec(G, C_root, n_root, S,
    Greedy.greedy_step(1n+p, 1n, Nil{}, gG, cwS, n, Nil{}, Nil{}, 0n,
      Greedy.GreedyFail{SolveFast.NoBuf{}}, gres)):
  match gres:
    case SolveFast.GuessRes{+items, buf2}:
      +ew = Arr.Arr.dpair_l(GR.ExpWit<G, C_root, n_root, S, n, items>,
              FH.FH.BufOk(G, C_root, n_root, True{}, True{}, buf2), hgres)
      +hbuf2 = Arr.Arr.dpair_r(GR.ExpWit<G, C_root, n_root, S, n, items>,
                 FH.FH.BufOk(G, C_root, n_root, True{}, True{}, buf2), hgres)
      GR.greedy_phase1_ew(p, G, C_root, n_root, gG, cwS, S, n, items, buf2,
        en, hai, hnd, ew, hbuf2, gj_guess)

def GR.gjobs_zero(+G: +List<+List<Nat>>, +C_root: +List<+List<Nat>>,
    +n_root: Nat, +gG: SolveFast.GList, +jobs: +List<+List<+List<Nat>>>) ->
  GR.GJobs(0n, G, C_root, n_root, gG, jobs):
  match jobs:
    case Nil{}:
      Unit{}
    case Con{+ws, +rest}:
      ((+cws => +wlen => b_in => +ecws => +ewlen => +hcws => +hb_in => hb_in),
       GR.gjobs_zero(G, C_root, n_root, gG, rest))

def GR.gjob_step_one(+p: Nat, +G: +List<+List<Nat>>,
    +C_root: +List<+List<Nat>>, +n_root: Nat, +gG: SolveFast.GList,
    +ws: +List<+List<Nat>>, +S: +List<SolveFast.CWord>, +n: Nat,
    buf: SolveFast.Buf5,
    +hgG: {GR.glist_ok_b(G, n_root, gG) == True{} : Bool},
    +ecws: {SolveFast.cwords_words(S) == ws : +List<+List<Nat>>},
    +en: {n == Groups.len_words(ws) : Nat},
    +hS: {FT.FT.cwords_ok_b(G, C_root, n_root, S) == True{} : Bool},
    +hai: {FO.FO.all_in_ref(ws, G) == True{} : Bool},
    +hnd: {FN.FN.no_dup_ref(ws) == True{} : Bool},
    +hbuf: FH.FH.BufOk(G, C_root, n_root, True{}, True{}, buf),
    gj_ws: GR.GJobs(p, G, C_root, n_root, gG, MV.MV.next_guess(G, ws))) ->
  GR.GreedySpec(G, C_root, n_root, ws,
    Greedy.greedy_step(1n+p, 2n, Nil{}, gG, S, n, Nil{}, Nil{}, 0n,
      Greedy.GreedyFail{SolveFast.NoBuf{}}, SolveFast.GuessRes{Nil{}, buf})):
  match S:
    case Nil{}:
      hbuf
    case Con{+cw, +t}:
      match t:
        case Nil{}:
          +w = SolveFast.cword_w(cw)
          +ew : {ws == w <> Nil{} : +List<+List<Nat>>} =
            Equal.trans(+List<+List<Nat>>, ws,
              SolveFast.cwords_words(cw <> Nil{}), w <> Nil{},
              Equal.sym(+List<+List<Nat>>, SolveFast.cwords_words(cw <> Nil{}),
                ws, ecws),
              FH.FH.cwords_words_cons(cw, Nil{}))
          +ai1 : {FO.FO.all_in_ref(w <> Nil{}, G) == True{} : Bool} =
            Equal.trans(Bool, FO.FO.all_in_ref(w <> Nil{}, G),
              FO.FO.all_in_ref(ws, G), True{},
              Equal.cong(+List<+List<Nat>>, Bool, l => FO.FO.all_in_ref(l, G),
                w <> Nil{}, ws,
                Equal.sym(+List<+List<Nat>>, ws, w <> Nil{}, ew)), hai)
          +win = FO.FO.all_in_head(w, Nil{}, G, ai1)
          +hvc : {Bool.and(FVal.FV.valid_b(Tree.Node{w, Nil{}}, G, w <> Nil{}),
                    Nat.is_le(Tree.cost(Tree.Node{w, Nil{}}, w <> Nil{}), 1n))
                  == True{} : Bool} =
            FO.FO.bool_and_intro(
              FVal.FV.valid_b(Tree.Node{w, Nil{}}, G, w <> Nil{}),
              Nat.is_le(Tree.cost(Tree.Node{w, Nil{}}, w <> Nil{}), 1n),
              FVal.FV.one_tree_valid_b(w, G, win),
              Fold.OQ.le_cong_l(Tree.cost(Tree.Node{w, Nil{}}, w <> Nil{}),
                1n, 1n, FVal.FV.one_tree_cost(w), {==}))
          Arr.DPair{
            Equal.trans(Bool,
              Bool.and(FVal.FV.valid_b(Tree.Node{w, Nil{}}, G, ws),
                Nat.is_le(Tree.cost(Tree.Node{w, Nil{}}, ws), 1n)),
              Bool.and(FVal.FV.valid_b(Tree.Node{w, Nil{}}, G, w <> Nil{}),
                Nat.is_le(Tree.cost(Tree.Node{w, Nil{}}, w <> Nil{}), 1n)),
              True{},
              Equal.cong(+List<+List<Nat>>, Bool,
                l => Bool.and(FVal.FV.valid_b(Tree.Node{w, Nil{}}, G, l),
                       Nat.is_le(Tree.cost(Tree.Node{w, Nil{}}, l), 1n)),
                ws, w <> Nil{}, ew),
              hvc),
            hbuf}
        case Con{+cw2, +t2}:
          match t2:
            case Nil{}:
              +w1 = SolveFast.cword_w(cw)
              +w2 = SolveFast.cword_w(cw2)
              +ws2 : +List<+List<Nat>> = w1 <> (w2 <> Nil{})
              +ew2 : {ws == ws2 : +List<+List<Nat>>} =
                Equal.trans(+List<+List<Nat>>, ws,
                  SolveFast.cwords_words(cw <> (cw2 <> Nil{})), ws2,
                  Equal.sym(+List<+List<Nat>>,
                    SolveFast.cwords_words(cw <> (cw2 <> Nil{})), ws, ecws),
                  Equal.trans(+List<+List<Nat>>,
                    SolveFast.cwords_words(cw <> (cw2 <> Nil{})),
                    w1 <> SolveFast.cwords_words(cw2 <> Nil{}), ws2,
                    FH.FH.cwords_words_cons(cw, cw2 <> Nil{}),
                    Equal.cong(+List<+List<Nat>>, +List<+List<Nat>>,
                      l => w1 <> l, SolveFast.cwords_words(cw2 <> Nil{}),
                      w2 <> Nil{}, FH.FH.cwords_words_cons(cw2, Nil{}))))
              +ew2_s = Equal.sym(+List<+List<Nat>>, ws, ws2, ew2)
              +ai2 : {FO.FO.all_in_ref(ws2, G) == True{} : Bool} =
                Equal.trans(Bool, FO.FO.all_in_ref(ws2, G),
                  FO.FO.all_in_ref(ws, G), True{},
                  Equal.cong(+List<+List<Nat>>, Bool,
                    l => FO.FO.all_in_ref(l, G), ws2, ws, ew2_s), hai)
              +w1in = FO.FO.all_in_head(w1, w2 <> Nil{}, G, ai2)
              +w2in = FO.FO.all_in_head(w2, Nil{}, G,
                        FO.FO.all_in_tail(w1, w2 <> Nil{}, G, ai2))
              +nd2 : {FN.FN.no_dup_ref(ws2) == True{} : Bool} =
                Equal.trans(Bool, FN.FN.no_dup_ref(ws2),
                  FN.FN.no_dup_ref(ws), True{},
                  Equal.cong(+List<+List<Nat>>, Bool, l => FN.FN.no_dup_ref(l),
                    ws2, ws, ew2_s), hnd)
              +hne = FVal.FV.word_eq_false_of_no_dup_two(w1, w2, nd2)
              +tr2 = SolveFast.two_tree(w1, w2)
              +hvc : {Bool.and(FVal.FV.valid_b(tr2, G, ws2),
                        Nat.is_le(Tree.cost(tr2, ws2), 3n))
                      == True{} : Bool} =
                FO.FO.bool_and_intro(FVal.FV.valid_b(tr2, G, ws2),
                  Nat.is_le(Tree.cost(tr2, ws2), 3n),
                  FVal.FV.two_tree_valid_b(w1, w2, G, w1in, w2in, hne),
                  Fold.OQ.le_cong_l(Tree.cost(tr2, ws2), 3n, 3n,
                    FVal.FV.two_tree_cost(w1, w2, hne), {==}))
              Arr.DPair{
                Equal.trans(Bool,
                  Bool.and(FVal.FV.valid_b(tr2, G, ws),
                    Nat.is_le(Tree.cost(tr2, ws), 3n)),
                  Bool.and(FVal.FV.valid_b(tr2, G, ws2),
                    Nat.is_le(Tree.cost(tr2, ws2), 3n)), True{},
                  Equal.cong(+List<+List<Nat>>, Bool,
                    l => Bool.and(FVal.FV.valid_b(tr2, G, l),
                           Nat.is_le(Tree.cost(tr2, l), 3n)), ws, ws2, ew2),
                  hvc),
                hbuf}
            case Con{+cw3, +t3}:
              +S3 : +List<SolveFast.CWord> = cw <> (cw2 <> (cw3 <> t3))
              +ws3 : +List<+List<Nat>> = SolveFast.cwords_words(S3)
              +en3 : {n == Groups.len_words(ws3) : Nat} =
                Equal.trans(Nat, n, Groups.len_words(ws), Groups.len_words(ws3),
                  en,
                  Equal.cong(+List<+List<Nat>>, Nat, l => Groups.len_words(l),
                    ws, ws3, Equal.sym(+List<+List<Nat>>, ws3, ws, ecws)))
              +hge1 : {Nat.is_le(1n, n) == True{} : Bool} =
                Equal.trans(Bool, Nat.is_le(1n, n),
                  Nat.is_le(1n, Groups.len_words(ws3)), True{},
                  Equal.cong(Nat, Bool, x => Nat.is_le(1n, x),
                    n, Groups.len_words(ws3), en3),
                  Equal.trans(Bool, Nat.is_le(1n, Groups.len_words(ws3)),
                    Nat.is_le(1n,
                      Nat.add(1n,
                        Groups.len_words(
                          SolveFast.cwords_words(cw2 <> (cw3 <> t3))))),
                    True{},
                    Equal.cong(+List<+List<Nat>>, Bool,
                      l => Nat.is_le(1n, Groups.len_words(l)), ws3,
                      SolveFast.cword_w(cw)
                      <> SolveFast.cwords_words(cw2 <> (cw3 <> t3)),
                      FH.FH.cwords_words_cons(cw, cw2 <> (cw3 <> t3))),
                    NatProof.Nat.is_le_zero_l(
                      Groups.len_words(
                        SolveFast.cwords_words(cw2 <> (cw3 <> t3))))))
              +hai3 : {FO.FO.all_in_ref(ws3, G) == True{} : Bool} =
                Equal.trans(Bool, FO.FO.all_in_ref(ws3, G),
                  FO.FO.all_in_ref(ws, G), True{},
                  Equal.cong(+List<+List<Nat>>, Bool,
                    l => FO.FO.all_in_ref(l, G), ws3, ws, ecws), hai)
              +hnd3 : {FN.FN.no_dup_ref(ws3) == True{} : Bool} =
                Equal.trans(Bool, FN.FN.no_dup_ref(ws3),
                  FN.FN.no_dup_ref(ws), True{},
                  Equal.cong(+List<+List<Nat>>, Bool, l => FN.FN.no_dup_ref(l),
                    ws3, ws, ecws), hnd)
              GR.with_dup_buf(
                GR.GreedySpec(G, C_root, n_root, ws,
                  Greedy.greedy_step(1n+p, 1n, Nil{}, gG, S3, n, Nil{},
                    Nil{}, 0n, Greedy.GreedyFail{SolveFast.NoBuf{}},
                    Greedy.greedy_expand(gG, S3, n, buf))),
                buf,
                b1 => b2 => +eb1 => +eb2 =>
                +hbuf1 = FH.FH.buf_ok_transport(G, C_root, n_root, True{},
                           True{}, buf, b1,
                           Equal.sym(SolveFast.Buf5, b1, buf, eb1), hbuf)
                +hexp1 = GR.greedy_expand_spec(G, C_root, n_root, gG, S3, n,
                           b1, hgG, hge1, en3, hS, hai3, hnd3, hbuf1)
                +eb12 : {b1 == b2 : SolveFast.Buf5} =
                  Equal.trans(SolveFast.Buf5, b1, buf, b2, eb1,
                    Equal.sym(SolveFast.Buf5, b2, buf, eb2))
                +hexp2 : GR.ExpSpec(G, C_root, n_root, ws, n,
                           Greedy.greedy_expand(gG, S3, n, b2)) =
                  %ecws : GR.ExpSpec(G, C_root, n_root, _, n,
                            Greedy.greedy_expand(gG, S3, n, b2))
                  %eb12 : GR.ExpSpec(G, C_root, n_root, ws3, n,
                            Greedy.greedy_expand(gG, S3, n, _))
                  hexp1
                %eb2 : GR.GreedySpec(G, C_root, n_root, ws,
                         Greedy.greedy_step(1n+p, 1n, Nil{}, gG, S3, n,
                           Nil{}, Nil{}, 0n,
                           Greedy.GreedyFail{SolveFast.NoBuf{}},
                           Greedy.greedy_expand(gG, S3, n, _)))
                GR.greedy_phase1_ok(p, G, C_root, n_root, gG, S3, ws, n,
                  Greedy.greedy_expand(gG, S3, n, b2), en, hai, hnd, hexp2,
                  gj_ws))

def GR.gjobs_step(+p: Nat, +G: +List<+List<Nat>>, +C_root: +List<+List<Nat>>,
    +n_root: Nat, +gG: SolveFast.GList, +jobs: +List<+List<+List<Nat>>>,
    +hgG: {GR.glist_ok_b(G, n_root, gG) == True{} : Bool},
    +aj: {FO.FO.all_in_jobs_b(jobs, G) == True{} : Bool},
    +nj: {FN.FN.nodup_ok_jobs(True{}, jobs) == True{} : Bool},
    gj_next: GR.GJobs(p, G, C_root, n_root, gG, MV.MV.next_jobs(G, jobs))) ->
  GR.GJobs(1n+p, G, C_root, n_root, gG, jobs):
  match jobs:
    case Nil{}:
      Unit{}
    case Con{+ws, +rest}:
      +ai = Logic.Proof.and_true_l(FO.FO.all_in_ref(ws, G),
              FO.FO.all_in_jobs_b(rest, G), aj)
      +aj_r = Logic.Proof.and_true_r(FO.FO.all_in_ref(ws, G),
                FO.FO.all_in_jobs_b(rest, G), aj)
      +nd = Logic.Proof.and_true_l(FN.FN.no_dup_ref(ws),
              FN.FN.nodup_ok_jobs(True{}, rest), nj)
      +nj_r = Logic.Proof.and_true_r(FN.FN.no_dup_ref(ws),
                FN.FN.nodup_ok_jobs(True{}, rest), nj)
      MV.MV.use_pair(
        GR.GJobs(1n+p, G, C_root, n_root, gG, ws <> rest),
        GR.GJobs(p, G, C_root, n_root, gG, MV.MV.next_guess(G, ws)),
        GR.GJobs(p, G, C_root, n_root, gG, MV.MV.next_jobs(G, rest)),
        GR.gjobs_split(p, G, C_root, n_root, gG, MV.MV.next_guess(G, ws),
          MV.MV.next_jobs(G, rest), gj_next),
        gj_ws => gj_rest =>
          ((+cws => +wlen => b_in => +ecws => +ewlen => +hcws => +hb_in =>
              GR.gjob_step_one(p, G, C_root, n_root, gG, ws, cws, wlen, b_in,
                hgG, ecws, ewlen, hcws, ai, nd, hb_in, gj_ws)),
           GR.gjobs_step(p, G, C_root, n_root, gG, rest, hgG, aj_r, nj_r,
             gj_rest)))

def GR.gjobs_ok(+fuel: Nat, +G: +List<+List<Nat>>, +C_root: +List<+List<Nat>>,
    +n_root: Nat, +gG: SolveFast.GList, +jobs: +List<+List<+List<Nat>>>,
    +hgG: {GR.glist_ok_b(G, n_root, gG) == True{} : Bool},
    +aj: {FO.FO.all_in_jobs_b(jobs, G) == True{} : Bool},
    +nj: {FN.FN.nodup_ok_jobs(True{}, jobs) == True{} : Bool}) ->
  GR.GJobs(fuel, G, C_root, n_root, gG, jobs):
  match fuel:
    case 0n:
      GR.gjobs_zero(G, C_root, n_root, gG, jobs)
    case 1n+p:
      GR.gjobs_step(p, G, C_root, n_root, gG, jobs, hgG, aj, nj,
        GR.gjobs_ok(p, G, C_root, n_root, gG, MV.MV.next_jobs(G, jobs), hgG,
          FO.FO.all_in_next_jobs(G, jobs, aj),
          FN.FN.nodup_ok_next_jobs(True{}, G, jobs, nj)))


# ---------------------------------------------------------------------------
# Section 3: Root Pass-1 bucket sorting (`rsort_fill`, `rsort_push_go`, `rsort_drain_tree`)
# ---------------------------------------------------------------------------

def GR.cwords_rg_ok(+G: +List<+List<Nat>>, +n_root: Nat, +S: +List<+List<Nat>>,
    +ws: +List<SolveFast.CWord>) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case Con{cw, rest}:
      match cw:
        case SolveFast.CWord{ci, row, g}:
          Bool.and(FT.FT.gentry_ok_b(G, n_root, row, g),
            Bool.and(Tree.member_word(g, G),
              Bool.and(Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
                GR.cwords_rg_ok(G, n_root, S, rest))))

def GR.member_of_all_in(+w: +List<Nat>, +xs: +List<+List<Nat>>,
    +ys: +List<+List<Nat>>,
    +hm: {Tree.member_word(w, xs) == True{} : Bool},
    +hai: {FO.FO.all_in_ref(xs, ys) == True{} : Bool}) ->
  {Tree.member_word(w, ys) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({Tree.member_word(w, ys) == True{} : Bool},
        Logic.Proof.false_ne_true(hm))
    case Con{+x, +t}:
      +hx = FO.FO.all_in_head(x, t, ys, hai)
      +ht = FO.FO.all_in_tail(x, t, ys, hai)
      GR.member_cons_split({Tree.member_word(w, ys) == True{} : Bool},
        w, x, t, hm,
        +ewx =>
          Equal.trans(Bool, Tree.member_word(w, ys), Tree.member_word(x, ys),
            True{},
            Equal.cong(+List<Nat>, Bool, u => Tree.member_word(u, ys), w, x,
              ewx), hx),
        +hmt => GR.member_of_all_in(w, t, ys, hmt, ht))

def GR.all_usable_in(+S: +List<+List<Nat>>, +seen_gs: +List<+List<Nat>>,
    +ws: +List<+List<Nat>>) -> Bool:
  match seen_gs:
    case Nil{}:
      True{}
    case Con{w, rest}:
      Bool.and(
        Feedback.Bool.case(Bool,
          Groups.groups_smaller(S, Groups.groups_build(w, S, Nil{})),
          Tree.member_word(w, ws), True{}),
        GR.all_usable_in(S, rest, ws))

def GR.all_usable_in_mono_step(+w: +List<Nat>, +ws1: +List<+List<Nat>>,
    +ws2: +List<+List<Nat>>, us: Bool,
    +hsub: {FO.FO.all_in_ref(ws1, ws2) == True{} : Bool},
    +h: {Feedback.Bool.case(Bool, us, Tree.member_word(w, ws1), True{})
         == True{} : Bool}) ->
  {Feedback.Bool.case(Bool, us, Tree.member_word(w, ws2), True{})
   == True{} : Bool}:
  match us:
    case False{}:
      {==}
    case True{}:
      GR.member_of_all_in(w, ws1, ws2, h, hsub)

def GR.all_usable_in_mono(+S: +List<+List<Nat>>, +seen_gs: +List<+List<Nat>>,
    +ws1: +List<+List<Nat>>, +ws2: +List<+List<Nat>>,
    +hsub: {FO.FO.all_in_ref(ws1, ws2) == True{} : Bool},
    +h: {GR.all_usable_in(S, seen_gs, ws1) == True{} : Bool}) ->
  {GR.all_usable_in(S, seen_gs, ws2) == True{} : Bool}:
  match seen_gs:
    case Nil{}:
      {==}
    case Con{+w, +rest}:
      +us = Groups.groups_smaller(S, Groups.groups_build(w, S, Nil{}))
      +h1 = Logic.Proof.and_true_l(
              Feedback.Bool.case(Bool, us, Tree.member_word(w, ws1), True{}),
              GR.all_usable_in(S, rest, ws1), h)
      +hr = Logic.Proof.and_true_r(
              Feedback.Bool.case(Bool, us, Tree.member_word(w, ws1), True{}),
              GR.all_usable_in(S, rest, ws1), h)
      FO.FO.bool_and_intro(
        Feedback.Bool.case(Bool, us, Tree.member_word(w, ws2), True{}),
        GR.all_usable_in(S, rest, ws2),
        GR.all_usable_in_mono_step(w, ws1, ws2, us, hsub, h1),
        GR.all_usable_in_mono(S, rest, ws1, ws2, hsub, hr))

def GR.all_usable_in_mem_go(+S: +List<+List<Nat>>, +w: +List<Nat>,
    +ws: +List<+List<Nat>>, us: Bool,
    +eus: {us == Groups.groups_smaller(S, Groups.groups_build(w, S, Nil{}))
           : Bool},
    +hus: {Groups.groups_smaller(S, Groups.groups_build(w, S, Nil{}))
           == True{} : Bool},
    +h: {Feedback.Bool.case(Bool, us, Tree.member_word(w, ws), True{})
         == True{} : Bool}) ->
  {Tree.member_word(w, ws) == True{} : Bool}:
  match us:
    case True{}:
      h
    case False{}:
      Empty.absurd({Tree.member_word(w, ws) == True{} : Bool},
        Logic.Proof.false_ne_true(
          Equal.trans(Bool, False{},
            Groups.groups_smaller(S, Groups.groups_build(w, S, Nil{})), True{},
            eus, hus)))

def GR.all_usable_in_mem(+S: +List<+List<Nat>>, +seen_gs: +List<+List<Nat>>,
    +ws: +List<+List<Nat>>, +w: +List<Nat>,
    +hall: {GR.all_usable_in(S, seen_gs, ws) == True{} : Bool},
    +hm: {Tree.member_word(w, seen_gs) == True{} : Bool},
    +hus: {Groups.groups_smaller(S, Groups.groups_build(w, S, Nil{}))
           == True{} : Bool}) ->
  {Tree.member_word(w, ws) == True{} : Bool}:
  match seen_gs:
    case Nil{}:
      Empty.absurd({Tree.member_word(w, ws) == True{} : Bool},
        Logic.Proof.false_ne_true(hm))
    case Con{+x, +rest}:
      +us = Groups.groups_smaller(S, Groups.groups_build(x, S, Nil{}))
      +h1 = Logic.Proof.and_true_l(
              Feedback.Bool.case(Bool, us, Tree.member_word(x, ws), True{}),
              GR.all_usable_in(S, rest, ws), hall)
      +hr = Logic.Proof.and_true_r(
              Feedback.Bool.case(Bool, us, Tree.member_word(x, ws), True{}),
              GR.all_usable_in(S, rest, ws), hall)
      GR.member_cons_split({Tree.member_word(w, ws) == True{} : Bool},
        w, x, rest, hm,
        +ewx =>
          +husx : {Groups.groups_smaller(S, Groups.groups_build(x, S, Nil{}))
                   == True{} : Bool} =
            Equal.trans(Bool,
              Groups.groups_smaller(S, Groups.groups_build(x, S, Nil{})),
              Groups.groups_smaller(S, Groups.groups_build(w, S, Nil{})),
              True{},
              Equal.cong(+List<Nat>, Bool,
                u => Groups.groups_smaller(S, Groups.groups_build(u, S, Nil{})),
                x, w, Equal.sym(+List<Nat>, w, x, ewx)), hus)
          +hx : {Tree.member_word(x, ws) == True{} : Bool} =
            GR.all_usable_in_mem_go(S, x, ws, us, {==}, husx, h1)
          Equal.trans(Bool, Tree.member_word(w, ws), Tree.member_word(x, ws),
            True{},
            Equal.cong(+List<Nat>, Bool, u => Tree.member_word(u, ws), w, x,
              ewx), hx),
        +hmt => GR.all_usable_in_mem(S, rest, ws, w, hr, hmt, hus))

def GR.and_intro(-a: Bool, -b: Bool,
    +ha: {a == True{} : Bool}, +hb: {b == True{} : Bool}) ->
  {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

def GR.bool_case_true_r(b: Bool, -x: Bool, +hx: {x == True{} : Bool}) ->
  {Feedback.Bool.case(Bool, b, x, True{}) == True{} : Bool}:
  match b:
    case True{}:
      hx
    case False{}:
      {==}

def GR.bool_case_true_l(b: Bool, +x: Bool, +hx: {x == True{} : Bool}) ->
  {Feedback.Bool.case(Bool, b, True{}, x) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      hx

def GR.all_usable_in_of_all_in(+S: +List<+List<Nat>>, +xs: +List<+List<Nat>>,
    +ws: +List<+List<Nat>>,
    +hai: {FO.FO.all_in_ref(xs, ws) == True{} : Bool}) ->
  {GR.all_usable_in(S, xs, ws) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+w, +rest}:
      +hw = FO.FO.all_in_head(w, rest, ws, hai)
      +hr = FO.FO.all_in_tail(w, rest, ws, hai)
      FO.FO.bool_and_intro(
        Feedback.Bool.case(Bool,
          Groups.groups_smaller(S, Groups.groups_build(w, S, Nil{})),
          Tree.member_word(w, ws), True{}),
        GR.all_usable_in(S, rest, ws),
        GR.bool_case_true_r(
          Groups.groups_smaller(S, Groups.groups_build(w, S, Nil{})),
          Tree.member_word(w, ws), hw),
        GR.all_usable_in_of_all_in(S, rest, ws, hr))

def GR.rev_words(+xs: +List<+List<Nat>>,
    +acc: +List<+List<Nat>>) -> +List<+List<Nat>>:
  match xs:
    case Nil{}:
      acc
    case Con{w, t}:
      GR.rev_words(t, w <> acc)

def GR.all_usable_in_rev_split(+S: +List<+List<Nat>>, +xs: +List<+List<Nat>>,
    +acc: +List<+List<Nat>>, +ws: +List<+List<Nat>>,
    +h: {GR.all_usable_in(S, GR.rev_words(xs, acc), ws) == True{} : Bool}) ->
  {Bool.and(GR.all_usable_in(S, xs, ws), GR.all_usable_in(S, acc, ws))
   == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case Con{+w, +t}:
      +ih = GR.all_usable_in_rev_split(S, t, w <> acc, ws, h)
      +ht = Logic.Proof.and_true_l(GR.all_usable_in(S, t, ws),
              GR.all_usable_in(S, w <> acc, ws), ih)
      +hwa = Logic.Proof.and_true_r(GR.all_usable_in(S, t, ws),
               GR.all_usable_in(S, w <> acc, ws), ih)
      +us = Groups.groups_smaller(S, Groups.groups_build(w, S, Nil{}))
      +hw = Logic.Proof.and_true_l(
              Feedback.Bool.case(Bool, us, Tree.member_word(w, ws), True{}),
              GR.all_usable_in(S, acc, ws), hwa)
      +ha = Logic.Proof.and_true_r(
              Feedback.Bool.case(Bool, us, Tree.member_word(w, ws), True{}),
              GR.all_usable_in(S, acc, ws), hwa)
      FO.FO.bool_and_intro(
        Bool.and(
          Feedback.Bool.case(Bool, us, Tree.member_word(w, ws), True{}),
          GR.all_usable_in(S, t, ws)),
        GR.all_usable_in(S, acc, ws),
        FO.FO.bool_and_intro(
          Feedback.Bool.case(Bool, us, Tree.member_word(w, ws), True{}),
          GR.all_usable_in(S, t, ws), hw, ht), ha)

def GR.prepend_rgs_ok(+G: +List<+List<Nat>>, +n_root: Nat, +S: +List<+List<Nat>>,
    +ws: +List<SolveFast.CWord>, +acc: +List<Greedy.RootGuess>,
    +hws: {GR.cwords_rg_ok(G, n_root, S, ws) == True{} : Bool},
    +hacc: {GR.rgs_ok_b(True{}, G, n_root, acc) == True{} : Bool},
    +hus: {GR.rgs_usable_b(S, acc) == True{} : Bool}) ->
  {Bool.and(GR.rgs_ok_b(True{}, G, n_root, Greedy.prepend_rgs(ws, acc)),
     GR.rgs_usable_b(S, Greedy.prepend_rgs(ws, acc))) == True{} : Bool}:
  match ws:
    case Nil{}:
      FO.FO.bool_and_intro(GR.rgs_ok_b(True{}, G, n_root, acc),
        GR.rgs_usable_b(S, acc), hacc, hus)
    case Con{cw, rest}:
      match cw:
        case SolveFast.CWord{ci, +row, +g}:
          +hrow = Logic.Proof.and_true_l(FT.FT.gentry_ok_b(G, n_root, row, g),
                    Bool.and(Tree.member_word(g, G),
                      Bool.and(
                        Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
                        GR.cwords_rg_ok(G, n_root, S, rest))), hws)
          +r1 = Logic.Proof.and_true_r(FT.FT.gentry_ok_b(G, n_root, row, g),
                  Bool.and(Tree.member_word(g, G),
                    Bool.and(
                      Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
                      GR.cwords_rg_ok(G, n_root, S, rest))), hws)
          +hwg = Logic.Proof.and_true_l(Tree.member_word(g, G),
                   Bool.and(
                     Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
                     GR.cwords_rg_ok(G, n_root, S, rest)), r1)
          +r2 = Logic.Proof.and_true_r(Tree.member_word(g, G),
                  Bool.and(
                    Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
                    GR.cwords_rg_ok(G, n_root, S, rest)), r1)
          +hgus = Logic.Proof.and_true_l(
                    Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
                    GR.cwords_rg_ok(G, n_root, S, rest), r2)
          +hrest = Logic.Proof.and_true_r(
                     Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
                     GR.cwords_rg_ok(G, n_root, S, rest), r2)
          GR.prepend_rgs_ok(G, n_root, S, rest,
            Greedy.RootGuess{row, g} <> acc, hrest,
            FO.FO.bool_and_intro(
              Bool.and(FT.FT.gentry_ok_b(G, n_root, row, g),
                Tree.member_word(g, G)),
              GR.rgs_ok_b(True{}, G, n_root, acc),
              FO.FO.bool_and_intro(FT.FT.gentry_ok_b(G, n_root, row, g),
                Tree.member_word(g, G), hrow, hwg), hacc),
            FO.FO.bool_and_intro(
              Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
              GR.rgs_usable_b(S, acc), hgus, hus))

def GR.prepend_rgs_inv(+G: +List<+List<Nat>>, +n_root: Nat,
    +S: +List<+List<Nat>>, +ws: +List<SolveFast.CWord>,
    +acc: +List<Greedy.RootGuess>,
    +hok: {GR.rgs_ok_b(True{}, G, n_root, Greedy.prepend_rgs(ws, acc))
           == True{} : Bool},
    +hus: {GR.rgs_usable_b(S, Greedy.prepend_rgs(ws, acc)) == True{} : Bool}) ->
  {Bool.and(GR.cwords_rg_ok(G, n_root, S, ws),
     Bool.and(GR.rgs_ok_b(True{}, G, n_root, acc),
       GR.rgs_usable_b(S, acc))) == True{} : Bool}:
  match ws:
    case Nil{}:
      FO.FO.bool_and_intro(GR.rgs_ok_b(True{}, G, n_root, acc),
        GR.rgs_usable_b(S, acc), hok, hus)
    case Con{cw, rest}:
      match cw:
        case SolveFast.CWord{ci, +row, +g}:
          +ih = GR.prepend_rgs_inv(G, n_root, S, rest,
                  Greedy.RootGuess{row, g} <> acc, hok, hus)
          +hrest = Logic.Proof.and_true_l(GR.cwords_rg_ok(G, n_root, S, rest),
                     Bool.and(
                       GR.rgs_ok_b(True{}, G, n_root,
                         Greedy.RootGuess{row, g} <> acc),
                       GR.rgs_usable_b(S, Greedy.RootGuess{row, g} <> acc)), ih)
          +hr1 = Logic.Proof.and_true_r(GR.cwords_rg_ok(G, n_root, S, rest),
                   Bool.and(
                     GR.rgs_ok_b(True{}, G, n_root,
                       Greedy.RootGuess{row, g} <> acc),
                     GR.rgs_usable_b(S, Greedy.RootGuess{row, g} <> acc)), ih)
          +hok_c = Logic.Proof.and_true_l(
                     GR.rgs_ok_b(True{}, G, n_root,
                       Greedy.RootGuess{row, g} <> acc),
                     GR.rgs_usable_b(S, Greedy.RootGuess{row, g} <> acc), hr1)
          +hus_c = Logic.Proof.and_true_r(
                     GR.rgs_ok_b(True{}, G, n_root,
                       Greedy.RootGuess{row, g} <> acc),
                     GR.rgs_usable_b(S, Greedy.RootGuess{row, g} <> acc), hr1)
          +hrg = Logic.Proof.and_true_l(
                   Bool.and(FT.FT.gentry_ok_b(G, n_root, row, g),
                     Tree.member_word(g, G)),
                   GR.rgs_ok_b(True{}, G, n_root, acc), hok_c)
          +hacc_ok = Logic.Proof.and_true_r(
                       Bool.and(FT.FT.gentry_ok_b(G, n_root, row, g),
                         Tree.member_word(g, G)),
                       GR.rgs_ok_b(True{}, G, n_root, acc), hok_c)
          +hrow = Logic.Proof.and_true_l(FT.FT.gentry_ok_b(G, n_root, row, g),
                    Tree.member_word(g, G), hrg)
          +hwg = Logic.Proof.and_true_r(FT.FT.gentry_ok_b(G, n_root, row, g),
                   Tree.member_word(g, G), hrg)
          +hgus = Logic.Proof.and_true_l(
                    Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
                    GR.rgs_usable_b(S, acc), hus_c)
          +hacc_us = Logic.Proof.and_true_r(
                       Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
                       GR.rgs_usable_b(S, acc), hus_c)
          FO.FO.bool_and_intro(
            Bool.and(FT.FT.gentry_ok_b(G, n_root, row, g),
              Bool.and(Tree.member_word(g, G),
                Bool.and(
                  Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
                  GR.cwords_rg_ok(G, n_root, S, rest)))),
            Bool.and(GR.rgs_ok_b(True{}, G, n_root, acc),
              GR.rgs_usable_b(S, acc)),
            FO.FO.bool_and_intro(FT.FT.gentry_ok_b(G, n_root, row, g),
              Bool.and(Tree.member_word(g, G),
                Bool.and(
                  Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
                  GR.cwords_rg_ok(G, n_root, S, rest))),
              hrow,
              FO.FO.bool_and_intro(Tree.member_word(g, G),
                Bool.and(
                  Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
                  GR.cwords_rg_ok(G, n_root, S, rest)),
                hwg,
                FO.FO.bool_and_intro(
                  Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
                  GR.cwords_rg_ok(G, n_root, S, rest), hgus, hrest))),
            FO.FO.bool_and_intro(GR.rgs_ok_b(True{}, G, n_root, acc),
              GR.rgs_usable_b(S, acc), hacc_ok, hacc_us))

def GR.prepend_rgs_mem_acc(+w: +List<Nat>, +ws: +List<SolveFast.CWord>,
    +acc: +List<Greedy.RootGuess>,
    +h: {Tree.member_word(w, GR.rgs_words(acc)) == True{} : Bool}) ->
  {Tree.member_word(w, GR.rgs_words(Greedy.prepend_rgs(ws, acc)))
   == True{} : Bool}:
  match ws:
    case Nil{}:
      h
    case Con{cw, rest}:
      match cw:
        case SolveFast.CWord{ci, +row, +g}:
          GR.prepend_rgs_mem_acc(w, rest, Greedy.RootGuess{row, g} <> acc,
            FN.FN.member_cons_r(w, g, GR.rgs_words(acc), h))

def GR.prepend_rgs_sub(+ws: +List<SolveFast.CWord>,
    +acc1: +List<Greedy.RootGuess>, +acc2: +List<Greedy.RootGuess>,
    +hsub: {FO.FO.all_in_ref(GR.rgs_words(acc1), GR.rgs_words(acc2))
            == True{} : Bool}) ->
  {FO.FO.all_in_ref(GR.rgs_words(Greedy.prepend_rgs(ws, acc1)),
     GR.rgs_words(Greedy.prepend_rgs(ws, acc2))) == True{} : Bool}:
  match ws:
    case Nil{}:
      hsub
    case Con{cw, rest}:
      match cw:
        case SolveFast.CWord{ci, +row, +g}:
          +hsub2 : {FO.FO.all_in_ref(g <> GR.rgs_words(acc1),
                      g <> GR.rgs_words(acc2)) == True{} : Bool} =
            FO.FO.bool_and_intro(Tree.member_word(g, g <> GR.rgs_words(acc2)),
              FO.FO.all_in_ref(GR.rgs_words(acc1), g <> GR.rgs_words(acc2)),
              GR.member_cons_l(g, g, GR.rgs_words(acc2),
                FbProof.FbPrf.word_eq_refl(g)),
              GR.all_in_sub(GR.rgs_words(acc1), GR.rgs_words(acc2), g, hsub))
          GR.prepend_rgs_sub(rest, Greedy.RootGuess{row, g} <> acc1,
            Greedy.RootGuess{row, g} <> acc2, hsub2)

# Structural depth + validity invariant on the 1024-slot bucket-sorting tree.
def GR.BktOk(+d: Nat, +G: +List<+List<Nat>>, +n_root: Nat,
    +S: +List<+List<Nat>>, a: Array<+List<SolveFast.CWord>>) -> Data:
  match d:
    case 0n:
      match a:
        case ALeaf{ws}:
          {GR.cwords_rg_ok(G, n_root, S, ws) == True{} : Bool}
        case ANode{_, _}:
          Empty
    case 1n+p:
      match a:
        case ALeaf{_}:
          Empty
        case ANode{xs, ys}:
          Arr.Arr.DPair<GR.BktOk(p, G, n_root, S, xs),
            GR.BktOk(p, G, n_root, S, ys)>

def GR.bkt_ok_transport(+d: Nat, +G: +List<+List<Nat>>, +n_root: Nat,
    +S: +List<+List<Nat>>, -a1: Array<+List<SolveFast.CWord>>,
    -a2: Array<+List<SolveFast.CWord>>,
    +ea: {a1 == a2 : Array<+List<SolveFast.CWord>>},
    +h: GR.BktOk(d, G, n_root, S, a1)) ->
  GR.BktOk(d, G, n_root, S, a2):
  %ea : GR.BktOk(d, G, n_root, S, _)
  h

def GR.bkt_ok_new(+d: Nat, +G: +List<+List<Nat>>, +n_root: Nat,
    +S: +List<+List<Nat>>) ->
  GR.BktOk(d, G, n_root, S, Array.new(+List<SolveFast.CWord>, d, Nil{})):
  match d:
    case 0n:
      {==}
    case 1n+p:
      +ih = GR.bkt_ok_new(p, G, n_root, S)
      Arr.DPair{ih, ih}

def GR.bkt_ok_push(+d: Nat, +G: +List<+List<Nat>>, +n_root: Nat,
    +S: +List<+List<Nat>>, +row: U32, +g: +List<Nat>,
    a: Array<+List<SolveFast.CWord>>, +half: U32, +idx: U32, lt: Bool,
    +hrow: {FT.FT.gentry_ok_b(G, n_root, row, g) == True{} : Bool},
    +hwg: {Tree.member_word(g, G) == True{} : Bool},
    +hus: {Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{}))
           == True{} : Bool},
    +ha: GR.BktOk(d, G, n_root, S, a)) ->
  GR.BktOk(d, G, n_root, S,
    Greedy.rsort_push_go(a, half, idx, SolveFast.CWord{0, row, g}, lt)):
  match d:
    case 0n:
      match a:
        case ALeaf{+ws}:
          FO.FO.bool_and_intro(FT.FT.gentry_ok_b(G, n_root, row, g),
            Bool.and(Tree.member_word(g, G),
              Bool.and(Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
                GR.cwords_rg_ok(G, n_root, S, ws))),
            hrow,
            FO.FO.bool_and_intro(Tree.member_word(g, G),
              Bool.and(Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
                GR.cwords_rg_ok(G, n_root, S, ws)),
              hwg,
              FO.FO.bool_and_intro(
                Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
                GR.cwords_rg_ok(G, n_root, S, ws), hus, ha)))
        case ANode{xs, ys}:
          Empty.absurd(
            GR.BktOk(0n, G, n_root, S,
              Greedy.rsort_push_go(ANode{xs, ys}, half, idx,
                SolveFast.CWord{0, row, g}, lt)), ha)
    case 1n+p:
      match a:
        case ALeaf{+ws}:
          Empty.absurd(
            GR.BktOk(1n+p, G, n_root, S,
              Greedy.rsort_push_go(ALeaf{ws}, half, idx,
                SolveFast.CWord{0, row, g}, lt)), ha)
        case ANode{xs, ys}:
          match lt:
            case True{}:
              +hxs = Arr.Arr.dpair_l(GR.BktOk(p, G, n_root, S, xs),
                       GR.BktOk(p, G, n_root, S, ys), ha)
              +hys = Arr.Arr.dpair_r(GR.BktOk(p, G, n_root, S, xs),
                       GR.BktOk(p, G, n_root, S, ys), ha)
              +h2 = U32.shr(half)
              Arr.DPair{
                GR.bkt_ok_push(p, G, n_root, S, row, g, xs, h2, idx,
                  U32.is_lt(idx, h2), hrow, hwg, hus, hxs),
                hys}
            case False{}:
              +hxs = Arr.Arr.dpair_l(GR.BktOk(p, G, n_root, S, xs),
                       GR.BktOk(p, G, n_root, S, ys), ha)
              +hys = Arr.Arr.dpair_r(GR.BktOk(p, G, n_root, S, xs),
                       GR.BktOk(p, G, n_root, S, ys), ha)
              +h2 = U32.shr(half)
              +idx2 = U32.sub(idx, half)
              Arr.DPair{
                hxs,
                GR.bkt_ok_push(p, G, n_root, S, row, g, ys, h2, idx2,
                  U32.is_lt(idx2, h2), hrow, hwg, hus, hys)}

def GR.DrainOk(+G: +List<+List<Nat>>, +n_root: Nat, +S: +List<+List<Nat>>,
    +rgs: +List<Greedy.RootGuess>) -> Data:
  Arr.Arr.DPair<
    {GR.rgs_ok_b(True{}, G, n_root, rgs) == True{} : Bool},
    {GR.rgs_usable_b(S, rgs) == True{} : Bool}>

def GR.drain_tree_ok(+d: Nat, +G: +List<+List<Nat>>, +n_root: Nat,
    +S: +List<+List<Nat>>, a: Array<+List<SolveFast.CWord>>,
    +acc: +List<Greedy.RootGuess>,
    +ha: GR.BktOk(d, G, n_root, S, a),
    +hacc_ok: {GR.rgs_ok_b(True{}, G, n_root, acc) == True{} : Bool},
    +hacc_us: {GR.rgs_usable_b(S, acc) == True{} : Bool}) ->
  GR.DrainOk(G, n_root, S, Greedy.rsort_drain_tree(a, acc)):
  match d:
    case 0n:
      match a:
        case ALeaf{+ws}:
          +hp = GR.prepend_rgs_ok(G, n_root, S, ws, acc, ha, hacc_ok, hacc_us)
          Arr.DPair{
            Logic.Proof.and_true_l(
              GR.rgs_ok_b(True{}, G, n_root, Greedy.prepend_rgs(ws, acc)),
              GR.rgs_usable_b(S, Greedy.prepend_rgs(ws, acc)), hp),
            Logic.Proof.and_true_r(
              GR.rgs_ok_b(True{}, G, n_root, Greedy.prepend_rgs(ws, acc)),
              GR.rgs_usable_b(S, Greedy.prepend_rgs(ws, acc)), hp)}
        case ANode{xs, ys}:
          Empty.absurd(
            GR.DrainOk(G, n_root, S, Greedy.rsort_drain_tree(ANode{xs, ys}, acc)),
            ha)
    case 1n+p:
      match a:
        case ALeaf{+ws}:
          Empty.absurd(
            GR.DrainOk(G, n_root, S, Greedy.rsort_drain_tree(ALeaf{ws}, acc)), ha)
        case ANode{xs, ys}:
          +hxs = Arr.Arr.dpair_l(GR.BktOk(p, G, n_root, S, xs),
                   GR.BktOk(p, G, n_root, S, ys), ha)
          +hys = Arr.Arr.dpair_r(GR.BktOk(p, G, n_root, S, xs),
                   GR.BktOk(p, G, n_root, S, ys), ha)
          GR.with_dup_arr(+List<SolveFast.CWord>,
            GR.DrainOk(G, n_root, S,
              Greedy.rsort_drain_tree(xs, Greedy.rsort_drain_tree(ys, acc))),
            ys,
            y1 => y2 => +ey1 => +ey2 =>
            +hys1 = GR.bkt_ok_transport(p, G, n_root, S, ys, y1,
                      Equal.sym(Array<+List<SolveFast.CWord>>, y1, ys, ey1), hys)
            +hy1 = GR.drain_tree_ok(p, G, n_root, S, y1, acc, hys1, hacc_ok,
                     hacc_us)
            +ey12 : {y1 == y2 : Array<+List<SolveFast.CWord>>} =
              Equal.trans(Array<+List<SolveFast.CWord>>, y1, ys, y2, ey1,
                Equal.sym(Array<+List<SolveFast.CWord>>, y2, ys, ey2))
            +hy2 : GR.DrainOk(G, n_root, S, Greedy.rsort_drain_tree(y2, acc)) =
              %ey12 : GR.DrainOk(G, n_root, S, Greedy.rsort_drain_tree(_, acc))
              hy1
            +hy_ok = Arr.Arr.dpair_l(
                       {GR.rgs_ok_b(True{}, G, n_root,
                          Greedy.rsort_drain_tree(y2, acc)) == True{} : Bool},
                       {GR.rgs_usable_b(S, Greedy.rsort_drain_tree(y2, acc))
                        == True{} : Bool}, hy2)
            +hy_us = Arr.Arr.dpair_r(
                       {GR.rgs_ok_b(True{}, G, n_root,
                          Greedy.rsort_drain_tree(y2, acc)) == True{} : Bool},
                       {GR.rgs_usable_b(S, Greedy.rsort_drain_tree(y2, acc))
                        == True{} : Bool}, hy2)
            %ey2 : GR.DrainOk(G, n_root, S,
                     Greedy.rsort_drain_tree(xs, Greedy.rsort_drain_tree(_, acc)))
            GR.drain_tree_ok(p, G, n_root, S, xs,
              Greedy.rsort_drain_tree(y2, acc), hxs, hy_ok, hy_us))

def GR.drain_tree_all_in_mono(+d: Nat, +G: +List<+List<Nat>>, +n_root: Nat,
    +S: +List<+List<Nat>>, a: Array<+List<SolveFast.CWord>>,
    +acc1: +List<Greedy.RootGuess>, +acc2: +List<Greedy.RootGuess>,
    +ha: GR.BktOk(d, G, n_root, S, a),
    +hsub: {FO.FO.all_in_ref(GR.rgs_words(acc1), GR.rgs_words(acc2))
            == True{} : Bool}) ->
  {FO.FO.all_in_ref(GR.rgs_words(Greedy.rsort_drain_tree(a, acc1)),
     GR.rgs_words(Greedy.rsort_drain_tree(a, acc2))) == True{} : Bool}:
  match d:
    case 0n:
      match a:
        case ALeaf{+ws}:
          GR.prepend_rgs_sub(ws, acc1, acc2, hsub)
        case ANode{xs, ys}:
          Empty.absurd(
            {FO.FO.all_in_ref(
               GR.rgs_words(Greedy.rsort_drain_tree(ANode{xs, ys}, acc1)),
               GR.rgs_words(Greedy.rsort_drain_tree(ANode{xs, ys}, acc2)))
             == True{} : Bool}, ha)
    case 1n+p:
      match a:
        case ALeaf{+ws}:
          Empty.absurd(
            {FO.FO.all_in_ref(
               GR.rgs_words(Greedy.rsort_drain_tree(ALeaf{ws}, acc1)),
               GR.rgs_words(Greedy.rsort_drain_tree(ALeaf{ws}, acc2)))
             == True{} : Bool}, ha)
        case ANode{xs, ys}:
          +hxs = Arr.Arr.dpair_l(GR.BktOk(p, G, n_root, S, xs),
                   GR.BktOk(p, G, n_root, S, ys), ha)
          +hys = Arr.Arr.dpair_r(GR.BktOk(p, G, n_root, S, xs),
                   GR.BktOk(p, G, n_root, S, ys), ha)
          GR.with_dup_arr(+List<SolveFast.CWord>,
            {FO.FO.all_in_ref(
               GR.rgs_words(Greedy.rsort_drain_tree(xs,
                 Greedy.rsort_drain_tree(ys, acc1))),
               GR.rgs_words(Greedy.rsort_drain_tree(xs,
                 Greedy.rsort_drain_tree(ys, acc2)))) == True{} : Bool},
            ys,
            y1 => yr => +ey1 => +eyr =>
            GR.with_dup_arr(+List<SolveFast.CWord>,
              {FO.FO.all_in_ref(
                 GR.rgs_words(Greedy.rsort_drain_tree(xs,
                   Greedy.rsort_drain_tree(ys, acc1))),
                 GR.rgs_words(Greedy.rsort_drain_tree(xs,
                   Greedy.rsort_drain_tree(ys, acc2)))) == True{} : Bool},
              yr,
              y2 => y3 => +ey2r => +ey3r =>
              +ey2 : {y2 == ys : Array<+List<SolveFast.CWord>>} =
                Equal.trans(Array<+List<SolveFast.CWord>>, y2, yr, ys, ey2r, eyr)
              +ey3 : {y3 == ys : Array<+List<SolveFast.CWord>>} =
                Equal.trans(Array<+List<SolveFast.CWord>>, y3, yr, ys, ey3r, eyr)
              +hys1 = GR.bkt_ok_transport(p, G, n_root, S, ys, y1,
                        Equal.sym(Array<+List<SolveFast.CWord>>, y1, ys, ey1),
                        hys)
              +hy1 = GR.drain_tree_all_in_mono(p, G, n_root, S, y1, acc1, acc2,
                       hys1, hsub)
              +ey12 : {y1 == y2 : Array<+List<SolveFast.CWord>>} =
                Equal.trans(Array<+List<SolveFast.CWord>>, y1, ys, y2, ey1,
                  Equal.sym(Array<+List<SolveFast.CWord>>, y2, ys, ey2))
              +ey13 : {y1 == y3 : Array<+List<SolveFast.CWord>>} =
                Equal.trans(Array<+List<SolveFast.CWord>>, y1, ys, y3, ey1,
                  Equal.sym(Array<+List<SolveFast.CWord>>, y3, ys, ey3))
              +hy23 : {FO.FO.all_in_ref(
                         GR.rgs_words(Greedy.rsort_drain_tree(y2, acc1)),
                         GR.rgs_words(Greedy.rsort_drain_tree(y3, acc2)))
                       == True{} : Bool} =
                %ey13 :
                  {FO.FO.all_in_ref(
                     GR.rgs_words(Greedy.rsort_drain_tree(y2, acc1)),
                     GR.rgs_words(Greedy.rsort_drain_tree(_, acc2)))
                   == True{} : Bool}
                %ey12 :
                  {FO.FO.all_in_ref(
                     GR.rgs_words(Greedy.rsort_drain_tree(_, acc1)),
                     GR.rgs_words(Greedy.rsort_drain_tree(y1, acc2)))
                   == True{} : Bool}
                hy1
              %ey2 :
                {FO.FO.all_in_ref(
                   GR.rgs_words(Greedy.rsort_drain_tree(xs,
                     Greedy.rsort_drain_tree(_, acc1))),
                   GR.rgs_words(Greedy.rsort_drain_tree(xs,
                     Greedy.rsort_drain_tree(ys, acc2)))) == True{} : Bool}
              %ey3 :
                {FO.FO.all_in_ref(
                   GR.rgs_words(Greedy.rsort_drain_tree(xs,
                     Greedy.rsort_drain_tree(y2, acc1))),
                   GR.rgs_words(Greedy.rsort_drain_tree(xs,
                     Greedy.rsort_drain_tree(_, acc2)))) == True{} : Bool}
              GR.drain_tree_all_in_mono(p, G, n_root, S, xs,
                Greedy.rsort_drain_tree(y2, acc1),
                Greedy.rsort_drain_tree(y3, acc2), hxs, hy23)))

def GR.SubMem(+g: +List<Nat>, +r1: +List<Greedy.RootGuess>,
    +r2: +List<Greedy.RootGuess>) -> Data:
  Arr.Arr.DPair<
    {FO.FO.all_in_ref(GR.rgs_words(r1), GR.rgs_words(r2)) == True{} : Bool},
    {Tree.member_word(g, GR.rgs_words(r2)) == True{} : Bool}>

def GR.drain_tree_lift_sub_mem(+d: Nat, +G: +List<+List<Nat>>, +n_root: Nat,
    +S: +List<+List<Nat>>, +g: +List<Nat>, a: Array<+List<SolveFast.CWord>>,
    +acc1: +List<Greedy.RootGuess>, +acc2: +List<Greedy.RootGuess>,
    +ha: GR.BktOk(d, G, n_root, S, a),
    +hsub: {FO.FO.all_in_ref(GR.rgs_words(acc1), GR.rgs_words(acc2))
            == True{} : Bool},
    +hm: {Tree.member_word(g, GR.rgs_words(acc2)) == True{} : Bool}) ->
  GR.SubMem(g, Greedy.rsort_drain_tree(a, acc1),
    Greedy.rsort_drain_tree(a, acc2)):
  match d:
    case 0n:
      match a:
        case ALeaf{+ws}:
          Arr.DPair{
            GR.prepend_rgs_sub(ws, acc1, acc2, hsub),
            GR.prepend_rgs_mem_acc(g, ws, acc2, hm)}
        case ANode{xs, ys}:
          Empty.absurd(
            GR.SubMem(g, Greedy.rsort_drain_tree(ANode{xs, ys}, acc1),
              Greedy.rsort_drain_tree(ANode{xs, ys}, acc2)), ha)
    case 1n+p:
      match a:
        case ALeaf{+ws}:
          Empty.absurd(
            GR.SubMem(g, Greedy.rsort_drain_tree(ALeaf{ws}, acc1),
              Greedy.rsort_drain_tree(ALeaf{ws}, acc2)), ha)
        case ANode{xs, ys}:
          +hxs = Arr.Arr.dpair_l(GR.BktOk(p, G, n_root, S, xs),
                   GR.BktOk(p, G, n_root, S, ys), ha)
          +hys = Arr.Arr.dpair_r(GR.BktOk(p, G, n_root, S, xs),
                   GR.BktOk(p, G, n_root, S, ys), ha)
          GR.with_dup_arr(+List<SolveFast.CWord>,
            GR.SubMem(g,
              Greedy.rsort_drain_tree(xs, Greedy.rsort_drain_tree(ys, acc1)),
              Greedy.rsort_drain_tree(xs, Greedy.rsort_drain_tree(ys, acc2))),
            ys,
            y1 => yr => +ey1 => +eyr =>
            GR.with_dup_arr(+List<SolveFast.CWord>,
              GR.SubMem(g,
                Greedy.rsort_drain_tree(xs, Greedy.rsort_drain_tree(ys, acc1)),
                Greedy.rsort_drain_tree(xs, Greedy.rsort_drain_tree(ys, acc2))),
              yr,
              y2 => y3 => +ey2r => +ey3r =>
              +ey2 : {y2 == ys : Array<+List<SolveFast.CWord>>} =
                Equal.trans(Array<+List<SolveFast.CWord>>, y2, yr, ys, ey2r, eyr)
              +ey3 : {y3 == ys : Array<+List<SolveFast.CWord>>} =
                Equal.trans(Array<+List<SolveFast.CWord>>, y3, yr, ys, ey3r, eyr)
              +hys1 = GR.bkt_ok_transport(p, G, n_root, S, ys, y1,
                        Equal.sym(Array<+List<SolveFast.CWord>>, y1, ys, ey1),
                        hys)
              +hy1 = GR.drain_tree_lift_sub_mem(p, G, n_root, S, g, y1, acc1,
                       acc2, hys1, hsub, hm)
              +ey12 : {y1 == y2 : Array<+List<SolveFast.CWord>>} =
                Equal.trans(Array<+List<SolveFast.CWord>>, y1, ys, y2, ey1,
                  Equal.sym(Array<+List<SolveFast.CWord>>, y2, ys, ey2))
              +ey13 : {y1 == y3 : Array<+List<SolveFast.CWord>>} =
                Equal.trans(Array<+List<SolveFast.CWord>>, y1, ys, y3, ey1,
                  Equal.sym(Array<+List<SolveFast.CWord>>, y3, ys, ey3))
              +hsub1 = Arr.Arr.dpair_l(
                         {FO.FO.all_in_ref(
                            GR.rgs_words(Greedy.rsort_drain_tree(y1, acc1)),
                            GR.rgs_words(Greedy.rsort_drain_tree(y1, acc2)))
                          == True{} : Bool},
                         {Tree.member_word(g,
                            GR.rgs_words(Greedy.rsort_drain_tree(y1, acc2)))
                          == True{} : Bool}, hy1)
              +hm1 = Arr.Arr.dpair_r(
                       {FO.FO.all_in_ref(
                          GR.rgs_words(Greedy.rsort_drain_tree(y1, acc1)),
                          GR.rgs_words(Greedy.rsort_drain_tree(y1, acc2)))
                        == True{} : Bool},
                       {Tree.member_word(g,
                          GR.rgs_words(Greedy.rsort_drain_tree(y1, acc2)))
                        == True{} : Bool}, hy1)
              +hsub23 : {FO.FO.all_in_ref(
                           GR.rgs_words(Greedy.rsort_drain_tree(y2, acc1)),
                           GR.rgs_words(Greedy.rsort_drain_tree(y3, acc2)))
                         == True{} : Bool} =
                %ey13 :
                  {FO.FO.all_in_ref(
                     GR.rgs_words(Greedy.rsort_drain_tree(y2, acc1)),
                     GR.rgs_words(Greedy.rsort_drain_tree(_, acc2)))
                   == True{} : Bool}
                %ey12 :
                  {FO.FO.all_in_ref(
                     GR.rgs_words(Greedy.rsort_drain_tree(_, acc1)),
                     GR.rgs_words(Greedy.rsort_drain_tree(y1, acc2)))
                   == True{} : Bool}
                hsub1
              +hm3 : {Tree.member_word(g,
                        GR.rgs_words(Greedy.rsort_drain_tree(y3, acc2)))
                      == True{} : Bool} =
                %ey13 :
                  {Tree.member_word(g,
                     GR.rgs_words(Greedy.rsort_drain_tree(_, acc2)))
                   == True{} : Bool}
                hm1
              +hx = GR.drain_tree_lift_sub_mem(p, G, n_root, S, g, xs,
                      Greedy.rsort_drain_tree(y2, acc1),
                      Greedy.rsort_drain_tree(y3, acc2), hxs, hsub23, hm3)
              +hx_sub = Arr.Arr.dpair_l(
                          {FO.FO.all_in_ref(
                             GR.rgs_words(Greedy.rsort_drain_tree(xs,
                               Greedy.rsort_drain_tree(y2, acc1))),
                             GR.rgs_words(Greedy.rsort_drain_tree(xs,
                               Greedy.rsort_drain_tree(y3, acc2))))
                           == True{} : Bool},
                          {Tree.member_word(g,
                             GR.rgs_words(Greedy.rsort_drain_tree(xs,
                               Greedy.rsort_drain_tree(y3, acc2))))
                           == True{} : Bool}, hx)
              +hx_m = Arr.Arr.dpair_r(
                        {FO.FO.all_in_ref(
                           GR.rgs_words(Greedy.rsort_drain_tree(xs,
                             Greedy.rsort_drain_tree(y2, acc1))),
                           GR.rgs_words(Greedy.rsort_drain_tree(xs,
                             Greedy.rsort_drain_tree(y3, acc2))))
                         == True{} : Bool},
                        {Tree.member_word(g,
                           GR.rgs_words(Greedy.rsort_drain_tree(xs,
                             Greedy.rsort_drain_tree(y3, acc2))))
                         == True{} : Bool}, hx)
              +hsub_f : {FO.FO.all_in_ref(
                           GR.rgs_words(Greedy.rsort_drain_tree(xs,
                             Greedy.rsort_drain_tree(ys, acc1))),
                           GR.rgs_words(Greedy.rsort_drain_tree(xs,
                             Greedy.rsort_drain_tree(ys, acc2))))
                         == True{} : Bool} =
                %ey2 :
                  {FO.FO.all_in_ref(
                     GR.rgs_words(Greedy.rsort_drain_tree(xs,
                       Greedy.rsort_drain_tree(_, acc1))),
                     GR.rgs_words(Greedy.rsort_drain_tree(xs,
                       Greedy.rsort_drain_tree(ys, acc2)))) == True{} : Bool}
                %ey3 :
                  {FO.FO.all_in_ref(
                     GR.rgs_words(Greedy.rsort_drain_tree(xs,
                       Greedy.rsort_drain_tree(y2, acc1))),
                     GR.rgs_words(Greedy.rsort_drain_tree(xs,
                       Greedy.rsort_drain_tree(_, acc2)))) == True{} : Bool}
                hx_sub
              +hm_f : {Tree.member_word(g,
                         GR.rgs_words(Greedy.rsort_drain_tree(xs,
                           Greedy.rsort_drain_tree(ys, acc2)))) == True{} : Bool} =
                %ey3 :
                  {Tree.member_word(g,
                     GR.rgs_words(Greedy.rsort_drain_tree(xs,
                       Greedy.rsort_drain_tree(_, acc2)))) == True{} : Bool}
                hx_m
              Arr.DPair{hsub_f, hm_f}))

def GR.drain_tree_push_sub(+d: Nat, +G: +List<+List<Nat>>, +n_root: Nat,
    +S: +List<+List<Nat>>, +row: U32, +g: +List<Nat>,
    a: Array<+List<SolveFast.CWord>>, +half: U32, +idx: U32, lt: Bool,
    +acc1: +List<Greedy.RootGuess>, +acc2: +List<Greedy.RootGuess>,
    +ha: GR.BktOk(d, G, n_root, S, a),
    +hsub: {FO.FO.all_in_ref(GR.rgs_words(acc1), GR.rgs_words(acc2))
            == True{} : Bool}) ->
  GR.SubMem(g, Greedy.rsort_drain_tree(a, acc1),
    Greedy.rsort_drain_tree(
      Greedy.rsort_push_go(a, half, idx, SolveFast.CWord{0, row, g}, lt),
      acc2)):
  match d:
    case 0n:
      match a:
        case ALeaf{+ws}:
          +acc2c : +List<Greedy.RootGuess> = Greedy.RootGuess{row, g} <> acc2
          Arr.DPair{
            GR.prepend_rgs_sub(ws, acc1, acc2c,
              GR.all_in_sub(GR.rgs_words(acc1), GR.rgs_words(acc2), g, hsub)),
            GR.prepend_rgs_mem_acc(g, ws, acc2c,
              GR.member_cons_l(g, g, GR.rgs_words(acc2),
                FbProof.FbPrf.word_eq_refl(g)))}
        case ANode{xs, ys}:
          Empty.absurd(
            GR.SubMem(g, Greedy.rsort_drain_tree(ANode{xs, ys}, acc1),
              Greedy.rsort_drain_tree(
                Greedy.rsort_push_go(ANode{xs, ys}, half, idx,
                  SolveFast.CWord{0, row, g}, lt), acc2)), ha)
    case 1n+p:
      match a:
        case ALeaf{+ws}:
          Empty.absurd(
            GR.SubMem(g, Greedy.rsort_drain_tree(ALeaf{ws}, acc1),
              Greedy.rsort_drain_tree(
                Greedy.rsort_push_go(ALeaf{ws}, half, idx,
                  SolveFast.CWord{0, row, g}, lt), acc2)), ha)
        case ANode{xs, ys}:
          match lt:
            case True{}:
              +hxs = Arr.Arr.dpair_l(GR.BktOk(p, G, n_root, S, xs),
                       GR.BktOk(p, G, n_root, S, ys), ha)
              +hys = Arr.Arr.dpair_r(GR.BktOk(p, G, n_root, S, xs),
                       GR.BktOk(p, G, n_root, S, ys), ha)
              +h2 = U32.shr(half)
              +lt2 = U32.is_lt(idx, h2)
              +cw : SolveFast.CWord = SolveFast.CWord{0, row, g}
              GR.with_dup_arr(+List<SolveFast.CWord>,
                GR.SubMem(g,
                  Greedy.rsort_drain_tree(xs, Greedy.rsort_drain_tree(ys, acc1)),
                  Greedy.rsort_drain_tree(
                    Greedy.rsort_push_go(xs, h2, idx, cw, lt2),
                    Greedy.rsort_drain_tree(ys, acc2))),
                ys,
                y1 => yr => +ey1 => +eyr =>
                GR.with_dup_arr(+List<SolveFast.CWord>,
                  GR.SubMem(g,
                    Greedy.rsort_drain_tree(xs, Greedy.rsort_drain_tree(ys, acc1)),
                    Greedy.rsort_drain_tree(
                      Greedy.rsort_push_go(xs, h2, idx, cw, lt2),
                      Greedy.rsort_drain_tree(ys, acc2))),
                  yr,
                  y2 => y3 => +ey2r => +ey3r =>
                  +ey2 : {y2 == ys : Array<+List<SolveFast.CWord>>} =
                    Equal.trans(Array<+List<SolveFast.CWord>>, y2, yr, ys,
                      ey2r, eyr)
                  +ey3 : {y3 == ys : Array<+List<SolveFast.CWord>>} =
                    Equal.trans(Array<+List<SolveFast.CWord>>, y3, yr, ys,
                      ey3r, eyr)
                  +hys1 = GR.bkt_ok_transport(p, G, n_root, S, ys, y1,
                            Equal.sym(Array<+List<SolveFast.CWord>>, y1, ys,
                              ey1), hys)
                  +hy1 = GR.drain_tree_all_in_mono(p, G, n_root, S, y1, acc1,
                           acc2, hys1, hsub)
                  +ey12 : {y1 == y2 : Array<+List<SolveFast.CWord>>} =
                    Equal.trans(Array<+List<SolveFast.CWord>>, y1, ys, y2, ey1,
                      Equal.sym(Array<+List<SolveFast.CWord>>, y2, ys, ey2))
                  +ey13 : {y1 == y3 : Array<+List<SolveFast.CWord>>} =
                    Equal.trans(Array<+List<SolveFast.CWord>>, y1, ys, y3, ey1,
                      Equal.sym(Array<+List<SolveFast.CWord>>, y3, ys, ey3))
                  +hy23 : {FO.FO.all_in_ref(
                             GR.rgs_words(Greedy.rsort_drain_tree(y2, acc1)),
                             GR.rgs_words(Greedy.rsort_drain_tree(y3, acc2)))
                           == True{} : Bool} =
                    %ey13 :
                      {FO.FO.all_in_ref(
                         GR.rgs_words(Greedy.rsort_drain_tree(y2, acc1)),
                         GR.rgs_words(Greedy.rsort_drain_tree(_, acc2)))
                       == True{} : Bool}
                    %ey12 :
                      {FO.FO.all_in_ref(
                         GR.rgs_words(Greedy.rsort_drain_tree(_, acc1)),
                         GR.rgs_words(Greedy.rsort_drain_tree(y1, acc2)))
                       == True{} : Bool}
                    hy1
                  +hx = GR.drain_tree_push_sub(p, G, n_root, S, row, g, xs, h2,
                          idx, lt2,
                          Greedy.rsort_drain_tree(y2, acc1),
                          Greedy.rsort_drain_tree(y3, acc2), hxs, hy23)
                  +hx_sub = Arr.Arr.dpair_l(
                              {FO.FO.all_in_ref(
                                 GR.rgs_words(Greedy.rsort_drain_tree(xs,
                                   Greedy.rsort_drain_tree(y2, acc1))),
                                 GR.rgs_words(Greedy.rsort_drain_tree(
                                   Greedy.rsort_push_go(xs, h2, idx, cw, lt2),
                                   Greedy.rsort_drain_tree(y3, acc2))))
                               == True{} : Bool},
                              {Tree.member_word(g,
                                 GR.rgs_words(Greedy.rsort_drain_tree(
                                   Greedy.rsort_push_go(xs, h2, idx, cw, lt2),
                                   Greedy.rsort_drain_tree(y3, acc2))))
                               == True{} : Bool}, hx)
                  +hx_m = Arr.Arr.dpair_r(
                            {FO.FO.all_in_ref(
                               GR.rgs_words(Greedy.rsort_drain_tree(xs,
                                 Greedy.rsort_drain_tree(y2, acc1))),
                               GR.rgs_words(Greedy.rsort_drain_tree(
                                 Greedy.rsort_push_go(xs, h2, idx, cw, lt2),
                                 Greedy.rsort_drain_tree(y3, acc2))))
                             == True{} : Bool},
                            {Tree.member_word(g,
                               GR.rgs_words(Greedy.rsort_drain_tree(
                                 Greedy.rsort_push_go(xs, h2, idx, cw, lt2),
                                 Greedy.rsort_drain_tree(y3, acc2))))
                             == True{} : Bool}, hx)
                  +hsub_f : {FO.FO.all_in_ref(
                               GR.rgs_words(Greedy.rsort_drain_tree(xs,
                                 Greedy.rsort_drain_tree(ys, acc1))),
                               GR.rgs_words(Greedy.rsort_drain_tree(
                                 Greedy.rsort_push_go(xs, h2, idx, cw, lt2),
                                 Greedy.rsort_drain_tree(ys, acc2))))
                             == True{} : Bool} =
                    %ey2 :
                      {FO.FO.all_in_ref(
                         GR.rgs_words(Greedy.rsort_drain_tree(xs,
                           Greedy.rsort_drain_tree(_, acc1))),
                         GR.rgs_words(Greedy.rsort_drain_tree(
                           Greedy.rsort_push_go(xs, h2, idx, cw, lt2),
                           Greedy.rsort_drain_tree(ys, acc2)))) == True{} : Bool}
                    %ey3 :
                      {FO.FO.all_in_ref(
                         GR.rgs_words(Greedy.rsort_drain_tree(xs,
                           Greedy.rsort_drain_tree(y2, acc1))),
                         GR.rgs_words(Greedy.rsort_drain_tree(
                           Greedy.rsort_push_go(xs, h2, idx, cw, lt2),
                           Greedy.rsort_drain_tree(_, acc2)))) == True{} : Bool}
                    hx_sub
                  +hm_f : {Tree.member_word(g,
                             GR.rgs_words(Greedy.rsort_drain_tree(
                               Greedy.rsort_push_go(xs, h2, idx, cw, lt2),
                               Greedy.rsort_drain_tree(ys, acc2))))
                           == True{} : Bool} =
                    %ey3 :
                      {Tree.member_word(g,
                         GR.rgs_words(Greedy.rsort_drain_tree(
                           Greedy.rsort_push_go(xs, h2, idx, cw, lt2),
                           Greedy.rsort_drain_tree(_, acc2)))) == True{} : Bool}
                    hx_m
                  Arr.DPair{hsub_f, hm_f}))
            case False{}:
              +hxs = Arr.Arr.dpair_l(GR.BktOk(p, G, n_root, S, xs),
                       GR.BktOk(p, G, n_root, S, ys), ha)
              +hys = Arr.Arr.dpair_r(GR.BktOk(p, G, n_root, S, xs),
                       GR.BktOk(p, G, n_root, S, ys), ha)
              +h2 = U32.shr(half)
              +idx2 = U32.sub(idx, half)
              +lt2 = U32.is_lt(idx2, h2)
              +cw : SolveFast.CWord = SolveFast.CWord{0, row, g}
              GR.with_dup_arr(+List<SolveFast.CWord>,
                GR.SubMem(g,
                  Greedy.rsort_drain_tree(xs, Greedy.rsort_drain_tree(ys, acc1)),
                  Greedy.rsort_drain_tree(xs,
                    Greedy.rsort_drain_tree(
                      Greedy.rsort_push_go(ys, h2, idx2, cw, lt2), acc2))),
                ys,
                y1 => yr => +ey1 => +eyr =>
                GR.with_dup_arr(+List<SolveFast.CWord>,
                  GR.SubMem(g,
                    Greedy.rsort_drain_tree(xs, Greedy.rsort_drain_tree(ys, acc1)),
                    Greedy.rsort_drain_tree(xs,
                      Greedy.rsort_drain_tree(
                        Greedy.rsort_push_go(ys, h2, idx2, cw, lt2), acc2))),
                  yr,
                  y2 => y3 => +ey2r => +ey3r =>
                  +ey2 : {y2 == ys : Array<+List<SolveFast.CWord>>} =
                    Equal.trans(Array<+List<SolveFast.CWord>>, y2, yr, ys,
                      ey2r, eyr)
                  +ey3 : {y3 == ys : Array<+List<SolveFast.CWord>>} =
                    Equal.trans(Array<+List<SolveFast.CWord>>, y3, yr, ys,
                      ey3r, eyr)
                  +hys1 = GR.bkt_ok_transport(p, G, n_root, S, ys, y1,
                            Equal.sym(Array<+List<SolveFast.CWord>>, y1, ys,
                              ey1), hys)
                  +hy1 = GR.drain_tree_push_sub(p, G, n_root, S, row, g, y1,
                           h2, idx2, lt2, acc1, acc2, hys1, hsub)
                  +ey12 : {y1 == y2 : Array<+List<SolveFast.CWord>>} =
                    Equal.trans(Array<+List<SolveFast.CWord>>, y1, ys, y2, ey1,
                      Equal.sym(Array<+List<SolveFast.CWord>>, y2, ys, ey2))
                  +ey13 : {y1 == y3 : Array<+List<SolveFast.CWord>>} =
                    Equal.trans(Array<+List<SolveFast.CWord>>, y1, ys, y3, ey1,
                      Equal.sym(Array<+List<SolveFast.CWord>>, y3, ys, ey3))
                  +hsub1 = Arr.Arr.dpair_l(
                             {FO.FO.all_in_ref(
                                GR.rgs_words(Greedy.rsort_drain_tree(y1, acc1)),
                                GR.rgs_words(Greedy.rsort_drain_tree(
                                  Greedy.rsort_push_go(y1, h2, idx2, cw, lt2),
                                  acc2))) == True{} : Bool},
                             {Tree.member_word(g,
                                GR.rgs_words(Greedy.rsort_drain_tree(
                                  Greedy.rsort_push_go(y1, h2, idx2, cw, lt2),
                                  acc2))) == True{} : Bool}, hy1)
                  +hm1 = Arr.Arr.dpair_r(
                           {FO.FO.all_in_ref(
                              GR.rgs_words(Greedy.rsort_drain_tree(y1, acc1)),
                              GR.rgs_words(Greedy.rsort_drain_tree(
                                Greedy.rsort_push_go(y1, h2, idx2, cw, lt2),
                                acc2))) == True{} : Bool},
                           {Tree.member_word(g,
                              GR.rgs_words(Greedy.rsort_drain_tree(
                                Greedy.rsort_push_go(y1, h2, idx2, cw, lt2),
                                acc2))) == True{} : Bool}, hy1)
                  +hsub23 : {FO.FO.all_in_ref(
                               GR.rgs_words(Greedy.rsort_drain_tree(y2, acc1)),
                               GR.rgs_words(Greedy.rsort_drain_tree(
                                 Greedy.rsort_push_go(y3, h2, idx2, cw, lt2),
                                 acc2))) == True{} : Bool} =
                    %ey13 :
                      {FO.FO.all_in_ref(
                         GR.rgs_words(Greedy.rsort_drain_tree(y2, acc1)),
                         GR.rgs_words(Greedy.rsort_drain_tree(
                           Greedy.rsort_push_go(_, h2, idx2, cw, lt2), acc2)))
                       == True{} : Bool}
                    %ey12 :
                      {FO.FO.all_in_ref(
                         GR.rgs_words(Greedy.rsort_drain_tree(_, acc1)),
                         GR.rgs_words(Greedy.rsort_drain_tree(
                           Greedy.rsort_push_go(y1, h2, idx2, cw, lt2), acc2)))
                       == True{} : Bool}
                    hsub1
                  +hm3 : {Tree.member_word(g,
                            GR.rgs_words(Greedy.rsort_drain_tree(
                              Greedy.rsort_push_go(y3, h2, idx2, cw, lt2), acc2)))
                          == True{} : Bool} =
                    %ey13 :
                      {Tree.member_word(g,
                         GR.rgs_words(Greedy.rsort_drain_tree(
                           Greedy.rsort_push_go(_, h2, idx2, cw, lt2), acc2)))
                       == True{} : Bool}
                    hm1
                  +hx = GR.drain_tree_lift_sub_mem(p, G, n_root, S, g, xs,
                          Greedy.rsort_drain_tree(y2, acc1),
                          Greedy.rsort_drain_tree(
                            Greedy.rsort_push_go(y3, h2, idx2, cw, lt2), acc2),
                          hxs, hsub23, hm3)
                  +hx_sub = Arr.Arr.dpair_l(
                              {FO.FO.all_in_ref(
                                 GR.rgs_words(Greedy.rsort_drain_tree(xs,
                                   Greedy.rsort_drain_tree(y2, acc1))),
                                 GR.rgs_words(Greedy.rsort_drain_tree(xs,
                                   Greedy.rsort_drain_tree(
                                     Greedy.rsort_push_go(y3, h2, idx2, cw, lt2),
                                     acc2)))) == True{} : Bool},
                              {Tree.member_word(g,
                                 GR.rgs_words(Greedy.rsort_drain_tree(xs,
                                   Greedy.rsort_drain_tree(
                                     Greedy.rsort_push_go(y3, h2, idx2, cw, lt2),
                                     acc2)))) == True{} : Bool}, hx)
                  +hx_m = Arr.Arr.dpair_r(
                            {FO.FO.all_in_ref(
                               GR.rgs_words(Greedy.rsort_drain_tree(xs,
                                 Greedy.rsort_drain_tree(y2, acc1))),
                               GR.rgs_words(Greedy.rsort_drain_tree(xs,
                                 Greedy.rsort_drain_tree(
                                   Greedy.rsort_push_go(y3, h2, idx2, cw, lt2),
                                   acc2)))) == True{} : Bool},
                            {Tree.member_word(g,
                               GR.rgs_words(Greedy.rsort_drain_tree(xs,
                                 Greedy.rsort_drain_tree(
                                   Greedy.rsort_push_go(y3, h2, idx2, cw, lt2),
                                   acc2)))) == True{} : Bool}, hx)
                  +hsub_f : {FO.FO.all_in_ref(
                               GR.rgs_words(Greedy.rsort_drain_tree(xs,
                                 Greedy.rsort_drain_tree(ys, acc1))),
                               GR.rgs_words(Greedy.rsort_drain_tree(xs,
                                 Greedy.rsort_drain_tree(
                                   Greedy.rsort_push_go(ys, h2, idx2, cw, lt2),
                                   acc2)))) == True{} : Bool} =
                    %ey2 :
                      {FO.FO.all_in_ref(
                         GR.rgs_words(Greedy.rsort_drain_tree(xs,
                           Greedy.rsort_drain_tree(_, acc1))),
                         GR.rgs_words(Greedy.rsort_drain_tree(xs,
                           Greedy.rsort_drain_tree(
                             Greedy.rsort_push_go(ys, h2, idx2, cw, lt2),
                             acc2)))) == True{} : Bool}
                    %ey3 :
                      {FO.FO.all_in_ref(
                         GR.rgs_words(Greedy.rsort_drain_tree(xs,
                           Greedy.rsort_drain_tree(y2, acc1))),
                         GR.rgs_words(Greedy.rsort_drain_tree(xs,
                           Greedy.rsort_drain_tree(
                             Greedy.rsort_push_go(_, h2, idx2, cw, lt2),
                             acc2)))) == True{} : Bool}
                    hx_sub
                  +hm_f : {Tree.member_word(g,
                             GR.rgs_words(Greedy.rsort_drain_tree(xs,
                               Greedy.rsort_drain_tree(
                                 Greedy.rsort_push_go(ys, h2, idx2, cw, lt2),
                                 acc2)))) == True{} : Bool} =
                    %ey3 :
                      {Tree.member_word(g,
                         GR.rgs_words(Greedy.rsort_drain_tree(xs,
                           Greedy.rsort_drain_tree(
                             Greedy.rsort_push_go(_, h2, idx2, cw, lt2),
                             acc2)))) == True{} : Bool}
                    hx_m
                  Arr.DPair{hsub_f, hm_f}))

# Pure `Data` invariant on the 1024-slot bucket-sorting array during `rsort_fill`.
def GR.RBktsInv(+G: +List<+List<Nat>>, +n_root: Nat, +S: +List<+List<Nat>>,
    +seen_gs: +List<+List<Nat>>, a: Array<+List<SolveFast.CWord>>) -> Data:
  Arr.Arr.DPair<
    GR.BktOk(10n, G, n_root, S, a),
    {GR.all_usable_in(S, seen_gs,
       GR.rgs_words(Greedy.rsort_drain_tree(a, Nil{}))) == True{} : Bool}>

def GR.rbkts_inv_transport(+G: +List<+List<Nat>>, +n_root: Nat,
    +S: +List<+List<Nat>>, +seen_gs: +List<+List<Nat>>,
    -a1: Array<+List<SolveFast.CWord>>, -a2: Array<+List<SolveFast.CWord>>,
    +ea: {a1 == a2 : Array<+List<SolveFast.CWord>>},
    +h: GR.RBktsInv(G, n_root, S, seen_gs, a1)) ->
  GR.RBktsInv(G, n_root, S, seen_gs, a2):
  %ea : GR.RBktsInv(G, n_root, S, seen_gs, _)
  h

def GR.rbkts_inv_new(+G: +List<+List<Nat>>, +n_root: Nat,
    +S: +List<+List<Nat>>) ->
  GR.RBktsInv(G, n_root, S, Nil{},
    Array.new(+List<SolveFast.CWord>, 10n, Nil{})):
  Arr.DPair{GR.bkt_ok_new(10n, G, n_root, S), {==}}

def GR.rbkts_inv_skip(+G: +List<+List<Nat>>, +n_root: Nat,
    +S: +List<+List<Nat>>, +seen_gs: +List<+List<Nat>>, +g: +List<Nat>,
    -a: Array<+List<SolveFast.CWord>>,
    +hunus: {Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{}))
             == False{} : Bool},
    +hinv: GR.RBktsInv(G, n_root, S, seen_gs, a)) ->
  GR.RBktsInv(G, n_root, S, g <> seen_gs, a):
  +hb = Arr.Arr.dpair_l(GR.BktOk(10n, G, n_root, S, a),
          {GR.all_usable_in(S, seen_gs,
             GR.rgs_words(Greedy.rsort_drain_tree(a, Nil{}))) == True{} : Bool},
          hinv)
  +hall = Arr.Arr.dpair_r(GR.BktOk(10n, G, n_root, S, a),
            {GR.all_usable_in(S, seen_gs,
               GR.rgs_words(Greedy.rsort_drain_tree(a, Nil{}))) == True{} : Bool},
            hinv)
  +hhead : {Feedback.Bool.case(Bool,
              Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
              Tree.member_word(g,
                GR.rgs_words(Greedy.rsort_drain_tree(a, Nil{}))), True{})
            == True{} : Bool} =
    %Equal.sym(Bool,
       Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
       False{}, hunus) :
      {Feedback.Bool.case(Bool, _,
         Tree.member_word(g, GR.rgs_words(Greedy.rsort_drain_tree(a, Nil{}))),
         True{}) == True{} : Bool}
    {==}
  +hall2 : {GR.all_usable_in(S, g <> seen_gs,
              GR.rgs_words(Greedy.rsort_drain_tree(a, Nil{}))) == True{} : Bool} =
    %Equal.sym(Bool,
       Feedback.Bool.case(Bool,
         Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
         Tree.member_word(g, GR.rgs_words(Greedy.rsort_drain_tree(a, Nil{}))),
         True{}), True{}, hhead) :
      {Bool.and(_,
         GR.all_usable_in(S, seen_gs,
           GR.rgs_words(Greedy.rsort_drain_tree(a, Nil{})))) == True{} : Bool}
    hall
  Arr.DPair{hb, hall2}

def GR.rbkts_push_all_usable(+S: +List<+List<Nat>>, +seen_gs: +List<+List<Nat>>,
    +g: +List<Nat>, +rgs1: +List<Greedy.RootGuess>,
    +rgs2: +List<Greedy.RootGuess>,
    +hall1: {GR.all_usable_in(S, seen_gs, GR.rgs_words(rgs1)) == True{} : Bool},
    +hsub: {FO.FO.all_in_ref(GR.rgs_words(rgs1), GR.rgs_words(rgs2))
            == True{} : Bool},
    +hm: {Tree.member_word(g, GR.rgs_words(rgs2)) == True{} : Bool}) ->
  {GR.all_usable_in(S, g <> seen_gs, GR.rgs_words(rgs2)) == True{} : Bool}:
  FO.FO.bool_and_intro(
    Feedback.Bool.case(Bool,
      Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
      Tree.member_word(g, GR.rgs_words(rgs2)), True{}),
    GR.all_usable_in(S, seen_gs, GR.rgs_words(rgs2)),
    GR.bool_case_true_r(
      Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
      Tree.member_word(g, GR.rgs_words(rgs2)), hm),
    GR.all_usable_in_mono(S, seen_gs, GR.rgs_words(rgs1), GR.rgs_words(rgs2),
      hsub, hall1))

def GR.rbkts_inv_push(+G: +List<+List<Nat>>, +n_root: Nat,
    +S: +List<+List<Nat>>, +seen_gs: +List<+List<Nat>>,
    +row: U32, +g: +List<Nat>, +half: U32, +idx: U32, +lt: Bool,
    a: Array<+List<SolveFast.CWord>>,
    +hrow: {FT.FT.gentry_ok_b(G, n_root, row, g) == True{} : Bool},
    +hwg: {Tree.member_word(g, G) == True{} : Bool},
    +hus: {Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{}))
           == True{} : Bool},
    +hinv: GR.RBktsInv(G, n_root, S, seen_gs, a)) ->
  GR.RBktsInv(G, n_root, S, g <> seen_gs,
    Greedy.rsort_push_go(a, half, idx, SolveFast.CWord{0, row, g}, lt)):
  +cw : SolveFast.CWord = SolveFast.CWord{0, row, g}
  +hb = Arr.Arr.dpair_l(GR.BktOk(10n, G, n_root, S, a),
          {GR.all_usable_in(S, seen_gs,
             GR.rgs_words(Greedy.rsort_drain_tree(a, Nil{}))) == True{} : Bool},
          hinv)
  +hall = Arr.Arr.dpair_r(GR.BktOk(10n, G, n_root, S, a),
            {GR.all_usable_in(S, seen_gs,
               GR.rgs_words(Greedy.rsort_drain_tree(a, Nil{}))) == True{} : Bool},
            hinv)
  GR.with_dup_arr(+List<SolveFast.CWord>,
    GR.RBktsInv(G, n_root, S, g <> seen_gs,
      Greedy.rsort_push_go(a, half, idx, cw, lt)),
    a,
    a1 => ar1 => +ea1 => +ear1 =>
    GR.with_dup_arr(+List<SolveFast.CWord>,
      GR.RBktsInv(G, n_root, S, g <> seen_gs,
        Greedy.rsort_push_go(a, half, idx, cw, lt)),
      ar1,
      a2 => ar2 => +ea2r => +ear2r =>
      GR.with_dup_arr(+List<SolveFast.CWord>,
        GR.RBktsInv(G, n_root, S, g <> seen_gs,
          Greedy.rsort_push_go(a, half, idx, cw, lt)),
        ar2,
        a3 => a4 => +ea3r => +ea4r =>
        +ea2 : {a2 == a : Array<+List<SolveFast.CWord>>} =
          Equal.trans(Array<+List<SolveFast.CWord>>, a2, ar1, a, ea2r, ear1)
        +ear2 : {ar2 == a : Array<+List<SolveFast.CWord>>} =
          Equal.trans(Array<+List<SolveFast.CWord>>, ar2, ar1, a, ear2r, ear1)
        +ea3 : {a3 == a : Array<+List<SolveFast.CWord>>} =
          Equal.trans(Array<+List<SolveFast.CWord>>, a3, ar2, a, ea3r, ear2)
        +ea4 : {a4 == a : Array<+List<SolveFast.CWord>>} =
          Equal.trans(Array<+List<SolveFast.CWord>>, a4, ar2, a, ea4r, ear2)
        +hb1 = GR.bkt_ok_transport(10n, G, n_root, S, a, a1,
                 Equal.sym(Array<+List<SolveFast.CWord>>, a1, a, ea1), hb)
        +hb2 = GR.bkt_ok_transport(10n, G, n_root, S, a, a2,
                 Equal.sym(Array<+List<SolveFast.CWord>>, a2, a, ea2), hb)
        +hb_p : GR.BktOk(10n, G, n_root, S,
                  Greedy.rsort_push_go(a, half, idx, cw, lt)) =
          %ea1 : GR.BktOk(10n, G, n_root, S,
                   Greedy.rsort_push_go(_, half, idx, cw, lt))
          GR.bkt_ok_push(10n, G, n_root, S, row, g, a1, half, idx, lt, hrow,
            hwg, hus, hb1)
        +hsm2 = GR.drain_tree_push_sub(10n, G, n_root, S, row, g, a2, half,
                  idx, lt, Nil{}, Nil{}, hb2, {==})
        +hsub2 = Arr.Arr.dpair_l(
                   {FO.FO.all_in_ref(
                      GR.rgs_words(Greedy.rsort_drain_tree(a2, Nil{})),
                      GR.rgs_words(Greedy.rsort_drain_tree(
                        Greedy.rsort_push_go(a2, half, idx, cw, lt), Nil{})))
                    == True{} : Bool},
                   {Tree.member_word(g,
                      GR.rgs_words(Greedy.rsort_drain_tree(
                        Greedy.rsort_push_go(a2, half, idx, cw, lt), Nil{})))
                    == True{} : Bool}, hsm2)
        +hm2 = Arr.Arr.dpair_r(
                 {FO.FO.all_in_ref(
                    GR.rgs_words(Greedy.rsort_drain_tree(a2, Nil{})),
                    GR.rgs_words(Greedy.rsort_drain_tree(
                      Greedy.rsort_push_go(a2, half, idx, cw, lt), Nil{})))
                  == True{} : Bool},
                 {Tree.member_word(g,
                    GR.rgs_words(Greedy.rsort_drain_tree(
                      Greedy.rsort_push_go(a2, half, idx, cw, lt), Nil{})))
                  == True{} : Bool}, hsm2)
        +ea23 : {a2 == a3 : Array<+List<SolveFast.CWord>>} =
          Equal.trans(Array<+List<SolveFast.CWord>>, a2, a, a3, ea2,
            Equal.sym(Array<+List<SolveFast.CWord>>, a3, a, ea3))
        +ea24 : {a2 == a4 : Array<+List<SolveFast.CWord>>} =
          Equal.trans(Array<+List<SolveFast.CWord>>, a2, a, a4, ea2,
            Equal.sym(Array<+List<SolveFast.CWord>>, a4, a, ea4))
        +hall3 : {GR.all_usable_in(S, seen_gs,
                    GR.rgs_words(Greedy.rsort_drain_tree(a3, Nil{})))
                  == True{} : Bool} =
          %Equal.sym(Array<+List<SolveFast.CWord>>, a3, a, ea3) :
            {GR.all_usable_in(S, seen_gs,
               GR.rgs_words(Greedy.rsort_drain_tree(_, Nil{})))
             == True{} : Bool}
          hall
        +hsub34 : {FO.FO.all_in_ref(
                     GR.rgs_words(Greedy.rsort_drain_tree(a3, Nil{})),
                     GR.rgs_words(Greedy.rsort_drain_tree(
                       Greedy.rsort_push_go(a4, half, idx, cw, lt), Nil{})))
                   == True{} : Bool} =
          %ea24 :
            {FO.FO.all_in_ref(
               GR.rgs_words(Greedy.rsort_drain_tree(a3, Nil{})),
               GR.rgs_words(Greedy.rsort_drain_tree(
                 Greedy.rsort_push_go(_, half, idx, cw, lt), Nil{})))
             == True{} : Bool}
          %ea23 :
            {FO.FO.all_in_ref(
               GR.rgs_words(Greedy.rsort_drain_tree(_, Nil{})),
               GR.rgs_words(Greedy.rsort_drain_tree(
                 Greedy.rsort_push_go(a2, half, idx, cw, lt), Nil{})))
             == True{} : Bool}
          hsub2
        +hm4 : {Tree.member_word(g,
                  GR.rgs_words(Greedy.rsort_drain_tree(
                    Greedy.rsort_push_go(a4, half, idx, cw, lt), Nil{})))
                == True{} : Bool} =
          %ea24 :
            {Tree.member_word(g,
               GR.rgs_words(Greedy.rsort_drain_tree(
                 Greedy.rsort_push_go(_, half, idx, cw, lt), Nil{})))
             == True{} : Bool}
          hm2
        +hall_p : {GR.all_usable_in(S, g <> seen_gs,
                     GR.rgs_words(Greedy.rsort_drain_tree(
                       Greedy.rsort_push_go(a, half, idx, cw, lt), Nil{})))
                   == True{} : Bool} =
          %ea4 :
            {GR.all_usable_in(S, g <> seen_gs,
               GR.rgs_words(Greedy.rsort_drain_tree(
                 Greedy.rsort_push_go(_, half, idx, cw, lt), Nil{})))
             == True{} : Bool}
          GR.rbkts_push_all_usable(S, seen_gs, g,
            Greedy.rsort_drain_tree(a3, Nil{}),
            Greedy.rsort_drain_tree(
              Greedy.rsort_push_go(a4, half, idx, cw, lt), Nil{}),
            hall3, hsub34, hm4)
        Arr.DPair{hb_p, hall_p})))

# `fgroups_total(fgroups_build_fast(g, ws, fg0)) <= len_words(ws) + fgroups_total(fg0)`.
def GR.fgroups_total_next_le(+g: +List<Nat>, +w: +List<Nat>,
    +fg: +List<SolveFast.FGroup>, same: Bool) ->
  {Nat.is_le(
     FH.FH.fgroups_total(SolveFast.fgroups_next_acc(g, w, fg, same)),
     Nat.add(1n, FH.FH.fgroups_total(fg))) == True{} : Bool}:
  match same:
    case True{}:
      NatProof.Nat.is_le_of_lt(FH.FH.fgroups_total(fg),
        1n+FH.FH.fgroups_total(fg),
        NatProof.Nat.is_lt_succ_self(FH.FH.fgroups_total(fg)))
    case False{}:
      Fold.OQ.le_cong_l(
        FH.FH.fgroups_total(
          SolveFast.fgroup_add_fast(w, SolveFast.feedback_fast(g, w), fg)),
        Nat.add(1n, FH.FH.fgroups_total(fg)),
        Nat.add(1n, FH.FH.fgroups_total(fg)),
        FH.FH.fgroup_add_total(w, SolveFast.feedback_fast(g, w), fg,
          SolveFast.next_fgroup_hit(SolveFast.feedback_fast(g, w), fg)),
        NatProof.Nat.is_le_refl(Nat.add(1n, FH.FH.fgroups_total(fg))))

def GR.fgroups_total_build_le(+g: +List<Nat>, +ws: +List<+List<Nat>>,
    +fg0: +List<SolveFast.FGroup>) ->
  {Nat.is_le(
     FH.FH.fgroups_total(SolveFast.fgroups_build_fast(g, ws, fg0)),
     Nat.add(Groups.len_words(ws), FH.FH.fgroups_total(fg0)))
   == True{} : Bool}:
  match ws:
    case Nil{}:
      NatProof.Nat.is_le_refl(FH.FH.fgroups_total(fg0))
    case Con{+w, +rest}:
      +fg1 = SolveFast.fgroups_next_acc(g, w, fg0, SolveFast.word_eq_fast(g, w))
      NatProof.Nat.is_le_trans(
        FH.FH.fgroups_total(SolveFast.fgroups_build_fast(g, rest, fg1)),
        Nat.add(Groups.len_words(rest), FH.FH.fgroups_total(fg1)),
        Nat.add(1n+Groups.len_words(rest), FH.FH.fgroups_total(fg0)),
        GR.fgroups_total_build_le(g, rest, fg1),
        NatProof.Nat.is_le_eq_r(
          Nat.add(Groups.len_words(rest), FH.FH.fgroups_total(fg1)),
          Nat.add(Groups.len_words(rest), Nat.add(1n, FH.FH.fgroups_total(fg0))),
          Nat.add(1n+Groups.len_words(rest), FH.FH.fgroups_total(fg0)),
          NatProof.NatPrf.add_succ(Groups.len_words(rest),
            FH.FH.fgroups_total(fg0)),
          NatProof.Nat.is_le_add_l(FH.FH.fgroups_total(fg1),
            Nat.add(1n, FH.FH.fgroups_total(fg0)), Groups.len_words(rest),
            GR.fgroups_total_next_le(g, w, fg0, SolveFast.word_eq_fast(g, w)))))

def GR.not_le_succ_self(n: Nat,
    +h: {Nat.is_le(1n+n, n) == True{} : Bool}) -> Empty:
  match n:
    case 0n:
      Logic.Proof.false_ne_true(h)
    case 1n+p:
      GR.not_le_succ_self(p, h)

def GR.not_le_succ_add(+n: Nat, +k: Nat,
    +h: {Nat.is_le(Nat.add(1n, Nat.add(n, k)), n) == True{} : Bool}) -> Empty:
  +h1 : {Nat.is_le(1n+n, n) == True{} : Bool} =
    NatProof.Nat.is_le_trans(1n+n, 1n+Nat.add(n, k), n,
      NatProof.Nat.is_le_add_l(n, Nat.add(n, k), 1n, FT.FT.nat_le_add_l(n, k)),
      h)
  GR.not_le_succ_self(n, h1)

def GR.RSortSpec(+G: +List<+List<Nat>>, +C_root: +List<+List<Nat>>,
    +n_root: Nat, +S: +List<+List<Nat>>, +seen_gs: +List<+List<Nat>>,
    st: Greedy.RSortSt) -> Data:
  match st:
    case Greedy.RSortSt{seen, bkts, tbl, gen}:
      Arr.Arr.DPair<
        FH.FH.SeenTree(10n, 0, seen, gen, Nil{}),
        Arr.Arr.DPair<
          FT.FT.TblOk(G, C_root, n_root, tbl),
          GR.RBktsInv(G, n_root, S, seen_gs, bkts)>>

def GR.rsort_spec_transport(+G: +List<+List<Nat>>, +C_root: +List<+List<Nat>>,
    +n_root: Nat, +S: +List<+List<Nat>>, +seen_gs: +List<+List<Nat>>,
    -s1: Greedy.RSortSt, -s2: Greedy.RSortSt,
    +e: {s1 == s2 : Greedy.RSortSt},
    +h: GR.RSortSpec(G, C_root, n_root, S, seen_gs, s1)) ->
  GR.RSortSpec(G, C_root, n_root, S, seen_gs, s2):
  %e : GR.RSortSpec(G, C_root, n_root, S, seen_gs, _)
  h

def GR.rsort_usable_ok(+G: +List<+List<Nat>>, +C_root: +List<+List<Nat>>,
    +n_root: Nat, +S: +List<+List<Nat>>, +seen_gs: +List<+List<Nat>>,
    +row: U32, +g: +List<Nat>, +n: Nat, +base_lb: Nat,
    seen: Array<Nat>, bkts: Array<+List<SolveFast.CWord>>, tbl: Array<U32>,
    +gen2: Nat, +m: Nat, +k: Nat, usable: Bool,
    +eus: {usable == Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{}))
           : Bool},
    +hrow: {FT.FT.gentry_ok_b(G, n_root, row, g) == True{} : Bool},
    +hwg: {Tree.member_word(g, G) == True{} : Bool},
    +hs: FH.FH.SeenTree(10n, 0, seen, gen2, Nil{}),
    +ht: FT.FT.TblOk(G, C_root, n_root, tbl),
    +hb: GR.RBktsInv(G, n_root, S, seen_gs, bkts)) ->
  GR.RSortSpec(G, C_root, n_root, S, g <> seen_gs,
    Greedy.rsort_hist_usable(row, g, n, base_lb, seen, bkts, tbl, gen2, m, k,
      usable)):
  match usable:
    case False{}:
      Arr.DPair{hs, Arr.DPair{ht,
        GR.rbkts_inv_skip(G, n_root, S, seen_gs, g, bkts,
          Equal.sym(Bool, False{},
            Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})), eus),
          hb)}}
    case True{}:
      +lb = Nat.sub(Nat.add(n, Nat.add(m, m)), k)
      +idx_u = U32.from_nat(Greedy.nat_min_1023(Nat.sub(lb, base_lb)))
      +hus = Equal.sym(Bool, True{},
               Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})), eus)
      Arr.DPair{hs, Arr.DPair{ht,
        GR.rbkts_inv_push(G, n_root, S, seen_gs, row, g, 512, idx_u,
          U32.is_lt(idx_u, 512), bkts, hrow, hwg, hus, hb)}}

def GR.rsort_hist_one_ok(+G: +List<+List<Nat>>, +C_root: +List<+List<Nat>>,
    +n_root: Nat, +ws: +List<+List<Nat>>, +seen_gs: +List<+List<Nat>>,
    +row: U32, +g: +List<Nat>, +n: Nat, +base_lb: Nat,
    bkts: Array<+List<SolveFast.CWord>>, -tbl0: Array<U32>, +gen: Nat,
    hr: SolveFast.Hist5Res,
    +hge1: {Nat.is_le(1n, n) == True{} : Bool},
    +en: {n == Groups.len_words(ws) : Nat},
    +hrow: {FT.FT.gentry_ok_b(G, n_root, row, g) == True{} : Bool},
    +hwg: {Tree.member_word(g, G) == True{} : Bool},
    +ht0: FT.FT.TblOk(G, C_root, n_root, tbl0),
    +hb: GR.RBktsInv(G, n_root, ws, seen_gs, bkts),
    +hhr: FH.FH.HistSpec(g, ws, Nil{}, gen, n, False{}, tbl0, hr)) ->
  GR.RSortSpec(G, C_root, n_root, ws, g <> seen_gs,
    Greedy.rsort_hist_one(row, g, n, base_lb, bkts, gen, hr)):
  match hr:
    case SolveFast.Hist5Pruned{seen2, tbl2}:
      +r1 = Arr.Arr.dpair_r(
              FH.FH.SeenTree(10n, 0, seen2, Nat.add(1n, gen), Nil{}),
              Arr.Arr.DPair<{tbl2 == tbl0 : Array<U32>},
                {FH.FH.pruned_reason(g, ws, Nil{}, n, False{})
                 == True{} : Bool}>, hhr)
      +hpr = Arr.Arr.dpair_r({tbl2 == tbl0 : Array<U32>},
               {FH.FH.pruned_reason(g, ws, Nil{}, n, False{})
                == True{} : Bool}, r1)
      +fg = SolveFast.fgroups_build_fast(g, ws, Nil{})
      +hle_m : {Nat.is_le(FH.FH.fgroups_total(fg), n) == True{} : Bool} =
        NatProof.Nat.is_le_eq_r(FH.FH.fgroups_total(fg),
          Nat.add(Groups.len_words(ws), 0n), n,
          Equal.trans(Nat, Nat.add(Groups.len_words(ws), 0n),
            Groups.len_words(ws), n,
            NatProof.NatPrf.add_zero(Groups.len_words(ws)),
            Equal.sym(Nat, n, Groups.len_words(ws), en)),
          GR.fgroups_total_build_le(g, ws, Nil{}))
      Empty.absurd(
        GR.RSortSpec(G, C_root, n_root, ws, g <> seen_gs,
          Greedy.RSortSt{seen2, bkts, tbl2, Nat.add(1n, gen)}),
        GR.not_le_succ_add(n, FH.FH.fgroups_count(fg),
          NatProof.Nat.is_le_trans(
            Nat.add(1n, Nat.add(n, FH.FH.fgroups_count(fg))),
            FH.FH.fgroups_total(fg), n, hpr, hle_m)))
    case SolveFast.Hist5Ok{seen2, tbl2, +m, +k, +b}:
      +fg = SolveFast.fgroups_build_fast(g, ws, Nil{})
      +hs2 = Arr.Arr.dpair_l(FH.FH.SeenTree(10n, 0, seen2, gen, fg),
               Arr.Arr.DPair<{tbl2 == tbl0 : Array<U32>},
                 Arr.Arr.DPair<{FH.FH.fgroups_wf(fg) == True{} : Bool},
                   Arr.Arr.DPair<{m == FH.FH.fgroups_total(fg) : Nat},
                     Arr.Arr.DPair<{k == FH.FH.fgroups_count(fg) : Nat},
                       Arr.Arr.DPair<{Nat.add(b, m) == Nat.add(n, k) : Nat},
                         {Nat.is_le(m, Nat.add(Groups.len_words(ws), 0n))
                          == True{} : Bool}>>>>>, hhr)
      +r1 = Arr.Arr.dpair_r(FH.FH.SeenTree(10n, 0, seen2, gen, fg),
              Arr.Arr.DPair<{tbl2 == tbl0 : Array<U32>},
                Arr.Arr.DPair<{FH.FH.fgroups_wf(fg) == True{} : Bool},
                  Arr.Arr.DPair<{m == FH.FH.fgroups_total(fg) : Nat},
                    Arr.Arr.DPair<{k == FH.FH.fgroups_count(fg) : Nat},
                      Arr.Arr.DPair<{Nat.add(b, m) == Nat.add(n, k) : Nat},
                        {Nat.is_le(m, Nat.add(Groups.len_words(ws), 0n))
                         == True{} : Bool}>>>>>, hhr)
      +et20 = Arr.Arr.dpair_l({tbl2 == tbl0 : Array<U32>},
                Arr.Arr.DPair<{FH.FH.fgroups_wf(fg) == True{} : Bool},
                  Arr.Arr.DPair<{m == FH.FH.fgroups_total(fg) : Nat},
                    Arr.Arr.DPair<{k == FH.FH.fgroups_count(fg) : Nat},
                      Arr.Arr.DPair<{Nat.add(b, m) == Nat.add(n, k) : Nat},
                        {Nat.is_le(m, Nat.add(Groups.len_words(ws), 0n))
                         == True{} : Bool}>>>>, r1)
      +r2 = Arr.Arr.dpair_r({tbl2 == tbl0 : Array<U32>},
              Arr.Arr.DPair<{FH.FH.fgroups_wf(fg) == True{} : Bool},
                Arr.Arr.DPair<{m == FH.FH.fgroups_total(fg) : Nat},
                  Arr.Arr.DPair<{k == FH.FH.fgroups_count(fg) : Nat},
                    Arr.Arr.DPair<{Nat.add(b, m) == Nat.add(n, k) : Nat},
                      {Nat.is_le(m, Nat.add(Groups.len_words(ws), 0n))
                       == True{} : Bool}>>>>, r1)
      +hwf = Arr.Arr.dpair_l({FH.FH.fgroups_wf(fg) == True{} : Bool},
               Arr.Arr.DPair<{m == FH.FH.fgroups_total(fg) : Nat},
                 Arr.Arr.DPair<{k == FH.FH.fgroups_count(fg) : Nat},
                   Arr.Arr.DPair<{Nat.add(b, m) == Nat.add(n, k) : Nat},
                     {Nat.is_le(m, Nat.add(Groups.len_words(ws), 0n))
                      == True{} : Bool}>>>, r2)
      +r3 = Arr.Arr.dpair_r({FH.FH.fgroups_wf(fg) == True{} : Bool},
              Arr.Arr.DPair<{m == FH.FH.fgroups_total(fg) : Nat},
                Arr.Arr.DPair<{k == FH.FH.fgroups_count(fg) : Nat},
                  Arr.Arr.DPair<{Nat.add(b, m) == Nat.add(n, k) : Nat},
                    {Nat.is_le(m, Nat.add(Groups.len_words(ws), 0n))
                     == True{} : Bool}>>>, r2)
      +hm = Arr.Arr.dpair_l({m == FH.FH.fgroups_total(fg) : Nat},
              Arr.Arr.DPair<{k == FH.FH.fgroups_count(fg) : Nat},
                Arr.Arr.DPair<{Nat.add(b, m) == Nat.add(n, k) : Nat},
                  {Nat.is_le(m, Nat.add(Groups.len_words(ws), 0n))
                   == True{} : Bool}>>, r3)
      +r4 = Arr.Arr.dpair_r({m == FH.FH.fgroups_total(fg) : Nat},
              Arr.Arr.DPair<{k == FH.FH.fgroups_count(fg) : Nat},
                Arr.Arr.DPair<{Nat.add(b, m) == Nat.add(n, k) : Nat},
                  {Nat.is_le(m, Nat.add(Groups.len_words(ws), 0n))
                   == True{} : Bool}>>, r3)
      +hk = Arr.Arr.dpair_l({k == FH.FH.fgroups_count(fg) : Nat},
              Arr.Arr.DPair<{Nat.add(b, m) == Nat.add(n, k) : Nat},
                {Nat.is_le(m, Nat.add(Groups.len_words(ws), 0n))
                 == True{} : Bool}>, r4)
      +r5 = Arr.Arr.dpair_r({k == FH.FH.fgroups_count(fg) : Nat},
              Arr.Arr.DPair<{Nat.add(b, m) == Nat.add(n, k) : Nat},
                {Nat.is_le(m, Nat.add(Groups.len_words(ws), 0n))
                 == True{} : Bool}>, r4)
      +hle0 = Arr.Arr.dpair_r({Nat.add(b, m) == Nat.add(n, k) : Nat},
                {Nat.is_le(m, Nat.add(Groups.len_words(ws), 0n))
                 == True{} : Bool}, r5)
      +ht2 = FT.FT.tbl_ok_transport(G, C_root, n_root, tbl0, tbl2,
               Equal.sym(Array<U32>, tbl2, tbl0, et20), ht0)
      +eus = GR.usable_eq_of_hist(g, ws, n, m, k, hge1, en, hwf, hm, hk, hle0)
      GR.with_dup_arr(Nat,
        GR.RSortSpec(G, C_root, n_root, ws, g <> seen_gs,
          Greedy.rsort_hist_usable(row, g, n, base_lb, seen2, bkts, tbl2,
            Nat.add(1n, gen), m, k,
            Bool.or(Nat.is_lt(m, n), Nat.is_le(2n, k)))),
        seen2,
        s1 => s2 => +es1 => +es2 =>
        +hbump = FH.FH.seen_tree_transport(10n, 0, s2, s1, Nat.add(1n, gen),
                   Nil{},
                   Equal.trans(Array<Nat>, s2, seen2, s1, es2,
                     Equal.sym(Array<Nat>, s1, seen2, es1)),
                   FH.FH.seen_tree_bump(10n, 0, s2, gen, fg,
                     FH.FH.seen_tree_transport(10n, 0, seen2, s2, gen, fg,
                       Equal.sym(Array<Nat>, s2, seen2, es2), hs2)))
        %es1 : GR.RSortSpec(G, C_root, n_root, ws, g <> seen_gs,
                 Greedy.rsort_hist_usable(row, g, n, base_lb, _, bkts, tbl2,
                   Nat.add(1n, gen), m, k,
                   Bool.or(Nat.is_lt(m, n), Nat.is_le(2n, k))))
        GR.rsort_usable_ok(G, C_root, n_root, ws, seen_gs, row, g, n, base_lb,
          s1, bkts, tbl2, Nat.add(1n, gen), m, k,
          Bool.or(Nat.is_lt(m, n), Nat.is_le(2n, k)), eus, hrow, hwg, hbump,
          ht2, hb))

def GR.rsort_fill_ok(+rem: +List<+List<Nat>>, +row: U32,
    +G: +List<+List<Nat>>, +C_root: +List<+List<Nat>>, +n_root: Nat,
    +S: +List<SolveFast.CWord>, +n: Nat, +base_lb: Nat,
    +seen_gs: +List<+List<Nat>>, st: Greedy.RSortSt,
    +hrws: {FT.FT.rws_ok_b(G, n_root, FT.FT.guesses_to_rws(rem, row, 1))
            == True{} : Bool},
    +hai_rem: {FO.FO.all_in_ref(rem, G) == True{} : Bool},
    +hge1: {Nat.is_le(1n, n) == True{} : Bool},
    +en: {n == Groups.len_words(SolveFast.cwords_words(S)) : Nat},
    +hS: {FT.FT.cwords_ok_b(G, C_root, n_root, S) == True{} : Bool},
    +hst: GR.RSortSpec(G, C_root, n_root, SolveFast.cwords_words(S), seen_gs,
            st)) ->
  GR.RSortSpec(G, C_root, n_root, SolveFast.cwords_words(S),
    GR.rev_words(rem, seen_gs),
    Greedy.rsort_fill(rem, row, S, n, base_lb, st)):
  match rem:
    case Nil{}:
      hst
    case Con{+g, +rest}:
      match st:
        case Greedy.RSortSt{seen, bkts, tbl, +gen}:
          +ws = SolveFast.cwords_words(S)
          +hs = Arr.Arr.dpair_l(FH.FH.SeenTree(10n, 0, seen, gen, Nil{}),
                  Arr.Arr.DPair<FT.FT.TblOk(G, C_root, n_root, tbl),
                    GR.RBktsInv(G, n_root, ws, seen_gs, bkts)>, hst)
          +r1 = Arr.Arr.dpair_r(FH.FH.SeenTree(10n, 0, seen, gen, Nil{}),
                  Arr.Arr.DPair<FT.FT.TblOk(G, C_root, n_root, tbl),
                    GR.RBktsInv(G, n_root, ws, seen_gs, bkts)>, hst)
          +ht = Arr.Arr.dpair_l(FT.FT.TblOk(G, C_root, n_root, tbl),
                  GR.RBktsInv(G, n_root, ws, seen_gs, bkts), r1)
          +hb = Arr.Arr.dpair_r(FT.FT.TblOk(G, C_root, n_root, tbl),
                  GR.RBktsInv(G, n_root, ws, seen_gs, bkts), r1)
          +hrow = Logic.Proof.and_true_l(FT.FT.gentry_ok_b(G, n_root, row, g),
                    FT.FT.rws_ok_b(G, n_root,
                      FT.FT.guesses_to_rws(rest, U32.add(row, 1), 1)), hrws)
          +hrws_r = Logic.Proof.and_true_r(FT.FT.gentry_ok_b(G, n_root, row, g),
                      FT.FT.rws_ok_b(G, n_root,
                        FT.FT.guesses_to_rws(rest, U32.add(row, 1), 1)), hrws)
          +hwg = FO.FO.all_in_head(g, rest, G, hai_rem)
          +hai_r = FO.FO.all_in_tail(g, rest, G, hai_rem)
          GR.with_dup_arr(Nat,
            GR.RSortSpec(G, C_root, n_root, ws, GR.rev_words(rest, g <> seen_gs),
              Greedy.rsort_fill(rest, U32.add(row, 1), S, n, base_lb,
                Greedy.rsort_hist_one(row, g, n, base_lb, bkts, gen,
                  SolveFast.hist5_go(row, S, gen, False{},
                    SolveFast.Hist5Ok{seen, tbl, 0n, 0n, n})))),
            seen,
            s_hi => s_run => +es_hi => +es_run =>
            GR.with_dup_arr(U32,
              GR.RSortSpec(G, C_root, n_root, ws,
                GR.rev_words(rest, g <> seen_gs),
                Greedy.rsort_fill(rest, U32.add(row, 1), S, n, base_lb,
                  Greedy.rsort_hist_one(row, g, n, base_lb, bkts, gen,
                    SolveFast.hist5_go(row, S, gen, False{},
                      SolveFast.Hist5Ok{seen, tbl, 0n, 0n, n})))),
              tbl,
              t_hi => t_run => +et_hi => +et_run =>
              GR.with_dup_arr(+List<SolveFast.CWord>,
                GR.RSortSpec(G, C_root, n_root, ws,
                  GR.rev_words(rest, g <> seen_gs),
                  Greedy.rsort_fill(rest, U32.add(row, 1), S, n, base_lb,
                    Greedy.rsort_hist_one(row, g, n, base_lb, bkts, gen,
                      SolveFast.hist5_go(row, S, gen, False{},
                        SolveFast.Hist5Ok{seen, tbl, 0n, 0n, n})))),
                bkts,
                b_step => b_run => +eb_step => +eb_run =>
                +hs_hi = FH.FH.seen_tree_transport(10n, 0, seen, s_hi, gen,
                           Nil{}, Equal.sym(Array<Nat>, s_hi, seen, es_hi), hs)
                +ht_hi = FT.FT.tbl_ok_transport(G, C_root, n_root, tbl, t_hi,
                           Equal.sym(Array<U32>, t_hi, tbl, et_hi), ht)
                +hb_st = GR.rbkts_inv_transport(G, n_root, ws, seen_gs, bkts,
                           b_step,
                           Equal.sym(Array<+List<SolveFast.CWord>>, b_step, bkts,
                             eb_step), hb)
                +hhr_hi = FH.FH.hist5_go_spec(S, G, C_root, n_root, row, g,
                            Nil{}, s_hi, t_hi, gen, 0n, 0n, n, n, False{}, ht_hi,
                            hrow, hS,
                            Equal.trans(Nat, Nat.add(n, 0n), n, Nat.add(n, 0n),
                              NatProof.NatPrf.add_zero(n),
                              Equal.sym(Nat, Nat.add(n, 0n), n,
                                NatProof.NatPrf.add_zero(n))),
                            {==}, {==}, {==}, hs_hi)
                +es_run_hi : {s_run == s_hi : Array<Nat>} =
                  Equal.trans(Array<Nat>, s_run, seen, s_hi, es_run,
                    Equal.sym(Array<Nat>, s_hi, seen, es_hi))
                +et_run_hi : {t_run == t_hi : Array<U32>} =
                  Equal.trans(Array<U32>, t_run, tbl, t_hi, et_run,
                    Equal.sym(Array<U32>, t_hi, tbl, et_hi))
                +hhr_run : FH.FH.HistSpec(g, ws, Nil{}, gen, n, False{}, t_hi,
                             SolveFast.hist5_go(row, S, gen, False{},
                               SolveFast.Hist5Ok{s_run, t_run, 0n, 0n, n})) =
                  %Equal.sym(Array<Nat>, s_run, s_hi, es_run_hi) :
                    FH.FH.HistSpec(g, ws, Nil{}, gen, n, False{}, t_hi,
                      SolveFast.hist5_go(row, S, gen, False{},
                        SolveFast.Hist5Ok{_, t_run, 0n, 0n, n}))
                  %Equal.sym(Array<U32>, t_run, t_hi, et_run_hi) :
                    FH.FH.HistSpec(g, ws, Nil{}, gen, n, False{}, t_hi,
                      SolveFast.hist5_go(row, S, gen, False{},
                        SolveFast.Hist5Ok{s_hi, _, 0n, 0n, n}))
                  hhr_hi
                GR.with_dup_arr(Nat,
                  GR.RSortSpec(G, C_root, n_root, ws,
                    GR.rev_words(rest, g <> seen_gs),
                    Greedy.rsort_fill(rest, U32.add(row, 1), S, n, base_lb,
                      Greedy.rsort_hist_one(row, g, n, base_lb, bkts, gen,
                        SolveFast.hist5_go(row, S, gen, False{},
                          SolveFast.Hist5Ok{seen, tbl, 0n, 0n, n})))),
                  s_run,
                  s_r1 => s_r2 => +es_r1 => +es_r2 =>
                  GR.with_dup_arr(U32,
                    GR.RSortSpec(G, C_root, n_root, ws,
                      GR.rev_words(rest, g <> seen_gs),
                      Greedy.rsort_fill(rest, U32.add(row, 1), S, n, base_lb,
                        Greedy.rsort_hist_one(row, g, n, base_lb, bkts, gen,
                          SolveFast.hist5_go(row, S, gen, False{},
                            SolveFast.Hist5Ok{seen, tbl, 0n, 0n, n})))),
                    t_run,
                    t_r1 => t_r2 => +et_r1 => +et_r2 =>
                    +es_r1_s : {s_r1 == seen : Array<Nat>} =
                      Equal.trans(Array<Nat>, s_r1, s_run, seen, es_r1, es_run)
                    +es_r2_s : {s_r2 == seen : Array<Nat>} =
                      Equal.trans(Array<Nat>, s_r2, s_run, seen, es_r2, es_run)
                    +et_r1_t : {t_r1 == tbl : Array<U32>} =
                      Equal.trans(Array<U32>, t_r1, t_run, tbl, et_r1, et_run)
                    +et_r2_t : {t_r2 == tbl : Array<U32>} =
                      Equal.trans(Array<U32>, t_r2, t_run, tbl, et_r2, et_run)
                    +hhr_r1 : FH.FH.HistSpec(g, ws, Nil{}, gen, n, False{},
                                t_hi,
                                SolveFast.hist5_go(row, S, gen, False{},
                                  SolveFast.Hist5Ok{s_r1, t_r1, 0n, 0n, n})) =
                      %Equal.sym(Array<Nat>, s_r1, s_run, es_r1) :
                        FH.FH.HistSpec(g, ws, Nil{}, gen, n, False{}, t_hi,
                          SolveFast.hist5_go(row, S, gen, False{},
                            SolveFast.Hist5Ok{_, t_r1, 0n, 0n, n}))
                      %Equal.sym(Array<U32>, t_r1, t_run, et_r1) :
                        FH.FH.HistSpec(g, ws, Nil{}, gen, n, False{}, t_hi,
                          SolveFast.hist5_go(row, S, gen, False{},
                            SolveFast.Hist5Ok{s_run, _, 0n, 0n, n}))
                      hhr_run
                    +hst_next = GR.rsort_hist_one_ok(G, C_root, n_root, ws,
                                  seen_gs, row, g, n, base_lb, b_step, t_hi,
                                  gen,
                                  SolveFast.hist5_go(row, S, gen, False{},
                                    SolveFast.Hist5Ok{s_r1, t_r1, 0n, 0n, n}),
                                  hge1, en, hrow, hwg, ht_hi, hb_st, hhr_r1)
                    +hst_run : GR.RSortSpec(G, C_root, n_root, ws, g <> seen_gs,
                                 Greedy.rsort_hist_one(row, g, n, base_lb,
                                   b_run, gen,
                                   SolveFast.hist5_go(row, S, gen, False{},
                                     SolveFast.Hist5Ok{s_r2, t_r2, 0n, 0n, n}))) =
                      %Equal.trans(Array<+List<SolveFast.CWord>>, b_step, bkts,
                         b_run, eb_step,
                         Equal.sym(Array<+List<SolveFast.CWord>>, b_run, bkts,
                           eb_run)) :
                        GR.RSortSpec(G, C_root, n_root, ws, g <> seen_gs,
                          Greedy.rsort_hist_one(row, g, n, base_lb, _, gen,
                            SolveFast.hist5_go(row, S, gen, False{},
                              SolveFast.Hist5Ok{s_r2, t_r2, 0n, 0n, n})))
                      %Equal.trans(Array<Nat>, s_r1, seen, s_r2, es_r1_s,
                         Equal.sym(Array<Nat>, s_r2, seen, es_r2_s)) :
                        GR.RSortSpec(G, C_root, n_root, ws, g <> seen_gs,
                          Greedy.rsort_hist_one(row, g, n, base_lb, b_step, gen,
                            SolveFast.hist5_go(row, S, gen, False{},
                              SolveFast.Hist5Ok{_, t_r2, 0n, 0n, n})))
                      %Equal.trans(Array<U32>, t_r1, tbl, t_r2, et_r1_t,
                         Equal.sym(Array<U32>, t_r2, tbl, et_r2_t)) :
                        GR.RSortSpec(G, C_root, n_root, ws, g <> seen_gs,
                          Greedy.rsort_hist_one(row, g, n, base_lb, b_step, gen,
                            SolveFast.hist5_go(row, S, gen, False{},
                              SolveFast.Hist5Ok{s_r1, _, 0n, 0n, n})))
                      hst_next
                    +hres = GR.rsort_fill_ok(rest, U32.add(row, 1), G, C_root,
                              n_root, S, n, base_lb, g <> seen_gs,
                              Greedy.rsort_hist_one(row, g, n, base_lb, b_run,
                                gen,
                                SolveFast.hist5_go(row, S, gen, False{},
                                  SolveFast.Hist5Ok{s_r2, t_r2, 0n, 0n, n})),
                              hrws_r, hai_r, hge1, en, hS, hst_run)
                    %es_r2_s :
                      GR.RSortSpec(G, C_root, n_root, ws,
                        GR.rev_words(rest, g <> seen_gs),
                        Greedy.rsort_fill(rest, U32.add(row, 1), S, n, base_lb,
                          Greedy.rsort_hist_one(row, g, n, base_lb, bkts, gen,
                            SolveFast.hist5_go(row, S, gen, False{},
                              SolveFast.Hist5Ok{_, tbl, 0n, 0n, n}))))
                    %et_r2_t :
                      GR.RSortSpec(G, C_root, n_root, ws,
                        GR.rev_words(rest, g <> seen_gs),
                        Greedy.rsort_fill(rest, U32.add(row, 1), S, n, base_lb,
                          Greedy.rsort_hist_one(row, g, n, base_lb, bkts, gen,
                            SolveFast.hist5_go(row, S, gen, False{},
                              SolveFast.Hist5Ok{s_r2, _, 0n, 0n, n}))))
                    %eb_run :
                      GR.RSortSpec(G, C_root, n_root, ws,
                        GR.rev_words(rest, g <> seen_gs),
                        Greedy.rsort_fill(rest, U32.add(row, 1), S, n, base_lb,
                          Greedy.rsort_hist_one(row, g, n, base_lb, _, gen,
                            SolveFast.hist5_go(row, S, gen, False{},
                              SolveFast.Hist5Ok{s_r2, t_r2, 0n, 0n, n}))))
                    hres)))))

# ---------------------------------------------------------------------------
# Section 4: `seed_top_go` and `root_prepare_spec`
# ---------------------------------------------------------------------------

def GR.elt_ok(+limit: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +r: SolveRef.Best) -> Bool:
  Bool.and(FVal.FV.best_ok_b(limit, G, S, r),
    Nat.is_le(Eval.Eval.cost_of(r), limit))

def GR.seed_step_spec(+inf: Nat, +G: +List<+List<Nat>>,
    +C_root: +List<+List<Nat>>, +n_root: Nat, +S: +List<+List<Nat>>,
    sr: SolveFast.StepRes) -> Data:
  match sr:
    case SolveFast.StepRes{best, buf}:
      Arr.Arr.DPair<
        {GR.elt_ok(inf, G, S, best) == True{} : Bool},
        FH.FH.BufOk(G, C_root, n_root, True{}, True{}, buf)>

def GR.seed_update_ok(+inf: Nat, +G: +List<+List<Nat>>,
    +C_root: +List<+List<Nat>>, +n_root: Nat, +S: +List<+List<Nat>>,
    +best: SolveRef.Best, gr: Greedy.GreedyRes,
    +hbest: {GR.elt_ok(inf, G, S, best) == True{} : Bool},
    +hgr: GR.GreedySpec(G, C_root, n_root, S, gr)) ->
  GR.seed_step_spec(inf, G, C_root, n_root, S, Greedy.seed_update(best, gr)):
  match gr:
    case Greedy.GreedyFail{buf2}:
      Arr.DPair{hbest, hgr}
    case Greedy.GreedyOk{+tree, +cost, buf2}:
      +hvc = Arr.Arr.dpair_l(
               {Bool.and(FVal.FV.valid_b(tree, G, S),
                  Nat.is_le(Tree.cost(tree, S), cost)) == True{} : Bool},
               FH.FH.BufOk(G, C_root, n_root, True{}, True{}, buf2), hgr)
      +hbuf2 = Arr.Arr.dpair_r(
                 {Bool.and(FVal.FV.valid_b(tree, G, S),
                    Nat.is_le(Tree.cost(tree, S), cost)) == True{} : Bool},
                 FH.FH.BufOk(G, C_root, n_root, True{}, True{}, buf2), hgr)
      +hv = Logic.Proof.and_true_l(FVal.FV.valid_b(tree, G, S),
              Nat.is_le(Tree.cost(tree, S), cost), hvc)
      +hc = Logic.Proof.and_true_r(FVal.FV.valid_b(tree, G, S),
              Nat.is_le(Tree.cost(tree, S), cost), hvc)
      +hokb = Logic.Proof.and_true_l(FVal.FV.best_ok_b(inf, G, S, best),
                Nat.is_le(Eval.Eval.cost_of(best), inf), hbest)
      +hleb = Logic.Proof.and_true_r(FVal.FV.best_ok_b(inf, G, S, best),
                Nat.is_le(Eval.Eval.cost_of(best), inf), hbest)
      +hok2 = FVal.FV.best_ok_better(inf, G, S, cost, tree, best, hv, hc, hokb)
      +hle2 = NatProof.Nat.is_le_trans(
                Eval.Eval.cost_of(SolveRef.better(cost, tree, best)),
                Eval.Eval.cost_of(best), inf,
                Fold.OQ.better_le_best(cost, tree, best), hleb)
      Arr.DPair{
        FO.FO.bool_and_intro(
          FVal.FV.best_ok_b(inf, G, S, SolveRef.better(cost, tree, best)),
          Nat.is_le(Eval.Eval.cost_of(SolveRef.better(cost, tree, best)), inf),
          hok2, hle2),
        hbuf2}

def GR.seed_top_go_ok(+rem: Nat, +rgs: +List<Greedy.RootGuess>,
    +p: Nat, +inf: Nat, +G: +List<+List<Nat>>, +C_root: +List<+List<Nat>>,
    +n_root: Nat, +gG: SolveFast.GList, +cs: +List<SolveFast.CWord>,
    +n: Nat, st: SolveFast.StepRes,
    +hgG: {GR.glist_ok_b(G, n_root, gG) == True{} : Bool},
    +en: {n == Groups.len_words(SolveFast.cwords_words(cs)) : Nat},
    +enp: {n == 1n+p : Nat},
    +hcs: {FT.FT.cwords_ok_b(G, C_root, n_root, cs) == True{} : Bool},
    +hai: {FO.FO.all_in_ref(SolveFast.cwords_words(cs), G) == True{} : Bool},
    +hnd: {FN.FN.no_dup_ref(SolveFast.cwords_words(cs)) == True{} : Bool},
    +hrgs: {GR.rgs_ok_b(True{}, G, n_root, rgs) == True{} : Bool},
    +hrus: {GR.rgs_usable_b(SolveFast.cwords_words(cs), rgs) == True{} : Bool},
    +hst: GR.seed_step_spec(inf, G, C_root, n_root, SolveFast.cwords_words(cs),
            st)) ->
  GR.seed_step_spec(inf, G, C_root, n_root, SolveFast.cwords_words(cs),
    Greedy.seed_top_go(rem, rgs, gG, cs, n, st)):
  match rem:
    case 0n:
      hst
    case 1n+q:
      match rgs:
        case Nil{}:
          hst
        case Con{+rg, +rest}:
          match rg:
            case Greedy.RootGuess{+row, +g}:
              match st:
                case SolveFast.StepRes{+best, buf}:
                  +ws = SolveFast.cwords_words(cs)
                  +hbest = Arr.Arr.dpair_l(
                             {GR.elt_ok(inf, G, ws, best) == True{} : Bool},
                             FH.FH.BufOk(G, C_root, n_root, True{}, True{}, buf),
                             hst)
                  +hbuf = Arr.Arr.dpair_r(
                            {GR.elt_ok(inf, G, ws, best) == True{} : Bool},
                            FH.FH.BufOk(G, C_root, n_root, True{}, True{}, buf),
                            hst)
                  +hrg = Logic.Proof.and_true_l(
                           Bool.and(FT.FT.gentry_ok_b(G, n_root, row, g),
                             Tree.member_word(g, G)),
                           GR.rgs_ok_b(True{}, G, n_root, rest), hrgs)
                  +hrest_ok = Logic.Proof.and_true_r(
                                Bool.and(FT.FT.gentry_ok_b(G, n_root, row, g),
                                  Tree.member_word(g, G)),
                                GR.rgs_ok_b(True{}, G, n_root, rest), hrgs)
                  +hrow = Logic.Proof.and_true_l(
                            FT.FT.gentry_ok_b(G, n_root, row, g),
                            Tree.member_word(g, G), hrg)
                  +hwg = Logic.Proof.and_true_r(
                           FT.FT.gentry_ok_b(G, n_root, row, g),
                           Tree.member_word(g, G), hrg)
                  +hus = Logic.Proof.and_true_l(
                           Groups.groups_smaller(ws, Groups.groups_build(g, ws, Nil{})),
                           GR.rgs_usable_b(ws, rest), hrus)
                  +hrest_us = Logic.Proof.and_true_r(
                                Groups.groups_smaller(ws,
                                  Groups.groups_build(g, ws, Nil{})),
                                GR.rgs_usable_b(ws, rest), hrus)
                  +ele : {Nat.is_le(Groups.len_words(ws), 1n+p) == True{} : Bool} =
                    Fold.OQ.le_cong_l(Groups.len_words(ws), 1n+p, 1n+p,
                      Equal.trans(Nat, Groups.len_words(ws), n, 1n+p,
                        Equal.sym(Nat, n, Groups.len_words(ws), en), enp),
                      NatProof.Nat.is_le_refl(1n+p))
                  GR.with_dup_buf(
                    GR.seed_step_spec(inf, G, C_root, n_root, ws,
                      Greedy.seed_top_go(q, rest, gG, cs, n,
                        Greedy.seed_update(best,
                          Greedy.greedy_step(n, 1n, Nil{}, gG, cs, n, Nil{},
                            Nil{}, 0n, Greedy.GreedyFail{SolveFast.NoBuf{}},
                            Greedy.greedy_expand_forced(row, g, cs, n, buf))))),
                    buf,
                    b1 => br1 => +eb1 => +ebr1 =>
                    GR.with_dup_buf(
                      GR.seed_step_spec(inf, G, C_root, n_root, ws,
                        Greedy.seed_top_go(q, rest, gG, cs, n,
                          Greedy.seed_update(best,
                            Greedy.greedy_step(n, 1n, Nil{}, gG, cs, n, Nil{},
                              Nil{}, 0n, Greedy.GreedyFail{SolveFast.NoBuf{}},
                              Greedy.greedy_expand_forced(row, g, cs, n, buf))))),
                      br1,
                      b2 => br2 => +eb2r => +ebr2r =>
                      GR.with_dup_buf(
                        GR.seed_step_spec(inf, G, C_root, n_root, ws,
                          Greedy.seed_top_go(q, rest, gG, cs, n,
                            Greedy.seed_update(best,
                              Greedy.greedy_step(n, 1n, Nil{}, gG, cs, n, Nil{},
                                Nil{}, 0n, Greedy.GreedyFail{SolveFast.NoBuf{}},
                                Greedy.greedy_expand_forced(row, g, cs, n,
                                  buf))))),
                        br2,
                        b3 => b4 => +eb3r => +eb4r =>
                        +eb2 : {b2 == buf : SolveFast.Buf5} =
                          Equal.trans(SolveFast.Buf5, b2, br1, buf, eb2r, ebr1)
                        +ebr2 : {br2 == buf : SolveFast.Buf5} =
                          Equal.trans(SolveFast.Buf5, br2, br1, buf, ebr2r, ebr1)
                        +eb3 : {b3 == buf : SolveFast.Buf5} =
                          Equal.trans(SolveFast.Buf5, b3, br2, buf, eb3r, ebr2)
                        +eb4 : {b4 == buf : SolveFast.Buf5} =
                          Equal.trans(SolveFast.Buf5, b4, br2, buf, eb4r, ebr2)
                        +hbuf1 = FH.FH.buf_ok_transport(G, C_root, n_root,
                                   True{}, True{}, buf, b1,
                                   Equal.sym(SolveFast.Buf5, b1, buf, eb1), hbuf)
                        +hexp1 = GR.greedy_expand_forced_spec(G, C_root, n_root,
                                   row, g, cs, n, b1, hrow, hwg, hcs, hus, hnd,
                                   hbuf1)
                        +eb12 : {b1 == b2 : SolveFast.Buf5} =
                          Equal.trans(SolveFast.Buf5, b1, buf, b2, eb1,
                            Equal.sym(SolveFast.Buf5, b2, buf, eb2))
                        +hexp2 : GR.ExpSpec(G, C_root, n_root, ws, n,
                                   Greedy.greedy_expand_forced(row, g, cs, n,
                                     b2)) =
                          %eb12 : GR.ExpSpec(G, C_root, n_root, ws, n,
                                    Greedy.greedy_expand_forced(row, g, cs, n,
                                      _))
                          hexp1
                        +hgr_p = GR.greedy_phase1_ok(p, G, C_root, n_root, gG,
                                   cs, ws, n,
                                   Greedy.greedy_expand_forced(row, g, cs, n,
                                     b2),
                                   en, hai, hnd, hexp2,
                                   GR.gjobs_ok(p, G, C_root, n_root, gG,
                                     MV.MV.next_guess(G, ws), hgG,
                                     FO.FO.all_in_next_guess(G, ws, G, hai),
                                     FN.FN.nodup_ok_next_guess(True{}, G, ws,
                                       hnd)))
                        +eb23 : {b2 == b3 : SolveFast.Buf5} =
                          Equal.trans(SolveFast.Buf5, b2, buf, b3, eb2,
                            Equal.sym(SolveFast.Buf5, b3, buf, eb3))
                        +hgr_n : GR.GreedySpec(G, C_root, n_root, ws,
                                   Greedy.greedy_step(n, 1n, Nil{}, gG, cs, n,
                                     Nil{}, Nil{}, 0n,
                                     Greedy.GreedyFail{SolveFast.NoBuf{}},
                                     Greedy.greedy_expand_forced(row, g, cs, n,
                                       b3))) =
                          %Equal.sym(Nat, n, 1n+p, enp) :
                            GR.GreedySpec(G, C_root, n_root, ws,
                              Greedy.greedy_step(_, 1n, Nil{}, gG, cs, n, Nil{},
                                Nil{}, 0n, Greedy.GreedyFail{SolveFast.NoBuf{}},
                                Greedy.greedy_expand_forced(row, g, cs, n, b3)))
                          %eb23 :
                            GR.GreedySpec(G, C_root, n_root, ws,
                              Greedy.greedy_step(1n+p, 1n, Nil{}, gG, cs, n,
                                Nil{}, Nil{}, 0n,
                                Greedy.GreedyFail{SolveFast.NoBuf{}},
                                Greedy.greedy_expand_forced(row, g, cs, n, _)))
                          hgr_p
                        +hst3 = GR.seed_update_ok(inf, G, C_root, n_root, ws,
                                  best,
                                  Greedy.greedy_step(n, 1n, Nil{}, gG, cs, n,
                                    Nil{}, Nil{}, 0n,
                                    Greedy.GreedyFail{SolveFast.NoBuf{}},
                                    Greedy.greedy_expand_forced(row, g, cs, n,
                                      b3)), hbest, hgr_n)
                        +eb34 : {b3 == b4 : SolveFast.Buf5} =
                          Equal.trans(SolveFast.Buf5, b3, buf, b4, eb3,
                            Equal.sym(SolveFast.Buf5, b4, buf, eb4))
                        +hst4 : GR.seed_step_spec(inf, G, C_root, n_root, ws,
                                  Greedy.seed_update(best,
                                    Greedy.greedy_step(n, 1n, Nil{}, gG, cs, n,
                                      Nil{}, Nil{}, 0n,
                                      Greedy.GreedyFail{SolveFast.NoBuf{}},
                                      Greedy.greedy_expand_forced(row, g, cs, n,
                                        b4)))) =
                          %eb34 :
                            GR.seed_step_spec(inf, G, C_root, n_root, ws,
                              Greedy.seed_update(best,
                                Greedy.greedy_step(n, 1n, Nil{}, gG, cs, n,
                                  Nil{}, Nil{}, 0n,
                                  Greedy.GreedyFail{SolveFast.NoBuf{}},
                                  Greedy.greedy_expand_forced(row, g, cs, n,
                                    _))))
                          hst3
                        %eb4 :
                          GR.seed_step_spec(inf, G, C_root, n_root, ws,
                            Greedy.seed_top_go(q, rest, gG, cs, n,
                              Greedy.seed_update(best,
                                Greedy.greedy_step(n, 1n, Nil{}, gG, cs, n,
                                  Nil{}, Nil{}, 0n,
                                  Greedy.GreedyFail{SolveFast.NoBuf{}},
                                  Greedy.greedy_expand_forced(row, g, cs, n,
                                    _)))))
                        GR.seed_top_go_ok(q, rest, p, inf, G, C_root, n_root,
                          gG, cs, n,
                          Greedy.seed_update(best,
                            Greedy.greedy_step(n, 1n, Nil{}, gG, cs, n, Nil{},
                              Nil{}, 0n, Greedy.GreedyFail{SolveFast.NoBuf{}},
                              Greedy.greedy_expand_forced(row, g, cs, n, b4))),
                          hgG, en, enp, hcs, hai, hnd, hrest_ok, hrest_us,
                          hst4))))


# Final specification of `Greedy.root_prepare`.
def GR.RootPrepSpec(+inf: Nat, +G: +List<+List<Nat>>, +cs: +List<+List<Nat>>,
    +has_buf: Bool, +nd: Bool, pr: Greedy.RootPrepRes) -> Data:
  match pr:
    case Greedy.RootPrepRes{b0, rgs, buf2}:
      Arr.Arr.DPair<
        {GR.elt_ok(inf, G, cs, b0) == True{} : Bool},
        Arr.Arr.DPair<
          {GR.rgs_ok_b(has_buf, G, Groups.len_words(cs), rgs) == True{} : Bool},
          Arr.Arr.DPair<
            FH.FH.BufOk(G, cs, Groups.len_words(cs), has_buf, nd, buf2),
            {GR.all_usable_in(cs, G, GR.rgs_words(rgs)) == True{} : Bool}>>>

def GR.finish_seed_spec(+inf: Nat, +G: +List<+List<Nat>>,
    +cs: +List<+List<Nat>>, +rgs: +List<Greedy.RootGuess>,
    sr: SolveFast.StepRes,
    +hrgs: {GR.rgs_ok_b(True{}, G, Groups.len_words(cs), rgs) == True{} : Bool},
    +hcov: {GR.all_usable_in(cs, G, GR.rgs_words(rgs)) == True{} : Bool},
    +hsr: GR.seed_step_spec(inf, G, cs, Groups.len_words(cs), cs, sr)) ->
  GR.RootPrepSpec(inf, G, cs, True{}, True{}, Greedy.finish_seed(rgs, sr)):
  match sr:
    case SolveFast.StepRes{+b0, buf2}:
      +hb0 = Arr.Arr.dpair_l({GR.elt_ok(inf, G, cs, b0) == True{} : Bool},
               FH.FH.BufOk(G, cs, Groups.len_words(cs), True{}, True{}, buf2),
               hsr)
      +hbuf2 = Arr.Arr.dpair_r({GR.elt_ok(inf, G, cs, b0) == True{} : Bool},
                 FH.FH.BufOk(G, cs, Groups.len_words(cs), True{}, True{}, buf2),
                 hsr)
      Arr.DPair{hb0, Arr.DPair{hrgs, Arr.DPair{hbuf2, hcov}}}

def GR.finish_rsort_go(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +gG: SolveFast.GList, +cwS: +List<SolveFast.CWord>, +cs: +List<+List<Nat>>,
    +rgs: +List<Greedy.RootGuess>, seen: Array<Nat>,
    bkts_orig: Array<+List<SolveFast.CWord>>, tbl: Array<U32>, +gen: Nat,
    +en: {Groups.len_words(cs) == 1n+p : Nat},
    +ecwS: {SolveFast.cwords_words(cwS) == cs : +List<+List<Nat>>},
    +hcwS: {FT.FT.cwords_ok_b(G, cs, Groups.len_words(cs), cwS)
            == True{} : Bool},
    +hgG: {GR.glist_ok_b(G, Groups.len_words(cs), gG) == True{} : Bool},
    +hai: {FO.FO.all_in_ref(cs, G) == True{} : Bool},
    +hnd: {FN.FN.no_dup_ref(cs) == True{} : Bool},
    +hs: FH.FH.SeenTree(10n, 0, seen, gen, Nil{}),
    +hb_orig: FH.FH.BktTree(G, cs, Groups.len_words(cs), 10n, 0, bkts_orig,
                Nil{}),
    +ht: FT.FT.TblOk(G, cs, Groups.len_words(cs), tbl),
    +hrgs_ok0: {GR.rgs_ok_b(True{}, G, Groups.len_words(cs), rgs)
                == True{} : Bool},
    +hrgs_us0: {GR.rgs_usable_b(cs, rgs) == True{} : Bool},
    +hall_rev0: {GR.all_usable_in(cs, GR.rev_words(G, Nil{}),
                   GR.rgs_words(rgs)) == True{} : Bool}) ->
  GR.RootPrepSpec(inf, G, cs, True{}, True{},
    Greedy.finish_seed(rgs,
      Greedy.seed_top_go(5n, rgs, gG, cwS, Groups.len_words(cs),
        SolveFast.StepRes{SolveFast.dummy_inf(inf),
          SolveFast.Buf5{seen, bkts_orig, tbl, gen}}))):
  +n = Groups.len_words(cs)
  +hcov = Logic.Proof.and_true_l(
            GR.all_usable_in(cs, G, GR.rgs_words(rgs)), True{},
            GR.all_usable_in_rev_split(cs, G, Nil{}, GR.rgs_words(rgs),
              hall_rev0))
  +hb0 : {GR.elt_ok(inf, G, cs, SolveFast.dummy_inf(inf)) == True{} : Bool} =
    FO.FO.bool_and_intro(
      FVal.FV.best_ok_b(inf, G, cs, SolveFast.dummy_inf(inf)),
      Nat.is_le(Eval.Eval.cost_of(SolveFast.dummy_inf(inf)), inf),
      FVal.FV.best_ok_init(inf, G, cs, SolveFast.dummy_inf(inf),
        Nat.ge_refl(inf)),
      NatProof.Nat.is_le_refl(inf))
  +hbuf_s : FH.FH.BufOk(G, cs, n, True{}, True{},
              SolveFast.Buf5{seen, bkts_orig, tbl, gen}) =
    Arr.DPair{{==}, Arr.DPair{hs, Arr.DPair{hb_orig, ht}}}
  +ecwS_s = Equal.sym(+List<+List<Nat>>, SolveFast.cwords_words(cwS), cs,
              ecwS)
  +en_cw : {n == Groups.len_words(SolveFast.cwords_words(cwS)) : Nat} =
    Equal.cong(+List<+List<Nat>>, Nat, l => Groups.len_words(l), cs,
      SolveFast.cwords_words(cwS), ecwS_s)
  +hai_cw : {FO.FO.all_in_ref(SolveFast.cwords_words(cwS), G)
             == True{} : Bool} =
    Equal.trans(Bool, FO.FO.all_in_ref(SolveFast.cwords_words(cwS), G),
      FO.FO.all_in_ref(cs, G), True{},
      Equal.cong(+List<+List<Nat>>, Bool, l => FO.FO.all_in_ref(l, G),
        SolveFast.cwords_words(cwS), cs, ecwS), hai)
  +hnd_cw : {FN.FN.no_dup_ref(SolveFast.cwords_words(cwS))
             == True{} : Bool} =
    Equal.trans(Bool, FN.FN.no_dup_ref(SolveFast.cwords_words(cwS)),
      FN.FN.no_dup_ref(cs), True{},
      Equal.cong(+List<+List<Nat>>, Bool, l => FN.FN.no_dup_ref(l),
        SolveFast.cwords_words(cwS), cs, ecwS), hnd)
  +hrgs_us_cw : {GR.rgs_usable_b(SolveFast.cwords_words(cwS), rgs)
                 == True{} : Bool} =
    Equal.trans(Bool, GR.rgs_usable_b(SolveFast.cwords_words(cwS), rgs),
      GR.rgs_usable_b(cs, rgs), True{},
      Equal.cong(+List<+List<Nat>>, Bool, l => GR.rgs_usable_b(l, rgs),
        SolveFast.cwords_words(cwS), cs, ecwS), hrgs_us0)
  GR.with_dup_buf(
    GR.RootPrepSpec(inf, G, cs, True{}, True{},
      Greedy.finish_seed(rgs,
        Greedy.seed_top_go(5n, rgs, gG, cwS, n,
          SolveFast.StepRes{SolveFast.dummy_inf(inf),
            SolveFast.Buf5{seen, bkts_orig, tbl, gen}}))),
    SolveFast.Buf5{seen, bkts_orig, tbl, gen},
    b1 => b2 => +eb1 => +eb2 =>
    +hbuf1 = FH.FH.buf_ok_transport(G, cs, n, True{}, True{},
               SolveFast.Buf5{seen, bkts_orig, tbl, gen}, b1,
               Equal.sym(SolveFast.Buf5, b1,
                 SolveFast.Buf5{seen, bkts_orig, tbl, gen}, eb1), hbuf_s)
    +hst0_cw : GR.seed_step_spec(inf, G, cs, n, SolveFast.cwords_words(cwS),
                 SolveFast.StepRes{SolveFast.dummy_inf(inf), b1}) =
      %ecwS_s : GR.seed_step_spec(inf, G, cs, n, _,
                  SolveFast.StepRes{SolveFast.dummy_inf(inf), b1})
      Arr.DPair{hb0, hbuf1}
    +hseed_cw = GR.seed_top_go_ok(5n, rgs, p, inf, G, cs, n, gG, cwS, n,
                  SolveFast.StepRes{SolveFast.dummy_inf(inf), b1},
                  hgG, en_cw, en, hcwS, hai_cw, hnd_cw, hrgs_ok0,
                  hrgs_us_cw, hst0_cw)
    +eb12 : {b1 == b2 : SolveFast.Buf5} =
      Equal.trans(SolveFast.Buf5, b1,
        SolveFast.Buf5{seen, bkts_orig, tbl, gen}, b2, eb1,
        Equal.sym(SolveFast.Buf5, b2,
          SolveFast.Buf5{seen, bkts_orig, tbl, gen}, eb2))
    +hseed : GR.seed_step_spec(inf, G, cs, n, cs,
               Greedy.seed_top_go(5n, rgs, gG, cwS, n,
                 SolveFast.StepRes{SolveFast.dummy_inf(inf), b2})) =
      %ecwS : GR.seed_step_spec(inf, G, cs, n, _,
                Greedy.seed_top_go(5n, rgs, gG, cwS, n,
                  SolveFast.StepRes{SolveFast.dummy_inf(inf), b2}))
      %eb12 : GR.seed_step_spec(inf, G, cs, n, SolveFast.cwords_words(cwS),
                Greedy.seed_top_go(5n, rgs, gG, cwS, n,
                  SolveFast.StepRes{SolveFast.dummy_inf(inf), _}))
      hseed_cw
    %eb2 : GR.RootPrepSpec(inf, G, cs, True{}, True{},
             Greedy.finish_seed(rgs,
               Greedy.seed_top_go(5n, rgs, gG, cwS, n,
                 SolveFast.StepRes{SolveFast.dummy_inf(inf), _})))
    GR.finish_seed_spec(inf, G, cs, rgs,
      Greedy.seed_top_go(5n, rgs, gG, cwS, n,
        SolveFast.StepRes{SolveFast.dummy_inf(inf), b2}),
      hrgs_ok0, hcov, hseed))

def GR.finish_rsort_spec(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +gG: SolveFast.GList, +cwS: +List<SolveFast.CWord>, +cs: +List<+List<Nat>>,
    bkts_orig: Array<+List<SolveFast.CWord>>, st: Greedy.RSortSt,
    +en: {Groups.len_words(cs) == 1n+p : Nat},
    +ecwS: {SolveFast.cwords_words(cwS) == cs : +List<+List<Nat>>},
    +hcwS: {FT.FT.cwords_ok_b(G, cs, Groups.len_words(cs), cwS)
            == True{} : Bool},
    +hgG: {GR.glist_ok_b(G, Groups.len_words(cs), gG) == True{} : Bool},
    +hai: {FO.FO.all_in_ref(cs, G) == True{} : Bool},
    +hnd: {FN.FN.no_dup_ref(cs) == True{} : Bool},
    +hb_orig: FH.FH.BktTree(G, cs, Groups.len_words(cs), 10n, 0, bkts_orig,
                Nil{}),
    +hst: GR.RSortSpec(G, cs, Groups.len_words(cs), cs,
            GR.rev_words(G, Nil{}), st)) ->
  GR.RootPrepSpec(inf, G, cs, True{}, True{},
    Greedy.finish_rsort(gG, cwS, Groups.len_words(cs), inf, bkts_orig, st)):
  match st:
    case Greedy.RSortSt{seen, bkts_sort, tbl, +gen}:
      +n = Groups.len_words(cs)
      +hs = Arr.Arr.dpair_l(FH.FH.SeenTree(10n, 0, seen, gen, Nil{}),
              Arr.Arr.DPair<FT.FT.TblOk(G, cs, n, tbl),
                GR.RBktsInv(G, n, cs, GR.rev_words(G, Nil{}), bkts_sort)>, hst)
      +rr1 = Arr.Arr.dpair_r(FH.FH.SeenTree(10n, 0, seen, gen, Nil{}),
               Arr.Arr.DPair<FT.FT.TblOk(G, cs, n, tbl),
                 GR.RBktsInv(G, n, cs, GR.rev_words(G, Nil{}), bkts_sort)>, hst)
      +ht = Arr.Arr.dpair_l(FT.FT.TblOk(G, cs, n, tbl),
              GR.RBktsInv(G, n, cs, GR.rev_words(G, Nil{}), bkts_sort), rr1)
      +hinv = Arr.Arr.dpair_r(FT.FT.TblOk(G, cs, n, tbl),
                GR.RBktsInv(G, n, cs, GR.rev_words(G, Nil{}), bkts_sort), rr1)
      +hbok = Arr.Arr.dpair_l(GR.BktOk(10n, G, n, cs, bkts_sort),
                {GR.all_usable_in(cs, GR.rev_words(G, Nil{}),
                   GR.rgs_words(Greedy.rsort_drain_tree(bkts_sort, Nil{})))
                 == True{} : Bool}, hinv)
      +hall_rev0 = Arr.Arr.dpair_r(GR.BktOk(10n, G, n, cs, bkts_sort),
                     {GR.all_usable_in(cs, GR.rev_words(G, Nil{}),
                        GR.rgs_words(Greedy.rsort_drain_tree(bkts_sort, Nil{})))
                      == True{} : Bool}, hinv)
      GR.with_dup_arr(+List<SolveFast.CWord>,
        GR.RootPrepSpec(inf, G, cs, True{}, True{},
          Greedy.finish_seed(Greedy.rsort_drain_tree(bkts_sort, Nil{}),
            Greedy.seed_top_go(5n, Greedy.rsort_drain_tree(bkts_sort, Nil{}),
              gG, cwS, n,
              SolveFast.StepRes{SolveFast.dummy_inf(inf),
                SolveFast.Buf5{seen, bkts_orig, tbl, gen}}))),
        bkts_sort,
        bs1 => bs2 => +ebs1 => +ebs2 =>
        +hbok1 = GR.bkt_ok_transport(10n, G, n, cs, bkts_sort, bs1,
                   Equal.sym(Array<+List<SolveFast.CWord>>, bs1, bkts_sort,
                     ebs1), hbok)
        +hdr1 = GR.drain_tree_ok(10n, G, n, cs, bs1, Nil{}, hbok1, {==}, {==})
        +ebs12 : {bs1 == bs2 : Array<+List<SolveFast.CWord>>} =
          Equal.trans(Array<+List<SolveFast.CWord>>, bs1, bkts_sort, bs2, ebs1,
            Equal.sym(Array<+List<SolveFast.CWord>>, bs2, bkts_sort, ebs2))
        +hdr2 : GR.DrainOk(G, n, cs, Greedy.rsort_drain_tree(bs2, Nil{})) =
          %ebs12 : GR.DrainOk(G, n, cs, Greedy.rsort_drain_tree(_, Nil{}))
          hdr1
        +hrgs_ok2 = Arr.Arr.dpair_l(
                      {GR.rgs_ok_b(True{}, G, n,
                         Greedy.rsort_drain_tree(bs2, Nil{}))
                       == True{} : Bool},
                      {GR.rgs_usable_b(cs, Greedy.rsort_drain_tree(bs2, Nil{}))
                       == True{} : Bool}, hdr2)
        +hrgs_us2 = Arr.Arr.dpair_r(
                      {GR.rgs_ok_b(True{}, G, n,
                         Greedy.rsort_drain_tree(bs2, Nil{}))
                       == True{} : Bool},
                      {GR.rgs_usable_b(cs, Greedy.rsort_drain_tree(bs2, Nil{}))
                       == True{} : Bool}, hdr2)
        +hall_rev2 : {GR.all_usable_in(cs, GR.rev_words(G, Nil{}),
                        GR.rgs_words(Greedy.rsort_drain_tree(bs2, Nil{})))
                      == True{} : Bool} =
          %Equal.sym(Array<+List<SolveFast.CWord>>, bs2, bkts_sort, ebs2) :
            {GR.all_usable_in(cs, GR.rev_words(G, Nil{}),
               GR.rgs_words(Greedy.rsort_drain_tree(_, Nil{})))
             == True{} : Bool}
          hall_rev0
        +er : {Greedy.rsort_drain_tree(bs2, Nil{})
               == Greedy.rsort_drain_tree(bkts_sort, Nil{})
               : +List<Greedy.RootGuess>} =
          Equal.cong(Array<+List<SolveFast.CWord>>, +List<Greedy.RootGuess>,
            x => Greedy.rsort_drain_tree(x, Nil{}), bs2, bkts_sort, ebs2)
        %er :
          GR.RootPrepSpec(inf, G, cs, True{}, True{},
            Greedy.finish_seed(_,
              Greedy.seed_top_go(5n, _, gG, cwS, n,
                SolveFast.StepRes{SolveFast.dummy_inf(inf),
                  SolveFast.Buf5{seen, bkts_orig, tbl, gen}})))
        GR.finish_rsort_go(p, inf, G, gG, cwS, cs,
          Greedy.rsort_drain_tree(bs2, Nil{}),
          seen, bkts_orig, tbl, gen, en, ecwS, hcwS, hgG, hai, hnd, hs,
          hb_orig, ht, hrgs_ok2, hrgs_us2, hall_rev2))

def GR.root_prepare_spec(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +cs: +List<+List<Nat>>, +nd: Bool, +has_buf: Bool,
    +gG: SolveFast.GList, +cwS: +List<SolveFast.CWord>,
    buf: SolveFast.Buf5,
    +en: {Groups.len_words(cs) == 1n+p : Nat},
    +egG: {gG == SolveFast.glist_of_guesses(G, 0, 1) : SolveFast.GList},
    +ecwS: {SolveFast.cwords_words(cwS) == cs : +List<+List<Nat>>},
    +hcwS: {FH.FH.cwords_ok_if(has_buf, G, cs, Groups.len_words(cs), cwS)
            == True{} : Bool},
    +hai: {FO.FO.all_in_ref(cs, G) == True{} : Bool},
    +hnd: {FN.FN.nodup_ok(nd, cs) == True{} : Bool},
    +hbuf: FH.FH.BufOk(G, cs, Groups.len_words(cs), has_buf, nd, buf)) ->
  GR.RootPrepSpec(inf, G, cs, has_buf, nd,
    Greedy.root_prepare(G, gG, cwS, Groups.len_words(cs), inf, buf)):
  match has_buf:
    case False{}:
      match buf:
        case SolveFast.NoBuf{}:
          +n = Groups.len_words(cs)
          +hb0 : {GR.elt_ok(inf, G, cs, SolveFast.dummy_inf(inf))
                  == True{} : Bool} =
            FO.FO.bool_and_intro(
              FVal.FV.best_ok_b(inf, G, cs, SolveFast.dummy_inf(inf)),
              Nat.is_le(Eval.Eval.cost_of(SolveFast.dummy_inf(inf)), inf),
              FVal.FV.best_ok_init(inf, G, cs, SolveFast.dummy_inf(inf),
                Nat.ge_refl(inf)),
              NatProof.Nat.is_le_refl(inf))
          +hrgs = GR.rgs_of_G_ok_go(G, G, n, 0, GR.all_in_refl(G))
          +ew = GR.rgs_of_G_words(G, 0)
          +hcov : {GR.all_usable_in(cs, G,
                     GR.rgs_words(Greedy.rgs_of_G(G, 0))) == True{} : Bool} =
            Equal.trans(Bool,
              GR.all_usable_in(cs, G, GR.rgs_words(Greedy.rgs_of_G(G, 0))),
              GR.all_usable_in(cs, G, G), True{},
              Equal.cong(+List<+List<Nat>>, Bool,
                l => GR.all_usable_in(cs, G, l),
                GR.rgs_words(Greedy.rgs_of_G(G, 0)), G, ew),
              GR.all_usable_in_of_all_in(cs, G, G, GR.all_in_refl(G)))
          Arr.DPair{hb0, Arr.DPair{hrgs, Arr.DPair{Unit{}, hcov}}}
        case SolveFast.Buf5{s, bk, tb, gn}:
          Empty.absurd(
            GR.RootPrepSpec(inf, G, cs, False{}, nd,
              Greedy.root_prepare(G, gG, cwS, Groups.len_words(cs), inf,
                SolveFast.Buf5{s, bk, tb, gn})),
            hbuf)
    case True{}:
      match buf:
        case SolveFast.NoBuf{}:
          Empty.absurd(
            GR.RootPrepSpec(inf, G, cs, True{}, nd,
              Greedy.root_prepare(G, gG, cwS, Groups.len_words(cs), inf,
                SolveFast.NoBuf{})), hbuf)
        case SolveFast.Buf5{seen, bkts, tbl, +gen}:
          +n = Groups.len_words(cs)
          +end_t = Arr.Arr.dpair_l({nd == True{} : Bool},
                     Arr.Arr.DPair<FH.FH.SeenTree(10n, 0, seen, gen, Nil{}),
                       Arr.Arr.DPair<
                         FH.FH.BktTree(G, cs, n, 10n, 0, bkts, Nil{}),
                         FT.FT.TblOk(G, cs, n, tbl)>>, hbuf)
          +r1 = Arr.Arr.dpair_r({nd == True{} : Bool},
                  Arr.Arr.DPair<FH.FH.SeenTree(10n, 0, seen, gen, Nil{}),
                    Arr.Arr.DPair<
                      FH.FH.BktTree(G, cs, n, 10n, 0, bkts, Nil{}),
                      FT.FT.TblOk(G, cs, n, tbl)>>, hbuf)
          +hs = Arr.Arr.dpair_l(FH.FH.SeenTree(10n, 0, seen, gen, Nil{}),
                  Arr.Arr.DPair<FH.FH.BktTree(G, cs, n, 10n, 0, bkts, Nil{}),
                    FT.FT.TblOk(G, cs, n, tbl)>, r1)
          +r2 = Arr.Arr.dpair_r(FH.FH.SeenTree(10n, 0, seen, gen, Nil{}),
                  Arr.Arr.DPair<FH.FH.BktTree(G, cs, n, 10n, 0, bkts, Nil{}),
                    FT.FT.TblOk(G, cs, n, tbl)>, r1)
          +hb = Arr.Arr.dpair_l(FH.FH.BktTree(G, cs, n, 10n, 0, bkts, Nil{}),
                  FT.FT.TblOk(G, cs, n, tbl), r2)
          +ht = Arr.Arr.dpair_r(FH.FH.BktTree(G, cs, n, 10n, 0, bkts, Nil{}),
                  FT.FT.TblOk(G, cs, n, tbl), r2)
          +hnd_t : {FN.FN.no_dup_ref(cs) == True{} : Bool} =
            Equal.trans(Bool, FN.FN.no_dup_ref(cs), FN.FN.nodup_ok(nd, cs),
              True{},
              Equal.cong(Bool, Bool, b => FN.FN.nodup_ok(b, cs), True{}, nd,
                Equal.sym(Bool, nd, True{}, end_t)), hnd)
          +rwsG = FT.FT.guesses_to_rws(G, 0, 1)
          +hrwsG : {FT.FT.rws_ok_b(G, n, rwsG) == True{} : Bool} =
            FOpt.FOpt.guesses_to_rws_ok_if(True{}, G, n)
          +erwsG : {FT.FT.rws_words(rwsG) == G : +List<+List<Nat>>} =
            FT.FT.guesses_to_rws_words(G, 0, 1)
          +hai_rws : {FO.FO.all_in_ref(FT.FT.rws_words(rwsG), G)
                      == True{} : Bool} =
            Equal.trans(Bool, FO.FO.all_in_ref(FT.FT.rws_words(rwsG), G),
              FO.FO.all_in_ref(G, G), True{},
              Equal.cong(+List<+List<Nat>>, Bool, l => FO.FO.all_in_ref(l, G),
                FT.FT.rws_words(rwsG), G, erwsG), GR.all_in_refl(G))
          +hgG_rws = GR.glist_of_rws_ok(G, n, rwsG, SolveFast.GEnd{}, hrwsG,
                       hai_rws, {==})
          +hgG : {GR.glist_ok_b(G, n, gG) == True{} : Bool} =
            Equal.trans(Bool, GR.glist_ok_b(G, n, gG),
              GR.glist_ok_b(G, n, FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{})),
              True{},
              Equal.cong(SolveFast.GList, Bool, gl => GR.glist_ok_b(G, n, gl),
                gG, FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}),
                Equal.trans(SolveFast.GList, gG,
                  SolveFast.glist_of_guesses(G, 0, 1),
                  FT.FT.glist_of_rws(rwsG, SolveFast.GEnd{}), egG,
                  FT.FT.glist_of_guesses_eq(G, 0, 1))), hgG_rws)
          +hge1 : {Nat.is_le(1n, n) == True{} : Bool} =
            Equal.trans(Bool, Nat.is_le(1n, n), Nat.is_le(1n, 1n+p), True{},
              Equal.cong(Nat, Bool, x => Nat.is_le(1n, x), n, 1n+p, en),
              NatProof.Nat.is_le_zero_l(p))
          +ecwS_s = Equal.sym(+List<+List<Nat>>, SolveFast.cwords_words(cwS),
                      cs, ecwS)
          +en_cw : {n == Groups.len_words(SolveFast.cwords_words(cwS)) : Nat} =
            Equal.cong(+List<+List<Nat>>, Nat, l => Groups.len_words(l), cs,
              SolveFast.cwords_words(cwS), ecwS_s)
          +base_lb = SolveFast.init_floor(n)
          GR.with_dup_arr(Nat,
            GR.RootPrepSpec(inf, G, cs, True{}, nd,
              Greedy.finish_rsort(gG, cwS, n, inf, bkts,
                Greedy.rsort_fill(G, 0, cwS, n, base_lb,
                  Greedy.RSortSt{seen,
                    Array.new(+List<SolveFast.CWord>, 10n, Nil{}), tbl, gen}))),
            seen,
            s1 => s2 => +es1 => +es2 =>
            GR.with_dup_arr(U32,
              GR.RootPrepSpec(inf, G, cs, True{}, nd,
                Greedy.finish_rsort(gG, cwS, n, inf, bkts,
                  Greedy.rsort_fill(G, 0, cwS, n, base_lb,
                    Greedy.RSortSt{seen,
                      Array.new(+List<SolveFast.CWord>, 10n, Nil{}), tbl, gen}))),
              tbl,
              t1 => t2 => +et1 => +et2 =>
              +hs1 = FH.FH.seen_tree_transport(10n, 0, seen, s1, gen, Nil{},
                       Equal.sym(Array<Nat>, s1, seen, es1), hs)
              +ht1 = FT.FT.tbl_ok_transport(G, cs, n, tbl, t1,
                       Equal.sym(Array<U32>, t1, tbl, et1), ht)
              +hst0 : GR.RSortSpec(G, cs, n, SolveFast.cwords_words(cwS), Nil{},
                        Greedy.RSortSt{s1,
                          Array.new(+List<SolveFast.CWord>, 10n, Nil{}),
                          t1, gen}) =
                Arr.DPair{hs1, Arr.DPair{ht1,
                  GR.rbkts_inv_new(G, n, SolveFast.cwords_words(cwS))}}
              +hfill_cw = GR.rsort_fill_ok(G, 0, G, cs, n, cwS, n, base_lb,
                            Nil{},
                            Greedy.RSortSt{s1,
                              Array.new(+List<SolveFast.CWord>, 10n, Nil{}),
                              t1, gen},
                            hrwsG, GR.all_in_refl(G), hge1, en_cw, hcwS, hst0)
              +es12 : {s1 == s2 : Array<Nat>} =
                Equal.trans(Array<Nat>, s1, seen, s2, es1,
                  Equal.sym(Array<Nat>, s2, seen, es2))
              +et12 : {t1 == t2 : Array<U32>} =
                Equal.trans(Array<U32>, t1, tbl, t2, et1,
                  Equal.sym(Array<U32>, t2, tbl, et2))
              +hfill : GR.RSortSpec(G, cs, n, cs, GR.rev_words(G, Nil{}),
                         Greedy.rsort_fill(G, 0, cwS, n, base_lb,
                           Greedy.RSortSt{s2,
                             Array.new(+List<SolveFast.CWord>, 10n, Nil{}),
                             t2, gen})) =
                %ecwS : GR.RSortSpec(G, cs, n, _, GR.rev_words(G, Nil{}),
                          Greedy.rsort_fill(G, 0, cwS, n, base_lb,
                            Greedy.RSortSt{s2,
                              Array.new(+List<SolveFast.CWord>, 10n, Nil{}),
                              t2, gen}))
                %es12 : GR.RSortSpec(G, cs, n, SolveFast.cwords_words(cwS),
                          GR.rev_words(G, Nil{}),
                          Greedy.rsort_fill(G, 0, cwS, n, base_lb,
                            Greedy.RSortSt{_,
                              Array.new(+List<SolveFast.CWord>, 10n, Nil{}),
                              t2, gen}))
                %et12 : GR.RSortSpec(G, cs, n, SolveFast.cwords_words(cwS),
                          GR.rev_words(G, Nil{}),
                          Greedy.rsort_fill(G, 0, cwS, n, base_lb,
                            Greedy.RSortSt{s1,
                              Array.new(+List<SolveFast.CWord>, 10n, Nil{}),
                              _, gen}))
                hfill_cw
              %Equal.sym(Bool, nd, True{}, end_t) :
                GR.RootPrepSpec(inf, G, cs, True{}, _,
                  Greedy.finish_rsort(gG, cwS, n, inf, bkts,
                    Greedy.rsort_fill(G, 0, cwS, n, base_lb,
                      Greedy.RSortSt{seen,
                        Array.new(+List<SolveFast.CWord>, 10n, Nil{}),
                        tbl, gen})))
              %es2 :
                GR.RootPrepSpec(inf, G, cs, True{}, True{},
                  Greedy.finish_rsort(gG, cwS, n, inf, bkts,
                    Greedy.rsort_fill(G, 0, cwS, n, base_lb,
                      Greedy.RSortSt{_,
                        Array.new(+List<SolveFast.CWord>, 10n, Nil{}),
                        tbl, gen})))
              %et2 :
                GR.RootPrepSpec(inf, G, cs, True{}, True{},
                  Greedy.finish_rsort(gG, cwS, n, inf, bkts,
                    Greedy.rsort_fill(G, 0, cwS, n, base_lb,
                      Greedy.RSortSt{s2,
                        Array.new(+List<SolveFast.CWord>, 10n, Nil{}),
                        _, gen})))
              GR.finish_rsort_spec(p, inf, G, gG, cwS, cs, bkts,
                Greedy.rsort_fill(G, 0, cwS, n, base_lb,
                  Greedy.RSortSt{s2,
                    Array.new(+List<SolveFast.CWord>, 10n, Nil{}), t2, gen}),
                en, ecwS, hcwS, hgG, hai, hnd_t, hb, hfill)))
