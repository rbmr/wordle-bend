# Obligation B: the class branching factor counted by `class_k_start`.
#
# `class_k_start` scans the guess list once per guess with the already proved
# histogram fold `FH.hist5_go`, so the `k` of one pass is `FH.hist5_go_spec`'s
# number of feedback groups of that guess on the class. `CK.ck_loop_spec` folds
# the maximum over the guesses and `CK.class_k_spec` states the result: `k`
# bounds `CK.prefmax`, the largest number of feedback classes any guess of the
# whole guess list produces on the class.
import Base
import ../src/groups.bend as Groups
import ../src/solve_fast.bend as SolveFast
import ./fast_hist5.bend as FH
import ./nat.bend as NatProof
import ./logic.bend as Logic
import ./fast_tbl.bend as FT
import ./array.bend as Arr
import ./feedback.bend as FbProof
import ../src/feedback.bend as Feedback

def CK.len(+xs: +List<+List<Nat>>) -> Nat:
  List.length(&2, +List<Nat>, xs)

# The number of feedback groups of `g` on the class `ws`.
def CK.count(+g: +List<Nat>, +ws: +List<+List<Nat>>) -> Nat:
  FH.FH.fgroups_count(SolveFast.fgroups_build_fast(g, ws, Nil{}))

# The largest count over the first `i` guesses.
def CK.prefmax(+G: +List<+List<Nat>>, +ws: +List<+List<Nat>>,
               +i: Nat) -> Nat:
  match i:
    case 0n:
      0n
    case 1n+p:
      Nat.max(CK.count(FT.FT.nth_word(G, p), ws), CK.prefmax(G, ws, p))

# `max a b <= c` from both bounds.
def CK.max_le(+a: Nat, +b: Nat, +c: Nat,
    ha: {Nat.is_le(a, c) == True{} : Bool},
    hb: {Nat.is_le(b, c) == True{} : Bool}) ->
  {Nat.is_le(Nat.max(a, b), c) == True{} : Bool}:
  match a b:
    case 0n _:
      hb
    case 1n+ap 0n:
      ha
    case 1n++ap 1n++bp:
      match c:
        case 0n:
          Empty.absurd({Nat.is_le(Nat.max(1n+ap, 1n+bp), 0n) == True{} : Bool},
            Logic.Proof.false_ne_true(ha))
        case 1n++cp:
          +ha2 : {Nat.is_le(ap, cp) == True{} : Bool} =
            NatProof.Nat.is_le_succ_inv(ap, cp, ha)
          +hb2 : {Nat.is_le(bp, cp) == True{} : Bool} =
            NatProof.Nat.is_le_succ_inv(bp, cp, hb)
          NatProof.Nat.is_le_succ(Nat.max(ap, bp), cp,
            CK.max_le(ap, bp, cp, ha2, hb2))

# `a <= max a b`.
def CK.le_max_l(+a: Nat, +b: Nat) ->
  {Nat.is_le(a, Nat.max(a, b)) == True{} : Bool}:
  match a b:
    case 0n _:
      NatProof.Nat.is_le_zero_l(b)
    case 1n+ap 0n:
      NatProof.Nat.is_le_refl(1n+ap)
    case 1n+ap 1n+bp:
      NatProof.Nat.is_le_succ(ap, Nat.max(ap, bp), CK.le_max_l(ap, bp))

# `b <= max a b`.
def CK.le_max_r(+a: Nat, +b: Nat) ->
  {Nat.is_le(b, Nat.max(a, b)) == True{} : Bool}:
  match a b:
    case 0n _:
      NatProof.Nat.is_le_refl(b)
    case 1n+ap 0n:
      NatProof.Nat.is_le_zero_l(1n+ap)
    case 1n+ap 1n+bp:
      NatProof.Nat.is_le_succ(bp, Nat.max(ap, bp), CK.le_max_r(ap, bp))

# `a < b` rules out `b <= a`.
def CK.not_le_of_lt(+a: Nat, +b: Nat,
    +h: {Nat.is_lt(a, b) == True{} : Bool}) ->
  {Nat.is_le(b, a) == False{} : Bool}:
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.is_le(0n, 0n) == False{} : Bool},
        Logic.Proof.false_ne_true(h))
    case 0n 1n+bp:
      {==}
    case 1n+ap 0n:
      Empty.absurd({Nat.is_le(0n, 1n+ap) == False{} : Bool},
        Logic.Proof.false_ne_true(h))
    case 1n+ap 1n+bp:
      CK.not_le_of_lt(ap, bp, h)

# Substitution in the second argument of `is_lt`.
def CK.lt_eq_r(+a: Nat, +b: Nat, +c: Nat, e: {b == c : Nat},
    p: {Nat.is_lt(a, b) == True{} : Bool}) ->
  {Nat.is_lt(a, c) == True{} : Bool}:
  %e : {Nat.is_lt(a, _) == True{} : Bool}
  p

# `a <= a + b`.
def CK.le_self_add(+a: Nat, +b: Nat) ->
  {Nat.is_le(a, Nat.add(a, b)) == True{} : Bool}:
  match b:
    case 0n:
      NatProof.Nat.is_le_eq_r(a, a, Nat.add(a, 0n),
        Equal.sym(Nat, Nat.add(a, 0n), a, NatProof.NatPrf.add_zero(a)),
        NatProof.Nat.is_le_refl(a))
    case 1n+bp:
      +ih : {Nat.is_le(a, Nat.add(a, bp)) == True{} : Bool} =
        CK.le_self_add(a, bp)
      +hadd : {Nat.add(a, 1n+bp) == Nat.add(1n, Nat.add(a, bp)) : Nat} =
        NatProof.NatPrf.add_succ(a, bp)
      +hlt0 : {Nat.is_lt(Nat.add(a, bp), 1n+Nat.add(a, bp)) == True{} : Bool} =
        NatProof.Nat.is_lt_succ_self(Nat.add(a, bp))
      +hlt : {Nat.is_lt(Nat.add(a, bp), Nat.add(a, 1n+bp)) == True{} : Bool} =
        CK.lt_eq_r(Nat.add(a, bp), 1n+Nat.add(a, bp), Nat.add(a, 1n+bp),
          Equal.sym(Nat, Nat.add(a, 1n+bp), Nat.add(1n, Nat.add(a, bp)), hadd),
          hlt0)
      NatProof.Nat.is_le_trans(a, Nat.add(a, bp), Nat.add(a, 1n+bp), ih,
        NatProof.Nat.is_le_of_lt(Nat.add(a, bp), Nat.add(a, 1n+bp), hlt))

# `a + (1 + b) = (1 + a) + b`.
def CK.add_rot(+a: Nat, +b: Nat) ->
  {Nat.add(a, Nat.add(1n, b)) == Nat.add(Nat.add(1n, a), b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+ap:
      Equal.cong(Nat, Nat, x => Nat.add(1n, x),
        Nat.add(ap, Nat.add(1n, b)),
        Nat.add(Nat.add(1n, ap), b),
        CK.add_rot(ap, b))

# `is_le 2 (1 + p) = False` forces `p = 0`.
def CK.pred_zero(+p: Nat,
    +h: {Nat.is_le(2n, Nat.add(1n, p)) == False{} : Bool}) ->
  {p == 0n : Nat}:
  match p:
    case 0n:
      {==}
    case 1n+pp:
      Empty.absurd({1n+pp == 0n : Nat},
        Logic.Proof.true_ne_false(
          Equal.trans(Bool, True{}, Nat.is_le(2n, Nat.add(1n, 1n+pp)), False{},
            Equal.sym(Bool, Nat.is_le(2n, Nat.add(1n, 1n+pp)), True{},
              NatProof.Nat.is_le_succ(1n, 1n+pp,
                NatProof.Nat.is_le_succ(0n, pp,
                  NatProof.Nat.is_le_zero_l(pp)))),
            h)))

# `prefmax` does not decrease when one more guess is folded in.
def CK.prefmax_mono(+G: +List<+List<Nat>>, +ws: +List<+List<Nat>>, +i: Nat) ->
  {Nat.is_le(CK.prefmax(G, ws, i), CK.prefmax(G, ws, Nat.add(1n, i)))
   == True{} : Bool}:
  match i:
    case 0n:
      NatProof.Nat.is_le_zero_l(CK.prefmax(G, ws, 1n))
    case 1n+p:
      CK.le_max_r(CK.count(FT.FT.nth_word(G, Nat.add(1n, p)), ws),
        CK.prefmax(G, ws, Nat.add(1n, p)))

# `prefmax i <= prefmax (i + fuel)`.
def CK.prefmax_le_add(+G: +List<+List<Nat>>, +ws: +List<+List<Nat>>,
    +i: Nat, +fuel: Nat) ->
  {Nat.is_le(CK.prefmax(G, ws, i), CK.prefmax(G, ws, Nat.add(i, fuel)))
   == True{} : Bool}:
  match fuel:
    case 0n:
      NatProof.Nat.is_le_eq_r(CK.prefmax(G, ws, i), CK.prefmax(G, ws, i),
        CK.prefmax(G, ws, Nat.add(i, 0n)),
        Equal.cong(Nat, Nat, x => CK.prefmax(G, ws, x),
          i, Nat.add(i, 0n),
          Equal.sym(Nat, Nat.add(i, 0n), i, NatProof.NatPrf.add_zero(i))),
        NatProof.Nat.is_le_refl(CK.prefmax(G, ws, i)))
    case 1n+p:
      +ih : {Nat.is_le(CK.prefmax(G, ws, i),
                       CK.prefmax(G, ws, Nat.add(i, p))) == True{} : Bool} =
        CK.prefmax_le_add(G, ws, i, p)
      +hst : {Nat.is_le(CK.prefmax(G, ws, Nat.add(i, p)),
                        CK.prefmax(G, ws, Nat.add(1n, Nat.add(i, p))))
              == True{} : Bool} =
        CK.prefmax_mono(G, ws, Nat.add(i, p))
      +hfin : {Nat.is_le(CK.prefmax(G, ws, i),
                         CK.prefmax(G, ws, Nat.add(1n, Nat.add(i, p))))
               == True{} : Bool} =
        NatProof.Nat.is_le_trans(CK.prefmax(G, ws, i),
          CK.prefmax(G, ws, Nat.add(i, p)),
          CK.prefmax(G, ws, Nat.add(1n, Nat.add(i, p))), ih, hst)
      +es : {Nat.add(i, 1n+p) == Nat.add(1n, Nat.add(i, p)) : Nat} =
        NatProof.NatPrf.add_succ(i, p)
      NatProof.Nat.is_le_eq_r(CK.prefmax(G, ws, i),
        CK.prefmax(G, ws, Nat.add(1n, Nat.add(i, p))),
        CK.prefmax(G, ws, Nat.add(i, 1n+p)),
        Equal.cong(Nat, Nat, x => CK.prefmax(G, ws, x),
          Nat.add(1n, Nat.add(i, p)), Nat.add(i, 1n+p),
          Equal.sym(Nat, Nat.add(i, 1n+p), Nat.add(1n, Nat.add(i, p)), es)),
        hfin)

# `keep_fast` never exceeds the list length.
def CK.keep_le_len_step(+g: +List<Nat>, +w: +List<Nat>,
    +t: +List<+List<Nat>>, same: Bool,
    +ih: {Nat.is_le(SolveFast.keep_fast(g, t), Groups.len_words(t))
          == True{} : Bool}) ->
  {Nat.is_le(SolveFast.keep_step(SolveFast.keep_fast(g, t), same),
     Groups.len_words(w <> t)) == True{} : Bool}:
  match same:
    case True{}:
      NatProof.Nat.is_le_trans(SolveFast.keep_fast(g, t), Groups.len_words(t),
        Groups.len_words(w <> t), ih,
        NatProof.Nat.is_le_add_self_l(1n, Groups.len_words(t)))
    case False{}:
      NatProof.Nat.is_le_add_l(SolveFast.keep_fast(g, t), Groups.len_words(t),
        1n, ih)

def CK.keep_le_len(+g: +List<Nat>, +S: +List<+List<Nat>>) ->
  {Nat.is_le(SolveFast.keep_fast(g, S), Groups.len_words(S))
   == True{} : Bool}:
  match S:
    case Nil{}:
      NatProof.Nat.is_le_zero_l(0n)
    case Con{+w, +t}:
      CK.keep_le_len_step(g, w, t, SolveFast.word_eq_fast(g, w),
        CK.keep_le_len(g, t))

# The histogram fold never prunes when its budget starts at the class length
# and the class is scanned without `skip_self`: the pruning test would need
# `1 + m + count <= total` while `total <= m`.
def CK.prune_impossible(+g: +List<Nat>, +ws: +List<+List<Nat>>, +m: Nat,
    +hm: {m == Groups.len_words(ws) : Nat},
    +h: {FH.FH.pruned_reason(g, ws, Nil{}, m, False{}) == True{} : Bool}) ->
  Empty:
  +fg1 : +List<SolveFast.FGroup> = SolveFast.fgroups_build_fast(g, ws, Nil{})
  +hle : {Nat.is_le(Nat.add(1n, Nat.add(m, FH.FH.fgroups_count(fg1))),
          FH.FH.fgroups_total(fg1)) == True{} : Bool} = h
  +etot : {FH.FH.fgroups_total(fg1) == SolveFast.keep_fast(g, ws) : Nat} =
    Equal.trans(Nat, FH.FH.fgroups_total(fg1),
      Nat.add(SolveFast.keep_fast(g, ws), FH.FH.fgroups_total(Nil{})),
      SolveFast.keep_fast(g, ws),
      FH.FH.fgroups_build_total_eq_keep(g, ws, Nil{}),
      NatProof.NatPrf.add_zero(SolveFast.keep_fast(g, ws)))
  +hkeep : {Nat.is_le(SolveFast.keep_fast(g, ws), m) == True{} : Bool} =
    NatProof.Nat.is_le_eq_r(SolveFast.keep_fast(g, ws),
      Groups.len_words(ws), m,
      Equal.sym(Nat, m, Groups.len_words(ws), hm),
      CK.keep_le_len(g, ws))
  +hlem : {Nat.is_le(Nat.add(1n, Nat.add(m, FH.FH.fgroups_count(fg1))), m)
           == True{} : Bool} =
    NatProof.Nat.is_le_trans(
      Nat.add(1n, Nat.add(m, FH.FH.fgroups_count(fg1))),
      FH.FH.fgroups_total(fg1), m, hle,
      NatProof.Nat.is_le_eq_l(m, SolveFast.keep_fast(g, ws),
        FH.FH.fgroups_total(fg1),
        Equal.sym(Nat, FH.FH.fgroups_total(fg1), SolveFast.keep_fast(g, ws),
          etot),
        hkeep))
  +hsucc : {Nat.is_le(Nat.add(1n, m), Nat.add(1n, Nat.add(m,
              FH.FH.fgroups_count(fg1)))) == True{} : Bool} =
    NatProof.Nat.is_le_add_l(m, Nat.add(m, FH.FH.fgroups_count(fg1)), 1n,
      CK.le_self_add(m, FH.FH.fgroups_count(fg1)))
  +hfinal : {Nat.is_le(Nat.add(1n, m), m) == True{} : Bool} =
    NatProof.Nat.is_le_trans(Nat.add(1n, m),
      Nat.add(1n, Nat.add(m, FH.FH.fgroups_count(fg1))), m, hsucc, hlem)
  +hfalse : {Nat.is_le(Nat.add(1n, m), m) == False{} : Bool} =
    CK.not_le_of_lt(m, Nat.add(1n, m), NatProof.Nat.is_lt_succ_self(m))
  Logic.Proof.false_ne_true(
    Equal.trans(Bool, False{}, Nat.is_le(Nat.add(1n, m), m), True{},
      Equal.sym(Bool, Nat.is_le(Nat.add(1n, m), m), False{}, hfalse), hfinal))

# The loop's hypothesis: the table is valid, the scratch array is stamped for
# `gen` with the codes of guess `i`, and that guess produced at most `k`
# codes on the class.
def CK.HistEntry(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n_root: Nat,
    +ws: +List<+List<Nat>>, +i: Nat, +gen: Nat,
    hist: SolveFast.Hist5Res) -> Data:
  match hist:
    case SolveFast.Hist5Pruned{seen, tbl}:
      Empty
    case SolveFast.Hist5Ok{seen, tbl, m, k, budget}:
      Arr.Arr.DPair<FT.FT.TblOk(G, C, n_root, tbl),
        Arr.Arr.DPair<FH.FH.SeenTree(10n, 0, seen, gen,
            SolveFast.fgroups_build_fast(FT.FT.nth_word(G, i), ws, Nil{})),
          {Nat.is_le(CK.count(FT.FT.nth_word(G, i), ws), k)
           == True{} : Bool}>>

# The loop's postcondition: the table is valid and `k` covers `prefmax t`.
def CK.LoopOk(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n_root: Nat,
    +ws: +List<+List<Nat>>, +t: Nat, r: SolveFast.CKRes) -> Data:
  match r:
    case SolveFast.CKRes{tbl, k}:
      Arr.Arr.DPair<FT.FT.TblOk(G, C, n_root, tbl),
        {Nat.is_le(CK.prefmax(G, ws, t), k) == True{} : Bool}>

# `k` of `max kmax k2` covers `prefmax (i + 1)`.
def CK.prefmax_succ(+G: +List<+List<Nat>>, +ws: +List<+List<Nat>>,
    +i: Nat, +kmax: Nat, +k2: Nat,
    +hk: {Nat.is_le(CK.prefmax(G, ws, i), kmax) == True{} : Bool},
    +hc: {Nat.is_le(CK.count(FT.FT.nth_word(G, i), ws), k2)
          == True{} : Bool}) ->
  {Nat.is_le(CK.prefmax(G, ws, Nat.add(1n, i)), Nat.max(kmax, k2))
   == True{} : Bool}:
  CK.max_le(CK.count(FT.FT.nth_word(G, i), ws), CK.prefmax(G, ws, i),
    Nat.max(kmax, k2),
    NatProof.Nat.is_le_trans(CK.count(FT.FT.nth_word(G, i), ws), k2,
      Nat.max(kmax, k2), hc, CK.le_max_r(kmax, k2)),
    NatProof.Nat.is_le_trans(CK.prefmax(G, ws, i), kmax,
      Nat.max(kmax, k2), hk, CK.le_max_l(kmax, k2)))

# Substitution in the left argument of `U32.is_eq` under a proposition.
def CK.u32_eq_l(+a1: Nat, +a2: Nat, +u: U32, e: {a1 == a2 : Nat},
    p: {U32.is_eq(U32.from_nat(a1), u) == True{} : Bool}) ->
  {U32.is_eq(U32.from_nat(a2), u) == True{} : Bool}:
  +ee : {U32.from_nat(a2) == U32.from_nat(a1) : U32} =
    Equal.cong(Nat, U32, x => U32.from_nat(x), a2, a1,
      Equal.sym(Nat, a1, a2, e))
  +eq : {U32.is_eq(U32.from_nat(a2), u) == U32.is_eq(U32.from_nat(a1), u)
         : Bool} =
    Equal.cong(U32, Bool, x => U32.is_eq(x, u),
      U32.from_nat(a2), U32.from_nat(a1), ee)
  Equal.trans(Bool, U32.is_eq(U32.from_nat(a2), u),
    U32.is_eq(U32.from_nat(a1), u), True{}, eq, p)

# Substitution in the right argument of `U32.is_eq` under a proposition.
def CK.u32_eq_r(+l: U32, +u1: U32, +u2: U32, e: {u1 == u2 : U32},
    p: {U32.is_eq(l, u1) == True{} : Bool}) ->
  {U32.is_eq(l, u2) == True{} : Bool}:
  +eq : {U32.is_eq(l, u2) == U32.is_eq(l, u1) : Bool} =
    Equal.cong(U32, Bool, x => U32.is_eq(l, x), u2, u1,
      Equal.sym(U32, u1, u2, e))
  Equal.trans(Bool, U32.is_eq(l, u2), U32.is_eq(l, u1), True{}, eq, p)

# Rewrite under a proposition-valued equality.
def CK.true_eq_r(+x: Bool, +y: Bool, e: {x == y : Bool},
    p: {x == True{} : Bool}) -> {y == True{} : Bool}:
  Equal.trans(Bool, y, x, True{}, Equal.sym(Bool, x, y, e), p)

# `has_grow_go` only reads the row, so an equal row gives the same answer.
def CK.hg_row_eq(+G: +List<+List<Nat>>, +n: Nat, +r1: U32, +r2: U32,
    +g: +List<Nat>, +cur: Nat, e: {r1 == r2 : U32},
    p: {FT.FT.has_grow_go(G, n, r1, g, cur) == True{} : Bool}) ->
  {FT.FT.has_grow_go(G, n, r2, g, cur) == True{} : Bool}:
  CK.true_eq_r(FT.FT.has_grow_go(G, n, r1, g, cur),
    FT.FT.has_grow_go(G, n, r2, g, cur),
    Equal.cong(U32, Bool, x => FT.FT.has_grow_go(G, n, x, g, cur), r1, r2, e),
    p)

# The row/word correspondence of the table: the `j`-th word of `G` sits at row
# `from_nat (cur + j)` of the scan that starts at offset `cur`.
def CK.hg_nth(+G: +List<+List<Nat>>, +n: Nat, +j: Nat, +cur: Nat,
    +h: {Nat.is_le(Nat.add(1n, j), Groups.len_words(G)) == True{} : Bool}) ->
  {FT.FT.has_grow_go(G, n, U32.from_nat(Nat.add(cur, j)), FT.FT.nth_word(G, j),
     cur) == True{} : Bool}:
  match G:
    case Nil{}:
      Empty.absurd(
        {FT.FT.has_grow_go(Nil{}, n, U32.from_nat(Nat.add(cur, j)),
           FT.FT.nth_word(Nil{}, j), cur) == True{} : Bool},
        Logic.Proof.false_ne_true(h))
    case Con{+w, +rest}:
      match j:
        case 0n:
          +e0 : {Nat.add(cur, 0n) == cur : Nat} = NatProof.NatPrf.add_zero(cur)
          +hi : {U32.is_eq(U32.from_nat(Nat.add(cur, 0n)), U32.from_nat(cur))
                 == True{} : Bool} =
            CK.u32_eq_l(cur, Nat.add(cur, 0n), U32.from_nat(cur),
              Equal.sym(Nat, Nat.add(cur, 0n), cur, e0),
              Arr.Arr.u32_is_eq_refl(U32.from_nat(cur)))
          +hw : {Feedback.word_eq(w, w) == True{} : Bool} =
            FbProof.FbPrf.word_eq_refl(w)
          +hand : {Bool.and(U32.is_eq(U32.from_nat(Nat.add(cur, 0n)),
                       U32.from_nat(cur)), Feedback.word_eq(w, w))
                   == True{} : Bool} =
            Logic.Proof.and_intro(U32.is_eq(U32.from_nat(Nat.add(cur, 0n)),
                U32.from_nat(cur)), Feedback.word_eq(w, w), hi, hw)
          FH.FH.bool_or_l(
            Bool.and(U32.is_eq(U32.from_nat(Nat.add(cur, 0n)),
              U32.from_nat(cur)), Feedback.word_eq(w, w)),
            FT.FT.has_grow_go(rest, n, U32.from_nat(Nat.add(cur, 0n)),
              w, 1n+cur), hand)
        case 1n+p:
          +hle : {Nat.is_le(Nat.add(1n, p), Groups.len_words(rest))
                  == True{} : Bool} =
            NatProof.Nat.is_le_succ_inv(1n+p, Groups.len_words(rest), h)
          +ih : {FT.FT.has_grow_go(rest, n,
                    U32.from_nat(Nat.add(Nat.add(1n, cur), p)),
                    FT.FT.nth_word(rest, p), Nat.add(1n, cur))
                  == True{} : Bool} =
            CK.hg_nth(rest, n, p, Nat.add(1n, cur), hle)
          +er : {U32.from_nat(Nat.add(Nat.add(1n, cur), p))
                 == U32.from_nat(Nat.add(cur, 1n+p)) : U32} =
            Equal.cong(Nat, U32, x => U32.from_nat(x),
              Nat.add(Nat.add(1n, cur), p), Nat.add(cur, 1n+p),
              Equal.sym(Nat, Nat.add(cur, 1n+p),
                Nat.add(Nat.add(1n, cur), p), CK.add_rot(cur, p)))
          +ih2 : {FT.FT.has_grow_go(rest, n,
                     U32.from_nat(Nat.add(cur, 1n+p)),
                     FT.FT.nth_word(rest, p), Nat.add(1n, cur))
                   == True{} : Bool} =
            CK.hg_row_eq(rest, n, U32.from_nat(Nat.add(Nat.add(1n, cur), p)),
              U32.from_nat(Nat.add(cur, 1n+p)), FT.FT.nth_word(rest, p),
              Nat.add(1n, cur), er, ih)
          FH.FH.bool_or_r(
            Bool.and(U32.is_eq(U32.from_nat(Nat.add(cur, 1n+p)),
              U32.from_nat(cur)),
              Feedback.word_eq(FT.FT.nth_word(rest, p), w)),
            FT.FT.has_grow_go(rest, n, U32.from_nat(Nat.add(cur, 1n+p)),
              FT.FT.nth_word(rest, p), Nat.add(1n, cur)), ih2)

# `fgroups_wf` holds for the empty group list, the accumulator a fresh pass
# starts from.
def CK.wf_nil() -> {FH.FH.fgroups_wf(Nil{}) == True{} : Bool}:
  {==}

# Three copies of an array, for a proof step that needs the scratch buffer in
# three places: the implementation term, the histogram specification and the
# generation bump.
def CK.dup3_node(-T: Data, -xs: Array<T>, -ys: Array<T>,
    rx: &x1: Array<T> -> &x2: Array<T> -> &x3: Array<T> ->
        {x1 == xs : Array<T>}
        & Arr.Arr.DPair<{x2 == x1 : Array<T>}, {x3 == x1 : Array<T>}>,
    ry: &y1: Array<T> -> &y2: Array<T> -> &y3: Array<T> ->
        {y1 == ys : Array<T>}
        & Arr.Arr.DPair<{y2 == y1 : Array<T>}, {y3 == y1 : Array<T>}>) ->
  &a1: Array<T> -> &a2: Array<T> -> &a3: Array<T> ->
  {a1 == ANode{xs, ys} : Array<T>}
  & Arr.Arr.DPair<{a2 == a1 : Array<T>}, {a3 == a1 : Array<T>}>:
  (x1, rx2) = rx
  (x2, rx3) = rx2
  (x3, pex) = rx3
  (ex1, pey) = pex
  match pey:
    case Arr.DPair{ex2, ex3}:
      (y1, ry2) = ry
      (y2, ry3) = ry2
      (y3, pey2) = ry3
      (ey1, pez) = pey2
      match pez:
        case Arr.DPair{ey2, ey3}:
          e1 = Equal.trans(Array<T>, ANode{x1, y1}, ANode{xs, y1},
            ANode{xs, ys},
            Equal.cong(Array<T>, Array<T>, l => ANode{l, y1}, x1, xs, ex1),
            Equal.cong(Array<T>, Array<T>, r => ANode{xs, r}, y1, ys, ey1))
          e2 = Equal.trans(Array<T>, ANode{x2, y2}, ANode{x1, y2},
            ANode{x1, y1},
            Equal.cong(Array<T>, Array<T>, l => ANode{l, y2}, x2, x1, ex2),
            Equal.cong(Array<T>, Array<T>, r => ANode{x1, r}, y2, y1, ey2))
          e3 = Equal.trans(Array<T>, ANode{x3, y3}, ANode{x1, y3},
            ANode{x1, y1},
            Equal.cong(Array<T>, Array<T>, l => ANode{l, y3}, x3, x1, ex3),
            Equal.cong(Array<T>, Array<T>, r => ANode{x1, r}, y3, y1, ey3))
          (ANode{x1, y1},
            (ANode{x2, y2},
              (ANode{x3, y3}, (e1, Arr.DPair{e2, e3}))))

def CK.dup3(-T: Data, a: Array<T>) ->
  &a1: Array<T> -> &a2: Array<T> -> &a3: Array<T> ->
  {a1 == a : Array<T>}
  & Arr.Arr.DPair<{a2 == a1 : Array<T>}, {a3 == a1 : Array<T>}>:
  match a:
    case ALeaf{+x}:
      (ALeaf{x},
        (ALeaf{x}, (ALeaf{x}, ({==}, Arr.DPair{{==}, {==}}))))
    case ANode{xs, ys}:
      CK.dup3_node(T, xs, ys, CK.dup3(T, xs), CK.dup3(T, ys))

# Consume one histogram result. `hist` and its specification are parameters, so
# the branches can read them; the continuation receives the rebuilt result and
# its entry invariant, which are the hypotheses of the recursive call.
def CK.take_hist(-R: SolveFast.Hist5Res -> Data,
    +G: +List<+List<Nat>>, +Croot: +List<+List<Nat>>,
    +ws: +List<+List<Nat>>, +n_root: Nat, +i: Nat, +gen: Nat, +m: Nat,
    +g: +List<Nat>, +S: +List<+List<Nat>>, -tbl0: Array<U32>,
    +ew: {S == ws : +List<+List<Nat>>},
    +eg: {g == FT.FT.nth_word(G, i) : +List<Nat>},
    +hm: {m == Groups.len_words(ws) : Nat},
    +htbl0: FT.FT.TblOk(G, Croot, n_root, tbl0),
    hist: SolveFast.Hist5Res,
    hspec: FH.FH.HistSpec(g, S, Nil{}, gen, m, False{}, tbl0, hist),
    kont: @h2: SolveFast.Hist5Res ->
          CK.HistEntry(G, Croot, n_root, ws, i, gen, h2) -> R(h2)) -> R(hist):
  match hist:
    case SolveFast.Hist5Pruned{seen3, tbl3}:
      match hspec:
        case Arr.DPair{hs3, r}:
          match r:
            case Arr.DPair{et3, hpr}:
              +hmS : {m == Groups.len_words(S) : Nat} =
                Equal.trans(Nat, m, Groups.len_words(ws), Groups.len_words(S),
                  hm, Equal.cong(+List<+List<Nat>>, Nat, x => Groups.len_words(x), ws, S,
                    Equal.sym(+List<+List<Nat>>, S, ws, ew)))
              Empty.absurd(R(SolveFast.Hist5Pruned{seen3, tbl3}),
                CK.prune_impossible(g, S, m, hmS, hpr))
    case SolveFast.Hist5Ok{seen3, tbl3, +m3, +k3, b3}:
      match hspec:
        case Arr.DPair{hs3, r}:
          match r:
            case Arr.DPair{et3, r2}:
              match r2:
                case Arr.DPair{hwf, r3}:
                  match r3:
                    case Arr.DPair{hm3, r4}:
                      match r4:
                        case Arr.DPair{hk3, r5}:
                          match r5:
                            case Arr.DPair{hb3, hle3}:
                                  +htbl3 : FT.FT.TblOk(G, Croot, n_root, tbl3) =
                                    FT.FT.tbl_ok_transport(G, Croot, n_root,
                                      tbl0, tbl3,
                                      Equal.sym(Array<U32>, tbl3, tbl0, et3),
                                      htbl0)
                                  +fgA : +List<SolveFast.FGroup> =
                                    SolveFast.fgroups_build_fast(
                                      FT.FT.nth_word(G, i), ws, Nil{})
                                  +fgB : +List<SolveFast.FGroup> =
                                    SolveFast.fgroups_build_fast(g, S, Nil{})
                                  +efg1 : {fgB == fgA : +List<SolveFast.FGroup>} =
                                    Equal.sym(+List<SolveFast.FGroup>, fgA, fgB,
                                      Equal.trans(+List<SolveFast.FGroup>,
                                        fgA,
                                        SolveFast.fgroups_build_fast(g, ws,
                                          Nil{}),
                                        fgB,
                                        Equal.cong(+List<Nat>,
                                          +List<SolveFast.FGroup>,
                                          x => SolveFast.fgroups_build_fast(x,
                                            ws, Nil{}),
                                          FT.FT.nth_word(G, i), g,
                                          Equal.sym(+List<Nat>, g,
                                            FT.FT.nth_word(G, i), eg)),
                                        Equal.cong(+List<+List<Nat>>,
                                          +List<SolveFast.FGroup>,
                                          w => SolveFast.fgroups_build_fast(g, w,
                                            Nil{}),
                                          ws, S,
                                          Equal.sym(+List<+List<Nat>>, S, ws,
                                            ew))))
                                  +hsE : FH.FH.SeenTree(10n, 0, seen3, gen,
                                      fgA) =
                                    FH.FH.seen_tree_transport_fg(10n, 0, seen3,
                                      gen, fgB, fgA, efg1, hs3)
                                  +hk3c : {k3 == CK.count(FT.FT.nth_word(G, i),
                                             ws) : Nat} =
                                    Equal.trans(Nat, k3,
                                      FH.FH.fgroups_count(fgB),
                                      CK.count(FT.FT.nth_word(G, i), ws),
                                      hk3,
                                      Equal.cong(+List<SolveFast.FGroup>, Nat,
                                        x => FH.FH.fgroups_count(x), fgB, fgA,
                                        efg1))
                                  +hc : {Nat.is_le(
                                           CK.count(FT.FT.nth_word(G, i), ws),
                                           k3) == True{} : Bool} =
                                    NatProof.Nat.is_le_eq_r(
                                      CK.count(FT.FT.nth_word(G, i), ws),
                                      CK.count(FT.FT.nth_word(G, i), ws), k3,
                                      Equal.sym(Nat, k3,
                                        CK.count(FT.FT.nth_word(G, i), ws),
                                        hk3c),
                                      NatProof.Nat.is_le_refl(
                                        CK.count(FT.FT.nth_word(G, i), ws)))
                                  kont(SolveFast.Hist5Ok{seen3, tbl3, m3, k3,
                                         b3},
                                    Arr.DPair{htbl3,
                                      Arr.DPair{hsE, hc}})

# One step of the scan: run the pass for the next guess and hand its entry
# invariant to the recursive call `rec`. The caller supplies the recursive
# lemma and duplicates the two arrays, so the scratch buffer stays available
# for the implementation term.
def CK.ck_step(+p: Nat, +i: Nat, +C: +List<SolveFast.CWord>, +gen: Nat,
    +m: Nat, +kmax: Nat, +k2: Nat, +kmax2: Nat,
    +G: +List<+List<Nat>>, +Croot: +List<+List<Nat>>, +n_root: Nat,
    +ws: +List<+List<Nat>>, +t: Nat,
    +ew: {SolveFast.cwords_words(C) == ws : +List<+List<Nat>>},
    +hS: {FT.FT.cwords_ok_b(G, Croot, n_root, C) == True{} : Bool},
    +hm: {m == Groups.len_words(ws) : Nat},
    +ht2: {Nat.add(Nat.add(1n, i), p) == t : Nat},
    +hi: {Nat.is_le(t, Groups.len_words(G)) == True{} : Bool},
    +hk2: {Nat.is_le(CK.prefmax(G, ws, Nat.add(1n, i)), kmax2)
           == True{} : Bool},
    +hrow: {FT.FT.gentry_ok_b(G, n_root, U32.from_nat(Nat.add(1n, i)),
              FT.FT.nth_word(G, Nat.add(1n, i))) == True{} : Bool},
    rec: @+i2: Nat -> @+g2: Nat -> @+k2b: Nat ->
         @h2: SolveFast.Hist5Res ->
         CK.HistEntry(G, Croot, n_root, ws, i2, g2, h2) ->
         {Nat.add(i2, p) == t : Nat} ->
         {Nat.is_le(CK.prefmax(G, ws, i2), k2b) == True{} : Bool} ->
         CK.LoopOk(G, Croot, n_root, ws, t,
           SolveFast.ck_loop(p, i2, C, g2, m, k2b, h2, Nat.is_le(2n, p))),
    -seen: Array<Nat>, -tbl: Array<U32>,
    +htbl: FT.FT.TblOk(G, Croot, n_root, tbl),
    +hs: FH.FH.SeenTree(10n, 0, seen, gen,
           SolveFast.fgroups_build_fast(FT.FT.nth_word(G, i), ws, Nil{})),
    dp3: &s1: Array<Nat> -> &s2: Array<Nat> -> &s3: Array<Nat> ->
         {s1 == seen : Array<Nat>}
         & Arr.Arr.DPair<{s2 == s1 : Array<Nat>}, {s3 == s1 : Array<Nat>}>,
    dpt: &t1: Array<U32> -> &t2: Array<U32> ->
         {t1 == tbl : Array<U32>} & {t2 == t1 : Array<U32>}) ->
  CK.LoopOk(G, Croot, n_root, ws, t,
    SolveFast.ck_loop(p, Nat.add(1n, i), C, Nat.add(1n, gen), m, kmax2,
      SolveFast.hist5_go(U32.from_nat(Nat.add(1n, i)), C, Nat.add(1n, gen),
        False{},
        SolveFast.Hist5Ok{seen, tbl, 0n, 0n, m}),
      Nat.is_le(2n, p))):
  (s1, dp32) = dp3
  (s2, dp33) = dp32
  (s3, pes) = dp33
  (+es1, pe32) = pes
  match pe32:
    case Arr.DPair{+es2, +es3}:
  (t1, dpt2) = dpt
  (t2, pet) = dpt2
  (+et1, +et2) = pet
  +es2_s : {s2 == seen : Array<Nat>} =
    Equal.trans(Array<Nat>, s2, s1, seen, es2, es1)
  +es3_s : {s3 == seen : Array<Nat>} =
    Equal.trans(Array<Nat>, s3, s1, seen, es3, es1)
  +et2_t : {t2 == tbl : Array<U32>} =
    Equal.trans(Array<U32>, t2, t1, tbl, et2, et1)
  +g1 : +List<Nat> = FT.FT.nth_word(G, Nat.add(1n, i))
  +row : U32 = U32.from_nat(Nat.add(1n, i))
  +gen2 : Nat = Nat.add(1n, gen)
  +hs3a : FH.FH.SeenTree(10n, 0, s3, gen,
      SolveFast.fgroups_build_fast(FT.FT.nth_word(G, i), ws, Nil{})) =
    FH.FH.seen_tree_transport(10n, 0, seen, s3, gen,
      SolveFast.fgroups_build_fast(FT.FT.nth_word(G, i), ws, Nil{}),
      Equal.sym(Array<Nat>, s3, seen, es3_s), hs)
  +hs3 : FH.FH.SeenTree(10n, 0, s3, gen2, Nil{}) =
    FH.FH.seen_tree_bump(10n, 0, s3, gen,
      SolveFast.fgroups_build_fast(FT.FT.nth_word(G, i), ws, Nil{}), hs3a)
  +e32 : {s3 == s2 : Array<Nat>} =
    Equal.trans(Array<Nat>, s3, s1, s2, es3, Equal.sym(Array<Nat>, s2, s1, es2))
  +hs2 : FH.FH.SeenTree(10n, 0, s2, gen2, Nil{}) =
    FH.FH.seen_tree_transport(10n, 0, s3, s2, gen2, Nil{}, e32, hs3)
  +ht2ok : FT.FT.TblOk(G, Croot, n_root, t2) =
    FT.FT.tbl_ok_transport(G, Croot, n_root, tbl, t2,
      Equal.sym(Array<U32>, t2, tbl, et2_t), htbl)
  +hhr2 : FH.FH.HistSpec(g1, SolveFast.cwords_words(C), Nil{}, gen2, m,
      False{}, t2, SolveFast.hist5_go(row, C, gen2, False{},
        SolveFast.Hist5Ok{s2, t2, 0n, 0n, m})) =
    FH.FH.hist5_go_spec(C, G, Croot, n_root, row, g1, Nil{}, s2, t2, gen2,
      0n, 0n, m, m, False{}, ht2ok, hrow, hS, {==}, CK.wf_nil(),
      {==}, {==}, hs2)
  +hhr_t : FH.FH.HistSpec(g1, SolveFast.cwords_words(C), Nil{}, gen2, m,
      False{}, tbl, SolveFast.hist5_go(row, C, gen2, False{},
        SolveFast.Hist5Ok{s2, t2, 0n, 0n, m})) =
    FH.FH.hist_spec_transport_tbl(g1, SolveFast.cwords_words(C), Nil{}, gen2,
      m, False{}, t2, tbl,
      SolveFast.hist5_go(row, C, gen2, False{},
        SolveFast.Hist5Ok{s2, t2, 0n, 0n, m}), et2_t, hhr2)
  +eq12 : {SolveFast.hist5_go(row, C, gen2, False{},
              SolveFast.Hist5Ok{s2, t2, 0n, 0n, m})
           == SolveFast.hist5_go(row, C, gen2, False{},
                SolveFast.Hist5Ok{s1, t1, 0n, 0n, m})
           : SolveFast.Hist5Res} =
    Equal.trans(SolveFast.Hist5Res,
      SolveFast.hist5_go(row, C, gen2, False{},
        SolveFast.Hist5Ok{s2, t2, 0n, 0n, m}),
      SolveFast.hist5_go(row, C, gen2, False{},
        SolveFast.Hist5Ok{s1, t2, 0n, 0n, m}),
      SolveFast.hist5_go(row, C, gen2, False{},
        SolveFast.Hist5Ok{s1, t1, 0n, 0n, m}),
      Equal.cong(Array<Nat>, SolveFast.Hist5Res,
        x => SolveFast.hist5_go(row, C, gen2, False{},
               SolveFast.Hist5Ok{x, t2, 0n, 0n, m}), s2, s1, es2),
      Equal.cong(Array<U32>, SolveFast.Hist5Res,
        y => SolveFast.hist5_go(row, C, gen2, False{},
               SolveFast.Hist5Ok{s1, y, 0n, 0n, m}), t2, t1, et2))
  +hhr1 : FH.FH.HistSpec(g1, SolveFast.cwords_words(C), Nil{}, gen2, m,
      False{}, tbl, SolveFast.hist5_go(row, C, gen2, False{},
        SolveFast.Hist5Ok{s1, t1, 0n, 0n, m})) =
    FH.FH.hist_spec_transport(g1, SolveFast.cwords_words(C), Nil{}, gen2, m,
      False{}, tbl,
      SolveFast.hist5_go(row, C, gen2, False{},
        SolveFast.Hist5Ok{s2, t2, 0n, 0n, m}),
      SolveFast.hist5_go(row, C, gen2, False{},
        SolveFast.Hist5Ok{s1, t1, 0n, 0n, m}), eq12, hhr_t)
  %es1 : CK.LoopOk(G, Croot, n_root, ws, t,
           SolveFast.ck_loop(p, Nat.add(1n, i), C, gen2, m, kmax2,
             SolveFast.hist5_go(row, C, gen2, False{},
               SolveFast.Hist5Ok{_, tbl, 0n, 0n, m}),
             Nat.is_le(2n, p)))
  %et1 : CK.LoopOk(G, Croot, n_root, ws, t,
           SolveFast.ck_loop(p, Nat.add(1n, i), C, gen2, m, kmax2,
             SolveFast.hist5_go(row, C, gen2, False{},
               SolveFast.Hist5Ok{s1, _, 0n, 0n, m}),
             Nat.is_le(2n, p)))
  CK.take_hist(
    h2 => CK.LoopOk(G, Croot, n_root, ws, t,
      SolveFast.ck_loop(p, Nat.add(1n, i), C, gen2, m, kmax2, h2,
        Nat.is_le(2n, p))),
    G, Croot, ws, n_root, Nat.add(1n, i), gen2, m, g1,
    SolveFast.cwords_words(C), tbl, ew, {==}, hm, htbl,
    SolveFast.hist5_go(row, C, gen2, False{},
      SolveFast.Hist5Ok{s1, t1, 0n, 0n, m}),
    hhr1,
    h2 => hh2 => rec(Nat.add(1n, i), gen2, kmax2, h2, hh2, ht2, hk2))

# The scan induction. `t` is `i + fuel` at entry and does not change.
def CK.ck_loop_spec(+fuel: Nat, +i: Nat, +C: +List<SolveFast.CWord>,
    +gen: Nat, +m: Nat, +kmax: Nat, hist: SolveFast.Hist5Res, more: Bool,
    +G: +List<+List<Nat>>, +Croot: +List<+List<Nat>>, +n_root: Nat,
    +ws: +List<+List<Nat>>, +t: Nat,
    +ew: {SolveFast.cwords_words(C) == ws : +List<+List<Nat>>},
    +hS: {FT.FT.cwords_ok_b(G, Croot, n_root, C) == True{} : Bool},
    +hm: {m == Groups.len_words(ws) : Nat},
    +ht: {Nat.add(i, fuel) == t : Nat},
    +hi: {Nat.is_le(t, Groups.len_words(G)) == True{} : Bool},
    +hmr: {more == Nat.is_le(2n, fuel) : Bool},
    +hk: {Nat.is_le(CK.prefmax(G, ws, i), kmax) == True{} : Bool},
    +hh: CK.HistEntry(G, Croot, n_root, ws, i, gen, hist)) ->
  CK.LoopOk(G, Croot, n_root, ws, t,
    SolveFast.ck_loop(fuel, i, C, gen, m, kmax, hist, more)):
  match fuel:
    case 0n:
      match hist:
        case SolveFast.Hist5Pruned{seen, tbl}:
          Empty.absurd(
            CK.LoopOk(G, Croot, n_root, ws, t,
              SolveFast.ck_loop(0n, i, C, gen, m, kmax,
                SolveFast.Hist5Pruned{seen, tbl}, more)), hh)
        case SolveFast.Hist5Ok{seen, tbl, +m2, +k2, budget}:
          +hh1 = Arr.Arr.dpair_l(FT.FT.TblOk(G, Croot, n_root, tbl),
                    Arr.Arr.DPair<FH.FH.SeenTree(10n, 0, seen, gen,
                        SolveFast.fgroups_build_fast(FT.FT.nth_word(G, i), ws,
                          Nil{})),
                      {Nat.is_le(CK.count(FT.FT.nth_word(G, i), ws), k2)
                       == True{} : Bool}>, hh)
          +htbl = Arr.Arr.dpair_l(FT.FT.TblOk(G, Croot, n_root, tbl),
                    Arr.Arr.DPair<FH.FH.SeenTree(10n, 0, seen, gen,
                        SolveFast.fgroups_build_fast(FT.FT.nth_word(G, i), ws,
                          Nil{})),
                      {Nat.is_le(CK.count(FT.FT.nth_word(G, i), ws), k2)
                       == True{} : Bool}>, hh)
          +e0 : {Nat.add(i, 0n) == t : Nat} = ht
          +ei : {CK.prefmax(G, ws, i) == CK.prefmax(G, ws, Nat.add(i, 0n))
                 : Nat} =
            Equal.cong(Nat, Nat, x => CK.prefmax(G, ws, x),
              i, Nat.add(i, 0n),
              Equal.sym(Nat, Nat.add(i, 0n), i, NatProof.NatPrf.add_zero(i)))
          +hk2 : {Nat.is_le(CK.prefmax(G, ws, Nat.add(i, 0n)), kmax)
                  == True{} : Bool} =
            NatProof.Nat.is_le_eq_l(kmax, CK.prefmax(G, ws, i),
              CK.prefmax(G, ws, Nat.add(i, 0n)), ei, hk)
          +hleK : {Nat.is_le(CK.prefmax(G, ws, t), kmax) == True{} : Bool} =
            NatProof.Nat.is_le_eq_l(kmax,
              CK.prefmax(G, ws, Nat.add(i, 0n)), CK.prefmax(G, ws, t),
              Equal.cong(Nat, Nat, x => CK.prefmax(G, ws, x),
                Nat.add(i, 0n), t, e0),
              hk2)
          +hgoal : {Nat.is_le(CK.prefmax(G, ws, t), Nat.max(kmax, k2))
                    == True{} : Bool} =
            NatProof.Nat.is_le_trans(CK.prefmax(G, ws, t), kmax,
              Nat.max(kmax, k2), hleK, CK.le_max_l(kmax, k2))
          Arr.DPair{htbl, hgoal}
    case 1n+p:
      match hist:
        case SolveFast.Hist5Pruned{seen, tbl}:
          Empty.absurd(
            CK.LoopOk(G, Croot, n_root, ws, t,
              SolveFast.ck_loop(1n+p, i, C, gen, m, kmax,
                SolveFast.Hist5Pruned{seen, tbl}, more)), hh)
        case SolveFast.Hist5Ok{seen, tbl, +m2, +k2, budget}:
          match more:
            case False{}:
              match hh:
                case Arr.DPair{htbl, r1}:
                  match r1:
                    case Arr.DPair{hsE, hc}:
                      +hle2 : {Nat.is_le(2n, 1n+p) == False{} : Bool} =
                        Equal.trans(Bool, Nat.is_le(2n, 1n+p), more, False{},
                          Equal.sym(Bool, more, Nat.is_le(2n, 1n+p), hmr), {==})
                      +ep : {p == 0n : Nat} = CK.pred_zero(p, hle2)
                      +hpre : {Nat.is_le(CK.prefmax(G, ws, Nat.add(1n, i)),
                                Nat.max(kmax, k2)) == True{} : Bool} =
                        CK.prefmax_succ(G, ws, i, kmax, k2, hk, hc)
                      +ep2 : {Nat.add(i, p) == i : Nat} =
                        Equal.trans(Nat, Nat.add(i, p), Nat.add(i, 0n), i,
                          Equal.cong(Nat, Nat, x => Nat.add(i, x), p, 0n, ep),
                          NatProof.NatPrf.add_zero(i))
                      +eA : {Nat.add(i, 1n+p)
                             == Nat.add(1n, Nat.add(i, p)) : Nat} =
                        NatProof.NatPrf.add_succ(i, p)
                      +eB : {Nat.add(1n, Nat.add(i, p)) == Nat.add(1n, i)
                             : Nat} =
                        Equal.cong(Nat, Nat, x => Nat.add(1n, x),
                          Nat.add(i, p), i, ep2)
                      +e2 : {Nat.add(i, 1n+p) == Nat.add(1n, i) : Nat} =
                        Equal.trans(Nat, Nat.add(i, 1n+p),
                          Nat.add(1n, Nat.add(i, p)), Nat.add(1n, i), eA, eB)
                      +hgoal : {Nat.is_le(CK.prefmax(G, ws, t),
                                 Nat.max(kmax, k2)) == True{} : Bool} =
                        NatProof.Nat.is_le_eq_l(Nat.max(kmax, k2),
                          CK.prefmax(G, ws, Nat.add(1n, i)),
                          CK.prefmax(G, ws, t),
                          Equal.cong(Nat, Nat, x => CK.prefmax(G, ws, x),
                            Nat.add(1n, i), t,
                            Equal.trans(Nat, Nat.add(1n, i),
                              Nat.add(i, 1n+p), t,
                              Equal.sym(Nat, Nat.add(i, 1n+p),
                                Nat.add(1n, i), e2), ht)),
                          hpre)
                      Arr.DPair{htbl, hgoal}
            case True{}:
              match hh:
                case Arr.DPair{htbl, r1}:
                  match r1:
                    case Arr.DPair{hsE, hc}:
                      +hle2 : {Nat.is_le(2n, 1n+p) == True{} : Bool} =
                        Equal.trans(Bool, Nat.is_le(2n, 1n+p), more, True{},
                          Equal.sym(Bool, more, Nat.is_le(2n, 1n+p), hmr), {==})
                      +hle1 : {Nat.is_le(1n, p) == True{} : Bool} =
                        NatProof.Nat.is_le_succ_inv(1n, p, hle2)
                      +hk2 : {Nat.is_le(CK.prefmax(G, ws, Nat.add(1n, i)),
                                Nat.max(kmax, k2)) == True{} : Bool} =
                        CK.prefmax_succ(G, ws, i, kmax, k2, hk, hc)
                      +hsucc2a : {Nat.is_le(Nat.add(2n, i),
                                   Nat.add(Nat.add(1n, p), i))
                                  == True{} : Bool} =
                        NatProof.Nat.is_le_add_r(2n, Nat.add(1n, p), i, hle2)
                      +hsucc2 : {Nat.is_le(Nat.add(2n, i),
                                  Nat.add(i, Nat.add(1n, p)))
                                 == True{} : Bool} =
                        NatProof.Nat.is_le_eq_r(Nat.add(2n, i),
                          Nat.add(Nat.add(1n, p), i), Nat.add(i, Nat.add(1n, p)),
                          NatProof.NatPrf.add_comm(Nat.add(1n, p), i), hsucc2a)
                      +hsucc : {Nat.is_le(Nat.add(1n, Nat.add(1n, i)),
                                  Groups.len_words(G)) == True{} : Bool} =
                        NatProof.Nat.is_le_trans(Nat.add(1n, Nat.add(1n, i)),
                          Nat.add(i, Nat.add(1n, p)), Groups.len_words(G),
                          NatProof.Nat.is_le_eq_l(Nat.add(i, Nat.add(1n, p)),
                            Nat.add(2n, i), Nat.add(1n, Nat.add(1n, i)),
                            {==}, hsucc2),
                          NatProof.Nat.is_le_eq_l(Groups.len_words(G), t,
                            Nat.add(i, Nat.add(1n, p)),
                            Equal.sym(Nat, Nat.add(i, 1n+p), t, ht), hi))
                      +hrow : {FT.FT.gentry_ok_b(G, n_root,
                                 U32.from_nat(Nat.add(1n, i)),
                                 FT.FT.nth_word(G, Nat.add(1n, i)))
                               == True{} : Bool} =
                        CK.hg_nth(G, n_root, Nat.add(1n, i), 0n, hsucc)
                      +ht2 : {Nat.add(Nat.add(1n, i), p) == t : Nat} =
                        Equal.trans(Nat, Nat.add(Nat.add(1n, i), p),
                          Nat.add(i, Nat.add(1n, p)), t,
                          Equal.sym(Nat, Nat.add(i, Nat.add(1n, p)),
                            Nat.add(Nat.add(1n, i), p), CK.add_rot(i, p)), ht)
                      CK.ck_step(p, i, C, gen, m, kmax, k2,
                        Nat.max(kmax, k2), G, Croot, n_root, ws, t, ew, hS, hm,
                        ht2, hi, hk2, hrow,
                        +i2 => +g2b => +k2b => h2 => hh2 => ht2b => hk2b =>
                          CK.ck_loop_spec(p, i2, C, g2b, m, k2b, h2,
                            Nat.is_le(2n, p), G, Croot, n_root, ws, t, ew,
                            hS, hm, ht2b, hi, {==}, hk2b, hh2),
                seen, tbl, htbl, hsE, CK.dup3(Nat, seen), Arr.Arr.dup(U32, tbl))


# The scan of `class_k_start`: on a non-empty guess list the first pass is
# already run and the loop consumes it; on an empty list the result is `0`.
def CK.class_k_b_spec(+G: +List<+List<Nat>>, +Croot: +List<+List<Nat>>,
    +ws: +List<+List<Nat>>, +n_root: Nat, +S: +List<SolveFast.CWord>,
    +m: Nat, +gn: Nat, -tbl: Array<U32>,
    +ew: {SolveFast.cwords_words(S) == ws : +List<+List<Nat>>},
    +hS: {FT.FT.cwords_ok_b(G, Croot, n_root, S) == True{} : Bool},
    +hm: {m == Groups.len_words(ws) : Nat},
    +hgn : {gn == Groups.len_words(G) : Nat},
    +htbl: FT.FT.TblOk(G, Croot, n_root, tbl),
    dpt: &t1: Array<U32> -> &t2: Array<U32> ->
         {t1 == tbl : Array<U32>} & {t2 == t1 : Array<U32>}) ->
  CK.LoopOk(G, Croot, n_root, ws, gn,
    SolveFast.class_k_start_b(Nat.is_le(gn, 0n), S, m, gn, tbl)):
  match gn:
    case 0n:
      Arr.DPair{htbl, NatProof.Nat.is_le_refl(0n)}
    case 1n+p:
      (t1, dpt2) = dpt
      (t2, pet) = dpt2
      (+et1, +et2) = pet
      +et2_t : {t2 == tbl : Array<U32>} =
        Equal.trans(Array<U32>, t2, t1, tbl, et2, et1)
      +hb1 : {Nat.is_le(1n, 1n+p) == True{} : Bool} =
        NatProof.Nat.is_le_succ(0n, p, NatProof.Nat.is_le_zero_l(p))
      +hb : {Nat.is_le(1n, Groups.len_words(G)) == True{} : Bool} =
        NatProof.Nat.is_le_eq_r(1n, 1n+p, Groups.len_words(G), hgn, hb1)
      +hrow0 : {FT.FT.gentry_ok_b(G, n_root, 0, FT.FT.nth_word(G, 0n))
                == True{} : Bool} =
        CK.hg_nth(G, n_root, 0n, 0n, hb)
      +ht2ok : FT.FT.TblOk(G, Croot, n_root, t2) =
        FT.FT.tbl_ok_transport(G, Croot, n_root, tbl, t2,
          Equal.sym(Array<U32>, t2, tbl, et2_t), htbl)
      +hhr2 : FH.FH.HistSpec(FT.FT.nth_word(G, 0n),
          SolveFast.cwords_words(S), Nil{}, 1n, m, False{}, t2,
          SolveFast.hist5_go(0, S, 1n, False{},
            SolveFast.Hist5Ok{Array.new(Nat, 10n, 0n), t2, 0n, 0n, m})) =
        FH.FH.hist5_go_spec(S, G, Croot, n_root, 0, FT.FT.nth_word(G, 0n),
          Nil{}, Array.new(Nat, 10n, 0n), t2, 1n, 0n, 0n, m, m, False{},
          ht2ok, hrow0, hS, {==}, CK.wf_nil(), {==}, {==},
          FH.FH.seen_tree_new(10n, 0))
      +hhr_t : FH.FH.HistSpec(FT.FT.nth_word(G, 0n),
          SolveFast.cwords_words(S), Nil{}, 1n, m, False{}, tbl,
          SolveFast.hist5_go(0, S, 1n, False{},
            SolveFast.Hist5Ok{Array.new(Nat, 10n, 0n), t2, 0n, 0n, m})) =
        FH.FH.hist_spec_transport_tbl(FT.FT.nth_word(G, 0n),
          SolveFast.cwords_words(S), Nil{}, 1n, m, False{}, t2, tbl,
          SolveFast.hist5_go(0, S, 1n, False{},
            SolveFast.Hist5Ok{Array.new(Nat, 10n, 0n), t2, 0n, 0n, m}),
          et2_t, hhr2)
      +eq12 : {SolveFast.hist5_go(0, S, 1n, False{},
                  SolveFast.Hist5Ok{Array.new(Nat, 10n, 0n), t2, 0n, 0n, m})
               == SolveFast.hist5_go(0, S, 1n, False{},
                    SolveFast.Hist5Ok{Array.new(Nat, 10n, 0n), t1, 0n, 0n, m})
               : SolveFast.Hist5Res} =
        Equal.cong(Array<U32>, SolveFast.Hist5Res,
          y => SolveFast.hist5_go(0, S, 1n, False{},
                 SolveFast.Hist5Ok{Array.new(Nat, 10n, 0n), y, 0n, 0n, m}),
          t2, t1, et2)
      +hhr1 : FH.FH.HistSpec(FT.FT.nth_word(G, 0n),
          SolveFast.cwords_words(S), Nil{}, 1n, m, False{}, tbl,
          SolveFast.hist5_go(0, S, 1n, False{},
            SolveFast.Hist5Ok{Array.new(Nat, 10n, 0n), t1, 0n, 0n, m})) =
        FH.FH.hist_spec_transport(FT.FT.nth_word(G, 0n),
          SolveFast.cwords_words(S), Nil{}, 1n, m, False{}, tbl,
          SolveFast.hist5_go(0, S, 1n, False{},
            SolveFast.Hist5Ok{Array.new(Nat, 10n, 0n), t2, 0n, 0n, m}),
          SolveFast.hist5_go(0, S, 1n, False{},
            SolveFast.Hist5Ok{Array.new(Nat, 10n, 0n), t1, 0n, 0n, m}),
          eq12, hhr_t)
      %et1 : CK.LoopOk(G, Croot, n_root, ws, gn,
               SolveFast.ck_loop(gn, 0n, S, 1n, m, 0n,
                 SolveFast.hist5_go(0, S, 1n, False{},
                   SolveFast.Hist5Ok{Array.new(Nat, 10n, 0n), _, 0n, 0n, m}),
                 Nat.is_le(2n, gn)))
      CK.take_hist(
        h2 => CK.LoopOk(G, Croot, n_root, ws, gn,
          SolveFast.ck_loop(gn, 0n, S, 1n, m, 0n, h2, Nat.is_le(2n, gn))),
        G, Croot, ws, n_root, 0n, 1n, m, FT.FT.nth_word(G, 0n),
        SolveFast.cwords_words(S), tbl, ew, {==}, hm, htbl,
        SolveFast.hist5_go(0, S, 1n, False{},
          SolveFast.Hist5Ok{Array.new(Nat, 10n, 0n), t1, 0n, 0n, m}),
        hhr1,
        h2 => hh2 =>
          CK.ck_loop_spec(gn, 0n, S, 1n, m, 0n, h2, Nat.is_le(2n, gn),
            G, Croot, n_root, ws, gn, ew, hS, hm, {==},
            NatProof.Nat.is_le_eq_r(gn, gn, Groups.len_words(G), hgn,
              NatProof.Nat.is_le_refl(gn)),
            {==}, NatProof.Nat.is_le_zero_l(0n), hh2))

# The scan result covers `prefmax` over the whole guess list.
def CK.class_k_spec(+G: +List<+List<Nat>>, +Croot: +List<+List<Nat>>,
    +ws: +List<+List<Nat>>, +n_root: Nat, +S: +List<SolveFast.CWord>,
    +m: Nat, +gn: Nat, -tbl: Array<U32>,
    +ew: {SolveFast.cwords_words(S) == ws : +List<+List<Nat>>},
    +hS: {FT.FT.cwords_ok_b(G, Croot, n_root, S) == True{} : Bool},
    +hm: {m == Groups.len_words(ws) : Nat},
    +hgn : {gn == Groups.len_words(G) : Nat},
    +htbl: FT.FT.TblOk(G, Croot, n_root, tbl),
    dpt: &t1: Array<U32> -> &t2: Array<U32> ->
         {t1 == tbl : Array<U32>} & {t2 == t1 : Array<U32>}) ->
  CK.LoopOk(G, Croot, n_root, ws, gn,
    SolveFast.class_k_start(S, m, gn, tbl)):
  CK.class_k_b_spec(G, Croot, ws, n_root, S, m, gn, tbl, ew, hS, hm, hgn,
    htbl, dpt)
