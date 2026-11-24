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

# ---------------------------------------------------------------------------
# Obligation B: the class branching factor counted by `class_k_start`
# ---------------------------------------------------------------------------
#
# `class_k_start` scans the guess list once per guess with the already proved
# histogram fold `FH.hist5_go`, so the `k` of one pass is `FH.hist5_go_spec`'s
# number of feedback groups of that guess on the class. `CK.ck_loop_spec` folds
# the maximum over the guesses, and `CK.class_k_start_spec` states the result:
# `k` bounds `CK.prefmax`, the largest number of feedback classes any guess of
# the whole guess list produces on the class. Nothing here is assumed.

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
def CK.max_le(a: Nat, b: Nat, c: Nat,
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

# `a <= a + b`.
def CK.le_self_add(a: Nat, +b: Nat) ->
  {Nat.is_le(a, Nat.add(a, b)) == True{} : Bool}:
  match b:
    case 0n:
      NatProof.Nat.is_le_eq_r(a, a, Nat.add(a, 0n),
        Equal.sym(Nat, Nat.add(a, 0n), a, NatProof.NatPrf.add_zero(a)),
        NatProof.Nat.is_le_refl(a))
    case 1n+bp:
      +ih : {Nat.is_le(a, Nat.add(a, bp)) == True{} : Bool} =
        CK.le_self_add(a, bp)
      +hlt : {Nat.is_lt(Nat.add(a, bp), Nat.add(a, 1n+bp)) == True{} : Bool} =
        NatProof.Nat.is_lt_succ_self(Nat.add(a, bp))
      NatProof.Nat.is_le_trans(a, Nat.add(a, bp), Nat.add(a, 1n+bp), ih,
        NatProof.Nat.is_le_of_lt(Nat.add(a, bp), Nat.add(a, 1n+bp), hlt))

# `a + (1 + b) = (1 + a) + b`.
def CK.add_rot(a: Nat, +b: Nat) ->
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
      +ih : {Nat.is_le(CK.prefmax(G, ws, p),
                       CK.prefmax(G, ws, Nat.add(1n, p))) == True{} : Bool} =
        CK.prefmax_mono(G, ws, p)
      +hle : {Nat.is_le(CK.prefmax(G, ws, p),
                        Nat.max(CK.count(FT.FT.nth_word(G, p), ws),
                          CK.prefmax(G, ws, p))) == True{} : Bool} =
        NatProof.Nat.max_ge_r(CK.count(FT.FT.nth_word(G, p), ws),
          CK.prefmax(G, ws, p))
      NatProof.Nat.is_le_trans(CK.prefmax(G, ws, 1n+p),
        Nat.max(CK.count(FT.FT.nth_word(G, p), ws), CK.prefmax(G, ws, p)),
        CK.prefmax(G, ws, Nat.add(1n, 1n+p)), hle, ih)

# `prefmax i <= prefmax (i + fuel)`.
def CK.prefmax_le_add(+G: +List<+List<Nat>>, +ws: +List<+List<Nat>>,
    +i: Nat, +fuel: Nat) ->
  {Nat.is_le(CK.prefmax(G, ws, i), CK.prefmax(G, ws, Nat.add(i, fuel)))
   == True{} : Bool}:
  match fuel:
    case 0n:
      NatProof.Nat.is_le_eq_r(CK.prefmax(G, ws, i), CK.prefmax(G, ws, i),
        CK.prefmax(G, ws, Nat.add(i, 0n)),
        Equal.cong(Nat, Nat, x => CK.prefmax(G, ws, x), Nat.add(i, 0n), i,
          NatProof.NatPrf.add_zero(i)),
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
      NatProof.Nat.is_le_eq_r(CK.prefmax(G, ws, i),
        CK.prefmax(G, ws, Nat.add(1n, Nat.add(i, p))),
        CK.prefmax(G, ws, Nat.add(i, Nat.add(1n, p))),
        Equal.cong(Nat, Nat, x => CK.prefmax(G, ws, x),
          Nat.add(i, Nat.add(1n, p)), Nat.add(1n, Nat.add(i, p)),
          NatProof.NatPrf.add_comm(i, Nat.add(1n, p))),
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
  +hle : {Nat.is_le(Nat.add(1n, Nat.add(m, FH.fgroups_count(fg1))),
          FH.fgroups_total(fg1)) == True{} : Bool} = h
  +etot : {FH.fgroups_total(fg1) == SolveFast.keep_fast(g, ws) : Nat} =
    Equal.trans(Nat, FH.fgroups_total(fg1),
      Nat.add(SolveFast.keep_fast(g, ws), FH.fgroups_total(Nil{})),
      SolveFast.keep_fast(g, ws),
      FH.fgroups_build_total_eq_keep(g, ws, Nil{}),
      NatProof.NatPrf.add_zero(SolveFast.keep_fast(g, ws)))
  +hkeep : {Nat.is_le(SolveFast.keep_fast(g, ws), m) == True{} : Bool} =
    NatProof.Nat.is_le_eq_r(SolveFast.keep_fast(g, ws),
      Groups.len_words(ws), m, Equal.sym(Nat, m, Groups.len_words(ws), hm),
      CK.keep_le_len(g, ws))
  +hlem : {Nat.is_le(Nat.add(1n, Nat.add(m, FH.fgroups_count(fg1))), m)
           == True{} : Bool} =
    NatProof.Nat.is_le_trans(
      Nat.add(1n, Nat.add(m, FH.fgroups_count(fg1))),
      FH.fgroups_total(fg1), m, hle,
      NatProof.Nat.is_le_eq_r(SolveFast.keep_fast(g, ws),
        FH.fgroups_total(fg1), m,
        Equal.sym(Nat, m, FH.fgroups_total(fg1),
          Equal.trans(Nat, FH.fgroups_total(fg1), SolveFast.keep_fast(g, ws),
            m, etot, Equal.sym(Nat, m, SolveFast.keep_fast(g, ws), hkeep))),
        hkeep))
  +hsucc : {Nat.is_le(Nat.add(1n, m), Nat.add(1n, Nat.add(m,
              FH.fgroups_count(fg1)))) == True{} : Bool} =
    NatProof.Nat.is_le_add_l(m, Nat.add(m, FH.fgroups_count(fg1)), 1n,
      CK.le_self_add(m, FH.fgroups_count(fg1)))
  +hfinal : {Nat.is_le(Nat.add(1n, m), m) == True{} : Bool} =
    NatProof.Nat.is_le_trans(Nat.add(1n, m),
      Nat.add(1n, Nat.add(m, FH.fgroups_count(fg1))), m, hsucc, hlem)
  +hfalse : {Nat.is_le(Nat.add(1n, m), m) == False{} : Bool} =
    CK.not_le_of_lt(m, Nat.add(1n, m), NatProof.Nat.is_lt_succ_self(m))
  Logic.Proof.false_ne_true(
    Equal.trans(Bool, True{}, Nat.is_le(Nat.add(1n, m), m), False{},
      Equal.sym(Bool, Nat.is_le(Nat.add(1n, m), m), True{}, hfinal), hfalse))

# The loop's hypothesis: the table is valid, the scratch array is stamped for
# `gen`, and `count` of the current guess is at most `k`.
def CK.HistEntry(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n_root: Nat,
    +ws: +List<+List<Nat>>, +i: Nat, +gen: Nat,
    hist: SolveFast.Hist5Res) -> Data:
  match hist:
    case SolveFast.Hist5Pruned{seen, tbl}:
      Empty
    case SolveFast.Hist5Ok{seen, tbl, m, k, budget}:
      Arr.Arr.DPair<FT.FT.TblOk(G, C, n_root, tbl),
        Arr.Arr.DPair<FH.FH.SeenTree(10n, 0, seen, gen, Nil{}),
          {Nat.is_le(CK.count(FT.FT.nth_word(G, i), ws), k)
           == True{} : Bool}>>

# The loop's postcondition: the table is valid and `k` covers `prefmax t`.
def CK.LoopOk(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n_root: Nat,
    +ws: +List<+List<Nat>>, +t: Nat, r: SolveFast.CKRes) -> Data:
  match r:
    case SolveFast.CKRes{seen, tbl, k}:
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
      Nat.max(kmax, k2), hc, NatProof.Nat.max_ge_r(kmax, k2)),
    NatProof.Nat.is_le_trans(CK.prefmax(G, ws, i), kmax,
      Nat.max(kmax, k2), hk, NatProof.Nat.max_ge_l(kmax, k2)))

# The recursive call the scan makes after one guess, as a function of the next
# histogram result: the proof of `NextOk` is what the continuation returns.
def CK.NextOk(+p: Nat, +i: Nat, +C: +List<SolveFast.CWord>, +gen: Nat,
    +m: Nat, +kmax: Nat, +G: +List<+List<Nat>>, +Croot: +List<+List<Nat>>,
    +n_root: Nat, +ws: +List<+List<Nat>>, +t: Nat,
    hist: SolveFast.Hist5Res) -> Data:
  CK.LoopOk(G, Croot, n_root, ws, t,
    SolveFast.ck_loop(p, Nat.add(1n, i), C, Nat.add(1n, gen), m, kmax, hist,
      Nat.is_le(2n, p)))

# Consume one histogram result. `hist` and its specification are parameters, so
# the branches can read them; the continuation receives the rebuilt result and
# its entry invariant, which are the hypotheses of the recursive call.
def CK.take_hist(-R: SolveFast.Hist5Res -> Data,
    +G: +List<+List<Nat>>, +Croot: +List<+List<Nat>>,
    +ws: +List<+List<Nat>>, +n_root: Nat, +i: Nat, +gen: Nat, +m: Nat,
    +g: +List<Nat>, +S: +List<+List<Nat>>, tbl0: Array<U32>,
    +ew: {S == ws : +List<+List<Nat>>},
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
              Empty.absurd(R(SolveFast.Hist5Pruned{seen3, tbl3}),
                CK.prune_impossible(g, S, m,
                  Equal.trans(Nat, m, Groups.len_words(ws), Groups.len_words(S),
                    hm, Equal.cong(+List<+List<Nat>>, Nat, Groups.len_words, ws, S,
                      Equal.sym(+List<+List<Nat>>, S, ws, ew))),
                  hpr))
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
                          +htbl3 = FT.FT.tbl_ok_transport(G, Croot, n_root,
                                     tbl0, tbl3,
                                     Equal.sym(Array<U32>, tbl3, tbl0, et3),
                                     htbl0)
                          +efg : {CK.count(g, S) == CK.count(g, ws) : Nat} =
                            Equal.cong(+List<+List<Nat>>, Nat,
                              w => FH.FH.fgroups_count(
                                SolveFast.fgroups_build_fast(g, w, Nil{})),
                              S, ws, ew)
                          +hc0 : {Nat.is_le(CK.count(g, S), k3)
                                  == True{} : Bool} =
                            NatProof.Nat.is_le_eq_r(CK.count(g, S),
                              CK.count(g, S), k3, hk3,
                              NatProof.Nat.is_le_refl(CK.count(g, S)))
                          +hc1 : {Nat.is_le(CK.count(g, ws), k3)
                                  == True{} : Bool} =
                            NatProof.Nat.is_le_eq_l(k3, CK.count(g, S),
                              CK.count(g, ws), efg, hc0)
                          kont(SolveFast.Hist5Ok{seen3, tbl3, m3, k3, b3},
                            Arr.DPair{htbl3, Arr.DPair{hs3, hc1}})

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
          +r1 = Arr.Arr.dpair_l(FT.FT.TblOk(G, Croot, n_root, tbl),
                  Arr.Arr.DPair<FH.FH.SeenTree(10n, 0, seen, gen, Nil{}),
                    {Nat.is_le(CK.count(FT.FT.nth_word(G, i), ws), k2)
                     == True{} : Bool}>, hh)
          +r2 = Arr.Arr.dpair_r(FT.FT.TblOk(G, Croot, n_root, tbl),
                  Arr.Arr.DPair<FH.FH.SeenTree(10n, 0, seen, gen, Nil{}),
                    {Nat.is_le(CK.count(FT.FT.nth_word(G, i), ws), k2)
                     == True{} : Bool}>, hh)
          +htbl = Arr.Arr.dpair_l(FT.FT.TblOk(G, Croot, n_root, tbl),
                    Arr.Arr.DPair<FH.FH.SeenTree(10n, 0, seen, gen, Nil{}),
                      {Nat.is_le(CK.count(FT.FT.nth_word(G, i), ws), k2)
                       == True{} : Bool}>, r1)
          +r3 = Arr.Arr.dpair_r(FH.FH.SeenTree(10n, 0, seen, gen, Nil{}),
                  {Nat.is_le(CK.count(FT.FT.nth_word(G, i), ws), k2)
                   == True{} : Bool}, r2)
          +hc = Arr.Arr.dpair_r(FH.FH.SeenTree(10n, 0, seen, gen, Nil{}),
                 {Nat.is_le(CK.count(FT.FT.nth_word(G, i), ws), k2)
                  == True{} : Bool}, r3)
          +hpre : {Nat.is_le(CK.prefmax(G, ws, Nat.add(1n, i)),
                    Nat.max(kmax, k2)) == True{} : Bool} =
            CK.prefmax_succ(G, ws, i, kmax, k2, hk, hc)
          +hidx : {Nat.add(1n, i) == t : Nat} =
            Equal.trans(Nat, Nat.add(1n, i), Nat.add(i, 0n), t,
              NatProof.NatPrf.add_comm(1n, i),
              Equal.trans(Nat, Nat.add(i, 0n), Nat.add(i, 0n), t, {==}, ht))
          +hgoal : {Nat.is_le(CK.prefmax(G, ws, t), Nat.max(kmax, k2))
                    == True{} : Bool} =
            NatProof.Nat.is_le_eq_l(Nat.max(kmax, k2),
              CK.prefmax(G, ws, Nat.add(1n, i)), CK.prefmax(G, ws, t),
              Equal.cong(Nat, Nat, x => CK.prefmax(G, ws, x),
                Nat.add(1n, i), t, hidx), hpre)
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
              +r1 = Arr.Arr.dpair_l(FT.FT.TblOk(G, Croot, n_root, tbl),
                      Arr.Arr.DPair<FH.FH.SeenTree(10n, 0, seen, gen, Nil{}),
                        {Nat.is_le(CK.count(FT.FT.nth_word(G, i), ws), k2)
                         == True{} : Bool}>, hh)
              +r2 = Arr.Arr.dpair_r(FT.FT.TblOk(G, Croot, n_root, tbl),
                      Arr.Arr.DPair<FH.FH.SeenTree(10n, 0, seen, gen, Nil{}),
                        {Nat.is_le(CK.count(FT.FT.nth_word(G, i), ws), k2)
                         == True{} : Bool}>, hh)
              +htbl = Arr.Arr.dpair_l(FT.FT.TblOk(G, Croot, n_root, tbl),
                        Arr.Arr.DPair<FH.FH.SeenTree(10n, 0, seen, gen, Nil{}),
                          {Nat.is_le(CK.count(FT.FT.nth_word(G, i), ws), k2)
                           == True{} : Bool}>, r1)
              +r3 = Arr.Arr.dpair_r(FH.FH.SeenTree(10n, 0, seen, gen, Nil{}),
                      {Nat.is_le(CK.count(FT.FT.nth_word(G, i), ws), k2)
                       == True{} : Bool}, r2)
              +hc = Arr.Arr.dpair_r(FH.FH.SeenTree(10n, 0, seen, gen, Nil{}),
                     {Nat.is_le(CK.count(FT.FT.nth_word(G, i), ws), k2)
                      == True{} : Bool}, r3)
              +hpre : {Nat.is_le(CK.prefmax(G, ws, Nat.add(1n, i)),
                        Nat.max(kmax, k2)) == True{} : Bool} =
                CK.prefmax_succ(G, ws, i, kmax, k2, hk, hc)
              +ep : {p == 0n : Nat} =
                CK.pred_zero(p,
                  Equal.trans(Bool, Nat.is_le(2n, Nat.add(1n, p)), more,
                    False{},
                    Equal.sym(Bool, more, Nat.is_le(2n, Nat.add(1n, p)), hmr),
                    {==}))
              +hidx : {Nat.add(1n, i) == t : Nat} =
                Equal.trans(Nat, Nat.add(1n, i), Nat.add(i, 1n), t,
                  NatProof.NatPrf.add_comm(1n, i),
                  Equal.trans(Nat, Nat.add(i, 1n),
                    Nat.add(i, Nat.add(1n, p)), t,
                    Equal.cong(Nat, Nat, x => Nat.add(i, x), 1n,
                      Nat.add(1n, p), ep),
                    ht))
              +hgoal : {Nat.is_le(CK.prefmax(G, ws, t), Nat.max(kmax, k2))
                        == True{} : Bool} =
                NatProof.Nat.is_le_eq_l(Nat.max(kmax, k2),
                  CK.prefmax(G, ws, Nat.add(1n, i)), CK.prefmax(G, ws, t),
                  Equal.cong(Nat, Nat, x => CK.prefmax(G, ws, x),
                    Nat.add(1n, i), t, hidx), hpre)
              Arr.DPair{htbl, hgoal}
            case True{}:
              +r1 = Arr.Arr.dpair_l(FT.FT.TblOk(G, Croot, n_root, tbl),
                      Arr.Arr.DPair<FH.FH.SeenTree(10n, 0, seen, gen, Nil{}),
                        {Nat.is_le(CK.count(FT.FT.nth_word(G, i), ws), k2)
                         == True{} : Bool}>, hh)
              +r2 = Arr.Arr.dpair_r(FT.FT.TblOk(G, Croot, n_root, tbl),
                      Arr.Arr.DPair<FH.FH.SeenTree(10n, 0, seen, gen, Nil{}),
                        {Nat.is_le(CK.count(FT.FT.nth_word(G, i), ws), k2)
                         == True{} : Bool}>, hh)
              +htbl = Arr.Arr.dpair_l(FT.FT.TblOk(G, Croot, n_root, tbl),
                        Arr.Arr.DPair<FH.FH.SeenTree(10n, 0, seen, gen, Nil{}),
                          {Nat.is_le(CK.count(FT.FT.nth_word(G, i), ws), k2)
                           == True{} : Bool}>, r1)
              +r3 = Arr.Arr.dpair_r(FH.FH.SeenTree(10n, 0, seen, gen, Nil{}),
                      {Nat.is_le(CK.count(FT.FT.nth_word(G, i), ws), k2)
                       == True{} : Bool}, r2)
              +hs0 = Arr.Arr.dpair_l(FH.FH.SeenTree(10n, 0, seen, gen, Nil{}),
                       {Nat.is_le(CK.count(FT.FT.nth_word(G, i), ws), k2)
                        == True{} : Bool}, r3)
              +hc = Arr.Arr.dpair_r(FH.FH.SeenTree(10n, 0, seen, gen, Nil{}),
                     {Nat.is_le(CK.count(FT.FT.nth_word(G, i), ws), k2)
                      == True{} : Bool}, r3)
              +hle2 : {Nat.is_le(2n, Nat.add(1n, p)) == True{} : Bool} =
                Equal.trans(Bool, Nat.is_le(2n, Nat.add(1n, p)), more, True{},
                  Equal.sym(Bool, more, Nat.is_le(2n, Nat.add(1n, p)), hmr),
                  {==})
              +hle1 : {Nat.is_le(1n, p) == True{} : Bool} =
                NatProof.Nat.is_le_succ_inv(1n, p, hle2)
              # The next guess index stays inside the guess list.
              +hsucc : {Nat.is_le(1n, Nat.add(1n, p)) == True{} : Bool} =
                NatProof.Nat.is_le_eq_r(1n, 1n, Nat.add(1n, p),
                  Equal.sym(Nat, Nat.add(1n, p), 1n, hle1),
                  NatProof.Nat.is_le_refl(1n))
              +hi2 : {Nat.is_le(Nat.add(1n, i), t) == True{} : Bool} =
                NatProof.Nat.is_le_eq_r(Nat.add(1n, i),
                  Nat.add(Nat.add(1n, i), p), t,
                  Equal.trans(Nat, Nat.add(Nat.add(1n, i), p),
                    Nat.add(i, Nat.add(1n, p)), t,
                    CK.add_rot(i, p),
                    Equal.sym(Nat, t, Nat.add(i, Nat.add(1n, p)), ht)),
                  NatProof.Nat.is_le_add_r(Nat.add(1n, i),
                    Nat.add(Nat.add(1n, i), p), 0n,
                    CK.le_self_add(Nat.add(1n, i), p)))
              +hrowg : {FT.FT.gentry_ok_b(G, n_root,
                          U32.from_nat(Nat.add(1n, i)),
                          FT.FT.nth_word(G, Nat.add(1n, i)))
                        == True{} : Bool} =
                CK.hg_nth(G, n_root, Nat.add(1n, i), 0n, hi2)
              (s1, dp2) = Arr.Arr.dup(Nat, seen)
              (s2, pe) = dp2
              (+es1, +es2) = pe
              +hs1 : FH.FH.SeenTree(10n, 0, s1, gen, Nil{}) =
                FH.FH.seen_tree_transport(10n, 0, seen, s1, gen, Nil{},
                  Equal.sym(Array<Nat>, s1, seen, es1), hs0)
              +hs2a : FH.FH.SeenTree(10n, 0, s2, gen, Nil{}) =
                FH.FH.seen_tree_transport(10n, 0, s1, s2, gen, Nil{}, es2, hs1)
              +hs2b : FH.FH.SeenTree(10n, 0, s2, Nat.add(1n, gen), Nil{}) =
                FH.FH.seen_tree_bump(10n, 0, s2, gen, Nil{}, hs2a)
              +hgoal : CK.NextOk(p, i, C, gen, Nat.max(kmax, k2),
                         G, Croot, n_root, ws, t,
                         SolveFast.hist5_go(U32.from_nat(Nat.add(1n, i)), C,
                           Nat.add(1n, gen), False{},
                           SolveFast.Hist5Ok{s2, tbl, 0n, 0n, m})) =
                CK.take_hist(h2 => CK.NextOk(p, i, C, gen, Nat.max(kmax, k2),
                                G, Croot, n_root, ws, t, h2),
                  G, Croot, ws, n_root, Nat.add(1n, i), Nat.add(1n, gen), m,
                  FT.FT.nth_word(G, Nat.add(1n, i)), SolveFast.cwords_words(C),
                  tbl, ew, hm, htbl,
                  SolveFast.hist5_go(U32.from_nat(Nat.add(1n, i)), C,
                    Nat.add(1n, gen), False{},
                    SolveFast.Hist5Ok{s2, tbl, 0n, 0n, m}),
                  FH.FH.hist5_go_spec(C, G, Croot, n_root,
                    U32.from_nat(Nat.add(1n, i)),
                    FT.FT.nth_word(G, Nat.add(1n, i)), Nil{}, s2, tbl,
                    Nat.add(1n, gen), 0n, 0n, m, m, False{},
                    htbl, hrowg, hS, {==}, {==}, {==}, {==}, hs2b),
                  h2 => hh2 =>
                    CK.ck_loop_spec(p, Nat.add(1n, i), C, Nat.add(1n, gen), m,
                      Nat.max(kmax, k2), h2, Nat.is_le(2n, p),
                      G, Croot, n_root, ws, t, ew, hS, hm,
                      Equal.sym(Nat, t, Nat.add(Nat.add(1n, i), p),
                        Equal.trans(Nat, Nat.add(Nat.add(1n, i), p),
                          Nat.add(i, Nat.add(1n, p)), t, CK.add_rot(i, p), ht)),
                      hi, {==},
                      CK.prefmax_succ(G, ws, i, kmax, k2, hk, hc), hh2))
              hgoal

# The initial histogram pass of `class_k_start_b`, taken through `take_hist`.
def CK.start_pass(-R: SolveFast.Hist5Res -> Data,
    +G: +List<+List<Nat>>, +Croot: +List<+List<Nat>>, +ws: +List<+List<Nat>>,
    +n_root: Nat, +S: +List<SolveFast.CWord>, +m: Nat, tbl: Array<U32>,
    +ew: {SolveFast.cwords_words(S) == ws : +List<+List<Nat>>},
    +hS: {FT.FT.cwords_ok_b(G, Croot, n_root, S) == True{} : Bool},
    +hm: {m == Groups.len_words(ws) : Nat},
    +hnonempty: {Nat.is_lt(0n, Groups.len_words(G)) == True{} : Bool},
    +htbl: FT.FT.TblOk(G, Croot, n_root, tbl),
    kont: @h2: SolveFast.Hist5Res ->
          CK.HistEntry(G, Croot, n_root, ws, 0n, 1n, h2) -> R(h2)) ->
  R(SolveFast.hist5_go(0, S, 1n, False{},
      SolveFast.Hist5Ok{Array.new(Nat, 10n, 0n), tbl, 0n, 0n, m})):
  +hrow : {FT.FT.gentry_ok_b(G, n_root, 0, FT.FT.nth_word(G, 0n))
           == True{} : Bool} =
    CK.hg_nth(G, n_root, 0n, 0n, NatProof.Nat.is_le_of_lt(
      0n, Groups.len_words(G), hnonempty))
  CK.take_hist(R, G, Croot, ws, n_root, 0n, 1n, m, FT.FT.nth_word(G, 0n),
    SolveFast.cwords_words(S), tbl, ew, hm, htbl,
    SolveFast.hist5_go(0, S, 1n, False{},
      SolveFast.Hist5Ok{Array.new(Nat, 10n, 0n), tbl, 0n, 0n, m}),
    FH.FH.hist5_go_spec(S, G, Croot, n_root, 0, FT.FT.nth_word(G, 0n), Nil{},
      Array.new(Nat, 10n, 0n), tbl, 1n, 0n, 0n, m, m, False{},
      htbl, hrow, hS, {==}, {==}, {==}, {==},
      FH.FH.seen_tree_new(10n, 0)),
    kont)

# `class_k_start` on a non-empty class and guess list, with the loop's target
# index pinned to `gn`.
def CK.class_k_b_spec(+G: +List<+List<Nat>>, +Croot: +List<+List<Nat>>,
    +ws: +List<+List<Nat>>, +n_root: Nat, +S: +List<SolveFast.CWord>,
    +m: Nat, +gn: Nat, tbl: Array<U32>,
    +ew: {SolveFast.cwords_words(S) == ws : +List<+List<Nat>>},
    +hS: {FT.FT.cwords_ok_b(G, Croot, n_root, S) == True{} : Bool},
    +hm: {m == Groups.len_words(ws) : Nat},
    +hgn : {gn == Groups.len_words(G) : Nat},
    +hpos : {Nat.is_lt(0n, gn) == True{} : Bool},
    +htbl: FT.FT.TblOk(G, Croot, n_root, tbl)) ->
  CK.LoopOk(G, Croot, n_root, ws, gn,
    SolveFast.ck_loop(gn, 0n, S, 1n, m, 0n,
      SolveFast.hist5_go(0, S, 1n, False{},
        SolveFast.Hist5Ok{Array.new(Nat, 10n, 0n), tbl, 0n, 0n, m}),
      Nat.is_le(2n, gn))):
  CK.start_pass(R = h2 => CK.LoopOk(G, Croot, n_root, ws, gn,
      SolveFast.ck_loop(gn, 0n, S, 1n, m, 0n, h2, Nat.is_le(2n, gn))),
    G, Croot, ws, n_root, S, m, tbl, ew, hS, hm,
    NatProof.Nat.is_le_lt_trans(1n, gn, Groups.len_words(G), hpos, 
      NatProof.Nat.is_le_eq_r(1n, gn, Groups.len_words(G), hgn,
        NatProof.Nat.is_le_refl(1n))),
    htbl,
    h2 => hh2 =>
      CK.ck_loop_spec(gn, 0n, S, 1n, m, 0n, h2, Nat.is_le(2n, gn),
        G, Croot, n_root, ws, gn, ew, hS, hm, {==},
        NatProof.Nat.is_le_eq_r(gn, gn, Groups.len_words(G), hgn,
          NatProof.Nat.is_le_refl(gn)),
        {==}, NatProof.Nat.is_le_zero_l(0n), hh2))

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
            Equal.cong(Nat, Bool,
              x => U32.is_eq(U32.from_nat(x), U32.from_nat(cur)),
              Nat.add(cur, 0n), cur, e0,
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
              FT.FT.nth_word(rest, 0n), 1n+cur), hand)
        case 1n+p:
          +hle : {Nat.is_le(Nat.add(1n, p), Groups.len_words(rest))
                  == True{} : Bool} =
            NatProof.Nat.is_le_succ_inv(1n+p, Groups.len_words(rest), h)
          +ih : {FT.FT.has_grow_go(rest, n,
                    U32.from_nat(Nat.add(Nat.add(1n, cur), p)),
                    FT.FT.nth_word(rest, p), Nat.add(1n, cur))
                  == True{} : Bool} =
            CK.hg_nth(rest, n, p, Nat.add(1n, cur), hle)
          +er : {U32.from_nat(Nat.add(cur, 1n+p))
                 == U32.from_nat(Nat.add(Nat.add(1n, cur), p)) : U32} =
            Equal.cong(Nat, U32, x => U32.from_nat(x),
              Nat.add(cur, 1n+p), Nat.add(Nat.add(1n, cur), p),
              CK.add_rot(cur, p))
          +ih2 : {FT.FT.has_grow_go(rest, n,
                     U32.from_nat(Nat.add(cur, 1n+p)),
                     FT.FT.nth_word(rest, p), Nat.add(1n, cur))
                   == True{} : Bool} =
            Equal.cong(U32, Bool,
              r => FT.FT.has_grow_go(rest, n, r, FT.FT.nth_word(rest, p),
                Nat.add(1n, cur)),
              U32.from_nat(Nat.add(Nat.add(1n, cur), p)),
              U32.from_nat(Nat.add(cur, 1n+p)), Equal.sym(U32,
                U32.from_nat(Nat.add(cur, 1n+p)),
                U32.from_nat(Nat.add(Nat.add(1n, cur), p)), er), ih)
          FH.FH.bool_or_r(
            Bool.and(U32.is_eq(U32.from_nat(Nat.add(cur, 1n+p)),
              U32.from_nat(cur)), Feedback.word_eq(w, FT.FT.nth_word(rest, p))),
            FT.FT.has_grow_go(rest, n, U32.from_nat(Nat.add(cur, 1n+p)),
              FT.FT.nth_word(rest, p), Nat.add(1n, cur)), ih2)

# `2 <= fuel` puts the next guess index at most `i + fuel`.
def CK.succ2_le_add(+i: Nat, +fuel: Nat,
    +h: {Nat.is_le(2n, fuel) == True{} : Bool}) ->
  {Nat.is_le(Nat.add(2n, i), Nat.add(i, fuel)) == True{} : Bool}:
  +h1 : {Nat.is_le(Nat.add(2n, i), Nat.add(fuel, i)) == True{} : Bool} =
    NatProof.Nat.is_le_add_r(2n, fuel, i, h)
  +h2 : {Nat.is_le(Nat.add(i, 2n), Nat.add(fuel, i)) == True{} : Bool} =
    NatProof.Nat.is_le_eq_l(Nat.add(fuel, i), Nat.add(2n, i), Nat.add(i, 2n),
      NatProof.NatPrf.add_comm(2n, i), h1)
  NatProof.Nat.is_le_eq_r(Nat.add(i, 2n), Nat.add(fuel, i), Nat.add(i, fuel),
    NatProof.NatPrf.add_comm(fuel, i), h2)
