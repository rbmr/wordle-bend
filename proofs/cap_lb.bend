# The capacity lower bound of a class list.
#
# `src/solve_fast.bend` computes the capacity bound with a truncated sequence
# (`cap_go` keeps `min(n, 1 + k * cap)`), while `proofs/lb_capacity.bend`
# proves the soundness theorem for the untruncated sequence `G`. The first part
# of this module shows that the two functions agree.
import Base
import ../src/solve_fast.bend as SolveFast
import ../src/groups.bend as Groups
import ./logic.bend as Logic
import ./nat.bend as NatProof
import ./min.bend as Min
import ./classbound_nat.bend as CBN
import ./lb_capacity.bend as CapProof
import ./lb_capacity_sound.bend as LBS
import ./cover_list.bend as CoverList
import ./fast_cutoff.bend as FC
import ./fast_hist5.bend as FH
import ./fast_tbl.bend as FT
import ./class_k.bend as CK
import ./class_wid.bend as WK
import ./fast_lb.bend as FLB
import ./fast_step.bend as FStep
import ./fast_nodup.bend as FN
import ./eval.bend as Eval
import ./sat.bend as Sat
import ./mainvalid.bend as MV
import ./solvevalid.bend as SV
import ./classbound_sum.bend as CBS
import ./fast_perm.bend as FP
import ./array.bend as Arr
import ../src/solve_ref.bend as SolveRef
import ../src/tree.bend as Tree
import ./bestok.bend as BO

# ---------------------------------------------------------------------------
# Truncation helpers
# ---------------------------------------------------------------------------

# `min a b == a` when `a <= b`.
def CP.min_eq_l_go(+a: Nat, +b: Nat,
    r: {Nat.min(a, b) == a : Nat} | {Nat.min(a, b) == b : Nat},
    h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.min(a, b) == a : Nat}:
  match r:
    case Inl{e}:
      e
    case Inr{+e2}:
      +hba : {Nat.is_le(b, a) == True{} : Bool} =
        NatProof.Nat.is_le_eq_l(a, Nat.min(a, b), b, e2, Min.Nat.min_le_l(a, b))
      +eab : {a == b : Nat} = CoverList.Cover.is_le_antisym(a, b, h, hba)
      Equal.trans(Nat, Nat.min(a, b), b, a, e2, Equal.sym(Nat, a, b, eab))

def CP.min_eq_l(+a: Nat, +b: Nat,
    h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.min(a, b) == a : Nat}:
  CP.min_eq_l_go(a, b, Min.Nat.min_is_arg(a, b), h)

# `min a b == b` when `b <= a`.
def CP.min_eq_r_go(+a: Nat, +b: Nat,
    r: {Nat.min(a, b) == a : Nat} | {Nat.min(a, b) == b : Nat},
    h: {Nat.is_le(b, a) == True{} : Bool}) -> {Nat.min(a, b) == b : Nat}:
  match r:
    case Inl{+e2}:
      +hab : {Nat.is_le(a, b) == True{} : Bool} =
        NatProof.Nat.is_le_eq_l(b, Nat.min(a, b), a, e2, Min.Nat.min_le_r(a, b))
      +eba : {b == a : Nat} = CoverList.Cover.is_le_antisym(b, a, h, hab)
      Equal.trans(Nat, Nat.min(a, b), a, b, e2, Equal.sym(Nat, b, a, eba))
    case Inr{e}:
      e

def CP.min_eq_r(+a: Nat, +b: Nat,
    h: {Nat.is_le(b, a) == True{} : Bool}) -> {Nat.min(a, b) == b : Nat}:
  CP.min_eq_r_go(a, b, Min.Nat.min_is_arg(a, b), h)

# `n - n == 0`.
def CP.sub_self(n: Nat) -> {Nat.sub(n, n) == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      CP.sub_self(p)

# `n - min(n, g) == n - g`.
def CP.sub_min_b(+n: Nat, +g: Nat, le: Bool,
    +e: {le == Nat.is_le(g, n) : Bool}) ->
  {Nat.sub(n, Nat.min(n, g)) == Nat.sub(n, g) : Nat}:
  match le:
    case True{}:
      +h : {Nat.is_le(g, n) == True{} : Bool} =
        Equal.sym(Bool, True{}, Nat.is_le(g, n), e)
      Equal.cong(Nat, Nat, x => Nat.sub(n, x), Nat.min(n, g), g,
        CP.min_eq_r(n, g, h))
    case False{}:
      +hf : {Nat.is_le(g, n) == False{} : Bool} =
        Equal.sym(Bool, False{}, Nat.is_le(g, n), e)
      +hlt : {Nat.is_lt(n, g) == True{} : Bool} = FC.FC.lt_of_le_false(g, n, hf)
      +hle : {Nat.is_le(n, g) == True{} : Bool} =
        NatProof.Nat.is_le_of_lt(n, g, hlt)
      +hn : {Nat.min(n, g) == n : Nat} = CP.min_eq_l(n, g, hle)
      Equal.trans(Nat, Nat.sub(n, Nat.min(n, g)), Nat.sub(n, n), Nat.sub(n, g),
        Equal.cong(Nat, Nat, x => Nat.sub(n, x), Nat.min(n, g), n, hn),
        Equal.trans(Nat, Nat.sub(n, n), 0n, Nat.sub(n, g),
          CP.sub_self(n),
          Equal.sym(Nat, Nat.sub(n, g), 0n,
            LBS.LBS.sub_eq_zero(n, g, hle))))

def CP.sub_min(+n: Nat, +g: Nat) ->
  {Nat.sub(n, Nat.min(n, g)) == Nat.sub(n, g) : Nat}:
  CP.sub_min_b(n, g, Nat.is_le(g, n), {==})

# `x <= 1 + (x + q * x)`.
def CP.le_one_add_mul(+q: Nat, +x: Nat) ->
  {Nat.is_le(x, Nat.add(1n, Nat.add(x, Nat.mul(q, x)))) == True{} : Bool}:
  +t : Nat = Nat.add(x, Nat.mul(q, x))
  +ht : {Nat.is_le(x, t) == True{} : Bool} =
    CBN.CB.is_le_add_self_r(x, Nat.mul(q, x))
  +ht2 : {Nat.is_le(t, Nat.add(1n, t)) == True{} : Bool} =
    NatProof.Nat.is_le_of_lt(t, Nat.add(1n, t),
      NatProof.Nat.is_lt_succ_self(t))
  NatProof.Nat.is_le_trans(x, t, Nat.add(1n, t), ht, ht2)

# `min(n, 1 + (x + q * x)) == n` when `n <= x`: the truncated sequence never
# grows past the candidate count.
def CP.min_mul_ge(+n: Nat, +q: Nat, +x: Nat,
    h: {Nat.is_le(n, x) == True{} : Bool}) ->
  {Nat.min(n, Nat.add(1n, Nat.add(x, Nat.mul(q, x)))) == n : Nat}:
  +t : Nat = Nat.add(x, Nat.mul(q, x))
  +hx : {Nat.is_le(x, Nat.add(1n, t)) == True{} : Bool} =
    CP.le_one_add_mul(q, x)
  CP.min_eq_l(n, Nat.add(1n, t),
    NatProof.Nat.is_le_trans(n, x, Nat.add(1n, t), h, hx))

# `min(n, 1 + k * min(n, g)) == min(n, 1 + k * g)`.
def CP.min_mul_trunc_b(+n: Nat, +k: Nat, +g: Nat, le: Bool,
    +e: {le == Nat.is_le(g, n) : Bool}) ->
  {Nat.min(n, Nat.add(1n, Nat.mul(k, Nat.min(n, g))))
   == Nat.min(n, Nat.add(1n, Nat.mul(k, g))) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+q:
      match le:
        case True{}:
          +h : {Nat.is_le(g, n) == True{} : Bool} =
            Equal.sym(Bool, True{}, Nat.is_le(g, n), e)
          Equal.cong(Nat, Nat,
            x => Nat.min(n, Nat.add(1n, Nat.add(x, Nat.mul(q, x)))),
            Nat.min(n, g), g, CP.min_eq_r(n, g, h))
        case False{}:
          +hf : {Nat.is_le(g, n) == False{} : Bool} =
            Equal.sym(Bool, False{}, Nat.is_le(g, n), e)
          +hlt : {Nat.is_lt(n, g) == True{} : Bool} = FC.FC.lt_of_le_false(g, n, hf)
          +hng : {Nat.min(n, g) == n : Nat} =
            CP.min_eq_l(n, g, NatProof.Nat.is_le_of_lt(n, g, hlt))
          +hnn : {Nat.min(n, Nat.add(1n, Nat.add(n, Nat.mul(q, n)))) == n : Nat} =
            CP.min_mul_ge(n, q, n, NatProof.Nat.is_le_refl(n))
          +hgg : {Nat.min(n, Nat.add(1n, Nat.add(g, Nat.mul(q, g)))) == n : Nat} =
            CP.min_mul_ge(n, q, g, NatProof.Nat.is_le_of_lt(n, g, hlt))
          +el : Nat =
            Nat.min(n, Nat.add(1n, Nat.add(Nat.min(n, g), Nat.mul(q, Nat.min(n, g)))))
          +em : Nat = Nat.min(n, Nat.add(1n, Nat.add(n, Nat.mul(q, n))))
          +er : Nat = Nat.min(n, Nat.add(1n, Nat.add(g, Nat.mul(q, g))))
          +emid : {el == em : Nat} =
            Equal.cong(Nat, Nat,
              x => Nat.min(n, Nat.add(1n, Nat.add(x, Nat.mul(q, x)))),
              Nat.min(n, g), n, hng)
          Equal.trans(Nat, el, n, er,
            Equal.trans(Nat, el, em, n, emid, hnn),
            Equal.sym(Nat, er, n, hgg))

def CP.min_mul_trunc(+n: Nat, +k: Nat, +g: Nat) ->
  {Nat.min(n, Nat.add(1n, Nat.mul(k, Nat.min(n, g))))
   == Nat.min(n, Nat.add(1n, Nat.mul(k, g))) : Nat}:
  CP.min_mul_trunc_b(n, k, g, Nat.is_le(g, n), {==})

# `(a + b) + c == b + (a + c)`.
def CP.add_rot(+a: Nat, +b: Nat, +c: Nat) ->
  {Nat.add(Nat.add(a, b), c) == Nat.add(b, Nat.add(a, c)) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(a, b), c), Nat.add(a, Nat.add(b, c)),
    Nat.add(b, Nat.add(a, c)),
    NatProof.NatPrf.add_assoc(a, b, c),
    Equal.trans(Nat, Nat.add(a, Nat.add(b, c)),
      Nat.add(a, Nat.add(c, b)), Nat.add(b, Nat.add(a, c)),
      Equal.cong(Nat, Nat, x => Nat.add(a, x), Nat.add(b, c),
        Nat.add(c, b), NatProof.NatPrf.add_comm(b, c)),
      Equal.trans(Nat, Nat.add(a, Nat.add(c, b)), Nat.add(Nat.add(a, c), b),
        Nat.add(b, Nat.add(a, c)),
        Equal.sym(Nat, Nat.add(Nat.add(a, c), b), Nat.add(a, Nat.add(c, b)),
          NatProof.NatPrf.add_assoc(a, c, b)),
        NatProof.NatPrf.add_comm(Nat.add(a, c), b))))

# ---------------------------------------------------------------------------
# The truncated sequence agrees with `G`
# ---------------------------------------------------------------------------

# The accumulator form of `SolveFast.cap_go`: after `rem` steps the
# accumulator is `acc + capSum(n, k, rem, j)`, provided the running cap is
# `min(n, G(k, j))`.
def CP.cap_go_eq(+rem: Nat, +n: Nat, +k: Nat, +j: Nat, +cap: Nat, +acc: Nat,
    +eq: {cap == Nat.min(n, CapProof.LB.G(k, j)) : Nat}) ->
  {SolveFast.cap_go(rem, n, k, cap, acc)
   == Nat.add(acc, CapProof.LB.capSum(n, k, rem, j)) : Nat}:
  match rem:
    case 0n:
      Equal.sym(Nat, Nat.add(acc, 0n), acc, NatProof.NatPrf.add_zero(acc))
    case 1n+p:
      +cap2 : Nat = Nat.min(n, Nat.add(1n, Nat.mul(k, cap)))
      +acc2 : Nat = Nat.add(Nat.sub(n, cap), acc)
      +eq2 : {cap2 == Nat.min(n, CapProof.LB.G(k, Nat.add(1n, j))) : Nat} =
        Equal.trans(Nat, cap2,
          Nat.min(n, Nat.add(1n, Nat.mul(k, Nat.min(n, CapProof.LB.G(k, j))))),
          Nat.min(n, CapProof.LB.G(k, Nat.add(1n, j))),
          Equal.cong(Nat, Nat,
            x => Nat.min(n, Nat.add(1n, Nat.mul(k, x))),
            cap, Nat.min(n, CapProof.LB.G(k, j)), eq),
          CP.min_mul_trunc(n, k, CapProof.LB.G(k, j)))
      +ih : {SolveFast.cap_go(p, n, k, cap2, acc2)
             == Nat.add(acc2, CapProof.LB.capSum(n, k, p, Nat.add(1n, j))) : Nat} =
        CP.cap_go_eq(p, n, k, Nat.add(1n, j), cap2, acc2, eq2)
      +esub : {Nat.sub(n, cap) == Nat.sub(n, CapProof.LB.G(k, j)) : Nat} =
        Equal.trans(Nat, Nat.sub(n, cap),
          Nat.sub(n, Nat.min(n, CapProof.LB.G(k, j))),
          Nat.sub(n, CapProof.LB.G(k, j)),
          Equal.cong(Nat, Nat, x => Nat.sub(n, x), cap,
            Nat.min(n, CapProof.LB.G(k, j)), eq),
          CP.sub_min(n, CapProof.LB.G(k, j)))
      +et : Nat = CapProof.LB.capSum(n, k, p, Nat.add(1n, j))
      +es : Nat = Nat.sub(n, CapProof.LB.G(k, j))
      +e1 : {Nat.add(acc2, et) == Nat.add(Nat.add(es, acc), et) : Nat} =
        Equal.cong(Nat, Nat, x => Nat.add(x, et), acc2,
          Nat.add(es, acc),
          Equal.cong(Nat, Nat, x => Nat.add(x, acc), Nat.sub(n, cap), es, esub))
      +e2 : {Nat.add(Nat.add(es, acc), et)
             == Nat.add(acc, CapProof.LB.capSum(n, k, Nat.add(1n, p), j)) : Nat} =
        CP.add_rot(es, acc, et)
      Equal.trans(Nat, SolveFast.cap_go(p, n, k, cap2, acc2),
        Nat.add(acc2, et),
        Nat.add(acc, CapProof.LB.capSum(n, k, Nat.add(1n, p), j)),
        ih, Equal.trans(Nat, Nat.add(acc2, et), Nat.add(Nat.add(es, acc), et),
          Nat.add(acc, CapProof.LB.capSum(n, k, Nat.add(1n, p), j)), e1, e2))

# `G(k, 1) == 1`.
def CP.g_one(+k: Nat) -> {CapProof.LB.G(k, 1n) == 1n : Nat}:
  Equal.trans(Nat, CapProof.LB.G(k, 1n), Nat.add(1n, Nat.mul(k, 0n)), 1n,
    {==},
    Equal.trans(Nat, Nat.add(1n, Nat.mul(k, 0n)), Nat.add(1n, 0n), 1n,
      Equal.cong(Nat, Nat, x => Nat.add(1n, x), Nat.mul(k, 0n), 0n,
        CBN.CB.mul_zero(k)),
      NatProof.NatPrf.add_zero(1n)))

# `min(n, G(k, 1)) == 1` for `n` at least one.
def CP.min_g_one(+n: Nat, +k: Nat,
    h: {Nat.is_le(1n, n) == True{} : Bool}) ->
  {Nat.min(n, CapProof.LB.G(k, 1n)) == 1n : Nat}:
  Equal.trans(Nat, Nat.min(n, CapProof.LB.G(k, 1n)), Nat.min(n, 1n), 1n,
    Equal.cong(Nat, Nat, x => Nat.min(n, x), CapProof.LB.G(k, 1n), 1n,
      CP.g_one(k)),
    CP.min_eq_r(n, 1n, h))

# The two capacity bound functions agree.
def CP.capbound_eq(+n: Nat, +k: Nat) ->
  {SolveFast.capbound(n, k) == CapProof.LB.capbound(n, k) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      Equal.cong(Nat, Nat, x => Nat.add(1n+m, x), SolveFast.cap_go(1n+m, 1n+m, k, 1n, 0n),
        CapProof.LB.capSum(1n+m, k, 1n+m, 1n),
        CP.cap_go_eq(1n+m, 1n+m, k, 1n, 1n, 0n,
          Equal.sym(Nat, Nat.min(1n+m, CapProof.LB.G(k, 1n)), 1n,
            CP.min_g_one(1n+m, k, NatProof.Nat.is_le_succ(0n, m,
              NatProof.Nat.is_le_zero_l(m))))))

# ---------------------------------------------------------------------------
# The class bound against a reference tree
# ---------------------------------------------------------------------------

# `FH.cap_count` is the number of codes of `class_k.bend`.
def CP.count_eq(+g: +List<Nat>, +ws: +List<+List<Nat>>) ->
  {FH.FH.cap_count(g, ws) == CK.CK.count(g, ws) : Nat}:
  {==}

# `FH.prefmax` is the prefix maximum of `class_k.bend`.
def CP.prefmax_eq(+G: +List<+List<Nat>>, +ws: +List<+List<Nat>>, +i: Nat) ->
  {FH.FH.prefmax(G, ws, i) == CK.CK.prefmax(G, ws, i) : Nat}:
  match i:
    case 0n:
      {==}
    case 1n+p:
      +e1 : {Nat.max(FH.FH.cap_count(FT.FT.nth_word(G, p), ws),
                   FH.FH.prefmax(G, ws, p))
             == Nat.max(CK.CK.count(FT.FT.nth_word(G, p), ws),
                   FH.FH.prefmax(G, ws, p)) : Nat} =
        Equal.cong(Nat, Nat, x => Nat.max(x, FH.FH.prefmax(G, ws, p)),
          FH.FH.cap_count(FT.FT.nth_word(G, p), ws),
          CK.CK.count(FT.FT.nth_word(G, p), ws),
          CP.count_eq(FT.FT.nth_word(G, p), ws))
      +e2 : {Nat.max(CK.CK.count(FT.FT.nth_word(G, p), ws),
                   FH.FH.prefmax(G, ws, p))
             == Nat.max(CK.CK.count(FT.FT.nth_word(G, p), ws),
                   CK.CK.prefmax(G, ws, p)) : Nat} =
        Equal.cong(Nat, Nat,
          x => Nat.max(CK.CK.count(FT.FT.nth_word(G, p), ws), x),
          FH.FH.prefmax(G, ws, p), CK.CK.prefmax(G, ws, p),
          CP.prefmax_eq(G, ws, p))
      Equal.trans(Nat,
        Nat.max(FH.FH.cap_count(FT.FT.nth_word(G, p), ws),
          FH.FH.prefmax(G, ws, p)),
        Nat.max(CK.CK.count(FT.FT.nth_word(G, p), ws),
          FH.FH.prefmax(G, ws, p)),
        Nat.max(CK.CK.count(FT.FT.nth_word(G, p), ws),
          CK.CK.prefmax(G, ws, p)), e1, e2)

# The capacity class bound of a class is at most the cost of its reference
# tree.
def CP.cap_class_le_child(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +ws: +List<+List<Nat>>,
    +ble: {Nat.is_le(Groups.len_words(ws), p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +clt: {Nat.is_lt(Sat.SB.child_cost(p, G, ws, inf), inf) == True{} : Bool},
    +hnd: {FN.FN.no_dup_ref(ws) == True{} : Bool}) ->
  {Nat.is_le(FH.FH.cap_class(G, ws),
     Sat.SB.child_cost(p, G, ws, inf)) == True{} : Bool}:
  +cr : SolveRef.Best = FStep.FS.ref_run_at(p, inf, G, ws)
  ok : BO.BO.BestOK(inf, cr, G, ws) = MV.MV.main_ok(p, inf, G, ws, ble)
  v : Tree.Valid(Eval.Eval.tree_of(cr), G, ws) =
    SV.SV.valid_of_ok_lt(inf, cr, G, ws, clt, ok)
  +hb0 : {Nat.is_le(SolveFast.class_lb(ws),
     Sat.SB.child_cost(p, G, ws, inf)) == True{} : Bool} =
    FLB.FS.child_size_le(p, inf, G, ws, ble, hz, clt)
  +efast : {SolveFast.class_lb_fast(True{}, Groups.len_words(ws), ws)
            == SolveFast.class_lb(ws) : Nat} =
    FN.FN.class_lb_fast_eq(True{}, Groups.len_words(ws), ws, {==}, hnd)
  +hb : {Nat.is_le(SolveFast.class_lb_fast(True{}, Groups.len_words(ws), ws),
     Sat.SB.child_cost(p, G, ws, inf)) == True{} : Bool} =
    NatProof.Nat.is_le_eq_l(Sat.SB.child_cost(p, G, ws, inf),
      SolveFast.class_lb(ws),
      SolveFast.class_lb_fast(True{}, Groups.len_words(ws), ws),
      Equal.sym(Nat, SolveFast.class_lb_fast(True{}, Groups.len_words(ws), ws),
        SolveFast.class_lb(ws), efast), hb0)
  +hpref : {Nat.is_le(CK.CK.prefmax(G, ws, Groups.len_words(G)),
     FH.FH.prefmax(G, ws, Groups.len_words(G))) == True{} : Bool} =
    NatProof.Nat.is_le_eq_r(CK.CK.prefmax(G, ws, Groups.len_words(G)),
      CK.CK.prefmax(G, ws, Groups.len_words(G)),
      FH.FH.prefmax(G, ws, Groups.len_words(G)),
      Equal.sym(Nat, FH.FH.prefmax(G, ws, Groups.len_words(G)),
        CK.CK.prefmax(G, ws, Groups.len_words(G)),
        CP.prefmax_eq(G, ws, Groups.len_words(G))),
      NatProof.Nat.is_le_refl(CK.CK.prefmax(G, ws, Groups.len_words(G))))
  +hc0 : {Nat.is_le(CapProof.LB.capbound(Groups.len_words(ws),
     FH.FH.prefmax(G, ws, Groups.len_words(G))),
     Tree.cost(Eval.Eval.tree_of(cr), ws)) == True{} : Bool} =
    WK.WK.class_cap(p, inf, G, ws,
      FH.FH.prefmax(G, ws, Groups.len_words(G)), hpref, ble, hnd, v)
  +hc1 : {Nat.is_le(Tree.cost(Eval.Eval.tree_of(cr), ws),
     Sat.SB.child_cost(p, G, ws, inf)) == True{} : Bool} =
    FLB.FS.child_cost_ok(p, inf, G, ws, ble, hz, clt)
  +hc : {Nat.is_le(CapProof.LB.capbound(Groups.len_words(ws),
     FH.FH.prefmax(G, ws, Groups.len_words(G))),
     Sat.SB.child_cost(p, G, ws, inf)) == True{} : Bool} =
    NatProof.Nat.is_le_trans(
      CapProof.LB.capbound(Groups.len_words(ws),
        FH.FH.prefmax(G, ws, Groups.len_words(G))),
      Tree.cost(Eval.Eval.tree_of(cr), ws), Sat.SB.child_cost(p, G, ws, inf),
      hc0, hc1)
  CK.CK.max_le(SolveFast.class_lb_fast(True{}, Groups.len_words(ws), ws),
    CapProof.LB.capbound(Groups.len_words(ws),
      FH.FH.prefmax(G, ws, Groups.len_words(G))),
    Sat.SB.child_cost(p, G, ws, inf), hb, hc)

# The fold of the class bounds is at most the sum of the child costs.
def CP.cap_fold_le_sum(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +groups: +List<Groups.Group>,
    bounds: MV.MV.Bounds(p, MV.MV.next_groups(groups)),
    all: CBS.CU.AllLt(inf, Sat.SB.child_costs(p, G, groups, inf)),
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +ng: {FN.FN.nodup_ok_jobs(True{}, MV.MV.next_groups(groups))
          == True{} : Bool}) ->
  {Nat.is_le(FH.FH.cap_fold(G, groups),
     CBN.CB.sum(Sat.SB.child_costs(p, G, groups, inf))) == True{} : Bool}:
  match groups:
    case Nil{}:
      NatProof.Nat.is_le_refl(0n)
    case Con{gp, rest}:
      match gp:
        case Groups.Group{fb, ws}:
          (+ble, bt) = bounds
          (+clt, at) = all
          +nh : {FN.FN.nodup_ok(True{}, ws) == True{} : Bool} =
            Logic.Proof.and_true_l(FN.FN.nodup_ok(True{}, ws),
              FN.FN.nodup_ok_jobs(True{}, MV.MV.next_groups(rest)), ng)
          +nt : {FN.FN.nodup_ok_jobs(True{}, MV.MV.next_groups(rest))
                 == True{} : Bool} =
            Logic.Proof.and_true_r(FN.FN.nodup_ok(True{}, ws),
              FN.FN.nodup_ok_jobs(True{}, MV.MV.next_groups(rest)), ng)
          +hd : {Nat.is_le(FH.FH.cap_class(G, ws),
                   Sat.SB.child_cost(p, G, ws, inf)) == True{} : Bool} =
            CP.cap_class_le_child(p, inf, G, ws, ble, hz, clt, nh)
          +tl : {Nat.is_le(FH.FH.cap_fold(G, rest),
                   CBN.CB.sum(Sat.SB.child_costs(p, G, rest, inf)))
                 == True{} : Bool} =
            CP.cap_fold_le_sum(p, inf, G, rest, bt, at, hz, nt)
          CBN.CB.is_le_add(FH.FH.cap_class(G, ws),
            Sat.SB.child_cost(p, G, ws, inf),
            FH.FH.cap_fold(G, rest),
            CBN.CB.sum(Sat.SB.child_costs(p, G, rest, inf)), hd, tl)

# ---------------------------------------------------------------------------
# The class bound is decreasing in the branching factor
# ---------------------------------------------------------------------------

# `G` grows with the branching factor.
def CP.G_mono_k(+k1: Nat, +k2: Nat, +j: Nat,
    +h: {Nat.is_le(k1, k2) == True{} : Bool}) ->
  {Nat.is_le(CapProof.LB.G(k1, j), CapProof.LB.G(k2, j)) == True{} : Bool}:
  match j:
    case 0n:
      NatProof.Nat.is_le_refl(0n)
    case 1n+p:
      +ih : {Nat.is_le(CapProof.LB.G(k1, p), CapProof.LB.G(k2, p))
             == True{} : Bool} =
        CP.G_mono_k(k1, k2, p, h)
      +h1 : {Nat.is_le(Nat.mul(k1, CapProof.LB.G(k1, p)),
                        Nat.mul(k2, CapProof.LB.G(k1, p))) == True{} : Bool} =
        CBN.CB.is_le_mul_l(k1, k2, CapProof.LB.G(k1, p), h)
      +h2 : {Nat.is_le(Nat.mul(k2, CapProof.LB.G(k1, p)),
                        Nat.mul(k2, CapProof.LB.G(k2, p))) == True{} : Bool} =
        CBN.CB.is_le_mul_r(CapProof.LB.G(k1, p), CapProof.LB.G(k2, p), k2, ih)
      +h3 : {Nat.is_le(Nat.mul(k1, CapProof.LB.G(k1, p)),
                        Nat.mul(k2, CapProof.LB.G(k2, p))) == True{} : Bool} =
        NatProof.Nat.is_le_trans(Nat.mul(k1, CapProof.LB.G(k1, p)),
          Nat.mul(k2, CapProof.LB.G(k1, p)),
          Nat.mul(k2, CapProof.LB.G(k2, p)), h1, h2)
      CBN.CB.is_le_add(1n, 1n, Nat.mul(k1, CapProof.LB.G(k1, p)),
        Nat.mul(k2, CapProof.LB.G(k2, p)), NatProof.Nat.is_le_refl(1n), h3)

# The level sum shrinks when the branching factor grows.
def CP.capSum_k_le(+n: Nat, +k1: Nat, +k2: Nat, +fuel: Nat, +j: Nat,
    +h: {Nat.is_le(k1, k2) == True{} : Bool}) ->
  {Nat.is_le(CapProof.LB.capSum(n, k2, fuel, j),
             CapProof.LB.capSum(n, k1, fuel, j)) == True{} : Bool}:
  match fuel:
    case 0n:
      NatProof.Nat.is_le_refl(0n)
    case 1n+pf:
      +hg : {Nat.is_le(CapProof.LB.G(k1, j), CapProof.LB.G(k2, j))
             == True{} : Bool} =
        CP.G_mono_k(k1, k2, j, h)
      +hd : {Nat.is_le(Nat.sub(n, CapProof.LB.G(k2, j)),
                        Nat.sub(n, CapProof.LB.G(k1, j))) == True{} : Bool} =
        LBS.LBS.sub_le_r(n, CapProof.LB.G(k2, j), CapProof.LB.G(k1, j), hg)
      +ht : {Nat.is_le(CapProof.LB.capSum(n, k2, pf, Nat.add(1n, j)),
                        CapProof.LB.capSum(n, k1, pf, Nat.add(1n, j)))
             == True{} : Bool} =
        CP.capSum_k_le(n, k1, k2, pf, Nat.add(1n, j), h)
      CBN.CB.is_le_add(Nat.sub(n, CapProof.LB.G(k2, j)),
        Nat.sub(n, CapProof.LB.G(k1, j)),
        CapProof.LB.capSum(n, k2, pf, Nat.add(1n, j)),
        CapProof.LB.capSum(n, k1, pf, Nat.add(1n, j)), hd, ht)

# The capacity bound is decreasing in the branching factor.
def CP.capbound_k_le(+n: Nat, +k1: Nat, +k2: Nat,
    +h: {Nat.is_le(k1, k2) == True{} : Bool}) ->
  {Nat.is_le(CapProof.LB.capbound(n, k2), CapProof.LB.capbound(n, k1))
   == True{} : Bool}:
  NatProof.Nat.is_le_add_l(CapProof.LB.capSum(n, k2, n, 1n),
    CapProof.LB.capSum(n, k1, n, 1n), n,
    CP.capSum_k_le(n, k1, k2, n, 1n, h))

# The same monotonicity for the solver's truncated function.
def CP.capbound_src_k_le(+n: Nat, +k1: Nat, +k2: Nat,
    +h: {Nat.is_le(k1, k2) == True{} : Bool}) ->
  {Nat.is_le(SolveFast.capbound(n, k2), SolveFast.capbound(n, k1))
   == True{} : Bool}:
  NatProof.Nat.is_le_eq_r(SolveFast.capbound(n, k2),
    CapProof.LB.capbound(n, k1), SolveFast.capbound(n, k1),
    Equal.sym(Nat, SolveFast.capbound(n, k1), CapProof.LB.capbound(n, k1),
      CP.capbound_eq(n, k1)),
    NatProof.Nat.is_le_eq_l(CapProof.LB.capbound(n, k1),
      CapProof.LB.capbound(n, k2), SolveFast.capbound(n, k2),
      Equal.sym(Nat, SolveFast.capbound(n, k2), CapProof.LB.capbound(n, k2),
        CP.capbound_eq(n, k2)),
      CP.capbound_k_le(n, k1, k2, h)))

# The class bound fold is invariant under a permutation of the class list.
def CP.cap_fold_perm(p: FP.FP.Perm, +G: +List<+List<Nat>>,
    +xs: +List<Groups.Group>, +ys: +List<Groups.Group>,
    +ok: FP.FP.PermOk(p, xs, ys)) ->
  {FH.FH.cap_fold(G, xs) == FH.FH.cap_fold(G, ys) : Nat}:
  match p:
    case FP.PRefl{}:
      Equal.cong(+List<Groups.Group>, Nat, gs => FH.FH.cap_fold(G, gs),
        xs, ys, ok)
    case FP.PSkip{pr}:
      match xs:
        case Nil{}:
          Empty.absurd({0n == FH.FH.cap_fold(G, ys) : Nat}, ok)
        case Con{hx, tx}:
          match ys:
            case Nil{}:
              Empty.absurd({FH.FH.cap_fold(G, hx <> tx) == 0n : Nat}, ok)
            case Con{hy, ty}:
              match hy:
                case Groups.Group{+fy, +wy}:
                  +eh = Arr.Arr.dpair_l({hx == Groups.Group{fy, wy} : Groups.Group},
                          FP.FP.PermOk(pr, tx, ty), ok)
                  +et = Arr.Arr.dpair_r({hx == Groups.Group{fy, wy} : Groups.Group},
                          FP.FP.PermOk(pr, tx, ty), ok)
                  %Equal.sym(Groups.Group, hx, Groups.Group{fy, wy}, eh) : {FH.FH.cap_fold(G, _ <> tx) == FH.FH.cap_fold(G, Groups.Group{fy, wy} <> ty) : Nat}
                  Equal.cong(Nat, Nat, z => Nat.add(FH.FH.cap_class(G, wy), z),
                    FH.FH.cap_fold(G, tx), FH.FH.cap_fold(G, ty),
                    CP.cap_fold_perm(pr, G, tx, ty, et))
    case FP.PSwap{}:
      match xs:
        case Nil{}:
          Empty.absurd({0n == FH.FH.cap_fold(G, ys) : Nat}, ok)
        case Con{a, t1}:
          match t1:
            case Nil{}:
              Empty.absurd({FH.FH.cap_fold(G, a <> Nil{}) == FH.FH.cap_fold(G, ys) : Nat}, ok)
            case Con{b, tx}:
              match ys:
                case Nil{}:
                  Empty.absurd({FH.FH.cap_fold(G, a <> (b <> tx)) == 0n : Nat}, ok)
                case Con{c, t2}:
                  match c:
                    case Groups.Group{+fc, +wc}:
                      match t2:
                        case Nil{}:
                          Empty.absurd({FH.FH.cap_fold(G, a <> (b <> tx)) == FH.FH.cap_fold(G, Groups.Group{fc, wc} <> Nil{}) : Nat}, ok)
                        case Con{d, ty}:
                          match d:
                            case Groups.Group{+fd, +wd}:
                              +ead = Arr.Arr.dpair_l({a == Groups.Group{fd, wd} : Groups.Group},
                                       Arr.Arr.DPair<{b == Groups.Group{fc, wc} : Groups.Group},
                                         {tx == ty : +List<Groups.Group>}>, ok)
                              +r1 = Arr.Arr.dpair_r({a == Groups.Group{fd, wd} : Groups.Group},
                                      Arr.Arr.DPair<{b == Groups.Group{fc, wc} : Groups.Group},
                                        {tx == ty : +List<Groups.Group>}>, ok)
                              +ebc = Arr.Arr.dpair_l({b == Groups.Group{fc, wc} : Groups.Group},
                                       {tx == ty : +List<Groups.Group>}, r1)
                              +et = Arr.Arr.dpair_r({b == Groups.Group{fc, wc} : Groups.Group},
                                      {tx == ty : +List<Groups.Group>}, r1)
                              %Equal.sym(Groups.Group, a, Groups.Group{fd, wd}, ead) : {FH.FH.cap_fold(G, _ <> (b <> tx)) == FH.FH.cap_fold(G, Groups.Group{fc, wc} <> (Groups.Group{fd, wd} <> ty)) : Nat}
                              %Equal.sym(Groups.Group, b, Groups.Group{fc, wc}, ebc) : {FH.FH.cap_fold(G, Groups.Group{fd, wd} <> (_ <> tx)) == FH.FH.cap_fold(G, Groups.Group{fc, wc} <> (Groups.Group{fd, wd} <> ty)) : Nat}
                              %Equal.sym(+List<Groups.Group>, tx, ty, et) : {FH.FH.cap_fold(G, Groups.Group{fd, wd} <> (Groups.Group{fc, wc} <> _)) == FH.FH.cap_fold(G, Groups.Group{fc, wc} <> (Groups.Group{fd, wd} <> ty)) : Nat}
                              FP.FP.nat_add_swap(FH.FH.cap_class(G, wd),
                                FH.FH.cap_class(G, wc),
                                FH.FH.cap_fold(G, ty))
    case FP.PTrans{+mid, p1, p2}:
      +ok1 = Arr.Arr.dpair_l(FP.FP.PermOk(p1, xs, mid), FP.FP.PermOk(p2, mid, ys), ok)
      +ok2 = Arr.Arr.dpair_r(FP.FP.PermOk(p1, xs, mid), FP.FP.PermOk(p2, mid, ys), ok)
      Equal.trans(Nat, FH.FH.cap_fold(G, xs),
        FH.FH.cap_fold(G, mid), FH.FH.cap_fold(G, ys),
        CP.cap_fold_perm(p1, G, xs, mid, ok1),
        CP.cap_fold_perm(p2, G, mid, ys, ok2))

# ---------------------------------------------------------------------------
# The self bound `capbound(n, n) = 2n - 1`
# ---------------------------------------------------------------------------

# `G` is monotone in the level.
def CP.G_le_succ(+k: Nat, +j: Nat,
    +hk: {Nat.is_le(1n, k) == True{} : Bool}) ->
  {Nat.is_le(CapProof.LB.G(k, j), CapProof.LB.G(k, Nat.add(1n, j)))
   == True{} : Bool}:
  match k:
    case 0n:
      Empty.absurd(
        {Nat.is_le(CapProof.LB.G(0n, j), CapProof.LB.G(0n, Nat.add(1n, j)))
         == True{} : Bool}, Logic.Proof.false_ne_true(hk))
    case 1n+q:
      +h1 : {Nat.is_le(CapProof.LB.G(1n+q, j),
                        Nat.mul(1n+q, CapProof.LB.G(1n+q, j))) == True{} : Bool} =
        CBN.CB.is_le_add_self_r(CapProof.LB.G(1n+q, j),
          Nat.mul(q, CapProof.LB.G(1n+q, j)))
      +h2 : {Nat.is_le(Nat.mul(1n+q, CapProof.LB.G(1n+q, j)),
                        Nat.add(1n, Nat.mul(1n+q, CapProof.LB.G(1n+q, j))))
             == True{} : Bool} =
        NatProof.Nat.is_le_add_self_l(1n,
          Nat.mul(1n+q, CapProof.LB.G(1n+q, j)))
      NatProof.Nat.is_le_trans(CapProof.LB.G(1n+q, j),
        Nat.mul(1n+q, CapProof.LB.G(1n+q, j)),
        Nat.add(1n, Nat.mul(1n+q, CapProof.LB.G(1n+q, j))), h1, h2)

# Once a level cannot hold all `n` candidates, no later level can.
def CP.capSum_zero(+n: Nat, +k: Nat, +fuel: Nat, +j: Nat,
    +hk: {Nat.is_le(1n, k) == True{} : Bool},
    +h: {Nat.is_le(n, CapProof.LB.G(k, j)) == True{} : Bool}) ->
  {CapProof.LB.capSum(n, k, fuel, j) == 0n : Nat}:
  match fuel:
    case 0n:
      {==}
    case 1n+pf:
      +hz : {Nat.sub(n, CapProof.LB.G(k, j)) == 0n : Nat} =
        LBS.LBS.sub_eq_zero(n, CapProof.LB.G(k, j), h)
      +hg : {Nat.is_le(CapProof.LB.G(k, j),
                        CapProof.LB.G(k, Nat.add(1n, j))) == True{} : Bool} =
        CP.G_le_succ(k, j, hk)
      +h2 : {Nat.is_le(n, CapProof.LB.G(k, Nat.add(1n, j))) == True{} : Bool} =
        NatProof.Nat.is_le_trans(n, CapProof.LB.G(k, j),
          CapProof.LB.G(k, Nat.add(1n, j)), h, hg)
      +ih : {CapProof.LB.capSum(n, k, pf, Nat.add(1n, j)) == 0n : Nat} =
        CP.capSum_zero(n, k, pf, Nat.add(1n, j), hk, h2)
      +e1 : {Nat.add(Nat.sub(n, CapProof.LB.G(k, j)),
                     CapProof.LB.capSum(n, k, pf, Nat.add(1n, j)))
             == Nat.add(0n, CapProof.LB.capSum(n, k, pf, Nat.add(1n, j)))
             : Nat} =
        Equal.cong(Nat, Nat,
          x => Nat.add(x, CapProof.LB.capSum(n, k, pf, Nat.add(1n, j))),
          Nat.sub(n, CapProof.LB.G(k, j)), 0n, hz)
      Equal.trans(Nat,
        Nat.add(Nat.sub(n, CapProof.LB.G(k, j)),
          CapProof.LB.capSum(n, k, pf, Nat.add(1n, j))),
        Nat.add(0n, CapProof.LB.capSum(n, k, pf, Nat.add(1n, j))),
        0n, e1, ih)

# `G(n, 2) = 1 + n`.
def CP.g_two(+n: Nat) ->
  {CapProof.LB.G(n, 2n) == Nat.add(1n, n) : Nat}:
  Equal.trans(Nat, CapProof.LB.G(n, 2n),
    Nat.add(1n, Nat.mul(n, Nat.add(1n, Nat.mul(n, 0n)))),
    Nat.add(1n, n),
    {==},
    Equal.trans(Nat,
      Nat.add(1n, Nat.mul(n, Nat.add(1n, Nat.mul(n, 0n)))),
      Nat.add(1n, Nat.mul(n, 1n)),
      Nat.add(1n, n),
      Equal.cong(Nat, Nat, x => Nat.add(1n, Nat.mul(n, x)),
        Nat.add(1n, Nat.mul(n, 0n)), 1n,
        Equal.trans(Nat, Nat.add(1n, Nat.mul(n, 0n)), Nat.add(1n, 0n), 1n,
          Equal.cong(Nat, Nat, x => Nat.add(1n, x), Nat.mul(n, 0n), 0n,
            CBN.CB.mul_zero(n)),
          NatProof.NatPrf.add_zero(1n))),
      Equal.cong(Nat, Nat, x => Nat.add(1n, x), Nat.mul(n, 1n), n,
        CBN.CB.mul_one(n))))

# `1 + (m + m) == (1 + m) + m` under the predecessor.
def CP.cap_self_arith(+m: Nat) ->
  {Nat.add(Nat.add(1n, m), m)
   == Nat.sub(Nat.add(Nat.add(1n, m), Nat.add(1n, m)), 1n) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(1n, m), m), Nat.add(m, Nat.add(1n, m)),
    Nat.sub(Nat.add(Nat.add(1n, m), Nat.add(1n, m)), 1n),
    Equal.trans(Nat, Nat.add(Nat.add(1n, m), m), Nat.add(1n, Nat.add(m, m)),
      Nat.add(m, Nat.add(1n, m)),
      {==},
      Equal.sym(Nat, Nat.add(m, Nat.add(1n, m)), Nat.add(1n, Nat.add(m, m)),
        NatProof.NatPrf.add_succ(m, m))),
    Equal.sym(Nat, Nat.sub(Nat.add(m, Nat.add(1n, m)), 0n),
      Nat.add(m, Nat.add(1n, m)),
      FLB.FS.sub_zero(Nat.add(m, Nat.add(1n, m)))))

# `capbound(n, n) = 2n - 1`: the truncated capacity sequence is already full
# after the first level.
def CP.capbound_self(+n: Nat) ->
  {CapProof.LB.capbound(n, n) == Nat.sub(Nat.add(n, n), 1n) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      +hl : {CapProof.LB.G(1n+m, 1n) == 1n : Nat} = CP.g_one(1n+m)
      +hr : {Nat.is_le(1n+m, CapProof.LB.G(1n+m, 2n)) == True{} : Bool} =
        Equal.trans(Bool,
          Nat.is_le(1n+m, CapProof.LB.G(1n+m, 2n)),
          Nat.is_le(1n+m, Nat.add(1n, 1n+m)), True{},
          Equal.cong(Nat, Bool, x => Nat.is_le(1n+m, x),
            CapProof.LB.G(1n+m, 2n), Nat.add(1n, 1n+m), CP.g_two(1n+m)),
          NatProof.Nat.is_le_of_lt(1n+m, Nat.add(1n, 1n+m),
            NatProof.Nat.is_lt_succ_self(1n+m)))
      +hz : {CapProof.LB.capSum(1n+m, 1n+m, m, 2n) == 0n : Nat} =
        CP.capSum_zero(1n+m, 1n+m, m, 2n,
          NatProof.Nat.is_le_zero_l(m), hr)
      +e1 : {Nat.sub(1n+m, CapProof.LB.G(1n+m, 1n)) == m : Nat} =
        Equal.trans(Nat, Nat.sub(1n+m, CapProof.LB.G(1n+m, 1n)),
          Nat.sub(1n+m, 1n), m,
          Equal.cong(Nat, Nat, x => Nat.sub(1n+m, x),
            CapProof.LB.G(1n+m, 1n), 1n, hl),
          FLB.FS.sub_zero(m))
      Equal.trans(Nat, CapProof.LB.capbound(1n+m, 1n+m),
        Nat.add(1n+m, Nat.add(Nat.sub(1n+m, CapProof.LB.G(1n+m, 1n)),
          CapProof.LB.capSum(1n+m, 1n+m, m, 2n))),
        Nat.sub(Nat.add(1n+m, 1n+m), 1n),
        {==},
        Equal.trans(Nat,
          Nat.add(1n+m, Nat.add(Nat.sub(1n+m, CapProof.LB.G(1n+m, 1n)),
            CapProof.LB.capSum(1n+m, 1n+m, m, 2n))),
          Nat.add(1n+m, m),
          Nat.sub(Nat.add(1n+m, 1n+m), 1n),
          Equal.cong(Nat, Nat, x => Nat.add(1n+m, x),
            Nat.add(Nat.sub(1n+m, CapProof.LB.G(1n+m, 1n)),
              CapProof.LB.capSum(1n+m, 1n+m, m, 2n)),
            m,
            Equal.trans(Nat,
              Nat.add(Nat.sub(1n+m, CapProof.LB.G(1n+m, 1n)),
                CapProof.LB.capSum(1n+m, 1n+m, m, 2n)),
              Nat.add(m, CapProof.LB.capSum(1n+m, 1n+m, m, 2n)),
              m,
              Equal.cong(Nat, Nat, x => Nat.add(x,
                  CapProof.LB.capSum(1n+m, 1n+m, m, 2n)),
                Nat.sub(1n+m, CapProof.LB.G(1n+m, 1n)), m, e1),
              Equal.trans(Nat,
                Nat.add(m, CapProof.LB.capSum(1n+m, 1n+m, m, 2n)),
                Nat.add(m, 0n), m,
                Equal.cong(Nat, Nat, x => Nat.add(m, x),
                  CapProof.LB.capSum(1n+m, 1n+m, m, 2n), 0n, hz),
                NatProof.NatPrf.add_zero(m)))),
          CP.cap_self_arith(m)))

# The solver's capped function agrees at `k = n`.
def CP.capbound_src_self(+n: Nat) ->
  {Nat.is_le(SolveFast.capbound(n, n), Nat.sub(Nat.add(n, n), 1n))
   == True{} : Bool}:
  NatProof.Nat.is_le_eq_l(Nat.sub(Nat.add(n, n), 1n),
    CapProof.LB.capbound(n, n), SolveFast.capbound(n, n),
    Equal.sym(Nat, SolveFast.capbound(n, n), CapProof.LB.capbound(n, n),
      CP.capbound_eq(n, n)),
    NatProof.Nat.is_le_eq_r(CapProof.LB.capbound(n, n),
      CapProof.LB.capbound(n, n), Nat.sub(Nat.add(n, n), 1n),
      CP.capbound_self(n),
      NatProof.Nat.is_le_refl(CapProof.LB.capbound(n, n))))

# ---------------------------------------------------------------------------
# The never-stopping walk total
# ---------------------------------------------------------------------------

# `cap_sum(bs, gn, st)` is the sum of the raised class bounds the capacity walk
# would reach if it never stopped, from state `(bs, st)` where `st` is the state
# before the head has been scanned.
def CP.cap_sum(+bs: +List<SolveFast.BigClass>, +gn: Nat,
    st: SolveFast.CKRes) -> Nat:
  match bs:
    case Nil{}:
      0n
    case Con{bc, rest}:
      match bc:
        case SolveFast.BigClass{fb, ws, +len}:
          match st:
            case SolveFast.CKRes{tbl, k}:
              +dep = Nat.sub(Nat.add(len, len), 1n)
              Nat.add(Nat.max(dep, SolveFast.capbound(len, k)),
                CP.cap_sum(rest, gn,
                  SolveFast.class_k_opt(Nat.is_le(16n, len), ws, len, gn,
                    tbl)))

# After the head's scan, the head's raised bound plus the tail.
def CP.cap_sum_step(+rest: +List<SolveFast.BigClass>, +gn: Nat,
    +dep: Nat, +len: Nat, st: SolveFast.CKRes) -> Nat:
  match st:
    case SolveFast.CKRes{tbl, +k}:
      Nat.add(Nat.max(dep, SolveFast.capbound(len, k)),
        CP.cap_sum(rest, gn, st))

# The part of the walk's remaining total at a given phase: at phase zero the
# head has been scanned (its `k` is in `st`), at a positive phase it has not.
def CP.pending(+bs: +List<SolveFast.BigClass>, +gn: Nat, +phase: Nat,
    st: SolveFast.CKRes) -> Nat:
  match bs:
    case Nil{}:
      0n
    case Con{bc, rest}:
      match bc:
        case SolveFast.BigClass{fb, ws, +len}:
          match phase:
            case 0n:
              +dep = Nat.sub(Nat.add(len, len), 1n)
              CP.cap_sum_step(rest, gn, dep, len, st)
            case 1n+q:
              CP.cap_sum(bs, gn, st)
