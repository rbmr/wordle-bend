# Obligation C: the capacity walk's skip is justified by the class bounds.
#
# `cap_walk` raises the bound of every big class from its depth bound
# `2 * len - 1` to `max (2 * len - 1) (capbound len k)`, where `k` is the number
# of distinct feedback codes the class's best guess produces on it, as counted
# by `class_k_start`. It drops the guess once the running total reaches the
# best cost. This module proves the walk's total is at most the guess's
# capacity bound `FH.cap_lb`, so the skip is sound.
#
# The walk's total is `cap_base` plus, for every class, its raised bound minus
# its depth bound. Written as a running total it is
#
#   cap_base + bigs_depth(bs0) + sum over the classes scanned so far of
#     (raised bound - depth bound),
#
# so it stays below `cap_base + cap_fold (bigs_groups bs0)` as long as every
# class's raised bound is at most its capacity bound. That is the invariant
# `CW.walk` carries, together with the slack `CW.slack` of the classes the walk
# has not reached yet.
import Base
import ../src/solve_fast.bend as SolveFast
import ../src/solve_ref.bend as SolveRef
import ../src/groups.bend as Groups
import ../src/tree.bend as Tree
import ../src/feedback.bend as Feedback
import ./fast_hist5.bend as FH
import ./fast_tbl.bend as FT
import ./class_k.bend as CK
import ./cap_lb.bend as CP
import ./lb_capacity.bend as CapProof
import ./lb_capacity_sound.bend as LBS
import ./fast_cutoff.bend as FC
import ./nat.bend as NatProof
import ./array.bend as Arr
import ./classbound_nat.bend as CBN
import ./logic.bend as Logic
import ./fast_perm.bend as FP

# ---------------------------------------------------------------------------
# The depth bound, the class bound, and the slack between them
# ---------------------------------------------------------------------------

def CW.dep(+len: Nat) -> Nat:
  Nat.sub(Nat.add(len, len), 1n)

# The capacity bound of one big class minus its depth bound.
def CW.slk(+G: +List<+List<Nat>>, +len: Nat,
           +ws: +List<SolveFast.CWord>) -> Nat:
  Nat.sub(FH.FH.cap_class(G, SolveFast.cwords_words(ws)), CW.dep(len))

# The slack of the classes the walk has not reached yet.
def CW.slack(+G: +List<+List<Nat>>, +bs: +List<SolveFast.BigClass>) -> Nat:
  match bs:
    case Nil{}:
      0n
    case Con{bc, rest}:
      match bc:
        case SolveFast.BigClass{fb, ws, +len, clb}:
          Nat.add(CW.slk(G, len, ws), CW.slack(G, rest))

# `x <= x + y`.
def CW.le_add_r(+x: Nat, +y: Nat) ->
  {Nat.is_le(x, Nat.add(x, y)) == True{} : Bool}:
  match y:
    case 0n:
      NatProof.Nat.is_le_eq_r(x, x, Nat.add(x, 0n),
        Equal.sym(Nat, Nat.add(x, 0n), x, NatProof.NatPrf.add_zero(x)),
        NatProof.Nat.is_le_refl(x))
    case 1n+p:
      +ih : {Nat.is_le(x, Nat.add(x, p)) == True{} : Bool} = CW.le_add_r(x, p)
      +h1 : {Nat.is_le(x, Nat.add(1n, Nat.add(x, p))) == True{} : Bool} =
        NatProof.Nat.is_le_trans(x, Nat.add(x, p),
          Nat.add(1n, Nat.add(x, p)), ih,
          NatProof.Nat.is_le_of_lt(Nat.add(x, p), Nat.add(1n, Nat.add(x, p)),
            NatProof.Nat.is_lt_succ_self(Nat.add(x, p))))
      NatProof.Nat.is_le_eq_r(x, Nat.add(1n, Nat.add(x, p)),
        Nat.add(x, 1n+p),
        Equal.sym(Nat, Nat.add(x, 1n+p), Nat.add(1n, Nat.add(x, p)),
          NatProof.NatPrf.add_succ(x, p)), h1)

# `x <= (x + y) + z`.
def CW.le_add_r2(+x: Nat, +y: Nat, +z: Nat) ->
  {Nat.is_le(x, Nat.add(Nat.add(x, y), z)) == True{} : Bool}:
  NatProof.Nat.is_le_trans(x, Nat.add(x, y), Nat.add(Nat.add(x, y), z),
    CW.le_add_r(x, y), CW.le_add_r(Nat.add(x, y), z))

# The depth bound is at most the class bound of the class.
def CW.dep_le_class(+G: +List<+List<Nat>>, +ws: +List<+List<Nat>>) ->
  {Nat.is_le(CW.dep(Groups.len_words(ws)), FH.FH.cap_class(G, ws))
   == True{} : Bool}:
  CK.CK.le_max_l(CW.dep(Groups.len_words(ws)),
    CapProof.LB.capbound(Groups.len_words(ws),
      FH.FH.prefmax(G, ws, Groups.len_words(G))))

# The same, with the class size written as a separate parameter.
def CW.dep_le_class_eq(+G: +List<+List<Nat>>, +len: Nat,
    +ws: +List<+List<Nat>>,
    +hlen: {len == Groups.len_words(ws) : Nat}) ->
  {Nat.is_le(CW.dep(len), FH.FH.cap_class(G, ws)) == True{} : Bool}:
  +es : {Groups.len_words(ws) == len : Nat} =
    Equal.sym(Nat, len, Groups.len_words(ws), hlen)
  +ed : {CW.dep(Groups.len_words(ws)) == CW.dep(len) : Nat} =
    Equal.cong(Nat, Nat, x => CW.dep(x), Groups.len_words(ws), len, es)
  NatProof.Nat.is_le_eq_l(FH.FH.cap_class(G, ws),
    CW.dep(Groups.len_words(ws)), CW.dep(len), ed,
    CW.dep_le_class(G, ws))

# The raised bound of a big class is at most its capacity bound: the scan's `k`
# covers the branching factor over the whole guess list.
def CW.step_le(+G: +List<+List<Nat>>, +len: Nat,
    +ws: +List<SolveFast.CWord>, +k: Nat,
    +hlen: {len == Groups.len_words(SolveFast.cwords_words(ws)) : Nat},
    +hk: {Nat.is_le(FH.FH.prefmax(G, SolveFast.cwords_words(ws),
              Groups.len_words(G)), k) == True{} : Bool}) ->
  {Nat.is_le(Nat.max(CW.dep(len), SolveFast.capbound(len, k)),
     FH.FH.cap_class(G, SolveFast.cwords_words(ws))) == True{} : Bool}:
  +ww = SolveFast.cwords_words(ws)
  +lw = Groups.len_words(ww)
  +pf = FH.FH.prefmax(G, ww, Groups.len_words(G))
  +h1 : {Nat.is_le(CW.dep(len), FH.FH.cap_class(G, ww)) == True{} : Bool} =
    CW.dep_le_class_eq(G, len, ww, hlen)
  +hs1 : {Nat.is_le(SolveFast.capbound(len, k),
                    SolveFast.capbound(len, pf)) == True{} : Bool} =
    CP.CP.capbound_src_k_le(len, pf, k, hk)
  +hp1 : {Nat.is_le(SolveFast.capbound(len, pf),
                    CapProof.LB.capbound(len, pf)) == True{} : Bool} =
    NatProof.Nat.is_le_eq_l(CapProof.LB.capbound(len, pf),
      CapProof.LB.capbound(len, pf), SolveFast.capbound(len, pf),
      Equal.sym(Nat, SolveFast.capbound(len, pf),
        CapProof.LB.capbound(len, pf), CP.CP.capbound_eq(len, pf)),
      NatProof.Nat.is_le_refl(CapProof.LB.capbound(len, pf)))
  +es : {Groups.len_words(ww) == len : Nat} =
    Equal.sym(Nat, len, Groups.len_words(ww), hlen)
  +eb : {CapProof.LB.capbound(len, pf)
         == CapProof.LB.capbound(lw, pf) : Nat} =
    Equal.cong(Nat, Nat, x => CapProof.LB.capbound(x, pf), len, lw,
      Equal.sym(Nat, lw, len, es))
  +hp2 : {Nat.is_le(SolveFast.capbound(len, pf),
                    CapProof.LB.capbound(lw, pf)) == True{} : Bool} =
    NatProof.Nat.is_le_eq_r(SolveFast.capbound(len, pf),
      CapProof.LB.capbound(len, pf), CapProof.LB.capbound(lw, pf), eb, hp1)
  +hp3 : {Nat.is_le(CapProof.LB.capbound(lw, pf),
                    FH.FH.cap_class(G, ww)) == True{} : Bool} =
    CK.CK.le_max_r(CW.dep(lw), CapProof.LB.capbound(lw, pf))
  +hs2 : {Nat.is_le(SolveFast.capbound(len, pf),
                    FH.FH.cap_class(G, ww)) == True{} : Bool} =
    NatProof.Nat.is_le_trans(SolveFast.capbound(len, pf),
      CapProof.LB.capbound(lw, pf), FH.FH.cap_class(G, ww), hp2, hp3)
  +h2 : {Nat.is_le(SolveFast.capbound(len, k),
                   FH.FH.cap_class(G, ww)) == True{} : Bool} =
    NatProof.Nat.is_le_trans(SolveFast.capbound(len, k),
      SolveFast.capbound(len, pf), FH.FH.cap_class(G, ww), hs1, hs2)
  CK.CK.max_le(CW.dep(len), SolveFast.capbound(len, k),
    FH.FH.cap_class(G, ww), h1, h2)

# The raised bound of a small class (`k = len`) is at most its capacity bound.
def CW.step_le_cheap(+G: +List<+List<Nat>>, +len: Nat,
    +ws: +List<SolveFast.CWord>,
    +hlen: {len == Groups.len_words(SolveFast.cwords_words(ws)) : Nat}) ->
  {Nat.is_le(Nat.max(CW.dep(len), SolveFast.capbound(len, len)),
     FH.FH.cap_class(G, SolveFast.cwords_words(ws))) == True{} : Bool}:
  +ww = SolveFast.cwords_words(ws)
  +h1 : {Nat.is_le(CW.dep(len), FH.FH.cap_class(G, ww)) == True{} : Bool} =
    CW.dep_le_class_eq(G, len, ww, hlen)
  +h2 : {Nat.is_le(SolveFast.capbound(len, len), CW.dep(len))
         == True{} : Bool} =
    CP.CP.capbound_src_self(len)
  +h3 : {Nat.is_le(SolveFast.capbound(len, len),
                   FH.FH.cap_class(G, ww)) == True{} : Bool} =
    NatProof.Nat.is_le_trans(SolveFast.capbound(len, len), CW.dep(len),
      FH.FH.cap_class(G, ww), h2, h1)
  CK.CK.max_le(CW.dep(len), SolveFast.capbound(len, len),
    FH.FH.cap_class(G, ww), h1, h3)

# The depth bounds and the slacks of a class list add up to its class bounds.
def CW.dsum_slack(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +bs: +List<SolveFast.BigClass>,
    +hok: {FH.FH.bigs_ok_b(G, C, n_root, bs) == True{} : Bool}) ->
  {Nat.add(SolveFast.bigs_depth(bs), CW.slack(G, bs))
   == FH.FH.cap_fold(G, FH.FH.bigs_groups(bs)) : Nat}:
  match bs:
    case Nil{}:
      {==}
    case Con{bc, rest}:
      match bc:
        case SolveFast.BigClass{+fb, +ws, +len, clb}:
          +bcp : SolveFast.BigClass = SolveFast.BigClass{fb, ws, len, clb}
          +hh : {FH.FH.big_ok_b(G, C, n_root, bcp) == True{} : Bool} =
            Logic.Proof.and_true_l(FH.FH.big_ok_b(G, C, n_root, bcp),
              FH.FH.bigs_ok_b(G, C, n_root, rest), hok)
          +ht : {FH.FH.bigs_ok_b(G, C, n_root, rest) == True{} : Bool} =
            Logic.Proof.and_true_r(FH.FH.big_ok_b(G, C, n_root, bcp),
              FH.FH.bigs_ok_b(G, C, n_root, rest), hok)
          +hlen : {len == Groups.len_words(SolveFast.cwords_words(ws))
                   : Nat} =
            NatProof.NatPrf.is_eq_true(len,
              Groups.len_words(SolveFast.cwords_words(ws)),
              Logic.Proof.and_true_r(FT.FT.cwords_ok_b(G, C, n_root, ws),
                Nat.is_eq(len, Groups.len_words(SolveFast.cwords_words(ws))),
                hh))
          +ih : {Nat.add(SolveFast.bigs_depth(rest), CW.slack(G, rest))
                 == FH.FH.cap_fold(G, FH.FH.bigs_groups(rest)) : Nat} =
            CW.dsum_slack(G, C, n_root, rest, ht)
          +hcc : {Nat.is_le(CW.dep(len),
                    FH.FH.cap_class(G, SolveFast.cwords_words(ws)))
                  == True{} : Bool} =
            CW.dep_le_class_eq(G, len, SolveFast.cwords_words(ws), hlen)
          +hsub : {Nat.add(CW.dep(len),
                     Nat.sub(FH.FH.cap_class(G, SolveFast.cwords_words(ws)),
                       CW.dep(len)))
                   == FH.FH.cap_class(G, SolveFast.cwords_words(ws)) : Nat} =
            FC.FC.add_sub_of_le(FH.FH.cap_class(G,
                SolveFast.cwords_words(ws)), CW.dep(len), hcc)
          +e1 : {Nat.add(Nat.add(CW.dep(len), SolveFast.bigs_depth(rest)),
                   Nat.add(Nat.sub(FH.FH.cap_class(G,
                       SolveFast.cwords_words(ws)), CW.dep(len)),
                     CW.slack(G, rest)))
                 == Nat.add(Nat.add(CW.dep(len),
                     Nat.sub(FH.FH.cap_class(G, SolveFast.cwords_words(ws)),
                       CW.dep(len))),
                   Nat.add(SolveFast.bigs_depth(rest), CW.slack(G, rest)))
                 : Nat} =
            NatProof.NatPrf.add4(CW.dep(len), SolveFast.bigs_depth(rest),
              Nat.sub(FH.FH.cap_class(G, SolveFast.cwords_words(ws)),
                CW.dep(len)), CW.slack(G, rest))
          +e2 : {Nat.add(Nat.add(CW.dep(len),
                     Nat.sub(FH.FH.cap_class(G, SolveFast.cwords_words(ws)),
                       CW.dep(len))),
                   Nat.add(SolveFast.bigs_depth(rest), CW.slack(G, rest)))
                 == Nat.add(FH.FH.cap_class(G, SolveFast.cwords_words(ws)),
                   Nat.add(SolveFast.bigs_depth(rest), CW.slack(G, rest)))
                 : Nat} =
            Equal.cong(Nat, Nat,
              x => Nat.add(x, Nat.add(SolveFast.bigs_depth(rest),
                CW.slack(G, rest))),
              Nat.add(CW.dep(len),
                Nat.sub(FH.FH.cap_class(G, SolveFast.cwords_words(ws)),
                  CW.dep(len))),
              FH.FH.cap_class(G, SolveFast.cwords_words(ws)), hsub)
          +e3 : {Nat.add(FH.FH.cap_class(G, SolveFast.cwords_words(ws)),
                   Nat.add(SolveFast.bigs_depth(rest), CW.slack(G, rest)))
                 == Nat.add(FH.FH.cap_class(G, SolveFast.cwords_words(ws)),
                   FH.FH.cap_fold(G, FH.FH.bigs_groups(rest))) : Nat} =
            Equal.cong(Nat, Nat,
              x => Nat.add(FH.FH.cap_class(G, SolveFast.cwords_words(ws)), x),
              Nat.add(SolveFast.bigs_depth(rest), CW.slack(G, rest)),
              FH.FH.cap_fold(G, FH.FH.bigs_groups(rest)), ih)
          Equal.trans(Nat,
            Nat.add(SolveFast.bigs_depth(bs), CW.slack(G, bs)),
            Nat.add(Nat.add(CW.dep(len), SolveFast.bigs_depth(rest)),
              Nat.add(Nat.sub(FH.FH.cap_class(G, SolveFast.cwords_words(ws)),
                  CW.dep(len)), CW.slack(G, rest))),
            FH.FH.cap_fold(G, FH.FH.bigs_groups(bs)),
            {==},
            Equal.trans(Nat,
              Nat.add(Nat.add(CW.dep(len), SolveFast.bigs_depth(rest)),
                Nat.add(Nat.sub(FH.FH.cap_class(G,
                    SolveFast.cwords_words(ws)), CW.dep(len)),
                  CW.slack(G, rest))),
              Nat.add(FH.FH.cap_class(G, SolveFast.cwords_words(ws)),
                FH.FH.cap_fold(G, FH.FH.bigs_groups(rest))),
              FH.FH.cap_fold(G, FH.FH.bigs_groups(bs)),
              Equal.trans(Nat,
                Nat.add(Nat.add(CW.dep(len), SolveFast.bigs_depth(rest)),
                  Nat.add(Nat.sub(FH.FH.cap_class(G,
                      SolveFast.cwords_words(ws)), CW.dep(len)),
                    CW.slack(G, rest))),
                Nat.add(FH.FH.cap_class(G, SolveFast.cwords_words(ws)),
                  Nat.add(SolveFast.bigs_depth(rest), CW.slack(G, rest))),
                Nat.add(FH.FH.cap_class(G, SolveFast.cwords_words(ws)),
                  FH.FH.cap_fold(G, FH.FH.bigs_groups(rest))),
                Equal.trans(Nat,
                  Nat.add(Nat.add(CW.dep(len), SolveFast.bigs_depth(rest)),
                    Nat.add(Nat.sub(FH.FH.cap_class(G,
                        SolveFast.cwords_words(ws)), CW.dep(len)),
                      CW.slack(G, rest))),
                  Nat.add(Nat.add(CW.dep(len),
                      Nat.sub(FH.FH.cap_class(G, SolveFast.cwords_words(ws)),
                        CW.dep(len))),
                    Nat.add(SolveFast.bigs_depth(rest), CW.slack(G, rest))),
                  Nat.add(FH.FH.cap_class(G, SolveFast.cwords_words(ws)),
                    Nat.add(SolveFast.bigs_depth(rest), CW.slack(G, rest))),
                  e1, e2),
                e3),
              {==}))

# ---------------------------------------------------------------------------
# The walk's state predicates
# ---------------------------------------------------------------------------

# The scan of the head class has not happened yet at a positive phase, and at
# phase zero it has: the state's table is valid and its raised bound is within
# the class bound.
def CW.Prend(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n_root: Nat,
    +phase: Nat, +bs: +List<SolveFast.BigClass>,
    st: SolveFast.CKRes) -> Data:
  match phase:
    case 0n:
      match bs:
        case Nil{}:
          Unit
        case Con{bc, rest}:
          match bc:
            case SolveFast.BigClass{fb, ws, +len, clb}:
              match st:
                case SolveFast.CKRes{tbl, +k}:
                  Arr.Arr.DPair<FT.FT.TblOk(G, C, n_root, tbl),
                    {Nat.is_le(Nat.max(CW.dep(len),
                        SolveFast.capbound(len, k)),
                       FH.FH.cap_class(G, SolveFast.cwords_words(ws)))
                     == True{} : Bool}>
    case 1n+p:
      Unit

# The state's table is valid.
def CW.TblOf(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n_root: Nat,
    st: SolveFast.CKRes) -> Data:
  match st:
    case SolveFast.CKRes{tbl, k}:
      FT.FT.TblOk(G, C, n_root, tbl)

# The walk's result: dropping the guess needs the best cost at most the class
# bound of the guess, and keeping it needs the class list unchanged. Both
# carry the table the buffer keeps.


# The scan's postcondition is stated about the scan call; move it to the value
# the scan returned.
def CW.loop_ok_transport(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +ws: +List<+List<Nat>>, +gn: Nat,
    -r1: SolveFast.CKRes, -r2: SolveFast.CKRes,
    +e: {r2 == r1 : SolveFast.CKRes},
    +h: CK.CK.LoopOk(G, C, n_root, ws, gn, r1)) ->
  CK.CK.LoopOk(G, C, n_root, ws, gn, r2):
  %Equal.sym(SolveFast.CKRes, r2, r1, e) : CK.CK.LoopOk(G, C, n_root, ws, gn, _)
  h

# The scan of one class hands over its table and a `k` that covers the class's
# branching factor over the whole guess list.
def CW.scan_take(-R: SolveFast.CKRes -> Data, +G: +List<+List<Nat>>,
    +C: +List<+List<Nat>>, +n_root: Nat, +ws: +List<SolveFast.CWord>,
    +len: Nat, +gn: Nat, big: Bool, tbl: Array<U32>,
    +hgn: {gn == Groups.len_words(G) : Nat},
    +hlen: {len == Groups.len_words(SolveFast.cwords_words(ws)) : Nat},
    +hcwo: {FT.FT.cwords_ok_b(G, C, n_root, ws) == True{} : Bool},
    +htbl: FT.FT.TblOk(G, C, n_root, tbl),
    r: SolveFast.CKRes,
    +e: {r == SolveFast.class_k_opt(big, ws, len, gn, tbl) : SolveFast.CKRes},
    kont: @tbl2: Array<U32> -> @+k: Nat ->
          FT.FT.TblOk(G, C, n_root, tbl2) ->
          {Nat.is_le(Nat.max(CW.dep(len), SolveFast.capbound(len, k)),
             FH.FH.cap_class(G, SolveFast.cwords_words(ws))) == True{} : Bool} ->
          R(SolveFast.CKRes{tbl2, k})) -> R(r):
  match big:
    case True{}:
      match r:
        case SolveFast.CKRes{tbl2, +k}:
          +hloop : CK.CK.LoopOk(G, C, n_root, SolveFast.cwords_words(ws), gn,
              SolveFast.class_k_start(ws, len, gn, tbl)) =
            CK.CK.class_k_spec(G, C, SolveFast.cwords_words(ws), n_root, ws,
              len, gn, tbl, {==}, hcwo, hlen, hgn, htbl,
              Arr.Arr.dup(U32, tbl))
          +hl1 : CK.CK.LoopOk(G, C, n_root, SolveFast.cwords_words(ws), gn,
              SolveFast.CKRes{tbl2, k}) =
            CW.loop_ok_transport(G, C, n_root, SolveFast.cwords_words(ws), gn,
              SolveFast.class_k_start(ws, len, gn, tbl),
              SolveFast.CKRes{tbl2, k}, e, hloop)
          +htbl2 : FT.FT.TblOk(G, C, n_root, tbl2) =
            Arr.Arr.dpair_l(FT.FT.TblOk(G, C, n_root, tbl2),
              {Nat.is_le(CK.CK.prefmax(G, SolveFast.cwords_words(ws), gn), k)
               == True{} : Bool}, hl1)
          +hck : {Nat.is_le(CK.CK.prefmax(G, SolveFast.cwords_words(ws), gn), k)
                  == True{} : Bool} =
            Arr.Arr.dpair_r(FT.FT.TblOk(G, C, n_root, tbl2),
              {Nat.is_le(CK.CK.prefmax(G, SolveFast.cwords_words(ws), gn), k)
               == True{} : Bool}, hl1)
          +epf : {FH.FH.prefmax(G, SolveFast.cwords_words(ws),
                     Groups.len_words(G))
                  == CK.CK.prefmax(G, SolveFast.cwords_words(ws), gn) : Nat} =
            Equal.trans(Nat,
              FH.FH.prefmax(G, SolveFast.cwords_words(ws), Groups.len_words(G)),
              FH.FH.prefmax(G, SolveFast.cwords_words(ws), gn),
              CK.CK.prefmax(G, SolveFast.cwords_words(ws), gn),
              Equal.cong(Nat, Nat,
                x => FH.FH.prefmax(G, SolveFast.cwords_words(ws), x),
                Groups.len_words(G), gn,
                Equal.sym(Nat, gn, Groups.len_words(G), hgn)),
              CP.CP.prefmax_eq(G, SolveFast.cwords_words(ws), gn))
          +hk : {Nat.is_le(FH.FH.prefmax(G, SolveFast.cwords_words(ws),
                     Groups.len_words(G)), k) == True{} : Bool} =
            NatProof.Nat.is_le_eq_l(k,
              CK.CK.prefmax(G, SolveFast.cwords_words(ws), gn),
              FH.FH.prefmax(G, SolveFast.cwords_words(ws),
                Groups.len_words(G)),
              Equal.sym(Nat, FH.FH.prefmax(G, SolveFast.cwords_words(ws),
                Groups.len_words(G)),
                CK.CK.prefmax(G, SolveFast.cwords_words(ws), gn), epf), hck)
          kont(tbl2, k, htbl2, CW.step_le(G, len, ws, k, hlen, hk))
    case False{}:
      +es : {SolveFast.CKRes{tbl, len} == r : SolveFast.CKRes} =
        Equal.sym(SolveFast.CKRes, r, SolveFast.CKRes{tbl, len}, e)
      %es : R(_)
      kont(tbl, len, htbl, CW.step_le_cheap(G, len, ws, hlen))

# The parts of a scan state, as projections (the state may be matched only once,
# but a projection may be applied to the reconstructed value).
def CW.tbl_of(r: SolveFast.CKRes) -> Array<U32>:
  match r:
    case SolveFast.CKRes{tbl, k}:
      tbl

def CW.k_of(r: SolveFast.CKRes) -> Nat:
  match r:
    case SolveFast.CKRes{tbl, k}:
      k

# ---------------------------------------------------------------------------
# The walk
# ---------------------------------------------------------------------------

# `c <= capv` from the stop test, the running invariant and the bound.
def CW.skip_le(+c: Nat, +x: Nat, +bound: Nat, +capv: Nat, +slack: Nat,
    +hbest: {Nat.is_le(c, x) == True{} : Bool},
    +hinv: {Nat.is_le(Nat.add(x, slack), bound) == True{} : Bool},
    +hb: {Nat.is_le(bound, capv) == True{} : Bool}) ->
  {Nat.is_le(c, capv) == True{} : Bool}:
  NatProof.Nat.is_le_trans(c, bound, capv,
    NatProof.Nat.is_le_trans(c, x, bound, hbest,
      NatProof.Nat.is_le_trans(x, Nat.add(x, slack), bound,
        CW.le_add_r(x, slack), hinv)),
    hb)


# ---------------------------------------------------------------------------
# The head of a class list
# ---------------------------------------------------------------------------

def CW.head_ws(+bs: +List<SolveFast.BigClass>) -> +List<SolveFast.CWord>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{bc, rest}:
      match bc:
        case SolveFast.BigClass{fb, ws, len, clb}:
          ws

def CW.head_len(+bs: +List<SolveFast.BigClass>) -> Nat:
  match bs:
    case Nil{}:
      0n
    case Con{bc, rest}:
      match bc:
        case SolveFast.BigClass{fb, ws, len, clb}:
          len

# A valid scan state for the head class is exactly the phase-zero predicate:
# the table is valid and the scanned `k` covers the class bound.
def CW.prend_of_loop(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +bs: +List<SolveFast.BigClass>, +gn: Nat,
    +hgn: {gn == Groups.len_words(G) : Nat},
    st: SolveFast.CKRes,
    +hok: {FH.FH.bigs_ok_b(G, C, n_root, bs) == True{} : Bool},
    +hloop: CK.CK.LoopOk(G, C, n_root,
      SolveFast.cwords_words(CW.head_ws(bs)), gn, st)) ->
  CW.Prend(G, C, n_root, 0n, bs, st):
  match bs:
    case Nil{}:
      Unit{}
    case Con{bc, rest}:
      match bc:
        case SolveFast.BigClass{+fb, +ws, +len, clb}:
          match st:
            case SolveFast.CKRes{tbl, +k}:
              +hh : {FH.FH.big_ok_b(G, C, n_root,
                       SolveFast.BigClass{fb, ws, len, clb}) == True{} : Bool} =
                Logic.Proof.and_true_l(FH.FH.big_ok_b(G, C, n_root,
                    SolveFast.BigClass{fb, ws, len, clb}),
                  FH.FH.bigs_ok_b(G, C, n_root, rest), hok)
              +hlen : {len == Groups.len_words(SolveFast.cwords_words(ws))
                       : Nat} =
                NatProof.NatPrf.is_eq_true(len,
                  Groups.len_words(SolveFast.cwords_words(ws)),
                  Logic.Proof.and_true_r(FT.FT.cwords_ok_b(G, C, n_root, ws),
                    Nat.is_eq(len,
                      Groups.len_words(SolveFast.cwords_words(ws))), hh))
              +htbl : FT.FT.TblOk(G, C, n_root, tbl) =
                Arr.Arr.dpair_l(FT.FT.TblOk(G, C, n_root, tbl),
                  {Nat.is_le(CK.CK.prefmax(G, SolveFast.cwords_words(ws), gn), k)
                   == True{} : Bool}, hloop)
              +hck : {Nat.is_le(CK.CK.prefmax(G, SolveFast.cwords_words(ws), gn),
                       k) == True{} : Bool} =
                Arr.Arr.dpair_r(FT.FT.TblOk(G, C, n_root, tbl),
                  {Nat.is_le(CK.CK.prefmax(G, SolveFast.cwords_words(ws), gn), k)
                   == True{} : Bool}, hloop)
              +epf : {FH.FH.prefmax(G, SolveFast.cwords_words(ws),
                         Groups.len_words(G))
                      == CK.CK.prefmax(G, SolveFast.cwords_words(ws), gn) : Nat} =
                Equal.trans(Nat,
                  FH.FH.prefmax(G, SolveFast.cwords_words(ws), Groups.len_words(G)),
                  FH.FH.prefmax(G, SolveFast.cwords_words(ws), gn),
                  CK.CK.prefmax(G, SolveFast.cwords_words(ws), gn),
                  Equal.cong(Nat, Nat,
                    x => FH.FH.prefmax(G, SolveFast.cwords_words(ws), x),
                    Groups.len_words(G), gn,
                    Equal.sym(Nat, gn, Groups.len_words(G), hgn)),
                  CP.CP.prefmax_eq(G, SolveFast.cwords_words(ws), gn))
              +hk : {Nat.is_le(FH.FH.prefmax(G, SolveFast.cwords_words(ws),
                         Groups.len_words(G)), k) == True{} : Bool} =
                NatProof.Nat.is_le_eq_l(k,
                  CK.CK.prefmax(G, SolveFast.cwords_words(ws), gn),
                  FH.FH.prefmax(G, SolveFast.cwords_words(ws),
                    Groups.len_words(G)),
                  Equal.sym(Nat,
                    FH.FH.prefmax(G, SolveFast.cwords_words(ws),
                      Groups.len_words(G)),
                    CK.CK.prefmax(G, SolveFast.cwords_words(ws), gn), epf), hck)
              Arr.DPair{htbl, CW.step_le(G, len, ws, k, hlen, hk)}

# The cheap scan (`k = len`) satisfies the phase-zero predicate.
def CW.prend_cheap(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +bs: +List<SolveFast.BigClass>,
    -tbl: Array<U32>,
    +hok: {FH.FH.bigs_ok_b(G, C, n_root, bs) == True{} : Bool},
    +htbl: FT.FT.TblOk(G, C, n_root, tbl)) ->
  CW.Prend(G, C, n_root, 0n, bs, SolveFast.ck_cheap(CW.head_len(bs), tbl)):
  match bs:
    case Nil{}:
      Unit{}
    case Con{bc, rest}:
      match bc:
        case SolveFast.BigClass{+fb, +ws, +len, clb}:
          +hh : {FH.FH.big_ok_b(G, C, n_root,
                   SolveFast.BigClass{fb, ws, len, clb}) == True{} : Bool} =
            Logic.Proof.and_true_l(FH.FH.big_ok_b(G, C, n_root,
                SolveFast.BigClass{fb, ws, len, clb}),
              FH.FH.bigs_ok_b(G, C, n_root, rest), hok)
          +hlen : {len == Groups.len_words(SolveFast.cwords_words(ws)) : Nat} =
            NatProof.NatPrf.is_eq_true(len,
              Groups.len_words(SolveFast.cwords_words(ws)),
              Logic.Proof.and_true_r(FT.FT.cwords_ok_b(G, C, n_root, ws),
                Nat.is_eq(len, Groups.len_words(SolveFast.cwords_words(ws))),
                hh))
          Arr.DPair{htbl, CW.step_le_cheap(G, len, ws, hlen)}

# The valid table of a scan state, from the scan's specification.
def CW.tbl_of_loop(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +ws: +List<+List<Nat>>, +gn: Nat, st: SolveFast.CKRes,
    +hloop: CK.CK.LoopOk(G, C, n_root, ws, gn, st)) ->
  CW.TblOf(G, C, n_root, st):
  match st:
    case SolveFast.CKRes{tbl, k}:
      Arr.Arr.dpair_l(FT.FT.TblOk(G, C, n_root, tbl),
        {Nat.is_le(CK.CK.prefmax(G, ws, gn), k) == True{} : Bool}, hloop)

# Transport the phase-zero predicate and the table predicate along an equality
# of states.
def CW.prend_transport(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +bs: +List<SolveFast.BigClass>, +phase: Nat,
    -st1: SolveFast.CKRes, -st2: SolveFast.CKRes,
    +e: {st2 == st1 : SolveFast.CKRes},
    +h: CW.Prend(G, C, n_root, phase, bs, st1)) ->
  CW.Prend(G, C, n_root, phase, bs, st2):
  %Equal.sym(SolveFast.CKRes, st2, st1, e) : CW.Prend(G, C, n_root, phase, bs, _)
  h

def CW.tbl_transport(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, -st1: SolveFast.CKRes, -st2: SolveFast.CKRes,
    +e: {st2 == st1 : SolveFast.CKRes},
    +h: CW.TblOf(G, C, n_root, st1)) -> CW.TblOf(G, C, n_root, st2):
  %Equal.sym(SolveFast.CKRes, st2, st1, e) : CW.TblOf(G, C, n_root, _)
  h

# One scan step with the table duplicated: the fact is built on the first
# copy, the walk's next state on the second. The continuation receives the

# Build the phase-zero predicate and the table predicate about an already
# matched scan state, then hand the state to a continuation (so that the state
# is consumed exactly once).
def CW.facts_of_state(-R: SolveFast.CKRes -> Data,
    +G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n_root: Nat,
    +bs: +List<SolveFast.BigClass>, +gn: Nat,
    +hgn: {gn == Groups.len_words(G) : Nat},
    +hok: {FH.FH.bigs_ok_b(G, C, n_root, bs) == True{} : Bool},
    st: SolveFast.CKRes,
    +hloop: CK.CK.LoopOk(G, C, n_root,
      SolveFast.cwords_words(CW.head_ws(bs)), gn, st),
    kont: @s: SolveFast.CKRes -> CW.TblOf(G, C, n_root, s) ->
          CW.Prend(G, C, n_root, 0n, bs, s) -> R(s)) -> R(st):
  match bs:
    case Nil{}:
      match st:
        case SolveFast.CKRes{tbl, +k}:
          +htb : FT.FT.TblOk(G, C, n_root, tbl) =
            Arr.Arr.dpair_l(FT.FT.TblOk(G, C, n_root, tbl),
              {Nat.is_le(CK.CK.prefmax(G, SolveFast.cwords_words(Nil{}), gn), k)
               == True{} : Bool}, hloop)
          kont(SolveFast.CKRes{tbl, k}, htb, Unit{})
    case Con{bc, rest}:
      match bc:
        case SolveFast.BigClass{+fb, +ws, +len, clb}:
          match st:
            case SolveFast.CKRes{tbl, +k}:
              +hh : {FH.FH.big_ok_b(G, C, n_root,
                       SolveFast.BigClass{fb, ws, len, clb}) == True{} : Bool} =
                Logic.Proof.and_true_l(FH.FH.big_ok_b(G, C, n_root,
                    SolveFast.BigClass{fb, ws, len, clb}),
                  FH.FH.bigs_ok_b(G, C, n_root, rest), hok)
              +hlen : {len == Groups.len_words(SolveFast.cwords_words(ws))
                       : Nat} =
                NatProof.NatPrf.is_eq_true(len,
                  Groups.len_words(SolveFast.cwords_words(ws)),
                  Logic.Proof.and_true_r(FT.FT.cwords_ok_b(G, C, n_root, ws),
                    Nat.is_eq(len,
                      Groups.len_words(SolveFast.cwords_words(ws))), hh))
              +htbl : FT.FT.TblOk(G, C, n_root, tbl) =
                Arr.Arr.dpair_l(FT.FT.TblOk(G, C, n_root, tbl),
                  {Nat.is_le(CK.CK.prefmax(G, SolveFast.cwords_words(ws), gn), k)
                   == True{} : Bool}, hloop)
              +hck : {Nat.is_le(CK.CK.prefmax(G, SolveFast.cwords_words(ws), gn),
                       k) == True{} : Bool} =
                Arr.Arr.dpair_r(FT.FT.TblOk(G, C, n_root, tbl),
                  {Nat.is_le(CK.CK.prefmax(G, SolveFast.cwords_words(ws), gn), k)
                   == True{} : Bool}, hloop)
              +epf : {FH.FH.prefmax(G, SolveFast.cwords_words(ws),
                         Groups.len_words(G))
                      == CK.CK.prefmax(G, SolveFast.cwords_words(ws), gn) : Nat} =
                Equal.trans(Nat,
                  FH.FH.prefmax(G, SolveFast.cwords_words(ws), Groups.len_words(G)),
                  FH.FH.prefmax(G, SolveFast.cwords_words(ws), gn),
                  CK.CK.prefmax(G, SolveFast.cwords_words(ws), gn),
                  Equal.cong(Nat, Nat,
                    x => FH.FH.prefmax(G, SolveFast.cwords_words(ws), x),
                    Groups.len_words(G), gn,
                    Equal.sym(Nat, gn, Groups.len_words(G), hgn)),
                  CP.CP.prefmax_eq(G, SolveFast.cwords_words(ws), gn))
              +hk : {Nat.is_le(FH.FH.prefmax(G, SolveFast.cwords_words(ws),
                         Groups.len_words(G)), k) == True{} : Bool} =
                NatProof.Nat.is_le_eq_l(k,
                  CK.CK.prefmax(G, SolveFast.cwords_words(ws), gn),
                  FH.FH.prefmax(G, SolveFast.cwords_words(ws),
                    Groups.len_words(G)),
                  Equal.sym(Nat,
                    FH.FH.prefmax(G, SolveFast.cwords_words(ws),
                      Groups.len_words(G)),
                    CK.CK.prefmax(G, SolveFast.cwords_words(ws), gn), epf), hck)
              kont(SolveFast.CKRes{tbl, k}, htbl,
                Arr.DPair{htbl, CW.step_le(G, len, ws, k, hlen, hk)})

# One scan step with the table duplicated: the second copy is the scan's input,
# the first is the walk's next state. No proof state mentions the scratch array.
def CW.scan_step(-R: SolveFast.CKRes -> Data,
    +G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n_root: Nat,
    big: Bool, +bc: SolveFast.BigClass, +rest: +List<SolveFast.BigClass>,
    +gn: Nat,
    +hgn: {gn == Groups.len_words(G) : Nat},
    +hh: {FH.FH.big_ok_b(G, C, n_root, bc) == True{} : Bool},
    +hok: {FH.FH.bigs_ok_b(G, C, n_root, Con{bc, rest}) == True{} : Bool},
    -tbl: Array<U32>,
    dpt: &t1: Array<U32> -> &t2: Array<U32> ->
         {t1 == tbl : Array<U32>} & {t2 == t1 : Array<U32>},
    +htbl: FT.FT.TblOk(G, C, n_root, tbl),
    kont: @st: SolveFast.CKRes -> CW.TblOf(G, C, n_root, st) ->
          CW.Prend(G, C, n_root, 0n, Con{bc, rest}, st) -> R(st)) ->
  R(SolveFast.class_k_opt(big, CW.head_ws(Con{bc, rest}),
      CW.head_len(Con{bc, rest}), gn, tbl)):
  match big:
    case True{}:
      match bc:
        case SolveFast.BigClass{+fb, +ws, +len, clb}:
          (t1, d2) = dpt
          (t2, pe) = d2
          (+e1, +e2) = pe
          +et2 : {t2 == tbl : Array<U32>} =
            Equal.trans(Array<U32>, t2, t1, tbl, e2, e1)
          +et1 : {t1 == t2 : Array<U32>} =
            Equal.sym(Array<U32>, t2, t1, e2)
          +htbl2 : FT.FT.TblOk(G, C, n_root, t2) =
            FT.FT.tbl_ok_transport(G, C, n_root, tbl, t2,
              Equal.sym(Array<U32>, t2, tbl, et2), htbl)
          +hlen : {len == Groups.len_words(SolveFast.cwords_words(ws)) : Nat} =
            NatProof.NatPrf.is_eq_true(len,
              Groups.len_words(SolveFast.cwords_words(ws)),
              Logic.Proof.and_true_r(FT.FT.cwords_ok_b(G, C, n_root, ws),
                Nat.is_eq(len, Groups.len_words(SolveFast.cwords_words(ws))), hh))
          +hcwo : {FT.FT.cwords_ok_b(G, C, n_root, ws) == True{} : Bool} =
            Logic.Proof.and_true_l(FT.FT.cwords_ok_b(G, C, n_root, ws),
              Nat.is_eq(len, Groups.len_words(SolveFast.cwords_words(ws))), hh)
          +hloop2 : CK.CK.LoopOk(G, C, n_root, SolveFast.cwords_words(ws), gn,
              SolveFast.class_k_start(ws, len, gn, t2)) =
            CK.CK.class_k_spec(G, C, SolveFast.cwords_words(ws), n_root, ws,
              len, gn, t2, {==}, hcwo, hlen, hgn, htbl2,
              Arr.Arr.dup(U32, t2))
          +e_s : {SolveFast.class_k_start(ws, len, gn, t1)
                  == SolveFast.class_k_start(ws, len, gn, t2)
                  : SolveFast.CKRes} =
            Equal.cong(Array<U32>, SolveFast.CKRes,
              x => SolveFast.class_k_start(ws, len, gn, x), t1, t2, et1)
          +hloop1 : CK.CK.LoopOk(G, C, n_root, SolveFast.cwords_words(ws), gn,
              SolveFast.class_k_start(ws, len, gn, t1)) =
            CW.loop_ok_transport(G, C, n_root, SolveFast.cwords_words(ws), gn,
              SolveFast.class_k_start(ws, len, gn, t2),
              SolveFast.class_k_start(ws, len, gn, t1), e_s, hloop2)
          +e_g : {SolveFast.class_k_start(ws, len, gn, t1)
                  == SolveFast.class_k_opt(big, CW.head_ws(Con{bc, rest}),
                       CW.head_len(Con{bc, rest}), gn, tbl)
                  : SolveFast.CKRes} =
            Equal.trans(SolveFast.CKRes,
              SolveFast.class_k_start(ws, len, gn, t1),
              SolveFast.class_k_start(ws, len, gn, tbl),
              SolveFast.class_k_opt(big, CW.head_ws(Con{bc, rest}),
                CW.head_len(Con{bc, rest}), gn, tbl),
              Equal.cong(Array<U32>, SolveFast.CKRes,
                x => SolveFast.class_k_start(ws, len, gn, x), t1, tbl,
                Equal.trans(Array<U32>, t1, t2, tbl, Equal.sym(Array<U32>, t2, t1, e2), et2)),
              {==})
          %e_g : R(_)
          CW.facts_of_state(R, G, C, n_root, Con{bc, rest}, gn, hgn, hok,
            SolveFast.class_k_start(ws, len, gn, t1), hloop1, kont)
    case False{}:
      match bc:
        case SolveFast.BigClass{+fb, +ws, +len, clb}:
          (t1, d2) = dpt
          (t2, pe) = d2
          (+e1, +e2) = pe
          +et2 : {t2 == tbl : Array<U32>} =
            Equal.trans(Array<U32>, t2, t1, tbl, e2, e1)
          +hlenc : {len == Groups.len_words(SolveFast.cwords_words(ws)) : Nat} =
            NatProof.NatPrf.is_eq_true(len,
              Groups.len_words(SolveFast.cwords_words(ws)),
              Logic.Proof.and_true_r(FT.FT.cwords_ok_b(G, C, n_root, ws),
                Nat.is_eq(len, Groups.len_words(SolveFast.cwords_words(ws))), hh))
          +htbl2 : FT.FT.TblOk(G, C, n_root, t1) =
            FT.FT.tbl_ok_transport(G, C, n_root, tbl, t1,
              Equal.sym(Array<U32>, t1, tbl, e1), htbl)
          +e_g : {SolveFast.ck_cheap(CW.head_len(Con{bc, rest}), t1)
                  == SolveFast.class_k_opt(big, CW.head_ws(Con{bc, rest}),
                       CW.head_len(Con{bc, rest}), gn, tbl)
                  : SolveFast.CKRes} =
            Equal.cong(Array<U32>, SolveFast.CKRes,
              x => SolveFast.ck_cheap(CW.head_len(Con{bc, rest}), x), t1, tbl, e1)
          %e_g : R(_)
          kont(SolveFast.ck_cheap(CW.head_len(Con{bc, rest}), t1), htbl2,
            CW.prend_cheap(G, C, n_root, Con{bc, rest}, t1, hok, htbl2))

# The capacity invariant of one phase-zero step: the gain grows by the
# difference between the raised bound and the depth bound, which is at most
# the slack of the class that is being consumed.
def CW.inv_step(+dep: Nat, +clb2: Nat, +cc: Nat, +gain: Nat, +gain2: Nat,
    +total0: Nat, +slack_rest: Nat, +capv: Nat,
    +hgain2: {gain2 == Nat.add(gain, Nat.sub(clb2, dep)) : Nat},
    +hstep: {Nat.is_le(clb2, cc) == True{} : Bool},
    +hdepc: {Nat.is_le(dep, cc) == True{} : Bool},
    +hinv: {Nat.is_le(Nat.add(Nat.add(total0, gain),
              Nat.add(Nat.sub(cc, dep), slack_rest)), capv) == True{} : Bool}) ->
  {Nat.is_le(Nat.add(Nat.add(total0, gain2), slack_rest), capv)
   == True{} : Bool}:
  +e0 : {cc == Nat.add(Nat.sub(cc, dep), dep) : Nat} =
    Equal.trans(Nat, cc, Nat.add(dep, Nat.sub(cc, dep)),
      Nat.add(Nat.sub(cc, dep), dep),
      Equal.sym(Nat, Nat.add(dep, Nat.sub(cc, dep)), cc,
        FC.FC.add_sub_of_le(cc, dep, hdepc)),
      NatProof.NatPrf.add_comm(dep, Nat.sub(cc, dep)))
  +hdep : {Nat.is_le(dep, Nat.add(Nat.sub(cc, dep), dep)) == True{} : Bool} =
    NatProof.Nat.is_le_eq_r(dep, cc, Nat.add(Nat.sub(cc, dep), dep), e0, hdepc)
  +hcc : {Nat.is_le(cc, Nat.add(Nat.sub(cc, dep), dep)) == True{} : Bool} =
    NatProof.Nat.is_le_eq_r(cc, cc, Nat.add(Nat.sub(cc, dep), dep), e0,
      NatProof.Nat.is_le_refl(cc))
  +hstep2 : {Nat.is_le(clb2, Nat.add(Nat.sub(cc, dep), dep)) == True{} : Bool} =
    NatProof.Nat.is_le_trans(clb2, cc, Nat.add(Nat.sub(cc, dep), dep),
      hstep, hcc)
  +hsub : {Nat.is_le(Nat.sub(clb2, dep), Nat.sub(cc, dep)) == True{} : Bool} =
    LBS.LBS.sub_le_of_le_add(clb2, Nat.sub(cc, dep), dep, hstep2)
  +hg1 : {Nat.is_le(Nat.add(gain, Nat.sub(clb2, dep)),
                    Nat.add(gain, Nat.sub(cc, dep))) == True{} : Bool} =
    FT.FT.nat_add_le_add(gain, gain, Nat.sub(clb2, dep), Nat.sub(cc, dep),
      NatProof.Nat.is_le_refl(gain), hsub)
  +hg2 : {Nat.is_le(Nat.add(Nat.add(total0, gain), Nat.sub(clb2, dep)),
                    Nat.add(Nat.add(total0, gain), Nat.sub(cc, dep)))
          == True{} : Bool} =
    FT.FT.nat_add_le_add(Nat.add(total0, gain), Nat.add(total0, gain),
      Nat.sub(clb2, dep), Nat.sub(cc, dep),
      NatProof.Nat.is_le_refl(Nat.add(total0, gain)), hsub)
  +hmid : {Nat.is_le(Nat.add(Nat.add(Nat.add(total0, gain),
               Nat.sub(clb2, dep)), slack_rest),
             Nat.add(Nat.add(Nat.add(total0, gain),
               Nat.sub(cc, dep)), slack_rest)) == True{} : Bool} =
    FT.FT.nat_add_le_add(Nat.add(Nat.add(total0, gain), Nat.sub(clb2, dep)),
      Nat.add(Nat.add(total0, gain), Nat.sub(cc, dep)), slack_rest, slack_rest,
      hg2, NatProof.Nat.is_le_refl(slack_rest))
  +eNa : {Nat.add(Nat.add(Nat.add(total0, gain), Nat.sub(clb2, dep)),
             slack_rest)
          == Nat.add(Nat.add(total0, Nat.add(gain, Nat.sub(clb2, dep))),
               slack_rest) : Nat} =
    Equal.cong(Nat, Nat, x => Nat.add(x, slack_rest),
      Nat.add(Nat.add(total0, gain), Nat.sub(clb2, dep)),
      Nat.add(total0, Nat.add(gain, Nat.sub(clb2, dep))),
      NatProof.NatPrf.add_assoc(total0, gain, Nat.sub(clb2, dep)))
  +eNb : {Nat.add(Nat.add(total0, Nat.add(gain, Nat.sub(clb2, dep))),
             slack_rest)
          == Nat.add(Nat.add(total0, gain2), slack_rest) : Nat} =
    Equal.cong(Nat, Nat,
      x => Nat.add(Nat.add(total0, x), slack_rest),
      Nat.add(gain, Nat.sub(clb2, dep)), gain2,
      Equal.sym(Nat, gain2, Nat.add(gain, Nat.sub(clb2, dep)), hgain2))
  +eN : {Nat.add(Nat.add(Nat.add(total0, gain), Nat.sub(clb2, dep)),
            slack_rest)
         == Nat.add(Nat.add(total0, gain2), slack_rest) : Nat} =
    Equal.trans(Nat,
      Nat.add(Nat.add(Nat.add(total0, gain), Nat.sub(clb2, dep)), slack_rest),
      Nat.add(Nat.add(total0, Nat.add(gain, Nat.sub(clb2, dep))), slack_rest),
      Nat.add(Nat.add(total0, gain2), slack_rest), eNa, eNb)
  +eM : {Nat.add(Nat.add(Nat.add(total0, gain), Nat.sub(cc, dep)),
            slack_rest)
         == Nat.add(Nat.add(total0, gain),
              Nat.add(Nat.sub(cc, dep), slack_rest)) : Nat} =
    NatProof.NatPrf.add_assoc(Nat.add(total0, gain), Nat.sub(cc, dep),
      slack_rest)
  +h1 : {Nat.is_le(Nat.add(Nat.add(Nat.add(total0, gain),
            Nat.sub(clb2, dep)), slack_rest),
           Nat.add(Nat.add(total0, gain),
             Nat.add(Nat.sub(cc, dep), slack_rest))) == True{} : Bool} =
    NatProof.Nat.is_le_eq_r(
      Nat.add(Nat.add(Nat.add(total0, gain), Nat.sub(clb2, dep)), slack_rest),
      Nat.add(Nat.add(Nat.add(total0, gain), Nat.sub(cc, dep)), slack_rest),
      Nat.add(Nat.add(total0, gain), Nat.add(Nat.sub(cc, dep), slack_rest)),
      eM, hmid)
  +h2 : {Nat.is_le(Nat.add(Nat.add(total0, gain2), slack_rest),
           Nat.add(Nat.add(total0, gain),
             Nat.add(Nat.sub(cc, dep), slack_rest))) == True{} : Bool} =
    NatProof.Nat.is_le_eq_l(
      Nat.add(Nat.add(total0, gain), Nat.add(Nat.sub(cc, dep), slack_rest)),
      Nat.add(Nat.add(Nat.add(total0, gain), Nat.sub(clb2, dep)), slack_rest),
      Nat.add(Nat.add(total0, gain2), slack_rest), eN, h1)
  NatProof.Nat.is_le_trans(Nat.add(Nat.add(total0, gain2), slack_rest),
    Nat.add(Nat.add(total0, gain), Nat.add(Nat.sub(cc, dep), slack_rest)),
    capv, h2, hinv)

# Shifting one class from the accumulator to the source list.
def CW.rev_bigs_shift(+acc: +List<SolveFast.BigClass>, +b: SolveFast.BigClass,
    +rest: +List<SolveFast.BigClass>) ->
  {SolveFast.rev_bigs(b <> acc, rest)
   == SolveFast.rev_bigs(acc, b <> rest) : List<&2, SolveFast.BigClass>}:
  match acc:
    case Nil{}:
      {==}
    case Con{h, t}:
      CW.rev_bigs_shift(t, h, b <> rest)

# ---------------------------------------------------------------------------
# The walk
# ---------------------------------------------------------------------------

# The walk's specification, by induction on its fuel. `total0 + gain + slack`
# stays below `capv`; the stop test relates the best cost to `total0 + gain`;
# the accumulator invariant is `rev_bigs(acc, bs) == bs0`, so a completed walk
# hands back exactly the input class list.
def CW.walk(+fuel: Nat, +G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +bs0: +List<SolveFast.BigClass>, +capv: Nat,
    +best: SolveRef.Best, +gn: Nat,
    +bs: +List<SolveFast.BigClass>, +phase: Nat, stop: Bool,
    +acc: +List<SolveFast.BigClass>, +gain: Nat, +total0: Nat,
    +hgn: {gn == Groups.len_words(G) : Nat},
    +hok: {FH.FH.bigs_ok_b(G, C, n_root, bs) == True{} : Bool},
    +hb: {Nat.is_le(Nat.add(Nat.add(total0, gain), CW.slack(G, bs)), capv)
          == True{} : Bool},
    +hs: {stop == Nat.is_le(SolveFast.best_cost(best), Nat.add(total0, gain))
          : Bool},
    +hacc: {SolveFast.rev_bigs(acc, bs) == bs0
            : List<&2, SolveFast.BigClass>},
    st: SolveFast.CKRes,
    +htbl: CW.TblOf(G, C, n_root, st),
    +hpref: CW.Prend(G, C, n_root, phase, bs, st)) ->
  FH.FH.CapWalkWit(G, C, n_root, bs0, capv, best,
    SolveFast.cap_walk(fuel, bs0, bs, phase, stop, acc, gain, total0, best, gn,
      st)):
  match fuel:
    case 0n:
      match st:
        case SolveFast.CKRes{tbl, k}:
          Arr.DPair{{==}, htbl}
    case 1n+f:
      match bs:
        case Nil{}:
          match phase:
            case 0n:
              match stop:
                case True{}:
                  match st:
                    case SolveFast.CKRes{tbl, k}:
                      Arr.DPair{
                        CW.skip_le(SolveFast.best_cost(best),
                          Nat.add(total0, gain), capv, capv, CW.slack(G, bs),
                          Equal.sym(Bool, True{},
                            Nat.is_le(SolveFast.best_cost(best),
                              Nat.add(total0, gain)), hs),
                          hb, NatProof.Nat.is_le_refl(capv)),
                        htbl}
                case False{}:
                  match st:
                    case SolveFast.CKRes{tbl, k}:
                      Arr.DPair{hacc, htbl}
            case 1n+hp:
              match stop:
                case True{}:
                  match st:
                    case SolveFast.CKRes{tbl, k}:
                      Arr.DPair{
                        CW.skip_le(SolveFast.best_cost(best),
                          Nat.add(total0, gain), capv, capv, CW.slack(G, bs),
                          Equal.sym(Bool, True{},
                            Nat.is_le(SolveFast.best_cost(best),
                              Nat.add(total0, gain)), hs),
                          hb, NatProof.Nat.is_le_refl(capv)),
                        htbl}
                case False{}:
                  match st:
                    case SolveFast.CKRes{tbl, k}:
                      Arr.DPair{hacc, htbl}
        case Con{bc, rest}:
          match bc:
            case SolveFast.BigClass{+fb, +ws, +len, clb}:
              match phase:
                case 1n+hp:
                  match stop:
                    case True{}:
                      match st:
                        case SolveFast.CKRes{tbl, k}:
                          Arr.DPair{
                            CW.skip_le(SolveFast.best_cost(best),
                              Nat.add(total0, gain), capv, capv, CW.slack(G, bs),
                              Equal.sym(Bool, True{},
                                Nat.is_le(SolveFast.best_cost(best),
                                  Nat.add(total0, gain)), hs),
                              hb, NatProof.Nat.is_le_refl(capv)),
                            htbl}
                    case False{}:
                      match st:
                        case SolveFast.CKRes{tbl, k}:
                          +big = Nat.is_le(16n, len)
                          +stop2 = Nat.is_le(SolveFast.best_cost(best),
                            Nat.add(total0, gain))
                          +hh : {FH.FH.big_ok_b(G, C, n_root,
                                   SolveFast.BigClass{fb, ws, len, clb})
                                 == True{} : Bool} =
                            Logic.Proof.and_true_l(FH.FH.big_ok_b(G, C, n_root,
                                SolveFast.BigClass{fb, ws, len, clb}),
                              FH.FH.bigs_ok_b(G, C, n_root, rest), hok)
                          CW.scan_step(
                            st2 => FH.FH.CapWalkWit(G, C, n_root, bs0, capv, best,
                              SolveFast.cap_walk(f, bs0, bs, 0n, stop2, acc,
                                gain, total0, best, gn, st2)),
                            G, C, n_root, big,
                            SolveFast.BigClass{fb, ws, len, clb}, rest, gn,
                            hgn, hh, hok, tbl, Arr.Arr.dup(U32, tbl), htbl,
                            st2 => htbl2 => hpref2 =>
                              CW.walk(f, G, C, n_root, bs0, capv, best, gn,
                                bs, 0n, stop2, acc, gain, total0, hgn, hok,
                                hb, {==}, hacc, st2, htbl2, hpref2))
                case 0n:
                  match stop:
                    case True{}:
                      match st:
                        case SolveFast.CKRes{tbl, k}:
                          Arr.DPair{
                            CW.skip_le(SolveFast.best_cost(best),
                              Nat.add(total0, gain), capv, capv, CW.slack(G, bs),
                              Equal.sym(Bool, True{},
                                Nat.is_le(SolveFast.best_cost(best),
                                  Nat.add(total0, gain)), hs),
                              hb, NatProof.Nat.is_le_refl(capv)),
                            htbl}
                    case False{}:
                      match st:
                        case SolveFast.CKRes{tbl, +k}:
                          +dep = CW.dep(len)
                          +clb2 = Nat.max(dep, SolveFast.capbound(len, k))
                          +gain2 = Nat.add(gain, Nat.sub(clb2, dep))
                          +stop2 = Nat.is_le(SolveFast.best_cost(best),
                            Nat.add(total0, gain2))
                          +cc = FH.FH.cap_class(G,
                            SolveFast.cwords_words(ws))
                          +hstep : {Nat.is_le(clb2, cc) == True{} : Bool} =
                            Arr.Arr.dpair_r(FT.FT.TblOk(G, C, n_root, tbl),
                              {Nat.is_le(Nat.max(CW.dep(len),
                                  SolveFast.capbound(len, k)),
                                 FH.FH.cap_class(G,
                                   SolveFast.cwords_words(ws)))
                               == True{} : Bool}, hpref)
                          +hh0 : {FH.FH.big_ok_b(G, C, n_root,
                                    SolveFast.BigClass{fb, ws, len, clb})
                                  == True{} : Bool} =
                            Logic.Proof.and_true_l(FH.FH.big_ok_b(G, C, n_root,
                                SolveFast.BigClass{fb, ws, len, clb}),
                              FH.FH.bigs_ok_b(G, C, n_root, rest), hok)
                          +hlen : {len == Groups.len_words(
                                     SolveFast.cwords_words(ws)) : Nat} =
                            NatProof.NatPrf.is_eq_true(len,
                              Groups.len_words(SolveFast.cwords_words(ws)),
                              Logic.Proof.and_true_r(
                                FT.FT.cwords_ok_b(G, C, n_root, ws),
                                Nat.is_eq(len, Groups.len_words(
                                  SolveFast.cwords_words(ws))), hh0))
                          +hdepc : {Nat.is_le(dep, cc) == True{} : Bool} =
                            CW.dep_le_class_eq(G, len,
                              SolveFast.cwords_words(ws), hlen)
                          +hinv2 : {Nat.is_le(Nat.add(Nat.add(total0, gain2),
                                      CW.slack(G, rest)), capv)
                                    == True{} : Bool} =
                            CW.inv_step(dep, clb2, cc, gain, gain2, total0,
                              CW.slack(G, rest), capv, {==}, hstep, hdepc, hb)
                          +hrest : {FH.FH.bigs_ok_b(G, C, n_root, rest)
                                    == True{} : Bool} =
                            Logic.Proof.and_true_r(FH.FH.big_ok_b(G, C, n_root,
                                SolveFast.BigClass{fb, ws, len, clb}),
                              FH.FH.bigs_ok_b(G, C, n_root, rest), hok)
                          +hacc2 : {SolveFast.rev_bigs(
                                      SolveFast.BigClass{fb, ws, len, clb}
                                      <> acc, rest) == bs0
                                    : List<&2, SolveFast.BigClass>} =
                            Equal.trans(List<&2, SolveFast.BigClass>,
                              SolveFast.rev_bigs(
                                SolveFast.BigClass{fb, ws, len, clb} <> acc,
                                rest),
                              SolveFast.rev_bigs(acc,
                                SolveFast.BigClass{fb, ws, len, clb} <> rest),
                              bs0,
                              CW.rev_bigs_shift(acc,
                                SolveFast.BigClass{fb, ws, len, clb}, rest),
                              hacc)
                          +htbl2 : CW.TblOf(G, C, n_root,
                              SolveFast.CKRes{tbl, k}) =
                            Arr.Arr.dpair_l(FT.FT.TblOk(G, C, n_root, tbl),
                              {Nat.is_le(Nat.max(CW.dep(len),
                                  SolveFast.capbound(len, k)),
                                 FH.FH.cap_class(G,
                                   SolveFast.cwords_words(ws)))
                               == True{} : Bool}, hpref)
                          CW.walk(f, G, C, n_root, bs0, capv, best, gn,
                            rest, 1n, stop2,
                            SolveFast.BigClass{fb, ws, len, clb} <> acc,
                            gain2, total0, hgn, hrest, hinv2, {==}, hacc2,
                            SolveFast.CKRes{tbl, k}, htbl2, Unit{})

# `a + (b + c) = b + (a + c)`.
def CW.add3_shift(+a: Nat, +b: Nat, +c: Nat) ->
  {Nat.add(a, Nat.add(b, c)) == Nat.add(b, Nat.add(a, c)) : Nat}:
  Equal.trans(Nat, Nat.add(a, Nat.add(b, c)), Nat.add(Nat.add(a, b), c),
    Nat.add(b, Nat.add(a, c)),
    Equal.sym(Nat, Nat.add(Nat.add(a, b), c), Nat.add(a, Nat.add(b, c)),
      NatProof.NatPrf.add_assoc(a, b, c)),
    Equal.trans(Nat, Nat.add(Nat.add(a, b), c), Nat.add(Nat.add(b, a), c),
      Nat.add(b, Nat.add(a, c)),
      Equal.cong(Nat, Nat, x => Nat.add(x, c),
        Nat.add(a, b), Nat.add(b, a), NatProof.NatPrf.add_comm(a, b)),
      NatProof.NatPrf.add_assoc(b, a, c)))

# A finished three-candidate class has exactly three words.
def CW.done_three_len(+G: +List<+List<Nat>>, +ws: +List<+List<Nat>>,
    +tree: Tree.Tree, +cost: Nat,
    +hdws: {FH.FH.done_ws_ok_b(G, ws, tree, cost) == True{} : Bool}) ->
  {Groups.len_words(ws) == 3n : Nat}:
  match ws:
    case Nil{}:
      Empty.absurd({Groups.len_words(Nil{}) == 3n : Nat},
        Logic.Proof.false_ne_true(hdws))
    case Con{w1, t1}:
      match t1:
        case Nil{}:
          Empty.absurd({Groups.len_words(Con{w1, Nil{}}) == 3n : Nat},
            Logic.Proof.false_ne_true(hdws))
        case Con{w2, t2}:
          match t2:
            case Nil{}:
              Empty.absurd(
                {Groups.len_words(Con{w1, Con{w2, Nil{}}}) == 3n : Nat},
                Logic.Proof.false_ne_true(hdws))
            case Con{w3, t3}:
              match t3:
                case Nil{}:
                  {==}
                case Con{w4, t4}:
                  Empty.absurd(
                    {Groups.len_words(
                       Con{w1, Con{w2, Con{w3, Con{w4, t4}}}}) == 3n : Nat},
                    Logic.Proof.false_ne_true(hdws))

# The class-independent part of the bound, compared with the class fold: this
# is the `hb` premise of `CW.walk` at the initial state.
def CW.base_le(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n_root: Nat,
    +has_buf: Bool, +nodup: Bool, +n: Nat,
    +ig: +List<Groups.Group>, +items: +List<SolveFast.Item>,
    +hbm: FH.FH.BodyMatch(G, C, n_root, has_buf, nodup, n, ig, items)) ->
  {Nat.is_le(SolveFast.cap_base(n, items),
     Nat.add(n, FH.FH.cap_fold(G, ig))) == True{} : Bool}:
  match ig:
    case Nil{}:
      %Equal.sym(+List<SolveFast.Item>, items, SolveFast.End{} <> Nil{}, hbm) :
        {Nat.is_le(SolveFast.cap_base(n, _),
           Nat.add(n, FH.FH.cap_fold(G, Nil{}))) == True{} : Bool}
      NatProof.Nat.is_le_refl(Nat.add(n, 0n))
    case Con{gp, restg}:
      match gp:
        case Groups.Group{+fb, +ws}:
          match items:
            case Nil{}:
              Empty.absurd(
                {Nat.is_le(SolveFast.cap_base(n, Nil{}),
                   Nat.add(n, FH.FH.cap_fold(G, Groups.Group{fb, ws} <> restg)))
                 == True{} : Bool}, hbm)
            case Con{it, restb}:
              match it:
                case SolveFast.Begin{g2}:
                  Empty.absurd(
                    {Nat.is_le(SolveFast.cap_base(n, SolveFast.Begin{g2} <> restb),
                       Nat.add(n,
                         FH.FH.cap_fold(G, Groups.Group{fb, ws} <> restg)))
                     == True{} : Bool}, hbm)
                case SolveFast.OneItem{+f, +w}:
                  +hb1 = Arr.Arr.dpair_r({f == fb : +List<Feedback.Color>},
                    Arr.Arr.DPair<{ws == w <> Nil{} : +List<+List<Nat>>},
                      FH.FH.BodyMatch(G, C, n_root, has_buf, nodup, n, restg,
                        restb)>, hbm)
                  +ews = Arr.Arr.dpair_l({ws == w <> Nil{} : +List<+List<Nat>>},
                    FH.FH.BodyMatch(G, C, n_root, has_buf, nodup, n, restg,
                      restb), hb1)
                  +hbm2 = Arr.Arr.dpair_r({ws == w <> Nil{} : +List<+List<Nat>>},
                    FH.FH.BodyMatch(G, C, n_root, has_buf, nodup, n, restg,
                      restb), hb1)
                  +ih = CW.base_le(G, C, n_root, has_buf, nodup, n, restg,
                    restb, hbm2)
                  +elw : {Groups.len_words(w <> Nil{}) == Groups.len_words(ws)
                          : Nat} =
                    Equal.cong(+List<+List<Nat>>, Nat, l => Groups.len_words(l),
                      w <> Nil{}, ws, Equal.sym(+List<+List<Nat>>, ws,
                        w <> Nil{}, ews))
                  +hlen1 : {1n == Groups.len_words(ws) : Nat} =
                    Equal.trans(Nat, 1n, Groups.len_words(w <> Nil{}),
                      Groups.len_words(ws), {==}, elw)
                  +hc : {Nat.is_le(1n, FH.FH.cap_class(G, ws)) == True{} : Bool} =
                    CW.dep_le_class_eq(G, 1n, ws, hlen1)
                  NatProof.Nat.is_le_eq_r(
                    Nat.add(1n, SolveFast.cap_base(n, restb)),
                    Nat.add(FH.FH.cap_class(G, ws),
                      Nat.add(n, FH.FH.cap_fold(G, restg))),
                    Nat.add(n,
                      Nat.add(FH.FH.cap_class(G, ws),
                        FH.FH.cap_fold(G, restg))),
                    CW.add3_shift(FH.FH.cap_class(G, ws), n,
                      FH.FH.cap_fold(G, restg)),
                    FT.FT.nat_add_le_add(1n, FH.FH.cap_class(G, ws),
                      SolveFast.cap_base(n, restb),
                      Nat.add(n, FH.FH.cap_fold(G, restg)), hc, ih))
                case SolveFast.TwoItem{+f, +w1, +w2}:
                  +hb1 = Arr.Arr.dpair_r({nodup == True{} : Bool},
                    Arr.Arr.DPair<{f == fb : +List<Feedback.Color>},
                      Arr.Arr.DPair<
                        {ws == w1 <> (w2 <> Nil{}) : +List<+List<Nat>>},
                        FH.FH.BodyMatch(G, C, n_root, has_buf, nodup, n, restg,
                          restb)>>, hbm)
                  +hb2 = Arr.Arr.dpair_r({f == fb : +List<Feedback.Color>},
                    Arr.Arr.DPair<
                      {ws == w1 <> (w2 <> Nil{}) : +List<+List<Nat>>},
                      FH.FH.BodyMatch(G, C, n_root, has_buf, nodup, n, restg,
                        restb)>, hb1)
                  +ews = Arr.Arr.dpair_l(
                    {ws == w1 <> (w2 <> Nil{}) : +List<+List<Nat>>},
                    FH.FH.BodyMatch(G, C, n_root, has_buf, nodup, n, restg,
                      restb), hb2)
                  +hbm2 = Arr.Arr.dpair_r(
                    {ws == w1 <> (w2 <> Nil{}) : +List<+List<Nat>>},
                    FH.FH.BodyMatch(G, C, n_root, has_buf, nodup, n, restg,
                      restb), hb2)
                  +ih = CW.base_le(G, C, n_root, has_buf, nodup, n, restg,
                    restb, hbm2)
                  +elw : {Groups.len_words(w1 <> (w2 <> Nil{}))
                          == Groups.len_words(ws) : Nat} =
                    Equal.cong(+List<+List<Nat>>, Nat, l => Groups.len_words(l),
                      w1 <> (w2 <> Nil{}), ws,
                      Equal.sym(+List<+List<Nat>>, ws, w1 <> (w2 <> Nil{}), ews))
                  +hlen2 : {2n == Groups.len_words(ws) : Nat} =
                    Equal.trans(Nat, 2n, Groups.len_words(w1 <> (w2 <> Nil{})),
                      Groups.len_words(ws), {==}, elw)
                  +hc : {Nat.is_le(3n, FH.FH.cap_class(G, ws)) == True{} : Bool} =
                    CW.dep_le_class_eq(G, 2n, ws, hlen2)
                  NatProof.Nat.is_le_eq_r(
                    Nat.add(3n, SolveFast.cap_base(n, restb)),
                    Nat.add(FH.FH.cap_class(G, ws),
                      Nat.add(n, FH.FH.cap_fold(G, restg))),
                    Nat.add(n,
                      Nat.add(FH.FH.cap_class(G, ws),
                        FH.FH.cap_fold(G, restg))),
                    CW.add3_shift(FH.FH.cap_class(G, ws), n,
                      FH.FH.cap_fold(G, restg)),
                    FT.FT.nat_add_le_add(3n, FH.FH.cap_class(G, ws),
                      SolveFast.cap_base(n, restb),
                      Nat.add(n, FH.FH.cap_fold(G, restg)), hc, ih))
                case SolveFast.DoneItem{+f, +tree, +cost}:
                  +hb1 = Arr.Arr.dpair_r({nodup == True{} : Bool},
                    Arr.Arr.DPair<{f == fb : +List<Feedback.Color>},
                      Arr.Arr.DPair<
                        {FH.FH.done_ws_ok_b(G, ws, tree, cost) == True{} : Bool},
                        FH.FH.BodyMatch(G, C, n_root, has_buf, nodup, n, restg,
                          restb)>>, hbm)
                  +hb2 = Arr.Arr.dpair_r({f == fb : +List<Feedback.Color>},
                    Arr.Arr.DPair<
                      {FH.FH.done_ws_ok_b(G, ws, tree, cost) == True{} : Bool},
                      FH.FH.BodyMatch(G, C, n_root, has_buf, nodup, n, restg,
                        restb)>, hb1)
                  +hdws = Arr.Arr.dpair_l(
                    {FH.FH.done_ws_ok_b(G, ws, tree, cost) == True{} : Bool},
                    FH.FH.BodyMatch(G, C, n_root, has_buf, nodup, n, restg,
                      restb), hb2)
                  +hbm2 = Arr.Arr.dpair_r(
                    {FH.FH.done_ws_ok_b(G, ws, tree, cost) == True{} : Bool},
                    FH.FH.BodyMatch(G, C, n_root, has_buf, nodup, n, restg,
                      restb), hb2)
                  +ih = CW.base_le(G, C, n_root, has_buf, nodup, n, restg,
                    restb, hbm2)
                  +hlw : {Groups.len_words(ws) == 3n : Nat} =
                    CW.done_three_len(G, ws, tree, cost, hdws)
                  +hc : {Nat.is_le(5n, FH.FH.cap_class(G, ws)) == True{} : Bool} =
                    CW.dep_le_class_eq(G, 3n, ws,
                      Equal.sym(Nat, Groups.len_words(ws), 3n, hlw))
                  NatProof.Nat.is_le_eq_r(
                    Nat.add(5n, SolveFast.cap_base(n, restb)),
                    Nat.add(FH.FH.cap_class(G, ws),
                      Nat.add(n, FH.FH.cap_fold(G, restg))),
                    Nat.add(n,
                      Nat.add(FH.FH.cap_class(G, ws),
                        FH.FH.cap_fold(G, restg))),
                    CW.add3_shift(FH.FH.cap_class(G, ws), n,
                      FH.FH.cap_fold(G, restg)),
                    FT.FT.nat_add_le_add(5n, FH.FH.cap_class(G, ws),
                      SolveFast.cap_base(n, restb),
                      Nat.add(n, FH.FH.cap_fold(G, restg)), hc, ih))
                case SolveFast.ClassItem{+f, +cws, +wlen, +tlb}:
                  match restb:
                    case Nil{}:
                      Empty.absurd(
                        {Nat.is_le(
                           SolveFast.cap_base(n,
                             SolveFast.ClassItem{f, cws, wlen, tlb} <> Nil{}),
                           Nat.add(n,
                             FH.FH.cap_fold(G, Groups.Group{fb, ws} <> restg)))
                         == True{} : Bool}, hbm)
                    case Con{it2, restb2}:
                      match it2:
                        case SolveFast.Add{+f2, +tlb2}:
                          +hb1 = Arr.Arr.dpair_r(
                            {f == fb : +List<Feedback.Color>},
                            Arr.Arr.DPair<{f2 == fb : +List<Feedback.Color>},
                              Arr.Arr.DPair<
                                {SolveFast.cwords_words(cws) == ws
                                 : +List<+List<Nat>>},
                                Arr.Arr.DPair<
                                  {wlen == Groups.len_words(ws) : Nat},
                                  Arr.Arr.DPair<
                                    {FH.FH.cwords_ok_if(has_buf, G, C, n_root,
                                       cws) == True{} : Bool},
                                    Arr.Arr.DPair<
                                      {tlb == FH.FH.body_lb(nodup, n, restb2)
                                       : Nat},
                                      Arr.Arr.DPair<
                                        {tlb2 == tlb : Nat},
                                        FH.FH.BodyMatch(G, C, n_root, has_buf,
                                          nodup, n, restg, restb2)>>>>>>, hbm)
                          +hb2 = Arr.Arr.dpair_r(
                            {f2 == fb : +List<Feedback.Color>},
                            Arr.Arr.DPair<
                              {SolveFast.cwords_words(cws) == ws
                               : +List<+List<Nat>>},
                              Arr.Arr.DPair<
                                {wlen == Groups.len_words(ws) : Nat},
                                Arr.Arr.DPair<
                                  {FH.FH.cwords_ok_if(has_buf, G, C, n_root,
                                     cws) == True{} : Bool},
                                  Arr.Arr.DPair<
                                    {tlb == FH.FH.body_lb(nodup, n, restb2)
                                     : Nat},
                                    Arr.Arr.DPair<
                                      {tlb2 == tlb : Nat},
                                      FH.FH.BodyMatch(G, C, n_root, has_buf,
                                        nodup, n, restg, restb2)>>>>>, hb1)
                          +hb3 = Arr.Arr.dpair_r(
                            {SolveFast.cwords_words(cws) == ws
                             : +List<+List<Nat>>},
                            Arr.Arr.DPair<
                              {wlen == Groups.len_words(ws) : Nat},
                              Arr.Arr.DPair<
                                {FH.FH.cwords_ok_if(has_buf, G, C, n_root, cws)
                                 == True{} : Bool},
                                Arr.Arr.DPair<
                                  {tlb == FH.FH.body_lb(nodup, n, restb2)
                                   : Nat},
                                  Arr.Arr.DPair<
                                    {tlb2 == tlb : Nat},
                                    FH.FH.BodyMatch(G, C, n_root, has_buf,
                                      nodup, n, restg, restb2)>>>>, hb2)
                          +hwlen = Arr.Arr.dpair_l(
                            {wlen == Groups.len_words(ws) : Nat},
                            Arr.Arr.DPair<
                              {FH.FH.cwords_ok_if(has_buf, G, C, n_root, cws)
                               == True{} : Bool},
                              Arr.Arr.DPair<
                                {tlb == FH.FH.body_lb(nodup, n, restb2) : Nat},
                                Arr.Arr.DPair<
                                  {tlb2 == tlb : Nat},
                                  FH.FH.BodyMatch(G, C, n_root, has_buf,
                                    nodup, n, restg, restb2)>>>, hb3)
                          +hb4 = Arr.Arr.dpair_r(
                            {wlen == Groups.len_words(ws) : Nat},
                            Arr.Arr.DPair<
                              {FH.FH.cwords_ok_if(has_buf, G, C, n_root, cws)
                               == True{} : Bool},
                              Arr.Arr.DPair<
                                {tlb == FH.FH.body_lb(nodup, n, restb2) : Nat},
                                Arr.Arr.DPair<
                                  {tlb2 == tlb : Nat},
                                  FH.FH.BodyMatch(G, C, n_root, has_buf,
                                    nodup, n, restg, restb2)>>>, hb3)
                          +hb5 = Arr.Arr.dpair_r(
                            {FH.FH.cwords_ok_if(has_buf, G, C, n_root, cws)
                             == True{} : Bool},
                            Arr.Arr.DPair<
                              {tlb == FH.FH.body_lb(nodup, n, restb2) : Nat},
                              Arr.Arr.DPair<
                                {tlb2 == tlb : Nat},
                                FH.FH.BodyMatch(G, C, n_root, has_buf,
                                  nodup, n, restg, restb2)>>, hb4)
                          +hb6 = Arr.Arr.dpair_r(
                            {tlb == FH.FH.body_lb(nodup, n, restb2) : Nat},
                            Arr.Arr.DPair<{tlb2 == tlb : Nat},
                              FH.FH.BodyMatch(G, C, n_root, has_buf, nodup, n,
                                restg, restb2)>, hb5)
                          +hbm2 = Arr.Arr.dpair_r(
                            {tlb2 == tlb : Nat},
                            FH.FH.BodyMatch(G, C, n_root, has_buf, nodup, n,
                              restg, restb2), hb6)
                          +ih = CW.base_le(G, C, n_root, has_buf, nodup, n,
                            restg, restb2, hbm2)
                          +hc : {Nat.is_le(CW.dep(wlen),
                                   FH.FH.cap_class(G, ws))
                                 == True{} : Bool} =
                            CW.dep_le_class_eq(G, wlen, ws, hwlen)
                          +elhs : {Nat.add(CW.dep(wlen),
                                     SolveFast.cap_base(n, restb2))
                                   == SolveFast.cap_base(n, it <> restb) : Nat} =
                            {==}
                          %elhs :
                            {Nat.is_le(_,
                               Nat.add(n, FH.FH.cap_fold(G,
                                 Groups.Group{fb, ws} <> restg)))
                             == True{} : Bool}
                          NatProof.Nat.is_le_eq_r(
                            Nat.add(CW.dep(wlen),
                              SolveFast.cap_base(n, restb2)),
                            Nat.add(FH.FH.cap_class(G, ws),
                              Nat.add(n, FH.FH.cap_fold(G, restg))),
                            Nat.add(n,
                              Nat.add(FH.FH.cap_class(G, ws),
                                FH.FH.cap_fold(G, restg))),
                            CW.add3_shift(FH.FH.cap_class(G, ws), n,
                              FH.FH.cap_fold(G, restg)),
                            FT.FT.nat_add_le_add(CW.dep(wlen),
                              FH.FH.cap_class(G, ws),
                              SolveFast.cap_base(n, restb2),
                              Nat.add(n, FH.FH.cap_fold(G, restg)), hc, ih))
                        case SolveFast.Begin{g2}:
                          Empty.absurd(
                            {Nat.is_le(
                               SolveFast.cap_base(n,
                                 SolveFast.ClassItem{f, cws, wlen, tlb}
                                 <> (SolveFast.Begin{g2} <> restb2)),
                               Nat.add(n,
                                 FH.FH.cap_fold(G,
                                   Groups.Group{fb, ws} <> restg)))
                             == True{} : Bool}, hbm)
                        case SolveFast.ClassItem{_, _, _, _}:
                          Empty.absurd(
                            {Nat.is_le(
                               SolveFast.cap_base(n,
                                 SolveFast.ClassItem{f, cws, wlen, tlb} <> restb),
                               Nat.add(n,
                                 FH.FH.cap_fold(G,
                                   Groups.Group{fb, ws} <> restg)))
                             == True{} : Bool}, hbm)
                        case SolveFast.OneItem{_, _}:
                          Empty.absurd(
                            {Nat.is_le(
                               SolveFast.cap_base(n,
                                 SolveFast.ClassItem{f, cws, wlen, tlb} <> restb),
                               Nat.add(n,
                                 FH.FH.cap_fold(G,
                                   Groups.Group{fb, ws} <> restg)))
                             == True{} : Bool}, hbm)
                        case SolveFast.TwoItem{_, _, _}:
                          Empty.absurd(
                            {Nat.is_le(
                               SolveFast.cap_base(n,
                                 SolveFast.ClassItem{f, cws, wlen, tlb} <> restb),
                               Nat.add(n,
                                 FH.FH.cap_fold(G,
                                   Groups.Group{fb, ws} <> restg)))
                             == True{} : Bool}, hbm)
                        case SolveFast.DoneItem{_, _, _}:
                          Empty.absurd(
                            {Nat.is_le(
                               SolveFast.cap_base(n,
                                 SolveFast.ClassItem{f, cws, wlen, tlb} <> restb),
                               Nat.add(n,
                                 FH.FH.cap_fold(G,
                                   Groups.Group{fb, ws} <> restg)))
                             == True{} : Bool}, hbm)
                        case SolveFast.End{}:
                          Empty.absurd(
                            {Nat.is_le(
                               SolveFast.cap_base(n,
                                 SolveFast.ClassItem{f, cws, wlen, tlb}
                                 <> (SolveFast.End{} <> restb2)),
                               Nat.add(n,
                                 FH.FH.cap_fold(G,
                                   Groups.Group{fb, ws} <> restg)))
                             == True{} : Bool}, hbm)
                case SolveFast.Add{_, _}:
                  Empty.absurd(
                    {Nat.is_le(SolveFast.cap_base(n, it <> restb),
                       Nat.add(n,
                         FH.FH.cap_fold(G, Groups.Group{fb, ws} <> restg)))
                     == True{} : Bool}, hbm)
                case SolveFast.End{}:
                  Empty.absurd(
                    {Nat.is_le(SolveFast.cap_base(n, it <> restb),
                       Nat.add(n,
                         FH.FH.cap_fold(G, Groups.Group{fb, ws} <> restg)))
                     == True{} : Bool}, hbm)

# The slack is the class fold minus the depth bounds.
def CW.slack_eq(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n_root: Nat,
    +bs: +List<SolveFast.BigClass>,
    +hok: {FH.FH.bigs_ok_b(G, C, n_root, bs) == True{} : Bool}) ->
  {CW.slack(G, bs)
   == Nat.sub(FH.FH.cap_fold(G, FH.FH.bigs_groups(bs)),
        SolveFast.bigs_depth(bs)) : Nat}:
  +hds = CW.dsum_slack(G, C, n_root, bs, hok)
  +e1 : {Nat.sub(FH.FH.cap_fold(G, FH.FH.bigs_groups(bs)),
            SolveFast.bigs_depth(bs))
         == Nat.sub(Nat.add(SolveFast.bigs_depth(bs), CW.slack(G, bs)),
              SolveFast.bigs_depth(bs)) : Nat} =
    Equal.cong(Nat, Nat, x => Nat.sub(x, SolveFast.bigs_depth(bs)),
      FH.FH.cap_fold(G, FH.FH.bigs_groups(bs)),
      Nat.add(SolveFast.bigs_depth(bs), CW.slack(G, bs)),
      Equal.sym(Nat, Nat.add(SolveFast.bigs_depth(bs), CW.slack(G, bs)),
        FH.FH.cap_fold(G, FH.FH.bigs_groups(bs)), hds))
  +e2 : {Nat.sub(Nat.add(SolveFast.bigs_depth(bs), CW.slack(G, bs)),
            SolveFast.bigs_depth(bs))
         == CW.slack(G, bs) : Nat} =
    Equal.trans(Nat,
      Nat.sub(Nat.add(SolveFast.bigs_depth(bs), CW.slack(G, bs)),
        SolveFast.bigs_depth(bs)),
      Nat.sub(Nat.add(CW.slack(G, bs), SolveFast.bigs_depth(bs)),
        SolveFast.bigs_depth(bs)),
      CW.slack(G, bs),
      Equal.cong(Nat, Nat, x => Nat.sub(x, SolveFast.bigs_depth(bs)),
        Nat.add(SolveFast.bigs_depth(bs), CW.slack(G, bs)),
        Nat.add(CW.slack(G, bs), SolveFast.bigs_depth(bs)),
        NatProof.NatPrf.add_comm(SolveFast.bigs_depth(bs), CW.slack(G, bs))),
      FH.FH.nat_sub_add_cancel(CW.slack(G, bs), SolveFast.bigs_depth(bs)))
  Equal.sym(Nat,
    Nat.sub(FH.FH.cap_fold(G, FH.FH.bigs_groups(bs)),
      SolveFast.bigs_depth(bs)), CW.slack(G, bs), Equal.trans(Nat,
      Nat.sub(FH.FH.cap_fold(G, FH.FH.bigs_groups(bs)),
        SolveFast.bigs_depth(bs)),
      Nat.sub(Nat.add(SolveFast.bigs_depth(bs), CW.slack(G, bs)),
        SolveFast.bigs_depth(bs)),
      CW.slack(G, bs), e1, e2))

# The walk specification as the model's hook: `CW.walk` at the initial state
# (`ck_cheap 0`, phase one, empty accumulator, the class-independent base).
def CW.hook(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>) ->
  FH.FH.CapHookType(G, C):
  gn => n_root => bigs0 => items0 => tbl0 => best => n => capv =>
  hgn => hok => htbl => hb =>
    CW.walk(
      Nat.add(Nat.add(SolveFast.bigs_len(bigs0), SolveFast.bigs_len(bigs0)), 2n),
      G, C, n_root, bigs0, capv, best, gn, bigs0, 1n,
      Nat.is_le(SolveFast.best_cost(best),
        Nat.add(SolveFast.bigs_depth(bigs0), SolveFast.cap_base(n, items0))),
      Nil{}, 0n,
      Nat.add(SolveFast.bigs_depth(bigs0), SolveFast.cap_base(n, items0)),
      hgn, hok,
      NatProof.Nat.is_le_eq_l(
        capv,
        Nat.add(Nat.add(Nat.add(SolveFast.bigs_depth(bigs0),
          SolveFast.cap_base(n, items0)), 0n),
          Nat.sub(FH.FH.cap_fold(G, FH.FH.bigs_groups(bigs0)),
            SolveFast.bigs_depth(bigs0))),
        Nat.add(Nat.add(Nat.add(SolveFast.bigs_depth(bigs0),
          SolveFast.cap_base(n, items0)), 0n), CW.slack(G, bigs0)),
        Equal.cong(Nat, Nat,
          x => Nat.add(Nat.add(Nat.add(SolveFast.bigs_depth(bigs0),
            SolveFast.cap_base(n, items0)), 0n), x),
          Nat.sub(FH.FH.cap_fold(G, FH.FH.bigs_groups(bigs0)),
            SolveFast.bigs_depth(bigs0)), CW.slack(G, bigs0),
          Equal.sym(Nat, CW.slack(G, bigs0),
            Nat.sub(FH.FH.cap_fold(G, FH.FH.bigs_groups(bigs0)),
              SolveFast.bigs_depth(bigs0)),
            CW.slack_eq(G, C, n_root, bigs0, hok))),
        hb),
      Equal.cong(Nat, Bool,
        x => Nat.is_le(SolveFast.best_cost(best), x),
        Nat.add(SolveFast.bigs_depth(bigs0), SolveFast.cap_base(n, items0)),
        Nat.add(Nat.add(SolveFast.bigs_depth(bigs0),
          SolveFast.cap_base(n, items0)), 0n),
        Equal.sym(Nat, Nat.add(Nat.add(SolveFast.bigs_depth(bigs0),
            SolveFast.cap_base(n, items0)), 0n),
          Nat.add(SolveFast.bigs_depth(bigs0), SolveFast.cap_base(n, items0)),
          NatProof.NatPrf.add_zero(
            Nat.add(SolveFast.bigs_depth(bigs0),
              SolveFast.cap_base(n, items0))))),
      {==},
      SolveFast.ck_cheap(0n, tbl0), htbl, Unit{})
