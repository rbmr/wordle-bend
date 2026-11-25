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
import ../src/groups.bend as Groups
import ./fast_hist5.bend as FH
import ./fast_tbl.bend as FT
import ./class_k.bend as CK
import ./cap_lb.bend as CP
import ./lb_capacity.bend as CapProof
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
