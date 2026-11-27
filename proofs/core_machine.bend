# The count machine's steps over the modelled array.
#
# `CM.Store` models the array cells, `CR.CR.*` the meaning of each scratch region
# (count cells, touched list, result, untouched tail).  This file proves one
# step at a time, in the shape `src/core/dcount.bend`'s phases produce: one
# `Array.set` at a cell, then every region's proof for the new array.
#
# Phase 6 is the last step (write the result cell); the candidate pass steps
# (phase 3's two writes) are the same proof with the two other write lemmas.
import Base
import ./core_list.bend as CS
import ./core_nat.bend as CN
import ./core_natlist.bend as CNL
import ./core_store.bend as CMem
import ./core_write.bend as CWrite
import ./core_region.bend as CR
import ./array.bend as Arr
import ./fast_tbl.bend as FT
import ./nat.bend as NatProof

# Phase 6: `Array.set(a, 512, t)` writes the result cell.  The store model
# follows the write, the result cell becomes `t`, the count and touched regions
# and every cell from 768 on are untouched.
def CMm.phase6(+d: Nat, a: Array<U32>, +xs: +List<U32>, +xs0: +List<U32>,
    +t: U32, +nl: +List<Nat>, +tl: +List<Nat>,
    +hd: {Nat.is_lt(d, 32n) == True{} : Bool},
    +hk: {Nat.is_lt(512n, FT.FT.pow2(d)) == True{} : Bool},
    +hlen: {Nat.is_le(Nat.add(0n, FT.FT.pow2(d)), CS.CS.len(xs)) == True{}
            : Bool},
    +hs: CMem.CM.Store(d, 0n, a, xs),
    hcount: CR.CR.Count(0n, 256n, xs, nl),
    htouch: CR.CR.Touch(0n, xs, tl),
    +htle: {Nat.is_lt(Nat.add(256n, CR.CR.nlen(tl)), 512n) == True{} : Bool},
    +hi512: {Nat.is_lt(512n, CS.CS.len(xs)) == True{} : Bool},
    ha: CR.CR.Agree(xs, xs0)) ->
  CMem.CM.Store(d, 0n, Array.set(U32, a, 512, t), CS.CS.set(xs, 512n, t))
  & (CR.CR.Res(CS.CS.set(xs, 512n, t), t)
     & (CR.CR.Count(0n, 256n, CS.CS.set(xs, 512n, t), nl)
        & (CR.CR.Touch(0n, CS.CS.set(xs, 512n, t), tl)
           & CR.CR.Agree(CS.CS.set(xs, 512n, t), xs0)))):
  +hs2 : CMem.CM.Store(d, 0n, Array.set(U32, a, 512, t), CS.CS.set(xs, 512n, t)) =
    CWrite.CW.store_set(d, a, xs, 512n, t, hd, hk, hs, hlen)
  (hs2,
   (CR.CR.res_set(xs, t, hi512),
    (CR.CR.count_set_after(256n, 0n, 512n, t, xs, nl, hcount, {==}),
     (CR.CR.touch_set_above(tl, 0n, 512n, xs, t, htouch, htle),
      CR.CR.agree_after_set(xs, xs0, 512n, t, ha, {==})))))

# The candidate-pass writes, one write per region.  `write_count_region` is the
# mark (`Array.set(a, code, 1)` with `code < 256`), `write_touch_region` is the
# touched-list append (`Array.set(a, 256 + t, code)` with `t = len tl`).  Both
# keep every region they do not write, so the machine's phase 3 is these two
# steps in sequence.

def CMm.write_count_region(+d: Nat, a: Array<U32>, +xs: +List<U32>,
    +xs0: +List<U32>, +c: Nat, +nl: +List<Nat>, +tl: +List<Nat>,
    +hd: {Nat.is_lt(d, 32n) == True{} : Bool},
    +hk: {Nat.is_lt(c, FT.FT.pow2(d)) == True{} : Bool},
    +hlen: {Nat.is_le(Nat.add(0n, FT.FT.pow2(d)), CS.CS.len(xs)) == True{}
            : Bool},
    +hs: CMem.CM.Store(d, 0n, a, xs),
    hcount: CR.CR.Count(0n, 256n, xs, nl),
    htouch: CR.CR.Touch(0n, xs, tl),
    ha: CR.CR.Agree(xs, xs0),
    +hc256: {Nat.is_lt(c, 256n) == True{} : Bool},
    +hend: {Nat.is_lt(Nat.add(0n, 256n), CS.CS.len(xs)) == True{} : Bool}) ->
  CMem.CM.Store(d, 0n, Array.set(U32, a, U32.from_nat(c), 1),
    CS.CS.set(xs, c, 1))
  & (CR.CR.Count(0n, 256n, CS.CS.set(xs, c, 1), c <> nl)
     & (CR.CR.Touch(0n, CS.CS.set(xs, c, 1), tl)
        & CR.CR.Agree(CS.CS.set(xs, c, 1), xs0))):
  +hs2 : CMem.CM.Store(d, 0n, Array.set(U32, a, U32.from_nat(c), 1),
           CS.CS.set(xs, c, 1)) =
    CWrite.CW.store_set(d, a, xs, c, 1, hd, hk, hs, hlen)
  (hs2,
   (CR.CR.count_set_new(256n, 0n, c, xs, nl, hcount, hc256, hend),
    (CR.CR.touch_set_below(tl, 0n, c, xs, 1, htouch, hc256),
     CR.CR.agree_after_set(xs, xs0, c, 1, ha,
       NatProof.Nat.is_lt_le_trans(c, 256n, 768n, hc256, {==})))))

def CMm.write_touch_region(+d: Nat, a: Array<U32>, +xs: +List<U32>,
    +xs0: +List<U32>, +c: Nat, +nl: +List<Nat>, +tl: +List<Nat>,
    +hd: {Nat.is_lt(d, 32n) == True{} : Bool},
    +hk: {Nat.is_lt(Nat.add(256n, CR.CR.nlen(tl)), FT.FT.pow2(d))
          == True{} : Bool},
    +hlen: {Nat.is_le(Nat.add(0n, FT.FT.pow2(d)), CS.CS.len(xs)) == True{}
            : Bool},
    +hs: CMem.CM.Store(d, 0n, a, xs),
    hcount: CR.CR.Count(0n, 256n, xs, nl),
    htouch: CR.CR.Touch(0n, xs, tl),
    ha: CR.CR.Agree(xs, xs0),
    +htle: {Nat.is_lt(Nat.add(256n, CR.CR.nlen(tl)), 512n) == True{} : Bool}) ->
  CMem.CM.Store(d, 0n,
    Array.set(U32, a, U32.from_nat(Nat.add(256n, CR.CR.nlen(tl))),
      U32.from_nat(c)),
    CS.CS.set(xs, Nat.add(256n, CR.CR.nlen(tl)), U32.from_nat(c)))
  & (CR.CR.Count(0n, 256n,
       CS.CS.set(xs, Nat.add(256n, CR.CR.nlen(tl)), U32.from_nat(c)), nl)
     & (CR.CR.Touch(0n,
          CS.CS.set(xs, Nat.add(256n, CR.CR.nlen(tl)), U32.from_nat(c)),
          CR.CR.snoc(c, tl))
        & CR.CR.Agree(
            CS.CS.set(xs, Nat.add(256n, CR.CR.nlen(tl)), U32.from_nat(c)),
            xs0))):
  +hs2 : CMem.CM.Store(d, 0n,
           Array.set(U32, a, U32.from_nat(Nat.add(256n, CR.CR.nlen(tl))),
             U32.from_nat(c)),
           CS.CS.set(xs, Nat.add(256n, CR.CR.nlen(tl)), U32.from_nat(c))) =
    CWrite.CW.store_set(d, a, xs, Nat.add(256n, CR.CR.nlen(tl)),
      U32.from_nat(c), hd, hk, hs, hlen)
  +hk2 : {Nat.is_lt(Nat.add(256n, CR.CR.nlen(tl)), CS.CS.len(xs))
          == True{} : Bool} =
    NatProof.Nat.is_lt_le_trans(Nat.add(256n, CR.CR.nlen(tl)),
      FT.FT.pow2(d), CS.CS.len(xs), hk, hlen)
  +hcle : {Nat.is_le(Nat.add(0n, 256n), Nat.add(256n, CR.CR.nlen(tl)))
           == True{} : Bool} =
    NatProof.Nat.is_le_add_l(0n, CR.CR.nlen(tl), 256n,
      NatProof.Nat.is_le_zero_l(CR.CR.nlen(tl)))
  (hs2,
   (CR.CR.count_set_after(256n, 0n, Nat.add(256n, CR.CR.nlen(tl)),
      U32.from_nat(c), xs, nl, hcount, hcle),
    (CR.CR.touch_append(tl, 0n, Nat.add(256n, CR.CR.nlen(tl)), xs, c, htouch,
       {==}, hk2),
     CR.CR.agree_after_set(xs, xs0, Nat.add(256n, CR.CR.nlen(tl)),
       U32.from_nat(c), ha,
       NatProof.Nat.is_lt_le_trans(Nat.add(256n, CR.CR.nlen(tl)), 512n, 768n,
         htle, {==})))))

# ---------------------------------------------- the machine's own indices ---
#
# The machine's write index is the value it read (`code`) and its slot counter
# (`U32.add(256, t)`), while the lemmas are stated at the ghost indices.  One
# congruence on the write index plus one `CM.store_transport` bridges a step;
# the region predicates are about the ghost list, so they do not move.

def CMm.mark_code_go(+d: Nat, -a: Array<U32>, +xs: +List<U32>,
    +xs0: +List<U32>, +c: Nat, +code: U32, +nl: +List<Nat>, +tl: +List<Nat>,
    +hcode: {code == U32.from_nat(c) : U32},
    r: CMem.CM.Store(d, 0n, Array.set(U32, a, U32.from_nat(c), 1),
         CS.CS.set(xs, c, 1))
       & (CR.CR.Count(0n, 256n, CS.CS.set(xs, c, 1), c <> nl)
          & (CR.CR.Touch(0n, CS.CS.set(xs, c, 1), tl)
             & CR.CR.Agree(CS.CS.set(xs, c, 1), xs0)))) ->
  CMem.CM.Store(d, 0n, Array.set(U32, a, code, 1), CS.CS.set(xs, c, 1))
  & (CR.CR.Count(0n, 256n, CS.CS.set(xs, c, 1), c <> nl)
     & (CR.CR.Touch(0n, CS.CS.set(xs, c, 1), tl)
        & CR.CR.Agree(CS.CS.set(xs, c, 1), xs0))):
  (hs1, rest) = r
  +ea : {Array.set(U32, a, code, 1)
         == Array.set(U32, a, U32.from_nat(c), 1) : Array<U32>} =
    Equal.cong(U32, Array<U32>, z => Array.set(U32, a, z, 1),
      code, U32.from_nat(c), hcode)
  (CMem.CM.store_transport(d, 0n, Array.set(U32, a, U32.from_nat(c), 1),
     Array.set(U32, a, code, 1), CS.CS.set(xs, c, 1),
     Equal.sym(Array<U32>, Array.set(U32, a, code, 1),
       Array.set(U32, a, U32.from_nat(c), 1), ea), hs1),
   rest)

def CMm.mark_code(+d: Nat, a: Array<U32>, +xs: +List<U32>, +xs0: +List<U32>,
    +c: Nat, +code: U32, +nl: +List<Nat>, +tl: +List<Nat>,
    +hcode: {code == U32.from_nat(c) : U32},
    +hd: {Nat.is_lt(d, 32n) == True{} : Bool},
    +hk: {Nat.is_lt(c, FT.FT.pow2(d)) == True{} : Bool},
    +hlen: {Nat.is_le(Nat.add(0n, FT.FT.pow2(d)), CS.CS.len(xs)) == True{}
            : Bool},
    +hs: CMem.CM.Store(d, 0n, a, xs),
    hcount: CR.CR.Count(0n, 256n, xs, nl),
    htouch: CR.CR.Touch(0n, xs, tl),
    ha: CR.CR.Agree(xs, xs0),
    +hc256: {Nat.is_lt(c, 256n) == True{} : Bool},
    +hend: {Nat.is_lt(Nat.add(0n, 256n), CS.CS.len(xs)) == True{} : Bool}) ->
  CMem.CM.Store(d, 0n, Array.set(U32, a, code, 1), CS.CS.set(xs, c, 1))
  & (CR.CR.Count(0n, 256n, CS.CS.set(xs, c, 1), c <> nl)
     & (CR.CR.Touch(0n, CS.CS.set(xs, c, 1), tl)
        & CR.CR.Agree(CS.CS.set(xs, c, 1), xs0))):
  CMm.mark_code_go(d, a, xs, xs0, c, code, nl, tl, hcode,
    CMm.write_count_region(d, a, xs, xs0, c, nl, tl, hd, hk, hlen, hs,
      hcount, htouch, ha, hc256, hend))

def CMm.touch_write_go(+d: Nat, -a: Array<U32>, +xs: +List<U32>,
    +xs0: +List<U32>, +c: Nat, +code: U32, +t: U32, +nl: +List<Nat>,
    +tl: +List<Nat>,
    +htn: {t == U32.from_nat(CR.CR.nlen(tl)) : U32},
    +hcode: {code == U32.from_nat(c) : U32},
    r: CMem.CM.Store(d, 0n,
         Array.set(U32, a, U32.from_nat(Nat.add(256n, CR.CR.nlen(tl))),
           U32.from_nat(c)),
         CS.CS.set(xs, Nat.add(256n, CR.CR.nlen(tl)), U32.from_nat(c)))
       & (CR.CR.Count(0n, 256n,
            CS.CS.set(xs, Nat.add(256n, CR.CR.nlen(tl)), U32.from_nat(c)), nl)
          & (CR.CR.Touch(0n,
               CS.CS.set(xs, Nat.add(256n, CR.CR.nlen(tl)), U32.from_nat(c)),
               CR.CR.snoc(c, tl))
             & CR.CR.Agree(
                 CS.CS.set(xs, Nat.add(256n, CR.CR.nlen(tl)), U32.from_nat(c)),
                 xs0)))) ->
  CMem.CM.Store(d, 0n, Array.set(U32, a, U32.add(256, t), code),
    CS.CS.set(xs, Nat.add(256n, CR.CR.nlen(tl)), U32.from_nat(c)))
  & (CR.CR.Count(0n, 256n,
       CS.CS.set(xs, Nat.add(256n, CR.CR.nlen(tl)), U32.from_nat(c)), nl)
     & (CR.CR.Touch(0n,
          CS.CS.set(xs, Nat.add(256n, CR.CR.nlen(tl)), U32.from_nat(c)),
          CR.CR.snoc(c, tl))
        & CR.CR.Agree(
            CS.CS.set(xs, Nat.add(256n, CR.CR.nlen(tl)), U32.from_nat(c)),
            xs0))):
  (hs1, rest) = r
  +eidx1 : {U32.add(256, t)
            == U32.add(256, U32.from_nat(CR.CR.nlen(tl))) : U32} =
    Equal.cong(U32, U32, z => U32.add(256, z), t,
      U32.from_nat(CR.CR.nlen(tl)), htn)
  +eidx2 : {U32.add(256, U32.from_nat(CR.CR.nlen(tl)))
            == U32.from_nat(Nat.add(256n, CR.CR.nlen(tl))) : U32} =
    FT.FT.u32_add_from_nat(256n, CR.CR.nlen(tl))
  +eidx : {U32.add(256, t)
           == U32.from_nat(Nat.add(256n, CR.CR.nlen(tl))) : U32} =
    Equal.trans(U32, U32.add(256, t),
      U32.add(256, U32.from_nat(CR.CR.nlen(tl))),
      U32.from_nat(Nat.add(256n, CR.CR.nlen(tl))), eidx1, eidx2)
  +e1 : {Array.set(U32, a, U32.add(256, t), code)
         == Array.set(U32, a, U32.from_nat(Nat.add(256n, CR.CR.nlen(tl))),
              code) : Array<U32>} =
    Equal.cong(U32, Array<U32>, z => Array.set(U32, a, z, code),
      U32.add(256, t), U32.from_nat(Nat.add(256n, CR.CR.nlen(tl))), eidx)
  +e2 : {Array.set(U32, a, U32.from_nat(Nat.add(256n, CR.CR.nlen(tl))), code)
         == Array.set(U32, a, U32.from_nat(Nat.add(256n, CR.CR.nlen(tl))),
              U32.from_nat(c)) : Array<U32>} =
    Equal.cong(U32, Array<U32>,
      z => Array.set(U32, a, U32.from_nat(Nat.add(256n, CR.CR.nlen(tl))), z),
      code, U32.from_nat(c), hcode)
  +eall : {Array.set(U32, a, U32.add(256, t), code)
           == Array.set(U32, a, U32.from_nat(Nat.add(256n, CR.CR.nlen(tl))),
                U32.from_nat(c)) : Array<U32>} =
    Equal.trans(Array<U32>, Array.set(U32, a, U32.add(256, t), code),
      Array.set(U32, a, U32.from_nat(Nat.add(256n, CR.CR.nlen(tl))), code),
      Array.set(U32, a, U32.from_nat(Nat.add(256n, CR.CR.nlen(tl))),
        U32.from_nat(c)), e1, e2)
  (CMem.CM.store_transport(d, 0n,
     Array.set(U32, a, U32.from_nat(Nat.add(256n, CR.CR.nlen(tl))),
       U32.from_nat(c)),
     Array.set(U32, a, U32.add(256, t), code),
     CS.CS.set(xs, Nat.add(256n, CR.CR.nlen(tl)), U32.from_nat(c)),
     Equal.sym(Array<U32>, Array.set(U32, a, U32.add(256, t), code),
       Array.set(U32, a, U32.from_nat(Nat.add(256n, CR.CR.nlen(tl))),
         U32.from_nat(c)), eall), hs1),
   rest)

def CMm.write_touch_code(+d: Nat, a: Array<U32>, +xs: +List<U32>,
    +xs0: +List<U32>, +c: Nat, +code: U32, +t: U32, +nl: +List<Nat>,
    +tl: +List<Nat>,
    +htn: {t == U32.from_nat(CR.CR.nlen(tl)) : U32},
    +hcode: {code == U32.from_nat(c) : U32},
    +hd: {Nat.is_lt(d, 32n) == True{} : Bool},
    +hk: {Nat.is_lt(Nat.add(256n, CR.CR.nlen(tl)), FT.FT.pow2(d))
          == True{} : Bool},
    +hlen: {Nat.is_le(Nat.add(0n, FT.FT.pow2(d)), CS.CS.len(xs)) == True{}
            : Bool},
    +hs: CMem.CM.Store(d, 0n, a, xs),
    hcount: CR.CR.Count(0n, 256n, xs, nl),
    htouch: CR.CR.Touch(0n, xs, tl),
    ha: CR.CR.Agree(xs, xs0),
    +htle: {Nat.is_lt(Nat.add(256n, CR.CR.nlen(tl)), 512n) == True{} : Bool}) ->
  CMem.CM.Store(d, 0n, Array.set(U32, a, U32.add(256, t), code),
    CS.CS.set(xs, Nat.add(256n, CR.CR.nlen(tl)), U32.from_nat(c)))
  & (CR.CR.Count(0n, 256n,
       CS.CS.set(xs, Nat.add(256n, CR.CR.nlen(tl)), U32.from_nat(c)), nl)
     & (CR.CR.Touch(0n,
          CS.CS.set(xs, Nat.add(256n, CR.CR.nlen(tl)), U32.from_nat(c)),
          CR.CR.snoc(c, tl))
        & CR.CR.Agree(
            CS.CS.set(xs, Nat.add(256n, CR.CR.nlen(tl)), U32.from_nat(c)),
            xs0))):
  CMm.touch_write_go(d, a, xs, xs0, c, code, t, nl, tl, htn, hcode,
    CMm.write_touch_region(d, a, xs, xs0, c, nl, tl, hd, hk, hlen, hs,
      hcount, htouch, ha, htle))

# Phase 3 as the machine runs it: mark the code's cell, then append the code to
# the touched list at `256 + t`.  Both writes in sequence, with the regions the
# first write established feeding the second.
def CMm.mark_touch_go(+d: Nat, a: Array<U32>, +xs: +List<U32>,
    +xs0: +List<U32>, +c: Nat, +code: U32, +t: U32, +nl: +List<Nat>,
    +tl: +List<Nat>,
    +hcode: {code == U32.from_nat(c) : U32},
    +htn: {t == U32.from_nat(CR.CR.nlen(tl)) : U32},
    +hd: {Nat.is_lt(d, 32n) == True{} : Bool},
    +hk2: {Nat.is_lt(Nat.add(256n, CR.CR.nlen(tl)), FT.FT.pow2(d))
           == True{} : Bool},
    +hlen: {Nat.is_le(Nat.add(0n, FT.FT.pow2(d)), CS.CS.len(xs)) == True{}
            : Bool},
    +htle: {Nat.is_lt(Nat.add(256n, CR.CR.nlen(tl)), 512n) == True{} : Bool},
    r: CMem.CM.Store(d, 0n, Array.set(U32, a, code, 1), CS.CS.set(xs, c, 1))
       & (CR.CR.Count(0n, 256n, CS.CS.set(xs, c, 1), c <> nl)
          & (CR.CR.Touch(0n, CS.CS.set(xs, c, 1), tl)
             & CR.CR.Agree(CS.CS.set(xs, c, 1), xs0)))) ->
  CMem.CM.Store(d, 0n,
    Array.set(U32, Array.set(U32, a, code, 1), U32.add(256, t), code),
    CS.CS.set(CS.CS.set(xs, c, 1), Nat.add(256n, CR.CR.nlen(tl)),
      U32.from_nat(c)))
  & (CR.CR.Count(0n, 256n,
       CS.CS.set(CS.CS.set(xs, c, 1), Nat.add(256n, CR.CR.nlen(tl)),
         U32.from_nat(c)), c <> nl)
     & (CR.CR.Touch(0n,
          CS.CS.set(CS.CS.set(xs, c, 1), Nat.add(256n, CR.CR.nlen(tl)),
            U32.from_nat(c)),
          CR.CR.snoc(c, tl))
        & CR.CR.Agree(
            CS.CS.set(CS.CS.set(xs, c, 1), Nat.add(256n, CR.CR.nlen(tl)),
              U32.from_nat(c)), xs0))):
  (hs1, (hc1, (ht1, ha1))) = r
  +els : {CS.CS.len(CS.CS.set(xs, c, 1)) == CS.CS.len(xs) : Nat} =
    CS.CS.len_set(xs, c, 1)
  +heen : {Nat.is_le(Nat.add(0n, FT.FT.pow2(d)),
            CS.CS.len(CS.CS.set(xs, c, 1)))
           == Nat.is_le(Nat.add(0n, FT.FT.pow2(d)), CS.CS.len(xs)) : Bool} =
    Equal.cong(Nat, Bool, z => Nat.is_le(Nat.add(0n, FT.FT.pow2(d)), z),
      CS.CS.len(CS.CS.set(xs, c, 1)), CS.CS.len(xs), els)
  +hlen2 : {Nat.is_le(Nat.add(0n, FT.FT.pow2(d)),
             CS.CS.len(CS.CS.set(xs, c, 1))) == True{} : Bool} =
    Equal.trans(Bool, Nat.is_le(Nat.add(0n, FT.FT.pow2(d)),
        CS.CS.len(CS.CS.set(xs, c, 1))),
      Nat.is_le(Nat.add(0n, FT.FT.pow2(d)), CS.CS.len(xs)), True{}, heen, hlen)
  CMm.write_touch_code(d, Array.set(U32, a, code, 1), CS.CS.set(xs, c, 1),
    xs0, c, code, t, c <> nl, tl, htn, hcode, hd, hk2, hlen2, hs1, hc1, ht1,
    ha1, htle)

# ------------------------------------------------------ the clear-pass step ---
#
# The clear pass reads a code from the touched list and writes its count cell to
# `0` (`rem_all` in the ghost list, since duplicate candidate lines put the same
# code in it more than once).  The touched list itself is not modified.

def CMm.clear_step_go(+d: Nat, -a: Array<U32>, +xs: +List<U32>,
    +xs0: +List<U32>, +c: Nat, +code: U32, +rest: +List<Nat>,
    +nl: +List<Nat>,
    +hcode: {code == U32.from_nat(c) : U32},
    r: CMem.CM.Store(d, 0n, Array.set(U32, a, U32.from_nat(c), 0),
         CS.CS.set(xs, c, 0))
       & (CR.CR.Count(0n, 256n, CS.CS.set(xs, c, 0), CR.CR.rem_all(c, nl))
          & (CR.CR.Touch(0n, CS.CS.set(xs, c, 0), c <> rest)
             & CR.CR.Agree(CS.CS.set(xs, c, 0), xs0)))) ->
  CMem.CM.Store(d, 0n, Array.set(U32, a, code, 0), CS.CS.set(xs, c, 0))
  & (CR.CR.Count(0n, 256n, CS.CS.set(xs, c, 0), CR.CR.rem_all(c, nl))
     & (CR.CR.Touch(0n, CS.CS.set(xs, c, 0), c <> rest)
        & CR.CR.Agree(CS.CS.set(xs, c, 0), xs0))):
  (hs1, restp) = r
  +ea : {Array.set(U32, a, code, 0)
         == Array.set(U32, a, U32.from_nat(c), 0) : Array<U32>} =
    Equal.cong(U32, Array<U32>, z => Array.set(U32, a, z, 0),
      code, U32.from_nat(c), hcode)
  (CMem.CM.store_transport(d, 0n, Array.set(U32, a, U32.from_nat(c), 0),
     Array.set(U32, a, code, 0), CS.CS.set(xs, c, 0),
     Equal.sym(Array<U32>, Array.set(U32, a, code, 0),
       Array.set(U32, a, U32.from_nat(c), 0), ea), hs1),
   restp)

def CMm.clear_step(+d: Nat, a: Array<U32>, +xs: +List<U32>, +xs0: +List<U32>,
    +c: Nat, +code: U32, +rest: +List<Nat>, +nl: +List<Nat>,
    +hcode: {code == U32.from_nat(c) : U32},
    +hd: {Nat.is_lt(d, 32n) == True{} : Bool},
    +hk: {Nat.is_lt(c, FT.FT.pow2(d)) == True{} : Bool},
    +hlen: {Nat.is_le(Nat.add(0n, FT.FT.pow2(d)), CS.CS.len(xs)) == True{}
            : Bool},
    +hs: CMem.CM.Store(d, 0n, a, xs),
    hcount: CR.CR.Count(0n, 256n, xs, nl),
    htouch: CR.CR.Touch(0n, xs, c <> rest),
    ha: CR.CR.Agree(xs, xs0),
    +hc256: {Nat.is_lt(c, 256n) == True{} : Bool},
    +hend: {Nat.is_lt(Nat.add(0n, 256n), CS.CS.len(xs)) == True{} : Bool}) ->
  CMem.CM.Store(d, 0n, Array.set(U32, a, code, 0), CS.CS.set(xs, c, 0))
  & (CR.CR.Count(0n, 256n, CS.CS.set(xs, c, 0), CR.CR.rem_all(c, nl))
     & (CR.CR.Touch(0n, CS.CS.set(xs, c, 0), c <> rest)
        & CR.CR.Agree(CS.CS.set(xs, c, 0), xs0))):
  +hlt768 : {Nat.is_lt(c, 768n) == True{} : Bool} =
    NatProof.Nat.is_lt_le_trans(c, 256n, 768n, hc256, {==})
  CMm.clear_step_go(d, a, xs, xs0, c, code, rest, nl, hcode,
    (CWrite.CW.store_set(d, a, xs, c, 0, hd, hk, hs, hlen),
     (CR.CR.count_clear(256n, 0n, c, xs, nl, hcount, hc256, hend),
      (CR.CR.touch_set_below(c <> rest, 0n, c, xs, 0, htouch, hc256),
       CR.CR.agree_after_set(xs, xs0, c, 0, ha, hlt768)))))

# ------------------------------------------- the machine's read indices ---
#
# Phase 0 reads the candidate-set cell at `U32.add(o, i)`; the ghost replay
# needs that index as `Nat.add(no, ni)`.  This is the read counterpart of the
# write-index bridges above.

def CMm.add_set_index(+o: U32, +i: U32, +no: Nat, +ni: Nat,
    +ho: {o == U32.from_nat(no) : U32},
    +hi: {i == U32.from_nat(ni) : U32}) ->
  {U32.add(o, i) == U32.from_nat(Nat.add(no, ni)) : U32}:
  +e1 : {U32.add(o, i) == U32.add(U32.from_nat(no), i) : U32} =
    Equal.cong(U32, U32, z => U32.add(z, i), o, U32.from_nat(no), ho)
  +e2 : {U32.add(U32.from_nat(no), i)
         == U32.add(U32.from_nat(no), U32.from_nat(ni)) : U32} =
    Equal.cong(U32, U32, z => U32.add(U32.from_nat(no), z), i,
      U32.from_nat(ni), hi)
  Equal.trans(U32, U32.add(o, i), U32.add(U32.from_nat(no), i),
    U32.from_nat(Nat.add(no, ni)), e1,
    Equal.trans(U32, U32.add(U32.from_nat(no), i),
      U32.add(U32.from_nat(no), U32.from_nat(ni)),
      U32.from_nat(Nat.add(no, ni)), e2,
      FT.FT.u32_add_from_nat(no, ni)))

# Phase 0's read: the value returned for candidate `ni` is the ghost index at
# position `ni` of the candidate set.  `CM.store_read` supplies the cell value
# and `CR.set_get` turns the cell into the candidate index; the only work is
# the index bridge above and the `0 + ni` normalisation of `CR.Set`'s start.
def CMm.read_set_value(+d: Nat, a: Array<U32>, +xs: +List<U32>,
    +idxs: +List<Nat>, +o: U32, +i: U32, +no: Nat, +ni: Nat, +k: Nat,
    +ho: {o == U32.from_nat(no) : U32},
    +hi: {i == U32.from_nat(ni) : U32},
    +hd: {Nat.is_lt(d, 32n) == True{} : Bool},
    +hk: {Nat.is_lt(Nat.add(no, ni), FT.FT.pow2(d)) == True{} : Bool},
    +hs: CMem.CM.Store(d, 0n, a, xs),
    hset: CR.CR.Set(no, k, 0n, xs, idxs),
    +he: {Nat.is_lt(ni, k) == True{} : Bool}) ->
  {Arr.Arr.snd(Array<U32>, U32, Array.get(U32, a, U32.add(o, i)))
   == U32.from_nat(CR.CR.nnth(idxs, ni)) : U32}:
  +eidx : {U32.add(o, i) == U32.from_nat(Nat.add(no, ni)) : U32} =
    CMm.add_set_index(o, i, no, ni, ho, hi)
  +hval : {Arr.Arr.snd(Array<U32>, U32,
             Array.get(U32, a, U32.from_nat(Nat.add(no, ni))))
           == CS.CS.nth(xs, Nat.add(no, ni)) : U32} =
    CMem.CM.store_read(d, a, xs, Nat.add(no, ni), hd, hk, hs)
  +hidx : {Arr.Arr.snd(Array<U32>, U32, Array.get(U32, a, U32.add(o, i)))
           == Arr.Arr.snd(Array<U32>, U32,
                Array.get(U32, a, U32.from_nat(Nat.add(no, ni)))) : U32} =
    Equal.cong(U32, U32,
      z => Arr.Arr.snd(Array<U32>, U32, Array.get(U32, a, z)),
      U32.add(o, i), U32.from_nat(Nat.add(no, ni)), eidx)
  +e0 : {Nat.add(0n, ni) == ni : Nat} = {==}
  +e0a : {Nat.add(no, Nat.add(0n, ni)) == Nat.add(no, ni) : Nat} =
    Equal.cong(Nat, Nat, z => Nat.add(no, z), Nat.add(0n, ni), ni, e0)
  +hsetv : {CS.CS.nth(xs, Nat.add(no, Nat.add(0n, ni)))
            == U32.from_nat(CR.CR.nnth(idxs, ni)) : U32} =
    CR.CR.set_get(no, k, 0n, ni, xs, idxs, hset, he)
  Equal.trans(U32, Arr.Arr.snd(Array<U32>, U32, Array.get(U32, a, U32.add(o, i))),
    Arr.Arr.snd(Array<U32>, U32, Array.get(U32, a, U32.from_nat(Nat.add(no, ni)))),
    U32.from_nat(CR.CR.nnth(idxs, ni)), hidx,
    Equal.trans(U32,
      Arr.Arr.snd(Array<U32>, U32, Array.get(U32, a, U32.from_nat(Nat.add(no, ni)))),
      CS.CS.nth(xs, Nat.add(no, ni)),
      U32.from_nat(CR.CR.nnth(idxs, ni)), hval,
      Equal.trans(U32, CS.CS.nth(xs, Nat.add(no, ni)),
        CS.CS.nth(xs, Nat.add(no, Nat.add(0n, ni))),
        U32.from_nat(CR.CR.nnth(idxs, ni)),
        Equal.cong(Nat, U32, z => CS.CS.nth(xs, z),
          Nat.add(no, ni), Nat.add(no, Nat.add(0n, ni)),
          Equal.sym(Nat, Nat.add(no, Nat.add(0n, ni)), Nat.add(no, ni), e0a)),
        hsetv)))

# Phase 4's read: the touched-list cell at `U32.add(256, cj)`, with the clear
# cursor `cj` as `from_nat(nj)`.  The value is the code at position `nj` of the
# ghost touched list, which is what `CR.touch_get` supplies.
def CMm.read_touch_value(+d: Nat, a: Array<U32>, +xs: +List<U32>,
    +tl: +List<Nat>, +cj: U32, +nj: Nat,
    +hcj: {cj == U32.from_nat(nj) : U32},
    +hd: {Nat.is_lt(d, 32n) == True{} : Bool},
    +hk: {Nat.is_lt(Nat.add(256n, nj), FT.FT.pow2(d)) == True{} : Bool},
    +hs: CMem.CM.Store(d, 0n, a, xs),
    htouch: CR.CR.Touch(0n, xs, tl),
    +he: {Nat.is_lt(nj, CR.CR.nlen(tl)) == True{} : Bool}) ->
  {Arr.Arr.snd(Array<U32>, U32, Array.get(U32, a, U32.add(256, cj)))
   == U32.from_nat(CR.CR.nnth(tl, nj)) : U32}:
  +eidx1 : {U32.add(256, cj)
            == U32.add(256, U32.from_nat(nj)) : U32} =
    Equal.cong(U32, U32, z => U32.add(256, z), cj, U32.from_nat(nj), hcj)
  +eidx2 : {U32.add(256, U32.from_nat(nj))
            == U32.from_nat(Nat.add(256n, nj)) : U32} =
    FT.FT.u32_add_from_nat(256n, nj)
  +eidx : {U32.add(256, cj) == U32.from_nat(Nat.add(256n, nj)) : U32} =
    Equal.trans(U32, U32.add(256, cj), U32.add(256, U32.from_nat(nj)),
      U32.from_nat(Nat.add(256n, nj)), eidx1, eidx2)
  +hval : {Arr.Arr.snd(Array<U32>, U32,
             Array.get(U32, a, U32.from_nat(Nat.add(256n, nj))))
           == CS.CS.nth(xs, Nat.add(256n, nj)) : U32} =
    CMem.CM.store_read(d, a, xs, Nat.add(256n, nj), hd, hk, hs)
  +hidx : {Arr.Arr.snd(Array<U32>, U32, Array.get(U32, a, U32.add(256, cj)))
           == Arr.Arr.snd(Array<U32>, U32,
                Array.get(U32, a, U32.from_nat(Nat.add(256n, nj)))) : U32} =
    Equal.cong(U32, U32,
      z => Arr.Arr.snd(Array<U32>, U32, Array.get(U32, a, z)),
      U32.add(256, cj), U32.from_nat(Nat.add(256n, nj)), eidx)
  +e0 : {Nat.add(0n, nj) == nj : Nat} = {==}
  +e0a : {Nat.add(256n, Nat.add(0n, nj)) == Nat.add(256n, nj) : Nat} =
    Equal.cong(Nat, Nat, z => Nat.add(256n, z), Nat.add(0n, nj), nj, e0)
  +htv : {CS.CS.nth(xs, Nat.add(256n, Nat.add(0n, nj)))
          == U32.from_nat(CR.CR.nnth(tl, nj)) : U32} =
    CR.CR.touch_get(tl, 0n, nj, xs, htouch, he)
  Equal.trans(U32, Arr.Arr.snd(Array<U32>, U32, Array.get(U32, a, U32.add(256, cj))),
    Arr.Arr.snd(Array<U32>, U32, Array.get(U32, a, U32.from_nat(Nat.add(256n, nj)))),
    U32.from_nat(CR.CR.nnth(tl, nj)), hidx,
    Equal.trans(U32,
      Arr.Arr.snd(Array<U32>, U32, Array.get(U32, a, U32.from_nat(Nat.add(256n, nj)))),
      CS.CS.nth(xs, Nat.add(256n, nj)),
      U32.from_nat(CR.CR.nnth(tl, nj)), hval,
      Equal.trans(U32, CS.CS.nth(xs, Nat.add(256n, nj)),
        CS.CS.nth(xs, Nat.add(256n, Nat.add(0n, nj))),
        U32.from_nat(CR.CR.nnth(tl, nj)),
        Equal.cong(Nat, U32, z => CS.CS.nth(xs, z),
          Nat.add(256n, nj), Nat.add(256n, Nat.add(0n, nj)),
          Equal.sym(Nat, Nat.add(256n, Nat.add(0n, nj)), Nat.add(256n, nj), e0a)),
        htv)))

# ------------------------------------------------- the phase-3 ghost state ---
#
# After the two writes the array is fixed; only the ghost lists differ by
# branch.  On a first occurrence (`mem c nl = False`) the touched list gains the
# code (`snoc`), on a duplicate it keeps its old list (`touch_prefix` drops the
# cell that the free-slot write put past the end).  The counter invariant
# `len tl = len(dedup nl)` follows in each branch from the `Nat` list lemmas.

def CMm.phase3_new(+d: Nat, -a: Array<U32>, +xs: +List<U32>,
    +xs0: +List<U32>, +c: Nat, +code: U32, +t: U32, +nl: +List<Nat>,
    +tl: +List<Nat>,
    +hm: {CR.CR.mem(c, nl) == False{} : Bool},
    +ht: {CR.CR.nlen(tl) == CR.CR.nlen(CNL.CNL.dedup(nl)) : Nat},
    r: CMem.CM.Store(d, 0n,
         Array.set(U32, Array.set(U32, a, code, 1), U32.add(256, t), code),
         CS.CS.set(CS.CS.set(xs, c, 1), Nat.add(256n, CR.CR.nlen(tl)),
           U32.from_nat(c)))
       & (CR.CR.Count(0n, 256n,
            CS.CS.set(CS.CS.set(xs, c, 1), Nat.add(256n, CR.CR.nlen(tl)),
              U32.from_nat(c)), c <> nl)
          & (CR.CR.Touch(0n,
               CS.CS.set(CS.CS.set(xs, c, 1), Nat.add(256n, CR.CR.nlen(tl)),
                 U32.from_nat(c)), CR.CR.snoc(c, tl))
             & CR.CR.Agree(
                 CS.CS.set(CS.CS.set(xs, c, 1), Nat.add(256n, CR.CR.nlen(tl)),
                   U32.from_nat(c)), xs0)))) ->
  CMem.CM.Store(d, 0n,
    Array.set(U32, Array.set(U32, a, code, 1), U32.add(256, t), code),
    CS.CS.set(CS.CS.set(xs, c, 1), Nat.add(256n, CR.CR.nlen(tl)),
      U32.from_nat(c)))
  & (CR.CR.Count(0n, 256n,
       CS.CS.set(CS.CS.set(xs, c, 1), Nat.add(256n, CR.CR.nlen(tl)),
         U32.from_nat(c)), c <> nl)
     & (CR.CR.Touch(0n,
          CS.CS.set(CS.CS.set(xs, c, 1), Nat.add(256n, CR.CR.nlen(tl)),
            U32.from_nat(c)), CR.CR.snoc(c, tl))
        & ({CR.CR.nlen(CR.CR.snoc(c, tl))
            == CR.CR.nlen(CNL.CNL.dedup(c <> nl)) : Nat}
           & CR.CR.Agree(
               CS.CS.set(CS.CS.set(xs, c, 1), Nat.add(256n, CR.CR.nlen(tl)),
                 U32.from_nat(c)), xs0)))):
  (hs, (hc, (hto, ha))) = r
  (hs, (hc, (hto, (CNL.CNL.touch_counter(c, nl, tl, ht, hm), ha))))

def CMm.phase3_dup(+d: Nat, -a: Array<U32>, +xs: +List<U32>,
    +xs0: +List<U32>, +c: Nat, +code: U32, +t: U32, +nl: +List<Nat>,
    +tl: +List<Nat>,
    +hm: {CR.CR.mem(c, nl) == True{} : Bool},
    +ht: {CR.CR.nlen(tl) == CR.CR.nlen(CNL.CNL.dedup(nl)) : Nat},
    r: CMem.CM.Store(d, 0n,
         Array.set(U32, Array.set(U32, a, code, 1), U32.add(256, t), code),
         CS.CS.set(CS.CS.set(xs, c, 1), Nat.add(256n, CR.CR.nlen(tl)),
           U32.from_nat(c)))
       & (CR.CR.Count(0n, 256n,
            CS.CS.set(CS.CS.set(xs, c, 1), Nat.add(256n, CR.CR.nlen(tl)),
              U32.from_nat(c)), c <> nl)
          & (CR.CR.Touch(0n,
               CS.CS.set(CS.CS.set(xs, c, 1), Nat.add(256n, CR.CR.nlen(tl)),
                 U32.from_nat(c)), CR.CR.snoc(c, tl))
             & CR.CR.Agree(
                 CS.CS.set(CS.CS.set(xs, c, 1), Nat.add(256n, CR.CR.nlen(tl)),
                   U32.from_nat(c)), xs0)))) ->
  CMem.CM.Store(d, 0n,
    Array.set(U32, Array.set(U32, a, code, 1), U32.add(256, t), code),
    CS.CS.set(CS.CS.set(xs, c, 1), Nat.add(256n, CR.CR.nlen(tl)),
      U32.from_nat(c)))
  & (CR.CR.Count(0n, 256n,
       CS.CS.set(CS.CS.set(xs, c, 1), Nat.add(256n, CR.CR.nlen(tl)),
         U32.from_nat(c)), c <> nl)
     & (CR.CR.Touch(0n,
          CS.CS.set(CS.CS.set(xs, c, 1), Nat.add(256n, CR.CR.nlen(tl)),
            U32.from_nat(c)), tl)
        & ({CR.CR.nlen(tl) == CR.CR.nlen(CNL.CNL.dedup(c <> nl)) : Nat}
           & CR.CR.Agree(
               CS.CS.set(CS.CS.set(xs, c, 1), Nat.add(256n, CR.CR.nlen(tl)),
                 U32.from_nat(c)), xs0)))):
  (hs, (hc, (hto, ha))) = r
  +hd : {CR.CR.nlen(CNL.CNL.dedup(c <> nl))
         == CR.CR.nlen(CNL.CNL.dedup(nl)) : Nat} = CNL.CNL.dup_counter(c, nl, hm)
  +hct : {CR.CR.nlen(tl) == CR.CR.nlen(CNL.CNL.dedup(c <> nl)) : Nat} =
    Equal.trans(Nat, CR.CR.nlen(tl), CR.CR.nlen(CNL.CNL.dedup(nl)),
      CR.CR.nlen(CNL.CNL.dedup(c <> nl)), ht, Equal.sym(Nat,
        CR.CR.nlen(CNL.CNL.dedup(c <> nl)), CR.CR.nlen(CNL.CNL.dedup(nl)), hd))
  (hs, (hc, (CR.CR.touch_prefix(tl, 0n,
    CS.CS.set(CS.CS.set(xs, c, 1), Nat.add(256n, CR.CR.nlen(tl)),
      U32.from_nat(c)), c, hto), (hct, ha))))

# ------------------------------------------------------ the machine invariant -
#
# One predicate for the ghost state every phase of `dc_go` must preserve: the
# array is the `Store` model, the count cells are the ghost code list `nl` (all
# codes processed, duplicates kept), the touched cells are the first-occurrence
# list `tl`, `tl`'s length is the deduplicated length of `nl` (so the machine's
# `t` is the distinct count so far), every cell from 768 on is unchanged, and
# the candidate set is the index list `idxs`.  The phase-dependent parts (the
# result cell at phase 6, the branch-selected touched list at phase 3) are not
# part of it: `CMm.phase3_new`/`phase3_dup` and `CMm.phase6` are the lemmas that
# extend it, which is why this predicate is phase-independent.
def CMm.Inv(+d: Nat, a: Array<U32>, +xs: +List<U32>, +xs0: +List<U32>,
    +nl: +List<Nat>, +tl: +List<Nat>, +o: Nat, +k: Nat, +idxs: +List<Nat>)
    -> Type:
  CMem.CM.Store(d, 0n, a, xs)
  & (CR.CR.Count(0n, 256n, xs, nl)
     & (CR.CR.Touch(0n, xs, tl)
        & ({CR.CR.nlen(tl) == CR.CR.nlen(CNL.CNL.dedup(nl)) : Nat}
           & (CR.CR.Agree(xs, xs0)
              & CR.CR.Set(o, k, 0n, xs, idxs)))))

# Projections, so a phase lemma can take the invariant and hand each part to the
# step lemma it needs without destructuring at the call site.
def CMm.inv_store(+d: Nat, a: Array<U32>, +xs: +List<U32>, +xs0: +List<U32>,
    +nl: +List<Nat>, +tl: +List<Nat>, +o: Nat, +k: Nat, +idxs: +List<Nat>,
    h: CMm.Inv(d, a, xs, xs0, nl, tl, o, k, idxs)) ->
  CMem.CM.Store(d, 0n, a, xs):
  (hs, _) = h
  hs

def CMm.inv_count(+d: Nat, a: Array<U32>, +xs: +List<U32>, +xs0: +List<U32>,
    +nl: +List<Nat>, +tl: +List<Nat>, +o: Nat, +k: Nat, +idxs: +List<Nat>,
    h: CMm.Inv(d, a, xs, xs0, nl, tl, o, k, idxs)) ->
  CR.CR.Count(0n, 256n, xs, nl):
  (_, r) = h
  (hc, _) = r
  hc

def CMm.inv_touch(+d: Nat, a: Array<U32>, +xs: +List<U32>, +xs0: +List<U32>,
    +nl: +List<Nat>, +tl: +List<Nat>, +o: Nat, +k: Nat, +idxs: +List<Nat>,
    h: CMm.Inv(d, a, xs, xs0, nl, tl, o, k, idxs)) ->
  CR.CR.Touch(0n, xs, tl):
  (_, r) = h
  (_, r2) = r
  (ht, _) = r2
  ht

def CMm.inv_len(+d: Nat, a: Array<U32>, +xs: +List<U32>, +xs0: +List<U32>,
    +nl: +List<Nat>, +tl: +List<Nat>, +o: Nat, +k: Nat, +idxs: +List<Nat>,
    h: CMm.Inv(d, a, xs, xs0, nl, tl, o, k, idxs)) ->
  {CR.CR.nlen(tl) == CR.CR.nlen(CNL.CNL.dedup(nl)) : Nat}:
  (_, r) = h
  (_, r2) = r
  (_, r3) = r2
  (hl, _) = r3
  hl

def CMm.inv_agree(+d: Nat, a: Array<U32>, +xs: +List<U32>, +xs0: +List<U32>,
    +nl: +List<Nat>, +tl: +List<Nat>, +o: Nat, +k: Nat, +idxs: +List<Nat>,
    h: CMm.Inv(d, a, xs, xs0, nl, tl, o, k, idxs)) ->
  CR.CR.Agree(xs, xs0):
  (_, r) = h
  (_, r2) = r
  (_, r3) = r2
  (_, r4) = r3
  (ha, _) = r4
  ha

def CMm.inv_set(+d: Nat, a: Array<U32>, +xs: +List<U32>, +xs0: +List<U32>,
    +nl: +List<Nat>, +tl: +List<Nat>, +o: Nat, +k: Nat, +idxs: +List<Nat>,
    h: CMm.Inv(d, a, xs, xs0, nl, tl, o, k, idxs)) ->
  CR.CR.Set(o, k, 0n, xs, idxs):
  (_, r) = h
  (_, r2) = r
  (_, r3) = r2
  (_, r4) = r3
  (_, hset) = r4
  hset

# ------------------------------------------------- phase 3 over the invariant -
#
# The two branches of the candidate pass produce the same array and differ only
# in the ghost touched list, so each branch has its own def (a branch-selected
# list cannot be repacked once).  Both hand the candidate range on: the two
# scratch writes sit below it, so `CR.set_set_below` keeps it.
#
# `phase3_new` / `phase3_dup` already state the branch ghost state; what is left
# is `Set`, which `set_scratch` discharges for both write indices.  The result of
# `phase3_*` is taken as a *parameter* of a helper (`_go`), because a match
# cannot scrutinise a computed value.

def CMm.set_scratch(+o: Nat, +k: Nat, +w: Nat, +v: U32, +xs: +List<U32>,
    +idxs: +List<Nat>,
    hs: CR.CR.Set(o, k, 0n, xs, idxs),
    +hw: {Nat.is_lt(w, o) == True{} : Bool}) ->
  CR.CR.Set(o, k, 0n, CS.CS.set(xs, w, v), idxs):
  CR.CR.set_set_below(o, k, 0n, w, v, xs, idxs, hs,
    CR.CR.is_lt_rewrite_r(w, o, Nat.add(o, 0n),
      Equal.sym(Nat, Nat.add(o, 0n), o, NatProof.NatPrf.add_zero(o)), hw))

def CMm.phase3_new_pack(+d: Nat, -a: Array<U32>, +xs: +List<U32>,
    +xs0: +List<U32>, +c: Nat, +code: U32, +t: U32, +nl: +List<Nat>,
    +tl: +List<Nat>, +o: Nat, +k: Nat, +idxs: +List<Nat>,
    hset2: CR.CR.Set(o, k, 0n,
             CS.CS.set(CS.CS.set(xs, c, 1), Nat.add(256n, CR.CR.nlen(tl)),
               U32.from_nat(c)), idxs),
    r2: CMem.CM.Store(d, 0n,
          Array.set(U32, Array.set(U32, a, code, 1), U32.add(256, t), code),
          CS.CS.set(CS.CS.set(xs, c, 1), Nat.add(256n, CR.CR.nlen(tl)),
            U32.from_nat(c)))
        & (CR.CR.Count(0n, 256n,
             CS.CS.set(CS.CS.set(xs, c, 1), Nat.add(256n, CR.CR.nlen(tl)),
               U32.from_nat(c)), c <> nl)
           & (CR.CR.Touch(0n,
                CS.CS.set(CS.CS.set(xs, c, 1), Nat.add(256n, CR.CR.nlen(tl)),
                  U32.from_nat(c)), CR.CR.snoc(c, tl))
              & ({CR.CR.nlen(CR.CR.snoc(c, tl))
                  == CR.CR.nlen(CNL.CNL.dedup(c <> nl)) : Nat}
                 & CR.CR.Agree(
                     CS.CS.set(CS.CS.set(xs, c, 1),
                       Nat.add(256n, CR.CR.nlen(tl)), U32.from_nat(c)),
                     xs0))))) ->
  CMm.Inv(d, Array.set(U32, Array.set(U32, a, code, 1), U32.add(256, t), code),
    CS.CS.set(CS.CS.set(xs, c, 1), Nat.add(256n, CR.CR.nlen(tl)),
      U32.from_nat(c)),
    xs0, c <> nl, CR.CR.snoc(c, tl), o, k, idxs):
  (hs, (hc, (hto, (hl, ha)))) = r2
  (hs, (hc, (hto, (hl, (ha, hset2)))))

def CMm.phase3_new_inv(+d: Nat, -a: Array<U32>, +xs: +List<U32>,
    +xs0: +List<U32>, +c: Nat, +code: U32, +t: U32, +nl: +List<Nat>,
    +tl: +List<Nat>, +o: Nat, +k: Nat, +idxs: +List<Nat>,
    +hm: {CR.CR.mem(c, nl) == False{} : Bool},
    +ht: {CR.CR.nlen(tl) == CR.CR.nlen(CNL.CNL.dedup(nl)) : Nat},
    +hc256: {Nat.is_lt(c, 256n) == True{} : Bool},
    +htl: {Nat.is_lt(Nat.add(256n, CR.CR.nlen(tl)), 512n) == True{} : Bool},
    +ho: {Nat.is_le(768n, o) == True{} : Bool},
    hset: CR.CR.Set(o, k, 0n, xs, idxs),
    r: CMem.CM.Store(d, 0n,
         Array.set(U32, Array.set(U32, a, code, 1), U32.add(256, t), code),
         CS.CS.set(CS.CS.set(xs, c, 1), Nat.add(256n, CR.CR.nlen(tl)),
           U32.from_nat(c)))
       & (CR.CR.Count(0n, 256n,
            CS.CS.set(CS.CS.set(xs, c, 1), Nat.add(256n, CR.CR.nlen(tl)),
              U32.from_nat(c)), c <> nl)
          & (CR.CR.Touch(0n,
               CS.CS.set(CS.CS.set(xs, c, 1), Nat.add(256n, CR.CR.nlen(tl)),
                 U32.from_nat(c)), CR.CR.snoc(c, tl))
             & CR.CR.Agree(
                 CS.CS.set(CS.CS.set(xs, c, 1), Nat.add(256n, CR.CR.nlen(tl)),
                   U32.from_nat(c)), xs0)))) ->
  CMm.Inv(d, Array.set(U32, Array.set(U32, a, code, 1), U32.add(256, t), code),
    CS.CS.set(CS.CS.set(xs, c, 1), Nat.add(256n, CR.CR.nlen(tl)),
      U32.from_nat(c)),
    xs0, c <> nl, CR.CR.snoc(c, tl), o, k, idxs):
  +ho256 : {Nat.is_le(256n, o) == True{} : Bool} =
    NatProof.Nat.is_le_trans(256n, 768n, o, {==}, ho)
  +ho512 : {Nat.is_le(512n, o) == True{} : Bool} =
    NatProof.Nat.is_le_trans(512n, 768n, o, {==}, ho)
  +hco : {Nat.is_lt(c, o) == True{} : Bool} =
    NatProof.Nat.is_lt_le_trans(c, 256n, o, hc256, ho256)
  +hto : {Nat.is_lt(Nat.add(256n, CR.CR.nlen(tl)), o) == True{} : Bool} =
    NatProof.Nat.is_lt_le_trans(Nat.add(256n, CR.CR.nlen(tl)), 512n, o, htl,
      ho512)
  hset1 = CMm.set_scratch(o, k, c, 1, xs, idxs, hset, hco)
  hset2 = CMm.set_scratch(o, k, Nat.add(256n, CR.CR.nlen(tl)), U32.from_nat(c),
    CS.CS.set(xs, c, 1), idxs, hset1, hto)
  CMm.phase3_new_pack(d, a, xs, xs0, c, code, t, nl, tl, o, k, idxs, hset2,
    CMm.phase3_new(d, a, xs, xs0, c, code, t, nl, tl, hm, ht, r))

def CMm.phase3_dup_pack(+d: Nat, -a: Array<U32>, +xs: +List<U32>,
    +xs0: +List<U32>, +c: Nat, +code: U32, +t: U32, +nl: +List<Nat>,
    +tl: +List<Nat>, +o: Nat, +k: Nat, +idxs: +List<Nat>,
    hset2: CR.CR.Set(o, k, 0n,
             CS.CS.set(CS.CS.set(xs, c, 1), Nat.add(256n, CR.CR.nlen(tl)),
               U32.from_nat(c)), idxs),
    r2: CMem.CM.Store(d, 0n,
          Array.set(U32, Array.set(U32, a, code, 1), U32.add(256, t), code),
          CS.CS.set(CS.CS.set(xs, c, 1), Nat.add(256n, CR.CR.nlen(tl)),
            U32.from_nat(c)))
        & (CR.CR.Count(0n, 256n,
             CS.CS.set(CS.CS.set(xs, c, 1), Nat.add(256n, CR.CR.nlen(tl)),
               U32.from_nat(c)), c <> nl)
           & (CR.CR.Touch(0n,
                CS.CS.set(CS.CS.set(xs, c, 1), Nat.add(256n, CR.CR.nlen(tl)),
                  U32.from_nat(c)), tl)
              & ({CR.CR.nlen(tl) == CR.CR.nlen(CNL.CNL.dedup(c <> nl)) : Nat}
                 & CR.CR.Agree(
                     CS.CS.set(CS.CS.set(xs, c, 1),
                       Nat.add(256n, CR.CR.nlen(tl)), U32.from_nat(c)),
                     xs0))))) ->
  CMm.Inv(d, Array.set(U32, Array.set(U32, a, code, 1), U32.add(256, t), code),
    CS.CS.set(CS.CS.set(xs, c, 1), Nat.add(256n, CR.CR.nlen(tl)),
      U32.from_nat(c)),
    xs0, c <> nl, tl, o, k, idxs):
  (hs, (hc, (hto, (hl, ha)))) = r2
  (hs, (hc, (hto, (hl, (ha, hset2)))))

def CMm.phase3_dup_inv(+d: Nat, -a: Array<U32>, +xs: +List<U32>,
    +xs0: +List<U32>, +c: Nat, +code: U32, +t: U32, +nl: +List<Nat>,
    +tl: +List<Nat>, +o: Nat, +k: Nat, +idxs: +List<Nat>,
    +hm: {CR.CR.mem(c, nl) == True{} : Bool},
    +ht: {CR.CR.nlen(tl) == CR.CR.nlen(CNL.CNL.dedup(nl)) : Nat},
    +hc256: {Nat.is_lt(c, 256n) == True{} : Bool},
    +htl: {Nat.is_lt(Nat.add(256n, CR.CR.nlen(tl)), 512n) == True{} : Bool},
    +ho: {Nat.is_le(768n, o) == True{} : Bool},
    hset: CR.CR.Set(o, k, 0n, xs, idxs),
    r: CMem.CM.Store(d, 0n,
         Array.set(U32, Array.set(U32, a, code, 1), U32.add(256, t), code),
         CS.CS.set(CS.CS.set(xs, c, 1), Nat.add(256n, CR.CR.nlen(tl)),
           U32.from_nat(c)))
       & (CR.CR.Count(0n, 256n,
            CS.CS.set(CS.CS.set(xs, c, 1), Nat.add(256n, CR.CR.nlen(tl)),
              U32.from_nat(c)), c <> nl)
          & (CR.CR.Touch(0n,
               CS.CS.set(CS.CS.set(xs, c, 1), Nat.add(256n, CR.CR.nlen(tl)),
                 U32.from_nat(c)), CR.CR.snoc(c, tl))
             & CR.CR.Agree(
                 CS.CS.set(CS.CS.set(xs, c, 1), Nat.add(256n, CR.CR.nlen(tl)),
                   U32.from_nat(c)), xs0)))) ->
  CMm.Inv(d, Array.set(U32, Array.set(U32, a, code, 1), U32.add(256, t), code),
    CS.CS.set(CS.CS.set(xs, c, 1), Nat.add(256n, CR.CR.nlen(tl)),
      U32.from_nat(c)),
    xs0, c <> nl, tl, o, k, idxs):
  +ho256 : {Nat.is_le(256n, o) == True{} : Bool} =
    NatProof.Nat.is_le_trans(256n, 768n, o, {==}, ho)
  +ho512 : {Nat.is_le(512n, o) == True{} : Bool} =
    NatProof.Nat.is_le_trans(512n, 768n, o, {==}, ho)
  +hco : {Nat.is_lt(c, o) == True{} : Bool} =
    NatProof.Nat.is_lt_le_trans(c, 256n, o, hc256, ho256)
  +hto : {Nat.is_lt(Nat.add(256n, CR.CR.nlen(tl)), o) == True{} : Bool} =
    NatProof.Nat.is_lt_le_trans(Nat.add(256n, CR.CR.nlen(tl)), 512n, o, htl,
      ho512)
  hset1 = CMm.set_scratch(o, k, c, 1, xs, idxs, hset, hco)
  hset2 = CMm.set_scratch(o, k, Nat.add(256n, CR.CR.nlen(tl)), U32.from_nat(c),
    CS.CS.set(xs, c, 1), idxs, hset1, hto)
  CMm.phase3_dup_pack(d, a, xs, xs0, c, code, t, nl, tl, o, k, idxs, hset2,
    CMm.phase3_dup(d, a, xs, xs0, c, code, t, nl, tl, hm, ht, r))

# The touched list after phase 3, as a function of the machine's first-occurrence
# flag: a duplicate keeps the list, a new code appends it.  The bisimulation's
# result type must name one list, and after the match on the flag this selector
# reduces to the branch's list.
def CMm.tlnext(+b: Bool, +c: Nat, +tl: +List<Nat>) -> +List<Nat>:
  match b:
    case True{}:
      tl
    case False{}:
      CR.CR.snoc(c, tl)

def CMm.phase3_go(+d: Nat, -a: Array<U32>, +xs: +List<U32>,
    +xs0: +List<U32>, +c: Nat, +code: U32, +t: U32, +nl: +List<Nat>,
    +tl: +List<Nat>, +o: Nat, +k: Nat, +idxs: +List<Nat>, +b: Bool,
    +hb: {b == CR.CR.mem(c, nl) : Bool},
    +hc256: {Nat.is_lt(c, 256n) == True{} : Bool},
    +htl: {Nat.is_lt(Nat.add(256n, CR.CR.nlen(tl)), 512n) == True{} : Bool},
    +ho: {Nat.is_le(768n, o) == True{} : Bool},
    +ht: {CR.CR.nlen(tl) == CR.CR.nlen(CNL.CNL.dedup(nl)) : Nat},
    hset: CR.CR.Set(o, k, 0n, xs, idxs),
    r: CMem.CM.Store(d, 0n,
         Array.set(U32, Array.set(U32, a, code, 1), U32.add(256, t), code),
         CS.CS.set(CS.CS.set(xs, c, 1), Nat.add(256n, CR.CR.nlen(tl)),
           U32.from_nat(c)))
       & (CR.CR.Count(0n, 256n,
            CS.CS.set(CS.CS.set(xs, c, 1), Nat.add(256n, CR.CR.nlen(tl)),
              U32.from_nat(c)), c <> nl)
          & (CR.CR.Touch(0n,
               CS.CS.set(CS.CS.set(xs, c, 1), Nat.add(256n, CR.CR.nlen(tl)),
                 U32.from_nat(c)), CR.CR.snoc(c, tl))
             & CR.CR.Agree(
                 CS.CS.set(CS.CS.set(xs, c, 1), Nat.add(256n, CR.CR.nlen(tl)),
                   U32.from_nat(c)), xs0)))) ->
  CMm.Inv(d, Array.set(U32, Array.set(U32, a, code, 1), U32.add(256, t), code),
    CS.CS.set(CS.CS.set(xs, c, 1), Nat.add(256n, CR.CR.nlen(tl)),
      U32.from_nat(c)),
    xs0, c <> nl, CMm.tlnext(b, c, tl), o, k, idxs):
  match b:
    case True{}:
      CMm.phase3_dup_inv(d, a, xs, xs0, c, code, t, nl, tl, o, k, idxs,
        Equal.sym(Bool, True{}, CR.CR.mem(c, nl), hb), ht, hc256, htl, ho, hset,
        r)
    case False{}:
      CMm.phase3_new_inv(d, a, xs, xs0, c, code, t, nl, tl, o, k, idxs,
        Equal.sym(Bool, False{}, CR.CR.mem(c, nl), hb), ht, hc256, htl, ho,
        hset, r)

# Phase 3 of the count machine over the invariant, as the machine runs it: the
# mark step is already done (`r1`, the result of `CMm.mark_code`), this def adds
# the touched-list write on top of it, splits on the machine's own
# first-occurrence flag, and repacks into the invariant.  `a` is the pre-mark
# array; it appears in `r1`'s type and is consumed once by `mark_touch_go`.
def CMm.phase3(+d: Nat, a: Array<U32>, +xs: +List<U32>, +xs0: +List<U32>,
    +c: Nat, +code: U32, +t: U32, +nl: +List<Nat>, +tl: +List<Nat>,
    +o: Nat, +k: Nat, +idxs: +List<Nat>, +b: Bool,
    +hb: {b == CR.CR.mem(c, nl) : Bool},
    +hcode: {code == U32.from_nat(c) : U32},
    +htn: {t == U32.from_nat(CR.CR.nlen(tl)) : U32},
    +hc256: {Nat.is_lt(c, 256n) == True{} : Bool},
    +htl: {Nat.is_lt(Nat.add(256n, CR.CR.nlen(tl)), 512n) == True{} : Bool},
    +ho: {Nat.is_le(768n, o) == True{} : Bool},
    +ht: {CR.CR.nlen(tl) == CR.CR.nlen(CNL.CNL.dedup(nl)) : Nat},
    hset: CR.CR.Set(o, k, 0n, xs, idxs),
    +hd: {Nat.is_lt(d, 32n) == True{} : Bool},
    +hk2: {Nat.is_lt(Nat.add(256n, CR.CR.nlen(tl)), FT.FT.pow2(d))
           == True{} : Bool},
    +hlen: {Nat.is_le(Nat.add(0n, FT.FT.pow2(d)), CS.CS.len(xs)) == True{}
            : Bool},
    r1: CMem.CM.Store(d, 0n, Array.set(U32, a, code, 1), CS.CS.set(xs, c, 1))
        & (CR.CR.Count(0n, 256n, CS.CS.set(xs, c, 1), c <> nl)
           & (CR.CR.Touch(0n, CS.CS.set(xs, c, 1), tl)
              & CR.CR.Agree(CS.CS.set(xs, c, 1), xs0)))) ->
  CMm.Inv(d, Array.set(U32, Array.set(U32, a, code, 1), U32.add(256, t), code),
    CS.CS.set(CS.CS.set(xs, c, 1), Nat.add(256n, CR.CR.nlen(tl)),
      U32.from_nat(c)),
    xs0, c <> nl, CMm.tlnext(b, c, tl), o, k, idxs):
  CMm.phase3_go(d, a, xs, xs0, c, code, t, nl, tl, o, k, idxs, b, hb, hc256,
    htl, ho, ht, hset,
    CMm.mark_touch_go(d, a, xs, xs0, c, code, t, nl, tl, hcode, htn, hd, hk2,
      hlen, htl, r1))
