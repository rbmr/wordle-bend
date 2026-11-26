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
