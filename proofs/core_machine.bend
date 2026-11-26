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
