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
