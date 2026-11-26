# EXPERIMENT (separate tree, @unsafe): split the branching-factor scan (kmax)
# of one large bucket across four lanes.
#
# Rust's `compute_max_branching_factor_seq_with_target` scans all 14855 guesses
# for every split bucket. That scan is the hottest loop of the port and it sits
# inside ONE search node, so splitting only the root does not reach it. Here the
# scan is split into four contiguous guess ranges and the four lanes run as four
# parallel tasks over four `Array.fork` handles to the SAME block:
#   - the feedback table, the bucket set, the guess masks and the profile table
#     are only READ (the read-only sharing the fork provides);
#   - each lane writes its own count/touched/result cells (disjoint);
#   - `sh` selects how the running maximum is shared: 0 = each lane keeps its
#     own (the caller takes the max of the four), 1 = one shared cell updated
#     with Array.atomic.max on every improvement, so all lanes stop at
#     `mx >= eff` like the sequential scan.
#
# Soundness: every reported value is "the largest number of distinct responses
# of a guess over the bucket" (a valid value for Rust's k_max_seq), and taking
# the max over the lanes is exact. A lane that stops early does so because the
# maximum already reached `eff`, which is all the caller tests for; the shared
# cell only ever grows with real counts.
#
# Layout: the prof region is 5 x 1024 cells. 0..1023 holds the per-(c,gg)
# tables (shared, read-only here); lane l uses 1024*(l+1) for
# counts (0..255), touched list (256..511) and the result (512).
import Base
import ./geo.bend as G
import ./arith.bend as A
import ./prof.bend as P

def lqb(+c: U32, +gg: U32, +lane: U32) -> U32:
  U32.add(G.off_prof(c, gg), U32.mul(1024, U32.inc(lane)))

def mxcell(+c: U32, +gg: U32) -> U32:
  U32.add(G.off_qgen(c, gg), 728)

def atomax(+cell: U32, +v: U32, p: Array<U32> & U32) -> Array<U32>:
  (a, _) = p
  a

def keep1(r0: Array<U32>, r1: Array<U32>, r2: Array<U32>, r3: Array<U32>) -> Array<U32>:
  r0

# ------------------------------------------------------- distinct count -------
# prof.dcount with the lane's own scratch region (identical phases).
def dn2_go(+fuel: Nat, +ph: U32, +i: U32, +j: U32, +fb: U32, +o: U32, +k: U32,
           +t: U32, +r: U32, +pb: U32, p: Array<U32> & U32) -> Array<U32>:
  match fuel:
    case 0n:
      (a2, _) = p
      a2
    case 1n+f:
      match ph:
        case 0:
          (a2, _) = p
          dn2_go(f, 1, i, j, fb, o, k, t, r, pb, Array.get(U32, a2, U32.add(o, i)))
        case 1:
          (a2, +v) = p
          +fi = U32.add(fb, v)
          dn2_go(f, 2, i, U32.and(fi, 3), fb, o, k, t, r, pb,
                 Array.get(U32, a2, U32.shrn(fi, 2n)))
        case 2:
          # Byte extract with constant shifts only (see tab.pack_fb).
          (a2, +w) = p
          +hi = U32.sub(1, U32.shrn(U32.sub(j, 2), 31n))
          +t1 = U32.add(w, U32.mul(hi, U32.sub(U32.shrn(w, 16n), w)))
          +t2 = U32.add(t1, U32.mul(U32.and(j, 1),
                                    U32.sub(U32.shrn(t1, 8n), t1)))
          +resp = U32.and(t2, 255)
          dn2_go(f, 3, i, 0, fb, o, k, t, resp, pb,
                 Array.get(U32, a2, U32.add(pb, resp)))
        case 3:
          (a2, +v) = p
          +new = U32.shrn(U32.sub(v, 1), 31n)
          a3 = Array.set(U32, a2, U32.add(pb, r), U32.inc(v))
          a4 = Array.set(U32, a3, U32.add(U32.add(pb, 256), t), r)
          +i2 = U32.inc(i)
          +t2 = U32.add(t, new)
          +done = U32.sub(1, U32.shrn(U32.sub(i2, k), 31n))
          +sb = U32.add(o, i2)
          +cb = pb
          +idx = U32.add(sb, U32.mul(done, U32.sub(cb, sb)))
          dn2_go(f, U32.mul(done, 4), i2, 0, fb, o, k, t2, r, pb,
                 Array.get(U32, a4, idx))
        case 4:
          (a2, _) = p
          +done = U32.sub(1, U32.shrn(U32.sub(j, t), 31n))
          +tb = U32.add(U32.add(pb, 256), j)
          +idx = U32.add(tb, U32.mul(done, U32.sub(pb, tb)))
          dn2_go(f, U32.add(5, done), i, j, fb, o, k, t, r, pb,
                 Array.get(U32, a2, idx))
        case 5:
          (a2, +v) = p
          a3 = Array.set(U32, a2, U32.add(pb, v), 0)
          +j2 = U32.inc(j)
          +done = U32.sub(1, U32.shrn(U32.sub(j2, t), 31n))
          +tb = U32.add(U32.add(pb, 256), j2)
          +idx = U32.add(tb, U32.mul(done, U32.sub(pb, tb)))
          dn2_go(f, U32.add(4, U32.mul(done, 2)), i, j2, fb, o, k, t, r, pb,
                 Array.get(U32, a3, idx))
        case 6:
          (a2, _) = p
          a3 = Array.set(U32, a2, U32.add(pb, 512), t)
          dn2_go(f, 7, i, j, fb, o, k, t, r, pb, Array.get(U32, a3, 0))
        case _:
          (a2, _) = p
          a2

def dcount2(a: Array<U32>, +g: U32, +o: U32, +k: U32, +c: U32, +gg: U32,
            +lane: U32) -> Array<U32>:
  +fb = U32.mul(g, c)
  +pb = lqb(c, gg, lane)
  +fuel = Nat.add(Nat.mul(U32.to_nat(k), 8n), 80n)
  dn2_go(fuel, 0, 0, 0, fb, o, k, 0, 0, pb, Array.get(U32, a, o))

# ------------------------------------------------ one lane of k_max_seq ------
# prof.km_go with a guess range [g, hi), the shared `mx` cell read at every
# head, and the atomic update only when `sh` is set and a count improves it.
#
# ph 0 read the shared max; 91 head; 1 filter 1; 20..24 factors; 8 filter 2;
# 5 advance skipped; 2/3 count; 30 atomic update; 31 advance; 11 done.
def km2_go(+fuel: Nat, +ph: U32, +g: U32, +hi: U32, +o: U32, +k: U32,
           +mx: U32, +eff: U32, +dep: U32, +c: U32, +gg: U32, +act: U32,
           +pk: U32, +pr: U32, +lane: U32, +sh: U32,
           p: Array<U32> & U32) -> Array<U32>:
  match fuel:
    case 0n:
      (a2, _) = p
      a2
    case 1n+f:
      match ph:
        case 0:
          (a2, _) = p
          km2_go(f, 91, g, hi, o, k, mx, eff, dep, c, gg, act, pk, pr, lane, sh,
                 Array.get(U32, a2, mxcell(c, gg)))
        case 91:
          (a2, +mv) = p
          +mx2 = U32.max(mx, mv)
          +over = A.ge01(g, hi)
          +stop = U32.max(over, A.ge01(mx2, eff))
          +idx = A.sel(stop, 0, U32.add(G.off_gmask(c, gg), g))
          km2_go(f, A.sel(stop, 11, 1), g, hi, o, k, mx2, eff, dep, c, gg, act,
                 pk, pr, lane, sh, Array.get(U32, a2, idx))
        case 1:
          (a2, +gm) = p
          +non = U32.xor(act, 4294967295)
          +mo = P.mnover(mx)
          +skip1 = A.ge01(P.pc32(U32.and(gm, non)), mo)
          +idx = A.sel(skip1, 0, U32.add(G.off_gpack(c, gg), g))
          km2_go(f, A.sel(skip1, 5, 20), g, hi, o, k, mx, eff, dep, c, gg, act,
                 pk, pr, lane, sh, Array.get(U32, a2, idx))
        case 20:
          (a2, +v) = p
          km2_go(f, 21, g, hi, o, k, mx, eff, dep, c, gg, act, v, v, lane, sh,
                 Array.get(U32, a2, P.mcell(c, gg, 0, U32.and(v, 31))))
        case 21:
          (a2, +v) = p
          +l = U32.and(U32.shrn(pk, 5n), 31)
          km2_go(f, 22, g, hi, o, k, mx, eff, dep, c, gg, act, pk, U32.mul(pr, v),
                 lane, sh, Array.get(U32, a2, P.mcell(c, gg, 1, l)))
        case 22:
          (a2, +v) = p
          +l = U32.and(U32.shrn(pk, 10n), 31)
          km2_go(f, 23, g, hi, o, k, mx, eff, dep, c, gg, act, pk, U32.mul(pr, v),
                 lane, sh, Array.get(U32, a2, P.mcell(c, gg, 2, l)))
        case 23:
          (a2, +v) = p
          +l = U32.and(U32.shrn(pk, 15n), 31)
          km2_go(f, 24, g, hi, o, k, mx, eff, dep, c, gg, act, pk, U32.mul(pr, v),
                 lane, sh, Array.get(U32, a2, P.mcell(c, gg, 3, l)))
        case 24:
          (a2, +v) = p
          +l = U32.and(U32.shrn(pk, 20n), 31)
          km2_go(f, 8, g, hi, o, k, mx, eff, dep, c, gg, act, pk, U32.mul(pr, v),
                 lane, sh, Array.get(U32, a2, P.mcell(c, gg, 4, l)))
        case 8:
          (a2, _) = p
          +skip2 = A.ge01(mx, pr)
          km2_go(f, A.sel(skip2, 5, 2), g, hi, o, k, mx, eff, dep, c, gg, act,
                 pk, pr, lane, sh, Array.get(U32, a2, 0))
        case 5:
          (a2, _) = p
          +g2 = U32.inc(g)
          +idx = A.sel(A.ge01(g2, hi), 0, U32.add(G.off_gmask(c, gg), g2))
          km2_go(f, 0, g2, hi, o, k, mx, eff, dep, c, gg, act, pk, pr, lane, sh,
                 Array.get(U32, a2, idx))
        case 2:
          (a2, _) = p
          a3 = dcount2(a2, g, o, k, c, gg, lane)
          km2_go(f, 3, g, hi, o, k, mx, eff, dep, c, gg, act, pk, pr, lane, sh,
                 Array.get(U32, a3, U32.add(lqb(c, gg, lane), 512)))
        case 3:
          (a2, +t) = p
          +mx2 = U32.max(mx, t)
          +big = U32.mul(sh, A.ge01(t, U32.inc(mx)))
          km2_go(f, A.sel(big, 30, 31), g, hi, o, k, mx2, eff, dep, c, gg, act,
                 pk, pr, lane, sh, Array.get(U32, a2, 0))
        case 30:
          (a2, _) = p
          a3 = atomax(mxcell(c, gg), mx, Array.atomic.max(a2, mxcell(c, gg), mx))
          km2_go(f, 31, g, hi, o, k, mx, eff, dep, c, gg, act, pk, pr, lane, sh,
                 Array.get(U32, a3, 0))
        case 31:
          (a2, _) = p
          +g2 = U32.inc(g)
          +idx = A.sel(A.ge01(g2, hi), 0, U32.add(G.off_gmask(c, gg), g2))
          km2_go(f, 0, g2, hi, o, k, mx, eff, dep, c, gg, act, pk, pr, lane, sh,
                 Array.get(U32, a2, idx))
        case 11:
          (a2, _) = p
          a3 = Array.set(U32, a2, U32.add(lqb(c, gg, lane), 512), mx)
          km2_go(f, 12, g, hi, o, k, mx, eff, dep, c, gg, act, pk, pr, lane, sh,
                 Array.get(U32, a3, 0))
        case 12:
          (a2, _) = p
          a2
        case _:
          (a2, _) = p
          a2

# ------------------------------------------------ merge the lane maxima ------
# ph 0 read lane i's result; 1 fold and advance; 2 write uused; 3 done.
def mrg(+fuel: Nat, +ph: U32, +i: U32, +acc: U32, +c: U32, +gg: U32,
        p: Array<U32> & U32) -> Array<U32>:
  match fuel:
    case 0n:
      (a2, _) = p
      a2
    case 1n+f:
      match ph:
        case 0:
          (a2, _) = p
          mrg(f, 1, i, acc, c, gg,
              Array.get(U32, a2, U32.add(lqb(c, gg, i), 512)))
        case 1:
          (a2, +v) = p
          +acc2 = U32.max(acc, v)
          +i2 = U32.inc(i)
          +done = A.ge01(i2, 4)
          mrg(f, A.sel(done, 2, 0), i2, acc2, c, gg, Array.get(U32, a2, 0))
        case 2:
          (a2, _) = p
          a3 = Array.set(U32, a2, mxcell(c, gg), acc)
          mrg(f, 3, i, acc, c, gg, Array.get(U32, a3, 0))
        case _:
          (a2, _) = p
          a2

def mrgall(a: Array<U32>, +init: U32, +c: U32, +gg: U32) -> Array<U32>:
  mrg(32n, 0, 0, init, c, gg, Array.get(U32, a, 0))

# ------------------------------------------------------------ four lanes -----
def kp4(q: Array<U32> & Array<U32>, h0: Array<U32>, h1: Array<U32>, +o: U32,
        +k: U32, +init: U32, +eff: U32, +dep: U32, +c: U32, +gg: U32,
        +act: U32, +sh: U32, +fuel: Nat, +qtr: U32) -> Array<U32>:
  (h2, h3) = q
  r0 r1 r2 r3 = km2_go(fuel, 0, 0, qtr, o, k, init, eff, dep, c, gg, act, 0, 1, 0, sh, Array.get(U32, h0, 0)) km2_go(fuel, 0, qtr, U32.mul(2, qtr), o, k, init, eff, dep, c, gg, act, 0, 1, 1, sh, Array.get(U32, h1, 0)) km2_go(fuel, 0, U32.mul(2, qtr), U32.mul(3, qtr), o, k, init, eff, dep, c, gg, act, 0, 1, 2, sh, Array.get(U32, h2, 0)) km2_go(fuel, 0, U32.mul(3, qtr), gg, o, k, init, eff, dep, c, gg, act, 0, 1, 3, sh, Array.get(U32, h3, 0))
  mrgall(keep1(r0, r1, r2, r3), init, c, gg)

def kp3(q: Array<U32> & Array<U32>, h0: Array<U32>, +o: U32, +k: U32,
        +init: U32, +eff: U32, +dep: U32, +c: U32, +gg: U32, +act: U32,
        +sh: U32, +fuel: Nat, +qtr: U32) -> Array<U32>:
  (h1, r) = q
  kp4(Array.fork(U32, r), h0, h1, o, k, init, eff, dep, c, gg, act, sh, fuel, qtr)

def kp2(q: Array<U32> & Array<U32>, +o: U32, +k: U32, +init: U32, +eff: U32,
        +dep: U32, +c: U32, +gg: U32, +act: U32, +sh: U32, +fuel: Nat,
        +qtr: U32) -> Array<U32>:
  (h0, r) = q
  kp3(Array.fork(U32, r), h0, o, k, init, eff, dep, c, gg, act, sh, fuel, qtr)

def kp_act(+o: U32, +k: U32, +init: U32, +eff: U32, +dep: U32, +c: U32,
           +gg: U32, +sh: U32, +fuel: Nat, +qtr: U32,
           p: Array<U32> & U32) -> Array<U32>:
  (a, +act) = p
  kp2(Array.fork(U32, a), o, k, init, eff, dep, c, gg, act, sh, fuel, qtr)

def kmax_par(a: Array<U32>, +o: U32, +k: U32, +init: U32, +eff: U32,
             +dep: U32, +c: U32, +gg: U32, +sh: U32) -> Array<U32>:
  +per = Nat.add(Nat.mul(U32.to_nat(k), 8n), 96n)
  +fuel = Nat.add(Nat.mul(U32.to_nat(gg), per), 1024n)
  +qtr = U32.div(gg, 4)
  a1 = Array.set(U32, a, mxcell(c, gg), init)
  kp_act(o, k, init, eff, dep, c, gg, sh, fuel, qtr,
         Array.get(U32, a1, P.actcell(c, gg)))

# Flag cell: 1 = four lanes with local maxima, 2 = four lanes with the atomic
# shared maximum. Read by big.bg before the call.
def fcell(+c: U32, +gg: U32) -> U32:
  U32.add(G.off_qgen(c, gg), 756)
