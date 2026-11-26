# The new search core: one self-recursive machine, flat structures only.
#
# Rust's core is mutually recursive (min_state_val_with_hash <->
# min_guess_val_inner) and safe Bend forbids mutual recursion, so one def runs
# both; `ph` selects which (0..99 state, 100..119 guess, 199.. the return path).
# The call stack is a flat frame array (16 cells per depth, G.off_fr),
# candidate sets are index ranges in a flat stack array, the count and sort
# buffers are flat per-depth regions, and the transposition table is a region of
# the same array.
#
# The step order is the one in proto3/test/ref.py, written from solver.rs and
# validated against the Rust binary: base cases, quick eval for n <= 15, parent
# capacity bound, phase 1 (candidate guesses), tuple sort and beta walk, phase 2
# (other guesses), the tight bound update, the phase 2 walk, and the
# exact/lower-bound return. The guess pass is min_guess_val_inner's generic
# body: count, `3n - total - win`, the capacity bound per bucket, the small-set
# eval, and the b = cost - used accounting per recursive bucket.
#
# This slice has no transposition table and no bucket order: values are exact,
# some pruning is missing, and buckets are visited in response order.
import Base
import ./geo.bend as G
import ./arith.bend as A
import ./heur.bend as H
import ./sec.bend as S
import ./bounds.bend as B
import ./p12.bend as P

def maxu() -> U32:
  4294967295

def qo(+c: U32, +gg: U32) -> U32:
  U32.add(G.off_qgen(c, gg), 760)

# p12 result cells: 700 best, 701 lmk, 702 v1k/v2k, 703 mv, 704 nt,
# 705 ngs delta, 706 npr delta.
def rc(+i: U32, +c: U32, +gg: U32) -> U32:
  U32.add(U32.add(G.off_qgen(c, gg), 700), i)

def p1tb(+dep: U32, +c: U32, +gg: U32) -> U32:
  U32.add(G.off_p1t(c, gg), U32.mul(dep, U32.mul(c, 3)))

def p2tb(+dep: U32, +c: U32, +gg: U32) -> U32:
  U32.add(G.off_p2t(c, gg), U32.mul(dep, U32.mul(gg, 3)))

def bkb(+dep: U32, +c: U32, +gg: U32) -> U32:
  U32.add(G.off_bkt(c, gg), U32.mul(dep, c))

def fsl(+dep: U32, +c: U32, +gg: U32) -> U32:
  U32.add(G.off_fr(c, gg), U32.mul(dep, G.fr_slot()))

def met(+i: U32, +c: U32, +gg: U32) -> U32:
  U32.add(G.off_meta(c, gg), i)

def gen0(+gg: U32) -> U32:
  U32.mul(gg, 1024)

# Where a finished value goes: 250 ends the whole search at the root, 199 pops
# the parent frame otherwise.
def fin(+dep: U32) -> U32:
  A.sel(A.eq01(dep, 0), 250, 199)

# ------------------------------------------------------------- frame writes ---
#
# State frame (parent of a guess): 0 retph, 1 ss, 2 n, 3 beta, 4 pmk, 5 best,
# 6 lb, 7 lmk, 8 v1k, 9 v2k, 10 mv, 11 ti, 12 tn, 15 loader phase.
def ssave(a: Array<U32>, +fs: U32, +retph: U32, +ss: U32, +n: U32,
          +beta: U32, +pmk: U32, +best: U32, +lb: U32, +lmk: U32, +v1k: U32,
          +v2k: U32, +mv: U32, +ti: U32, +tn: U32) -> Array<U32>:
  a0 = a[U32.add(fs, 0)] <- retph
  a1 = a0[U32.add(fs, 1)] <- ss
  a2 = a1[U32.add(fs, 2)] <- n
  a3 = a2[U32.add(fs, 3)] <- beta
  a4 = a3[U32.add(fs, 4)] <- pmk
  a5 = a4[U32.add(fs, 5)] <- best
  a6 = a5[U32.add(fs, 6)] <- lb
  a7 = a6[U32.add(fs, 7)] <- lmk
  a8 = a7[U32.add(fs, 8)] <- v1k
  a9 = a8[U32.add(fs, 9)] <- v2k
  a10 = a9[U32.add(fs, 10)] <- mv
  a11 = a10[U32.add(fs, 11)] <- ti
  a12 = a11[U32.add(fs, 12)] <- tn
  a12[U32.add(fs, 15)] <- 200

# Guess frame (parent of a state): 0 retph, 1 beta, 2 cost, 3 used, 4 ti,
# 15 loader phase.
def gsave(a: Array<U32>, +fs: U32, +retph: U32, +beta: U32, +cost: U32,
          +used: U32, +ti: U32, +tn: U32) -> Array<U32>:
  a0 = a[U32.add(fs, 0)] <- retph
  a1 = a0[U32.add(fs, 1)] <- beta
  a2 = a1[U32.add(fs, 2)] <- cost
  a3 = a2[U32.add(fs, 3)] <- used
  a4 = a3[U32.add(fs, 4)] <- ti
  a5 = a4[U32.add(fs, 5)] <- tn
  a5[U32.add(fs, 15)] <- 220

# --------------------------------------------------------------- the machine ---
#
# Registers: ss n = the set; beta = the cutoff; pmk = the parent's max k;
# dep = depth; best lb lmk v1k v2k mv = the state's search values; ti tn =
# tuple cursor/count (state) or bucket cursor/total (guess); g = guess index;
# cost used = the guess's accumulated cost and current bucket value; ret = the
# value being returned; nst ngs npr = counters.
def step(+fuel: Nat, +c: U32, +gg: U32, +ph: U32, +ss: U32, +n: U32,
         +beta: U32, +pmk: U32, +dep: U32, +best: U32, +lb: U32, +lmk: U32,
         +v1k: U32, +v2k: U32, +mv: U32, +ti: U32, +tn: U32, +g: U32,
         +cost: U32, +used: U32, +ret: U32, +nst: U32, +ngs: U32, +npr: U32,
         p: Array<U32> & U32) -> Array<U32>:
  match fuel:
    case 0n:
      (a2, _) = p
      a3 = Array.set(U32, a2, met(0, c, gg), ret)
      a4 = Array.set(U32, a3, met(1, c, gg), nst)
      Array.set(U32, a4, met(2, c, gg), ngs)
    case 1n+f:
      match ph:
        # ============================================================ state ====
        case 0:
          (a2, _) = p
          +small = U32.sub(1, A.ge01(n, 3))
          +bv = A.sel(A.ge01(n, 2), 3, n)
          step(f, c, gg, A.sel(small, fin(dep), 1), ss, n, beta, pmk, dep, best, lb,
               lmk, v1k, v2k, mv, ti, tn, g, cost, used, bv, nst, ngs, npr,
               Array.get(U32, a2, 0))
        case 1:
          (a2, _) = p
          # nst += 1; quick eval only for n <= 15.
          +big = A.ge01(n, 16)
          step(f, c, gg, A.sel(big, 4, 2), ss, n, beta, pmk, dep, best, lb, lmk,
               v1k, v2k, mv, ti, tn, g, cost, used, ret, U32.inc(nst), ngs, npr,
               Array.get(U32, a2, 0))
        case 2:
          (a2, _) = p
          +qf = Nat.add(Nat.mul(U32.to_nat(n), 64n), 64n)
          a3 = H.quick(qf, 6, 0, 0, 0, 0, 0, 0, 0, 0, ss, n, c, gg, qo(c, gg),
                        Array.get(U32, a2, ss))
          step(f, c, gg, 3, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k,
               mv, ti, tn, g, cost, used, ret, nst, ngs, npr,
               Array.get(U32, a3, qo(c, gg)))
        case 3:
          (a2, +pk) = p
          +ex = U32.and(pk, 1)
          +qv = U32.shrn(pk, 1n)
          +u = A.sel(A.eq01(ex, 1), fin(dep), 4)
          step(f, c, gg, u, ss, n, beta, pmk, dep, best, U32.max(lb, qv), lmk,
               v1k, v2k, mv, ti, tn, g, cost, used, qv, nst, ngs, npr, Array.get(U32, a2, 0))
        case 4:
          (a2, _) = p
          step(f, c, gg, 5, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               ti, tn, g, cost, used, ret, nst, ngs, npr,
               Array.get(U32, a2, S.cap_at(pmk, n, c, gg)))
        case 5:
          (a2, +clb) = p
          +lb2 = U32.max(lb, clb)
          +cut = A.ge01(lb2, beta)
          step(f, c, gg, A.sel(cut, fin(dep), 6), ss, n, beta, pmk, dep,
               A.sel(cut, best, beta), lb2, lmk, v1k, v2k, mv, ti, tn, g, cost,
               used, A.sel(cut, lb2, ret), nst, ngs, npr,
               Array.get(U32, a2, 0))
        case 6:
          (a2, _) = p
          a3 = P.p1_scan(a2, ss, n, beta, pmk, dep, gen0(gg), c, gg)
          step(f, c, gg, 7, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               ti, tn, g, cost, used, ret, nst, ngs, npr,
               Array.get(U32, a3, rc(0, c, gg)))
        case 7:
          (a2, +v) = p
          step(f, c, gg, 8, ss, n, beta, pmk, dep, U32.max(best, v), lb, lmk,
               v1k, v2k, mv, ti, tn, g, cost, used, ret, nst, ngs, npr,
               Array.get(U32, a2, rc(1, c, gg)))
        case 8:
          (a2, +v) = p
          step(f, c, gg, 9, ss, n, beta, pmk, dep, best, lb, v, v1k, v2k, mv,
               ti, tn, g, cost, used, ret, nst, ngs, npr,
               Array.get(U32, a2, rc(2, c, gg)))
        case 9:
          (a2, +v) = p
          step(f, c, gg, 10, ss, n, beta, pmk, dep, best, lb, lmk, v, v2k, mv,
               ti, tn, g, cost, used, ret, nst, ngs, npr,
               Array.get(U32, a2, rc(3, c, gg)))
        case 10:
          (a2, +v) = p
          step(f, c, gg, 11, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, v,
               ti, tn, g, cost, used, ret, nst, ngs, npr,
               Array.get(U32, a2, rc(4, c, gg)))
        case 11:
          (a2, +v) = p
          step(f, c, gg, 12, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               ti, v, g, cost, used, ret, nst, ngs, npr,
               Array.get(U32, a2, rc(5, c, gg)))
        case 12:
          (a2, +v) = p
          +npr2 = U32.add(npr, v)
          +walk = U32.mul(A.ge01(best, U32.inc(lb)), A.ge01(tn, 0))
          step(f, c, gg, A.sel(walk, 13, 30), ss, n, beta, pmk, dep, best, lb,
               lmk, v1k, v2k, mv, 0, tn, g, cost, used, ret, nst, ngs, npr2,
               Array.get(U32, a2, 0))
        case 13:
          (a2, _) = p
          a3 = P.sort3(a2, p1tb(dep, c, gg), tn)
          step(f, c, gg, 14, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               ti, tn, g, cost, used, ret, nst, ngs, npr,
               Array.get(U32, a3, 0))
        case 14:
          (a2, _) = p
          +more = A.ge01(tn, U32.inc(ti))
          step(f, c, gg, A.sel(more, 15, 30), ss, n, beta, pmk, dep, best, lb,
               lmk, v1k, v2k, mv, ti, tn, g, cost, used, ret, nst, ngs, npr,
               Array.get(U32, a2, U32.add(U32.add(p1tb(dep, c, gg),
                                                  U32.mul(ti, 3)), 2)))
        case 15:
          (a2, +tg) = p
          step(f, c, gg, 16, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               ti, tn, tg, cost, used, ret, nst, ngs, npr,
               Array.get(U32, a2, U32.add(p1tb(dep, c, gg), U32.mul(ti, 3))))
        case 16:
          (a2, +tlb) = p
          +skip = A.ge01(tlb, best)
          +mv2 = A.sel(skip, U32.min(mv, tlb), mv)
          +npr2 = U32.add(npr, U32.mul(skip, U32.sub(tn, ti)))
          step(f, c, gg, A.sel(skip, 30, 17), ss, n, A.sel(skip, beta, best),
               pmk, dep, best, lb, lmk, v1k, v2k, mv2, ti, tn, g, cost, used,
               ret, nst, ngs, npr2, Array.get(U32, a2, 0))
        case 17:
          (a2, _) = p
          a3 = ssave(a2, fsl(dep, c, gg), 18, ss, n, beta, pmk, best, lb, lmk,
                      v1k, v2k, mv, ti, tn)
          step(f, c, gg, 100, ss, n, best, pmk, U32.add(dep, 1), best, 0, 0, 0,
               0, maxu(), ti, tn, g, 0, 0, ret, nst, ngs, npr,
               Array.get(U32, a3, g))
        case 18:
          (a2, _) = p
          +val = ret
          +bt = A.sel(A.ge01(val, best), best, val)
          +cont = U32.mul(A.ge01(bt, U32.inc(lb)), A.ge01(tn, U32.inc(ti)))
          step(f, c, gg, A.sel(cont, 14, 30), ss, n, beta, pmk, dep, bt, lb,
               lmk, v1k, v2k, U32.min(mv, val), U32.inc(ti), tn, g, cost, used,
               ret, nst, ngs, npr, Array.get(U32, a2, 0))
        case 30:
          (a2, _) = p
          +p2m = U32.from_nat(B.phase2_capacity_bound(U32.to_nat(n),
                                                      U32.to_nat(pmk),
                                                      U32.to_nat(pmk)))
          +eff = U32.max(lb, p2m)
          +run = A.ge01(best, U32.inc(eff))
          step(f, c, gg, A.sel(run, 31, 60), ss, n, beta, pmk, dep, best, lb,
               lmk, v1k, v2k, A.sel(run, mv, U32.min(mv, p2m)), ti, tn, g, cost,
               used, ret, nst, ngs, npr, Array.get(U32, a2, 0))
        case 31:
          (a2, _) = p
          a3 = P.p2_scan(a2, ss, n, best, pmk, dep, gen0(gg), lmk, c, gg)
          step(f, c, gg, 32, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               ti, tn, g, cost, used, ret, nst, ngs, npr,
               Array.get(U32, a3, rc(0, c, gg)))
        case 32:
          (a2, +v) = p
          step(f, c, gg, 33, ss, n, beta, pmk, dep, U32.max(best, v), lb, lmk,
               v1k, v2k, mv, ti, tn, g, cost, used, ret, nst, ngs, npr,
               Array.get(U32, a2, rc(1, c, gg)))
        case 33:
          (a2, +v) = p
          step(f, c, gg, 34, ss, n, beta, pmk, dep, best, lb, U32.max(lmk, v),
               v1k, v2k, mv, ti, tn, g, cost, used, ret, nst, ngs, npr,
               Array.get(U32, a2, rc(2, c, gg)))
        case 34:
          (a2, +v) = p
          step(f, c, gg, 35, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v, mv,
               ti, tn, g, cost, used, ret, nst, ngs, npr,
               Array.get(U32, a2, rc(3, c, gg)))
        case 35:
          (a2, +v) = p
          step(f, c, gg, 36, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k,
               U32.min(mv, v), ti, tn, g, cost, used, ret, nst, ngs, npr,
               Array.get(U32, a2, rc(4, c, gg)))
        case 36:
          (a2, +v) = p
          step(f, c, gg, 37, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               ti, v, g, cost, used, ret, nst, ngs, npr,
               Array.get(U32, a2, rc(5, c, gg)))
        case 37:
          (a2, +v) = p
          step(f, c, gg, 38, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               ti, tn, g, cost, used, ret, nst, U32.add(ngs, v), npr,
               Array.get(U32, a2, rc(6, c, gg)))
        case 38:
          (a2, +v) = p
          +npr2 = U32.add(npr, v)
          step(f, c, gg, 39, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               ti, tn, g, cost, used, ret, nst, ngs, npr2,
               Array.get(U32, a2, S.cap_at(lmk, n, c, gg)))
        case 39:
          (a2, +cb) = p
          +lb2 = U32.max(lb, cb)
          +tl1 = A.sel(A.ge01(v1k, 1),
                       U32.from_nat(B.tight_capacity_bound(U32.to_nat(n),
                                                           U32.to_nat(v1k),
                                                           U32.to_nat(lmk))),
                       maxu())
          +tl2 = A.sel(A.ge01(v2k, 1),
                       U32.from_nat(B.phase2_capacity_bound(U32.to_nat(n),
                                                            U32.to_nat(v2k),
                                                            U32.to_nat(lmk))),
                       maxu())
          +tl = U32.min(tl1, tl2)
          +usetl = U32.mul(U32.sub(1, A.eq01(tl, maxu())),
                           A.ge01(tl, U32.inc(lb2)))
          +lb3 = A.sel(usetl, tl, lb2)
          +walk = U32.mul(A.ge01(best, U32.inc(lb3)), A.ge01(tn, 0))
          step(f, c, gg, A.sel(walk, 40, 60), ss, n, beta, pmk, dep, best, lb3,
               lmk, v1k, v2k, mv, 0, tn, g, cost, used, ret, nst, ngs, npr,
               Array.get(U32, a2, 0))
        case 40:
          (a2, _) = p
          a3 = P.sort3(a2, p2tb(dep, c, gg), tn)
          step(f, c, gg, 41, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               ti, tn, g, cost, used, ret, nst, ngs, npr,
               Array.get(U32, a3, 0))
        case 41:
          (a2, _) = p
          +more = A.ge01(tn, U32.inc(ti))
          step(f, c, gg, A.sel(more, 42, 60), ss, n, beta, pmk, dep, best, lb,
               lmk, v1k, v2k, mv, ti, tn, g, cost, used, ret, nst, ngs, npr,
               Array.get(U32, a2, U32.add(U32.add(p2tb(dep, c, gg),
                                                  U32.mul(ti, 3)), 2)))
        case 42:
          (a2, +tg) = p
          step(f, c, gg, 43, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               ti, tn, tg, cost, used, ret, nst, ngs, npr,
               Array.get(U32, a2, U32.add(p2tb(dep, c, gg), U32.mul(ti, 3))))
        case 43:
          (a2, +tlb) = p
          +skip = A.ge01(tlb, best)
          +mv2 = A.sel(skip, U32.min(mv, tlb), mv)
          +npr2 = U32.add(npr, U32.mul(skip, U32.sub(tn, ti)))
          step(f, c, gg, A.sel(skip, 60, 44), ss, n, A.sel(skip, beta, best),
               lmk, dep, best, lb, lmk, v1k, v2k, mv2, ti, tn, g, cost, used,
               ret, nst, ngs, npr2, Array.get(U32, a2, 0))
        case 44:
          (a2, _) = p
          a3 = ssave(a2, fsl(dep, c, gg), 45, ss, n, beta, lmk, best, lb, lmk,
                      v1k, v2k, mv, ti, tn)
          step(f, c, gg, 100, ss, n, best, lmk, U32.add(dep, 1), best, 0, 0, 0,
               0, maxu(), ti, tn, g, 0, 0, ret, nst, ngs, npr,
               Array.get(U32, a3, g))
        case 45:
          (a2, _) = p
          +val = ret
          +bt = A.sel(A.ge01(val, best), best, val)
          +cont = U32.mul(A.ge01(bt, U32.inc(lb)), A.ge01(tn, U32.inc(ti)))
          step(f, c, gg, A.sel(cont, 41, 60), ss, n, beta, pmk, dep, bt, lb,
               lmk, v1k, v2k, U32.min(mv, val), U32.inc(ti), tn, g, cost, used,
               ret, nst, ngs, npr, Array.get(U32, a2, 0))
        case 60:
          (a2, _) = p
          +exact = A.lt01(best, beta)
          +fl = U32.max(beta, lb)
          +fl2 = A.sel(U32.mul(A.ge01(best, U32.inc(lb)), A.ge01(mv, maxu())),
                       fl, U32.max(fl, mv))
          +rv = A.sel(exact, best, fl2)
          +root = A.eq01(dep, 0)
          step(f, c, gg, A.sel(root, 250, 199), ss, n, beta, pmk, dep, best, lb,
               lmk, v1k, v2k, mv, ti, tn, g, cost, used, rv, nst, ngs, npr,
               Array.get(U32, a2, A.sel(root, 0,
                                         U32.add(fsl(U32.sub(dep, 1), c, gg),
                                                 15))))
        # ============================================================ guess ====
        case 100:
          (a2, _) = p
          a3 = S.cnt(g, ss, n, maxu(), dep, c, gg, a2)
          step(f, c, gg, 101, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k,
               mv, ti, tn, g, 0, 0, ret, nst, U32.inc(ngs), npr,
               Array.get(U32, a3, S.pkcell(c, gg)))
        case 101:
          (a2, +pk) = p
          +total = U32.and(pk, 4095)
          +hw = U32.shrn(pk, 24n)
          +none = U32.sub(1, A.ge01(total, 2))
          +cst = U32.sub(U32.sub(U32.mul(3, n), total), hw)
          +prune = U32.mul(A.ge01(cst, beta), U32.sub(1, none))
          +go2 = A.sel(none, fin(dep), A.sel(prune, fin(dep), 102))
          step(f, c, gg, go2, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k,
               mv, 0, total, g, cst, 0, A.sel(none, beta, A.sel(prune, cst, ret)),
               nst, ngs, U32.add(npr, prune), Array.get(U32, a2,
                                                        S.n3cell(c, gg)))
        case 102:
          (a2, +n3) = p
          +noeval = U32.sub(1, A.ge01(n3, 1))
          +u = A.sel(noeval, fin(dep), 103)
          step(f, c, gg, u, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               0, tn, g, cost, used, cost, nst, ngs, npr,
               Array.get(U32, a2, 0))
        case 103:
          (a2, _) = p
          a3 = S.offsets(tn, dep, bkb(dep, c, gg), c, gg, a2)
          step(f, c, gg, 104, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k,
               mv, 0, tn, g, cost, used, ret, nst, ngs, npr,
               Array.get(U32, a3, S.ent_at(dep, c, gg)))
        case 104:
          (a2, +k) = p
          +more = A.ge01(tn, U32.inc(ti))
          +ski = U32.sub(1, A.ge01(k, 3))
          +next = U32.max(U32.sub(1, more), ski)
          +u = A.sel(more, A.sel(ski, 104, 105), 112)
          step(f, c, gg, u, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               U32.add(ti, next), tn, k, cost, used, ret, nst, ngs, npr,
               Array.get(U32, a2, U32.add(S.ent_at(dep, c, gg),
                                          U32.add(ti, next))))
        case 105:
          (a2, _) = p
          step(f, c, gg, 106, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k,
               mv, ti, tn, g, cost, used, ret, nst, ngs, npr,
               Array.get(U32, a2, U32.add(S.off_at(dep, c, gg), ti)))
        case 106:
          (a2, +off) = p
          step(f, c, gg, 107, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k,
               mv, ti, tn, g, cost, off, ret, nst, ngs, npr,
               Array.get(U32, a2, S.cap_at(pmk, g, c, gg)))
        case 107:
          (a2, +lp) = p
          +goq = U32.sub(1, A.ge01(g, 16))
          +u = A.sel(goq, 111, 109)
          step(f, c, gg, u, ss, n, beta, pmk, dep, best, lb, lmk, lp, v2k, mv,
               ti, tn, g, cost, used, ret, nst, ngs, npr,
               Array.get(U32, a2, U32.add(bkb(dep, c, gg),
                                          U32.add(used, 0))))
        case 108:
          (a2, +pk) = p
          +ex = U32.and(pk, 1)
          +qv = U32.shrn(pk, 1n)
          +usd = U32.max(v1k, qv)
          +u = A.sel(A.eq01(ex, 1), 110, 109)
          step(f, c, gg, u, ss, n, beta, pmk, dep, best, lb, lmk, usd, v2k, mv,
               ti, tn, g, cost, used, ret, nst, ngs, npr,
               Array.get(U32, a2, 0))
        case 109:
          (a2, _) = p
          # usd in v1k; cost += usd - (2k-1); recurse.
          +c2 = U32.sub(U32.add(cost, v1k), U32.sub(U32.mul(2, g), 1))
          +b = U32.sub(c2, v1k)
          +nbe = U32.sub(beta, U32.min(beta, b))
          +pr = A.ge01(U32.inc(v1k), nbe)
          +ck = U32.max(U32.min(g, pmk), 2)
          a3 = gsave(a2, fsl(dep, c, gg), 113, beta, c2, v1k, ti, tn)
          +sbk = U32.add(bkb(dep, c, gg), used)
          step(f, c, gg, A.sel(pr, fin(dep), 0), sbk, g, nbe, ck,
               U32.add(dep, A.sel(pr, 0, 1)), 0,
               0, 0, 0, 0, 0, ti, tn, g, c2, v1k, A.sel(pr, c2, ret), nst, ngs,
               U32.add(npr, pr), Array.get(U32, a3, 0))
        case 110:
          (a2, _) = p
          # Exact quick bucket: cost += usd - (2k-1), no recursion.
          +c2 = U32.sub(U32.add(cost, v1k), U32.sub(U32.mul(2, g), 1))
          step(f, c, gg, 104, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k,
               mv, U32.inc(ti), tn, g, c2, used, ret, nst, ngs, npr,
               Array.get(U32, a2, U32.add(S.ent_at(dep, c, gg),
                                          U32.inc(ti))))
        case 111:
          (a2, _) = p
          # Quick eval call for a 3..15 bucket. Its set is bkb + off.
          +sbk = U32.add(bkb(dep, c, gg), used)
          a3 = H.quick(Nat.add(Nat.mul(U32.to_nat(g), 64n), 64n), 6, 0, 0, 0,
                        0, 0, 0, 0, 0, sbk, g, c, gg, qo(c, gg),
                        Array.get(U32, a2, 0))
          step(f, c, gg, 108, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k,
               mv, ti, tn, g, cost, used, ret, nst, ngs, npr,
               Array.get(U32, a3, qo(c, gg)))
        case 112:
          (a2, _) = p
          +pr = A.ge01(cost, beta)
          +root = A.eq01(dep, 0)
          step(f, c, gg, A.sel(root, 250, 199), ss, n, beta, pmk, dep, best, lb,
               lmk, v1k, v2k, mv, ti, tn, g, cost, used, cost, nst, ngs,
               U32.add(npr, pr),
               Array.get(U32, a2, A.sel(root, 0,
                                         U32.add(fsl(U32.sub(dep, 1), c, gg),
                                                 15))))
        case 113:
          (a2, _) = p
          +val = ret
          +b = U32.sub(cost, used)
          +c2 = U32.add(b, val)
          +cut = A.ge01(c2, beta)
          step(f, c, gg, A.sel(cut, 112, 104), ss, n, beta, pmk, dep, best, lb,
               lmk, v1k, v2k, mv, U32.inc(ti), tn, g, A.sel(cut, cost, c2), used,
               A.sel(cut, c2, ret), nst, ngs, U32.add(npr, cut),
               Array.get(U32, a2, 0))
        # ========================================================== returns ====
        case 199:
          (a2, +lp) = p
          step(f, c, gg, lp, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               ti, tn, g, cost, used, ret, nst, ngs, npr,
               Array.get(U32, a2, 0))
        case 200:
          (a2, _) = p
          step(f, c, gg, 201, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               ti, tn, g, cost, used, ret, nst, ngs, npr,
               Array.get(U32, a2, U32.add(fsl(U32.sub(dep, 1), c, gg), 1)))
        case 201:
          (a2, +v) = p
          step(f, c, gg, 202, v, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               ti, tn, g, cost, used, ret, nst, ngs, npr,
               Array.get(U32, a2, U32.add(fsl(U32.sub(dep, 1), c, gg), 2)))
        case 202:
          (a2, +v) = p
          step(f, c, gg, 203, ss, v, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               ti, tn, g, cost, used, ret, nst, ngs, npr,
               Array.get(U32, a2, U32.add(fsl(U32.sub(dep, 1), c, gg), 3)))
        case 203:
          (a2, +v) = p
          step(f, c, gg, 204, ss, n, v, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               ti, tn, g, cost, used, ret, nst, ngs, npr,
               Array.get(U32, a2, U32.add(fsl(U32.sub(dep, 1), c, gg), 4)))
        case 204:
          (a2, +v) = p
          step(f, c, gg, 205, ss, n, beta, v, dep, best, lb, lmk, v1k, v2k, mv,
               ti, tn, g, cost, used, ret, nst, ngs, npr,
               Array.get(U32, a2, U32.add(fsl(U32.sub(dep, 1), c, gg), 5)))
        case 205:
          (a2, +v) = p
          step(f, c, gg, 206, ss, n, beta, pmk, dep, v, lb, lmk, v1k, v2k, mv,
               ti, tn, g, cost, used, ret, nst, ngs, npr,
               Array.get(U32, a2, U32.add(fsl(U32.sub(dep, 1), c, gg), 6)))
        case 206:
          (a2, +v) = p
          step(f, c, gg, 207, ss, n, beta, pmk, dep, best, v, lmk, v1k, v2k, mv,
               ti, tn, g, cost, used, ret, nst, ngs, npr,
               Array.get(U32, a2, U32.add(fsl(U32.sub(dep, 1), c, gg), 7)))
        case 207:
          (a2, +v) = p
          step(f, c, gg, 208, ss, n, beta, pmk, dep, best, lb, v, v1k, v2k, mv,
               ti, tn, g, cost, used, ret, nst, ngs, npr,
               Array.get(U32, a2, U32.add(fsl(U32.sub(dep, 1), c, gg), 8)))
        case 208:
          (a2, +v) = p
          step(f, c, gg, 209, ss, n, beta, pmk, dep, best, lb, lmk, v, v2k, mv,
               ti, tn, g, cost, used, ret, nst, ngs, npr,
               Array.get(U32, a2, U32.add(fsl(U32.sub(dep, 1), c, gg), 9)))
        case 209:
          (a2, +v) = p
          step(f, c, gg, 210, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v, mv,
               ti, tn, g, cost, used, ret, nst, ngs, npr,
               Array.get(U32, a2, U32.add(fsl(U32.sub(dep, 1), c, gg), 10)))
        case 210:
          (a2, +v) = p
          step(f, c, gg, 211, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, v,
               ti, tn, g, cost, used, ret, nst, ngs, npr,
               Array.get(U32, a2, U32.add(fsl(U32.sub(dep, 1), c, gg), 11)))
        case 211:
          (a2, +v) = p
          step(f, c, gg, 212, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               v, tn, g, cost, used, ret, nst, ngs, npr,
               Array.get(U32, a2, U32.add(fsl(U32.sub(dep, 1), c, gg), 12)))
        case 212:
          (a2, +v) = p
          step(f, c, gg, 213, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               ti, v, g, cost, used, ret, nst, ngs, npr,
               Array.get(U32, a2, U32.add(fsl(U32.sub(dep, 1), c, gg), 0)))
        case 213:
          (a2, +rph) = p
          step(f, c, gg, rph, ss, n, beta, pmk, U32.sub(dep, 1), best, lb, lmk,
               v1k, v2k, mv, ti, tn, g, cost, used, ret, nst, ngs, npr,
               Array.get(U32, a2, 0))
        case 220:
          (a2, _) = p
          step(f, c, gg, 221, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               ti, tn, g, cost, used, ret, nst, ngs, npr,
               Array.get(U32, a2, U32.add(fsl(U32.sub(dep, 1), c, gg), 1)))
        case 221:
          (a2, +v) = p
          step(f, c, gg, 222, ss, n, v, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               ti, tn, g, cost, used, ret, nst, ngs, npr,
               Array.get(U32, a2, U32.add(fsl(U32.sub(dep, 1), c, gg), 2)))
        case 222:
          (a2, +v) = p
          step(f, c, gg, 223, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               ti, tn, g, v, used, ret, nst, ngs, npr,
               Array.get(U32, a2, U32.add(fsl(U32.sub(dep, 1), c, gg), 3)))
        case 223:
          (a2, +v) = p
          step(f, c, gg, 224, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               ti, tn, g, cost, v, ret, nst, ngs, npr,
               Array.get(U32, a2, U32.add(fsl(U32.sub(dep, 1), c, gg), 4)))
        case 224:
          (a2, +v) = p
          step(f, c, gg, 225, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               v, tn, g, cost, used, ret, nst, ngs, npr,
               Array.get(U32, a2, U32.add(fsl(U32.sub(dep, 1), c, gg), 5)))
        case 225:
          (a2, +v) = p
          step(f, c, gg, 226, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               ti, v, g, cost, used, ret, nst, ngs, npr,
               Array.get(U32, a2, U32.add(fsl(U32.sub(dep, 1), c, gg), 0)))
        case 226:
          (a2, +rph) = p
          step(f, c, gg, rph, ss, n, beta, pmk, U32.sub(dep, 1), best, lb, lmk,
               v1k, v2k, mv, ti, tn, g, cost, used, ret, nst, ngs, npr,
               Array.get(U32, a2, 0))
        case 250:
          (a2, _) = p
          a3 = Array.set(U32, a2, met(0, c, gg), ret)
          a4 = Array.set(U32, a3, met(1, c, gg), nst)
          a5 = Array.set(U32, a4, met(2, c, gg), ngs)
          Array.set(U32, a5, met(3, c, gg), npr)
        case _:
          (a2, _) = p
          a3 = Array.set(U32, a2, met(0, c, gg), ret)
          Array.set(U32, a3, met(1, c, gg), nst)
