# Rust's phase-1 and phase-2 guess scans (min_state_val_with_hash), and the
# tuple insertion sort. Each scan is one self-recursive phase machine over the
# flat state array; results go to fixed cells and the tuple buffers.
#
# Phase 1: walk the candidates of the set (the guess is the candidate itself,
#   skipped in the count). Cheap lower bounds 2n-1 (no duplicate response) and
#   2n (one duplicate); otherwise the cap bound and the expected-remaining
#   equality test. Accepted cheap values raise `best`; the rest become tuples.
# Phase 2: walk every guess not in the set, filtered by the letter masks, with
#   Rust's shortcut for buckets that never reach size 3, the 2-bucket skip, and
#   the same cap/expected bound. Another tuple buffer.
#
# Result cells (offsets inside off_qgen):
#   700 best   701 lmk   702 v1/v2   703 mv   704 nt
#   705 ngs delta   706 npr delta   707 gen   708 cmask   709 multi
#   710..712 scratch tuple (an append that must not happen lands here)
import Base
import ./geo.bend as G
import ./arith.bend as A
import ./sec.bend as S

def qc(+c: U32, +gg: U32, +i: U32) -> U32:
  U32.add(G.off_qgen(c, gg), i)

def sat(+a: U32, +b: U32) -> U32:
  U32.sub(a, U32.min(a, b))

# min_k_needed for phase 1: min(local_max_k + 1, 3n - best).
def mkn1(+best: U32, +lmk: U32, +n: U32) -> U32:
  U32.min(U32.inc(lmk), sat(U32.mul(3, n), best))

# phase 2 uses 3n - (best - 1).
def mkn2(+best: U32, +lmk: U32, +n: U32) -> U32:
  U32.min(U32.inc(lmk), sat(U32.mul(3, n), sat(best, 1)))

# Lexicographic (lb, exp, g) comparison: 1 when the triple a is greater.
def tgt(+alb: U32, +aex: U32, +ag: U32, +blb: U32, +bex: U32, +bg: U32) -> U32:
  +hi = A.gt01b(alb, blb)
  +eq = A.eq01(alb, blb)
  +hi2 = A.gt01b(aex, bex)
  +eq2 = A.eq01(aex, bex)
  +hi3 = A.gt01b(ag, bg)
  U32.max(hi, U32.mul(eq, U32.max(hi2, U32.mul(eq2, hi3))))

# ---------------------------------------------------------------- sort -------
#
# Insertion sort of `count` triples at `base`, ascending by (lb, exp, g), the
# same order as GuessTuple's Ord. ins_go shifts one key left while the previous
# triple is greater, then writes the key; sort_go walks j = 1..count-1.
#
# ins phases: 0 read prev.lb, 1 read prev.exp, 2 read prev.g, 3 write key.
def ins_go(+fuel: Nat, +ph: U32, +k: U32, +klb: U32, +kex: U32, +kg: U32,
           +base: U32, +plb: U32, +pex: U32, +pg: U32,
           p: Array<U32> & U32) -> Array<U32>:
  match fuel:
    case 0n:
      (a0, _) = p
      a0
    case 1n+f:
      match ph:
        case 0:
          (a2, _) = p
          +zero = A.eq01(k, 0)
          +idx = U32.add(base, U32.mul(U32.sub(k, 1), 3))
          ins_go(f, A.sel(zero, 5, 1), k, klb, kex, kg, base, 0, 0, 0,
                 Array.get(U32, a2, idx))
        case 1:
          (a2, +v) = p
          +idx = U32.add(U32.add(base, U32.mul(U32.sub(k, 1), 3)), 1)
          ins_go(f, 2, k, klb, kex, kg, base, v, 0, 0,
                 Array.get(U32, a2, idx))
        case 2:
          (a2, +v) = p
          +idx = U32.add(U32.add(base, U32.mul(U32.sub(k, 1), 3)), 2)
          ins_go(f, 3, k, klb, kex, kg, base, plb, v, 0,
                 Array.get(U32, a2, idx))
        case 3:
          (a2, +v) = p
          +mv = tgt(plb, pex, v, klb, kex, kg)
          +idx = U32.add(base, U32.mul(k, 3))
          ins_go(f, A.sel(mv, 4, 5), k, klb, kex, kg, base, plb, pex, v,
                 Array.get(U32, a2, idx))
        case 4:
          # prev > key: move prev into slot k, then read the next prev.lb.
          (a2, _) = p
          +dst = U32.add(base, U32.mul(k, 3))
          a3 = Array.set(U32, a2, dst, plb)
          a4 = Array.set(U32, a3, U32.inc(dst), pex)
          a5 = Array.set(U32, a4, U32.inc(U32.inc(dst)), pg)
          +k2 = U32.sub(k, 1)
          +idx = U32.add(base, U32.mul(U32.sub(k2, 1), 3))
          ins_go(f, A.sel(A.eq01(k2, 0), 5, 1), k2, klb, kex, kg, base, 0, 0,
                 0, Array.get(U32, a5, idx))
        case 5:
          (a2, _) = p
          +dst = U32.add(base, U32.mul(k, 3))
          a3 = Array.set(U32, a2, dst, klb)
          a4 = Array.set(U32, a3, U32.inc(dst), kex)
          Array.set(U32, a4, U32.inc(U32.inc(dst)), kg)
        case _:
          (a2, _) = p
          a2

def sort_go(+fuel: Nat, +ph: U32, +j: U32, +count: U32, +base: U32,
            +klb: U32, +kex: U32, +kg: U32, p: Array<U32> & U32) -> Array<U32>:
  match fuel:
    case 0n:
      (a0, _) = p
      a0
    case 1n+f:
      match ph:
        case 0:
          (a2, _) = p
          +done = A.ge01(j, count)
          +idx = U32.add(base, U32.mul(j, 3))
          sort_go(f, A.sel(done, 9, 1), j, count, base, 0, 0, 0,
                  Array.get(U32, a2, idx))
        case 1:
          (a2, +v) = p
          +idx = U32.add(U32.add(base, U32.mul(j, 3)), 1)
          sort_go(f, 2, j, count, base, v, kex, kg, Array.get(U32, a2, idx))
        case 2:
          (a2, +v) = p
          +idx = U32.add(U32.add(base, U32.mul(j, 3)), 2)
          sort_go(f, 3, j, count, base, klb, v, kg, Array.get(U32, a2, idx))
        case 3:
          (a2, +v) = p
          +idx = U32.add(base, U32.mul(j, 3))
          sort_go(f, 4, j, count, base, klb, kex, v, Array.get(U32, a2, idx))
        case 4:
          (a2, _) = p
          +fuel2 = Nat.add(Nat.mul(U32.to_nat(j), 8n), 32n)
          +idx = U32.add(base, U32.mul(j, 3))
          a3 = ins_go(fuel2, 0, j, klb, kex, kg, base, 0, 0, 0,
                      Array.get(U32, a2, idx))
          +j2 = U32.inc(j)
          +idx2 = U32.add(base, U32.mul(j2, 3))
          sort_go(f, A.sel(A.ge01(j2, count), 9, 0), j2, count, base, 0, 0, 0,
                  Array.get(U32, a3, idx2))
        case 9:
          (a2, _) = p
          a2
        case _:
          (a2, _) = p
          a2

def sort3(a: Array<U32>, +base: U32, +count: U32) -> Array<U32>:
  +fuel = Nat.add(Nat.mul(U32.to_nat(count), Nat.mul(U32.to_nat(count), 8n)),
                  64n)
  +idx = U32.add(base, 3)
  sort_go(fuel, A.sel(A.ge01(1, count), 9, 0), 1, count, base, 0, 0, 0,
          Array.get(U32, a, idx))

# -------------------------------------------------------------- phase 1 ------
#
# ph 0 read set[ci] -> 1 read c2g -> 2 cnt -> 3 read pk -> 4 read n3 ->
# 5 decide/read dummy -> 6 stats -> 7 read lb -> 8 read exp -> 9 shortcut
# decision -> 10 generic decision -> 11 finish. A decision that continues
# reads set[ci+1] and returns to ph 1.
def p1_go(+fuel: Nat, +ph: U32, +ci: U32, +best: U32, +lmk: U32, +v1: U32,
          +mv: U32, +nt: U32, +ngs: U32, +npr: U32, +gen: U32,
          +ss: U32, +n: U32, +pmk: U32, +dep: U32, +c: U32, +gg: U32,
          +cand: U32, +g: U32, +dup: U32, +t: U32, +h3: U32, +ab: U32,
          +lb: U32, +exp: U32, +plb: U32, +pex: U32, +pg: U32,
          p: Array<U32> & U32) -> Array<U32>:
  match fuel:
    case 0n:
      (a2, _) = p
      a2
    case 1n+f:
      match ph:
        case 0:
          (a2, _) = p
          +done = A.ge01(ci, n)
          +idx = A.sel(done, 0, U32.add(ss, ci))
          p1_go(f, A.sel(done, 15, 1), ci, best, lmk, v1, mv, nt, ngs, npr,
                gen, ss, n, pmk, dep, c, gg, cand, g, dup, t, h3, ab, lb, exp,
                plb, pex, pg, Array.get(U32, a2, idx))
        case 1:
          (a2, +v) = p
          +idx = U32.add(G.off_c2g(c, gg), v)
          p1_go(f, 2, ci, best, lmk, v1, mv, nt, ngs, npr, gen, ss, n, pmk,
                dep, c, gg, v, g, dup, t, h3, ab, lb, exp, plb, pex, pg,
                Array.get(U32, a2, idx))
        case 2:
          (a2, +v) = p
          +gen2 = U32.add(gen, 1024)
          a3 = S.cnt(v, ss, n, ci, gen2, dep, c, gg, a2)
          p1_go(f, 3, ci, best, lmk, v1, mv, nt, ngs, npr, gen2, ss, n, pmk,
                dep, c, gg, cand, v, dup, t, h3, ab, lb, exp, plb, pex, pg,
                Array.get(U32, a3, S.pkcell(c, gg)))
        case 3:
          (a2, +v) = p
          +t0 = U32.and(v, 4095)
          +dup0 = U32.and(U32.shrn(v, 12n), 4095)
          p1_go(f, 4, ci, best, lmk, v1, mv, nt, ngs, npr, gen, ss, n, pmk,
                dep, c, gg, cand, g, dup0, t0, h3, ab, lb, exp, plb, pex, pg,
                Array.get(U32, a2, S.n3cell(c, gg)))
        case 4:
          (a2, +v) = p
          +h3b = A.nz(v)
          +abb = A.gt01b(dup, sat(n, mkn1(best, lmk, n)))
          +lmk2 = A.sel(abb, lmk, U32.max(lmk, U32.inc(t)))
          +ml1 = U32.sub(U32.add(U32.mul(2, n), dup), 1)
          +early = U32.mul(h3b, U32.mul(A.ge01(ml1, best),
                                        A.lt01(mv, U32.inc(ml1))))
          +next = A.sel(abb, 13, A.sel(h3b, A.sel(early, 12, 6), 9))
          p1_go(f, next, ci, best, lmk2, v1, mv, nt, ngs, npr, gen, ss, n,
                pmk, dep, c, gg, cand, g, dup, t, h3b, abb, lb, exp, plb, pex,
                pg, Array.get(U32, a2, 0))
        case 6:
          (a2, _) = p
          a3 = S.stats(0, t, dep, c, gg, pmk, n, 1, gen, 1, a2)
          p1_go(f, 7, ci, best, lmk, v1, mv, nt, ngs, npr, gen, ss, n, pmk,
                dep, c, gg, cand, g, dup, t, h3, ab, lb, exp, plb, pex, pg,
                Array.get(U32, a3, S.lbcell(c, gg)))
        case 7:
          (a2, +v) = p
          p1_go(f, 8, ci, best, lmk, v1, mv, nt, ngs, npr, gen, ss, n, pmk,
                dep, c, gg, cand, g, dup, t, h3, ab, v, exp, plb, pex, pg,
                Array.get(U32, a2, S.expcell(c, gg)))
        case 8:
          (a2, +v) = p
          p1_go(f, 10, ci, best, lmk, v1, mv, nt, ngs, npr, gen, ss, n, pmk,
                dep, c, gg, cand, g, dup, t, h3, ab, lb, v, plb, pex, pg,
                Array.get(U32, a2, 0))
        case 9:
          # no bucket reaches 3: lb = 2n - 1 + dup (Rust's shortcut).
          (a2, _) = p
          +l1 = U32.sub(U32.add(U32.mul(2, n), dup), 1)
          +take1 = A.lt01(l1, best)
          +v1b = A.sel(U32.mul(take1, A.ge01(U32.inc(t), v1)), U32.inc(t), v1)
          +ngsb = U32.add(ngs, take1)
          +mv1 = U32.min(mv, l1)
          +best1 = A.sel(take1, l1, best)
          +stop0 = U32.mul(take1, A.eq01(dup, 0))
          +stop1 = A.ge01(mkn1(best1, lmk, n), U32.inc(n))
          +stop = U32.max(U32.max(stop0, stop1), A.ge01(U32.inc(ci), n))
          p1_go(f, A.sel(stop, 15, 1), U32.inc(ci), best1, lmk, v1b, mv1, nt, ngsb,
                npr, gen, ss, n, pmk, dep, c, gg, cand, g, dup, t, h3, ab,
                lb, exp, plb, pex, pg,
                Array.get(U32, a2, A.sel(stop, 0, U32.add(ss, U32.inc(ci)))))
        case 10:
          # generic: lb from stats; accept when exp == n + 2*dup, else tuple.
          (a2, _) = p
          +take = A.lt01(lb, best)
          +v1b = A.sel(U32.mul(take, A.ge01(U32.inc(t), v1)), U32.inc(t), v1)
          +cheap = U32.mul(take, A.eq01(exp, U32.add(n, U32.mul(2, dup))))
          +ngsb = U32.add(ngs, cheap)
          +best1 = A.sel(cheap, lb, best)
          +mv1 = U32.min(mv, lb)
          +app = U32.sub(take, cheap)
          +mv2 = A.sel(app, mv, U32.min(mv, lb))
          +ntb = U32.add(nt, app)
          +base = U32.mul(dep, U32.mul(c, 3))
          +slot0 = U32.add(G.off_p1t(c, gg), base)
          +slot = A.sel(app, U32.add(slot0, U32.mul(nt, 3)),
                        qc(c, gg, 710))
          a3 = Array.set(U32, a2, slot, lb)
          a4 = Array.set(U32, a3, U32.inc(slot), exp)
          a5 = Array.set(U32, a4, U32.inc(U32.inc(slot)), g)
          +stop = U32.max(A.ge01(mkn1(best1, lmk, n), U32.inc(n)),
                          A.ge01(U32.inc(ci), n))
          p1_go(f, A.sel(stop, 15, 1), U32.inc(ci), best1, lmk, v1b, mv2, ntb, ngsb,
                npr, gen, ss, n, pmk, dep, c, gg, cand, g, dup, t, h3, ab,
                lb, exp, plb, pex, pg,
                Array.get(U32, a5, A.sel(stop, 0, U32.add(ss, U32.inc(ci)))))
        case 12:
          # early-out: min_lb >= best and min_val_found <= min_lb.
          (a2, _) = p
          +stop = U32.max(A.ge01(mkn1(best, lmk, n), U32.inc(n)),
                          A.ge01(U32.inc(ci), n))
          p1_go(f, A.sel(stop, 15, 1), U32.inc(ci), best, lmk, v1, mv, nt, ngs, npr,
                gen, ss, n, pmk, dep, c, gg, cand, g, dup, t, h3, ab, lb, exp,
                plb, pex, pg,
                Array.get(U32, a2, A.sel(stop, 0, U32.add(ss, U32.inc(ci)))))
        case 13:
          (a2, _) = p
          +afin = A.ge01(U32.inc(ci), n)
          p1_go(f, A.sel(afin, 15, 1), U32.inc(ci), best, lmk, v1,
                U32.min(mv, best), nt, ngs, npr, gen, ss, n, pmk, dep, c, gg,
                cand, g, dup, t, h3, ab, lb, exp, plb, pex, pg,
                Array.get(U32, a2, A.sel(afin, 0, U32.add(ss, U32.inc(ci)))))
        case 15:
          (a2, _) = p
          a3 = Array.set(U32, a2, qc(c, gg, 700), best)
          a4 = Array.set(U32, a3, qc(c, gg, 701), lmk)
          a5 = Array.set(U32, a4, qc(c, gg, 702), v1)
          a6 = Array.set(U32, a5, qc(c, gg, 703), mv)
          a7 = Array.set(U32, a6, qc(c, gg, 704), nt)
          a8 = Array.set(U32, a7, qc(c, gg, 705), ngs)
          a9 = Array.set(U32, a8, qc(c, gg, 706), npr)
          Array.set(U32, a9, qc(c, gg, 707), gen)

        case _:
          (a2, _) = p
          a3 = Array.set(U32, a2, qc(c, gg, 700), best)
          a4 = Array.set(U32, a3, qc(c, gg, 701), lmk)
          a5 = Array.set(U32, a4, qc(c, gg, 702), v1)
          a6 = Array.set(U32, a5, qc(c, gg, 703), mv)
          a7 = Array.set(U32, a6, qc(c, gg, 704), nt)
          a8 = Array.set(U32, a7, qc(c, gg, 705), ngs)
          a9 = Array.set(U32, a8, qc(c, gg, 706), npr)
          Array.set(U32, a9, qc(c, gg, 707), gen)

def p1_scan(a: Array<U32>, +ss: U32, +n: U32, +beta: U32, +pmk: U32,
            +dep: U32, +gen: U32, +c: U32, +gg: U32) -> Array<U32>:
  +fuel = Nat.add(Nat.mul(U32.to_nat(n), 64n), 64n)
  p1_go(fuel, 0, 0, beta, 0, 0, 4294967295, 0, 0, 0, gen, ss, n, pmk, dep, c,
        gg, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, Array.get(U32, a, ss))

# -------------------------------------------------------------- phase 2 ------
#
# Setup phases 20..24 mark the set's guess indices (tag = gen + 512) and build
# c_mask_set / multi_c_mask exactly as the Rust loop does. Then the guess walk:
# 30 read the mark -> 31 read gmask -> 32 cnt -> 33 read pk -> 34 read n3 ->
# 35 decide/read dummy -> 36 stats -> 37 read lb -> 38 read exp and decide ->
# 40 advance (read the next mark) -> 44 finish.
def p2_go(+fuel: Nat, +ph: U32, +ci: U32, +g: U32, +best: U32, +lmk: U32,
          +v2: U32, +mv: U32, +nt: U32, +ngs: U32, +npr: U32, +gen: U32,
          +cm: U32, +mu: U32, +ss: U32, +n: U32, +pmk: U32, +dep: U32,
          +c: U32, +gg: U32, +cand: U32, +m: U32, +dup: U32, +t: U32,
          +h3: U32, +ab: U32, +lb: U32, +exp: U32, +plb: U32, +pex: U32,
          +pg: U32, p: Array<U32> & U32) -> Array<U32>:
  match fuel:
    case 0n:
      (a2, _) = p
      a2
    case 1n+f:
      match ph:
        case 20:
          (a2, _) = p
          +done = A.ge01(ci, n)
          +idx = A.sel(done, 0, U32.add(ss, ci))
          p2_go(f, A.sel(done, 24, 21), ci, g, best, lmk, v2, mv, nt, ngs, npr,
                gen, cm, mu, ss, n, pmk, dep, c, gg, cand, m, dup, t, h3, ab,
                lb, exp, plb, pex, pg, Array.get(U32, a2, idx))
        case 21:
          (a2, +v) = p
          +idx = U32.add(G.off_c2g(c, gg), v)
          p2_go(f, 22, ci, g, best, lmk, v2, mv, nt, ngs, npr, gen, cm, mu,
                ss, n, pmk, dep, c, gg, v, m, dup, t, h3, ab, lb, exp, plb,
                pex, pg, Array.get(U32, a2, idx))
        case 22:
          (a2, +v) = p
          +idx = U32.add(G.off_cmask(c, gg), cand)
          p2_go(f, 23, ci, v, best, lmk, v2, mv, nt, ngs, npr, gen, cm, mu,
                ss, n, pmk, dep, c, gg, cand, m, dup, t, h3, ab, lb, exp, plb,
                pex, pg, Array.get(U32, a2, idx))
        case 23:
          (a2, +v) = p
          +mb = U32.or(mu, U32.and(cm, v))
          +cmb = U32.or(cm, v)
          +tag = U32.add(gen, 512)
          +midx = U32.add(G.off_sset(c, gg), U32.mul(dep, gg))
          a3 = Array.set(U32, a2, U32.add(midx, g), tag)
          +ci2 = U32.inc(ci)
          +done = A.ge01(ci2, n)
          +idx = A.sel(done, 0, U32.add(ss, ci2))
          p2_go(f, A.sel(done, 24, 21), ci2, g, best, lmk, v2, mv, nt, ngs, npr,
                gen, cmb, mb, ss, n, pmk, dep, c, gg, cand, m, dup, t, h3, ab,
                lb, exp, plb, pex, pg, Array.get(U32, a3, idx))
        case 24:
          (a2, _) = p
          +midx = U32.add(G.off_sset(c, gg), U32.mul(dep, gg))
          a3 = Array.set(U32, a2, qc(c, gg, 708), cm)
          a4 = Array.set(U32, a3, qc(c, gg, 709), mu)
          p2_go(f, 30, 0, 0, best, lmk, v2, mv, nt, ngs, npr, gen, cm, mu, ss,
                n, pmk, dep, c, gg, cand, m, dup, t, h3, ab, lb, exp, plb, pex,
                pg, Array.get(U32, a4, midx))
        case 30:
          # p holds mark[g].
          (a2, +v) = p
          +done = A.ge01(g, gg)
          +same = A.eq01(v, U32.add(gen, 512))
          +g2 = A.sel(same, U32.inc(g), g)
          +sbase = U32.add(G.off_sset(c, gg), U32.mul(dep, gg))
          +idx = A.sel(same, U32.add(sbase, g2),
                       U32.add(G.off_gmask(c, gg), g))
          p2_go(f, A.sel(done, 44, A.sel(same, 30, 31)), ci, g2, best, lmk, v2, mv,
                nt, ngs, npr, gen, cm, mu, ss, n, pmk, dep, c, gg, cand, m, dup,
                t, h3, ab, lb, exp, plb, pex, pg, Array.get(U32, a2, idx))
        case 31:
          # p holds gmask[g]; Rust's single-shared-letter filter.
          (a2, +v) = p
          +sh = U32.and(v, cm)
          +pc = U32.and(sh, U32.sub(sh, 1))
          +alone = A.eq01(pc, 0)
          +nomulti = U32.sub(1, A.nz(U32.and(sh, mu)))
          +skipf = U32.and(alone, nomulti)
          +g2 = A.sel(skipf, U32.inc(g), g)
          +sbase = U32.add(G.off_sset(c, gg), U32.mul(dep, gg))
          +idx = A.sel(skipf, U32.add(sbase, g2), 0)
          p2_go(f, A.sel(skipf, 30, 32), ci, g2, best, lmk, v2, mv, nt, ngs, npr,
                gen, cm, mu, ss, n, pmk, dep, c, gg, cand, m, dup, t, h3, ab,
                lb, exp, plb, pex, pg, Array.get(U32, a2, idx))
        case 32:
          (a2, _) = p
          +gen2 = U32.add(gen, 1024)
          a3 = S.cnt(g, ss, n, 4294967295, gen2, dep, c, gg, a2)
          p2_go(f, 33, ci, g, best, lmk, v2, mv, nt, ngs, npr, gen2, cm, mu,
                ss, n, pmk, dep, c, gg, cand, m, dup, t, h3, ab, lb, exp, plb,
                pex, pg, Array.get(U32, a3, S.pkcell(c, gg)))
        case 33:
          (a2, +v) = p
          +t0 = U32.and(v, 4095)
          +dup0 = U32.and(U32.shrn(v, 12n), 4095)
          p2_go(f, 34, ci, g, best, lmk, v2, mv, nt, ngs, npr, gen, cm, mu,
                ss, n, pmk, dep, c, gg, cand, m, dup0, t0, h3, ab, lb, exp,
                plb, pex, pg, Array.get(U32, a2, S.n3cell(c, gg)))
        case 34:
          (a2, +v) = p
          +h3b = A.nz(v)
          +abb = A.gt01b(dup, sat(n, mkn2(best, lmk, n)))
          +minlb = U32.add(U32.mul(2, n), dup)
          +early = U32.and(A.ge01(sat(n, dup), 3),
                           U32.and(A.ge01(minlb, best), A.lt01(mv, minlb)))
          +next = A.sel(abb, 40, A.sel(h3b, A.sel(early, 43,
                                       A.sel(A.eq01(t, 1), 40, 36)), 42))
          p2_go(f, next, ci, g, best, lmk, v2, mv, nt, ngs, npr, gen, cm, mu,
                ss, n, pmk, dep, c, gg, cand, m, dup, t, h3b, abb, lb, exp,
                plb, pex, pg, Array.get(U32, a2, 0))
        case 36:
          (a2, _) = p
          a3 = S.stats(0, t, dep, c, gg, pmk, n, 0, gen, 1, a2)
          p2_go(f, 37, ci, g, best, lmk, v2, mv, nt, ngs, npr, gen, cm, mu,
                ss, n, pmk, dep, c, gg, cand, m, dup, t, h3, ab, lb, exp, plb,
                pex, pg, Array.get(U32, a3, S.lbcell(c, gg)))
        case 37:
          (a2, +v) = p
          p2_go(f, 38, ci, g, best, lmk, v2, mv, nt, ngs, npr, gen, cm, mu,
                ss, n, pmk, dep, c, gg, cand, m, dup, t, h3, ab, v, exp, plb,
                pex, pg, Array.get(U32, a2, S.expcell(c, gg)))
        case 38:
          # p holds exp and lb is known: the {1, n-1} skip, then the generic
          # acceptance test. local_max_k is only updated when we proceed.
          (a2, +v) = p
          +nsq = U32.mul(U32.sub(n, 1), U32.sub(n, 1))
          +twoone = U32.and(A.eq01(t, 2), A.eq01(v, U32.inc(nsq)))
          +proceed = U32.sub(1, twoone)
          +lmk2 = A.sel(proceed, U32.max(lmk, t), lmk)
          +take = U32.and(proceed, A.lt01(lb, best))
          +v2b = A.sel(U32.mul(take, A.ge01(t, v2)), t, v2)
          +cheap = U32.mul(take, A.eq01(v, U32.add(n, U32.mul(2, dup))))
          +ngsb = U32.add(ngs, cheap)
          +best1 = A.sel(cheap, lb, best)
          +app = U32.sub(take, cheap)
          +mv1 = A.sel(U32.max(app, twoone), mv, U32.min(mv, lb))
          +ntb = U32.add(nt, app)
          +base = U32.mul(dep, U32.mul(gg, 3))
          +slot0 = U32.add(G.off_p2t(c, gg), base)
          +slot = A.sel(app, U32.add(slot0, U32.mul(nt, 3)), qc(c, gg, 711))
          +stop = A.ge01(mkn2(best1, lmk2, n), U32.inc(n))
          +g2 = U32.inc(g)
          +done2 = A.ge01(g2, gg)
          +sbase = U32.add(G.off_sset(c, gg), U32.mul(dep, gg))
          +idx = A.sel(done2, 0, U32.add(sbase, g2))
          a3 = Array.set(U32, a2, slot, lb)
          a4 = Array.set(U32, a3, U32.inc(slot), v)
          a5 = Array.set(U32, a4, U32.inc(U32.inc(slot)), g)
          +next = A.sel(twoone, 40, A.sel(stop, 44, 30))
          p2_go(f, next, ci, g2, best1, lmk2, v2b, mv1, ntb, ngsb,
                npr, gen, cm, mu, ss, n, pmk, dep, c, gg, cand, m, dup, t, h3,
                ab, lb, v, plb, pex, pg, Array.get(U32, a5, idx))
        case 42:
          # !has_size_ge_3: lb = 2n + dup; a dup of 0 and lb < best breaks.
          (a2, _) = p
          +lmk2 = U32.max(lmk, t)
          +lbA = U32.add(U32.mul(2, n), dup)
          +takeA = A.lt01(lbA, best)
          +v2b = A.sel(U32.mul(takeA, A.ge01(t, v2)), t, v2)
          +ngsb = U32.add(ngs, takeA)
          +bestA = A.sel(takeA, lbA, best)
          +mvA = U32.min(mv, lbA)
          +stop = U32.max(U32.mul(takeA, A.eq01(dup, 0)),
                          A.ge01(mkn2(bestA, lmk2, n), U32.inc(n)))
          p2_go(f, A.sel(stop, 44, 40), ci, g, bestA, lmk2, v2b, mvA, nt, ngsb,
                npr, gen, cm, mu, ss, n, pmk, dep, c, gg, cand, m, dup, t, h3,
                ab, lb, exp, plb, pex, pg, Array.get(U32, a2, 0))
        case 43:
          # has a size-3 bucket and the cheap min_lb test holds; lmk counts.
          (a2, _) = p
          +lmk2 = U32.max(lmk, t)
          +stop = A.ge01(mkn2(best, lmk2, n), U32.inc(n))
          p2_go(f, A.sel(stop, 44, 40), ci, g, best, lmk2, v2, mv, nt, ngs, npr,
                gen, cm, mu, ss, n, pmk, dep, c, gg, cand, m, dup, t, h3, ab,
                lb, exp, plb, pex, pg, Array.get(U32, a2, 0))
        case 40:
          # advance to g+1 (p is unused here; read its mark next round).
          (a2, _) = p
          +g2 = U32.inc(g)
          +sbase = U32.add(G.off_sset(c, gg), U32.mul(dep, gg))
          +done2 = A.ge01(g2, gg)
          +idx = A.sel(done2, 0, U32.add(sbase, g2))
          p2_go(f, A.sel(done2, 44, 30), ci, g2, best, lmk, v2, mv, nt, ngs, npr,
                gen, cm, mu, ss, n, pmk, dep, c, gg, cand, m, dup, t, h3, ab,
                lb, exp, plb, pex, pg, Array.get(U32, a2, idx))
        case 44:
          (a2, _) = p
          a3 = Array.set(U32, a2, qc(c, gg, 700), best)
          a4 = Array.set(U32, a3, qc(c, gg, 701), lmk)
          a5 = Array.set(U32, a4, qc(c, gg, 702), v2)
          a6 = Array.set(U32, a5, qc(c, gg, 703), mv)
          a7 = Array.set(U32, a6, qc(c, gg, 704), nt)
          a8 = Array.set(U32, a7, qc(c, gg, 705), ngs)
          a9 = Array.set(U32, a8, qc(c, gg, 706), npr)
          Array.set(U32, a9, qc(c, gg, 707), gen)

        case _:
          (a2, _) = p
          a3 = Array.set(U32, a2, qc(c, gg, 700), best)
          a4 = Array.set(U32, a3, qc(c, gg, 701), lmk)
          a5 = Array.set(U32, a4, qc(c, gg, 702), v2)
          a6 = Array.set(U32, a5, qc(c, gg, 703), mv)
          a7 = Array.set(U32, a6, qc(c, gg, 704), nt)
          a8 = Array.set(U32, a7, qc(c, gg, 705), ngs)
          a9 = Array.set(U32, a8, qc(c, gg, 706), npr)
          Array.set(U32, a9, qc(c, gg, 707), gen)

def p2_scan(a: Array<U32>, +ss: U32, +n: U32, +beta: U32, +pmk: U32,
            +dep: U32, +gen: U32, +c: U32, +gg: U32) -> Array<U32>:
  +fuel = Nat.add(Nat.mul(U32.to_nat(gg), 64n), 64n)
  p2_go(fuel, 20, 0, 0, beta, 0, 0, 4294967295, 0, 0, 0, gen, 0, 0, ss, n,
        pmk, dep, c, gg, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        Array.get(U32, a, ss))
