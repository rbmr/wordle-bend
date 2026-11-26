# Per-bucket evaluation in the guess pass, Rust's EvalEntry loop
# (min_guess_val_inner, c_len <= 16 body): the bucket's set hash, the
# transposition lookup, the small-set (quick) eval on a miss, and the insert.
#
# One self-recursive machine. Phases:
#   0..3   hash walk over the bucket: h1/h2 = xor of the two Zobrist words
#   10     write the child's hash cells (read by the child state at entry),
#          compute the table base, read slot 1 key1
#   4..9   two-slot lookup (slot 1 first)
#   12/15  miss: buckets up to 15 run the quick eval, larger ones keep the cap
#   16/17  quick, then used = max(quick, cap)
#   20..30 insert with Rust's GlobalCache::insert policy
#   14     done: result cells hold used and the exactness bit
#
# The result cells are read straight after the call by the engine.
import Base
import ./geo.bend as G
import ./arith.bend as A
import ./heur.bend as H
import ./big.bend as Bg
import ./ttw.bend as W

def res_used(+c: U32, +gg: U32) -> U32:
  U32.add(G.off_qgen(c, gg), 717)

def res_ex(+c: U32, +gg: U32) -> U32:
  U32.add(G.off_qgen(c, gg), 718)

def res_out(+c: U32, +gg: U32) -> U32:
  U32.add(G.off_qgen(c, gg), 719)

# Scratch cells a skipped write is redirected to (never read). Four of them:
# key word 1, key word 2, the packed value and the witness word.
def res_sc(+c: U32, +gg: U32) -> U32:
  U32.add(G.off_qgen(c, gg), 621)

def res_ck(+c: U32, +gg: U32) -> U32:
  U32.add(G.off_qgen(c, gg), 729)

def cmk1(+dep: U32, +c: U32, +gg: U32) -> U32:
  U32.add(G.off_cmk(c, gg), U32.mul(dep, 1024))

def pack_ex(+v: U32, +ex: U32, +n: U32) -> U32:
  U32.add(U32.add(U32.and(v, 262143), U32.mul(ex, 262144)), U32.shln(n, 19n))

# 1 when the entry may be replaced by (v, nex), matching Rust's same-state
# rules: an old exact entry is never replaced by a bound, and a tighter old
# bound is kept.
def upd2(+oex: U32, +old: U32, +v: U32, +nex: U32) -> U32:
  +nlb = U32.sub(1, nex)
  U32.sub(U32.sub(1, U32.mul(oex, nlb)), U32.mul(nlb, A.lt01(v, old)))

def ttmaskb() -> U32:
  U32.sub(G.ttb(), 1)

def ev(+fuel: Nat, +ph: U32, +j: U32, +o: U32, +k: U32, +cv: U32,
       +pmk: U32, +pn: U32, +h1: U32, +h2: U32, +k1: U32, +k2h: U32, +base: U32,
       +used: U32, +ex: U32, +dep: U32, +c: U32, +gg: U32, +cand: U32,
       +val: U32, p: Array<U32> & U32) -> Array<U32>:
  match fuel:
    case 0n:
      (a2, _) = p
      a2
    case 1n+f:
      match ph:
        case 0:
          (a2, _) = p
          ev(f, 1, j, o, k, cv, pmk, pn, h1, h2, k1, k2h, base, used, ex, dep, c, gg,
             cand, val, Array.get(U32, a2, U32.add(o, j)))
        case 1:
          (a2, +v) = p
          ev(f, 2, j, o, k, cv, pmk, pn, h1, h2, k1, k2h, base, used, ex, dep, c, gg,
             v, val, Array.get(U32, a2, U32.add(G.off_z1(c, gg), v)))
        case 2:
          (a2, +z) = p
          ev(f, 3, j, o, k, cv, pmk, pn, U32.xor(h1, z), h2, k1, k2h, base, used, ex,
             dep, c, gg, cand, val,
             Array.get(U32, a2, U32.add(G.off_z2(c, gg), cand)))
        case 3:
          (a2, +z) = p
          +h2b = U32.xor(h2, z)
          +j2 = U32.inc(j)
          +more = A.lt01(j2, k)
          +idx = A.sel(more, U32.add(o, j2), 0)
          ev(f, A.sel(more, 1, 10), j2, o, k, cv, pmk, pn, h1, h2b, k1, k2h, base,
             used, ex, dep, c, gg, cand, val, Array.get(U32, a2, idx))
        case 10:
          (a2, _) = p
          +k1b = U32.or(h1, 1)
          +base0 = U32.add(G.off_tt(c, gg),
                           U32.mul(U32.and(k1b, ttmaskb()), 8))
          +cm1 = cmk1(dep, c, gg)
          a3 = Array.set(U32, a2, cm1, h1)
          a4 = Array.set(U32, a3, U32.inc(cm1), h2)
          ev(f, 4, j, o, k, cv, pmk, pn, h1, h2, k1b, h2, base0, used, ex, dep, c,
             gg, cand, val, Array.get(U32, a4, U32.add(base0, 4)))
        case 4:
          (a2, +v) = p
          +hit = A.eq01(v, k1)
          ev(f, A.sel(hit, 5, 7), j, o, k, cv, pmk, pn, h1, h2, k1, k2h, base, used,
             ex, dep, c, gg, cand, val,
             Array.get(U32, a2, A.sel(hit, U32.add(base, 5), base)))
        case 5:
          (a2, +v) = p
          +hit = A.eq01(v, k2h)
          ev(f, A.sel(hit, 6, 7), j, o, k, cv, pmk, pn, h1, h2, k1, k2h, base, used,
             ex, dep, c, gg, cand, val,
             Array.get(U32, a2, A.sel(hit, U32.add(base, 6), base)))
        case 6:
          # Key matched: the value counts only if the stored set is this set.
          (a2, +v) = p
          ev(f, 34, j, o, k, cv, pmk, pn, h1, h2, k1, k2h, base, used, U32.and(U32.shrn(v, 18n), 1), dep, c,
             gg, cand, v, Array.get(U32, a2, U32.add(base, 7)))
        case 34:
          # The stored set size must match and there must be a witness copy;
          # `h1` is free here, so it carries the witness word into 38.
          (a2, +w) = p
          +okw = U32.mul(A.eq01(U32.shrn(val, 19n), k), A.nz(w))
          ev(f, A.sel(okw, 38, 12), j, o, k, cv, pmk, pn, w, h2, k1, k2h, base,
             used, ex, dep, c, gg, cand, val, Array.get(U32, a2, 0))
        case 38:
          (a2, _) = p
          a3 = W.wcmp(a2, o, U32.sub(U32.add(G.off_wit(c, gg), h1), 1), k, c, gg)
          ev(f, 35, j, o, k, cv, pmk, pn, h1, h2, k1, k2h, base, used, ex, dep, c,
             gg, cand, val, Array.get(U32, a3, W.wflagcell(c, gg)))
        case 35:
          # wflagcell is 1 only when every candidate of the set matches.
          (a2, +f2) = p
          ev(f, A.sel(f2, 37, 12), j, o, k, cv, pmk, pn, h1, h2, k1, k2h, base, used,
             ex, dep, c, gg, cand, val, Array.get(U32, a2, 0))
        case 37:
          (a2, _) = p
          +val0 = U32.and(val, 262143)
          +ex0 = U32.and(U32.shrn(val, 18n), 1)
          +used0 = U32.max(val0, cv)
          +ck = U32.max(U32.min(k, pmk), 2)
          a3 = Array.set(U32, a2, res_used(c, gg), used0)
          a4 = Array.set(U32, a3, res_ck(c, gg), ck)
          a5 = Array.set(U32, a4, res_ex(c, gg), U32.add(ex0, U32.mul(ck, 2)))
          ev(f, 14, j, o, k, cv, pmk, pn, h1, h2, k1, k2h, base, used0, ex0, dep, c,
             gg, cand, val, Array.get(U32, a5, 0))
        case 7:
          (a2, +v) = p
          +hit = A.eq01(v, k1)
          ev(f, A.sel(hit, 8, 12), j, o, k, cv, pmk, pn, h1, h2, k1, k2h, base, used,
             ex, dep, c, gg, cand, val,
             Array.get(U32, a2, A.sel(hit, U32.add(base, 1), base)))
        case 8:
          (a2, +v) = p
          +hit = A.eq01(v, k2h)
          ev(f, A.sel(hit, 9, 12), j, o, k, cv, pmk, pn, h1, h2, k1, k2h, base, used,
             ex, dep, c, gg, cand, val,
             Array.get(U32, a2, A.sel(hit, U32.add(base, 2), base)))
        case 9:
          (a2, +v) = p
          ev(f, 34, j, o, k, cv, pmk, pn, h1, h2, k1, k2h, base, used, U32.and(U32.shrn(v, 18n), 1), dep, c,
             gg, cand, v, Array.get(U32, a2, U32.add(base, 3)))
        case 12:
          (a2, _) = p
          ev(f, A.sel(A.ge01(15, k), 16, 15), j, o, k, cv, pmk, pn, h1, h2, k1, k2h,
             base, used, ex, dep, c, gg, cand, val, Array.get(U32, a2, 0))
        case 15:
          # Larger than 15: the branching-factor bound chain, then insert.
          (a2, _) = p
          a3 = Bg.eval(a2, o, k, cv, pmk, dep, c, gg)
          ev(f, 18, j, o, k, cv, pmk, pn, h1, h2, k1, k2h, base, cv, 0, dep, c,
             gg, cand, val, Array.get(U32, a3, res_used(c, gg)))
        case 18:
          (a2, +v) = p
          ev(f, 19, j, o, k, cv, pmk, pn, h1, h2, k1, k2h, base, v, 0, dep, c, gg,
             cand, val, Array.get(U32, a2, res_ck(c, gg)))
        case 19:
          (a2, +ck) = p
          a3 = Array.set(U32, a2, res_ex(c, gg), U32.mul(ck, 2))
          ev(f, 20, j, o, k, cv, pmk, pn, h1, h2, k1, k2h, base, used, 0, dep, c,
             gg, cand, val, Array.get(U32, a3, 0))
        case 16:
          (a2, _) = p
          a3 = H.quick_at(a2, o, k, c, gg, res_out(c, gg))
          ev(f, 17, j, o, k, cv, pmk, pn, h1, h2, k1, k2h, base, used, ex, dep, c, gg,
             cand, val, Array.get(U32, a3, res_out(c, gg)))
        case 17:
          (a2, +pk) = p
          +ex0 = U32.and(pk, 1)
          +used0 = U32.max(U32.shrn(pk, 1n), cv)
          +ck = U32.max(U32.min(k, pmk), 2)
          a3 = Array.set(U32, a2, res_used(c, gg), used0)
          a4 = Array.set(U32, a3, res_ck(c, gg), ck)
          a5 = Array.set(U32, a4, res_ex(c, gg), U32.add(ex0, U32.mul(ck, 2)))
          ev(f, 20, j, o, k, cv, pmk, pn, h1, h2, k1, k2h, base, used0, ex0, dep, c,
             gg, cand, val, Array.get(U32, a5, 0))
        # ------------------------------------------------ insert ------
        case 20:
          (a2, _) = p
          ev(f, 21, j, o, k, cv, pmk, pn, h1, h2, k1, k2h, base, used, ex, dep, c, gg,
             cand, val, Array.get(U32, a2, U32.add(base, 4)))
        case 21:
          (a2, +v) = p
          +same = A.eq01(v, k1)
          ev(f, A.sel(same, 22, 24), j, o, k, cv, pmk, pn, h1, h2, k1, k2h, base, used,
             ex, dep, c, gg, cand, val,
             Array.get(U32, a2, U32.add(base, A.sel(same, 5, 6))))
        case 22:
          (a2, +v) = p
          +same = A.eq01(v, k2h)
          ev(f, A.sel(same, 23, 24), j, o, k, cv, pmk, pn, h1, h2, k1, k2h, base,
             used, ex, dep, c, gg, cand, val,
             Array.get(U32, a2, U32.add(base, 6)))
        case 23:
          (a2, +v) = p
          +old = U32.and(v, 262143)
          +oex = U32.and(U32.shrn(v, 18n), 1)
          +upd = upd2(oex, old, used, ex)
          ev(f, A.sel(upd, 39, 14), j, o, k, cv, pmk, pn, h1, h2, k1, k2h, base,
             used, ex, dep, c, gg, cand, val, Array.get(U32, a2, 0))
        case 39:
          (a2, _) = p
          a3 = W.wcopy(a2, o, k, c, gg)
          ev(f, 42, j, o, k, cv, pmk, pn, h1, h2, k1, k2h, base, used, ex, dep, c,
             gg, cand, val, Array.get(U32, a3, W.wrescell(c, gg)))
        case 42:
          (a2, +wo) = p
          +sc = res_sc(c, gg)
          a3 = Array.set(U32, a2, U32.add(base, 4), k1)
          a4 = Array.set(U32, a3, U32.add(base, 5), k2h)
          a5 = Array.set(U32, a4, U32.add(base, 6), pack_ex(used, ex, k))
          a6 = Array.set(U32, a5, U32.add(base, 7), wo)
          ev(f, 14, j, o, k, cv, pmk, pn, h1, h2, k1, k2h, base, used, ex, dep, c, gg,
             cand, val, Array.get(U32, a6, 0))
        case 24:
          (a2, +v) = p
          +old = U32.and(v, 262143)
          +rep = A.ge01(used, old)
          +nb = A.sel(rep, 4, 0)
          ev(f, A.sel(rep, 30, 25), j, o, k, cv, pmk, pn, h1, h2, k1, k2h, base, used,
             ex, dep, c, gg, nb, val,
             Array.get(U32, a2, U32.add(base, A.sel(rep, 4, 0))))
        case 25:
          (a2, +v) = p
          +same = A.eq01(v, k1)
          ev(f, A.sel(same, 26, 30), j, o, k, cv, pmk, pn, h1, h2, k1, k2h, base, used,
             ex, dep, c, gg, cand, val,
             Array.get(U32, a2, U32.add(base, A.sel(same, 1, 0))))
        case 26:
          (a2, +v) = p
          +same = A.eq01(v, k2h)
          ev(f, A.sel(same, 27, 30), j, o, k, cv, pmk, pn, h1, h2, k1, k2h, base, used,
             ex, dep, c, gg, cand, val,
             Array.get(U32, a2, U32.add(base, A.sel(same, 2, 0))))
        case 27:
          (a2, +v) = p
          +old = U32.and(v, 262143)
          +oex = U32.and(U32.shrn(v, 18n), 1)
          +upd = upd2(oex, old, used, ex)
          ev(f, A.sel(upd, 40, 14), j, o, k, cv, pmk, pn, h1, h2, k1, k2h, base,
             used, ex, dep, c, gg, cand, val, Array.get(U32, a2, 0))
        case 40:
          (a2, _) = p
          a3 = W.wcopy(a2, o, k, c, gg)
          ev(f, 43, j, o, k, cv, pmk, pn, h1, h2, k1, k2h, base, used, ex, dep, c,
             gg, cand, val, Array.get(U32, a3, W.wrescell(c, gg)))
        case 43:
          (a2, +wo) = p
          a3 = Array.set(U32, a2, base, k1)
          a4 = Array.set(U32, a3, U32.add(base, 1), k2h)
          a5 = Array.set(U32, a4, U32.add(base, 2), pack_ex(used, ex, k))
          a6 = Array.set(U32, a5, U32.add(base, 3), wo)
          ev(f, 14, j, o, k, cv, pmk, pn, h1, h2, k1, k2h, base, used, ex, dep, c, gg,
             cand, val, Array.get(U32, a6, 0))
        case 30:
          (a2, _) = p
          ev(f, 41, j, o, k, cv, pmk, pn, h1, h2, k1, k2h, base, used, ex, dep, c, gg,
             cand, val, Array.get(U32, a2, 0))
        case 41:
          (a2, _) = p
          a3 = W.wcopy(a2, o, k, c, gg)
          ev(f, 44, j, o, k, cv, pmk, pn, h1, h2, k1, k2h, base, used, ex, dep, c,
             gg, cand, val, Array.get(U32, a3, W.wrescell(c, gg)))
        case 44:
          (a2, +wo) = p
          a3 = Array.set(U32, a2, U32.add(base, cand), k1)
          a4 = Array.set(U32, a3, U32.add(U32.add(base, cand), 1), k2h)
          a5 = Array.set(U32, a4, U32.add(U32.add(base, cand), 2),
                         pack_ex(used, ex, k))
          a6 = Array.set(U32, a5, U32.add(U32.add(base, cand), 3), wo)
          ev(f, 14, j, o, k, cv, pmk, pn, h1, h2, k1, k2h, base, used, ex, dep, c, gg,
             cand, val, Array.get(U32, a6, 0))
        case 14:
          (a2, _) = p
          a2
        case _:
          (a2, _) = p
          a2

def eval(a: Array<U32>, +o: U32, +k: U32, +cv: U32, +pmk: U32, +pn: U32,
         +dep: U32, +c: U32, +gg: U32) -> Array<U32>:
  +fuel = Nat.add(Nat.mul(U32.to_nat(k), 8n), 160n)
  ev(fuel, 0, 0, o, k, cv, pmk, pn, 0, 0, 0, 0, 0, cv, 0, dep, c, gg, 0, 0,
     Array.get(U32, a, o))
