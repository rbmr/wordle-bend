# Rust's c_len > 16 bucket path for one bucket: the branching-factor bound
# chain (heuristic::min_k_for_target_bound, k_cand, k_max_seq, k_upper,
# bucket_capacity_bound). Used values:
#   lb = cap[parent_max_k][p_len]
#   target_k = min_k_for_target_bound(p_len, parent_max_k, lb)
#   ku = k_upper(bucket)
#   kc = k_cand(bucket, min(target_k, ku))
#   if kc >= target_k        -> used = lb            (no improvement possible)
#   elif kc >= ku            -> k = ku
#   else                     -> k = k_max_seq(bucket, kc, min(target_k, ku))
#        and then k >= target_k -> used = lb, else k = that k
#   used = max(bucket_capacity_bound(p_len, k, parent_max_k), lb)
# The child's max branching factor is max(min(k, p_len, parent_max_k), 2).
#
# Result cells (offsets inside off_qgen): 728 used, 729 child k.
import Base
import ./geo.bend as G
import ./arith.bend as A
import ./sec.bend as S
import ./bounds.bend as B
import ./kup.bend as K

# Scratch cell for the k_cand / k_max_seq result.
def uused(+c: U32, +gg: U32) -> U32:
  U32.add(G.off_qgen(c, gg), 728)

# Result cells, the same ones buck.bend reads: used, and the child max k.
def rused(+c: U32, +gg: U32) -> U32:
  U32.add(G.off_qgen(c, gg), 717)

def rck(+c: U32, +gg: U32) -> U32:
  U32.add(G.off_qgen(c, gg), 729)

def nosk() -> U32:
  4294967295

# ------------------------------------------------ k_cand ----------------------
#
# The largest number of distinct responses any candidate guess of the bucket
# has, with an early stop at `eff`. ph 0 head, 1 guess index, 2 count, 3 step,
# 9 write the max.
def kc_go(+fuel: Nat, +ph: U32, +i: U32, +o: U32, +k: U32, +mx: U32,
          +eff: U32, +dep: U32, +c: U32, +gg: U32, +g: U32,
          p: Array<U32> & U32) -> Array<U32>:
  match fuel:
    case 0n:
      (a2, _) = p
      a2
    case 1n+f:
      match ph:
        case 0:
          (a2, _) = p
          +stop = U32.max(A.ge01(i, k), A.ge01(mx, eff))
          +idx = A.sel(stop, 0, U32.add(o, i))
          kc_go(f, A.sel(stop, 9, 1), i, o, k, mx, eff, dep, c, gg, g,
                Array.get(U32, a2, idx))
        case 1:
          (a2, +v) = p
          +idx = U32.add(G.off_c2g(c, gg), v)
          kc_go(f, 2, i, o, k, mx, eff, dep, c, gg, v,
                Array.get(U32, a2, idx))
        case 2:
          (a2, _) = p
          a3 = S.cnt(g, o, k, nosk(), dep, c, gg, a2)
          kc_go(f, 3, i, o, k, mx, eff, dep, c, gg, g,
                Array.get(U32, a3, S.pkcell(c, gg)))
        case 3:
          (a2, +pk) = p
          +t = U32.and(pk, 4095)
          +mx2 = U32.max(mx, t)
          +i2 = U32.inc(i)
          +stop = U32.max(A.ge01(i2, k), A.ge01(mx2, eff))
          +idx = A.sel(stop, 0, U32.add(o, i2))
          kc_go(f, A.sel(stop, 9, 0), i2, o, k, mx2, eff, dep, c, gg, g,
                Array.get(U32, a2, idx))
        case 9:
          (a2, _) = p
          a3 = Array.set(U32, a2, uused(c, gg), mx)
          kc_go(f, 10, i, o, k, mx, eff, dep, c, gg, g,
                Array.get(U32, a3, 0))
        case 10:
          (a2, _) = p
          a2
        case _:
          (a2, _) = p
          a2

def kcand(a: Array<U32>, +o: U32, +k: U32, +eff: U32, +dep: U32, +c: U32,
          +gg: U32) -> Array<U32>:
  +fuel = Nat.add(Nat.mul(U32.to_nat(k), Nat.mul(U32.to_nat(k), 16n)), 512n)
  kc_go(fuel, 0, 0, o, k, 0, eff, dep, c, gg, 0,
        Array.get(U32, a, o))

# ------------------------------------------------ k_max_seq -------------------
#
# Walk every guess in index order, count its distinct responses on the bucket,
# keep the max, and stop at `eff` (min(target, k_upper)). ph 0 head, 1 guess
# index, 2 count, 3 step, 4 write.
def km_go(+fuel: Nat, +ph: U32, +g: U32, +o: U32, +k: U32, +mx: U32,
          +eff: U32, +dep: U32, +c: U32, +gg: U32,
          p: Array<U32> & U32) -> Array<U32>:
  match fuel:
    case 0n:
      (a2, _) = p
      a2
    case 1n+f:
      match ph:
        case 0:
          (a2, _) = p
          +stop = U32.max(A.ge01(g, gg), A.ge01(mx, eff))
          +idx = A.sel(stop, 0, g)
          km_go(f, A.sel(stop, 4, 1), g, o, k, mx, eff, dep, c, gg,
                Array.get(U32, a2, idx))
        case 1:
          # g is already the guess index; only the candidate loop maps through
          # c2g.
          (a2, _) = p
          +idx = U32.add(G.off_gmask(c, gg), g)
          km_go(f, 2, g, o, k, mx, eff, dep, c, gg,
                Array.get(U32, a2, idx))
        case 2:
          (a2, _) = p
          a3 = S.cnt(g, o, k, nosk(), dep, c, gg, a2)
          km_go(f, 3, g, o, k, mx, eff, dep, c, gg,
                Array.get(U32, a3, S.pkcell(c, gg)))
        case 3:
          (a2, +pk) = p
          +t = U32.and(pk, 4095)
          +mx2 = U32.max(mx, t)
          +g2 = U32.inc(g)
          +idx = A.sel(A.ge01(g2, gg), 0, U32.add(G.off_gmask(c, gg), g2))
          km_go(f, 0, g2, o, k, mx2, eff, dep, c, gg,
                Array.get(U32, a2, idx))
        case 4:
          (a2, _) = p
          a3 = Array.set(U32, a2, uused(c, gg), mx)
          km_go(f, 5, g, o, k, mx, eff, dep, c, gg,
                Array.get(U32, a3, 0))
        case 5:
          (a2, _) = p
          a2
        case _:
          (a2, _) = p
          a2

def kmax(a: Array<U32>, +o: U32, +k: U32, +init: U32, +eff: U32, +dep: U32,
         +c: U32, +gg: U32) -> Array<U32>:
  +fuel = Nat.add(Nat.mul(U32.to_nat(gg), 16n), 512n)
  km_go(fuel, 0, 0, o, k, init, eff, dep, c, gg, Array.get(U32, a, 0))

# ------------------------------------------------ orchestrator ----------------
#
# ph 0 k_upper, 1 target, 2 k_cand, 3 k_cand result, 4 k_max_seq,
# 5 k_max_seq result, 6 bucket_capacity_bound, 9/10 write.
def bg(+fuel: Nat, +ph: U32, +o: U32, +k: U32, +cv: U32, +pmk: U32,
       +dep: U32, +c: U32, +gg: U32, +ku: U32, +target: U32, +kc: U32,
       +used: U32, +ck: U32, p: Array<U32> & U32) -> Array<U32>:
  match fuel:
    case 0n:
      (a2, _) = p
      a2
    case 1n+f:
      match ph:
        case 0:
          (a2, _) = p
          a3 = K.k_upper(a2, o, k, c, gg)
          bg(f, 1, o, k, cv, pmk, dep, c, gg, ku, target, kc, used, ck,
             Array.get(U32, a3, K.kcell(c, gg)))
        case 1:
          (a2, +v) = p
          +tb = U32.from_nat(B.min_k_for_target_bound(U32.to_nat(k),
                                                     U32.to_nat(pmk),
                                                     U32.to_nat(cv)))
          +kp = U32.max(U32.min(k, pmk), 2)
          +small = A.ge01(2, tb)
          +ku0 = U32.max(v, 2)
          +used0 = A.sel(small, cv, 0)
          +ck0 = A.sel(small, kp, 0)
          bg(f, A.sel(small, 9, 2), o, k, cv, pmk, dep, c, gg, ku0, tb, 0,
             used0, ck0, Array.get(U32, a2, 0))
        case 2:
          (a2, _) = p
          a3 = kcand(a2, o, k, U32.min(target, ku), U32.sub(dep, 1), c, gg)
          bg(f, 3, o, k, cv, pmk, dep, c, gg, ku, target, kc, used, ck,
             Array.get(U32, a3, uused(c, gg)))
        case 3:
          (a2, +v) = p
          +kp = U32.max(U32.min(k, pmk), 2)
          +gave = A.ge01(v, target)
          +kuge = A.ge01(v, ku)
          bg(f, A.sel(gave, 9, A.sel(kuge, 6, 4)), o, k, cv, pmk, dep, c,
             gg, ku, target, v, A.sel(gave, cv, 0), A.sel(gave, kp, 0),
             Array.get(U32, a2, 0))
        case 4:
          (a2, _) = p
          a3 = kmax(a2, o, k, kc, U32.min(target, ku), U32.sub(dep, 1), c, gg)
          bg(f, 5, o, k, cv, pmk, dep, c, gg, ku, target, kc, used, ck,
             Array.get(U32, a3, uused(c, gg)))
        case 5:
          (a2, +v) = p
          +kp = U32.max(U32.min(k, pmk), 2)
          +gave = A.ge01(v, target)
          bg(f, A.sel(gave, 9, 6), o, k, cv, pmk, dep, c, gg, ku, target,
             v, A.sel(gave, cv, 0), A.sel(gave, kp, 0),
             Array.get(U32, a2, 0))
        case 6:
          # used = max(bucket_capacity_bound(k, chosen k, pmk), cv), child k
          (a2, _) = p
          +ch = A.sel(A.ge01(kc, ku), ku, kc)
          +bcb = U32.from_nat(B.bucket_capacity_bound(U32.to_nat(k),
                                                      U32.to_nat(ch),
                                                      U32.to_nat(pmk)))
          +used0 = U32.max(bcb, cv)
          +ck0 = U32.max(U32.min(U32.min(ch, k), pmk), 2)
          bg(f, 9, o, k, cv, pmk, dep, c, gg, ku, target, kc, used0, ck0,
             Array.get(U32, a2, 0))
        case 9:
          (a2, _) = p
          a3 = Array.set(U32, a2, rused(c, gg), used)
          a4 = Array.set(U32, a3, rck(c, gg), ck)
          bg(f, 10, o, k, cv, pmk, dep, c, gg, ku, target, kc, used, ck,
             Array.get(U32, a4, 0))
        case 10:
          (a2, _) = p
          a2
        case _:
          (a2, _) = p
          a2

def eval(a: Array<U32>, +o: U32, +k: U32, +cv: U32, +pmk: U32, +dep: U32,
         +c: U32, +gg: U32) -> Array<U32>:
  bg(Nat.add(Nat.mul(U32.to_nat(gg), 16n), 1024n), 0, o, k, cv, pmk, dep, c,
     gg, 0, 0, 0, cv, 0, Array.get(U32, a, 0))
