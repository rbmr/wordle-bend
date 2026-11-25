# Capacity table, greedy upper bound, small-set (quick) evaluation.
#
# Every array read is one call, so each loop here is one phase machine that
# receives the read pair as its last argument and issues the next read as its
# own recursive argument.
import Base
import ./geo.bend as G
import ./arith.bend as A
import ./bounds.bend as B
import ./tab.bend as T

# ------------------------------------------------------------ capacity table ---
#
# cap2d[k][n] = capacity_bound(n, k), for k = 2..maxk and n = 0..c. Writes only.
def cap_n(+fuel: Nat, +k: U32, +n: U32, +maxk: U32, +c: U32, +gg: U32,
          a: Array<U32>) -> Array<U32>:
  match fuel:
    case 0n:
      a
    case 1n+p:
      +v = U32.from_nat(B.capacity_bound(U32.to_nat(n), U32.to_nat(k)))
      +base = U32.add(G.off_cap(c, gg), U32.mul(k, U32.inc(c)))
      a[U32.add(base, n)] <- v
      +nd = A.eq01(n, c)
      +k2 = A.sel(nd, U32.inc(k), k)
      cap_n(p, A.sel(A.eq01(k2, U32.inc(maxk)), k, k2),
            A.sel(nd, 0, U32.inc(n)), maxk, c, gg, a)

def cap_fill(+maxk: U32, +c: U32, +gg: U32, a: Array<U32>) -> Array<U32>:
  +rows = Nat.sub(U32.to_nat(U32.max(maxk, 2)), 1n)
  cap_n(Nat.mul(rows, U32.to_nat(U32.inc(c))), 2, 0, maxk, c, gg, a)

# --------------------------------------------------------------- quick eval ---
#
# Exact for at most 15 candidates: take each in-set guess in turn and count how
# many of its responses to the bucket collide. No collision gives 2n-1 (every
# non-win bucket a singleton), exactly one gives 2n; the lowest value over the
# in-set guesses is exact when some guess has at most one collision. Packed as
# 2*value + exact.
#
# Count cells are generation stamped (cell = gen*256 + count), so a stale cell
# reads as 0 without a reset pass.
#
# Phase 3: v = set[sb+i] for a new guess.  4: v = its guess index.
# Phase 0: v = set[sb+m].  1: v = its feedback.  2: v = its count cell.
# Phase 5: stop.
def qcount(+cell: U32, +genb: U32) -> U32:
  +diff = U32.sub(cell, genb)
  +fresh = U32.sub(1, U32.div(diff, 2147483648))
  U32.mul(diff, fresh)

def qresult(+a0: U32, +a1: U32, +n: U32) -> U32:
  +val = A.sel(a0, U32.sub(U32.mul(2, n), 1), U32.mul(2, n))
  U32.add(U32.mul(2, val), U32.max(a0, a1))

def quick(+fuel: Nat, +ph: U32, +i: U32, +m: U32, +si: U32, +coll: U32,
          +a0: U32, +a1: U32, +genb: U32, +row: U32, +sb: U32, +n: U32,
          +c: U32, +gg: U32, r: Array<U32> & U32) -> U32:
  match fuel:
    case 0n:
      (a2, _) = r
      qresult(a0, a1, n)
    case 1n+p:
      match ph:
        case 3:
          (a2, +x) = r
          quick(p, 4, i, 0, x, 0, a0, a1, genb, row, sb, n, c, gg,
                Array.get(U32, a2, U32.add(G.off_c2g(c, gg), x)))
        case 4:
          (a2, +x) = r
          quick(p, 0, i, 0, 0, 0, a0, a1, genb, U32.mul(x, c), sb, n, c, gg,
                Array.get(U32, a2, U32.add(sb, 0)))
        case 0:
          (a2, +x) = r
          quick(p, 1, i, m, x, coll, a0, a1, genb, row, sb, n, c, gg,
                Array.get(U32, a2, U32.add(row, x)))
        case 1:
          (a2, +x) = r
          quick(p, 2, i, m, x, coll, a0, a1, genb, row, sb, n, c, gg,
                Array.get(U32, a2, U32.add(G.off_qcnt(c, gg), x)))

        case 2:
          (a2, +x) = r
          +cnt = qcount(x, genb)
          a3 = Array.set(U32, a2, U32.add(G.off_qcnt(c, gg), si),
                         U32.add(genb, U32.inc(cnt)))
          +coll2 = U32.add(coll, A.nz(cnt))
          +m2 = U32.inc(m)
          +gend = A.eq01(m2, n)
          +a0b = U32.add(a0, U32.mul(U32.sub(1, a0), A.eq01(coll2, 0)))
          +a1b = U32.add(a1, U32.mul(U32.sub(1, a1), A.eq01(coll2, 1)))
          +i2 = U32.add(i, gend)
          +stop = U32.mul(gend, U32.max(a0b, A.eq01(i2, n)))
          +nxt = A.sel(stop, 0, A.sel(gend, U32.add(sb, i2),
                                      U32.add(sb, m2)))
          quick(p, A.sel(stop, 5, A.sel(gend, 3, 0)), i2,
                A.sel(gend, 0, m2), si, A.sel(gend, 0, coll2), a0b, a1b,
                U32.add(genb, U32.mul(gend, 256)), row, sb, n, c, gg,
                Array.get(U32, a3, nxt))
        case _:
          (a2, _) = r
          qresult(a0, a1, n)

# ------------------------------------------------------------- test helpers ---
def fill_set(+fuel: Nat, +i: U32, +n: U32, +k: U32, +base: U32,
             a: Array<U32>) -> Array<U32>:
  match fuel:
    case 0n:
      a
    case 1n+p:
      a[U32.add(base, i)] <- U32.add(k, i)
      fill_set(p, U32.inc(i), n, k, base, a)

# Quick-evaluate candidates k..k+n-1, which must be copied into the depth-0 set
# region first.
def run_quick(a: Array<U32>, +k: U32, +n: U32, +c: U32, +gg: U32) -> U32:
  +sb = G.off_sets(c, gg)
  +fuel = Nat.add(Nat.mul(U32.to_nat(n), Nat.mul(U32.to_nat(n), 8n)), 64n)
  a1 = fill_set(U32.to_nat(n), 0, n, k, sb, a)
  quick(fuel, 3, 0, 0, 0, 0, 0, 0, 0, 0, sb, n, c, gg,
        Array.get(U32, a1, sb))
