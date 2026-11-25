# heuristic::compute_branching_factor_upper_bound over a candidate set:
# an instant information-theoretic upper bound on the branching factor any
# guess can achieve on that set, from the per-letter profiles only.
#
# ph 0 set[o+j] -> 1 cmask[cand] -> 2 cdup[cand] -> 3..8 cat[cand*5+i]
# ph 9 next candidate / finish.  ph 10 product and result cell.
#
# Rust's `if m != u32::MAX` guard around the profile update is dropped: m is the
# letter mask of a five-letter word, so it has five bits set and is never all
# ones.
import Base
import ./geo.bend as G
import ./arith.bend as A

def kcell(+c: U32, +gg: U32) -> U32:
  U32.add(G.off_qgen(c, gg), 727)

def maxu() -> U32:
  4294967295

# (a & (a - 1)) == 0 means a has at most one bit: b_r = !a, else all ones.
def brmask(+a: U32) -> U32:
  +isp = A.eq01(U32.and(a, U32.sub(a, 1)), 0)
  A.sel(isp, U32.xor(a, maxu()), maxu())

def fct(+a: U32, +e: U32, +du: U32, +bu: U32, +cd: U32) -> U32:
  +br = brmask(a)
  +b1 = U32.and(br, U32.or(bu, cd))
  +ae = U32.and(a, e)
  +aoe = U32.or(a, e)
  +aed = U32.and(a, du)
  +aoed = U32.or(a, du)
  +eq3 = U32.or(U32.or(U32.and(ae, bu), U32.and(ae, b1)), U32.and(aed, br))
  +ge2 = U32.or(U32.or(U32.or(ae, U32.and(aoe, bu)),
                       U32.or(ae, U32.and(aoe, b1))),
                U32.or(aed, U32.and(aoed, br)))
  A.sel(A.nz(eq3), 3, A.sel(A.nz(ge2), 2, 1))

def kup(+fuel: Nat, +ph: U32, +j: U32, +o: U32, +k: U32, +cand: U32, +m: U32,
        +dup: U32, +cm: U32, +ca: U32, +cd: U32, +a0: U32, +a1: U32,
        +a2: U32, +a3: U32, +a4: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32,
        +e4: U32, +d0: U32, +d1: U32, +d2: U32, +d3: U32, +d4: U32,
        +c: U32, +gg: U32, p: Array<U32> & U32) -> Array<U32>:
  match fuel:
    case 0n:
      (a2p, _) = p
      a2p
    case 1n+f:
      match ph:
        case 0:
          (a2p, _) = p
          kup(f, 1, j, o, k, cand, m, dup, cm, ca, cd, a0, a1, a2, a3, a4,
              e0, e1, e2, e3, e4, d0, d1, d2, d3, d4, c, gg,
              Array.get(U32, a2p, U32.add(o, j)))
        case 1:
          (a2p, +v) = p
          kup(f, 2, j, o, k, v, m, dup, cm, ca, cd, a0, a1, a2, a3, a4,
              e0, e1, e2, e3, e4, d0, d1, d2, d3, d4, c, gg,
              Array.get(U32, a2p, U32.add(G.off_cmask(c, gg), v)))
        case 2:
          (a2p, +v) = p
          kup(f, 3, j, o, k, cand, v, dup, U32.or(cm, v), U32.and(ca, v), cd,
              a0, a1, a2, a3, a4, e0, e1, e2, e3, e4, d0, d1, d2, d3, d4,
              c, gg, Array.get(U32, a2p, U32.add(G.off_cdup(c, gg), cand)))
        case 3:
          (a2p, +v) = p
          +oa = U32.add(G.off_cat(c, gg), U32.mul(5, cand))
          kup(f, 4, j, o, k, cand, m, v, cm, ca, U32.or(cd, v), a0, a1, a2,
              a3, a4, e0, e1, e2, e3, e4, d0, d1, d2, d3, d4, c, gg,
              Array.get(U32, a2p, oa))
        case 4:
          (a2p, +v) = p
          +oa = U32.add(G.off_cat(c, gg), U32.mul(5, cand))
          kup(f, 5, j, o, k, cand, m, dup, cm, ca, cd,
              U32.or(a0, v), a1, a2, a3, a4,
              U32.or(e0, U32.and(m, U32.xor(v, maxu()))),
              e1, e2, e3, e4,
              U32.or(d0, U32.and(dup, U32.xor(v, maxu()))),
              d1, d2, d3, d4, c, gg, Array.get(U32, a2p, U32.add(oa, 1)))
        case 5:
          (a2p, +v) = p
          +oa = U32.add(G.off_cat(c, gg), U32.mul(5, cand))
          kup(f, 6, j, o, k, cand, m, dup, cm, ca, cd, a0,
              U32.or(a1, v), a2, a3, a4, e0,
              U32.or(e1, U32.and(m, U32.xor(v, maxu()))), e2, e3, e4, d0,
              U32.or(d1, U32.and(dup, U32.xor(v, maxu()))), d2, d3, d4, c,
              gg, Array.get(U32, a2p, U32.add(oa, 2)))
        case 6:
          (a2p, +v) = p
          +oa = U32.add(G.off_cat(c, gg), U32.mul(5, cand))
          kup(f, 7, j, o, k, cand, m, dup, cm, ca, cd, a0, a1,
              U32.or(a2, v), a3, a4, e0, e1,
              U32.or(e2, U32.and(m, U32.xor(v, maxu()))), e3, e4, d0, d1,
              U32.or(d2, U32.and(dup, U32.xor(v, maxu()))), d3, d4, c, gg,
              Array.get(U32, a2p, U32.add(oa, 3)))
        case 7:
          (a2p, +v) = p
          +oa = U32.add(G.off_cat(c, gg), U32.mul(5, cand))
          kup(f, 8, j, o, k, cand, m, dup, cm, ca, cd, a0, a1, a2,
              U32.or(a3, v), a4, e0, e1, e2,
              U32.or(e3, U32.and(m, U32.xor(v, maxu()))), e4, d0, d1, d2,
              U32.or(d3, U32.and(dup, U32.xor(v, maxu()))), d4, c, gg,
              Array.get(U32, a2p, U32.add(oa, 4)))
        case 8:
          (a2p, +v) = p
          +j2 = U32.inc(j)
          +more = A.lt01(j2, k)
          +idx = A.sel(more, U32.add(o, j2), 0)
          kup(f, A.sel(more, 0, 9), j2, o, k, cand, m, dup, cm, ca, cd, a0,
              a1, a2, a3, U32.or(a4, v), e0, e1, e2, e3,
              U32.or(e4, U32.and(m, U32.xor(v, maxu()))), d0, d1, d2, d3,
              U32.or(d4, U32.and(dup, U32.xor(v, maxu()))), c, gg,
              Array.get(U32, a2p, idx))
        case 9:
          (a2p, _) = p
          +bu = U32.xor(ca, maxu())
          +p1 = fct(a0, e0, d0, bu, cd)
          +p2 = U32.mul(p1, fct(a1, e1, d1, bu, cd))
          +p3 = U32.mul(p2, fct(a2, e2, d2, bu, cd))
          +p4 = U32.mul(p3, fct(a3, e3, d3, bu, cd))
          +p5 = U32.mul(p4, fct(a4, e4, d4, bu, cd))
          +res = U32.min(U32.min(p5, k), 242)
          a3p = Array.set(U32, a2p, kcell(c, gg), res)
          kup(f, 11, j, o, k, cand, m, dup, cm, ca, cd, a0, a1, a2, a3, a4,
              e0, e1, e2, e3, e4, d0, d1, d2, d3, d4, c, gg,
              Array.get(U32, a3p, 0))
        case 11:
          (a2p, _) = p
          a2p
        case _:
          (a2p, _) = p
          a2p

# Rust returns n.min(num_responses) when the union of the letter masks is all
# ones; that cannot happen for five-letter words (the union has at most 26 bits
# and Rust's check is `c_mask == u32::MAX`, i.e. all 32), so the shortcut is
# unreachable here. It is kept in the product form: the product is min'ed with
# n and 242, which is what that branch returns.
def k_upper(a: Array<U32>, +o: U32, +k: U32, +c: U32, +gg: U32) -> Array<U32>:
  +fuel = Nat.add(Nat.mul(U32.to_nat(k), 12n), 64n)
  kup(fuel, 0, 0, o, k, 0, 0, 0, 0, maxu(), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, c, gg, Array.get(U32, a, o))
