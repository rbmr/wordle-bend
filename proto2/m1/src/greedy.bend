# Rust's `greedy_solve` (solver.rs:10228), transcribed over flat index ranges.
#
# At each node: scan every guess over the set, keep the one with the smallest
# sum of squared bucket sizes (Rust's expected_rem) among the guesses that split
# the set into more than one bucket, partition the set by that guess, then
# recurse into every non-win bucket. cost = n + sum(child costs); n <= 2 is
# n*(n+1)/2.
#
# Rust does the same recursion directly. Safe Bend forbids mutual recursion, so
# here the recursion is one self-recursive def with an explicit frame stack of
# (cost, response, depth) per pending bucket. Depth 0 reads the root set copied
# into the greedy arena; a node at depth d writes its partition into depth d+1.
#
# Per depth the arena holds: the set (c), counts (256), offsets (256), scatter
# cursors (256) and the touched-response list (256).
import Base
import ./geo.bend as G
import ./arith.bend as A
import ./sec.bend as S

def win() -> U32:
  121

def gdepths() -> U32:
  256

def gslot(+c: U32) -> U32:
  U32.add(c, 1280)

def gbase(+dep: U32, +c: U32, +gg: U32) -> U32:
  U32.add(G.off_greedy(c, gg), U32.mul(dep, gslot(c)))

def gset(+dep: U32, +c: U32, +gg: U32) -> U32:
  gbase(dep, c, gg)

def gcnt(+dep: U32, +c: U32, +gg: U32) -> U32:
  U32.add(gset(dep, c, gg), c)

def goff(+dep: U32, +c: U32, +gg: U32) -> U32:
  U32.add(gcnt(dep, c, gg), 256)

def gcur(+dep: U32, +c: U32, +gg: U32) -> U32:
  U32.add(goff(dep, c, gg), 257)

def gtou(+dep: U32, +c: U32, +gg: U32) -> U32:
  U32.add(gcur(dep, c, gg), 256)

# Result cell of one greedy_solve call (next to the engine's scratch cells).
def rescell(+c: U32, +gg: U32) -> U32:
  U32.add(G.off_qgen(c, gg), 617)

# The feedback response of guess `g` for candidate `v`: fb[g*c + v].
def fbat(+g: U32, +v: U32, +c: U32) -> U32:
  U32.add(U32.mul(g, c), v)

type GFr is Type:
  GF{cost: U32, r: U32, dep: U32}

# Phases:
#   0 enter, 1/2 clear counts, 3/4 guess header, 5/6/7 count pass,
#   8/9 best update + touched clear, 10 next guess,
#   20..23 recount with the best guess, 24/25 offsets + cursor reset,
#   27/28/29/35 scatter, 30..36 bucket loop, 90 deliver.
def gr(+fuel: Nat, +c: U32, +gg: U32, +ph: U32, +dep: U32, +ss: U32,
       +n: U32, +g: U32, +i: U32, +best: U32, +bg: U32, +exp: U32, +ne: U32,
       +tc: U32, +r: U32, +cost: U32, +off: U32, +ret: U32,
       stk: List<GFr>, p: Array<U32> & U32) -> Array<U32>:
  match fuel:
    case 0n:
      (a2, _) = p
      a2
    case 1n+f:
      match ph:
        case 0:
          (a2, _) = p
          +big = A.ge01(n, 3)
          gr(f, c, gg, A.sel(big, 1, 90), dep, ss, n, g, i, best, bg, exp, ne,
             tc, r, cost, off,
             A.sel(big, ret, U32.div(U32.mul(n, U32.inc(n)), 2)), stk,
             Array.get(U32, a2, 0))
        case 1:
          (a2, _) = p
          gr(f, c, gg, 2, dep, ss, n, g, 0, best, bg, 0, 0, 0, r, cost, off,
             ret, stk, Array.get(U32, a2, 0))
        case 2:
          (a2, _) = p
          +c2 = gcnt(dep, c, gg)
          a3 = Array.set(U32, a2, U32.add(c2, i), 0)
          +i2 = U32.inc(i)
          gr(f, c, gg, A.sel(A.lt01(i2, 256), 2, 3), dep, ss, n, g, i2, best,
             bg, exp, ne, tc, r, cost, off, ret, stk,
             Array.get(U32, a3, 0))
        case 3:
          (a2, _) = p
          gr(f, c, gg, 4, dep, ss, n, 0, 0, 2147483647, 0, 0, 0, 0, r, cost,
             off, ret, stk, Array.get(U32, a2, 0))
        case 4:
          (a2, _) = p
          +more = A.lt01(g, gg)
          gr(f, c, gg, A.sel(more, 5, 20), dep, ss, n, g, 0, best, bg, 0, 0, 0,
             r, cost, off, ret, stk, Array.get(U32, a2, ss))
        case 5:
          (a2, +v) = p
          +fi = fbat(g, v, c)
          gr(f, c, gg, 6, dep, ss, n, g, i, best, bg, exp, ne, tc,
             U32.and(fi, 3), cost, v,
             ret, stk, Array.get(U32, a2, U32.shrn(fi, 2n)))
        case 6:
          (a2, +w) = p
          +hi = U32.sub(1, U32.shrn(U32.sub(r, 2), 31n))
          +t1 = U32.add(w, U32.mul(hi, U32.sub(U32.shrn(w, 16n), w)))
          +t2 = U32.add(t1, U32.mul(U32.and(r, 1),
                                    U32.sub(U32.shrn(t1, 8n), t1)))
          +rv = U32.and(t2, 255)
          gr(f, c, gg, 7, dep, ss, n, g, i, best, bg, exp, ne, tc, 0, cost, rv,
             ret, stk, Array.get(U32, a2, U32.add(gcnt(dep, c, gg), rv)))
        case 7:
          (a2, +old) = p
          +new = A.eq01(old, 0)
          +c2 = gcnt(dep, c, gg)
          +t2 = gtou(dep, c, gg)
          a3 = Array.set(U32, a2, U32.add(c2, off), U32.add(old, 1))
          a4 = Array.set(U32, a3, U32.add(t2, A.sel(new, tc, 255)), off)
          +i2 = U32.inc(i)
          +more = A.lt01(i2, n)
          gr(f, c, gg, A.sel(more, 5, 8), dep, ss, n, g, i2, best, bg,
             U32.add(exp, U32.inc(U32.mul(2, old))), U32.add(ne, new),
             U32.add(tc, new), r, cost, off, ret, stk,
             Array.get(U32, a4, A.sel(more, U32.add(ss, i2), 0)))
        case 8:
          (a2, _) = p
          +ok = U32.mul(A.ge01(ne, 2), A.lt01(exp, best))
          gr(f, c, gg, 9, dep, ss, n, g, 0, A.sel(ok, exp, best),
             A.sel(ok, g, bg), exp, ne, tc, r, cost, off, ret, stk,
             Array.get(U32, a2, gtou(dep, c, gg)))
        case 9:
          (a2, +v) = p
          a3 = Array.set(U32, a2, U32.add(gcnt(dep, c, gg), v), 0)
          +i2 = U32.inc(i)
          gr(f, c, gg, A.sel(A.lt01(i2, tc), 9, 10), dep, ss, n, g, i2, best,
             bg, exp, ne, tc, r, cost, off, ret, stk,
             Array.get(U32, a3, U32.add(gtou(dep, c, gg),
                                        A.sel(A.lt01(i2, tc), i2, 255))))
        case 10:
          (a2, _) = p
          gr(f, c, gg, 4, dep, ss, n, U32.inc(g), i, best, bg, exp, ne, tc, r,
             cost, off, ret, stk, Array.get(U32, a2, 0))
        # ------------------------------------------ recount with the best ----
        case 20:
          (a2, _) = p
          gr(f, c, gg, 21, dep, ss, n, bg, 0, best, bg, 0, 0, 0, r, cost, off,
             ret, stk, Array.get(U32, a2, ss))
        case 21:
          (a2, +v) = p
          +fi = fbat(g, v, c)
          gr(f, c, gg, 22, dep, ss, n, g, i, best, bg, exp, ne, tc,
             U32.and(fi, 3), cost, v,
             ret, stk, Array.get(U32, a2, U32.shrn(fi, 2n)))
        case 22:
          (a2, +w) = p
          +hi = U32.sub(1, U32.shrn(U32.sub(r, 2), 31n))
          +t1 = U32.add(w, U32.mul(hi, U32.sub(U32.shrn(w, 16n), w)))
          +t2 = U32.add(t1, U32.mul(U32.and(r, 1),
                                    U32.sub(U32.shrn(t1, 8n), t1)))
          +rv = U32.and(t2, 255)
          gr(f, c, gg, 23, dep, ss, n, g, i, best, bg, exp, ne, tc, 0, cost, rv,
             ret, stk, Array.get(U32, a2, U32.add(gcnt(dep, c, gg), rv)))
        case 23:
          (a2, +old) = p
          a3 = Array.set(U32, a2, U32.add(gcnt(dep, c, gg), off),
                         U32.add(old, 1))
          +i2 = U32.inc(i)
          +more = A.lt01(i2, n)
          gr(f, c, gg, A.sel(more, 21, 24), dep, ss, n, g, i2, best,
             bg, exp, ne, tc, r, cost, off, ret, stk,
             Array.get(U32, a3, A.sel(more, U32.add(ss, i2), 0)))
        # ------------------------------------------------------ offsets ----
        case 24:
          (a2, _) = p
          gr(f, c, gg, 25, dep, ss, n, g, i, best, bg, exp, ne, tc, 0, cost, 0,
             ret, stk, Array.get(U32, a2, gcnt(dep, c, gg)))
        case 25:
          (a2, +v) = p
          a3 = Array.set(U32, a2, U32.add(goff(dep, c, gg), r), off)
          a4 = Array.set(U32, a3, U32.add(gcur(dep, c, gg), r), 0)
          +r2 = U32.inc(r)
          gr(f, c, gg, A.sel(A.lt01(r2, 256), 25, 26), dep, ss, n, g, i, best,
             bg, exp, ne, tc, r2, cost, U32.add(off, v), ret, stk,
             Array.get(U32, a4, U32.add(gcnt(dep, c, gg),
                                        A.sel(A.lt01(r2, 256), r2, 0))))
        # ------------------------------------------------------ scatter ----
        case 26:
          (a2, _) = p
          gr(f, c, gg, 27, dep, ss, n, g, 0, best, bg, exp, ne, tc, r, cost,
             off, ret, stk, Array.get(U32, a2, ss))
        case 27:
          (a2, +v) = p
          +fi = fbat(bg, v, c)
          gr(f, c, gg, 28, dep, ss, n, g, i, best, bg, exp, ne, tc,
             U32.and(fi, 3), v, off,
             ret, stk, Array.get(U32, a2, U32.shrn(fi, 2n)))
        case 28:
          (a2, +w) = p
          +hi = U32.sub(1, U32.shrn(U32.sub(r, 2), 31n))
          +t1 = U32.add(w, U32.mul(hi, U32.sub(U32.shrn(w, 16n), w)))
          +t2 = U32.add(t1, U32.mul(U32.and(r, 1),
                                    U32.sub(U32.shrn(t1, 8n), t1)))
          +rv = U32.and(t2, 255)
          gr(f, c, gg, 29, dep, ss, n, g, i, best, bg, exp, ne, tc, 0, cost,
             rv, ret, stk, Array.get(U32, a2, U32.add(gcur(dep, c, gg), rv)))
        case 29:
          (a2, +pos) = p
          gr(f, c, gg, 35, dep, ss, n, g, i, best, bg, exp, ne, tc, r, cost,
             off, pos, stk, Array.get(U32, a2, U32.add(goff(dep, c, gg), off)))
        case 35:
          (a2, +ov) = p
          +rv = off
          a3 = Array.set(U32, a2, U32.add(gcur(dep, c, gg), rv),
                         U32.inc(ret))
          a4 = Array.set(U32, a3, U32.add(U32.add(gset(U32.inc(dep), c, gg),
                                                  ov), ret), cost)
          +i2 = U32.inc(i)
          +more = A.lt01(i2, n)
          gr(f, c, gg, A.sel(more, 27, 30), dep, ss, n, g, i2, best,
             bg, exp, ne, tc, r, cost, off, ret, stk,
             Array.get(U32, a4, A.sel(more, U32.add(ss, i2), 0)))
        # ------------------------------------------------------- buckets ----
        case 30:
          (a2, _) = p
          gr(f, c, gg, 31, dep, ss, n, g, i, best, bg, exp, ne, tc, 0, n, off,
             ret, stk, Array.get(U32, a2, 0))
        case 31:
          (a2, _) = p
          +inb = A.lt01(r, 256)
          gr(f, c, gg, A.sel(inb, 32, 90), dep, ss, n, g, i, best, bg, exp, ne,
             tc, r, cost, off, A.sel(inb, ret, cost), stk,
             Array.get(U32, a2, U32.add(gcnt(dep, c, gg),
                                        A.sel(inb, r, 0))))
        case 32:
          (a2, +v) = p
          +inb = A.lt01(r, 256)
          gr(f, c, gg, 33, dep, ss, n, g, i, best, bg, v, ne, tc, r, cost, off,
             ret, stk,
             Array.get(U32, a2, U32.add(goff(dep, c, gg),
                                        A.sel(inb, r, 0))))
        case 33:
          (a2, +o) = p
          +skip = U32.max(A.eq01(exp, 0), A.eq01(r, win()))
          gr(f, c, gg, A.sel(skip, 34, 36), dep, ss, n, g, i, best, bg, exp,
             ne, tc, r, cost, o, ret, stk, Array.get(U32, a2, 0))
        case 34:
          (a2, _) = p
          gr(f, c, gg, 31, dep, ss, n, g, i, best, bg, exp, ne, tc, U32.inc(r),
             cost, off, ret, stk, Array.get(U32, a2, 0))
        case 36:
          (a2, _) = p
          stk2 : List<GFr> = Con{GF{cost, r, dep}, stk}
          gr(f, c, gg, 0, U32.inc(dep), U32.add(gset(U32.inc(dep), c, gg), off),
             exp, 0, 0, 2147483647, 0, 0, 0, 0, 0, 0, 0, 0, stk2,
             Array.get(U32, a2, 0))
        # ------------------------------------------------------- deliver ----
        case 90:
          match stk:
            case Nil{}:
              (a2, _) = p
              Array.set(U32, a2, rescell(c, gg), ret)
            case Con{GF{+cost2, +r2, +dep2}, rest}:
              (a2, _) = p
              +r3 = U32.inc(r2)
              gr(f, c, gg, 31, dep2, ss, n, g, i, best, bg, exp, ne, tc, r3,
                 U32.add(cost2, ret), off, ret, rest, Array.get(U32, a2, 0))
        case _:
          (a2, _) = p
          a2

# Copy the root set into the greedy arena's depth 0.
def gcp(+fuel: Nat, +i: U32, +c: U32, +gg: U32,
        p: Array<U32> & U32) -> Array<U32>:
  match fuel:
    case 0n:
      (a2, _) = p
      a2
    case 1n+f:
      (a2, +v) = p
      a3 = Array.set(U32, a2, U32.add(gset(0, c, gg), i), v)
      +i2 = U32.inc(i)
      +more = A.lt01(i2, c)
      gcp(f, i2, c, gg,
          Array.get(U32, a3, U32.add(S.set_at(0, c, gg),
                                     A.sel(more, i2, 0))))

# Rust's greedy_solve over the depth-0 set (candidate ids in set[0]).
def greedy(a: Array<U32>, +c: U32, +gg: U32) -> Array<U32>:
  a0 = Array.set(U32, a, rescell(c, gg), 4294967295)
  a1 = gcp(U32.to_nat(c), 0, c, gg,
           Array.get(U32, a0, S.set_at(0, c, gg)))
  +fuel = Nat.add(Nat.mul(Nat.mul(U32.to_nat(gg), U32.to_nat(c)),
                          Nat.mul(U32.to_nat(U32.add(c, 8)), 64n)), 1024n)
  gr(fuel, c, gg, 0, 0, gset(0, c, gg), c, 0, 0, 2147483647, 0, 0, 0, 0, 0,
     0, 0, 0, Nil{}, Array.get(U32, a1, 0))
