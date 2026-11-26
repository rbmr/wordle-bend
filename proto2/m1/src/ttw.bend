# Witness copies for the transposition table.
#
# A cache keyed by hashes alone cannot be certified: two different candidate
# sets can share a key pair, and the stored value belongs to only one of them.
# So every cached entry names an immutable copy of the set that produced it,
# and a hit is accepted only after comparing the node's set with that copy cell
# by cell. The copy lives in an append-only arena (`off_wit`): offsets are
# never reused, and once the arena is full no further entries are inserted
# (their witness word is 0, and an entry with witness 0 never hits).
#
# Cells used here (all in the qgen block): 614 the arena cursor, 615 the copy
# result (offset + 1, or 0 when there is no room), 616 the compare flag.
import Base
import ./geo.bend as G
import ./arith.bend as A

def wcurcell(+c: U32, +gg: U32) -> U32:
  U32.add(G.off_qgen(c, gg), 614)

def wrescell(+c: U32, +gg: U32) -> U32:
  U32.add(G.off_qgen(c, gg), 615)

def wflagcell(+c: U32, +gg: U32) -> U32:
  U32.add(G.off_qgen(c, gg), 616)

# --------------------------------------------------------------- copy n cells --
#
# ph 0 read the cursor and decide; 1 copy one cell and advance; 2 arena full;
# 3 bump the cursor and store the result; 4/5 return.
def wcp_go(+fuel: Nat, +ph: U32, +i: U32, +src: U32, +dst: U32, +n: U32,
           +cur: U32, +c: U32, +gg: U32, r: Array<U32> & U32) -> Array<U32>:
  match fuel:
    case 0n:
      (a2, _) = r
      a2
    case 1n+f:
      match ph:
        case 0:
          (a2, +v) = r
          +room = U32.sub(1, A.ge01(U32.add(v, n), U32.inc(G.wit_size())))
          +d = A.sel(room, U32.add(G.off_wit(c, gg), v), 0)
          wcp_go(f, A.sel(room, 1, 2), 0, src, d, n, v, c, gg,
                 Array.get(U32, a2, A.sel(room, src, 0)))
        case 1:
          (a2, +v) = r
          a3 = Array.set(U32, a2, U32.add(dst, i), v)
          +i2 = U32.inc(i)
          +done = A.ge01(i2, n)
          +idx = A.sel(done, wcurcell(c, gg), U32.add(src, i2))
          wcp_go(f, A.sel(done, 3, 1), i2, src, dst, n, cur, c, gg,
                 Array.get(U32, a3, idx))
        case 3:
          # The cursor read arrives here; cur + n is the new cursor and the
          # result is dst - off_wit + 1.
          (a2, +v) = r
          a3 = Array.set(U32, a2, wcurcell(c, gg), U32.add(v, n))
          a4 = Array.set(U32, a3, wrescell(c, gg),
                         U32.inc(U32.sub(dst, G.off_wit(c, gg))))
          wcp_go(f, 4, i, src, dst, n, cur, c, gg, Array.get(U32, a4, 0))
        case 2:
          (a2, _) = r
          a3 = Array.set(U32, a2, wrescell(c, gg), 0)
          wcp_go(f, 4, i, src, dst, n, cur, c, gg, Array.get(U32, a3, 0))
        case 4:
          (a2, _) = r
          wcp_go(f, 5, i, src, dst, n, cur, c, gg, Array.get(U32, a2, 0))
        case _:
          (a2, _) = r
          a2

def wcopy(a: Array<U32>, +src: U32, +n: U32, +c: U32, +gg: U32) -> Array<U32>:
  +fuel = Nat.add(Nat.mul(U32.to_nat(n), 8n), 24n)
  wcp_go(fuel, 0, 0, src, 0, n, 0, c, gg, Array.get(U32, a, wcurcell(c, gg)))

# ------------------------------------------------------- compare n cells ------
#
# wflagcell becomes 1 when a[from..from+n) equals a[to..to+n) cell by cell,
# else 0. ph 0 read from[i]; 1 read to[i] and fold; 2 write the flag; 3 return.
def wcm_go(+fuel: Nat, +ph: U32, +i: U32, +from: U32, +to: U32, +n: U32,
           +ok: U32, +v0: U32, +c: U32, +gg: U32,
           r: Array<U32> & U32) -> Array<U32>:
  match fuel:
    case 0n:
      (a2, _) = r
      a2
    case 1n+f:
      match ph:
        case 0:
          (a2, +v) = r
          wcm_go(f, 1, i, from, to, n, ok, v, c, gg,
                 Array.get(U32, a2, U32.add(to, i)))
        case 1:
          (a2, +v) = r
          +same = A.eq01(v0, v)
          +ok2 = U32.mul(ok, same)
          +i2 = U32.inc(i)
          +done = A.ge01(i2, n)
          +idx = A.sel(done, 0, U32.add(from, i2))
          wcm_go(f, A.sel(done, 2, 0), i2, from, to, n, ok2, v0, c, gg,
                 Array.get(U32, a2, idx))
        case 2:
          (a2, _) = r
          a3 = Array.set(U32, a2, wflagcell(c, gg), ok)
          wcm_go(f, 3, i, from, to, n, ok, v0, c, gg, Array.get(U32, a3, 0))
        case _:
          (a2, _) = r
          a2

def wcmp(a: Array<U32>, +from: U32, +to: U32, +n: U32, +c: U32,
         +gg: U32) -> Array<U32>:
  +fuel = Nat.add(Nat.mul(U32.to_nat(n), 8n), 24n)
  wcm_go(fuel, 0, 0, from, to, n, 1, 0, c, gg, Array.get(U32, a, from))
