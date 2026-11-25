import Base
import ../src/main.bend as M
import ../src/geo.bend as G
import ../src/tab.bend as T
import ../src/sec.bend as S
import ../src/arith.bend as A

# Checksum test for the scan primitives, one guess per line:
#   g <g> t <t> hw <hw> n3 <n3> sq <sq> ne <hash> ar <hash>
# The hashes are rolling (h = h*31 + v) over the distinct-response list and
# over the scattered bucket arena.

def hcell(+c: U32, +gg: U32) -> U32:
  U32.add(G.off_qgen(c, gg), 500)

def acell(+c: U32, +gg: U32) -> U32:
  U32.add(G.off_qgen(c, gg), 501)

# Rolling hash over [base, base+n), written to cell `out`.
def hash_go(+fuel: Nat, +ph: U32, +i: U32, +n: U32, +base: U32, +h: U32,
            +out: U32, p: Array<U32> & U32) -> Array<U32>:
  match fuel:
    case 0n:
      (a2, _) = p
      Array.set(U32, a2, out, h)
    case 1n+p2:
      match ph:
        case 0:
          (a2, +v) = p
          +i2 = U32.inc(i)
          +last = A.eq01(i2, n)
          +idx = A.sel(last, 0, U32.add(base, i2))
          hash_go(p2, A.sel(last, 1, 0), i2, n, base,
                  U32.add(U32.mul(h, 31), v), out, Array.get(U32, a2, idx))
        case _:
          (a2, _) = p
          Array.set(U32, a2, out, h)

def hash(+base: U32, +n: U32, +out: U32, a: Array<U32>) -> Array<U32>:
  hash_go(Nat.add(Nat.mul(U32.to_nat(n), 4n), 64n), 0, 0, n, base, 0, out,
          Array.get(U32, a, base))

def depth_for(+size: U32) -> Nat:
  Nat.add(U32.log2(U32.sub(size, 1)), 1n)

def fill_ids(+fuel: Nat, +i: U32, +base: U32, a: Array<U32>) -> Array<U32>:
  match fuel:
    case 0n:
      a
    case 1n+p:
      fill_ids(p, U32.inc(i), base, Array.set(U32, a, U32.add(base, i), i))

# One scan, in phases, each step consuming the read pair `r`.
def one(+fuel: Nat, +ph: U32, +g: U32, +c: U32, +gg: U32, +t: U32, +n3: U32,
        +sq: U32, +pk: U32, r: Array<U32> & U32) -> IO(Array<U32>):
  match fuel:
    case 0n:
      (a0, _) = r
      IO.pure(Array<U32>, a0)
    case 1n+fu:
      match ph:
        case 0:
          (a, _) = r
          a1 = S.cnt(g, S.set_at(0, c, gg), c, 4294967295, U32.mul(g, 1024),
                     0, c, gg, a)
          one(fu, 1, g, c, gg, t, n3, sq, pk,
              Array.get(U32, a1, S.pkcell(c, gg)))
        case 1:
          (a, +v) = r
          one(fu, 2, g, c, gg, U32.and(v, 4095), n3, sq, U32.shrn(v, 24n),
              Array.get(U32, a, S.n3cell(c, gg)))
        case 2:
          (a, v) = r
          one(fu, 3, g, c, gg, t, v, sq, pk,
              Array.get(U32, a, S.sqcell(c, gg)))
        case 3:
          (a, v) = r
          a1 = S.offsets(t, 0, S.set_at(1, c, gg), c, gg, U32.mul(g, 1024), a)
          a2 = S.scatter(g, S.set_at(0, c, gg), c, 0, S.set_at(1, c, gg), c,
                         gg, a1)
          one(fu, 4, g, c, gg, t, n3, v, pk,
              Array.get(U32, a2, S.ne_at(0, c, gg)))
        case 4:
          (a, v) = r
          a1 = hash(S.ne_at(0, c, gg), t, hcell(c, gg), a)
          one(fu, 5, g, c, gg, t, n3, sq, pk,
              Array.get(U32, a1, S.set_at(1, c, gg)))
        case 5:
          (a, v) = r
          a1 = hash(S.set_at(1, c, gg), c, acell(c, gg), a)
          one(fu, 6, g, c, gg, t, n3, sq, pk,
              Array.get(U32, a1, hcell(c, gg)))
        case 6:
          (a, _) = r
          one(fu, 7, g, c, gg, t, n3, sq, pk,
              Array.get(U32, a, acell(c, gg)))
        case 7:
          (a, v) = r
          do IO<Array<U32>>:
            Unit <- IO.print("g " ++ U32.show(g) ++ " t " ++ U32.show(t)
                             ++ " hw " ++ U32.show(pk)
                             ++ " n3 " ++ U32.show(n3) ++ " sq " ++ U32.show(sq)
                             ++ " ar " ++ U32.show(v))
            IO.pure(Array<U32>, a)
        case _:
          (a2, _) = r
          IO.pure(Array<U32>, a2)

def loop(+fuel: Nat, +g: U32, +c: U32, +gg: U32, a: Array<U32>) -> IO(Unit):
  match fuel:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+p:
      do IO<Unit>:
        a2 : Array<U32> <- one(16n, 0, g, c, gg, 0, 0, 0, 0,
                               Array.get(U32, a, 0))
        loop(p, U32.inc(g), c, gg, a2)

def go(+gp: String, +cp: String, +n: U32) -> IO(Unit):
  do IO<Unit>:
    +gtext : String <- M.read_file(gp)
    +ctext : String <- M.read_file(cp)
    +c : U32 = T.word_count(ctext)
    +gg : U32 = T.word_count(gtext)
    total : U32 = G.total_size(c, gg)
    a : Array<U32> = Array.new(U32, depth_for(total), 0)
    a0 : Array<U32> = M.build_all(c, gg, gtext, ctext, a)
    a1 : Array<U32> = fill_ids(U32.to_nat(c), 0, S.set_at(0, c, gg), a0)
    loop(Nat.add(U32.to_nat(n), 1n), 0, c, gg, a1)

def go_m(m: Maybe<&2, U32>, +gp: String, +cp: String) -> IO(Unit):
  match m:
    case Some{+n}:
      go(gp, cp, n)
    case None{}:
      IO.print("bad n")

def go3(r2: List<&1, String>, +gp: String, +cp: String) -> IO(Unit):
  match r2:
    case Nil{}:
      IO.print("usage: scan <guesses> <candidates> <nguesses>")
    case Con{ns, _}:
      go_m(U32.read(ns), gp, cp)

def go2(r1: List<&1, String>, +gp: String) -> IO(Unit):
  match r1:
    case Nil{}:
      IO.print("usage: scan <guesses> <candidates> <nguesses>")
    case Con{cp, r2}:
      go3(r2, gp, cp)

def go1(args: List<&1, String>) -> IO(Unit):
  match args:
    case Nil{}:
      IO.print("usage: scan <guesses> <candidates> <nguesses>")
    case Con{gp, r1}:
      go2(r1, gp)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<&1, String> <- IO.args()
    go1(List.tail(&1, String, args))
