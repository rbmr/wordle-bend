import Base
import ../src/main.bend as M
import ../src/geo.bend as G
import ../src/tab.bend as T
import ../src/sec.bend as S
import ../src/arith.bend as A

# Checksum test for the scan primitives: for each guess 0..n-1, count/offsets/
# scatter the full candidate set and print a rolling hash of the distinct
# response list (with its offsets and counts), a rolling hash of the scattered
# bucket arena, and the packed counters.
#
# Hashes are written into scratch cells of the state array (there is no way to
# return a second value), then printed by a one-cell read.

def scratch() -> U32:
  512

# Rolling hash h = h*31 + v over [base, base+n), written to cell `out`.
# ph 0: process the value just read.  ph 1: write and stop.
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
  +fuel = Nat.add(Nat.mul(U32.to_nat(n), 4n), 64n)
  hash_go(fuel, 0, 0, n, base, 0, out, Array.get(U32, a, base))

def prcell(r: Array<U32> & U32) -> IO(Array<U32>):
  (a, v) = r
  do IO<Array<U32>>:
    Unit <- IO.print(U32.show(v))
    IO.pure(Array<U32>, a)

def depth_for(+size: U32) -> Nat:
  Nat.add(U32.log2(U32.sub(size, 1)), 1n)

def fill_ids(+fuel: Nat, +i: U32, +base: U32, a: Array<U32>) -> Array<U32>:
  match fuel:
    case 0n:
      a
    case 1n+p:
      fill_ids(p, U32.inc(i), base,
               Array.set(U32, a, U32.add(base, i), i))

def one(st: S.CR, +g: U32, +c: U32, +gg: U32, +dep: U32) -> IO(Array<U32>):
  match st:
    case S.CR{a, +pk, +n3}:
      do IO<Array<U32>>:
        +t : U32 = U32.and(pk, 4095)
        +nb : U32 = S.ne_at(dep, c, gg)
        +dst : U32 = S.set_at(U32.inc(dep), c, gg)
        +hcell : U32 = U32.add(G.off_qgen(c, gg), 512)
        +acell : U32 = U32.add(hcell, 1)
        +head : String = "g " ++ U32.show(g) ++ " pk " ++ U32.show(pk)
                          ++ " n3 " ++ U32.show(n3) ++ " ne "
        a1 : Array<U32> = S.offsets(t, dep, dst, c, gg, U32.mul(g, 1024), a)
        a2 : Array<U32> = hash(nb, t, hcell, a1)
        a3 : Array<U32> = S.scatter(g, S.set_at(dep, c, gg), c, dep, dst, c,
                                    gg, a2)
        a4 : Array<U32> = hash(dst, c, acell, a3)
        Unit <- IO.print(head)
        a5 : Array<U32> <- prcell(Array.get(U32, a4, hcell))
        Unit <- IO.print("ar")
        a6 : Array<U32> <- prcell(Array.get(U32, a5, acell))
        IO.pure(Array<U32>, a6)

def loop(+fuel: Nat, +g: U32, +c: U32, +gg: U32, a: Array<U32>) -> IO(Unit):
  match fuel:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+p:
      do IO<Unit>:
        +sb : U32 = S.set_at(0, c, gg)
        a2 : Array<U32> <- one(S.cnt(g, sb, c, 4294967295, U32.mul(g, 1024), 0, c, gg, a),
                               g, c, gg, 0)
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
    +sb : U32 = S.set_at(0, c, gg)
    a1 : Array<U32> = fill_ids(U32.to_nat(c), 0, sb, a0)
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
