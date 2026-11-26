# dcount check: distinct responses of a few guesses over prefix sets of several
# sizes, using prof.dcount (the branching scan's counting walk).
import Base
import ../src/main.bend as M
import ../src/geo.bend as G
import ../src/tab.bend as T
import ../src/sec.bend as S
import ../src/prof.bend as P
import ../src/arith.bend as A

def prn(r: Array<U32> & U32, +tag: String) -> IO(Array<U32>):
  (a, v) = r
  do IO<Array<U32>>:
    Unit <- IO.print(tag ++ " " ++ U32.show(v))
    IO.pure(Array<U32>, a)

def fill_range(+fuel: Nat, +i: U32, +n: U32, +start: U32, +base: U32,
               a: Array<U32>) -> Array<U32>:
  match fuel:
    case 0n:
      a
    case 1n+p:
      a[U32.add(base, i)] <- U32.add(start, i)
      fill_range(p, U32.inc(i), n, start, base, a)

# guesses 0..gm-1 over set sizes 2..km-1, printing "c g k count".
def cells(+fuel: Nat, +g: U32, +k: U32, +km: U32, +gm: U32, +c: U32,
          +gg: U32, a: Array<U32>) -> IO(Unit):
  match fuel:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+f:
      do IO<Unit>:
        a1 : Array<U32> = P.dcount(a, g, S.set_at(0, c, gg), k, c, gg)
        a2 : Array<U32> <- prn(Array.get(U32, a1, P.dnres(c, gg)),
                               "c " ++ U32.show(g) ++ " " ++ U32.show(k))
        +over : U32 = A.ge01(U32.inc(k), km)
        cells(f, U32.add(g, over), U32.mul(U32.sub(1, over), U32.inc(k)), km,
              gm, c, gg, a2)

def run(+gp: String, +cp: String, +n: U32) -> IO(Unit):
  do IO<Unit>:
    +gtext : String <- M.read_file(gp)
    +ctext : String <- M.read_file(cp)
    +c : U32 = T.word_count(ctext)
    +gg : U32 = T.word_count(gtext)
    total : U32 = G.total_size(c, gg)
    a : Array<U32> = Array.new(U32, M.depth_for(total), 0)
    a1 : Array<U32> = M.build_all(c, gg, gtext, ctext, a)
    a2 : Array<U32> = fill_range(32n, 0, n, 0, S.set_at(0, c, gg), a1)
    cells(Nat.add(Nat.mul(U32.to_nat(n), Nat.mul(32n, U32.to_nat(n))), 64n),
          0, 2, U32.add(n, 1), 6, c, gg, a2)

def rdm(m: Maybe<&2, U32>, +gp: String, +cp: String) -> IO(Unit):
  match m:
    case Some{+b}:
      run(gp, cp, b)
    case None{}:
      run(gp, cp, 24)

def go3(r2: List<&1, String>, +gp: String, +cp: String) -> IO(Unit):
  match r2:
    case Nil{}:
      run(gp, cp, 24)
    case Con{bs, _}:
      rdm(U32.read(bs), gp, cp)

def go2(r1: List<&1, String>, +gp: String) -> IO(Unit):
  match r1:
    case Nil{}:
      IO.print("usage: dncount <guesses> <candidates> [n]")
    case Con{cp, r2}:
      go3(r2, gp, cp)

def go1(args: List<&1, String>) -> IO(Unit):
  match args:
    case Nil{}:
      IO.print("usage: dncount <guesses> <candidates> [n]")
    case Con{gp, r1}:
      go2(r1, gp)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<&1, String> <- IO.args()
    go1(List.tail(&1, String, args))
