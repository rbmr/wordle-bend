import Base
import ../src/main.bend as M
import ../src/geo.bend as G
import ../src/tab.bend as T
import ../src/sec.bend as S
import ../src/big.bend as Bg

# For each of the first 24 candidates in the set, print "i g t" with t the
# distinct-response count of its guess over the set. Compare with ref.py.

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

# ph 0 read bucket[i], 1 read c2g, 2 cnt, 3 read pk, 4 next.
def go(+fuel: Nat, +ph: U32, +i: U32, +g: U32, +sb: U32, +n: U32, +c: U32,
       +gg: U32, r: Array<U32> & U32) -> IO(Unit):
  match fuel:
    case 0n:
      (a2, _) = r
      IO.pure(Unit, Unit{})
    case 1n+f:
      match ph:
        case 0:
          (a2, _) = r
          +done = U32.sub(1, U32.min(1, U32.sub(i, n)))
          go(f, U32.add(1, U32.mul(done, 3)), i, g, sb, n, c, gg,
             Array.get(U32, a2, U32.add(sb, i)))
        case 1:
          (a2, +v) = r
          go(f, 2, i, g, sb, n, c, gg,
             Array.get(U32, a2, U32.add(G.off_c2g(c, gg), v)))
        case 2:
          (a2, +v) = r
          a3 = S.cnt(v, sb, n, 4294967295, 0, c, gg, a2)
          go(f, 3, i, v, sb, n, c, gg,
             Array.get(U32, a3, S.pkcell(c, gg)))
        case 3:
          (a2, +pk) = r
          do IO<Unit>:
            Unit <- IO.print(U32.show(i) ++ " " ++ U32.show(g) ++ " "
                             ++ U32.show(U32.and(pk, 4095)))
            go(f, 0, U32.inc(i), g, sb, n, c, gg, Array.get(U32, a2, 0))
        case _:
          (a2, _) = r
          IO.pure(Unit, Unit{})

def keep(a: Array<U32>) -> IO(Unit):
  IO.pure(Unit, Unit{})

def run(+gp: String, +cp: String) -> IO(Unit):
  do IO<Unit>:
    +gtext : String <- M.read_file(gp)
    +ctext : String <- M.read_file(cp)
    +c : U32 = T.word_count(ctext)
    +gg : U32 = T.word_count(gtext)
    total : U32 = G.total_size(c, gg)
    a : Array<U32> = Array.new(U32, M.depth_for(total), 0)
    a1 : Array<U32> = M.build_all(c, gg, gtext, ctext, a)
    +sb : U32 = S.set_at(0, c, gg)
    a2 : Array<U32> = fill_range(32n, 0, 24, 0, sb, a1)
    a3 : Array<U32> = Bg.kcand(a2, sb, 24, 1000, 0, c, gg)
    a4 : Array<U32> <- prn(Array.get(U32, a3, Bg.uused(c, gg)), "kcand")
    a5 : Array<U32> = Bg.kmax(a4, sb, 24, 0, 1000, 0, c, gg)
    a6 : Array<U32> <- prn(Array.get(U32, a5, Bg.uused(c, gg)), "kmax")
    Unit <- keep(a6)
    IO.pure(Unit, Unit{})

def go2(r1: List<&1, String>, +gp: String) -> IO(Unit):
  match r1:
    case Nil{}:
      IO.print("usage: kcd <guesses> <candidates>")
    case Con{cp, _}:
      run(gp, cp)

def go1(args: List<&1, String>) -> IO(Unit):
  match args:
    case Nil{}:
      IO.print("usage: kcd <guesses> <candidates>")
    case Con{gp, r1}:
      go2(r1, gp)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<&1, String> <- IO.args()
    go1(List.tail(&1, String, args))
