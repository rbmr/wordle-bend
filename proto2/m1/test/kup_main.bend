import Base
import ../src/main.bend as M
import ../src/geo.bend as G
import ../src/tab.bend as T
import ../src/sec.bend as S
import ../src/kup.bend as K

# Print k_upper for a few subsets of the candidate list, as "start len value",
# so the values can be checked against ref.k_upper on the same subsets.

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

# spec j: start = (j*37) mod c, len = 3 + (j*13) mod 60 (clamped to c-start)
def spec_start(+j: U32, +c: U32) -> U32:
  U32.mod(U32.mul(j, 37), c)

def spec_len(+j: U32, +s: U32, +c: U32) -> U32:
  +l0 = U32.add(3, U32.mod(U32.mul(j, 13), 60))
  U32.min(l0, U32.sub(c, s))

def one(a: Array<U32>, +j: U32, +c: U32, +gg: U32) -> IO(Array<U32>):
  do IO<Array<U32>>:
    +s : U32 = spec_start(j, c)
    +l : U32 = spec_len(j, s, c)
    +sb : U32 = S.set_at(0, c, gg)
    a1 : Array<U32> = fill_range(U32.to_nat(l), 0, l, s, sb, a)
    a2 : Array<U32> = K.k_upper(a1, sb, l, c, gg)
    a3 : Array<U32> <- prn(Array.get(U32, a2, K.kcell(c, gg)),
                             U32.show(s) ++ " " ++ U32.show(l))
    IO.pure(Array<U32>, a3)

def loop(+fuel: Nat, +j: U32, +c: U32, +gg: U32, a: Array<U32>) -> IO(Unit):
  match fuel:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+p:
      do IO<Unit>:
        a1 : Array<U32> <- one(a, j, c, gg)
        loop(p, U32.inc(j), c, gg, a1)

def run(+gp: String, +cp: String) -> IO(Unit):
  do IO<Unit>:
    +gtext : String <- M.read_file(gp)
    +ctext : String <- M.read_file(cp)
    +c : U32 = T.word_count(ctext)
    +gg : U32 = T.word_count(gtext)
    total : U32 = G.total_size(c, gg)
    a : Array<U32> = Array.new(U32, M.depth_for(total), 0)
    a1 : Array<U32> = M.build_all(c, gg, gtext, ctext, a)
    loop(U32.to_nat(U32.mul(c, 2)), 0, c, gg, a1)

def go2(r1: List<&1, String>, +gp: String) -> IO(Unit):
  match r1:
    case Nil{}:
      IO.print("usage: kup <guesses> <candidates>")
    case Con{cp, _}:
      run(gp, cp)

def go1(args: List<&1, String>) -> IO(Unit):
  match args:
    case Nil{}:
      IO.print("usage: kup <guesses> <candidates>")
    case Con{gp, r1}:
      go2(r1, gp)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<&1, String> <- IO.args()
    go1(List.tail(&1, String, args))
