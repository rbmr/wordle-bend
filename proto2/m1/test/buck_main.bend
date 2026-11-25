import Base
import ../src/main.bend as M
import ../src/geo.bend as G
import ../src/tab.bend as T
import ../src/sec.bend as S
import ../src/buck.bend as Be
import ../src/heur.bend as H

# Check the bucket hash written by Be.eval against S.hset and against ref.py:
# print "hset h1 h2", then "beval h1 h2", then the used/exact result.

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
    a2 : Array<U32> = fill_range(24n, 0, 24, 0, sb, a1)
    +o1 : U32 = S.cnt_at(0, c, gg)
    +o2 : U32 = U32.inc(o1)
    a3 : Array<U32> = S.hset(a2, sb, 24, o1, o2, c, gg)
    a4 : Array<U32> <- prn(Array.get(U32, a3, o1), "hset h1")
    a5 : Array<U32> <- prn(Array.get(U32, a4, o2), "hset h2")
    a6 : Array<U32> = Be.eval(a5, sb, 24, 47, 30, 1, c, gg)
    +cm1 : U32 = U32.add(G.off_cmk(c, gg), 1024)
    a7 : Array<U32> <- prn(Array.get(U32, a6, cm1), "beval h1")
    a8 : Array<U32> <- prn(Array.get(U32, a7, U32.inc(cm1)), "beval h2")
    a9 : Array<U32> <- prn(Array.get(U32, a8, Be.res_used(c, gg)), "used")
    a10 : Array<U32> <- prn(Array.get(U32, a9, Be.res_ex(c, gg)), "ex|ck")
    Unit <- keep(a10)
    IO.pure(Unit, Unit{})

def go2(r1: List<&1, String>, +gp: String) -> IO(Unit):
  match r1:
    case Nil{}:
      IO.print("usage: buck <guesses> <candidates>")
    case Con{cp, _}:
      run(gp, cp)

def go1(args: List<&1, String>) -> IO(Unit):
  match args:
    case Nil{}:
      IO.print("usage: buck <guesses> <candidates>")
    case Con{gp, r1}:
      go2(r1, gp)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<&1, String> <- IO.args()
    go1(List.tail(&1, String, args))
