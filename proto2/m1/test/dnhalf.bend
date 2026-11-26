import Base
import ../src/main.bend as M
import ../src/geo.bend as G
import ../src/tab.bend as T
import ../src/sec.bend as S
import ../src/prof.bend as P

def prn(r: Array<U32> & U32, +tag: String) -> IO(Array<U32>):
  (a, v) = r
  do IO<Array<U32>>:
    Unit <- IO.print(tag ++ " " ++ U32.show(v))
    IO.pure(Array<U32>, a)

def gv(r: Array<U32> & U32) -> U32:
  (a, +v) = r
  v

def fill_range(+fuel: Nat, +i: U32, +n: U32, +start: U32, +base: U32,
               a: Array<U32>) -> Array<U32>:
  match fuel:
    case 0n:
      a
    case 1n+p:
      a[U32.add(base, i)] <- U32.add(start, i)
      fill_range(p, U32.inc(i), n, start, base, a)

def step4(p: Array<U32> & U32, +c: U32, +gg: U32, +sb: U32) -> IO(Unit):
  (a7, +v) = p
  do IO<Unit>:
    Unit <- IO.print("h2alone " ++ U32.show(v))
    a8 : Array<U32> = P.dcount_part(a7, 0, sb, 0, 24, 0, c, gg, 1)
    a9 : Array<U32> <- prn(Array.get(U32, a8, P.dnres(c, gg)), "fullagain")
    IO.pure(Unit, Unit{})

def rd4(q: Array<U32> & U32, +c: U32, +gg: U32) -> IO(Array<U32>):
  (a, +r) = q
  do IO<Array<U32>>:
    a2 : Array<U32> <- prn(Array.get(U32, a, U32.add(U32.add(G.off_prof(c, gg), 224), r)), "cnt_of_touched0")
    IO.pure(Array<U32>, a2)

def rd3(q: Array<U32> & U32, +c: U32, +gg: U32) -> IO(Array<U32>):
  (a, +r) = q
  do IO<Array<U32>>:
    Unit <- IO.print("touched0 " ++ U32.show(r))
    a2 : Array<U32> <- prn(Array.get(U32, a, U32.add(U32.add(G.off_prof(c, gg), 224), r)), "cnt0")
    a3 : Array<U32> <- rd4(Array.get(U32, a2, U32.add(U32.add(G.off_prof(c, gg), 480), 0)), c, gg)
    IO.pure(Array<U32>, a3)

def rd2(q: Array<U32> & U32, +c: U32, +gg: U32) -> IO(Array<U32>):
  (a, _) = q
  rd3(Array.get(U32, a, 0), c, gg)

def step3(p: Array<U32> & U32, +c: U32, +gg: U32, +sb: U32) -> IO(Unit):
  (a5, +h1) = p
  do IO<Unit>:
    Unit <- IO.print("h1 " ++ U32.show(h1))
    a5b : Array<U32> <- rd2(Array.get(U32, a5, 0), c, gg)
    a7 : Array<U32> = P.dcount_part(a5b, 0, sb, 12, 24, h1, c, gg, 1)
    a8 : Array<U32> <- prn(Array.get(U32, a7, P.dnres(c, gg)), "h2total")
    a8b : Array<U32> = P.dcount_part(a8, 0, sb, 0, 12, 0, c, gg, 0)
    a8c : Array<U32> = P.dnclear(a8b, c, gg)
    a8d : Array<U32> <- prn(Array.get(U32, a8c, P.dnres(c, gg)), "after_clear_res")
    a8e : Array<U32> <- rd2(Array.get(U32, a8d, 0), c, gg)
    a9 : Array<U32> = P.dcount_part(a8e, 0, sb, 12, 24, 0, c, gg, 1)
    step4(Array.get(U32, a9, P.dnres(c, gg)), c, gg, sb)

def step2(p: Array<U32> & U32, +c: U32, +gg: U32, +sb: U32) -> IO(Unit):
  (a4, +fv) = p
  do IO<Unit>:
    Unit <- IO.print("full " ++ U32.show(fv))
    a5 : Array<U32> = P.dcount_part(a4, 0, sb, 0, 12, 0, c, gg, 0)
    step3(Array.get(U32, a5, P.dnres(c, gg)), c, gg, sb)

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
    a3 : Array<U32> = P.dcount(a2, 0, sb, 24, c, gg)
    step2(Array.get(U32, a3, P.dnres(c, gg)), c, gg, sb)

def go2(r1: List<&1, String>, +gp: String) -> IO(Unit):
  match r1:
    case Nil{}:
      IO.print("usage: dnhalf <guesses> <candidates>")
    case Con{cp, _}:
      run(gp, cp)

def go1(args: List<&1, String>) -> IO(Unit):
  match args:
    case Nil{}:
      IO.print("usage: dnhalf <guesses> <candidates>")
    case Con{gp, r1}:
      go2(r1, gp)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<&1, String> <- IO.args()
    go1(List.tail(&1, String, args))
