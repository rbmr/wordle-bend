import Base
import ../src/main.bend as M
import ../src/geo.bend as G
import ../src/tab.bend as T
import ../src/driver.bend as D
import ../src/sec.bend as S

def prn(r: Array<U32> & U32, +tag: String) -> IO(Array<U32>):
  (a, v) = r
  do IO<Array<U32>>:
    Unit <- IO.print(tag ++ " " ++ U32.show(v))
    IO.pure(Array<U32>, a)

def dump(+fuel: Nat, +i: U32, +c: U32, +gg: U32, a: Array<U32>) -> IO(Unit):
  match fuel:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+f:
      +base = G.off_c2g(c, gg)
      do IO<Unit>:
        a1 : Array<U32> <- prn(Array.get(U32, a, U32.add(base, i)),
                               "c2g " ++ U32.show(i))
        dump(f, U32.inc(i), c, gg, a1)

def go2(r: List<&1, String>, +gtext: String, +gn: U32) -> IO(Unit):
  match r:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{cp, _}:
      do IO<Unit>:
        +ctext : String <- M.read_file(cp)
        +cn : U32 = T.word_count(ctext)
        total : U32 = G.total_size(cn, gn)
        a : Array<U32> = Array.new(U32, D.depth_for(total), 0)
        a1 : Array<U32> = M.build_all(cn, gn, gtext, ctext, a)
        dump(U32.to_nat(cn), 0, cn, gn, a1)

def go1(r: List<&1, String>) -> IO(Unit):
  match r:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{gp, more}:
      do IO<Unit>:
        +gtext : String <- M.read_file(gp)
        go2(more, gtext, T.word_count(gtext))

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<&1, String> <- IO.args()
    go1(List.tail(&1, String, args))
