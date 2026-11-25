import Base
import ../src/main.bend as M
import ../src/geo.bend as G
import ../src/tab.bend as T
import ../src/heur.bend as H
import ../src/sec.bend as S
import ../src/driver.bend as D
import ../src/p12.bend as P

def prn(r: Array<U32> & U32, +tag: String) -> IO(Array<U32>):
  (a, v) = r
  do IO<Array<U32>>:
    Unit <- IO.print(tag ++ " " ++ U32.show(v))
    IO.pure(Array<U32>, a)

def dump(+fuel: Nat, +i: U32, +nt: U32, +base: U32,
         r: Array<U32> & U32) -> IO(Unit):
  match fuel:
    case 0n:
      (a, _) = r
      IO.pure(Unit, Unit{})
    case 1n+f:
      (a, +v) = r
      do IO<Unit>:
        Unit <- IO.print("tuple " ++ U32.show(i) ++ " " ++ U32.show(v))
        dump(f, U32.inc(i), nt, base, Array.get(U32, a, U32.add(base, U32.add(U32.mul(i, 3), 1))))

def after(p: Array<U32> & U32, +c: U32, +gg: U32) -> IO(Unit):
  (a, +pk) = p
  +mx = U32.and(pk, 255)
  do IO<Unit>:
    +sb : U32 = S.set_at(0, c, gg)
    a2 : Array<U32> = D.fill_ids(U32.to_nat(c), 0, sb,
                                 H.cap_fill(U32.max(mx, 2), c, gg, a))
    a3 : Array<U32> = P.p2_scan(a2, sb, c, 873, U32.max(mx, 2), 0,
                                1048576, c, gg)
    +cm : U32 = G.off_qgen(c, gg)
    a4 : Array<U32> <- prn(Array.get(U32, a3, U32.add(cm, 700)), "p2best")
    a5 : Array<U32> <- prn(Array.get(U32, a4, U32.add(cm, 701)), "lmk")
    a6 : Array<U32> <- prn(Array.get(U32, a5, U32.add(cm, 702)), "v2")
    a7 : Array<U32> <- prn(Array.get(U32, a6, U32.add(cm, 703)), "mv")
    a8 : Array<U32> <- prn(Array.get(U32, a7, U32.add(cm, 704)), "nt")
    a9 : Array<U32> <- prn(Array.get(U32, a8, U32.add(cm, 705)), "ngs")
    a10 : Array<U32> <- prn(Array.get(U32, a9, U32.add(cm, 706)), "npr")
    +b0 : U32 = G.off_p2t(c, gg)
    a11 : Array<U32> <- prn(Array.get(U32, a10, b0), "t0lb")
    a12 : Array<U32> <- prn(Array.get(U32, a11, U32.add(b0, 1)), "t0exp")
    a13 : Array<U32> <- prn(Array.get(U32, a12, U32.add(b0, 2)), "t0g")
    a14 : Array<U32> <- prn(Array.get(U32, a13, U32.add(b0, 3)), "t1lb")
    a15 : Array<U32> <- prn(Array.get(U32, a14, U32.add(b0, 4)), "t1exp")
    a16 : Array<U32> <- prn(Array.get(U32, a15, U32.add(b0, 5)), "t1g")
    IO.pure(Unit, Unit{})

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
        after(Array.get(U32, D.maxk(cn, gn, a1), D.mxcell(cn, gn)), cn, gn)

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
