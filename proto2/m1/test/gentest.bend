import Base
import ../src/main.bend as M
import ../src/geo.bend as G
import ../src/tab.bend as T
import ../src/heur.bend as H
import ../src/sec.bend as S
import ../src/engine.bend as E
import ../src/driver.bend as D
import ../src/p12.bend as P

def prn(r: Array<U32> & U32, +tag: String) -> IO(Array<U32>):
  (a, v) = r
  do IO<Array<U32>>:
    Unit <- IO.print(tag ++ " " ++ U32.show(v))
    IO.pure(Array<U32>, a)

def qc(+c: U32, +gg: U32, +i: U32) -> U32:
  U32.add(G.off_qgen(c, gg), i)

def gph(+fuel: Nat, +ph: U32, +g1: U32, +g2: U32, +sb: U32, +c: U32,
        +gg: U32, +mx: U32, p: Array<U32> & U32) -> IO(Unit):
  match fuel:
    case 0n:
      (a, _) = p
      IO.pure(Unit, Unit{})
    case 1n+f:
      match ph:
        case 0:
          (a, +v) = p
          gph(f, 1, v, g2, sb, c, gg, mx, Array.get(U32, a, qc(c, gg, 707)))
        case 1:
          (a, +v) = p
          a1 = P.p2_scan(a, sb, c, 1000000, mx, 0, g1, c, gg)
          gph(f, 2, g1, v, sb, c, gg, mx, Array.get(U32, a1, qc(c, gg, 707)))
        case 2:
          (a, +v) = p
          a1 = S.cnt(0, sb, c, 4294967295, U32.add(v, 4096), 0, c, gg, a)
          gph(f, 3, g1, v, sb, c, gg, mx, Array.get(U32, a1, S.pkcell(c, gg)))
        case _:
          (a, +v) = p
          do IO<Unit>:
            Unit <- IO.print("pk " ++ U32.show(v) ++ " p1gen " ++ U32.show(g1)
                             ++ " p2gen " ++ U32.show(g2))
            IO.pure(Unit, Unit{})

def after(p: Array<U32> & U32, +c: U32, +gg: U32) -> IO(Unit):
  (a, +pk) = p
  +mx = U32.and(pk, 255)
  do IO<Unit>:
    +sb : U32 = S.set_at(0, c, gg)
    a2 : Array<U32> = D.fill_ids(U32.to_nat(c), 0, sb,
                                 H.cap_fill(U32.max(mx, 2), c, gg, a))
    +g0 : U32 = 1115000000
    a3 : Array<U32> = P.p1_scan(a2, sb, c, 1000000, U32.max(mx, 2), 0, g0, c, gg)
    gph(16n, 0, 0, 0, sb, c, gg, U32.max(mx, 2),
        Array.get(U32, a3, qc(c, gg, 707)))

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
