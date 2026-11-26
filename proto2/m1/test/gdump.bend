import Base
import ../src/main.bend as M
import ../src/geo.bend as G
import ../src/tab.bend as T
import ../src/sec.bend as S
import ../src/driver.bend as D
import ../src/greedy.bend as R

# Dump a range of the array as "tag index value" lines.
def dump(+fuel: Nat, +j: U32, +len: U32, +base: U32, +tag: String,
         r: Array<U32> & U32) -> IO(Array<U32>):
  match fuel:
    case 0n:
      (a2, _) = r
      IO.pure(Array<U32>, a2)
    case 1n+p:
      (a2, v) = r
      +j2 = U32.inc(j)
      +b = U32.add(base, U32.min(j2, U32.sub(len, 1)))
      nxt = Array.get(U32, a2, b)
      do IO<Array<U32>>:
        Unit <- IO.print(tag ++ " " ++ U32.show(j) ++ " " ++ U32.show(v))
        dump(p, j2, len, base, tag, nxt)

def pv(p: Array<U32> & U32, +tag: String) -> IO(Array<U32>):
  (a, v) = p
  do IO<Array<U32>>:
    Unit <- IO.print(tag ++ " " ++ U32.show(v))
    IO.pure(Array<U32>, a)

def go(+c: U32, +gg: U32, a: Array<U32>) -> IO(Unit):
  do IO<Unit>:
    +sb : U32 = S.set_at(0, c, gg)
    a1 : Array<U32> = D.fill_ids(U32.to_nat(c), 0, sb, a)
    a1g : Array<U32> = R.greedy(a1, c, gg)
    a2 : Array<U32> <- pv(Array.get(U32, a1g, R.rescell(c, gg)), "greedy")
    a3 : Array<U32> <- dump(U32.to_nat(U32.inc(c)), 0, c, R.gset(0, c, gg), "arena",
                            Array.get(U32, a2, R.gset(0, c, gg)))
    a4 : Array<U32> <- dump(12n, 0, 10, R.gcnt(0, c, gg), "count",
                            Array.get(U32, a3, R.gcnt(0, c, gg)))
    a5 : Array<U32> <- dump(30n, 0, 10, R.goff(0, c, gg), "off",
                            Array.get(U32, a4, R.goff(0, c, gg)))
    a6 : Array<U32> <- dump(U32.to_nat(U32.inc(c)), 0, c, R.gset(1, c, gg),
                            "child", Array.get(U32, a5, R.gset(1, c, gg)))
    IO.pure(Unit, Unit{})

def depth_for(+size: U32) -> Nat:
  Nat.add(U32.log2(U32.sub(size, 1)), 1n)

def go3(+gtext: String, +ctext: String) -> IO(Unit):
  do IO<Unit>:
    +c : U32 = T.word_count(ctext)
    +gg : U32 = T.word_count(gtext)
    total : U32 = G.total_size(c, gg)
    a : Array<U32> = Array.new(U32, depth_for(total), 0)
    a1 : Array<U32> = M.build_all(c, gg, gtext, ctext, a)
    go(c, gg, a1)

def go2(r2: List<&1, String>, +gtext: String) -> IO(Unit):
  match r2:
    case Nil{}:
      IO.print("usage: gdump <guesses> <candidates>")
    case Con{cp, _}:
      do IO<Unit>:
        +ctext : String <- M.read_file(cp)
        go3(gtext, ctext)

def go1(r1: List<&1, String>) -> IO(Unit):
  match r1:
    case Nil{}:
      IO.print("usage: gdump <guesses> <candidates>")
    case Con{gp, r2}:
      do IO<Unit>:
        +gtext : String <- M.read_file(gp)
        go2(r2, gtext)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<&1, String> <- IO.args()
    go1(List.tail(&1, String, args))
