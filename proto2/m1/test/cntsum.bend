import Base
import ../src/main.bend as M
import ../src/geo.bend as G
import ../src/tab.bend as T
import ../src/sec.bend as S

# Sum of distinct-response counts and of count-squared sums over all guesses on
# one fixed subset, as "sumt sumsq". Compare with ref.py on the same subset.

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

# ph 0 over check, 1 count, 2 read pk, 3 read sq, 4 next.
# Print the packed count for one guess over the fixed set.
def one_g(a: Array<U32>, +g: U32, +sb: U32, +n: U32, +c: U32,
          +gg: U32) -> IO(Array<U32>):
  a1 = S.cnt(g, sb, n, 4294967295, 0, c, gg, a)
  prn(Array.get(U32, a1, S.pkcell(c, gg)), U32.show(g))

def dump_c2g(+fuel: Nat, +i: U32, +c: U32, +gg: U32,
             r: Array<U32> & U32) -> IO(Unit):
  match fuel:
    case 0n:
      (a, _) = r
      IO.pure(Unit, Unit{})
    case 1n+f:
      (a, +v) = r
      do IO<Unit>:
        Unit <- IO.print("c2g " ++ U32.show(i) ++ " " ++ U32.show(v))
        dump_c2g(f, U32.inc(i), c, gg,
                 Array.get(U32, a, U32.add(U32.add(G.off_c2g(c, gg), i), 1)))

def keep(a: Array<U32>) -> IO(Unit):
  IO.pure(Unit, Unit{})

def g_go(+fuel: Nat, +ph: U32, +g: U32, +st: U32, +sq: U32, +sb: U32,
         +n: U32, +c: U32, +gg: U32, r: Array<U32> & U32) -> Array<U32>:
  match fuel:
    case 0n:
      (a2, _) = r
      a2
    case 1n+f:
      match ph:
        case 0:
          (a2, _) = r
          +over = U32.sub(1, U32.min(1, U32.sub(g, gg)))
          g_go(f, U32.add(1, U32.mul(over, 4)), g, st, sq, sb, n, c, gg,
               Array.get(U32, a2, 0))
        case 1:
          (a2, _) = r
          a3 = S.cnt(g, sb, n, 4294967295, 0, c, gg, a2)
          g_go(f, 2, g, st, sq, sb, n, c, gg, Array.get(U32, a3, S.pkcell(c, gg)))
        case 2:
          (a2, +v) = r
          g_go(f, 3, g, U32.add(st, U32.and(v, 4095)), sq, sb, n, c, gg,
               Array.get(U32, a2, S.sqcell(c, gg)))
        case 3:
          (a2, +v) = r
          g_go(f, 0, U32.inc(g), st, U32.add(sq, v), sb, n, c, gg,
               Array.get(U32, a2, 0))
        case _:
          (a2, _) = r
          +b = U32.add(G.off_qgen(c, gg), 600)
          a3 = Array.set(U32, a2, b, st)
          a4 = Array.set(U32, a3, U32.inc(b), sq)
          g_go(f, 5, g, st, sq, sb, n, c, gg, Array.get(U32, a4, 0))
        case 5:
          (a2, _) = r
          a2

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
    a3 : Array<U32> = g_go(Nat.mul(U32.to_nat(gg), 8n), 0, 0, 0, 0, sb, 24, c,
                           gg, Array.get(U32, a2, 0))
    +b : U32 = U32.add(G.off_qgen(c, gg), 600)
    a4 : Array<U32> <- prn(Array.get(U32, a3, b), "sumt")
    a5 : Array<U32> <- prn(Array.get(U32, a4, U32.inc(b)), "sumsq")
    Unit <- keep(a5)
    IO.pure(Unit, Unit{})

def go2(r1: List<&1, String>, +gp: String) -> IO(Unit):
  match r1:
    case Nil{}:
      IO.print("usage: cntsum <guesses> <candidates>")
    case Con{cp, _}:
      run(gp, cp)

def go1(args: List<&1, String>) -> IO(Unit):
  match args:
    case Nil{}:
      IO.print("usage: cntsum <guesses> <candidates>")
    case Con{gp, r1}:
      go2(r1, gp)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<&1, String> <- IO.args()
    go1(List.tail(&1, String, args))
