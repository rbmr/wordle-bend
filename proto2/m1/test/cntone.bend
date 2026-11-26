import Base
import ../src/main.bend as M
import ../src/geo.bend as G
import ../src/tab.bend as T
import ../src/sec.bend as S

# Dump the count statistics of the first `lim` guesses over the first `n`
# candidates, one line per guess: "g t dup hw n3 sq".
# ph 0 over check, 1 run cnt, 2 read pk, 3 read n3, 4 read sq, 5 print, 6 next.

def fill_range(+fuel: Nat, +i: U32, +n: U32, +start: U32, +base: U32,
               a: Array<U32>) -> Array<U32>:
  match fuel:
    case 0n:
      a
    case 1n+p:
      a[U32.add(base, i)] <- U32.add(start, i)
      fill_range(p, U32.inc(i), n, start, base, a)

def show(+g: U32, +pk: U32, +n3: U32, +sq: U32) -> String:
  U32.show(g) ++ " t=" ++ U32.show(U32.and(pk, 4095))
  ++ " dup=" ++ U32.show(U32.and(U32.shrn(pk, 12n), 4095))
  ++ " hw=" ++ U32.show(U32.and(U32.shrn(pk, 24n), 1))
  ++ " n3=" ++ U32.show(n3) ++ " sq=" ++ U32.show(sq)

def go(+fuel: Nat, +ph: U32, +g: U32, +lim: U32, +pk: U32, +n3: U32,
       +sb: U32, +n: U32, +c: U32, +gg: U32,
       r: Array<U32> & U32) -> IO(Unit):
  match fuel:
    case 0n:
      (a2, _) = r
      IO.pure(Unit, Unit{})
    case 1n+f:
      match ph:
        case 0:
          (a2, _) = r
          +over = U32.sub(1, U32.min(1, U32.sub(g, lim)))
          go(f, U32.add(1, U32.mul(over, 6)), g, lim, pk, n3, sb, n, c, gg,
             Array.get(U32, a2, 0))
        case 1:
          (a2, _) = r
          a3 = S.cnt(g, sb, n, 4294967295, 0, c, gg, a2)
          go(f, 2, g, lim, 0, 0, sb, n, c, gg,
             Array.get(U32, a3, S.pkcell(c, gg)))
        case 2:
          (a2, +v) = r
          go(f, 3, g, lim, v, n3, sb, n, c, gg,
             Array.get(U32, a2, S.n3cell(c, gg)))
        case 3:
          (a2, +v) = r
          go(f, 4, g, lim, pk, v, sb, n, c, gg,
             Array.get(U32, a2, S.sqcell(c, gg)))
        case 4:
          (a2, +v) = r
          do IO<Unit>:
            Unit <- IO.print(show(g, pk, n3, v))
            go(f, 0, U32.inc(g), lim, 0, 0, sb, n, c, gg,
               Array.get(U32, a2, 0))
        case _:
          (a2, _) = r
          IO.pure(Unit, Unit{})

def run(+gp: String, +cp: String, +n: U32, +lim: U32) -> IO(Unit):
  do IO<Unit>:
    +gtext : String <- M.read_file(gp)
    +ctext : String <- M.read_file(cp)
    +c : U32 = T.word_count(ctext)
    +gg : U32 = T.word_count(gtext)
    total : U32 = G.total_size(c, gg)
    a : Array<U32> = Array.new(U32, M.depth_for(total), 0)
    a1 : Array<U32> = M.build_all(c, gg, gtext, ctext, a)
    +sb : U32 = S.set_at(0, c, gg)
    a2 : Array<U32> = fill_range(U32.to_nat(n), 0, n, 0, sb, a1)
    go(Nat.mul(U32.to_nat(lim), 8n), 0, 0, lim, 0, 0, sb, n, c, gg,
       Array.get(U32, a2, 0))

def go2(r1: List<&1, String>, +gp: String) -> IO(Unit):
  match r1:
    case Nil{}:
      IO.print("usage: cntone <guesses> <candidates>")
    case Con{cp, _}:
      run(gp, cp, 24, 6)

def go1(args: List<&1, String>) -> IO(Unit):
  match args:
    case Nil{}:
      IO.print("usage: cntone <guesses> <candidates>")
    case Con{gp, r1}:
      go2(r1, gp)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<&1, String> <- IO.args()
    go1(List.tail(&1, String, args))
