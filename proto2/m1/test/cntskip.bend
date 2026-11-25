import Base
import ../src/main.bend as M
import ../src/geo.bend as G
import ../src/tab.bend as T
import ../src/sec.bend as S
import ../src/arith.bend as A

# Phase 1's counting in isolation: for ci = 0..c-1 count guess c2g[ci] over the
# root set with element ci skipped, and print "ci pk".
# ph 0: pair = c2g[ci].  ph 1: pair = pk.  ph 2: stop.
def go(+fuel: Nat, +ph: U32, +ci: U32, +c: U32, +gg: U32, +sb: U32,
       r: Array<U32> & U32) -> IO(Unit):
  match fuel:
    case 0n:
      (a, _) = r
      IO.pure(Unit, Unit{})
    case 1n+f:
      match ph:
        case 0:
          (a, +v) = r
          a1 = S.cnt(v, sb, c, ci, 0, c, gg, a)
          go(f, 1, ci, c, gg, sb, Array.get(U32, a1, S.pkcell(c, gg)))
        case 1:
          (a, +v) = r
          +ci2 = U32.inc(ci)
          +done = A.ge01(ci2, c)
          +msg = U32.show(ci) ++ " " ++ U32.show(v)
          +idx = A.sel(done, 0, U32.add(G.off_c2g(c, gg), ci2))
          do IO<Unit>:
            Unit <- IO.print(msg)
            go(f, A.sel(done, 2, 0), ci2, c, gg, sb, Array.get(U32, a, idx))
        case _:
          (a, _) = r
          IO.pure(Unit, Unit{})

def fill(+fuel: Nat, +i: U32, +n: U32, +base: U32, a: Array<U32>) -> Array<U32>:
  match fuel:
    case 0n:
      a
    case 1n+p:
      a[U32.add(base, i)] <- i
      fill(p, U32.inc(i), n, base, a)

def run1(+c: U32, +gg: U32, +gtext: String, +ctext: String) -> IO(Unit):
  do IO<Unit>:
    total : U32 = G.total_size(c, gg)
    a : Array<U32> = Array.new(U32, Nat.add(U32.log2(total), 1n), 0)
    a1 : Array<U32> = M.build_all(c, gg, gtext, ctext, a)
    +sb : U32 = S.set_at(0, c, gg)
    a2 : Array<U32> = fill(U32.to_nat(c), 0, c, sb, a1)
    +f1 : Nat = Nat.add(Nat.mul(U32.to_nat(c), 4n), 64n)
    go(f1, 0, 0, c, gg, sb,
       Array.get(U32, a2, U32.add(G.off_c2g(c, gg), 0)))

def go2(rest: List<&1, String>, +gtext: String, +gn: U32) -> IO(Unit):
  match rest:
    case Nil{}:
      IO.print("usage: cntskip <guesses> <candidates>")
    case Con{cand_path, more}:
      do IO<Unit>:
        +ctext : String <- M.read_file(cand_path)
        +cn : U32 = T.word_count(ctext)
        run1(cn, gn, gtext, ctext)

def go1(rest: List<&1, String>) -> IO(Unit):
  match rest:
    case Nil{}:
      IO.print("usage: cntskip <guesses> <candidates>")
    case Con{gpath, more}:
      do IO<Unit>:
        +gtext : String <- M.read_file(gpath)
        +gn : U32 = T.word_count(gtext)
        go2(more, gtext, gn)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<&1, String> <- IO.args()
    go1(List.tail(&1, String, args))
