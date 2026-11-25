import Base
import ../src/main.bend as M
import ../src/geo.bend as G
import ../src/tab.bend as T
import ../src/sec.bend as S
import ../src/arith.bend as A

def prn(+show: U32, +m: String) -> IO(Unit):
  match show:
    case 0:
      IO.pure(Unit, Unit{})
    case _:
      IO.print(m)

# st 0: count g=0. st 1: count g=i with the element i skipped, i = 0..c-1.
# st 2: count g=0 again. st 3: stop. The pair holds the pk of the last count.
def go(+fuel: Nat, +st: U32, +i: U32, +c: U32, +gg: U32, +sb: U32,
       r: Array<U32> & U32) -> IO(Unit):
  match fuel:
    case 0n:
      (a, _) = r
      IO.pure(Unit, Unit{})
    case 1n+f:
      (a, +pv) = r
      +s0 = A.eq01(st, 0)
      +s1 = A.eq01(st, 1)
      +s2 = A.eq01(st, 2)
      +s3 = A.eq01(st, 3)
      +show0 = U32.and(s1, A.eq01(i, 0))
      +show = U32.max(show0, s3)
      +msg = U32.show(st) ++ " " ++ U32.show(pv)
      +garg = A.sel(s1, i, 0)
      +skip = A.sel(s1, i, 4294967295)
      +st2 = A.sel(s0, 1, A.sel(s2, 3, st))
      a1 = S.cnt(A.sel(s3, 0, garg), sb, c, A.sel(s3, 4294967295, skip),
                 0, c, gg, a)
      +i2 = U32.inc(i)
      +last = A.ge01(i2, c)
      +st3 = A.sel(s1, A.sel(last, 2, 1), st2)
      +i3 = A.sel(U32.and(s1, U32.sub(1, last)), i2, 0)
      +done = s3
      +idx = A.sel(done, 0, S.pkcell(c, gg))
      do IO<Unit>:
        Unit <- prn(show, msg)
        go(f, st3, i3, c, gg, sb, Array.get(U32, a1, idx))

def fill(+fuel: Nat, +i: U32, +n: U32, +base: U32,
         a: Array<U32>) -> Array<U32>:
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
    +f1 : Nat = Nat.add(Nat.mul(U32.to_nat(c), 128n), 64n)
    go(f1, 0, 0, c, gg, sb, Array.get(U32, a2, 0))

def go2(rest: List<&1, String>, +gtext: String, +gn: U32) -> IO(Unit):
  match rest:
    case Nil{}:
      IO.print("usage: cnttmp <guesses> <candidates>")
    case Con{cand_path, more}:
      do IO<Unit>:
        +ctext : String <- M.read_file(cand_path)
        +cn : U32 = T.word_count(ctext)
        run1(cn, gn, gtext, ctext)

def go1(rest: List<&1, String>) -> IO(Unit):
  match rest:
    case Nil{}:
      IO.print("usage: cnttmp <guesses> <candidates>")
    case Con{gpath, more}:
      do IO<Unit>:
        +gtext : String <- M.read_file(gpath)
        +gn : U32 = T.word_count(gtext)
        go2(more, gtext, gn)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<&1, String> <- IO.args()
    go1(List.tail(&1, String, args))
