import Base
import ../src/main.bend as M
import ../src/geo.bend as G
import ../src/tab.bend as T
import ../src/sec.bend as S
import ../src/kup.bend as K
import ../src/prof.bend as P
import ../src/arith.bend as A

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

def dump(+fuel: Nat, +i: U32, +n: U32, +base: U32,
         r: Array<U32> & U32) -> IO(Array<U32>):
  match fuel:
    case 0n:
      (a2, _) = r
      IO.pure(Array<U32>, a2)
    case 1n+f:
      (a2, +v) = r
      +i2 = U32.inc(i)
      +more = A.lt01(i2, n)
      do IO<Array<U32>>:
        Unit <- IO.print("C " ++ U32.show(i) ++ " " ++ U32.show(v))
        dump(f, U32.mul(more, i2), n, base,
             Array.get(U32, a2, U32.add(base, U32.mul(more, i2))))

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
    a3 : Array<U32> <- dump(9n, 0, 8, G.off_gcls(c, gg),
                            Array.get(U32, a2, G.off_gcls(c, gg)))
    a4 : Array<U32> = K.k_upper(a3, sb, 24, c, gg)
    a5 : Array<U32> = P.mtab(a4, c, gg)
    a5k : Array<U32> <- prn(Array.get(U32, a5, K.kcell(c, gg)), "kupper")
    a6 : Array<U32> <- dump(31n, 0, 30, G.off_prof(c, gg),
                            Array.get(U32, a5k, G.off_prof(c, gg)))
    a6b : Array<U32> <- dump(25n, 0, 24, G.off_cdup(c, gg),
                             Array.get(U32, a6, G.off_cdup(c, gg)))
    a6c : Array<U32> <- dump(25n, 0, 24, G.off_cmask(c, gg),
                             Array.get(U32, a6b, G.off_cmask(c, gg)))
    a6d : Array<U32> <- dump(121n, 0, 120, G.off_cat(c, gg),
                             Array.get(U32, a6c, G.off_cat(c, gg)))
    a7 : Array<U32> <- dump(481n, 0, 480, G.off_mtab(c, gg),
                            Array.get(U32, a6d, G.off_mtab(c, gg)))
    IO.pure(Unit, Unit{})

def go(rest: List<&1, String>, +gp: String) -> IO(Unit):
  match rest:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{cp, _}:
      run(gp, cp)

def go1(rest: List<&1, String>) -> IO(Unit):
  match rest:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{gp, more}:
      go(more, gp)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<&1, String> <- IO.args()
    go1(List.tail(&1, String, args))
