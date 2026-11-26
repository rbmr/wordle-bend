# Benchmark of the certified flat-array count (`src/core/dcount.bend`) on the
# same input as `proto2/m1/bench/dn_main.bend`: the same packed table, the same
# candidate-index set, the same k, the same result and count-cell checksum.
import Base
import ../src/core/arith.bend as A
import ../src/core/dcount.bend as DCount

def gg() -> U32:
  14855

def kk() -> U32:
  40

def tbl0() -> U32:
  1024

def sbase(+c: U32) -> U32:
  U32.add(U32.add(tbl0(), U32.div(U32.mul(c, gg()), 4)), 8)

def asize(+c: U32) -> U32:
  U32.add(sbase(c), 64)

def depth_for(+size: U32) -> Nat:
  Nat.add(U32.log2(U32.sub(size, 1)), 1n)

def fill_fb_go(+fuel: Nat, +i: U32, +n: U32, +seed: U32,
               a: Array<U32>) -> Array<U32>:
  match fuel:
    case 0n:
      a
    case 1n+f:
      +s = U32.add(U32.mul(seed, 1664525), 1013904223)
      fill_fb_go(f, U32.inc(i), n, s,
        Array.set(U32, a, U32.add(tbl0(), i), s))

def fill_fb(a: Array<U32>, +n: U32) -> Array<U32>:
  fill_fb_go(U32.to_nat(n), 0, n, 12345, a)

def fill_set_go(+fuel: Nat, +i: U32, +k: U32, +c: U32, +base: U32,
                a: Array<U32>) -> Array<U32>:
  match fuel:
    case 0n:
      a
    case 1n+f:
      +v = U32.mod(U32.add(U32.mul(i, 37), 11), c)
      fill_set_go(f, U32.inc(i), k, c, base,
        Array.set(U32, a, U32.add(base, i), v))

def fill_set(a: Array<U32>, +k: U32, +c: U32, +base: U32) -> Array<U32>:
  fill_set_go(U32.to_nat(k), 0, k, c, base, a)

def lp(+fuel: Nat, +g: U32, +c: U32, +o: U32,
       a: Array<U32>) -> Array<U32>:
  match fuel:
    case 0n:
      a
    case 1n+f:
      a2 = DCount.dc_go(Nat.add(Nat.mul(U32.to_nat(kk()), 8n), 80n),
                        0, 0, Nat.sub(U32.to_nat(kk()), 1n), 0n, 0,
                        U32.add(U32.mul(4, tbl0()), U32.mul(g, c)), o,
                        0, 0, (a, 0))
      +g2 = U32.inc(g)
      +wrap = A.ge01(g2, gg())
      lp(f, U32.mul(U32.sub(1, wrap), g2), c, o, a2)

def chk_go(+fuel: Nat, +i: U32, +acc: U32,
           r: Array<U32> & U32) -> U32:
  match fuel:
    case 0n:
      (a2, _) = r
      acc
    case 1n+f:
      (a2, +v) = r
      +i2 = U32.inc(i)
      +b1 = A.sel(A.ge01(i, 64), 512, U32.add(tbl0(), i))
      +b2 = A.sel(A.ge01(i, 65), U32.sub(i, 65), b1)
      +c1 = A.sel(A.ge01(i2, 64), 512, U32.add(tbl0(), i2))
      +c2 = A.sel(A.ge01(i2, 65), U32.sub(i2, 65), c1)
      chk_go(f, i2, U32.add(U32.mul(acc, 31), v),
        Array.get(U32, a2, A.sel(A.eq01(i2, 129), b2, c2)))

def checksum(a: Array<U32>) -> U32:
  chk_go(129n, 0, 0, Array.get(U32, a, tbl0()))

def body(+c: U32, +reps: U32) -> IO(Unit):
  do IO<Unit>:
    +total : U32 = asize(c)
    +words : U32 = U32.div(U32.mul(c, gg()), 4)
    +o : U32 = sbase(c)
    a : Array<U32> = Array.new(U32, depth_for(total), 0)
    a1 : Array<U32> = fill_fb(a, words)
    a2 : Array<U32> = fill_set(a1, kk(), c, o)
    a3 : Array<U32> = lp(U32.to_nat(U32.mul(reps, gg())), 0, c, o, a2)
    IO.print("C=" ++ U32.show(c) ++ " G=" ++ U32.show(gg())
             ++ " k=" ++ U32.show(kk()) ++ " iters="
             ++ U32.show(U32.mul(reps, gg())))
    IO.print("chk " ++ U32.show(checksum(a3)))

def pickarg(m: Maybe<&2, U32>, +d: U32) -> U32:
  match m:
    case None{}:
      d
    case Some{+v}:
      v

def arg1(rest: List<&1, String>, +d: U32) -> U32:
  match rest:
    case Nil{}:
      d
    case Con{h, _}:
      pickarg(U32.read(h), d)

def arg2(rest: List<&1, String>, +d: U32) -> U32:
  match rest:
    case Nil{}:
      d
    case Con{_, t}:
      arg1(t, d)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<&1, String> <- IO.args()
    +m : U32 = arg1(List.tail(&1, String, args), 5000400)
    body(U32.div(m, 10000), U32.mod(m, 10000))
