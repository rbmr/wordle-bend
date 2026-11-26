# Microbenchmark of the real distinct-response walk (src/prof.bend dn_go) in
# isolation, with the same packed feedback layout the solver uses.
#
# Why: the solver spends ~93% of its N=500 runtime in the branching-factor
# chain, which is this loop. This program calls the *same* machine with a
# synthetic table so the per-(guess,candidate) cost can be compared with the
# identical loop in C (dnbench.c beside this file) and with the published
# Rust cost per visit.
#
# Usage: dnbench [c] [reps]      (default 500 400; gg=14855, k=40 fixed)
#
# Layout (independent of geo.bend, so the allocation is only the fb table):
#   [0 .. c*gg/4)          packed feedback words, 4 responses per U32
#   [pb .. pb+1024)        dn_go's count cells (pb+224), touched list (pb+480),
#                          result cell (pb+736)
#   [o .. o+k)             the bucket's candidate ids
import Base
import ../src/geo.bend as G
import ../src/prof.bend as P
import ../src/arith.bend as A

def gg() -> U32:
  14855

def kk() -> U32:
  40

def pbase(+c: U32) -> U32:
  U32.add(U32.div(U32.mul(c, gg()), 4), 8)

def sbase(+c: U32) -> U32:
  U32.add(pbase(c), 1024)

def asize(+c: U32) -> U32:
  U32.add(sbase(c), 64)

def depth_for(+size: U32) -> Nat:
  Nat.add(U32.log2(U32.sub(size, 1)), 1n)

# Fill n words with an LCG pattern.
def fbgo(+fuel: Nat, +i: U32, +n: U32, +seed: U32,
         r: Array<U32> & U32) -> Array<U32>:
  match fuel:
    case 0n:
      (a2, _) = r
      a2
    case 1n+f:
      (a2, _) = r
      +s = U32.add(U32.mul(seed, 1664525), 1013904223)
      +i2 = U32.inc(i)
      +done = A.ge01(i2, n)
      a3 = Array.set(U32, a2, i, s)
      fbgo(f, i2, n, s, Array.get(U32, a3, A.sel(done, 0, i2)))

def fill_fb(a: Array<U32>, +n: U32) -> Array<U32>:
  fbgo(U32.to_nat(n), 0, n, 12345, Array.get(U32, a, 0))

# The bucket's candidate ids: distinct values below c.
def stgo(+fuel: Nat, +i: U32, +k: U32, +c: U32, +base: U32,
         r: Array<U32> & U32) -> Array<U32>:
  match fuel:
    case 0n:
      (a2, _) = r
      a2
    case 1n+f:
      (a2, _) = r
      +v = U32.mod(U32.add(U32.mul(i, 37), 11), c)
      +i2 = U32.inc(i)
      +done = A.ge01(i2, k)
      a3 = Array.set(U32, a2, U32.add(base, i), v)
      stgo(f, i2, k, c, base, Array.get(U32, a3, U32.add(base, A.sel(done, 0, i2))))

def fill_set(a: Array<U32>, +k: U32, +c: U32, +base: U32) -> Array<U32>:
  stgo(U32.to_nat(k), 0, k, c, base, Array.get(U32, a, base))

# One dn_go invocation per iteration (what dcount does, with pb passed in), for
# `left` iterations, cycling the guess index over [0, gg).
def lp(+fuel: Nat, +g: U32, +c: U32, +o: U32, +pb: U32,
       a: Array<U32>) -> Array<U32>:
  match fuel:
    case 0n:
      a
    case 1n+f:
      a2 = P.dn_go(Nat.add(Nat.mul(U32.to_nat(kk()), 8n), 80n), 0, 0, 0,
                   U32.mul(g, c), o, kk(), 0, 0, pb, Array.get(U32, a, o))
      +g2 = U32.inc(g)
      +wrap = A.ge01(g2, gg())
      +g3 = U32.mul(U32.sub(1, wrap), g2)
      lp(f, g3, c, o, pb, a2)

# One checksum over 129 cells so the array is consumed once: 64 fb words, the
# result cell, then 64 count cells. acc = acc*31 + v.
def chk(+fuel: Nat, +i: U32, +acc: U32, +pb: U32,
        r: Array<U32> & U32) -> U32:
  match fuel:
    case 0n:
      (a2, _) = r
      acc
    case 1n+f:
      (a2, +v) = r
      +i2 = U32.inc(i)
      +b1 = A.sel(A.ge01(i, 64), U32.add(pb, 736), i)
      +b2 = A.sel(A.ge01(i, 65), U32.add(U32.add(pb, 224), U32.sub(i, 65)), b1)
      +c1 = A.sel(A.ge01(i2, 64), U32.add(pb, 736), i2)
      +c2 = A.sel(A.ge01(i2, 65), U32.add(U32.add(pb, 224), U32.sub(i2, 65)), c1)
      chk(f, i2, U32.add(U32.mul(acc, 31), v), pb,
          Array.get(U32, a2, A.sel(A.eq01(i2, 129), b2, c2)))

def checksum(a: Array<U32>, +pb: U32) -> U32:
  chk(129n, 0, 0, pb, Array.get(U32, a, 0))

def body(+c: U32, +reps: U32) -> IO(Unit):
  do IO<Unit>:
    +total : U32 = asize(c)
    +words : U32 = U32.div(U32.mul(c, gg()), 4)
    +pb : U32 = pbase(c)
    +o : U32 = sbase(c)
    a : Array<U32> = Array.new(U32, depth_for(total), 0)
    a1 : Array<U32> = fill_fb(a, words)
    a2 : Array<U32> = fill_set(a1, kk(), c, o)
    a3 : Array<U32> = lp(U32.to_nat(U32.mul(reps, gg())), 0, c, o, pb, a2)
    IO.print("C=" ++ U32.show(c) ++ " G=" ++ U32.show(gg())
             ++ " k=" ++ U32.show(kk()) ++ " iters="
             ++ U32.show(U32.mul(reps, gg())))
    IO.print("chk " ++ U32.show(checksum(a3, pb)))

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

# One argv number encodes both (c, reps): c*10000 + reps.
def main() -> IO(Unit):
  do IO<Unit>:
    args : List<&1, String> <- IO.args()
    +m : U32 = arg1(List.tail(&1, String, args), 5000400)
    body(U32.div(m, 10000), U32.mod(m, 10000))
