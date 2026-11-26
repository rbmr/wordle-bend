# Benchmark entry point for the certified distinct-response count
# (`src/core/dcount.bend`), on the same synthetic input as
# `proto2/m1/bench/dn_main.bend`:
#
#   gg = 14855 guess rows, c candidates, a fixed k = 40 candidate indices,
#   packed feedback table of c*gg/4 U32 words filled with the same LCG, and
#   reps*gg dcount calls cycling the guess row.
#
# The prototype's `dn_main` keeps the set in a flat `Array<U32>`; here the set
# is a copyable `List<&2, CWord>` built once, so the timed loop is the count
# machine only. Output is a checksum of the returned distinct counts (the
# prototype prints a checksum of table/count cells; the counts are compared
# separately against a reference on small c).
import Base
import ../src/solve_fast.bend as SolveFast
import ../src/core/packed.bend as Packed
import ../src/core/dcount.bend as DCount

def gg() -> U32:
  14855

def kk() -> U32:
  40

def depth_for(+size: U32) -> Nat:
  Nat.add(U32.log2(U32.sub(size, 1)), 1n)

# Packed table words, same LCG as the prototype.
def fill_go(+fuel: Nat, +i: U32, +n: U32, +seed: U32,
            a: Array<U32>) -> Array<U32>:
  match fuel:
    case 0n:
      a
    case 1n+f:
      +s = U32.add(U32.mul(seed, 1664525), 1013904223)
      fill_go(f, U32.inc(i), n, s, Array.set(U32, a, i, s))

def fill(a: Array<U32>, +n: U32) -> Array<U32>:
  fill_go(U32.to_nat(n), 0, n, 12345, a)

# Candidate set: ids (i*37+11) mod c, in order.
def set_go(+fuel: Nat, +i: U32, +k: U32, +c: U32,
           acc: +List<SolveFast.CWord>) -> +List<SolveFast.CWord>:
  match fuel:
    case 0n:
      acc
    case 1n+f:
      +ci = U32.mod(U32.add(U32.mul(i, 37), 11), c)
      set_go(f, U32.inc(i), k, c,
        SolveFast.CWord{ci, 0, Nil{}} <> acc)

def make_set(+k: U32, +c: U32) -> +List<SolveFast.CWord>:
  set_go(U32.to_nat(k), 0, k, c, Nil{})

# The count loop. `r` is the result of the previous `dcount` call, so the
# machine never matches a computed value. `S` is copyable and is passed to every
# call unchanged.
def lp(+fuel: Nat, r: DCount.DState, +g: U32, +gen: Nat,
       +acc: U32, +c: U32, +S: +List<SolveFast.CWord>) -> U32:
  match fuel:
    case 0n:
      acc
    case 1n+f:
      match r:
        case DCount.DState{seen2, tbl2, +n, +k}:
          +gw = U32.mod(U32.add(g, 1), gg())
          lp(f, DCount.dcount(U32.mul(gw, c), S, Nat.add(1n, gen),
                              seen2, tbl2),
             gw, Nat.add(1n, gen),
             U32.add(U32.mul(acc, 31), U32.from_nat(k)), c, S)

def body(+c: U32, +reps: U32) -> IO(Unit):
  do IO<Unit>:
    +total : U32 = U32.add(U32.div(U32.mul(c, gg()), 4), 8)
    +words : U32 = U32.div(U32.mul(c, gg()), 4)
    a : Array<U32> = Array.new(U32, depth_for(total), 0)
    a1 : Array<U32> = fill(a, words)
    seen : Array<Nat> = Array.new(Nat, 10n, 0n)
    +S : +List<SolveFast.CWord> = make_set(kk(), c)
    +iters : Nat = U32.to_nat(U32.mul(reps, gg()))
    r0 : DCount.DState = DCount.dcount(U32.from_nat(0n), S, 1n, seen, a1)
    +acc : U32 = lp(iters, r0, U32.from_nat(0n), 1n, 0, c, S)
    IO.print("C=" ++ U32.show(c) ++ " G=" ++ U32.show(gg())
             ++ " k=" ++ U32.show(kk()) ++ " iters="
             ++ U32.show(U32.mul(reps, gg())))
    IO.print("chk " ++ U32.show(acc))

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

# One argv number encodes (c, reps): c*10000 + reps.
def main() -> IO(Unit):
  do IO<Unit>:
    args : List<&1, String> <- IO.args()
    +m : U32 = arg1(List.tail(&1, String, args), 5000400)
    body(U32.div(m, 10000), U32.mod(m, 10000))
