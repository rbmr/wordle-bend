import Base
import ./main.bend as M
import ./geo.bend as G
import ./tab.bend as T
import ./heur.bend as H
import ./sec.bend as S
import ./engine.bend as E
import ./arith.bend as A

# Slice-2 driver: build the tables, compute the root maximum branching factor
# exactly (as Rust's compute_max_branching_factor does), fill the capacity
# table, run the step machine, print the cost and the counters.
#
# Usage: search <guesses> <candidates> [beta0]

def setdep() -> U32:
  127

def mxcell(+c: U32, +gg: U32) -> U32:
  U32.add(G.off_qgen(c, gg), 620)

def prn(r: Array<U32> & U32, +tag: String) -> IO(Array<U32>):
  (a, v) = r
  do IO<Array<U32>>:
    Unit <- IO.print(tag ++ " " ++ U32.show(v))
    IO.pure(Array<U32>, a)

def depth_for(+size: U32) -> Nat:
  Nat.add(U32.log2(U32.sub(size, 1)), 1n)

def fill_ids(+fuel: Nat, +i: U32, +base: U32, a: Array<U32>) -> Array<U32>:
  match fuel:
    case 0n:
      a
    case 1n+p:
      fill_ids(p, U32.inc(i), base, Array.set(U32, a, U32.add(base, i), i))

# max over all guesses of the number of distinct responses on the root set.
# ph 0: over check. 1: count. 2: done. 3: pk read.
def maxk_go(+fuel: Nat, +ph: U32, +g: U32, +mx: U32, +gen: U32, +c: U32,
            +gg: U32, r: Array<U32> & U32) -> Array<U32>:
  match fuel:
    case 0n:
      (a2, _) = r
      Array.set(U32, a2, mxcell(c, gg), mx)
    case 1n+f:
      match ph:
        case 0:
          (a2, _) = r
          +over = A.ge01(g, gg)
          maxk_go(f, A.sel(over, 2, 1), g, mx, gen, c, gg, Array.get(U32, a2, 0))
        case 1:
          (a2, _) = r
          +sb = S.set_at(setdep(), c, gg)
          +gen2 = U32.add(gen, 1024)
          a1 = S.cnt(g, sb, c, 4294967295, gen2, setdep(), c, gg, a2)
          maxk_go(f, 3, g, mx, gen2, c, gg, Array.get(U32, a1, S.pkcell(c, gg)))
        case 2:
          (a2, _) = r
          Array.set(U32, a2, mxcell(c, gg), mx)
        case _:
          (a2, +v) = r
          maxk_go(f, 0, U32.inc(g), U32.max(mx, U32.and(v, 4095)), gen, c, gg,
                  Array.get(U32, a2, 0))

def maxk(+c: U32, +gg: U32, a: Array<U32>) -> Array<U32>:
  +sb = S.set_at(setdep(), c, gg)
  a1 = fill_ids(U32.to_nat(c), 0, sb, a)
  maxk_go(Nat.add(Nat.mul(U32.to_nat(gg), Nat.mul(U32.to_nat(c), 4n)),
                  Nat.mul(U32.to_nat(gg), 256n)),
          0, 0, 0, 0, c, gg, Array.get(U32, a1, 0))

# maxk writes its result into a scratch cell; `after_max` reads it and runs the
# search. (A read can only be destructured by a callee whose parameter it is.)
def after_max(p: Array<U32> & U32, +c: U32, +gg: U32, +beta0: U32) -> IO(Unit):
  (a, +mx) = p
  do IO<Unit>:
    Unit <- IO.print("C=" ++ U32.show(c) ++ " G=" ++ U32.show(gg)
                     ++ " maxk=" ++ U32.show(mx))
    +sb : U32 = S.set_at(0, c, gg)
    a2 : Array<U32> = fill_ids(U32.to_nat(c), 0, sb,
                               H.cap_fill(U32.max(mx, 2), c, gg, a))
    a2h : Array<U32> = S.hset(a2, sb, c, E.hsh1(0, c, gg), E.hsh2(0, c, gg),
                              c, gg)
    a2b : Array<U32> = E.step(Nat.add(Nat.mul(U32.to_nat(c), 8192n),
                                      Nat.mul(U32.to_nat(gg), 1024n)),
                              0, c, gg, sb, c, beta0, U32.max(mx, 2), 0, beta0,
                              0, 0, 0, 0, 0, 0, U32.mul(gg, 1024), 0, 0, 0, 0,
                              0, Nil{}, Array.get(U32, a2h, 0))
    +cm : U32 = G.off_qgen(c, gg)
    a3 : Array<U32> <- prn(Array.get(U32, a2b, U32.add(cm, 609)), "cost")
    a3b : Array<U32> <- prn(Array.get(U32, a3, U32.add(cm, 610)), "states")
    a4 : Array<U32> <- prn(Array.get(U32, a3b, U32.add(cm, 611)), "guesses")
    a5 : Array<U32> <- prn(Array.get(U32, a4, U32.add(cm, 612)), "hits")
    a6 : Array<U32> <- prn(Array.get(U32, a5, U32.add(cm, 613)), "pruned")
    IO.pure(Unit, Unit{})

def run(+c: U32, +gg: U32, +beta0: U32, a: Array<U32>) -> IO(Unit):
  after_max(Array.get(U32, maxk(c, gg, a), mxcell(c, gg)), c, gg, beta0)

def go4(+gp: String, +cp: String, +beta0: U32) -> IO(Unit):
  do IO<Unit>:
    +gtext : String <- M.read_file(gp)
    +ctext : String <- M.read_file(cp)
    +c : U32 = T.word_count(ctext)
    +gg : U32 = T.word_count(gtext)
    total : U32 = G.total_size(c, gg)
    a : Array<U32> = Array.new(U32, depth_for(total), 0)
    a1 : Array<U32> = M.build_all(c, gg, gtext, ctext, a)
    run(c, gg, U32.max(beta0, U32.mul(c, U32.inc(c))), a1)

def betm(m: Maybe<&2, U32>, +gp: String, +cp: String) -> IO(Unit):
  match m:
    case Some{+b}:
      go4(gp, cp, b)
    case None{}:
      go4(gp, cp, 0)

def bet(bs: String, +gp: String, +cp: String) -> IO(Unit):
  betm(U32.read(bs), gp, cp)

def go3(r2: List<&1, String>, +gp: String, +cp: String) -> IO(Unit):
  match r2:
    case Nil{}:
      go4(gp, cp, 0)
    case Con{bs, _}:
      bet(bs, gp, cp)

def go2(r1: List<&1, String>, +gp: String) -> IO(Unit):
  match r1:
    case Nil{}:
      IO.print("usage: search <guesses> <candidates> [beta0]")
    case Con{cp, r2}:
      go3(r2, gp, cp)

def go1(args: List<&1, String>) -> IO(Unit):
  match args:
    case Nil{}:
      IO.print("usage: search <guesses> <candidates> [beta0]")
    case Con{gp, r1}:
      go2(r1, gp)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<&1, String> <- IO.args()
    go1(List.tail(&1, String, args))
