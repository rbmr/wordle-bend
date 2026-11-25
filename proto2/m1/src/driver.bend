# Search driver: build the tables, compute the root maximum branching factor,
# fill the capacity table, hash the root set, run the step machine and print the
# cost with the counters. Used by src/main.bend (the pc2 entry point) and by
# search_main.bend (local experiments with an explicit beta).
import Base
import ./geo.bend as G
import ./tab.bend as T
import ./heur.bend as H
import ./sec.bend as S
import ./engine.bend as E
import ./arith.bend as A

def setdep() -> U32:
  127

# DEBUG: dump the root bucket trace (0 = absent).
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

# One pass over every guess on the root set: max distinct responses (Rust's
# compute_max_branching_factor) and the smallest sum of squares (the greedy
# guess choice). Both are packed into one cell: mx | minsq << 8.
# ph 0: over check. 1: count. 2: done. 3: pk read. 4: sum-of-squares read.
def maxk_go(+fuel: Nat, +ph: U32, +g: U32, +mx: U32, +gen: U32, +c: U32,
            +gg: U32, +sq: U32, r: Array<U32> & U32) -> Array<U32>:
  match fuel:
    case 0n:
      (a2, _) = r
      Array.set(U32, a2, mxcell(c, gg), mx)
    case 1n+f:
      match ph:
        case 0:
          (a2, _) = r
          +over = A.ge01(g, gg)
          maxk_go(f, A.sel(over, 2, 1), g, mx, gen, c, gg, sq,
                  Array.get(U32, a2, 0))
        case 1:
          (a2, _) = r
          +sb = S.set_at(setdep(), c, gg)
          a1 = S.cnt(g, sb, c, 4294967295, setdep(), c, gg, a2)
          maxk_go(f, 3, g, mx, gen, c, gg, sq,
                  Array.get(U32, a1, S.pkcell(c, gg)))
        case 2:
          (a2, _) = r
          Array.set(U32, a2, mxcell(c, gg), U32.add(mx, U32.mul(sq, 256)))
        case 3:
          (a2, +v) = r
          maxk_go(f, 4, g, U32.max(mx, U32.and(v, 4095)), gen, c, gg, sq,
                  Array.get(U32, a2, S.sqcell(c, gg)))
        case _:
          (a2, +v) = r
          maxk_go(f, 0, U32.inc(g), mx, gen, c, gg,
                  U32.min(U32.max(sq, 1), U32.max(v, 1)),
                  Array.get(U32, a2, 0))

def maxk(+c: U32, +gg: U32, a: Array<U32>) -> Array<U32>:
  +sb = S.set_at(setdep(), c, gg)
  a1 = fill_ids(U32.to_nat(c), 0, sb, a)
  maxk_go(Nat.add(Nat.mul(U32.to_nat(gg), Nat.mul(U32.to_nat(c), 8n)),
                  Nat.mul(U32.to_nat(gg), 512n)),
          0, 0, 0, 0, c, gg, 65535, Array.get(U32, a1, 0))

# maxk writes its result into a scratch cell; `after_max` reads it and runs the
# search. (A read can only be destructured by a callee whose parameter it is.)
def after_max(p: Array<U32> & U32, +c: U32, +gg: U32, +beta0: U32,
              +dbg: U32) -> IO(Unit):
  (a, +pk) = p
  +mx = U32.and(pk, 255)
  +sq = U32.shrn(pk, 8n)
  +ub = U32.add(c, U32.div(U32.add(sq, c), 2))
  +beta1 = U32.max(beta0, U32.mul(c, U32.inc(c)))
  +beta2 = U32.min(beta1, ub)
  do IO<Unit>:
    Unit <- IO.print("C=" ++ U32.show(c) ++ " G=" ++ U32.show(gg)
                     ++ " maxk=" ++ U32.show(mx) ++ " ub=" ++ U32.show(ub)
                     ++ " beta=" ++ U32.show(beta2))
    +sb : U32 = S.set_at(0, c, gg)
    a2 : Array<U32> = fill_ids(U32.to_nat(c), 0, sb,
                               H.cap_fill(U32.max(mx, 2), c, gg, a))
    a2h : Array<U32> = S.hset(a2, sb, c, E.hsh1(0, c, gg), E.hsh2(0, c, gg),
                              c, gg)
    a2b : Array<U32> = E.step(Nat.add(Nat.mul(U32.to_nat(c), 65536n),
                                      Nat.mul(U32.to_nat(gg), 16384n)),
                              c, gg, 0, 0, sb, c, beta2, U32.max(mx, 2), 0,
                              beta2, 0, 0, 0, 0, 4294967295, 0, 0, 0, 0, 0, 0,
                              0, 0, beta2, U32.mul(gg, 1024), 0, 0, 0, 0, 0,
                              Nil{}, Array.get(U32, a2h, 0))
    +cm : U32 = G.off_qgen(c, gg)
    a3 : Array<U32> <- prn(Array.get(U32, a2b, U32.add(cm, 609)), "cost")
    a3b : Array<U32> <- prn(Array.get(U32, a3, U32.add(cm, 610)), "states")
    a4 : Array<U32> <- prn(Array.get(U32, a3b, U32.add(cm, 611)), "guesses")
    a5 : Array<U32> <- prn(Array.get(U32, a4, U32.add(cm, 612)), "hits")
    a6 : Array<U32> <- prn(Array.get(U32, a5, U32.add(cm, 613)), "pruned")
    IO.pure(Unit, Unit{})

def run(+c: U32, +gg: U32, +beta0: U32, a: Array<U32>) -> IO(Unit):
  after_max(Array.get(U32, maxk(c, gg, a), mxcell(c, gg)), c, gg, beta0, 1)

