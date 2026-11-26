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
import ./greedy.bend as R
import ./arith.bend as A

def setdep() -> U32:
  127

# DEBUG: dump the root bucket trace (0 = absent).
# Sum of the first `n` cells (a debug check of the feedback table).
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

# ---------------------------------------------------------- parallel root ---
#
# Rust's solve_parallel_depth2 splits the buckets of the root guess across
# threads with a shared atomic beta. Safe Bend has no shared writable array, so
# the shared state is replaced by copies: the probe stops the state after the
# phase-2 tuple sort, four copies walk one quarter of the tuples each with the
# same beta, and the results are merged (min for the value, sum for the
# counters). No bound is shared, so each lane prunes less than the sequential
# search would; the value is still exact because a lane returns the exact value
# whenever it finds one below beta, and the other lanes return only bounds.
#
# The lane encoding lives in `mode`: bit 2 marks a parallel worker, bits 3.. its
# lane, low two bits the scan (1 = phase 1, 2 = phase 2). A sequential state has
# mode 1/2 and therefore no filter.

def fuel_for(+c: U32, +gg: U32) -> Nat:
  Nat.add(Nat.mul(U32.to_nat(c), 65536n), Nat.mul(U32.to_nat(gg), 16384n))

def lane_mode(+lane: U32) -> U32:
  U32.add(6, U32.mul(8, lane))

# One lane worker: resume the probe state at the tuple walk.
def runlane(+lane: U32, +c: U32, +gg: U32, +ss: U32, +beta: U32,
            +pmk: U32, +gen: U32, a: Array<U32>) -> Array<U32>:
  E.step(fuel_for(c, gg), c, gg, 0, 190, ss, c, beta, pmk, 0, beta, 0, 0, 0,
         0, 4294967295, 0, 0, lane_mode(lane), 0, 0, 0, 0, 0, beta, gen, 0,
         0, 0, 0, 0, Nil{}, Array.get(U32, a, 0))

# Cell of the worker result block: 609 cost, 610..613 the four counters.
def rescell(+i: U32, +c: U32, +gg: U32) -> U32:
  U32.add(U32.add(G.off_qgen(c, gg), 609), i)

# Probe counters, written by phase 178 into cells the workers never touch.
def basecell(+i: U32, +c: U32, +gg: U32) -> U32:
  U32.add(U32.add(G.off_qgen(c, gg), 738), i)

# mg_go folds five worker result cells of the source array into the destination:
# the cost (i = 0) by min, the counters (i = 1..4) by sum. The pair alternates
# between a source cell and a destination cell; `o` is the other array, which is
# the one the *next* phase reads. ph 0: pair = src[i], o = dst. ph 1: pair =
# dst[i], o = src. The terminal phase returns `o`, which is the destination.
def mg_go(+fuel: Nat, +ph: U32, +i: U32, +acc: U32, +c: U32, +gg: U32,
          o: Array<U32>, p: Array<U32> & U32) -> Array<U32>:
  match fuel:
    case 0n:
      (a2, _) = p
      a2
    case 1n+f:
      match ph:
        case 0:
          (s2, +v) = p
          mg_go(f, 1, i, v, c, gg, s2, Array.get(U32, o, rescell(i, c, gg)))
        case 1:
          (d2, +old) = p
          +idx = rescell(i, c, gg)
          +is0 = A.eq01(i, 0)
          +sum = U32.add(old, acc)
          +mn = A.sel(A.lt01(acc, old), acc, old)
          a3 = Array.set(U32, d2, idx, A.sel(is0, mn, sum))
          +i2 = U32.inc(i)
          +done = A.ge01(i2, 5)
          mg_go(f, A.sel(done, 9, 0), i2, 0, c, gg, a3,
                Array.get(U32, o, A.sel(done, 0, rescell(i2, c, gg))))
        case _:
          (a2, _) = p
          o

def fold5(dst: Array<U32>, src: Array<U32>, +c: U32, +gg: U32) -> Array<U32>:
  mg_go(Nat.add(Nat.mul(5n, 8n), 8n), 0, 0, 0, c, gg, dst,
        Array.get(U32, src, rescell(0, c, gg)))

# Add the probe counters (738..741) to the counter cells 610..613. The workers
# start their counters at zero, so lane 0's own counters are already there and
# the base has to be added rather than written over them. ph 0 reads base[i],
# ph 1 reads dst[i+1] and writes the sum.
def ini_go(+fuel: Nat, +ph: U32, +i: U32, +acc: U32, +c: U32, +gg: U32,
           p: Array<U32> & U32) -> Array<U32>:
  match fuel:
    case 0n:
      (a2, _) = p
      a2
    case 1n+f:
      match ph:
        case 0:
          (a2, +v) = p
          ini_go(f, 1, i, v, c, gg,
                 Array.get(U32, a2, rescell(U32.inc(i), c, gg)))
        case 1:
          (a2, +old) = p
          a3 = Array.set(U32, a2, rescell(U32.inc(i), c, gg),
                         U32.add(old, acc))
          +i2 = U32.inc(i)
          +done = A.ge01(i2, 4)
          ini_go(f, A.sel(done, 9, 0), i2, 0, c, gg,
                 Array.get(U32, a3, A.sel(done, 0, basecell(i2, c, gg))))
        case _:
          (a2, _) = p
          a2

def initcnt(a: Array<U32>, +c: U32, +gg: U32) -> Array<U32>:
  ini_go(16n, 0, 0, 0, c, gg, Array.get(U32, a, basecell(0, c, gg)))

def merge(a1: Array<U32>, a2: Array<U32>, a3: Array<U32>, a4: Array<U32>,
          +c: U32, +gg: U32) -> Array<U32>:
  b1 = initcnt(a1, c, gg)
  b2 = fold5(b1, a2, c, gg)
  b3 = fold5(b2, a3, c, gg)
  fold5(b3, a4, c, gg)

# Sequential witness: run lane 0 alone, then start the other three lanes from
# its value. This is the only bound sharing safe Bend allows without a shared
# writable array: a finished lane's value is a valid lower bound for the others'
# starting best. The three remaining lanes run on clones of the witness array.
def c3d(p: Array<U32> & Array<U32>, a1: Array<U32>, c1: Array<U32>,
        +c: U32, +gg: U32, +ss: U32, +beta: U32, +pmk: U32,
        +gen: U32) -> Array<U32>:
  (b1, d1) = p
  r1 r2 r3 = runlane(1, c, gg, ss, beta, pmk, gen, b1) runlane(2, c, gg, ss, beta, pmk, gen, c1) runlane(3, c, gg, ss, beta, pmk, gen, d1)
  merge(a1, r1, r2, r3, c, gg)

def c3c(p: Array<U32> & Array<U32>, b1: Array<U32>, +c: U32, +gg: U32,
        +ss: U32, +beta: U32, +pmk: U32, +gen: U32) -> Array<U32>:
  (a1, c1) = p
  c3d(Array.clone(U32, b1), a1, c1, c, gg, ss, beta, pmk, gen)

def c3b(p: Array<U32> & Array<U32>, +c: U32, +gg: U32, +ss: U32,
        +beta: U32, +pmk: U32, +gen: U32) -> Array<U32>:
  (a1, b1) = p
  c3c(Array.clone(U32, a1), b1, c, gg, ss, beta, pmk, gen)

# w1 receives the witness array with the witness value as the read value; it
# lowers the probe best to min(probe_best, witness) before cloning.
def w1b(p: Array<U32> & U32, +c: U32, +gg: U32, +ss: U32, +beta: U32,
        +pmk: U32, +gen: U32, +w: U32) -> Array<U32>:
  (a, +pb) = p
  a1 = Array.set(U32, a, E.pr_best(c, gg), U32.min(pb, w))
  c3b(Array.clone(U32, a1), c, gg, ss, beta, pmk, gen)

def w1(p: Array<U32> & U32, +c: U32, +gg: U32, +ss: U32, +beta: U32,
       +pmk: U32, +gen: U32) -> Array<U32>:
  (a, +w) = p
  w1b(Array.get(U32, a, E.pr_best(c, gg)), c, gg, ss, beta, pmk, gen, w)

# `par2` sees the probe's sentinel cell: MAXU means the probe never reached the
# phase-2 sort (it finished the small search itself), so its own result stands.
def par2(p: Array<U32> & U32, +c: U32, +gg: U32, +ss: U32, +beta: U32,
         +pmk: U32, +gen: U32) -> Array<U32>:
  (a2, +v) = p
  match v:
    case 4294967295:
      a2
    case _:
      w1(Array.get(U32, runlane(0, c, gg, ss, beta, pmk, gen, a2),
                   rescell(0, c, gg)),
         c, gg, ss, beta, pmk, gen)

def par(a: Array<U32>, +c: U32, +gg: U32, +ss: U32, +beta: U32,
        +pmk: U32, +gen: U32) -> Array<U32>:
  par2(Array.get(U32, a, E.pr_best(c, gg)), c, gg, ss, beta, pmk, gen)

# Sequential search: one state machine over the whole candidate set.
def seq_search(a: Array<U32>, +c: U32, +gg: U32, +beta: U32, +pmk: U32,
               +sb: U32) -> Array<U32>:
  E.step(fuel_for(c, gg), c, gg, 0, 0, sb, c, beta, pmk, 0, beta, 0, 0, 0, 0,
         4294967295, 0, 0, 0, 0, 0, 0, 0, 0, beta, U32.mul(gg, 1024), 0, 0, 0,
         0, 0, Nil{}, Array.get(U32, a, 0))

# Parallel root: the probe stops the root state after the phase-2 tuple sort,
# then four lane workers on cloned arrays walk contiguous quarters of the tuple
# list and the merge keeps the minimum value and the summed counters.
def par_search(a: Array<U32>, +c: U32, +gg: U32, +beta: U32, +pmk: U32,
               +sb: U32) -> Array<U32>:
  a0 = Array.set(U32, a, E.pr_best(c, gg), 4294967295)
  a1 = Array.set(U32, a0, E.pr_flag(c, gg), 1)
  a2 = E.step(fuel_for(c, gg), c, gg, 0, 180, sb, c, beta, pmk, 0, beta, 0, 0,
              0, 0, 4294967295, 0, 0, 0, 0, 0, 0, 0, 0, beta,
              U32.mul(gg, 1024), 0, 0, 0, 0, 0, Nil{}, Array.get(U32, a1, 0))
  par(a2, c, gg, sb, beta, pmk, U32.mul(gg, 1024))

def choose(+par: U32, a: Array<U32>, +c: U32, +gg: U32, +beta: U32,
           +pmk: U32, +sb: U32) -> Array<U32>:
  match par:
    case 1:
      par_search(a, c, gg, beta, pmk, sb)
    case _:
      seq_search(a, c, gg, beta, pmk, sb)

def after_greedy(p: Array<U32> & U32, +c: U32, +gg: U32, +mx: U32,
                 +beta0: U32, +par: U32) -> IO(Unit):
  (a, +gb) = p
  +beta = A.sel(A.eq01(gb, 4294967295), beta0, U32.min(gb, beta0))
  do IO<Unit>:
    Unit <- IO.print("greedy=" ++ U32.show(gb) ++ " beta=" ++ U32.show(beta))
    +sb : U32 = S.set_at(0, c, gg)
    +pmk : U32 = U32.max(mx, 2)
    a3 : Array<U32> = choose(par, a, c, gg, beta, pmk, sb)
    +cm : U32 = G.off_qgen(c, gg)
    a4 : Array<U32> <- prn(Array.get(U32, a3, U32.add(cm, 609)), "cost")
    a4b : Array<U32> <- prn(Array.get(U32, a4, U32.add(cm, 610)), "states")
    a5 : Array<U32> <- prn(Array.get(U32, a4b, U32.add(cm, 611)), "guesses")
    a6 : Array<U32> <- prn(Array.get(U32, a5, U32.add(cm, 612)), "hits")
    a7 : Array<U32> <- prn(Array.get(U32, a6, U32.add(cm, 613)), "pruned")
    IO.pure(Unit, Unit{})

def after_max(p: Array<U32> & U32, +c: U32, +gg: U32, +beta0: U32,
              +dbg: U32, +par: U32) -> IO(Unit):
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
    a3 : Array<U32> = R.greedy(a2h, c, gg)
    Unit <- after_greedy(Array.get(U32, a3, R.rescell(c, gg)), c, gg, mx,
                         beta2, par)
    IO.pure(Unit, Unit{})

def run(+c: U32, +gg: U32, +beta0: U32, a: Array<U32>, +par: U32) -> IO(Unit):
  after_max(Array.get(U32, maxk(c, gg, a), mxcell(c, gg)), c, gg, beta0, 1,
            par)

