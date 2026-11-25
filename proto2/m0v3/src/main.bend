# M0 v3: generation-stamped counts.
#
# Same partition loop as m0, but a count cell holds gen*1024 + count. A stale
# cell (from an earlier generation) is detected without a branch: its
# (cell - genbase) wraps above 2^31, so (diff >> 31) is 1 and the count is 0.
# There is no touched list and no reset pass. Args: <n> <reps>.
# Requires rows = reps*14855 < 2^22 (genbase must stay below 2^32).
import Base

def gcount() -> U32:
  14855

def gcount_nat() -> Nat:
  14855n

def depth_for(+size: U32) -> Nat:
  Nat.add(U32.log2(U32.sub(size, 1)), 1n)

def cnt_base(+n: U32) -> U32:
  U32.mul(gcount(), n)

def total_size(+n: U32) -> U32:
  U32.add(cnt_base(n), 256)

# --- table fill (setup) -----------------------------------------------------

def fill_row(+fuel: Nat, +i: U32, +base: U32, +g: U32,
             a: Array<U32>) -> Array<U32>:
  match fuel:
    case 0n:
      a
    case 1n+p:
      +v = U32.and(U32.add(U32.mul(g, 37), U32.mul(i, 11)), 255)
      fill_row(p, U32.inc(i), base, g,
               Array.set(U32, a, U32.add(base, i), v))

def fill_all(+fuel: Nat, +g: U32, +n: U32, a: Array<U32>) -> Array<U32>:
  match fuel:
    case 0n:
      a
    case 1n+p:
      fill_all(p, U32.inc(g), n,
               fill_row(U32.to_nat(n), 0, U32.mul(g, n), g, a))

# --- one row ----------------------------------------------------------------

type RowRes is Type:
  RowRes{a: Array<U32>, acc: U32}

# phase=True: r is the feedback read; phase=False: r is the count read.
def scan(+fuel: Nat, +phase: Bool, +last: Bool, +rem: U32, +i: U32,
         +n: U32, +base: U32, +f: U32, +sq: U32, +genb: U32, +acc: U32,
         +coff: U32, r: Array<U32> & U32) -> RowRes:
  match fuel:
    case 0n:
      (a, _) = r
      RowRes{a, acc}
    case 1n+p:
      match phase:
        case True{}:
          (a, +fb) = r
          scan(p, False{}, last, rem, i, n, base, fb, sq, genb, acc, coff,
               Array.get(U32, a, U32.add(coff, fb)))
        case False{}:
          match last:
            case True{}:
              (a, +cell) = r
              +diff = U32.sub(cell, genb)
              +fresh = U32.sub(1, U32.shrn(diff, 31n))
              +old = U32.mul(diff, fresh)
              +sq2 = U32.add(sq, U32.add(U32.mul(old, 2), 1))
              +newc = U32.add(genb, U32.inc(old))
              a2 = Array.set(U32, a, U32.add(coff, f), newc)
              RowRes{a2, U32.add(acc, sq2)}
            case False{}:
              (a, +cell) = r
              +diff = U32.sub(cell, genb)
              +fresh = U32.sub(1, U32.shrn(diff, 31n))
              +old = U32.mul(diff, fresh)
              +sq2 = U32.add(sq, U32.add(U32.mul(old, 2), 1))
              +newc = U32.add(genb, U32.inc(old))
              a2 = Array.set(U32, a, U32.add(coff, f), newc)
              +rem2 = U32.sub(rem, 1)
              scan(p, True{}, U32.is_eq(rem2, 1), rem2, U32.inc(i), n, base, f,
                   sq2, genb, acc, coff,
                   Array.get(U32, a2, U32.add(base, U32.inc(i))))

def row_start(+fuel: Nat, +n: U32, +base: U32, +sq: U32, +genb: U32,
              +acc: U32, +coff: U32, r: Array<U32> & U32) -> RowRes:
  (a, +fb) = r
  scan(fuel, False{}, U32.is_eq(n, 1), n, 0, n, base, fb, sq, genb, acc, coff,
       Array.get(U32, a, U32.add(coff, fb)))

# --- all rows ---------------------------------------------------------------

def rows_go(+fuel: Nat, +g: U32, +n: U32, +genb: U32,
            st: RowRes) -> RowRes:
  match fuel:
    case 0n:
      st
    case 1n+p:
      match st:
        case RowRes{a, +acc}:
          +nn = U32.to_nat(n)
          +rest = Nat.sub(Nat.add(nn, nn), 1n)
          +base = U32.mul(g, n)
          +coff = cnt_base(n)
          +genb2 = U32.add(genb, 1024)
          rows_go(p, U32.mod(U32.inc(g), gcount()), n, genb2,
                  row_start(rest, n, base, 0, genb2, acc, coff,
                            Array.get(U32, a, base)))

# --- entry ------------------------------------------------------------------

def print_res(st: RowRes) -> IO(Unit):
  match st:
    case RowRes{a, +acc}:
      IO.print(U32.show(acc))

def bench(+n: U32, +reps: U32) -> IO(Unit):
  +d = depth_for(total_size(n))
  a = Array.new(U32, d, 0)
  a2 = fill_all(gcount_nat(), 0, n, a)
  +rows = Nat.mul(U32.to_nat(reps), gcount_nat())
  print_res(rows_go(rows, 0, n, 0, RowRes{a2, 0}))

def go_reps(a: Maybe<&2, U32>, +n: U32) -> IO(Unit):
  match a:
    case None{}:
      IO.print("bad reps")
    case Some{+reps}:
      bench(reps, n)

def go_n(a: Maybe<&2, U32>, +rs: String) -> IO(Unit):
  match a:
    case None{}:
      IO.print("bad n")
    case Some{+n}:
      go_reps(U32.read(rs), n)

def run3(rest: List<String>, +rs: String) -> IO(Unit):
  match rest:
    case Nil{}:
      IO.print("usage: m0 <n> <reps>")
    case Con{+ns, _}:
      go_n(U32.read(ns), rs)

def run2(rest: List<String>) -> IO(Unit):
  match rest:
    case Nil{}:
      IO.print("usage: m0 <n> <reps>")
    case Con{+rs, more}:
      run3(more, rs)

def run(args: List<String>) -> IO(Unit):
  match args:
    case Nil{}:
      IO.print("usage: m0 <n> <reps>")
    case Con{_p, rest}:
      run2(rest)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    run(args)
