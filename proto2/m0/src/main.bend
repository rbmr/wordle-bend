# M0: inner-loop cost of the guess-scan partition.
#
# For every one of the 14855 guesses, histogram n candidates with a flat
# feedback table and a flat count array, then reset the touched counts.
# One flat Array<U32> holds the feedback table, the counts and the touched
# list; every step of the scan consumes one read pair of that same array and
# issues the next read, so no record is built per candidate.
# Args: <n> <reps>.
import Base

def gcount() -> U32:
  14855

def gcount_nat() -> Nat:
  14855n

def depth_for(+size: U32) -> Nat:
  Nat.add(U32.log2(U32.sub(size, 1)), 1n)

# Region starts. `tbase` depends on n.
def tbl_size(+n: U32) -> U32:
  U32.mul(gcount(), n)

def cnt_base(+n: U32) -> U32:
  tbl_size(n)

def touch_base(+n: U32) -> U32:
  U32.add(cnt_base(n), 256)

def total_size(+n: U32) -> U32:
  U32.add(touch_base(n), n)

# --- table fill (setup, outside the measured inner loop) --------------------

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

# Reset the touched counts; r is the read of touch[j].
def reset_go(+fuel: Nat, +j: U32, +sq: U32, +acc: U32, +n: U32,
             r: Array<U32> & U32) -> RowRes:
  match fuel:
    case 0n:
      (a, _) = r
      RowRes{a, acc}
    case 1n+p:
      match p:
        case 0n:
          (a, +f) = r
          a2 = Array.set(U32, a, U32.add(cnt_base(n), f), 0)
          RowRes{a2, U32.add(acc, sq)}
        case 1n+q:
          (a, +f) = r
          a2 = Array.set(U32, a, U32.add(cnt_base(n), f), 0)
          reset_go(p, U32.inc(j), sq, acc, n,
                   Array.get(U32, a2, U32.add(touch_base(n), U32.inc(j))))

# phase=True: r is the feedback read; phase=False: r is the count read.
# rem counts the candidates left including the current one; last = rem == 1.
def scan(+fuel: Nat, +phase: Bool, +last: Bool, +rem: U32, +i: U32,
         +n: U32, +base: U32, +f: U32, +sq: U32, +nt: U32, +acc: U32,
         r: Array<U32> & U32) -> RowRes:
  match fuel:
    case 0n:
      (a, _) = r
      RowRes{a, acc}
    case 1n+p:
      match phase:
        case True{}:
          (a, +fb) = r
          scan(p, False{}, last, rem, i, n, base, fb, sq, nt, acc,
               Array.get(U32, a, U32.add(cnt_base(n), fb)))
        case False{}:
          match last:
            case True{}:
              (a, +old) = r
              +sq2 = U32.add(sq, U32.add(U32.mul(old, 2), 1))
              a2 = Array.set(U32, a, U32.add(cnt_base(n), f), U32.inc(old))
              a3 = Array.set(U32, a2, U32.add(touch_base(n), nt), f)
              reset_go(U32.to_nat(U32.inc(nt)), 0, sq2, acc, n,
                       Array.get(U32, a3, touch_base(n)))
            case False{}:
              (a, +old) = r
              +sq2 = U32.add(sq, U32.add(U32.mul(old, 2), 1))
              a2 = Array.set(U32, a, U32.add(cnt_base(n), f), U32.inc(old))
              a3 = Array.set(U32, a2, U32.add(touch_base(n), nt), f)
              +nt2 = U32.inc(nt)
              +rem2 = U32.sub(rem, 1)
              scan(p, True{}, U32.is_eq(rem2, 1), rem2, U32.inc(i), n, base, f,
                   sq2, nt2, acc,
                   Array.get(U32, a3, U32.add(base, U32.inc(i))))

# Consume the first feedback read, then scan at the count phase.
def row_start(+fuel: Nat, +n: U32, +base: U32, +sq: U32, +nt: U32,
              +acc: U32, r: Array<U32> & U32) -> RowRes:
  (a, +fb) = r
  scan(fuel, False{}, U32.is_eq(n, 1), n, 0, n, base, fb, sq, nt, acc,
       Array.get(U32, a, U32.add(cnt_base(n), fb)))

# --- all rows ---------------------------------------------------------------

def rows_go(+fuel: Nat, +g: U32, +n: U32, st: RowRes) -> RowRes:
  match fuel:
    case 0n:
      st
    case 1n+p:
      match st:
        case RowRes{a, +acc}:
          +nn = U32.to_nat(n)
          +rest = Nat.sub(Nat.add(nn, nn), 1n)
          +base = U32.mul(g, n)
          rows_go(p, U32.mod(U32.inc(g), gcount()), n,
                  row_start(rest, n, base, 0, 0, acc,
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
  print_res(rows_go(rows, 0, n, RowRes{a2, 0}))

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
