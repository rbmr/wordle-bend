# M0: inner-loop cost of the guess-scan partition.
#
# For all 14855 guesses, partition a candidate set of size n with one flat
# feedback array `fb[g*n + i]` and one flat count array `cnt[256]`.
#
# Two loop shapes, selected by the variant argument:
#   0 = touched list: after the row, clear the touched count cells.
#   1 = generation stamp: a count cell holds gen*65536 + count; a stale cell is
#       detected arithmetically, so there is no touched list and no clear pass.
#
# Every step consumes one read of the previous step's result and issues the
# next read, so the load chain is not broken by the recursion.
# Args: <n> <reps> <variant>.
import Base

def gcount() -> U32:
  14855

def gcount_nat() -> Nat:
  14855n

def depth_for(+size: U32) -> Nat:
  Nat.add(U32.log2(U32.sub(size, 1)), 1n)

def tbl_size(+n: U32) -> U32:
  U32.mul(gcount(), n)

def touch_base(+n: U32) -> U32:
  U32.add(tbl_size(n), 256)

def cnt_base(+n: U32) -> U32:
  tbl_size(n)

def total_size_a(+n: U32) -> U32:
  U32.add(touch_base(n), n)

def total_size_b(+n: U32) -> U32:
  U32.add(tbl_size(n), 256)

# --- table fill (setup, outside the measured inner loop) --------------------

def fill_row(+fuel: Nat, +i: U32, +base: U32, +g: U32,
             a: Array<U32>) -> Array<U32>:
  match fuel:
    case 0n:
      a
    case 1n+p:
      +v = U32.and(U32.add(U32.mul(g, 37), U32.mul(i, 11)), 255)
      fill_row(p, U32.inc(i), base, g, Array.set(U32, a, U32.add(base, i), v))

def fill_all(+fuel: Nat, +g: U32, +n: U32, a: Array<U32>) -> Array<U32>:
  match fuel:
    case 0n:
      a
    case 1n+p:
      fill_all(p, U32.inc(g), n, fill_row(U32.to_nat(n), 0, U32.mul(g, n), g, a))

# --- variant 0: touched list ------------------------------------------------

type RowRes is Type:
  RowRes{a: Array<U32>, acc: U32}

# Read of touch[j]; clear that count cell with the value read.
def clr_go(+fuel: Nat, +j: U32, +sq: U32, +acc: U32, +n: U32,
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
          clr_go(p, U32.inc(j), sq, acc, n,
                 Array.get(U32, a2, U32.add(touch_base(n), U32.inc(j))))

# phase=True: r holds fb[i]; phase=False: r holds cnt[f].
def scan_a(+fuel: Nat, +phase: Bool, +last: Bool, +rem: U32, +i: U32,
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
          scan_a(p, False{}, last, rem, i, n, base, fb, sq, nt, acc,
                 Array.get(U32, a, U32.add(cnt_base(n), fb)))
        case False{}:
          match last:
            case True{}:
              (a, +old) = r
              +sq2 = U32.add(sq, U32.add(U32.mul(old, 2), 1))
              a2 = Array.set(U32, a, U32.add(cnt_base(n), f), U32.inc(old))
              a3 = Array.set(U32, a2, U32.add(touch_base(n), nt), f)
              clr_go(U32.to_nat(U32.inc(nt)), 0, sq2, acc, n,
                     Array.get(U32, a3, touch_base(n)))
            case False{}:
              (a, +old) = r
              +sq2 = U32.add(sq, U32.add(U32.mul(old, 2), 1))
              a2 = Array.set(U32, a, U32.add(cnt_base(n), f), U32.inc(old))
              a3 = Array.set(U32, a2, U32.add(touch_base(n), nt), f)
              +rem2 = U32.sub(rem, 1)
              scan_a(p, True{}, U32.is_eq(rem2, 1), rem2, U32.inc(i), n, base,
                     f, sq2, U32.inc(nt), acc,
                     Array.get(U32, a3, U32.add(base, U32.inc(i))))

def row_a(+fuel: Nat, +n: U32, +base: U32, +acc: U32,
          r: Array<U32> & U32) -> RowRes:
  (a, +fb) = r
  scan_a(fuel, False{}, U32.is_eq(n, 1), n, 0, n, base, fb, 0, 0, acc,
         Array.get(U32, a, U32.add(cnt_base(n), fb)))

def rows_a(+fuel: Nat, +g: U32, +n: U32, st: RowRes) -> RowRes:
  match fuel:
    case 0n:
      st
    case 1n+p:
      match st:
        case RowRes{a, +acc}:
          +nn = U32.to_nat(n)
          +rest = Nat.sub(Nat.add(nn, nn), 1n)
          +base = U32.mul(g, n)
          rows_a(p, U32.mod(U32.inc(g), gcount()), n,
                 row_a(rest, n, base, acc, Array.get(U32, a, base)))

# --- variant 1: generation stamp --------------------------------------------

# r holds the count cell; genb is this row's generation base (gen << 16).
def scan_b(+fuel: Nat, +phase: Bool, +last: Bool, +rem: U32, +i: U32,
           +n: U32, +base: U32, +f: U32, +sq: U32, +genb: U32, +acc: U32,
           r: Array<U32> & U32) -> RowRes:
  match fuel:
    case 0n:
      (a, _) = r
      RowRes{a, acc}
    case 1n+p:
      match phase:
        case True{}:
          (a, +fb) = r
          scan_b(p, False{}, last, rem, i, n, base, fb, sq, genb, acc,
                 Array.get(U32, a, U32.add(cnt_base(n), fb)))
        case False{}:
          match last:
            case True{}:
              (a, +cell) = r
              +diff = U32.sub(cell, genb)
              +fresh = U32.sub(1, U32.shrn(diff, 31n))
              +old = U32.mul(diff, fresh)
              +sq2 = U32.add(sq, U32.add(U32.mul(old, 2), 1))
              a2 = Array.set(U32, a, U32.add(cnt_base(n), f),
                             U32.add(genb, U32.inc(old)))
              RowRes{a2, U32.add(acc, sq2)}
            case False{}:
              (a, +cell) = r
              +diff = U32.sub(cell, genb)
              +fresh = U32.sub(1, U32.shrn(diff, 31n))
              +old = U32.mul(diff, fresh)
              +sq2 = U32.add(sq, U32.add(U32.mul(old, 2), 1))
              a2 = Array.set(U32, a, U32.add(cnt_base(n), f),
                             U32.add(genb, U32.inc(old)))
              +rem2 = U32.sub(rem, 1)
              scan_b(p, True{}, U32.is_eq(rem2, 1), rem2, U32.inc(i), n, base,
                     f, sq2, genb, acc,
                     Array.get(U32, a2, U32.add(base, U32.inc(i))))

def row_b(+fuel: Nat, +n: U32, +base: U32, +gen: U32, +acc: U32,
          r: Array<U32> & U32) -> RowRes:
  (a, +fb) = r
  scan_b(fuel, False{}, U32.is_eq(n, 1), n, 0, n, base, fb, 0,
         U32.mul(gen, 65536), acc, Array.get(U32, a, U32.add(cnt_base(n), fb)))

def rows_b(+fuel: Nat, +g: U32, +n: U32, +gen: U32, st: RowRes) -> RowRes:
  match fuel:
    case 0n:
      st
    case 1n+p:
      match st:
        case RowRes{a, +acc}:
          +nn = U32.to_nat(n)
          +rest = Nat.sub(Nat.add(nn, nn), 1n)
          +base = U32.mul(g, n)
          rows_b(p, U32.mod(U32.inc(g), gcount()), n, U32.inc(gen),
                 row_b(rest, n, base, gen, acc, Array.get(U32, a, base)))

# --- entry ------------------------------------------------------------------

def show_res(res: RowRes) -> IO(Unit):
  match res:
    case RowRes{a2, +acc}:
      IO.print(U32.show(acc))

def bench_a(+n: U32, +rows: Nat) -> IO(Unit):
  +d = depth_for(total_size_a(n))
  a = fill_all(gcount_nat(), 0, n, Array.new(U32, d, 0))
  show_res(rows_a(rows, 0, n, RowRes{a, 0}))

def bench_b(+n: U32, +rows: Nat) -> IO(Unit):
  +d = depth_for(total_size_b(n))
  a = fill_all(gcount_nat(), 0, n, Array.new(U32, d, 0))
  show_res(rows_b(rows, 0, n, 0, RowRes{a, 0}))

def pick_bench(b: Bool, +n: U32, +rows: Nat) -> IO(Unit):
  match b:
    case True{}:
      bench_a(n, rows)
    case False{}:
      bench_b(n, rows)

def bench(+n: U32, +reps: U32, +variant: U32) -> IO(Unit):
  +rows = Nat.mul(U32.to_nat(reps), gcount_nat())
  pick_bench(U32.is_eq(variant, 0), n, rows)

def go3(m: Maybe<&2, U32>, +n: U32, +reps: U32) -> IO(Unit):
  match m:
    case None{}:
      IO.print("bad variant")
    case Some{+v}:
      bench(n, reps, v)

def go2(m: Maybe<&2, U32>, +n: U32, +rs: String) -> IO(Unit):
  match m:
    case None{}:
      IO.print("bad reps")
    case Some{+reps}:
      go3(U32.read(rs), n, reps)

def go1(m: Maybe<&2, U32>, +ns: String, +rs: String) -> IO(Unit):
  match m:
    case None{}:
      IO.print("bad n")
    case Some{+n}:
      go2(U32.read(rs), n, ns)

def run3(rest: List<String>, +ns: String, +rs: String) -> IO(Unit):
  match rest:
    case Nil{}:
      IO.print("usage: m0 <n> <reps> <variant>")
    case Con{+vs, _}:
      go1(U32.read(ns), ns, rs)

def run2(rest: List<String>, +ns: String) -> IO(Unit):
  match rest:
    case Nil{}:
      IO.print("usage: m0 <n> <reps> <variant>")
    case Con{+rs, more}:
      run3(more, ns, rs)

def run(args: List<String>) -> IO(Unit):
  match args:
    case Nil{}:
      IO.print("usage: m0 <n> <reps> <variant>")
    case Con{_p, rest}:
      match rest:
        case Nil{}:
          IO.print("usage: m0 <n> <reps> <variant>")
        case Con{+ns, more}:
          run2(more, ns)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    run(args)
