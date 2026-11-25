import Base
import ./geo.bend as G
import ./arith.bend as A
import ./tab.bend as T
import ./heur.bend as H

# ------------------------------------------------------------------- input ---

def chunk_size() -> U32:
  1000000

def max_chunks() -> Nat:
  64n

def open_result(path: String, opened: Result<&1, &1, U32 & String, File>) -> IO(File):
  match opened:
    case Done{file}:
      IO.pure(File, file)
    case Fail{e}:
      (code, message) = e
      IO.die(File, 1, "error: cannot open " ++ path ++ ": " ++ message)

def close_then_die(file: File, +message: String) -> IO(List<&2, String>):
  do IO<List<&2, String>>:
    Unit <- File.close(file)
    IO.die(List<&2, String>, 1, message)

type Reading is Type:
  NeedRead{file: File}
  HaveChunk{pair: File & Result<&1, &1, U32 & String, String>}

def read_loop(fuel: Nat, +acc: List<&2, String>, +path: String,
              state: Reading) -> IO(List<&2, String>):
  match fuel:
    case 0n:
      IO.die(List<&2, String>, 1, "error: " ++ path ++ " is too large to read")
    case 1n+rest:
      match state:
        case NeedRead{file}:
          IO.bind(File & Result<&1, &1, U32 & String, String>, List<&2, String>,
                  File.read(file, chunk_size()),
                  pair => read_loop(rest, acc, path, HaveChunk{pair}))
        case HaveChunk{pair}:
          (file, result) = pair
          match result:
            case Fail{e}:
              (code, message) = e
              close_then_die(file, "error: cannot read " ++ path ++ ": " ++ message)
            case Done{+text}:
              match text:
                case SNil{}:
                  do IO<List<&2, String>>:
                    Unit <- File.close(file)
                    IO.pure(List<&2, String>, acc)
                case SCon{h, t}:
                  read_loop(rest, SCon{h, t} <> acc, path, NeedRead{file})

def read_file(+path: String) -> IO(String):
  do IO<String>:
    opened : Result<&1, &1, U32 & String, File> <- File.open(path, "r")
    file : File <- open_result(path, opened)
    chunks : List<&2, String> <- read_loop(max_chunks(), Nil{}, path, NeedRead{file})
    return String.concat(List.reverse(&2, String, chunks))

# ------------------------------------------------------------------ checks ---

# Sum of `n` cells from `base` modulo 2^32. One read per call: the next read is
# the argument of the recursive call.
def sum_go(fuel: Nat, +i: U32, +n: U32, +base: U32, +acc: U32,
           r: Array<U32> & U32) -> U32:
  match fuel:
    case 0n:
      (a2, _) = r
      acc
    case 1n+p:
      (a2, +v) = r
      +i2 = U32.inc(i)
      +done = A.eq01(i2, n)
      r2 = Array.get(U32, a2, U32.add(base, A.sel(done, 0, i2)))
      sum_go(p, i2, n, base, U32.add(acc, v), r2)

def region_sum(a: Array<U32>, +base: U32, +n: U32) -> U32:
  sum_go(U32.to_nat(n), 0, n, base, 0, Array.get(U32, a, base))

def build_all(+c: U32, +gg: U32, +gtext: String, +ctext: String,
              a: Array<U32>) -> Array<U32>:
  a2 = T.fill_c(ctext, c, gg, T.fill_g(gtext, c, gg, a))
  a3 = T.fill_zob(c, gg, a2)
  a4 = T.fill_hh_init(c, gg, a3)
  a5 = T.fill_hh(c, gg, a4)
  a6 = T.fill_c2g(c, gg, a5)
  T.fill_fb(c, gg, a6)

# -------------------------------------------------------------------- main ---

def depth_for(+size: U32) -> Nat:
  Nat.add(U32.log2(U32.sub(size, 1)), 1n)

def report_if(a: Array<U32>, +mode: U32, +qk: U32, +qn: U32, +b: U32,
              +n: U32, +c: U32, +gg: U32, k: U32) -> IO(Unit):
  match k:
    case 0:
      +s = region_sum(a, b, n)
      IO.print("mode=" ++ U32.show(mode) ++ " b=" ++ U32.show(b)
               ++ " n=" ++ U32.show(n) ++ " sum=" ++ U32.show(s))
    case 1:
      +qs = H.run_quick(a, qk, qn, c, gg)
      IO.print("mode=" ++ U32.show(mode) ++ " q=" ++ U32.show(qs))
    case _:
      +s = region_sum(a, U32.sub(mode, 500), 1)
      IO.print("mode=" ++ U32.show(mode) ++ " cell=" ++ U32.show(s))

def report_go(a: Array<U32>, +mode: U32, +qk: U32, +qn: U32, +b: U32, +n: U32,
              +c: U32, +gg: U32) -> IO(Unit):
  +hi5 = A.ge01(mode, 500)
  +hi4 = A.ge01(mode, 400)
  +inner = A.sel(hi5, 2, 1)
  +kind = A.sel(hi4, inner, 0)

  report_if(a, mode, qk, qn, b, n, c, gg, kind)

def mode_base(+mode: U32, +c: U32, +gg: U32) -> U32:
  +m2 = A.eq01(mode, 2)
  +m3 = A.eq01(mode, 3)
  +m4 = A.eq01(mode, 4)
  +m5 = A.eq01(mode, 5)
  +m6 = A.eq01(mode, 6)
  +m7 = A.eq01(mode, 7)
  +h5 = A.ge01(mode, 500)
  +h3 = U32.mul(A.ge01(mode, 300), U32.sub(1, h5))
  +h2 = U32.mul(A.ge01(mode, 100), U32.sub(1, h3))
  +hf = U32.mul(h2, U32.sub(1, h3))
  +hi = U32.mul(A.ge01(mode, 8), U32.sub(1, A.ge01(mode, 100)))
  U32.add(U32.mul(h5, U32.sub(mode, 500)),
    U32.add(U32.mul(h3, G.off_gcnt(c, gg)),
    U32.add(U32.mul(hf, 0),
    U32.add(U32.mul(hi, U32.mul(U32.sub(mode, 8), c)),
    U32.add(U32.mul(m2, G.off_c2g(c, gg)),
      U32.add(U32.mul(m3, G.off_z1(c, gg)),
        U32.add(U32.mul(m4, G.off_gpack(c, gg)),
          U32.add(U32.mul(m5, G.off_cpack(c, gg)),
            U32.add(U32.mul(m6, G.off_cmask(c, gg)),
              U32.mul(m7, G.off_cat(c, gg)))))))))))

def mode_n(+mode: U32, +c: U32, +gg: U32, +total: U32) -> U32:
  +m0 = A.eq01(mode, 0)
  +m1 = A.eq01(mode, 1)
  +m2 = A.eq01(mode, 2)
  +m3 = A.eq01(mode, 3)
  +m4 = A.eq01(mode, 4)
  +m5 = A.eq01(mode, 5)
  +m6 = A.eq01(mode, 6)
  +m7 = A.eq01(mode, 7)
  +h5 = A.ge01(mode, 500)
  +h3 = U32.mul(A.ge01(mode, 300), U32.sub(1, h5))
  +h2 = U32.mul(A.ge01(mode, 100), U32.sub(1, h3))
  +hf = U32.mul(h2, U32.sub(1, h3))
  +hi = U32.mul(A.ge01(mode, 8), U32.sub(1, A.ge01(mode, 100)))
  U32.add(U32.mul(h5, 1),
    U32.add(U32.mul(h3, U32.sub(mode, 300)),
    U32.add(U32.mul(hf, U32.sub(mode, 100)),
    U32.add(U32.mul(hi, c),
    U32.add(U32.mul(m0, total),
      U32.add(U32.mul(m1, U32.mul(c, gg)),
        U32.add(U32.mul(m2, c),
          U32.add(U32.mul(m3, c),
            U32.add(U32.mul(m4, gg),
              U32.add(U32.mul(m5, c),
                U32.add(U32.mul(m6, c),
                  U32.mul(m7, U32.mul(5, c)))))))))))))

def run(+mode: U32, +c: U32, +gg: U32, +gtext: String, +ctext: String) -> IO(Unit):
  do IO<Unit>:
    +total : U32 = G.total_size(c, gg)
    IO.print("C=" ++ U32.show(c) ++ " G=" ++ U32.show(gg)
             ++ " cells=" ++ U32.show(total))
    a : Array<U32> = Array.new(U32, depth_for(total), 0)
    a1 : Array<U32> = build_all(c, gg, gtext, ctext, a)
    +qk : U32 = U32.div(U32.sub(mode, 400), 32)
    +qn : U32 = U32.mod(U32.sub(mode, 400), 32)
    +b : U32 = mode_base(mode, c, gg)
    +n : U32 = mode_n(mode, c, gg, total)
    report_go(a1, mode, qk, qn, b, n, c, gg)

def go5(+gtext: String, +ctext: String, +c: U32, +gg: U32,
        m: Maybe<&2, U32>) -> IO(Unit):
  match m:
    case None{}:
      run(0, c, gg, gtext, ctext)
    case Some{+m2}:
      run(m2, c, gg, gtext, ctext)

def go4(+gtext: String, +ctext: String, +c: U32, +gg: U32,
        +mode: String) -> IO(Unit):
  go5(gtext, ctext, c, gg, U32.read(mode))

def go3b(+gtext: String, +ctext: String, +c: U32, +gg: U32,
         rest: List<&1, String>) -> IO(Unit):
  match rest:
    case Nil{}:
      run(0, c, gg, gtext, ctext)
    case Con{m, _}:
      go4(gtext, ctext, c, gg, m)

def go2(rest: List<&1, String>, +gtext: String, +gn: U32) -> IO(Unit):
  match rest:
    case Nil{}:
      IO.print("usage: solver <guesses> <candidates>")
    case Con{cand_path, more}:
      do IO<Unit>:
        +ctext : String <- read_file(cand_path)
        +cn : U32 = T.word_count(ctext)
        go3b(gtext, ctext, cn, gn, more)

def go1(rest: List<&1, String>) -> IO(Unit):
  match rest:
    case Nil{}:
      IO.print("usage: solver <guesses> <candidates>")
    case Con{gpath, more}:
      do IO<Unit>:
        +gtext : String <- read_file(gpath)
        +gn : U32 = T.word_count(gtext)
        go2(more, gtext, gn)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<&1, String> <- IO.args()
    go1(List.tail(&1, String, args))
