import Base
import ./geo.bend as G
import ./tab.bend as T
import ./driver.bend as D

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

# ------------------------------------------------------------------- tables ---

def build_all(+c: U32, +gg: U32, +gtext: String, +ctext: String,
              a: Array<U32>) -> Array<U32>:
  a1 = T.fill_g(gtext, c, gg, a)
  a2 = T.fill_c(ctext, c, gg, a1)
  a3 = T.fill_zob(c, gg, a2)
  a4 = T.fill_hh_init(c, gg, a3)
  a5 = T.fill_hh(c, gg, a4)
  a6 = T.fill_c2g(c, gg, a5)
  T.fill_fb(c, gg, a6)

def depth_for(+size: U32) -> Nat:
  Nat.add(U32.log2(U32.sub(size, 1)), 1n)

# ------------------------------------------------------------------- main ----

def go4(+gp: String, +cp: String, +beta0: U32) -> IO(Unit):
  do IO<Unit>:
    +gtext : String <- read_file(gp)
    +ctext : String <- read_file(cp)
    +c : U32 = T.word_count(ctext)
    +gg : U32 = T.word_count(gtext)
    total : U32 = G.total_size(c, gg)
    a : Array<U32> = Array.new(U32, depth_for(total), 0)
    a1 : Array<U32> = build_all(c, gg, gtext, ctext, a)
    D.run(c, gg, beta0, a1)

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
      IO.print("usage: solver <guesses> <candidates> [beta0]")
    case Con{cp, r2}:
      go3(r2, gp, cp)

def go1(args: List<&1, String>) -> IO(Unit):
  match args:
    case Nil{}:
      IO.print("usage: solver <guesses> <candidates> [beta0]")
    case Con{gp, r1}:
      go2(r1, gp)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<&1, String> <- IO.args()
    go1(List.tail(&1, String, args))
