import Base
import ./main.bend as M
import ./geo.bend as G
import ./tab.bend as T
import ./heur.bend as H
import ./sec.bend as S
import ./driver.bend as D

# Slice-2 driver: build the tables, compute the root maximum branching factor
# exactly (as Rust's compute_max_branching_factor does), fill the capacity
# table, run the step machine, print the cost and the counters.
#
# Usage: search <guesses> <candidates> [beta0]

def go4(+gp: String, +cp: String, +beta0: U32) -> IO(Unit):
  do IO<Unit>:
    +gtext : String <- M.read_file(gp)
    +ctext : String <- M.read_file(cp)
    +c : U32 = T.word_count(ctext)
    +gg : U32 = T.word_count(gtext)
    total : U32 = G.total_size(c, gg)
    a : Array<U32> = Array.new(U32, D.depth_for(total), 0)
    a1 : Array<U32> = M.build_all(c, gg, gtext, ctext, a)
    D.run(c, gg, U32.max(beta0, U32.mul(c, U32.inc(c))), a1)

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
