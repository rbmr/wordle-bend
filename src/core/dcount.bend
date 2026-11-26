# Certified distinct-response count over a packed feedback table.
#
# This is the prototype's `prof.dcount` slice (`proto2/m1/src/prof.bend`): for
# one guess row it walks a candidate list, reads the packed response code of
# each candidate, and counts how many distinct codes occurred. The prototype
# wrote a count array and a touched list into a scratch region; here the mark
# buffer is the solver's already-proved generation-stamped `SeenTree` buffer.
# Only the table read is new: it goes through `packed.peek`.
#
# The candidate list is `+List<CWord>` (the copyable kind), so a benchmark can
# run the same input many times without rebuilding it. The machine shape is the
# prototype's: one recursive call per candidate, the table and the buffer are
# threaded through the state, `n` is the number of candidates seen and `k` is
# the number of distinct response codes.
import Base
import ../feedback.bend as Feedback
import ../solve_fast.bend as SolveFast
import ./packed.bend as Packed

# Words of a copyable candidate list, for the specification.
def words(+S: +List<SolveFast.CWord>) -> +List<+List<Nat>>:
  match S:
    case Nil{}:
      Nil{}
    case Con{cw, rest}:
      match cw:
        case SolveFast.CWord{ci, grow, w}:
          w <> words(rest)

def count(+S: +List<SolveFast.CWord>) -> Nat:
  match S:
    case Nil{}:
      0n
    case Con{cw, rest}:
      Nat.add(1n, count(rest))

# The group list the count buffer represents: every candidate is added,
# including one equal to the guess (the reference `groups_build` drops that one;
# the count over the whole set must not). This is proof-only.
def build(+g: +List<Nat>, +S: +List<SolveFast.CWord>,
          +acc: +List<SolveFast.FGroup>) -> +List<SolveFast.FGroup>:
  match S:
    case Nil{}:
      acc
    case Con{cw, rest}:
      match cw:
        case SolveFast.CWord{ci, grow, w}:
          build(g, rest,
            SolveFast.fgroup_add_fast(w, Feedback.feedback(g, w), acc))

type DState is Type:
  DState{seen: Array<Nat>, tbl: Array<U32>, +n: Nat, +k: Nat}

def dc_branch(seen2: Array<Nat>, tbl2: Array<U32>, +gen: Nat,
              +n: Nat, +k: Nat, same: Bool) -> DState:
  match same:
    case True{}:
      DState{seen2, tbl2, Nat.add(1n, n), k}
    case False{}:
      DState{seen2, tbl2, Nat.add(1n, n), Nat.add(1n, k)}

def dc_swap(tbl2: Array<U32>, sw: Array<Nat> & Nat,
            +gen: Nat, +n: Nat, +k: Nat) -> DState:
  (seen2, +old) = sw
  dc_branch(seen2, tbl2, gen, n, k, Nat.is_eq(old, gen))

def dc_step(r: Array<U32> & U32, seen: Array<Nat>,
            +gen: Nat, +n: Nat, +k: Nat) -> DState:
  (tbl2, +code) = r
  dc_swap(tbl2, Array.swap(Nat, seen, code, gen), gen, n, k)

def dc_go(+row: U32, +S: +List<SolveFast.CWord>, +gen: Nat,
          st: DState) -> DState:
  match S:
    case Nil{}:
      st
    case Con{cw, rest}:
      match cw:
        case SolveFast.CWord{+ci, grow, w}:
          match st:
            case DState{seen, tbl, +n, +k}:
              dc_go(row, rest, gen,
                dc_step(Packed.peek(tbl, U32.add(row, ci)), seen, gen, n, k))

# Start from an empty set and an empty buffer.
def dcount(+row: U32, +S: +List<SolveFast.CWord>, +gen: Nat,
           seen: Array<Nat>, tbl: Array<U32>) -> DState:
  dc_go(row, S, gen, DState{seen, tbl, 0n, 0n})

def res_k(r: DState) -> Nat:
  match r:
    case DState{seen2, tbl2, +n, +k}:
      k

# The count as a plain `Nat`, for callers that only need the branching factor.
def dcount_n(+row: U32, +S: +List<SolveFast.CWord>, +gen: Nat,
             seen: Array<Nat>, tbl: Array<U32>) -> Nat:
  res_k(dcount(row, S, gen, seen, tbl))
