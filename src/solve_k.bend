# The exact solver, with greedy root seeding, Pass-1 root presorting, and
# round-robin parallel root chunking.
#
# For a candidate list of at least three words, `solve_chunked` first runs
# `Greedy.root_prepare` on a single root buffer: it presorts the usable root
# guesses by their Pass-1 depth-two lower bound (`n + 2*m - k`) and seeds an
# initial valid upper bound `b0` from up to five greedy(lb) rollouts starting
# at the lowest-bound root guesses.
#
# When `d = 0` (`k <= 1`), the sorted root queue runs directly on the existing
# buffer from `b0`. When `d >= 1` (`k >= 2`), the sorted root queue is dealt
# round-robin (`deal_even` / `deal_odd`) into `2^d <= k` balanced chunks, every
# chunk starts from the shared valid bound `b0` with its own feedback-table
# buffer, and the chunk results are folded with `SolveRef.better`.
#
# The search is pure: `solve_k(guesses, candidates, k)` takes the chunk count
# as an ordinary argument and has no ambient state. `Solve.solve` is its
# `k = 1` instance, and `K.solve_k` is valid and optimal for every `k`.
import Base
import ./feedback.bend as Feedback
import ./tree.bend as Tree
import ./groups.bend as Groups
import ./solve_ref.bend as SolveRef
import ./solve_fast.bend as SolveFast
import ./greedy.bend as Greedy

# The split depth: the largest `d` with `2^d <= k`, and at least zero.
def depth_go(fuel: Nat, +k: Nat, +d: Nat) -> Nat:
  match fuel:
    case 0n:
      d
    case 1n+p:
      match k:
        case 0n:
          d
        case 1n+q:
          match q:
            case 0n:
              d
            case 1n+r:
              depth_go(p, Nat.div(k, 2n), Nat.add(1n, d))

def depth_of(+k: Nat) -> Nat:
  depth_go(k, k, 0n)

# The best result over the root guesses `rgs`, starting from the valid initial
# bound `b0` with the full guess list `glist_G` available at every child node.
def chunk_best(+fuel: Nat, +rgs: +List<Greedy.RootGuess>,
               +glist_G: SolveFast.GList, +cs: +List<SolveFast.CWord>,
               +n: Nat, +nodup: Bool, +floor: Nat, +inf: Nat,
               +b0: SolveRef.Best, buf: SolveFast.Buf5) -> SolveRef.Best:
  SolveFast.step_res_best(
    SolveFast.step(fuel, Greedy.glist_of_rgs(rgs), 0n, Nil{},
      glist_G, cs, n, nodup, floor, inf, Nil{}, Nil{}, 0n, b0,
      SolveFast.dummy_step_zero(), False{},
      SolveFast.is_floor_hit(nodup, floor, b0),
      SolveFast.GuessRes{Nil{}, buf}))

# Round-robin split into even- and odd-indexed root guesses so every chunk
# receives the same mix of low-bound and high-bound guesses.
def deal_even(+xs: +List<Greedy.RootGuess>) -> +List<Greedy.RootGuess>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      match t:
        case Nil{}:
          x <> Nil{}
        case Con{y, rest}:
          x <> deal_even(rest)

def deal_odd(+xs: +List<Greedy.RootGuess>) -> +List<Greedy.RootGuess>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      match t:
        case Nil{}:
          Nil{}
        case Con{y, rest}:
          y <> deal_odd(rest)

# Split `rgs` round-robin `d` times and evaluate the leaves in parallel from
# the seeded bound `b0`. An empty or one-word chunk stops splitting early.
def par_chunks(+d: Nat, +rgs: +List<Greedy.RootGuess>,
               +fuel: Nat, +G: +List<+List<Nat>>, +glist_G: SolveFast.GList,
               +cs: +List<SolveFast.CWord>, +S: +List<+List<Nat>>, +n: Nat,
               +nodup: Bool, +floor: Nat, +inf: Nat,
               +b0: SolveRef.Best) -> +List<SolveRef.Best>:
  match d:
    case 0n:
      chunk_best(fuel, rgs, glist_G, cs, n, nodup, floor, inf, b0,
        SolveFast.mk_buf_tbl(nodup, G, S, n)) <> Nil{}
    case 1n+p:
      match rgs:
        case Nil{}:
          Nil{}
        case Con{w, rest}:
          match rest:
            case Nil{}:
              chunk_best(fuel, rgs, glist_G, cs, n, nodup, floor, inf, b0,
                SolveFast.mk_buf_tbl(nodup, G, S, n)) <> Nil{}
            case Con{w2, rest2}:
              +left = deal_even(rgs)
              +right = deal_odd(rgs)
              ra rb = par_chunks(p, left, fuel, G, glist_G, cs, S, n,
                nodup, floor, inf, b0) par_chunks(p, right, fuel, G, glist_G,
                cs, S, n, nodup, floor, inf, b0)
              List.append(&2, SolveRef.Best, ra, rb)

# Fold the chunk results with `SolveRef.better`.
def fold_results(+rs: +List<SolveRef.Best>, best: SolveRef.Best) -> SolveRef.Best:
  match rs:
    case Nil{}:
      best
    case Con{+r, +rest}:
      match r:
        case SolveRef.Best{+tree, +cost}:
          fold_results(rest, SolveRef.better(cost, tree, best))

def after_prep(+d: Nat, +G: +List<+List<Nat>>, +gG: SolveFast.GList,
               +cwS: +List<SolveFast.CWord>, +cs: +List<+List<Nat>>,
               +n: Nat, +nd: Bool, +fl: Nat, +inf: Nat,
               pr: Greedy.RootPrepRes) -> Maybe<Tree.Tree>:
  match d:
    case 0n:
      match pr:
        case Greedy.RootPrepRes{+b0, +rgs, buf0}:
          SolveRef.best_to_maybe(inf,
            chunk_best(n, rgs, gG, cwS, n, nd, fl, inf, b0, buf0))
    case 1n+dp:
      match pr:
        case Greedy.RootPrepRes{+b0, +rgs, buf0}:
          +rs = par_chunks(1n+dp, rgs, n, G, gG, cwS, cs, n, nd, fl, inf, b0)
          SolveRef.best_to_maybe(inf, fold_results(rs, b0))

# The seeded, presorted, chunked root for a candidate list of at least three
# words whose words are all guesses.
def solve_chunked(+G: +List<+List<Nat>>, +cs: +List<+List<Nat>>,
                  +d: Nat) -> Maybe<Tree.Tree>:
  +n : Nat = Groups.len_words(cs)
  +gcount : U32 = U32.from_nat(Groups.len_words(G))
  +inf : Nat = SolveRef.inf_of(n)
  +nd : Bool = SolveFast.no_dup_fast(cs)
  +fl : Nat = SolveFast.init_floor(n)
  +gG : SolveFast.GList = SolveFast.glist_of_guesses(G, 0, 1)
  +cwS : +List<SolveFast.CWord> = SolveFast.build_cwords(cs, G, 0, gcount)
  after_prep(d, G, gG, cwS, cs, n, nd, fl, inf,
    Greedy.root_prepare(G, gG, cwS, n, inf, SolveFast.mk_buf_tbl(nd, G, cs, n)))

# A candidate list too short to have classes keeps the direct path.
def solve_small(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
                +d: Nat) -> Maybe<Tree.Tree>:
  match C:
    case Nil{}:
      SolveFast.solve_fast_valid(G, C)
    case Con{w, t}:
      match t:
        case Nil{}:
          SolveFast.solve_fast_valid(G, C)
        case Con{w2, t2}:
          match t2:
            case Nil{}:
              SolveFast.solve_fast_valid(G, C)
            case Con{w3, t3}:
              solve_chunked(G, w <> (w2 <> (w3 <> t3)), d)

# The same input gate as the sequential solver, then the seeded root.
def solve_k_checked(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
                    +d: Nat, ok: Bool) -> Maybe<Tree.Tree>:
  match ok:
    case False{}:
      None{}
    case True{}:
      solve_small(G, C, d)

# The solver with a pure chunk count `k`. `k <= 1` runs one seeded chunk on
# the root buffer; `k >= 2` splits the presorted root guesses round-robin into
# `2^d <= k` chunks starting from the same seeded bound.
def solve_k(+guesses: +List<+List<Nat>>,
            +candidates: +List<+List<Nat>>, +k: Nat) -> Maybe<Tree.Tree>:
  solve_k_checked(guesses, candidates, depth_of(k),
    SolveFast.all_in_fast(candidates, guesses))
