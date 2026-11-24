# The exact solver, with the root guess list split into chunks.
#
# The root guess list of the bound-pruned search is dealt into `2^d` contiguous
# segments, each segment is evaluated by the fast search machine (`SolveFast.step`)
# from the neutral accumulator over only its own guesses, with the full guess
# list still available at every child node, and the chunk results are folded in
# guess order with the reference `better`. That fold keeps the first strictly
# cheapest result, which is the sequential root's tie-break, so the folded tree
# is the sequential root's tree: the chunk split only changes how much work each
# part of the root loop does without a shared bound, never which tree wins.
#
# The chunk count is `2^d <= k`, where `k` is the thread count the runtime was
# started with. `k <= 1` runs the sequential root unchanged, so a single-thread
# run is exactly the un-split solver.
#
# The search is pure: `solve_k(guesses, candidates, k)` takes the chunk count as
# an ordinary argument and has no ambient state. `Solve.solve` is its `k = 1`
# instance, and `K.solve_k` is valid and optimal for every `k`, so the CLI may
# pick `k` from the runtime's thread count.
import Base
import ./feedback.bend as Feedback
import ./tree.bend as Tree
import ./groups.bend as Groups
import ./solve_ref.bend as SolveRef
import ./solve_fast.bend as SolveFast

# The split depth: the largest `d` with `2^d <= k`, and at least zero. The
# recursion is bounded by `k` so the termination checker accepts it: every step
# halves the bound.
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

# The best result over the words `seg`, all of them from the guess list `G`, in
# their guess-list order, starting at row `off` of the feedback table. The
# search runs from the neutral accumulator with the full `G` as the child guess
# list, so only the root loop is restricted. A leaf owns its buffer because a
# `Buf5` holds arrays and cannot be shared between lanes.
def chunk_best(+fuel: Nat, +seg: +List<+List<Nat>>, +off: U32,
               +G: +List<+List<Nat>>, +glist_G: SolveFast.GList,
               +cs: +List<SolveFast.CWord>, +S: +List<+List<Nat>>, +n: Nat,
               +nodup: Bool, +floor: Nat, +inf: Nat,
               buf: SolveFast.Buf5) -> SolveRef.Best:
  +b0 = SolveFast.dummy_inf(inf)
  SolveFast.step_res_best(
    SolveFast.step(fuel, SolveFast.glist_of_guesses(seg, off, 1), 0n, Nil{},
      glist_G, cs, n, nodup, floor, inf, Nil{}, Nil{}, 0n, b0,
      SolveFast.dummy_step_zero(), False{},
      SolveFast.is_floor_hit(nodup, floor, b0),
      SolveFast.GuessRes{Nil{}, buf}))

# Split `seg` into halves `d` times and evaluate the leaves in parallel, left
# half first. `off` is the row of `seg`'s first word in the guess list, so each
# leaf addresses its feedback-table rows directly. An empty or one-word segment
# is a leaf whatever the remaining depth: the extra levels would only produce
# empty chunks. The leaves come back in guess-list order.
def par_chunks(+d: Nat, +seg: +List<+List<Nat>>, +off: U32,
               +fuel: Nat, +G: +List<+List<Nat>>, +glist_G: SolveFast.GList,
               +cs: +List<SolveFast.CWord>, +S: +List<+List<Nat>>, +n: Nat,
               +nodup: Bool, +floor: Nat, +inf: Nat) -> +List<SolveRef.Best>:
  match d:
    case 0n:
      chunk_best(fuel, seg, off, G, glist_G, cs, S, n, nodup, floor, inf,
        SolveFast.mk_buf_tbl(nodup, G, S, n)) <> Nil{}
    case 1n+p:
      match seg:
        case Nil{}:
          Nil{}
        case Con{w, rest}:
          match rest:
            case Nil{}:
              chunk_best(fuel, seg, off, G, glist_G, cs, S, n, nodup, floor,
                inf, SolveFast.mk_buf_tbl(nodup, G, S, n)) <> Nil{}
            case Con{w2, rest2}:
              +len : Nat = Groups.len_words(seg)
              +half : Nat = Nat.div(len, 2n)
              +left : +List<+List<Nat>> = List.take(&2, +List<Nat>, seg, half)
              +right : +List<+List<Nat>> = List.drop(&2, +List<Nat>, seg, half)
              +off2 : U32 = U32.add(off, U32.from_nat(half))
              ra rb = par_chunks(p, left, off, fuel, G, glist_G, cs, S, n,
                nodup, floor, inf) par_chunks(p, right, off2, fuel, G, glist_G,
                cs, S, n, nodup, floor, inf)
              List.append(&2, SolveRef.Best, ra, rb)

# Fold the chunk results in guess order: a strictly cheaper result replaces the
# accumulator, so the first minimal result wins, exactly as in the sequential
# root loop.
def fold_results(+rs: +List<SolveRef.Best>, best: SolveRef.Best) -> SolveRef.Best:
  match rs:
    case Nil{}:
      best
    case Con{+r, +rest}:
      match r:
        case SolveRef.Best{+tree, +cost}:
          fold_results(rest, SolveRef.better(cost, tree, best))

# The chunked root for a candidate list of at least three words whose words are
# all guesses. The table, the candidate wrappers and the floor are the ones the
# sequential root uses; only the root guess list is split.
def solve_chunked(+G: +List<+List<Nat>>, +cs: +List<+List<Nat>>,
                  +d: Nat) -> Maybe<Tree.Tree>:
  +n : Nat = Groups.len_words(cs)
  +gcount : U32 = U32.from_nat(Groups.len_words(G))
  +inf : Nat = SolveRef.inf_of(n)
  +nd : Bool = SolveFast.no_dup_fast(cs)
  +b0 : SolveRef.Best = SolveFast.dummy_inf(inf)
  +fl : Nat = SolveFast.init_floor(n)
  +gG : SolveFast.GList = SolveFast.glist_of_guesses(G, 0, 1)
  +cwS : +List<SolveFast.CWord> = SolveFast.build_cwords(cs, G, 0, gcount)
  +rs : +List<SolveRef.Best> =
    par_chunks(d, G, 0, n, G, gG, cwS, cs, n, nd, fl, inf)
  SolveRef.best_to_maybe(inf, fold_results(rs, b0))

# A candidate list too short to have classes keeps the direct path: it has no
# root loop to split, the sequential solver already answers in one step.
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

# The same input gate as the sequential solver, then the split root.
def solve_k_checked(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
                    +d: Nat, ok: Bool) -> Maybe<Tree.Tree>:
  match ok:
    case False{}:
      None{}
    case True{}:
      solve_small(G, C, d)

# The solver with a pure chunk count. `k <= 1` is the sequential solver byte for
# byte; `k >= 2` splits the root into `2^d <= k` chunks.
def solve_k(+guesses: +List<+List<Nat>>,
            +candidates: +List<+List<Nat>>, +k: Nat) -> Maybe<Tree.Tree>:
  match k:
    case 0n:
      SolveFast.solve(guesses, candidates)
    case 1n+p:
      match p:
        case 0n:
          SolveFast.solve(guesses, candidates)
        case 1n+q:
          solve_k_checked(guesses, candidates, depth_of(k),
            SolveFast.all_in_fast(candidates, guesses))
