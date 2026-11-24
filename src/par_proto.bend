# Prototype: parallel root for the bound-pruned solver. NOT PROVED, and not
# wired into the command line (src/solve.bend still delegates to
# src/solve_fast.bend, which is what the laws talk about).
#
# The root guess list is dealt round robin into `2^d` chunks, each chunk runs
# the fast search machine (`SolveFast.step`) from the neutral accumulator over
# only its own guesses with its own candidate-first root list, and the chunk
# results are folded by (cost, index of the root guess in the guess list). The
# fold therefore returns the same tree as the sequential root loop, which keeps
# the first strictly cheapest guess. Each lane builds its own copy of the
# reusable buffer (`mk_buf_tbl`), because a `Buf5` holds arrays and is affine;
# cloning a built table instead would save three of the four table builds.
#
# Why it is not shipped: the optimality proof at the root
# (`FOpt.root_ge3_dup`, `proofs/fast_opt.bend`) proves the result of `step` over
# the *whole* guess list is at least as cheap as `FS.FS.ref_run_at(fuel, inf, G,
# S)`, that is, as the cheapest tree over every guess in `G`. A chunk tries only
# a sub-list, so `FOpt.job_res_b` does not apply to it. Chunking needs a new
# specification ("the cheapest tree over this sub-list") plus a composition
# lemma over the deal, and neither exists yet.
import Base
import ./feedback.bend as Feedback
import ./tree.bend as Tree
import ./groups.bend as Groups
import ./solve_ref.bend as SolveRef
import ./solve_fast.bend as SolveFast

# The best result of the chunk that tries only the guesses `gs`, from the
# neutral accumulator, under the root's candidate list.
def chunk_best(+fuel: Nat, +gs: SolveFast.GList,
               +glist_G: SolveFast.GList, +S: +List<SolveFast.CWord>,
               +n: Nat, +nodup: Bool, +floor: Nat, +inf: Nat,
               buf: SolveFast.Buf5) -> SolveRef.Best:
  +b0 = SolveFast.dummy_inf(inf)
  SolveFast.step_res_best(
    SolveFast.step(fuel, gs, 0n, Nil{}, glist_G, S, n, nodup, floor, inf,
      Nil{}, Nil{}, 0n, b0, SolveFast.dummy_step_zero(), False{},
      SolveFast.is_floor_hit(nodup, floor, b0),
      SolveFast.GuessRes{Nil{}, buf}))

# Fold the per-chunk results with the reference `better`, keeping the chunk
# whose root guess comes first in the guess list: that is the sequential
# tie-break, because the sequential root loop keeps the first strictly cheapest
# guess. With interleaved chunks the fold order is no longer the guess order, so
# the comparison is on (cost, index in G), encoded as `cost * big + index` with
# `big` larger than any index.
def tree_idx(+t: Tree.Tree, +G: +List<+List<Nat>>) -> Nat:
  match t:
    case Tree.Node{+g, +kids}:
      U32.to_nat(SolveFast.find_grow(g, G, 1))

def key_of(+r: SolveRef.Best, +G: +List<+List<Nat>>, +big: Nat) -> SolveRef.Best:
  match r:
    case SolveRef.Best{+tree, +cost}:
      SolveRef.Best{tree, Nat.add(Nat.mul(cost, big), tree_idx(tree, G))}

def keys_of(+rs: +List<SolveRef.Best>, +G: +List<+List<Nat>>, +big: Nat,
            +acc: +List<SolveRef.Best>) -> +List<SolveRef.Best>:
  match rs:
    case Nil{}:
      acc
    case Con{+r, +rest}:
      keys_of(rest, G, big, key_of(r, G, big) <> acc)

def fold_results(+rs: +List<SolveRef.Best>, best: SolveRef.Best) -> SolveRef.Best:
  match rs:
    case Nil{}:
      best
    case Con{+r, +rest}:
      match r:
        case SolveRef.Best{+tree, +cost}:
          fold_results(rest, SolveRef.better(cost, tree, best))

# Reverse a word list (the alternating filter below accumulates in reverse).
def rev_go(+xs: +List<+List<Nat>>, +acc: +List<+List<Nat>>) -> +List<+List<Nat>>:
  match xs:
    case Nil{}:
      acc
    case Con{+x, +rest}:
      rev_go(rest, x <> acc)

# The words at positions `i` of `xs` with `i % 2 == par`, in order.
def alt_at(+xs: +List<+List<Nat>>, +i: U32, +par: U32,
           +acc: +List<+List<Nat>>) -> +List<+List<Nat>>:
  match xs:
    case Nil{}:
      acc
    case Con{+w, +rest}:
      +j = U32.inc(i)
      alt_at(rest, j, par,
        Feedback.Bool.case(+List<+List<Nat>>, U32.is_eq(U32.mod(i, 2), par),
          w <> acc, acc))

def alt(+par: U32, +xs: +List<+List<Nat>>) -> +List<+List<Nat>>:
  rev_go(alt_at(xs, 0, par, Nil{}), Nil{})

# Split `seg` into `2^d` interleaved chunks and evaluate the leaves in
# parallel. `off` is the index of `seg`'s first word in the root guess list and
# `stride` the distance between consecutive words of `seg`; together they give
# each guess its row offset in the feedback table. Deals round robin, so every
# chunk gets a mixture of cheap and expensive root guesses. A leaf builds its
# own buffer.
def par_split(+d: Nat, +seg: +List<+List<Nat>>, +off: U32, +stride: U32,
              +fuel: Nat, +G: +List<+List<Nat>>, +glist_G: SolveFast.GList,
              +cs: +List<+List<Nat>>, +S: +List<SolveFast.CWord>, +n: Nat,
              +nodup: Bool, +floor: Nat, +inf: Nat) -> +List<SolveRef.Best>:
  match d:
    case 0n:
      chunk_best(fuel, SolveFast.glist_of_guesses(seg, off, stride), glist_G,
        S, n, nodup, floor, inf, SolveFast.mk_buf_tbl(nodup, G, cs, n)) <> Nil{}
    case 1n+p:
      +stride2 = U32.add(stride, stride)
      +off2 = U32.add(off, stride)
      ra rb = par_split(p, alt(0, seg), off, stride2, fuel, G, glist_G, cs, S, n, nodup, floor, inf) par_split(p, alt(1, seg), off2, stride2, fuel, G, glist_G, cs, S, n, nodup, floor, inf)
      List.append(&2, SolveRef.Best, ra, rb)

# Decode a keyed result back to its cost.
def keyed_decode(best: SolveRef.Best, +big: Nat, +inf: Nat) -> Maybe<Tree.Tree>:
  match best:
    case SolveRef.Best{+tree, +key}:
      SolveRef.best_to_maybe(inf, SolveRef.Best{tree, Nat.div(key, big)})

# Fold the keyed chunk results and decode the cost.
def keyed_fold(+rs: +List<SolveRef.Best>, +G: +List<+List<Nat>>, +big: Nat,
               +inf: Nat) -> Maybe<Tree.Tree>:
  keyed_decode(fold_results(keys_of(rs, G, big, Nil{}),
    SolveRef.Best{Tree.Node{Nil{}, Nil{}}, Nat.mul(inf, big)}), big, inf)

def par_solve_ge3(+G: +List<+List<Nat>>, +cs: +List<+List<Nat>>,
                  +d: Nat) -> Maybe<Tree.Tree>:
  +n = Groups.len_words(cs)
  +gcount = U32.from_nat(Groups.len_words(G))
  +inf = SolveRef.inf_of(n)
  +nd = SolveFast.no_dup_fast(cs)
  +b0 = SolveFast.dummy_inf(inf)
  +fl = SolveFast.init_floor(n)
  +gG = SolveFast.glist_of_guesses(G, 0, 1)
  +cwS = SolveFast.build_cwords(cs, G, 0, gcount)
  +big = Nat.add(Groups.len_words(G), 1n)
  keyed_fold(par_split(d, G, 0, 1, n, G, gG, cs, cwS, n, nd, fl, inf), G, big,
    inf)

def solve_d(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +d: Nat) -> Maybe<Tree.Tree>:
  match C:
    case Nil{}:
      SolveFast.solve_fast(G, C)
    case Con{+w, +t}:
      match t:
        case Nil{}:
          SolveFast.solve_fast(G, C)
        case Con{+w2, +t2}:
          match t2:
            case Nil{}:
              SolveFast.solve_fast(G, C)
            case Con{+w3, +t3}:
              par_solve_ge3(G, w <> (w2 <> (w3 <> t3)), d)

# The chunk count is 2^2 = 4, one per core of the test machine.
def solve(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>) -> Maybe<Tree.Tree>:
  solve_d(G, C, 2n)

