# Table-backed greedy(lb) upper-bound seeding and root guess presorting.
#
# Before launching the exact search over the root guess list, `root_prepare`:
# 1. Scores every guess in `G` by its Pass-1 depth-two lower bound
#    `lb = n + 2*m - k` using `SolveFast.hist5_go` and bucket-sorts the usable
#    guesses in non-decreasing `lb` order using the 1024-slot `buckets` array,
#    then drains all 1024 slots back to `Nil{}`.
# 2. Runs up to five greedy rollouts starting from the lowest-`lb` root guesses.
#    Each rollout recursively picks the guess minimizing `lb = |S| + 2*m - k`
#    (trying candidates in `S` before the rest of `G`, stopping on the exact
#    floor) and partitions with `SolveFast.fill5_go` and `SolveFast.run_drain5`.
#
# When the 5-letter duplicate-free table buffer is absent (`NoBuf{}`),
# `root_prepare` falls back to the neutral bound and the original guess order.
import Base
import ./feedback.bend as Feedback
import ./tree.bend as Tree
import ./groups.bend as Groups
import ./solve_ref.bend as SolveRef
import ./solve_fast.bend as SolveFast

# A root guess paired with its precomputed row index in the feedback table.
type RootGuess is Data:
  RootGuess{row: U32, g: +List<Nat>}

# State of the per-node greedy guess picker (minimizing Pass-1 `lb`).
type GPickSt is Type:
  GPickOk{seen: Array<Nat>, tbl: Array<U32>, gen: Nat,
          has: Bool, brow: U32, bg: +List<Nat>, blb: Nat, hit: Bool}

def gpick_cmp(+row: U32, +g: +List<Nat>, +lb: Nat, +fl: Nat,
              seen: Array<Nat>, tbl: Array<U32>, +gen2: Nat,
              +has: Bool, +brow: U32, +bg: +List<Nat>, +blb: Nat,
              better: Bool) -> GPickSt:
  match better:
    case True{}:
      GPickOk{seen, tbl, gen2, True{}, row, g, lb, Nat.is_le(lb, fl)}
    case False{}:
      GPickOk{seen, tbl, gen2, has, brow, bg, blb,
        Bool.and(has, Nat.is_le(blb, fl))}

def gpick_usable(+row: U32, +g: +List<Nat>, +n: Nat, +fl: Nat,
                 seen: Array<Nat>, tbl: Array<U32>, +gen2: Nat,
                 +has: Bool, +brow: U32, +bg: +List<Nat>, +blb: Nat,
                 +m: Nat, +k: Nat, usable: Bool) -> GPickSt:
  match usable:
    case False{}:
      GPickOk{seen, tbl, gen2, has, brow, bg, blb,
        Bool.and(has, Nat.is_le(blb, fl))}
    case True{}:
      +lb = Nat.sub(Nat.add(n, Nat.add(m, m)), k)
      gpick_cmp(row, g, lb, fl, seen, tbl, gen2, has, brow, bg, blb,
        Bool.or(Bool.not(has), Nat.is_lt(lb, blb)))

def gpick_res(+row: U32, +g: +List<Nat>, +n: Nat, +fl: Nat, +gen: Nat,
              +has: Bool, +brow: U32, +bg: +List<Nat>, +blb: Nat,
              hr: SolveFast.Hist5Res) -> GPickSt:
  match hr:
    case SolveFast.Hist5Pruned{seen2, tbl2}:
      GPickOk{seen2, tbl2, Nat.add(1n, gen), has, brow, bg, blb,
        Bool.and(has, Nat.is_le(blb, fl))}
    case SolveFast.Hist5Ok{seen2, tbl2, +m, +k, budget}:
      gpick_usable(row, g, n, fl, seen2, tbl2, Nat.add(1n, gen), has, brow, bg,
        blb, m, k, Bool.or(Nat.is_lt(m, n), Nat.is_le(2n, k)))

def gpick_budget(+n: Nat, +has: Bool, +blb: Nat, +skip_self: Bool) -> Nat:
  match has:
    case False{}:
      n
    case True{}:
      match skip_self:
        case True{}:
          Nat.sub(Nat.sub(blb, Nat.add(n, n)), 1n)
        case False{}:
          Nat.sub(blb, Nat.add(n, n))

def gpick_loop(+gs: SolveFast.GList, +S: +List<SolveFast.CWord>, +n: Nat,
               +fl: Nat, +skip_self: Bool, st: GPickSt) -> GPickSt:
  match gs:
    case SolveFast.GEnd{}:
      st
    case SolveFast.GThen{rest}:
      match st:
        case GPickOk{seen, tbl, +gen, +has, +brow, +bg, +blb, hit}:
          +fl2 = Nat.add(n, n)
          gpick_loop(rest, S, n, fl2, True{},
            GPickOk{seen, tbl, gen, has, brow, bg, blb,
              Bool.and(has, Nat.is_le(blb, fl2))})
    case SolveFast.GTry{+row, +g, +rest}:
      match st:
        case GPickOk{seen, tbl, +gen, +has, +brow, +bg, +blb, hit}:
          match hit:
            case True{}:
              GPickOk{seen, tbl, gen, has, brow, bg, blb, True{}}
            case False{}:
              +bgt = gpick_budget(n, has, blb, skip_self)
              gpick_loop(rest, S, n, fl, skip_self,
                gpick_res(row, g, n, fl, gen, has, brow, bg, blb,
                  SolveFast.hist5_go(row, S, gen, skip_self,
                    SolveFast.Hist5Ok{seen, tbl, 0n, 0n, bgt})))

def gpick_split(+S: +List<SolveFast.CWord>, +n: Nat,
                bkts: Array<+List<SolveFast.CWord>>,
                st: GPickSt) -> SolveFast.GuessRes:
  match st:
    case GPickOk{seen, tbl, +gen, +has, +brow, +bg, +blb, hit}:
      match has:
        case False{}:
          SolveFast.GuessRes{Nil{}, SolveFast.Buf5{seen, bkts, tbl, gen}}
        case True{}:
          SolveFast.run_drain5(bg, n, seen, gen,
            SolveFast.fill5_go(brow, S, SolveFast.Fill5State{bkts, tbl, Nil{}}))

def greedy_expand(+gG: SolveFast.GList, +S: +List<SolveFast.CWord>, +n: Nat,
                  buf: SolveFast.Buf5) -> SolveFast.GuessRes:
  match buf:
    case SolveFast.NoBuf{}:
      SolveFast.GuessRes{Nil{}, SolveFast.NoBuf{}}
    case SolveFast.Buf5{seen, bkts, tbl, +gen}:
      +fl = SolveFast.init_floor(n)
      +q = SolveFast.glist_of_cwords(S, SolveFast.GThen{gG})
      gpick_split(S, n, bkts,
        gpick_loop(q, S, n, fl, False{},
          GPickOk{seen, tbl, gen, False{}, 0, Nil{}, 0n, False{}}))

def greedy_expand_forced(+row: U32, +g: +List<Nat>, +S: +List<SolveFast.CWord>,
                         +n: Nat, buf: SolveFast.Buf5) -> SolveFast.GuessRes:
  match buf:
    case SolveFast.NoBuf{}:
      SolveFast.GuessRes{Nil{}, SolveFast.NoBuf{}}
    case SolveFast.Buf5{seen, bkts, tbl, +gen}:
      SolveFast.run_drain5(g, n, seen, gen,
        SolveFast.fill5_go(row, S, SolveFast.Fill5State{bkts, tbl, Nil{}}))

type GreedyRes is Type:
  GreedyOk{tree: Tree.Tree, cost: Nat, buf: SolveFast.Buf5}
  GreedyFail{buf: SolveFast.Buf5}

def gres_buf(r: SolveFast.GuessRes) -> SolveFast.Buf5:
  match r:
    case SolveFast.GuessRes{_, buf}:
      buf

# Build one valid decision tree greedily by always expanding the guess with
# smallest Pass-1 lower bound. `phase = 2` dispatches a candidate subset `S`;
# `phase = 1` unpacks a precomputed `GuessRes`; `phase = 0` walks its items.
def greedy_step(+fuel: Nat, +phase: Nat, +cs: +List<SolveFast.Item>,
                +gG: SolveFast.GList, +S: +List<SolveFast.CWord>, +n: Nat,
                +g: +List<Nat>, +kids: +List<Tree.Child>, +sum: Nat,
                pending: GreedyRes, gres: SolveFast.GuessRes) -> GreedyRes:
  match fuel:
    case 0n:
      GreedyFail{gres_buf(gres)}
    case 1n+p:
      match phase:
        case 1n+q:
          match q:
            case 0n:
              match gres:
                case SolveFast.GuessRes{items, buf2}:
                  match items:
                    case Nil{}:
                      GreedyFail{buf2}
                    case Con{h, t}:
                      greedy_step(fuel, 0n, h <> t, gG, S, n, Nil{}, Nil{}, 0n,
                        GreedyFail{SolveFast.NoBuf{}},
                        SolveFast.GuessRes{Nil{}, buf2})
            case 1n+q2:
              match S:
                case Nil{}:
                  GreedyFail{gres_buf(gres)}
                case Con{+cw, +t}:
                  match t:
                    case Nil{}:
                      GreedyOk{Tree.Node{SolveFast.cword_w(cw), Nil{}}, 1n,
                               gres_buf(gres)}
                    case Con{+cw2, +t2}:
                      match t2:
                        case Nil{}:
                          GreedyOk{SolveFast.two_tree(SolveFast.cword_w(cw),
                                     SolveFast.cword_w(cw2)), 3n, gres_buf(gres)}
                        case Con{+cw3, +t3}:
                          match gres:
                            case SolveFast.GuessRes{_, buf}:
                              greedy_step(fuel, q, Nil{}, gG,
                                cw <> (cw2 <> (cw3 <> t3)), n, Nil{}, Nil{}, 0n,
                                GreedyFail{SolveFast.NoBuf{}},
                                greedy_expand(gG, cw <> (cw2 <> (cw3 <> t3)),
                                  n, buf))
        case 0n:
          match cs:
            case Nil{}:
              GreedyFail{gres_buf(gres)}
            case Con{item, rest}:
              match item:
                case SolveFast.Begin{g2}:
                  greedy_step(fuel, 0n, rest, gG, S, n, g2, Nil{}, 0n,
                    pending, gres)
                case SolveFast.OneItem{fb, w}:
                  greedy_step(fuel, 0n, rest, gG, S, n, g,
                    Tree.Child{fb, Tree.Node{w, Nil{}}} <> kids,
                    Nat.add(sum, 1n), pending, gres)
                case SolveFast.TwoItem{fb, w1, w2}:
                  greedy_step(fuel, 0n, rest, gG, S, n, g,
                    Tree.Child{fb, SolveFast.two_tree(w1, w2)} <> kids,
                    Nat.add(sum, 3n), pending, gres)
                case SolveFast.DoneItem{fb, tree, cost}:
                  greedy_step(fuel, 0n, rest, gG, S, n, g,
                    Tree.Child{fb, tree} <> kids,
                    Nat.add(sum, cost), pending, gres)
                case SolveFast.ClassItem{fb, words, +wlen, tail_lb}:
                  match gres:
                    case SolveFast.GuessRes{_, buf}:
                      greedy_step(fuel, 0n, rest, gG, S, n, g, kids, sum,
                        greedy_step(p, 2n, Nil{}, gG, words, wlen, Nil{}, Nil{},
                          0n, GreedyFail{SolveFast.NoBuf{}},
                          SolveFast.GuessRes{Nil{}, buf}),
                        SolveFast.GuessRes{Nil{}, SolveFast.NoBuf{}})
                case SolveFast.Add{fb, tail_lb}:
                  match pending:
                    case GreedyFail{pbuf}:
                      GreedyFail{pbuf}
                    case GreedyOk{tree, +cost, pbuf}:
                      greedy_step(fuel, 0n, rest, gG, S, n, g,
                        Tree.Child{fb, tree} <> kids, Nat.add(sum, cost),
                        GreedyFail{SolveFast.NoBuf{}},
                        SolveFast.GuessRes{Nil{}, pbuf})
                case SolveFast.End{}:
                  GreedyOk{Tree.Node{g, SolveRef.rev_kids(kids, Nil{})},
                           Nat.add(sum, n), gres_buf(gres)}

# Root Pass-1 bucket sort by `lb - init_floor(n)`, clamped to 0..1023.
def nat_min_1023_go(+x: Nat, le: Bool) -> Nat:
  match le:
    case True{}:
      x
    case False{}:
      1023n

def nat_min_1023(+x: Nat) -> Nat:
  nat_min_1023_go(x, Nat.is_le(x, 1023n))

def rsort_push_go(a: Array<+List<SolveFast.CWord>>, +half: U32, +idx: U32,
                  +cw: SolveFast.CWord, lt: Bool) ->
    Array<+List<SolveFast.CWord>>:
  match a:
    case ALeaf{+ws}:
      ALeaf{cw <> ws}
    case ANode{xs, ys}:
      match lt:
        case True{}:
          +h2 = U32.shr(half)
          ANode{rsort_push_go(xs, h2, idx, cw, U32.is_lt(idx, h2)), ys}
        case False{}:
          +h2 = U32.shr(half)
          +idx2 = U32.sub(idx, half)
          ANode{xs, rsort_push_go(ys, h2, idx2, cw, U32.is_lt(idx2, h2))}

type RSortSt is Type:
  RSortSt{seen: Array<Nat>, bkts: Array<+List<SolveFast.CWord>>, tbl: Array<U32>,
          gen: Nat}

def rsort_hist_usable(+row: U32, +g: +List<Nat>, +n: Nat, +base_lb: Nat,
                      seen: Array<Nat>, bkts: Array<+List<SolveFast.CWord>>,
                      tbl: Array<U32>, +gen2: Nat, +m: Nat, +k: Nat,
                      usable: Bool) -> RSortSt:
  match usable:
    case False{}:
      RSortSt{seen, bkts, tbl, gen2}
    case True{}:
      +lb = Nat.sub(Nat.add(n, Nat.add(m, m)), k)
      +idx_u = U32.from_nat(nat_min_1023(Nat.sub(lb, base_lb)))
      bkts2 = rsort_push_go(bkts, 512, idx_u, SolveFast.CWord{0, row, g},
                U32.is_lt(idx_u, 512))
      RSortSt{seen, bkts2, tbl, gen2}

def rsort_hist_one(+row: U32, +g: +List<Nat>, +n: Nat, +base_lb: Nat,
                   bkts: Array<+List<SolveFast.CWord>>, +gen: Nat,
                   hr: SolveFast.Hist5Res) -> RSortSt:
  match hr:
    case SolveFast.Hist5Pruned{seen2, tbl2}:
      RSortSt{seen2, bkts, tbl2, Nat.add(1n, gen)}
    case SolveFast.Hist5Ok{seen2, tbl2, +m, +k, budget}:
      rsort_hist_usable(row, g, n, base_lb, seen2, bkts, tbl2,
        Nat.add(1n, gen), m, k,
        Bool.or(Nat.is_lt(m, n), Nat.is_le(2n, k)))

def rsort_fill(+G: +List<+List<Nat>>, +row: U32, +S: +List<SolveFast.CWord>,
               +n: Nat, +base_lb: Nat, st: RSortSt) -> RSortSt:
  match G:
    case Nil{}:
      st
    case Con{+g, +rest}:
      match st:
        case RSortSt{seen, bkts, tbl, +gen}:
          rsort_fill(rest, U32.add(row, 1), S, n, base_lb,
            rsort_hist_one(row, g, n, base_lb, bkts, gen,
              SolveFast.hist5_go(row, S, gen, False{},
                SolveFast.Hist5Ok{seen, tbl, 0n, 0n, n})))

def prepend_rgs(+ws: +List<SolveFast.CWord>,
                +acc: +List<RootGuess>) -> +List<RootGuess>:
  match ws:
    case Nil{}:
      acc
    case Con{cw, rest}:
      match cw:
        case SolveFast.CWord{ci, row, g}:
          prepend_rgs(rest, RootGuess{row, g} <> acc)

def rsort_drain_tree(a: Array<+List<SolveFast.CWord>>,
                     +acc: +List<RootGuess>) -> +List<RootGuess>:
  match a:
    case ALeaf{+ws}:
      prepend_rgs(ws, acc)
    case ANode{xs, ys}:
      rsort_drain_tree(xs, rsort_drain_tree(ys, acc))

type RootPrepRes is Type:
  RootPrepRes{b0: SolveRef.Best, rgs: +List<RootGuess>, buf: SolveFast.Buf5}

def glist_of_rgs(+rgs: +List<RootGuess>) -> SolveFast.GList:
  match rgs:
    case Nil{}:
      SolveFast.GEnd{}
    case Con{rg, rest}:
      match rg:
        case RootGuess{row, g}:
          SolveFast.GTry{row, g, glist_of_rgs(rest)}

def rgs_of_G(+G: +List<+List<Nat>>, +row: U32) -> +List<RootGuess>:
  match G:
    case Nil{}:
      Nil{}
    case Con{g, rest}:
      RootGuess{row, g} <> rgs_of_G(rest, U32.add(row, 1))

def seed_update(+best: SolveRef.Best, gr: GreedyRes) -> SolveFast.StepRes:
  match gr:
    case GreedyFail{buf2}:
      SolveFast.StepRes{best, buf2}
    case GreedyOk{+tree, +cost, buf2}:
      SolveFast.StepRes{SolveRef.better(cost, tree, best), buf2}

def seed_top_go(+rem: Nat, +rgs: +List<RootGuess>, +gG: SolveFast.GList,
                +cs: +List<SolveFast.CWord>, +n: Nat,
                st: SolveFast.StepRes) -> SolveFast.StepRes:
  match rem:
    case 0n:
      st
    case 1n+p:
      match rgs:
        case Nil{}:
          st
        case Con{rg, rest}:
          match rg:
            case RootGuess{+row, +g}:
              match st:
                case SolveFast.StepRes{+best, buf}:
                  seed_top_go(p, rest, gG, cs, n,
                    seed_update(best,
                      greedy_step(n, 1n, Nil{}, gG, cs, n, Nil{}, Nil{}, 0n,
                        GreedyFail{SolveFast.NoBuf{}},
                        greedy_expand_forced(row, g, cs, n, buf))))

def finish_seed(+rgs: +List<RootGuess>, sr: SolveFast.StepRes) -> RootPrepRes:
  match sr:
    case SolveFast.StepRes{+b0, buf2}:
      RootPrepRes{b0, rgs, buf2}

def finish_rsort(+gG: SolveFast.GList, +cs: +List<SolveFast.CWord>,
                 +n: Nat, +inf: Nat, bkts_orig: Array<+List<SolveFast.CWord>>,
                 st: RSortSt) -> RootPrepRes:
  match st:
    case RSortSt{seen, bkts_sort, tbl, +gen}:
      +rgs = rsort_drain_tree(bkts_sort, Nil{})
      finish_seed(rgs,
        seed_top_go(5n, rgs, gG, cs, n,
          SolveFast.StepRes{SolveFast.dummy_inf(inf),
                            SolveFast.Buf5{seen, bkts_orig, tbl, gen}}))

def root_prepare(+G: +List<+List<Nat>>, +gG: SolveFast.GList,
                 +cs: +List<SolveFast.CWord>, +n: Nat, +inf: Nat,
                 buf: SolveFast.Buf5) -> RootPrepRes:
  match buf:
    case SolveFast.NoBuf{}:
      RootPrepRes{SolveFast.dummy_inf(inf), rgs_of_G(G, 0), SolveFast.NoBuf{}}
    case SolveFast.Buf5{seen, bkts, tbl, +gen}:
      +base_lb = SolveFast.init_floor(n)
      finish_rsort(gG, cs, n, inf, bkts,
        rsort_fill(G, 0, cs, n, base_lb,
          RSortSt{seen, Array.new(+List<SolveFast.CWord>, 10n, Nil{}), tbl, gen}))
