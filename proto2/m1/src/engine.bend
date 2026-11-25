# The ported search core: one self-recursive step machine.
#
# Rust's core is mutually recursive (min_state_val_with_hash <-> min_guess_val_inner)
# and safe Bend forbids that. Here a single def `step` runs both, with the pending
# child call represented by an explicit stack of `Fr` frames. The order of
# operations follows the Rust generic path (solver.rs), with the slice-2
# simplifications listed in DESIGN.md.
#
# The state array is never passed separately: `step` receives the pending read
# pair as its last parameter and issues the next read as the last argument of its
# own recursive call, like the scan loops in sec.bend. Loop results that are
# scalars are written into scratch cells by the scan and read back one per step.
#
# Node state (U32 parameters, so no record is built per call):
#   sb, n     candidate set: n ids at set[dep][sb..sb+n)
#   beta      the node's own cutoff (min_state's beta)
#   pmk       parent's maximum branching factor: row of the cap2d table
#   dep       depth (set / count / ne / off / size regions)
#   best      best complete value so far; starts at beta and only decreases
#   lb        local lower bound of this node
#   g         guess index being tried
#   cost      cost accumulated for the current guess
#   bcur      next bucket of the current guess
#   t         distinct responses of the current guess
#   lbk       carries has_win, then the response r, then a bucket start
#   gen       generation stamp base of the last count pass
#   ret       the value being delivered
#   nst,ngs,nht,npr   counters: states, guesses evaluated, cache hits, pruned
#
# Guess cost accounting (Rust's min_guess):
#   cost = 3n - t - has_win, then for every bucket with count >= 3:
#   cost += cap[pmk][p] - (2p-1)          (cap pass, phase 61..63)
#   and per bucket, with used = cap[pmk][p]:
#   b = cost - used; new_beta = best - b; if new_beta <= used -> give up (cost);
#   else val = child(new_beta); cost = b + val; if cost >= best -> give up.
#
# Phases
#   0 enter node                20 deliver a node value
#   22 quick call               1  quick result            24 issue cap read
#   23 cap read: cutoff or start guesses
#   3  next guess               30 count call              4  pk read
#   5  n3 read                  6  lb read                 31 skip a guess
#   60 partition                61,62,63 cap pass           7  bucket head
#   80 ne/size read             9  bucket skip test         83 bucket start
#   84 bucket cutoff            11 deliver a guess value
import Base
import ./geo.bend as G
import ./arith.bend as A
import ./heur.bend as H
import ./sec.bend as S

def noskip() -> U32:
  4294967295

def qcell(+c: U32, +gg: U32) -> U32:
  U32.add(G.off_qgen(c, gg), 604)

def cell_val(+c: U32, +gg: U32) -> U32:
  U32.add(G.off_qgen(c, gg), 609)

def cell_nst(+c: U32, +gg: U32) -> U32:
  U32.add(G.off_qgen(c, gg), 610)

def cell_ngs(+c: U32, +gg: U32) -> U32:
  U32.add(G.off_qgen(c, gg), 611)

def cell_nht(+c: U32, +gg: U32) -> U32:
  U32.add(G.off_qgen(c, gg), 612)

def cell_npr(+c: U32, +gg: U32) -> U32:
  U32.add(G.off_qgen(c, gg), 613)

# ------------------------------------------------------------------ frames ---

# The frame holds everything the parent needs to continue after a bucket child
# returns; lbk is the `used` of the bucket being recursed into.
type Fr is Type:
  Fr{sb: U32, n: U32, beta: U32, pmk: U32, dep: U32, best: U32, lb: U32,
     g: U32, cost: U32, bcur: U32, t: U32, lbk: U32}

# ------------------------------------------------------------------- engine ---

def step(+fuel: Nat, +ph: U32, +c: U32, +gg: U32, +sb: U32, +n: U32,
         +beta: U32, +pmk: U32, +dep: U32, +best: U32, +lb: U32, +g: U32,
         +cost: U32, +bcur: U32, +t: U32, +lbk: U32, +gen: U32, +ret: U32,
         +nst: U32, +ngs: U32, +nht: U32, +npr: U32,
         stk: List<Fr>, p: Array<U32> & U32) -> Array<U32>:
  match fuel:
    case 0n:
      (a2, _) = p
      a2
    case 1n+f:
      match ph:
        case 0:
          # Enter a node: n <= 2 is exact, 3..15 tries the quick eval.
          (a2, _) = p
          +isbase = U32.sub(1, A.ge01(n, 3))
          +toq = U32.mul(A.ge01(n, 3), A.ge01(16, n))
          step(f, A.sel(isbase, 20, A.sel(toq, 22, 24)), c, gg, sb, n, beta,
               pmk, dep, best, lb, g, cost, bcur, t, lbk, gen,
               A.sel(isbase, U32.div(U32.mul(n, U32.inc(n)), 2), ret),
               U32.add(nst, U32.sub(1, isbase)), ngs, nht, npr, stk,
               Array.get(U32, a2, 0))
        case 22:
          (a2, _) = p
          a3 = H.quick_at(a2, sb, n, c, gg, gen, qcell(c, gg))
          step(f, 1, c, gg, sb, n, beta, pmk, dep, best, lb, g, cost, bcur, t,
               lbk, U32.add(gen, 4096), ret, nst, ngs, nht, npr, stk,
               Array.get(U32, a3, qcell(c, gg)))
        case 1:
          # Quick result: packed as 2*value + exact.
          (a2, +pk) = p
          +ex = U32.and(pk, 1)
          step(f, A.sel(ex, 20, 24), c, gg, sb, n, beta, pmk, dep, best,
               A.sel(ex, lb, U32.shrn(pk, 1n)), g, cost, bcur, t, lbk, gen,
               A.sel(ex, U32.shrn(pk, 1n), ret), nst, ngs, nht, npr, stk,
               Array.get(U32, a2, 0))
        case 24:
          (a2, _) = p
          step(f, 23, c, gg, sb, n, beta, pmk, dep, best, lb, g, cost, bcur, t,
               lbk, gen, ret, nst, ngs, nht, npr, stk,
               Array.get(U32, a2, S.cap_at(pmk, n, c, gg)))
        case 23:
          # Capacity lower bound against this node's own cutoff.
          (a2, +cv) = p
          +lb2 = U32.max(lb, cv)
          +cut = A.ge01(lb2, beta)
          step(f, A.sel(cut, 20, 3), c, gg, sb, n, beta, pmk, dep,
               A.sel(cut, best, beta), lb2, 0, cost, bcur, t, lbk, gen,
               A.sel(cut, lb2, ret), nst, ngs, nht, npr, stk,
               Array.get(U32, a2, 0))
        case 3:
          # Next guess, in index order.
          (a2, _) = p
          +over = A.ge01(g, gg)
          step(f, A.sel(over, 20, 30), c, gg, sb, n, beta, pmk, dep, best, lb, g,
               cost, bcur, t, lbk, gen, A.sel(over, best, ret), nst, ngs, nht,
               npr, stk, Array.get(U32, a2, 0))
        case 30:
          (a2, _) = p
          +gen2 = U32.add(gen, 1024)
          a3 = S.cnt(g, sb, n, noskip(), gen2, dep, c, gg, a2)
          step(f, 4, c, gg, sb, n, beta, pmk, dep, best, lb, g, cost, bcur, t,
               lbk, gen2, ret, nst, ngs, nht, npr, stk,
               Array.get(U32, a3, S.pkcell(c, gg)))
        case 4:
          (a2, +v) = p
          step(f, 5, c, gg, sb, n, beta, pmk, dep, best, lb, g, cost, bcur,
               U32.and(v, 4095), U32.and(U32.shrn(v, 24n), 1), gen, ret, nst,
               ngs, nht, npr, stk,
               Array.get(U32, a2, S.n3cell(c, gg)))
        case 5:
          (a2, +v) = p
          a3 = S.stats(0, t, dep, c, gg, pmk, n, 1, gen, 1, a2)
          step(f, 6, c, gg, sb, n, beta, pmk, dep, best, lb, g, cost, bcur, t,
               lbk, gen, ret, nst, ngs, nht, npr, stk,
               Array.get(U32, a3, S.lbcell(c, gg)))
        case 6:
          # Skip a guess whose lower bound cannot beat the current best, and a
          # guess that separates nothing (Rust returns beta for it).
          (a2, +v) = p
          +skip = U32.max(A.ge01(v, best), U32.sub(1, A.ge01(t, 2)))
          step(f, A.sel(skip, 31, 60), c, gg, sb, n, beta, pmk, dep, best, lb,
               g, cost, bcur, t, lbk, gen, ret,
               nst, U32.add(ngs, U32.sub(1, skip)), nht, npr, stk,
               Array.get(U32, a2, 0))
        case 31:
          (a2, _) = p
          step(f, 3, c, gg, sb, n, beta, pmk, dep, best, lb, U32.inc(g), cost,
               bcur, t, lbk, gen, ret, nst, ngs, nht, npr, stk,
               Array.get(U32, a2, 0))
        case 60:
          # Partition, then cost = 3n - t - has_win.
          (a2, _) = p
          a3 = S.offsets(t, dep, S.set_at(U32.inc(dep), c, gg), c, gg, gen, a2)
          a4 = S.scatter(g, sb, n, dep, S.set_at(U32.inc(dep), c, gg), c, gg, a3)
          +cost2 = U32.sub(U32.sub(U32.mul(3, n), t), lbk)
          step(f, 61, c, gg, sb, n, beta, pmk, dep, best, lb, g, cost2, 0, t,
               lbk, gen, 0, nst, ngs, nht, npr, stk, Array.get(U32, a4, 0))
        case 61:
          # Cap pass over the buckets: add cap[pmk][p] - (2p-1) for p >= 3.
          (a2, _) = p
          +donec = A.ge01(bcur, t)
          step(f, A.sel(donec, 68, 64), c, gg, sb, n, beta, pmk, dep, best, lb,
               g, cost, bcur, t, lbk, gen, ret, nst, ngs, nht, npr, stk,
               Array.get(U32, a2, 0))
        case 64:
          (a2, _) = p
          +zb = S.ent_at(dep, c, gg)
          step(f, 65, c, gg, sb, n, beta, pmk, dep, best, lb, g, cost, bcur, t,
               lbk, gen, ret, nst, ngs, nht, npr, stk,
               Array.get(U32, a2, U32.add(zb, bcur)))
        case 65:
          (a2, +k) = p
          +skipc = U32.sub(1, A.ge01(k, 3))
          +idx = A.sel(skipc, 0, S.cap_at(pmk, k, c, gg))
          step(f, A.sel(skipc, 66, 67), c, gg, sb, n, beta, pmk, dep, best, lb,
               g, cost, bcur, t, lbk, gen, k, nst, ngs, nht, npr, stk,
               Array.get(U32, a2, idx))
        case 66:
          (a2, _) = p
          step(f, 61, c, gg, sb, n, beta, pmk, dep, best, lb, g, cost,
               U32.inc(bcur), t, lbk, gen, ret, nst, ngs, nht, npr, stk,
               Array.get(U32, a2, 0))
        case 67:
          (a2, +cv) = p
          +k2 = ret
          +cost2 = U32.sub(U32.add(cost, cv), U32.sub(U32.mul(k2, 2), 1))
          step(f, 66, c, gg, sb, n, beta, pmk, dep, best, lb, g, cost2, bcur, t,
               lbk, gen, ret, nst, ngs, nht, npr, stk, Array.get(U32, a2, 0))
        case 68:
          (a2, _) = p
          step(f, 7, c, gg, sb, n, beta, pmk, dep, best, lb, g, cost, 0, t,
               lbk, gen, ret, nst, ngs, nht, npr, stk, Array.get(U32, a2, 0))
        case 7:
          (a2, _) = p
          +doneb = A.ge01(bcur, t)
          step(f, A.sel(doneb, 11, 80), c, gg, sb, n, beta, pmk, dep, best, lb,
               g, cost, bcur, t, lbk, gen, A.sel(doneb, cost, ret), nst, ngs,
               nht, npr, stk, Array.get(U32, a2, 0))
        case 80:
          # r of this bucket, then its size.
          (a2, _) = p
          +nb2 = S.ne_at(dep, c, gg)
          step(f, 81, c, gg, sb, n, beta, pmk, dep, best, lb, g, cost, bcur, t,
               lbk, gen, ret, nst, ngs, nht, npr, stk,
               Array.get(U32, a2, U32.add(nb2, bcur)))
        case 81:
          (a2, +r) = p
          +zb = S.ent_at(dep, c, gg)
          step(f, 9, c, gg, sb, n, beta, pmk, dep, best, lb, g, cost, bcur, t,
               r, gen, ret, nst, ngs, nht, npr, stk,
               Array.get(U32, a2, U32.add(zb, bcur)))
        case 9:
          (a2, +k) = p
          +skipb = U32.max(A.eq01(lbk, 121), U32.sub(1, A.ge01(k, 3)))
          step(f, A.sel(skipb, 32, 83), c, gg, sb, n, beta, pmk, dep, best, lb,
               g, cost, A.sel(skipb, U32.inc(bcur), bcur), t, lbk, gen, k, nst,
               ngs, nht, npr, stk, Array.get(U32, a2, 0))
        case 32:
          (a2, _) = p
          step(f, 7, c, gg, sb, n, beta, pmk, dep, best, lb, g, cost, bcur, t,
               lbk, gen, ret, nst, ngs, nht, npr, stk, Array.get(U32, a2, 0))
        case 83:
          # Bucket start offset; k is in ret.
          (a2, _) = p
          +ob = S.off_at(dep, c, gg)
          step(f, 84, c, gg, sb, n, beta, pmk, dep, best, lb, g, cost, bcur, t,
               lbk, gen, ret, nst, ngs, nht, npr, stk,
               Array.get(U32, a2, U32.add(ob, bcur)))
        case 84:
          (a2, +o) = p
          +k2 = ret
          step(f, 85, c, gg, sb, n, beta, pmk, dep, best, lb, g, cost, bcur, t,
               o, gen, k2, nst, ngs, nht, npr, stk,
               Array.get(U32, a2, S.cap_at(pmk, k2, c, gg)))
        case 85:
          # Bucket cutoff. When new_beta <= used the guess cannot beat best, and
          # the child is entered with beta = used so that it returns `used`
          # immediately; the parent then adds 0 and sees cost >= best.
          (a2, +cv) = p
          +k2 = ret
          +cut2 = U32.sub(best, U32.sub(cost, cv))
          +cut3 = U32.max(cut2, cv)
          stk2 : List<Fr> = Con{Fr{sb, n, beta, pmk, dep, best, lb, g, cost,
                                   U32.inc(bcur), t, cv}, stk}
          step(f, 0, c, gg, lbk, k2, cut3, pmk, U32.inc(dep), cut3, 0, 0, 0,
               0, 0, 0, gen, ret, nst, ngs, nht, npr, stk2,
               Array.get(U32, a2, 0))
        case 11:
          (a2, _) = p
          +better = U32.mul(A.lt01(ret, best), U32.sub(best, ret))
          +best2 = U32.sub(best, better)
          +stop2 = A.ge01(lb, best2)
          step(f, A.sel(stop2, 20, 3), c, gg, sb, n, beta, pmk, dep, best2, lb,
               U32.inc(g), cost, bcur, t, lbk, gen, A.sel(stop2, best2, ret),
               nst, ngs, nht, npr, stk, Array.get(U32, a2, 0))
        case 20:
          # Deliver a node value to the parent frame, or finish at the root.
          match stk:
            case Nil{}:
              (a2, _) = p
              a3 = Array.set(U32, a2, cell_val(c, gg), ret)
              a4 = Array.set(U32, a3, cell_nst(c, gg), nst)
              a5 = Array.set(U32, a4, cell_ngs(c, gg), ngs)
              a6 = Array.set(U32, a5, cell_nht(c, gg), nht)
              Array.set(U32, a6, cell_npr(c, gg), npr)
            case Con{Fr{+sb2, +n2, +beta2, +pmk2, +dep2, +best2, +lb2, +g2,
                        +cost2, +bcur2, +t2, +used2}, rest}:
              (a2, _) = p
              +cost3 = U32.sub(U32.add(cost2, ret), used2)
              +pr = A.ge01(cost3, best2)
              step(f, A.sel(pr, 11, 7), c, gg, sb2, n2, beta2, pmk2, dep2,
                   best2, lb2, g2, cost3, bcur2, t2, used2, gen,
                   A.sel(pr, cost3, ret), nst, ngs, nht, U32.add(npr, pr),
                   rest, Array.get(U32, a2, 0))
        case _:
          (a2, _) = p
          a2
