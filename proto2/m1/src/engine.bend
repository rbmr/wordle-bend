# The ported search core: one self-recursive machine with an explicit frame
# stack. Rust's core is mutually recursive (min_state_val_with_hash <->
# min_guess_val_inner); safe Bend forbids mutual recursion, so a single def
# runs both and a stack of frames is the call stack.
#
# `kind` says what the current computation is: 0 = a state node, 1 = a guess
# evaluation. A state entering a guess pushes an Sf; a guess entering a bucket
# pushes a Gf. Returning a value goes through phase 120, which pops the frame
# according to the current kind.
#
# The state follows Rust's generic path (solver.rs): base cases, the two-slot
# transposition table, the quick eval for n <= 15, the parent cap bound, phase 1
# over the candidates, phase 2 over the filtered guesses, the tuple sorts and
# beta cuts, and the final exact/lower-bound store. The guess follows
# min_guess_val_inner: counting, the cost formula, the cap pass over buckets,
# and the bucket recursion with Rust's b = cost - used accounting.
#
# Phase map
#   state: 0 enter, 90..99 TT lookup, 89/22/1/24/23 quick+cap,
#          40..49 phase 1 read, 50..63 phase 2, 70 final, 170..173 tuple walk,
#          100..113 TT insert, 120 deliver
#   guess: 300..302 count and cost, 461..468 cap pass, 7/80/81/9/83/84/85 buckets,
#          32 skip, 120 deliver
import Base
import ./geo.bend as G
import ./arith.bend as A
import ./heur.bend as H
import ./sec.bend as S
import ./bounds.bend as B
import ./p12.bend as P
import ./buck.bend as Be

def noskip() -> U32:
  4294967295

def qcell(+c: U32, +gg: U32, +i: U32) -> U32:
  U32.add(G.off_qgen(c, gg), i)

def hsh1(+dep: U32, +c: U32, +gg: U32) -> U32:
  U32.add(G.off_cmk(c, gg), U32.mul(dep, 1024))

def hsh2(+dep: U32, +c: U32, +gg: U32) -> U32:
  U32.add(U32.add(G.off_cmk(c, gg), U32.mul(dep, 1024)), 1)

def ttmask() -> U32:
  U32.sub(G.ttb(), 1)

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

def pack_val(+v: U32, +beta: U32) -> U32:
  U32.add(U32.and(v, 262143), U32.mul(A.lt01(v, beta), 262144))

def upd_ok(+oex: U32, +old: U32, +v: U32, +beta: U32) -> U32:
  +nex = A.lt01(v, beta)
  +nlb = U32.sub(1, nex)
  U32.sub(U32.sub(1, U32.mul(oex, nlb)), U32.mul(nlb, A.lt01(v, old)))

# p12 result cells
def rb(+c: U32, +gg: U32) -> U32:
  qcell(c, gg, 700)

def rl(+c: U32, +gg: U32) -> U32:
  qcell(c, gg, 701)

def rv(+c: U32, +gg: U32) -> U32:
  qcell(c, gg, 702)

def rm(+c: U32, +gg: U32) -> U32:
  qcell(c, gg, 703)

def rn(+c: U32, +gg: U32) -> U32:
  qcell(c, gg, 704)

def rg(+c: U32, +gg: U32) -> U32:
  qcell(c, gg, 707)

# p1/p2 tuple buffer bases for this depth.
def p1base(+dep: U32, +c: U32, +gg: U32) -> U32:
  U32.add(G.off_p1t(c, gg), U32.mul(dep, U32.mul(c, 3)))

def p2base(+dep: U32, +c: U32, +gg: U32) -> U32:
  U32.add(G.off_p2t(c, gg), U32.mul(dep, U32.mul(gg, 3)))

# ------------------------------------------------------------------ frames ---

type Fr is Type:
  Sf{ss: U32, n: U32, beta: U32, pmk: U32, dep: U32, best: U32, lb: U32,
     lmk: U32, v1k: U32, v2k: U32, mv: U32, nt: U32, ti: U32, mode: U32,
     rph: U32}
  Gf{ss: U32, n: U32, beta: U32, pmk: U32, dep: U32, best: U32, lb: U32,
     g: U32, cost: U32, bcur: U32, t: U32, used: U32}

# ------------------------------------------------------------------- engine ---

def step(+fuel: Nat, +c: U32, +gg: U32, +kind: U32, +ph: U32, +ss: U32, +n: U32, +beta: U32,
         +pmk: U32, +dep: U32, +best: U32, +lb: U32, +lmk: U32, +v1k: U32,
         +v2k: U32, +mv: U32, +nt: U32, +ti: U32, +mode: U32, +g: U32,
         +cost: U32, +bcur: U32, +t: U32, +lbk: U32, +cut: U32, +gen: U32,
         +ret: U32, +nst: U32, +ngs: U32, +nht: U32, +npr: U32,
         stk: List<Fr>, p: Array<U32> & U32) -> Array<U32>:
  match fuel:
    case 0n:
      (a2, _) = p
      a2
    case 1n+f:
      match ph:
        # ------------------------------------------------------ state ----
        case 0:
          (a2, _) = p
          +isbase = U32.sub(1, A.ge01(n, 3))
          step(f, c, gg, A.sel(isbase, 0, 0), A.sel(isbase, 120, 90), ss, n, beta, pmk,
               dep, best, lb, lmk, v1k, v2k, mv, nt, ti, mode, g, cost, bcur, t,
               lbk, cut, gen,
               A.sel(isbase, U32.div(U32.mul(n, U32.inc(n)), 2), ret), nst, ngs,
               nht, npr, stk, Array.get(U32, a2, 0))
        case 90:
          (a2, _) = p
          step(f, c, gg, 0, 91, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               nt, ti, mode, g, cost, bcur, t, lbk, cut, gen, ret, nst, ngs,
               nht, npr, stk, Array.get(U32, a2, hsh1(dep, c, gg)))
        case 91:
          (a2, +h1) = p
          step(f, c, gg, 0, 92, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               nt, ti, mode, g, cost, U32.or(h1, 1), t, lbk, cut, gen, ret,
               nst, ngs, nht, npr, stk, Array.get(U32, a2, hsh2(dep, c, gg)))
        case 92:
          (a2, +h2) = p
          +base = U32.add(G.off_tt(c, gg),
                          U32.mul(U32.and(bcur, ttmask()), 6))
          step(f, c, gg, 0, 93, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               nt, ti, mode, g, base, bcur, h2, lbk, cut, gen, ret, nst, ngs,
               nht, npr, stk, Array.get(U32, a2, U32.add(base, 3)))
        case 93:
          (a2, +k1) = p
          +hit1 = A.eq01(k1, bcur)
          step(f, c, gg, 0, A.sel(hit1, 94, 95), ss, n, beta, pmk, dep, best, lb, lmk,
               v1k, v2k, mv, nt, ti, mode, g, cost, bcur, t, lbk, cut, gen,
               ret, nst, ngs, nht, npr, stk,
               Array.get(U32, a2, A.sel(hit1, U32.add(cost, 4), cost)))
        case 94:
          (a2, +k2) = p
          +hit2 = A.eq01(k2, t)
          step(f, c, gg, 0, A.sel(hit2, 96, 95), ss, n, beta, pmk, dep, best, lb, lmk,
               v1k, v2k, mv, nt, ti, mode, g, cost, bcur, t, lbk, cut, gen,
               ret, nst, ngs, nht, npr, stk,
               Array.get(U32, a2, A.sel(hit2, U32.add(cost, 5), cost)))
        case 95:
          (a2, +k1) = p
          +hit1 = A.eq01(k1, bcur)
          step(f, c, gg, 0, A.sel(hit1, 97, 98), ss, n, beta, pmk, dep, best, lb, lmk,
               v1k, v2k, mv, nt, ti, mode, g, cost, bcur, t, lbk, cut, gen,
               ret, nst, ngs, nht, npr, stk,
               Array.get(U32, a2, A.sel(hit1, U32.add(cost, 1), 0)))
        case 97:
          (a2, +k2) = p
          +hit2 = A.eq01(k2, t)
          step(f, c, gg, 0, A.sel(hit2, 99, 98), ss, n, beta, pmk, dep, best, lb, lmk,
               v1k, v2k, mv, nt, ti, mode, g, cost, bcur, t, lbk, cut, gen,
               ret, nst, ngs, nht, npr, stk,
               Array.get(U32, a2, A.sel(hit2, U32.add(cost, 2), 0)))
        case 96:
          (a2, +v) = p
          +val = U32.and(v, 262143)
          +ex = U32.and(U32.shrn(v, 18n), 1)
          +take = U32.max(ex, A.ge01(val, beta))
          step(f, c, gg, 0, A.sel(take, 120, 89), ss, n, beta, pmk, dep, best,
               U32.max(lb, val), lmk, v1k, v2k, mv, nt, ti, mode, g, cost,
               bcur, t, lbk, cut, gen, A.sel(take, val, ret), nst, ngs,
               U32.add(nht, 1), npr, stk, Array.get(U32, a2, 0))
        case 99:
          (a2, +v) = p
          +val = U32.and(v, 262143)
          +ex = U32.and(U32.shrn(v, 18n), 1)
          +take = U32.max(ex, A.ge01(val, beta))
          step(f, c, gg, 0, A.sel(take, 120, 89), ss, n, beta, pmk, dep, best,
               U32.max(lb, val), lmk, v1k, v2k, mv, nt, ti, mode, g, cost,
               bcur, t, lbk, cut, gen, A.sel(take, val, ret), nst, ngs,
               U32.add(nht, 1), npr, stk, Array.get(U32, a2, 0))
        case 98:
          (a2, _) = p
          step(f, c, gg, 0, 89, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               nt, ti, mode, g, cost, bcur, t, lbk, cut, gen, ret, nst, ngs,
               nht, npr, stk, Array.get(U32, a2, 0))
        case 89:
          (a2, _) = p
          +useq = U32.mul(A.eq01(lb, 0), U32.mul(A.ge01(n, 3), A.ge01(16, n)))
          step(f, c, gg, 0, A.sel(useq, 22, 24), ss, n, beta, pmk, dep, best, lb, lmk,
               v1k, v2k, mv, nt, ti, mode, g, cost, bcur, t, lbk, cut, gen,
               ret, U32.add(nst, 1), ngs, nht, npr, stk,
               Array.get(U32, a2, 0))
        case 22:
          (a2, _) = p
          a3 = H.quick_at(a2, ss, n, c, gg, qcell(c, gg, 604))
          step(f, c, gg, 0, 1, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               nt, ti, mode, g, cost, bcur, t, lbk, cut, gen,
               ret, nst, ngs, nht, npr, stk,
               Array.get(U32, a3, qcell(c, gg, 604)))
        case 1:
          (a2, +pk) = p
          +ex = U32.and(pk, 1)
          step(f, c, gg, 0, A.sel(ex, 120, 24), ss, n, beta, pmk, dep, best,
               A.sel(ex, lb, U32.shrn(pk, 1n)), lmk, v1k, v2k, mv, nt, ti,
               mode, g, cost, bcur, t, lbk, cut, gen,
               A.sel(ex, U32.shrn(pk, 1n), ret), nst, ngs, nht, npr, stk,
               Array.get(U32, a2, 0))
        case 24:
          (a2, _) = p
          step(f, c, gg, 0, 23, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               nt, ti, mode, g, cost, bcur, t, lbk, cut, gen, ret, nst, ngs,
               nht, npr, stk, Array.get(U32, a2, S.cap_at(pmk, n, c, gg)))
        case 23:
          (a2, +cv) = p
          +lb2 = U32.max(lb, cv)
          +cut2 = A.ge01(lb2, beta)
          step(f, c, gg, 0, A.sel(cut2, 120, 40), ss, n, beta, pmk, dep,
               A.sel(cut2, best, beta), lb2, 0, 0, 0, 4294967295, 0, 0, 0, g,
               cost, bcur, t, lbk, cut, gen, A.sel(cut2, lb2, ret), nst, ngs,
               nht, npr, stk, Array.get(U32, a2, 0))
        case 40:
          (a2, _) = p
          a3 = P.p1_scan(a2, ss, n, best, pmk, dep, gen, c, gg)
          step(f, c, gg, 0, 41, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               nt, ti, mode, g, cost, bcur, t, lbk, cut, gen, ret, nst, ngs,
               nht, npr, stk, Array.get(U32, a3, rb(c, gg)))
        case 41:
          (a2, +v) = p
          step(f, c, gg, 0, 42, ss, n, beta, pmk, dep, v, lb, lmk, v1k, v2k, mv, nt,
               ti, mode, g, cost, bcur, t, lbk, cut, gen, ret, nst, ngs, nht,
               npr, stk, Array.get(U32, a2, rl(c, gg)))
        case 42:
          (a2, +v) = p
          step(f, c, gg, 0, 43, ss, n, beta, pmk, dep, best, lb, v, v1k, v2k, mv, nt,
               ti, mode, g, cost, bcur, t, lbk, cut, gen, ret, nst, ngs, nht,
               npr, stk, Array.get(U32, a2, rv(c, gg)))
        case 43:
          (a2, +v) = p
          step(f, c, gg, 0, 44, ss, n, beta, pmk, dep, best, lb, lmk, v, v2k, mv, nt,
               ti, mode, g, cost, bcur, t, lbk, cut, gen, ret, nst, ngs, nht,
               npr, stk, Array.get(U32, a2, rm(c, gg)))
        case 44:
          (a2, +v) = p
          step(f, c, gg, 0, 45, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, v, nt,
               ti, mode, g, cost, bcur, t, lbk, cut, gen, ret, nst, ngs, nht,
               npr, stk, Array.get(U32, a2, rn(c, gg)))
        case 45:
          (a2, +v) = p
          step(f, c, gg, 0, 46, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv, v,
               ti, mode, g, cost, bcur, t, lbk, cut, gen, ret, nst, ngs, nht,
               npr, stk, Array.get(U32, a2, qcell(c, gg, 705)))
        case 46:
          (a2, +v) = p
          step(f, c, gg, 0, 47, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               nt, ti, mode, g, cost, bcur, t, lbk, cut, gen, ret, nst,
               U32.add(ngs, v), nht, npr, stk,
               Array.get(U32, a2, qcell(c, gg, 706)))
        case 47:
          (a2, +v) = p
          step(f, c, gg, 0, 48, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               nt, ti, mode, g, cost, bcur, t, lbk, cut, gen, ret, nst, ngs,
               nht, U32.add(npr, v), stk, Array.get(U32, a2, rg(c, gg)))
        case 48:
          (a2, +v) = p
          +walk = U32.and(A.gt01b(best, lb), A.ge01(nt, 1))
          step(f, c, gg, 0, A.sel(walk, 49, 50), ss, n, beta, pmk, dep, best, lb, lmk,
               v1k, v2k, mv, nt, 0, 1, g, cost, bcur, t, lbk, cut, v, ret,
               nst, ngs, nht, npr, stk, Array.get(U32, a2, 0))
        case 49:
          (a2, _) = p
          +b0 = p1base(dep, c, gg)
          a3 = P.sort3(a2, b0, nt)
          +idx = U32.add(b0, 0)
          step(f, c, gg, 0, 170, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               nt, 0, 1, g, cost, bcur, t, lbk, cut, gen, ret, nst, ngs, nht,
               npr, stk, Array.get(U32, a3, idx))
        case 50:
          (a2, _) = p
          +p2min = U32.from_nat(B.phase2_capacity_bound(U32.to_nat(n),
                                                        U32.to_nat(pmk),
                                                        U32.to_nat(pmk)))
          +eff = U32.max(lb, p2min)
          +run = A.gt01b(best, eff)
          +enough = A.ge01(n, P.mkn2(best, lmk, n))
          +next = A.sel(run, A.sel(enough, 51, 62), 70)
          step(f, c, gg, 0, next, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k,
               A.sel(run, mv, U32.min(mv, p2min)), A.sel(run, 0, nt), 0, 2, g,
               cost, bcur, t, lbk, cut, gen, ret, nst, ngs, nht, npr, stk,
               Array.get(U32, a2, 0))
        case 51:
          (a2, _) = p
          a3 = P.p2_scan(a2, ss, n, best, pmk, dep, gen, c, gg)
          step(f, c, gg, 0, 52, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               nt, ti, mode, g, cost, bcur, t, lbk, cut, gen, ret, nst, ngs,
               nht, npr, stk, Array.get(U32, a3, rb(c, gg)))
        case 52:
          (a2, +v) = p
          step(f, c, gg, 0, 53, ss, n, beta, pmk, dep, v, lb, lmk, v1k, v2k, mv, nt,
               ti, mode, g, cost, bcur, t, lbk, cut, gen, ret, nst, ngs, nht,
               npr, stk, Array.get(U32, a2, rl(c, gg)))
        case 53:
          (a2, +v) = p
          step(f, c, gg, 0, 54, ss, n, beta, pmk, dep, best, lb, v, v1k, v2k, mv, nt,
               ti, mode, g, cost, bcur, t, lbk, cut, gen, ret, nst, ngs, nht,
               npr, stk, Array.get(U32, a2, rv(c, gg)))
        case 54:
          (a2, +v) = p
          step(f, c, gg, 0, 55, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v, mv, nt,
               ti, mode, g, cost, bcur, t, lbk, cut, gen, ret, nst, ngs, nht,
               npr, stk, Array.get(U32, a2, rm(c, gg)))
        case 55:
          (a2, +v) = p
          step(f, c, gg, 0, 56, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, v, nt,
               ti, mode, g, cost, bcur, t, lbk, cut, gen, ret, nst, ngs, nht,
               npr, stk, Array.get(U32, a2, rn(c, gg)))
        case 56:
          (a2, +v) = p
          step(f, c, gg, 0, 57, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv, v,
               ti, mode, g, cost, bcur, t, lbk, cut, gen, ret, nst, ngs, nht,
               npr, stk, Array.get(U32, a2, qcell(c, gg, 705)))
        case 57:
          (a2, +v) = p
          step(f, c, gg, 0, 58, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               nt, ti, mode, g, cost, bcur, t, lbk, cut, gen, ret, nst,
               U32.add(ngs, v), nht, npr, stk,
               Array.get(U32, a2, qcell(c, gg, 706)))
        case 58:
          (a2, +v) = p
          step(f, c, gg, 0, 59, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               nt, ti, mode, g, cost, bcur, t, lbk, cut, gen, ret, nst, ngs,
               nht, U32.add(npr, v), stk, Array.get(U32, a2, rg(c, gg)))
        case 59:
          (a2, +v) = p
          step(f, c, gg, 0, 161, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               nt, 0, 2, g, cost, bcur, t, lbk, cut, v, ret, nst, ngs, nht,
               npr, stk, Array.get(U32, a2, S.cap_at(lmk, n, c, gg)))
        case 161:
          (a2, +v) = p
          +lb2 = U32.max(lb, v)
          +walk = U32.and(A.lt01(lb2, best), A.ge01(nt, 1))
          step(f, c, gg, 0, A.sel(walk, 63, 70), ss, n, beta, pmk, dep, best, lb2,
               lmk, v1k, v2k, mv, nt, ti, mode, g, cost, bcur, t, lbk, cut,
               gen, ret, nst, ngs, nht, npr, stk, Array.get(U32, a2, 0))
        case 62:
          # Too small for phase 2: mv = min(mv, best), then the base_lb read.
          (a2, _) = p
          step(f, c, gg, 0, 63, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k,
               U32.min(mv, best), nt, ti, mode, g, cost, bcur, t, lbk, cut,
               gen, ret, nst, ngs, nht, npr, stk,
               Array.get(U32, a2, S.cap_at(lmk, n, c, gg)))
        case 63:
          (a2, _) = p
          +b0 = p2base(dep, c, gg)
          a3 = P.sort3(a2, b0, nt)
          step(f, c, gg, 0, 170, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               nt, 0, 2, g, cost, bcur, t, lbk, cut, gen, ret, nst, ngs, nht,
               npr, stk, Array.get(U32, a3, b0))
        # -------------------------------------------------- tuple walk ---
        case 170:
          (a2, _) = p
          +done = A.ge01(ti, nt)
          +base = A.sel(A.eq01(mode, 1), p1base(dep, c, gg),
                        p2base(dep, c, gg))
          +idx = A.sel(done, 0, U32.add(base, U32.mul(ti, 3)))
          +next = A.sel(done, A.sel(A.eq01(mode, 1), 50, 70), 171)
          step(f, c, gg, 0, next, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               nt, ti, mode, g, cost, bcur, t, lbk, cut, gen, ret, nst, ngs,
               nht, npr, stk, Array.get(U32, a2, idx))
        case 171:
          (a2, +v) = p
          +prune = A.ge01(v, best)
          +base = A.sel(A.eq01(mode, 1), p1base(dep, c, gg),
                        p2base(dep, c, gg))
          +idx = A.sel(prune, 0, U32.add(U32.add(base, U32.mul(ti, 3)), 2))
          +next = A.sel(prune, A.sel(A.eq01(mode, 1), 50, 70), 172)
          step(f, c, gg, 0, next, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k,
               U32.min(mv, v), nt, ti, mode, g, cost, bcur, t, lbk, cut, gen,
               ret, nst, ngs, nht, U32.add(npr, U32.mul(prune, U32.sub(nt, ti))),
               stk, Array.get(U32, a2, idx))
        case 172:
          (a2, +v) = p
          stk2 : List<Fr> = Con{Sf{ss, n, beta, pmk, dep, best, lb, lmk, v1k,
                                   v2k, mv, nt, ti, mode, 173}, stk}
          # Rust passes the state's local_max_k (the largest bucket seen in
          # phase 1/2) to min_guess, which uses that row of the capacity table.
          step(f, c, gg, 1, 300, ss, n, beta, lmk, dep, best, lb, lmk, v1k, v2k, mv,
               nt, ti, mode, v, 0, 0, 0, 0, best, gen, ret, nst, ngs, nht, npr,
               stk2, Array.get(U32, a2, 0))
        case 173:
          (a2, _) = p
          +btr = A.lt01(ret, best)
          +best2 = A.sel(btr, ret, best)
          +stop = U32.and(btr, A.ge01(lb, ret))
          +next = A.sel(stop, A.sel(A.eq01(mode, 1), 50, 70), 170)
          step(f, c, gg, 0, next, ss, n, beta, pmk, dep, best2, lb, lmk, v1k, v2k,
               U32.min(mv, ret), nt, U32.add(ti, U32.sub(1, stop)), mode, g,
               cost, bcur, t, lbk, cut, gen, ret, nst, ngs, nht, npr, stk,
               Array.get(U32, a2, 0))
        # --------------------------------------------------- final -------
        case 70:
          (a2, _) = p
          +ex = A.lt01(best, beta)
          +f1 = U32.max(beta, lb)
          +usemv = U32.and(A.gt01b(best, lb),
                           U32.sub(1, A.eq01(mv, 4294967295)))
          +f2 = U32.max(f1, U32.mul(usemv, mv))
          +val = A.sel(ex, best, f2)
          step(f, c, gg, 0, 100, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               nt, ti, mode, g, cost, bcur, t, lbk, cut, gen, val, nst, ngs,
               nht, npr, stk, Array.get(U32, a2, 0))
        # --------------------------------------------- transposition -----
        case 100:
          (a2, _) = p
          step(f, c, gg, 0, 101, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               nt, ti, mode, g, cost, bcur, t, lbk, cut, gen, ret, nst, ngs,
               nht, npr, stk, Array.get(U32, a2, hsh1(dep, c, gg)))
        case 101:
          (a2, +h1) = p
          step(f, c, gg, 0, 102, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               nt, ti, mode, g, cost, U32.or(h1, 1), t, lbk, cut, gen, ret,
               nst, ngs, nht, npr, stk, Array.get(U32, a2, hsh2(dep, c, gg)))
        case 102:
          (a2, +h2) = p
          +base = U32.add(G.off_tt(c, gg),
                          U32.mul(U32.and(bcur, ttmask()), 6))
          step(f, c, gg, 0, 103, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               nt, ti, mode, g, base, bcur, h2, lbk, cut, gen, ret, nst,
               ngs, nht, npr, stk, Array.get(U32, a2, U32.add(base, 3)))
        case 103:
          (a2, +k1) = p
          +same = A.eq01(k1, bcur)
          step(f, c, gg, 0, A.sel(same, 104, 105), ss, n, beta, pmk, dep, best, lb,
               lmk, v1k, v2k, mv, nt, ti, mode, g, cost, bcur, t, lbk, cut,
               gen, ret, nst, ngs, nht, npr, stk,
               Array.get(U32, a2, A.sel(same, U32.add(cost, 4), U32.add(cost, 5))))
        case 104:
          (a2, +k2) = p
          +same = A.eq01(k2, t)
          step(f, c, gg, 0, A.sel(same, 106, 105), ss, n, beta, pmk, dep, best, lb,
               lmk, v1k, v2k, mv, nt, ti, mode, g, cost, bcur, t, lbk, cut,
               gen, ret, nst, ngs, nht, npr, stk,
               Array.get(U32, a2, U32.add(cost, 5)))
        case 105:
          (a2, +v1) = p
          +old = U32.and(v1, 262143)
          +go1 = A.ge01(ret, old)
          +empty = A.eq01(bcur, 0)
          +put = U32.max(go1, empty)
          +sc = U32.add(G.off_qgen(c, gg), 640)
          +i1 = A.sel(put, U32.add(cost, 3), sc)
          +i2 = A.sel(put, U32.add(cost, 4), U32.add(sc, 1))
          +i3 = A.sel(put, U32.add(cost, 5), U32.add(sc, 2))
          a3 = Array.set(U32, a2, i1, bcur)
          a4 = Array.set(U32, a3, i2, t)
          a5 = Array.set(U32, a4, i3, pack_val(ret, beta))
          step(f, c, gg, 0, A.sel(put, 120, 109), ss, n, beta, pmk, dep, best, lb,
               lmk, v1k, v2k, mv, nt, ti, mode, g, cost, bcur, t, lbk, cut,
               gen, ret, nst, ngs, nht, npr, stk, Array.get(U32, a5, 0))
        case 106:
          (a2, +v1) = p
          +old = U32.and(v1, 262143)
          +oex = U32.and(U32.shrn(v1, 18n), 1)
          +upd = upd_ok(oex, old, ret, beta)
          +sc = U32.add(G.off_qgen(c, gg), 640)
          +i1 = A.sel(upd, U32.add(cost, 3), sc)
          +i2 = A.sel(upd, U32.add(cost, 4), U32.add(sc, 1))
          +i3 = A.sel(upd, U32.add(cost, 5), U32.add(sc, 2))
          a3 = Array.set(U32, a2, i1, bcur)
          a4 = Array.set(U32, a3, i2, t)
          a5 = Array.set(U32, a4, i3, pack_val(ret, beta))
          step(f, c, gg, 0, 120, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               nt, ti, mode, g, cost, bcur, t, lbk, cut, gen, ret, nst, ngs,
               nht, npr, stk, Array.get(U32, a5, 0))
        case 109:
          (a2, _) = p
          step(f, c, gg, 0, 110, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               nt, ti, mode, g, cost, bcur, t, lbk, cut, gen, ret, nst, ngs,
               nht, npr, stk, Array.get(U32, a2, cost))
        case 110:
          (a2, +k1) = p
          +same = A.eq01(k1, bcur)
          step(f, c, gg, 0, A.sel(same, 111, 112), ss, n, beta, pmk, dep, best, lb,
               lmk, v1k, v2k, mv, nt, ti, mode, g, cost, bcur, t, lbk, cut,
               gen, ret, nst, ngs, nht, npr, stk,
               Array.get(U32, a2, A.sel(same, U32.add(cost, 1), U32.add(cost, 0))))
        case 111:
          (a2, +k2) = p
          +same = A.eq01(k2, t)
          step(f, c, gg, 0, A.sel(same, 113, 112), ss, n, beta, pmk, dep, best, lb,
               lmk, v1k, v2k, mv, nt, ti, mode, g, cost, bcur, t, lbk, cut,
               gen, ret, nst, ngs, nht, npr, stk,
               Array.get(U32, a2, U32.add(cost, 2)))
        case 113:
          (a2, +v1) = p
          +old = U32.and(v1, 262143)
          +oex = U32.and(U32.shrn(v1, 18n), 1)
          +upd = upd_ok(oex, old, ret, beta)
          +sc = U32.add(G.off_qgen(c, gg), 640)
          +i1 = A.sel(upd, cost, sc)
          +i2 = A.sel(upd, U32.add(cost, 1), U32.add(sc, 1))
          +i3 = A.sel(upd, U32.add(cost, 2), U32.add(sc, 2))
          a3 = Array.set(U32, a2, i1, bcur)
          a4 = Array.set(U32, a3, i2, t)
          a5 = Array.set(U32, a4, i3, pack_val(ret, beta))
          step(f, c, gg, 0, 120, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               nt, ti, mode, g, cost, bcur, t, lbk, cut, gen, ret, nst, ngs,
               nht, npr, stk, Array.get(U32, a5, 0))
        case 112:
          (a2, _) = p
          a3 = Array.set(U32, a2, cost, bcur)
          a4 = Array.set(U32, a3, U32.add(cost, 1), t)
          a5 = Array.set(U32, a4, U32.add(cost, 2), pack_val(ret, beta))
          step(f, c, gg, 0, 120, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               nt, ti, mode, g, cost, bcur, t, lbk, cut, gen, ret, nst, ngs,
               nht, npr, stk, Array.get(U32, a5, 0))
        # ------------------------------------------------------ guess ----
        case 300:
          (a2, _) = p
          a3 = S.cnt(g, ss, n, noskip(), dep, c, gg, a2)
          step(f, c, gg, 1, 301, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               nt, ti, mode, g, cost, bcur, t, lbk, cut, gen, ret,
               nst, U32.add(ngs, 1), nht, npr, stk,
               Array.get(U32, a3, S.pkcell(c, gg)))
        case 301:
          (a2, +v) = p
          +t0 = U32.and(v, 4095)
          +hw = U32.and(U32.shrn(v, 24n), 1)
          +t1 = U32.sub(1, A.ge01(t0, 2))
          +cost0 = U32.sub(U32.sub(U32.mul(3, n), t0), hw)
          +badc = A.ge01(cost0, cut)
          +bad = U32.max(t1, badc)
          step(f, c, gg, 1, A.sel(bad, 120, 302), ss, n, beta, pmk, dep, best, lb,
               lmk, v1k, v2k, mv, nt, ti, mode, g, A.sel(bad, cost0, cost0), bcur,
               t0, hw, cut, gen, A.sel(t1, cut, cost0), nst, ngs, nht,
               U32.add(npr, badc), stk, Array.get(U32, a2, 0))
        case 302:
          (a2, _) = p
          +dst = S.set_at(U32.inc(dep), c, gg)
          a3 = S.offsets(t, dep, dst, c, gg, a2)
          a4 = S.scatter(g, ss, n, dep, dst, c, gg, a3)
          step(f, c, gg, 1, 61, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               nt, ti, mode, g, cost, 0, t, lbk, cut, gen, ret, nst, ngs, nht,
               npr, stk, Array.get(U32, a4, 0))
        case 61:
          (a2, _) = p
          +donec = A.ge01(bcur, t)
          step(f, c, gg, 1, A.sel(donec, 68, 64), ss, n, beta, pmk, dep, best, lb,
               lmk, v1k, v2k, mv, nt, ti, mode, g, cost, bcur, t, lbk, cut,
               gen, ret, nst, ngs, nht, npr, stk, Array.get(U32, a2, 0))
        case 64:
          (a2, _) = p
          +zb = S.ent_at(dep, c, gg)
          step(f, c, gg, 1, 65, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               nt, ti, mode, g, cost, bcur, t, lbk, cut, gen, ret, nst, ngs,
               nht, npr, stk, Array.get(U32, a2, U32.add(zb, bcur)))
        case 65:
          (a2, +k) = p
          +skipc = U32.sub(1, A.ge01(k, 3))
          +idx = A.sel(skipc, 0, S.cap_at(pmk, k, c, gg))
          step(f, c, gg, 1, A.sel(skipc, 66, 67), ss, n, beta, pmk, dep, best, lb,
               lmk, v1k, v2k, mv, nt, ti, mode, g, cost, bcur, t, lbk, cut,
               gen, k, nst, ngs, nht, npr, stk, Array.get(U32, a2, idx))
        case 66:
          (a2, _) = p
          step(f, c, gg, 1, 61, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               nt, ti, mode, g, cost, U32.inc(bcur), t, lbk, cut, gen, ret,
               nst, ngs, nht, npr, stk, Array.get(U32, a2, 0))
        case 67:
          (a2, +cv) = p
          +cost2 = U32.sub(U32.add(cost, cv), U32.sub(U32.mul(ret, 2), 1))
          step(f, c, gg, 1, 66, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               nt, ti, mode, g, cost2, bcur, t, lbk, cut, gen, ret, nst, ngs,
               nht, npr, stk, Array.get(U32, a2, 0))
        case 68:
          (a2, _) = p
          step(f, c, gg, 1, 7, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv, nt,
               ti, mode, g, cost, 0, t, lbk, cut, gen, ret, nst, ngs, nht, npr,
               stk, Array.get(U32, a2, 0))
        case 7:
          (a2, _) = p
          +doneb = A.ge01(bcur, t)
          +over = A.ge01(cost, cut)
          +stop = U32.max(doneb, over)
          step(f, c, gg, 1, A.sel(stop, 120, 80), ss, n, beta, pmk, dep, best, lb,
               lmk, v1k, v2k, mv, nt, ti, mode, g, cost, bcur, t, lbk, cut,
               gen, A.sel(stop, cost, ret), nst, ngs, nht,
               U32.add(npr, U32.mul(over, U32.sub(1, doneb))), stk,
               Array.get(U32, a2, 0))
        case 80:
          (a2, _) = p
          +nb2 = S.ne_at(dep, c, gg)
          step(f, c, gg, 1, 81, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               nt, ti, mode, g, cost, bcur, t, lbk, cut, gen, ret, nst, ngs,
               nht, npr, stk, Array.get(U32, a2, U32.add(nb2, bcur)))
        case 81:
          (a2, +r) = p
          +zb = S.ent_at(dep, c, gg)
          step(f, c, gg, 1, 9, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               nt, ti, mode, g, cost, bcur, t, r, cut, gen, ret, nst, ngs, nht,
               npr, stk, Array.get(U32, a2, U32.add(zb, bcur)))
        case 9:
          (a2, +k) = p
          +skipb = U32.max(A.eq01(lbk, 121), U32.sub(1, A.ge01(k, 3)))
          step(f, c, gg, 1, A.sel(skipb, 32, 83), ss, n, beta, pmk, dep, best, lb,
               lmk, v1k, v2k, mv, nt, ti, mode, g, cost,
               A.sel(skipb, U32.inc(bcur), bcur), t, lbk, cut, gen, k, nst,
               ngs, nht, npr, stk, Array.get(U32, a2, 0))
        case 32:
          (a2, _) = p
          step(f, c, gg, 1, 7, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               nt, ti, mode, g, cost, bcur, t, lbk, cut, gen, ret, nst, ngs,
               nht, npr, stk, Array.get(U32, a2, 0))
        case 83:
          (a2, _) = p
          +ob = S.off_at(dep, c, gg)
          step(f, c, gg, 1, 84, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               nt, ti, mode, g, cost, bcur, t, lbk, cut, gen, ret, nst, ngs,
               nht, npr, stk, Array.get(U32, a2, U32.add(ob, bcur)))
        case 84:
          (a2, +o) = p
          +k2 = ret
          step(f, c, gg, 1, 85, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, cut,
               nt, ti, mode, g, cost, bcur, t, o, cut, gen, k2, nst,
               ngs, nht, npr, stk, Array.get(U32, a2, S.cap_at(pmk, k2, c, gg)))
        case 85:
          (a2, +cv) = p
          +k2 = ret
          a3 = Be.eval(a2, lbk, k2, cv, pmk, U32.inc(dep), c, gg)
          step(f, c, gg, 1, 86, ss, n, beta, pmk, dep, best, lb, lmk, cv, v2k,
               mv, nt, ti, mode, g, cost, bcur, t, lbk, cut, gen, k2, nst, ngs,
               nht, npr, stk, Array.get(U32, a3, Be.res_used(c, gg)))
        case 86:
          (a2, +used) = p
          +d = U32.sub(used, v1k)
          step(f, c, gg, 1, 87, ss, n, beta, pmk, dep, best, lb, used, v1k,
               d, mv, nt, ti, mode, g, cost, bcur, t, lbk, cut, gen, ret,
               nst, ngs, nht, npr, stk,
               Array.get(U32, a2, Be.res_ex(c, gg)))
        case 87:
          (a2, +pk) = p
          +ex = U32.and(pk, 1)
          +ck = U32.shrn(pk, 1n)
          step(f, c, gg, 1, A.sel(ex, 7, 88), ss, n, beta, pmk, dep, best, lb,
               lmk, v1k, v2k, mv, ck, ti, mode, g,
               U32.add(cost, U32.mul(ex, v2k)),
               A.sel(ex, U32.inc(bcur), bcur), t, lbk, cut, gen, ret, nst,
               ngs, nht, npr, stk, Array.get(U32, a2, 0))
        case 88:
          (a2, _) = p
          +b = U32.sub(cost, v1k)
          +cut2 = G.sat_sub(cut, b)
          +prune = A.ge01(lmk, cut2)
          step(f, c, gg, 1, A.sel(prune, 133, 134), ss, n, beta, pmk, dep, best,
               lb, lmk, v1k, v2k, mv, nt, ti, mode, g, cost, bcur, t, lbk,
               cut2, gen, ret, nst, ngs, nht, U32.add(npr, prune), stk,
               Array.get(U32, a2, 0))
        case 133:
          (a2, _) = p
          step(f, c, gg, 1, 120, ss, n, beta, pmk, dep, best, lb, lmk, v1k,
               v2k, mv, nt, ti, mode, g, cost, bcur, t, lbk, cut, gen,
               U32.add(cost, v2k), nst, ngs, nht, npr, stk,
               Array.get(U32, a2, 0))
        case 134:
          (a2, _) = p
          +k2 = ret
          +known = U32.mul(A.ge01(16, k2), lmk)
          stk2 : List<Fr> = Con{Gf{ss, n, beta, pmk, dep, mv, lb, g, cost,
                                   U32.inc(bcur), t, v1k}, stk}
          step(f, c, gg, 0, 0, lbk, k2, cut, nt, U32.inc(dep), cut, known, 0,
               0, 0, 4294967295, 0, 0, 0, 0, 0, 0, 0, 0, cut, gen, ret, nst,
               ngs, nht, npr, stk2, Array.get(U32, a2, 0))
        # ---------------------------------------------------- deliver ----
        case 120:
          # kind 0: pop a guess frame (or finish at the root); kind 1: pop a
          # state frame. Dispatch without matching `kind`.
          (a2, _) = p
          +k0 = A.eq01(kind, 0)
          step(f, c, gg, kind, A.sel(k0, 121, 122), ss, n, beta, pmk, dep,
               best, lb, lmk, v1k, v2k, mv, nt, ti, mode, g, cost, bcur, t, lbk,
               cut, gen, ret, nst, ngs, nht, npr, stk, Array.get(U32, a2, 0))
        case 121:
          match stk:
            case Nil{}:
              (a2, _) = p
              a3 = Array.set(U32, a2, cell_val(c, gg), ret)
              a4 = Array.set(U32, a3, cell_nst(c, gg), nst)
              a5 = Array.set(U32, a4, cell_ngs(c, gg), ngs)
              a6 = Array.set(U32, a5, cell_nht(c, gg), nht)
              Array.set(U32, a6, cell_npr(c, gg), npr)
            case Con{Gf{+ss2, +n2, +beta2, +pmk2, +dep2, +best2, +lb2, +g2,
                        +cost2, +bcur2, +t2, +used2}, rest}:
              (a2, _) = p
              +cost3 = U32.sub(U32.add(cost2, ret), used2)
              +pr = A.ge01(cost3, best2)
              step(f, c, gg, 1, A.sel(pr, 120, 7), ss2, n2, beta2, pmk2, dep2,
                   best2, lb2, lmk, v1k, v2k, mv, nt, ti, mode, g2, cost3,
                   bcur2, t2, used2, best2, gen, A.sel(pr, cost3, ret), nst,
                   ngs, nht, U32.add(npr, pr), rest, Array.get(U32, a2, 0))
            case Con{Sf{+ss2, +n2, +beta2, +pmk2, +dep2, +best2, +lb2,
                        +lmk2, +v1b, +v2b, +mv2, +nt2, +ti2, +mode2,
                        +rph2}, rest}:
              (a2, _) = p
              step(f, c, gg, 0, rph2, ss2, n2, beta2, pmk2, dep2, best2, lb2,
                   lmk2, v1b, v2b, mv2, nt2, ti2, mode2, g, cost, bcur, t,
                   lbk, cut, gen, ret, nst, ngs, nht, npr, rest,
                   Array.get(U32, a2, 0))
        case 122:
          match stk:
            case Nil{}:
              (a2, _) = p
              Array.set(U32, a2, cell_val(c, gg), ret)
            case Con{Sf{+ss2, +n2, +beta2, +pmk2, +dep2, +best2, +lb2,
                        +lmk2, +v1b, +v2b, +mv2, +nt2, +ti2, +mode2,
                        +rph2}, rest}:
              (a2, _) = p
              step(f, c, gg, 0, rph2, ss2, n2, beta2, pmk2, dep2, best2, lb2,
                   lmk2, v1b, v2b, mv2, nt2, ti2, mode2, g, cost, bcur, t,
                   lbk, cut, gen, ret, nst, ngs, nht, npr, rest,
                   Array.get(U32, a2, 0))
            case Con{Gf{+ss2, +n2, +beta2, +pmk2, +dep2, +best2, +lb2, +g2,
                        +cost2, +bcur2, +t2, +used2}, rest}:
              (a2, _) = p
              +cost3 = U32.sub(U32.add(cost2, ret), used2)
              +pr = A.ge01(cost3, best2)
              step(f, c, gg, 1, A.sel(pr, 120, 7), ss2, n2, beta2, pmk2, dep2,
                   best2, lb2, lmk, v1k, v2k, mv, nt, ti, mode, g2, cost3,
                   bcur2, t2, used2, best2, gen, A.sel(pr, cost3, ret), nst,
                   ngs, nht, U32.add(npr, pr), rest, Array.get(U32, a2, 0))
        case _:
          (a2, _) = p
          a2
