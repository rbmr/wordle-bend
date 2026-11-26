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
import ./kup.bend as K
import ./p12.bend as P
import ./buck.bend as Be
import ./ttw.bend as W

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

def pack_val(+v: U32, +beta: U32, +n: U32) -> U32:
  U32.add(U32.add(U32.and(v, 262143), U32.mul(A.lt01(v, beta), 262144)),
          U32.shln(n, 19n))

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

# Root-parallel scratch. The probe run stops after the phase-2 tuple sort
# (phase 178) and writes the state it would have resumed with; four lane
# workers load it again at phase 190 and walk one quarter of the tuples each.
def pr_best(+c: U32, +gg: U32) -> U32:
  qcell(c, gg, 731)

def pr_lb(+c: U32, +gg: U32) -> U32:
  qcell(c, gg, 732)

def pr_lmk(+c: U32, +gg: U32) -> U32:
  qcell(c, gg, 733)

def pr_v1k(+c: U32, +gg: U32) -> U32:
  qcell(c, gg, 734)

def pr_v2k(+c: U32, +gg: U32) -> U32:
  qcell(c, gg, 735)

def pr_mv(+c: U32, +gg: U32) -> U32:
  qcell(c, gg, 736)

def pr_nt(+c: U32, +gg: U32) -> U32:
  qcell(c, gg, 737)

# The probe's counters, kept where the workers do not write: the merge adds
# them to the sum of the four lanes (each lane starts its counters at zero).
def pr_nst(+c: U32, +gg: U32) -> U32:
  qcell(c, gg, 738)

def pr_ngs(+c: U32, +gg: U32) -> U32:
  qcell(c, gg, 739)

def pr_nht(+c: U32, +gg: U32) -> U32:
  qcell(c, gg, 740)

def pr_npr(+c: U32, +gg: U32) -> U32:
  qcell(c, gg, 741)

# 1 in the array the driver passes to the probe; read only by a depth-0 state
# after the phase-2 sort, so a nested node can never stop there.
def pr_flag(+c: U32, +gg: U32) -> U32:
  qcell(c, gg, 742)

# p1/p2 tuple buffer bases for this depth.
def p1base(+dep: U32, +c: U32, +gg: U32) -> U32:
  U32.add(G.off_p1t(c, gg), U32.mul(dep, U32.mul(c, 3)))

def p2base(+dep: U32, +c: U32, +gg: U32) -> U32:
  U32.add(G.off_p2t(c, gg), U32.mul(dep, U32.mul(gg, 3)))

# Per-entry pass-1 results, 4 cells per bucket: used | exact<<20 | child_k<<21,
# the bucket's hash word 1, its hash word 2, and the k_upper computed by the
# approximate-bound pre-pass. The `flg` region is unused elsewhere and has 1024
# cells per depth, enough for the 243 possible buckets.
def flgcell(+dep: U32, +c: U32, +gg: U32, +j: U32) -> U32:
  U32.add(U32.add(G.off_flg(c, gg), U32.mul(dep, 1024)), U32.mul(j, 4))

def flgh1(+dep: U32, +c: U32, +gg: U32, +j: U32) -> U32:
  U32.add(flgcell(dep, c, gg, j), 1)

def flgh2(+dep: U32, +c: U32, +gg: U32, +j: U32) -> U32:
  U32.add(flgcell(dep, c, gg, j), 2)

def flgk(+dep: U32, +c: U32, +gg: U32, +j: U32) -> U32:
  U32.add(flgcell(dep, c, gg, j), 3)

# Rust keeps the approximate tight lower bound per eval entry in `p_lbs`; the
# unused `plb` region (1024 cells per depth) holds it here, 2 cells per bucket.
def plbv(+dep: U32, +c: U32, +gg: U32, +j: U32) -> U32:
  U32.add(U32.add(G.off_plb(c, gg), U32.mul(dep, 1024)), U32.mul(j, 2))

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
                          U32.mul(U32.and(bcur, ttmask()), 8))
          step(f, c, gg, 0, 93, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               nt, ti, mode, g, base, bcur, h2, lbk, cut, gen, ret, nst, ngs,
               nht, npr, stk, Array.get(U32, a2, U32.add(base, 4)))
        case 93:
          (a2, +k1) = p
          +hit1 = A.eq01(k1, bcur)
          step(f, c, gg, 0, A.sel(hit1, 94, 95), ss, n, beta, pmk, dep, best, lb, lmk,
               v1k, v2k, mv, nt, ti, mode, g, cost, bcur, t, lbk, cut, gen,
               ret, nst, ngs, nht, npr, stk,
               Array.get(U32, a2, A.sel(hit1, U32.add(cost, 5), cost)))
        case 94:
          (a2, +k2) = p
          +hit2 = A.eq01(k2, t)
          step(f, c, gg, 0, A.sel(hit2, 96, 95), ss, n, beta, pmk, dep, best, lb, lmk,
               v1k, v2k, mv, nt, ti, mode, g, cost, bcur, t, lbk, cut, gen,
               ret, nst, ngs, nht, npr, stk,
               Array.get(U32, a2, A.sel(hit2, U32.add(cost, 6), cost)))
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
          # A key match is only a candidate hit: the stored set must be this
          # set. `lbk` and `ti` are free before the guess scan, so they carry
          # the packed value and the witness word.
          (a2, +v) = p
          step(f, c, gg, 0, 124, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               nt, 0, mode, g, cost, bcur, t, v, cut, gen, ret, nst, ngs,
               nht, npr, stk, Array.get(U32, a2, U32.add(cost, 7)))
        case 99:
          (a2, +v) = p
          step(f, c, gg, 0, 124, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               nt, 0, mode, g, cost, bcur, t, v, cut, gen, ret, nst, ngs,
               nht, npr, stk, Array.get(U32, a2, U32.add(cost, 3)))
        case 124:
          (a2, +w) = p
          +okw = U32.mul(A.eq01(U32.shrn(lbk, 19n), n), A.nz(w))
          step(f, c, gg, 0, A.sel(okw, 125, 98), ss, n, beta, pmk, dep, best, lb, lmk,
               v1k, v2k, mv, nt, w, mode, g, cost, bcur, t, lbk, cut, gen, ret,
               nst, ngs, nht, npr, stk, Array.get(U32, a2, 0))
        case 125:
          (a2, _) = p
          a3 = W.wcmp(a2, ss, U32.sub(U32.add(G.off_wit(c, gg), ti), 1), n, c, gg)
          step(f, c, gg, 0, 126, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               nt, ti, mode, g, cost, bcur, t, lbk, cut, gen, ret, nst, ngs,
               nht, npr, stk, Array.get(U32, a3, W.wflagcell(c, gg)))
        case 126:
          (a2, +f2) = p
          step(f, c, gg, 0, A.sel(f2, 127, 98), ss, n, beta, pmk, dep, best, lb, lmk,
               v1k, v2k, mv, nt, ti, mode, g, cost, bcur, t, lbk, cut, gen,
               ret, nst, ngs, nht, npr, stk, Array.get(U32, a2, 0))
        case 127:
          (a2, _) = p
          +val = U32.and(lbk, 262143)
          +ex = U32.and(U32.shrn(lbk, 18n), 1)
          +take = U32.max(ex, A.ge01(val, beta))
          step(f, c, gg, 0, A.sel(take, 120, 89), ss, n, beta, pmk, dep, best,
               U32.max(lb, val), lmk, v1k, v2k, mv, nt, ti, mode, g, cost,
               bcur, t, 0, cut, gen, A.sel(take, val, ret), nst, ngs,
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
          # Rust's final local_lb: the base row cap[local_max_k][n] plus
          # tight_capacity_bound / phase2_capacity_bound with the best
          # branching factors found by phase 1 and phase 2.
          +p1 = A.sel(A.nz(v1k),
                      U32.from_nat(B.tight_capacity_bound(U32.to_nat(n),
                                                          U32.to_nat(v1k),
                                                          U32.to_nat(lmk))),
                      4294967295)
          +p2 = A.sel(A.nz(v2k),
                      U32.from_nat(B.phase2_capacity_bound(U32.to_nat(n),
                                                           U32.to_nat(v2k),
                                                           U32.to_nat(lmk))),
                      4294967295)
          # tl == MAXU means "not available" (Rust skips it).
          +tl = U32.min(p1, p2)
          +lb2 = U32.max(U32.max(lb, v),
                         U32.mul(tl, U32.sub(1, A.eq01(tl, 4294967295))))
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
          step(f, c, gg, 0, 183, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k,
               mv, nt, ti, mode, g, cost, bcur, t, lbk, cut, gen, ret, nst,
               ngs, nht, npr, stk, Array.get(U32, a2, pr_flag(c, gg)))
        case 183:
          (a2, +v) = p
          +b0 = p2base(dep, c, gg)
          a3 = P.sort3(a2, b0, nt)
          # A depth-0 state of the probe stops here and lets the driver resume
          # four lane workers at phase 190 (see 178).
          +probe = U32.mul(A.eq01(dep, 0), A.eq01(v, 1))
          step(f, c, gg, 0, A.sel(probe, 178, 170), ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               nt, 0, 2, g, cost, bcur, t, lbk, cut, gen, ret, nst, ngs, nht,
               npr, stk, Array.get(U32, a3, b0))
        # -------------------------------------------------- probe stop ---
        case 178:
          # Save everything the tuple walk would resume with, so four lane
          # workers can start at 170 without redoing the scans.
          (a2, _) = p
          a3 = Array.set(U32, a2, pr_best(c, gg), best)
          a4 = Array.set(U32, a3, pr_lb(c, gg), lb)
          a5 = Array.set(U32, a4, pr_lmk(c, gg), lmk)
          a6 = Array.set(U32, a5, pr_v1k(c, gg), v1k)
          a7 = Array.set(U32, a6, pr_v2k(c, gg), v2k)
          a8 = Array.set(U32, a7, pr_mv(c, gg), mv)
          a9 = Array.set(U32, a8, pr_nt(c, gg), nt)
          a10 = Array.set(U32, a9, pr_nst(c, gg), nst)
          a11 = Array.set(U32, a10, pr_ngs(c, gg), ngs)
          a12 = Array.set(U32, a11, pr_nht(c, gg), nht)
          a13 = Array.set(U32, a12, pr_npr(c, gg), npr)
          step(f, c, gg, 0, 120, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               nt, ti, mode, g, cost, bcur, t, lbk, cut, gen, best, nst, ngs,
               nht, npr, stk, Array.get(U32, a13, 0))
        case 180:
          # Probe entry: the driver has set the depth-0 stop flag (pr_flag).
          (a2, _) = p
          step(f, c, gg, 0, 0, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k,
               mv, nt, ti, mode, g, cost, bcur, t, lbk, cut, gen,
               ret, nst, ngs, nht, npr, stk, Array.get(U32, a2, 0))
        # -------------------------------------- lane worker entry (190..197) ---
        # Load the probe cells one per phase, then enter the tuple walk with
        # ti = 0, counters 0, and the lane mode the driver passed.
        case 190:
          (a2, _) = p
          step(f, c, gg, 0, 191, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k,
               mv, nt, ti, mode, g, cost, bcur, t, lbk, cut, gen, ret, 0, 0, 0,
               0, stk, Array.get(U32, a2, pr_best(c, gg)))
        case 191:
          (a2, +v) = p
          step(f, c, gg, 0, 192, ss, n, beta, pmk, dep, v, lb, lmk, v1k, v2k,
               mv, nt, ti, mode, g, cost, bcur, t, lbk, cut, gen, ret, 0, 0, 0,
               0, stk, Array.get(U32, a2, pr_lb(c, gg)))
        case 192:
          (a2, +v) = p
          step(f, c, gg, 0, 193, ss, n, beta, pmk, dep, best, v, lmk, v1k, v2k,
               mv, nt, ti, mode, g, cost, bcur, t, lbk, cut, gen, ret, 0, 0, 0,
               0, stk, Array.get(U32, a2, pr_lmk(c, gg)))
        case 193:
          (a2, +v) = p
          step(f, c, gg, 0, 194, ss, n, beta, pmk, dep, best, lb, v, v1k, v2k,
               mv, nt, ti, mode, g, cost, bcur, t, lbk, cut, gen, ret, 0, 0, 0,
               0, stk, Array.get(U32, a2, pr_v1k(c, gg)))
        case 194:
          (a2, +v) = p
          step(f, c, gg, 0, 195, ss, n, beta, pmk, dep, best, lb, lmk, v, v2k,
               mv, nt, ti, mode, g, cost, bcur, t, lbk, cut, gen, ret, 0, 0, 0,
               0, stk, Array.get(U32, a2, pr_v2k(c, gg)))
        case 195:
          (a2, +v) = p
          step(f, c, gg, 0, 196, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v,
               mv, nt, ti, mode, g, cost, bcur, t, lbk, cut, gen, ret, 0, 0, 0,
               0, stk, Array.get(U32, a2, pr_mv(c, gg)))
        case 196:
          (a2, +v) = p
          step(f, c, gg, 0, 197, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k,
               v, nt, ti, mode, g, cost, bcur, t, lbk, cut, gen, ret, 0, 0, 0,
               0, stk, Array.get(U32, a2, pr_nt(c, gg)))
        case 197:
          (a2, +v) = p
          step(f, c, gg, 0, 170, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k,
               mv, v, 0, mode, g, cost, bcur, t, lbk, cut, gen, 0, 0, 0, 0, 0,
               stk, Array.get(U32, a2, 0))
        # -------------------------------------------------- tuple walk ---
        case 170:
          (a2, _) = p
          +done = A.ge01(ti, nt)
          +base = A.sel(A.eq01(U32.and(mode, 3), 1), p1base(dep, c, gg),
                        p2base(dep, c, gg))
          +idx = A.sel(done, 0, U32.add(base, U32.mul(ti, 3)))
          +next = A.sel(done, A.sel(A.eq01(U32.and(mode, 3), 1), 50, 70), 171)
          step(f, c, gg, 0, next, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               nt, ti, mode, g, cost, bcur, t, lbk, cut, gen, ret, nst, ngs,
               nht, npr, stk, Array.get(U32, a2, idx))
        case 171:
          (a2, +v) = p
          +prune = A.ge01(v, best)
          +base = A.sel(A.eq01(U32.and(mode, 3), 1), p1base(dep, c, gg),
                        p2base(dep, c, gg))
          +idx = A.sel(prune, 0, U32.add(U32.add(base, U32.mul(ti, 3)), 2))
          +next = A.sel(prune, A.sel(A.eq01(U32.and(mode, 3), 1), 50, 70), 172)
          step(f, c, gg, 0, next, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k,
               U32.min(mv, v), nt, ti, mode, g, cost, bcur, t, lbk, cut, gen,
               ret, nst, ngs, nht, U32.add(npr, U32.mul(prune, U32.sub(nt, ti))),
               stk, Array.get(U32, a2, idx))
        case 172:
          # Lane filter: mode's bit 2 marks a parallel root worker (the driver
          # passes 6 + 8*lane), and then the walk takes only the tuples whose
          # index is congruent to the lane. A sequential state keeps mode = 1/2,
          # so every tuple is evaluated.
          (a2, +v) = p
          +lane = U32.shrn(mode, 3n)
          +par = U32.and(U32.shrn(mode, 2n), 1)
          # Witness lane (0) takes ti%16 == 0, the other three lanes the
          # remaining fifteen sixteenths in fifths.
          +r8 = U32.and(ti, 15)
          +part = U32.add(A.nz(r8),
                          U32.add(A.ge01(r8, 6), A.ge01(r8, 11)))
          +hit = U32.max(U32.sub(1, par), A.eq01(part, lane))
          step(f, c, gg, 0, A.sel(hit, 177, 176), ss, n, beta, pmk, dep, best, lb, lmk,
               v1k, v2k, mv, nt, ti, mode, A.sel(hit, v, g), cost, bcur, t,
               lbk, cut, gen, ret, nst, ngs, nht, npr, stk,
               Array.get(U32, a2, 0))
        case 176:
          (a2, _) = p
          step(f, c, gg, 0, 170, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k,
               mv, nt, U32.inc(ti), mode, g, cost, bcur, t, lbk, cut, gen, ret,
               nst, ngs, nht, npr, stk, Array.get(U32, a2, 0))
        case 177:
          (a2, _) = p
          stk2 : List<Fr> = Con{Sf{ss, n, beta, pmk, dep, best, lb, lmk, v1k,
                                   v2k, mv, nt, ti, mode, 173}, stk}
          # Rust passes the state's local_max_k (the largest bucket seen in
          # phase 1/2) to min_guess, which uses that row of the capacity table.
          step(f, c, gg, 1, 300, ss, n, beta, lmk, dep, best, lb, lmk, v1k, v2k, mv,
               nt, ti, mode, g, 0, 0, 0, 0, best, gen, ret, nst, ngs, nht, npr,
               stk2, Array.get(U32, a2, 0))
        case 173:
          (a2, _) = p
          +btr = A.lt01(ret, best)
          +best2 = A.sel(btr, ret, best)
          +stop = U32.and(btr, A.ge01(lb, ret))
          +next = A.sel(stop, A.sel(A.eq01(U32.and(mode, 3), 1), 50, 70), 170)
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
                          U32.mul(U32.and(bcur, ttmask()), 8))
          step(f, c, gg, 0, 103, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               nt, ti, mode, g, base, bcur, h2, lbk, cut, gen, ret, nst,
               ngs, nht, npr, stk, Array.get(U32, a2, U32.add(base, 4)))
        case 103:
          (a2, +k1) = p
          +same = A.eq01(k1, bcur)
          step(f, c, gg, 0, A.sel(same, 104, 105), ss, n, beta, pmk, dep, best, lb,
               lmk, v1k, v2k, mv, nt, ti, mode, g, cost, bcur, t, lbk, cut,
               gen, ret, nst, ngs, nht, npr, stk,
               Array.get(U32, a2, A.sel(same, U32.add(cost, 5), U32.add(cost, 6))))
        case 104:
          (a2, +k2) = p
          +same = A.eq01(k2, t)
          step(f, c, gg, 0, A.sel(same, 106, 105), ss, n, beta, pmk, dep, best, lb,
               lmk, v1k, v2k, mv, nt, ti, mode, g, cost, bcur, t, lbk, cut,
               gen, ret, nst, ngs, nht, npr, stk,
               Array.get(U32, a2, U32.add(cost, 6)))
        case 105:
          (a2, +v1) = p
          +old = U32.and(v1, 262143)
          +go1 = A.ge01(ret, old)
          +empty = A.eq01(bcur, 0)
          +put = U32.max(go1, empty)
          step(f, c, gg, 0, A.sel(put, 134, 109), ss, n, beta, pmk, dep, best, lb,
               lmk, v1k, v2k, mv, nt, ti, mode, g, cost, bcur, t, lbk, cut,
               gen, ret, nst, ngs, nht, npr, stk, Array.get(U32, a2, 0))
        case 134:
          (a2, _) = p
          a3 = W.wcopy(a2, ss, n, c, gg)
          step(f, c, gg, 0, 135, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               nt, ti, mode, g, cost, bcur, t, lbk, cut, gen, ret, nst, ngs,
               nht, npr, stk, Array.get(U32, a3, W.wrescell(c, gg)))
        case 135:
          # Slot 1 (depth preferred): key pair, packed value, witness word.
          (a2, +wo) = p
          a3 = Array.set(U32, a2, U32.add(cost, 4), bcur)
          a4 = Array.set(U32, a3, U32.add(cost, 5), t)
          a5 = Array.set(U32, a4, U32.add(cost, 6), pack_val(ret, beta, n))
          a6 = Array.set(U32, a5, U32.add(cost, 7), wo)
          step(f, c, gg, 0, 120, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               nt, ti, mode, g, cost, bcur, t, lbk, cut, gen, ret, nst, ngs,
               nht, npr, stk, Array.get(U32, a6, 0))
        case 106:
          (a2, +v1) = p
          +old = U32.and(v1, 262143)
          +oex = U32.and(U32.shrn(v1, 18n), 1)
          +upd = upd_ok(oex, old, ret, beta)
          step(f, c, gg, 0, A.sel(upd, 136, 120), ss, n, beta, pmk, dep, best, lb,
               lmk, v1k, v2k, mv, nt, ti, mode, g, cost, bcur, t, lbk, cut,
               gen, ret, nst, ngs, nht, npr, stk, Array.get(U32, a2, 0))
        case 136:
          (a2, _) = p
          a3 = W.wcopy(a2, ss, n, c, gg)
          step(f, c, gg, 0, 137, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               nt, ti, mode, g, cost, bcur, t, lbk, cut, gen, ret, nst, ngs,
               nht, npr, stk, Array.get(U32, a3, W.wrescell(c, gg)))
        case 137:
          (a2, +wo) = p
          a3 = Array.set(U32, a2, U32.add(cost, 4), bcur)
          a4 = Array.set(U32, a3, U32.add(cost, 5), t)
          a5 = Array.set(U32, a4, U32.add(cost, 6), pack_val(ret, beta, n))
          a6 = Array.set(U32, a5, U32.add(cost, 7), wo)
          step(f, c, gg, 0, 120, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               nt, ti, mode, g, cost, bcur, t, lbk, cut, gen, ret, nst, ngs,
               nht, npr, stk, Array.get(U32, a6, 0))
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
               Array.get(U32, a2, A.sel(same, U32.add(cost, 1), U32.add(cost, 2))))
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
          step(f, c, gg, 0, A.sel(upd, 138, 120), ss, n, beta, pmk, dep, best, lb,
               lmk, v1k, v2k, mv, nt, ti, mode, g, cost, bcur, t, lbk, cut,
               gen, ret, nst, ngs, nht, npr, stk, Array.get(U32, a2, 0))
        case 138:
          (a2, _) = p
          a3 = W.wcopy(a2, ss, n, c, gg)
          step(f, c, gg, 0, 139, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               nt, ti, mode, g, cost, bcur, t, lbk, cut, gen, ret, nst, ngs,
               nht, npr, stk, Array.get(U32, a3, W.wrescell(c, gg)))
        case 139:
          (a2, +wo) = p
          a3 = Array.set(U32, a2, cost, bcur)
          a4 = Array.set(U32, a3, U32.add(cost, 1), t)
          a5 = Array.set(U32, a4, U32.add(cost, 2), pack_val(ret, beta, n))
          a6 = Array.set(U32, a5, U32.add(cost, 3), wo)
          step(f, c, gg, 0, 120, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               nt, ti, mode, g, cost, bcur, t, lbk, cut, gen, ret, nst, ngs,
               nht, npr, stk, Array.get(U32, a6, 0))
        case 112:
          (a2, _) = p
          step(f, c, gg, 0, 140, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               nt, ti, mode, g, cost, bcur, t, lbk, cut, gen, ret, nst, ngs,
               nht, npr, stk, Array.get(U32, a2, 0))
        case 140:
          (a2, _) = p
          a3 = W.wcopy(a2, ss, n, c, gg)
          step(f, c, gg, 0, 141, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               nt, ti, mode, g, cost, bcur, t, lbk, cut, gen, ret, nst, ngs,
               nht, npr, stk, Array.get(U32, a3, W.wrescell(c, gg)))
        case 141:
          (a2, +wo) = p
          a3 = Array.set(U32, a2, cost, bcur)
          a4 = Array.set(U32, a3, U32.add(cost, 1), t)
          a5 = Array.set(U32, a4, U32.add(cost, 2), pack_val(ret, beta, n))
          a6 = Array.set(U32, a5, U32.add(cost, 3), wo)
          step(f, c, gg, 0, 120, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               nt, ti, mode, g, cost, bcur, t, lbk, cut, gen, ret, nst, ngs,
               nht, npr, stk, Array.get(U32, a6, 0))
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
          step(f, c, gg, 1, 303, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               nt, ti, mode, g, cost, 0, t, lbk, cut, gen, ret, nst, ngs, nht,
               npr, stk, Array.get(U32, a4, 0))
        case 303:
          # Rust sorts the eval entries by count descending (packed
          # (count<<16)|!response); the order decides how early pass 1's fast
          # bound reaches the cutoff, i.e. how many split buckets reach the
          # branch chain. Values are order-independent.
          (a2, _) = p
          a3 = S.ordsort(a2, t, dep, c, gg)
          step(f, c, gg, 1, 61, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               nt, ti, mode, g, cost, 0, t, lbk, cut, gen, ret, nst, ngs, nht,
               npr, stk, Array.get(U32, a3, 0))
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
          # Enter the approximate-bound pre-pass (Rust's eval_approx_tight_lb,
          # solver.rs: before any bucket is evaluated, every split bucket
          # (p_len > 15) contributes bucket_capacity_bound(p_len, k_upper,
          # parent_max_k) - cap to a fast lower bound; reaching the cutoff
          # abandons the whole guess). `lb` carries Rust's fast_cost through
          # the pre-pass and pass 1, so the cutoff fires where Rust's does.
          step(f, c, gg, 1, 400, ss, n, beta, pmk, dep, best, cost, 0, v1k, 0, mv, 0,
               0, mode, g, cost, 0, t, 0, cut, gen, ret, nst, ngs, nht, npr,
               stk, Array.get(U32, a2, 0))
        # --------------------- approximate tight bound over split buckets -----
        # Rust: for each eval bucket with p_len > 15,
        #   k_upper = compute_branching_factor_upper_bound(p)
        #   approx_tight_lb = bucket_capacity_bound(p_len, k_upper, parent_max_k)
        #                     .max(cap[parent_max_k][p_len])
        #   fast_cost += approx_tight_lb - cap; if fast_cost >= cutoff return.
        # k_upper is stored per entry for pass 1 (and, as in Rust, for the
        # branch chain that follows).
        case 400:
          (a2, _) = p
          +doneb = A.ge01(bcur, t)
          +idx0 = A.sel(doneb, 0, U32.add(S.ent_at(dep, c, gg), bcur))
          +bc2 = A.sel(doneb, 0, bcur)
          step(f, c, gg, 1, A.sel(doneb, 510, 401), ss, n, beta, pmk, dep, best, lb,
               lmk, v1k, v2k, mv, nt, ti, mode, g, cost, bc2, t, lbk, cut, gen,
               ret, nst, ngs, nht, npr, stk, Array.get(U32, a2, idx0))
        case 401:
          (a2, +k3) = p
          +small = U32.sub(1, A.ge01(k3, 16))
          +bc = U32.add(bcur, small)
          +idx0 = A.sel(small, 0, S.cap_at(pmk, k3, c, gg))
          step(f, c, gg, 1, A.sel(small, 400, 402), ss, n, beta, pmk, dep, best,
               lb, lmk, v1k, v2k, mv, nt, ti, mode, g, cost, bc, t, k3, cut,
               gen, k3, nst, ngs, nht, npr, stk, Array.get(U32, a2, idx0))
        case 402:
          (a2, +cv) = p
          +ob = S.off_at(dep, c, gg)
          step(f, c, gg, 1, 403, ss, n, beta, pmk, dep, best, lb, cv, v1k, v2k,
               mv, nt, ti, mode, g, cost, bcur, t, lbk, cut, gen, ret, nst, ngs,
               nht, npr, stk, Array.get(U32, a2, U32.add(ob, bcur)))
        case 403:
          (a2, +o) = p
          a3 = K.k_upper(a2, o, ret, c, gg)
          step(f, c, gg, 1, 404, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k,
               mv, nt, ti, mode, g, cost, bcur, t, o, cut, gen, ret, nst, ngs,
               nht, npr, stk, Array.get(U32, a3, K.kcell(c, gg)))
        case 404:
          (a2, +ku0) = p
          +ku = U32.max(ku0, 2)
          +bcb = U32.from_nat(B.bucket_capacity_bound(U32.to_nat(ret), U32.to_nat(ku),
                                                      U32.to_nat(pmk)))
          +approx = U32.max(bcb, lmk)
          +f2 = U32.add(lb, U32.sub(approx, lmk))
          +bad = A.ge01(f2, cut)
          a3 = Array.set(U32, a2, flgk(dep, c, gg, bcur), ku)
          a3b = Array.set(U32, a3, plbv(dep, c, gg, bcur), approx)
          step(f, c, gg, 1, A.sel(bad, 120, 400), ss, n, beta, pmk, dep, best,
               f2, lmk, v1k, 0, mv, nt, ti, mode, g, cost, U32.inc(bcur), t, lbk,
               cut, gen, A.sel(bad, f2, ret), nst, ngs, nht, U32.add(npr, bad),
               stk, Array.get(U32, a3b, 0))
        # -------------------------------- pass 1: used values for every bucket ---
        # Rust's min_guess_val_inner computes `used` (TT hit or quick eval) for
        # every bucket with count >= 3, adds used - cap to the running cost, and
        # only then recurses. Nothing is recursed here.
        case 510:
          # Head of the quick sub-pass: buckets with 3 <= k <= 15 first, so the
          # running fast bound (lb) reaches Rust's value before any split
          # bucket's branch chain runs (Rust: TT probe, approx pass, quick
          # pass, chain pass, recursion pass - in that order).
          (a2, _) = p
          +doneb = A.ge01(bcur, t)
          +over = A.ge01(lb, cut)
          +go = A.sel(doneb, 511, A.sel(over, 120, 80))
          step(f, c, gg, 1, go, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k,
               mv, 0, ti, mode, g, cost, A.sel(doneb, 0, bcur), t, lbk, cut, gen,
               A.sel(over, lb, ret), nst, ngs, nht,
               U32.add(npr, U32.mul(over, U32.sub(1, doneb))), stk,
               Array.get(U32, a2, 0))
        case 511:
          # Head of the split sub-pass: k >= 16, branch chain or TT hit.
          (a2, _) = p
          +doneb = A.ge01(bcur, t)
          +over = A.ge01(lb, cut)
          +go = A.sel(doneb, 200, A.sel(over, 120, 80))
          step(f, c, gg, 1, go, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k,
               mv, 1, ti, mode, g, cost, bcur, t, lbk, cut, gen,
               A.sel(over, lb, ret), nst, ngs, nht,
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
          +toosmall = U32.sub(1, A.ge01(k, 3))
          +big = A.ge01(k, 16)
          +badsize = U32.max(toosmall, A.sel(A.eq01(nt, 0), big, U32.sub(1, big)))
          +skipb = U32.max(A.eq01(lbk, 121), badsize)
          step(f, c, gg, 1, A.sel(skipb, 32, 83), ss, n, beta, pmk, dep, best, lb,
               lmk, v1k, v2k, mv, nt, ti, mode, g, cost,
               A.sel(skipb, U32.inc(bcur), bcur), t, lbk, cut, gen, k, nst,
               ngs, nht, npr, stk, Array.get(U32, a2, 0))
        case 32:
          (a2, _) = p
          step(f, c, gg, 1, A.sel(nt, 511, 510), ss, n, beta, pmk, dep, best, lb,
               lmk, v1k, v2k, mv, nt, ti, mode, g, cost, bcur, t, lbk, cut, gen,
               ret, nst, ngs, nht, npr, stk, Array.get(U32, a2, 0))
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
          a3 = Be.eval(a2, lbk, k2, cv, pmk, n, U32.inc(dep), c, gg)
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
          # Save used | exact<<20 | child_k<<21 and the bucket hash for pass 2.
          +cellv = U32.add(U32.add(lmk, U32.mul(ex, 1048576)),
                           U32.mul(ck, 2097152))
          a3 = Array.set(U32, a2, flgcell(dep, c, gg, bcur), cellv)
          step(f, c, gg, 1, 213, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k,
               mv, nt, U32.add(ti, U32.sub(1, ex)), mode, g, U32.add(cost, v2k),
               bcur, t, lbk, cut, gen, ret, nst, ngs, nht, npr, stk,
               Array.get(U32, a3, plbv(dep, c, gg, bcur)))
        case 213:
          # fast += used - approx (split buckets), used - cap (quick buckets).
          (a2, +ap) = p
          +ap2 = A.sel(A.ge01(ret, 16), ap, v1k)
          +fast2 = U32.add(lb, G.sat_sub(lmk, ap2))
          step(f, c, gg, 1, 209, ss, n, beta, pmk, dep, best, fast2, lmk, v1k,
               v2k, mv, nt, ti, mode, g, cost, bcur, t, lbk, cut, gen, ret, nst,
               ngs, nht, npr, stk, Array.get(U32, a2, hsh1(U32.inc(dep), c, gg)))
        case 209:
          # Be.eval wrote the bucket hash into the child's per-depth cell; copy
          # both words into the per-entry cells for pass 2.
          (a2, +h1) = p
          a3 = Array.set(U32, a2, flgh1(dep, c, gg, bcur), h1)
          step(f, c, gg, 1, 210, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k,
               mv, nt, ti, mode, g, cost, bcur, t, lbk, cut, gen, ret, nst,
               ngs, nht, npr, stk,
               Array.get(U32, a3, hsh2(U32.inc(dep), c, gg)))
        case 210:
          (a2, +h2) = p
          a3 = Array.set(U32, a2, flgh2(dep, c, gg, bcur), h2)
          step(f, c, gg, 1, A.sel(nt, 511, 510), ss, n, beta, pmk, dep, best, lb,
               lmk, v1k, v2k, mv, nt, ti, mode, g, cost, U32.inc(bcur), t, lbk,
               cut, gen, ret, nst, ngs, nht, npr, stk, Array.get(U32, a3, 0))
        # End of pass 1: every bucket's used value is in `cost`.
        case 200:
          (a2, _) = p
          +nonex = A.eq01(ti, 0)
          +over = A.ge01(cost, cut)
          +stop = U32.max(nonex, over)
          step(f, c, gg, 1, A.sel(stop, 120, 201), ss, n, beta, pmk, dep, best,
               lb, lmk, v1k, v2k, mv, nt, ti, mode, g, cost, 0, t, lbk, cut,
               gen, A.sel(stop, cost, ret), nst, ngs, nht,
               U32.add(npr, U32.mul(over, U32.sub(1, nonex))), stk,
               Array.get(U32, a2, 0))
        # ------------------------------- pass 2: recurse into inexact buckets ---
        case 201:
          (a2, _) = p
          +doneb = A.ge01(bcur, t)
          +over = A.ge01(cost, cut)
          +stop = U32.max(doneb, over)
          step(f, c, gg, 1, A.sel(doneb, 120, A.sel(over, 120, 202)), ss, n, beta,
               pmk, dep, best, lb, lmk, v1k, v2k, mv, nt, ti, mode, g, cost,
               bcur, t, lbk, cut, gen, A.sel(stop, cost, ret), nst, ngs, nht,
               U32.add(npr, U32.mul(over, U32.sub(1, doneb))), stk,
               Array.get(U32, a2, 0))
        case 202:
          (a2, _) = p
          +zb = S.ent_at(dep, c, gg)
          step(f, c, gg, 1, 203, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               nt, ti, mode, g, cost, bcur, t, lbk, cut, gen, ret, nst, ngs,
               nht, npr, stk, Array.get(U32, a2, U32.add(zb, bcur)))
        case 203:
          # Buckets with fewer than 3 candidates were skipped in pass 1 and must
          # be skipped here too (their saved cell is stale).
          (a2, +k) = p
          +skipb = U32.sub(1, A.ge01(k, 3))
          step(f, c, gg, 1, A.sel(skipb, 201, 204), ss, n, beta, pmk, dep, best,
               lb, lmk, k, v2k, mv, nt, ti, mode, g, cost,
               U32.add(bcur, skipb), t, lbk, cut, gen, k, nst, ngs, nht, npr,
               stk, Array.get(U32, a2, 0))
        case 204:
          (a2, _) = p
          step(f, c, gg, 1, 205, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               nt, ti, mode, g, cost, bcur, t, lbk, cut, gen, ret, nst, ngs,
               nht, npr, stk,
               Array.get(U32, a2, flgcell(dep, c, gg, bcur)))
        case 205:
          (a2, +cell) = p
          +ex = U32.and(U32.shrn(cell, 20n), 1)
          step(f, c, gg, 1, A.sel(ex, 201, 206), ss, n, beta, pmk, dep, best, lb,
               lmk, v1k, v2k, mv, nt, ti, mode, g, cost,
               U32.add(bcur, ex), t, lbk, cut, gen, cell, nst, ngs, nht, npr,
               stk, Array.get(U32, a2, 0))
        case 206:
          (a2, _) = p
          +ob = S.off_at(dep, c, gg)
          step(f, c, gg, 1, 207, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k, mv,
               nt, ti, mode, g, cost, bcur, t, lbk, cut, gen, ret, nst, ngs,
               nht, npr, stk, Array.get(U32, a2, U32.add(ob, bcur)))
        case 207:
          (a2, +o) = p
          +used = U32.and(ret, 1048575)
          +ck = U32.shrn(ret, 21n)
          +b = G.sat_sub(cost, used)
          +cut2 = G.sat_sub(cut, b)
          +prune = A.ge01(used, cut2)
          step(f, c, gg, 1, A.sel(prune, 133, 208), ss, n, beta, pmk, dep, best,
               lb, used, v1k, v2k, mv, ck, cut2, mode, g, cost, bcur, t, o,
               cut, gen, ret, nst, ngs, nht, U32.add(npr, prune), stk,
               Array.get(U32, a2, 0))
        case 133:
          (a2, _) = p
          step(f, c, gg, 1, 120, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k,
               mv, nt, ti, mode, g, cost, bcur, t, lbk, cut, gen, cost, nst,
               ngs, nht, npr, stk, Array.get(U32, a2, 0))
        case 208:
          # lmk = used, v1k = bucket size, nt = child k, ti = effective beta.
          (a2, _) = p
          step(f, c, gg, 1, 211, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k,
               mv, nt, ti, mode, g, cost, bcur, t, lbk, cut, gen, ret, nst,
               ngs, nht, npr, stk,
               Array.get(U32, a2, flgh1(dep, c, gg, bcur)))
        case 211:
          # The child state reads its set hash from the per-depth cell, so the
          # bucket's hash has to be written there just before the descent.
          (a2, +h1) = p
          a3 = Array.set(U32, a2, hsh1(U32.inc(dep), c, gg), h1)
          step(f, c, gg, 1, 212, ss, n, beta, pmk, dep, best, lb, lmk, v1k, v2k,
               mv, nt, ti, mode, g, cost, bcur, t, lbk, cut, gen, ret, nst,
               ngs, nht, npr, stk, Array.get(U32, a3, flgh2(dep, c, gg, bcur)))
        case 212:
          (a2, +h2) = p
          a3 = Array.set(U32, a2, hsh2(U32.inc(dep), c, gg), h2)
          # Rust passes the bucket's used value as known_quick unless the
          # bucket took the c_len>16 split path (parent > 16 and bucket > 15).
          +known = U32.mul(U32.max(A.ge01(15, v1k), A.ge01(16, n)), lmk)
          stk2 : List<Fr> = Con{Gf{ss, n, beta, pmk, dep, cut, lb, g, cost,
                                   U32.inc(bcur), t, lmk}, stk}
          step(f, c, gg, 0, 0, lbk, v1k, ti, nt, U32.inc(dep), ti, known, 0,
               0, 0, 4294967295, 0, 0, 0, 0, 0, 0, 0, 0, ti, gen, ret, nst,
               ngs, nht, npr, stk2, Array.get(U32, a3, 0))
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
              step(f, c, gg, 1, A.sel(pr, 120, 201), ss2, n2, beta2, pmk2, dep2,
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
              step(f, c, gg, 1, A.sel(pr, 120, 201), ss2, n2, beta2, pmk2, dep2,
                   best2, lb2, lmk, v1k, v2k, mv, nt, ti, mode, g2, cost3,
                   bcur2, t2, used2, best2, gen, A.sel(pr, cost3, ret), nst,
                   ngs, nht, U32.add(npr, pr), rest, Array.get(U32, a2, 0))
        case _:
          (a2, _) = p
          a2
