# Rust's letter-profile fast path for the branching-factor scan, transcribed
# from `heuristic::compute_max_branching_factor_seq_with_target` (heuristic.rs
# 612). The per-position profile aggregates are the ones `kup` already builds;
# this file turns them into the per-letter factor table and provides the two
# filters that skip a guess before its response row is counted.
#
# Layout inside the prof region (G.off_prof, 512 cells):
#   0..29   per position i: i*6 + 0 ge2_u, 1 eq3_u, 2 ge2_1, 3 eq3_1,
#           4 ge2_2, 5 eq3_2
#   30      active_letter_mask
#   64..223 m_tab[i*32 + letter], a factor in 1..3
import Base
import ./geo.bend as G
import ./arith.bend as A

def actcell(+c: U32, +gg: U32) -> U32:
  U32.add(G.off_prof(c, gg), 30)

def pcell(+c: U32, +gg: U32, +i: U32, +q: U32) -> U32:
  U32.add(U32.add(G.off_prof(c, gg), U32.mul(i, 6)), q)

def mcell(+c: U32, +gg: U32, +i: U32, +l: U32) -> U32:
  U32.add(U32.add(G.off_prof(c, gg), 64), U32.add(U32.mul(i, 32), l))

# heuristic::min_non_overlap_for_len(5, max_k). max_k is bounded by the number
# of responses (242), so only the last five steps of Rust's ladder can fire.
def mnover(+mx: U32) -> U32:
  U32.add(U32.add(U32.add(U32.add(1, A.lt01(mx, 81)), A.lt01(mx, 27)),
                  A.lt01(mx, 9)), A.lt01(mx, 3))

# Population count of a 32-bit word as a U32. U32.popcount returns a Nat (and
# going through it costs a Word.to_nat recursion), so the same bit trick is
# done in U32 arithmetic.
def pc32(+n: U32) -> U32:
  +a = U32.sub(n, U32.and(U32.shrn(n, 1n), 1431655765))
  +b = U32.add(U32.and(a, 858993459), U32.and(U32.shrn(a, 2n), 858993459))
  +c = U32.and(U32.add(b, U32.shrn(b, 4n)), 252645135)
  U32.shrn(U32.mul(c, 16843009), 24n)

# --------------------------------------------------------------- m_tab build ---
#
# m_tab[i][l] is Rust's per-position factor: 1 by default, 2 + the eq3 bit for
# a letter in that position's ge2 mask. Rust writes the three mask classes in
# the order u, then 1, then 2 (offsets 0/32/64), so the last write wins; here
# the same priority is resolved arithmetically.
# ph 0..5 read the six masks of row i; 6 writes one cell and advances;
# 7 is done.
def mt_go(+fuel: Nat, +ph: U32, +i: U32, +l: U32, +g2u: U32, +e3u: U32,
          +g21: U32, +e31: U32, +g22: U32, +e32: U32, +c: U32, +gg: U32,
          p: Array<U32> & U32) -> Array<U32>:
  match fuel:
    case 0n:
      (a2, _) = p
      a2
    case 1n+f:
      match ph:
        case 10:
          (a2, _) = p
          a3 = Array.set(U32, a2, actcell(c, gg), 0)
          mt_go(f, 0, i, l, g2u, e3u, g21, e31, g22, e32, c, gg,
                Array.get(U32, a3, 0))
        case 0:
          (a2, _) = p
          mt_go(f, 1, i, l, g2u, e3u, g21, e31, g22, e32, c, gg,
                Array.get(U32, a2, pcell(c, gg, i, 0)))
        case 1:
          (a2, +v) = p
          mt_go(f, 2, i, l, g2u, v, g21, e31, g22, e32, c, gg,
                Array.get(U32, a2, pcell(c, gg, i, 1)))
        case 2:
          (a2, +v) = p
          mt_go(f, 3, i, l, g2u, e3u, v, e31, g22, e32, c, gg,
                Array.get(U32, a2, pcell(c, gg, i, 2)))
        case 3:
          (a2, +v) = p
          mt_go(f, 4, i, l, g2u, e3u, g21, v, g22, e32, c, gg,
                Array.get(U32, a2, pcell(c, gg, i, 3)))
        case 4:
          (a2, +v) = p
          mt_go(f, 5, i, l, g2u, e3u, g21, e31, v, e32, c, gg,
                Array.get(U32, a2, pcell(c, gg, i, 4)))
        case 5:
          (a2, +v) = p
          mt_go(f, 8, i, l, g2u, e3u, g21, e31, g22, v, c, gg,
                Array.get(U32, a2, pcell(c, gg, i, 5)))
        case 8:
          (a2, _) = p
          mt_go(f, 9, i, l, g2u, e3u, g21, e31, g22, e32, c, gg,
                Array.get(U32, a2, actcell(c, gg)))
        case 9:
          # active_letter_mask |= ge2_u | ge2_1 | ge2_2 for this row.
          (a2, +ac) = p
          a3 = Array.set(U32, a2, actcell(c, gg),
                         U32.or(ac, U32.or(g2u, U32.or(g21, g22))))
          mt_go(f, 6, i, l, g2u, e3u, g21, e31, g22, e32, c, gg,
                Array.get(U32, a3, 0))
        case 6:
          (a2, _) = p
          +bit = U32.shln(1, U32.to_nat(l))
          +w2 = A.nz(U32.and(g22, bit))
          +w1 = U32.mul(U32.sub(1, w2), A.nz(U32.and(g21, bit)))
          +w0 = U32.mul(U32.sub(1, w2),
                        U32.mul(U32.sub(1, w1), A.nz(U32.and(g2u, bit))))
          +f2 = U32.mul(w2, U32.add(1, A.nz(U32.and(e32, bit))))
          +f1 = U32.mul(w1, U32.add(1, A.nz(U32.and(e31, bit))))
          +f0 = U32.mul(w0, U32.add(1, A.nz(U32.and(e3u, bit))))
          +fv = U32.add(U32.add(U32.add(1, f2), f1), f0)
          a3 = Array.set(U32, a2, mcell(c, gg, i, l), fv)
          +l2 = U32.inc(l)
          +rown = A.ge01(l2, 32)
          +l3 = U32.mul(U32.sub(1, rown), l2)
          +i2 = U32.add(i, rown)
          +done = A.ge01(i2, 5)
          +idx = A.sel(done, 0, pcell(c, gg, i2, 0))
          mt_go(f, A.sel(done, 7, 0), i2, l3, g2u, e3u, g21, e31, g22, e32,
                c, gg, Array.get(U32, a3, idx))
        case _:
          (a2, _) = p
          a2

def mtab(a: Array<U32>, +c: U32, +gg: U32) -> Array<U32>:
  +fuel = Nat.mul(8192n, 2n)
  mt_go(fuel, 10, 0, 0, 0, 0, 0, 0, 0, 0, c, gg, Array.get(U32, a, 0))

# ------------------------------------------------ distinct-response count ------
#
# heuristic::count_unique_responses_from_row_u8 as a lean machine: the number of
# distinct responses of guess `g` over set[o..o+k), with no bucket statistics
# (the branching scans need only the count). Count cells are cleared through a
# touched list, so the region is all-zero on entry and on exit.
#
# Layout: counts at prof+224 (256 cells), touched list at prof+480 (256),
# result at prof+736.
def dn_cell(+c: U32, +gg: U32, +r: U32) -> U32:
  U32.add(U32.add(G.off_prof(c, gg), 224), r)

def dnt_cell(+c: U32, +gg: U32, +j: U32) -> U32:
  U32.add(U32.add(G.off_prof(c, gg), 480), j)

def dnres(+c: U32, +gg: U32) -> U32:
  U32.add(G.off_prof(c, gg), 736)

# ph 0 set[o+i] -> 1 fb[fb+v] -> 2 cnt[r] -> 3 count (two writes, advance)
# -> 4..5 clear the touched cells -> 6 write the result.
#
# The region bases are precomputed once per call of dcount (`pb` = off_prof,
# `fb` = g*c): the offset chain is ~30 arithmetic ops (three multiplies by c and
# five by the depth count), and this is the hottest loop of the port.
def dn_go(+fuel: Nat, +ph: U32, +i: U32, +j: U32, +fb: U32, +o: U32, +k: U32,
          +t: U32, +r: U32, +pb: U32, p: Array<U32> & U32) -> Array<U32>:
  match fuel:
    case 0n:
      (a2, _) = p
      a2
    case 1n+f:
      match ph:
        case 0:
          (a2, _) = p
          dn_go(f, 1, i, j, fb, o, k, t, r, pb, Array.get(U32, a2, U32.add(o, i)))
        case 1:
          (a2, +v) = p
          dn_go(f, 2, i, j, fb, o, k, t, r, pb, Array.get(U32, a2, U32.add(fb, v)))
        case 2:
          (a2, +v) = p
          dn_go(f, 3, i, j, fb, o, k, t, v, pb,
                Array.get(U32, a2, U32.add(U32.add(pb, 224), v)))
        case 3:
          (a2, +v) = p
          +new = A.eq01(v, 0)
          a3 = Array.set(U32, a2, U32.add(U32.add(pb, 224), r), U32.inc(v))
          a4 = Array.set(U32, a3, U32.add(U32.add(pb, 480), t), r)
          +i2 = U32.inc(i)
          +t2 = U32.add(t, new)
          +done = A.ge01(i2, k)
          +idx = A.sel(done, U32.add(pb, 224), U32.add(o, i2))
          dn_go(f, A.sel(done, 4, 0), i2, 0, fb, o, k, t2, r, pb,
                Array.get(U32, a4, idx))
        case 4:
          (a2, _) = p
          +done = A.ge01(j, t)
          +idx = A.sel(done, U32.add(pb, 224), U32.add(U32.add(pb, 480), j))
          dn_go(f, A.sel(done, 6, 5), i, j, fb, o, k, t, r, pb,
                Array.get(U32, a2, idx))
        case 5:
          (a2, +v) = p
          a3 = Array.set(U32, a2, U32.add(U32.add(pb, 224), v), 0)
          +j2 = U32.inc(j)
          +done = A.ge01(j2, t)
          +idx = A.sel(done, U32.add(pb, 224), U32.add(U32.add(pb, 480), j2))
          dn_go(f, A.sel(done, 6, 4), i, j2, fb, o, k, t, r, pb,
                Array.get(U32, a3, idx))
        case 6:
          (a2, _) = p
          a3 = Array.set(U32, a2, U32.add(pb, 736), t)
          dn_go(f, 7, i, j, fb, o, k, t, r, pb, Array.get(U32, a3, 0))
        case _:
          (a2, _) = p
          a2

def dcount(a: Array<U32>, +g: U32, +o: U32, +k: U32, +c: U32,
           +gg: U32) -> Array<U32>:
  +fb = U32.mul(g, c)
  +pb = G.off_prof(c, gg)
  +fuel = Nat.add(Nat.mul(U32.to_nat(k), 8n), 80n)
  dn_go(fuel, 0, 0, 0, fb, o, k, 0, 0, pb, Array.get(U32, a, o))
