# Flat-array scan primitives for the ported search core.
#
# Every scan is one self-recursive def that receives the current read pair as
# its last argument and issues the next read as its own recursive argument.
# Phases are numbered; nothing is matched except the phase and the fuel.
#
# Regions used (all in the single flat state array, see geo.bend):
#   set[d]  : c cells  candidate ids of the set being processed at depth d
#   cnt[d]  : 256      generation-stamped response counts (cell = gen + count)
#   off[d]  : 256      bucket start offset for a response
#   cur[d]  : 256      scatter cursor for a response
#   ne[d]   : 256      distinct responses, in first-seen order
#
# A stale count cell reads as 0 branchlessly: (cell - gen) wraps above 2^31,
# so (cell - gen) >> 31 is 1 and the old count is 0.
import Base
import ./geo.bend as G
import ./arith.bend as A

# ------------------------------------------------------------- region bases ---

def set_at(+dep: U32, +c: U32, +gg: U32) -> U32:
  U32.add(G.off_sets(c, gg), U32.mul(dep, c))

def cnt_at(+dep: U32, +c: U32, +gg: U32) -> U32:
  U32.add(G.off_cnt(c, gg), U32.mul(dep, 256))

def off_at(+dep: U32, +c: U32, +gg: U32) -> U32:
  U32.add(G.off_off(c, gg), U32.mul(dep, 256))

def cur_at(+dep: U32, +c: U32, +gg: U32) -> U32:
  U32.add(G.off_h1(c, gg), U32.mul(dep, 256))

def ne_at(+dep: U32, +c: U32, +gg: U32) -> U32:
  U32.add(G.off_h2(c, gg), U32.mul(dep, 256))

def ent_at(+dep: U32, +c: U32, +gg: U32) -> U32:
  U32.add(G.off_ent(c, gg), U32.mul(dep, 256))

# cap2d[k][n] cell offset.
def cap_at(+k: U32, +n: U32, +c: U32, +gg: U32) -> U32:
  U32.add(U32.add(G.off_cap(c, gg), U32.mul(k, U32.inc(c))), n)

# ----------------------------------------------------------------- keepsakes ---
#
# The count region (256 cells per depth) is reused by every scan at that depth.
# Instead of stamping cells with a generation (which needs more bits than a
# 32-bit cell can spare once a search does millions of scans), `cnt` clears the
# cells its *previous* scan at the same depth touched: the distinct responses of
# that scan are exactly `ne[0..t)`, and cell 255 of the count block holds the
# number of them. So a scan starts from an all-zero count region without a
# 256-cell clear pass, and no caller can leave the region dirty.

# Per-depth counter of the count cells the previous scan touched (cell 255 of
# the count block; responses are <= 242 so it is never used for a count).
def dirty(+dep: U32, +c: U32, +gg: U32) -> U32:
  U32.add(cnt_at(dep, c, gg), 255)

def markgencell(+c: U32, +gg: U32) -> U32:
  U32.add(G.off_qgen(c, gg), 722)

def quickgencell(+c: U32, +gg: U32) -> U32:
  U32.add(G.off_qgen(c, gg), 723)

# ------------------------------------------------------------------ counting ---

# Result cells written by cnt: pk, n3, sq.
def pkcell(+c: U32, +gg: U32) -> U32:
  U32.add(U32.add(G.off_qgen(c, gg), 600), 0)

def n3cell(+c: U32, +gg: U32) -> U32:
  U32.add(U32.add(G.off_qgen(c, gg), 600), 1)

def sqcell(+c: U32, +gg: U32) -> U32:
  U32.add(U32.add(G.off_qgen(c, gg), 600), 11)

# Count the responses of guess `g` over set[sb..sb+n), skipping set element
# index `skip` (0xFFFFFFFF for none). Fills cnt[dep][r] = (gen<<10) + count for a
# fresh gen from the global counter, appends each first-seen response to
# ne[dep], and counts responses reaching 3.
# Returns pk = distinct | duplicates<<12 | has_win<<24.
#
# ph 9: the pair holds the global gen counter.  ph 0: the pair holds set[sb+i].
# ph 1: the pair holds fb[g][x].   ph 2: the pair holds cnt[r].
# ph 3: stop (dummy read).
def cnt_go(+fuel: Nat, +ph: U32, +j: U32, +lim: U32, +g: U32, +i: U32,
           +n: U32, +sb: U32, +skip: U32, +dep: U32, +c: U32, +gg: U32,
           +t: U32, +dup: U32, +hw: U32, +n3: U32, +sq: U32, +x: U32,
           +r: U32, p: Array<U32> & U32) -> Array<U32>:
  match fuel:
    case 0n:
      (a2, _) = p
      a2
    case 1n+p2:
      match ph:
        case 9:
          # p holds the number of cells the previous scan left dirty.
          (a2, +v) = p
          a3 = Array.set(U32, a2, dirty(dep, c, gg), 0)
          +nb0 = ne_at(dep, c, gg)
          +z = U32.shrn(U32.sub(v, 1), 31n)
          +idx9 = U32.add(nb0, U32.mul(z, U32.sub(sb, nb0)))
          cnt_go(p2, U32.mul(U32.sub(1, z), 7), 0, v, g, 0, n, sb, skip, dep,
                 c, gg, 0, 0, 0, 0, 0, 0, 0, Array.get(U32, a3, idx9))
        case 7:
          # p holds ne[j]: clear that response's count cell.
          (a2, +r0) = p
          a3 = Array.set(U32, a2, U32.add(cnt_at(dep, c, gg), r0), 0)
          +j2 = U32.inc(j)
          +last = U32.sub(1, U32.shrn(U32.sub(j2, lim), 31n))
          +nb = ne_at(dep, c, gg)
          +tb = U32.add(nb, j2)
          +idx7 = U32.add(tb, U32.mul(last, U32.sub(sb, tb)))
          cnt_go(p2, U32.mul(U32.sub(1, last), 7), j2, lim, g, 0, n, sb, skip,
                 dep, c, gg, 0, 0, 0, 0, 0, 0, 0,
                 Array.get(U32, a3, idx7))
        case 0:
          (a2, +v) = p
          +i2 = U32.inc(i)
          +last = U32.sub(1, U32.shrn(U32.sub(i2, n), 31n))
          +sk = U32.sub(1, U32.or(U32.shrn(U32.sub(i, skip), 31n),
                                  U32.shrn(U32.sub(skip, i), 31n)))
          +ti = U32.mul(U32.sub(1, last), U32.add(sb, i2))
          +fi = U32.add(U32.mul(g, c), v)
          +wid = U32.shrn(fi, 2n)
          +idx = U32.add(wid, U32.mul(sk, U32.sub(ti, wid)))
          cnt_go(p2, U32.add(U32.sub(1, sk), U32.mul(sk, U32.mul(last, 3))),
                 U32.and(fi, 3), lim, g, U32.add(i, sk), n, sb, skip, dep, c,
                 gg, t, dup, hw, n3, sq, U32.mul(U32.sub(1, sk), v), r,
                 Array.get(U32, a2, idx))
        case 1:
          # Byte extract with constant shifts only (see tab.pack_fb).
          (a2, +w) = p
          +hi = U32.sub(1, U32.shrn(U32.sub(j, 2), 31n))
          +t1 = U32.add(w, U32.mul(hi, U32.sub(U32.shrn(w, 16n), w)))
          +t2 = U32.add(t1, U32.mul(U32.and(j, 1),
                                    U32.sub(U32.shrn(t1, 8n), t1)))
          +fb = U32.and(t2, 255)
          +cb = cnt_at(dep, c, gg)
          cnt_go(p2, 2, 0, lim, g, i, n, sb, skip, dep, c, gg, t, dup, hw, n3,
                 sq, x, fb, Array.get(U32, a2, U32.add(cb, fb)))
        case 2:
          (a2, +old) = p
          +new = U32.shrn(U32.sub(old, 1), 31n)
          +cb = cnt_at(dep, c, gg)
          +nb = ne_at(dep, c, gg)
          +tb = U32.add(nb, t)
          +neidx = U32.add(U32.add(nb, 255),
                           U32.mul(new, U32.sub(tb, U32.add(nb, 255))))
          a3 = Array.set(U32, a2, U32.add(cb, r), U32.inc(old))
          a4 = Array.set(U32, a3, neidx, r)
          +i2 = U32.inc(i)
          +last = U32.sub(1, U32.shrn(U32.sub(i2, n), 31n))
          +idx2 = U32.mul(U32.sub(1, last), U32.add(sb, i2))
          +eqw = U32.sub(1, U32.or(U32.shrn(U32.sub(r, 121), 31n),
                                   U32.shrn(U32.sub(121, r), 31n)))
          +eq2 = U32.sub(1, U32.or(U32.shrn(U32.sub(old, 2), 31n),
                                   U32.shrn(U32.sub(2, old), 31n)))
          cnt_go(p2, U32.mul(last, 3), j, lim, g, i2, n, sb, skip, dep, c, gg,
                 U32.add(t, new), U32.add(dup, U32.sub(1, new)),
                 U32.or(hw, eqw), U32.add(n3, eq2),
                 U32.add(sq, U32.add(U32.mul(old, 2), 1)), 0, 0,
                 Array.get(U32, a4, idx2))
        case _:
          (a2, _) = p
          a5 = Array.set(U32, a2, pkcell(c, gg),
                         U32.add(U32.add(t, U32.mul(dup, 4096)),
                                 U32.mul(hw, 16777216)))
          a6 = Array.set(U32, a5, n3cell(c, gg), n3)
          a7 = Array.set(U32, a6, sqcell(c, gg), sq)
          Array.set(U32, a7, dirty(dep, c, gg), t)

def cnt(+g: U32, +sb: U32, +n: U32, +skip: U32, +dep: U32,
        +c: U32, +gg: U32, a: Array<U32>) -> Array<U32>:
  +fuel = Nat.add(Nat.add(Nat.mul(U32.to_nat(n), 8n), 68n),
                  Nat.mul(U32.to_nat(n), 4n))
  cnt_go(fuel, 9, 0, 0, g, 0, n, sb, skip, dep, c, gg, 0, 0, 0, 0, 0, 0, 0,
         Array.get(U32, a, dirty(dep, c, gg)))

# --------------------------------------------------------- stats from ne/cnt ---

def lbcell(+c: U32, +gg: U32) -> U32:
  U32.add(U32.add(G.off_qgen(c, gg), 600), 2)

def expcell(+c: U32, +gg: U32) -> U32:
  U32.add(U32.add(G.off_qgen(c, gg), 600), 3)

def write_stats(a: Array<U32>, +lb: U32, +exp: U32, +c: U32,
                +gg: U32) -> Array<U32>:
  a1 = Array.set(U32, a, lbcell(c, gg), lb)
  Array.set(U32, a1, expcell(c, gg), exp)


# lb = n + sum over distinct responses of cap[pmk][k]; exp = 1 + sum k*k.
# ph 8: the pair holds the global gen counter.  ph 0: the pair holds ne[j].
# ph 1: the pair holds cnt[r].   ph 2: the pair holds cap[pmk][k].
# ph 3: stop.
def stats_go(+fuel: Nat, +ph: U32, +j: U32, +t: U32, +dep: U32, +c: U32,
             +gg: U32, +pmk: U32, +lb: U32, +exp: U32, +gen: U32, +r: U32,
             +skipwin: U32, +rw: U32, p: Array<U32> & U32) -> Array<U32>:
  match fuel:
    case 0n:
      (a2, _) = p
      write_stats(a2, lb, exp, c, gg)
    case 1n+p2:
      match ph:
        case 8:
          (a2, +v) = p
          +nb = ne_at(dep, c, gg)
          stats_go(p2, 0, j, t, dep, c, gg, pmk, lb, exp, v, r, skipwin, rw,
                   Array.get(U32, a2, U32.add(nb, j)))
        case 0:
          (a2, +v) = p
          +cb = cnt_at(dep, c, gg)
          stats_go(p2, 1, j, t, dep, c, gg, pmk, lb, exp, gen, v, skipwin, v,
                   Array.get(U32, a2, U32.add(cb, v)))
        case 1:
          (a2, +k) = p
          +cb = cnt_at(dep, c, gg)
          a2a = Array.set(U32, a2, U32.add(cb, r), 0)
          +cp = cap_at(pmk, k, c, gg)
          stats_go(p2, 2, j, t, dep, c, gg, pmk, lb, exp, gen, k, skipwin, rw,
                   Array.get(U32, a2a, cp))
        case 2:
          (a2, +cv) = p
          +j2 = U32.inc(j)
          +last = A.eq01(j2, t)
          +nb = ne_at(dep, c, gg)
          +keep = U32.sub(1, U32.mul(skipwin, A.eq01(rw, 121)))
          stats_go(p2, A.sel(last, 3, 0), j2, t, dep, c, gg, pmk,
                   U32.add(lb, U32.mul(cv, keep)),
                   U32.add(exp, U32.mul(r, r)), gen, r, skipwin, rw,
                   Array.get(U32, a2, U32.add(nb, A.sel(last, 0, j2))))
        case _:
          (a2, _) = p
          write_stats(a2, lb, exp, c, gg)

# j0 = starting index into ne, t = number of distinct responses to walk.
def stats(+j0: U32, +t: U32, +dep: U32, +c: U32, +gg: U32, +pmk: U32,
          +lb0: U32, +exp0: U32, +skipwin: U32,
          a: Array<U32>) -> Array<U32>:
  +fuel = Nat.add(Nat.mul(U32.to_nat(t), 8n), 68n)
  +nb = ne_at(dep, c, gg)
  stats_go(fuel, 8, j0, t, dep, c, gg, pmk, lb0, exp0, 0, 0, skipwin, 0,
           Array.get(U32, a, dirty(dep, c, gg)))

# ------------------------------------------------------------------ offsets ---

# For each distinct response in ne order, off[r] = start of its bucket in the
# destination set and cur[r] = the same, as a running cursor.
# ph 8: the pair holds the global gen counter.  ph 0: the pair holds ne[j].
# ph 1: the pair holds cnt[r].   ph 2: stop.
def offs_go(+fuel: Nat, +ph: U32, +j: U32, +t: U32, +dep: U32, +dst: U32,
            +cur: U32, +c: U32, +gg: U32, +gen: U32, +r: U32,
            p: Array<U32> & U32) -> Array<U32>:
  match fuel:
    case 0n:
      (a2, _) = p
      a2
    case 1n+p2:
      match ph:
        case 8:
          (a2, +v) = p
          +nb = ne_at(dep, c, gg)
          offs_go(p2, 0, j, t, dep, dst, cur, c, gg, v, r,
                  Array.get(U32, a2, U32.add(nb, j)))
        case 0:
          (a2, +v) = p
          +cb = cnt_at(dep, c, gg)
          offs_go(p2, 1, j, t, dep, dst, cur, c, gg, gen, v,
                  Array.get(U32, a2, U32.add(cb, v)))
        case 1:
          (a2, +k) = p
          +cb = cnt_at(dep, c, gg)
          a2a = Array.set(U32, a2, U32.add(cb, r), 0)
          +ob = off_at(dep, c, gg)
          +ub = cur_at(dep, c, gg)
          +zb = ent_at(dep, c, gg)
          a3 = Array.set(U32, a2a, U32.add(ob, j), cur)
          a4 = Array.set(U32, a3, U32.add(zb, j), k)
          a5 = Array.set(U32, a4, U32.add(ub, r), cur)
          +j2 = U32.inc(j)
          +last = A.eq01(j2, t)
          +nb = ne_at(dep, c, gg)
          offs_go(p2, A.sel(last, 2, 0), j2, t, dep, U32.add(dst, k),
                  U32.add(cur, k), c, gg, gen, r,
                  Array.get(U32, a5, U32.add(nb, A.sel(last, 0, j2))))
        case _:
          (a2, _) = p
          a2

def offsets(+t: U32, +dep: U32, +dst: U32, +c: U32, +gg: U32,
            a: Array<U32>) -> Array<U32>:
  +fuel = Nat.add(Nat.mul(U32.to_nat(t), 8n), 68n)
  +nb = ne_at(dep, c, gg)
  offs_go(fuel, 8, 0, t, dep, dst, dst, c, gg, 0, 0,
          Array.get(U32, a, dirty(dep, c, gg)))

# ------------------------------------------------------------------ scatter ---

# Scatter set[sb..sb+n) into buckets at dst, using cur[] as the cursors.
# ph 0: the pair holds set[sb+i].   ph 1: the pair holds fb[g][x].
# ph 2: the pair holds cur[r].      ph 3: stop.
def sc_go(+fuel: Nat, +ph: U32, +i: U32, +n: U32, +sb: U32, +g: U32,
          +dep: U32, +dst: U32, +c: U32, +gg: U32, +x: U32, +r: U32,
          p: Array<U32> & U32) -> Array<U32>:
  match fuel:
    case 0n:
      (a2, _) = p
      a2
    case 1n+p2:
      match ph:
        case 0:
          (a2, +v) = p
          +fi = U32.add(U32.mul(g, c), v)
          sc_go(p2, 1, i, n, sb, g, dep, dst, c, gg, v, U32.and(fi, 3),
                Array.get(U32, a2, U32.shrn(fi, 2n)))
        case 1:
          (a2, +w) = p
          +hi = U32.sub(1, U32.shrn(U32.sub(r, 2), 31n))
          +t1 = U32.add(w, U32.mul(hi, U32.sub(U32.shrn(w, 16n), w)))
          +t2 = U32.add(t1, U32.mul(U32.and(r, 1),
                                    U32.sub(U32.shrn(t1, 8n), t1)))
          +fb = U32.and(t2, 255)
          +ub = cur_at(dep, c, gg)
          sc_go(p2, 2, i, n, sb, g, dep, dst, c, gg, x, fb,
                Array.get(U32, a2, U32.add(ub, fb)))
        case 2:
          (a2, +pos) = p
          +ub = cur_at(dep, c, gg)
          a3 = Array.set(U32, a2, U32.add(ub, r), U32.inc(pos))
          a4 = Array.set(U32, a3, pos, x)
          +i2 = U32.inc(i)
          +last = U32.sub(1, U32.shrn(U32.sub(i2, n), 31n))
          +idx = U32.mul(U32.sub(1, last), U32.add(sb, i2))
          sc_go(p2, U32.mul(last, 3), i2, n, sb, g, dep, dst, c, gg, 0, 0,
                Array.get(U32, a4, idx))
        case _:
          (a2, _) = p
          a2

def scatter(+g: U32, +sb: U32, +n: U32, +dep: U32, +dst: U32, +c: U32,
            +gg: U32, a: Array<U32>) -> Array<U32>:
  +fuel = Nat.add(Nat.mul(U32.to_nat(n), 8n), 64n)
  sc_go(fuel, 0, 0, n, sb, g, dep, dst, c, gg, 0, 0,
        Array.get(U32, a, sb))

# ------------------------------------------------------ entry order (Rust) ---
#
# Rust packs each eval entry as (count << 16) | !response and sorts the entry
# list by that word descending: bucket count descending, and on a tie response
# ascending. The order changes work, not values: pass 1 accumulates the `fast`
# bound bucket by bucket and abandons the whole guess as soon as it reaches the
# cutoff, so evaluating the big buckets first (as Rust does) lets that cutoff
# fire before the branch chain runs on the medium ones. The three parallel
# arrays (ent, off, ne) are permuted in place with a selection sort, so the
# result is always a valid permutation even if the fuel runs out.
#
# ph 0 outer head; 1/2 key of the current best; 3/4 inner scan; 10..14 load the
# six cells of a swap; 15 swaps them; 20 done.
def ord_go(+fuel: Nat, +ph: U32, +i: U32, +j: U32, +bi: U32, +bkey: U32,
           +kj: U32, +t: U32, +dep: U32, +c: U32, +gg: U32, +ei: U32,
           +ebi: U32, +oi: U32, +obi: U32, +ni: U32, +nbi: U32,
           r: Array<U32> & U32) -> Array<U32>:
  match fuel:
    case 0n:
      (a2, _) = r
      a2
    case 1n+f:
      match ph:
        case 0:
          (a2, _) = r
          +done = A.ge01(U32.inc(i), t)
          +eb = ent_at(dep, c, gg)
          +idx = A.sel(done, 0, U32.add(eb, i))
          ord_go(f, A.sel(done, 20, 1), i, U32.inc(i), i, 0, 0, t, dep, c, gg,
                 ei, ebi, oi, obi, ni, nbi, Array.get(U32, a2, idx))
        case 1:
          (a2, +v) = r
          +nb = ne_at(dep, c, gg)
          ord_go(f, 2, i, j, bi, U32.mul(v, 256), kj, t, dep, c, gg,
                 ei, ebi, oi, obi, ni, nbi, Array.get(U32, a2, U32.add(nb, bi)))
        case 2:
          (a2, +v) = r
          +eb = ent_at(dep, c, gg)
          ord_go(f, 3, i, j, bi, U32.add(bkey, U32.sub(255, v)), kj, t, dep, c,
                 gg, ei, ebi, oi, obi, ni, nbi,
                 Array.get(U32, a2, U32.add(eb, j)))
        case 3:
          (a2, +v) = r
          +nb = ne_at(dep, c, gg)
          ord_go(f, 4, i, j, bi, bkey, U32.mul(v, 256), t, dep, c, gg,
                 ei, ebi, oi, obi, ni, nbi, Array.get(U32, a2, U32.add(nb, j)))
        case 4:
          # kj is complete; keep the larger key and its index, advance j.
          (a2, +v) = r
          +kj2 = U32.add(kj, U32.sub(255, v))
          +gt = U32.shrn(U32.sub(bkey, kj2), 31n)
          +bi2 = A.sel(gt, j, bi)
          +bk2 = A.sel(gt, kj2, bkey)
          +j2 = U32.inc(j)
          +more = U32.sub(1, A.ge01(j2, t))
          +eb = ent_at(dep, c, gg)
          +idx = A.sel(more, U32.add(eb, j2), U32.add(eb, i))
          ord_go(f, A.sel(more, 3, 10), i, j2, bi2, bk2, kj2, t, dep, c, gg,
                 ei, ebi, oi, obi, ni, nbi, Array.get(U32, a2, idx))
        case 10:
          (a2, +v) = r
          +eb = ent_at(dep, c, gg)
          ord_go(f, 11, i, j, bi, bkey, kj, t, dep, c, gg, v, ebi, oi, obi, ni,
                 nbi, Array.get(U32, a2, U32.add(eb, bi)))
        case 11:
          (a2, +v) = r
          +ob = off_at(dep, c, gg)
          ord_go(f, 12, i, j, bi, bkey, kj, t, dep, c, gg, ei, v, oi, obi, ni,
                 nbi, Array.get(U32, a2, U32.add(ob, i)))
        case 12:
          (a2, +v) = r
          +ob = off_at(dep, c, gg)
          ord_go(f, 13, i, j, bi, bkey, kj, t, dep, c, gg, ei, ebi, v, obi, ni,
                 nbi, Array.get(U32, a2, U32.add(ob, bi)))
        case 13:
          (a2, +v) = r
          +nb = ne_at(dep, c, gg)
          ord_go(f, 14, i, j, bi, bkey, kj, t, dep, c, gg, ei, ebi, oi, v, ni,
                 nbi, Array.get(U32, a2, U32.add(nb, i)))
        case 14:
          (a2, +v) = r
          +nb = ne_at(dep, c, gg)
          ord_go(f, 15, i, j, bi, bkey, kj, t, dep, c, gg, ei, ebi, oi, obi, v,
                 nbi, Array.get(U32, a2, U32.add(nb, bi)))
        case 15:
          # Swap the two entries in one phase, then advance the outer index.
          (a2, +v) = r
          +eb = ent_at(dep, c, gg)
          +ob = off_at(dep, c, gg)
          +nb = ne_at(dep, c, gg)
          a3 = Array.set(U32, a2, U32.add(eb, i), ebi)
          a4 = Array.set(U32, a3, U32.add(eb, bi), ei)
          a5 = Array.set(U32, a4, U32.add(ob, i), obi)
          a6 = Array.set(U32, a5, U32.add(ob, bi), oi)
          a7 = Array.set(U32, a6, U32.add(nb, i), v)
          a8 = Array.set(U32, a7, U32.add(nb, bi), ni)
          +i2 = U32.inc(i)
          +idx = A.sel(A.ge01(i2, t), 0, U32.add(eb, i2))
          ord_go(f, 0, i2, j, bi, bkey, kj, t, dep, c, gg, ei, ebi, oi, obi, ni,
                 nbi, Array.get(U32, a8, idx))
        case 20:
          (a2, _) = r
          a2
        case _:
          (a2, _) = r
          a2

def ordsort(a: Array<U32>, +t: U32, +dep: U32, +c: U32,
            +gg: U32) -> Array<U32>:
  +tt = Nat.mul(U32.to_nat(t), U32.to_nat(t))
  +fuel = Nat.add(Nat.mul(tt, 4n), Nat.add(Nat.mul(U32.to_nat(t), 32n), 64n))
  ord_go(fuel, 0, 0, 0, 0, 0, 0, t, dep, c, gg, 0, 0, 0, 0, 0, 0,
         Array.get(U32, a, ent_at(dep, c, gg)))

# ------------------------------------------------------------ set hashing ---

# One set hash: h1/h2 = xor of the two Zobrist words of every candidate in
# set[base..base+n), written to cells o1/o2.
# ph 0: the pair holds set[base+j].  ph 1: z1[cand].  ph 2: z2[cand].  ph 3: stop.
def hset_go(+fuel: Nat, +ph: U32, +j: U32, +n: U32, +base: U32, +h1: U32,
            +h2: U32, +o1: U32, +o2: U32, +cand: U32, +c: U32, +gg: U32,
            p: Array<U32> & U32) -> Array<U32>:
  match fuel:
    case 0n:
      (a2, _) = p
      a2
    case 1n+f:
      match ph:
        case 0:
          (a2, +v) = p
          +z = G.off_z1(c, gg)
          hset_go(f, 1, j, n, base, h1, h2, o1, o2, v, c, gg,
                  Array.get(U32, a2, U32.add(z, v)))
        case 1:
          (a2, +v) = p
          +z = G.off_z2(c, gg)
          hset_go(f, 2, j, n, base, U32.xor(h1, v), h2, o1, o2, cand, c, gg,
                  Array.get(U32, a2, U32.add(z, cand)))
        case 2:
          (a2, +v) = p
          +j2 = U32.inc(j)
          +last = A.eq01(j2, n)
          +idx = A.sel(last, 0, U32.add(base, j2))
          hset_go(f, A.sel(last, 3, 0), j2, n, base, h1, U32.xor(h2, v), o1,
                  o2, cand, c, gg, Array.get(U32, a2, idx))
        case _:
          (a2, _) = p
          a3 = Array.set(U32, a2, o1, h1)
          Array.set(U32, a3, o2, h2)

def hset(a: Array<U32>, +base: U32, +n: U32, +o1: U32, +o2: U32, +c: U32,
         +gg: U32) -> Array<U32>:
  +fuel = Nat.add(Nat.mul(U32.to_nat(n), 16n), 64n)
  hset_go(fuel, 0, 0, n, base, 0, 0, o1, o2, 0, c, gg,
          Array.get(U32, a, base))
