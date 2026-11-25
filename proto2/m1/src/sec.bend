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

# ------------------------------------------------------------------ counting ---

# Result cells written by cnt: pk, n3, sq.
def pkcell(+c: U32, +gg: U32) -> U32:
  U32.add(U32.add(G.off_qgen(c, gg), 600), 0)

def n3cell(+c: U32, +gg: U32) -> U32:
  U32.add(U32.add(G.off_qgen(c, gg), 600), 1)

def sqcell(+c: U32, +gg: U32) -> U32:
  U32.add(U32.add(G.off_qgen(c, gg), 600), 11)

# Count the responses of guess `g` over set[sb..sb+n), skipping set element
# index `skip` (0xFFFFFFFF for none). Fills cnt[dep][r] = gen + count, appends
# each first-seen response to ne[dep], and counts responses reaching 3.
# Returns pk = distinct | duplicates<<12 | has_win<<24.
#
# ph 0: the pair holds set[sb+i].            ph 1: the pair holds fb[g][x].
# ph 2: the pair holds cnt[r].               ph 3: stop (dummy read).
def cnt_go(+fuel: Nat, +ph: U32, +g: U32, +i: U32, +n: U32, +sb: U32,
           +skip: U32, +gen: U32, +dep: U32, +c: U32, +gg: U32,
           +t: U32, +dup: U32, +hw: U32, +n3: U32, +sq: U32, +x: U32,
           +r: U32, p: Array<U32> & U32) -> Array<U32>:
  match fuel:
    case 0n:
      (a2, _) = p
      a2
    case 1n+p2:
      match ph:
        case 0:
          (a2, +v) = p
          +i2 = U32.inc(i)
          +last = A.eq01(i2, n)
          +sk = A.eq01(i, skip)
          +idx = A.sel(sk, A.sel(last, 0, U32.add(sb, i2)),
                       U32.add(U32.mul(g, c), v))
          cnt_go(p2, A.sel(sk, A.sel(last, 3, 0), 1), g, A.sel(sk, i2, i), n,
                 sb, skip, gen, dep, c, gg, t, dup, hw, n3, sq,
                 A.sel(sk, 0, v), r, Array.get(U32, a2, idx))
        case 1:
          (a2, +fb) = p
          +cb = cnt_at(dep, c, gg)
          cnt_go(p2, 2, g, i, n, sb, skip, gen, dep, c, gg, t, dup, hw, n3, sq,
                 x, fb, Array.get(U32, a2, U32.add(cb, fb)))
        case 2:
          (a2, +cell) = p
          +diff = U32.sub(cell, gen)
          +fresh = U32.sub(1, U32.shrn(diff, 31n))
          +old = U32.mul(diff, fresh)
          +new = A.eq01(old, 0)
          +cb = cnt_at(dep, c, gg)
          +nb = ne_at(dep, c, gg)
          +neidx = A.sel(new, U32.add(nb, t), U32.add(nb, 255))
          a3 = Array.set(U32, a2, U32.add(cb, r), U32.add(gen, U32.inc(old)))
          a4 = Array.set(U32, a3, neidx, r)
          +i2 = U32.inc(i)
          +last = A.eq01(i2, n)
          +idx = A.sel(last, 0, U32.add(sb, i2))
          cnt_go(p2, A.sel(last, 3, 0), g, i2, n, sb, skip, gen, dep, c, gg,
                 U32.add(t, new), U32.add(dup, U32.sub(1, new)),
                 U32.max(hw, A.eq01(r, 121)), U32.add(n3, A.eq01(old, 2)),
                 U32.add(sq, U32.inc(U32.mul(old, 2))), 0, 0,
                 Array.get(U32, a4, idx))
        case _:
          (a2, _) = p
          a5 = Array.set(U32, a2, pkcell(c, gg),
                         U32.add(U32.add(t, U32.mul(dup, 4096)),
                                 U32.mul(hw, 16777216)))
          a6 = Array.set(U32, a5, n3cell(c, gg), n3)
          Array.set(U32, a6, sqcell(c, gg), sq)

def cnt(+g: U32, +sb: U32, +n: U32, +skip: U32, +gen: U32, +dep: U32,
        +c: U32, +gg: U32, a: Array<U32>) -> Array<U32>:
  +fuel = Nat.add(Nat.mul(U32.to_nat(n), 8n), 64n)
  cnt_go(fuel, 0, g, 0, n, sb, skip, gen, dep, c, gg, 0, 0, 0, 0, 0, 0, 0,
         Array.get(U32, a, sb))

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
# ph 0: the pair holds ne[j].   ph 1: the pair holds cnt[r].
# ph 2: the pair holds cap[pmk][k].   ph 3: stop.
def stats_go(+fuel: Nat, +ph: U32, +j: U32, +t: U32, +dep: U32, +c: U32,
             +gg: U32, +pmk: U32, +lb: U32, +exp: U32, +gen: U32, +r: U32,
             +skipwin: U32, +rw: U32, p: Array<U32> & U32) -> Array<U32>:
  match fuel:
    case 0n:
      (a2, _) = p
      write_stats(a2, lb, exp, c, gg)
    case 1n+p2:
      match ph:
        case 0:
          (a2, +v) = p
          +cb = cnt_at(dep, c, gg)
          stats_go(p2, 1, j, t, dep, c, gg, pmk, lb, exp, gen, v, skipwin, v,
                   Array.get(U32, a2, U32.add(cb, v)))
        case 1:
          (a2, +cell) = p
          +k = U32.sub(cell, gen)
          +cp = cap_at(pmk, k, c, gg)
          stats_go(p2, 2, j, t, dep, c, gg, pmk, lb, exp, gen, k, skipwin, rw,
                   Array.get(U32, a2, cp))
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
          +lb0: U32, +exp0: U32, +gen: U32, +skipwin: U32,
          a: Array<U32>) -> Array<U32>:
  +fuel = Nat.add(Nat.mul(U32.to_nat(t), 8n), 64n)
  +nb = ne_at(dep, c, gg)
  stats_go(fuel, 0, j0, t, dep, c, gg, pmk, lb0, exp0, gen, 0, skipwin, 0,
           Array.get(U32, a, U32.add(nb, j0)))

# ------------------------------------------------------------------ offsets ---

# For each distinct response in ne order, off[r] = start of its bucket in the
# destination set and cur[r] = the same, as a running cursor.
# ph 0: the pair holds ne[j].   ph 1: the pair holds cnt[r].   ph 2: stop.
def offs_go(+fuel: Nat, +ph: U32, +j: U32, +t: U32, +dep: U32, +dst: U32,
            +cur: U32, +c: U32, +gg: U32, +gen: U32, +r: U32,
            p: Array<U32> & U32) -> Array<U32>:
  match fuel:
    case 0n:
      (a2, _) = p
      a2
    case 1n+p2:
      match ph:
        case 0:
          (a2, +v) = p
          +cb = cnt_at(dep, c, gg)
          offs_go(p2, 1, j, t, dep, dst, cur, c, gg, gen, v,
                  Array.get(U32, a2, U32.add(cb, v)))
        case 1:
          (a2, +cell) = p
          +k = U32.sub(cell, gen)
          +ob = off_at(dep, c, gg)
          +ub = cur_at(dep, c, gg)
          +zb = ent_at(dep, c, gg)
          a3 = Array.set(U32, a2, U32.add(ob, j), cur)
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

def offsets(+t: U32, +dep: U32, +dst: U32, +c: U32, +gg: U32, +gen: U32,
            a: Array<U32>) -> Array<U32>:
  +fuel = Nat.add(Nat.mul(U32.to_nat(t), 8n), 64n)
  +nb = ne_at(dep, c, gg)
  offs_go(fuel, 0, 0, t, dep, dst, dst, c, gg, gen, 0,
          Array.get(U32, a, nb))

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
          sc_go(p2, 1, i, n, sb, g, dep, dst, c, gg, v, r,
                Array.get(U32, a2, U32.add(U32.mul(g, c), v)))
        case 1:
          (a2, +fb) = p
          +ub = cur_at(dep, c, gg)
          sc_go(p2, 2, i, n, sb, g, dep, dst, c, gg, x, fb,
                Array.get(U32, a2, U32.add(ub, fb)))
        case 2:
          (a2, +pos) = p
          +ub = cur_at(dep, c, gg)
          a3 = Array.set(U32, a2, U32.add(ub, r), U32.inc(pos))
          a4 = Array.set(U32, a3, pos, x)
          +i2 = U32.inc(i)
          +last = A.eq01(i2, n)
          +idx = A.sel(last, 0, U32.add(sb, i2))
          sc_go(p2, A.sel(last, 3, 0), i2, n, sb, g, dep, dst, c, gg, 0, 0,
                Array.get(U32, a4, idx))
        case _:
          (a2, _) = p
          a2

def scatter(+g: U32, +sb: U32, +n: U32, +dep: U32, +dst: U32, +c: U32,
            +gg: U32, a: Array<U32>) -> Array<U32>:
  +fuel = Nat.add(Nat.mul(U32.to_nat(n), 8n), 64n)
  sc_go(fuel, 0, 0, n, sb, g, dep, dst, c, gg, 0, 0,
        Array.get(U32, a, sb))

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
