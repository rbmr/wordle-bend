# Table building for the flat-array search prototype.
#
# One flat `Array<U32>` holds every table and every scratch region; the region
# offsets are pure functions of the candidate count `c` and the guess count `g`
# (see G.bend). Every offset is the previous region's offset plus its size.
import Base

# CAPROWS is a fixed upper bound on the root branching factor; a larger root
# branching factor than this is reported and the run stops.
def caprows() -> U32:
  256

def depths() -> U32:
  128

def entn() -> U32:
  1024

def ttb() -> U32:
  1048576

# ---------------------------------------------------------------- layout ----
def off_z1(+c: U32, +g: U32) -> U32:
  U32.mul(g, c)

def off_z2(+c: U32, +g: U32) -> U32:
  U32.add(off_z1(c, g), c)

def off_cmask(+c: U32, +g: U32) -> U32:
  U32.add(off_z2(c, g), c)

def off_cat(+c: U32, +g: U32) -> U32:
  U32.add(off_cmask(c, g), c)

def off_cdup(+c: U32, +g: U32) -> U32:
  U32.add(off_cat(c, g), U32.mul(5, c))

def off_c2g(+c: U32, +g: U32) -> U32:
  U32.add(off_cdup(c, g), c)

def off_gmask(+c: U32, +g: U32) -> U32:
  U32.add(off_c2g(c, g), c)

def off_gpack(+c: U32, +g: U32) -> U32:
  U32.add(off_gmask(c, g), g)

def off_cpack(+c: U32, +g: U32) -> U32:
  U32.add(off_gpack(c, g), g)

def hh_size() -> U32:
  131072

def off_hh(+c: U32, +g: U32) -> U32:
  U32.add(off_cpack(c, g), c)

def cap_size(+c: U32) -> U32:
  U32.mul(caprows(), U32.inc(c))

def off_cap(+c: U32, +g: U32) -> U32:
  U32.add(off_hh(c, g), hh_size())

def off_tt(+c: U32, +g: U32) -> U32:
  U32.add(off_cap(c, g), cap_size(c))

def tt_size() -> U32:
  U32.mul(6, ttb())

def off_sets(+c: U32, +g: U32) -> U32:
  U32.add(off_tt(c, g), tt_size())

def off_cnt(+c: U32, +g: U32) -> U32:
  U32.add(off_sets(c, g), U32.mul(depths(), c))

def off_off(+c: U32, +g: U32) -> U32:
  U32.add(off_cnt(c, g), U32.mul(depths(), 256))

def off_h1(+c: U32, +g: U32) -> U32:
  U32.add(off_off(c, g), U32.mul(depths(), 256))

def off_h2(+c: U32, +g: U32) -> U32:
  U32.add(off_h1(c, g), U32.mul(depths(), 256))

def off_ent(+c: U32, +g: U32) -> U32:
  U32.add(off_h2(c, g), U32.mul(depths(), 256))

def off_plb(+c: U32, +g: U32) -> U32:
  U32.add(off_ent(c, g), U32.mul(depths(), entn()))

def off_cmk(+c: U32, +g: U32) -> U32:
  U32.add(off_plb(c, g), U32.mul(depths(), entn()))

def off_flg(+c: U32, +g: U32) -> U32:
  U32.add(off_cmk(c, g), U32.mul(depths(), entn()))

def off_p1t(+c: U32, +g: U32) -> U32:
  U32.add(off_flg(c, g), U32.mul(depths(), entn()))

def off_p2t(+c: U32, +g: U32) -> U32:
  U32.add(off_p1t(c, g), U32.mul(depths(), U32.mul(c, 3)))

# Phase 2 can append one tuple per guess, so its buffer is depths*g*3.
def off_sset(+c: U32, +g: U32) -> U32:
  U32.add(off_p2t(c, g), U32.mul(depths(), U32.mul(g, 3)))

def off_gset(+c: U32, +g: U32) -> U32:
  U32.add(off_sset(c, g), U32.mul(depths(), g))

def gset_size(+c: U32) -> U32:
  U32.mul(8, c)

def off_gstk(+c: U32, +g: U32) -> U32:
  U32.add(off_gset(c, g), gset_size(c))

def gstk_size() -> U32:
  U32.mul(4, 4096)

def off_gcnt(+c: U32, +g: U32) -> U32:
  U32.add(off_gstk(c, g), gstk_size())

# MISC: 0..255 quick/k_cand count cells, 256..511 greedy count cells.
def off_qcnt(+c: U32, +g: U32) -> U32:
  off_gcnt(c, g)

def off_qgen(+c: U32, +g: U32) -> U32:
  U32.add(off_qcnt(c, g), 256)

# Letter-profile scratch for the branching-factor scan (see prof.bend): 30
# per-position masks, the active letter mask, the 5x32 factor table, and the
# distinct-count walk's count and touched cells.
def prof_size() -> U32:
  1024

def off_prof(+c: U32, +g: U32) -> U32:
  U32.add(off_qgen(c, g), 768)

# Greedy-bound arena (greedy.bend): 256 depths of (set c, counts 256,
# offsets 257, scatter cursors 256, touched list 256).
def greedy_depth_slot(+c: U32) -> U32:
  U32.add(c, 1280)

def off_greedy(+c: U32, +g: U32) -> U32:
  U32.add(off_prof(c, g), prof_size())

def greedy_size(+c: U32) -> U32:
  U32.mul(256, greedy_depth_slot(c))

# ---- proto3 additions: the new core's flat structures ----
# Bucket stacks: one contiguous c-cell block per depth. A guess at depth d
# scatters its whole set into block d; the buckets keep the ranges recorded in
# off_at(d) / ent_at(d).
# Result cells for the driver: cost, states, guesses, pruned.
def off_meta(+c: U32, +g: U32) -> U32:
  U32.add(off_greedy(c, g), greedy_size(c))

def meta_size() -> U32:
  16

def off_bkt(+c: U32, +g: U32) -> U32:
  U32.add(off_meta(c, g), meta_size())

def bkt_size(+c: U32) -> U32:
  U32.mul(depths(), c)

# Frames: 24 U32 cells per depth. The search keeps its per-frame registers
# here, so a descent writes 22 cells and a return reads them back; no list and
# no heap cell per call.
def fr_slot() -> U32:
  24

def off_fr(+c: U32, +g: U32) -> U32:
  U32.add(off_bkt(c, g), bkt_size(c))

def fr_size() -> U32:
  U32.mul(depths(), fr_slot())

# Bucket order lists: one 256-cell index list per depth, sorted by (size desc,
# response asc) as Rust's ge3 ordering.
def off_ord(+c: U32, +g: U32) -> U32:
  U32.add(off_fr(c, g), fr_size())

def ord_size() -> U32:
  U32.mul(depths(), 256)

def total_size(+c: U32, +g: U32) -> U32:
  U32.add(off_ord(c, g), ord_size())

# ------------------------------------------------------------- small ops ----

def sat_sub(+a: U32, +b: U32) -> U32:
  U32.sub(a, U32.min(a, b))

# 1 when b, else 0.
def b2u(b: Bool) -> U32:
  match b:
    case True{}:
      1
    case False{}:
      0

def pick(+cond: Bool, +a: U32, +b: U32) -> U32:
  match cond:
    case True{}:
      a
    case False{}:
      b
