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

# Per-guess letter classes (2 bits per position, 10 bits used): Rust's
# guess_profile_chars class, which selects one of the three m_tab planes.
def off_gcls(+c: U32, +g: U32) -> U32:
  U32.add(off_cpack(c, g), c)

def hh_size() -> U32:
  131072

def off_hh(+c: U32, +g: U32) -> U32:
  U32.add(off_gcls(c, g), g)

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
# 5 x 1024: the per-(c,gg) profile tables in the first block, then one scratch
# block (counts/touched/result) per parallel scan lane.
def prof_size() -> U32:
  5120

def off_prof(+c: U32, +g: U32) -> U32:
  U32.add(off_qgen(c, g), 768)

# Greedy-bound arena (greedy.bend): 256 depths of (set c, counts 256,
# offsets 257, scatter cursors 256, touched list 256).
def greedy_depth_slot(+c: U32) -> U32:
  U32.add(c, 1280)

# Rust's m_tab is [[1u8; 96]; 8]: five positions x three class planes x 32
# letters; the guess's profile class at position i selects the plane.
def mtab_size() -> U32:
  480

def off_mtab(+c: U32, +g: U32) -> U32:
  U32.add(off_prof(c, g), prof_size())

def off_greedy(+c: U32, +g: U32) -> U32:
  U32.add(off_mtab(c, g), mtab_size())

def greedy_size(+c: U32) -> U32:
  U32.mul(256, greedy_depth_slot(c))

def total_size(+c: U32, +g: U32) -> U32:
  U32.add(off_greedy(c, g), greedy_size(c))

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
