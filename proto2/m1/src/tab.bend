# Building every table the search reads, in the single flat state array.
#
# The heavy loop is the feedback table: `fb[g*C + c]` is the Wordle response of
# guess `g` against candidate `c`, with the green digit 1, yellow 2, position 0
# least significant, so the all-green response is 121. The response is computed
# with pure 32-bit arithmetic from the two packed 5x5-bit words: no arrays, no
# branches, one read and one write per pair.
import Base
import ./geo.bend as G
import ./arith.bend as A

# ------------------------------------------------------------- arithmetic ---

# Field `sh` of a packed word (letters 0..25 in 5-bit fields).
def fld(+x: U32, +sh: Nat) -> U32:
  U32.and(U32.shrn(x, sh), 31)

# 1 when a > b, else 0.
def gt01(+a: U32, +b: U32) -> U32:
  A.lt01(b, a)

# The Wordle response of guess `gp` against secret `sp`, both packed. q01..q34
# are the per-row same-letter bits: qij is 1 when guess positions i and j carry
# the same letter (j > i), computed once per guess row.
#
# Position i is green iff the letters match. Otherwise it is yellow iff the
# secret holds more unconsumed copies of the letter than earlier non-green guess
# positions carrying it. `c` counts the letter anywhere in the secret, `gc` the
# green positions with it (a green consumes its copy), `b` the earlier non-green
# guess positions with it.
def resp(+q01: U32, +q02: U32, +q03: U32, +q04: U32, +q12: U32, +q13: U32,
         +q14: U32, +q23: U32, +q24: U32, +q34: U32, +gp: U32, +sp: U32) -> U32:
  +g0 = fld(gp, 20n)
  +g1 = fld(gp, 15n)
  +g2 = fld(gp, 10n)
  +g3 = fld(gp, 5n)
  +g4 = fld(gp, 0n)
  +e0 = A.eq01(g0, fld(sp, 20n))
  +e1 = A.eq01(g1, fld(sp, 15n))
  +e2 = A.eq01(g2, fld(sp, 10n))
  +e3 = A.eq01(g3, fld(sp, 5n))
  +e4 = A.eq01(g4, fld(sp, 0n))
  +n0 = U32.sub(1, e0)
  +n1 = U32.sub(1, e1)
  +n2 = U32.sub(1, e2)
  +n3 = U32.sub(1, e3)
  +n4 = U32.sub(1, e4)
  +c0 = U32.add(e0, U32.add(A.eq01(fld(sp, 15n), g0),
                           U32.add(A.eq01(fld(sp, 10n), g0),
                                   U32.add(A.eq01(fld(sp, 5n), g0),
                                           A.eq01(fld(sp, 0n), g0)))))
  +c1 = U32.add(e1, U32.add(A.eq01(fld(sp, 20n), g1),
                           U32.add(A.eq01(fld(sp, 10n), g1),
                                   U32.add(A.eq01(fld(sp, 5n), g1),
                                           A.eq01(fld(sp, 0n), g1)))))
  +c2 = U32.add(e2, U32.add(A.eq01(fld(sp, 20n), g2),
                           U32.add(A.eq01(fld(sp, 15n), g2),
                                   U32.add(A.eq01(fld(sp, 5n), g2),
                                           A.eq01(fld(sp, 0n), g2)))))
  +c3 = U32.add(e3, U32.add(A.eq01(fld(sp, 20n), g3),
                           U32.add(A.eq01(fld(sp, 15n), g3),
                                   U32.add(A.eq01(fld(sp, 10n), g3),
                                           A.eq01(fld(sp, 0n), g3)))))
  +c4 = U32.add(e4, U32.add(A.eq01(fld(sp, 20n), g4),
                           U32.add(A.eq01(fld(sp, 15n), g4),
                                   U32.add(A.eq01(fld(sp, 10n), g4),
                                           A.eq01(fld(sp, 5n), g4)))))
  +gc0 = U32.add(e0, U32.add(U32.mul(e1, q01),
                            U32.add(U32.mul(e2, q02),
                                    U32.add(U32.mul(e3, q03),
                                            U32.mul(e4, q04)))))
  +gc1 = U32.add(e1, U32.add(U32.mul(e0, q01),
                            U32.add(U32.mul(e2, q12),
                                    U32.add(U32.mul(e3, q13),
                                            U32.mul(e4, q14)))))
  +gc2 = U32.add(e2, U32.add(U32.mul(e0, q02),
                            U32.add(U32.mul(e1, q12),
                                    U32.add(U32.mul(e3, q23),
                                            U32.mul(e4, q24)))))
  +gc3 = U32.add(e3, U32.add(U32.mul(e0, q03),
                            U32.add(U32.mul(e1, q13),
                                    U32.add(U32.mul(e2, q23),
                                            U32.mul(e4, q34)))))
  +gc4 = U32.add(e4, U32.add(U32.mul(e0, q04),
                            U32.add(U32.mul(e1, q14),
                                    U32.add(U32.mul(e2, q24),
                                            U32.mul(e3, q34)))))
  +b1 = U32.mul(n0, q01)
  +b2 = U32.add(U32.mul(n0, q02), U32.mul(n1, q12))
  +b3 = U32.add(U32.add(U32.mul(n0, q03), U32.mul(n1, q13)),
                U32.mul(n2, q23))
  +b4 = U32.add(U32.add(U32.mul(n0, q04), U32.mul(n1, q14)),
                U32.add(U32.mul(n2, q24), U32.mul(n3, q34)))
  +y0 = U32.mul(n0, gt01(U32.sub(c0, gc0), 0))
  +y1 = U32.mul(n1, gt01(U32.sub(c1, gc1), b1))
  +y2 = U32.mul(n2, gt01(U32.sub(c2, gc2), b2))
  +y3 = U32.mul(n3, gt01(U32.sub(c3, gc3), b3))
  +y4 = U32.mul(n4, gt01(U32.sub(c4, gc4), b4))
  +d0 = U32.add(e0, U32.mul(2, y0))
  +d1 = U32.add(e1, U32.mul(2, y1))
  +d2 = U32.add(e2, U32.mul(2, y2))
  +d3 = U32.add(e3, U32.mul(2, y3))
  +d4 = U32.add(e4, U32.mul(2, y4))
  U32.add(U32.add(d0, U32.mul(3, d1)),
          U32.add(U32.mul(9, d2), U32.add(U32.mul(27, d3), U32.mul(81, d4))))

# --------------------------------------------------------------- word fill ---
#
# The text is walked once, character by character, as a tail recursion (no list
# of lines: a deep non-tail recursion over a 90 KB string overflows). A sliding
# window keeps the last five letters; the word's cells are written at index `n`
# on every character and `n` advances only when a newline follows five letters.
# The last line needs no trailing newline.

def lbit(+l: U32) -> U32:
  U32.shln(1, U32.to_nat(l))

def pack5(+l0: U32, +l1: U32, +l2: U32, +l3: U32, +l4: U32) -> U32:
  U32.add(U32.add(U32.shln(l0, 20n), U32.shln(l1, 15n)),
          U32.add(U32.shln(l2, 10n), U32.add(U32.shln(l3, 5n), l4)))

# Letters used by the word, and the letters it repeats.
def lmask5(+a0: U32, +a1: U32, +a2: U32, +a3: U32, +a4: U32) -> U32:
  +b0 = lbit(a0)
  +b1 = lbit(a1)
  +b2 = lbit(a2)
  +b3 = lbit(a3)
  +b4 = lbit(a4)
  U32.or(U32.or(b0, b1), U32.or(U32.or(b2, b3), b4))

def ldup5(+a0: U32, +a1: U32, +a2: U32, +a3: U32, +a4: U32) -> U32:
  +b0 = lbit(a0)
  +b1 = lbit(a1)
  +b2 = lbit(a2)
  +b3 = lbit(a3)
  +b4 = lbit(a4)
  U32.or(U32.or(U32.or(U32.and(b0, b1), U32.and(b0, b2)),
                U32.or(U32.and(b0, b3), U32.and(b0, b4))),
         U32.or(U32.or(U32.or(U32.and(b1, b2), U32.and(b1, b3)),
                       U32.or(U32.and(b1, b4), U32.and(b2, b3))),
                U32.or(U32.and(b2, b4), U32.and(b3, b4))))

# Per-position letter class of a guess, Rust's guess_profile_chars encoding:
# 0 = letter occurs once (plane 0), 1 = first occurrence of a repeated letter
# (plane 1), 2 = later occurrence of a repeated letter (plane 2). Two bits per
# position, position 0 in the low bits.
def gcls5(+a0: U32, +a1: U32, +a2: U32, +a3: U32, +a4: U32) -> U32:
  +e01 = A.eq01(a0, a1)
  +e02 = A.eq01(a0, a2)
  +e03 = A.eq01(a0, a3)
  +e04 = A.eq01(a0, a4)
  +e12 = A.eq01(a1, a2)
  +e13 = A.eq01(a1, a3)
  +e14 = A.eq01(a1, a4)
  +e23 = A.eq01(a2, a3)
  +e24 = A.eq01(a2, a4)
  +e34 = A.eq01(a3, a4)
  +c0 = A.nz(U32.or(U32.or(e01, e02), U32.or(e03, e04)))
  +l1 = A.nz(U32.or(U32.or(e12, e13), e14))
  +c1 = U32.add(U32.mul(2, e01), U32.mul(U32.sub(1, e01), l1))
  +b2 = A.nz(U32.or(e02, e12))
  +l2 = A.nz(U32.or(e23, e24))
  +c2 = U32.add(U32.mul(2, b2), U32.mul(U32.sub(1, b2), l2))
  +b3 = A.nz(U32.or(U32.or(e03, e13), e23))
  +c3 = U32.add(U32.mul(2, b3), U32.mul(U32.sub(1, b3), e34))
  +c4 = U32.mul(2, A.nz(U32.or(U32.or(e04, e14), U32.or(e24, e34))))
  U32.add(U32.add(c0, U32.shln(c1, 2n)),
          U32.add(U32.shln(c2, 4n),
                   U32.add(U32.shln(c3, 6n), U32.shln(c4, 8n))))

# Walk the text of the guesses file.
def fill_g_go(s: String, +n: U32, +k: U32, +q0: U32, +q1: U32, +q2: U32,
              +q3: U32, +q4: U32, +c: U32, +gg: U32,
              a: Array<U32>) -> Array<U32>:
  match s:
    case SNil{}:
      a
    case SCon{Chr{+x}, t}:
      +isnl = U32.max(A.eq01(x, 10), A.eq01(x, 13))
      +d0 = A.sel(isnl, q0, q1)
      +d1 = A.sel(isnl, q1, q2)
      +d2 = A.sel(isnl, q2, q3)
      +d3 = A.sel(isnl, q3, q4)
      +d4 = A.sel(isnl, q4, U32.and(U32.sub(x, 65), 31))
      +p = pack5(d0, d1, d2, d3, d4)
      +m = lmask5(d0, d1, d2, d3, d4)
      +o1 = G.off_gpack(c, gg)
      +o2 = G.off_gmask(c, gg)
      +o3 = U32.add(G.off_gcls(c, gg), n)
      +cl = gcls5(d0, d1, d2, d3, d4)
      a[U32.add(o1, n)] <- p
      a[U32.add(o2, n)] <- m
      a[o3] <- cl
      fill_g_go(t, U32.add(n, U32.mul(isnl, A.eq01(k, 5))),
                A.sel(isnl, 0, U32.add(k, 1)), d0, d1, d2, d3, d4, c, gg, a)

def fill_g(s: String, +c: U32, +gg: U32, a: Array<U32>) -> Array<U32>:
  fill_g_go(s, 0, 0, 0, 0, 0, 0, 0, c, gg, a)

# Walk the text of the candidates file.
def fill_c_go(s: String, +n: U32, +k: U32, +q0: U32, +q1: U32, +q2: U32,
              +q3: U32, +q4: U32, +c: U32, +gg: U32,
              a: Array<U32>) -> Array<U32>:
  match s:
    case SNil{}:
      a
    case SCon{Chr{+x}, t}:
      +isnl = U32.max(A.eq01(x, 10), A.eq01(x, 13))
      +d0 = A.sel(isnl, q0, q1)
      +d1 = A.sel(isnl, q1, q2)
      +d2 = A.sel(isnl, q2, q3)
      +d3 = A.sel(isnl, q3, q4)
      +d4 = A.sel(isnl, q4, U32.and(U32.sub(x, 65), 31))
      +p = pack5(d0, d1, d2, d3, d4)
      +b0 = lbit(d0)
      +b1 = lbit(d1)
      +b2 = lbit(d2)
      +b3 = lbit(d3)
      +b4 = lbit(d4)
      +oc = G.off_cpack(c, gg)
      +om = G.off_cmask(c, gg)
      +oa = U32.add(G.off_cat(c, gg), U32.mul(5, n))
      +od = G.off_cdup(c, gg)
      a[U32.add(oc, n)] <- p
      a[U32.add(om, n)] <- U32.or(U32.or(b0, b1), U32.or(U32.or(b2, b3), b4))
      a[oa] <- b0
      a[U32.add(oa, 1)] <- b1
      a[U32.add(oa, 2)] <- b2
      a[U32.add(oa, 3)] <- b3
      a[U32.add(oa, 4)] <- b4
      a[U32.add(od, n)] <- ldup5(d0, d1, d2, d3, d4)
      fill_c_go(t, U32.add(n, U32.mul(isnl, A.eq01(k, 5))),
                A.sel(isnl, 0, U32.add(k, 1)), d0, d1, d2, d3, d4, c, gg, a)

def fill_c(s: String, +c: U32, +gg: U32, a: Array<U32>) -> Array<U32>:
  fill_c_go(s, 0, 0, 0, 0, 0, 0, 0, c, gg, a)

# Words in a text: one per newline-terminated line of five letters, plus a
# final unterminated one.
def wc_go(s: String, +k: U32, +n: U32) -> U32:
  match s:
    case SNil{}:
      U32.add(n, A.nz(k))
    case SCon{Chr{+x}, t}:
      +isnl = U32.max(A.eq01(x, 10), A.eq01(x, 13))
      wc_go(t, A.sel(isnl, 0, U32.add(k, 1)),
            U32.add(n, U32.mul(isnl, A.eq01(k, 5))))

def word_count(s: String) -> U32:
  wc_go(s, 0, 0)

# Zobrist: two independent 32-bit words per candidate from an LCG. The search
# hashes a set as the xor of its candidates' words.
def zob_go(+fuel: Nat, +i: U32, +c: U32, +gg: U32, +s: U32,
           a: Array<U32>) -> Array<U32>:
  match fuel:
    case 0n:
      a
    case 1n+p:
      +s1 = U32.add(U32.mul(s, 1103515245), 12345)
      +s2 = U32.add(U32.mul(s1, 1103515245), 12345)
      a[U32.add(G.off_z1(c, gg), i)] <- s1
      a[U32.add(G.off_z2(c, gg), i)] <- s2
      zob_go(p, U32.inc(i), c, gg, s2, a)

def fill_zob(+c: U32, +gg: U32, a: Array<U32>) -> Array<U32>:
  zob_go(U32.to_nat(c), 0, c, gg, 12345, a)

# ------------------------------------------------------------ feedback table ---
# ------------------------------------------------------------ feedback table ---
#
# Phase 0: the value just read is the packed guess word of row `g`.
# Phase 1: the value just read is the packed secret of candidate `i` of row `g`.
# Phase 2: stop. `a` is never passed separately: the read pair carries it.
def fb_go(+fuel: Nat, +phase: U32, +g: U32, +i: U32, +gp: U32,
          +q01: U32, +q02: U32, +q03: U32, +q04: U32, +q12: U32, +q13: U32,
          +q14: U32, +q23: U32, +q24: U32, +q34: U32,
          +c: U32, +gg: U32, r: Array<U32> & U32) -> Array<U32>:
  match fuel:
    case 0n:
      (a2, _) = r
      a2
    case 1n+p:
      match phase:
        case 0:
          (a2, +v) = r
          r2 = Array.get(U32, a2, U32.add(G.off_cpack(c, gg), 0))
          fb_go(p, 1, g, 0, v,
                A.eq01(fld(v, 20n), fld(v, 15n)),
                A.eq01(fld(v, 20n), fld(v, 10n)),
                A.eq01(fld(v, 20n), fld(v, 5n)),
                A.eq01(fld(v, 20n), fld(v, 0n)),
                A.eq01(fld(v, 15n), fld(v, 10n)),
                A.eq01(fld(v, 15n), fld(v, 5n)),
                A.eq01(fld(v, 15n), fld(v, 0n)),
                A.eq01(fld(v, 10n), fld(v, 5n)),
                A.eq01(fld(v, 10n), fld(v, 0n)),
                A.eq01(fld(v, 5n), fld(v, 0n)),
                c, gg, r2)
        case 1:
          (a2, +v) = r
          +i2 = U32.inc(i)
          +rowdone = A.eq01(i2, c)
          +g2 = U32.inc(g)
          +stop = A.eq01(g2, gg)
          +at = U32.add(U32.mul(g, c), i)
          +idx = A.sel(rowdone, U32.add(G.off_gpack(c, gg), g2),
                       U32.add(G.off_cpack(c, gg), i2))
          a3 = Array.set(U32, a2, at,
                         resp(q01, q02, q03, q04, q12, q13, q14, q23, q24,
                              q34, gp, v))

          r2 = Array.get(U32, a3, idx)
          fb_go(p, A.sel(rowdone, A.sel(stop, 2, 0), 1),
                A.sel(rowdone, g2, g), i2, gp, q01, q02, q03, q04, q12,
                q13, q14, q23, q24, q34, c, gg, r2)
        case _:
          (a2, _) = r
          a2

def fill_fb(+c: U32, +gg: U32, a: Array<U32>) -> Array<U32>:
  +fuel = Nat.add(Nat.mul(U32.to_nat(gg), U32.to_nat(c)), Nat.add(U32.to_nat(gg), 64n))
  fb_go(fuel, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, c, gg,
        Array.get(U32, a, G.off_gpack(c, gg)))

# ---------------------------------------------------- packed response table ---
#
# Pack four 8-bit responses into one U32 cell, in place: word k is built from
# cells 4k..4k+3 and written to cell k, walking k UPWARDS. Ascending order is
# safe because when word k is written the cells already written are 0..k-1, all
# strictly below 4k, so no source word has been overwritten.
#
# The table itself is the first g*c cells of the array (index x = g*c + i). The
# last word may also take bytes from cells past the table (the z1 region); no
# reader asks for a response beyond the last candidate of the last guess, so
# those bytes are never observed.
#
# ph 0 reads 4k, ph 1..3 read 4k+1..4k+3 and accumulate, ph 4 writes cell k and
# steps up, ph 5 is done.
def pack_go(+fuel: Nat, +ph: U32, +k: U32, +si: U32, +lim: U32, +acc: U32,
            r: Array<U32> & U32) -> Array<U32>:
  match fuel:
    case 0n:
      (a2, _) = r
      a2
    case 1n+f:
      match ph:
        case 0:
          (a2, _) = r
          +idx = U32.mul(k, 4)
          pack_go(f, 1, k, idx, lim, 0, Array.get(U32, a2, idx))
        case 1:
          (a2, +v) = r
          +idx = U32.inc(si)
          pack_go(f, 2, k, idx, lim, v, Array.get(U32, a2, idx))
        case 2:
          (a2, +v) = r
          +idx = U32.inc(si)
          pack_go(f, 3, k, idx, lim, U32.or(acc, U32.shln(v, 8n)),
                  Array.get(U32, a2, idx))
        case 3:
          (a2, +v) = r
          +idx = U32.inc(si)
          pack_go(f, 4, k, idx, lim, U32.or(acc, U32.shln(v, 16n)),
                  Array.get(U32, a2, idx))
        case 4:
          (a2, +v) = r
          +w = U32.or(acc, U32.shln(v, 24n))
          +kn = U32.inc(k)
          a3 = a2[k] <- w
          +last = A.eq01(k, lim)
          pack_go(f, A.sel(last, 5, 0), A.sel(last, 0, kn), 0, lim, 0,
                  Array.get(U32, a3, 0))
        case _:
          (a2, _) = r
          a2

def pack_fb(+c: U32, +gg: U32, a: Array<U32>) -> Array<U32>:
  +n = U32.mul(gg, c)
  +words = U32.add(U32.shrn(n, 2n), A.nz(U32.and(n, 3)))
  +fuel = Nat.add(Nat.mul(U32.to_nat(words), 6n), 8n)
  pack_go(fuel, 0, 0, 0, U32.sub(words, 1), 0, Array.get(U32, a, 0))

# ------------------------------------------------------- candidate -> guess ---
#
# The candidate list is not sorted, so a merge pass will not do. A 2^16-slot
# open-addressing table maps a packed word to its guess index: `hh[2p]` holds
# the packed word, `hh[2p+1]` the guess index, and an empty key is 0xFFFFFFFF.

# Mark every slot empty (0xFFFFFFFF) before inserting.
def hh_init(+fuel: Nat, +i: U32, +base: U32, a: Array<U32>) -> Array<U32>:
  match fuel:
    case 0n:
      a
    case 1n+p:
      a[U32.add(base, i)] <- 4294967295
      hh_init(p, U32.inc(i), base, a)

def fill_hh_init(+c: U32, +gg: U32, a: Array<U32>) -> Array<U32>:
  hh_init(U32.to_nat(G.hh_size()), 0, G.off_hh(c, gg), a)

def hhash(+p: U32) -> U32:
  U32.and(U32.mul(p, 2654435761), 65535)

# Phase 0: v is the packed word of guess `g`. Phase 1: v is the key at slot
# `pos`. Phase 2: v is unused; insert `g` at `pos`. Phase 3: stop.
# The value cell is written only in phase 2, never while probing: a probe must
# not disturb the entries it walks over.
def hh_go(+fuel: Nat, +phase: U32, +g: U32, +pos: U32, +key: U32, +c: U32,
          +gg: U32, r: Array<U32> & U32) -> Array<U32>:
  match fuel:
    case 0n:
      (a2, _) = r
      a2
    case 1n+p:
      match phase:
        case 0:
          (a2, +v) = r
          r2 = Array.get(U32, a2,
                         U32.add(G.off_hh(c, gg),
                                 U32.mul(2, hhash(v))))
          hh_go(p, 1, g, hhash(v), v, c, gg, r2)
        case 1:
          (a2, +v) = r
          +empty = A.eq01(v, 4294967295)
          +pos2 = U32.and(U32.inc(pos), 65535)
          +idx = A.sel(empty, U32.add(G.off_gpack(c, gg), g),
                       U32.add(G.off_hh(c, gg), U32.mul(2, pos2)))
          r2 = Array.get(U32, a2, idx)
          hh_go(p, A.sel(empty, 2, 1), g, A.sel(empty, pos, pos2), key, c, gg,
                r2)
        case 2:
          (a2, +v) = r
          +g2 = U32.inc(g)
          +widx = U32.add(G.off_hh(c, gg), U32.mul(2, pos))
          a3 = Array.set(U32, a2, widx, key)
          a4 = Array.set(U32, a3, U32.inc(widx), g)
          +stop = A.eq01(g2, gg)
          r2 = Array.get(U32, a4, U32.add(G.off_gpack(c, gg),
                                          A.sel(stop, 0, g2)))
          hh_go(p, A.sel(stop, 3, 0), g2, 0, 0, c, gg, r2)
        case _:
          (a2, _) = r
          a2

def fill_hh(+c: U32, +gg: U32, a: Array<U32>) -> Array<U32>:
  +fuel = Nat.add(Nat.mul(U32.to_nat(gg), 32n), 64n)
  hh_go(fuel, 0, 0, 0, 0, c, gg,
        Array.get(U32, a, U32.add(G.off_gpack(c, gg), 0)))

# Phase 0: v is the packed word of candidate `ic`. Phase 1: v is the key at slot
# `pos`. Phase 2: v is the guess index stored at `pos`. Phase 4: not found.
# Phase 3: stop.
def c2g_go(+fuel: Nat, +phase: U32, +ic: U32, +pos: U32, +key: U32, +c: U32,
           +gg: U32, r: Array<U32> & U32) -> Array<U32>:
  match fuel:
    case 0n:
      (a2, _) = r
      a2
    case 1n+p:
      match phase:
        case 0:
          (a2, +v) = r
          r2 = Array.get(U32, a2,
                         U32.add(G.off_hh(c, gg), U32.mul(2, hhash(v))))
          c2g_go(p, 1, ic, hhash(v), v, c, gg, r2)
        case 1:
          (a2, +v) = r
          +found = A.eq01(v, key)
          +empty = A.eq01(v, 4294967295)
          +pos2 = U32.and(U32.inc(pos), 65535)
          +idx = A.sel(empty, 0,
                       A.sel(found,
                             U32.add(G.off_hh(c, gg),
                                     U32.inc(U32.mul(2, pos))),
                             U32.add(G.off_hh(c, gg), U32.mul(2, pos2))))
          r2 = Array.get(U32, a2, idx)
          c2g_go(p, A.sel(empty, 4, A.sel(found, 2, 1)), ic, pos2, key, c, gg,
                 r2)
        case 2:
          (a2, +v) = r
          +ic2 = U32.inc(ic)
          a3 = Array.set(U32, a2, U32.add(G.off_c2g(c, gg), ic), v)
          r2 = Array.get(U32, a3,
                         U32.add(G.off_cpack(c, gg), A.sel(A.eq01(ic2, c), 0,
                                                           ic2)))
          c2g_go(p, A.sel(A.eq01(ic2, c), 3, 0), ic2, 0, 0, c, gg, r2)
        case 4:
          (a2, _) = r
          +ic2 = U32.inc(ic)
          a3 = Array.set(U32, a2, U32.add(G.off_c2g(c, gg), ic), 0)
          r2 = Array.get(U32, a3, U32.add(G.off_cpack(c, gg), ic2))
          c2g_go(p, A.sel(A.eq01(ic2, c), 3, 0), ic2, 0, 0, c, gg, r2)
        case _:
          (a2, _) = r
          a2

def fill_c2g(+c: U32, +gg: U32, a: Array<U32>) -> Array<U32>:
  +fuel = Nat.add(Nat.mul(U32.to_nat(c), 32n), 64n)
  c2g_go(fuel, 0, 0, 0, 0, c, gg,
         Array.get(U32, a, U32.add(G.off_cpack(c, gg), 0)))

