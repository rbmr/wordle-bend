# Distinct-response count on the prototype's flat-array layout.
#
# The state is one `Array<U32>`:
#   0 .. 256               256 `U32` count cells, each 0 or 1
#   256 .. 512             256 `U32` touched cells, holding candidate codes
#   512                    result cell (the distinct count)
#   1024 ..                packed feedback table (4 codes per word)
#   o .. o+k               candidate-index range, read as a slice
#
# This is `proto2/m1/src/prof.bend` `dn_go`/`dcount`: the same flat layout, the
# same five reads and writes per candidate, the same phases.  Two details are
# different, both so that the count can be certified without bit-level order
# predicates:
#
# * the candidate pass and the clear pass are bounded by a `Nat` measure
#   (`rem`, `crem`) instead of `(i - k) >> 31` order tests, so no comparison is
#   computed at run time; and
# * a count cell is written as the constant `1` and the first-occurrence flag
#   is `U32.sub(1, v)` on a cell that is only ever 0 or 1, instead of the
#   prototype's `v + 1` and `(v - 1) >> 31`.
#
# Both keep the runtime data: one `Array<U32>`, `U32` counters and cells, no
# lists, `Nat` buffers or records inside a phase.  `rem`/`crem` are `Nat` loop
# measures, not buffers.
#
# ph 0: p is (array, candidate index from the set) -> read the table word
# ph 1: p is (array, packed word) -> extract the response code, read its cell
# ph 2: p is (array, count cell value 0/1) -> write the cell and the touched
#       slot, advance the candidate or switch to the clear pass
# ph 3: p is (array, count cell value 0/1) -> the same writes, then either the
#       next candidate's set cell or the clear pass
# ph 4: p is (array, 0) -> either read the touched slot at `cj` or write the
#       result cell
# ph 5: p is (array, touched code) -> clear its count cell, advance
# ph 6: p is (array, 0) -> write the result cell
import Base

# `o` is the set base, `fb` is the absolute flat slot base of the guess row
# (`fb >> 2` is its first packed word and `fb & 3 = 0`), `t` is the running
# distinct count, `i` the candidate cursor, `cj` the clear cursor, `rem` the
# candidates after the current one, `crem` the touched slots left to clear.
def dc_go(+fuel: Nat, +ph: U32, +i: U32, +rem: Nat, +crem: Nat, +cj: U32,
          +fb: U32, +o: U32, +t: U32, +code: U32,
          p: Array<U32> & U32) -> Array<U32>:
  match fuel:
    case 0n:
      (a2, _) = p
      a2
    case 1n+f:
      match ph:
        case 0:
          (a2, _) = p
          dc_go(f, 1, i, rem, crem, cj, fb, o, t, code,
            Array.get(U32, a2, U32.add(o, i)))
        case 1:
          (a2, +ci) = p
          +fi = U32.add(fb, ci)
          dc_go(f, 2, i, rem, crem, cj, fb, o, t, U32.and(fi, 3),
            Array.get(U32, a2, U32.shrn(fi, 2n)))
        case 2:
          # Byte extract with constant shifts only (Bend has no variable shift
          # by a `U32`): shift 16 when the byte index is >= 2, then shift 8
          # when it is odd, then mask.
          (a2, +w) = p
          +b = code
          +hi = U32.sub(1, U32.shrn(U32.sub(b, 2), 31n))
          +u1 = U32.add(w, U32.mul(hi, U32.sub(U32.shrn(w, 16n), w)))
          +u2 = U32.add(u1, U32.mul(U32.and(b, 1),
                                    U32.sub(U32.shrn(u1, 8n), u1)))
          +c = U32.and(u2, 255)
          dc_go(f, 3, i, rem, crem, cj, fb, o, t, c,
            Array.get(U32, a2, c))
        case 3:
          match rem:
            case 0n:
              (a2, +v) = p
              +new = U32.sub(1, v)
              a3 = Array.set(U32, a2, code, 1)
              a4 = Array.set(U32, a3, U32.add(256, t), code)
              +t2 = U32.add(t, new)
              dc_go(f, 4, i, 0n, U32.to_nat(t2), 0, fb, o, t2, 0, (a4, 0))
            case 1n+rm:
              (a2, +v) = p
              +new = U32.sub(1, v)
              a3 = Array.set(U32, a2, code, 1)
              a4 = Array.set(U32, a3, U32.add(256, t), code)
              +t2 = U32.add(t, new)
              +i2 = U32.inc(i)
              dc_go(f, 0, i2, rm, crem, cj, fb, o, t2, 0,
                Array.get(U32, a4, U32.add(o, i2)))
        case 4:
          match crem:
            case 0n:
              dc_go(f, 6, i, rem, 0n, cj, fb, o, t, code, p)
            case 1n+cr:
              (a2, _) = p
              dc_go(f, 5, i, rem, cr, cj, fb, o, t, code,
                Array.get(U32, a2, U32.add(256, cj)))
        case 5:
          (a2, +tc) = p
          dc_go(f, 4, i, rem, crem, U32.inc(cj), fb, o, t, code,
            (Array.set(U32, a2, tc, 0), 0))
        case 6:
          (a2, _) = p
          Array.set(U32, a2, 512, t)
        case _:
          (a2, _) = p
          a2

# `fb` is `g*c`; `o` is the set base and `k` its length.  The fuel is the
# prototype's `8k + 80` (the machine uses four steps per candidate and at most
# two per touched code).  `k >= 1`: the caller reads the first candidate cell
# and the `rem` measure counts the candidates after it.
def dcount(a: Array<U32>, +fb: U32, +o: U32, +k: U32,
           +pb: U32) -> Array<U32>:
  +fuel = Nat.add(Nat.mul(U32.to_nat(k), 8n), 80n)
  dc_go(fuel, 0, 0, Nat.sub(U32.to_nat(k), 1n), 0n, 0, fb, o, 0, 0, (a, 0))

def result_go(r: Array<U32> & U32) -> U32:
  (_, +v) = r
  v

def result(a: Array<U32>, +pb: U32) -> U32:
  result_go(Array.get(U32, a, 512))
