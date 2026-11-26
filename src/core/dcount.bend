# Distinct-response count on the prototype's flat-array layout.
#
# The state is one `Array<U32>`:
#   0 .. 256               256 `U32` count cells (one per response code)
#   256 .. 512             256 `U32` touched-list cells
#   512                    result cell
#   1024 ..                packed feedback table (4 codes per word)
#   o .. o+k               candidate-index range, read as a slice
# The first 1024 cells are the scratch region modelled by `proofs/core_scratch`.
# `fb = 1024 + g*c` is the row base in the packed table.
#
# This is `proto2/m1/src/prof.bend` `dn_go`/`dcount` with the packed read
# inserted in phase 1. Phases 0..3 are the candidate pass (one state-machine
# step per phase, exactly the prototype's shape); 4..5 clear the touched count
# cells; 6 writes the distinct count. The decision values are 0/1 `U32` and the
# next phase/index is selected arithmetically, as in the prototype.
import Base

# ph 0: p is the previous read pair; read set[o+i] -> 1
# ph 1: p is (array, candidate index); read peek(row+ci) -> 2
# ph 2: p is (array, code); read count[code] -> 3
# ph 3: p is (array, count); write count+1 and touched[t], advance -> 0 or 4
# ph 4: choose the next touched entry or the result cell -> 5 or 6
# ph 5: p is (array, touched code); clear its count, advance -> 4 or 6
# ph 6: write the result and stop
def dc_go(+fuel: Nat, +ph: U32, +i: U32, +j: U32, +fb: U32, +o: U32,
          +k: U32, +t: U32, +code: U32,
          p: Array<U32> & U32) -> Array<U32>:
  match fuel:
    case 0n:
      (a2, _) = p
      a2
    case 1n+f:
      match ph:
        case 0:
          (a2, _) = p
          dc_go(f, 1, i, j, fb, o, k, t, code,
            Array.get(U32, a2, U32.add(o, i)))
        case 1:
          (a2, +ci) = p
          +fi = U32.add(fb, ci)
          dc_go(f, 2, i, U32.and(fi, 3), fb, o, k, t, code,
            Array.get(U32, a2, U32.add(1024, U32.shrn(fi, 2n))))
        case 2:
          (a2, +w) = p
          +b = j
          +hi = U32.sub(1, U32.shrn(U32.sub(b, 2), 31n))
          +u1 = U32.add(w, U32.mul(hi, U32.sub(U32.shrn(w, 16n), w)))
          +u2 = U32.add(u1, U32.mul(U32.and(b, 1),
                                    U32.sub(U32.shrn(u1, 8n), u1)))
          +c = U32.and(u2, 255)
          dc_go(f, 3, i, j, fb, o, k, t, c,
            Array.get(U32, a2, c))
        case 3:
          (a2, +v) = p
          +new = U32.shrn(U32.sub(v, 1), 31n)
          a3 = Array.set(U32, a2, code, U32.add(v, 1))
          a4 = Array.set(U32, a3, U32.add(256, t), code)
          +i2 = U32.inc(i)
          +t2 = U32.add(t, new)
          +done = U32.sub(1, U32.shrn(U32.sub(i2, k), 31n))
          +sb = U32.add(o, i2)
          +cb : U32 = 0
          +idx = U32.add(sb, U32.mul(done, U32.sub(cb, sb)))
          dc_go(f, U32.mul(done, 4), i2, 0, fb, o, k, t2, 0,
            Array.get(U32, a4, idx))
        case 4:
          (a2, _) = p
          +done = U32.sub(1, U32.shrn(U32.sub(j, t), 31n))
          +tb = U32.add(256, j)
          +cb : U32 = 0
          +idx = U32.add(tb, U32.mul(done, U32.sub(cb, tb)))
          dc_go(f, U32.add(5, done), i, j, fb, o, k, t, code,
            Array.get(U32, a2, idx))
        case 5:
          (a2, +tc) = p
          a3 = Array.set(U32, a2, tc, 0)
          +j2 = U32.inc(j)
          +done = U32.sub(1, U32.shrn(U32.sub(j2, t), 31n))
          +tb = U32.add(256, j2)
          +cb : U32 = 0
          +idx = U32.add(tb, U32.mul(done, U32.sub(cb, tb)))
          dc_go(f, U32.add(4, U32.mul(done, 2)), i, j2, fb, o, k, t, code,
            Array.get(U32, a3, idx))
        case 6:
          (a2, _) = p
          Array.set(U32, a2, 512, t)
        case _:
          (a2, _) = p
          a2

# `fb` is `g*c`; `o` is the set base and `k` its length.
def dcount(a: Array<U32>, +fb: U32, +o: U32, +k: U32,
           +pb: U32) -> Array<U32>:
  +fuel = Nat.add(Nat.mul(U32.to_nat(k), 8n), 80n)
  dc_go(fuel, 0, 0, 0, fb, o, k, 0, 0, (a, 0))

def result_go(r: Array<U32> & U32) -> U32:
  (_, +v) = r
  v

def result(a: Array<U32>, +pb: U32) -> U32:
  result_go(Array.get(U32, a, 512))
