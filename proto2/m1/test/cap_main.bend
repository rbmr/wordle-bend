import Base
import ../src/geo.bend as G
import ../src/heur.bend as H

# Build the cap2d table for c candidates and maxk rows, then print every cell as
# "k n value" so it can be compared with ref.capacity_bound.
def dump(+fuel: Nat, +j: U32, +c: U32, +gg: U32,
         r: Array<U32> & U32) -> IO(Unit):
  match fuel:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+p:
      (a2, v) = r
      +w = U32.inc(c)
      +k = U32.add(2, U32.div(j, w))
      +n = U32.mod(j, w)
      +base = U32.add(U32.add(G.off_cap(c, gg), U32.mul(k, w)), n)
      nxt = Array.get(U32, a2, U32.add(base, 1))
      do IO<Unit>:
        Unit <- IO.print(U32.show(k) ++ " " ++ U32.show(n) ++ " " ++ U32.show(v))
        dump(p, U32.inc(j), c, gg, nxt)

def depth_for(+size: U32) -> Nat:
  Nat.add(U32.log2(U32.sub(size, 1)), 1n)

def build(+c: U32, +gg: U32, +maxk: U32) -> IO(Unit):
  do IO<Unit>:
    total : U32 = G.total_size(c, gg)
    a : Array<U32> = Array.new(U32, depth_for(total), 0)
    a1 : Array<U32> = H.cap_fill(maxk, c, gg, a)
    f1 : Nat = Nat.mul(Nat.sub(U32.to_nat(maxk), 1n), U32.to_nat(U32.inc(c)))
    dump(f1, 0, c, gg, Array.get(U32, a1, G.off_cap(c, gg)))

def main() -> IO(Unit):
  build(20, 1, 12)
