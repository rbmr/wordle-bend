import Base
import ../src/bounds.bend as B

# Print min_k_for_target_bound(n, max_k, target) for a grid, as "n mk t v",
# and compare with ref.min_k_for_target_bound.

def prn(r: U32 & U32, +tag: String) -> IO(U32):
  (a, v) = r
  do IO<U32>:
    Unit <- IO.print(tag ++ " " ++ U32.show(v))
    IO.pure(U32, a)

# j -> (n, max_k, target): n = 16 + (j % 20), max_k in {24,30,50,82},
# target = 20 + (j * 7) % 200.
def loop(+fuel: Nat, +j: U32) -> IO(Unit):
  match fuel:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+p:
      +n = U32.add(16, U32.mod(j, 20))
      +mk0 = U32.mod(j, 4)
      +mk = U32.add(U32.mul(mk0, 19), 24)
      +tg = U32.add(20, U32.mod(U32.mul(j, 7), 200))
      +v = U32.from_nat(B.min_k_for_target_bound(U32.to_nat(n), U32.to_nat(mk),
                                                 U32.to_nat(tg)))
      do IO<Unit>:
        Unit <- IO.print(U32.show(n) ++ " " ++ U32.show(mk) ++ " "
                         ++ U32.show(tg) ++ " " ++ U32.show(v))
        loop(p, U32.inc(j))

def main() -> IO(Unit):
  loop(400n, 0)
