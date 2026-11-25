import Base
import ../src/bounds.bend as B

# Print tight_capacity_bound and phase2_capacity_bound over a grid:
# "n rk mk tight phase2", to compare with ref.heuristic.

def loop(+fuel: Nat, +j: U32) -> IO(Unit):
  match fuel:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+p:
      +n = U32.add(3, U32.mod(j, 30))
      +rk = U32.add(2, U32.mod(U32.mul(j, 3), 40))
      +mk = U32.add(2, U32.mod(U32.mul(j, 7), 80))
      +t = U32.from_nat(B.tight_capacity_bound(U32.to_nat(n), U32.to_nat(rk),
                                               U32.to_nat(mk)))
      +q = U32.from_nat(B.phase2_capacity_bound(U32.to_nat(n), U32.to_nat(rk),
                                                U32.to_nat(mk)))
      do IO<Unit>:
        Unit <- IO.print(U32.show(n) ++ " " ++ U32.show(rk) ++ " "
                         ++ U32.show(mk) ++ " " ++ U32.show(t) ++ " "
                         ++ U32.show(q))
        loop(p, U32.inc(j))

def main() -> IO(Unit):
  loop(300n, 0)
