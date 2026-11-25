import Base
import ../src/bounds.bend as B

def p(+s: String, n: Nat) -> IO(Unit):
  IO.print(s ++ "=" ++ Nat.show(n))

def main() -> IO(Unit):
  do IO<Unit>:
    p("cap1k3", B.capacity_bound(1n, 3n))
    p("cap2k3", B.capacity_bound(2n, 3n))
    p("cap3k3", B.capacity_bound(3n, 3n))
    p("cap4k3", B.capacity_bound(4n, 3n))
    p("cap7k3", B.capacity_bound(7n, 3n))
    p("cap20k100", B.capacity_bound(20n, 100n))
    p("tight5k2", B.tight_capacity_bound(5n, 2n, 2n))
    p("phase5k2", B.phase2_capacity_bound(5n, 2n, 2n))
    p("bucket5k2", B.bucket_capacity_bound(5n, 2n, 2n))
    p("cap300k30", B.capacity_bound(300n, 30n))
