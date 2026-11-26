import Base

# One lane of pure dependent arithmetic, then a write to its own cell.
def spin(+n: Nat, +acc: U32, +i: U32, a: Array<U32>) -> Array<U32>:
  match n:
    case 0n:
      Array.set(U32, a, i, acc)
    case 1n+f:
      +a2 = U32.add(U32.mul(acc, 1664525), 1013904223)
      spin(f, a2, i, a)

def keep4(b: Array<U32>, c: Array<U32>, d: Array<U32>, e: Array<U32>) -> Array<U32>:
  e

def l4(q: Array<U32> & Array<U32>, h0: Array<U32>, h1: Array<U32> +v0: U32, +n: Nat) -> Array<U32>:
  (h2, h3) = q
  b c d e = spin(n, v0, 0, h0) spin(n, v0, 1, h1) spin(n, v0, 2, h2) spin(n, v0, 3, h3)
  keep4(b, c, d, e)

def l3(q: Array<U32> & Array<U32>, h0: Array<U32>, +v0: U32, +n: Nat) -> Array<U32>:
  (h1, r) = q
  l4(Array.fork(U32, r), h0, h1, v0, n)

def l2(q: Array<U32> & Array<U32>, +v0: U32, +n: Nat) -> Array<U32>:
  (h0, r) = q
  l3(Array.fork(U32, r), h0, v0, n)

def go(a: Array<U32>, +v0: U32, +n: Nat) -> Array<U32>:
  l2(Array.fork(U32, a), v0, n)

def pu(r: Array<U32> & U32) -> IO(Array<U32>):
  (a, +v) = r
  do IO<Array<U32>>:
    Unit <- IO.print(U32.show(v))
    IO.pure(Array<U32>, a)

def main() -> IO(Unit):
  a = Array.new(U32, 4n, 0)
  c = go(a, 7, 4000000000n)
  do IO<Unit>:
    a1 : Array<U32> <- pu(Array.get(U32, c, 0))
    a2 : Array<U32> <- pu(Array.get(U32, a1, 1))
    a3 : Array<U32> <- pu(Array.get(U32, a2, 2))
    a4 : Array<U32> <- pu(Array.get(U32, a3, 3))
    Unit <- IO.print("done")
    IO.pure(Unit, Unit{})
