import Base
import ../src/p12.bend as P

def fill(+fuel: Nat, +i: U32, a: Array<U32>) -> Array<U32>:
  match fuel:
    case 0n:
      a
    case 1n+f:
      a1 = Array.set(U32, a, U32.mul(i, 3), U32.sub(10, i))
      a2 = Array.set(U32, a1, U32.add(U32.mul(i, 3), 1), U32.add(100, i))
      a3 = Array.set(U32, a2, U32.add(U32.mul(i, 3), 2), U32.add(200, i))
      fill(f, U32.inc(i), a3)

def prn(r: Array<U32> & U32) -> IO(Array<U32>):
  (a, v) = r
  do IO<Array<U32>>:
    Unit <- IO.print(U32.show(v))
    IO.pure(Array<U32>, a)

def dump(+fuel: Nat, +i: U32, +n: U32, r: Array<U32> & U32) -> IO(Unit):
  match fuel:
    case 0n:
      (a, _) = r
      IO.pure(Unit, Unit{})
    case 1n+f:
      (a, +v) = r
      do IO<Unit>:
        Unit <- IO.print("tuple " ++ U32.show(i) ++ " lb " ++ U32.show(v))
        dump(f, U32.inc(i), n, Array.get(U32, a, U32.add(U32.mul(i, 3), 1)))

def go(a: Array<U32>, +n: U32) -> IO(Unit):
  do IO<Unit>:
    a1 : Array<U32> = fill(U32.to_nat(n), 0, a)
    b0 : Array<U32> <- prn(Array.get(U32, a1, 0))
    b1 : Array<U32> <- prn(Array.get(U32, b0, 1))
    b2 : Array<U32> <- prn(Array.get(U32, b1, 2))
    b3 : Array<U32> <- prn(Array.get(U32, b2, 3))
    b4 : Array<U32> <- prn(Array.get(U32, b3, 4))
    b5 : Array<U32> <- prn(Array.get(U32, b4, 5))
    a2 : Array<U32> = P.sort3(b5, 0, n)
    a3 : Array<U32> <- prn(Array.get(U32, a2, 0))
    a4 : Array<U32> <- prn(Array.get(U32, a3, 1))
    a5 : Array<U32> <- prn(Array.get(U32, a4, 2))
    a6 : Array<U32> <- prn(Array.get(U32, a5, 3))
    a7 : Array<U32> <- prn(Array.get(U32, a6, 4))
    a8 : Array<U32> <- prn(Array.get(U32, a7, 5))
    a9 : Array<U32> <- prn(Array.get(U32, a8, 6))
    a10 : Array<U32> <- prn(Array.get(U32, a9, 7))
    a11 : Array<U32> <- prn(Array.get(U32, a10, 8))
    a12 : Array<U32> <- prn(Array.get(U32, a11, 9))
    a13 : Array<U32> <- prn(Array.get(U32, a12, 10))
    a14 : Array<U32> <- prn(Array.get(U32, a13, 11))
    a15 : Array<U32> <- prn(Array.get(U32, a14, 12))
    a16 : Array<U32> <- prn(Array.get(U32, a15, 13))
    a17 : Array<U32> <- prn(Array.get(U32, a16, 14))
    IO.pure(Unit, Unit{})

def main() -> IO(Unit):
  do IO<Unit>:
    a : Array<U32> = Array.new(U32, 4n, 0)
    go(a, 5)
