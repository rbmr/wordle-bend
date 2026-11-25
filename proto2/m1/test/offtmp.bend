import Base
import ../src/geo.bend as G

def main() -> IO(Unit):
  do IO<Unit>:
    Unit <- IO.print("off_tt " ++ U32.show(G.off_tt(123, 14855)))
    Unit <- IO.print("off_cap " ++ U32.show(G.off_cap(123, 14855)))
    Unit <- IO.print("off_hh " ++ U32.show(G.off_hh(123, 14855)))
    Unit <- IO.print("tt_size " ++ U32.show(G.tt_size()))
    Unit <- IO.print("total " ++ U32.show(G.total_size(123, 14855)))
    Unit <- IO.print("off_tt0 " ++ U32.show(G.off_tt(0, 0)))
    IO.pure(Unit, Unit{})
