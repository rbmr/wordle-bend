import Base
import ../src/tree.bend as Tree
import ../src/groups.bend as Groups
import ../src/solve_fast.bend as SolveFast
import ./nat.bend as NatProof
import ./logic.bend as Logic
import ./fast_lb.bend as FS
import ./fast_nodup.bend as FN
import ./lb_capacity.bend as CapProof

# ---------------------------------------------------------------------------
# Obligation C, hypothesis-carrying class cost bound
# ---------------------------------------------------------------------------
#
# Once a class of size `m` has a branching factor `k` (obligation B) and the
# abstract capacity soundness theorem (obligation A, `LB.capbound_sound`) is
# available, every valid tree over the class costs at least
#
#   max(2*m - 1, capbound(m, k)).
#
# The `2*m - 1` half is the depth-two bound of `fast_lb.bend` for a
# duplicate-free class. The capacity half is exactly A, carried here as the
# explicit premise `hcap`; when A lands on main this file discharges it and the
# premise disappears. Nothing here states A itself.

def CKC.max_le(a: Nat, b: Nat, c: Nat,
    ha: {Nat.is_le(a, c) == True{} : Bool},
    hb: {Nat.is_le(b, c) == True{} : Bool}) ->
  {Nat.is_le(Nat.max(a, b), c) == True{} : Bool}:
  match a b:
    case 0n _:
      hb
    case 1n+ap 0n:
      ha
    case 1n++ap 1n++bp:
      match c:
        case 0n:
          Empty.absurd({Nat.is_le(Nat.max(1n+ap, 1n+bp), 0n) == True{} : Bool},
            Logic.Proof.false_ne_true(ha))
        case 1n++cp:
          +ha2 : {Nat.is_le(ap, cp) == True{} : Bool} =
            NatProof.Nat.is_le_succ_inv(ap, cp, ha)
          +hb2 : {Nat.is_le(bp, cp) == True{} : Bool} =
            NatProof.Nat.is_le_succ_inv(bp, cp, hb)
          NatProof.Nat.is_le_succ(Nat.max(ap, bp), cp,
            CKC.max_le(ap, bp, cp, ha2, hb2))

def CKC.class_cost(+m: Nat, +k: Nat, t: Tree.Tree,
    +G: +List<+List<Nat>>, +ws: +List<+List<Nat>>,
    v: Tree.Valid(t, G, ws),
    +hnodup: {FN.FN.no_dup_ref(ws) == True{} : Bool},
    +hm: {m == Groups.len_words(ws) : Nat},
    +hcap: {Nat.is_le(CapProof.LB.capbound(m, k), Tree.cost(t, ws))
           == True{} : Bool}) ->
  {Nat.is_le(Nat.max(SolveFast.class_lb_fast(True{}, m, ws),
                     CapProof.LB.capbound(m, k)),
             Tree.cost(t, ws)) == True{} : Bool}:
  +tc : Tree.Tree = t
  +hclb : {Nat.is_le(SolveFast.class_lb(ws), Tree.cost(tc, ws))
           == True{} : Bool} =
    FS.FS.valid_cost_ge_class_lb(tc, G, ws, v)
  +em : {Nat.sub(Nat.add(m, m), 1n) == SolveFast.class_lb(ws) : Nat} =
    Equal.trans(Nat,
      Nat.sub(Nat.add(m, m), 1n),
      Nat.sub(Nat.add(Groups.len_words(ws), Groups.len_words(ws)), 1n),
      SolveFast.class_lb(ws),
      Equal.cong(Nat, Nat,
        x => Nat.sub(Nat.add(x, x), 1n),
        m, Groups.len_words(ws), hm),
      FN.FN.class_lb_nodup_eq(ws, hnodup))
  +hfast : {Nat.is_le(SolveFast.class_lb_fast(True{}, m, ws),
                      Tree.cost(tc, ws)) == True{} : Bool} =
    NatProof.Nat.is_le_eq_l(Tree.cost(tc, ws),
      SolveFast.class_lb(ws),
      SolveFast.class_lb_fast(True{}, m, ws),
      Equal.sym(Nat, SolveFast.class_lb_fast(True{}, m, ws),
        SolveFast.class_lb(ws), em),
      hclb)
  CKC.max_le(SolveFast.class_lb_fast(True{}, m, ws),
    CapProof.LB.capbound(m, k), Tree.cost(tc, ws), hfast, hcap)

# `max a b <= c` from both bounds (local copy: no module on this path exports
# it, and keeping it here avoids another import).
