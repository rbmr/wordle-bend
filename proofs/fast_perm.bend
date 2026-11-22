# Group-list permutations (`FP.Perm`) and preservation of all validity,
# bound, and optimality invariants under child-class reordering (LCF).
import Base
import ../src/feedback.bend as Feedback
import ../src/tree.bend as Tree
import ../src/groups.bend as Groups
import ../src/solve_ref.bend as SolveRef
import ../src/solve_fast.bend as SolveFast
import ./logic.bend as Logic
import ./nat.bend as NatProof
import ./feedback.bend as FbProof
import ./eval.bend as Eval
import ./sat.bend as Sat
import ./optfold.bend as Fold
import ./classbound_kids.bend as CBK
import ./nodevalid.bend as NV
import ./groupcost.bend as GC
import ./mainvalid.bend as MV
import ./fast_one.bend as FO
import ./fast_nodup.bend as FN
import ./fast_cutoff.bend as FC
import ./fast_lb.bend as FLB
import ./array.bend as Arr

# Concrete permutation script over `+List<Groups.Group>` and its `Data`
# validity predicate.
type FP.Perm is Data:
  PRefl{}
  PSkip{p: FP.Perm}
  PSwap{}
  PTrans{mid: +List<Groups.Group>, p1: FP.Perm, p2: FP.Perm}

def FP.PermOk(p: FP.Perm, +xs: +List<Groups.Group>,
              +ys: +List<Groups.Group>) -> Data:
  match p:
    case PRefl{}:
      {xs == ys : +List<Groups.Group>}
    case PSkip{pr}:
      match xs:
        case Nil{}:
          Empty
        case Con{hx, tx}:
          match ys:
            case Nil{}:
              Empty
            case Con{hy, ty}:
              Arr.Arr.DPair<{hx == hy : Groups.Group}, FP.PermOk(pr, tx, ty)>
    case PSwap{}:
      match xs:
        case Nil{}:
          Empty
        case Con{a, t1}:
          match t1:
            case Nil{}:
              Empty
            case Con{b, tx}:
              match ys:
                case Nil{}:
                  Empty
                case Con{c, t2}:
                  match t2:
                    case Nil{}:
                      Empty
                    case Con{d, ty}:
                      Arr.Arr.DPair<{a == d : Groups.Group},
                        Arr.Arr.DPair<{b == c : Groups.Group},
                          {tx == ty : +List<Groups.Group>}>>
    case PTrans{mid, p1, p2}:
      Arr.Arr.DPair<FP.PermOk(p1, xs, mid), FP.PermOk(p2, mid, ys)>

# Symmetry of `FP.Perm`.
def FP.perm_sym(p: FP.Perm) -> FP.Perm:
  match p:
    case PRefl{}:
      PRefl{}
    case PSkip{pr}:
      PSkip{FP.perm_sym(pr)}
    case PSwap{}:
      PSwap{}
    case PTrans{mid, p1, p2}:
      PTrans{mid, FP.perm_sym(p2), FP.perm_sym(p1)}

def FP.perm_sym_ok(p: FP.Perm, +xs: +List<Groups.Group>,
    +ys: +List<Groups.Group>, +ok: FP.PermOk(p, xs, ys)) ->
  FP.PermOk(FP.perm_sym(p), ys, xs):
  match p:
    case PRefl{}:
      Equal.sym(+List<Groups.Group>, xs, ys, ok)
    case PSkip{pr}:
      match xs:
        case Nil{}:
          Empty.absurd(FP.PermOk(PSkip{FP.perm_sym(pr)}, ys, Nil{}), ok)
        case Con{+hx, +tx}:
          match ys:
            case Nil{}:
              Empty.absurd(
                FP.PermOk(PSkip{FP.perm_sym(pr)}, Nil{}, hx <> tx), ok)
            case Con{+hy, +ty}:
              +eh = Arr.Arr.dpair_l({hx == hy : Groups.Group},
                      FP.PermOk(pr, tx, ty), ok)
              +et = Arr.Arr.dpair_r({hx == hy : Groups.Group},
                      FP.PermOk(pr, tx, ty), ok)
              Arr.DPair{Equal.sym(Groups.Group, hx, hy, eh),
                FP.perm_sym_ok(pr, tx, ty, et)}
    case PSwap{}:
      match xs:
        case Nil{}:
          Empty.absurd(FP.PermOk(PSwap{}, ys, Nil{}), ok)
        case Con{+a, +t1}:
          match t1:
            case Nil{}:
              Empty.absurd(FP.PermOk(PSwap{}, ys, a <> Nil{}), ok)
            case Con{+b, +tx}:
              match ys:
                case Nil{}:
                  Empty.absurd(FP.PermOk(PSwap{}, Nil{}, a <> (b <> tx)), ok)
                case Con{+c, +t2}:
                  match t2:
                    case Nil{}:
                      Empty.absurd(
                        FP.PermOk(PSwap{}, c <> Nil{}, a <> (b <> tx)), ok)
                    case Con{+d, +ty}:
                      +ead = Arr.Arr.dpair_l({a == d : Groups.Group},
                               Arr.Arr.DPair<{b == c : Groups.Group},
                                 {tx == ty : +List<Groups.Group>}>, ok)
                      +r1 = Arr.Arr.dpair_r({a == d : Groups.Group},
                              Arr.Arr.DPair<{b == c : Groups.Group},
                                {tx == ty : +List<Groups.Group>}>, ok)
                      +ebc = Arr.Arr.dpair_l({b == c : Groups.Group},
                               {tx == ty : +List<Groups.Group>}, r1)
                      +et = Arr.Arr.dpair_r({b == c : Groups.Group},
                              {tx == ty : +List<Groups.Group>}, r1)
                      Arr.DPair{Equal.sym(Groups.Group, b, c, ebc),
                        Arr.DPair{Equal.sym(Groups.Group, a, d, ead),
                          Equal.sym(+List<Groups.Group>, tx, ty, et)}}
    case PTrans{+mid, p1, p2}:
      +ok1 = Arr.Arr.dpair_l(FP.PermOk(p1, xs, mid),
               FP.PermOk(p2, mid, ys), ok)
      +ok2 = Arr.Arr.dpair_r(FP.PermOk(p1, xs, mid),
               FP.PermOk(p2, mid, ys), ok)
      Arr.DPair{FP.perm_sym_ok(p2, mid, ys, ok2),
        FP.perm_sym_ok(p1, xs, mid, ok1)}

def FP.perm_skip_n(+xs: +List<Groups.Group>, p: FP.Perm) -> FP.Perm:
  match xs:
    case Nil{}:
      p
    case Con{_, t}:
      PSkip{FP.perm_skip_n(t, p)}

def FP.perm_append_l(+xs: +List<Groups.Group>, +ys1: +List<Groups.Group>,
    +ys2: +List<Groups.Group>, +p: FP.Perm, +ok: FP.PermOk(p, ys1, ys2)) ->
  FP.PermOk(FP.perm_skip_n(xs, p),
    List.append(&2, Groups.Group, xs, ys1),
    List.append(&2, Groups.Group, xs, ys2)):
  match xs:
    case Nil{}:
      ok
    case Con{+h, +t}:
      Arr.DPair{{==}, FP.perm_append_l(t, ys1, ys2, p, ok)}

# Moving an element from the middle of an append to the front:
# `xs ++ (x <> ys)` permutes to `x <> (xs ++ ys)`.
def FP.perm_pull(+x: Groups.Group, +xs: +List<Groups.Group>,
    +ys: +List<Groups.Group>) -> FP.Perm:
  match xs:
    case Nil{}:
      PRefl{}
    case Con{+h, +t}:
      PTrans{h <> (x <> List.append(&2, Groups.Group, t, ys)),
        PSkip{FP.perm_pull(x, t, ys)}, PSwap{}}

def FP.perm_pull_ok(+x: Groups.Group, +xs: +List<Groups.Group>,
    +ys: +List<Groups.Group>) ->
  FP.PermOk(FP.perm_pull(x, xs, ys),
    List.append(&2, Groups.Group, xs, x <> ys),
    x <> List.append(&2, Groups.Group, xs, ys)):
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Arr.DPair{
        Arr.DPair{{==}, FP.perm_pull_ok(x, t, ys)},
        Arr.DPair{{==}, Arr.DPair{{==}, {==}}}}

# Reversal onto an accumulator is a permutation of `List.append`.
def FP.rev_groups(+gs: +List<Groups.Group>,
    +acc: +List<Groups.Group>) -> +List<Groups.Group>:
  match gs:
    case Nil{}:
      acc
    case Con{gp, t}:
      FP.rev_groups(t, gp <> acc)

def FP.perm_rev_append(+xs: +List<Groups.Group>,
    +ys: +List<Groups.Group>) -> FP.Perm:
  match xs:
    case Nil{}:
      PRefl{}
    case Con{+h, +t}:
      PTrans{List.append(&2, Groups.Group, t, h <> ys),
        FP.perm_rev_append(t, h <> ys),
        FP.perm_pull(h, t, ys)}

def FP.perm_rev_append_ok(+xs: +List<Groups.Group>,
    +ys: +List<Groups.Group>) ->
  FP.PermOk(FP.perm_rev_append(xs, ys),
    FP.rev_groups(xs, ys),
    List.append(&2, Groups.Group, xs, ys)):
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Arr.DPair{
        FP.perm_rev_append_ok(t, h <> ys),
        FP.perm_pull_ok(h, t, ys)}

# ---------------------------------------------------------------------------
# Bool / Nat helpers for swap steps
# ---------------------------------------------------------------------------

def FP.bool_and_swap(+a: Bool, +b: Bool, +c: Bool) ->
  {Bool.and(a, Bool.and(b, c)) == Bool.and(b, Bool.and(a, c)) : Bool}:
  match a:
    case True{}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}

def FP.nat_add_swap(+a: Nat, +b: Nat, +c: Nat) ->
  {Nat.add(a, Nat.add(b, c)) == Nat.add(b, Nat.add(a, c)) : Nat}:
  FLB.FS.add_swap_l(a, b, c)

# ---------------------------------------------------------------------------
# 1. `CBK.distinctB` and `NV.InGroupsFb`
# ---------------------------------------------------------------------------

def FP.allNe_perm(p: FP.Perm, +f: +List<Feedback.Color>,
    +xs: +List<Groups.Group>, +ys: +List<Groups.Group>,
    +ok: FP.PermOk(p, xs, ys)) ->
  {CBK.CBK.allNe(f, xs) == CBK.CBK.allNe(f, ys) : Bool}:
  match p:
    case PRefl{}:
      Equal.cong(+List<Groups.Group>, Bool, gs => CBK.CBK.allNe(f, gs),
        xs, ys, ok)
    case PSkip{pr}:
      match xs:
        case Nil{}:
          Empty.absurd({CBK.CBK.allNe(f, Nil{}) == CBK.CBK.allNe(f, ys) : Bool}, ok)
        case Con{hx, tx}:
          match ys:
            case Nil{}:
              Empty.absurd(
                {CBK.CBK.allNe(f, hx <> tx) == CBK.CBK.allNe(f, Nil{}) : Bool}, ok)
            case Con{hy, ty}:
              match hy:
                case Groups.Group{+fy, +wy}:
                  +eh = Arr.Arr.dpair_l({hx == Groups.Group{fy, wy} : Groups.Group},
                          FP.PermOk(pr, tx, ty), ok)
                  +et = Arr.Arr.dpair_r({hx == Groups.Group{fy, wy} : Groups.Group},
                          FP.PermOk(pr, tx, ty), ok)
                  %Equal.sym(Groups.Group, hx, Groups.Group{fy, wy}, eh) : {CBK.CBK.allNe(f, _ <> tx) == CBK.CBK.allNe(f, Groups.Group{fy, wy} <> ty) : Bool}
                  Equal.cong(Bool, Bool,
                    b => Bool.and(Bool.not(Feedback.feedback_eq(f, fy)), b),
                    CBK.CBK.allNe(f, tx), CBK.CBK.allNe(f, ty),
                    FP.allNe_perm(pr, f, tx, ty, et))
    case PSwap{}:
      match xs:
        case Nil{}:
          Empty.absurd({CBK.CBK.allNe(f, Nil{}) == CBK.CBK.allNe(f, ys) : Bool}, ok)
        case Con{a, t1}:
          match t1:
            case Nil{}:
              Empty.absurd({CBK.CBK.allNe(f, a <> Nil{}) == CBK.CBK.allNe(f, ys) : Bool}, ok)
            case Con{b, tx}:
              match ys:
                case Nil{}:
                  Empty.absurd({CBK.CBK.allNe(f, a <> (b <> tx)) == True{} : Bool}, ok)
                case Con{c, t2}:
                  match c:
                    case Groups.Group{+fc, +wc}:
                      match t2:
                        case Nil{}:
                          Empty.absurd(
                            {CBK.CBK.allNe(f, a <> (b <> tx)) == CBK.CBK.allNe(f, Groups.Group{fc, wc} <> Nil{}) : Bool}, ok)
                        case Con{d, ty}:
                          match d:
                            case Groups.Group{+fd, +wd}:
                              +ead = Arr.Arr.dpair_l({a == Groups.Group{fd, wd} : Groups.Group},
                                       Arr.Arr.DPair<{b == Groups.Group{fc, wc} : Groups.Group},
                                         {tx == ty : +List<Groups.Group>}>, ok)
                              +r1 = Arr.Arr.dpair_r({a == Groups.Group{fd, wd} : Groups.Group},
                                      Arr.Arr.DPair<{b == Groups.Group{fc, wc} : Groups.Group},
                                        {tx == ty : +List<Groups.Group>}>, ok)
                              +ebc = Arr.Arr.dpair_l({b == Groups.Group{fc, wc} : Groups.Group},
                                       {tx == ty : +List<Groups.Group>}, r1)
                              +et = Arr.Arr.dpair_r({b == Groups.Group{fc, wc} : Groups.Group},
                                      {tx == ty : +List<Groups.Group>}, r1)
                              %Equal.sym(Groups.Group, a, Groups.Group{fd, wd}, ead) : {CBK.CBK.allNe(f, _ <> (b <> tx)) == CBK.CBK.allNe(f, Groups.Group{fc, wc} <> (Groups.Group{fd, wd} <> ty)) : Bool}
                              %Equal.sym(Groups.Group, b, Groups.Group{fc, wc}, ebc) : {CBK.CBK.allNe(f, Groups.Group{fd, wd} <> (_ <> tx)) == CBK.CBK.allNe(f, Groups.Group{fc, wc} <> (Groups.Group{fd, wd} <> ty)) : Bool}
                              %Equal.sym(+List<Groups.Group>, tx, ty, et) : {CBK.CBK.allNe(f, Groups.Group{fd, wd} <> (Groups.Group{fc, wc} <> _)) == CBK.CBK.allNe(f, Groups.Group{fc, wc} <> (Groups.Group{fd, wd} <> ty)) : Bool}
                              FP.bool_and_swap(
                                Bool.not(Feedback.feedback_eq(f, fd)),
                                Bool.not(Feedback.feedback_eq(f, fc)),
                                CBK.CBK.allNe(f, ty))
    case PTrans{+mid, p1, p2}:
      +ok1 = Arr.Arr.dpair_l(FP.PermOk(p1, xs, mid), FP.PermOk(p2, mid, ys), ok)
      +ok2 = Arr.Arr.dpair_r(FP.PermOk(p1, xs, mid), FP.PermOk(p2, mid, ys), ok)
      Equal.trans(Bool, CBK.CBK.allNe(f, xs), CBK.CBK.allNe(f, mid),
        CBK.CBK.allNe(f, ys),
        FP.allNe_perm(p1, f, xs, mid, ok1),
        FP.allNe_perm(p2, f, mid, ys, ok2))

def FP.bool_and4_swap(p: Bool, q: Bool, r: Bool, s: Bool) ->
  {Bool.and(Bool.and(p, q), Bool.and(r, s))
   == Bool.and(Bool.and(p, r), Bool.and(q, s)) : Bool}:
  match p:
    case True{}:
      match q:
        case True{}:
          match r:
            case True{}:
              {==}
            case False{}:
              {==}
        case False{}:
          match r:
            case True{}:
              {==}
            case False{}:
              {==}
    case False{}:
      {==}

def FP.distinctB_swap_aux(+fa: +List<Feedback.Color>, +fb: +List<Feedback.Color>,
    +t: +List<Groups.Group>) ->
  {Bool.and(Bool.and(Bool.not(Feedback.feedback_eq(fa, fb)), CBK.CBK.allNe(fa, t)),
     Bool.and(CBK.CBK.allNe(fb, t), CBK.CBK.distinctB(t)))
   == Bool.and(Bool.and(Bool.not(Feedback.feedback_eq(fb, fa)), CBK.CBK.allNe(fb, t)),
        Bool.and(CBK.CBK.allNe(fa, t), CBK.CBK.distinctB(t))) : Bool}:
  +esym : {Feedback.feedback_eq(fa, fb) == Feedback.feedback_eq(fb, fa) : Bool} =
    FbProof.FeedbackProof.feedback_eq_sym_bool(fa, fb)
  +p : Bool = Bool.not(Feedback.feedback_eq(fb, fa))
  +q : Bool = CBK.CBK.allNe(fa, t)
  +r : Bool = CBK.CBK.allNe(fb, t)
  +s : Bool = CBK.CBK.distinctB(t)
  %Equal.sym(Bool, Feedback.feedback_eq(fa, fb), Feedback.feedback_eq(fb, fa), esym) :
    {Bool.and(Bool.and(Bool.not(_), q), Bool.and(r, s))
     == Bool.and(Bool.and(p, r), Bool.and(q, s)) : Bool}
  FP.bool_and4_swap(p, q, r, s)

def FP.distinctB_perm(+p: FP.Perm, +xs: +List<Groups.Group>,
    +ys: +List<Groups.Group>, +ok: FP.PermOk(p, xs, ys)) ->
  {CBK.CBK.distinctB(xs) == CBK.CBK.distinctB(ys) : Bool}:
  match p:
    case PRefl{}:
      Equal.cong(+List<Groups.Group>, Bool, gs => CBK.CBK.distinctB(gs), xs, ys, ok)
    case PSkip{+pr}:
      match xs:
        case Nil{}:
          Empty.absurd({CBK.CBK.distinctB(Nil{}) == CBK.CBK.distinctB(ys) : Bool}, ok)
        case Con{hx, tx}:
          match ys:
            case Nil{}:
              Empty.absurd(
                {CBK.CBK.distinctB(hx <> tx) == CBK.CBK.distinctB(Nil{}) : Bool}, ok)
            case Con{hy, ty}:
              match hy:
                case Groups.Group{+fy, +wy}:
                  +eh = Arr.Arr.dpair_l({hx == Groups.Group{fy, wy} : Groups.Group},
                          FP.PermOk(pr, tx, ty), ok)
                  +et = Arr.Arr.dpair_r({hx == Groups.Group{fy, wy} : Groups.Group},
                          FP.PermOk(pr, tx, ty), ok)
                  %Equal.sym(Groups.Group, hx, Groups.Group{fy, wy}, eh) : {CBK.CBK.distinctB(_ <> tx) == CBK.CBK.distinctB(Groups.Group{fy, wy} <> ty) : Bool}
                  Equal.trans(Bool,
                    Bool.and(CBK.CBK.allNe(fy, tx), CBK.CBK.distinctB(tx)),
                    Bool.and(CBK.CBK.allNe(fy, ty), CBK.CBK.distinctB(tx)),
                    Bool.and(CBK.CBK.allNe(fy, ty), CBK.CBK.distinctB(ty)),
                    Equal.cong(Bool, Bool, b => Bool.and(b, CBK.CBK.distinctB(tx)),
                      CBK.CBK.allNe(fy, tx), CBK.CBK.allNe(fy, ty),
                      FP.allNe_perm(pr, fy, tx, ty, et)),
                    Equal.cong(Bool, Bool, b => Bool.and(CBK.CBK.allNe(fy, ty), b),
                      CBK.CBK.distinctB(tx), CBK.CBK.distinctB(ty),
                      FP.distinctB_perm(pr, tx, ty, et)))
    case PSwap{}:
      match xs:
        case Nil{}:
          Empty.absurd({CBK.CBK.distinctB(Nil{}) == CBK.CBK.distinctB(ys) : Bool}, ok)
        case Con{a, t1}:
          match t1:
            case Nil{}:
              Empty.absurd({CBK.CBK.distinctB(a <> Nil{}) == CBK.CBK.distinctB(ys) : Bool}, ok)
            case Con{b, tx}:
              match ys:
                case Nil{}:
                  Empty.absurd({CBK.CBK.distinctB(a <> (b <> tx)) == True{} : Bool}, ok)
                case Con{c, t2}:
                  match c:
                    case Groups.Group{+fc, +wc}:
                      match t2:
                        case Nil{}:
                          Empty.absurd(
                            {CBK.CBK.distinctB(a <> (b <> tx)) == CBK.CBK.distinctB(Groups.Group{fc, wc} <> Nil{}) : Bool}, ok)
                        case Con{d, ty}:
                          match d:
                            case Groups.Group{+fd, +wd}:
                              +ead = Arr.Arr.dpair_l({a == Groups.Group{fd, wd} : Groups.Group},
                                       Arr.Arr.DPair<{b == Groups.Group{fc, wc} : Groups.Group},
                                         {tx == ty : +List<Groups.Group>}>, ok)
                              +r1 = Arr.Arr.dpair_r({a == Groups.Group{fd, wd} : Groups.Group},
                                      Arr.Arr.DPair<{b == Groups.Group{fc, wc} : Groups.Group},
                                        {tx == ty : +List<Groups.Group>}>, ok)
                              +ebc = Arr.Arr.dpair_l({b == Groups.Group{fc, wc} : Groups.Group},
                                       {tx == ty : +List<Groups.Group>}, r1)
                              +et = Arr.Arr.dpair_r({b == Groups.Group{fc, wc} : Groups.Group},
                                      {tx == ty : +List<Groups.Group>}, r1)
                              %Equal.sym(Groups.Group, a, Groups.Group{fd, wd}, ead) : {CBK.CBK.distinctB(_ <> (b <> tx)) == CBK.CBK.distinctB(Groups.Group{fc, wc} <> (Groups.Group{fd, wd} <> ty)) : Bool}
                              %Equal.sym(Groups.Group, b, Groups.Group{fc, wc}, ebc) : {CBK.CBK.distinctB(Groups.Group{fd, wd} <> (_ <> tx)) == CBK.CBK.distinctB(Groups.Group{fc, wc} <> (Groups.Group{fd, wd} <> ty)) : Bool}
                              %Equal.sym(+List<Groups.Group>, tx, ty, et) : {CBK.CBK.distinctB(Groups.Group{fd, wd} <> (Groups.Group{fc, wc} <> _)) == CBK.CBK.distinctB(Groups.Group{fc, wc} <> (Groups.Group{fd, wd} <> ty)) : Bool}
                              FP.distinctB_swap_aux(fd, fc, ty)
    case PTrans{+mid, p1, p2}:
      +ok1 = Arr.Arr.dpair_l(FP.PermOk(p1, xs, mid), FP.PermOk(p2, mid, ys), ok)
      +ok2 = Arr.Arr.dpair_r(FP.PermOk(p1, xs, mid), FP.PermOk(p2, mid, ys), ok)
      Equal.trans(Bool, CBK.CBK.distinctB(xs), CBK.CBK.distinctB(mid),
        CBK.CBK.distinctB(ys),
        FP.distinctB_perm(p1, xs, mid, ok1),
        FP.distinctB_perm(p2, mid, ys, ok2))

def FP.in_groups_fb_skip_go(+fx: +List<Feedback.Color>, +wx: +List<+List<Nat>>,
    +tx: +List<Groups.Group>, +ty: +List<Groups.Group>, +w: +List<Nat>,
    +fb: +List<Feedback.Color>,
    m: NV.NV.InGroupsFb(w, fb, Groups.Group{fx, wx} <> tx),
    rec: NV.NV.InGroupsFb(w, fb, tx) -> NV.NV.InGroupsFb(w, fb, ty)) ->
  NV.NV.InGroupsFb(w, fb, Groups.Group{fx, wx} <> ty):
  match m:
    case Inl{pin}:
      Inl{pin}
    case Inr{mt}:
      Inr{rec(mt)}

def FP.in_groups_fb_swap_go(+fa: +List<Feedback.Color>, +wa: +List<+List<Nat>>,
    +fb2: +List<Feedback.Color>, +wb: +List<+List<Nat>>,
    +tx: +List<Groups.Group>, +w: +List<Nat>, +fb: +List<Feedback.Color>,
    m: NV.NV.InGroupsFb(w, fb, Groups.Group{fa, wa} <> (Groups.Group{fb2, wb} <> tx))) ->
  NV.NV.InGroupsFb(w, fb, Groups.Group{fb2, wb} <> (Groups.Group{fa, wa} <> tx)):
  match m:
    case Inl{pa}:
      Inr{Inl{pa}}
    case Inr{m1}:
      match m1:
        case Inl{pb}:
          Inl{pb}
        case Inr{mt}:
          Inr{Inr{mt}}

def FP.in_groups_fb_perm(p: FP.Perm, +xs: +List<Groups.Group>,
    +ys: +List<Groups.Group>, +ok: FP.PermOk(p, xs, ys),
    +w: +List<Nat>, +fb: +List<Feedback.Color>,
    m: NV.NV.InGroupsFb(w, fb, xs)) -> NV.NV.InGroupsFb(w, fb, ys):
  match p:
    case PRefl{}:
      %ok : NV.NV.InGroupsFb(w, fb, _)
      m
    case PSkip{pr}:
      match xs:
        case Nil{}:
          Empty.absurd(NV.NV.InGroupsFb(w, fb, ys), ok)
        case Con{hx, tx}:
          match hx:
            case Groups.Group{+fx, +wx}:
              match ys:
                case Nil{}:
                  Empty.absurd(NV.NV.InGroupsFb(w, fb, Nil{}), ok)
                case Con{hy, ty}:
                  +eh = Arr.Arr.dpair_l({Groups.Group{fx, wx} == hy : Groups.Group},
                          FP.PermOk(pr, tx, ty), ok)
                  +et = Arr.Arr.dpair_r({Groups.Group{fx, wx} == hy : Groups.Group},
                          FP.PermOk(pr, tx, ty), ok)
                  %eh :
                    NV.NV.InGroupsFb(w, fb, _ <> ty)
                  FP.in_groups_fb_skip_go(fx, wx, tx, ty, w, fb, m,
                    mt => FP.in_groups_fb_perm(pr, tx, ty, et, w, fb, mt))
    case PSwap{}:
      match xs:
        case Nil{}:
          Empty.absurd(NV.NV.InGroupsFb(w, fb, ys), ok)
        case Con{a, t1}:
          match a:
            case Groups.Group{+fa, +wa}:
              match t1:
                case Nil{}:
                  Empty.absurd(NV.NV.InGroupsFb(w, fb, ys), ok)
                case Con{b, tx}:
                  match b:
                    case Groups.Group{+fb2, +wb}:
                      match ys:
                        case Nil{}:
                          Empty.absurd(NV.NV.InGroupsFb(w, fb, Nil{}), ok)
                        case Con{c, t2}:
                          match t2:
                            case Nil{}:
                              Empty.absurd(NV.NV.InGroupsFb(w, fb, c <> Nil{}), ok)
                            case Con{d, ty}:
                              +ead = Arr.Arr.dpair_l({Groups.Group{fa, wa} == d : Groups.Group},
                                       Arr.Arr.DPair<{Groups.Group{fb2, wb} == c : Groups.Group},
                                         {tx == ty : +List<Groups.Group>}>, ok)
                              +r1 = Arr.Arr.dpair_r({Groups.Group{fa, wa} == d : Groups.Group},
                                      Arr.Arr.DPair<{Groups.Group{fb2, wb} == c : Groups.Group},
                                        {tx == ty : +List<Groups.Group>}>, ok)
                              +ebc = Arr.Arr.dpair_l({Groups.Group{fb2, wb} == c : Groups.Group},
                                       {tx == ty : +List<Groups.Group>}, r1)
                              +et = Arr.Arr.dpair_r({Groups.Group{fb2, wb} == c : Groups.Group},
                                      {tx == ty : +List<Groups.Group>}, r1)
                              %ead :
                                NV.NV.InGroupsFb(w, fb, c <> (_ <> ty))
                              %ebc :
                                NV.NV.InGroupsFb(w, fb, _ <> (Groups.Group{fa, wa} <> ty))
                              %et :
                                NV.NV.InGroupsFb(w, fb, Groups.Group{fb2, wb} <> (Groups.Group{fa, wa} <> _))
                              FP.in_groups_fb_swap_go(fa, wa, fb2, wb, tx, w, fb, m)
    case PTrans{+mid, p1, p2}:
      +ok1 = Arr.Arr.dpair_l(FP.PermOk(p1, xs, mid), FP.PermOk(p2, mid, ys), ok)
      +ok2 = Arr.Arr.dpair_r(FP.PermOk(p1, xs, mid), FP.PermOk(p2, mid, ys), ok)
      FP.in_groups_fb_perm(p2, mid, ys, ok2, w, fb,
        FP.in_groups_fb_perm(p1, xs, mid, ok1, w, fb, m))

# ---------------------------------------------------------------------------
# 2. Additive / multiplicative folds: `GC.Total`, `lower_bound`,
#    `groups_smaller`, `all_in_jobs_b`, `nodup_ok_jobs`, `MV.Bounds`
# ---------------------------------------------------------------------------

def FP.total_perm(p: FP.Perm, +ks: +List<Tree.Child>,
    +xs: +List<Groups.Group>, +ys: +List<Groups.Group>,
    +ok: FP.PermOk(p, xs, ys)) ->
  {GC.GC.Total(ks, xs) == GC.GC.Total(ks, ys) : Nat}:
  match p:
    case PRefl{}:
      Equal.cong(+List<Groups.Group>, Nat, gs => GC.GC.Total(ks, gs), xs, ys, ok)
    case PSkip{pr}:
      match xs:
        case Nil{}:
          Empty.absurd({GC.GC.Total(ks, Nil{}) == GC.GC.Total(ks, ys) : Nat}, ok)
        case Con{hx, tx}:
          match ys:
            case Nil{}:
              Empty.absurd({GC.GC.Total(ks, hx <> tx) == 0n : Nat}, ok)
            case Con{hy, ty}:
              +eh = Arr.Arr.dpair_l({hx == hy : Groups.Group},
                      FP.PermOk(pr, tx, ty), ok)
              +et = Arr.Arr.dpair_r({hx == hy : Groups.Group},
                      FP.PermOk(pr, tx, ty), ok)
              %Equal.sym(Groups.Group, hx, hy, eh) : {GC.GC.Total(ks, _ <> tx) == GC.GC.Total(ks, hy <> ty) : Nat}
              Equal.cong(Nat, Nat, z => Nat.add(GC.GC.GroupCost(ks, hy), z),
                GC.GC.Total(ks, tx), GC.GC.Total(ks, ty),
                FP.total_perm(pr, ks, tx, ty, et))
    case PSwap{}:
      match xs:
        case Nil{}:
          Empty.absurd({0n == GC.GC.Total(ks, ys) : Nat}, ok)
        case Con{a, t1}:
          match t1:
            case Nil{}:
              Empty.absurd({GC.GC.Total(ks, a <> Nil{}) == GC.GC.Total(ks, ys) : Nat}, ok)
            case Con{b, tx}:
              match ys:
                case Nil{}:
                  Empty.absurd({GC.GC.Total(ks, a <> (b <> tx)) == 0n : Nat}, ok)
                case Con{c, t2}:
                  match t2:
                    case Nil{}:
                      Empty.absurd({GC.GC.Total(ks, a <> (b <> tx)) == GC.GC.Total(ks, c <> Nil{}) : Nat}, ok)
                    case Con{d, ty}:
                      +ead = Arr.Arr.dpair_l({a == d : Groups.Group},
                               Arr.Arr.DPair<{b == c : Groups.Group},
                                 {tx == ty : +List<Groups.Group>}>, ok)
                      +r1 = Arr.Arr.dpair_r({a == d : Groups.Group},
                              Arr.Arr.DPair<{b == c : Groups.Group},
                                {tx == ty : +List<Groups.Group>}>, ok)
                      +ebc = Arr.Arr.dpair_l({b == c : Groups.Group},
                               {tx == ty : +List<Groups.Group>}, r1)
                      +et = Arr.Arr.dpair_r({b == c : Groups.Group},
                              {tx == ty : +List<Groups.Group>}, r1)
                      %Equal.sym(Groups.Group, a, d, ead) : {GC.GC.Total(ks, _ <> (b <> tx)) == GC.GC.Total(ks, c <> (d <> ty)) : Nat}
                      %Equal.sym(Groups.Group, b, c, ebc) : {GC.GC.Total(ks, d <> (_ <> tx)) == GC.GC.Total(ks, c <> (d <> ty)) : Nat}
                      %Equal.sym(+List<Groups.Group>, tx, ty, et) : {GC.GC.Total(ks, d <> (c <> _)) == GC.GC.Total(ks, c <> (d <> ty)) : Nat}
                      FP.nat_add_swap(GC.GC.GroupCost(ks, d),
                        GC.GC.GroupCost(ks, c), GC.GC.Total(ks, ty))
    case PTrans{+mid, p1, p2}:
      +ok1 = Arr.Arr.dpair_l(FP.PermOk(p1, xs, mid), FP.PermOk(p2, mid, ys), ok)
      +ok2 = Arr.Arr.dpair_r(FP.PermOk(p1, xs, mid), FP.PermOk(p2, mid, ys), ok)
      Equal.trans(Nat, GC.GC.Total(ks, xs), GC.GC.Total(ks, mid),
        GC.GC.Total(ks, ys),
        FP.total_perm(p1, ks, xs, mid, ok1),
        FP.total_perm(p2, ks, mid, ys, ok2))

def FP.lower_bound_perm(p: FP.Perm, +n: Nat, +xs: +List<Groups.Group>,
    +ys: +List<Groups.Group>, +ok: FP.PermOk(p, xs, ys)) ->
  {SolveFast.lower_bound(n, xs) == SolveFast.lower_bound(n, ys) : Nat}:
  match p:
    case PRefl{}:
      Equal.cong(+List<Groups.Group>, Nat, gs => SolveFast.lower_bound(n, gs),
        xs, ys, ok)
    case PSkip{pr}:
      match xs:
        case Nil{}:
          Empty.absurd({n == SolveFast.lower_bound(n, ys) : Nat}, ok)
        case Con{hx, tx}:
          match ys:
            case Nil{}:
              Empty.absurd({SolveFast.lower_bound(n, hx <> tx) == n : Nat}, ok)
            case Con{hy, ty}:
              match hy:
                case Groups.Group{+fy, +wy}:
                  +eh = Arr.Arr.dpair_l({hx == Groups.Group{fy, wy} : Groups.Group},
                          FP.PermOk(pr, tx, ty), ok)
                  +et = Arr.Arr.dpair_r({hx == Groups.Group{fy, wy} : Groups.Group},
                          FP.PermOk(pr, tx, ty), ok)
                  %Equal.sym(Groups.Group, hx, Groups.Group{fy, wy}, eh) : {SolveFast.lower_bound(n, _ <> tx) == SolveFast.lower_bound(n, Groups.Group{fy, wy} <> ty) : Nat}
                  Equal.cong(Nat, Nat, z => Nat.add(SolveFast.class_lb(wy), z),
                    SolveFast.lower_bound(n, tx), SolveFast.lower_bound(n, ty),
                    FP.lower_bound_perm(pr, n, tx, ty, et))
    case PSwap{}:
      match xs:
        case Nil{}:
          Empty.absurd({n == SolveFast.lower_bound(n, ys) : Nat}, ok)
        case Con{a, t1}:
          match t1:
            case Nil{}:
              Empty.absurd({SolveFast.lower_bound(n, a <> Nil{}) == SolveFast.lower_bound(n, ys) : Nat}, ok)
            case Con{b, tx}:
              match ys:
                case Nil{}:
                  Empty.absurd({SolveFast.lower_bound(n, a <> (b <> tx)) == n : Nat}, ok)
                case Con{c, t2}:
                  match c:
                    case Groups.Group{+fc, +wc}:
                      match t2:
                        case Nil{}:
                          Empty.absurd({SolveFast.lower_bound(n, a <> (b <> tx)) == SolveFast.lower_bound(n, Groups.Group{fc, wc} <> Nil{}) : Nat}, ok)
                        case Con{d, ty}:
                          match d:
                            case Groups.Group{+fd, +wd}:
                              +ead = Arr.Arr.dpair_l({a == Groups.Group{fd, wd} : Groups.Group},
                                       Arr.Arr.DPair<{b == Groups.Group{fc, wc} : Groups.Group},
                                         {tx == ty : +List<Groups.Group>}>, ok)
                              +r1 = Arr.Arr.dpair_r({a == Groups.Group{fd, wd} : Groups.Group},
                                      Arr.Arr.DPair<{b == Groups.Group{fc, wc} : Groups.Group},
                                        {tx == ty : +List<Groups.Group>}>, ok)
                              +ebc = Arr.Arr.dpair_l({b == Groups.Group{fc, wc} : Groups.Group},
                                       {tx == ty : +List<Groups.Group>}, r1)
                              +et = Arr.Arr.dpair_r({b == Groups.Group{fc, wc} : Groups.Group},
                                      {tx == ty : +List<Groups.Group>}, r1)
                              %Equal.sym(Groups.Group, a, Groups.Group{fd, wd}, ead) : {SolveFast.lower_bound(n, _ <> (b <> tx)) == SolveFast.lower_bound(n, Groups.Group{fc, wc} <> (Groups.Group{fd, wd} <> ty)) : Nat}
                              %Equal.sym(Groups.Group, b, Groups.Group{fc, wc}, ebc) : {SolveFast.lower_bound(n, Groups.Group{fd, wd} <> (_ <> tx)) == SolveFast.lower_bound(n, Groups.Group{fc, wc} <> (Groups.Group{fd, wd} <> ty)) : Nat}
                              %Equal.sym(+List<Groups.Group>, tx, ty, et) : {SolveFast.lower_bound(n, Groups.Group{fd, wd} <> (Groups.Group{fc, wc} <> _)) == SolveFast.lower_bound(n, Groups.Group{fc, wc} <> (Groups.Group{fd, wd} <> ty)) : Nat}
                              FP.nat_add_swap(SolveFast.class_lb(wd),
                                SolveFast.class_lb(wc),
                                SolveFast.lower_bound(n, ty))
    case PTrans{+mid, p1, p2}:
      +ok1 = Arr.Arr.dpair_l(FP.PermOk(p1, xs, mid), FP.PermOk(p2, mid, ys), ok)
      +ok2 = Arr.Arr.dpair_r(FP.PermOk(p1, xs, mid), FP.PermOk(p2, mid, ys), ok)
      Equal.trans(Nat, SolveFast.lower_bound(n, xs),
        SolveFast.lower_bound(n, mid), SolveFast.lower_bound(n, ys),
        FP.lower_bound_perm(p1, n, xs, mid, ok1),
        FP.lower_bound_perm(p2, n, mid, ys, ok2))

def FP.groups_smaller_perm(p: FP.Perm, +S: +List<+List<Nat>>,
    +xs: +List<Groups.Group>, +ys: +List<Groups.Group>,
    +ok: FP.PermOk(p, xs, ys)) ->
  {Groups.groups_smaller(S, xs) == Groups.groups_smaller(S, ys) : Bool}:
  match p:
    case PRefl{}:
      Equal.cong(+List<Groups.Group>, Bool, gs => Groups.groups_smaller(S, gs),
        xs, ys, ok)
    case PSkip{pr}:
      match xs:
        case Nil{}:
          Empty.absurd({True{} == Groups.groups_smaller(S, ys) : Bool}, ok)
        case Con{hx, tx}:
          match ys:
            case Nil{}:
              Empty.absurd({Groups.groups_smaller(S, hx <> tx) == True{} : Bool}, ok)
            case Con{hy, ty}:
              match hy:
                case Groups.Group{+fy, +wy}:
                  +eh = Arr.Arr.dpair_l({hx == Groups.Group{fy, wy} : Groups.Group},
                          FP.PermOk(pr, tx, ty), ok)
                  +et = Arr.Arr.dpair_r({hx == Groups.Group{fy, wy} : Groups.Group},
                          FP.PermOk(pr, tx, ty), ok)
                  %Equal.sym(Groups.Group, hx, Groups.Group{fy, wy}, eh) : {Groups.groups_smaller(S, _ <> tx) == Groups.groups_smaller(S, Groups.Group{fy, wy} <> ty) : Bool}
                  Equal.cong(Bool, Bool,
                    b => Bool.and(Nat.is_lt(Groups.len_words(wy), Groups.len_words(S)), b),
                    Groups.groups_smaller(S, tx), Groups.groups_smaller(S, ty),
                    FP.groups_smaller_perm(pr, S, tx, ty, et))
    case PSwap{}:
      match xs:
        case Nil{}:
          Empty.absurd({True{} == Groups.groups_smaller(S, ys) : Bool}, ok)
        case Con{a, t1}:
          match t1:
            case Nil{}:
              Empty.absurd({Groups.groups_smaller(S, a <> Nil{}) == Groups.groups_smaller(S, ys) : Bool}, ok)
            case Con{b, tx}:
              match ys:
                case Nil{}:
                  Empty.absurd({Groups.groups_smaller(S, a <> (b <> tx)) == True{} : Bool}, ok)
                case Con{c, t2}:
                  match c:
                    case Groups.Group{+fc, +wc}:
                      match t2:
                        case Nil{}:
                          Empty.absurd({Groups.groups_smaller(S, a <> (b <> tx)) == Groups.groups_smaller(S, Groups.Group{fc, wc} <> Nil{}) : Bool}, ok)
                        case Con{d, ty}:
                          match d:
                            case Groups.Group{+fd, +wd}:
                              +ead = Arr.Arr.dpair_l({a == Groups.Group{fd, wd} : Groups.Group},
                                       Arr.Arr.DPair<{b == Groups.Group{fc, wc} : Groups.Group},
                                         {tx == ty : +List<Groups.Group>}>, ok)
                              +r1 = Arr.Arr.dpair_r({a == Groups.Group{fd, wd} : Groups.Group},
                                      Arr.Arr.DPair<{b == Groups.Group{fc, wc} : Groups.Group},
                                        {tx == ty : +List<Groups.Group>}>, ok)
                              +ebc = Arr.Arr.dpair_l({b == Groups.Group{fc, wc} : Groups.Group},
                                       {tx == ty : +List<Groups.Group>}, r1)
                              +et = Arr.Arr.dpair_r({b == Groups.Group{fc, wc} : Groups.Group},
                                      {tx == ty : +List<Groups.Group>}, r1)
                              %Equal.sym(Groups.Group, a, Groups.Group{fd, wd}, ead) : {Groups.groups_smaller(S, _ <> (b <> tx)) == Groups.groups_smaller(S, Groups.Group{fc, wc} <> (Groups.Group{fd, wd} <> ty)) : Bool}
                              %Equal.sym(Groups.Group, b, Groups.Group{fc, wc}, ebc) : {Groups.groups_smaller(S, Groups.Group{fd, wd} <> (_ <> tx)) == Groups.groups_smaller(S, Groups.Group{fc, wc} <> (Groups.Group{fd, wd} <> ty)) : Bool}
                              %Equal.sym(+List<Groups.Group>, tx, ty, et) : {Groups.groups_smaller(S, Groups.Group{fd, wd} <> (Groups.Group{fc, wc} <> _)) == Groups.groups_smaller(S, Groups.Group{fc, wc} <> (Groups.Group{fd, wd} <> ty)) : Bool}
                              FP.bool_and_swap(
                                Nat.is_lt(Groups.len_words(wd), Groups.len_words(S)),
                                Nat.is_lt(Groups.len_words(wc), Groups.len_words(S)),
                                Groups.groups_smaller(S, ty))
    case PTrans{+mid, p1, p2}:
      +ok1 = Arr.Arr.dpair_l(FP.PermOk(p1, xs, mid), FP.PermOk(p2, mid, ys), ok)
      +ok2 = Arr.Arr.dpair_r(FP.PermOk(p1, xs, mid), FP.PermOk(p2, mid, ys), ok)
      Equal.trans(Bool, Groups.groups_smaller(S, xs),
        Groups.groups_smaller(S, mid), Groups.groups_smaller(S, ys),
        FP.groups_smaller_perm(p1, S, xs, mid, ok1),
        FP.groups_smaller_perm(p2, S, mid, ys, ok2))

def FP.all_in_jobs_perm(p: FP.Perm, +G: +List<+List<Nat>>,
    +xs: +List<Groups.Group>, +ys: +List<Groups.Group>,
    +ok: FP.PermOk(p, xs, ys)) ->
  {FO.FO.all_in_jobs_b(MV.MV.next_groups(xs), G)
   == FO.FO.all_in_jobs_b(MV.MV.next_groups(ys), G) : Bool}:
  match p:
    case PRefl{}:
      Equal.cong(+List<Groups.Group>, Bool,
        gs => FO.FO.all_in_jobs_b(MV.MV.next_groups(gs), G), xs, ys, ok)
    case PSkip{pr}:
      match xs:
        case Nil{}:
          Empty.absurd({True{} == FO.FO.all_in_jobs_b(MV.MV.next_groups(ys), G) : Bool}, ok)
        case Con{hx, tx}:
          match ys:
            case Nil{}:
              Empty.absurd({FO.FO.all_in_jobs_b(MV.MV.next_groups(hx <> tx), G) == True{} : Bool}, ok)
            case Con{hy, ty}:
              match hy:
                case Groups.Group{+fy, +wy}:
                  +eh = Arr.Arr.dpair_l({hx == Groups.Group{fy, wy} : Groups.Group},
                          FP.PermOk(pr, tx, ty), ok)
                  +et = Arr.Arr.dpair_r({hx == Groups.Group{fy, wy} : Groups.Group},
                          FP.PermOk(pr, tx, ty), ok)
                  %Equal.sym(Groups.Group, hx, Groups.Group{fy, wy}, eh) : {FO.FO.all_in_jobs_b(MV.MV.next_groups(_ <> tx), G)
                         == FO.FO.all_in_jobs_b(MV.MV.next_groups(Groups.Group{fy, wy} <> ty), G) : Bool}
                  Equal.cong(Bool, Bool,
                    b => Bool.and(FO.FO.all_in_ref(wy, G), b),
                    FO.FO.all_in_jobs_b(MV.MV.next_groups(tx), G),
                    FO.FO.all_in_jobs_b(MV.MV.next_groups(ty), G),
                    FP.all_in_jobs_perm(pr, G, tx, ty, et))
    case PSwap{}:
      match xs:
        case Nil{}:
          Empty.absurd({True{} == FO.FO.all_in_jobs_b(MV.MV.next_groups(ys), G) : Bool}, ok)
        case Con{a, t1}:
          match t1:
            case Nil{}:
              Empty.absurd({FO.FO.all_in_jobs_b(MV.MV.next_groups(a <> Nil{}), G)
                            == FO.FO.all_in_jobs_b(MV.MV.next_groups(ys), G) : Bool}, ok)
            case Con{b, tx}:
              match ys:
                case Nil{}:
                  Empty.absurd({FO.FO.all_in_jobs_b(MV.MV.next_groups(a <> (b <> tx)), G) == True{} : Bool}, ok)
                case Con{c, t2}:
                  match c:
                    case Groups.Group{+fc, +wc}:
                      match t2:
                        case Nil{}:
                          Empty.absurd({FO.FO.all_in_jobs_b(MV.MV.next_groups(a <> (b <> tx)), G)
                                        == FO.FO.all_in_jobs_b(MV.MV.next_groups(Groups.Group{fc, wc} <> Nil{}), G) : Bool}, ok)
                        case Con{d, ty}:
                          match d:
                            case Groups.Group{+fd, +wd}:
                              +ead = Arr.Arr.dpair_l({a == Groups.Group{fd, wd} : Groups.Group},
                                       Arr.Arr.DPair<{b == Groups.Group{fc, wc} : Groups.Group},
                                         {tx == ty : +List<Groups.Group>}>, ok)
                              +r1 = Arr.Arr.dpair_r({a == Groups.Group{fd, wd} : Groups.Group},
                                      Arr.Arr.DPair<{b == Groups.Group{fc, wc} : Groups.Group},
                                        {tx == ty : +List<Groups.Group>}>, ok)
                              +ebc = Arr.Arr.dpair_l({b == Groups.Group{fc, wc} : Groups.Group},
                                       {tx == ty : +List<Groups.Group>}, r1)
                              +et = Arr.Arr.dpair_r({b == Groups.Group{fc, wc} : Groups.Group},
                                      {tx == ty : +List<Groups.Group>}, r1)
                              %Equal.sym(Groups.Group, a, Groups.Group{fd, wd}, ead) : {FO.FO.all_in_jobs_b(MV.MV.next_groups(_ <> (b <> tx)), G)
                                      == FO.FO.all_in_jobs_b(MV.MV.next_groups(Groups.Group{fc, wc} <> (Groups.Group{fd, wd} <> ty)), G) : Bool}
                              %Equal.sym(Groups.Group, b, Groups.Group{fc, wc}, ebc) : {FO.FO.all_in_jobs_b(MV.MV.next_groups(Groups.Group{fd, wd} <> (_ <> tx)), G)
                                      == FO.FO.all_in_jobs_b(MV.MV.next_groups(Groups.Group{fc, wc} <> (Groups.Group{fd, wd} <> ty)), G) : Bool}
                              %Equal.sym(+List<Groups.Group>, tx, ty, et) : {FO.FO.all_in_jobs_b(MV.MV.next_groups(Groups.Group{fd, wd} <> (Groups.Group{fc, wc} <> _)), G)
                                     == FO.FO.all_in_jobs_b(MV.MV.next_groups(Groups.Group{fc, wc} <> (Groups.Group{fd, wd} <> ty)), G) : Bool}
                              FP.bool_and_swap(FO.FO.all_in_ref(wd, G),
                                FO.FO.all_in_ref(wc, G),
                                FO.FO.all_in_jobs_b(MV.MV.next_groups(ty), G))
    case PTrans{+mid, p1, p2}:
      +ok1 = Arr.Arr.dpair_l(FP.PermOk(p1, xs, mid), FP.PermOk(p2, mid, ys), ok)
      +ok2 = Arr.Arr.dpair_r(FP.PermOk(p1, xs, mid), FP.PermOk(p2, mid, ys), ok)
      Equal.trans(Bool,
        FO.FO.all_in_jobs_b(MV.MV.next_groups(xs), G),
        FO.FO.all_in_jobs_b(MV.MV.next_groups(mid), G),
        FO.FO.all_in_jobs_b(MV.MV.next_groups(ys), G),
        FP.all_in_jobs_perm(p1, G, xs, mid, ok1),
        FP.all_in_jobs_perm(p2, G, mid, ys, ok2))

def FP.nodup_ok_jobs_perm(p: FP.Perm, +nodup: Bool,
    +xs: +List<Groups.Group>, +ys: +List<Groups.Group>,
    +ok: FP.PermOk(p, xs, ys)) ->
  {FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(xs))
   == FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(ys)) : Bool}:
  match p:
    case PRefl{}:
      Equal.cong(+List<Groups.Group>, Bool,
        gs => FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(gs)), xs, ys, ok)
    case PSkip{pr}:
      match xs:
        case Nil{}:
          Empty.absurd({True{} == FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(ys)) : Bool}, ok)
        case Con{hx, tx}:
          match ys:
            case Nil{}:
              Empty.absurd({FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(hx <> tx)) == True{} : Bool}, ok)
            case Con{hy, ty}:
              match hy:
                case Groups.Group{+fy, +wy}:
                  +eh = Arr.Arr.dpair_l({hx == Groups.Group{fy, wy} : Groups.Group},
                          FP.PermOk(pr, tx, ty), ok)
                  +et = Arr.Arr.dpair_r({hx == Groups.Group{fy, wy} : Groups.Group},
                          FP.PermOk(pr, tx, ty), ok)
                  %Equal.sym(Groups.Group, hx, Groups.Group{fy, wy}, eh) : {FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(_ <> tx))
                         == FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(Groups.Group{fy, wy} <> ty)) : Bool}
                  Equal.cong(Bool, Bool,
                    b => Bool.and(FN.FN.nodup_ok(nodup, wy), b),
                    FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(tx)),
                    FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(ty)),
                    FP.nodup_ok_jobs_perm(pr, nodup, tx, ty, et))
    case PSwap{}:
      match xs:
        case Nil{}:
          Empty.absurd({True{} == FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(ys)) : Bool}, ok)
        case Con{a, t1}:
          match t1:
            case Nil{}:
              Empty.absurd({FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(a <> Nil{}))
                            == FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(ys)) : Bool}, ok)
            case Con{b, tx}:
              match ys:
                case Nil{}:
                  Empty.absurd({FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(a <> (b <> tx))) == True{} : Bool}, ok)
                case Con{c, t2}:
                  match c:
                    case Groups.Group{+fc, +wc}:
                      match t2:
                        case Nil{}:
                          Empty.absurd({FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(a <> (b <> tx)))
                                        == FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(Groups.Group{fc, wc} <> Nil{})) : Bool}, ok)
                        case Con{d, ty}:
                          match d:
                            case Groups.Group{+fd, +wd}:
                              +ead = Arr.Arr.dpair_l({a == Groups.Group{fd, wd} : Groups.Group},
                                       Arr.Arr.DPair<{b == Groups.Group{fc, wc} : Groups.Group},
                                         {tx == ty : +List<Groups.Group>}>, ok)
                              +r1 = Arr.Arr.dpair_r({a == Groups.Group{fd, wd} : Groups.Group},
                                      Arr.Arr.DPair<{b == Groups.Group{fc, wc} : Groups.Group},
                                        {tx == ty : +List<Groups.Group>}>, ok)
                              +ebc = Arr.Arr.dpair_l({b == Groups.Group{fc, wc} : Groups.Group},
                                       {tx == ty : +List<Groups.Group>}, r1)
                              +et = Arr.Arr.dpair_r({b == Groups.Group{fc, wc} : Groups.Group},
                                      {tx == ty : +List<Groups.Group>}, r1)
                              %Equal.sym(Groups.Group, a, Groups.Group{fd, wd}, ead) : {FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(_ <> (b <> tx)))
                                      == FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(Groups.Group{fc, wc} <> (Groups.Group{fd, wd} <> ty))) : Bool}
                              %Equal.sym(Groups.Group, b, Groups.Group{fc, wc}, ebc) : {FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(Groups.Group{fd, wd} <> (_ <> tx)))
                                      == FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(Groups.Group{fc, wc} <> (Groups.Group{fd, wd} <> ty))) : Bool}
                              %Equal.sym(+List<Groups.Group>, tx, ty, et) : {FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(Groups.Group{fd, wd} <> (Groups.Group{fc, wc} <> _)))
                                     == FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(Groups.Group{fc, wc} <> (Groups.Group{fd, wd} <> ty))) : Bool}
                              FP.bool_and_swap(FN.FN.nodup_ok(nodup, wd),
                                FN.FN.nodup_ok(nodup, wc),
                                FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(ty)))
    case PTrans{+mid, p1, p2}:
      +ok1 = Arr.Arr.dpair_l(FP.PermOk(p1, xs, mid), FP.PermOk(p2, mid, ys), ok)
      +ok2 = Arr.Arr.dpair_r(FP.PermOk(p1, xs, mid), FP.PermOk(p2, mid, ys), ok)
      Equal.trans(Bool,
        FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(xs)),
        FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(mid)),
        FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(ys)),
        FP.nodup_ok_jobs_perm(p1, nodup, xs, mid, ok1),
        FP.nodup_ok_jobs_perm(p2, nodup, mid, ys, ok2))

# ---------------------------------------------------------------------------
# 3. `Eval.items` cost preservation under `FP.Perm` (via plain Nat sum when
#    finite, and trivial `<= inf` when saturated)
# ---------------------------------------------------------------------------

def FP.plain_ref_sum(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +groups: +List<Groups.Group>) -> Nat:
  match groups:
    case Nil{}:
      0n
    case Con{gp, rest}:
      match gp:
        case Groups.Group{fb, ws}:
          Nat.add(Sat.SB.child_cost(p, G, ws, inf),
            FP.plain_ref_sum(p, inf, G, rest))

def FP.plain_ref_sum_perm(perm: FP.Perm, +p: Nat, +inf: Nat,
    +G: +List<+List<Nat>>, +xs: +List<Groups.Group>, +ys: +List<Groups.Group>,
    +ok: FP.PermOk(perm, xs, ys)) ->
  {FP.plain_ref_sum(p, inf, G, xs) == FP.plain_ref_sum(p, inf, G, ys) : Nat}:
  match perm:
    case PRefl{}:
      Equal.cong(+List<Groups.Group>, Nat, gs => FP.plain_ref_sum(p, inf, G, gs),
        xs, ys, ok)
    case PSkip{pr}:
      match xs:
        case Nil{}:
          Empty.absurd({0n == FP.plain_ref_sum(p, inf, G, ys) : Nat}, ok)
        case Con{hx, tx}:
          match ys:
            case Nil{}:
              Empty.absurd({FP.plain_ref_sum(p, inf, G, hx <> tx) == 0n : Nat}, ok)
            case Con{hy, ty}:
              match hy:
                case Groups.Group{+fy, +wy}:
                  +eh = Arr.Arr.dpair_l({hx == Groups.Group{fy, wy} : Groups.Group},
                          FP.PermOk(pr, tx, ty), ok)
                  +et = Arr.Arr.dpair_r({hx == Groups.Group{fy, wy} : Groups.Group},
                          FP.PermOk(pr, tx, ty), ok)
                  %Equal.sym(Groups.Group, hx, Groups.Group{fy, wy}, eh) : {FP.plain_ref_sum(p, inf, G, _ <> tx)
                         == FP.plain_ref_sum(p, inf, G, Groups.Group{fy, wy} <> ty) : Nat}
                  Equal.cong(Nat, Nat,
                    z => Nat.add(Sat.SB.child_cost(p, G, wy, inf), z),
                    FP.plain_ref_sum(p, inf, G, tx),
                    FP.plain_ref_sum(p, inf, G, ty),
                    FP.plain_ref_sum_perm(pr, p, inf, G, tx, ty, et))
    case PSwap{}:
      match xs:
        case Nil{}:
          Empty.absurd({0n == FP.plain_ref_sum(p, inf, G, ys) : Nat}, ok)
        case Con{a, t1}:
          match t1:
            case Nil{}:
              Empty.absurd({FP.plain_ref_sum(p, inf, G, a <> Nil{}) == FP.plain_ref_sum(p, inf, G, ys) : Nat}, ok)
            case Con{b, tx}:
              match ys:
                case Nil{}:
                  Empty.absurd({FP.plain_ref_sum(p, inf, G, a <> (b <> tx)) == 0n : Nat}, ok)
                case Con{c, t2}:
                  match c:
                    case Groups.Group{+fc, +wc}:
                      match t2:
                        case Nil{}:
                          Empty.absurd({FP.plain_ref_sum(p, inf, G, a <> (b <> tx))
                                        == FP.plain_ref_sum(p, inf, G, Groups.Group{fc, wc} <> Nil{}) : Nat}, ok)
                        case Con{d, ty}:
                          match d:
                            case Groups.Group{+fd, +wd}:
                              +ead = Arr.Arr.dpair_l({a == Groups.Group{fd, wd} : Groups.Group},
                                       Arr.Arr.DPair<{b == Groups.Group{fc, wc} : Groups.Group},
                                         {tx == ty : +List<Groups.Group>}>, ok)
                              +r1 = Arr.Arr.dpair_r({a == Groups.Group{fd, wd} : Groups.Group},
                                      Arr.Arr.DPair<{b == Groups.Group{fc, wc} : Groups.Group},
                                        {tx == ty : +List<Groups.Group>}>, ok)
                              +ebc = Arr.Arr.dpair_l({b == Groups.Group{fc, wc} : Groups.Group},
                                       {tx == ty : +List<Groups.Group>}, r1)
                              +et = Arr.Arr.dpair_r({b == Groups.Group{fc, wc} : Groups.Group},
                                      {tx == ty : +List<Groups.Group>}, r1)
                              %Equal.sym(Groups.Group, a, Groups.Group{fd, wd}, ead) : {FP.plain_ref_sum(p, inf, G, _ <> (b <> tx))
                                      == FP.plain_ref_sum(p, inf, G, Groups.Group{fc, wc} <> (Groups.Group{fd, wd} <> ty)) : Nat}
                              %Equal.sym(Groups.Group, b, Groups.Group{fc, wc}, ebc) : {FP.plain_ref_sum(p, inf, G, Groups.Group{fd, wd} <> (_ <> tx))
                                      == FP.plain_ref_sum(p, inf, G, Groups.Group{fc, wc} <> (Groups.Group{fd, wd} <> ty)) : Nat}
                              %Equal.sym(+List<Groups.Group>, tx, ty, et) : {FP.plain_ref_sum(p, inf, G, Groups.Group{fd, wd} <> (Groups.Group{fc, wc} <> _))
                                     == FP.plain_ref_sum(p, inf, G, Groups.Group{fc, wc} <> (Groups.Group{fd, wd} <> ty)) : Nat}
                              FP.nat_add_swap(Sat.SB.child_cost(p, G, wd, inf),
                                Sat.SB.child_cost(p, G, wc, inf),
                                FP.plain_ref_sum(p, inf, G, ty))
    case PTrans{+mid, p1, p2}:
      +ok1 = Arr.Arr.dpair_l(FP.PermOk(p1, xs, mid), FP.PermOk(p2, mid, ys), ok)
      +ok2 = Arr.Arr.dpair_r(FP.PermOk(p1, xs, mid), FP.PermOk(p2, mid, ys), ok)
      Equal.trans(Nat, FP.plain_ref_sum(p, inf, G, xs),
        FP.plain_ref_sum(p, inf, G, mid), FP.plain_ref_sum(p, inf, G, ys),
        FP.plain_ref_sum_perm(p1, p, inf, G, xs, mid, ok1),
        FP.plain_ref_sum_perm(p2, p, inf, G, mid, ys, ok2))

def FP.ge_false_of_lt_go(a: Nat, b: Nat, c: Cmp,
    +ec: {c == Nat.cmp(a, b) : Cmp},
    +hlt: {Nat.is_lt(a, b) == True{} : Bool}) ->
  {Nat.is_ge(a, b) == False{} : Bool}:
  match c:
    case LT{}:
      %ec : {Cmp.is_ge(_) == False{} : Bool}
      {==}
    case EQ{}:
      +e2 : {Cmp.is_lt(EQ{}) == True{} : Bool} =
        Equal.trans(Bool, Cmp.is_lt(EQ{}), Cmp.is_lt(Nat.cmp(a, b)), True{},
          Equal.cong(Cmp, Bool, Cmp.is_lt, EQ{}, Nat.cmp(a, b), ec), hlt)
      Empty.absurd({Nat.is_ge(a, b) == False{} : Bool},
        Logic.Proof.false_ne_true(e2))
    case GT{}:
      +e2 : {Cmp.is_lt(GT{}) == True{} : Bool} =
        Equal.trans(Bool, Cmp.is_lt(GT{}), Cmp.is_lt(Nat.cmp(a, b)), True{},
          Equal.cong(Cmp, Bool, Cmp.is_lt, GT{}, Nat.cmp(a, b), ec), hlt)
      Empty.absurd({Nat.is_ge(a, b) == False{} : Bool},
        Logic.Proof.false_ne_true(e2))

def FP.ge_false_of_lt(+a: Nat, +b: Nat,
    +hlt: {Nat.is_lt(a, b) == True{} : Bool}) ->
  {Nat.is_ge(a, b) == False{} : Bool}:
  FP.ge_false_of_lt_go(a, b, Nat.cmp(a, b), {==}, hlt)

def FP.sat_add_eq_of_lt(+inf: Nat, +a: Nat, +b: Nat,
    +ha: {Nat.is_lt(a, inf) == True{} : Bool},
    +hb: {Nat.is_lt(b, inf) == True{} : Bool}) ->
  {SolveRef.sat_add(inf, a, b) == Nat.add(a, b) : Nat}:
  +ea : {Nat.is_ge(a, inf) == False{} : Bool} = FP.ge_false_of_lt(a, inf, ha)
  +eb : {Nat.is_ge(b, inf) == False{} : Bool} = FP.ge_false_of_lt(b, inf, hb)
  Equal.trans(Nat,
    SolveRef.sat_add(inf, a, b),
    Feedback.Bool.case(Nat, False{}, inf,
      Feedback.Bool.case(Nat, Nat.is_ge(b, inf), inf, Nat.add(a, b))),
    Nat.add(a, b),
    Equal.cong(Bool, Nat,
      x => Feedback.Bool.case(Nat, x, inf,
             Feedback.Bool.case(Nat, Nat.is_ge(b, inf), inf, Nat.add(a, b))),
      Nat.is_ge(a, inf), False{}, ea),
    Equal.cong(Bool, Nat,
      y => Feedback.Bool.case(Nat, y, inf, Nat.add(a, b)),
      Nat.is_ge(b, inf), False{}, eb))

def FP.lt_add_l(+a: Nat, +b: Nat, +c: Nat,
    +h: {Nat.is_lt(Nat.add(a, b), c) == True{} : Bool}) ->
  {Nat.is_lt(a, c) == True{} : Bool}:
  +hl0 : {Nat.is_le(Nat.add(a, 0n), Nat.add(a, b)) == True{} : Bool} =
    NatProof.Nat.is_le_add_l(0n, b, a, NatProof.Nat.is_le_zero_l(b))
  +hl : {Nat.is_le(a, Nat.add(a, b)) == True{} : Bool} =
    NatProof.Nat.is_le_eq_l(Nat.add(a, b), Nat.add(a, 0n), a,
      NatProof.NatPrf.add_zero(a), hl0)
  NatProof.Nat.is_le_lt_trans(a, Nat.add(a, b), c, hl, h)

def FP.lt_add_r(+a: Nat, +b: Nat, +c: Nat,
    +h: {Nat.is_lt(Nat.add(a, b), c) == True{} : Bool}) ->
  {Nat.is_lt(b, c) == True{} : Bool}:
  FP.lt_add_l(b, a, c,
    Equal.trans(Bool, Nat.is_lt(Nat.add(b, a), c), Nat.is_lt(Nat.add(a, b), c),
      True{},
      Equal.cong(Nat, Bool, x => Nat.is_lt(x, c), Nat.add(b, a), Nat.add(a, b),
        NatProof.NatPrf.add_comm(b, a)), h))

# When `ks_sum(Eval.items(..., groups, kids, sum, inf)) < inf`, it equals
# `sum + plain_ref_sum(groups)`.
def FP.items_sum_eq_plain_of_lt(+p: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +g: +List<Nat>, +groups: +List<Groups.Group>,
    +kids: +List<Tree.Child>, +sum: Nat, +inf: Nat,
    +hlt: {Nat.is_lt(Sat.SB.ks_sum(
             Eval.Eval.items(p, G, S, g, groups, kids, sum, inf)), inf)
           == True{} : Bool}) ->
  {Sat.SB.ks_sum(Eval.Eval.items(p, G, S, g, groups, kids, sum, inf))
   == Nat.add(sum, FP.plain_ref_sum(p, inf, G, groups)) : Nat}:
  match groups:
    case Nil{}:
      Equal.sym(Nat, Nat.add(sum, 0n), sum, NatProof.NatPrf.add_zero(sum))
    case Con{gp, rest}:
      match gp:
        case Groups.Group{+fb, +ws}:
          +pending : SolveRef.Best =
            SolveRef.step(p, SolveRef.mk_schedule(G, ws), G, ws, inf,
              Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero())
          +c : Nat = Eval.Eval.cost_of(pending)
          +kids2 : +List<Tree.Child> =
            Tree.Child{fb, Eval.Eval.tree_of(pending)} <> kids
          +sum2 : Nat = SolveRef.sat_add(inf, sum, c)
          +ewk : {Eval.Eval.with_kid(fb, kids, sum, inf, pending,
                    k2 => s2 => Eval.Eval.items(p, G, S, g, rest, k2, s2, inf))
                  == Eval.Eval.items(p, G, S, g, rest, kids2, sum2, inf)
                  : Eval.KS} =
            Eval.Eval.with_kid_eq(fb, kids, sum, inf, pending,
              k2 => s2 => Eval.Eval.items(p, G, S, g, rest, k2, s2, inf))
          +ek : {Sat.SB.ks_sum(Eval.Eval.items(p, G, S, g,
                   Groups.Group{fb, ws} <> rest, kids, sum, inf))
                 == Sat.SB.ks_sum(Eval.Eval.items(p, G, S, g, rest, kids2, sum2, inf))
                 : Nat} =
            Equal.cong(Eval.KS, Nat, ks => Sat.SB.ks_sum(ks),
              Eval.Eval.with_kid(fb, kids, sum, inf, pending,
                k2 => s2 => Eval.Eval.items(p, G, S, g, rest, k2, s2, inf)),
              Eval.Eval.items(p, G, S, g, rest, kids2, sum2, inf), ewk)
          +hlt2 : {Nat.is_lt(Sat.SB.ks_sum(
                     Eval.Eval.items(p, G, S, g, rest, kids2, sum2, inf)), inf)
                   == True{} : Bool} =
            Equal.trans(Bool,
              Nat.is_lt(Sat.SB.ks_sum(
                Eval.Eval.items(p, G, S, g, rest, kids2, sum2, inf)), inf),
              Nat.is_lt(Sat.SB.ks_sum(
                Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> rest,
                  kids, sum, inf)), inf),
              True{},
              Equal.cong(Nat, Bool, x => Nat.is_lt(x, inf),
                Sat.SB.ks_sum(Eval.Eval.items(p, G, S, g, rest, kids2, sum2, inf)),
                Sat.SB.ks_sum(Eval.Eval.items(p, G, S, g,
                  Groups.Group{fb, ws} <> rest, kids, sum, inf)),
                Equal.sym(Nat,
                  Sat.SB.ks_sum(Eval.Eval.items(p, G, S, g,
                    Groups.Group{fb, ws} <> rest, kids, sum, inf)),
                  Sat.SB.ks_sum(Eval.Eval.items(p, G, S, g, rest, kids2, sum2, inf)),
                  ek)),
              hlt)
          +ih : {Sat.SB.ks_sum(Eval.Eval.items(p, G, S, g, rest, kids2, sum2, inf))
                 == Nat.add(sum2, FP.plain_ref_sum(p, inf, G, rest)) : Nat} =
            FP.items_sum_eq_plain_of_lt(p, G, S, g, rest, kids2, sum2, inf, hlt2)
          +hs2_lt : {Nat.is_lt(sum2, inf) == True{} : Bool} =
            FP.lt_add_l(sum2, FP.plain_ref_sum(p, inf, G, rest), inf,
              Equal.trans(Bool,
                Nat.is_lt(Nat.add(sum2, FP.plain_ref_sum(p, inf, G, rest)), inf),
                Nat.is_lt(Sat.SB.ks_sum(
                  Eval.Eval.items(p, G, S, g, rest, kids2, sum2, inf)), inf),
                True{},
                Equal.cong(Nat, Bool, x => Nat.is_lt(x, inf),
                  Nat.add(sum2, FP.plain_ref_sum(p, inf, G, rest)),
                  Sat.SB.ks_sum(Eval.Eval.items(p, G, S, g, rest, kids2, sum2, inf)),
                  Equal.sym(Nat,
                    Sat.SB.ks_sum(Eval.Eval.items(p, G, S, g, rest, kids2, sum2, inf)),
                    Nat.add(sum2, FP.plain_ref_sum(p, inf, G, rest)), ih)),
                hlt2))
          +esum2 : {sum2 == Nat.add(sum, c) : Nat} =
            FP.sat_add_eq_of_lt(inf, sum, c,
              Sat.SB.sat_add_lt_l(inf, sum, c, hs2_lt),
              Sat.SB.sat_add_lt_r(inf, sum, c, hs2_lt))
          Equal.trans(Nat,
            Sat.SB.ks_sum(Eval.Eval.items(p, G, S, g,
              Groups.Group{fb, ws} <> rest, kids, sum, inf)),
            Sat.SB.ks_sum(Eval.Eval.items(p, G, S, g, rest, kids2, sum2, inf)),
            Nat.add(sum, Nat.add(c, FP.plain_ref_sum(p, inf, G, rest))),
            ek,
            Equal.trans(Nat,
              Sat.SB.ks_sum(Eval.Eval.items(p, G, S, g, rest, kids2, sum2, inf)),
              Nat.add(sum2, FP.plain_ref_sum(p, inf, G, rest)),
              Nat.add(sum, Nat.add(c, FP.plain_ref_sum(p, inf, G, rest))),
              ih,
              Equal.trans(Nat,
                Nat.add(sum2, FP.plain_ref_sum(p, inf, G, rest)),
                Nat.add(Nat.add(sum, c), FP.plain_ref_sum(p, inf, G, rest)),
                Nat.add(sum, Nat.add(c, FP.plain_ref_sum(p, inf, G, rest))),
                Equal.cong(Nat, Nat,
                  x => Nat.add(x, FP.plain_ref_sum(p, inf, G, rest)),
                  sum2, Nat.add(sum, c), esum2),
                NatProof.NatPrf.add_assoc(sum, c,
                  FP.plain_ref_sum(p, inf, G, rest)))))

# Conversely, if `sum + plain_ref_sum(groups) < inf`, then `Eval.items` stays
# finite and equals `sum + plain_ref_sum(groups)`.
def FP.items_sum_of_plain_lt(+p: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +g: +List<Nat>, +groups: +List<Groups.Group>,
    +kids: +List<Tree.Child>, +sum: Nat, +inf: Nat,
    +hlt: {Nat.is_lt(Nat.add(sum, FP.plain_ref_sum(p, inf, G, groups)), inf)
           == True{} : Bool}) ->
  {Sat.SB.ks_sum(Eval.Eval.items(p, G, S, g, groups, kids, sum, inf))
   == Nat.add(sum, FP.plain_ref_sum(p, inf, G, groups)) : Nat}:
  match groups:
    case Nil{}:
      Equal.sym(Nat, Nat.add(sum, 0n), sum, NatProof.NatPrf.add_zero(sum))
    case Con{gp, rest}:
      match gp:
        case Groups.Group{+fb, +ws}:
          +pending : SolveRef.Best =
            SolveRef.step(p, SolveRef.mk_schedule(G, ws), G, ws, inf,
              Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero())
          +c : Nat = Eval.Eval.cost_of(pending)
          +pr : Nat = FP.plain_ref_sum(p, inf, G, rest)
          +kids2 : +List<Tree.Child> =
            Tree.Child{fb, Eval.Eval.tree_of(pending)} <> kids
          +sum2 : Nat = SolveRef.sat_add(inf, sum, c)
          +hlt_assoc : {Nat.is_lt(Nat.add(Nat.add(sum, c), pr), inf)
                        == True{} : Bool} =
            Equal.trans(Bool,
              Nat.is_lt(Nat.add(Nat.add(sum, c), pr), inf),
              Nat.is_lt(Nat.add(sum, Nat.add(c, pr)), inf),
              True{},
              Equal.cong(Nat, Bool, x => Nat.is_lt(x, inf),
                Nat.add(Nat.add(sum, c), pr), Nat.add(sum, Nat.add(c, pr)),
                NatProof.NatPrf.add_assoc(sum, c, pr)),
              hlt)
          +hsum_lt : {Nat.is_lt(sum, inf) == True{} : Bool} =
            FP.lt_add_l(sum, Nat.add(c, pr), inf, hlt)
          +hc_lt : {Nat.is_lt(c, inf) == True{} : Bool} =
            FP.lt_add_l(c, pr, inf, FP.lt_add_r(sum, Nat.add(c, pr), inf, hlt))
          +esum2 : {sum2 == Nat.add(sum, c) : Nat} =
            FP.sat_add_eq_of_lt(inf, sum, c, hsum_lt, hc_lt)
          +hlt2 : {Nat.is_lt(Nat.add(sum2, pr), inf) == True{} : Bool} =
            Equal.trans(Bool,
              Nat.is_lt(Nat.add(sum2, pr), inf),
              Nat.is_lt(Nat.add(Nat.add(sum, c), pr), inf),
              True{},
              Equal.cong(Nat, Bool, x => Nat.is_lt(Nat.add(x, pr), inf),
                sum2, Nat.add(sum, c), esum2),
              hlt_assoc)
          +ewk : {Eval.Eval.with_kid(fb, kids, sum, inf, pending,
                    k2 => s2 => Eval.Eval.items(p, G, S, g, rest, k2, s2, inf))
                  == Eval.Eval.items(p, G, S, g, rest, kids2, sum2, inf)
                  : Eval.KS} =
            Eval.Eval.with_kid_eq(fb, kids, sum, inf, pending,
              k2 => s2 => Eval.Eval.items(p, G, S, g, rest, k2, s2, inf))
          +ek : {Sat.SB.ks_sum(Eval.Eval.items(p, G, S, g,
                   Groups.Group{fb, ws} <> rest, kids, sum, inf))
                 == Sat.SB.ks_sum(Eval.Eval.items(p, G, S, g, rest, kids2, sum2, inf))
                 : Nat} =
            Equal.cong(Eval.KS, Nat, ks => Sat.SB.ks_sum(ks),
              Eval.Eval.with_kid(fb, kids, sum, inf, pending,
                k2 => s2 => Eval.Eval.items(p, G, S, g, rest, k2, s2, inf)),
              Eval.Eval.items(p, G, S, g, rest, kids2, sum2, inf), ewk)
          Equal.trans(Nat,
            Sat.SB.ks_sum(Eval.Eval.items(p, G, S, g,
              Groups.Group{fb, ws} <> rest, kids, sum, inf)),
            Sat.SB.ks_sum(Eval.Eval.items(p, G, S, g, rest, kids2, sum2, inf)),
            Nat.add(sum, Nat.add(c, pr)),
            ek,
            Equal.trans(Nat,
              Sat.SB.ks_sum(Eval.Eval.items(p, G, S, g, rest, kids2, sum2, inf)),
              Nat.add(sum2, pr),
              Nat.add(sum, Nat.add(c, pr)),
              FP.items_sum_of_plain_lt(p, G, S, g, rest, kids2, sum2, inf, hlt2),
              Equal.trans(Nat, Nat.add(sum2, pr), Nat.add(Nat.add(sum, c), pr),
                Nat.add(sum, Nat.add(c, pr)),
                Equal.cong(Nat, Nat, x => Nat.add(x, pr), sum2,
                  Nat.add(sum, c), esum2),
                NatProof.NatPrf.add_assoc(sum, c, pr))))

def FP.ks_cost_eq_sat(+inf: Nat, +S: +List<+List<Nat>>, ks: Eval.KS) ->
  {Fold.OQ.ks_cost(inf, S, ks)
   == SolveRef.sat_add(inf, Groups.len_words(S), Sat.SB.ks_sum(ks)) : Nat}:
  match ks:
    case Eval.KS{kids, sum}:
      {==}

def FP.ks_cost_le_of_perm_go(perm: FP.Perm, +p: Nat, +inf: Nat,
    +G: +List<+List<Nat>>, +S: +List<+List<Nat>>, +g: +List<Nat>,
    +xs: +List<Groups.Group>, +ys: +List<Groups.Group>, +cost: Nat,
    +ok: FP.PermOk(perm, xs, ys),
    +hc_inf: {Nat.is_le(cost, inf) == True{} : Bool},
    +hle_ys: {Nat.is_le(cost, Fold.OQ.ks_cost(inf, S,
                Eval.Eval.items(p, G, S, g, ys, Nil{}, 0n, inf)))
              == True{} : Bool},
    fin: Bool,
    +efin: {fin == Nat.is_lt(Fold.OQ.ks_cost(inf, S,
                     Eval.Eval.items(p, G, S, g, xs, Nil{}, 0n, inf)), inf)
            : Bool}) ->
  {Nat.is_le(cost, Fold.OQ.ks_cost(inf, S,
     Eval.Eval.items(p, G, S, g, xs, Nil{}, 0n, inf))) == True{} : Bool}:
  match fin:
    case False{}:
      +hge : {Nat.is_le(inf, Fold.OQ.ks_cost(inf, S,
                Eval.Eval.items(p, G, S, g, xs, Nil{}, 0n, inf)))
              == True{} : Bool} =
        FC.FC.le_of_lt_false(
          Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g, xs, Nil{}, 0n, inf)),
          inf,
          Equal.sym(Bool, False{},
            Nat.is_lt(Fold.OQ.ks_cost(inf, S,
              Eval.Eval.items(p, G, S, g, xs, Nil{}, 0n, inf)), inf),
            efin))
      NatProof.Nat.is_le_trans(cost, inf,
        Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g, xs, Nil{}, 0n, inf)),
        hc_inf, hge)
    case True{}:
      +ksx : Eval.KS = Eval.Eval.items(p, G, S, g, xs, Nil{}, 0n, inf)
      +ksy : Eval.KS = Eval.Eval.items(p, G, S, g, ys, Nil{}, 0n, inf)
      +hlt_cx : {Nat.is_lt(Fold.OQ.ks_cost(inf, S, ksx), inf) == True{} : Bool} =
        Equal.sym(Bool, True{}, Nat.is_lt(Fold.OQ.ks_cost(inf, S, ksx), inf), efin)
      +hlt_sat : {Nat.is_lt(SolveRef.sat_add(inf, Groups.len_words(S),
                    Sat.SB.ks_sum(ksx)), inf) == True{} : Bool} =
        Equal.trans(Bool,
          Nat.is_lt(SolveRef.sat_add(inf, Groups.len_words(S), Sat.SB.ks_sum(ksx)), inf),
          Nat.is_lt(Fold.OQ.ks_cost(inf, S, ksx), inf),
          True{},
          Equal.cong(Nat, Bool, x => Nat.is_lt(x, inf),
            SolveRef.sat_add(inf, Groups.len_words(S), Sat.SB.ks_sum(ksx)),
            Fold.OQ.ks_cost(inf, S, ksx),
            Equal.sym(Nat, Fold.OQ.ks_cost(inf, S, ksx),
              SolveRef.sat_add(inf, Groups.len_words(S), Sat.SB.ks_sum(ksx)),
              FP.ks_cost_eq_sat(inf, S, ksx))),
          hlt_cx)
      +hlt_sx : {Nat.is_lt(Sat.SB.ks_sum(ksx), inf) == True{} : Bool} =
        Sat.SB.sat_add_lt_r(inf, Groups.len_words(S), Sat.SB.ks_sum(ksx), hlt_sat)
      +esx : {Sat.SB.ks_sum(ksx) == FP.plain_ref_sum(p, inf, G, xs) : Nat} =
        FP.items_sum_eq_plain_of_lt(p, G, S, g, xs, Nil{}, 0n, inf, hlt_sx)
      +ep : {FP.plain_ref_sum(p, inf, G, xs) == FP.plain_ref_sum(p, inf, G, ys)
             : Nat} =
        FP.plain_ref_sum_perm(perm, p, inf, G, xs, ys, ok)
      +hlt_py : {Nat.is_lt(FP.plain_ref_sum(p, inf, G, ys), inf)
                 == True{} : Bool} =
        Equal.trans(Bool,
          Nat.is_lt(FP.plain_ref_sum(p, inf, G, ys), inf),
          Nat.is_lt(Sat.SB.ks_sum(ksx), inf),
          True{},
          Equal.cong(Nat, Bool, x => Nat.is_lt(x, inf),
            FP.plain_ref_sum(p, inf, G, ys), Sat.SB.ks_sum(ksx),
            Equal.sym(Nat, Sat.SB.ks_sum(ksx), FP.plain_ref_sum(p, inf, G, ys),
              Equal.trans(Nat, Sat.SB.ks_sum(ksx),
                FP.plain_ref_sum(p, inf, G, xs),
                FP.plain_ref_sum(p, inf, G, ys), esx, ep))),
          hlt_sx)
      +esy : {Sat.SB.ks_sum(ksy) == FP.plain_ref_sum(p, inf, G, ys) : Nat} =
        FP.items_sum_of_plain_lt(p, G, S, g, ys, Nil{}, 0n, inf, hlt_py)
      +esum_eq : {Sat.SB.ks_sum(ksy) == Sat.SB.ks_sum(ksx) : Nat} =
        Equal.trans(Nat, Sat.SB.ks_sum(ksy), FP.plain_ref_sum(p, inf, G, ys),
          Sat.SB.ks_sum(ksx), esy,
          Equal.sym(Nat, Sat.SB.ks_sum(ksx), FP.plain_ref_sum(p, inf, G, ys),
            Equal.trans(Nat, Sat.SB.ks_sum(ksx),
              FP.plain_ref_sum(p, inf, G, xs),
              FP.plain_ref_sum(p, inf, G, ys), esx, ep)))
      +ecost_eq : {Fold.OQ.ks_cost(inf, S, ksy) == Fold.OQ.ks_cost(inf, S, ksx)
                   : Nat} =
        Equal.trans(Nat,
          Fold.OQ.ks_cost(inf, S, ksy),
          SolveRef.sat_add(inf, Groups.len_words(S), Sat.SB.ks_sum(ksy)),
          Fold.OQ.ks_cost(inf, S, ksx),
          FP.ks_cost_eq_sat(inf, S, ksy),
          Equal.trans(Nat,
            SolveRef.sat_add(inf, Groups.len_words(S), Sat.SB.ks_sum(ksy)),
            SolveRef.sat_add(inf, Groups.len_words(S), Sat.SB.ks_sum(ksx)),
            Fold.OQ.ks_cost(inf, S, ksx),
            Equal.cong(Nat, Nat,
              x => SolveRef.sat_add(inf, Groups.len_words(S), x),
              Sat.SB.ks_sum(ksy), Sat.SB.ks_sum(ksx), esum_eq),
            Equal.sym(Nat, Fold.OQ.ks_cost(inf, S, ksx),
              SolveRef.sat_add(inf, Groups.len_words(S), Sat.SB.ks_sum(ksx)),
              FP.ks_cost_eq_sat(inf, S, ksx))))
      Fold.OQ.le_cong_r(cost, Fold.OQ.ks_cost(inf, S, ksy),
        Fold.OQ.ks_cost(inf, S, ksx), ecost_eq, hle_ys)

def FP.bounds_skip_go(+fuel: Nat, +fx: +List<Feedback.Color>, +wx: +List<+List<Nat>>,
    +tx: +List<Groups.Group>, +ty: +List<Groups.Group>,
    bnd: MV.MV.Bounds(fuel, MV.MV.next_groups(Groups.Group{fx, wx} <> tx)),
    rec: MV.MV.Bounds(fuel, MV.MV.next_groups(tx)) ->
         MV.MV.Bounds(fuel, MV.MV.next_groups(ty))) ->
  MV.MV.Bounds(fuel, MV.MV.next_groups(Groups.Group{fx, wx} <> ty)):
  (h1, bt) = bnd
  (h1, rec(bt))

def FP.bounds_swap_go(+fuel: Nat, +fa: +List<Feedback.Color>, +wa: +List<+List<Nat>>,
    +fb2: +List<Feedback.Color>, +wb: +List<+List<Nat>>,
    +tx: +List<Groups.Group>,
    bnd: MV.MV.Bounds(fuel, MV.MV.next_groups(Groups.Group{fa, wa} <> (Groups.Group{fb2, wb} <> tx)))) ->
  MV.MV.Bounds(fuel, MV.MV.next_groups(Groups.Group{fb2, wb} <> (Groups.Group{fa, wa} <> tx))):
  (ha, r2) = bnd
  (hb, bt) = r2
  (hb, (ha, bt))

def FP.bounds_perm(p: FP.Perm, +fuel: Nat, +xs: +List<Groups.Group>,
    +ys: +List<Groups.Group>, +ok: FP.PermOk(p, xs, ys),
    bnd: MV.MV.Bounds(fuel, MV.MV.next_groups(xs))) ->
  MV.MV.Bounds(fuel, MV.MV.next_groups(ys)):
  match p:
    case PRefl{}:
      %ok :
        MV.MV.Bounds(fuel, MV.MV.next_groups(_))
      bnd
    case PSkip{pr}:
      match xs:
        case Nil{}:
          Empty.absurd(MV.MV.Bounds(fuel, MV.MV.next_groups(ys)), ok)
        case Con{hx, tx}:
          match hx:
            case Groups.Group{+fx, +wx}:
              match ys:
                case Nil{}:
                  Empty.absurd(MV.MV.Bounds(fuel, Nil{}), ok)
                case Con{hy, ty}:
                  +eh = Arr.Arr.dpair_l({Groups.Group{fx, wx} == hy : Groups.Group},
                          FP.PermOk(pr, tx, ty), ok)
                  +et = Arr.Arr.dpair_r({Groups.Group{fx, wx} == hy : Groups.Group},
                          FP.PermOk(pr, tx, ty), ok)
                  %eh :
                    MV.MV.Bounds(fuel, MV.MV.next_groups(_ <> ty))
                  FP.bounds_skip_go(fuel, fx, wx, tx, ty, bnd,
                    bt => FP.bounds_perm(pr, fuel, tx, ty, et, bt))
    case PSwap{}:
      match xs:
        case Nil{}:
          Empty.absurd(MV.MV.Bounds(fuel, MV.MV.next_groups(ys)), ok)
        case Con{a, t1}:
          match a:
            case Groups.Group{+fa, +wa}:
              match t1:
                case Nil{}:
                  Empty.absurd(MV.MV.Bounds(fuel, MV.MV.next_groups(ys)), ok)
                case Con{b, tx}:
                  match b:
                    case Groups.Group{+fb2, +wb}:
                      match ys:
                        case Nil{}:
                          Empty.absurd(MV.MV.Bounds(fuel, Nil{}), ok)
                        case Con{c, t2}:
                          match t2:
                            case Nil{}:
                              Empty.absurd(MV.MV.Bounds(fuel, MV.MV.next_groups(c <> Nil{})), ok)
                            case Con{d, ty}:
                              +ead = Arr.Arr.dpair_l({Groups.Group{fa, wa} == d : Groups.Group},
                                       Arr.Arr.DPair<{Groups.Group{fb2, wb} == c : Groups.Group},
                                         {tx == ty : +List<Groups.Group>}>, ok)
                              +r1 = Arr.Arr.dpair_r({Groups.Group{fa, wa} == d : Groups.Group},
                                      Arr.Arr.DPair<{Groups.Group{fb2, wb} == c : Groups.Group},
                                        {tx == ty : +List<Groups.Group>}>, ok)
                              +ebc = Arr.Arr.dpair_l({Groups.Group{fb2, wb} == c : Groups.Group},
                                       {tx == ty : +List<Groups.Group>}, r1)
                              +et = Arr.Arr.dpair_r({Groups.Group{fb2, wb} == c : Groups.Group},
                                      {tx == ty : +List<Groups.Group>}, r1)
                              %ead :
                                MV.MV.Bounds(fuel, MV.MV.next_groups(c <> (_ <> ty)))
                              %ebc :
                                MV.MV.Bounds(fuel, MV.MV.next_groups(_ <> (Groups.Group{fa, wa} <> ty)))
                              %et :
                                MV.MV.Bounds(fuel, MV.MV.next_groups(Groups.Group{fb2, wb} <> (Groups.Group{fa, wa} <> _)))
                              FP.bounds_swap_go(fuel, fa, wa, fb2, wb, tx, bnd)
    case PTrans{+mid, p1, p2}:
      +ok1 = Arr.Arr.dpair_l(FP.PermOk(p1, xs, mid), FP.PermOk(p2, mid, ys), ok)
      +ok2 = Arr.Arr.dpair_r(FP.PermOk(p1, xs, mid), FP.PermOk(p2, mid, ys), ok)
      FP.bounds_perm(p2, fuel, mid, ys, ok2,
        FP.bounds_perm(p1, fuel, xs, mid, ok1, bnd))

def FP.ks_cost_le_of_perm(perm: FP.Perm, +p: Nat, +inf: Nat,
    +G: +List<+List<Nat>>, +S: +List<+List<Nat>>, +g: +List<Nat>,
    +xs: +List<Groups.Group>, +ys: +List<Groups.Group>, +cost: Nat,
    +ok: FP.PermOk(perm, xs, ys),
    +hc_inf: {Nat.is_le(cost, inf) == True{} : Bool},
    +hle_ys: {Nat.is_le(cost, Fold.OQ.ks_cost(inf, S,
                Eval.Eval.items(p, G, S, g, ys, Nil{}, 0n, inf)))
              == True{} : Bool}) ->
  {Nat.is_le(cost, Fold.OQ.ks_cost(inf, S,
     Eval.Eval.items(p, G, S, g, xs, Nil{}, 0n, inf))) == True{} : Bool}:
  FP.ks_cost_le_of_perm_go(perm, p, inf, G, S, g, xs, ys, cost, ok, hc_inf,
    hle_ys,
    Nat.is_lt(Fold.OQ.ks_cost(inf, S,
      Eval.Eval.items(p, G, S, g, xs, Nil{}, 0n, inf)), inf), {==})
