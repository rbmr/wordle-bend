# Ports of the Rust heuristic bounds (src/heuristic.rs). Nat arithmetic
# throughout; these values are small and exact. Decision Bools are passed as
# parameters (Bend cannot match a computed value); every loop carries a fuel.
import Base

def nat_min(+a: Nat, +b: Nat) -> Nat:
  Nat.sub(a, Nat.sub(a, b))

# --- all_candidates_fill: depth d holds roots*(k-1)^(d-1) -------------------

def all_fill_go(+fuel: Nat, +rem: Nat, +depth: Nat, +cap: Nat, +cost: Nat,
                +k: Nat, le: Bool) -> Nat:
  match fuel:
    case 0n:
      cost
    case 1n+f:
      match le:
        case True{}:
          Nat.add(cost, Nat.mul(rem, depth))
        case False{}:
          +rem2 = Nat.sub(rem, cap)
          +cap2 = Nat.mul(cap, Nat.sub(k, 1n))
          all_fill_go(f, rem2, Nat.add(depth, 1n), cap2,
                      Nat.add(cost, Nat.mul(cap, depth)), k,
                      Nat.is_le(rem2, cap2))

def all_candidates_fill(+m: Nat, +roots: Nat, +k: Nat) -> Nat:
  all_fill_go(32n, m, 1n, roots, 0n, k, Nat.is_le(m, roots))

# --- forest_g: g(a1); once reach >= m every later term is 0 ----------------

def forest_g_go(+fuel: Nat, +m: Nat, +roots: Nat, +k: Nat, +a1: Nat,
                +pow: Nat, +cost: Nat, done: Bool) -> Nat:
  match fuel:
    case 0n:
      cost
    case 1n+f:
      match done:
        case True{}:
          cost
        case False{}:
          +cap = Nat.mul(roots, Nat.mul(pow, k))
          +used = Nat.mul(Nat.sub(pow, 1n), a1)
          +reach = Nat.sub(cap, used)
          +pow2 = Nat.mul(pow, k)
          +cap2 = Nat.mul(roots, Nat.mul(pow2, k))
          +used2 = Nat.mul(Nat.sub(pow2, 1n), a1)
          forest_g_go(f, m, roots, k, a1, pow2,
                      Nat.add(cost, Nat.sub(m, reach)),
                      Nat.is_le(m, Nat.sub(cap2, used2)))

def forest_g(+m: Nat, +roots: Nat, +k: Nat, +a1: Nat) -> Nat:
  +cap = Nat.mul(roots, k)
  forest_g_go(24n, m, roots, k, a1, 1n, Nat.add(m, Nat.sub(m, a1)),
              Nat.is_le(m, cap))

# --- forest_bound -----------------------------------------------------------

def forest_kinks(+fuel: Nat, +m: Nat, +roots: Nat, +k: Nat, +hi: Nat,
                 +pow: Nat, +best: Nat, done: Bool, cap_ge: Bool,
                 kink_le_hi: Bool, +kink: Nat) -> Nat:
  match fuel:
    case 0n:
      best
    case 1n+f:
      match done:
        case True{}:
          best
        case False{}:
          match cap_ge:
            case True{}:
              +pow2 = Nat.mul(pow, k)
              +coeff2 = Nat.sub(pow2, 1n)
              +cap2 = Nat.mul(roots, Nat.mul(pow2, k))
              +kink2 = Nat.div(Nat.sub(cap2, m), coeff2)
              forest_kinks(f, m, roots, k, hi, pow2, best,
                Nat.is_le(m, Nat.sub(cap2, Nat.mul(coeff2, hi))),
                Nat.is_le(cap2, m), Nat.is_le(Nat.add(kink2, 1n), hi), kink2)
            case False{}:
              match kink_le_hi:
                case True{}:
                  +b2 = nat_min(
                    nat_min(best, forest_g(m, roots, k, kink)),
                    forest_g(m, roots, k, Nat.add(kink, 1n)))
                  +pow2 = Nat.mul(pow, k)
                  +coeff2 = Nat.sub(pow2, 1n)
                  +cap2 = Nat.mul(roots, Nat.mul(pow2, k))
                  +kink2 = Nat.div(Nat.sub(cap2, m), coeff2)
                  forest_kinks(f, m, roots, k, hi, pow2, b2,
                    Nat.is_le(m, Nat.sub(cap2, Nat.mul(coeff2, hi))),
                    Nat.is_le(cap2, m), Nat.is_le(Nat.add(kink2, 1n), hi),
                    kink2)
                case False{}:
                  +b1 = nat_min(best, forest_g(m, roots, k, kink))
                  +pow2 = Nat.mul(pow, k)
                  +coeff2 = Nat.sub(pow2, 1n)
                  +cap2 = Nat.mul(roots, Nat.mul(pow2, k))
                  +kink2 = Nat.div(Nat.sub(cap2, m), coeff2)
                  forest_kinks(f, m, roots, k, hi, pow2, b1,
                    Nat.is_le(m, Nat.sub(cap2, Nat.mul(coeff2, hi))),
                    Nat.is_le(cap2, m), Nat.is_le(Nat.add(kink2, 1n), hi),
                    kink2)

def forest_bound_b(+m: Nat, +roots: Nat, +k: Nat,
                   mle_roots: Bool, mle_thresh: Bool) -> Nat:
  match mle_roots:
    case True{}:
      m
    case False{}:
      match mle_thresh:
        case True{}:
          all_candidates_fill(m, roots, k)
        case False{}:
          +hi = nat_min(roots, m)
          +b0 = forest_g(m, roots, k, 0n)
          +bh = forest_g(m, roots, k, hi)
          +best = nat_min(b0, bh)
          +cap = Nat.mul(roots, k)
          +coeff = Nat.sub(k, 1n)
          +kink = Nat.div(Nat.sub(cap, m), coeff)
          forest_kinks(24n, m, roots, k, hi, k, best,
            Nat.is_le(m, Nat.sub(cap, Nat.mul(coeff, hi))),
            Nat.is_le(cap, m), False{}, kink)

def forest_bound(+m: Nat, +roots: Nat, +k: Nat) -> Nat:
  match m:
    case 0n:
      0n
    case 1n+mp:
      match roots:
        case 0n:
          1000000000n
        case 1n+rp:
          +thresh = Nat.add(
            Nat.mul(roots, Nat.add(Nat.sub(Nat.mul(k, k), k), 1n)), 1n)
          forest_bound_b(m, roots, k, Nat.is_le(m, roots),
                         Nat.is_le(m, thresh))

# --- public bounds ----------------------------------------------------------

def capacity_bound(+n: Nat, +k: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n:
      1n
    case 2n:
      3n
    case 1n+np:
      match k:
        case 0n:
          0n
        case 1n:
          0n
        case 1n+kp:
          forest_bound(n, 1n, k)

def phase2_tail(+n: Nat, +root_k: Nat, +max_k: Nat, le: Bool) -> Nat:
  match le:
    case True{}:
      Nat.sub(Nat.mul(3n, n), nat_min(root_k, n))
    case False{}:
      Nat.add(n, forest_bound(n, root_k, max_k))

def phase2_capacity_bound(+n: Nat, +root_k: Nat, +max_k: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+np:
      match root_k:
        case 0n:
          capacity_bound(n, max_k)
        case 1n:
          capacity_bound(n, max_k)
        case 1n+rp:
          match max_k:
            case 0n:
              capacity_bound(n, max_k)
            case 1n:
              capacity_bound(n, max_k)
            case 1n+mk:
              phase2_tail(n, root_k, max_k, Nat.is_le(n, max_k))

def tight_tail(+n: Nat, +root_k: Nat, +max_k: Nat, le: Bool) -> Nat:
  match le:
    case True{}:
      Nat.sub(Nat.sub(Nat.mul(3n, n), 1n), nat_min(root_k, n))
    case False{}:
      Nat.add(n, forest_bound(Nat.sub(n, 1n), Nat.sub(root_k, 1n), max_k))

def tight_capacity_bound(+n: Nat, +root_k: Nat, +max_k: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n:
      1n
    case 2n:
      3n
    case 1n+np:
      match root_k:
        case 0n:
          capacity_bound(n, max_k)
        case 1n:
          capacity_bound(n, max_k)
        case 1n+rp:
          match max_k:
            case 0n:
              capacity_bound(n, max_k)
            case 1n:
              capacity_bound(n, max_k)
            case 1n+mk:
              tight_tail(n, root_k, max_k, Nat.is_le(n, max_k))

def bucket_capacity_bound(+n: Nat, +root_k: Nat, +max_k: Nat) -> Nat:
  nat_min(tight_capacity_bound(n, root_k, max_k),
          phase2_capacity_bound(n, root_k, max_k))
