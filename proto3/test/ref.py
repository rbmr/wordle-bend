# Reference model of the Rust search core, single thread, generic 5-letter path.
#
# Written from ~/projects/wordle-opt/src/{solver,heuristic,cache}.rs with the
# unrolled specialisations replaced by their generic bodies, and validated
# against the Rust binary's counters at N=100/300/500 (see NOTES.md).
#
# Usage: python3 ref.py <candidates.txt> <guesses.txt> [--n N]
import sys

WIN = 121  # 1+3+9+27+81: green digit is 1, yellow is 2
NRESP = 243
MAXU = 0xFFFFFFFF


def word_codes(w):
    return [ord(c) - 65 for c in w]


def response(secret, guess):
    # digits: 0 absent, 1 green, 2 yellow; position 0 least significant
    r = [0] * 5
    used = [False] * 5
    for i in range(5):
        if guess[i] == secret[i]:
            r[i] = 1
            used[i] = True
    for i in range(5):
        if r[i] == 1:
            continue
        for j in range(5):
            if guess[i] == secret[j] and not used[j]:
                r[i] = 2
                used[j] = True
                break
    v = 0
    m = 1
    for i in range(5):
        v += r[i] * m
        m *= 3
    return v


# ---------------------------------------------------------------- bounds ----
def nat_sub(a, b):
    return max(0, a - b)


def all_candidates_fill(m, roots, k):
    depth = 1
    cap = roots
    cost = 0
    rem = m
    while True:
        if rem <= cap:
            return cost + rem * depth
        rem2 = rem - cap
        cap2 = cap * (k - 1)
        cost += cap * depth
        depth += 1
        rem = rem2
        cap = cap2


def forest_g(m, roots, k, a1):
    cost = m + (m - a1)
    pow_ = 1
    while True:
        cap = roots * pow_ * k
        used = (pow_ - 1) * a1
        reach = cap - used
        if reach >= m:
            return cost
        cost += m - reach
        pow_ *= k


def forest_bound(m, roots, k):
    if m == 0:
        return 0
    if roots == 0:
        return 1000000000
    if m <= roots:
        return m
    if m <= roots * (k * k - k + 1) + 1:
        return all_candidates_fill(m, roots, k)
    hi = min(roots, m)
    best = min(forest_g(m, roots, k, 0), forest_g(m, roots, k, hi))
    pow_ = k
    while True:
        coeff = pow_ - 1
        cap = roots * pow_ * k
        if cap - coeff * hi >= m:
            break
        if cap >= m:
            kink = (cap - m) // coeff
            for a in (kink, kink + 1):
                if a <= hi:
                    best = min(best, forest_g(m, roots, k, a))
        pow_ *= k
    return best


def capacity_bound(n, k):
    if n == 0:
        return 0
    if n == 1:
        return 1
    if n == 2:
        return 3
    if k <= 1:
        return 0
    return forest_bound(n, 1, k)


def phase2_capacity_bound(n, root_k, max_k):
    if n == 0 or root_k <= 1 or max_k <= 1:
        return capacity_bound(n, max_k)
    if n <= max_k:
        return 3 * n - min(root_k, n)
    return n + forest_bound(n, root_k, max_k)


def tight_capacity_bound(n, root_k, max_k):
    if n == 0:
        return 0
    if n == 1:
        return 1
    if n == 2:
        return 3
    if root_k <= 1 or max_k <= 1:
        return capacity_bound(n, max_k)
    if n <= max_k:
        return 3 * n - 1 - min(root_k, n)
    return n + forest_bound(n - 1, root_k - 1, max_k)


def bucket_capacity_bound(n, root_k, max_k):
    return min(tight_capacity_bound(n, root_k, max_k),
               phase2_capacity_bound(n, root_k, max_k))


def min_k_for_target_bound(n, max_k, target):
    if 3 <= n <= max_k:
        if target < 2 * n - 1:
            return n + 1
        return max((3 * n - 1) - target, 2)
    max_possible = min(n, max_k)
    if target < capacity_bound(n, max_k):
        return max_possible + 1
    if tight_capacity_bound(n, 2, max_k) <= target:
        return 2
    if tight_capacity_bound(n, max_possible, max_k) > target:
        return max_possible + 1
    low, high = 2, max_possible
    while low + 1 < high:
        mid = (low + high) // 2
        if tight_capacity_bound(n, mid, max_k) <= target:
            high = mid
        else:
            low = mid
    return high


def min_non_overlap_for_len(word_len, max_k):
    for t, v in ((59049, 11), (19683, 10), (6561, 9), (2187, 8), (729, 7),
                 (243, 6), (81, 5), (27, 4), (9, 3), (3, 2)):
        if max_k >= t:
            return word_len - v + 1 if word_len > v else 1
    return word_len


# ------------------------------------------------------------ the model ----
def network_sort_counts(e):
    n = len(e)
    if n <= 1:
        return
    if n == 2:
        if e[0][1] < e[1][1]:
            e[0], e[1] = e[1], e[0]
        return
    if n == 3:
        pairs = [(0, 1), (1, 2), (0, 1)]
    elif n == 4:
        pairs = [(0, 1), (2, 3), (0, 2), (1, 3), (1, 2)]
    else:
        pairs = [(0, 1), (3, 4), (2, 4), (2, 3), (0, 3), (1, 4), (0, 2),
                 (1, 3), (1, 2)]
    for a, b in pairs:
        if e[a][1] < e[b][1]:
            e[a], e[b] = e[b], e[a]


class Model:
    def __init__(self, candidates, guesses, verbose=False):
        self.guesses = guesses
        self.candidates = candidates
        self.G = len(guesses)
        self.C = len(candidates)
        self.verbose = verbose
        # response table, guess-major
        self.fb = []
        for g in guesses:
            row = bytearray(self.C)
            for c, s in enumerate(candidates):
                row[c] = response(s, g)
            self.fb.append(row)
        self.gmask = []
        for g in guesses:
            m = 0
            for l in g:
                m |= 1 << l
            self.gmask.append(m)
        self.cmask = []
        self.cat = []
        self.cdup = []
        for s in candidates:
            m = 0
            at = [0] * 5
            dup = 0
            seen = 0
            for i, l in enumerate(s):
                m |= 1 << l
                at[i] = 1 << l
                dup |= seen & (1 << l)
                seen |= 1 << l
            self.cmask.append(m)
            self.cat.append(at)
            self.cdup.append(dup)
        self.c2g = [-1] * self.C
        gindex = {}
        for i, g in enumerate(guesses):
            gindex.setdefault(tuple(g), i)
        for c, s in enumerate(candidates):
            self.c2g[c] = gindex[tuple(s)]
        # deterministic zobrist, two 32-bit words
        self.z1 = []
        self.z2 = []
        st = 12345
        for _ in range(self.C):
            st = (1103515245 * st + 12345) % (1 << 31)
            self.z1.append(st)
            st = (1103515245 * st + 12345) % (1 << 31)
            self.z2.append(st)
        self.reset()

    def reset(self):
        self.states = 0
        self.guesses_eval = 0
        self.cache_hits = 0
        self.pruned = 0
        self.deep_states = 0
        self.deep_guesses = 0
        self.deep_hits = 0
        self.maxdepth = 0
        # tt: dict index -> [ (k1,k2,val,exact), (k1,k2,val,exact) ]
        self.tt = {}
        self.tt_mask = (1 << 20) - 1

    # ---- cache
    def tt_get(self, h):
        k1, k2 = h
        slots = self.tt.get(k1 & self.tt_mask)
        if not slots:
            return None
        for s in slots:
            if s is not None and s[0] == k1 and s[1] == k2:
                return (s[2], s[3])
        return None

    def tt_insert(self, h, value, is_exact):
        k1, k2 = h
        idx = k1 & self.tt_mask
        slots = self.tt.setdefault(idx, [None, None])
        s1 = slots[1]
        if s1 is not None:
            if s1[0] == k1 and s1[1] == k2:
                if s1[2] == value and s1[3] == is_exact:
                    return
                if s1[3] and not is_exact:
                    return
                if (not s1[3]) and (not is_exact) and value < s1[2]:
                    return
                slots[1] = (k1, k2, value, is_exact)
                return
            if value >= s1[2]:
                slots[1] = (k1, k2, value, is_exact)
                return
        else:
            slots[1] = (k1, k2, value, is_exact)
            return
        s0 = slots[0]
        if s0 is not None and s0[0] == k1 and s0[1] == k2:
            if s0[2] == value and s0[3] == is_exact:
                return
            if s0[3] and not is_exact:
                return
            if (not s0[3]) and (not is_exact) and value < s0[2]:
                return
        slots[0] = (k1, k2, value, is_exact)

    # ---- hashes
    def set_hash(self, st):
        h1 = 0
        h2 = 0
        for c in st:
            h1 ^= self.z1[c]
            h2 ^= self.z2[c]
        return (h1, h2)

    # ---- branching factors
    def k_upper(self, st):
        n = len(st)
        if n <= 2:
            return n
        c_mask = 0
        c_all = MAXU
        c_dup = 0
        at = [0] * 5
        el = [0] * 5
        de = [0] * 5
        for c in st:
            m = self.cmask[c]
            c_mask |= m
            c_all &= m
            if m != MAXU:
                dup = self.cdup[c]
                c_dup |= dup
                for i in range(5):
                    b = self.cat[c][i]
                    at[i] |= b
                    el[i] |= m & ~b & MAXU
                    de[i] |= dup & ~b & MAXU
        if c_mask == MAXU:
            return min(n, NRESP)
        b_u = ~c_all & MAXU
        b1_base = b_u | c_dup
        prod = 1
        for i in range(5):
            a = at[i]
            e = el[i]
            ed = de[i]
            b_r = (~a & MAXU) if (a & (a - 1)) == 0 else MAXU
            b1 = b_r & b1_base
            ae = a & e
            aoe = a | e
            aed = a & ed
            aoed = a | ed
            eq3 = (ae & b_u) | (ae & b1) | (aed & b_r)
            if eq3:
                f = 3
            elif (ae | (aoe & b_u)) | (ae | (aoe & b1)) | (aed | (aoed & b_r)):
                f = 2
            else:
                f = 1
            prod *= f
        return min(prod, n, NRESP)

    def distinct(self, g, st):
        seen = set()
        row = self.fb[g]
        for c in st:
            seen.add(row[c])
        return len(seen)

    def k_cand(self, st, target):
        if len(st) <= 2:
            return len(st)
        eff = min(target, len(st), NRESP)
        mx = 0
        for c in st:
            k = self.distinct(self.c2g[c], st)
            if k > mx:
                mx = k
                if mx >= eff:
                    return mx
        return mx

    def k_max_seq(self, st, initial, target):
        if len(st) <= 2:
            return len(st)
        eff = min(target, len(st), NRESP)
        mx = initial
        if mx >= eff:
            return mx
        if mx == 0:
            mx = self.k_cand(st, eff)
            if mx >= eff:
                return mx
        kup = self.k_upper(st)
        if mx >= kup:
            return mx
        eff = min(eff, kup)
        for g in range(self.G):
            k = self.distinct(g, st)
            if k > mx:
                mx = k
                if mx >= eff:
                    break
        return mx

    def max_branching(self, st):
        return self.k_max_seq(st, 0, min(len(st), NRESP))

    # ---- quick eval
    def quick(self, bucket):
        n = len(bucket)
        if n > 15:
            return (2 * n, False)
        if n <= 2:
            return [(0, True), (1, True), (3, True)][n]
        one = False
        for i, ci in enumerate(bucket):
            g = self.c2g[ci]
            row = self.fb[g]
            seen = set()
            coll = 0
            for j, cj in enumerate(bucket):
                if j == i:
                    continue
                r = row[cj]
                if r in seen:
                    coll += 1
                else:
                    seen.add(r)
            if coll == 0:
                return (2 * n - 1, True)
            if coll == 1:
                one = True
        return (2 * n, one)

    # ---- greedy upper bound (no projection dedup: same chosen guess)
    def greedy(self, st):
        n = len(st)
        if n <= 2:
            return n * (n + 1) // 2
        best_g = -1
        best_exp = MAXU
        for g in range(self.G):
            row = self.fb[g]
            counts = {}
            for c in st:
                r = row[c]
                counts[r] = counts.get(r, 0) + 1
            if len(counts) <= 1:
                continue
            exp = sum(v * v for v in counts.values())
            if exp < best_exp:
                best_exp = exp
                best_g = g
        row = self.fb[best_g]
        counts = {}
        for c in st:
            r = row[c]
            counts[r] = counts.get(r, 0) + 1
        cost = n
        for r, p_len in counts.items():
            if r == WIN:
                continue
            cost += self.greedy([c for c in st if row[c] == r])
        return cost

    # ---- main search
    def min_state(self, st, h, beta, depth, parent_max_k, known_quick=0):
        c_len = len(st)
        if c_len <= 2:
            return (0, 1, 3)[c_len]
        cached_lb = 0
        got = self.tt_get(h)
        if got is not None:
            self.cache_hits += 1
            if depth > 0:
                self.deep_hits += 1
            if got[1]:
                return got[0]
            if got[0] >= beta:
                return got[0]
            cached_lb = got[0]
        self.states += 1
        if depth > 0:
            self.deep_states += 1
        if depth > self.maxdepth:
            self.maxdepth = depth
        if known_quick:
            cached_lb = max(cached_lb, known_quick)
        elif cached_lb == 0 and c_len <= 15:
            v, ex = self.quick(st)
            if ex:
                self.tt_insert(h, v, True)
                return v
            cached_lb = max(cached_lb, v)
        parent_lb = self.cap2d[parent_max_k][c_len]
        cached_lb = max(cached_lb, parent_lb)
        cutoff = beta
        if cached_lb >= cutoff:
            self.tt_insert(h, cached_lb, False)
            return cached_lb
        best = beta
        local_lb = max(parent_lb, cached_lb)
        tuples = []
        local_max_k = 0
        valid_phase1_k = 0
        min_val_found = MAXU
        k_to_beat = max(0, 3 * c_len - best)
        min_k_needed = min(local_max_k + 1, k_to_beat)
        max_dup = max(0, c_len - min_k_needed)
        caprow = self.cap2d[parent_max_k]
        for cand_idx, cand in enumerate(st):
            g = self.c2g[cand]
            row = self.fb[g]
            counts = {}
            ne = []
            dup = 0
            aborted = False
            for i, c in enumerate(st):
                if i == cand_idx:
                    continue
                r = row[c]
                cnt = counts.get(r, 0)
                if cnt == 0:
                    ne.append(r)
                else:
                    dup += 1
                    if dup > max_dup:
                        aborted = True
                        break
                counts[r] = cnt + 1
            if aborted:
                min_val_found = min(min_val_found, best)
                continue
            total_ne = len(ne) + 1
            if total_ne > local_max_k:
                local_max_k = total_ne
                min_k_needed = min(local_max_k + 1, k_to_beat)
                max_dup = max(0, c_len - min_k_needed)
            if dup == 0:
                lb = 2 * c_len - 1
                if lb < best:
                    valid_phase1_k = max(valid_phase1_k, total_ne)
                    self.guesses_eval += 1
                    min_val_found = min(min_val_found, lb)
                    best = lb
                else:
                    min_val_found = min(min_val_found, lb)
                break
            if dup == 1:
                lb = 2 * c_len
                if lb < best:
                    valid_phase1_k = max(valid_phase1_k, total_ne)
                    self.guesses_eval += 1
                    min_val_found = min(min_val_found, lb)
                    best = lb
                    k_to_beat = max(0, 3 * c_len - best)
                    min_k_needed = min(local_max_k + 1, k_to_beat)
                    max_dup = max(0, c_len - min_k_needed)
                else:
                    min_val_found = min(min_val_found, lb)
                if min_k_needed > c_len:
                    break
                continue
            exp = 1
            lb = c_len
            for r in ne:
                k = counts[r]
                exp += k * k
                lb += caprow[k]
            if lb < best:
                if total_ne > valid_phase1_k:
                    valid_phase1_k = total_ne
                if exp == c_len + 2 * dup:
                    self.guesses_eval += 1
                    min_val_found = min(min_val_found, lb)
                    best = lb
                    k_to_beat = max(0, 3 * c_len - best)
                    min_k_needed = min(local_max_k + 1, k_to_beat)
                    max_dup = max(0, c_len - min_k_needed)
                else:
                    tuples.append((lb, exp, g))
            else:
                min_val_found = min(min_val_found, lb)
            if min_k_needed > c_len:
                break
        if best > local_lb and tuples:
            tuples.sort()
            for idx, t in enumerate(tuples):
                if t[0] >= best:
                    min_val_found = min(min_val_found, t[0])
                    self.pruned += len(tuples) - idx
                    break
                v = self.min_guess(st, t[2], best, depth, parent_max_k)
                min_val_found = min(min_val_found, v)
                if v < best:
                    best = v
                    if best <= local_lb:
                        break
        phase2_min_lb = phase2_capacity_bound(c_len, parent_max_k, parent_max_k)
        phase2_eff = max(local_lb, phase2_min_lb)
        if best > phase2_eff:
            valid_phase2_k = 0
            k_to_beat = max(0, 3 * c_len - max(0, best - 1))
            min_k_needed = min(local_max_k + 1, k_to_beat)
            phase2 = []
            if c_len >= min_k_needed:
                max_dup2 = c_len - min_k_needed
                is_in_set = set(self.c2g[c] for c in st)
                c_mask_set = 0
                multi = 0
                for c in st:
                    multi |= c_mask_set & self.cmask[c]
                    c_mask_set |= self.cmask[c]
                for g in range(self.G):
                    if g in is_in_set:
                        continue
                    shared = self.gmask[g] & c_mask_set
                    if (shared & (shared - 1)) == 0 and (shared & multi) == 0:
                        continue
                    row = self.fb[g]
                    counts = {}
                    ne = []
                    dup = 0
                    aborted = False
                    for i, c in enumerate(st):
                        r = row[c]
                        cnt = counts.get(r, 0)
                        if cnt == 0:
                            ne.append(r)
                        else:
                            dup += 1
                            if dup > max_dup2:
                                aborted = True
                                break
                        counts[r] = cnt + 1
                    if aborted:
                        min_val_found = min(min_val_found, best)
                        continue
                    if len(ne) == 1:
                        continue
                    if len(ne) == 2:
                        c0 = counts[ne[0]]
                        if c0 == 1 or c0 == c_len - 1:
                            continue
                        c1 = c_len - c0
                        exp = c0 * c0 + c1 * c1
                        lb = c_len + caprow[c0] + caprow[c1]
                    else:
                        exp = 0
                        lb = c_len
                        for r in ne:
                            k = counts[r]
                            exp += k * k
                            lb += caprow[k]
                    if len(ne) > local_max_k:
                        local_max_k = len(ne)
                        min_k_needed = min(local_max_k + 1, k_to_beat)
                        max_dup2 = max(0, c_len - min_k_needed)
                    if lb < best:
                        if len(ne) > valid_phase2_k:
                            valid_phase2_k = len(ne)
                        if exp == c_len + 2 * dup:
                            self.guesses_eval += 1
                            min_val_found = min(min_val_found, lb)
                            best = lb
                            k_to_beat = max(0, 3 * c_len - max(0, best - 1))
                            min_k_needed = min(local_max_k + 1, k_to_beat)
                            max_dup2 = max(0, c_len - min_k_needed)
                        else:
                            phase2.append((lb, exp, g))
                    else:
                        min_val_found = min(min_val_found, lb)
                    if min_k_needed > c_len:
                        break
            else:
                min_val_found = min(min_val_found, best)
            base_lb = self.cap2d[local_max_k][c_len]
            if base_lb > local_lb:
                local_lb = base_lb
            p1 = tight_capacity_bound(c_len, valid_phase1_k, local_max_k) \
                if valid_phase1_k else MAXU
            p2 = phase2_capacity_bound(c_len, valid_phase2_k, local_max_k) \
                if valid_phase2_k else MAXU
            tl = min(p1, p2)
            if tl != MAXU and tl > local_lb:
                local_lb = tl
            if local_lb < best:
                if phase2:
                    phase2.sort()
                    for idx, t in enumerate(phase2):
                        if t[0] >= best:
                            min_val_found = min(min_val_found, t[0])
                            self.pruned += len(phase2) - idx
                            break
                        v = self.min_guess(st, t[2], best, depth, local_max_k)
                        min_val_found = min(min_val_found, v)
                        if v < best:
                            best = v
                            if best <= local_lb:
                                break
        else:
            min_val_found = min(min_val_found, phase2_min_lb)
        is_exact = best < beta
        if is_exact:
            self.tt_insert(h, best, True)
            return best
        final_lb = max(beta, local_lb)
        if best > local_lb and min_val_found != MAXU:
            final_lb = max(final_lb, min_val_found)
        self.tt_insert(h, final_lb, False)
        return final_lb

    def cmask_of(self, st):
        m = 0
        for c in st:
            m |= self.cmask[c]
        return m

    def min_guess(self, st, guess, beta, depth, parent_max_k):
        c_len = len(st)
        self.guesses_eval += 1
        if depth > 0:
            self.deep_guesses += 1
        caprow = self.cap2d[parent_max_k]
        row = self.fb[guess]
        if c_len <= 16:
            counts = {}
            order = []
            ne = []
            num_eval = 0
            for i, c in enumerate(st):
                r = row[c]
                cnt = counts.get(r, 0)
                if cnt == 0:
                    ne.append(r)
                    counts[r] = 1
                elif cnt == 1:
                    counts[r] = 2
                elif cnt == 2:
                    counts[r] = 3
                    num_eval += 1
                else:
                    counts[r] = cnt + 1
            total = len(ne)
            if total <= 1:
                return beta
            cutoff = beta
            has_win = WIN in counts
            cost = 3 * c_len - total - (1 if has_win else 0)
            if cost >= cutoff:
                self.pruned += 1
                return cost
            if num_eval == 0:
                return cost
            entries = []
            for r in ne:
                if counts[r] >= 3:
                    entries.append([r, counts[r], 0, False])
            network_sort_counts(entries)
            all_exact = True
            for e in entries:
                r, p_len = e[0], e[1]
                lb = caprow[p_len]
                h = (0, 0)
                for c in st:
                    if row[c] == r:
                        h = (h[0] ^ self.z1[c], h[1] ^ self.z2[c])
                got = self.tt_get(h)
                if got is not None:
                    self.cache_hits += 1
                    used, ex = max(got[0], lb), got[1]
                else:
                    p = [c for c in st if row[c] == r]
                    qv, ex = self.quick(p)
                    used = max(qv, lb)
                    self.tt_insert(h, used, ex)
                e[2] = used
                e[3] = ex
                e.append(h)
                if not ex:
                    all_exact = False
                if used > lb:
                    cost += used - lb
                    if cost >= cutoff:
                        self.pruned += 1
                        return cost
            if all_exact:
                return cost
            if cost >= cutoff:
                self.pruned += 1
                return cost
            for e in entries:
                if e[3]:
                    continue
                if cost >= cutoff:
                    self.pruned += 1
                    return cost
                used = e[2]
                b = cost - used
                new_beta = max(0, beta - b)
                if new_beta <= used:
                    self.pruned += 1
                    return cost
                p = [c for c in st if row[c] == e[0]]
                val = self.min_state(p, e[4], new_beta, depth + 1, parent_max_k, used)
                if b + val >= cutoff:
                    self.pruned += 1
                    return b + val
                cost = b + val
            return cost
        # c_len > 16
        counts = {}
        ne = []
        ge3 = []
        for c in st:
            r = row[c]
            cnt = counts.get(r, 0) + 1
            counts[r] = cnt
            if cnt == 1:
                ne.append(r)
            elif cnt == 3:
                ge3.append(r)
        total = len(ne)
        if total <= 1:
            return beta
        cutoff = beta
        has_win = WIN in counts
        cost = 3 * c_len - total - (1 if has_win else 0)
        if cost >= cutoff:
            self.pruned += 1
            return cost
        entries = []
        for r in sorted(ge3, key=lambda r: -((counts[r] << 16) | ((~r) & 0xFFFF))):
            p_len = counts[r]
            lb = caprow[p_len]
            cost += lb - (2 * p_len - 1)
            if cost >= cutoff:
                self.pruned += 1
                return cost
            entries.append([r, p_len, 0, False])
        num_eval = len(entries)
        if num_eval == 0:
            return cost
        entries.sort(key=lambda e: -((e[1] << 16) | ((~e[0]) & 0xFFFF)))
        split = 0
        while split < num_eval and entries[split][1] > 15:
            split += 1
        for i, e in enumerate(entries):
            e.append(None)
        # hashes
        for e in entries:
            r = e[0]
            h1 = 0
            h2 = 0
            for c in st:
                if row[c] == r:
                    h1 ^= self.z1[c]
                    h2 ^= self.z2[c]
            e[4] = (h1, h2)
            e.append(0)  # child max k
        exact_mask = [False] * num_eval
        cached_mask = [False] * num_eval
        num_exact = 0
        for i, e in enumerate(entries):
            lb = caprow[e[1]]
            got = self.tt_get(e[4])
            if got is not None:
                self.cache_hits += 1
                used = max(got[0], lb)
                e[2] = used
                if got[1]:
                    exact_mask[i] = True
                    num_exact += 1
                cached_mask[i] = True
                if used > lb:
                    cost += used - lb
                    if cost >= cutoff:
                        self.pruned += 1
                        return cost
            else:
                e[2] = lb
        if num_exact == num_eval:
            return cost
        # extraction
        buckets = [[c for c in st if row[c] == e[0]] for e in entries]
        # fast path
        fast_cost = cost
        if split > 0:
            if cost >= cutoff:
                self.pruned += 1
                return cost
            for i in range(split):
                if cached_mask[i]:
                    continue
                e = entries[i]
                p = buckets[i]
                ku = self.k_upper(p)
                e[5] = ku
                lb = caprow[e[1]]
                atl = max(bucket_capacity_bound(e[1], ku, parent_max_k), lb)
                e[2] = atl
                if atl > lb:
                    fast_cost += atl - lb
                    if fast_cost >= cutoff:
                        self.pruned += 1
                        return fast_cost
        for i in range(split, num_eval):
            if cached_mask[i]:
                continue
            e = entries[i]
            p = buckets[i]
            lb = caprow[e[1]]
            qv, ex = self.quick(p)
            used = max(qv, lb)
            e[2] = used
            if ex:
                exact_mask[i] = True
                num_exact += 1
            self.tt_insert(e[4], used, ex)
            if used > lb:
                d = used - lb
                cost += d
                fast_cost += d
                if fast_cost >= cutoff:
                    self.pruned += 1
                    return fast_cost
        if num_exact == num_eval:
            return cost
        for i in range(split):
            if cached_mask[i]:
                continue
            if fast_cost >= cutoff:
                self.pruned += 1
                return fast_cost
            e = entries[i]
            p_len = e[1]
            lb = caprow[p_len]
            approx = e[2]
            approx_inc = approx - lb
            target_k = min_k_for_target_bound(p_len, parent_max_k, lb)
            p = buckets[i]
            if target_k == 2:
                e[2] = lb
                self.tt_insert(e[4], lb, False)
            else:
                ku = e[5]
                kc = self.k_cand(p, min(target_k, ku))
                if kc >= target_k:
                    e[2] = lb
                    self.tt_insert(e[4], lb, False)
                elif kc >= ku:
                    k = ku
                    tight = bucket_capacity_bound(p_len, k, parent_max_k)
                    used = max(tight, lb)
                    e[2] = used
                    self.tt_insert(e[4], used, False)
                    if used > lb:
                        actual = used - lb
                        cost += actual
                        fast_cost += actual - approx_inc
                        if fast_cost >= cutoff:
                            self.pruned += 1
                            return fast_cost
                else:
                    k = self.k_max_seq(p, kc, min(target_k, ku))
                    if k >= target_k:
                        e[2] = lb
                        self.tt_insert(e[4], lb, False)
                    else:
                        e[5] = k
                        tight = bucket_capacity_bound(p_len, k, parent_max_k)
                        used = max(tight, lb)
                        e[2] = used
                        self.tt_insert(e[4], used, False)
                        if used > lb:
                            actual = used - lb
                            cost += actual
                            fast_cost += actual - approx_inc
                            if fast_cost >= cutoff:
                                self.pruned += 1
                                return fast_cost
        if cost >= cutoff:
            self.pruned += 1
            return cost
        for i in range(num_eval):
            if exact_mask[i]:
                continue
            if cost >= cutoff:
                self.pruned += 1
                return cost
            e = entries[i]
            p = buckets[i]
            actual_lb = e[2]
            b = cost - actual_lb
            new_beta = beta - b
            if new_beta <= actual_lb:
                self.pruned += 1
                return cost
            child_k = p_len = e[1]
            if i < split and e[5] != 0:
                child_k = max(min(e[5], p_len, parent_max_k), 2)
            else:
                child_k = max(min(p_len, parent_max_k), 2)
            known_quick = actual_lb if i >= split else 0
            val = self.min_state(p, e[4], new_beta, depth + 1, child_k, known_quick)
            if b + val >= cutoff:
                self.pruned += 1
                return b + val
            cost = b + val
        return cost

    # ---- driver: like solve() but the root is a plain State (M1)
    def run(self, n, root_state=True):
        st = list(range(n))
        self.max_k = self.max_branching(st)
        self.cap2d = [[0] * (self.C + 1) for _ in range(self.max_k + 1)]
        for k in range(2, self.max_k + 1):
            for i in range(self.C + 1):
                self.cap2d[k][i] = capacity_bound(i, k)
        self.multi_c_mask = 0
        m = 0
        for c in st:
            self.multi_c_mask |= m & self.cmask[c]
            m |= self.cmask[c]
        ub = self.greedy(st)
        h = self.set_hash(st)
        if root_state:
            val = self.min_state(st, h, ub, 0, self.max_k)
        else:
            val = ub
        return val, ub, self.max_k


def load(path):
    with open(path) as f:
        return [word_codes(l.strip()) for l in f if l.strip()]


if __name__ == "__main__":
    cand_path = sys.argv[1]
    guess_path = sys.argv[2]
    n = int(sys.argv[3]) if len(sys.argv) > 3 else None
    cands = load(cand_path)
    if n:
        cands = cands[:n]
    guesses = load(guess_path)
    m = Model(cands, guesses)
    val, ub, mk = m.run(len(cands))
    print(f"cost {val} ub {ub} max_k {mk} states {m.states} "
          f"guesses {m.guesses_eval} hits {m.cache_hits} pruned {m.pruned} "
          f"| deep states {m.deep_states} guesses {m.deep_guesses} hits {m.deep_hits} "
          f"maxdepth {m.maxdepth}")
