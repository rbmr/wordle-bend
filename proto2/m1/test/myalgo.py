# Python model of the *Bend slice-2 engine* (proto2/m1/src/engine.bend), used
# only to locate a disagreement with ref.py; not part of the deliverable.
#
# Differences from ref.py on purpose (all slice-2 simplifications):
#   - no transposition table
#   - no phase1/phase2 split, no tuple sorting: every guess in index order
#   - no per-bucket quick eval before recursion (children start at the cap bound)
#   - the bucket's cutoff subtracts 2p-1 (not cap[p]) from the accumulated cost
import sys
import ref

MAXU = 0xFFFFFFFF
WIN = ref.WIN


class My(ref.Model):
    def __init__(self, *a, **k):
        super().__init__(*a, **k)
        self.trace = []

    # enter a node at the cap bound, as the frame machine does
    def node(self, st, beta, pmk, depth=0):
        n = len(st)
        if n <= 2:
            return (0, 1, 3)[n]
        cap = self.cap2d[pmk][n]
        lb = max(0, cap)
        qv = 0
        if 3 <= n <= 15:
            qv, ex = self.quick(st)
            if ex:
                print("QUICK-EXACT", n, qv) if self.trace else None
                return qv
            lb = max(lb, qv)
        if lb >= beta:
            return lb
        best = beta
        for g in range(self.G):
            row = self.fb[g]
            counts = {}
            for c in st:
                r = row[c]
                counts[r] = counts.get(r, 0) + 1
            t = len(counts)
            if t <= 1:
                continue
            hw = 1 if WIN in counts else 0
            # lower bound, as S.stats computes it
            lbg = n
            for r, k in counts.items():
                if r == WIN:
                    continue
                lbg += self.cap2d[pmk][k]
            if max(lbg, lb) >= best:
                continue
            cost = 3 * n - t - hw
            if cost >= best:
                continue
            ok = False
            for r, k in counts.items():
                if r == WIN or k <= 2:
                    continue
                base = 2 * k - 1
                cut = best - (cost - base)
                if cut <= self.cap2d[pmk][k]:
                    cost = cost + 0  # pruned: the guess cannot beat best
                    best = best
                    ok = True
                    break
                bucket = [c for c in st if row[c] == r]
                v = self.node(bucket, cut, pmk, depth + 1)
                cost = cost + v - base
                if cost >= best:
                    ok = True
                    break
            if not ok:
                if cost < best:
                    best = cost
        return best


def main():
    cand_path, guess_path, n = sys.argv[1], sys.argv[2], int(sys.argv[3])
    cands = ref.load(cand_path)[:n]
    guesses = ref.load(guess_path)
    m = My(cands, guesses)
    st = list(range(len(cands)))
    m.max_k = m.max_branching(st)
    m.cap2d = [[0] * (m.C + 1) for _ in range(m.max_k + 1)]
    for k in range(2, m.max_k + 1):
        for i in range(m.C + 1):
            m.cap2d[k][i] = ref.capacity_bound(i, k)
    ub = len(cands) * (len(cands) + 1) // 2
    v = m.node(st, ub, m.max_k)
    print("my", v, "ref", ref.Model(cands, guesses).run(len(cands))[0])


main()
