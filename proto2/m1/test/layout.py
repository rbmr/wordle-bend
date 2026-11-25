# Replicates the Bend prototype's table layout and contents, so its whole-array
# checksum can be compared with the real thing.
#
# Usage: python3 layout.py <candidates.txt> <guesses.txt>
import sys

CAPROWS = 256
DEPTHS = 24
ENTN = 1024
TTB = 1048576


def off_z1(c, g):
    return g * c


def off_z2(c, g):
    return off_z1(c, g) + c


def off_cmask(c, g):
    return off_z2(c, g) + c


def off_cat(c, g):
    return off_cmask(c, g) + c


def off_cdup(c, g):
    return off_cat(c, g) + 5 * c


def off_c2g(c, g):
    return off_cdup(c, g) + c


def off_gmask(c, g):
    return off_c2g(c, g) + c


def off_gpack(c, g):
    return off_gmask(c, g) + g


def off_cpack(c, g):
    return off_gpack(c, g) + g


def cap_size(c):
    return CAPROWS * (c + 1)


def off_hh(c, g):
    return off_cpack(c, g) + c


def off_cap(c, g):
    return off_hh(c, g) + 131072


def off_tt(c, g):
    return off_cap(c, g) + cap_size(c)


def off_sets(c, g):
    return off_tt(c, g) + 6 * TTB


def off_cnt(c, g):
    return off_sets(c, g) + DEPTHS * c


def off_off(c, g):
    return off_cnt(c, g) + DEPTHS * 256


def off_h1(c, g):
    return off_off(c, g) + DEPTHS * 256


def off_h2(c, g):
    return off_h1(c, g) + DEPTHS * 256


def off_ent(c, g):
    return off_h2(c, g) + DEPTHS * 256


def off_plb(c, g):
    return off_ent(c, g) + DEPTHS * ENTN


def off_cmk(c, g):
    return off_plb(c, g) + DEPTHS * ENTN


def off_flg(c, g):
    return off_cmk(c, g) + DEPTHS * ENTN


def off_p1t(c, g):
    return off_flg(c, g) + DEPTHS * ENTN


def off_p2t(c, g):
    return off_p1t(c, g) + DEPTHS * c * 3


def off_gset(c, g):
    return off_p2t(c, g) + DEPTHS * g * 3


def off_gstk(c, g):
    return off_gset(c, g) + 8 * c


def off_gcnt(c, g):
    return off_gstk(c, g) + 4 * 4096


def total_size(c, g):
    return off_gcnt(c, g) + 1024


def eq01(a, b):
    d = (a - b) & 0xFFFFFFFF
    return (1 - min(1, d)) & 0xFFFFFFFF


def lt01(a, b):
    return ((a - b) & 0xFFFFFFFF) // 2147483648


def resp(gp, sp):
    def fld(x, sh):
        return (x >> sh) & 31
    g = [fld(gp, 20), fld(gp, 15), fld(gp, 10), fld(gp, 5), fld(gp, 0)]
    s = [fld(sp, 20), fld(sp, 15), fld(sp, 10), fld(sp, 5), fld(sp, 0)]
    e = [eq01(g[i], s[i]) for i in range(5)]
    eb = e[0] | e[1] << 1 | e[2] << 2 | e[3] << 3 | e[4] << 4
    lm = [sum(eq01(g[j], g[i]) << j for j in range(5)) for i in range(5)]
    c = [sum(eq01(s[j], g[i]) for j in range(5)) for i in range(5)]
    y = [0] * 5
    for i in range(5):
        b = bin(lm[i] & ((eb ^ 31) & ((1 << i) - 1))).count("1")
        gc = bin(lm[i] & eb).count("1")
        y[i] = (1 - e[i]) * (1 if c[i] - gc > b else 0)
    d = [e[i] + 2 * y[i] for i in range(5)]
    return d[0] + 3 * d[1] + 9 * d[2] + 27 * d[3] + 81 * d[4]


def pack5(ls):
    return sum(ls[i] << (20 - 5 * i) for i in range(5))


def load(path):
    with open(path) as f:
        return [l.strip() for l in f if l.strip()]


def main():
    cands = load(sys.argv[1])
    guesses = load(sys.argv[2])
    C = len(cands)
    G = len(guesses)
    total = total_size(C, G)
    size = 1
    while size < total:
        size *= 2
    a = {}

    def put(i, v):
        a[i & (size - 1)] = v

    cpack = [pack5([ord(ch) - 65 for ch in w]) for w in cands]
    gpack = [pack5([ord(ch) - 65 for ch in w]) for w in guesses]
    for i, w in enumerate(guesses):
        put(off_gpack(C, G) + i, gpack[i])
        m = 0
        for ch in w:
            m |= 1 << (ord(ch) - 65)
        put(off_gmask(C, G) + i, m)
    for i, w in enumerate(cands):
        ls = [ord(ch) - 65 for ch in w]
        bits = [1 << l for l in ls]
        put(off_cpack(C, G) + i, cpack[i])
        put(off_cmask(C, G) + i, bits[0] | bits[1] | bits[2] | bits[3] | bits[4])
        for j in range(5):
            put(off_cat(C, G) + 5 * i + j, bits[j])
        dup = 0
        for x in range(5):
            for y in range(x + 1, 5):
                dup |= bits[x] & bits[y]
        put(off_cdup(C, G) + i, dup)
    s = 12345
    for i in range(C):
        s = (s * 1103515245 + 12345) & 0xFFFFFFFF
        put(off_z1(C, G) + i, s)
        s = (s * 1103515245 + 12345) & 0xFFFFFFFF
        put(off_z2(C, G) + i, s)
    # hash table, then the lookups
    for i in range(131072):
        put(off_hh(C, G) + i, 0xFFFFFFFF)
    for g in range(G):
        pos = (gpack[g] * 2654435761 & 0xFFFFFFFF) & 65535
        while True:
            if a.get((off_hh(C, G) + 2 * pos) & (size - 1)) == 0xFFFFFFFF:
                put(off_hh(C, G) + 2 * pos, gpack[g])
                put(off_hh(C, G) + 2 * pos + 1, g)
                break
            pos = (pos + 1) & 65535
    for ic in range(C):
        pos = (cpack[ic] * 2654435761 & 0xFFFFFFFF) & 65535
        while True:
            k = a.get((off_hh(C, G) + 2 * pos) & (size - 1))
            if k == cpack[ic]:
                put(off_c2g(C, G) + ic, a[(off_hh(C, G) + 2 * pos + 1) & (size - 1)])
                break
            if k == 0xFFFFFFFF:
                raise SystemExit(f"candidate {cands[ic]} not found")
            pos = (pos + 1) & 65535
    for g in range(G):
        for c in range(C):
            put(g * C + c, resp(gpack[g], cpack[c]))
    tot = sum(a.get(i, 0) for i in range(size)) & 0xFFFFFFFF
    print(f"C={C} G={G} cells={total} size={size} all={tot}")
    print(f"sanity: resp(AAAAA,AAAAA)={resp(pack5([0]*5), pack5([0]*5))}"
          f" resp(ABBEY,ADMIN)={resp(pack5([0,1,1,4,24]), pack5([0,3,12,8,13]))}")


if __name__ == "__main__":
    main()
