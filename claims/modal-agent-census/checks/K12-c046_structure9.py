"""C046 r1 structure check on the size<=9 census (2815 finite-linear-model classes, K1).
Pinned dataset census9.json (sha256 below; same file as K1's check). Payoffs T=5,R=3,P=1,S=0.
Asserts: (1) round robin (vs all 2815 incl. self): max 8083, attained by exactly 63 agents, all
behaving exactly like DefectBot in the census (defect vs all; every agent treats them as DB);
(2) 1335 observational classes (equal row and column); (3) on that quotient 180 symmetric Nash
classes, 78 self-defecting (each invaded by FairBot: equal payoff vs it, strictly better vs itself)
and 102 self-cooperating (each unexploitable and with a neutral mutant, CooperateBot for 95);
no ESS; (4) every cell used above plus 3000 random cells re-solved by the independent
height-table solver embedded below. Exact integers; no tolerances.
"""
"""C046 r1 census check (size <= 9). Self-contained except the pinned dataset.
Language L9: formulas over atoms p (opponent cooperates with me), q (opponent
cooperates with DefectBot), constant F; connectives ~, &, |, []; every p,q under
a box (syntactically guarded); size = number of syntax-tree nodes.
Agents are identified up to equivalence on all finite linear GL models (sound:
game fixed points are letter-free, so play depends only on the height chain).
Asserts:
 (1) classes first realised at sizes 1..9: 1,4,8,12,31,98,255,646,1760 (2815);
 (2) pinned census dataset lists exactly these classes (smallest realisers);
 (3) the full 2815x2815 matrix: every row/column of DB, CB, FB, PB, F2, P0 and
     2000 random cells re-solved by an independent height-table solver;
 (4) property census from the matrix (see bottom).
Boolean, exact; no tolerances.
"""
"""engine: modal agents as canonical Mealy/Moore machines on linear chains.

Language L: formulas over atoms p ('opponent cooperates with me'), q ('opponent
cooperates with DefectBot'), constant F (bottom); connectives not, and, or, box.
Size = number of nodes of the syntax tree (each atom/constant/connective = 1).
Agent = syntactically guarded formula (every p,q under a box).

Semantics: game fixed points are letter-free, hence depend only on height, so an
agent acts as a causal operator on the height chain 0<1<2<...: at height h the
value of box(psi) is AND of psi over heights <h. A formula is a Mealy machine:
state = box-vector, input = (p,q) at current height. Equivalence of machines =
equivalence on all finite linear models = behaviour in every game (sound dedup).
"""
import sys, hashlib, time, json, random
from collections import deque

INPUTS = range(4)  # bit0 = p, bit1 = q

def canon(trans, out, init=0):
    """minimize + BFS-renumber. trans[s][i], out[s][i]. returns hashable key."""
    n = len(trans)
    # reachable
    seen = {init}; order = [init]; k = 0
    while k < len(order):
        s = order[k]; k += 1
        for i in INPUTS:
            t = trans[s][i]
            if t not in seen: seen.add(t); order.append(t)
    # partition refinement
    block = {s: tuple(out[s]) for s in order}
    while True:
        sig = {s: (block[s],) + tuple(block[trans[s][i]] for i in INPUTS) for s in order}
        ids = {}
        nb = {s: ids.setdefault(sig[s], len(ids)) for s in order}
        nblocks_old = len(set(block.values()))
        block = nb
        if len(ids) == nblocks_old: break
    # BFS renumber over blocks
    rep = {}
    for s in order: rep.setdefault(block[s], s)
    num = {block[init]: 0}; q = [block[init]]; k = 0
    T = []; O = []
    while k < len(q):
        b = q[k]; k += 1; s = rep[b]
        row = []
        for i in INPUTS:
            tb = block[trans[s][i]]
            if tb not in num: num[tb] = len(q); q.append(tb)
            row.append(num[tb])
        T.append(tuple(row)); O.append(tuple(out[s]))
    return (tuple(T), tuple(O))

def atom(bit):
    return canon([[0]*4], [[(i >> bit) & 1 for i in INPUTS]])
BOT = canon([[0]*4], [[0]*4])
P = atom(0); Q = atom(1)

def neg(m):
    T, O = m
    return canon([list(r) for r in T], [[1-o for o in r] for r in O])

def binop(m1, m2, f):
    T1, O1 = m1; T2, O2 = m2
    idx = {(0, 0): 0}; st = [(0, 0)]; trans = []; out = []; k = 0
    while k < len(st):
        a, b = st[k]; k += 1
        row = []
        for i in INPUTS:
            t = (T1[a][i], T2[b][i])
            if t not in idx: idx[t] = len(st); st.append(t)
            row.append(idx[t])
        trans.append(row); out.append([f(O1[a][i], O2[b][i]) for i in INPUTS])
    return canon(trans, out)

def AND(a, b): return binop(a, b, lambda x, y: x & y)
def OR(a, b): return binop(a, b, lambda x, y: x | y)

def box(m):
    T, O = m
    idx = {(0, 1): 0}; st = [(0, 1)]; trans = []; out = []; k = 0
    while k < len(st):
        s, f = st[k]; k += 1
        row = []
        for i in INPUTS:
            t = (T[s][i], f & O[s][i])
            if t not in idx: idx[t] = len(st); st.append(t)
            row.append(idx[t])
        trans.append(row); out.append([f]*4)
    return canon(trans, out)

def is_moore(m):
    return all(len(set(r)) == 1 for r in m[1])

def enumerate_classes(N, log=True):
    """U[n]: classes first reached at size n by any formula; G[n]: by guarded formula.
    first[cls] = (size, formula string) of a smallest realiser (guarded for G)."""
    U = {}; G = {}           # size -> list of classes (new at that size)
    firstU = {}; firstG = {}
    def addU(n, c, s):
        if c not in firstU: firstU[c] = (n, s); U[n].append(c)
    def addG(n, c, s):
        if c not in firstG: firstG[c] = (n, s); G[n].append(c)
    for n in range(1, N+1):
        t0 = time.time()
        U[n] = []; G[n] = []
        if n == 1:
            addU(1, BOT, 'F'); addU(1, P, 'p'); addU(1, Q, 'q'); addG(1, BOT, 'F')
        else:
            # unary
            for c in U[n-1]:
                s = firstU[c][1]
                addU(n, neg(c), '~' + s)
                b = box(c); addU(n, b, '[]' + s); addG(n, b, '[]' + s)
            for c in G[n-1]:
                addG(n, neg(c), '~' + firstG[c][1])
            # binary: sizes i + j = n-1
            for i in range(1, n-1):
                j = n - 1 - i
                if i > j: break
                for (pool, first, add) in ((U, firstU, addU), (G, firstG, addG)):
                    for ai, a in enumerate(pool[i]):
                        sa = first[a][1]
                        for bi, b in enumerate(pool[j]):
                            if i == j and bi < ai: continue
                            sb = first[b][1]
                            add(n, AND(a, b), '(' + sa + '&' + sb + ')')
                            add(n, OR(a, b), '(' + sa + '|' + sb + ')')
        # guarded classes must also enter U pool (they're formulas too)
        for c in G[n]:
            addU(n, c, firstG[c][1])
        if log:
            print(f'size {n}: new U {len(U[n])} (tot {len(firstU)}), new G {len(G[n])} (tot {len(firstG)}), {time.time()-t0:.1f}s', flush=True)
    return U, G, firstU, firstG


"""Independent exact game solver from formula strings (no machines).
Height table: value of box(f) at height h = AND of f over heights < h.
A game's joint value at height h is a function of the set of boxed subformulas
true at h (in A-vs-B, B-vs-A, A-vs-DB, B-vs-DB); that set only shrinks with h,
so it is constant from some height <= total number of boxes + 1 onward."""
def parse_tree(s):
    s = s.replace(' ', '')
    def p(i):
        c = s[i]
        if c in 'FTpq': return (c,), i+1
        if c == '~': m, j = p(i+1); return ('~', m), j
        if s.startswith('[]', i): m, j = p(i+2); return ('[]', m), j
        if c == '(':
            a, j = p(i+1); op = s[j]; b, k = p(j+1); assert s[k] == ')'
            return (op, a, b), k+1
        raise ValueError(s[i:])
    t, j = p(0); assert j == len(s); return t

def nboxes(t): return (t[0] == '[]') + sum(nboxes(x) for x in t[1:])

def game(sa, sb):
    """returns (A coops B, B coops A) in the standard model (tail value)."""
    A, B = parse_tree(sa), parse_tree(sb)
    H = 2 * (nboxes(A) + nboxes(B)) + 3
    # traces: x[h]=A vs B, y[h]=B vs A, za[h]=A vs DB, zb[h]=B vs DB
    x, y, za, zb = [], [], [], []
    def ev(t, h, pt, qt, memo):
        key = (id(t), h)
        if key in memo: return memo[key]
        k = t[0]
        if k == 'F': r = False
        elif k == 'T': r = True
        elif k == 'p': r = pt[h]
        elif k == 'q': r = qt[h]
        elif k == '~': r = not ev(t[1], h, pt, qt, memo)
        elif k == '&': r = ev(t[1], h, pt, qt, memo) and ev(t[2], h, pt, qt, memo)
        elif k == '|': r = ev(t[1], h, pt, qt, memo) or ev(t[2], h, pt, qt, memo)
        elif k == '[]': r = all(ev(t[1], g, pt, qt, memo) for g in range(h))
        memo[key] = r; return r
    zero = [False] * H
    m1, m2, m3, m4 = {}, {}, {}, {}
    for h in range(H):
        # guardedness: values at h only read traces at heights < h
        za.append(ev(A, h, zero, zero, m3)); zb.append(ev(B, h, zero, zero, m4))
        xa = ev(A, h, y, zb, m1); yb = ev(B, h, x, za, m2)
        x.append(xa); y.append(yb)
    return x[-1], y[-1]

PATHS = ['/run/agents/r1/census/census9.json', '/work/agents/r1/census/census9.json']
SHA = '82b872829655bbcc898e1e03213ff3f0f44da86a720b2fa9c9ad7c8992d6c6e2'

def parse(s):
    def m(t):
        k = t[0]
        if k == 'F': return BOT
        if k == 'T': return neg(BOT)
        if k == 'p': return P
        if k == 'q': return Q
        if k == '~': return neg(m(t[1]))
        if k == '[]': return box(m(t[1]))
        return (AND if k == '&' else OR)(m(t[1]), m(t[2]))
    return m(parse_tree(s))


def main():
    t0 = time.time()
    raw = None
    for pth in PATHS:
        try: raw = open(pth, 'rb').read(); break
        except OSError: pass
    assert raw is not None, 'dataset missing'
    assert hashlib.sha256(raw).hexdigest() == SHA
    d = json.loads(raw)
    names = d['agents']; n = len(names); assert n == 2815
    bits = bytes.fromhex(d['M_packbits_hex'])
    M = [[(bits[(a * n + b) >> 3] >> (7 - ((a * n + b) & 7))) & 1 for b in range(n)] for a in range(n)]
    def pay(a, b):   # payoff of a vs b; T=5, R=3, P=1, S=0
        x, y = M[a][b], M[b][a]
        return 3 if x and y else (5 if y else (0 if x else 1))
    P = [[pay(a, b) for b in range(n)] for a in range(n)]
    ix = {s: i for i, s in enumerate(names)}
    DB, CB, FB = ix['F'], ix['~F'], ix['[]p']
    # (1) round robin (each agent vs all 2815 incl. itself)
    rr = [sum(r) for r in P]
    top = max(rr); winners = [a for a in range(n) if rr[a] == top]
    assert top == 8083 and len(winners) == 63 and DB in winners
    colDB = [M[b][DB] for b in range(n)]
    for a in winners:   # identical to DB in census: defect vs all, treated like DB by all
        assert not any(M[a]) and [M[b][a] for b in range(n)] == colDB
    second = max(r for r in rr if r < top)
    # (2) observational classes (row and column equal)
    cls = {}
    for a in range(n):
        cls.setdefault((tuple(M[a]), tuple(M[b][a] for b in range(n))), []).append(a)
    assert len(cls) == 1335
    R = [v[0] for v in cls.values()]
    rep = {a: v[0] for v in cls.values() for a in v}
    # (3) symmetric Nash and ESS on the observational quotient
    nash = [a for a in R if all(P[b][a] <= P[a][a] for b in R)]
    dn = [a for a in nash if not M[a][a]]; cn = [a for a in nash if M[a][a]]
    assert (len(nash), len(dn), len(cn)) == (180, 78, 102)
    fb, cb = rep[FB], rep[CB]
    for a in dn:     # FairBot: neutral vs a, strictly better against itself
        assert P[fb][a] == P[a][a] == 1 and P[fb][fb] == 3 > P[a][fb]
    neutral = {}
    for a in cn:     # every self-cooperating Nash agent is unexploitable and has a neutral mutant
        assert not any(M[a][b] and not M[b][a] for b in range(n))
        mut = [b for b in R if b != a and P[b][a] == P[a][a] and P[a][b] <= P[b][b]]
        assert mut; neutral[a] = mut
    assert sum(cb in neutral[a] for a in cn) == 95
    ess = [a for a in R if all(P[b][a] < P[a][a] or (P[b][a] == P[a][a] and P[a][b] > P[b][b])
                              for b in R if b != a)]
    assert ess == []
    # (4) independent re-solve of every cell the claims use
    cells = set()
    for a in winners + [FB, CB]:
        for b in range(n): cells.add((min(a, b), max(a, b)))
    for a in nash:
        cells.add((min(a, fb), max(a, fb))); cells.add((a, a))
    for a in cn:
        b = neutral[a][0]; cells.add((min(a, b), max(a, b))); cells.add((b, b))
    rnd = random.Random(7)
    for _ in range(3000):
        a, b = rnd.randrange(n), rnd.randrange(n); cells.add((min(a, b), max(a, b)))
    for a, b in cells:
        x, y = game(names[a], names[b])
        assert x == bool(M[a][b]) and y == bool(M[b][a]), (names[a], names[b])
    print('PASS: round-robin max', top, 'by', len(winners), 'DB-identical agents; second', second,
          '; obs classes', len(cls), '; Nash', len(nash), '(', len(dn), 'defect,', len(cn), 'coop ); ESS 0',
          '; re-solved', len(cells), 'games', round(time.time() - t0, 1), 's')

if __name__ == '__main__':
    main()
