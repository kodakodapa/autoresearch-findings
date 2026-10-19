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
    U, G, fU, fG = enumerate_classes(9, log=False)
    counts = [len(G[n]) for n in range(1, 10)]
    assert counts == [1, 4, 8, 12, 31, 98, 255, 646, 1760], counts
    assert all(is_moore(c) for c in fG)
    order = sorted(fG, key=lambda c: (fG[c][0], fG[c][1]))
    raw = None
    for pth in PATHS:
        try: raw = open(pth, 'rb').read(); break
        except OSError: pass
    assert raw is not None, 'dataset missing'
    assert hashlib.sha256(raw).hexdigest() == SHA
    d = json.loads(raw)
    names = d['agents']; n = len(names)
    assert names == [fG[c][1] for c in order] and d['sizes'] == [fG[c][0] for c in order]
    bits = bytes.fromhex(d['M_packbits_hex'])
    def Mv(a, b):
        k = a * n + b
        return (bits[k >> 3] >> (7 - (k & 7))) & 1
    idx = {c: i for i, c in enumerate(order)}
    named = {'DB': 'F', 'CB': '~F', 'FB': '[]p', 'PB': '([]p&[]([]F|~q))',
             'F2': '[][]p', 'P0': '([]p&[]~q)'}
    ix = {k: idx[parse(v)] for k, v in named.items()}
    # (3) independent re-solve
    checked = 0
    cells = [(ix[k], b) for k in ('DB', 'CB', 'FB', 'PB', 'F2', 'P0') for b in range(n)]
    rnd = random.Random(20261017)
    cells += [(rnd.randrange(n), rnd.randrange(n)) for _ in range(2000)]
    for a, b in cells:
        x, y = game(names[a], names[b])
        assert x == bool(Mv(a, b)) and y == bool(Mv(b, a)), (names[a], names[b])
        checked += 1
    # known literature rows (Barasz et al. 2014): FB/PB mutual C, PB defects vs CB
    assert Mv(ix['FB'], ix['FB']) and Mv(ix['PB'], ix['PB']) and Mv(ix['FB'], ix['PB']) and Mv(ix['PB'], ix['FB'])
    assert not Mv(ix['PB'], ix['CB']) and Mv(ix['FB'], ix['CB'])
    # (4) properties for every agent, relative to this census of 2815 opponents
    combos = {}
    for a in range(n):
        row = [Mv(a, b) for b in range(n)]; col = [Mv(b, a) for b in range(n)]
        key = (row[a], int(any(r and not c for r, c in zip(row, col))), row[ix['FB']], 1 - row[ix['CB']])
        combos.setdefault(key, a)
    assert len(combos) == 15 and (0, 0, 1, 0) not in combos
    # smallest agent cooperating with itself and FB, defecting vs CB, unexploitable: PB, size 8
    a = combos[(1, 0, 1, 1)]
    assert d['sizes'][a] == 8 and order[a] == parse(named['PB'])
    print('PASS: counts', counts, '; cells re-solved', checked, '; combos', len(combos), round(time.time() - t0, 1), 's')

if __name__ == '__main__':
    main()
