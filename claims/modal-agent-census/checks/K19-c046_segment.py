"""C046 r1: threshold law for self-defecting FairBot-cooperators, and its first
known failure.
Language L: atoms p (opponent cooperates with me), q (opponent cooperates with
DefectBot), constant F; ~, &, |, []; every atom under a box; size = syntax-tree
node count; agents up to equivalence on finite linear GL models (K1 engine).
F_k = []^k p (F_1 = FairBot), P_i = []p & []([]^i F | ~q) (P_0 = []p&[]~q).
'X CC Y' = both cooperate at the tail.
Asserts:
 (1) guarded class counts to size 14 (..., 100823, 279115);
 (2) LAW up to size 14: each of the 9979 agents with S=0 (defects vs itself) and
     CC with FairBot has CC-set {k<=8 : X CC F_k} = {1..a} and
     {i<=8 : X CC P_i} = {b..8}, and a < b whenever both are nonempty;
 (3) Y = []([][]F|(p&(q|~[](q&[][][]F)))) (size 17) breaks the law: S=0, CC with
     FairBot, CooperateBot, F_1 and F_k for k=4..12, D with F_2, F_3, CC with P_i
     iff i>=3 (i<=12), D vs DefectBot; it satisfies the universal unexploitability
     criterion U (K17), confirmed on random eventually-defecting traces;
 (4) Y's outcomes re-derived by an independent string height-table solver, and
     GLS fixed-point certificates (with flipped-candidate controls) for Y vs
     Y, F_1, F_2, F_3, F_4, P_2, P_3, CooperateBot.
The off-census statement 'law holds to size 15' (28485 agents) is from work/seg15.py
(16 min, not in this check). Boolean, exact; no tolerances."""
import sys, pickle, hashlib, time
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
    # U at the final size is not needed for guarded classes of size N
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
                if n < N: addU(n, neg(c), '~' + s)
                b = box(c); addG(n, b, '[]' + s)
                if n < N: addU(n, b, '[]' + s)
            for c in G[n-1]:
                addG(n, neg(c), '~' + firstG[c][1])
            # binary: sizes i + j = n-1
            for i in range(1, n-1):
                j = n - 1 - i
                if i > j: break
                for (pool, first, add) in (((U, firstU, addU), (G, firstG, addG)) if n < N else ((G, firstG, addG),)):
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

GLS_SRC = "F = ('F',)\ndef imp(a, b): return ('imp', a, b)\ndef neg(a): return imp(a, F)\ndef box(a): return ('box', a)\ndef conj(a, b): return neg(imp(a, neg(b)))\ndef disj(a, b): return imp(neg(a), b)\nT = neg(F)\ndef iff(a, b): return conj(imp(a, b), imp(b, a))\ndef boxn(x, n):\n    for _ in range(n): x = box(x)\n    return x\nimport functools\n@functools.lru_cache(maxsize=None)\ndef prove_seq(L, R):\n    if F in L or L & R: return True\n    for f in L:\n        if f[0] == 'imp':\n            L2 = L - {f}\n            return prove_seq(L2, R | {f[1]}) and prove_seq(L2 | {f[2]}, R)\n    for f in R:\n        if f[0] == 'imp':\n            return prove_seq(L | {f[1]}, (R - {f}) | {f[2]})\n    boxedL = frozenset(f for f in L if f[0] == 'box')\n    unb = frozenset(f[1] for f in boxedL)\n    for f in R:\n        if f[0] == 'box' and prove_seq(boxedL | unb | {f}, frozenset({f[1]})): return True\n    return False\ndef prove(f): return prove_seq(frozenset(), frozenset({f}))\ndef parse(s):\n    def p(i):\n        c = s[i]\n        if c == 'F': return F, i + 1\n        if c in 'pq': return (c,), i + 1\n        if c == '~': m, j = p(i + 1); return neg(m), j\n        if s.startswith('[]', i): m, j = p(i + 2); return box(m), j\n        a, j = p(i + 1); op = s[j]; b, k = p(j + 1); assert s[k] == ')'\n        return (conj if op == '&' else disj)(a, b), k + 1\n    t, j = p(0); assert j == len(s); return t\ndef subst(f, pv, qv):\n    t = f[0]\n    if t == 'p': return pv\n    if t == 'q': return qv\n    if t == 'F': return f\n    return (t,) + tuple(subst(x, pv, qv) for x in f[1:])\ndef ev(f, h, tr, vals):   # tr: dict name->list ; atoms ('v',name)\n    t = f[0]\n    if t == 'F': return False\n    if t == 'v': return tr[f[1]][h]\n    if t == 'imp': return (not ev(f[1], h, tr, vals)) or ev(f[2], h, tr, vals)\n    if t == 'box': return all(ev(f[1], g, tr, vals) for g in range(h))\n    raise ValueError(f)\ndef closed(trace):\n    m = len(trace) - 1\n    while m > 0 and trace[m - 1] == trace[-1]: m -= 1\n    if m == 0: return T if trace[-1] else F\n    parts = [conj(boxn(F, h + 1), neg(boxn(F, h))) for h in range(m) if trace[h]]\n    if trace[-1]: parts.append(neg(boxn(F, m)))\n    out = parts[0]\n    for q in parts[1:]: out = disj(out, q)\n    return out\ndef nb(f): return (f[0] == 'box') + sum(nb(x) for x in f[1:] if isinstance(x, tuple))\ndef solve(sa, sb):\n    A, B = parse(sa), parse(sb)\n    H = 2 * (nb(A) + nb(B)) + 4\n    VX, VY = ('v', 'x'), ('v', 'y')\n    # closed q-values: opponent vs DB (all-F inputs)\n    def vsDB(f):\n        tr = {}; t = []\n        for h in range(H):\n            t.append(ev(subst(f, F, F), h, {}, None))\n        return t\n    za, zb = vsDB(A), vsDB(B)\n    CA, CB_ = closed(za), closed(zb)\n    ex = subst(A, VY, CB_); ey = subst(B, VX, CA)\n    tr = {'x': [], 'y': []}\n    for h in range(H):\n        xa = ev(ex, h, tr, None); yb = ev(ey, h, tr, None)\n        tr['x'].append(xa); tr['y'].append(yb)\n    cx, cy = closed(tr['x']), closed(tr['y'])\n    sub = lambda f: subst_v(f, cx, cy)\n    assert prove(iff(cx, sub(ex))) and prove(iff(cy, sub(ey)))\n    # mutation control: flipping a candidate must be rejected\n    assert not (prove(iff(neg(cx), sub(ex))) and prove(iff(cy, sub(ey))))\n    assert not (prove(iff(cx, subst_v(ex, neg(cx), cy))) and prove(iff(neg(cx), subst_v(ex, neg(cx), cy))))\n    return tr['x'][-1], tr['y'][-1]\ndef subst_v(f, cx, cy):\n    if f[0] == 'v': return cx if f[1] == 'x' else cy\n    if f[0] == 'F': return f\n    return (f[0],) + tuple(subst_v(x, cx, cy) for x in f[1:])\n"
GL = {}
exec(GLS_SRC, GL)

def run(A, B):
    (TA, OA), (TB, OB) = A, B
    sA = sB = dA = dB = 0; seen = set()
    while True:
        st = (sA, sB, dA, dB)
        x = OA[sA][0]; y = OB[sB][0]; zA = OA[dA][0]; zB = OB[dB][0]
        if st in seen: return x, y
        seen.add(st)
        sA, sB, dA, dB = TA[sA][y+2*zB], TB[sB][x+2*zA], TA[dA][0], TB[dB][0]

def mparse(s):
    def p(i):
        c = s[i]
        if c == 'F': return BOT, i+1
        if c == 'p': return P, i+1
        if c == 'q': return Q, i+1
        if c == '~': m, j = p(i+1); return neg(m), j
        if s.startswith('[]', i): m, j = p(i+2); return box(m), j
        a, j = p(i+1); op = s[j]; b, k = p(j+1); assert s[k] == ')'
        return (AND(a, b) if op == '&' else OR(a, b)), k+1
    m, j = p(0); assert j == len(s); return m


def univ_unexpl(m):
    T, O = m
    for s0 in range(len(T)):
        for c in (0, 2):
            s = s0; seen = []
            while s not in seen: seen.append(s); s = T[s][c]
            cyc = seen[seen.index(s):]
            if all(O[t][c] == 1 for t in cyc): return False
    return True

def lit_eval(t, h, pt, qt):
    k = t[0]
    if k == 'F': return False
    if k == 'p': return pt[h]
    if k == 'q': return qt[h]
    if k == '~': return not lit_eval(t[1], h, pt, qt)
    if k == '&': return lit_eval(t[1], h, pt, qt) and lit_eval(t[2], h, pt, qt)
    if k == '|': return lit_eval(t[1], h, pt, qt) or lit_eval(t[2], h, pt, qt)
    if k == '[]': return all(lit_eval(t[1], g, pt, qt) for g in range(h))

Y = '[]([][]F|(p&(q|~[](q&[][][]F))))'

def size(s):
    return sum(1 for c in s if c in 'Fpq~&|') + s.count('[]')

def bx(k, x): return '[]' * k + x
def Fk(k): return bx(k, 'p')
def Pi(i): return '([]p&[](' + bx(i, 'F') + '|~q))' if i else '([]p&[]~q)'

def cc(a, b):
    x, y = run(a, b); return x & y

def main():
    import random
    t0 = time.time()
    N = 14
    U, G, fU, fG = enumerate_classes(N, log=False)
    del U, fU
    assert [len(G[n]) for n in range(1, N+1)] == [1,4,8,12,31,98,255,646,1760,4746,12880,36062,100823,279115]
    print('census', round(time.time()-t0, 1), 's', flush=True)
    FBm = mparse('[]p'); CBm = mparse('~F'); DBm = mparse('F')
    Fm = {k: mparse(Fk(k)) for k in range(1, 13)}
    Pm = {i: mparse(Pi(i)) for i in range(0, 13)}
    nlaw = 0
    for c, (n, s) in fG.items():
        if run(c, c)[0] or not cc(c, FBm): continue
        nlaw += 1
        fs = [k for k in range(1, 9) if cc(c, Fm[k])]
        ps = [i for i in range(0, 9) if cc(c, Pm[i])]
        assert fs == list(range(1, len(fs) + 1)), (s, fs)
        assert ps == list(range(9 - len(ps), 9)), (s, ps)
        assert not fs or not ps or max(fs) < min(ps), (s, fs, ps)
    assert nlaw == 9979, nlaw
    print('law ok on', nlaw, round(time.time()-t0, 1), 's', flush=True)
    # (3) the size-17 counterexample
    assert size(Y) == 17
    ym = mparse(Y)
    assert run(ym, ym) == (0, 0) and cc(ym, FBm) and cc(ym, CBm) and run(ym, DBm)[0] == 0
    fs = [k for k in range(1, 13) if cc(ym, Fm[k])]
    ps = [i for i in range(0, 13) if cc(ym, Pm[i])]
    assert fs == [1] + list(range(4, 13)), fs
    assert ps == list(range(3, 13)), ps
    for k in (2, 3): assert run(ym, Fm[k]) == (0, 0)
    assert univ_unexpl(ym)
    # (4) independent string solver
    assert game(Y, Y) == (False, False)
    assert game(Y, '~F') == (True, True) and game(Y, 'F')[0] is False
    for k in range(1, 13):
        assert game(Y, Fk(k)) == ((k == 1 or k >= 4),) * 2, k
    for i in range(0, 13):
        assert game(Y, Pi(i)) == ((i >= 3),) * 2, i
    rng = random.Random(17); t = parse_tree(Y)
    for _ in range(3000):
        L = rng.randint(1, 12); H = L + 30
        pt = [rng.random() < .5 for _ in range(L)] + [False] * 30
        qc = rng.random() < .5
        qt = [rng.random() < .5 for _ in range(L)] + [qc] * 30
        assert not all(lit_eval(t, g, pt, qt) for g in range(H - 6, H))
    print('Y ok', round(time.time()-t0, 1), 's', flush=True)
    # GLS certificates
    for opp in [Y, Fk(1), Fk(2), Fk(3), Fk(4), Pi(2), Pi(3), '~F']:
        x, y = GL['solve'](Y, opp)
        assert (x, y) == game(Y, opp), opp
        print('GLS', opp, x, y, round(time.time()-t0, 1), 's', flush=True)
    print('PASS', round(time.time()-t0, 1), 's')

main()
