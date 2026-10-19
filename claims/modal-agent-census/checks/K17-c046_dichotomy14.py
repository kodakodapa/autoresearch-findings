"""C046 r1: dichotomy for K6's property combination, all agents up to size 14.
Language L: atoms p (opponent cooperates with me), q (opponent cooperates with
DefectBot), constant F; ~, &, |, []; every atom under a box; size = syntax-tree
node count. Agents up to equivalence on finite linear GL models (K1 engine;
closed GL fixed points are letter-free, so play is decided on the height chain).
Combination: S=0 (defects vs itself), cooperates with FairBot []p and with
CooperateBot ~F (tail values).
Criterion U (universal unexploitability, sound for every modal opponent): in the
agent's minimized Mealy machine, from no state does constant input p=0 (q fixed
0 or 1) lead to a cycle whose outputs are all 1. Any game tail in which the
opponent defects (p eventually 0, q eventually constant) is such a run, so
U implies the agent never cooperates while the opponent defects.
Asserts:
 (1) guarded class counts per size 1..14 (..., 36062, 100823, 279115);
 (2) combination members per size 4..14: 2,2,4,8,19,46,120,357,900,2468,7032;
 (3) U holds for exactly 0 members of size <=11 and 3, 19, 75 of sizes 12,13,14
     (list pinned by sha256);
 (4) every member failing U is exploited (it cooperates, opponent defects) by
     one of four size<=3 agents: []~p, []p, []q, []F;
 (5) independent height-table solver (formula strings, no machines) re-checks
     400 random exploit witnesses and the combination properties of all 97 U agents;
     an independent literal evaluator finds no exploiting trace for the 97 on
     random eventually-defecting opponent traces.
Boolean, exact; no tolerances."""
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

SHA_U = 'd9bb03ac40552c50c07d6741b895735d4dba5f979e6a223f24916178c18c2208'

def main():
    import random
    t0 = time.time()
    N = 14
    U, G, fU, fG = enumerate_classes(N, log=False)
    del U, fU
    assert [len(G[n]) for n in range(1, N+1)] == [1,4,8,12,31,98,255,646,1760,4746,12880,36062,100823,279115]
    print('census', round(time.time()-t0, 1), 's', flush=True)
    FBm = mparse('[]p'); CBm = mparse('~F')
    OPP = ['[]~p', '[]p', '[]q', '[]F']; om = [mparse(s) for s in OPP]
    cand = {}; uset = []; wit = []
    for c, (n, s) in fG.items():
        if run(c, c)[0] or run(c, FBm)[0] != 1 or run(c, CBm)[0] != 1: continue
        cand[n] = cand.get(n, 0) + 1
        if univ_unexpl(c): uset.append((n, s)); continue
        for o, b in zip(OPP, om):
            r = run(c, b)
            if r[0] and not r[1]: wit.append((s, o)); break
        else: raise AssertionError('no exploiter among four: ' + s)
    assert [cand.get(n, 0) for n in range(1, N+1)] == [0,0,0,2,2,4,8,19,46,120,357,900,2468,7032], cand
    uset.sort()
    cnt = {}
    for n, s in uset: cnt[n] = cnt.get(n, 0) + 1
    assert cnt == {12: 3, 13: 19, 14: 75}, cnt
    h = hashlib.sha256('\n'.join(s for n, s in uset).encode()).hexdigest()
    print('U list sha256', h)
    if SHA_U: assert h == SHA_U
    assert '[]([][]F|(p&(q|~[]q)))' in [s for n, s in uset]
    print('dichotomy ok', len(wit), 'witnessed', round(time.time()-t0, 1), 's', flush=True)
    rng = random.Random(46)
    for s, o in rng.sample(wit, 400):
        assert game(s, o) == (True, False), (s, o)
    for n, s in uset:
        assert game(s, s)[0] is False and game(s, '[]p')[0] is True and game(s, '~F')[0] is True, s
        t = parse_tree(s)
        for _ in range(150):
            L = rng.randint(1, 12); H = L + 30
            pt = [rng.random() < .5 for _ in range(L)] + [False] * 30
            qc = rng.random() < .5
            qt = [rng.random() < .5 for _ in range(L)] + [qc] * 30
            assert not all(lit_eval(t, g, pt, qt) for g in range(H - 6, H)), s
    # negative control: the same trace test does find exploiting traces for
    # members failing U (so the test above is not vacuous)
    hits = 0
    for s, o in rng.sample(wit, 40):
        t = parse_tree(s)
        for _ in range(150):
            L = rng.randint(1, 12); H = L + 30
            pt = [rng.random() < .5 for _ in range(L)] + [False] * 30
            qc = rng.random() < .5
            qt = [rng.random() < .5 for _ in range(L)] + [qc] * 30
            if all(lit_eval(t, g, pt, qt) for g in range(H - 6, H)): hits += 1; break
    assert hits >= 30, hits
    print('controls', hits, '/40', round(time.time()-t0, 1), 's')
    print('PASS', round(time.time()-t0, 1), 's')

main()
