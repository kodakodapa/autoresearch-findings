"""C046 r1: the 'missing' property combination of K2 first occurs at size 12.
Language L: atoms p (opponent cooperates with me), q (opponent cooperates with
DefectBot), constant F; ~, &, |, []; every atom under a box; size = syntax-tree
node count. Agents up to equivalence on finite linear GL models (K1 engine).
Properties (standard model = tail of the height chain):
  S  = cooperates with itself;  FBc = cooperates with FairBot []p;
  CBc = cooperates with CooperateBot ~F;  exploitable = cooperates with some B
  while B defects (tested against all 2815 classes of size <= 9).
Asserts:
 (1) census counts per size 1..12 (1,4,8,12,31,98,255,646,1760,4746,12880,36062);
 (2) agents with S=0, FBc=1, CBc=1 per size 4..12: 2,2,4,8,19,46,120,357,900;
     none of size <= 11 is unexploitable vs census9; exactly 3 of size 12 are;
 (3) witness W=[]([][]F|(p&(q|~[]q))) checked by an independent height-table
     solver: W defects vs W, mutual cooperation with FB and CB, and no census9
     agent exploits W;
 (4) GLS certificates (cut-free GL prover, guarded fixed points are unique)
     for the closed fixed points of W vs W, W vs FB, W vs CB, with a flipped
     candidate rejected.
Unexploitability of W against EVERY opponent is a hand argument (reasoning
evidence): W true at the tail forces p at every height >= 2.
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

W = '[]([][]F|(p&(q|~[]q)))'

def main():
    t0 = time.time()
    U, G, fU, fG = enumerate_classes(12, log=False)
    assert [len(G[n]) for n in range(1, 13)] == [1,4,8,12,31,98,255,646,1760,4746,12880,36062]
    FBm = mparse('[]p'); CBm = mparse('~F')
    opp = [c for c in fG if fG[c][0] <= 9]; assert len(opp) == 2815
    cand = {}; found = []
    for c, (n, s) in fG.items():
        if run(c, c)[0] or run(c, FBm)[0] != 1 or run(c, CBm)[0] != 1: continue
        cand[n] = cand.get(n, 0) + 1
        if any(run(c, b)[0] and not run(c, b)[1] for b in opp): continue
        found.append((n, s))
    assert [cand.get(n, 0) for n in range(1, 13)] == [0,0,0,2,2,4,8,19,46,120,357,900], cand
    found.sort()
    assert [n for n, s in found] == [12, 12, 12], found
    assert W in [s for n, s in found]
    print('census+filter ok', found, round(time.time()-t0, 1), 's')
    # (3) independent solver
    names = [fG[c][1] for c in opp]
    assert game(W, W) == (False, False)
    assert game(W, '[]p') == (True, True) and game(W, '~F') == (True, True)
    assert game(W, 'F') == (False, False)
    ex = [b for b in names if (lambda r: r[0] and not r[1])(game(W, b))]
    assert ex == [], ex
    print('independent solver ok', round(time.time()-t0, 1), 's')
    # (4) GLS certificates
    for opp_s, want in ((W, (False, False)), ('[]p', (True, True)), ('~F', (True, True))):
        assert GL['solve'](W, opp_s) == want, opp_s
    g = GL; assert not g['prove'](g['iff'](g['F'], g['box'](g['F'])))
    assert g['prove'](g['imp'](g['box'](g['imp'](g['box'](('p',)), ('p',))), g['box'](('p',))))
    print('PASS', round(time.time()-t0, 1), 's')

main()
