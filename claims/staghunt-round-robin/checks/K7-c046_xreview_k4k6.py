"""C046 r1 cross-review of r2's K4, K5, K6 (Stag Hunt round robin) plus the StagBot split of A3's gain.
Census: language L (atoms p = opponent hunts stag vs me, q = opponent hunts stag vs HareBot = DB = F;
constant F; ~,&,|,[]; every p,q under a box; size = syntax nodes), guarded classes up to size 10
modulo equivalence on finite linear GL models (7561 classes), re-enumerated here with the engine of
prior check c046_chicken_q.py (a different file from r2's pinned c046_games10.py). True = stag.
Round robin: each class meets every class once, itself included. Row payoffs (SS,SH,HS,HH).
Asserts (exact, Fractions):
 (1) A3 = [](p|[][][]~(p|q)) has outcome counts (4444,543,487,2087); FairBot []p has (2417,0,1763,3381);
     the 11 FairBot->A3 outcome transitions equal r2's K4 table; 23411-21719 = 1692 at (4,0,3,2);
 (2) K6: for payoffs (4,0,t,2), A3 is the unique maximiser on all of 2<t<4 (score 21950+487t);
 (3) K5: for (4,0,3,h), 0<h<4, the upper envelope has breakpoints 116/1423, 15/22, 2537/1001,
     4079/1071, 463/116 with r2's seven winners and score lines; only the two lines meet at each breakpoint;
 (4) StagBot split: 4459 opponents hunt stag vs StagBot ~F. A3 ends stag/stag with 4444 of them
     (all its SS cells), HS with the other 15 (all of size >= 9 and containing []^4); against them A3 gains
     +3848 over FairBot, and against the other 3102 it loses 2156 net (3848-2156 = 1692);
     A3 hunts stag vs both StagBot and HareBot;
 (5) rows and columns of FB and all 8 envelope winners are re-solved against every census agent by an
     independent formula-level height solver; 4 headline cells carry GLS certificates.
"""

import sys, time, random
import numpy as np

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


# ---- GLS certificate prover (adapted from prior sk/gls_matrix_certs.py) ----
GLS_NS={}
exec(compile("import functools\nF = ('F',)\ndef imp(a, b): return ('imp', a, b)\ndef neg(a): return imp(a, F)\ndef box(a): return ('box', a)\ndef conj(a, b): return neg(imp(a, neg(b)))\ndef disj(a, b): return imp(neg(a), b)\nT = neg(F)\ndef iff(a, b): return conj(imp(a, b), imp(b, a))\ndef boxn(x, n):\n    for _ in range(n): x = box(x)\n    return x\nimport functools\n@functools.lru_cache(maxsize=None)\ndef prove_seq(L, R):\n    if F in L or L & R: return True\n    for f in L:\n        if f[0] == 'imp':\n            L2 = L - {f}\n            return prove_seq(L2, R | {f[1]}) and prove_seq(L2 | {f[2]}, R)\n    for f in R:\n        if f[0] == 'imp':\n            return prove_seq(L | {f[1]}, (R - {f}) | {f[2]})\n    boxedL = frozenset(f for f in L if f[0] == 'box')\n    unb = frozenset(f[1] for f in boxedL)\n    for f in R:\n        if f[0] == 'box' and prove_seq(boxedL | unb | {f}, frozenset({f[1]})): return True\n    return False\ndef prove(f): return prove_seq(frozenset(), frozenset({f}))\ndef gparse(s):\n    def p(i):\n        c = s[i]\n        if c == 'F': return F, i + 1\n        if c in 'pq': return (c,), i + 1\n        if c == '~': m, j = p(i + 1); return neg(m), j\n        if s.startswith('[]', i): m, j = p(i + 2); return box(m), j\n        a, j = p(i + 1); op = s[j]; b, k = p(j + 1); assert s[k] == ')'\n        return (conj if op == '&' else disj)(a, b), k + 1\n    t, j = p(0); assert j == len(s); return t\ndef subst(f, pv, qv):\n    t = f[0]\n    if t == 'p': return pv\n    if t == 'q': return qv\n    if t == 'F': return f\n    return (t,) + tuple(subst(x, pv, qv) for x in f[1:])\ndef ev(f, h, tr, vals):   # tr: dict name->list ; atoms ('v',name)\n    t = f[0]\n    if t == 'F': return False\n    if t == 'v': return tr[f[1]][h]\n    if t == 'imp': return (not ev(f[1], h, tr, vals)) or ev(f[2], h, tr, vals)\n    if t == 'box': return all(ev(f[1], g, tr, vals) for g in range(h))\n    raise ValueError(f)\ndef closed(trace):\n    m = len(trace) - 1\n    while m > 0 and trace[m - 1] == trace[-1]: m -= 1\n    if m == 0: return T if trace[-1] else F\n    parts = [conj(boxn(F, h + 1), neg(boxn(F, h))) for h in range(m) if trace[h]]\n    if trace[-1]: parts.append(neg(boxn(F, m)))\n    out = parts[0]\n    for q in parts[1:]: out = disj(out, q)\n    return out\ndef nb(f): return (f[0] == 'box') + sum(nb(x) for x in f[1:] if isinstance(x, tuple))\ndef solve(sa, sb):\n    A, B = gparse(sa), gparse(sb)\n    H = 2 * (nb(A) + nb(B)) + 4\n    VX, VY = ('v', 'x'), ('v', 'y')\n    # closed q-values: opponent vs DB (all-F inputs)\n    def vsDB(f):\n        tr = {}; t = []\n        for h in range(H):\n            t.append(ev(subst(f, F, F), h, {}, None))\n        return t\n    za, zb = vsDB(A), vsDB(B)\n    CA, CB_ = closed(za), closed(zb)\n    ex = subst(A, VY, CB_); ey = subst(B, VX, CA)\n    tr = {'x': [], 'y': []}\n    for h in range(H):\n        xa = ev(ex, h, tr, None); yb = ev(ey, h, tr, None)\n        tr['x'].append(xa); tr['y'].append(yb)\n    cx, cy = closed(tr['x']), closed(tr['y'])\n    sub = lambda f: subst_v(f, cx, cy)\n    assert prove(iff(cx, sub(ex))) and prove(iff(cy, sub(ey)))\n    # mutation control: flipping a candidate must be rejected\n    assert not (prove(iff(neg(cx), sub(ex))) and prove(iff(cy, sub(ey))))\n    assert not (prove(iff(cx, subst_v(ex, neg(cx), cy))) and prove(iff(neg(cx), subst_v(ex, neg(cx), cy))))\n    return tr['x'][-1], tr['y'][-1]\ndef subst_v(f, cx, cy):\n    if f[0] == 'v': return cx if f[1] == 'x' else cy\n    if f[0] == 'F': return f\n    return (f[0],) + tuple(subst_v(x, cx, cy) for x in f[1:])\n","gls","exec"),GLS_NS)
solve=GLS_NS["solve"]

import subprocess, shutil, os
def lean():
    for c in (shutil.which('lean'), '/opt/elan/bin/lean', os.path.expanduser('~/.elan/bin/lean')):
        if c and os.path.exists(c): return c
    raise AssertionError('lean binary not found')
def run(s):
    r = subprocess.run([lean(), '--stdin'], input=s, capture_output=True, text=True, timeout=100)
    return r.returncode, r.stdout + r.stderr

def parse_m(s):
    def m(t):
        k=t[0]
        if k=='F': return BOT
        if k=='T': return neg(BOT)
        if k=='p': return P
        if k=='q': return Q
        if k=='~': return neg(m(t[1]))
        if k=='[]': return box(m(t[1]))
        return (AND if k=='&' else OR)(m(t[1]),m(t[2]))
    return m(parse_tree(s))

def matrix(order):
    n=len(order); S=max(len(c[0]) for c in order)
    TT=np.zeros((n,S,4),np.int64); OO=np.zeros((n,S),np.int8)
    for k,(T,O) in enumerate(order):
        assert all(len(set(r))==1 for r in O)
        for s in range(len(T)): TT[k,s]=T[s]; OO[k,s]=O[s][0]
    return TT,OO,S
def solve_all(TT,OO,S,H,chunk=200):
    n=len(TT); z=np.zeros((n,H+1),np.int8); s=np.zeros(n,np.int64); ar=np.arange(n)
    for h in range(H+1): z[:,h]=OO[ar,s]; s=TT[ar,s,0]
    TTf=TT.reshape(-1); OOf=OO.reshape(-1); M=np.zeros((n,n),np.int8)
    for a0 in range(0,n,chunk):
        A=np.arange(a0,min(n,a0+chunk)); AA=np.repeat(A,n); BB=np.tile(ar,len(A))
        sA=np.zeros(len(AA),np.int64); sB=np.zeros(len(AA),np.int64); hist=[]
        for h in range(H+1):
            xa=OOf[AA*S+sA]; yb=OOf[BB*S+sB]; hist.append(xa)
            if h==H: break
            iA=yb+2*z[BB,h]; iB=xa+2*z[AA,h]
            sA=TTf[(AA*S+sA)*4+iA]; sB=TTf[(BB*S+sB)*4+iB]
        for k in range(1,5): assert (hist[-1]==hist[-1-k]).all()
        M[A]=hist[-1].reshape(len(A),n)
    return M


from fractions import Fraction as Fr

def envelope(c0, c1, lo, hi, names):
    lines = {}
    for i in range(len(c0)): lines.setdefault((int(c0[i]), int(c1[i])), []).append(i)
    L = sorted(lines); x = Fr(lo); out = []
    while x < hi:
        best = max(L, key=lambda l: (l[0] + l[1] * x, l[1]))
        nxt = Fr(hi)
        for l in L:
            if l[1] > best[1]:
                xb = Fr(best[0] - l[0], l[1] - best[1])
                if x < xb < nxt: nxt = xb
        if nxt < hi:  # only two distinct lines are maximal at the breakpoint
            top = max(l[0] + l[1] * nxt for l in L)
            assert sum(l[0] + l[1] * nxt == top for l in L) == 2
        out.append((x, best, sorted(names[i] for i in lines[best]))); x = nxt
    return out

def main():
    t0 = time.time()
    U, G, fU, fG = enumerate_classes(10, log=False)
    counts = [len(G[k]) for k in range(1, 11)]
    assert counts == [1, 4, 8, 12, 31, 98, 255, 646, 1760, 4746], counts
    order = sorted(fG, key=lambda c: (fG[c][0], fG[c][1]))
    names = [fG[c][1] for c in order]; sz = np.array([fG[c][0] for c in order]); n = len(names)
    assert n == 7561
    nb = max(s.count('[]') for s in names); H = 4 * nb + 3
    TT, OO, S = matrix(order); M = solve_all(TT, OO, S, H).astype(np.int64); Mt = M.T
    idx = {c: i for i, c in enumerate(order)}
    def ix(s): return idx[parse_m(s)]
    SS = (M * Mt).sum(1); SH = (M * (1 - Mt)).sum(1); HS = ((1 - M) * Mt).sum(1); HH = ((1 - M) * (1 - Mt)).sum(1)
    A3, FB, CB, DB = ix('[](p|[][][]~(p|q))'), ix('[]p'), ix('~F'), ix('F')
    assert (SS[A3], SH[A3], HS[A3], HH[A3]) == (4444, 543, 487, 2087)
    assert (SS[FB], SH[FB], HS[FB], HH[FB]) == (2417, 0, 1763, 3381)
    o = lambda i, j: ('S' if M[i, j] else 'H') + ('S' if M[j, i] else 'H')
    tr = {}
    for j in range(n): tr[(o(FB, j), o(A3, j))] = tr.get((o(FB, j), o(A3, j)), 0) + 1
    assert tr == {('HH', 'HH'): 1370, ('HH', 'HS'): 47, ('HH', 'SH'): 321, ('HH', 'SS'): 1643,
                  ('HS', 'HH'): 543, ('HS', 'HS'): 436, ('HS', 'SH'): 222, ('HS', 'SS'): 562,
                  ('SS', 'HH'): 174, ('SS', 'HS'): 4, ('SS', 'SS'): 2239}, tr
    sc = lambda i: 4 * SS[i] + 3 * HS[i] + 2 * HH[i]
    assert sc(A3) == 23411 and sc(FB) == 21719
    # (2) K6
    e = envelope(4 * SS + 2 * HH, HS, 2, 4, names)
    assert e == [(Fr(2), (21950, 487), ['[](p|[][][]~(p|q))'])], e
    # (3) K5
    e = envelope(4 * SS + 3 * HS, HH, 0, 4, names)
    want = [(Fr(0), (19368, 642), ['([][]~q|~[]~p)']), (Fr(116, 1423), (19252, 2065), ['[](p|[][][][][]~q)']),
            (Fr(15, 22), (19237, 2087), ['[](p|[][][]~(p|q))']), (Fr(2537, 1001), (16700, 3088), ['([]p|~[](~p|[]p))']),
            (Fr(4079, 1071), (12621, 4159), ['(~[]~p&[](p|[]p))', '(~[]~q&[](p|[]p))']),
            (Fr(463, 116), (11695, 4391), ['(~[][]F&[](p|[]p))'])]
    assert e == want, e
    winners = sorted({w for r in want for w in r[2]})
    # (4) StagBot split
    pay = {'SS': 4, 'SH': 0, 'HS': 3, 'HH': 2}
    Jc = [j for j in range(n) if M[j, CB] == 1]; Jn = [j for j in range(n) if M[j, CB] == 0]
    assert len(Jc) == 4459 and len(Jn) == 3102 and M[A3, CB] == 1 and M[A3, DB] == 1
    assert sum(o(A3, j) == 'SS' for j in Jc) == 4444 == SS[A3]
    ex = [j for j in Jc if o(A3, j) != 'SS']
    assert len(ex) == 15 and all(o(A3, j) == 'HS' and sz[j] >= 9 and '[][][][]' in names[j] for j in ex)
    gc = sum(pay[o(A3, j)] - pay[o(FB, j)] for j in Jc); gn = sum(pay[o(A3, j)] - pay[o(FB, j)] for j in Jn)
    assert all(pay[o(A3, j)] >= pay[o(FB, j)] for j in Jc)
    assert (gc, gn) == (3848, -2156) and gc + gn == 1692
    # (5) independent re-solve
    cells = 0
    for s in winners + ['[]p']:
        a = ix(s)
        for b in range(n):
            x, y = game(names[a], names[b]); cells += 1
            assert x == bool(M[a, b]) and y == bool(M[b, a]), (names[a], names[b])
    heads = [('[](p|[][][]~(p|q))', '~F'), ('[](p|[][][]~(p|q))', 'F'), ('[](p|[][][]~(p|q))', '[]q'),
             ('[](p|[][][]~(p|q))', '([]F|~[][][][]F)')]
    for a, b in heads:
        x, y = solve(a, b); assert (x, y) == (bool(M[ix(a), ix(b)]), bool(M[ix(b), ix(a)])), (a, b)
    assert solve('[](p|[][][]~(p|q))', '[]q') == (True, True)
    assert solve('[](p|[][][]~(p|q))', '([]F|~[][][][]F)') == (False, True)
    print('PASS xreview K4/K5/K6: %d classes, envelopes and transitions match, StagBot split 3848-2156=1692, '
          '%d cells re-solved, %d GLS certs, %.1fs' % (n, cells, len(heads), time.time() - t0))

if __name__ == '__main__':
    main()
