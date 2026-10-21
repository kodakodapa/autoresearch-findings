"""C046 r1: the A_3 winner of K4-K6/K14/K15 is a size-bound artifact too.
Census: language L (atoms p = opponent hunts stag vs me, q = opponent hunts stag vs HareBot = F;
constant F; ~,&,|,[]; every p,q under a box; size = syntax nodes), guarded classes up to size 10 modulo
equivalence on finite linear GL models (7561 classes), re-enumerated with the engine of prior check
c046_chicken_q.py. True = stag. A_k = [](p|[]^k~(p|q)) has size k+7: A_1..A_3 are census members, A_4.. not.
Asserts:
 (1) outcome counts (SS,SH,HS,HH) of A_k against the 7561 census agents, k=1..10 (formula-height solver
     game(); equal to the machine-solver matrix rows/columns for k=1..3);
 (2) SH = 543 and HH = 2087 for every k; SS = 4359, 4410, 4444, 4456, 4459, then 4459 to k=10; for k>=2 the
     only changes are HS -> SS; hence for any payoffs with a>t, score_{k+1}-score_k = dSS (a-t) > 0 for
     k<5 and = 0 for 5<=k<10; A_5 - A_3 = 15(a-t) (200 exact random payoffs);
 (3) A_5's stag/stag set is exactly the 4459 census agents that hunt stag vs StagBot ~F;
 (4) A_3 -> A_4 changes exactly 12 opponents, A_4 -> A_5 exactly 3 (listed), each HS -> SS;
 (5) A_k self-stag for k<=10; GLS certificates for A_3/A_4/A_5 vs ([]F|~[]^4F) and A_4/A_5 vs ([]F|~[]^5F).
"""
import time

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



def eq_counts(M, a, s, t, d):
    Mb = M.astype(bool); Mt = Mb.T
    U = np.where(Mb & Mt, a, np.where(Mb & ~Mt, s, np.where(~Mb & Mt, t, d)))
    BR = U == U.max(0)[None, :]
    EQ = BR & BR.T
    ss = int((EQ & Mb & Mt).sum()); hh = int((EQ & ~Mb & ~Mt).sum())
    sym = np.diag(EQ)
    return dict(tot=int(EQ.sum()), ss=ss, hh=hh, asym=int(EQ.sum()) - ss - hh, sym=int(sym.sum()),
                symss=int((sym & np.diag(Mb)).sum()), never_br=int((~BR.any(1)).sum()), symmask=sym)

# ---- exact winner partition of the normalized strict Stag Hunt triangle ----
from fractions import Fraction as Fr
def clip(poly, a, b, c):  # keep a*t + b*d + c >= 0
    out = []; m = len(poly)
    for i in range(m):
        P = poly[i]; Q = poly[(i + 1) % m]
        fp = a * P[0] + b * P[1] + c; fq = a * Q[0] + b * Q[1] + c
        if fp >= 0: out.append(P)
        if (fp > 0 and fq < 0) or (fp < 0 and fq > 0):
            s = fp / (fp - fq); out.append((P[0] + s * (Q[0] - P[0]), P[1] + s * (Q[1] - P[1])))
    return out
def area(p):
    return abs(sum(p[i][0] * p[(i + 1) % len(p)][1] - p[(i + 1) % len(p)][0] * p[i][1] for i in range(len(p)))) / 2



def A(k):
    return '[](p|%s~(p|q))' % ('[]' * k)

def main():
    t0 = time.time()
    U, G, fU, fG = enumerate_classes(10, log=False)
    counts = [len(G[k]) for k in range(1, 11)]
    assert counts == [1, 4, 8, 12, 31, 98, 255, 646, 1760, 4746], counts
    order = sorted(fG, key=lambda c: (fG[c][0], fG[c][1]))
    names = [fG[c][1] for c in order]; n = len(names)
    assert n == 7561
    nb = max(s.count('[]') for s in names); H = 4 * nb + 3
    TT, OO, S = matrix(order); M = solve_all(TT, OO, S, H)
    idx = {c: i for i, c in enumerate(order)}
    def ix(s): return idx[parse_m(s)]
    Mb = M.astype(bool)
    CB = ix('~F')
    SSexp = {1: 4359, 2: 4410, 3: 4444, 4: 4456}
    expect = {k: (SSexp.get(k, 4459), 543, 7561 - 543 - 2087 - SSexp.get(k, 4459), 2087) for k in range(1, 11)}
    codes = {}; rows = {}
    for k in range(1, 11):
        row = [game(A(k), o) for o in names]
        a = np.array([x for x, _ in row]); b = np.array([y for _, y in row])
        if k <= 3:
            i = ix(A(k)); assert names[i] == A(k)
            assert (Mb[i] == a).all() and (Mb[:, i] == b).all(), k
        else:
            assert parse_m(A(k)) not in idx
        ss, sh, hs, hh = int((a & b).sum()), int((a & ~b).sum()), int((~a & b).sum()), int((~a & ~b).sum())
        assert (ss, sh, hs, hh) == expect[k], (k, ss, sh, hs, hh)
        assert game(A(k), A(k)) == (True, True)
        codes[k] = 2 * a.astype(int) + b.astype(int); rows[k] = (a, b)
    for k in range(1, 10):
        assert ((codes[k] == 2) == (codes[1] == 2)).all()          # same SH set for all k
        if k >= 2:
            ch = np.flatnonzero(codes[k] != codes[k + 1])
            assert ((codes[k][ch] == 1) & (codes[k + 1][ch] == 3)).all()   # only HS -> SS
    a5, b5 = rows[5]
    assert ((a5 & b5) == Mb[:, CB]).all() and int(Mb[:, CB].sum()) == 4459
    from fractions import Fraction as Fr
    rnd = random.Random(46)
    for _ in range(200):
        a_ = Fr(rnd.randint(2, 999)); t_ = Fr(rnd.randint(0, int(a_) - 1)); d_ = Fr(rnd.randint(0, int(a_) - 1))
        s_ = Fr(rnd.randint(-999, 999))
        sc = {k: e[0] * a_ + e[1] * s_ + e[2] * t_ + e[3] * d_ for k, e in expect.items()}
        assert all(sc[k + 1] > sc[k] for k in range(1, 5)) and all(sc[k + 1] == sc[k] for k in range(5, 10))
        assert sc[5] - sc[3] == 15 * (a_ - t_)
    d34 = sorted(names[i] for i in np.flatnonzero(codes[3] != codes[4]))
    d45 = sorted(names[i] for i in np.flatnonzero(codes[4] != codes[5]))
    b4 = '[][][][]'; b5 = '[][][][][]'
    assert d34 == sorted(['([]F|~%sF)' % b4, '~[](p&%sF)' % b4, '~[](q&%sF)' % b4, '([]F|~%s~p)' % b4,
                          '([]F|~%s~q)' % b4, '([][]F|~%sF)' % b4, '([]~p|~%sF)' % b4, '([]~q|~%sF)' % b4,
                          '~[](p&%s~q)' % b4, '~[](q&%s~p)' % b4, '~[][](p&%sF)' % b4, '~[][](q&%sF)' % b4]), d34
    assert d45 == sorted(['([]F|~%sF)' % b5, '~[](p&%sF)' % b5, '~[](q&%sF)' % b5]), d45
    W4, W5 = '([]F|~%sF)' % b4, '([]F|~%sF)' % b5
    assert solve(A(3), W4) == (False, True)
    assert solve(A(4), W4) == (True, True)
    assert solve(A(5), W4) == (True, True)
    assert solve(A(4), W5) == (False, True)
    assert solve(A(5), W5) == (True, True)
    print('PASS: A_k census counts k=1..10; SH 543, HH 2087 fixed; score strictly increasing to k=5 then constant;'
          ' A_5-A_3=15(a-t); A_5 SS set = stag-vs-StagBot set (4459); 12 then 3 HS->SS changes; 5 GLS certificates;'
          ' %.1fs' % (time.time() - t0))

main()
