"""H family, bounded search size <=15. GLS engine embedded from sk via r2 K13; no data files."""
CERT_SOURCE='"""C046 sk: GLS proof certificates for random cells of r1\'s pinned census9 matrix (K1).\nIndependent route: re-parse agent strings, build x=A(B), y=B(A) with q:=B(DB) etc. as\nclosed formulas, get candidates from a naive height table, and PROVE x<->A[p:=y,q:=B[F,F]],\ny<->B[p:=x,q:=A[F,F]] in GLS (cut-free Valentini-style search, reflection-free, GL only);\nby uniqueness of guarded fixed points the proved candidates are the fixed points.\nThen compare standard-model action (tail) with the pinned matrix. Boolean, exact."""\nimport json, hashlib, random, sys, time\nPATHS = [\'/run/agents/r1/census/census9.json\', \'/work/agents/r1/census/census9.json\']\nSHA = \'82b872829655bbcc898e1e03213ff3f0f44da86a720b2fa9c9ad7c8992d6c6e2\'\nF = (\'F\',)\ndef imp(a, b): return (\'imp\', a, b)\ndef neg(a): return imp(a, F)\ndef box(a): return (\'box\', a)\ndef conj(a, b): return neg(imp(a, neg(b)))\ndef disj(a, b): return imp(neg(a), b)\nT = neg(F)\ndef iff(a, b): return conj(imp(a, b), imp(b, a))\ndef boxn(x, n):\n    for _ in range(n): x = box(x)\n    return x\nimport functools\n@functools.lru_cache(maxsize=None)\ndef prove_seq(L, R):\n    if F in L or L & R: return True\n    for f in L:\n        if f[0] == \'imp\':\n            L2 = L - {f}\n            return prove_seq(L2, R | {f[1]}) and prove_seq(L2 | {f[2]}, R)\n    for f in R:\n        if f[0] == \'imp\':\n            return prove_seq(L | {f[1]}, (R - {f}) | {f[2]})\n    boxedL = frozenset(f for f in L if f[0] == \'box\')\n    unb = frozenset(f[1] for f in boxedL)\n    for f in R:\n        if f[0] == \'box\' and prove_seq(boxedL | unb | {f}, frozenset({f[1]})): return True\n    return False\ndef prove(f): return prove_seq(frozenset(), frozenset({f}))\ndef parse(s):\n    def p(i):\n        c = s[i]\n        if c == \'F\': return F, i + 1\n        if c in \'pq\': return (c,), i + 1\n        if c == \'~\': m, j = p(i + 1); return neg(m), j\n        if s.startswith(\'[]\', i): m, j = p(i + 2); return box(m), j\n        a, j = p(i + 1); op = s[j]; b, k = p(j + 1); assert s[k] == \')\'\n        return (conj if op == \'&\' else disj)(a, b), k + 1\n    t, j = p(0); assert j == len(s); return t\ndef subst(f, pv, qv):\n    t = f[0]\n    if t == \'p\': return pv\n    if t == \'q\': return qv\n    if t == \'F\': return f\n    return (t,) + tuple(subst(x, pv, qv) for x in f[1:])\ndef ev(f, h, tr, vals):   # tr: dict name->list ; atoms (\'v\',name)\n    t = f[0]\n    if t == \'F\': return False\n    if t == \'v\': return tr[f[1]][h]\n    if t == \'imp\': return (not ev(f[1], h, tr, vals)) or ev(f[2], h, tr, vals)\n    if t == \'box\': return all(ev(f[1], g, tr, vals) for g in range(h))\n    raise ValueError(f)\ndef closed(trace):\n    m = len(trace) - 1\n    while m > 0 and trace[m - 1] == trace[-1]: m -= 1\n    if m == 0: return T if trace[-1] else F\n    parts = [conj(boxn(F, h + 1), neg(boxn(F, h))) for h in range(m) if trace[h]]\n    if trace[-1]: parts.append(neg(boxn(F, m)))\n    out = parts[0]\n    for q in parts[1:]: out = disj(out, q)\n    return out\ndef nb(f): return (f[0] == \'box\') + sum(nb(x) for x in f[1:] if isinstance(x, tuple))\ndef solve(sa, sb):\n    A, B = parse(sa), parse(sb)\n    H = 2 * (nb(A) + nb(B)) + 4\n    VX, VY = (\'v\', \'x\'), (\'v\', \'y\')\n    # closed q-values: opponent vs DB (all-F inputs)\n    def vsDB(f):\n        tr = {}; t = []\n        for h in range(H):\n            t.append(ev(subst(f, F, F), h, {}, None))\n        return t\n    za, zb = vsDB(A), vsDB(B)\n    CA, CB_ = closed(za), closed(zb)\n    ex = subst(A, VY, CB_); ey = subst(B, VX, CA)\n    tr = {\'x\': [], \'y\': []}\n    for h in range(H):\n        xa = ev(ex, h, tr, None); yb = ev(ey, h, tr, None)\n        tr[\'x\'].append(xa); tr[\'y\'].append(yb)\n    cx, cy = closed(tr[\'x\']), closed(tr[\'y\'])\n    sub = lambda f: subst_v(f, cx, cy)\n    assert prove(iff(cx, sub(ex))) and prove(iff(cy, sub(ey)))\n    # mutation control: flipping a candidate must be rejected\n    assert not (prove(iff(neg(cx), sub(ex))) and prove(iff(cy, sub(ey))))\n    assert not (prove(iff(cx, subst_v(ex, neg(cx), cy))) and prove(iff(neg(cx), subst_v(ex, neg(cx), cy))))\n    return tr[\'x\'][-1], tr[\'y\'][-1]\ndef subst_v(f, cx, cy):\n    if f[0] == \'v\': return cx if f[1] == \'x\' else cy\n    if f[0] == \'F\': return f\n    return (f[0],) + tuple(subst_v(x, cx, cy) for x in f[1:])\ndef main():\n    t0 = time.time()\n    raw = None\n    for pth in PATHS:\n        try: raw = open(pth, \'rb\').read(); break\n        except OSError: pass\n    assert raw and hashlib.sha256(raw).hexdigest() == SHA\n    d = json.loads(raw); names = d[\'agents\']; sizes = d[\'sizes\']; n = len(names)\n    bits = bytes.fromhex(d[\'M_packbits_hex\'])\n    Mv = lambda a, b: (bits[(a * n + b) >> 3] >> (7 - ((a * n + b) & 7))) & 1\n    rnd = random.Random(7)\n    small = [i for i in range(n) if sizes[i] <= 6]\n    cells = [(rnd.choice(small), rnd.choice(small)) for _ in range(300)]\n    big = [i for i in range(n)]\n    cells += [(rnd.choice(big), rnd.choice(small)) for _ in range(1500)]\n    # negative control: the verifier must reject a flipped candidate\n    done = 0\n    for a, b in cells:\n        if time.time() - t0 > 90: break\n        x, y = solve(names[a], names[b])\n        assert x == bool(Mv(a, b)) and y == bool(Mv(b, a)), (names[a], names[b])\n        done += 1\n    assert done >= 500, done\n    # negative control on the prover\n    A, B = parse(\'[]p\'), parse(\'[]p\')\n    assert not prove(iff(F, box(F))) and prove(iff(box(box(F)), box(box(F))))\n    print(\'PASS GLS certificates for\', done, \'matrix cells\', round(time.time() - t0, 1), \'s\')'
cert={}
exec(CERT_SOURCE,cert)

import hashlib,json
def H(m,j): return '[]'*(m+1)+'(p&(q|[]('+ '[]'*j+'F|~q)))'
def G(m,j): return '[]('+ '[]'*m+'p&(q|[]('+ '[]'*j+'F|~q)))'
def V(n,r): return '[]('+ '[]'*n+'F|(p&(q|~'+'[]'*r+'q)))'
def F(k): return '[]'*k+'p'
def P(i): return '([]p&[]('+'[]'*i+'F|~q))'
params=[(1,1),(2,1),(2,2),(3,1),(3,2),(4,1)]
seps=['[][](p|~[][]q)','[][](p|~[]q)','[][][](p|~[][]q)','[][](p|~[]q)','[][][](p|~[]q)','[][](p|~[]q)']
assert params==[(m,j) for m in range(1,5) for j in range(1,m+1) if m+j+10<=15]
rows=[]
def cell(a,b,expected):
    actual=cert['solve'](a,b)
    assert actual==expected,(a,b,actual,expected)
    rows.append((a,b,actual))
    cert['prove_seq'].cache_clear()
for (m,j),sep in zip(params,seps):
    h=H(m,j)
    cell(h,h,(False,False))
    cell(h,'~F',(True,True))
    cell(h,'F',(False,False))
    cell(h,'~[]F',(False,True))
    for k in range(1,5): cell(h,F(k),(k<=j,k<=j))
    for i in range(6): cell(h,P(i),(i>m,i>m))
    cell(h,sep,(False,True))
    cell(G(m,j),sep,(False,False))
    # Single boxed p gate shifted outwards: size remains m+j+10.
    def size(s): return len(s.replace('[]','B').replace('(','').replace(')',''))
    assert size(h)==m+j+10<=15
# ConBot separates H from every V in the common size <=15 comparison domain.
for n in range(2,6):
 for r in range(1,n):
    if n+r+9<=15: cell(V(n,r),'~[]F',(True,True))
# F/P rows distinguish all six H parameters in the common opponent bound <=12.
sigs=[tuple([k<=j for k in range(1,5)]+[i>m for i in range(6)]) for m,j in params]
assert len(set(sigs))==6
raw=json.dumps(rows,separators=(',',':')).encode()
assert len(rows)==102
assert hashlib.sha256(raw).hexdigest()=='4d63db184b4e6ef10f49b5fcf8aec8f8d826b8a2b278b5ec17e13188f420f15f'
print('PASS',len(rows),'GLS-certified cells; sha256',hashlib.sha256(raw).hexdigest())
