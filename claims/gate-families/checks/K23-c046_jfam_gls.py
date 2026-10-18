"""K23 GLS certificates: boundary cells of the box-placement family
J_{a,b,j} = []^{a+1}([]^b p & (q | []([]^j F | ~q))) against F_k, P_i, S_{u,t} = []^u(p | ~[]^t q),
self-play and CB/DB/ConBot.  For each cell the closed fixed-point candidates are taken from a height
table and PROVED in GLS (x <-> A[p:=y, q:=B(DB)], y <-> B[...]); flipped candidates are rejected.
Expected outcomes come from the K23 laws (not from the solver).  Prover: same embedded GLS engine
as c046_segment.py (sk's Valentini-style prover).  Self-contained; python -I.
"""
import time
GLS_SRC = "F = ('F',)\ndef imp(a, b): return ('imp', a, b)\ndef neg(a): return imp(a, F)\ndef box(a): return ('box', a)\ndef conj(a, b): return neg(imp(a, neg(b)))\ndef disj(a, b): return imp(neg(a), b)\nT = neg(F)\ndef iff(a, b): return conj(imp(a, b), imp(b, a))\ndef boxn(x, n):\n    for _ in range(n): x = box(x)\n    return x\nimport functools\n@functools.lru_cache(maxsize=None)\ndef prove_seq(L, R):\n    if F in L or L & R: return True\n    for f in L:\n        if f[0] == 'imp':\n            L2 = L - {f}\n            return prove_seq(L2, R | {f[1]}) and prove_seq(L2 | {f[2]}, R)\n    for f in R:\n        if f[0] == 'imp':\n            return prove_seq(L | {f[1]}, (R - {f}) | {f[2]})\n    boxedL = frozenset(f for f in L if f[0] == 'box')\n    unb = frozenset(f[1] for f in boxedL)\n    for f in R:\n        if f[0] == 'box' and prove_seq(boxedL | unb | {f}, frozenset({f[1]})): return True\n    return False\ndef prove(f): return prove_seq(frozenset(), frozenset({f}))\ndef parse(s):\n    def p(i):\n        c = s[i]\n        if c == 'F': return F, i + 1\n        if c in 'pq': return (c,), i + 1\n        if c == '~': m, j = p(i + 1); return neg(m), j\n        if s.startswith('[]', i): m, j = p(i + 2); return box(m), j\n        a, j = p(i + 1); op = s[j]; b, k = p(j + 1); assert s[k] == ')'\n        return (conj if op == '&' else disj)(a, b), k + 1\n    t, j = p(0); assert j == len(s); return t\ndef subst(f, pv, qv):\n    t = f[0]\n    if t == 'p': return pv\n    if t == 'q': return qv\n    if t == 'F': return f\n    return (t,) + tuple(subst(x, pv, qv) for x in f[1:])\ndef ev(f, h, tr, vals):   # tr: dict name->list ; atoms ('v',name)\n    t = f[0]\n    if t == 'F': return False\n    if t == 'v': return tr[f[1]][h]\n    if t == 'imp': return (not ev(f[1], h, tr, vals)) or ev(f[2], h, tr, vals)\n    if t == 'box': return all(ev(f[1], g, tr, vals) for g in range(h))\n    raise ValueError(f)\ndef closed(trace):\n    m = len(trace) - 1\n    while m > 0 and trace[m - 1] == trace[-1]: m -= 1\n    if m == 0: return T if trace[-1] else F\n    parts = [conj(boxn(F, h + 1), neg(boxn(F, h))) for h in range(m) if trace[h]]\n    if trace[-1]: parts.append(neg(boxn(F, m)))\n    out = parts[0]\n    for q in parts[1:]: out = disj(out, q)\n    return out\ndef nb(f): return (f[0] == 'box') + sum(nb(x) for x in f[1:] if isinstance(x, tuple))\ndef solve(sa, sb):\n    A, B = parse(sa), parse(sb)\n    H = 2 * (nb(A) + nb(B)) + 4\n    VX, VY = ('v', 'x'), ('v', 'y')\n    # closed q-values: opponent vs DB (all-F inputs)\n    def vsDB(f):\n        tr = {}; t = []\n        for h in range(H):\n            t.append(ev(subst(f, F, F), h, {}, None))\n        return t\n    za, zb = vsDB(A), vsDB(B)\n    CA, CB_ = closed(za), closed(zb)\n    ex = subst(A, VY, CB_); ey = subst(B, VX, CA)\n    tr = {'x': [], 'y': []}\n    for h in range(H):\n        xa = ev(ex, h, tr, None); yb = ev(ey, h, tr, None)\n        tr['x'].append(xa); tr['y'].append(yb)\n    cx, cy = closed(tr['x']), closed(tr['y'])\n    sub = lambda f: subst_v(f, cx, cy)\n    assert prove(iff(cx, sub(ex))) and prove(iff(cy, sub(ey)))\n    # mutation control: flipping a candidate must be rejected\n    assert not (prove(iff(neg(cx), sub(ex))) and prove(iff(cy, sub(ey))))\n    assert not (prove(iff(cx, subst_v(ex, neg(cx), cy))) and prove(iff(neg(cx), subst_v(ex, neg(cx), cy))))\n    return tr['x'][-1], tr['y'][-1]\ndef subst_v(f, cx, cy):\n    if f[0] == 'v': return cx if f[1] == 'x' else cy\n    if f[0] == 'F': return f\n    return (f[0],) + tuple(subst_v(x, cx, cy) for x in f[1:])\n"
GL = {}
exec(GLS_SRC, GL)

def bx(k, x): return '[]' * k + x
def J(a, b, j): return bx(a + 1, '(' + bx(b, 'p') + '&(q|[](' + bx(j, 'F') + '|~q)))')
def Fk(k): return bx(k, 'p')
def Pi(i): return '([]p&[](' + bx(i, 'F') + '|~q))' if i else '([]p&[]~q)'
def S(u, t): return bx(u, '(p|~' + bx(t, 'q') + ')')
def size(s): return sum(1 for c in s if c in 'Fpq~&|') + s.count('[]')

def expected(a, b, j, opp):
    kind, *par = opp
    if kind == 'F': return ((par[0] <= j),) * 2
    if kind == 'P': return ((par[0] > a + b),) * 2
    if kind == 'S':
        u, t = par
        if u <= j: return (True, True)
        return (False, t + b <= u)
    if kind == 'self': return (False, False)
    if kind == 'CB': return (True, True)
    if kind == 'DB': return (False, False)
    if kind == 'Con': return (False, True)

def opp_str(a, b, j, opp):
    kind, *par = opp
    return {'F': lambda: Fk(par[0]), 'P': lambda: Pi(par[0]), 'S': lambda: S(*par),
            'self': lambda: J(a, b, j), 'CB': lambda: '~F', 'DB': lambda: 'F', 'Con': lambda: '~[]F'}[kind]()

t0 = time.time()
AGENTS = [(a, b, j) for a in range(6) for b in range(6) for j in range(1, 6)
          if j <= a + b and a + b + j + 10 <= 15]
assert len(AGENTS) == 21
n = 0
for (a, b, j) in AGENTS:
    A = J(a, b, j)
    assert size(A) == a + b + j + 10
    opps = [('self',), ('CB',), ('DB',), ('Con',), ('F', j), ('F', j + 1), ('P', a + b), ('P', a + b + 1),
            ('S', j, j + 3)]
    for u in (j + 1, j + 2):
        tb = u - b                      # boundary t + b = u (D/C) and t + b = u + 1 (DD)
        for t in (tb, tb + 1):
            if t >= 1: opps.append(('S', u, t))
    for opp in opps:
        B = opp_str(a, b, j, opp)
        if opp[0] == 'DB':
            # DB has no p; solve() still certifies the fixed point of A vs F
            pass
        x, y = GL['solve'](A, B)
        exp = expected(a, b, j, opp)
        if opp[0] == 'DB': exp = (False, False)
        assert (bool(x), bool(y)) == exp, (A, B, x, y, exp)
        n += 1
        print('GLS', (a, b, j), opp, int(x), int(y), round(time.time() - t0, 1), 's', flush=True)
# the S-row reads off b: J_{1,1,1} and J_{2,0,1}=H_{2,1} and J_{0,2,1}=G_{2,1} differ on S_{2,1}, S_{2,2}
row = {}
for (a, b, j) in [(0, 2, 1), (1, 1, 1), (2, 0, 1)]:
    row[(a, b)] = tuple(GL['solve'](J(a, b, j), S(2, t)) for t in (1, 2))
    n += 2
assert row[(0, 2)] == ((False, False), (False, False))
assert row[(1, 1)] == ((False, True), (False, False))
assert row[(2, 0)] == ((False, True), (False, True))
print('certified cells', n, 'PASS', round(time.time() - t0, 1), 's')
