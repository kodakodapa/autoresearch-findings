"""Exact GL certificates for source-defined Chicken and Hobson agents.
True=Swerve/Cooperate, False=Straight/Defect. PA+n means iterated
consistency, with Prov_n(A)=box(box^n(False) or A); n=0 gives box(A).
GLS core copied from prior c046_jfam_gls.py; standalone stdlib only.
Every cell verifies both fixed-point equations in GL, not just a trace.
No q probes occur. AstuteBot uses its displayed formula, not prose.
"""
F = ('F',)
def imp(a, b): return ('imp', a, b)
def neg(a): return imp(a, F)
def box(a): return ('box', a)
def conj(a, b): return neg(imp(a, neg(b)))
def disj(a, b): return imp(neg(a), b)
T = neg(F)
def iff(a, b): return conj(imp(a, b), imp(b, a))
def boxn(x, n):
    for _ in range(n): x = box(x)
    return x
import functools
@functools.lru_cache(maxsize=None)
def prove_seq(L, R):
    if F in L or L & R: return True
    for f in L:
        if f[0] == 'imp':
            L2 = L - {f}
            return prove_seq(L2, R | {f[1]}) and prove_seq(L2 | {f[2]}, R)
    for f in R:
        if f[0] == 'imp':
            return prove_seq(L | {f[1]}, (R - {f}) | {f[2]})
    boxedL = frozenset(f for f in L if f[0] == 'box')
    unb = frozenset(f[1] for f in boxedL)
    for f in R:
        if f[0] == 'box' and prove_seq(boxedL | unb | {f}, frozenset({f[1]})): return True
    return False
def prove(f): return prove_seq(frozenset(), frozenset({f}))
def parse(s):
    def p(i):
        c = s[i]
        if c == 'F': return F, i + 1
        if c in 'pq': return (c,), i + 1
        if c == '~': m, j = p(i + 1); return neg(m), j
        if s.startswith('[]', i): m, j = p(i + 2); return box(m), j
        a, j = p(i + 1); op = s[j]; b, k = p(j + 1); assert s[k] == ')'
        return (conj if op == '&' else disj)(a, b), k + 1
    t, j = p(0); assert j == len(s); return t
def subst(f, pv, qv):
    t = f[0]
    if t == 'p': return pv
    if t == 'q': return qv
    if t == 'F': return f
    return (t,) + tuple(subst(x, pv, qv) for x in f[1:])
def ev(f, h, tr, vals):   # tr: dict name->list ; atoms ('v',name)
    t = f[0]
    if t == 'F': return False
    if t == 'v': return tr[f[1]][h]
    if t == 'imp': return (not ev(f[1], h, tr, vals)) or ev(f[2], h, tr, vals)
    if t == 'box': return all(ev(f[1], g, tr, vals) for g in range(h))
    raise ValueError(f)
def closed(trace):
    m = len(trace) - 1
    while m > 0 and trace[m - 1] == trace[-1]: m -= 1
    if m == 0: return T if trace[-1] else F
    parts = [conj(boxn(F, h + 1), neg(boxn(F, h))) for h in range(m) if trace[h]]
    if trace[-1]: parts.append(neg(boxn(F, m)))
    out = parts[0]
    for q in parts[1:]: out = disj(out, q)
    return out
def nb(f): return (f[0] == 'box') + sum(nb(x) for x in f[1:] if isinstance(x, tuple))
def solve(sa, sb):
    A, B = parse(sa), parse(sb)
    H = 2 * (nb(A) + nb(B)) + 4
    VX, VY = ('v', 'x'), ('v', 'y')
    # closed q-values: opponent vs DB (all-F inputs)
    def vsDB(f):
        tr = {}; t = []
        for h in range(H):
            t.append(ev(subst(f, F, F), h, {}, None))
        return t
    za, zb = vsDB(A), vsDB(B)
    CA, CB_ = closed(za), closed(zb)
    ex = subst(A, VY, CB_); ey = subst(B, VX, CA)
    tr = {'x': [], 'y': []}
    for h in range(H):
        xa = ev(ex, h, tr, None); yb = ev(ey, h, tr, None)
        tr['x'].append(xa); tr['y'].append(yb)
    cx, cy = closed(tr['x']), closed(tr['y'])
    sub = lambda f: subst_v(f, cx, cy)
    assert prove(iff(cx, sub(ex))) and prove(iff(cy, sub(ey)))
    # mutation control: flipping a candidate must be rejected
    assert not (prove(iff(neg(cx), sub(ex))) and prove(iff(cy, sub(ey))))
    assert not (prove(iff(cx, subst_v(ex, neg(cx), cy))) and prove(iff(neg(cx), subst_v(ex, neg(cx), cy))))
    return tr['x'][-1], tr['y'][-1]
def subst_v(f, cx, cy):
    if f[0] == 'v': return cx if f[1] == 'x' else cy
    if f[0] == 'F': return f
    return (f[0],) + tuple(subst_v(x, cx, cy) for x in f[1:])

# n iterated consistency axioms reduce to not box^n F over PA.
def prov(n,a):
    assert n >= 0
    return box(disj(boxn(F,n),a))
x,y=('v','x'),('v','y')
def careful(n,own,opp): return neg(prov(n,opp))
def bold(n,own,opp): return prov(n,neg(opp))
def astute(own,opp):
    d=neg(own)
    return neg(box(imp(neg(box(F)),conj(imp(d,box(d)),imp(box(d),opp)))))
def hobson(own,opp): return conj(neg(prov(0,opp)),prov(1,opp))
def fair(n,own,opp): return prov(n,opp)
def constant(b): return lambda own,opp: T if b else F

def truth(f):
    if f[0]=='F': return False
    if f[0]=='imp': return not truth(f[1]) or truth(f[2])
    if f[0]=='box': return truth(f[1])
    raise AssertionError(f)

def certify(A,B):
    ex,ey=A(x,y),B(y,x)
    H=2*(nb(ex)+nb(ey))+6
    tr={'x':[],'y':[]}
    for h in range(H):
        a,b=ev(ex,h,tr,None),ev(ey,h,tr,None)
        tr['x'].append(a); tr['y'].append(b)
    cx,cy=closed(tr['x']),closed(tr['y'])
    assert prove(iff(cx,subst_v(ex,cx,cy)))
    assert prove(iff(cy,subst_v(ey,cx,cy)))
    # Reject flipping either candidate in the simultaneous equations.
    for dx,dy in [(neg(cx),cy),(cx,neg(cy))]:
        assert not (prove(iff(dx,subst_v(ex,dx,dy))) and prove(iff(dy,subst_v(ey,dx,dy))))
    assert (truth(cx),truth(cy))==(tr['x'][-1],tr['y'][-1])
    prove_seq.cache_clear()
    return truth(cx),truth(cy)

def grade(fn,n): return lambda own,opp: fn(n,own,opp)


def H(a,b):
    return lambda own,opp: conj(neg(prov(a,opp)),prov(b,opp))
count=0
for a in range(4):
 for b in range(a+1,5):
  for c in range(4):
   for d in range(c+1,5):
    got=certify(H(a,b),H(c,d))
    assert got==(a==c,a==c),(a,b,c,d,got)
    count+=1
  for c in range(5):
   got=certify(H(a,b),grade(fair,c))
   assert got==(False,False),(a,b,c,got)
   count+=1
print('PASS',count,'GL-certified generalized Hobson cells')
