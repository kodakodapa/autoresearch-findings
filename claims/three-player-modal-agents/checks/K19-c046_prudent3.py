"""r1: a three-player PrudentBot (evaluator-replacement probes, language of K13/K15-K18).
Language {F,p1,p2,q1,q2,~,&,|,[]}, ordered raw trees, node-count size, every atom under a box. In world M (set of
slots replaced by the constant defector D) slot i reads p_j = local opponent j in M, q_j = local opponent j in
M+{i}. Height-chain semantics of closed GL fixed points; tails at H=30. u_i = 2*sum a - 3*a_i; True = contribute.
"Safe" = never earns less than either opponent. C = constant contributor ~F, D = F, FB = [](p1&p2).
E = []((p1&p2)&([]F|~q1)), size 10.
(1) E-cells, GL-certified (24 replacement equations each, flips rejected):
    EEE=111, ECC=011 (E earns 4, others 1), ECD=010, EDD=000, E FB FB=111, E E FB=111, E C FB=010,
    E D FB=000, EEC=111 (E probes only its first opponent).
(2) GL proves E -> [](p1&p2) (free atoms), so by Lean lag_tail (k=1) E is safe against every opponent pair.
(3) Exhaustive bound: among the 28125 guarded trees of size <=7, the trees that self-cooperate and defect
    against (C,C) number 0,0,4,4,68,220,1808 at sizes 1..7, and every one earns strictly less than an
    opponent against some pair of size <=3 trees. Hence no tree of size <=7 is safe, self-cooperating and
    defecting against two contributors.
Self-contained; stdlib + lean binary only.
"""
import itertools, sys, subprocess, shutil, os
from functools import lru_cache
sys.setrecursionlimit(100000)
H=30
ATOMS=['p1','p2','q1','q2']
def trees(n):
    out=[]
    if n==1: return [('F',)]+[(a,) for a in ATOMS]
    for c in trees(n-1): out+= [('not',c),('box',c)]
    for k in range(1,n-1):
        for a in trees(k):
            for b in trees(n-1-k): out+=[('and',a,b),('or',a,b)]
    return out
def guarded(f,ub=False):
    if f[0] in ATOMS: return ub
    if f[0]=='F': return True
    if f[0]=='box': return guarded(f[1],True)
    return all(guarded(x,ub) for x in f[1:])
def show(f):
    t=f[0]
    if t in ATOMS: return t
    if t=='F': return 'F'
    if t in('not','box'): return ('~' if t=='not' else '[]')+show(f[1])
    return '('+show(f[1])+('&' if t=='and' else '|')+show(f[2])+')'
N=7
census={n:[f for f in trees(n) if guarded(f)] for n in range(1,N+1)}
def solve(fs):
    @lru_cache(maxsize=None)
    def act(M,i,h):
        if M>>i&1: return False
        o=[j for j in range(3) if j!=i]
        def ev(f,h):
            t=f[0]
            if t=='F': return False
            if t=='not': return not ev(f[1],h)
            if t=='and': return ev(f[1],h) and ev(f[2],h)
            if t=='or': return ev(f[1],h) or ev(f[2],h)
            if t=='box': return all(ev(f[1],g) for g in range(h))
            j=int(t[1])-1
            return act(M|(1<<i) if t[0]=='q' else M, o[j], h)
        return ev(fs[i],h)
    tr=[[act(0,i,h) for h in range(H)] for i in range(3)]
    for t in tr: assert len(set(t[-12:]))==1
    return tuple(t[-1] for t in tr)
def u(a,i): return 2*sum(a)-3*a[i]
D=('F',); C=('not',('F',))
def dis(f,b,c):
    a=solve((f,b,c)); return u(a,0)<max(u(a,1),u(a,2))
Fl = ('F',)
def imp(a, b): return ('imp', a, b)
def neg(a): return imp(a, Fl)
def box(a): return ('box', a)
def conj(a, b): return neg(imp(a, neg(b)))
def iff(a, b): return conj(imp(a, b), imp(b, a))
Tr = neg(Fl)
@lru_cache(maxsize=None)
def prv(L, R):
    if Fl in L or L & R: return True
    for f in L:
        if f[0] == 'imp':
            L2 = L - {f}
            return prv(L2, R | {f[1]}) and prv(L2 | {f[2]}, R)
    for f in R:
        if f[0] == 'imp':
            return prv(L | {f[1]}, (R - {f}) | {f[2]})
    bl = frozenset(f for f in L if f[0] == 'box')
    ub = frozenset(f[1] for f in bl)
    return any(f[0] == 'box' and prv(bl | ub | {f}, frozenset({f[1]})) for f in R)
def prove(f): return prv(frozenset(), frozenset({f}))
def boxn(x, n):
    for _ in range(n): x = box(x)
    return x
def closed(tr):  # height-slice normal form of an eventually constant trace
    m = len(tr) - 1
    while m > 0 and tr[m-1] == tr[-1]: m -= 1
    if m == 0: return Tr if tr[-1] else Fl
    parts = [conj(boxn(Fl, h+1), neg(boxn(Fl, h))) for h in range(m) if tr[h]]
    if tr[-1]: parts.append(neg(boxn(Fl, m)))
    out = parts[0]
    for x in parts[1:]: out = imp(neg(out), x)
    return out

def has_q(f): return f[0] in ('q1','q2') or any(has_q(x) for x in f[1:] if isinstance(x,tuple))
def togl(f):
    t=f[0]
    if t in ATOMS: return (t,)
    if t=='F': return Fl
    if t=='not': return neg(togl(f[1]))
    if t=='and': return conj(togl(f[1]),togl(f[2]))
    if t=='or': return imp(neg(togl(f[1])),togl(f[2]))
    return box(togl(f[1]))
def tr2gl(f,M,i):
    t=f[0]
    if t=='F': return Fl
    if t=='not': return neg(tr2gl(f[1],M,i))
    if t=='and': return conj(tr2gl(f[1],M,i),tr2gl(f[2],M,i))
    if t=='or': return imp(neg(tr2gl(f[1],M,i)),tr2gl(f[2],M,i))
    if t=='box': return box(tr2gl(f[1],M,i))
    o=[j for j in range(3) if j!=i]; j=int(t[1])-1
    return ('v', M|(1<<i) if t[0]=='q' else M, o[j])
def certify(fs):
    @lru_cache(maxsize=None)
    def act(M,i,h):
        if M>>i&1: return False
        o=[j for j in range(3) if j!=i]
        def ev(f,h):
            t=f[0]
            if t=='F': return False
            if t=='not': return not ev(f[1],h)
            if t=='and': return ev(f[1],h) and ev(f[2],h)
            if t=='or': return ev(f[1],h) or ev(f[2],h)
            if t=='box': return all(ev(f[1],g) for g in range(h))
            j=int(t[1])-1
            return act(M|(1<<i) if t[0]=='q' else M, o[j], h)
        return ev(fs[i],h)
    eqn=lambda M,i: Fl if M>>i&1 else tr2gl(fs[i],M,i)
    cand={(M,i):closed([act(M,i,h) for h in range(14)]) for M in range(8) for i in range(3)}
    for (M,i) in cand: assert prove(iff(cand[M,i],sub(eqn(M,i),cand))),(fs,M,i)
    for i in range(3):
        bad=dict(cand); bad[0,i]=neg(bad[0,i])
        assert not all(prove(iff(bad[kk],sub(eqn(*kk),bad))) for kk in bad)
    prv.cache_clear()
    return tuple(act(0,i,13) for i in range(3))
def sub(f,c):
    if f[0]=='v': return c[(f[1],f[2])]
    return (f[0],)+tuple(sub(y,c) for y in f[1:])

FB=('box',('and',('p1',),('p2',)))
E=('box',('and',('and',('p1',),('p2',)),('or',('box',('F',)),('not',('q1',)))))
def size(f): return 1+sum(size(x) for x in f[1:])
assert size(E)==10 and guarded(E)
T,Fa=True,False
EXP={(E,E,E):(T,T,T),(E,C,C):(Fa,T,T),(E,C,D):(Fa,T,Fa),(E,D,D):(Fa,Fa,Fa),(E,FB,FB):(T,T,T),
     (E,E,FB):(T,T,T),(E,C,FB):(Fa,T,Fa),(E,D,FB):(Fa,Fa,Fa),(E,E,C):(T,T,T)}
for fs,v in EXP.items():
    assert solve(fs)==v and certify(fs)==v,(list(map(show,fs)),v)
a=EXP[(E,C,C)]; assert (u(a,0),u(a,1),u(a,2))==(4,1,1)
print('(1) 9 E-cells GL-certified:',{''.join('E' if x==E else 'C' if x==C else 'D' if x==D else 'B' for x in k):''.join(str(int(y)) for y in v) for k,v in EXP.items()})
P12=conj(('p1',),('p2',))
assert prove(imp(togl(E),box(P12)))
assert not prove(imp(togl(E),box(conj(P12,neg(('q1',))))))  # control: E does not prove []~q1
print('(2) GL proves E -> [](p1&p2); control rejected')
up3=census[1]+census[2]+census[3]
CNTS=[]
for n in range(1,N+1):
    cand=[f for f in census[n] if solve((f,C,C))[0]==False and solve((f,f,f))==(T,T,T)]
    for f in cand:
        w=next(((b,c) for b in (D,C) for c in (D,C) if dis(f,b,c)),None) or next(((b,c) for b in up3 for c in up3 if dis(f,b,c)),None)
        assert w is not None, show(f)
    CNTS.append(len(cand))
print('(3) self-coop & defect vs (C,C) per size 1..7:',CNTS,'all beaten by size<=3 pairs; total trees',sum(len(census[n]) for n in census))
assert [len(census[n]) for n in census]==[1,6,18,112,596,3756,23636] and CNTS==[0,0,4,4,68,220,1808] and sum(len(census[n]) for n in census)==28125
LEAN = r'''
theorem lag_tail (k : Nat) (x y z : Nat → Prop) (hx : ∀ h g, g + k ≤ h → x h → y g ∧ z g)
    (T : Nat) (X Y Z : Prop) (hX : ∀ h, T ≤ h → (x h ↔ X)) (hY : ∀ h, T ≤ h → (y h ↔ Y))
    (hZ : ∀ h, T ≤ h → (z h ↔ Z)) : X → Y ∧ Z := by
  intro hxX
  have H := hx (T+k) T (Nat.le_refl _) ((hX (T+k) (by omega)).2 hxX)
  exact ⟨(hY T (Nat.le_refl T)).1 H.1, (hZ T (Nat.le_refl T)).1 H.2⟩
def u (a b c : Bool) : Int := 2 * ((if a then 1 else 0) + (if b then 1 else 0) + (if c then 1 else 0)) - 3 * (if a then 1 else 0)
theorem fair3_payoff : ∀ X Y Z : Bool, (X = true → Y = true ∧ Z = true) →
    u Y X Z ≤ u X Y Z ∧ u Z X Y ≤ u X Y Z := by decide
#print axioms lag_tail
#print axioms fair3_payoff
'''
def lean():
    for c in (shutil.which('lean'), '/opt/elan/bin/lean', os.path.expanduser('~/.elan/bin/lean')):
        if c and os.path.exists(c): return c
    raise AssertionError('lean binary not found')
def run_lean(src):
    r = subprocess.run([lean(), '--stdin'], input=src, capture_output=True, text=True, timeout=100)
    return r.returncode, r.stdout + r.stderr
rc, out = run_lean(LEAN)
assert rc == 0 and 'sorryAx' not in out and 'error' not in out, out
bad = LEAN.replace('(X = true → Y = true ∧ Z = true) →', '')
assert bad != LEAN and run_lean(bad)[0] != 0
print('(5) Lean: lag_tail, fair3_payoff proved; false variant rejected')
print('PASS')
