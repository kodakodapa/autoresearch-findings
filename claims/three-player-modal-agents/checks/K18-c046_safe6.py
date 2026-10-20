"""r1: three-player safe self-cooperators up to size 6 (evaluator-replacement probes, K13/K15-K17 language).
Language {F,p1,p2,q1,q2,~,&,|,[]}, ordered raw trees, node-count size, every atom under a box.
World M = set of slots replaced by the constant defector; in world M slot i reads p_j = local opponent j in M,
q_j = local opponent j in M+{i}; local order = increasing global slot. Height-chain semantics of closed GL
fixed points ([]phi at h iff phi at all g<h), tails read at H=30. Payoffs u_i = 2*sum a - 3*a_i, True = contribute.
"Safe" = never earns less than either opponent (agent in slot 0).
(1) guarded raw trees per size 1..6: 1,6,18,112,596,3756 (4489 total).
(2) Self-cooperators: 11,41,263,1448 at sizes <=3,4,5,6. Every self-cooperator except exactly 66 trees has a
    witness pair of size <=3 against which it earns strictly less than an opponent; constant pairs suffice
    except for 8 size-6 trees, the conjunct/disjunct orders of [](p_i&(p_j|q_j)) (witness: ~F and []~p1).
(3) The 66 survivors (2,8,56 at sizes 4,5,6) contain no q atom and GL proves A -> [][][](p1&p2) for each
    (atoms as free propositional letters; GL is sound on the height chain for any opponent traces).
(4) All self-play and witness triples of sizes 4..6 GL-certified: 24 replacement equations each, own GLS
    prover, actual-player flips rejected.
(5) Lean 4 core: if x h -> y g & z g whenever g+k<=h (any k, any traces), eventual constancy gives tail
    X -> Y & Z, hence universal no-disadvantage; false variant rejected.
So for size <=6 the safe self-cooperators are exactly 66 trees, each GL-implying [][][](p1&p2).
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
census={n:[f for f in trees(n) if guarded(f)] for n in range(1,7)}
CNT=[len(census[n]) for n in range(1,7)]
print('(1) guarded raw trees per size 1..6:',CNT); assert CNT==[1,6,18,112,596,3756]
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
up3=census[1]+census[2]+census[3]
sc={n:[f for f in census[n] if solve((f,f,f))==(True,)*3] for n in range(1,7)}
NS=[len(sc[1])+len(sc[2])+len(sc[3])]+[len(sc[n]) for n in (4,5,6)]
print('(2) self-cooperators (<=3,4,5,6):',NS); assert NS==[11,41,263,1448]
wit={}; surv={n:[] for n in range(1,7)}; nonconst=[]
for n in range(1,7):
    for f in sc[n]:
        w=next(((b,c) for b in (D,C) for c in (D,C) if dis(f,b,c)),None)
        if w is None:
            w=next(((b,c) for b in up3 for c in up3 if dis(f,b,c)),None)
            if w: nonconst.append(show(f))
        if w: wit[f]=w
        else: surv[n].append(f)
NV=[len(surv[n]) for n in range(1,7)]
print('    survivors per size:',NV,'non-constant witnesses needed for',nonconst)
assert NV==[0,0,0,2,8,56] and sorted(nonconst)==sorted(['[](p1&(p2|q2))','[](p1&(q2|p2))','[](p2&(p1|q1))','[](p2&(q1|p1))','[]((p1|q1)&p2)','[]((p2|q2)&p1)','[]((q1|p1)&p2)','[]((q2|p2)&p1)'])
assert [show(f) for f in surv[4]]==['[](p1&p2)','[](p2&p1)']
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
P12=conj(('p1',),('p2',))
S=[f for n in range(1,7) for f in surv[n]]
for f in S:
    assert not has_q(f) and prove(imp(togl(f),boxn(P12,3))), show(f)
assert not prove(imp(togl(('box',('p1',))),boxn(P12,3)))  # control: []p1 does not imply it
print('(3)',len(S),'survivors q-free, each GL-proves A -> [][][](p1&p2); control []p1 rejected')
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
n=0
for k in (4,5,6):
    for f in sc[k]:
        assert certify((f,f,f))==(True,)*3; n+=1
        if f in wit:
            a=certify((f,)+wit[f]); assert a==solve((f,)+wit[f]) and u(a,0)<max(u(a,1),u(a,2)); n+=1
print('(4)',n,'triples GL-certified (24 equations each)')
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
