"""r1 cross-review of r2 K20 (probe_safe10.py) with r1's independent K19 engine (evaluator-replacement probes,
height-chain semantics, GL certificates on all 24 replacement equations, flips rejected).
(1) K20 cells AAA=111, AFF=111, ACC=011, ADC=001, ACD=010, RRR=000 re-certified (R: q1 -> p1).
(2) A = [](p1&(p2&([]F|~q1))) and K19's E = []((p1&p2)&([]F|~q1)) differ only by associativity of &: GL proves
    A<->E (open formula), and all 8 mixed triples of A/E in self-play are 111. Hence K20 and K19 name the same agent.
(3) GL does not prove A<->R (probe essential), control.
Self-contained; stdlib only.
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
N=3
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
T,Fa=True,False
A=('box',('and',('p1',),('and',('p2',),('or',('box',('F',)),('not',('q1',))))))
R=('box',('and',('p1',),('and',('p2',),('or',('box',('F',)),('not',('p1',))))))
assert size(A)==10 and guarded(A) and size(E)==10
EXP={(A,A,A):(T,T,T),(A,FB,FB):(T,T,T),(A,C,C):(Fa,T,T),(A,D,C):(Fa,Fa,T),(A,C,D):(Fa,T,Fa),(R,R,R):(Fa,Fa,Fa)}
for fs,v in EXP.items():
    assert solve(fs)==v and certify(fs)==v,(list(map(show,fs)),v)
print('(1) K20 six cells re-certified with r1 engine')
assert prove(iff(togl(A),togl(E)))
for fs in itertools.product((A,E),repeat=3):
    assert solve(fs)==(T,T,T) and certify(fs)==(T,T,T)
print('(2) GL proves A<->E; 8 mixed A/E triples certified 111')
assert not prove(iff(togl(A),togl(R)))
print('(3) GL rejects A<->R')
print('PASS')
