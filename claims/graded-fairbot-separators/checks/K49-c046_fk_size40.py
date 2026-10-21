"""C046 r1: size minima for F_k / F_{k+1} separators, exhaustive above the K58 depth bound.
Language L: guarded formulas over atoms p (opponent's move vs me), q (opponent's move vs DefectBot), F, ~, &, |, []
(top = ~F, 2 nodes); size = AST nodes; height semantics; game wiring as in K38/K58: against F_j = []^j p, O's p is
F_j's move vs O and O's q is F_j's DefectBot trace (h<j); outcome = pair of moves at the inclusive K40 horizon
H = 2(b(O)+j) (traces constant from H).
K58 (Lean, all k): no guarded O of modal depth <= k separates F_k from F_{k+1}. So minimal separators have depth
>= k+1, i.e. at least k+1 boxes, and size <= k+5 leaves at most 4 non-box nodes: a polynomial family.
This check enumerates EVERY reduced guarded formula of depth >= k+1 and size k+2..k+5 (two atoms, k<=KQ) or
k+2..k+6 (p only, k<=KP) and solves both games exactly (bitmask height traces, fixed point of the guarded game
recurrence, unique by guardedness). Reduction: no ~~x, no F child of & or |, no x&x, x|x, children unordered.
Every unreduced formula is semantically equal to a strictly smaller one (or to F), which is non-separating either
by K58 (depth <= k) or by this enumeration (smaller size), so the results hold for all formulas.
Asserts: two atoms, k=1..KQ: no separator of size <= k+4; at size k+5 the only reduced separator is
S_k = [](~q | []^k F) (CC vs F_k, DD vs F_{k+1}). p only, k=1..KP: none of size <= k+5; at size k+6 only
T_k = ~[](~p | []^k F) (DD vs F_k, (C,D) vs F_{k+1} in separator/opponent order, i.e. exploited). Cross-checks: full enumeration of all depths for small k
reproduces the minima (without using K58); bitmask game equals a naive literal height evaluator on samples.
"""
import sys, time, random
from functools import lru_cache
t0=time.time()
LEAVES=[('F',),('p',),('q',)]
def size(f): return 1 if len(f)==1 else 1+sum(size(c) for c in f[1:])
def nbox(f): return 0 if len(f)==1 else (f[0]=='b')+sum(nbox(c) for c in f[1:])
@lru_cache(None)
def gen(s, d, guarded, atoms):
    """formulas of size s, depth>=d; guarded: atoms only under boxes; reduced (no ~~, no F child of binary, ordered distinct binary children)"""
    out=[]
    if s==1:
        if d<=0:
            for l in LEAVES:
                if l[0]=='F' or (not guarded and l[0] in atoms): out.append(l)
        return tuple(out)
    if s-1 < d: return ()
    for c in gen(s-1, d-1, False, atoms): out.append(('b',c))
    for c in gen(s-1, d, guarded, atoms):
        if c[0]!='n': out.append(('n',c))
    seen=set()
    for s1 in range(1, s-1):
        s2=s-1-s1
        As=gen(s1,d,guarded,atoms)
        if d>0 and s2>=d+1:
            pass
        for a in As:
            if a==('F',): continue
            for b in (gen(s2,0,guarded,atoms) if s2 < d+1 or d==0 else gen(s2,0,guarded,atoms)):
                if b==('F',) or a==b: continue
                key=(a,b) if a<b else (b,a)
                if key in seen: continue
                seen.add(key)
                out.append(('a',)+key); out.append(('o',)+key)
    return tuple(out)
def ev(f, P, Q, FULL, NB):
    t=f[0]
    if t=='F': return 0
    if t=='p': return P
    if t=='q': return Q
    if t=='n': return ~ev(f[1],P,Q,FULL,NB)&FULL
    if t=='b':
        x=ev(f[1],P,Q,FULL,NB); z=(~x & (x+1)).bit_length()-1  # trailing ones count
        z=min(z,NB-1)
        return (1<<(z+1))-1 & FULL
    a=ev(f[1],P,Q,FULL,NB); b=ev(f[2],P,Q,FULL,NB)
    return a&b if t=='a' else a|b
def boxj(x, j, FULL, NB):
    for _ in range(j):
        z=(~x & (x+1)).bit_length()-1; z=min(z,NB-1); x=((1<<(z+1))-1)&FULL
    return x
def game(f, j):
    H=2*(nbox(f)+j); NB=H+1; FULL=(1<<NB)-1
    dF=(1<<j)-1
    x=FULL
    for it in range(NB+2):
        y=boxj(x,j,FULL,NB)
        x2=ev(f,y,dF,FULL,NB)
        if x2==x: break
        x=x2
    else: raise Exception('noconv')
    return ((x>>H)&1, (y>>H)&1)
def seps(k, s, atoms):
    r=[]
    for f in gen(s, k+1, True, atoms):
        if game(f,k)!=game(f,k+1): r.append(f)
    return r
def show(f):
    t=f[0]
    if len(f)==1: return t
    if t=='n': return '~'+show(f[1])
    if t=='b': return '[]'+show(f[1])
    return '('+show(f[1])+('&' if t=='a' else '|')+show(f[2])+')'

def naive_game(f, j, H):
    # literal recursion: x(h) = O(p=y,q=dF)(h), y(h) = all x(g) for g<=h-j
    xs=[]; ys=[]
    def val(g, h):
        t=g[0]
        if t=='F': return False
        if t=='p': return ys[h]
        if t=='q': return h<j
        if t=='n': return not val(g[1],h)
        if t=='b': return all(val(g[1],u) for u in range(h))
        a=val(g[1],h)
        return (a and val(g[2],h)) if t=='a' else (a or val(g[2],h))
    for h in range(H+1):
        ys.append(all(xs[g] for g in range(h-j+1)))
        xs.append(val(f,h))
    return (int(xs[H]), int(ys[H]))
def Sk(k):
    x=('F',)
    for _ in range(k): x=('b',x)
    return ('b',('o',('n',('q',)),x)) if ('n',('q',))<x else ('b',('o',x,('n',('q',))))
def Tk(k):
    x=('F',)
    for _ in range(k): x=('b',x)
    a,b=sorted([('n',('p',)),x])
    return ('n',('b',('o',a,b)))
KQ, KP = 40, 22
# 1. naive vs bitmask on samples
random.seed(7)
samp=[]
for s in range(2,9): samp+=random.sample(list(gen(s,0,True,'pq')),min(60,len(gen(s,0,True,'pq'))))
samp+=[Sk(k) for k in range(1,5)]+[Tk(k) for k in range(1,5)]
for f in samp:
    for j in (1,2,3,4):
        H=2*(nbox(f)+j)
        assert game(f,j)==naive_game(f,j,H), (show(f),j)
print('bitmask = naive on', len(samp)*4, 'games')
# 2. full enumeration (all depths) for small k, no K58
for atoms,K,ex in (('pq',2,5),('p',2,6)):
    for k in range(1,K+1):
        mins=None
        for s in range(1,k+ex+1):
            sp=[f for f in gen(s,0,True,atoms) if game(f,k)!=game(f,k+1)]
            if sp: mins=(s,sp); break
        want = Sk(k) if atoms=='pq' else Tk(k)
        assert mins and mins[0]==k+ex and mins[1]==[want], (atoms,k,mins and [show(f) for f in mins[1]])
print('full enumeration k<=2 reproduces minima k+5 / k+6 without K58')
# 3. main: depth >= k+1 enumeration
for atoms,K,ex in (('pq',KQ,5),('p',KP,6)):
    tot=0
    for k in range(1,K+1):
        want = Sk(k) if atoms=='pq' else Tk(k)
        for s in range(k+2,k+ex):
            fs=gen(s,k+1,True,atoms); tot+=len(fs)
            for f in fs: assert game(f,k)==game(f,k+1), (atoms,k,show(f))
        fs=gen(k+ex,k+1,True,atoms); tot+=len(fs)
        sp=[f for f in fs if game(f,k)!=game(f,k+1)]
        assert sp==[want], (atoms,k,[show(f) for f in sp])
        assert size(want)==k+ex
        if atoms=='pq': assert game(want,k)==(1,1) and game(want,k+1)==(0,0)
        else: assert game(want,k)==(0,0) and game(want,k+1)==(1,0)
    print(atoms, 'k=1..%d'%K, 'formulas solved', tot, 'min size k+%d, unique reduced separator'%ex, round(time.time()-t0,1),'s')
print('PASS')
