"""C046 r1 (round 1): replicator dynamics on the exact size<=10 census in PD, Chicken and Stag Hunt.
Self-contained: re-enumerates the census (same language/dedup as c046_games10.py: atoms p,q boxed;
F,~,&,|,[]; size = syntax nodes; 7561 finite-linear-model classes) and re-solves every cell.
Payoffs (row): PD 3,0,5,1; Chicken (C=swerve) 3,1,4,0; Stag Hunt (C=stag) 4,0,3,2 for CC,CD,DC,DD.
Recurrence (float64): x <- x*(Ax)/(x.Ax), uniform start over the 7561 classes, 2000 steps, no
mutation, no cutoff. Exact reduction: classes with identical row and column of M (3402
observational classes) keep equal weights; the run is on the quotient, start weight multiplicity/n.
Asserts: in all three games the classes with weight > 1e-6 after 2000 steps are the same 1116
observational classes (2158 chain classes), all other weights < 1e-12 (gap check); mean payoff
equals R (3, 3, 4) within 1e-9; the survivor set S is exactly mutually cooperative (every pair in S,
including self-play, plays CC: exact) and maximal (no class outside S mutually cooperates with all
of S: exact); FairBot []p is in S, DefectBot is not.
"""
import sys, hashlib, time, json, random
import numpy as np
from collections import deque, Counter


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
def payoff(M,R,S_,T,P):
    Mt=M.T; return R*M*Mt+S_*M*(1-Mt)+T*(1-M)*Mt+P*(1-M)*(1-Mt)

def main():
    t0=time.time()
    U,G,fU,fG=enumerate_classes(10,log=False)
    order=sorted(fG,key=lambda c:(fG[c][0],fG[c][1])); n=len(order); assert n==7561
    names=[fG[c][1] for c in order]
    nb=max(s.count('[]') for s in names); H=4*nb+3
    TT,OO,S=matrix(order); M=solve_all(TT,OO,S,H).astype(np.int64)
    key={}; cls=np.array([key.setdefault(M[a].tobytes()+M[:,a].tobytes(),len(key)) for a in range(n)]); k=len(key)
    assert k==3402
    rep=np.array([np.flatnonzero(cls==c)[0] for c in range(k)]); mult=np.bincount(cls,minlength=k).astype(float)
    Mr=M[np.ix_(rep,rep)]
    surv=None
    for g,(R,Sx,T,P) in {'PD':(3,0,5,1),'CH':(3,1,4,0),'SH':(4,0,3,2)}.items():
        B=payoff(Mr,R,Sx,T,P).astype(float); z=mult/n
        for _ in range(2000):
            f=B@z; z=z*f/(z@f)
        s=z>1e-6
        assert s.sum()==1116 and z[~s].max()<1e-12 and mult[s].sum()==2158, (g,s.sum(),z[~s].max())
        assert abs(z@B@z-R)<1e-9
        if surv is None: surv=s
        assert (s==surv).all(), g
        print(g,'survivors',int(s.sum()),'max dead %.2e'%z[~s].max(),'%.1fs'%(time.time()-t0),flush=True)
    Si=np.flatnonzero(surv)
    assert Mr[np.ix_(Si,Si)].all()
    out=np.flatnonzero(~surv)
    assert not (Mr[np.ix_(out,Si)].all(1)&Mr[np.ix_(Si,out)].all(0)).any()
    idx={c:i for i,c in enumerate(order)}
    FBc=cls[idx[parse_m('[]p')]]; DBc=cls[idx[parse_m('F')]]
    assert surv[FBc] and not surv[DBc]
    print('PASS replicator10 %.1fs'%(time.time()-t0))

if __name__=='__main__':
    main()
