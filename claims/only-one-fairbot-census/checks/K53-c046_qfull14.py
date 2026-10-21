"""C046 r1: unexploitable self-cooperating agents in full L (atoms p,q) up to size 14, versus FairBot (extends c046_qfull13.py, K52).
Language L: F, ~, &, |, [] over p (opponent cooperates with me) and q (opponent cooperates with
DefectBot); agents guarded (every atom under a box); size = syntax-tree nodes. Height semantics on
the chain (game fixed points are letter-free); agents = Mealy machines; outcome = tail values.
Key fact: an opponent's move at height h is the same against an agent A and against DefectBot until A
or A's DefectBot trace d_A first cooperates (the opponent's inputs are all (0,0) until then). So the
input words an agent can meet are exactly those with p(h)=q(h) for h <= g*, g* that first height.
Asserts:
 (1) guarded classes per size 1..14 (279115 at size 14; 20441 up to 11, as in prior census);
 (2) exact exploitability over realizable words; every exploitable self-cooperator is exploited by an
     explicit opponent (~D & sigma_q) | (D & sigma_p), D = ~[](~p&~q), re-solved;
 (3) unexploitable self-cooperating machine classes per size, and behaviour classes (agreement on all
     realizable words plus equal DefectBot trace) per size of smallest member; 16756 up to size 14 (6548 up to 13, K52);
 (4) the FairBot behaviour class: []p plus machine-distinct members, smallest [](p|(q&[]F)) (size 7); 387 machine classes
     (exact: equal realizable-word machine, K18);
     each member agrees with FairBot against all guarded opponents of size <= 7;
 (5) each of the 26062 other machine classes (16755 behaviour classes) gets a different outcome from FairBot against an explicit
     opponent built from the first realizable distinguishing word (re-solved);
 (6) rank-0 classes: 2468 up to 14 (= K51 prefix); smallest agents not CC with FairBot have size 9;
     1058 behaviour classes not CC with FB, 15306 CC with both FB and CB;
     Speed-up: unguarded (U) Boolean products are skipped at the top size N, since unguarded formulas only feed boxes (size+1).
 (7) an independent literal-formula height evaluator confirms headline cells.
"""
import sys, time
from collections import Counter, defaultdict, deque
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
                for (pool, first, add) in (((G, firstG, addG),) if n == N else ((U, firstU, addU), (G, firstG, addG))):
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
    return U, G, firstU, firstG



N=14
t0=time.time()
U,G,fU,fG=enumerate_classes(N,log=False)
assert [len(G[n]) for n in range(1,N+1)]==[1,4,8,12,31,98,255,646,1760,4746,12880,36062,100823,279115]
assert sum(len(G[n]) for n in range(1,12))==20441

def tailrun(step,s):
    seen={};tr=[]
    while s not in seen: seen[s]=len(tr); o,s2=step(s); tr.append(o); s=s2
    cyc=tr[seen[s]:]; assert len(set(cyc))==1,cyc; return cyc[0]
def game(A,B):
    TA,OA=A;TB,OB=B
    def step(st):
        sa,sb,da,db=st; a=OA[sa][0]; b=OB[sb][0]
        return (a,b),(TA[sa][b+2*OB[db][0]],TB[sb][a+2*OA[da][0]],TA[da][0],TB[db][0])
    return tailrun(step,(0,0,0,0))

def bxk(k,m):
    for _ in range(k): m=box(m)
    return m
def at(g): return AND(bxk(g+1,BOT),neg(bxk(g,BOT)))
def sig(S,cof=False):
    m=BOT
    for g in S: m=OR(m,at(g))
    return neg(m) if cof else m
def reader(h,a): return box(OR(OR(neg(bxk(h+1,BOT)),bxk(h,BOT)),a))
D=neg(box(AND(neg(P),neg(Q))))
def detector_opp(Sq,cofq,Sp):
    return OR(AND(neg(D),sig(Sq,cofq)),AND(D,sig(Sp)))

def exploit(m):
    """None if unexploitable, else an explicit exploiter (re-solved by caller)."""
    T,O=m
    par={(0,0):None};st=deque([(0,0)]);post={}
    while st:
        s=st.popleft();sa,sd=s;det=O[sa][0] or O[sd][0]
        for x in (0,3):
            nx=T[sa][x]
            if det:
                if nx not in post: post[nx]=(s,x)
            else:
                ns=(nx,T[sd][0])
                if ns not in par: par[ns]=(s,x);st.append(ns)
    ppar={s:('pre',)+post[s] for s in post};st=deque(post)
    while st:
        s=st.popleft()
        for i in range(4):
            t=T[s][i]
            if t not in ppar: ppar[t]=('post',s,i);st.append(t)
    for s0 in ppar:
        for c in (0,1):
            if tailrun(lambda s:(O[s][0],T[s][2*c]),s0)==1:
                w=[];t=s0
                while True:
                    e=ppar[t]
                    if e[0]=='pre': w.append(e[2]);t=e[1];break
                    w.append(e[2]);t=e[1]
                while par[t] is not None: t,i=par[t];w.append(i)
                w.reverse();L=len(w)
                Sq=[g for g in range(L) if w[g]>>1]; Sp=[g for g in range(L) if w[g]&1]
                if c: Sq=[g for g in range(L) if not w[g]>>1]
                return detector_opp(Sq,bool(c),Sp)
    return None

def behav(m):
    T,O=m;idx={};st=[];tr=[];out=[];SINK=('sink',)
    def get(s):
        if s not in idx: idx[s]=len(st);st.append(s)
        return idx[s]
    get((0,0,0));k=0
    while k<len(st):
        s=st[k];k+=1
        if s==SINK: tr.append([idx[SINK]]*4);out.append([4]*4);continue
        sa,sd,ph=s;a=O[sa][0];d=O[sd][0];nph=1 if (ph or a or d) else 0
        tr.append([get(SINK) if (not ph and i in (1,2)) else get((T[sa][i],T[sd][0],nph)) for i in range(4)])
        out.append([a+2*d]*4)
    return canon(tr,out)

FB=box(P); CB=neg(BOT); DB=BOT
assert game(FB,FB)==(1,1) and exploit(FB) is None
selfc=[(n,s,c) for c,(n,s) in fG.items() if game(c,c)==(1,1)]
nexp=0
U_=[]
for n,s,c in selfc:
    B=exploit(c)
    if B is None: U_.append((n,s,c))
    else:
        assert game(c,B)==(1,0),s; nexp+=1
U_.sort()
cnt=Counter(n for n,_,_ in U_)
assert [cnt[n] for n in range(1,N+1)]==[0,1,1,1,3,6,14,45,127,318,863,2380,6180,16510],cnt
assert len(selfc)==249390 and nexp==222941 and len(U_)==26449
print('self-cooperators',len(selfc),'exploitable (explicit exploiter re-solved)',nexp,'unexploitable',len(U_))
bc=defaultdict(list)
for n,s,c in U_: bc[behav(c)].append((n,s,c))
fbk=behav(FB)
bcnt=Counter(L[0][0] for L in bc.values())
assert len(bc)==16756 and [bcnt[n] for n in range(1,N+1)]==[0,1,1,1,3,6,13,35,95,231,600,1588,3974,10208],bcnt
fbcls=bc[fbk]; print('FairBot behaviour class:',len(fbcls),'members, sizes',sorted(Counter(n for n,_,_ in fbcls).items()))
assert sorted(Counter(n for n,_,_ in fbcls).items())==[(2,1),(7,1),(8,5),(9,2),(10,8),(11,19),(12,50),(13,93),(14,208)]
assert fbcls[0][1]=='[]p' and fbcls[1][:2]==(7,'[](p|(q&[]F))')
bank=[c for c,(n,s) in fG.items() if n<=7]
ref=[game(FB,B) for B in bank]
for n,s,c in fbcls: assert [game(c,B) for B in bank]==ref,s
# separators
def dword(m1,m2):
    (T1,O1),(T2,O2)=m1,m2;prev={(0,0):None};dq=deque([(0,0)])
    while dq:
        s=dq.popleft();a,b=s
        if O1[a][0]!=O2[b][0]:
            w=[];t=s
            while prev[t] is not None: t,i=prev[t];w.append(i)
            w.reverse();return len(w),O1[a][0],O2[b][0],w
        for i in range(4):
            t=(T1[a][i],T2[b][i])
            if t not in prev: prev[t]=(s,i);dq.append(t)
def separator(c1,c2):
    h,o1,o2,w=dword(behav(c1),behav(c2))
    if (o1>>1)!=(o2>>1): return AND(neg(bxk(h+1,BOT)),reader(h,Q)),h
    Sq=[g for g,i in enumerate(w) if i>>1];Sp=[g for g,i in enumerate(w) if i&1]
    post=OR(AND(bxk(h+1,BOT),sig(Sp)),AND(neg(bxk(h+1,BOT)),reader(h,P)))
    return OR(AND(neg(D),sig(Sq)),AND(D,post)),h
hs=Counter()
for k,L in bc.items():
    if k==fbk: continue
    for n,s,c in L:
        B,h=separator(c,FB);hs[h]+=1
        assert game(c,B)!=game(FB,B),s
assert sum(hs.values())==26449-387 and len(fbcls)==387
print('machine classes separated from FairBot:',sum(hs.values()),'by distinguishing height',sorted(hs.items()))
# rank 0 (K1) and K2 extension
r0=Counter(L[0][0] for L in bc.values() if any('q' not in s for _,s,_ in L))
assert sum(r0.values())==2468,r0
nofb=sorted(L[0][:2] for L in bc.values() if game(L[0][2],FB)!=(1,1))
assert nofb[0][0]==9
fbcb=[L[0] for k,L in bc.items() if game(L[0][2],FB)==(1,1) and game(L[0][2],CB)==(1,1)]
assert len(fbcb)==15306 and len(nofb)==1058
print('behaviour classes',len(bc),'nonFB',len(bc)-1,'not CC with FB',len(nofb),'CC with FB and CB',len(fbcb))
print('rank-0 classes',sum(r0.values()),'; behaviour classes not CC with FB',len(nofb),'smallest',nofb[:3])

# (7) independent literal evaluator
def parse(s):
    i=[0]
    def e():
        c=s[i[0]]
        if c=='(':
            i[0]+=1;a=e();op=s[i[0]];i[0]+=1;b=e();assert s[i[0]]==')';i[0]+=1;return (op,a,b)
        if c=='~': i[0]+=1;return ('~',e())
        if s.startswith('[]',i[0]): i[0]+=2;return ('[]',e())
        i[0]+=1;return c
    t=e();assert i[0]==len(s);return t
def val(f,h,pp,qq,memo):
    k=(id(f),h)
    if k in memo: return memo[k]
    if f=='F': r=0
    elif f=='T': r=1
    elif f=='p': r=pp[h]
    elif f=='q': r=qq[h]
    elif f[0]=='~': r=1-val(f[1],h,pp,qq,memo)
    elif f[0]=='&': r=val(f[1],h,pp,qq,memo)&val(f[2],h,pp,qq,memo)
    elif f[0]=='|': r=val(f[1],h,pp,qq,memo)|val(f[2],h,pp,qq,memo)
    else: r=int(all(val(f[1],g,pp,qq,memo) for g in range(h)))
    memo[k]=r;return r
def lit_game(sa,sb,H=40):
    fa,fb=parse(sa),parse(sb);a=[];b=[];da=[];db=[];ma={};mb={};mda={};mdb={};Z=[0]*H
    for h in range(H):
        da.append(val(fa,h,Z,Z,mda));db.append(val(fb,h,Z,Z,mdb))
        a.append(val(fa,h,b+[None],db+[None],ma));b.append(val(fb,h,a[:-1]+[None],da+[None],mb))
    assert len(set(a[-10:]))==1 and len(set(b[-10:]))==1
    return a[-1],b[-1]
X='[](p|(q&[]F))'
for opp in ['[]p','~F','F','[][]p','[](p|q)',X,'([]p&[](~[]F|~q))']:
    assert lit_game(X,opp)==lit_game('[]p',opp),opp
small=[s for c,(n,s) in fG.items() if n<=6]
for o in small: assert lit_game(X,o)==lit_game('[]p',o)
assert lit_game('[](p|q)','[](p|q)')==(1,1)
assert lit_game('[](p|q)','[]~p')==(1,0)
print('literal evaluator agrees; total %.1fs'%(time.time()-t0))
print('PASS')
