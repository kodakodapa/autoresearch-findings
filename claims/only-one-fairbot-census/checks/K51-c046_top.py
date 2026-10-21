"""C046 r1 (round 35): rank-0 census extended to size 15 (derived from c046_ponly12.py, same engine).
Original docstring follows (counts there are for size 12).
C046 r1: rank-0 (p-only) unexploitable self-cooperating agents up to size 12 vs FairBot.
Language: F, ~, &, |, [] over the single atom p (opponent cooperates with me), every p under a box;
size = syntax-tree nodes. Opponents may use the full language (q = opponent cooperates with DefectBot).
Agents up to equivalence on finite linear GL models (Mealy machines on the height chain; game fixed
points are letter-free). Outcomes are tail values (standard model). Boolean and exact.
Asserts: (1) guarded p-only classes per size 1..12;
 (2) exact unexploitability: a p-only agent is exploitable iff some reachable state's constant-defect orbit
     ends in an all-cooperate cycle; each exploitable self-cooperator is exploited by an explicit letterless
     opponent (re-solved by an independent height-table solver);
 (3) 591 unexploitable self-cooperating classes, per size 1,1,1,3,6,9,15,37,80,148,290 (sizes 2..12);
 (4) each of the 590 not equal to FairBot []p gets a different outcome than FairBot against an explicit opponent
     built from the first input word on which the machines differ (prefix-letterless + read-p-at-height-h);
 (5) the smallest such agents defecting against FairBot have size 9, e.g. ~[]F&[](p|[]F);
 (6) depth 1 (known, Hatfield-Dodds): only FairBot among Boolean functions of []p, []~p, []F.
"""
import sys, time
NI=2
def canon(trans,out,init=0):
    seen={init};order=[init];k=0
    while k<len(order):
        s=order[k];k+=1
        for i in range(NI):
            t=trans[s][i]
            if t not in seen: seen.add(t);order.append(t)
    block={s:tuple(out[s]) for s in order}
    while True:
        sig={s:(block[s],)+tuple(block[trans[s][i]] for i in range(NI)) for s in order}
        ids={};nb={s:ids.setdefault(sig[s],len(ids)) for s in order}
        old=len(set(block.values()));block=nb
        if len(ids)==old:break
    rep={}
    for s in order: rep.setdefault(block[s],s)
    num={block[init]:0};q=[block[init]];k=0;T=[];O=[]
    while k<len(q):
        b=q[k];k+=1;s=rep[b];row=[]
        for i in range(NI):
            tb=block[trans[s][i]]
            if tb not in num: num[tb]=len(q);q.append(tb)
            row.append(num[tb])
        T.append(tuple(row));O.append(tuple(out[s]))
    return (tuple(T),tuple(O))
BOT=canon([[0,0]],[[0,0]]); P=canon([[0,0]],[[0,1]])
def neg(m):
    T,O=m; return canon([list(r) for r in T],[[1-o for o in r] for r in O])
def binop(m1,m2,f):
    T1,O1=m1;T2,O2=m2;idx={(0,0):0};st=[(0,0)];tr=[];out=[];k=0
    while k<len(st):
        a,b=st[k];k+=1;row=[]
        for i in range(NI):
            t=(T1[a][i],T2[b][i])
            if t not in idx: idx[t]=len(st);st.append(t)
            row.append(idx[t])
        tr.append(row);out.append([f(O1[a][i],O2[b][i]) for i in range(NI)])
    return canon(tr,out)
AND=lambda a,b:binop(a,b,lambda x,y:x&y); OR=lambda a,b:binop(a,b,lambda x,y:x|y)
def box(m):
    T,O=m;idx={(0,1):0};st=[(0,1)];tr=[];out=[];k=0
    while k<len(st):
        s,f=st[k];k+=1;row=[]
        for i in range(NI):
            t=(T[s][i],f&O[s][i])
            if t not in idx: idx[t]=len(st);st.append(t)
            row.append(idx[t])
        tr.append(row);out.append([f]*NI)
    return canon(tr,out)
def enum(N):
    U={};G={};fU={};fG={}
    for n in range(1,N+1):
        t0=time.time();U[n]=[];G[n]=[]
        def aU(c,s):
            if c not in fU: fU[c]=(n,s);U[n].append(c)
        def aG(c,s):
            if c not in fG: fG[c]=(n,s);G[n].append(c)
        if n==1:
            aU(BOT,'F');aU(P,'p');aG(BOT,'F')
            if TOP: aU(neg(BOT),'~F');aG(neg(BOT),'~F')
        else:
            for c in U[n-1]:
                s=fU[c][1];aU(neg(c),'~'+s);b=box(c);aU(b,'[]'+s);aG(b,'[]'+s)
            for c in G[n-1]: aG(neg(c),'~'+fG[c][1])
            for i in range(1,n-1):
                j=n-1-i
                if i>j:break
                for pool,first,add in ((U,fU,aU),(G,fG,aG)):
                    for ai,a in enumerate(pool[i]):
                        sa=first[a][1]
                        for bi,b in enumerate(pool[j]):
                            if i==j and bi<ai:continue
                            sb=first[b][1]
                            add(AND(a,b),'('+sa+'&'+sb+')');add(OR(a,b),'('+sa+'|'+sb+')')
        for c in G[n]: aU(c,fG[c][1])
    return U,G,fU,fG

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



def sigma(S): # letterless, true exactly at heights in finite set S
    parts=['(%s&~%s)'%('[]'*(g+1)+'F','[]'*g+'F') if g>0 else '[]F' for g in sorted(S)]
    if not parts: return 'F'
    out=parts[0]
    for x in parts[1:]: out='('+out+'|'+x+')'
    return out
def read_at(h): # at heights > h: true iff p held at height h
    return '[](%s|(%s|p))'%('~'+'[]'*(h+1)+'F','[]'*h+'F' if h>0 else 'F')
def outw(m,w): # output at height len(w) after inputs w
    T,O=m; s=0
    for x in w: s=T[s][x]
    return O[s][0]
def first_diff(a,b):
    (Ta,Oa),(Tb,Ob)=a,b; seen={(0,0):()}; fr=[(0,0)]
    while fr:
        nx=[]
        for st in fr:
            if Oa[st[0]][0]!=Ob[st[1]][0]: return seen[st]
            for x in range(2):
                t=(Ta[st[0]][x],Tb[st[1]][x])
                if t not in seen: seen[t]=seen[st]+(x,); nx.append(t)
        fr=nx
    return None
def selftail(m):
    T,O=m; s=0; seen={}; tr=[]
    while s not in seen: seen[s]=len(tr); o=O[s][0]; tr.append(o); s=T[s][o]
    cyc=tr[seen[s]:]; assert len(set(cyc))==1; return cyc[0]
def exploit_word(m):
    """exact criterion: a reachable state whose constant-0-input orbit ends in an all-cooperate cycle.
    Returns a word reaching it, or None (then unexploitable by every opponent)."""
    T,O=m; seen={0:()}; fr=[0]
    while fr:
        nx=[]
        for s in fr:
            for x in range(2):
                if T[s][x] not in seen: seen[T[s][x]]=seen[s]+(x,); nx.append(T[s][x])
        fr=nx
    for s0 in sorted(seen,key=lambda s:(len(seen[s]),seen[s])):
        s=s0; vis=[]
        while s not in vis: vis.append(s); s=T[s][0]
        cyc=vis[vis.index(s):]
        if all(O[c][0]==1 for c in cyc): return seen[s0]
    return None
def main():
    # Primitive-top robustness (sk P266): enumerate again with T (=~F, a CooperateBot) as a size-1 primitive.
    # Expected: T is absorbed in every context (~T=F is smaller, []T=T, T&x=x, T|x=T), so only the class T
    # itself moves (size 2 -> 1); guarded counts from size 3 and the unexploitable self-cooperators are unchanged.
    global TOP
    from collections import Counter
    N=13; res={}
    for top in (False,True):
        TOP=top
        U,G,fU,fG=enum(N)
        good=Counter(fG[c][0] for c in fG if selftail(c) and exploit_word(c) is None)
        res[top]=([len(G[n]) for n in range(1,N+1)],sorted(good.items()),fG[neg(BOT)][0])
    a,b=res[False],res[True]
    assert a[0]==[1,3,5,6,9,25,60,102,189,424,925,1854,3755],a[0]
    assert b[0]==[2,2]+a[0][2:],b[0]
    assert a[2]==2 and b[2]==1
    assert a[1]==b[1] and sum(v for _,v in a[1])==1202,(a[1],b[1])
    assert not selftail(neg(BOT)) or exploit_word(neg(BOT)) is not None   # T itself is exploitable
    print('PASS: primitive top changes guarded counts only at sizes 1,2',a[0][:3],'->',b[0][:3],'; unexploitable self-cooperators unchanged',sum(v for _,v in a[1]),dict(a[1]))
TOP=False
main()
