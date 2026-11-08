"""Exact ranks over F3 for canonical MatchingLabels at (m,n,d)=(16,7,2).
Bit planes store residues 1 and 2; no packages, randomness or tolerance.
The canonical definitions are transcribed explicitly below. Integer vector
spanning modulo 3 is equivalent to rank(S)=number_labels-rank(top), once
all generators have top zero. This check verifies that inclusion separately.
"""
from itertools import combinations
M,N=16,7
labels=[(((a,b),),True,i) for a in range(M) for b in range(N) for i in range(M) if i!=a]
labels += [(((a,b),),False,j) for a in range(M) for b in range(N) for j in range(N) if j!=b]
index={g:i for i,g in enumerate(labels)}
assert len(index)==len(labels)==2352

def add(x,y):
    a,b=x;c,d=y
    z=~(a|b);w=~(c|d)
    return ((z&c)|(a&w)|(b&d), (z&d)|(b&w)|(a&c))

def rank(rows):
    basis={}
    for x in rows:
        while x[0]|x[1]:
            k=(x[0]|x[1]).bit_length()-1
            if k not in basis:
                if x[1]>>k&1:x=x[::-1]
                basis[k]=x;break
            y=basis[k]
            x=add(x,y if x[1]>>k&1 else y[::-1])
    return len(basis)

def pack(v):
    a=b=0
    for i,t in v.items():
        if t%3==1:a|=1<<i
        elif t%3==2:b|=1<<i
    return a,b

def vector(terms):
    v={}
    for c,g in terms:
        i=index[g];v[i]=(v.get(i,0)+c)%3
    return {i:c for i,c in v.items() if c}

def generators():
    for a,b in combinations(range(M),2):
        yield vector([(1,(((b,j),),True,a)) for j in range(N)]+[(-1,(((a,j),),True,b)) for j in range(N)])
    for a,b in combinations(range(N),2):
        yield vector([(1,(((i,b),),False,a)) for i in range(M)]+[(-1,(((i,a),),False,b)) for i in range(M)])
    for i in range(M):
        for j in range(N):
            yield vector([(1,(((a,j),),True,i)) for a in range(M) if a!=i]+[(-1,(((i,b),),False,j)) for b in range(N) if b!=j])
    # t=1: one anchored Z for every singleton matching.
    for a in range(M):
        for b in range(N):
            yield vector([(1,(((a,b),),True,i)) for i in range(M) if i!=a]+[(-1,(((a,b),),False,j)) for j in range(N) if j!=b])
    # t=2: empty anchor; maximal comparisons concern E only.
    yield vector([(1,(((a,b),),True,i)) for a in range(M) for b in range(N) for i in range(a+1,M)]+[(-1,(((a,b),),False,j)) for a in range(M) for b in range(N) for j in range(b+1,N)])

def main():
    for a in range(3):
        for b in range(3):
            assert add(pack({0:a}),pack({0:b})) == pack({0:(a+b)%3})
    # Canonical top coefficient rows: every 2-matching contributes four labels.
    tops=[]
    for a,c in combinations(range(M),2):
        for b in range(N):
            for d in range(N):
                if b==d:continue
                tops.append({index[g]:1 for g in [(((a,b),),True,c),(((a,b),),False,d),(((c,d),),True,a),(((c,d),),False,b)]})
    gs=list(generators())
    assert len(tops)==5040 and len(gs)==366
    for g in gs:
        assert all(sum(g.get(i,0)*v for i,v in t.items())%3==0 for t in tops), 'generator outside Kernel'
    rt=rank(map(pack,tops));rs=rank(map(pack,gs));nullity=len(labels)-rt
    print('# ar-table')
    print('m|n|r|field|labels|top_rows|top_rank|kernel_dimension|generators|generator_rank|holds')
    print(f'{M}|{N}|2|F3|{len(labels)}|{len(tops)}|{rt}|{nullity}|{len(gs)}|{rs}|{rs==nullity}')
    assert (rt,rs,nullity)==(2009,343,343)
    assert rs==nullity, ('Spanning fails',rs,nullity)
if __name__=='__main__':main()
