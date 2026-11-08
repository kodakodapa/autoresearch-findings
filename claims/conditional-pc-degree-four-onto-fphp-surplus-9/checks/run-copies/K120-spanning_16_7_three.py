"""Exact F3 rank decision for MatchingLabels.Spanning(3,16,7,3).
Self-contained transcription of matchings, labels, topLabel and syzygies.
Runs as a detached approved job, not an interactive step.
"""
from itertools import combinations,permutations
from time import monotonic
M,N,D=16,7,3

def matchings(d):
    for rs in combinations(range(M),d):
        for cs in permutations(range(N),d):yield tuple(zip(rs,cs))
def rows(b):return [i for i in range(M) if all(i!=a for a,c in b)]
def cols(b):return [j for j in range(N) if all(j!=c for a,c in b)]
def ordered(b):return tuple(sorted(b))
labels=[(b,r,i) for b in matchings(D-1) for r,marks in [(True,rows(b)),(False,cols(b))] for i in marks]
index={g:i for i,g in enumerate(labels)}
assert len(index)==len(labels)==95760

def vector(terms):
    v={}
    for c,g in terms:
        i=index[g];v[i]=(v.get(i,0)+c)%3
    return {i:c for i,c in v.items() if c}
def gens():
    for b in matchings(D-2):
        rr,cc=rows(b),cols(b)
        for a,c in combinations(rr,2):
            yield vector([(1,(ordered(b+((c,j),)),True,a)) for j in cc]+[(-1,(ordered(b+((a,j),)),True,c)) for j in cc])
        for a,c in combinations(cc,2):
            yield vector([(1,(ordered(b+((i,c),)),False,a)) for i in rr]+[(-1,(ordered(b+((i,a),)),False,c)) for i in rr])
        for i in rr:
            for j in cc:
                yield vector([(1,(ordered(b+((a,j),)),True,i)) for a in rr if a!=i]+[(-1,(ordered(b+((i,c),)),False,j)) for c in cc if c!=j])
    for t in range(1,D+1):
        for b in matchings(D-t):
            terms=[]
            for e in matchings(t-1):
                if not all(a in rows(b) and c in cols(b) for a,c in e):continue
                base=ordered(b+e)
                terms += [(1,(base,True,i)) for i in rows(base) if all(a<i for a,c in e)]
                terms += [(-1,(base,False,j)) for j in cols(base) if all(c<j for a,c in e)]
            yield vector(terms)
def top_zero(v):
    out={}
    for k,c in v.items():
        b,r,i=labels[k]
        for j in (cols(b) if r else rows(b)):
            e=(i,j) if r else (j,i)
            key=ordered(b+(e,));out[key]=(out.get(key,0)+c)%3
    return all(c==0 for c in out.values())
def pack(v):
    a=b=0
    for i,c in v.items():
        if c%3==1:a|=1<<i
        elif c%3==2:b|=1<<i
    return a,b
def add(x,y):
    a,b=x;c,d=y;z=~(a|b);w=~(c|d)
    return (z&c)|(a&w)|(b&d),(z&d)|(b&w)|(a&c)
def rank(stream,name):
    basis={};start=monotonic();count=0
    for v in stream:
        count+=1;x=pack(v)
        while x[0]|x[1]:
            k=(x[0]|x[1]).bit_length()-1
            if k not in basis:
                if x[1]>>k&1:x=x[::-1]
                basis[k]=x;break
            y=basis[k];x=add(x,y if x[1]>>k&1 else y[::-1])
        if count%1000==0:print(name,count,len(basis),round(monotonic()-start,2),flush=True)
    return len(basis),count

def checked_gens():
    for v in gens():
        assert top_zero(v),'generator not in kernel'
        yield v

def tops():
    for b in matchings(D):
        yield {index[(b[:k]+b[k+1:],r,e[0] if r else e[1])]:1 for k,e in enumerate(b) for r in [True,False]}

def main():
    for a in range(3):
        for b in range(3):assert add(pack({0:a}),pack({0:b}))==pack({0:(a+b)%3})
    rg,ng=rank(checked_gens(),'generators')
    print('GENERATOR_RANK',rg,'COUNT',ng,flush=True)
    assert ng==28673
    rt,nt=rank(tops(),'top')
    assert nt==117600 and rt+rg<=len(labels)
    print('# ar-table')
    print('m|n|r|field|labels|top_rows|top_rank|kernel_dimension|generators|generator_rank|holds')
    print(f'{M}|{N}|{D}|F3|{len(labels)}|{nt}|{rt}|{len(labels)-rt}|{ng}|{rg}|{rg+rt==len(labels)}',flush=True)
if __name__=='__main__':main()
