"""Standalone three-player GL certification, stdlib only; 5 named bots, not a census."""
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
def closed(trace):
    m = len(trace) - 1
    while m > 0 and trace[m - 1] == trace[-1]: m -= 1
    if m == 0: return T if trace[-1] else F
    parts = [conj(boxn(F, h + 1), neg(boxn(F, h))) for h in range(m) if trace[h]]
    if trace[-1]: parts.append(neg(boxn(F, m)))
    out = parts[0]
    for q in parts[1:]: out = disj(out, q)
    return out

from itertools import product
# Fixed slots; local opponent order is increasing global slot order.
# q_j reads that opponent after replacing the evaluator by D.
def instantiate(f, mask, slot):
    if f[0] in ('p','q'):
        opponent=[j for j in range(3) if j!=slot][f[1]]
        return ('v',(mask if f[0]=='p' else mask | ((1<<slot) if MODE=='evaluator' else (7 ^ (1<<opponent))),opponent))
    return (f[0],)+tuple(instantiate(x,mask,slot) for x in f[1:])
def replace(f, values):
    if f[0]=='v': return values[f[1]]
    return (f[0],)+tuple(replace(x,values) for x in f[1:])
def evaluate(f,h,tr):
    if f[0]=='F': return False
    if f[0]=='v': return tr[f[1]][h]
    if f[0]=='imp': return not evaluate(f[1],h,tr) or evaluate(f[2],h,tr)
    if f[0]=='box': return all(evaluate(f[1],g,tr) for g in range(h))
    raise AssertionError(f)
p0,p1=('p',0),('p',1)
q0,q1=('q',0),('q',1)
bots={'D':F,'C':T,'F':box(conj(p0,p1)), 'O':box(disj(p0,p1)), 'Q':box(conj(q0,q1))}
def solve(names):
    equations={(m,i):F if m & (1<<i) else instantiate(bots[names[i]],m,i)
               for m in range(8) for i in range(3)}
    tr={v:[] for v in equations}
    for h in range(12):
        row={v:evaluate(f,h,tr) for v,f in equations.items()}
        for v in tr: tr[v].append(row[v])
    candidates={v:closed(t) for v,t in tr.items()}
    # All 24 simultaneous equations certified, including counterfactual worlds.
    for v,f in equations.items():
        assert prove(iff(candidates[v],replace(f,candidates))),(names,v)
    # Changing each actual player in turn must break the simultaneous system.
    for i in range(3):
        bad=dict(candidates); bad[0,i]=neg(bad[0,i])
        assert not all(prove(iff(bad[v],replace(f,bad))) for v,f in equations.items())
    # Evaluate closed candidates beyond sampled heights, no box-as-identity shortcut.
    actual=tuple(evaluate(candidates[0,i],20,{}) for i in range(3))
    assert actual==tuple(tr[0,i][-1] for i in range(3))
    prove_seq.cache_clear()
    return actual

matrices={}
for MODE in ('evaluator','all_others'):
    matrices[MODE]={names:solve(names) for names in product(bots,repeat=3)}
differences=[(names,matrices['evaluator'][names],matrices['all_others'][names]) for names in matrices['evaluator'] if matrices['evaluator'][names]!=matrices['all_others'][names]]
assert len(differences)==9
expected={('Q','C','O'),('Q','O','C'),('Q','O','O'),('C','Q','O'),('O','Q','C'),('O','Q','O'),('C','O','Q'),('O','C','Q'),('O','O','Q')}
assert {x[0] for x in differences}==expected
for names,old,new in differences:
    assert old==(True,True,True)
    assert new==tuple(n!='Q' for n in names)
assert matrices['evaluator']['Q','O','C']==(True,True,True)
assert matrices['all_others']['Q','O','C']==(False,True,True)
assert all(matrices['evaluator'][n]==matrices['all_others'][n] for n in product(('D','C','F','O'),repeat=3))
print('PASS exact nine changed triples; QOC 111 -> 011; all probe-free triples unchanged')
print('PASS 250 triples, 6000 GL equations, 750 flip controls')
