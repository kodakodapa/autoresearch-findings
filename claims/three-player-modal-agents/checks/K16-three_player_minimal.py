"""Exhaustive guarded syntax through size 3, augmented by size-4 FairBot."""
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
        return ('v',(mask if f[0]=='p' else mask | (1<<slot),opponent))
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

# Enumerate raw ordered syntax, size nodes, then retain guarded trees.
def guarded(t,inside=False):
    if t[0] in ('p','q'): return inside
    return all(guarded(x,inside or t[0]=='box') for x in t[1:])
def compile_tree(t):
    if t[0]=='not': return neg(compile_tree(t[1]))
    if t[0]=='and': return conj(compile_tree(t[1]),compile_tree(t[2]))
    if t[0]=='or': return disj(compile_tree(t[1]),compile_tree(t[2]))
    return (t[0],)+tuple(compile_tree(x) for x in t[1:]) if t[0] not in ('p','q') else t
raw={1:[F,p0,p1,q0,q1]}
for n in (2,3):
    raw[n]=[(op,t) for op in ('not','box') for t in raw[n-1]]
    for k in range(1,n-1):
        raw[n]+=[(op,a,b) for op in ('and','or') for a in raw[k] for b in raw[n-1-k]]
trees=[t for n in (1,2,3) for t in raw[n] if guarded(t)]
print('raw counts',[sum(guarded(t) for t in raw[n]) for n in (1,2,3)],flush=True)
# Syntactically identical compiled formulas share a representative; multiplicities retained.
unique=list(dict.fromkeys(compile_tree(t) for t in trees))
bots={str(i):t for i,t in enumerate(unique)}
bots['F3']=box(conj(p0,p1))
assert len(trees)==25 and len(unique)==24 and len(bots)==25
print('compiled representatives plus FairBot',len(bots),flush=True)
matrix={ns:solve(ns) for ns in product(bots,repeat=3)}
def payoff(a,i): return 2*sum(a)-3*a[i]
safe=[a for a in bots if all(payoff(matrix[a,b,c],0)>=payoff(matrix[a,b,c],i)
    for b,c in product(bots,repeat=2) for i in (1,2))]
selfcoop=[a for a in bots if matrix[a,a,a]==(True,)*3]
print('safe',[(a,bots[a]) for a in safe],flush=True)
print('selfcoop',selfcoop,'intersection',set(safe)&set(selfcoop),flush=True)
assert set(safe)&set(selfcoop)=={'F3'}
assert matrix['F3','F3','F3']==(True,True,True)
print('PASS',len(matrix),'triples;',24*len(matrix),'equations')
# Every smaller self-cooperator has a certified disadvantage witness.
for a in selfcoop:
    if a=='F3': continue
    witnesses=[(b,c,i) for b,c in product(bots,repeat=2) for i in (1,2)
               if payoff(matrix[a,b,c],0)<payoff(matrix[a,b,c],i)]
    assert witnesses,a
# FairBot also defects with D in either opponent slot, across this entire set.
for b in bots:
    assert not matrix['F3','0',b][0]
    assert not matrix['F3',b,'0'][0]

# Universal upper bound reproduced from r1 K14, with attribution.
import subprocess, shutil, os
LEAN = r'''
theorem fair3_tail (x y z : Nat → Prop) (hx : ∀ h, x h ↔ ∀ g, g < h → y g ∧ z g)
    (T : Nat) (X Y Z : Prop) (hX : ∀ h, T ≤ h → (x h ↔ X)) (hY : ∀ h, T ≤ h → (y h ↔ Y))
    (hZ : ∀ h, T ≤ h → (z h ↔ Z)) : X → Y ∧ Z := by
  intro hxX
  have H := (hx (T+1)).1 ((hX (T+1) (by omega)).2 hxX) T (by omega)
  exact ⟨(hY T (Nat.le_refl T)).1 H.1, (hZ T (Nat.le_refl T)).1 H.2⟩
def u (a b c : Bool) : Int := 2 * ((if a then 1 else 0) + (if b then 1 else 0) + (if c then 1 else 0)) - 3 * (if a then 1 else 0)
theorem fair3_payoff : ∀ X Y Z : Bool, (X = true → Y = true ∧ Z = true) →
    u Y X Z ≤ u X Y Z ∧ u Z X Y ≤ u X Y Z := by decide
#print axioms fair3_tail
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
print('(4) Lean: fair3_tail, fair3_payoff proved; false variant rejected')
print('PASS')
