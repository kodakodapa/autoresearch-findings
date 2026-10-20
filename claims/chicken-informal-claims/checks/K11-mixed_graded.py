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
def parse(s):
    def p(i):
        c = s[i]
        if c == 'F': return F, i + 1
        if c in 'pq': return (c,), i + 1
        if c == '~': m, j = p(i + 1); return neg(m), j
        if s.startswith('[]', i): m, j = p(i + 2); return box(m), j
        a, j = p(i + 1); op = s[j]; b, k = p(j + 1); assert s[k] == ')'
        return (conj if op == '&' else disj)(a, b), k + 1
    t, j = p(0); assert j == len(s); return t
def subst(f, pv, qv):
    t = f[0]
    if t == 'p': return pv
    if t == 'q': return qv
    if t == 'F': return f
    return (t,) + tuple(subst(x, pv, qv) for x in f[1:])
def ev(f, h, tr, vals):   # tr: dict name->list ; atoms ('v',name)
    t = f[0]
    if t == 'F': return False
    if t == 'v': return tr[f[1]][h]
    if t == 'imp': return (not ev(f[1], h, tr, vals)) or ev(f[2], h, tr, vals)
    if t == 'box': return all(ev(f[1], g, tr, vals) for g in range(h))
    raise ValueError(f)
def closed(trace):
    m = len(trace) - 1
    while m > 0 and trace[m - 1] == trace[-1]: m -= 1
    if m == 0: return T if trace[-1] else F
    parts = [conj(boxn(F, h + 1), neg(boxn(F, h))) for h in range(m) if trace[h]]
    if trace[-1]: parts.append(neg(boxn(F, m)))
    out = parts[0]
    for q in parts[1:]: out = disj(out, q)
    return out
def nb(f): return (f[0] == 'box') + sum(nb(x) for x in f[1:] if isinstance(x, tuple))
def solve(sa, sb):
    A, B = parse(sa), parse(sb)
    H = 2 * (nb(A) + nb(B)) + 4
    VX, VY = ('v', 'x'), ('v', 'y')
    # closed q-values: opponent vs DB (all-F inputs)
    def vsDB(f):
        tr = {}; t = []
        for h in range(H):
            t.append(ev(subst(f, F, F), h, {}, None))
        return t
    za, zb = vsDB(A), vsDB(B)
    CA, CB_ = closed(za), closed(zb)
    ex = subst(A, VY, CB_); ey = subst(B, VX, CA)
    tr = {'x': [], 'y': []}
    for h in range(H):
        xa = ev(ex, h, tr, None); yb = ev(ey, h, tr, None)
        tr['x'].append(xa); tr['y'].append(yb)
    cx, cy = closed(tr['x']), closed(tr['y'])
    sub = lambda f: subst_v(f, cx, cy)
    assert prove(iff(cx, sub(ex))) and prove(iff(cy, sub(ey)))
    # mutation control: flipping a candidate must be rejected
    assert not (prove(iff(neg(cx), sub(ex))) and prove(iff(cy, sub(ey))))
    assert not (prove(iff(cx, subst_v(ex, neg(cx), cy))) and prove(iff(neg(cx), subst_v(ex, neg(cx), cy))))
    return tr['x'][-1], tr['y'][-1]
def subst_v(f, cx, cy):
    if f[0] == 'v': return cx if f[1] == 'x' else cy
    if f[0] == 'F': return f
    return (f[0],) + tuple(subst_v(x, cx, cy) for x in f[1:])

# n iterated consistency axioms reduce to not box^n F over PA.
def prov(n,a):
    assert n >= 0
    return box(disj(boxn(F,n),a))
x,y=('v','x'),('v','y')
def careful(n,own,opp): return neg(prov(n,opp))
def bold(n,own,opp): return prov(n,neg(opp))
def astute(own,opp):
    d=neg(own)
    return neg(box(imp(neg(box(F)),conj(imp(d,box(d)),imp(box(d),opp)))))
def hobson(own,opp): return conj(neg(prov(0,opp)),prov(1,opp))
def fair(n,own,opp): return prov(n,opp)
def constant(b): return lambda own,opp: T if b else F

def truth(f):
    if f[0]=='F': return False
    if f[0]=='imp': return not truth(f[1]) or truth(f[2])
    if f[0]=='box': return truth(f[1])
    raise AssertionError(f)

def certify(A,B):
    ex,ey=A(x,y),B(y,x)
    H=2*(nb(ex)+nb(ey))+6
    tr={'x':[],'y':[]}
    for h in range(H):
        a,b=ev(ex,h,tr,None),ev(ey,h,tr,None)
        tr['x'].append(a); tr['y'].append(b)
    cx,cy=closed(tr['x']),closed(tr['y'])
    assert prove(iff(cx,subst_v(ex,cx,cy)))
    assert prove(iff(cy,subst_v(ey,cx,cy)))
    # Reject flipping either candidate in the simultaneous equations.
    for dx,dy in [(neg(cx),cy),(cx,neg(cy))]:
        assert not (prove(iff(dx,subst_v(ex,dx,dy))) and prove(iff(dy,subst_v(ey,dx,dy))))
    assert (truth(cx),truth(cy))==(tr['x'][-1],tr['y'][-1])
    prove_seq.cache_clear()
    return truth(cx),truth(cy)

def grade(fn,n): return lambda own,opp: fn(n,own,opp)

LEAN_SRC = '/- Height semantics of closed GL fixed points on the chain 0<1<2<...:\n   a world of height h sees exactly heights g<h, so box phi holds at h iff phi holds at all g<h.\n   Gate agent W_n(X) = box( box^n False  or  (p and (q or not box q)) ),\n   p = "X cooperates with W_n", q = "X cooperates with DefectBot". W_2 is K6\'s W (size 12).\n   gate n p q is the formula under the outer box; W_n\'s action is bx (gate n p q). -/\n\ndef bx (φ : Nat → Prop) : Nat → Prop := fun h => ∀ g, g < h → φ g\ndef bxn : Nat → (Nat → Prop) → (Nat → Prop)\n  | 0, φ => φ\n  | n+1, φ => bx (bxn n φ)\n\ntheorem bxn_succ_iff (n : Nat) (φ : Nat → Prop) (h : Nat) :\n    bxn (n+1) φ h ↔ ∀ g, g + (n+1) ≤ h → φ g := by\n  induction n generalizing h with\n  | zero =>\n    simp only [bxn, bx]\n    exact ⟨fun H g hg => H g (by omega), fun H g hg => H g (by omega)⟩\n  | succ n ih =>\n    show bx (bxn (n+1) φ) h ↔ _\n    simp only [bx]\n    constructor\n    · intro H g hg\n      exact (ih (h-1)).1 (H (h-1) (by omega)) g (by omega)\n    · intro H g\' hg\'\n      exact (ih g\').2 (fun g hg => H g (by omega))\n\ntheorem bxn_iff (n : Nat) (hn : 1 ≤ n) (φ : Nat → Prop) (h : Nat) :\n    bxn n φ h ↔ ∀ g, g + n ≤ h → φ g := by\n  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩\n  exact bxn_succ_iff m φ h\n\ndef botn (n : Nat) : Nat → Prop := bxn n (fun _ => False)\n\ntheorem botn_iff (n h : Nat) : botn n h ↔ h < n := by\n  cases n with\n  | zero => simp [botn, bxn]\n  | succ m =>\n    unfold botn; rw [bxn_succ_iff]\n    constructor\n    · intro H; apply Classical.byContradiction; intro hn\n      exact H 0 (by omega)\n    · intro hlt g hg; omega\n\n\ndef PB (n : Nat) (p : Nat → Prop) (h : Nat) : Prop :=\n  ∀ g, g < h → (g < n ∨ p g)\n\ntheorem bold_step (n m h : Nat) (y : Nat → Prop)\n    (ih : ∀ g, g < h → (y g ↔ g ≤ m ∨ n < m)) :\n    PB n (fun g => ¬ y g) h ↔ h ≤ n ∨ m < n := by\n  constructor\n  · intro hb\n    by_cases hn : h ≤ n\n    · exact Or.inl hn\n    · have hn\' : n < h := by omega\n      have hy := hb n hn\'\n      rcases hy with bad | ny\n      · omega\n      · have nm : ¬ n ≤ m := fun le => ny ((ih n hn\').2 (Or.inl le))\n        exact Or.inr (by omega)\n  · intro hh g gh\n    by_cases gn : g < n\n    · exact Or.inl gn\n    · right\n      intro yg\n      have yy := (ih g gh).1 yg\n      omega\n\ntheorem bold_all (n m : Nat) (x y : Nat → Prop)\n    (hx : ∀ h, x h ↔ PB n (fun g => ¬ y g) h)\n    (hy : ∀ h, y h ↔ PB m (fun g => ¬ x g) h) :\n    ∀ h, (x h ↔ h ≤ n ∨ m < n) ∧ (y h ↔ h ≤ m ∨ n < m) := by\n  intro h\n  induction h using Nat.strongRecOn with\n  | ind h ih =>\n    exact ⟨(hx h).trans (bold_step n m h y (fun g gh => (ih g gh).2)),\n      (hy h).trans (bold_step m n h x (fun g gh => (ih g gh).1))⟩\n\ntheorem careful_all (n m : Nat) (x y : Nat → Prop)\n    (hx : ∀ h, x h ↔ ¬ PB n y h)\n    (hy : ∀ h, y h ↔ ¬ PB m x h) :\n    ∀ h, (x h ↔ n < h ∧ n ≤ m) ∧ (y h ↔ m < h ∧ m ≤ n) := by\n  classical\n  have hnx : ∀ h, (¬ x h) ↔ PB n (fun g => ¬ ¬ y g) h := by\n    intro h\n    simp only [Classical.not_not]\n    exact not_congr (hx h) |>.trans (Classical.not_not)\n  have hny : ∀ h, (¬ y h) ↔ PB m (fun g => ¬ ¬ x g) h := by\n    intro h\n    simp only [Classical.not_not]\n    exact not_congr (hy h) |>.trans (Classical.not_not)\n  intro h\n  have hh := bold_all n m (fun g => ¬ x g) (fun g => ¬ y g) hnx hny h\n  constructor\n  · have := not_congr hh.1\n    simp only [Classical.not_not] at this\n    constructor\n    · intro xh\n      have := this.mp xh\n      omega\n    · intro cond\n      apply this.mpr\n      omega\n  · have := not_congr hh.2\n    simp only [Classical.not_not] at this\n    constructor\n    · intro yh\n      have := this.mp yh\n      omega\n    · intro cond\n      apply this.mpr\n      omega\n\n#print axioms bold_all\n#print axioms careful_all\n\n\ntheorem prov_bridge (n : Nat) (p : Nat → Prop) (h : Nat) :\n    bx (fun g => botn n g ∨ p g) h ↔ PB n p h := by\n  simp only [bx, PB, botn_iff]\n\n#print axioms prov_bridge\n\ntheorem mixed_all (n m : Nat) (x y : Nat → Prop)\n    (hx : ∀ h, x h ↔ ¬ PB n y h)\n    (hy : ∀ h, y h ↔ PB m (fun g => ¬ x g) h) :\n    ∀ h, ¬ x h ∧ y h := by\n  intro h\n  induction h using Nat.strongRecOn with\n  | ind h ih =>\n    constructor\n    · intro xx\n      exact (hx h).mp xx (fun g gh => Or.inr (ih g gh).2)\n    · apply (hy h).mpr\n      intro g gh\n      exact Or.inr (ih g gh).1\n#print axioms mixed_all\n'

import subprocess, shutil
lean=shutil.which('lean') or '/opt/elan/bin/lean'
r=subprocess.run([lean,'--stdin'], input=LEAN_SRC,text=True,capture_output=True,timeout=50)
assert r.returncode==0,r.stdout+r.stderr
assert 'sorryAx' not in r.stdout
assert r.stdout.count('depends on axioms')==3 and "'mixed_all' does not depend on any axioms" in r.stdout,r.stdout
bad=LEAN_SRC.replace('∀ h, ¬ x h ∧ y h := by','∀ h, x h ∧ y h := by')
r=subprocess.run([lean,'--stdin'],input=bad,text=True,capture_output=True,timeout=50)
assert r.returncode!=0,'reversed outcome accepted'
for n in range(5):
 for m in range(5):
  assert certify(grade(careful,n),grade(bold,m))==(False,True)
for n in range(16):
 for m in range(16):
  xs,ys=[],[]
  for h in range(40):
   a=not all(g<n or ys[g] for g in range(h))
   b=all(g<m or not xs[g] for g in range(h))
   assert (a,b)==(False,True),(n,m,h)
   xs.append(a);ys.append(b)
print('PASS mixed_all: Lean all indices; 25 GLS cells; 10240 recurrence cells; negative control')
