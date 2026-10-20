"""C046 r1 (round 2): Chicken agents that never crash, and the family Q_k = box^k F | ~box(p & q).
Language L: atoms p (opponent swerves against me), q (opponent swerves against NerveBot = DB = F);
constant F; ~,&,|,[]; every p,q under a box; size = syntax nodes; agents up to equivalence on
finite linear GL models (census engine copied from c046_games10.py). True/C = swerve.
SwerveBot = CB = ~F, FairBot FB = []p. Chicken payoffs 3/3, 1/4, 0/0 (only outcomes are used).
Criterion SU (universal no-crash, sound for every modal opponent): in the agent's minimized Moore
machine, from no reachable state does a constant input with p=0 (q=0 or 1) reach a cycle whose
outputs are all 0. Any game tail where the opponent goes straight is such a run.
Asserts (exact):
 (1) 7561 classes up to size 10; 808 agents crash against no census agent; 695 satisfy SU, all
     among the 808;
 (2) agents crashing against no census agent, going straight vs SwerveBot and mutually swerving with
     FairBot: exactly 4, sizes 9,10,10,10, all SU; the unique one of size <= 9 is Q_2 =
     ([][]F|~[](p&q)); Q_1 ([]F|~[](p&q)) and Q_0 ~[](p&q) fail only the FairBot clause;
 (3) GLS fixed-point certificates for Q_2 vs itself, FB, CB, DB, [][]p, [](p|[]F), Q_1, Q_3 and Q_1 vs FB;
 (4) explicit height tables, k,j,m,n <= 8: Q_k vs F_j=[]^j p, G_j=[]([]^j F|p), Q_m, B_n=[]([]^n F|~p)
     agree with the Lean laws;
 (5) embedded Lean 4 (core) proves for ALL indices, for any traces solving the height equations:
     q_safe, q_sb, q_nb, q_fj, q_gj, q_db, q_qm_lt, q_qq, q_bn (no sorryAx); a false variant is rejected.
Height semantics: closed GL fixed points are letter-free; box phi holds at height h iff phi holds at
all g < h (Boolos, Logic of Provability ch. 7); standard-model value = eventual value.
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



"""Independent exact game solver from formula strings (no machines).
Height table: value of box(f) at height h = AND of f over heights < h.
A game's joint value at height h is a function of the set of boxed subformulas
true at h (in A-vs-B, B-vs-A, A-vs-DB, B-vs-DB); that set only shrinks with h,
so it is constant from some height <= total number of boxes + 1 onward."""
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


# ---- GLS certificate prover (adapted from prior sk/gls_matrix_certs.py) ----
GLS_NS={}
exec(compile("import functools\nF = ('F',)\ndef imp(a, b): return ('imp', a, b)\ndef neg(a): return imp(a, F)\ndef box(a): return ('box', a)\ndef conj(a, b): return neg(imp(a, neg(b)))\ndef disj(a, b): return imp(neg(a), b)\nT = neg(F)\ndef iff(a, b): return conj(imp(a, b), imp(b, a))\ndef boxn(x, n):\n    for _ in range(n): x = box(x)\n    return x\nimport functools\n@functools.lru_cache(maxsize=None)\ndef prove_seq(L, R):\n    if F in L or L & R: return True\n    for f in L:\n        if f[0] == 'imp':\n            L2 = L - {f}\n            return prove_seq(L2, R | {f[1]}) and prove_seq(L2 | {f[2]}, R)\n    for f in R:\n        if f[0] == 'imp':\n            return prove_seq(L | {f[1]}, (R - {f}) | {f[2]})\n    boxedL = frozenset(f for f in L if f[0] == 'box')\n    unb = frozenset(f[1] for f in boxedL)\n    for f in R:\n        if f[0] == 'box' and prove_seq(boxedL | unb | {f}, frozenset({f[1]})): return True\n    return False\ndef prove(f): return prove_seq(frozenset(), frozenset({f}))\ndef gparse(s):\n    def p(i):\n        c = s[i]\n        if c == 'F': return F, i + 1\n        if c in 'pq': return (c,), i + 1\n        if c == '~': m, j = p(i + 1); return neg(m), j\n        if s.startswith('[]', i): m, j = p(i + 2); return box(m), j\n        a, j = p(i + 1); op = s[j]; b, k = p(j + 1); assert s[k] == ')'\n        return (conj if op == '&' else disj)(a, b), k + 1\n    t, j = p(0); assert j == len(s); return t\ndef subst(f, pv, qv):\n    t = f[0]\n    if t == 'p': return pv\n    if t == 'q': return qv\n    if t == 'F': return f\n    return (t,) + tuple(subst(x, pv, qv) for x in f[1:])\ndef ev(f, h, tr, vals):   # tr: dict name->list ; atoms ('v',name)\n    t = f[0]\n    if t == 'F': return False\n    if t == 'v': return tr[f[1]][h]\n    if t == 'imp': return (not ev(f[1], h, tr, vals)) or ev(f[2], h, tr, vals)\n    if t == 'box': return all(ev(f[1], g, tr, vals) for g in range(h))\n    raise ValueError(f)\ndef closed(trace):\n    m = len(trace) - 1\n    while m > 0 and trace[m - 1] == trace[-1]: m -= 1\n    if m == 0: return T if trace[-1] else F\n    parts = [conj(boxn(F, h + 1), neg(boxn(F, h))) for h in range(m) if trace[h]]\n    if trace[-1]: parts.append(neg(boxn(F, m)))\n    out = parts[0]\n    for q in parts[1:]: out = disj(out, q)\n    return out\ndef nb(f): return (f[0] == 'box') + sum(nb(x) for x in f[1:] if isinstance(x, tuple))\ndef solve(sa, sb):\n    A, B = gparse(sa), gparse(sb)\n    H = 2 * (nb(A) + nb(B)) + 4\n    VX, VY = ('v', 'x'), ('v', 'y')\n    # closed q-values: opponent vs DB (all-F inputs)\n    def vsDB(f):\n        tr = {}; t = []\n        for h in range(H):\n            t.append(ev(subst(f, F, F), h, {}, None))\n        return t\n    za, zb = vsDB(A), vsDB(B)\n    CA, CB_ = closed(za), closed(zb)\n    ex = subst(A, VY, CB_); ey = subst(B, VX, CA)\n    tr = {'x': [], 'y': []}\n    for h in range(H):\n        xa = ev(ex, h, tr, None); yb = ev(ey, h, tr, None)\n        tr['x'].append(xa); tr['y'].append(yb)\n    cx, cy = closed(tr['x']), closed(tr['y'])\n    sub = lambda f: subst_v(f, cx, cy)\n    assert prove(iff(cx, sub(ex))) and prove(iff(cy, sub(ey)))\n    # mutation control: flipping a candidate must be rejected\n    assert not (prove(iff(neg(cx), sub(ex))) and prove(iff(cy, sub(ey))))\n    assert not (prove(iff(cx, subst_v(ex, neg(cx), cy))) and prove(iff(neg(cx), subst_v(ex, neg(cx), cy))))\n    return tr['x'][-1], tr['y'][-1]\ndef subst_v(f, cx, cy):\n    if f[0] == 'v': return cx if f[1] == 'x' else cy\n    if f[0] == 'F': return f\n    return (f[0],) + tuple(subst_v(x, cx, cy) for x in f[1:])\n","gls","exec"),GLS_NS)
solve=GLS_NS["solve"]

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

import subprocess, shutil, os
LEAN_SRC = "def bx (φ : Nat → Prop) : Nat → Prop := fun h => ∀ g, g < h → φ g\ndef bxn : Nat → (Nat → Prop) → (Nat → Prop)\n  | 0, φ => φ\n  | n+1, φ => bx (bxn n φ)\n\ntheorem bxn_succ_iff (n : Nat) (φ : Nat → Prop) (h : Nat) :\n    bxn (n+1) φ h ↔ ∀ g, g + (n+1) ≤ h → φ g := by\n  induction n generalizing h with\n  | zero =>\n    simp only [bxn, bx]\n    exact ⟨fun H g hg => H g (by omega), fun H g hg => H g (by omega)⟩\n  | succ n ih =>\n    show bx (bxn (n+1) φ) h ↔ _\n    simp only [bx]\n    constructor\n    · intro H g hg\n      exact (ih (h-1)).1 (H (h-1) (by omega)) g (by omega)\n    · intro H g' hg'\n      exact (ih g').2 (fun g hg => H g (by omega))\n\ntheorem bxn_iff (n : Nat) (hn : 1 ≤ n) (φ : Nat → Prop) (h : Nat) :\n    bxn n φ h ↔ ∀ g, g + n ≤ h → φ g := by\n  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩\n  exact bxn_succ_iff m φ h\n\ndef botn (n : Nat) : Nat → Prop := bxn n (fun _ => False)\n\ntheorem botn_iff (n h : Nat) : botn n h ↔ h < n := by\n  cases n with\n  | zero => simp [botn, bxn]\n  | succ m =>\n    unfold botn; rw [bxn_succ_iff]\n    constructor\n    · intro H; apply Classical.byContradiction; intro hn\n      exact H 0 (by omega)\n    · intro hlt g hg; omega\n\n\ntheorem strong (P : Nat → Prop) (step : ∀ h, (∀ g, g < h → P g) → P h) : ∀ h, P h := by\n  have key : ∀ N h, h < N → P h := by\n    intro N\n    induction N with\n    | zero => intro h hh; omega\n    | succ N ih => intro h hh; exact step h (fun g hg => ih g (by omega))\n  exact fun h => key (h+1) h (by omega)\n\n/-! Chicken agent Q_k = box^k F ∨ ¬ box(p ∧ q); True = swerve.\n    p = opponent swerves vs Q_k, q = opponent swerves vs NerveBot (trace d). -/\ndef qk (k : Nat) (y d : Nat → Prop) : Nat → Prop := fun h => botn k h ∨ ¬ bx (fun g => y g ∧ d g) h\n\n/-- Universal safety (any opponent traces): if Q_k goes straight at h ≥ k, the opponent swerved\n    at every g < h; so Q_k and the opponent never both go straight from some height on. -/\ntheorem q_safe (k : Nat) (x y d : Nat → Prop) (hx : ∀ h, x h ↔ qk k y d h) :\n    (∀ h, k ≤ h → ¬ x h → ∀ g, g < h → y g) ∧ ¬ (∃ H, ∀ h, H ≤ h → ¬ x h ∧ ¬ y h) := by\n  have A : ∀ h, k ≤ h → ¬ x h → ∀ g, g < h → y g := by\n    intro h hk nx g hg\n    apply Classical.byContradiction; intro nyg\n    exact nx ((hx h).2 (Or.inr (fun H => nyg (H g hg).1)))\n  refine ⟨A, ?_⟩\n  intro ⟨H, hH⟩\n  exact (hH (H + k) (by omega)).2 (A (H + k + 1) (by omega) (hH (H + k + 1) (by omega)).1 (H + k) (by omega))\n\ntheorem q_sb (k : Nat) (x : Nat → Prop) (hx : ∀ h, x h ↔ qk k (fun _ => True) (fun _ => True) h) :\n    ∀ h, k ≤ h → ¬ x h := by\n  intro h hk xh\n  rcases (hx h).1 xh with hb | hn\n  · rw [botn_iff] at hb; omega\n  · exact hn (fun _ _ => ⟨trivial, trivial⟩)\n\ntheorem q_nb (k : Nat) (x d : Nat → Prop) (hx : ∀ h, x h ↔ qk k (fun _ => False) d h) :\n    ∀ h, 1 ≤ h → x h := fun h hh => (hx h).2 (Or.inr (fun H => (H 0 (by omega)).1))\n\n/-- vs graded FairBot F_j = box^j p (j ≥ 1), whose NerveBot trace is box^j F. -/\ntheorem q_fj (k j : Nat) (hj : 1 ≤ j) (x y d : Nat → Prop) (hd : ∀ h, d h ↔ botn j h)\n    (hx : ∀ h, x h ↔ qk k y d h) (hy : ∀ h, y h ↔ bxn j x h) :\n    (j < k → ∀ h, x h ∧ y h) ∧ (k ≤ j → (∀ h, j < h → x h) ∧ (∀ h, k + j ≤ h → ¬ y h)) := by\n  have hd' : ∀ h, d h ↔ h < j := fun h => by rw [hd, botn_iff]\n  have xj : ∀ h, j < h → x h := fun h hh =>\n    (hx h).2 (Or.inr (fun H => by have := (hd' j).1 (H j hh).2; omega))\n  constructor\n  · intro hjk\n    apply strong\n    intro h ih\n    have xh : x h := by\n      by_cases hk : h < k\n      · exact (hx h).2 (Or.inl ((botn_iff k h).2 hk))\n      · exact xj h (by omega)\n    refine ⟨xh, (hy h).2 ((bxn_iff j hj x h).2 (fun g hg => ?_))⟩\n    by_cases hgh : g < h\n    · exact (ih g hgh).1\n    · have : g = h := by omega\n      subst this; exact xh\n  · intro hkj\n    have yt : ∀ g, g < j → y g := fun g hg =>\n      (hy g).2 ((bxn_iff j hj x g).2 (fun t ht => by omega))\n    have nxk : ¬ x k := by\n      intro xk\n      rcases (hx k).1 xk with hb | hn\n      · rw [botn_iff] at hb; omega\n      · exact hn (fun g hg => ⟨yt g (by omega), (hd' g).2 (by omega)⟩)\n    refine ⟨xj, fun h hh yh => nxk ((bxn_iff j hj x h).1 ((hy h).1 yh) k (by omega))⟩\n\n/-- vs FairBot of PA+j, G_j = box(box^j F ∨ p), whose NerveBot trace holds iff h ≤ j. -/\ntheorem q_gj (k j : Nat) (x y d : Nat → Prop) (hd : ∀ h, d h ↔ h ≤ j)\n    (hx : ∀ h, x h ↔ qk k y d h) (hy : ∀ h, y h ↔ bx (fun g => botn j g ∨ x g) h) :\n    (j + 2 ≤ k → ∀ h, x h ∧ y h) ∧ (k ≤ j + 1 → (∀ h, j + 1 < h → x h ∧ ¬ y h)) := by\n  have xj : ∀ h, j + 1 < h → x h := fun h hh =>\n    (hx h).2 (Or.inr (fun H => by have := (hd (j+1)).1 (H (j+1) hh).2; omega))\n  constructor\n  · intro hjk\n    have xa : ∀ h, x h := fun h => by\n      by_cases hk : h < k\n      · exact (hx h).2 (Or.inl ((botn_iff k h).2 hk))\n      · exact xj h (by omega)\n    exact fun h => ⟨xa h, (hy h).2 (fun g _ => Or.inr (xa g))⟩\n  · intro hkj\n    have yt : ∀ g, g ≤ j → y g := fun g hg =>\n      (hy g).2 (fun t ht => Or.inl ((botn_iff j t).2 (by omega)))\n    have nxj : ¬ x (j+1) := by\n      intro xh\n      rcases (hx (j+1)).1 xh with hb | hn\n      · rw [botn_iff] at hb; omega\n      · exact hn (fun g hg => ⟨yt g (by omega), (hd g).2 (by omega)⟩)\n    intro h hh\n    refine ⟨xj h hh, fun yh => ?_⟩\n    rcases (hy h).1 yh (j+1) (by omega) with hb | xg\n    · rw [botn_iff] at hb; omega\n    · exact nxj xg\n\n/-- Q_m's NerveBot trace: true iff h < m or 1 ≤ h. -/\ntheorem q_db (m : Nat) (d : Nat → Prop) (e : Nat → Prop)\n    (hd : ∀ h, d h ↔ qk m (fun _ => False) e h) : ∀ h, d h ↔ (h < m ∨ 1 ≤ h) := by\n  intro h; rw [hd h]; unfold qk; rw [botn_iff]\n  constructor\n  · rintro (H | H)\n    · exact Or.inl H\n    · apply Classical.byContradiction; intro hn\n      exact H (fun g hg => by omega)\n  · rintro (H | H)\n    · exact Or.inl H\n    · exact Or.inr (fun K => (K 0 (by omega)).1)\n\n/-- Q_k vs Q_m: lower index goes straight, higher swerves; equal indices (self-play) swerve. -/\ntheorem q_qm_lt (k m : Nat) (hkm : k < m) (x y dk dm : Nat → Prop)\n    (hdm : ∀ h, dm h ↔ (h < m ∨ 1 ≤ h))\n    (hx : ∀ h, x h ↔ qk k y dm h) (hy : ∀ h, y h ↔ qk m x dk h) :\n    ∀ h, (k ≤ h → ¬ x h) ∧ y h := by\n  apply strong\n  intro h ih\n  constructor\n  · intro hk xh\n    rcases (hx h).1 xh with hb | hn\n    · rw [botn_iff] at hb; omega\n    · exact hn (fun g hg => ⟨(ih g hg).2, (hdm g).2 (by omega)⟩)\n  · by_cases hm : h < m\n    · exact (hy h).2 (Or.inl ((botn_iff m h).2 hm))\n    · exact (hy h).2 (Or.inr (fun H => (ih k (by omega)).1 (Nat.le_refl _) (H k (by omega)).1))\n\ntheorem q_qq (k : Nat) (x y d : Nat → Prop) (hd : ∀ h, d h ↔ (h < k ∨ 1 ≤ h))\n    (hx : ∀ h, x h ↔ qk k y d h) (hy : ∀ h, y h ↔ qk k x d h) :\n    ∀ h, k < h → x h ∧ y h := by\n  have yt : ∀ g, g < k → y g := fun g hg => (hy g).2 (Or.inl ((botn_iff k g).2 hg))\n  have xt : ∀ g, g < k → x g := fun g hg => (hx g).2 (Or.inl ((botn_iff k g).2 hg))\n  have nxk : ¬ x k := by\n    intro xh\n    rcases (hx k).1 xh with hb | hn\n    · rw [botn_iff] at hb; omega\n    · exact hn (fun g hg => ⟨yt g hg, (hd g).2 (Or.inl hg)⟩)\n  have nyk : ¬ y k := by\n    intro yh\n    rcases (hy k).1 yh with hb | hn\n    · rw [botn_iff] at hb; omega\n    · exact hn (fun g hg => ⟨xt g hg, (hd g).2 (Or.inl hg)⟩)\n  intro h hh\n  exact ⟨(hx h).2 (Or.inr (fun H => nyk (H k hh).1)), (hy h).2 (Or.inr (fun H => nxk (H k hh).1))⟩\n\n/-- vs BoldBot B_n = box(box^n F ∨ ¬p), whose NerveBot trace is always true. -/\ntheorem q_bn (k n : Nat) (x y : Nat → Prop)\n    (hx : ∀ h, x h ↔ qk k y (fun _ => True) h) (hy : ∀ h, y h ↔ bx (fun g => botn n g ∨ ¬ x g) h) :\n    (n < k → ∀ h, n + 1 < h → x h ∧ ¬ y h) ∧ (k ≤ n → ∀ h, (k ≤ h → ¬ x h) ∧ y h) := by\n  constructor\n  · intro hnk\n    have xn : x n := (hx n).2 (Or.inl ((botn_iff k n).2 hnk))\n    have ny : ∀ h, n < h → ¬ y h := fun h hh yh => by\n      rcases (hy h).1 yh n hh with hb | nx\n      · rw [botn_iff] at hb; omega\n      · exact nx xn\n    intro h hh\n    exact ⟨(hx h).2 (Or.inr (fun H => ny (n+1) (by omega) (H (n+1) hh).1)), ny h (by omega)⟩\n  · intro hkn\n    apply strong\n    intro h ih\n    constructor\n    · intro hk xh\n      rcases (hx h).1 xh with hb | hn\n      · rw [botn_iff] at hb; omega\n      · exact hn (fun g hg => ⟨(ih g hg).2, trivial⟩)\n    · exact (hy h).2 (fun g hg => by\n        by_cases hgn : g < n\n        · exact Or.inl ((botn_iff n g).2 hgn)\n        · exact Or.inr ((ih g hg).1 (by omega)))\n\n#print axioms q_safe\n#print axioms q_sb\n#print axioms q_nb\n#print axioms q_fj\n#print axioms q_gj\n#print axioms q_db\n#print axioms q_qm_lt\n#print axioms q_qq\n#print axioms q_bn\n"
def lean():
    for c in (shutil.which('lean'), '/opt/elan/bin/lean', os.path.expanduser('~/.elan/bin/lean')):
        if c and os.path.exists(c): return c
    raise AssertionError('lean binary not found')
def run(s):
    r = subprocess.run([lean(), '--stdin'], input=s, capture_output=True, text=True, timeout=100)
    return r.returncode, r.stdout + r.stderr

def univ_bad(m, badout=0):
    T, O = m
    for s0 in range(len(T)):
        for i in (0, 2):
            s = s0; seen = []
            while s not in seen: seen.append(s); s = T[s][i]
            if all(O[t][0] == badout for t in seen[seen.index(s):]): return True
    return False

def bx(f, h): return all(f(g) for g in range(h))
def Qb(k): return lambda h, op, q: h < k or not bx(lambda g: op[g] and q[g], h)
def Fb(j): return lambda h, op, q: all(op[g] for g in range(h - j + 1))
def Gb(j): return lambda h, op, q: bx(lambda g: g < j or op[g], h)
def Bb(n): return lambda h, op, q: bx(lambda g: g < n or not op[g], h)
def vsDB(b, H):
    x = []
    for h in range(H): x.append(b(h, [False] * H, [False] * H))
    return x
def play(a, b, H=70):
    qa, qb = vsDB(b, H), vsDB(a, H); x, y = [], []
    for h in range(H):
        xa, yb = a(h, y, qa), b(h, x, qb); x.append(xa); y.append(yb)
    assert x[-1] == x[-20] and y[-1] == y[-20]
    return x[-1], y[-1]

def main():
    t0 = time.time()
    U, G, fU, fG = enumerate_classes(10, log=False)
    order = sorted(fG, key=lambda c: (fG[c][0], fG[c][1]))
    names = [fG[c][1] for c in order]; sz = np.array([fG[c][0] for c in order]); n = len(names)
    assert n == 7561
    nb = max(s.count('[]') for s in names); H = 4 * nb + 3
    TT, OO, S = matrix(order); M = solve_all(TT, OO, S, H).astype(bool); Mt = M.T
    idx = {c: i for i, c in enumerate(order)}
    def ix(s): return idx[parse_m(s)]
    DB, CB, FB = ix('F'), ix('~F'), ix('[]p')
    safe = (M | Mt).all(1)
    SU = np.array([not univ_bad(c) for c in order])
    assert safe.sum() == 808 and SU.sum() == 695 and not (SU & ~safe).any()
    # (2)
    prop = safe & ~M[:, CB] & M[:, FB] & Mt[:, FB]
    k = np.flatnonzero(prop)
    assert sorted(sz[k].tolist()) == [9, 10, 10, 10] and SU[k].all()
    Q0, Q1, Q2, Q3 = ix('~[](p&q)'), ix('([]F|~[](p&q))'), ix('([][]F|~[](p&q))'), ix('([][][]F|~[](p&q))')
    assert [i for i in k if sz[i] <= 9] == [Q2] and Q3 in k
    for qq in (Q0, Q1):
        assert safe[qq] and SU[qq] and not M[qq, CB] and not (M[qq, FB] and M[FB, qq])
    # (3) GLS certificates
    q2 = '([][]F|~[](p&q))'
    heads = [(q2, q2), (q2, '[]p'), (q2, '~F'), (q2, 'F'), (q2, '[][]p'), (q2, '[](p|[]F)'),
             (q2, '([]F|~[](p&q))'), (q2, '([][][]F|~[](p&q))'), ('([]F|~[](p&q))', '[]p')]
    for a, b in heads:
        x, y = solve(a, b); assert (x, y) == (bool(M[ix(a), ix(b)]), bool(M[ix(b), ix(a)])), (a, b)
    assert solve(q2, '[]p') == (True, True) and solve(q2, '[][]p') == (True, False)
    assert solve(q2, '[](p|[]F)') == (True, False) and solve('([]F|~[](p&q))', '[]p') == (True, False)
    # (4) height tables
    for kk in range(9):
        assert play(Qb(kk), Qb(kk)) == (True, True)
        assert play(Qb(kk), lambda h, op, q: True) == (False, True)
        assert play(Qb(kk), lambda h, op, q: False) == (True, False)
        for j in range(1, 9): assert play(Qb(kk), Fb(j)) == ((True, True) if j < kk else (True, False)), (kk, j)
        for j in range(9): assert play(Qb(kk), Gb(j)) == ((True, True) if j + 2 <= kk else (True, False)), (kk, j)
        for m in range(9):
            assert play(Qb(kk), Qb(m)) == (kk >= m, m >= kk), (kk, m)
            assert play(Qb(kk), Bb(m)) == ((True, False) if m < kk else (False, True)), (kk, m)
    # (5) Lean
    code, out = run(LEAN_SRC)
    assert code == 0 and 'sorryAx' not in out and 'error' not in out.lower(), out
    assert out.count('depends on axioms') == 9, out
    bad = LEAN_SRC.replace('(j + 2 ≤ k → ∀ h, x h ∧ y h)', '(j + 1 ≤ k → ∀ h, x h ∧ y h)')
    assert bad != LEAN_SRC and run(bad)[0] != 0, 'negative control accepted'
    print('PASS chicken_q: %d classes, 808 safe, 695 SU, 4 safe&strSB&FBss, %d GLS certs, Lean 9 theorems, %.1fs' % (n, len(heads), time.time() - t0))

if __name__ == '__main__':
    main()
