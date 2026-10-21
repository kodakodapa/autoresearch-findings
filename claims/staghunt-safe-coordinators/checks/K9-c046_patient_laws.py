"""C046 r1 (round 3): patient lenient bots X_k = R_k & ([]F | ~[]~p), R_k = [](p | []^k p), k >= 1.
Self-contained: engine copied from c046_dominate_fb.py (prior c046_chicken_q.py); no data files.
Stag Hunt reading: action 1 = stag, p = opponent hunts stag vs me, q = opponent hunts stag vs HareBot.
E_j = ~[]^j F, N_n = [](  []^n F | ~q ) (N_0 = []~q), Z_j = []~p | ~[]^j F, D_k = [](p | (q & []^k p)).
Asserts:
 (1) core Lean 4, 16 '#print axioms' lines, no sorryAx: xk_safe (universal: once the opponent hunts hare
     from H on, X_k hunts hare from H+k+1 on), xk_self, xx_pair, xr_pair, xd_pair (stag/stag with every
     X_m, R_m, D_m), xk_db (HareBot trace = height 0 only), xk_E (j>=1: stag/stag iff j<=k, else X_k
     hare), xk_N (stag/stag iff n>=1, else hare/hare), xk_Z (stag/stag iff j<=k+1, else X_k hare),
     xk_modal (the Lean trace is the height semantics of the modal formula); a false bound is rejected;
 (2) independent formula-level height solver, k<=7, j,n,m<=8: the same tables;
 (3) GLS fixed-point certificates for 10 headline cells;
 (4) census L up to size 10 (7561 classes, every cell re-solved): 1693 census-safe classes, 517 of them
     self-stag; 230 of those reach stag/stag with E_1, 75 with N_1, and none with both.
Height semantics: box phi holds at height h iff phi holds at all g < h.
"""

import sys, time, random
import numpy as np

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

import subprocess, shutil, os
def lean():
    for c in (shutil.which('lean'), '/opt/elan/bin/lean', os.path.expanduser('~/.elan/bin/lean')):
        if c and os.path.exists(c): return c
    raise AssertionError('lean binary not found')
def run(s):
    r = subprocess.run([lean(), '--stdin'], input=s, capture_output=True, text=True, timeout=100)
    return r.returncode, r.stdout + r.stderr

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


LEAN_SRC = 'def bx (φ : Nat → Prop) : Nat → Prop := fun h => ∀ g, g < h → φ g\ndef bxn : Nat → (Nat → Prop) → (Nat → Prop)\n  | 0, φ => φ\n  | n+1, φ => bx (bxn n φ)\n\ntheorem bxn_succ_iff (n : Nat) (φ : Nat → Prop) (h : Nat) :\n    bxn (n+1) φ h ↔ ∀ g, g + (n+1) ≤ h → φ g := by\n  induction n generalizing h with\n  | zero =>\n    simp only [bxn, bx]\n    exact ⟨fun H g hg => H g (by omega), fun H g hg => H g (by omega)⟩\n  | succ n ih =>\n    show bx (bxn (n+1) φ) h ↔ _\n    simp only [bx]\n    constructor\n    · intro H g hg\n      exact (ih (h-1)).1 (H (h-1) (by omega)) g (by omega)\n    · intro H g\' hg\'\n      exact (ih g\').2 (fun g hg => H g (by omega))\n\ntheorem bxn_iff (n : Nat) (hn : 1 ≤ n) (φ : Nat → Prop) (h : Nat) :\n    bxn n φ h ↔ ∀ g, g + n ≤ h → φ g := by\n  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩\n  exact bxn_succ_iff m φ h\n\ndef botn (n : Nat) : Nat → Prop := bxn n (fun _ => False)\n\ntheorem botn_iff (n h : Nat) : botn n h ↔ h < n := by\n  cases n with\n  | zero => simp [botn, bxn]\n  | succ m =>\n    unfold botn; rw [bxn_succ_iff]\n    constructor\n    · intro H; apply Classical.byContradiction; intro hn\n      exact H 0 (by omega)\n    · intro hlt g hg; omega\n\ntheorem strong (P : Nat → Prop) (step : ∀ h, (∀ g, g < h → P g) → P h) : ∀ h, P h := by\n  have key : ∀ N h, h < N → P h := by\n    intro N\n    induction N with\n    | zero => intro h hh; omega\n    | succ N ih => intro h hh; exact step h (fun g hg => ih g (by omega))\n  exact fun h => key (h+1) h (by omega)\n\n/-! Stag Hunt, True = stag. p-trace y = opponent\'s action against the agent,\n    q-trace e = opponent\'s action against HareBot (constant hare).\n    Lenient FairBot R_k = box(p ∨ box^k p); q-guarded D_k = box(p ∨ (q ∧ box^k p)).\n    For k = 0 the clause ∀ g\', g\' + 0 ≤ g → y g\' contains y g, so R_0 = D_0 = FairBot box p. -/\ndef rk (k : Nat) (y : Nat → Prop) : Nat → Prop :=\n  fun h => ∀ g, g < h → y g ∨ (∀ g\', g\' + k ≤ g → y g\')\ndef dk (k : Nat) (y e : Nat → Prop) : Nat → Prop :=\n  fun h => ∀ g, g < h → y g ∨ (e g ∧ ∀ g\', g\' + k ≤ g → y g\')\n\ntheorem rk_modal (k : Nat) (hk : 1 ≤ k) (y : Nat → Prop) (h : Nat) :\n    rk k y h ↔ bx (fun g => y g ∨ bxn k y g) h := by\n  simp only [rk, bx, bxn_iff k hk]\n\ntheorem dk_modal (k : Nat) (hk : 1 ≤ k) (y e : Nat → Prop) (h : Nat) :\n    dk k y e h ↔ bx (fun g => y g ∨ (e g ∧ bxn k y g)) h := by\n  simp only [dk, bx, bxn_iff k hk]\n\ntheorem r0_fair (y : Nat → Prop) (h : Nat) : rk 0 y h ↔ bx y h := by\n  simp only [rk, bx]\n  constructor\n  · intro H g hg\n    rcases H g hg with a | a\n    · exact a\n    · exact a g (by omega)\n  · intro H g hg; exact Or.inl (H g hg)\n\ntheorem d0_fair (y e : Nat → Prop) (h : Nat) : dk 0 y e h ↔ bx y h := by\n  simp only [dk, bx]\n  constructor\n  · intro H g hg\n    rcases H g hg with a | ⟨_, a⟩\n    · exact a\n    · exact a g (by omega)\n  · intro H g hg; exact Or.inl (H g hg)\n\ntheorem dk_true (k : Nat) (y : Nat → Prop) (h : Nat) : dk k y (fun _ => True) h ↔ rk k y h := by\n  simp only [dk, rk, true_and]\n\n/-- Universal safety: against ANY opponent trace y (and any e), once the opponent hunts hare\n    from height H on, the agent hunts hare from height H + k + 1 on. -/\ntheorem dk_safe (k : Nat) (x y e : Nat → Prop) (hx : ∀ h, x h ↔ dk k y e h)\n    (H : Nat) (hy : ∀ h, H ≤ h → ¬ y h) : ∀ h, H + k + 1 ≤ h → ¬ x h := by\n  intro h hh xh\n  rcases (hx h).1 xh (H + k) (by omega) with a | ⟨_, a⟩\n  · exact hy (H + k) (by omega) a\n  · exact hy H (Nat.le_refl _) (a H (by omega))\n\ntheorem rk_safe (k : Nat) (x y : Nat → Prop) (hx : ∀ h, x h ↔ rk k y h)\n    (H : Nat) (hy : ∀ h, H ≤ h → ¬ y h) : ∀ h, H + k + 1 ≤ h → ¬ x h :=\n  dk_safe k x y (fun _ => True) (fun h => (hx h).trans (dk_true k y h).symm) H hy\n\n/-- Any two agents that hunt stag whenever box p holds end in stag/stag at every height. -/\ntheorem fair_pair (x y : Nat → Prop) (hx : ∀ h, (∀ g, g < h → y g) → x h)\n    (hy : ∀ h, (∀ g, g < h → x g) → y h) : ∀ h, x h ∧ y h := by\n  apply strong\n  intro h ih\n  exact ⟨hx h (fun g hg => (ih g hg).2), hy h (fun g hg => (ih g hg).1)⟩\n\ntheorem rk_imp (k : Nat) (y : Nat → Prop) (h : Nat) (H : ∀ g, g < h → y g) : rk k y h :=\n  fun g hg => Or.inl (H g hg)\ntheorem dk_imp (k : Nat) (y e : Nat → Prop) (h : Nat) (H : ∀ g, g < h → y g) : dk k y e h :=\n  fun g hg => Or.inl (H g hg)\n\ntheorem dd_pair (k m : Nat) (x y e1 e2 : Nat → Prop) (hx : ∀ h, x h ↔ dk k y e1 h)\n    (hy : ∀ h, y h ↔ dk m x e2 h) : ∀ h, x h ∧ y h :=\n  fair_pair x y (fun h H => (hx h).2 (dk_imp k y e1 h H)) (fun h H => (hy h).2 (dk_imp m x e2 h H))\n\ntheorem rr_pair (k m : Nat) (x y : Nat → Prop) (hx : ∀ h, x h ↔ rk k y h)\n    (hy : ∀ h, y h ↔ rk m x h) : ∀ h, x h ∧ y h :=\n  fair_pair x y (fun h H => (hx h).2 (rk_imp k y h H)) (fun h H => (hy h).2 (rk_imp m x h H))\n\ntheorem rd_pair (k m : Nat) (x y e : Nat → Prop) (hx : ∀ h, x h ↔ rk k y h)\n    (hy : ∀ h, y h ↔ dk m x e h) : ∀ h, x h ∧ y h :=\n  fair_pair x y (fun h H => (hx h).2 (rk_imp k y h H)) (fun h H => (hy h).2 (dk_imp m x e h H))\n\n/-- HareBot traces: R_k hunts stag against HareBot exactly at heights h ≤ k; D_k only at h = 0. -/\ntheorem rk_db (k h : Nat) : rk k (fun _ => False) h ↔ h ≤ k := by\n  simp only [rk, false_or]\n  constructor\n  · intro H; apply Classical.byContradiction; intro hn\n    exact H k (by omega) 0 (by omega)\n  · intro hh g hg g\' hg\'; omega\n\ntheorem dk_db (k h : Nat) : dk k (fun _ => False) (fun _ => False) h ↔ h = 0 := by\n  simp only [dk, false_and, or_false]\n  constructor\n  · intro H; apply Classical.byContradiction; intro hn\n    exact H 0 (by omega)\n  · intro hh g hg; omega\n\n/-- vs E_j = ¬ box^j F (stag exactly from height j on; its HareBot trace is the same). -/\ntheorem e_trace (j h : Nat) : ¬ botn j h ↔ j ≤ h := by rw [botn_iff]; omega\n\ntheorem rk_E (k j : Nat) (hj : 1 ≤ j) (x y : Nat → Prop) (hy : ∀ h, y h ↔ j ≤ h)\n    (hx : ∀ h, x h ↔ rk k y h) :\n    (j ≤ k → ∀ h, x h) ∧ (k < j → ∀ h, k < h → ¬ x h) := by\n  constructor\n  · intro hjk h\n    apply (hx h).2\n    intro g hg\n    by_cases hgj : j ≤ g\n    · exact Or.inl ((hy g).2 hgj)\n    · exact Or.inr (fun g\' hg\' => by omega)\n  · intro hkj h hh xh\n    rcases (hx h).1 xh k hh with a | a\n    · have := (hy k).1 a; omega\n    · have := (hy 0).1 (a 0 (by omega)); omega\n\ntheorem dk_E (k j : Nat) (hj : 1 ≤ j) (x y : Nat → Prop) (hy : ∀ h, y h ↔ j ≤ h)\n    (hx : ∀ h, x h ↔ dk k y y h) : ∀ h, 1 ≤ h → ¬ x h := by\n  intro h hh xh\n  rcases (hx h).1 xh 0 (by omega) with a | ⟨a, _⟩\n  · have := (hy 0).1 a; omega\n  · have := (hy 0).1 a; omega\n\n/-- vs N_n = box(box^n F ∨ ¬q): the opponent hunts stag iff it is provable (in PA+n)\n    that the agent hunts hare against HareBot. d is the agent\'s HareBot trace. -/\ntheorem rk_N (k n : Nat) (x y d : Nat → Prop) (hd : ∀ h, d h ↔ h ≤ k)\n    (hx : ∀ h, x h ↔ rk k y h) (hy : ∀ h, y h ↔ bx (fun g => botn n g ∨ ¬ d g) h) :\n    (k < n → ∀ h, x h ∧ y h) ∧ (n ≤ k → ∀ h, n + k + 2 ≤ h → ¬ x h ∧ ¬ y h) := by\n  constructor\n  · intro hkn\n    have ya : ∀ h, y h := fun h => (hy h).2 (fun g _ => by\n      by_cases hg : g < n\n      · exact Or.inl ((botn_iff n g).2 hg)\n      · exact Or.inr (fun dg => by have := (hd g).1 dg; omega))\n    exact fun h => ⟨(hx h).2 (rk_imp k y h (fun g _ => ya g)), ya h⟩\n  · intro hnk\n    have ny : ∀ h, n + 1 ≤ h → ¬ y h := by\n      intro h hh yh\n      rcases (hy h).1 yh n (by omega) with a | a\n      · rw [botn_iff] at a; omega\n      · exact a ((hd n).2 hnk)\n    intro h hh\n    exact ⟨rk_safe k x y hx (n+1) ny h (by omega), ny h (by omega)⟩\n\ntheorem dk_N (k n : Nat) (x y d e : Nat → Prop) (hd : ∀ h, d h ↔ h = 0)\n    (hx : ∀ h, x h ↔ dk k y e h) (hy : ∀ h, y h ↔ bx (fun g => botn n g ∨ ¬ d g) h) :\n    (1 ≤ n → ∀ h, x h ∧ y h) ∧ (n = 0 → ∀ h, k + 2 ≤ h → ¬ x h ∧ ¬ y h) := by\n  constructor\n  · intro hn\n    have ya : ∀ h, y h := fun h => (hy h).2 (fun g _ => by\n      by_cases hg : g < n\n      · exact Or.inl ((botn_iff n g).2 hg)\n      · exact Or.inr (fun dg => by have := (hd g).1 dg; omega))\n    exact fun h => ⟨(hx h).2 (dk_imp k y e h (fun g _ => ya g)), ya h⟩\n  · intro hn\n    have ny : ∀ h, 1 ≤ h → ¬ y h := by\n      intro h hh yh\n      rcases (hy h).1 yh 0 (by omega) with a | a\n      · rw [botn_iff] at a; omega\n      · exact a ((hd 0).2 rfl)\n    intro h hh\n    exact ⟨dk_safe k x y e hx 1 ny h (by omega), ny h (by omega)⟩\n\n/-- vs Z_j = box ¬p ∨ ¬ box^j F (its HareBot trace is always stag, so D_k acts as R_k):\n    y h ↔ (∀ g < h, ¬ x g) ∨ j ≤ h. -/\ntheorem rk_Z (k j : Nat) (hj : 1 ≤ j) (x y : Nat → Prop)\n    (hx : ∀ h, x h ↔ rk k y h) (hy : ∀ h, y h ↔ (∀ g, g < h → ¬ x g) ∨ j ≤ h) :\n    (j ≤ k + 1 → (∀ h, x h) ∧ (∀ h, j ≤ h → y h)) ∧\n    (k + 1 < j → (∀ h, k + 2 ≤ h → ¬ x h) ∧ (∀ h, j ≤ h → y h)) := by\n  have y0 : y 0 := (hy 0).2 (Or.inl (fun g hg => by omega))\n  have x0 : x 0 := (hx 0).2 (fun g hg => by omega)\n  have ylate : ∀ h, j ≤ h → y h := fun h hh => (hy h).2 (Or.inr hh)\n  have ymid : ∀ g, 1 ≤ g → g < j → ¬ y g := by\n    intro g hg1 hgj yg\n    rcases (hy g).1 yg with a | a\n    · exact a 0 (by omega) x0\n    · omega\n  constructor\n  · intro hjk\n    refine ⟨fun h => (hx h).2 (fun g hg => ?_), ylate⟩\n    by_cases hgj : j ≤ g\n    · exact Or.inl (ylate g hgj)\n    · right; intro g\' hg\'\n      have : g\' = 0 := by omega\n      subst this; exact y0\n  · intro hkj\n    refine ⟨fun h hh xh => ?_, ylate⟩\n    rcases (hx h).1 xh (k+1) (by omega) with a | a\n    · exact ymid (k+1) (by omega) (by omega) a\n    · exact ymid 1 (by omega) (by omega) (a 1 (by omega))\n\ntheorem dk_Z (k j : Nat) (hj : 1 ≤ j) (x y : Nat → Prop)\n    (hx : ∀ h, x h ↔ dk k y (fun _ => True) h) (hy : ∀ h, y h ↔ (∀ g, g < h → ¬ x g) ∨ j ≤ h) :\n    (j ≤ k + 1 → (∀ h, x h) ∧ (∀ h, j ≤ h → y h)) ∧\n    (k + 1 < j → (∀ h, k + 2 ≤ h → ¬ x h) ∧ (∀ h, j ≤ h → y h)) :=\n  rk_Z k j hj x y (fun h => (hx h).trans (dk_true k y h)) hy\n\n\n/-! Patient lenient bot X_k = R_k ∧ (box F ∨ ¬ box ¬p): R_k, plus "the opponent has hunted stag at\n    some lower height" (vacuous at height 0). -/\ndef xk (k : Nat) (y : Nat → Prop) : Nat → Prop :=\n  fun h => rk k y h ∧ (h = 0 ∨ ∃ g, g < h ∧ y g)\n\ntheorem xk_modal (k : Nat) (hk : 1 ≤ k) (y : Nat → Prop) (h : Nat) :\n    xk k y h ↔ (bx (fun g => y g ∨ bxn k y g) h ∧ (botn 1 h ∨ ¬ bx (fun g => ¬ y g) h)) := by\n  classical\n  unfold xk\n  rw [rk_modal k hk y h, botn_iff]\n  constructor\n  · rintro ⟨a, b⟩\n    refine ⟨a, ?_⟩\n    rcases b with b | ⟨g, hg, yg⟩\n    · left; omega\n    · right; intro H; exact H g hg yg\n  · rintro ⟨a, b⟩\n    refine ⟨a, ?_⟩\n    rcases b with b | b\n    · left; omega\n    · right\n      apply Classical.byContradiction\n      intro hn\n      exact b (fun g hg yg => hn ⟨g, hg, yg⟩)\n\ntheorem xk_imp (k : Nat) (y : Nat → Prop) (h : Nat) (H : ∀ g, g < h → y g) : xk k y h := by\n  refine ⟨rk_imp k y h H, ?_⟩\n  rcases Nat.eq_zero_or_pos h with e | e\n  · exact Or.inl e\n  · exact Or.inr ⟨0, e, H 0 e⟩\n\ntheorem xk_safe (k : Nat) (x y : Nat → Prop) (hx : ∀ h, x h ↔ xk k y h)\n    (H : Nat) (hy : ∀ h, H ≤ h → ¬ y h) : ∀ h, H + k + 1 ≤ h → ¬ x h := by\n  intro h hh xh\n  rcases ((hx h).1 xh).1 (H + k) (by omega) with a | a\n  · exact hy (H + k) (by omega) a\n  · exact hy H (Nat.le_refl _) (a H (by omega))\n\ntheorem xk_self (k : Nat) (x : Nat → Prop) (hx : ∀ h, x h ↔ xk k x h) : ∀ h, x h :=\n  fun h => (fair_pair x x (fun h H => (hx h).2 (xk_imp k x h H))\n    (fun h H => (hx h).2 (xk_imp k x h H)) h).1\n\ntheorem xx_pair (k m : Nat) (x y : Nat → Prop) (hx : ∀ h, x h ↔ xk k y h)\n    (hy : ∀ h, y h ↔ xk m x h) : ∀ h, x h ∧ y h :=\n  fair_pair x y (fun h H => (hx h).2 (xk_imp k y h H)) (fun h H => (hy h).2 (xk_imp m x h H))\n\ntheorem xr_pair (k m : Nat) (x y : Nat → Prop) (hx : ∀ h, x h ↔ xk k y h)\n    (hy : ∀ h, y h ↔ rk m x h) : ∀ h, x h ∧ y h :=\n  fair_pair x y (fun h H => (hx h).2 (xk_imp k y h H)) (fun h H => (hy h).2 (rk_imp m x h H))\n\ntheorem xd_pair (k m : Nat) (x y e : Nat → Prop) (hx : ∀ h, x h ↔ xk k y h)\n    (hy : ∀ h, y h ↔ dk m x e h) : ∀ h, x h ∧ y h :=\n  fair_pair x y (fun h H => (hx h).2 (xk_imp k y h H)) (fun h H => (hy h).2 (dk_imp m x e h H))\n\n/-- HareBot trace of X_k: stag only at height 0 (like D_k, unlike R_k). -/\ntheorem xk_db (k h : Nat) : xk k (fun _ => False) h ↔ h = 0 := by\n  constructor\n  · rintro ⟨_, b | ⟨g, _, yg⟩⟩\n    · exact b\n    · exact yg.elim\n  · intro hh; subst hh\n    exact ⟨fun g hg => by omega, Or.inl rfl⟩\n\n/-- If the opponent hunts stag at height 0, X_k acts exactly as R_k. -/\ntheorem xk_y0 (k : Nat) (y : Nat → Prop) (y0 : y 0) (h : Nat) : xk k y h ↔ rk k y h := by\n  constructor\n  · exact fun H => H.1\n  · intro H; refine ⟨H, ?_⟩\n    rcases Nat.eq_zero_or_pos h with e | e\n    · exact Or.inl e\n    · exact Or.inr ⟨0, e, y0⟩\n\n/-- vs E_j = ¬ box^j F, j ≥ 1: stag/stag iff j ≤ k (X_k stag at h = 0 and all h > j), else X_k hare. -/\ntheorem xk_E (k j : Nat) (hj : 1 ≤ j) (x y : Nat → Prop) (hy : ∀ h, y h ↔ j ≤ h)\n    (hx : ∀ h, x h ↔ xk k y h) :\n    (j ≤ k → ∀ h, x h ↔ (h = 0 ∨ j < h)) ∧ (k < j → ∀ h, k < h → ¬ x h) := by\n  constructor\n  · intro hjk h\n    have r : rk k y h := by\n      intro g hg\n      by_cases hgj : j ≤ g\n      · exact Or.inl ((hy g).2 hgj)\n      · exact Or.inr (fun g\' hg\' => by omega)\n    rw [hx h]\n    constructor\n    · rintro ⟨_, e | ⟨g, hg, yg⟩⟩\n      · exact Or.inl e\n      · have := (hy g).1 yg; right; omega\n    · intro H\n      refine ⟨r, ?_⟩\n      rcases H with e | e\n      · exact Or.inl e\n      · exact Or.inr ⟨j, e, (hy j).2 (Nat.le_refl j)⟩\n  · intro hkj h hh xh\n    rcases ((hx h).1 xh).1 k hh with a | a\n    · have := (hy k).1 a; omega\n    · have := (hy 0).1 (a 0 (by omega)); omega\n\n/-- vs N_n = box(box^n F ∨ ¬q), d = X_k\'s HareBot trace (xk_db): stag/stag iff n ≥ 1. -/\ntheorem xk_N (k n : Nat) (x y d : Nat → Prop) (hd : ∀ h, d h ↔ h = 0)\n    (hx : ∀ h, x h ↔ xk k y h) (hy : ∀ h, y h ↔ bx (fun g => botn n g ∨ ¬ d g) h) :\n    (1 ≤ n → ∀ h, x h ∧ y h) ∧ (n = 0 → ∀ h, k + 2 ≤ h → ¬ x h ∧ ¬ y h) := by\n  constructor\n  · intro hn\n    have ya : ∀ h, y h := fun h => (hy h).2 (fun g _ => by\n      by_cases hg : g < n\n      · exact Or.inl ((botn_iff n g).2 hg)\n      · exact Or.inr (fun dg => by have := (hd g).1 dg; omega))\n    exact fun h => ⟨(hx h).2 (xk_imp k y h (fun g _ => ya g)), ya h⟩\n  · intro hn\n    have ny : ∀ h, 1 ≤ h → ¬ y h := by\n      intro h hh yh\n      rcases (hy h).1 yh 0 (by omega) with a | a\n      · rw [botn_iff] at a; omega\n      · exact a ((hd 0).2 rfl)\n    intro h hh\n    exact ⟨xk_safe k x y hx 1 ny h (by omega), ny h (by omega)⟩\n\n/-- vs Z_j = box ¬p ∨ ¬ box^j F: Z_j hunts stag at height 0, so X_k inherits R_k\'s law. -/\ntheorem xk_Z (k j : Nat) (hj : 1 ≤ j) (x y : Nat → Prop)\n    (hx : ∀ h, x h ↔ xk k y h) (hy : ∀ h, y h ↔ (∀ g, g < h → ¬ x g) ∨ j ≤ h) :\n    (j ≤ k + 1 → (∀ h, x h) ∧ (∀ h, j ≤ h → y h)) ∧\n    (k + 1 < j → (∀ h, k + 2 ≤ h → ¬ x h) ∧ (∀ h, j ≤ h → y h)) := by\n  have y0 : y 0 := (hy 0).2 (Or.inl (fun g hg => by omega))\n  exact rk_Z k j hj x y (fun h => (hx h).trans (xk_y0 k y y0 h)) hy\n\n#print axioms rk_safe\n#print axioms rk_E\n#print axioms rk_N\n#print axioms rk_Z\n#print axioms xk_modal\n#print axioms xk_imp\n#print axioms xk_safe\n#print axioms xk_self\n#print axioms xx_pair\n#print axioms xr_pair\n#print axioms xd_pair\n#print axioms xk_db\n#print axioms xk_y0\n#print axioms xk_E\n#print axioms xk_N\n#print axioms xk_Z\n'

bn = lambda k, s: '[]' * k + s
def R(k): return '[](p|%s)' % bn(k, 'p') if k else '[]p'
def D(k): return '[](p|(q&%s))' % bn(k, 'p') if k else '[]p'
def X(k): return '(%s&([]F|~[]~p))' % R(k)
def E(j): return '~' + bn(j, 'F')
def N(n): return '[](%s|~q)' % bn(n, 'F') if n else '[]~q'
def Z(j): return '([]~p|~%s)' % bn(j, 'F')
SS, HS, HH = (True, True), (False, True), (False, False)

def main():
    t0 = time.time()
    code, out = run(LEAN_SRC)
    assert code == 0 and 'sorryAx' not in out and 'error' not in out.lower(), out
    assert out.count('depends on axioms') + out.count('does not depend on any axioms') == 16, out
    old = '(j ≤ k → ∀ h, x h ↔ (h = 0 ∨ j < h))'
    assert LEAN_SRC.count(old) == 1
    bad = LEAN_SRC.replace(old, '(j ≤ k + 1 → ∀ h, x h ↔ (h = 0 ∨ j < h))')
    assert run(bad)[0] != 0, 'negative control accepted'
    cells = 0
    for k in range(1, 8):
        a = X(k)
        assert game(a, a) == SS and game(a, 'F') == HH and game(a, '~F') == SS and game(a, '[]p') == SS
        cells += 4
        for j in range(1, 9):
            assert game(a, E(j)) == (SS if j <= k else HS), (k, j)
            assert game(a, Z(j)) == (SS if j <= k + 1 else HS), (k, j)
            cells += 2
        for n in range(9):
            assert game(a, N(n)) == (SS if n >= 1 else HH), (k, n)
            cells += 1
        for m in range(8):
            assert game(a, R(m)) == game(a, D(m)) == SS
            cells += 2
            if m: assert game(a, X(m)) == SS; cells += 1
    heads = [(X(1), X(1), SS), (X(1), E(1), SS), (X(1), E(2), HS), (X(1), N(1), SS), (X(1), N(0), HH),
             (X(1), 'F', HH), (X(2), E(2), SS), (X(2), E(3), HS), (X(1), Z(2), SS), (X(1), '[]p', SS)]
    for a, b, want in heads:
        assert solve(a, b) == want, (a, b)
    # contrast: R_1 fails N_1, D_1 fails E_1 (K2/K3)
    assert solve(R(1), N(1)) == HH and solve(D(1), E(1)) == HS
    U, G, fU, fG = enumerate_classes(10, log=False)
    assert [len(G[k]) for k in range(1, 11)] == [1, 4, 8, 12, 31, 98, 255, 646, 1760, 4746]
    order = sorted(fG, key=lambda c: (fG[c][0], fG[c][1]))
    names = [fG[c][1] for c in order]; n = len(names); assert n == 7561
    nb = max(s.count('[]') for s in names); H = 4 * nb + 3
    TT, OO, S = matrix(order); M = solve_all(TT, OO, S, H).astype(np.int64); Mt = M.T
    idx = {c: i for i, c in enumerate(order)}
    def ix(s): return idx[parse_m(s)]
    e1, n1 = ix(E(1)), ix(N(1))
    safe = ~((M == 1) & (Mt == 0)).any(1); selfs = np.diag(M) == 1
    ssE = (M[:, e1] == 1) & (Mt[:, e1] == 1); ssN = (M[:, n1] == 1) & (Mt[:, n1] == 1)
    assert safe.sum() == 1693 and (safe & selfs).sum() == 517
    assert (safe & selfs & ssE).sum() == 230 and (safe & selfs & ssN).sum() == 75
    assert (safe & selfs & ssE & ssN).sum() == 0
    for i in np.flatnonzero(safe & selfs & (ssE | ssN))[::7]:
        assert game(names[i], E(1)) == (bool(M[i, e1]), bool(M[e1, i])) and game(names[i], N(1)) == (bool(M[i, n1]), bool(M[n1, i]))
        cells += 2
    print('PASS patient_laws: Lean 16 theorems + negative control, %d height cells, %d GLS certs, census 0/230/75, %.1fs'
          % (cells, len(heads) + 2, time.time() - t0))

if __name__ == '__main__':
    main()
