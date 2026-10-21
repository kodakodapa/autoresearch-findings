"""C046 r1: exact law for F_k height blends of V_{n,r} (W_n = V_{n,1}) against graded FairBots F_m = box^m p,
for every selection S, and the resulting uniform separator from FairBot and every box^m' p.

Language L: atoms p (opponent's move against me), q (opponent's move against DefectBot); F,~,&,|,[];
guarded; height semantics; outcomes are Boolean tails (no payoffs).
V_{n,r} = box(box^n F | (p & (q | ~box^r q))); B = (sigma_S & F_k) | (~sigma_S & V_{n,r}).
Law (n >= 1, r >= 1, k, m >= 1): B vs F_m is CC at every height iff m + r <= n or every height h > max(n,m)
is selected; otherwise both eventually defect. Finite S: CC iff m + r <= n, so the opponent
F_{max(1,n-r+1)} gets DD from every finite blend but CC from FairBot and every box^m' p.
Engine copied verbatim from c046_j_xcheck.py (minimised Mealy machines, exact games by cycle detection,
exact unexploitability test, realizable-word behaviour machines of K18). Shares no code with r2's GLS/Lean.
Grid: n = 2..5, r = 1..n+1, k = 1..3, S = any subset of {0..5} plus tail {h >= 6} in/out, m = 1..8:
6912 blends, 55296 cells vs F_m. Also asserted: unexploitable; finite-S self-CC blends never FB-equivalent.
Lean 4 core (SHA-pinned): vfm_coop, vfm_defect, vfm_law (iff, arbitrary S), fm_fm, v_separator;
no sorryAx; 3 mutations rejected. Height-trace bridge for modal fixed points assumed as in earlier claims.
"""
import hashlib, os, shutil, subprocess
import time
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
def depth(m1, m2):
    (T1, O1), (T2, O2) = m1, m2
    seen = {(0, 0)}; frontier = [(0, 0)]; h = 0
    while frontier:
        nxt = []
        for a, b in frontier:
            if O1[a][0] != O2[b][0]: return h
            for i in INPUTS:
                s = (T1[a][i], T2[b][i])
                if s not in seen: seen.add(s); nxt.append(s)
        frontier = nxt; h += 1
    return None

LEAN = "def blend (S f g : Nat → Prop) (h : Nat) := (S h ∧ f h) ∨ (¬ S h ∧ g h)\ndef eventual (x : Nat → Prop) := ∃ H, ∀ h, H ≤ h → x h\n-- V_{n,r} = box(box^n F ∨ (p ∧ (q ∨ ¬ box^r q))) in height semantics (W_n is r = 1)\ndef vgate (n r : Nat) (p q : Nat → Prop) (h : Nat) :=\n ∀ g, g < h → g < n ∨ (p g ∧ (q g ∨ ¬ ∀ j, j + r ≤ g → q j))\n\n/-- x = F_k height blend of V_{n,r} (selection S) against F_m; y = F_m, whose DefectBot trace is (g < m).\n    If m + r ≤ n, or every height above both n and m is selected, both cooperate at every height. -/\ntheorem vfm_coop (n r k m : Nat) (hk : 1 ≤ k) (hm : 1 ≤ m) (S x y : Nat → Prop)\n (hyp : m + r ≤ n ∨ ∀ h, n < h → m < h → S h)\n (ex : ∀ h, x h ↔ blend S (fun h => ∀ u, u+k ≤ h → y u) (vgate n r y (fun g => g < m)) h)\n (ey : ∀ h, y h ↔ ∀ u, u+m ≤ h → x u) : ∀ h, x h ∧ y h := by\n classical\n intro h\n induction h using Nat.strongRecOn with\n | ind h ih =>\n   constructor\n   · apply (ex h).2\n     by_cases sh : S h\n     · exact Or.inl ⟨sh, fun u uh => (ih u (by omega)).2⟩\n     · refine Or.inr ⟨sh, fun g gh => ?_⟩\n       by_cases gn : g < n\n       · exact Or.inl gn\n       · refine Or.inr ⟨(ih g gh).2, ?_⟩\n         by_cases gm : g < m\n         · exact Or.inl gm\n         · refine Or.inr (fun H => ?_)\n           rcases hyp with hy | hy\n           · have := H m (by omega); omega\n           · exact sh (hy h (by omega) (by omega))\n   · exact (ey h).2 (fun u uh => (ih u (by omega)).1)\n\n/-- If n < m + r and some unselected height h0 lies above both n and m, both eventually defect. -/\ntheorem vfm_defect (n r k m h0 : Nat) (hr1 : 1 ≤ r) (hr : n < m + r) (S x y : Nat → Prop)\n (s0 : ¬ S h0) (hn : n < h0) (hm0 : m < h0)\n (ex : ∀ h, x h ↔ blend S (fun h => ∀ u, u+k ≤ h → y u) (vgate n r y (fun g => g < m)) h)\n (ey : ∀ h, y h ↔ ∀ u, u+m ≤ h → x u) :\n eventual (fun h => ¬ x h) ∧ eventual (fun h => ¬ y h) := by\n classical\n have nx0 : ¬ x h0 := by\n   intro xh\n   rcases (ex h0).1 xh with ⟨sh,_⟩ | ⟨_,hg⟩\n   · exact s0 sh\n   · rcases Nat.le_total n m with nm | mn\n     · rcases hg m (by omega) with lt | ⟨_, hq⟩\n       · omega\n       · rcases hq with hq | hq\n         · omega\n         · exact hq (fun j hj => by omega)\n     · rcases hg n (by omega) with lt | ⟨_, hq⟩\n       · omega\n       · rcases hq with hq | hq\n         · omega\n         · exact hq (fun j hj => by omega)\n have ny : ∀ h, h0+m ≤ h → ¬ y h := fun h hh yh => nx0 ((ey h).1 yh h0 (by omega))\n refine ⟨⟨h0+m+k+1, ?_⟩, ⟨h0+m, ny⟩⟩\n intro h hh xh\n rcases (ex h).1 xh with ⟨_,hf⟩ | ⟨_,hg⟩\n · exact ny (h0+m) (by omega) (hf (h0+m) (by omega))\n · rcases hg (h0+m) (by omega) with lt | ⟨hp, _⟩\n   · omega\n   · exact ny (h0+m) (by omega) hp\n\n/-- Exact law for every selection S: all-height cooperation iff m + r ≤ n or every height above n and m\n    is selected; otherwise both eventually defect. -/\ntheorem vfm_law (n r k m : Nat) (hr1 : 1 ≤ r) (hk : 1 ≤ k) (hm : 1 ≤ m) (S x y : Nat → Prop)\n (ex : ∀ h, x h ↔ blend S (fun h => ∀ u, u+k ≤ h → y u) (vgate n r y (fun g => g < m)) h)\n (ey : ∀ h, y h ↔ ∀ u, u+m ≤ h → x u) :\n ((∀ h, x h ∧ y h) ↔ (m + r ≤ n ∨ ∀ h, n < h → m < h → S h)) ∧\n (¬ (m + r ≤ n ∨ ∀ h, n < h → m < h → S h) → eventual (fun h => ¬ x h) ∧ eventual (fun h => ¬ y h)) := by\n classical\n have dd : ¬ (m + r ≤ n ∨ ∀ h, n < h → m < h → S h) → eventual (fun h => ¬ x h) ∧ eventual (fun h => ¬ y h) := by\n   intro nh\n   have hr : n < m + r := by\n     apply Classical.byContradiction; intro c; exact nh (Or.inl (by omega))\n   have : ∃ h0, n < h0 ∧ m < h0 ∧ ¬ S h0 := by\n     apply Classical.byContradiction; intro c\n     exact nh (Or.inr (fun h a b => Classical.byContradiction (fun sh => c ⟨h, a, b, sh⟩)))\n   rcases this with ⟨h0, a, b, sh⟩\n   exact vfm_defect n r k m h0 hr1 hr S x y sh a b ex ey\n refine ⟨⟨fun all => ?_, fun hyp => vfm_coop n r k m hk hm S x y hyp ex ey⟩, dd⟩\n apply Classical.byContradiction; intro nh\n rcases (dd nh).1 with ⟨H, hH⟩\n exact hH H (Nat.le_refl H) (all H).1\n\n/-- F_m, F_m' (m, m' ≥ 1) cooperate with each other at every height. -/\ntheorem fm_fm (m m' : Nat) (hm : 1 ≤ m) (hm' : 1 ≤ m') (x y : Nat → Prop)\n (ex : ∀ h, x h ↔ ∀ u, u+m ≤ h → y u) (ey : ∀ h, y h ↔ ∀ u, u+m' ≤ h → x u) :\n ∀ h, x h ∧ y h := by\n intro h\n induction h using Nat.strongRecOn with\n | ind h ih =>\n   exact ⟨(ex h).2 (fun u uh => (ih u (by omega)).2), (ey h).2 (fun u uh => (ih u (by omega)).1)⟩\n\n/-- Separation: for finite S (r ≥ 1), F_{n-r+1} gets eventual mutual defection from the blend\n    but all-height cooperation from every F_{m'} (m' ≥ 1, FairBot is m' = 1). -/\ntheorem v_separator (n r k M m' : Nat) (hr1 : 1 ≤ r) (hm' : 1 ≤ m') (S x y u v : Nat → Prop)\n (fin : ∀ h, M ≤ h → ¬ S h)\n (ex : ∀ h, x h ↔ blend S (fun h => ∀ w, w+k ≤ h → y w) (vgate n r y (fun g => g < n-r+1)) h)\n (ey : ∀ h, y h ↔ ∀ w, w+(n-r+1) ≤ h → x w)\n (eu : ∀ h, u h ↔ ∀ w, w+m' ≤ h → v w) (ev : ∀ h, v h ↔ ∀ w, w+(n-r+1) ≤ h → u w) :\n eventual (fun h => ¬ x h) ∧ eventual (fun h => ¬ y h) ∧ (∀ h, u h ∧ v h) :=\n ⟨(vfm_defect n r k (n-r+1) (M+n+2) hr1 (by omega) S x y (fin _ (by omega)) (by omega) (by omega) ex ey).1,\n  (vfm_defect n r k (n-r+1) (M+n+2) hr1 (by omega) S x y (fin _ (by omega)) (by omega) (by omega) ex ey).2,\n  fm_fm m' (n-r+1) hm' (by omega) u v eu ev⟩\n\n#print axioms vfm_coop\n#print axioms vfm_defect\n#print axioms vfm_law\n#print axioms fm_fm\n#print axioms v_separator\n"
SHA = '6fad5df9162e85a33fd32b8f35fe15f4992350a8692a0563d1411c9626abe153'
t0 = time.time()
FB = box(P); CB = neg(BOT); DB = BOT
L = 6
ATS = [at(g) for g in range(L)]
TAIL = neg(bxk(L, BOT))
def sigma(Sfin, tail):
    m = TAIL if tail else BOT
    for g in Sfin: m = OR(m, ATS[g])
    return m
def V(n, r): return box(OR(bxk(n, BOT), AND(P, OR(Q, neg(bxk(r, Q))))))
def blend(sg, R, A): return OR(AND(sg, R), AND(neg(sg), A))
CC, DD = (1, 1), (0, 0)
Fm = {m: bxk(m, P) for m in range(1, 9)}
FBb = behav(FB)
for m in range(1, 9):
    for m2 in range(1, 9): assert game(Fm[m], Fm[m2]) == CC
nb = 0; cells = 0; ncc = 0; selfcc_fin = 0
for n in range(2, 6):
    for r in range(1, n + 2):
        A = V(n, r)
        assert game(A, A) == DD and exploit(A) is None
        for k in range(1, 4):
            for bits in range(1 << L):
                Sfin = [g for g in range(L) if bits >> g & 1]
                for tail in (False, True):
                    inS = lambda h: (h in Sfin) if h < L else tail
                    B = blend(sigma(Sfin, tail), Fm[k], A)
                    assert exploit(B) is None, ('exploitable', n, r, k, Sfin, tail)
                    for m in range(1, 9):
                        law = m + r <= n or all(inS(h) for h in range(max(n, m) + 1, max(n, m) + L + 2))
                        got = game(B, Fm[m])
                        assert got == (CC if law else DD), (n, r, k, Sfin, tail, m, got)
                        if not tail: assert law == (m + r <= n)
                        cells += 1; ncc += got == CC
                    if not tail:
                        assert game(B, Fm[max(1, n - r + 1)]) == DD
                        if game(B, B) == CC:
                            selfcc_fin += 1
                            assert depth(behav(B), FBb) is not None
                    nb += 1
assert nb == 6912 and cells == 55296, (nb, cells)
print('cells CC', ncc, 'finite self-CC blends', selfcc_fin)
# hand examples: W_2 = V_{2,1} with FairBot at {1} (K5/K21): F_1 CC, F_2 DD; V_{3,2} at {2} (K17): F_1 CC, F_2 DD
B = blend(sigma([1], False), FB, V(2, 1))
assert game(B, B) == CC and game(B, Fm[1]) == CC and all(game(B, Fm[m]) == DD for m in range(2, 9))
B = blend(sigma([2], False), FB, V(3, 2))
assert game(B, B) == CC and game(B, Fm[1]) == CC and all(game(B, Fm[m]) == DD for m in range(2, 9))
B = blend(sigma([2], False), FB, V(4, 1))
assert game(B, B) == CC and [game(B, Fm[m]) for m in (1, 2, 3, 4)] == [CC, CC, CC, DD]
binary = next((p for p in (shutil.which('lean'), '/opt/elan/bin/lean', os.path.expanduser('~/.elan/bin/lean')) if p and os.path.exists(p)), None)
assert binary, 'lean missing'
def run(s): return subprocess.run([binary, '--stdin'], input=s, text=True, capture_output=True, timeout=100)
assert hashlib.sha256(LEAN.encode()).hexdigest() == SHA
r = run(LEAN)
assert r.returncode == 0, r.stdout + r.stderr
assert 'sorryAx' not in r.stdout and r.stdout.count('depends on axioms') == 5, r.stdout
for x, y in [('(hyp : m + r ≤ n ∨', '(hyp : m + r ≤ n+1 ∨'), ('(hr1 : 1 ≤ r) (hr : n < m + r)', '(hr1 : 0 ≤ r) (hr : n < m + r)'),
             ("(hr1 : 1 ≤ r) (hm' : 1 ≤ m')", "(hr1 : 1 ≤ r) (hm' : 0 ≤ m')")]:
    assert LEAN.count(x) == 1, x
    assert run(LEAN.replace(x, y)).returncode != 0, ('mutation accepted', y)
print('PASS: %d V blends, %d cells vs F_m match the law; unexploitable; %d finite self-CC blends separated by F_{max(1,n-r+1)}; '
      'Lean 5 theorems, 3 mutations rejected (%.1fs)' % (nb, cells, selfcc_fin, time.time() - t0))
