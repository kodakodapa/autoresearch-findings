"""C046 r1: closes the cofinite gap of K20. Every F_k height blend of J_{a,b,j} (G, H included) with a COFINITE
selector S is either behaviourally FairBot (exactly when k = 1 and every height >= 1 is selected: then the blend is
the FairBot operator box p at every height on every input) or is separated from FairBot by one explicit opponent:
 (i) if its DefectBot trace d is true at some h >= 1:  R_h(q) = box(~box^{h+1}F | box^h F | q)
     (cooperate up to h, then forever copy the partner's DefectBot move at h): blend/R = CC, FB/R = DD;
 (ii) otherwise some unselected h0 >= a+b+1 exists, and Y_{h0} = (~sigma_{h0-1} | box ~p) & R_{h0}(p)
     (defect at h0-1 iff the partner has cooperated before; then copy its move at h0): blend/Y = DC, FB/Y = DD.
Lean 4 core (SHA-pinned): db_trace, reader (height semantics of R_h), cases3 (trichotomy), fb_case, rq_blend, rq_fb,
y_blend, y_fb for arbitrary a,b,j,k>=1 and any cofinite S; no sorryAx; 3 mutations rejected.
Engine (copied from c046_j_xcheck.py, K20; shares no code with r2's GLS/Lean): all 7680 cofinite blends
(1<=a+b<=4, 1<=j<=a+b, k=1..3, S = any subset of {0..5} plus all h>=6): FB-equivalent (behav) iff k=1 and
{1..5} in S (80); each of the other 7600 gets the stated cells with its separator; of the 6288 self-CC cofinite blends,
80 are FairBot and 6208 separated (108 of them were unseparated by the K20 bank). Height-trace bridge assumed.
Language L: atoms p (opponent's move vs me), q (opponent's move vs DefectBot); outcomes Boolean tails, no payoffs.
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

LEAN = "def blend (S f g : Nat → Prop) (h : Nat) := (S h ∧ f h) ∨ (¬ S h ∧ g h)\ndef eventual (x : Nat → Prop) := ∃ H, ∀ h, H ≤ h → x h\n-- normalized J_{a,b,j} = box^{a+1}(box^b p ∧ (q ∨ box(box^j F ∨ ¬q))), as in r2's j_self.lean\ndef gate (a b j : Nat) (p q : Nat → Prop) (h : Nat) :=\n (∀ u, u+a+b+1 ≤ h → p u) ∧\n (∀ g, g+a+1 ≤ h → q g ∨ ∀ f, j ≤ f → f < g → ¬ q f)\n/-- F_k = box^k p at height g reads y at every u with u+k ≤ g. -/\ndef fk (k : Nat) (y : Nat → Prop) (g : Nat) := ∀ u, u+k ≤ g → y u\n\n/-- DefectBot trace of the F_k height blend of J_{a,b,j}. -/\ntheorem db_trace (a b j k h : Nat) (S : Nat → Prop) :\n blend S (fk k (fun _ => False)) (gate a b j (fun _ => False) (fun _ => False)) h ↔\n (S h ∧ h < k) ∨ (¬ S h ∧ h < a+b+1) := by\n have F : fk k (fun _ => False) h ↔ h < k := by\n  constructor\n  · intro H; apply Classical.byContradiction; intro e; exact H 0 (by omega)\n  · intro H u uh; omega\n have G : gate a b j (fun _ => False) (fun _ => False) h ↔ h < a+b+1 := by\n  constructor\n  · intro ⟨hp,_⟩; apply Classical.byContradiction; intro hn; exact hp 0 (by omega)\n  · intro hh; exact ⟨(fun u uh => by omega),fun _ _ => Or.inr (fun _ _ _ => id)⟩\n simp only [blend, F, G]\n\n/-- Height semantics of the reader R_h(r) = box(~box^{h+1}F | box^h F | r): at g it is g ≤ h or r h. -/\ntheorem reader (h g : Nat) (r : Nat → Prop) :\n (∀ u, u < g → (h+1 ≤ u ∨ u < h ∨ r u)) ↔ (g ≤ h ∨ r h) := by\n constructor\n · intro H\n   by_cases gh : g ≤ h\n   · exact Or.inl gh\n   · rcases H h (by omega) with c | c | c\n     · omega\n     · omega\n     · exact Or.inr c\n · intro H u ug\n   rcases Nat.lt_trichotomy u h with c | c | c\n   · exact Or.inr (Or.inl c)\n   · subst c; rcases H with c | c\n     · omega\n     · exact Or.inr (Or.inr c)\n   · exact Or.inl c\n\n/-- Dichotomy for cofinite selectors: either the DefectBot trace is true at some h ≥ 1, or some\n    unselected height is ≥ a+b+1, or k ≤ 1 and every positive height is selected. -/\ntheorem cases3 (a b k : Nat) (hk : 1 ≤ k) (S : Nat → Prop) :\n (∃ h, 1 ≤ h ∧ ((S h ∧ h < k) ∨ (¬ S h ∧ h < a+b+1))) ∨ (∃ h0, a+b+1 ≤ h0 ∧ ¬ S h0) ∨\n (k = 1 ∧ ∀ h, 1 ≤ h → S h) := by\n classical\n by_cases c1 : ∃ h, 1 ≤ h ∧ ((S h ∧ h < k) ∨ (¬ S h ∧ h < a+b+1))\n · exact Or.inl c1\n · by_cases c2 : ∃ h0, a+b+1 ≤ h0 ∧ ¬ S h0\n   · exact Or.inr (Or.inl c2)\n   · have allS : ∀ h, 1 ≤ h → S h := by\n       intro h h1; apply Classical.byContradiction; intro ns\n       by_cases hl : h < a+b+1\n       · exact c1 ⟨h, h1, Or.inr ⟨ns, hl⟩⟩\n       · exact c2 ⟨h, by omega, ns⟩\n     refine Or.inr (Or.inr ⟨?_, allS⟩)\n     apply Classical.byContradiction; intro nk\n     exact c1 ⟨1, Nat.le_refl 1, Or.inl ⟨allS 1 (Nat.le_refl 1), by omega⟩⟩\n\n/-- Third case: the blend is the FairBot operator box p at every height, for every input. -/\ntheorem fb_case (a b j : Nat) (S y e : Nat → Prop) (allS : ∀ h, 1 ≤ h → S h) (h : Nat) :\n blend S (fk 1 y) (gate a b j y e) h ↔ fk 1 y h := by\n constructor\n · rintro (⟨_, f⟩ | ⟨ns, _⟩)\n   · exact f\n   · have h0 : h = 0 := by\n       apply Classical.byContradiction; intro hn; exact ns (allS h (by omega))\n     subst h0; intro u uh; omega\n · intro f\n   by_cases sh : S h\n   · exact Or.inl ⟨sh, f⟩\n   · have h0 : h = 0 := by\n       apply Classical.byContradiction; intro hn; exact sh (allS h (by omega))\n     subst h0\n     exact Or.inr ⟨sh, fun u uh => by omega, fun g gh => by omega⟩\n\n/-- First case: opponent R_h(q) (cooperate up to h, then copy the partner's DefectBot move at h).\n    Against a cofinite F_k blend whose DefectBot trace d is true at h, both cooperate eventually. -/\ntheorem rq_blend (a b j k h M : Nat) (S d x y e : Nat → Prop) (cof : ∀ g, M ≤ g → S g) (dh : d h)\n (ex : ∀ g, x g ↔ blend S (fk k y) (gate a b j y e) g)\n (ey : ∀ g, y g ↔ (g ≤ h ∨ d h)) : eventual x ∧ ∀ g, y g := by\n have ya : ∀ g, y g := fun g => (ey g).2 (Or.inr dh)\n exact ⟨⟨M, fun g gm => (ex g).2 (Or.inl ⟨cof g gm, fun u _ => ya u⟩)⟩, ya⟩\n\n/-- ... while FairBot (DefectBot trace true only at 0) and R_h(q), h ≥ 1, both defect eventually. -/\ntheorem rq_fb (h : Nat) (h1 : 1 ≤ h) (u v : Nat → Prop)\n (eu : ∀ g, u g ↔ fk 1 v g) (ev : ∀ g, v g ↔ (g ≤ h ∨ h < 1)) :\n eventual (fun g => ¬ u g) ∧ eventual (fun g => ¬ v g) := by\n have nv : ∀ g, h+1 ≤ g → ¬ v g := fun g hg vg => by rcases (ev g).1 vg with c | c <;> omega\n exact ⟨⟨h+2, fun g hg ug => nv (h+1) (Nat.le_refl _) ((eu g).1 ug (h+1) (by omega))⟩, ⟨h+1, nv⟩⟩\n\n/-- Second case: opponent Y = (~sigma_{h0-1} | box ~p) & R_{h0}(p): defect at h0-1 iff the partner\n    has cooperated before, then copy the partner's move at h0. Any cofinite F_k blend of J with an\n    unselected height h0 ≥ a+b+1 cooperates at h0 (only seeing Y's cooperations), then defects\n    forever, while Y cooperates forever. -/\ntheorem y_blend (a b j k h0 M : Nat) (hk : 1 ≤ k) (hab : 1 ≤ a+b) (hh0 : a+b+1 ≤ h0)\n (S x y e : Nat → Prop) (ns : ¬ S h0) (cof : ∀ g, M ≤ g → S g)\n (ex : ∀ g, x g ↔ blend S (fk k y) (gate a b j y e) g)\n (ey : ∀ g, y g ↔ (g ≠ h0-1 ∨ ∀ u, u < g → ¬ x u) ∧ (∀ u, u < g → (h0+1 ≤ u ∨ u < h0 ∨ x u)))\n (ee : ∀ g, e g ↔ (g ≠ h0-1 ∨ ∀ u, u < g → ¬ False) ∧ (∀ u, u < g → (h0+1 ≤ u ∨ u < h0 ∨ False))) :\n eventual (fun g => ¬ x g) ∧ eventual y := by\n have x0 : x 0 := by\n   apply (ex 0).2\n   by_cases s0 : S 0\n   · exact Or.inl ⟨s0, fun u uh => by omega⟩\n   · exact Or.inr ⟨s0, fun u uh => by omega, fun g gh => by omega⟩\n have ny : ¬ y (h0-1) := by\n   intro yh; rcases ((ey _).1 yh).1 with c | c\n   · exact c rfl\n   · exact c 0 (by omega) x0\n have ylow : ∀ u, u < h0-1 → y u := fun u uh =>\n   (ey u).2 ⟨Or.inl (by omega), fun w wu => Or.inr (Or.inl (by omega))⟩\n have elow : ∀ g, g < h0 → e g := fun g gh =>\n   (ee g).2 ⟨Or.inr (fun _ _ c => c), fun w wg => Or.inr (Or.inl (by omega))⟩\n have xh : x h0 := (ex h0).2 (Or.inr ⟨ns, fun u uh => ylow u (by omega),\n   fun g gh => Or.inl (elow g (by omega))⟩)\n refine ⟨⟨M+h0+k, fun g hg xg => ?_⟩, ⟨h0+1, fun g hg => ?_⟩⟩\n · rcases (ex g).1 xg with ⟨_, f⟩ | ⟨nsg, _⟩\n   · exact ny (f (h0-1) (by omega))\n   · exact nsg (cof g (by omega))\n · apply (ey g).2\n   refine ⟨Or.inl (by omega), fun w wg => ?_⟩\n   rcases Nat.lt_trichotomy w h0 with c | c | c\n   · exact Or.inr (Or.inl c)\n   · subst c; exact Or.inr (Or.inr xh)\n   · exact Or.inl c\n\n/-- ... while FairBot and Y both defect eventually (h0 ≥ 2). -/\ntheorem y_fb (h0 : Nat) (h2 : 2 ≤ h0) (u v : Nat → Prop)\n (eu : ∀ g, u g ↔ fk 1 v g)\n (ev : ∀ g, v g ↔ (g ≠ h0-1 ∨ ∀ w, w < g → ¬ u w) ∧ (∀ w, w < g → (h0+1 ≤ w ∨ w < h0 ∨ u w))) :\n eventual (fun g => ¬ u g) ∧ eventual (fun g => ¬ v g) := by\n have u0 : u 0 := (eu 0).2 (fun w wh => by omega)\n have nv : ¬ v (h0-1) := by\n   intro vh; rcases ((ev _).1 vh).1 with c | c\n   · exact c rfl\n   · exact c 0 (by omega) u0\n have nu : ∀ g, h0 ≤ g → ¬ u g := fun g hg ug => nv ((eu g).1 ug (h0-1) (by omega))\n refine ⟨⟨h0, nu⟩, ⟨h0+1, fun g hg vg => ?_⟩⟩\n rcases ((ev g).1 vg).2 h0 (by omega) with c | c | c\n · omega\n · omega\n · exact nu h0 (Nat.le_refl _) c\n\n#print axioms db_trace\n#print axioms reader\n#print axioms cases3\n#print axioms fb_case\n#print axioms rq_blend\n#print axioms rq_fb\n#print axioms y_blend\n#print axioms y_fb\n"
SHA = '8e14ccebc7bafa69139f259935238ceddb248884ba1515e304b0603348b3d5d1'

t0 = time.time()
FB = box(P); CB = neg(BOT); DB = BOT
L = 6
ATS = [at(g) for g in range(L)]
TAIL = neg(bxk(L, BOT))
def sigma(Sfin):
    m = TAIL
    for g in Sfin: m = OR(m, ATS[g])
    return m
def J(a, b, j): return bxk(a + 1, AND(bxk(b, P), OR(Q, box(OR(bxk(j, BOT), neg(Q))))))
def blend(sg, R, A): return OR(AND(sg, R), AND(neg(sg), A))
CC, DD, DC = (1, 1), (0, 0), (0, 1)
Fm = {m: bxk(m, P) for m in range(1, 4)}
PB = lambda i: AND(box(P), box(OR(neg(neg(bxk(i, BOT))), neg(Q))))
BANK = [DB, CB] + [bxk(m, P) for m in range(2, 8)] + [PB(i) for i in range(0, 7)]
FBb = behav(FB)
RQ = {h: reader(h, Q) for h in range(1, L)}
YS = {h0: AND(OR(neg(at(h0 - 1)), box(neg(P))), reader(h0, P)) for h0 in range(2, L)}
for h in RQ: assert game(FB, RQ[h]) == DD
for h0 in YS: assert game(FB, YS[h0]) == DD
n = 0; fbeq = 0; ci = 0; cii = 0; selfcc = 0; selfcc_sep = 0; bank_unsep = 0
for s_ in range(1, 5):
    for a in range(0, s_ + 1):
        b = s_ - a
        for j in range(1, a + b + 1):
            A = J(a, b, j)
            for k in range(1, 4):
                for bits in range(1 << L):
                    Sfin = [g for g in range(L) if bits >> g & 1]
                    inS = lambda h: h in Sfin if h < L else True
                    B = blend(sigma(Sfin), Fm[k], A)
                    d = [(inS(h) and h < k) or (not inS(h) and h < a + b + 1) for h in range(L + 1)]
                    eq = depth(behav(B), FBb) is None
                    fbcase = k == 1 and all(inS(h) for h in range(1, L))
                    assert eq == fbcase, (a, b, j, k, Sfin)
                    sc = game(B, B) == CC
                    selfcc += sc
                    if fbcase:
                        fbeq += 1
                    else:
                        hs = [h for h in range(1, L) if d[h]]
                        h0s = [h for h in range(a + b + 1, L) if not inS(h)]
                        assert hs or h0s, (a, b, j, k, Sfin)
                        if hs:
                            assert game(B, RQ[hs[0]]) == CC, ('Rq', a, b, j, k, Sfin); ci += 1
                        else:
                            assert game(B, YS[h0s[0]]) == DC, ('Y', a, b, j, k, Sfin); cii += 1
                        for h0 in h0s: assert game(B, YS[h0]) == DC
                        if sc:
                            selfcc_sep += 1
                            bank_unsep += all(game(B, O) == game(FB, O) for O in BANK)
                    n += 1
assert n == 7680 and fbeq == 80 and ci + cii == 7600, (n, fbeq, ci, cii)
assert selfcc == 6288 and selfcc_sep == 6208 and bank_unsep == 108, (selfcc, selfcc_sep, bank_unsep)
# hand examples
# (ii) G_{1,1} = J_{0,1,1} = box(box p & (q | box(box F | ~q))) at height 2, FairBot at every other height >= 1:
# one of the 108 bank-unseparated self-CC blends; Y_2 = (~sigma_1 | box ~p) & R_2(p) separates it from FairBot.
B1 = blend(sigma([1, 3, 4, 5]), FB, J(0, 1, 1))
assert game(B1, B1) == CC and game(B1, YS[2]) == DC and game(FB, YS[2]) == DD
assert all(game(B1, O) == game(FB, O) for O in BANK)
# (i) k = 2: DefectBot trace true at height 1; R_1(q) separates.
B2 = blend(sigma([1, 2, 3, 4, 5]), Fm[2], J(1, 1, 1))
assert game(B2, B2) == CC and game(B2, RQ[1]) == CC and game(FB, RQ[1]) == DD
t1 = time.time()
binary = next((p for p in (shutil.which('lean'), '/opt/elan/bin/lean', os.path.expanduser('~/.elan/bin/lean')) if p and os.path.exists(p)), None)
assert binary, 'lean missing'
def run(s): return subprocess.run([binary, '--stdin'], input=s, text=True, capture_output=True, timeout=100)
assert hashlib.sha256(LEAN.encode()).hexdigest() == SHA
r = run(LEAN)
assert r.returncode == 0, r.stdout + r.stderr
assert 'sorryAx' not in r.stdout and r.stdout.count('axioms') == 8, r.stdout
for x, y in [('(hk : 1 ≤ k) (hab : 1 ≤ a+b) (hh0', '(hk : 0 ≤ k) (hab : 1 ≤ a+b) (hh0'),
             ('(h2 : 2 ≤ h0)', '(h2 : 1 ≤ h0)'), ('(h1 : 1 ≤ h)', '(h1 : 0 ≤ h)')]:
    assert LEAN.count(x) == 1, x
    m = run(LEAN.replace(x, y))
    assert m.returncode != 0 or 'sorryAx' in m.stdout, ('mutation accepted', y)
print('PASS: %d cofinite J blends: %d FairBot-equivalent (k=1, S>=N+), %d separated by R_h(q), %d by Y_h0; '
      '%d self-CC, %d separated, %d of them bank-unseparated; Lean 8 theorems, 3 mutations rejected (%.1fs)'
      % (n, fbeq, ci, cii, selfcc, selfcc_sep, bank_unsep, time.time() - t0))
