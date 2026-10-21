"""C046 r1: cofinite gap of K22 closed for V_{n,r} (W_n = V_{n,1}), plus independent cross-check of r2's K25.
Every F_k height blend B = (sigma_S & box^k p) | (~sigma_S & V_{n,r}), n,r,k >= 1, is behaviourally FairBot iff
k = 1 and every height >= 1 is selected (then B is the FairBot operator at every height); otherwise, for cofinite S:
 (i) if its DefectBot trace d(h) = (S h & h<k) | (~S h & h<=n) is true at some h >= 1:
     R_h(q) = box(~box^{h+1}F | box^h F | q):  B/R = CC, FB/R = DD  (works for ANY unselected branch);
 (ii) otherwise k = 1, {1..n} in S and some unselected h0 >= n+1 exists:
     Z_{n,h0} = (~sigma_n | box(~box F | p)) & R_{h0}(p)  (at n cooperate iff partner cooperated at 0; from h0+1
     copy partner's move at h0). Against DefectBot Z defects at n, closing the V gate at witness n, so B defects
     at h0: B/Z = DD, FB/Z = CC.
Finite S: K22 (F_max(1,n-r+1) separates); here only re-checked that no finite blend is FairBot-equivalent.
Lean 4 core (SHA-pinned): db_trace, reader, cases3, fb_case, rq_blend, rq_fb, z_blend, z_fb; no sorryAx;
3 mutations rejected (n>=1, r>=1, h0>=n+1 in z_blend).
Engine (Mealy machines, from c046_jcof.py / K20; no code shared with r2's GLS or Lean): n=1..5, r=1..n+1,
k=1..3, S = any subset of {0..5}, tail from 6 all-in (cofinite) or all-out (finite): 7680 blends;
3840 cofinite: 40 FairBot, 3664 case (i), 136 case (ii); 2522 self-CC, 2482 separated (bank already separates all).
K25 cross-check: DB and CB height blends of V_{n,r}, n=1..5, r=1..n+2, same 128 selectors (3200 pairs): self-CC laws and
exact unexploitability (exploit() search, explicit exploiter re-solved).
Language L: atoms p (opponent's move vs me), q (opponent's move vs DefectBot). Outcomes Boolean tails, no payoffs.
Height-trace bridge assumed, as in all runs.
"""
import hashlib, os, shutil, subprocess, time
from collections import Counter, deque
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


LEAN = "def blend (S f g : Nat → Prop) (h : Nat) := (S h ∧ f h) ∨ (¬ S h ∧ g h)\ndef eventual (x : Nat → Prop) := ∃ H, ∀ h, H ≤ h → x h\n-- V_{n,r} = box(box^n F ∨ (p ∧ (q ∨ ¬box^r q))), height form as in r2's v_self.lean / v_other.lean\ndef gateV (n r : Nat) (p q : Nat → Prop) (h : Nat) : Prop :=\n ∀ g, g < h → g < n ∨ (p g ∧ (q g ∨ ¬ ∀ j, j + r ≤ g → q j))\n/-- F_k = box^k p at height g reads y at every u with u+k ≤ g. -/\ndef fk (k : Nat) (y : Nat → Prop) (g : Nat) := ∀ u, u+k ≤ g → y u\n\n/-- DefectBot trace of the F_k height blend of V_{n,r}. -/\ntheorem db_trace (n r k h : Nat) (S : Nat → Prop) :\n blend S (fk k (fun _ => False)) (gateV n r (fun _ => False) (fun _ => False)) h ↔\n (S h ∧ h < k) ∨ (¬ S h ∧ h ≤ n) := by\n have F : fk k (fun _ => False) h ↔ h < k := by\n  constructor\n  · intro H; apply Classical.byContradiction; intro e; exact H 0 (by omega)\n  · intro H u uh; omega\n have G : gateV n r (fun _ => False) (fun _ => False) h ↔ h ≤ n := by\n  constructor\n  · intro H; apply Classical.byContradiction; intro hn\n    rcases H n (by omega) with c | c\n    · omega\n    · exact c.1\n  · intro hh g gh; exact Or.inl (by omega)\n simp only [blend, F, G]\n\n/-- Height semantics of the reader R_h(r) = box(~box^{h+1}F | box^h F | r): at g it is g ≤ h or r h. -/\ntheorem reader (h g : Nat) (r : Nat → Prop) :\n (∀ u, u < g → (h+1 ≤ u ∨ u < h ∨ r u)) ↔ (g ≤ h ∨ r h) := by\n constructor\n · intro H\n   by_cases gh : g ≤ h\n   · exact Or.inl gh\n   · rcases H h (by omega) with c | c | c\n     · omega\n     · omega\n     · exact Or.inr c\n · intro H u ug\n   rcases Nat.lt_trichotomy u h with c | c | c\n   · exact Or.inr (Or.inl c)\n   · subst c; rcases H with c | c\n     · omega\n     · exact Or.inr (Or.inr c)\n   · exact Or.inl c\n\n/-- Trichotomy for any selector: DefectBot trace true at some h ≥ 1, or an unselected h0 ≥ n+1,\n    or k = 1 and every positive height selected. -/\ntheorem cases3 (n k : Nat) (hk : 1 ≤ k) (S : Nat → Prop) :\n (∃ h, 1 ≤ h ∧ ((S h ∧ h < k) ∨ (¬ S h ∧ h ≤ n))) ∨ (∃ h0, n+1 ≤ h0 ∧ ¬ S h0) ∨\n (k = 1 ∧ ∀ h, 1 ≤ h → S h) := by\n classical\n by_cases c1 : ∃ h, 1 ≤ h ∧ ((S h ∧ h < k) ∨ (¬ S h ∧ h ≤ n))\n · exact Or.inl c1\n · by_cases c2 : ∃ h0, n+1 ≤ h0 ∧ ¬ S h0\n   · exact Or.inr (Or.inl c2)\n   · have allS : ∀ h, 1 ≤ h → S h := by\n       intro h h1; apply Classical.byContradiction; intro ns\n       by_cases hl : h ≤ n\n       · exact c1 ⟨h, h1, Or.inr ⟨ns, hl⟩⟩\n       · exact c2 ⟨h, by omega, ns⟩\n     refine Or.inr (Or.inr ⟨?_, allS⟩)\n     apply Classical.byContradiction; intro nk\n     exact c1 ⟨1, Nat.le_refl 1, Or.inl ⟨allS 1 (Nat.le_refl 1), by omega⟩⟩\n\n/-- Third case: the blend is the FairBot operator box p at every height, for every input. -/\ntheorem fb_case (n r : Nat) (S y e : Nat → Prop) (allS : ∀ h, 1 ≤ h → S h) (h : Nat) :\n blend S (fk 1 y) (gateV n r y e) h ↔ fk 1 y h := by\n constructor\n · rintro (⟨_, f⟩ | ⟨ns, _⟩)\n   · exact f\n   · have h0 : h = 0 := by\n       apply Classical.byContradiction; intro hn; exact ns (allS h (by omega))\n     subst h0; intro u uh; omega\n · intro f\n   by_cases sh : S h\n   · exact Or.inl ⟨sh, f⟩\n   · have h0 : h = 0 := by\n       apply Classical.byContradiction; intro hn; exact sh (allS h (by omega))\n     subst h0\n     exact Or.inr ⟨sh, fun g gh => by omega⟩\n\n/-- First case, for ANY unselected branch G: R_h(q) cooperates forever against a cofinite F_k blend\n    whose DefectBot trace d is true at h, and the blend cooperates eventually. -/\ntheorem rq_blend (k h M : Nat) (S d x y : Nat → Prop) (G : Nat → Prop) (cof : ∀ g, M ≤ g → S g) (dh : d h)\n (ex : ∀ g, x g ↔ blend S (fk k y) G g)\n (ey : ∀ g, y g ↔ (g ≤ h ∨ d h)) : eventual x ∧ ∀ g, y g := by\n have ya : ∀ g, y g := fun g => (ey g).2 (Or.inr dh)\n exact ⟨⟨M, fun g gm => (ex g).2 (Or.inl ⟨cof g gm, fun u _ => ya u⟩)⟩, ya⟩\n\n/-- ... while FairBot (DefectBot trace true only at 0) and R_h(q), h ≥ 1, both defect eventually. -/\ntheorem rq_fb (h : Nat) (h1 : 1 ≤ h) (u v : Nat → Prop)\n (eu : ∀ g, u g ↔ fk 1 v g) (ev : ∀ g, v g ↔ (g ≤ h ∨ h < 1)) :\n eventual (fun g => ¬ u g) ∧ eventual (fun g => ¬ v g) := by\n have nv : ∀ g, h+1 ≤ g → ¬ v g := fun g hg vg => by rcases (ev g).1 vg with c | c <;> omega\n exact ⟨⟨h+2, fun g hg ug => nv (h+1) (Nat.le_refl _) ((eu g).1 ug (h+1) (by omega))⟩, ⟨h+1, nv⟩⟩\n\n/-- Second case: Z = (~sigma_n | box(~box F | p)) & R_{h0}(p): at height n cooperate iff the partner\n    cooperated at 0; from h0+1 copy the partner's move at h0. Against DefectBot Z defects at n, which\n    closes the V gate at witness n; so a cofinite F_k blend of V_{n,r} with unselected h0 ≥ n+1\n    defects at h0 and then the blend and Z defect forever. -/\ntheorem z_blend (n r k h0 M : Nat) (hn : 1 ≤ n) (hr : 1 ≤ r) (hh0 : n+1 ≤ h0)\n (S x y e : Nat → Prop) (ns : ¬ S h0) (cof : ∀ g, M ≤ g → S g)\n (ex : ∀ g, x g ↔ blend S (fk k y) (gateV n r y e) g)\n (ey : ∀ g, y g ↔ (g ≠ n ∨ ∀ u, u < g → (1 ≤ u ∨ x u)) ∧ (∀ u, u < g → (h0+1 ≤ u ∨ u < h0 ∨ x u)))\n (ee : ∀ g, e g ↔ (g ≠ n ∨ ∀ u, u < g → (1 ≤ u ∨ False)) ∧ (∀ u, u < g → (h0+1 ≤ u ∨ u < h0 ∨ False))) :\n eventual (fun g => ¬ x g) ∧ eventual (fun g => ¬ y g) := by\n have ne : ¬ e n := by\n   intro en; rcases ((ee n).1 en).1 with c | c\n   · exact c rfl\n   · rcases c 0 (by omega) with c | c\n     · omega\n     · exact c\n have elow : ∀ j, j < n → e j := fun j jn =>\n   (ee j).2 ⟨Or.inl (by omega), fun w wj => Or.inr (Or.inl (by omega))⟩\n have nxh : ¬ x h0 := by\n   intro xh\n   rcases (ex h0).1 xh with ⟨sh, _⟩ | ⟨_, gt⟩\n   · exact ns sh\n   · rcases gt n (by omega) with c | ⟨_, c⟩\n     · omega\n     · rcases c with c | c\n       · exact ne c\n       · exact c (fun j jr => elow j (by omega))\n have nyh : ∀ g, h0+1 ≤ g → ¬ y g := by\n   intro g hg yg\n   rcases ((ey g).1 yg).2 h0 (by omega) with c | c | c\n   · omega\n   · omega\n   · exact nxh c\n refine ⟨⟨M+h0+k+1, fun g hg xg => ?_⟩, ⟨h0+1, nyh⟩⟩\n rcases (ex g).1 xg with ⟨_, f⟩ | ⟨nsg, _⟩\n · exact nyh (h0+1) (Nat.le_refl _) (f (h0+1) (by omega))\n · exact nsg (cof g (by omega))\n\n/-- ... while FairBot and Z cooperate at every height (any n, h0). -/\ntheorem z_fb (n h0 : Nat) (u v : Nat → Prop)\n (eu : ∀ g, u g ↔ fk 1 v g)\n (ev : ∀ g, v g ↔ (g ≠ n ∨ ∀ w, w < g → (1 ≤ w ∨ u w)) ∧ (∀ w, w < g → (h0+1 ≤ w ∨ w < h0 ∨ u w))) :\n ∀ g, u g ∧ v g := by\n intro g\n induction g using Nat.strongRecOn with\n | ind g ih =>\n   have ug : u g := (eu g).2 (fun w wg => (ih w (by omega)).2)\n   refine ⟨ug, (ev g).2 ⟨?_, fun w wg => Or.inr (Or.inr (ih w wg).1)⟩⟩\n   exact Or.inr (fun w wg => Or.inr (ih w wg).1)\n\n#print axioms db_trace\n#print axioms reader\n#print axioms cases3\n#print axioms fb_case\n#print axioms rq_blend\n#print axioms rq_fb\n#print axioms z_blend\n#print axioms z_fb\n"
SHA = '19f32dc248930560bb2083f83b845b756629dd3f64d869d4d2c4bd4f7b12f2d2'

t0 = time.time()
FB = box(P); CB = neg(BOT); DB = BOT
L = 6
ATS = [at(g) for g in range(L)]
TAIL = neg(bxk(L, BOT))
def sigma(Sf, cof):
    m = TAIL if cof else BOT
    for g in Sf: m = OR(m, ATS[g])
    return m
def V(n, r): return box(OR(bxk(n, BOT), AND(P, OR(Q, neg(bxk(r, Q))))))
def blend(sg, R, A): return OR(AND(sg, R), AND(neg(sg), A))
CC, DD = (1, 1), (0, 0)
Fm = {m: bxk(m, P) for m in range(1, 4)}
PB = lambda i: AND(box(P), box(OR(neg(neg(bxk(i, BOT))), neg(Q))))
BANK = [DB, CB] + [bxk(m, P) for m in range(2, 8)] + [PB(i) for i in range(0, 7)]
FBb = behav(FB)
RQ = {h: reader(h, Q) for h in range(1, L)}
ZS = {(n, h0): AND(OR(neg(at(n)), box(OR(neg(box(BOT)), P))), reader(h0, P))
      for n in range(1, L) for h0 in range(n + 1, L)}
for h in RQ: assert game(FB, RQ[h]) == DD
for z in ZS.values(): assert game(FB, z) == CC
c = Counter()
for n in range(1, 6):
    for r in range(1, n + 2):
        A = V(n, r)
        for k in range(1, 4):
            for bits in range(1 << L):
                Sf = [g for g in range(L) if bits >> g & 1]
                for cof in (True, False):
                    inS = lambda h: (h in Sf) if h < L else cof
                    B = blend(sigma(Sf, cof), Fm[k], A)
                    eq = depth(behav(B), FBb) is None
                    fbcase = cof and k == 1 and all(inS(h) for h in range(1, L))
                    assert eq == fbcase, (n, r, k, Sf, cof)
                    sc = game(B, B) == CC
                    if not cof:
                        c['fin'] += 1; c['fin_selfCC'] += sc; continue
                    c['cof'] += 1; c['cof_selfCC'] += sc
                    if fbcase: c['fb'] += 1; continue
                    d = [(inS(h) and h < k) or (not inS(h) and h <= n) for h in range(L + 1)]
                    hs = [h for h in range(1, L) if d[h]]
                    h0s = [h for h in range(n + 1, L) if not inS(h)]
                    assert hs or h0s, (n, r, k, Sf)
                    for h in hs: assert game(B, RQ[h]) == CC, ('Rq', n, r, k, Sf, h)
                    if hs: c['i'] += 1
                    else:
                        assert k == 1
                        for h0 in h0s: assert game(B, ZS[n, h0]) == DD, ('Z', n, r, k, Sf, h0)
                        c['ii'] += 1
                    if sc:
                        c['selfCC_sep'] += 1
                        c['bank_unsep'] += all(game(B, O) == game(FB, O) for O in BANK)
assert c['cof'] == 3840 and c['fin'] == 3840 and c['fb'] == 40, c
assert c['i'] == 3664 and c['ii'] == 136 and c['cof_selfCC'] == 2522 and c['selfCC_sep'] == 2482, c
assert c['fin_selfCC'] == 1010 and c['bank_unsep'] == 0, c
# hand example (ii): W_2 with FairBot at every height except 3 (k=1): self-CC, Z_{2,3} gives DD, FB gets CC.
Bh = blend(sigma([0, 1, 2, 4, 5], True), FB, V(2, 1))
assert game(Bh, Bh) == CC and game(Bh, ZS[2, 3]) == DD and game(FB, ZS[2, 3]) == CC
assert game(Bh, FB) == CC and game(Bh, CB) == CC and exploit(Bh) is None
# hand example (i): W_2 with F_2 at every height >= 1: DefectBot trace true at 1, R_1(q) separates.
Bi = blend(sigma([1, 2, 3, 4, 5], True), Fm[2], V(2, 1))
assert game(Bi, RQ[1]) == CC and game(FB, RQ[1]) == DD

# K25 cross-check (r2): DB / CB height blends of V_{n,r}
k25 = Counter()
for n in range(1, 6):
    for r in range(1, n + 3):
        A = V(n, r)
        for bits in range(1 << L):
            Sf = [g for g in range(L) if bits >> g & 1]
            for cof in (True, False):
                Sset = set(Sf)
                sg = sigma(Sf, cof)
                Bd = blend(sg, DB, A)
                law = (not cof) and all(s < n for s in Sset) and any(s + r <= n + 1 for s in Sset)
                assert (game(Bd, Bd) == CC) == law, ('K25 DB', n, r, Sf, cof)
                ex = exploit(Bd)
                assert ex is None, ('DB blend exploitable', n, r, Sf, cof)
                Bc = blend(sg, CB, A)
                assert (game(Bc, Bc) == CC) == cof, ('K25 CB', n, r, Sf, cof)
                ex = exploit(Bc)
                if cof:
                    assert ex is not None and game(Bc, ex)[0] == 1 and game(Bc, ex)[1] == 0
                else:
                    assert ex is None, ('finite CB blend exploitable', n, r, Sf, cof)
                k25['cells'] += 1; k25['db_selfCC'] += law
assert k25['cells'] == 3200 and k25['db_selfCC'] == 258, k25

t1 = time.time()
binary = next((p for p in (shutil.which('lean'), '/opt/elan/bin/lean', os.path.expanduser('~/.elan/bin/lean')) if p and os.path.exists(p)), None)
assert binary, 'lean missing'
def run(s): return subprocess.run([binary, '--stdin'], input=s, text=True, capture_output=True, timeout=100)
assert hashlib.sha256(LEAN.encode()).hexdigest() == SHA
res = run(LEAN)
assert res.returncode == 0, res.stdout + res.stderr
assert 'sorryAx' not in res.stdout and res.stdout.count('axioms') == 8, res.stdout
for x, y in [('(hn : 1 ≤ n) (hr', '(hn : 0 ≤ n) (hr'), ('(hr : 1 ≤ r)', '(hr : 0 ≤ r)'),
             ('(hh0 : n+1 ≤ h0)', '(hh0 : n ≤ h0)')]:
    assert LEAN.count(x) == 1, x
    m = run(LEAN.replace(x, y))
    assert m.returncode != 0 or 'sorryAx' in m.stdout, ('mutation accepted', y)
print('PASS: cofinite V blends %d: %d FairBot (k=1, S>=N+), %d R_h(q)-separated (CC/DD), %d Z-separated (DD/CC); '
      '%d self-CC, %d separated, bank-unseparated %d; finite %d none FB-equivalent; K25: %d DB/CB cells '
      '(%d DB self-CC) laws and exact unexploitability; Lean 8 theorems, 3 mutations rejected (%.1fs)'
      % (c['cof'], c['fb'], c['i'], c['ii'], c['cof_selfCC'], c['selfCC_sep'], c['bank_unsep'], c['fin'],
         k25['cells'], k25['db_selfCC'], time.time() - t0))
