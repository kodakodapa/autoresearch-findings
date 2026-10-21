"""C046 r1: modal-depth lower bound for separators of consecutive graded FairBots F_k = []^k p, F_{k+1}.
Language L: atoms p (opponent's move vs me), q (opponent's move vs DefectBot); F,~,&,|,[]; guarded; size = AST
nodes; height semantics; game wiring as in K38 (O's p = F_j's move vs O, O's q = F_j's DefectBot trace h<j).
Part 1 (Lean 4 core, SHA-pinned): same_outcome -- every guarded O with md(O) <= k gets the same eventual outcome
 against F_k and F_{k+1} (both all-C, or from some height O's moves coincide and both F defect), for EVERY k;
 separator_bound -- hence any guarded separator has md >= k+1 and size >= k+2; sk_depth -- K49's S_k has md k+1
 (tight). Proof: O vs F_j sees p all-true up to its first defection g0, then thresholds (p below g0+j, q below j);
 depth-d formulas cannot tell threshold models apart when block lengths agree or are both >= d (explicit
 back-and-forth on clipped block counts). No sorryAx; 5 mutations rejected.
Part 2 (exact Mealy engine of c046_fk_sep14.py with (class, depth) enumeration): for k=1..6 no guarded class of
 depth <= k and size <= 12 separates F_k/F_{k+1}; control: at depth k+1 separators exist (k=1..4, incl. S_k).
Part 3 (independent literal evaluator, exact K40 horizon): 3200 random guarded opponents of depth <= k, k=1..8,
 same outcome; S_k and T_k (K56) of depth k+1 separate.
Scope: depth bound only; the size bound k+2 is weaker than the bounded minima k+5 (K49) / k+6 (K56).
"""
import sys, time
t0=time.time()

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
                for (pool, first, add) in (((G, firstG, addG),) if n == N else ((U, firstU, addU), (G, firstG, addG))):
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
    return U, G, firstU, firstG




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
LEAN = "set_option linter.unusedVariables false\n\ninductive Fm where\n  | bot | pa | qa | neg (a : Fm) | cj (a b : Fm) | dj (a b : Fm) | box (a : Fm)\nopen Fm\n\ndef md : Fm → Nat\n  | bot => 0 | pa => 0 | qa => 0\n  | neg a => md a\n  | cj a b => max (md a) (md b)\n  | dj a b => max (md a) (md b)\n  | box a => md a + 1\n\ndef size : Fm → Nat\n  | bot => 1 | pa => 1 | qa => 1\n  | neg a => size a + 1\n  | cj a b => size a + size b + 1\n  | dj a b => size a + size b + 1\n  | box a => size a + 1\n\ndef ev (P Q : Nat → Prop) : Fm → Nat → Prop\n  | bot, _ => False\n  | pa, h => P h\n  | qa, h => Q h\n  | neg a, h => ¬ ev P Q a h\n  | cj a b, h => ev P Q a h ∧ ev P Q b h\n  | dj a b, h => ev P Q a h ∨ ev P Q b h\n  | box a, h => ∀ g, g < h → ev P Q a g\n\ndef Guarded : Fm → Prop\n  | bot => True | pa => False | qa => False\n  | neg a => Guarded a\n  | cj a b => Guarded a ∧ Guarded b\n  | dj a b => Guarded a ∧ Guarded b\n  | box _ => True\n\ntheorem md_lt_size (a : Fm) : md a + 1 ≤ size a := by\n  induction a <;> simp only [md, size] <;> omega\n\n/-- causality: agreement up to h fixes truth at h -/\ntheorem upto (P Q P' Q' : Nat → Prop) : ∀ (a : Fm) (h : Nat),\n    (∀ g, g ≤ h → ((P g ↔ P' g) ∧ (Q g ↔ Q' g))) → (ev P Q a h ↔ ev P' Q' a h) := by\n  intro a\n  induction a with\n  | bot => intro h _; simp [ev]\n  | pa => intro h H; exact (H h (Nat.le_refl _)).1\n  | qa => intro h H; exact (H h (Nat.le_refl _)).2\n  | neg a ih => intro h H; simp only [ev]; rw [ih h H]\n  | cj a b iha ihb => intro h H; simp only [ev]; rw [iha h H, ihb h H]\n  | dj a b iha ihb => intro h H; simp only [ev]; rw [iha h H, ihb h H]\n  | box a ih =>\n    intro h H; simp only [ev]\n    constructor\n    · intro k g hg; exact (ih g (fun x hx => H x (by omega))).1 (k g hg)\n    · intro k g hg; exact (ih g (fun x hx => H x (by omega))).2 (k g hg)\n\n/-- guarded causality: agreement strictly below h fixes truth at h -/\ntheorem below (P Q P' Q' : Nat → Prop) : ∀ (a : Fm) (h : Nat), Guarded a →\n    (∀ g, g < h → ((P g ↔ P' g) ∧ (Q g ↔ Q' g))) → (ev P Q a h ↔ ev P' Q' a h) := by\n  intro a\n  induction a with\n  | bot => intro h _ _; simp [ev]\n  | pa => intro h hg; exact hg.elim\n  | qa => intro h hg; exact hg.elim\n  | neg a ih => intro h hg H; simp only [ev]; rw [ih h hg H]\n  | cj a b iha ihb => intro h hg H; simp only [ev]; rw [iha h hg.1 H, ihb h hg.2 H]\n  | dj a b iha ihb => intro h hg H; simp only [ev]; rw [iha h hg.1 H, ihb h hg.2 H]\n  | box a ih =>\n    intro h _ H; simp only [ev]\n    constructor\n    · intro k g hg; exact (upto P Q P' Q' a g (fun x hx => H x (by omega))).1 (k g hg)\n    · intro k g hg; exact (upto P Q P' Q' a g (fun x hx => H x (by omega))).2 (k g hg)\n\n/-! Threshold models: p true below Pt, q true below Qt (Qt ≤ Pt). -/\ndef T (n : Nat) : Nat → Prop := fun g => g < n\n\n/-- clipped block counts of the prefix [0,a): q-block, p-only block, empty block -/\ndef Cnt (d Pt Qt Pt' Qt' a b : Nat) : Prop :=\n  min (min a Qt) d = min (min b Qt') d ∧\n  min (min (a - Qt) (Pt - Qt)) d = min (min (b - Qt') (Pt' - Qt')) d ∧\n  min (a - Pt) d = min (b - Pt') d\n\ndef Lab (Pt Qt Pt' Qt' a b : Nat) : Prop := (a < Pt ↔ b < Pt') ∧ (a < Qt ↔ b < Qt')\n\ntheorem cnt_symm {d Pt Qt Pt' Qt' a b : Nat} : Cnt d Pt Qt Pt' Qt' a b → Cnt d Pt' Qt' Pt Qt b a := by\n  unfold Cnt; omega\n\ntheorem forth {d Pt Qt Pt' Qt' a b a' : Nat} (hQ : Qt ≤ Pt) (hQ' : Qt' ≤ Pt')\n    (H : Cnt (d+1) Pt Qt Pt' Qt' a b) (ha : a' < a) :\n    ∃ b', b' < b ∧ Cnt d Pt Qt Pt' Qt' a' b' ∧ Lab Pt Qt Pt' Qt' a' b' := by\n  obtain ⟨H0, H1, H2⟩ := H\n  unfold Cnt Lab\n  by_cases h0 : a' < Qt\n  · have hb : min a' d < min b Qt' := by clear H1 H2; omega\n    clear H0 H1 H2\n    exact ⟨min a' d, by omega, ⟨by omega, by omega, by omega⟩, by omega⟩\n  · by_cases h1 : a' < Pt\n    · have hb : min (a' - Qt) d < min (b - Qt') (Pt' - Qt') := by clear H0 H2; omega\n      have e0 : min Qt d = min Qt' d := by clear H1 H2; omega\n      clear H0 H1 H2\n      exact ⟨Qt' + min (a' - Qt) d, by omega, ⟨by omega, by omega, by omega⟩, by omega⟩\n    · have hb : min (a' - Pt) d < b - Pt' := by clear H0 H1; omega\n      have e0 : min Qt d = min Qt' d := by clear H1 H2; omega\n      have e1 : min (Pt - Qt) d = min (Pt' - Qt') d := by clear H0 H2; omega\n      clear H0 H1 H2\n      exact ⟨Pt' + min (a' - Pt) d, by omega, ⟨by omega, by omega, by omega⟩, by omega⟩\n\n/-- depth-d formulas cannot tell related positions of two threshold models apart -/\ntheorem ev_rel {Pt Qt Pt' Qt' : Nat} (hQ : Qt ≤ Pt) (hQ' : Qt' ≤ Pt') : ∀ (φ : Fm) (d a b : Nat),\n    md φ ≤ d → Cnt d Pt Qt Pt' Qt' a b → Lab Pt Qt Pt' Qt' a b →\n    (ev (T Pt) (T Qt) φ a ↔ ev (T Pt') (T Qt') φ b) := by\n  intro φ\n  induction φ with\n  | bot => intro d a b _ _ _; simp [ev]\n  | pa => intro d a b _ _ L; simp only [ev, T]; exact L.1\n  | qa => intro d a b _ _ L; simp only [ev, T]; exact L.2\n  | neg a ih => intro d x y hd C L; simp only [ev, md] at *; rw [ih d x y hd C L]\n  | cj a b iha ihb =>\n    intro d x y hd C L; simp only [ev, md] at *\n    rw [iha d x y (by omega) C L, ihb d x y (by omega) C L]\n  | dj a b iha ihb =>\n    intro d x y hd C L; simp only [ev, md] at *\n    rw [iha d x y (by omega) C L, ihb d x y (by omega) C L]\n  | box a ih =>\n    intro d x y hd C L; simp only [ev, md] at *\n    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩\n    constructor\n    · intro k y' hy'\n      obtain ⟨x', hx', C', L'⟩ := forth hQ' hQ (cnt_symm C) hy'\n      exact (ih d' x' y' (by omega) (cnt_symm C') (by unfold Lab at *; omega)).1 (k x' hx')\n    · intro k x' hx'\n      obtain ⟨y', hy', C', L'⟩ := forth hQ hQ' C hx'\n      exact (ih d' x' y' (by omega) C' L').2 (k y' hy')\n\n/-- for guarded formulas the own label is irrelevant -/\ntheorem ev_guarded {Pt Qt Pt' Qt' : Nat} (hQ : Qt ≤ Pt) (hQ' : Qt' ≤ Pt') : ∀ (φ : Fm) (d a b : Nat),\n    Guarded φ → md φ ≤ d → Cnt d Pt Qt Pt' Qt' a b →\n    (ev (T Pt) (T Qt) φ a ↔ ev (T Pt') (T Qt') φ b) := by\n  intro φ\n  induction φ with\n  | bot => intro d a b _ _ _; simp [ev]\n  | pa => intro d a b hg; exact hg.elim\n  | qa => intro d a b hg; exact hg.elim\n  | neg a ih => intro d x y hg hd C; simp only [ev, md, Guarded] at *; rw [ih d x y hg hd C]\n  | cj a b iha ihb =>\n    intro d x y hg hd C; simp only [ev, md, Guarded] at *\n    rw [iha d x y hg.1 (by omega) C, ihb d x y hg.2 (by omega) C]\n  | dj a b iha ihb =>\n    intro d x y hg hd C; simp only [ev, md, Guarded] at *\n    rw [iha d x y hg.1 (by omega) C, ihb d x y hg.2 (by omega) C]\n  | box a _ =>\n    intro d x y _ hd C; simp only [ev, md] at *\n    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩\n    constructor\n    · intro k y' hy'\n      obtain ⟨x', hx', C', L'⟩ := forth hQ' hQ (cnt_symm C) hy'\n      exact (ev_rel hQ hQ' a d' x' y' (by omega) (cnt_symm C') (by unfold Lab at *; omega)).1 (k x' hx')\n    · intro k x' hx'\n      obtain ⟨y', hy', C', L'⟩ := forth hQ hQ' C hx'\n      exact (ev_rel hQ hQ' a d' x' y' (by omega) C' L').2 (k y' hy')\n\n/-! Games of an opponent O against F_j = box^j p (K38 wiring):\n O's p = F_j's move, O's q = F_j's DefectBot trace (h < j); F_j's move needs O's moves at all g ≤ h - j. -/\ndef GameRec (O : Fm) (j : Nat) (o f : Nat → Prop) : Prop :=\n  ∀ h, (o h ↔ ev f (T j) O h) ∧ (f h ↔ ∀ g, g + j ≤ h → o g)\n\n/-- O against an all-cooperating partner -/\ndef A (O : Fm) (j x : Nat) : Prop := ev (fun _ => True) (T j) O x\n\ntheorem prefix_agree {O : Fm} {j : Nat} {o f : Nat → Prop} (hg : Guarded O) (G : GameRec O j o f)\n    (h : Nat) (hA : ∀ x, x < h → A O j x) : ∀ x, x ≤ h → (o x ↔ A O j x) := by\n  have main : ∀ n, ∀ x, x < n → x ≤ h → (o x ↔ A O j x) := by\n    intro n\n    induction n with\n    | zero => intro x hx; omega\n    | succ n ih =>\n      intro x hxn hx\n      rw [(G x).1]\n      apply below _ _ _ _ O x hg\n      intro g hg'\n      refine ⟨?_, Iff.rfl⟩\n      rw [(G g).2]\n      constructor\n      · intro _; trivial\n      · intro _ y hy\n        exact (ih y (by omega) (by omega)).2 (hA y (by omega))\n  exact fun x hx => main (x+1) x (by omega) hx\n\ntheorem all_coop {O : Fm} {j : Nat} {o f : Nat → Prop} (hg : Guarded O) (G : GameRec O j o f)\n    (hA : ∀ x, A O j x) : ∀ h, o h ∧ f h := by\n  have ho : ∀ h, o h := fun h => (prefix_agree hg G h (fun x _ => hA x) h (Nat.le_refl _)).2 (hA h)\n  exact fun h => ⟨ho h, (G h).2.2 (fun g _ => ho g)⟩\n\ntheorem tail_form {O : Fm} {j : Nat} {o f : Nat → Prop} (hg : Guarded O) (G : GameRec O j o f)\n    (g0 : Nat) (h0 : ¬ A O j g0) (hlt : ∀ x, x < g0 → A O j x) :\n    (∀ h, (f h ↔ h < g0 + j)) ∧ (∀ h, (o h ↔ ev (T (g0 + j)) (T j) O h)) := by\n  have pa := prefix_agree hg G g0 hlt\n  have hf : ∀ h, (f h ↔ h < g0 + j) := by\n    intro h\n    rw [(G h).2]\n    constructor\n    · intro k\n      apply Classical.byContradiction\n      intro hn\n      exact h0 ((pa g0 (Nat.le_refl _)).1 (k g0 (by omega)))\n    · intro hh y hy\n      exact (pa y (by omega)).2 (hlt y (by omega))\n  refine ⟨hf, fun h => ?_⟩\n  rw [(G h).1]\n  exact upto _ _ _ _ O h (fun g _ => ⟨hf g, Iff.rfl⟩)\n\ntheorem A_model {O : Fm} (hg : Guarded O) (j x Pt : Nat) (hx : x < Pt) :\n    (A O j x ↔ ev (T Pt) (T j) O x) :=\n  below _ _ _ _ O x hg (fun g hg' => ⟨⟨fun _ => show g < Pt by omega, fun _ => trivial⟩, Iff.rfl⟩)\n\ntheorem corr_low {O : Fm} {k : Nat} (hg : Guarded O) (hd : md O ≤ k) (x : Nat) (hx : x ≤ k) :\n    (A O k x ↔ A O (k+1) x) := by\n  rw [A_model hg k x (x+k+2) (by omega), A_model hg (k+1) x (x+k+2) (by omega)]\n  exact ev_guarded (by omega) (by omega) O k x x hg hd (by unfold Cnt; omega)\n\ntheorem corr_high {O : Fm} {k : Nat} (hg : Guarded O) (hd : md O ≤ k) (x : Nat) (hx : k + 1 ≤ x) :\n    (A O k (x - 1) ↔ A O (k+1) x) := by\n  rw [A_model hg k (x-1) (x+k+2) (by omega), A_model hg (k+1) x (x+k+2) (by omega)]\n  exact ev_guarded (by omega) (by omega) O k (x-1) x hg hd (by unfold Cnt; omega)\n\ntheorem least {R : Nat → Prop} (n : Nat) (hn : ¬ R n) : ∃ g, ¬ R g ∧ ∀ x, x < g → R x := by\n  induction n using Nat.strongRecOn with\n  | _ n ih =>\n    by_cases hall : ∀ x, x < n → R x\n    · exact ⟨n, hn, hall⟩\n    · have : ∃ x, x < n ∧ ¬ R x := Classical.byContradiction (fun hc =>\n        hall (fun x hx => Classical.byContradiction (fun hr => hc ⟨x, hx, hr⟩)))\n      obtain ⟨x, hx, hr⟩ := this\n      exact ih x hx hr\n\n/-- MAIN: an opponent of modal depth ≤ k gets the same eventual outcome against F_k and F_{k+1}\n (both all-cooperate, or from some height on its moves coincide and both FairBots defect). -/\ntheorem same_outcome (O : Fm) (k : Nat) (hg : Guarded O) (hd : md O ≤ k)\n    (o f o' f' : Nat → Prop) (G : GameRec O k o f) (G' : GameRec O (k+1) o' f') :\n    ((∀ h, o h ∧ f h) ∧ (∀ h, o' h ∧ f' h)) ∨\n    ∃ H, ∀ h, H ≤ h → ((o h ↔ o' h) ∧ ¬ f h ∧ ¬ f' h) := by\n  classical\n  by_cases hall : ∀ x, A O k x\n  · left\n    refine ⟨all_coop hg G hall, all_coop hg G' ?_⟩\n    intro x\n    by_cases hx : x ≤ k\n    · exact (corr_low hg hd x hx).1 (hall x)\n    · exact (corr_high hg hd x (by omega)).1 (hall (x-1))\n  · right\n    have ex : ∃ x, ¬ A O k x := Classical.byContradiction (fun hn => hall (fun x => Classical.byContradiction (fun hx => hn ⟨x, hx⟩)))\n    have ex' : ∃ x, ¬ A O (k+1) x := by\n      apply Classical.byContradiction\n      intro hn\n      apply hall\n      intro x\n      have hx1 : A O (k+1) (x+1) := Classical.byContradiction (fun hx => hn ⟨x+1, hx⟩)\n      have hx0 : A O (k+1) x := Classical.byContradiction (fun hx => hn ⟨x, hx⟩)\n      by_cases hxk : x ≤ k\n      · exact (corr_low hg hd x hxk).2 hx0\n      · have := (corr_high hg hd (x+1) (by omega)).2 hx1\n        simpa using this\n    obtain ⟨x0, hx0⟩ := ex\n    obtain ⟨x1, hx1⟩ := ex'\n    obtain ⟨g0, s0, m0⟩ := least x0 hx0\n    obtain ⟨g1, s1, m1⟩ := least x1 hx1\n    have key : min g0 k = min g1 k := by\n      by_cases c0 : g0 ≤ k\n      · have n1 : ¬ A O (k+1) g0 := fun h => s0 ((corr_low hg hd g0 c0).2 h)\n        have u1 : g1 ≤ g0 := Classical.byContradiction (fun hc => n1 (m1 g0 (by omega)))\n        have u2 : g0 ≤ g1 := Classical.byContradiction (fun hc =>\n          s1 ((corr_low hg hd g1 (by omega)).1 (m0 g1 (by omega))))\n        omega\n      · by_cases c1 : g1 ≤ k\n        · exact absurd ((corr_low hg hd g1 c1).1 (m0 g1 (by omega))) s1\n        · omega\n    obtain ⟨hf, ho⟩ := tail_form hg G g0 s0 m0\n    obtain ⟨hf', ho'⟩ := tail_form hg G' g1 s1 m1\n    refine ⟨g0 + g1 + 3 * k + 2, fun h hh => ⟨?_, ?_, ?_⟩⟩\n    · rw [ho h, ho' h]\n      exact ev_guarded (by omega) (by omega) O k h h hg hd (by unfold Cnt; omega)\n    · rw [hf h]; omega\n    · rw [hf' h]; omega\n\n/-- corollary: every guarded separator of F_k and F_{k+1} has modal depth ≥ k+1, hence size ≥ k+2 -/\ntheorem separator_bound (O : Fm) (k : Nat) (hg : Guarded O)\n    (o f o' f' : Nat → Prop) (G : GameRec O k o f) (G' : GameRec O (k+1) o' f')\n    (hsep : ¬ (((∀ h, o h ∧ f h) ∧ (∀ h, o' h ∧ f' h)) ∨\n      ∃ H, ∀ h, H ≤ h → ((o h ↔ o' h) ∧ ¬ f h ∧ ¬ f' h))) :\n    k + 1 ≤ md O ∧ k + 2 ≤ size O := by\n  have : k + 1 ≤ md O := by\n    apply Classical.byContradiction\n    intro hn\n    exact hsep (same_outcome O k hg (by omega) o f o' f' G G')\n  have := md_lt_size O\n  omega\n\ndef boxes : Nat → Fm → Fm\n  | 0, a => a\n  | n+1, a => box (boxes n a)\n\ntheorem md_boxes (n : Nat) : md (boxes n bot) = n := by\n  induction n with\n  | zero => rfl\n  | succ n ih => simp [boxes, md, ih]\n\n/-- tightness: K49's S_k = box(~q | box^k F) has depth exactly k+1 -/\ntheorem sk_depth (k : Nat) : md (box (dj (neg qa) (boxes k bot))) = k + 1 := by\n  simp [md, md_boxes]\n\n#print axioms same_outcome\n#print axioms separator_bound\n#print axioms sk_depth\n"
LEANSHA = 'f334a95b7febb77f00125e2e6821357f7d45ac7d0d0b92402b675dcb2cddbee9'

def Fk(k): return bxk(k,P)
def enum_depth(N,D):
    """(class, depth) pairs: every guarded p,q formula of size <= N and modal depth <= D is in some class
    recorded with a realiser of depth <= D (a class is re-added whenever a shallower realiser appears)."""
    U={};G={};bU={};bG={}
    def add(pool,best,n,c,d):
        if d<best.get(c,99): best[c]=d; pool[n].append((c,d))
    for n in range(1,N+1):
        U[n]=[];G[n]=[]
        if n==1:
            add(U,bU,1,BOT,0);add(U,bU,1,P,0);add(U,bU,1,Q,0);add(G,bG,1,BOT,0)
        else:
            for c,d in U[n-1]:
                add(U,bU,n,neg(c),d)
                if d<D:
                    b=box(c);add(U,bU,n,b,d+1);add(G,bG,n,b,d+1)
            for c,d in G[n-1]: add(G,bG,n,neg(c),d)
            for i in range(1,n-1):
                j=n-1-i
                if i>j: break
                pools=((G,bG),) if n==N else ((U,bU),(G,bG))
                for pool,best in pools:
                    for ai,(a,da) in enumerate(pool[i]):
                        for bi,(b,db) in enumerate(pool[j]):
                            if i==j and bi<ai: continue
                            m=max(da,db)
                            add(pool,best,n,AND(a,b),m);add(pool,best,n,OR(a,b),m)
        for c,d in G[n]: add(U,bU,n,c,d)
    return bG
EXP={1:406,2:10711,3:29127,4:43331,5:51382,6:54859}
for k in range(1,7):
    bG=enum_depth(12,k)
    A,B=Fk(k),Fk(k+1)
    assert all(game(A,c)==game(B,c) for c in bG), k
    assert len(bG)==EXP[k], (k,len(bG))
    print('engine: k=%d, %d guarded classes of depth <= k, size <= 12: none separates F_k/F_k+1'%(k,len(bG)))
for k in range(1,5):
    bG=enum_depth(10,k+1)
    n=sum(game(Fk(k),c)!=game(Fk(k+1),c) for c in bG)
    assert n>0
    Sk=box(OR(neg(Q),bxk(k,BOT)))
    assert bG.get(Sk)==k+1 and game(Fk(k),Sk)!=game(Fk(k+1),Sk)
    print('engine control: depth k+1 (size<=10) has %d separator classes for k=%d, incl. S_k'%(n,k))

# independent literal evaluator: random guarded formulas of depth <= k, exact horizon 2(b(O)+b(F)) (K40)
import random
random.seed(46)
def gen(depth,sz,guarded):
    if sz<=1 or random.random()<0.15:
        if guarded or depth<0: return 'F'
        return random.choice(['F','p','q'])
    r=random.random()
    if depth>0 and r<0.4: return ('[]',gen(depth-1,sz-1,False))
    if r<0.55: return ('~',gen(depth,sz-1,guarded))
    s1=random.randint(1,max(1,sz-2))
    return (random.choice('&|'),gen(depth,s1,guarded),gen(depth,max(1,sz-1-s1),guarded))
def md(f): return 0 if isinstance(f,str) else (1+md(f[1]) if f[0]=='[]' else max(md(x) for x in f[1:]))
def nbox(f): return 0 if isinstance(f,str) else (f[0]=='[]')+sum(nbox(x) for x in f[1:])
def ev(f,h,pp,qq,memo):
    key=(id(f),h)
    if key in memo: return memo[key]
    if f=='F': r=0
    elif f=='p': r=pp[h]
    elif f=='q': r=qq[h]
    elif f[0]=='~': r=1-ev(f[1],h,pp,qq,memo)
    elif f[0]=='&': r=ev(f[1],h,pp,qq,memo)&ev(f[2],h,pp,qq,memo)
    elif f[0]=='|': r=ev(f[1],h,pp,qq,memo)|ev(f[2],h,pp,qq,memo)
    else: r=int(all(ev(f[1],g,pp,qq,memo) for g in range(h)))
    memo[key]=r;return r
def vsF(O,j):
    L=2*(nbox(O)+j);o=[];f=[]
    for h in range(L+1):
        f.append(int(all(o[g] for g in range(h-j+1)) if h>=j else 1))
        o.append(ev(O,h,f+[None],[int(g<j) for g in range(h+1)],{}))
    return o[L],f[L]
cnt=0;ctl=0
for k in range(1,9):
    for _ in range(400):
        O=gen(k,random.randint(3,24),True)
        assert md(O)<=k
        assert vsF(O,k)==vsF(O,k+1),(k,O)
        cnt+=1
    for _ in range(400):
        O=gen(k+1,random.randint(3,24),True)
        if vsF(O,k)!=vsF(O,k+1): ctl+=1
assert ctl>0
for k in range(1,9):
    S='F'
    for _ in range(k): S=('[]',S)
    S=('[]',('|',('~','q'),S))
    T='F'
    for _ in range(k): T=('[]',T)
    T=('~',('[]',('|',('~','p'),T)))
    assert md(S)==k+1 and md(T)==k+1
    assert vsF(S,k)!=vsF(S,k+1) and vsF(T,k)!=vsF(T,k+1)
print('literal: %d random depth<=k opponents (k=1..8) same outcome vs F_k, F_k+1; %d depth-(k+1) random separators; S_k, T_k (depth k+1) separate'%(cnt,ctl))

import subprocess, shutil, os, hashlib
assert hashlib.sha256(LEAN.encode()).hexdigest() == LEANSHA
binary = next((p for p in (shutil.which('lean'), '/opt/elan/bin/lean', os.path.expanduser('~/.elan/bin/lean')) if p and os.path.exists(p)), None)
assert binary, 'lean missing'
def run(src): return subprocess.run([binary, '--stdin'], input=src, text=True, capture_output=True, timeout=100)
r = run(LEAN)
assert r.returncode == 0, (r.stdout + r.stderr)[-3000:]
assert 'sorryAx' not in r.stdout
for t in ('same_outcome','separator_bound','sk_depth'):
    assert "'"+t+"' depends on axioms" in r.stdout, t
MUTS = [('theorem same_outcome (O : Fm) (k : Nat) (hg : Guarded O) (hd : md O ≤ k)', 'theorem same_outcome (O : Fm) (k : Nat) (hg : Guarded O) (hd : md O ≤ k + 1)'),
        ('    exact ⟨min a\' d, by omega', '    exact ⟨min a\' (d+1), by omega'),
        ('    k + 1 ≤ md O ∧ k + 2 ≤ size O := by', '    k + 1 ≤ md O ∧ k + 3 ≤ size O := by'),
        ('theorem sk_depth (k : Nat) : md (box (dj (neg qa) (boxes k bot))) = k + 1', 'theorem sk_depth (k : Nat) : md (box (dj (neg qa) (boxes k bot))) = k'),
        ('    refine ⟨g0 + g1 + 3 * k + 2, fun h hh', '    refine ⟨g0 + g1 + k, fun h hh')]
from concurrent.futures import ThreadPoolExecutor
for a, b in MUTS: assert LEAN.count(a) == 1, a
with ThreadPoolExecutor(3) as ex:
    res=list(ex.map(lambda ab: run(LEAN.replace(ab[0], ab[1])).returncode, MUTS))
assert all(x != 0 for x in res), res
print('Lean: same_outcome, separator_bound, sk_depth; no sorryAx; %d mutations rejected; total %.1fs' % (len(MUTS), time.time()-t0))
print('PASS')
