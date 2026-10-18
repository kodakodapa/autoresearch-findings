"""C046 r1: Lean proof, for ALL m>=1, j>=1, of the laws of the prudent gate family
G_{m,j}(X) = box(box^m p & (q | box(box^j F | ~q)))   (p = X coops G, q = X coops DefectBot),
AST size m+j+10; G_{1,1} = [](([]p)&(q|[]([]F|~q))) is a size-12 agent in K17's U list.
Semantics: closed GL fixed points are letter-free, hence decided by height on the chain
(Boolos, Logic of Provability ch. 7): box phi at h iff phi at all g<h. Each theorem holds for
ANY solution of the height equations.
  gq: vs a DB trace (h<=c) the q-clause holds at g iff g<=c or c<j
  g_unexploitable: G coop at h => opponent coop at every f with f+m<h   (any opponent trace)
  g_db: DB trace is h<=m;  g_cb: cooperates with CooperateBot everywhere
  g_conbot: defects from m+1 against ConBot = ~box F (which cooperates at every h>=1)
  g_fk: k<=j -> mutual coop everywhere; j<k -> G defects h>=k+1, F_k h>=2k+1
  g_pj (j>=1): m<i -> mutual coop everywhere; i<=m -> P_i defects h>=i+1, G h>=i+m+2
  g_gg: any G_{m,j}, G_{m',j'} with j<=m, j'<=m' (incl. self-play) both defect h>=2(m+m')+3
  v_conbot: every V_{n,r} (K14) with n>=1 cooperates with ConBot everywhere -> no G equals any V
  g_params: thresholds (max F-index j, min P-index m+1) determine (m,j)
This script: (1) runs embedded Lean (`lean --stdin`), asserts success, 6 axiom reports, no sorryAx;
(2) four false variants rejected; (3) literal height tables (heights 0..69) for m<=8, 0<=j<=9,
k,i<=11, G-vs-G m,m'<=5, agree; (4) an independent string-based solver (formula parser, no
shared code) reproduces self/FB/CB/DB/ConBot outcomes for m,j<=3 and G_{2,1} vs V_{2,1}=W_2 split on ConBot.
"""
import subprocess, shutil, os
LEAN_SRC = r"""/- Height semantics of closed GL fixed points on the chain 0<1<2<...:
   a world of height h sees exactly heights g<h, so box phi holds at h iff phi holds at all g<h.
   Prudent gate G_{m,j}(X) = box( box^m p  and  (q or box(box^j False or not q)) ),
   p = "X cooperates with G", q = "X cooperates with DefectBot". G_{1,1} has size 12.
   This file: all m >= 1, j >= 1: safety, DB, CB, ConBot (= not box False), F_k, P_i, G vs G,
   and V_{n,r} vs ConBot. -/

def bx (φ : Nat → Prop) : Nat → Prop := fun h => ∀ g, g < h → φ g
def bxn : Nat → (Nat → Prop) → (Nat → Prop)
  | 0, φ => φ
  | n+1, φ => bx (bxn n φ)

theorem bxn_succ_iff (n : Nat) (φ : Nat → Prop) (h : Nat) :
    bxn (n+1) φ h ↔ ∀ g, g + (n+1) ≤ h → φ g := by
  induction n generalizing h with
  | zero =>
    simp only [bxn, bx]
    exact ⟨fun H g hg => H g (by omega), fun H g hg => H g (by omega)⟩
  | succ n ih =>
    show bx (bxn (n+1) φ) h ↔ _
    simp only [bx]
    constructor
    · intro H g hg
      exact (ih (h-1)).1 (H (h-1) (by omega)) g (by omega)
    · intro H g' hg'
      exact (ih g').2 (fun g hg => H g (by omega))

theorem bxn_iff (n : Nat) (hn : 1 ≤ n) (φ : Nat → Prop) (h : Nat) :
    bxn n φ h ↔ ∀ g, g + n ≤ h → φ g := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact bxn_succ_iff m φ h

def botn (n : Nat) : Nat → Prop := bxn n (fun _ => False)

theorem botn_iff (n h : Nat) : botn n h ↔ h < n := by
  cases n with
  | zero => simp [botn, bxn]
  | succ m =>
    unfold botn; rw [bxn_succ_iff]
    constructor
    · intro H; apply Classical.byContradiction; intro hn
      exact H 0 (by omega)
    · intro hlt g hg; omega


theorem strong (P : Nat → Prop) (step : ∀ h, (∀ g, g < h → P g) → P h) : ∀ h, P h := by
  have key : ∀ N h, h < N → P h := by
    intro N
    induction N with
    | zero => intro h hh; omega
    | succ N ih => intro h hh; exact step h (fun g hg => ih g (by omega))
  exact fun h => key (h+1) h (by omega)

/-! Two-parameter gates V_{n,r}(X) = box( box^n F  or  (p and (q or not box^r q)) ), r >= 1 (r2's K13).
    V_{n,1} = W_n. vgate n r p q is the formula under the outer box. -/
def vgate (n r : Nat) (p q : Nat → Prop) : Nat → Prop :=
  fun g => botn n g ∨ (p g ∧ (q g ∨ ¬ bxn r q g))


def ggate (m j : Nat) (p q : Nat → Prop) : Nat → Prop :=
  fun g => bxn m p g ∧ (q g ∨ bx (fun f => botn j f ∨ ¬ q f) g)

/-- Against a DefectBot trace true exactly at h <= c, the q-clause holds at g iff g <= c or c < j. -/
theorem gq (j c : Nat) (d : Nat → Prop) (hd : ∀ h, d h ↔ h ≤ c) (g : Nat) :
    (d g ∨ bx (fun f => botn j f ∨ ¬ d f) g) ↔ (g ≤ c ∨ c < j) := by
  rw [hd g]
  constructor
  · rintro (H | H)
    · exact Or.inl H
    · apply Classical.byContradiction; intro hn
      rcases H c (by omega) with hb | hb
      · rw [botn_iff] at hb; omega
      · exact hb ((hd c).2 (Nat.le_refl c))
  · rintro (H | H)
    · exact Or.inl H
    · refine Or.inr (fun f _ => ?_)
      by_cases hf : f < j
      · exact Or.inl ((botn_iff j f).2 hf)
      · exact Or.inr (fun df => by have := (hd f).1 df; omega)

theorem gq_hold (j c : Nat) (d : Nat → Prop) (hd : ∀ h, d h ↔ h ≤ c) (hc : c < j) (g : Nat) :
    d g ∨ bx (fun f => botn j f ∨ ¬ d f) g :=
  (gq j c d hd g).2 (Or.inr hc)

/-- If j <= c the q-clause fails at g = c+1, so G defects at every h >= c+2, whatever p is. -/
theorem g_fail (m j c : Nat) (p d : Nat → Prop) (hd : ∀ h, d h ↔ h ≤ c) (hjc : j ≤ c) :
    ∀ h, c + 2 ≤ h → ¬ bx (ggate m j p d) h := by
  intro h hh H
  have := (gq j c d hd (c+1)).1 (H (c+1) (by omega)).2
  omega

/-- Universal safety: whenever G acts C at h, the opponent acts C at every f with f + m < h. -/
theorem g_unexploitable (m j : Nat) (hm : 1 ≤ m) (x y d : Nat → Prop)
    (hx : ∀ h, x h ↔ bx (ggate m j y d) h) : ∀ h, x h → ∀ f, f + m < h → y f := by
  intro h xh f hf
  have := (((hx h).1 xh) (h-1) (by omega)).1
  rw [bxn_iff m hm] at this
  exact this f (by omega)

/-- G's DefectBot trace: true exactly at h <= m. -/
theorem g_db (m j : Nat) (hm : 1 ≤ m) (x : Nat → Prop)
    (hx : ∀ h, x h ↔ bx (ggate m j (fun _ => False) (fun _ => False)) h) : ∀ h, x h ↔ h ≤ m := by
  intro h; rw [hx h]
  constructor
  · intro H; apply Classical.byContradiction; intro hn
    have := (H m (by omega)).1
    rw [bxn_iff m hm] at this
    exact this 0 (by omega)
  · intro hh g hg
    refine ⟨?_, Or.inr (fun f _ => Or.inr (fun h => h))⟩
    rw [bxn_iff m hm]; intro f hf; omega

/-- G vs CooperateBot: cooperation at every height. -/
theorem g_cb (m j : Nat) (x : Nat → Prop)
    (hx : ∀ h, x h ↔ bx (ggate m j (fun _ => True) (fun _ => True)) h) : ∀ h, x h := by
  have tb : ∀ n g, bxn n (fun _ => True) g := by
    intro n; induction n with
    | zero => intro g; trivial
    | succ n ih => intro g f _; exact ih f
  intro h; rw [hx h]; intro g _; exact ⟨tb m g, Or.inl trivial⟩

/-- G vs ConBot = not box False (acts C exactly at heights >= 1, also against DefectBot):
    G defects at every h >= m+1 although ConBot cooperates at every h >= 1. -/
theorem g_conbot (m j : Nat) (hm : 1 ≤ m) (x : Nat → Prop)
    (hx : ∀ h, x h ↔ bx (ggate m j (fun h => 1 ≤ h) (fun h => 1 ≤ h)) h) :
    ∀ h, m + 1 ≤ h → ¬ x h := by
  intro h hh xh
  have := (((hx h).1 xh) m (by omega)).1
  rw [bxn_iff m hm] at this
  exact absurd (this 0 (by omega)) (by omega)

/-- G_{m,j} vs F_k (k >= 1; F_k's DB trace e is botn k): k <= j gives mutual cooperation at
    every height; j < k: G defects from k+1, F_k from 2k+1. -/
theorem g_fk (m j k : Nat) (hm : 1 ≤ m) (hk : 1 ≤ k) (x y e : Nat → Prop) (he : ∀ h, e h ↔ botn k h)
    (hx : ∀ h, x h ↔ bx (ggate m j y e) h) (hy : ∀ h, y h ↔ bxn k x h) :
    (k ≤ j → ∀ h, x h ∧ y h) ∧
    (j < k → (∀ h, k + 1 ≤ h → ¬ x h) ∧ (∀ h, 2 * k + 1 ≤ h → ¬ y h)) := by
  have he' : ∀ h, e h ↔ h ≤ k - 1 := fun h => by rw [he, botn_iff]; omega
  constructor
  · intro hkj
    apply strong
    intro h ih
    refine ⟨(hx h).2 (fun g hg => ⟨?_, gq_hold j (k-1) e he' (by omega) g⟩), (hy h).2 ?_⟩
    · rw [bxn_iff m hm]; intro f hf; exact (ih f (by omega)).2
    · rw [bxn_iff k hk]; intro g hg; exact (ih g (by omega)).1
  · intro hjk
    have nx : ∀ h, k + 1 ≤ h → ¬ x h := fun h hh xh =>
      g_fail m j (k-1) y e he' (by omega) h (by omega) ((hx h).1 xh)
    refine ⟨nx, fun h hh yh => ?_⟩
    rw [hy h, bxn_iff k hk] at yh
    exact nx (k+1) (by omega) (yh (k+1) (by omega))

/-- P_i's DefectBot trace is true exactly at height 0. -/
theorem pj_db (j : Nat) (d : Nat → Prop)
    (hd : ∀ h, d h ↔ (bx (fun _ => False) h ∧ bx (fun g => botn j g ∨ ¬ False) h)) :
    ∀ h, d h ↔ h ≤ 0 := by
  intro h
  rw [hd h]
  constructor
  · intro ⟨H, _⟩
    apply Classical.byContradiction; intro hh
    exact H 0 (by omega)
  · intro hh
    exact ⟨fun g hg => by omega, fun g hg => by omega⟩

/-- G_{m,j} (j >= 1) vs P_i = box p and box(box^i F or not q). d: P_i's DB trace (h <= 0);
    w: G's DB trace (g_db: h <= m). m < i: mutual cooperation at every height.
    i <= m: P_i defects from i+1, G from i+m+2. -/
theorem g_pj (m j i : Nat) (hm : 1 ≤ m) (hj : 1 ≤ j) (x y d w : Nat → Prop)
    (hd : ∀ h, d h ↔ h ≤ 0) (hw : ∀ h, w h ↔ h ≤ m)
    (hx : ∀ h, x h ↔ bx (ggate m j y d) h)
    (hy : ∀ h, y h ↔ (bx x h ∧ bx (fun g => botn i g ∨ ¬ w g) h)) :
    (m < i → ∀ h, x h ∧ y h) ∧
    (i ≤ m → (∀ h, i + 1 ≤ h → ¬ y h) ∧ (∀ h, i + m + 2 ≤ h → ¬ x h)) := by
  constructor
  · intro hmi
    apply strong
    intro h ih
    refine ⟨(hx h).2 (fun g hg => ⟨?_, gq_hold j 0 d hd (by omega) g⟩),
            (hy h).2 ⟨fun g hg => (ih g hg).1, ?_⟩⟩
    · rw [bxn_iff m hm]; intro f hf; exact (ih f (by omega)).2
    · intro g hg
      by_cases hgi : g < i
      · exact Or.inl ((botn_iff i g).2 hgi)
      · exact Or.inr (fun hwg => by rw [hw] at hwg; omega)
  · intro him
    have ny : ∀ h, i + 1 ≤ h → ¬ y h := by
      intro h hh yh
      rcases ((hy h).1 yh).2 i (by omega) with hb | hb
      · rw [botn_iff] at hb; omega
      · exact hb ((hw i).2 him)
    refine ⟨ny, fun h hh xh => ?_⟩
    have := (((hx h).1 xh) (i+m+1) (by omega)).1
    rw [bxn_iff m hm] at this
    exact ny (i+1) (by omega) (this (i+1) (by omega))

/-- G_{m,j} vs G_{m',j'} (includes self-play) with j <= m (the defining condition of the
    family) and j' <= m': both defect at every h >= 2(m+m')+3. -/
theorem g_gg (m j m' j' : Nat) (hm : 1 ≤ m) (hm' : 1 ≤ m') (hjm : j ≤ m) (hjm' : j' ≤ m')
    (x y dm dm' : Nat → Prop) (hdm : ∀ h, dm h ↔ h ≤ m) (hdm' : ∀ h, dm' h ↔ h ≤ m')
    (hx : ∀ h, x h ↔ bx (ggate m j y dm') h) (hy : ∀ h, y h ↔ bx (ggate m' j' x dm) h) :
    ∀ h, 2 * (m + m') + 3 ≤ h → ¬ x h ∧ ¬ y h := by
  intro h hh
  by_cases hc : j ≤ m'
  · have nx : ∀ h, m' + 2 ≤ h → ¬ x h := fun h hh' xh =>
      g_fail m j m' y dm' hdm' hc h hh' ((hx h).1 xh)
    refine ⟨nx h (by omega), fun yh => ?_⟩
    have := (((hy h).1 yh) (h-1) (by omega)).1
    rw [bxn_iff m' hm'] at this
    exact nx (m'+2) (by omega) (this (m'+2) (by omega))
  · have hc' : j' ≤ m := by omega
    have ny : ∀ h, m + 2 ≤ h → ¬ y h := fun h hh' yh =>
      g_fail m' j' m x dm hdm hc' h hh' ((hy h).1 yh)
    refine ⟨fun xh => ?_, ny h (by omega)⟩
    have := (((hx h).1 xh) (h-1) (by omega)).1
    rw [bxn_iff m hm] at this
    exact ny (m+2) (by omega) (this (m+2) (by omega))

/-! Two-parameter gates V_{n,r} (K14) for comparison: they cooperate with ConBot. -/

theorem v_conbot (n r : Nat) (hn : 1 ≤ n) (x : Nat → Prop)
    (hx : ∀ h, x h ↔ bx (vgate n r (fun h => 1 ≤ h) (fun h => 1 ≤ h)) h) : ∀ h, x h := by
  intro h; rw [hx h]; intro g _
  by_cases hg : g = 0
  · exact Or.inl ((botn_iff n g).2 (by omega))
  · exact Or.inr ⟨by omega, Or.inl (by omega)⟩

/-- Parameters are recovered from F/P thresholds: max F-index cooperated with is j, min P-index is m+1. -/
theorem g_params (m j m' j' : Nat)
    (hF : ∀ k, (k ≤ j ↔ k ≤ j')) (hP : ∀ i, (m < i ↔ m' < i)) : m = m' ∧ j = j' := by
  have a := (hF j).1 (Nat.le_refl j); have b := (hF j').2 (Nat.le_refl j')
  have c := (hP (m+1)).1 (by omega); have d := (hP (m'+1)).2 (by omega)
  omega

#print axioms g_unexploitable
#print axioms g_fk
#print axioms g_pj
#print axioms g_gg
#print axioms g_conbot
#print axioms v_conbot
"""

def lean():
    for c in (shutil.which('lean'), '/opt/elan/bin/lean', os.path.expanduser('~/.elan/bin/lean')):
        if c and os.path.exists(c): return c
    raise AssertionError('lean binary not found')
def run(s):
    r = subprocess.run([lean(), '--stdin'], input=s, capture_output=True, text=True, timeout=100)
    return r.returncode, r.stdout + r.stderr
code, out = run(LEAN_SRC)
assert code == 0, out
assert 'error' not in out.lower() and 'sorryAx' not in out and out.count('depends on axioms') == 6, out
bads = [('(k ≤ j → ∀ h, x h ∧ y h)', '(k ≤ j + 1 → ∀ h, x h ∧ y h)'),
        ('(m < i → ∀ h, x h ∧ y h)', '(m ≤ i → ∀ h, x h ∧ y h)'),
        ('↔ (g ≤ c ∨ c < j)', '↔ (g ≤ c ∨ c ≤ j)'),
        ('∀ h, m + 1 ≤ h → ¬ x h := by\n  intro h hh xh', '∀ h, m ≤ h → ¬ x h := by\n  intro h hh xh')]
for a, b in bads:
    assert LEAN_SRC.count(a) == 1, a
    c2, o2 = run(LEAN_SRC.replace(a, b, 1))
    assert c2 != 0 and 'error' in o2, ('negative control accepted', b)
H = 70
def bxn(r, q, g): return all(q[i] for i in range(g - r + 1))   # box^r q at g (r>=1)
def gg(m, j, p, q, g): return bxn(m, p, g) and (q[g] or all(f < j or not q[f] for f in range(g)))
def G(m, j, p, q, h): return all(gg(m, j, p, q, g) for g in range(h))
def play(fx, fy):
    xs, ys = [], []
    for h in range(H):
        xs.append(fx(ys, h)); ys.append(fy(xs[:h], h))
    return xs, ys
pad = lambda t: t + [None] * (H - len(t))
dG = lambda m: [h <= m for h in range(H)]
dP = [h == 0 for h in range(H)]
T = [True] * H; CON = [h >= 1 for h in range(H)]
for m in range(1, 9):
    for j in range(0, 10):
        assert [G(m, j, [False]*H, [False]*H, h) for h in range(H)] == dG(m)    # g_db
        assert all(G(m, j, T, T, h) for h in range(H))                           # g_cb
        assert [G(m, j, CON, CON, h) for h in range(H)] == dG(m)                 # g_conbot
        for k in range(1, 12):
            e = [h < k for h in range(H)]
            xs, ys = play(lambda ys, h: G(m, j, pad(ys), e, h), lambda xs, h: bxn(k, xs, h))
            if k <= j: assert all(xs) and all(ys), (m, j, k)
            else: assert not any(xs[k+1:]) and not any(ys[2*k+1:]), (m, j, k)
        if j >= 1:
            for i in range(12):
                xs, ys = play(lambda ys, h: G(m, j, pad(ys), dP, h),
                              lambda xs, h: all(xs[:h]) and all(g < i or not dG(m)[g] for g in range(h)))
                if m < i: assert all(xs) and all(ys), (m, j, i)
                else: assert not any(ys[i+1:]) and not any(xs[i+m+2:]), (m, j, i)
        xs, ys = play(lambda ys, h: G(m, j, pad(ys), dG(m), h), lambda xs, h: G(m, j, pad(xs), dG(m), h))
        assert xs == ys and (xs[-1] == (j > m)), (m, j)    # self-play: defect iff j<=m
for m in range(1, 6):
    for j in range(1, m+1):
        for m2 in range(1, 6):
            for j2 in range(1, m2+1):
                xs, ys = play(lambda ys, h: G(m, j, pad(ys), dG(m2), h), lambda xs, h: G(m2, j2, pad(xs), dG(m), h))
                assert not any(xs[2*(m+m2)+3:]) and not any(ys[2*(m+m2)+3:])
# (4) independent solver from formula strings
def parse(s):
    def p(i):
        c = s[i]
        if c in 'Fpq': return (c,), i+1
        if c == '~': a, k = p(i+1); return ('~', a), k
        if s.startswith('[]', i): a, k = p(i+2); return ('[]', a), k
        assert c == '('
        a, k = p(i+1); op = s[k]; b, l = p(k+1); assert s[l] == ')'
        return (op, a, b), l+1
    t, k = p(0); assert k == len(s); return t
def ev(t, h, P, Q, memo):
    key = (id(t), h)
    if key not in memo:
        k = t[0]
        if k == 'F': r = False
        elif k == 'p': r = P[h]
        elif k == 'q': r = Q[h]
        elif k == '~': r = not ev(t[1], h, P, Q, memo)
        elif k == '&': r = ev(t[1], h, P, Q, memo) and ev(t[2], h, P, Q, memo)
        elif k == '|': r = ev(t[1], h, P, Q, memo) or ev(t[2], h, P, Q, memo)
        else: r = all(ev(t[1], g, P, Q, memo) for g in range(h))
        memo[key] = r
    return memo[key]
def game(sa, sb, HH=40):
    A, B = parse(sa), parse(sb); x, y, za, zb = [], [], [], []; Z = [False]*HH; ms = [{}, {}, {}, {}]
    for h in range(HH):
        za.append(ev(A, h, Z, Z, ms[2])); zb.append(ev(B, h, Z, Z, ms[3]))
        xa = ev(A, h, y + [None], zb, ms[0]); yb = ev(B, h, x + [None], za, ms[1])
        x.append(xa); y.append(yb)
    return x[-1], y[-1]
bx = lambda s, n: '[]' * n + s
def Gstr(m, j): return '[](' + bx('p', m) + '&(q|[](' + bx('F', j) + '|~q)))'
def Vstr(n, r): return '[](' + bx('F', n) + '|(p&(q|~' + bx('q', r) + ')))'
def size(s): return len(s.replace('[]', 'B').replace('(', '').replace(')', ''))
assert Gstr(1, 1) == '[]([]p&(q|[]([]F|~q)))' and size(Gstr(1, 1)) == 12
assert all(size(Gstr(m, j)) == m + j + 10 for m in range(1, 6) for j in range(1, 6))
FB, CB, DB, CON = '[]p', '~F', 'F', '~[]F'
for m in range(1, 4):
    for j in range(1, m+1):
        g = Gstr(m, j)
        assert game(g, g) == (False, False) and game(g, FB) == (True, True) and game(g, CB) == (True, True)
        assert game(g, DB) == (False, False) and game(g, CON) == (False, True), (m, j)
assert game(Vstr(2, 1), CON) == (True, True)    # W_2 cooperates with ConBot, G_{2,1} does not
print('PASS: Lean G_{m,j} laws for all m,j; 4 negative controls rejected; tables and string solver agree')
