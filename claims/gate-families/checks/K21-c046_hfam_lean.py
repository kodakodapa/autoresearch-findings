"""C046 r1: Lean proof, for ALL m>=0 (H laws) / m>=1 (G comparison) and j>=1, of the laws of r2's
outer-box prudent family (K20)  H_{m,j}(X) = box^{m+1}(p & (q | box(box^j F | ~q))), AST size m+j+10,
and of a uniform separator S_j(X) = box^{j+1}(p | ~box^{j+1} q), size 2j+6, between H_{m,j} and the
prudent gate G_{m,j} = box(box^m p & (q | box(box^j F | ~q))) of K18.
Semantics: closed GL fixed points are letter-free, hence decided by height on the chain
(Boolos, Logic of Provability ch. 7): box phi at h iff phi at all g<h. Each theorem holds for ANY
solution of the height equations.
  h_unexploitable: H coop at h => opponent coop at all f with f+m+1<=h (any opponent trace)
  h_db: DB trace h<=m;  h_cb: coop with CooperateBot everywhere;  h_conbot: defects from m+1 vs ~box F
  h_fk: k<=j -> mutual coop everywhere; j<k -> H defects h>=k+m+1, F_k h>=2k+m+1
  h_pj (j>=1): m<i -> mutual coop everywhere; i<=m -> P_i defects h>=i+1, H h>=i+m+2
  h_hh: H_{m,j} vs H_{m',j'} with j<=m, j'<=m' (incl. self-play): both defect h>=2(m+m')+3
  s_db: S_j's DB trace is h<=j
  h_sep: H_{m,j} vs S_j: S_j coop everywhere, H coop exactly at h<=m+j+1  (tail D/C)
  g_sep (m>=1): G_{m,j} vs S_j: G defects h>=j+2, S_j h>=2j+3          (tail D/D)
  h_params: (max F-index, min P-index) = (j, m+1) determine (m,j)
This script: (1) runs embedded Lean (`lean --stdin`), 7 axiom reports, no sorryAx; (2) four false
variants rejected; (3) literal height tables (heights 0..79) m<=8, j<=8, k,i<=11, H-vs-H m,m'<=5,
H/G vs S_j; (4) independent string-formula solver for H,G,S_j with m,j<=3 (self, FB, CB, DB, ConBot,
F_k, P_i, S_j).
"""
import subprocess, shutil, os
LEAN_SRC = r"""def bx (φ : Nat → Prop) : Nat → Prop := fun h => ∀ g, g < h → φ g
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


/-! Outer-box prudent family (r2's K20): H_{m,j}(X) = box^{m+1}( p and (q or box(box^j F or not q)) ). -/
def hgate (j : Nat) (p q : Nat → Prop) : Nat → Prop :=
  fun g => p g ∧ (q g ∨ bx (fun f => botn j f ∨ ¬ q f) g)

/-- If j <= c the q-clause fails at g = c+1, so H defects at every h >= c+m+2, whatever p is. -/
theorem h_fail (m j c : Nat) (p d : Nat → Prop) (hd : ∀ h, d h ↔ h ≤ c) (hjc : j ≤ c) :
    ∀ h, c + m + 2 ≤ h → ¬ bxn (m+1) (hgate j p d) h := by
  intro h hh H
  rw [bxn_succ_iff] at H
  have := (gq j c d hd (c+1)).1 (H (c+1) (by omega)).2
  omega

/-- Universal safety: whenever H acts C at h, the opponent acts C at every f with f + m + 1 <= h. -/
theorem h_unexploitable (m j : Nat) (x y d : Nat → Prop)
    (hx : ∀ h, x h ↔ bxn (m+1) (hgate j y d) h) : ∀ h, x h → ∀ f, f + m + 1 ≤ h → y f := by
  intro h xh f hf
  have := (hx h).1 xh
  rw [bxn_succ_iff] at this
  exact (this f (by omega)).1

/-- H's DefectBot trace: true exactly at h <= m. -/
theorem h_db (m j : Nat) (x : Nat → Prop)
    (hx : ∀ h, x h ↔ bxn (m+1) (hgate j (fun _ => False) (fun _ => False)) h) : ∀ h, x h ↔ h ≤ m := by
  intro h; rw [hx h, bxn_succ_iff]
  constructor
  · intro H; apply Classical.byContradiction; intro hn
    exact (H 0 (by omega)).1
  · intro hh g hg; omega

theorem h_cb (m j : Nat) (x : Nat → Prop)
    (hx : ∀ h, x h ↔ bxn (m+1) (hgate j (fun _ => True) (fun _ => True)) h) : ∀ h, x h := by
  intro h; rw [hx h, bxn_succ_iff]; intro g _; exact ⟨trivial, Or.inl trivial⟩

/-- H vs ConBot (C exactly at heights >= 1): H defects at every h >= m+1. -/
theorem h_conbot (m j : Nat) (x : Nat → Prop)
    (hx : ∀ h, x h ↔ bxn (m+1) (hgate j (fun h => 1 ≤ h) (fun h => 1 ≤ h)) h) :
    ∀ h, m + 1 ≤ h → ¬ x h := by
  intro h hh xh
  rw [hx h, bxn_succ_iff] at xh
  exact absurd (xh 0 (by omega)).1 (by omega)

/-- H_{m,j} vs F_k: k <= j gives mutual cooperation everywhere; j < k: H defects from k+m+1,
    F_k from 2k+m+1. -/
theorem h_fk (m j k : Nat) (hk : 1 ≤ k) (x y e : Nat → Prop) (he : ∀ h, e h ↔ botn k h)
    (hx : ∀ h, x h ↔ bxn (m+1) (hgate j y e) h) (hy : ∀ h, y h ↔ bxn k x h) :
    (k ≤ j → ∀ h, x h ∧ y h) ∧
    (j < k → (∀ h, k + m + 1 ≤ h → ¬ x h) ∧ (∀ h, 2 * k + m + 1 ≤ h → ¬ y h)) := by
  have he' : ∀ h, e h ↔ h ≤ k - 1 := fun h => by rw [he, botn_iff]; omega
  constructor
  · intro hkj
    apply strong
    intro h ih
    refine ⟨(hx h).2 ?_, (hy h).2 ?_⟩
    · rw [bxn_succ_iff]; intro g hg
      exact ⟨(ih g (by omega)).2, gq_hold j (k-1) e he' (by omega) g⟩
    · rw [bxn_iff k hk]; intro g hg; exact (ih g (by omega)).1
  · intro hjk
    have nx : ∀ h, k + m + 1 ≤ h → ¬ x h := fun h hh xh =>
      h_fail m j (k-1) y e he' (by omega) h (by omega) ((hx h).1 xh)
    refine ⟨nx, fun h hh yh => ?_⟩
    rw [hy h, bxn_iff k hk] at yh
    exact nx (k+m+1) (by omega) (yh (k+m+1) (by omega))

/-- H_{m,j} (j >= 1) vs P_i. d: P_i's DB trace (h <= 0); w: H's DB trace (h <= m).
    m < i: mutual cooperation everywhere; i <= m: P_i defects from i+1, H from i+m+2. -/
theorem h_pj (m j i : Nat) (hj : 1 ≤ j) (x y d w : Nat → Prop)
    (hd : ∀ h, d h ↔ h ≤ 0) (hw : ∀ h, w h ↔ h ≤ m)
    (hx : ∀ h, x h ↔ bxn (m+1) (hgate j y d) h)
    (hy : ∀ h, y h ↔ (bx x h ∧ bx (fun g => botn i g ∨ ¬ w g) h)) :
    (m < i → ∀ h, x h ∧ y h) ∧
    (i ≤ m → (∀ h, i + 1 ≤ h → ¬ y h) ∧ (∀ h, i + m + 2 ≤ h → ¬ x h)) := by
  constructor
  · intro hmi
    apply strong
    intro h ih
    refine ⟨(hx h).2 ?_, (hy h).2 ⟨fun g hg => (ih g hg).1, ?_⟩⟩
    · rw [bxn_succ_iff]; intro g hg
      exact ⟨(ih g (by omega)).2, gq_hold j 0 d hd (by omega) g⟩
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
    rw [hx h, bxn_succ_iff] at xh
    exact ny (i+1) (by omega) (xh (i+1) (by omega)).1

/-- H_{m,j} vs H_{m',j'} (incl. self-play), j <= m, j' <= m': both defect at every h >= 2(m+m')+3. -/
theorem h_hh (m j m' j' : Nat) (hjm : j ≤ m) (hjm' : j' ≤ m')
    (x y dm dm' : Nat → Prop) (hdm : ∀ h, dm h ↔ h ≤ m) (hdm' : ∀ h, dm' h ↔ h ≤ m')
    (hx : ∀ h, x h ↔ bxn (m+1) (hgate j y dm') h) (hy : ∀ h, y h ↔ bxn (m'+1) (hgate j' x dm) h) :
    ∀ h, 2 * (m + m') + 3 ≤ h → ¬ x h ∧ ¬ y h := by
  intro h hh
  by_cases hc : j ≤ m'
  · have nx : ∀ h, m' + m + 2 ≤ h → ¬ x h := fun h hh' xh =>
      h_fail m j m' y dm' hdm' hc h hh' ((hx h).1 xh)
    refine ⟨nx h (by omega), fun yh => ?_⟩
    rw [hy h, bxn_succ_iff] at yh
    exact nx (m'+m+2) (by omega) (yh (m'+m+2) (by omega)).1
  · have hc' : j' ≤ m := by omega
    have ny : ∀ h, m + m' + 2 ≤ h → ¬ y h := fun h hh' yh =>
      h_fail m' j' m x dm hdm hc' h hh' ((hy h).1 yh)
    refine ⟨fun xh => ?_, ny h (by omega)⟩
    rw [hx h, bxn_succ_iff] at xh
    exact ny (m+m'+2) (by omega) (xh (m+m'+2) (by omega)).1

/-! Separator S_j(X) = box^{j+1}( p or not box^{j+1} q ), size 2j+6, independent of m.
    It splits H_{m,j} (D/C) from G_{m,j} (D/D) for every m >= 1. -/
def sgate (j : Nat) (p q : Nat → Prop) : Nat → Prop := fun g => p g ∨ ¬ bxn (j+1) q g

/-- S_j's DefectBot trace: true exactly at h <= j. -/
theorem s_db (j : Nat) (s : Nat → Prop)
    (hs : ∀ h, s h ↔ bxn (j+1) (sgate j (fun _ => False) (fun _ => False)) h) : ∀ h, s h ↔ h ≤ j := by
  intro h; rw [hs h, bxn_succ_iff]
  constructor
  · intro H; apply Classical.byContradiction; intro hn
    rcases H 0 (by omega) with hb | hb
    · exact hb
    · exact hb (by rw [bxn_succ_iff]; intro g hg; omega)
  · intro hh g hg; omega

/-- H_{m,j} vs S_j: H cooperates exactly at h <= m+j+1, S_j cooperates at every height. -/
theorem h_sep (m j : Nat) (x s dS w : Nat → Prop)
    (hdS : ∀ h, dS h ↔ h ≤ j) (hw : ∀ h, w h ↔ h ≤ m)
    (hx : ∀ h, x h ↔ bxn (m+1) (hgate j s dS) h) (hs : ∀ h, s h ↔ bxn (j+1) (sgate j x w) h) :
    ∀ h, s h ∧ (x h ↔ h ≤ m + j + 1) := by
  apply strong
  intro h ih
  have sh : s h := by
    rw [hs h, bxn_succ_iff]; intro g hg
    by_cases hgm : g ≤ m + j + 1
    · exact Or.inl ((ih g (by omega)).2.2 hgm)
    · refine Or.inr (fun hb => ?_)
      rw [bxn_succ_iff] at hb
      have := (hw (m+1)).1 (hb (m+1) (by omega)); omega
  refine ⟨sh, ?_⟩
  rw [hx h, bxn_succ_iff]
  constructor
  · intro H; apply Classical.byContradiction; intro hn
    have := (gq j j dS hdS (j+1)).1 (H (j+1) (by omega)).2
    omega
  · intro hh g hg
    exact ⟨(ih g (by omega)).1, (gq j j dS hdS g).2 (Or.inl (by omega))⟩

/-- G_{m,j} vs S_j: G defects from j+2, S_j from 2j+3: mutual defection. -/
theorem g_sep (m j : Nat) (hm : 1 ≤ m) (x s dS w : Nat → Prop)
    (hdS : ∀ h, dS h ↔ h ≤ j) (hw : ∀ h, w h ↔ h ≤ m)
    (hx : ∀ h, x h ↔ bx (ggate m j s dS) h) (hs : ∀ h, s h ↔ bxn (j+1) (sgate j x w) h) :
    (∀ h, j + 2 ≤ h → ¬ x h) ∧ (∀ h, 2 * j + 3 ≤ h → ¬ s h) := by
  have nx : ∀ h, j + 2 ≤ h → ¬ x h := fun h hh xh =>
    g_fail m j j s dS hdS (Nat.le_refl j) h hh ((hx h).1 xh)
  refine ⟨nx, fun h hh sh => ?_⟩
  rw [hs h, bxn_succ_iff] at sh
  rcases sh (j+2) (by omega) with hb | hb
  · exact nx (j+2) (by omega) hb
  · apply hb; rw [bxn_succ_iff]; intro f hf; exact (hw f).2 (by omega)

/-- Parameters are recovered from F/P thresholds: max F-index j, min P-index m+1. -/
theorem h_params (m j m' j' : Nat)
    (hF : ∀ k, (k ≤ j ↔ k ≤ j')) (hP : ∀ i, (m < i ↔ m' < i)) : m = m' ∧ j = j' := by
  have a := (hF j).1 (Nat.le_refl j); have b := (hF j').2 (Nat.le_refl j')
  have c := (hP (m+1)).1 (by omega); have d := (hP (m'+1)).2 (by omega)
  omega

#print axioms h_unexploitable
#print axioms h_fk
#print axioms h_pj
#print axioms h_hh
#print axioms h_conbot
#print axioms h_sep
#print axioms g_sep
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
assert 'error' not in out.lower() and 'sorryAx' not in out and out.count('depends on axioms') == 7, out
bads = [('(k ≤ j → ∀ h, x h ∧ y h) ∧\n    (j < k', '(k ≤ j + 1 → ∀ h, x h ∧ y h) ∧\n    (j < k'),
        ('(m < i → ∀ h, x h ∧ y h) ∧\n    (i ≤ m → (∀ h, i + 1 ≤ h → ¬ y h) ∧ (∀ h, i + m + 2',
         '(m ≤ i → ∀ h, x h ∧ y h) ∧\n    (i ≤ m → (∀ h, i + 1 ≤ h → ¬ y h) ∧ (∀ h, i + m + 2'),
        ('∀ h, s h ∧ (x h ↔ h ≤ m + j + 1)', '∀ h, s h ∧ (x h ↔ h ≤ m + j + 2)'),
        ('(∀ h, j + 2 ≤ h → ¬ x h) ∧ (∀ h, 2 * j + 3', '(∀ h, j + 1 ≤ h → ¬ x h) ∧ (∀ h, 2 * j + 3')]
for a, b in bads:
    assert LEAN_SRC.count(a) == 1, a
    c2, o2 = run(LEAN_SRC.replace(a, b, 1))
    assert c2 != 0 and 'error' in o2, ('negative control accepted', b)
# (3) literal tables: box^r phi at g = phi at all i <= g-r
H = 80
def bxn(r, q, g): return all(q[i] for i in range(g - r + 1)) if r >= 1 else q[g]
def qc(j, q, g): return q[g] or all(f < j or not q[f] for f in range(g))
def Hh(m, j, p, q, h): return all(p[g] and qc(j, q, g) for g in range(h - m))
def Gh(m, j, p, q, h): return all(bxn(m, p, g) and qc(j, q, g) for g in range(h))
def Sh(j, p, q, h): return all(p[g] or not bxn(j+1, q, g) for g in range(h - j))
def play(fx, fy):
    xs, ys = [], []
    for h in range(H):
        xs.append(fx(ys, h)); ys.append(fy(xs[:h], h))
    return xs, ys
pad = lambda t: t + [None] * (H - len(t))
dle = lambda c: [h <= c for h in range(H)]
T = [True] * H; Z = [False] * H; CON = [h >= 1 for h in range(H)]
for j in range(0, 9):
    assert [Sh(j, Z, Z, h) for h in range(H)] == dle(j)                                     # s_db
for m in range(0, 9):
    for j in range(0, 9):
        assert [Hh(m, j, Z, Z, h) for h in range(H)] == dle(m)                              # h_db
        assert all(Hh(m, j, T, T, h) for h in range(H))                                     # h_cb
        assert [Hh(m, j, CON, CON, h) for h in range(H)] == dle(m)                          # h_conbot
        for k in range(1, 12):
            xs, ys = play(lambda ys, h: Hh(m, j, pad(ys), dle(k-1), h), lambda xs, h: bxn(k, pad(xs), h))
            if k <= j: assert all(xs) and all(ys), (m, j, k)
            else: assert not any(xs[k+m+1:]) and not any(ys[2*k+m+1:]), (m, j, k)
        if j >= 1:
            for i in range(12):
                xs, ys = play(lambda ys, h: Hh(m, j, pad(ys), dle(0), h),
                              lambda xs, h: all(xs[:h]) and all(g < i or not dle(m)[g] for g in range(h)))
                if m < i: assert all(xs) and all(ys), (m, j, i)
                else: assert not any(ys[i+1:]) and not any(xs[i+m+2:]), (m, j, i)
            xs, ys = play(lambda ys, h: Hh(m, j, pad(ys), dle(j), h), lambda xs, h: Sh(j, pad(xs), dle(m), h))
            assert all(ys) and xs == dle(m+j+1), (m, j)                                     # h_sep
            if m >= 1:
                xs, ys = play(lambda ys, h: Gh(m, j, pad(ys), dle(j), h), lambda xs, h: Sh(j, pad(xs), dle(m), h))
                assert not any(xs[j+2:]) and not any(ys[2*j+3:]), (m, j)                    # g_sep
        xs, ys = play(lambda ys, h: Hh(m, j, pad(ys), dle(m), h), lambda xs, h: Hh(m, j, pad(xs), dle(m), h))
        assert xs == ys and (xs[-1] == (j > m)), (m, j)                                     # self-play
for m in range(1, 6):
    for j in range(1, m+1):
        for m2 in range(1, 6):
            for j2 in range(1, m2+1):
                xs, ys = play(lambda ys, h: Hh(m, j, pad(ys), dle(m2), h), lambda xs, h: Hh(m2, j2, pad(xs), dle(m), h))
                assert not any(xs[2*(m+m2)+3:]) and not any(ys[2*(m+m2)+3:])               # h_hh
# (4) independent solver from formula strings (no shared code with (3))
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
def Hstr(m, j): return bx('(p&(q|[](' + bx('F', j) + '|~q)))', m+1)
def Gstr(m, j): return '[](' + bx('p', m) + '&(q|[](' + bx('F', j) + '|~q)))'
def Sstr(j): return bx('(p|~' + bx('q', j+1) + ')', j+1)
def Fstr(k): return bx('p', k)
def Pstr(i): return '([]p&[](' + bx('F', i) + '|~q))'
def size(s): return len(s.replace('[]', 'B').replace('(', '').replace(')', ''))
assert Hstr(1, 1) == '[][](p&(q|[]([]F|~q)))' and size(Hstr(1, 1)) == 12
assert Sstr(1) == '[][](p|~[][]q)' and size(Sstr(1)) == 8
assert all(size(Hstr(m, j)) == m + j + 10 and size(Sstr(j)) == 2*j + 6 for m in range(0, 6) for j in range(1, 6))
FB, CB, DB, CON = '[]p', '~F', 'F', '~[]F'
for m in range(1, 4):
    for j in range(1, m+1):
        h = Hstr(m, j)
        assert game(h, h) == (False, False) and game(h, FB) == (True, True) and game(h, CB) == (True, True)
        assert game(h, DB) == (False, False) and game(h, CON) == (False, True), (m, j)
        for k in range(1, 5): assert game(h, Fstr(k)) == ((k <= j),) * 2, (m, j, k)
        for i in range(0, 6): assert game(h, Pstr(i)) == ((i > m),) * 2, (m, j, i)
        assert game(h, Sstr(j)) == (False, True) and game(Gstr(m, j), Sstr(j)) == (False, False), (m, j)
print('PASS: Lean H_{m,j} laws and S_j separator for all indices; 4 negative controls rejected; tables and string solver agree')
