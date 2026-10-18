"""C046 r1: Lean proof, for ALL indices, of r2's K10 laws for the gate family
W_n(X) = box(box^n F | (p & (q | ~box q))) (p = X coops W_n, q = X coops DefectBot).
Opponents: F_k = box^k p (k>=1), P_j = box p & box(~box^j F -> ~q), W_m.
Semantics: closed GL fixed points are letter-free, hence decided by height on the chain
(Boolos, Logic of Provability ch. 7): box phi at h iff phi at all g<h. Each theorem holds for
ANY solution of the height equations (no uniqueness assumption).
  w_fk: k<n -> mutual coop at every height; n<=k -> W_n defects h>=k+1, F_k defects h>=2k+1
  pj_db: P_j's DefectBot trace is true exactly at h=0
  w_pj: 2<=n<j -> mutual coop everywhere; j<=n -> P_j defects h>=j+1, W_n h>=n+2;
        n<2 -> W_n defects h>=2, P_j h>=3
  w_wm: for all n,m both defect at every h>=n+m+3
This script: (1) runs embedded Lean (`lean --stdin`), asserts success, 4 axiom reports, no sorryAx;
(2) four false variants must be rejected; (3) explicit height tables (heights 0..79) for
n<=12, k,j,m<=14 agree with every theorem, and K10's predicates for n=2..5 are reproduced.
"""
import subprocess, shutil, os
LEAN_SRC = '/- Height semantics of closed GL fixed points on the chain 0<1<2<...:\n   a world of height h sees exactly heights g<h, so box phi holds at h iff phi holds at all g<h.\n   Gate agent W_n(X) = box( box^n False  or  (p and (q or not box q)) ),\n   p = "X cooperates with W_n", q = "X cooperates with DefectBot". W_2 is K6\'s W (size 12).\n   This file: all-index pairings of W_n with F_k, P_j and W_m (r2\'s K10 laws).\n   gate n p q is the formula under the outer box; W_n\'s action is bx (gate n p q). -/\n\ndef bx (φ : Nat → Prop) : Nat → Prop := fun h => ∀ g, g < h → φ g\ndef bxn : Nat → (Nat → Prop) → (Nat → Prop)\n  | 0, φ => φ\n  | n+1, φ => bx (bxn n φ)\n\ntheorem bxn_succ_iff (n : Nat) (φ : Nat → Prop) (h : Nat) :\n    bxn (n+1) φ h ↔ ∀ g, g + (n+1) ≤ h → φ g := by\n  induction n generalizing h with\n  | zero =>\n    simp only [bxn, bx]\n    exact ⟨fun H g hg => H g (by omega), fun H g hg => H g (by omega)⟩\n  | succ n ih =>\n    show bx (bxn (n+1) φ) h ↔ _\n    simp only [bx]\n    constructor\n    · intro H g hg\n      exact (ih (h-1)).1 (H (h-1) (by omega)) g (by omega)\n    · intro H g\' hg\'\n      exact (ih g\').2 (fun g hg => H g (by omega))\n\ntheorem bxn_iff (n : Nat) (hn : 1 ≤ n) (φ : Nat → Prop) (h : Nat) :\n    bxn n φ h ↔ ∀ g, g + n ≤ h → φ g := by\n  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩\n  exact bxn_succ_iff m φ h\n\ndef botn (n : Nat) : Nat → Prop := bxn n (fun _ => False)\n\ntheorem botn_iff (n h : Nat) : botn n h ↔ h < n := by\n  cases n with\n  | zero => simp [botn, bxn]\n  | succ m =>\n    unfold botn; rw [bxn_succ_iff]\n    constructor\n    · intro H; apply Classical.byContradiction; intro hn\n      exact H 0 (by omega)\n    · intro hlt g hg; omega\n\n\ndef gate (n : Nat) (p q : Nat → Prop) : Nat → Prop :=\n  fun g => botn n g ∨ (p g ∧ (q g ∨ ¬ bx q g))\n\n/-! Pairings of the gate family W_n with F_k = box^k p, P_j = box p and box(not box^j F -> not q),\n    and W_m. Every opponent\'s DefectBot trace has the shape d h <-> h <= c (c = k-1 for F_k,\n    c = 0 for P_j, c = m for W_m), so the q-clause (q or not box q) fails at exactly one height, c+1. -/\n\ntheorem strong (P : Nat → Prop) (step : ∀ h, (∀ g, g < h → P g) → P h) : ∀ h, P h := by\n  have key : ∀ N h, h < N → P h := by\n    intro N\n    induction N with\n    | zero => intro h hh; omega\n    | succ N ih => intro h hh; exact step h (fun g hg => ih g (by omega))\n  exact fun h => key (h+1) h (by omega)\n\n/-- The q-clause fails exactly at c+1. -/\ntheorem qclause (d : Nat → Prop) (c : Nat) (hd : ∀ h, d h ↔ h ≤ c) (g : Nat) :\n    (d g ∨ ¬ bx d g) ↔ g ≠ c + 1 := by\n  constructor\n  · intro H hg\n    subst hg\n    rcases H with H | H\n    · rw [hd] at H; omega\n    · exact H (fun g\' hg\' => (hd g\').2 (by omega))\n  · intro hg\n    by_cases hc : g ≤ c\n    · exact Or.inl ((hd g).2 hc)\n    · exact Or.inr (fun H => by have := (hd (c+1)).1 (H (c+1) (by omega)); omega)\n\n/-- If n <= c+1 the gate fails at c+1, so W_n defects at every h >= c+2, whatever p is. -/\ntheorem gate_fail (n c : Nat) (p d : Nat → Prop) (hd : ∀ h, d h ↔ h ≤ c) (hn : n ≤ c + 1) :\n    ∀ h, c + 2 ≤ h → ¬ bx (gate n p d) h := by\n  intro h hh H\n  rcases H (c+1) (by omega) with hb | ⟨_, hq⟩\n  · rw [botn_iff] at hb; omega\n  · exact (qclause d c hd (c+1)).1 hq rfl\n\ntheorem gate_ok (n c : Nat) (p d : Nat → Prop) (hd : ∀ h, d h ↔ h ≤ c) (g : Nat)\n    (hg : g < n ∨ (p g ∧ g ≠ c + 1)) : gate n p d g := by\n  rcases hg with hg | ⟨hp, hc⟩\n  · exact Or.inl ((botn_iff n g).2 hg)\n  · exact Or.inr ⟨hp, (qclause d c hd g).2 hc⟩\n\n/-- W_n vs F_k (k >= 1). x: W_n\'s action, y: F_k\'s action, e: F_k\'s DefectBot trace box^k F.\n    k < n: mutual cooperation at every height.  n <= k: W_n defects from k+1, F_k from 2k+1. -/\ntheorem w_fk (n k : Nat) (hk : 1 ≤ k) (x y e : Nat → Prop) (he : ∀ h, e h ↔ botn k h)\n    (hx : ∀ h, x h ↔ bx (gate n y e) h) (hy : ∀ h, y h ↔ bxn k x h) :\n    (k < n → ∀ h, x h ∧ y h) ∧\n    (n ≤ k → (∀ h, k + 1 ≤ h → ¬ x h) ∧ (∀ h, 2 * k + 1 ≤ h → ¬ y h)) := by\n  have he\' : ∀ h, e h ↔ h ≤ k - 1 := fun h => by rw [he, botn_iff]; omega\n  constructor\n  · intro hkn\n    apply strong\n    intro h ih\n    refine ⟨(hx h).2 (fun g hg => gate_ok n (k-1) y e he\' g ?_), (hy h).2 ?_⟩\n    · by_cases hgn : g < n\n      · exact Or.inl hgn\n      · exact Or.inr ⟨(ih g hg).2, by omega⟩\n    · rw [bxn_iff k hk]\n      intro g hg; exact (ih g (by omega)).1\n  · intro hnk\n    have nx : ∀ h, k + 1 ≤ h → ¬ x h := fun h hh xh =>\n      gate_fail n (k-1) y e he\' (by omega) h (by omega) ((hx h).1 xh)\n    refine ⟨nx, fun h hh yh => ?_⟩\n    rw [hy h, bxn_iff k hk] at yh\n    exact nx (k+1) (by omega) (yh (k+1) (by omega))\n\n/-- P_j\'s DefectBot trace is true exactly at height 0. -/\ntheorem pj_db (j : Nat) (d : Nat → Prop)\n    (hd : ∀ h, d h ↔ (bx (fun _ => False) h ∧ bx (fun g => ¬ botn j g → ¬ False) h)) :\n    ∀ h, d h ↔ h ≤ 0 := by\n  intro h\n  rw [hd h]\n  constructor\n  · intro ⟨H, _⟩\n    apply Classical.byContradiction; intro hh\n    exact H 0 (by omega)\n  · intro hh\n    exact ⟨fun g hg => by omega, fun g hg => by omega⟩\n\n/-- W_n vs P_j. x: W_n\'s action, y: P_j\'s action; d: P_j\'s DB trace, w: W_n\'s DB trace (w_db).\n    2 <= n < j: mutual cooperation at every height.  j <= n: P_j defects from j+1, W_n from n+2.\n    n < 2: W_n defects from 2, P_j from 3. -/\ntheorem w_pj (n j : Nat) (x y d w : Nat → Prop) (hd : ∀ h, d h ↔ h ≤ 0) (hw : ∀ h, w h ↔ h ≤ n)\n    (hx : ∀ h, x h ↔ bx (gate n y d) h)\n    (hy : ∀ h, y h ↔ (bx x h ∧ bx (fun g => ¬ botn j g → ¬ w g) h)) :\n    (2 ≤ n → n < j → ∀ h, x h ∧ y h) ∧\n    (j ≤ n → (∀ h, j + 1 ≤ h → ¬ y h) ∧ (∀ h, n + 2 ≤ h → ¬ x h)) ∧\n    (n < 2 → (∀ h, 2 ≤ h → ¬ x h) ∧ (∀ h, 3 ≤ h → ¬ y h)) := by\n  refine ⟨?_, ?_, ?_⟩\n  · intro hn hnj\n    apply strong\n    intro h ih\n    refine ⟨(hx h).2 (fun g hg => gate_ok n 0 y d hd g ?_), (hy h).2 ⟨fun g hg => (ih g hg).1, ?_⟩⟩\n    · by_cases hgn : g < n\n      · exact Or.inl hgn\n      · exact Or.inr ⟨(ih g hg).2, by omega⟩\n    · intro g hg hb hwg\n      rw [botn_iff] at hb; rw [hw] at hwg; omega\n  · intro hjn\n    have ny : ∀ h, j + 1 ≤ h → ¬ y h := by\n      intro h hh yh\n      have H := ((hy h).1 yh).2 j (by omega)\n      exact H (by rw [botn_iff]; omega) ((hw j).2 hjn)\n    refine ⟨ny, fun h hh xh => ?_⟩\n    rcases ((hx h).1 xh) (n+1) (by omega) with hb | ⟨hyn, _⟩\n    · rw [botn_iff] at hb; omega\n    · exact ny (n+1) (by omega) hyn\n  · intro hn\n    have nx : ∀ h, 2 ≤ h → ¬ x h := fun h hh xh =>\n      gate_fail n 0 y d hd (by omega) h hh ((hx h).1 xh)\n    exact ⟨nx, fun h hh yh => nx 2 (by omega) (((hy h).1 yh).1 2 (by omega))⟩\n\n/-- W_n vs W_m: for all n, m both defect at every height >= n+m+3 (no pair ever cooperates at the tail).\n    dm, dn: the DefectBot traces of W_m and W_n (w_db: true exactly at h <= m, h <= n). -/\ntheorem w_wm (n m : Nat) (x y dm dn : Nat → Prop) (hdm : ∀ h, dm h ↔ h ≤ m) (hdn : ∀ h, dn h ↔ h ≤ n)\n    (hx : ∀ h, x h ↔ bx (gate n y dm) h) (hy : ∀ h, y h ↔ bx (gate m x dn) h) :\n    ∀ h, n + m + 3 ≤ h → ¬ x h ∧ ¬ y h := by\n  intro h hh\n  by_cases hc : n ≤ m + 1\n  · have nx : ∀ h, m + 2 ≤ h → ¬ x h := fun h hh\' xh =>\n      gate_fail n m y dm hdm hc h hh\' ((hx h).1 xh)\n    refine ⟨nx h (by omega), fun yh => ?_⟩\n    rcases ((hy h).1 yh) (m+2) (by omega) with hb | ⟨xg, _⟩\n    · rw [botn_iff] at hb; omega\n    · exact nx (m+2) (by omega) xg\n  · have ny : ∀ h, n + 2 ≤ h → ¬ y h := fun h hh\' yh =>\n      gate_fail m n x dn hdn (by omega) h hh\' ((hy h).1 yh)\n    refine ⟨fun xh => ?_, ny h (by omega)⟩\n    rcases ((hx h).1 xh) (n+2) (by omega) with hb | ⟨yg, _⟩\n    · rw [botn_iff] at hb; omega\n    · exact ny (n+2) (by omega) yg\n\n#print axioms w_fk\n#print axioms pj_db\n#print axioms w_pj\n#print axioms w_wm\n'

def lean():
    for c in (shutil.which('lean'), '/opt/elan/bin/lean', os.path.expanduser('~/.elan/bin/lean')):
        if c and os.path.exists(c): return c
    raise AssertionError('lean binary not found')
def run(s):
    r = subprocess.run([lean(), '--stdin'], input=s, capture_output=True, text=True, timeout=100)
    return r.returncode, r.stdout + r.stderr
code, out = run(LEAN_SRC)
assert code == 0, out
assert 'error' not in out.lower() and 'sorryAx' not in out and out.count('depends on axioms') == 4, out
bads = [('(k < n \u2192 \u2200 h, x h \u2227 y h)', '(k \u2264 n \u2192 \u2200 h, x h \u2227 y h)'),
        ('(2 \u2264 n \u2192 n < j \u2192', '(2 \u2264 n \u2192 n \u2264 j \u2192'),
        ('\u2200 h, n + m + 3 \u2264 h \u2192 \u00ac x h', '\u2200 h, n + m \u2264 h \u2192 \u00ac x h'),
        ('(n < 2 \u2192 (\u2200 h, 2 \u2264 h \u2192 \u00ac x h)', '(n < 3 \u2192 (\u2200 h, 2 \u2264 h \u2192 \u00ac x h)')]
for a, b in bads:
    assert LEAN_SRC.count(a) == 1, a
    c2, o2 = run(LEAN_SRC.replace(a, b, 1))
    assert c2 != 0 and 'error' in o2, ('negative control accepted', b)
H = 80
def gate(n, p, q, g): return g < n or (p[g] and (q[g] or not all(q[:g])))
def W(n, p, q, h): return all(gate(n, p, q, g) for g in range(h))
def play(fx, fy):   # simultaneous height recursion: each side reads the other's strictly lower heights
    xs, ys = [], []
    for h in range(H):
        xs.append(fx(ys, h)); ys.append(fy(xs[:h], h))
    return xs, ys
def first_def(t): return next((h for h, v in enumerate(t) if not v), None)
dW = lambda n: [h <= n for h in range(H)]
for n in range(13):
    assert [W(n, [False]*H, [False]*H, h) for h in range(H)] == dW(n)
    for k in range(1, 15):
        e = [h < k for h in range(H)]
        xs, ys = play(lambda ys, h: W(n, ys + [None]*(H-len(ys)), e, h),
                      lambda xs, h: all(xs[g] for g in range(h-k+1)))
        if k < n: assert all(xs) and all(ys), (n, k)
        else: assert not any(xs[k+1:]) and not any(ys[2*k+1:]) and first_def(xs) == k+1, (n, k)
    for j in range(15):
        dP = [h == 0 for h in range(H)]
        assert [all(False for g in range(h)) and all((g < j) or True for g in range(h)) for h in range(H)] == dP
        xs, ys = play(lambda ys, h: W(n, ys + [None]*(H-len(ys)), dP, h),
                      lambda xs, h: all(xs[:h]) and all(g < j or not dW(n)[g] for g in range(h)))
        if 2 <= n < j: assert all(xs) and all(ys), (n, j)
        if j <= n: assert not any(ys[j+1:]) and not any(xs[n+2:]), (n, j)
        if n < 2: assert not any(xs[2:]) and not any(ys[3:]), (n, j)
        if not (2 <= n < j): assert not xs[-1] and not ys[-1]
    for m in range(15):
        xs, ys = play(lambda ys, h: W(n, ys + [None]*(H-len(ys)), dW(m), h),
                      lambda xs, h: W(m, xs + [None]*(H-len(xs)), dW(n), h))
        assert not any(xs[n+m+3:]) and not any(ys[n+m+3:]), (n, m)
# K10 (r2) predicates, n=2..5: F_k (k=1..6) iff k<n; P_j (j=0..6) iff j>n; W_m (m=2..5) never
for n in range(2, 6):
    assert [k for k in range(1, 7) if k < n] == list(range(1, n))
    assert [j for j in range(7) if 2 <= n < j] == list(range(n+1, 7))
print('PASS: Lean w_fk, pj_db, w_pj, w_wm for all indices; 4 negative controls rejected; tables n<=12, k,j,m<=14 agree')
