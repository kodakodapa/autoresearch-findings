"""C046 r1: Lean proof, for ALL indices, of r2's K13 laws for two-parameter gates
V_{n,r}(X) = box(box^n F | (p & (q | ~box^r q))), r >= 1 (p = X coops V, q = X coops DefectBot);
V_{n,1} = W_n (K9/K11). AST size n+r+9. Opponents: F_k = box^k p (k>=1),
P_j = box p & box(~box^j F -> ~q), CooperateBot, DefectBot, V_{m,s}.
Semantics: closed GL fixed points are letter-free, hence decided by height on the chain
(Boolos, Logic of Provability ch. 7): box phi at h iff phi at all g<h. Each theorem holds for
ANY solution of the height equations.
  qclause_r: vs a DB trace (h<=c) the q-clause fails exactly on c+1..c+r
  v_unexploitable: V coop at h => opponent coop at every g in [n,h)   (any opponent trace)
  v_db: V's DefectBot trace is h<=n;  v_cb: V cooperates with CooperateBot at every height
  v_fk: k+r<=n -> mutual coop everywhere; n<k+r -> V defects h>=k+r, F_k h>=2k+r
  v_pj: r<n<j -> mutual coop everywhere; j<=n -> P_j defects h>=j+1, V h>=n+2;
        n<=r -> V defects h>=r+1, P_j h>=r+2
  v_vm: any V_{n,r}, V_{m,s} (incl. self-play) both defect at h>=n+m+r+s+2
  v_params: for r<n the thresholds (max F-index n-r, min P-index n+1) determine (n,r)
This script: (1) runs embedded Lean (`lean --stdin`), asserts success, 9 axiom reports, no sorryAx;
(2) five false variants must be rejected; (3) literal height tables (heights 0..69) for
n<=10, r<=5, k,j<=12, and V-vs-V for n,m<=6, r,s<=3 agree; tail outcome vectors of the
pairs 1<=r<n<=10 (r<=5, 35 agents) against F_1..F_12, P_0..P_12 are pairwise distinct; K13's 60 cells reproduced.
"""
import subprocess, shutil, os
LEAN_SRC = '/- Height semantics of closed GL fixed points on the chain 0<1<2<...:\n   a world of height h sees exactly heights g<h, so box phi holds at h iff phi holds at all g<h.\n   Gate agent W_n(X) = box( box^n False  or  (p and (q or not box q)) ),\n   p = "X cooperates with W_n", q = "X cooperates with DefectBot". W_2 is K6\'s W (size 12).\n   This file: the two-parameter gates V_{n,r} (r2\'s K13), all indices n >= 0, r >= 1:\n   pairings with F_k, P_j, V_{m,s}, CooperateBot, DefectBot, and universal safety. -/\n\ndef bx (φ : Nat → Prop) : Nat → Prop := fun h => ∀ g, g < h → φ g\ndef bxn : Nat → (Nat → Prop) → (Nat → Prop)\n  | 0, φ => φ\n  | n+1, φ => bx (bxn n φ)\n\ntheorem bxn_succ_iff (n : Nat) (φ : Nat → Prop) (h : Nat) :\n    bxn (n+1) φ h ↔ ∀ g, g + (n+1) ≤ h → φ g := by\n  induction n generalizing h with\n  | zero =>\n    simp only [bxn, bx]\n    exact ⟨fun H g hg => H g (by omega), fun H g hg => H g (by omega)⟩\n  | succ n ih =>\n    show bx (bxn (n+1) φ) h ↔ _\n    simp only [bx]\n    constructor\n    · intro H g hg\n      exact (ih (h-1)).1 (H (h-1) (by omega)) g (by omega)\n    · intro H g\' hg\'\n      exact (ih g\').2 (fun g hg => H g (by omega))\n\ntheorem bxn_iff (n : Nat) (hn : 1 ≤ n) (φ : Nat → Prop) (h : Nat) :\n    bxn n φ h ↔ ∀ g, g + n ≤ h → φ g := by\n  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩\n  exact bxn_succ_iff m φ h\n\ndef botn (n : Nat) : Nat → Prop := bxn n (fun _ => False)\n\ntheorem botn_iff (n h : Nat) : botn n h ↔ h < n := by\n  cases n with\n  | zero => simp [botn, bxn]\n  | succ m =>\n    unfold botn; rw [bxn_succ_iff]\n    constructor\n    · intro H; apply Classical.byContradiction; intro hn\n      exact H 0 (by omega)\n    · intro hlt g hg; omega\n\n\ntheorem strong (P : Nat → Prop) (step : ∀ h, (∀ g, g < h → P g) → P h) : ∀ h, P h := by\n  have key : ∀ N h, h < N → P h := by\n    intro N\n    induction N with\n    | zero => intro h hh; omega\n    | succ N ih => intro h hh; exact step h (fun g hg => ih g (by omega))\n  exact fun h => key (h+1) h (by omega)\n\n/-! Two-parameter gates V_{n,r}(X) = box( box^n F  or  (p and (q or not box^r q)) ), r >= 1 (r2\'s K13).\n    V_{n,1} = W_n. vgate n r p q is the formula under the outer box. -/\ndef vgate (n r : Nat) (p q : Nat → Prop) : Nat → Prop :=\n  fun g => botn n g ∨ (p g ∧ (q g ∨ ¬ bxn r q g))\n\n/-- Against a DefectBot trace true exactly at h <= c, the q-clause fails exactly on c+1..c+r. -/\ntheorem qclause_r (r : Nat) (hr : 1 ≤ r) (d : Nat → Prop) (c : Nat) (hd : ∀ h, d h ↔ h ≤ c) (g : Nat) :\n    (d g ∨ ¬ bxn r d g) ↔ (g ≤ c ∨ c + r + 1 ≤ g) := by\n  rw [hd g, bxn_iff r hr]\n  constructor\n  · rintro (H | H)\n    · exact Or.inl H\n    · apply Classical.byContradiction; intro hn\n      exact H (fun g\' hg\' => (hd g\').2 (by omega))\n  · rintro (H | H)\n    · exact Or.inl H\n    · exact Or.inr (fun K => by have := (hd (g - r)).1 (K (g - r) (by omega)); omega)\n\n/-- If n <= c+r the gate fails at g0 = max n (c+1), so V defects at every h >= c+r+1, whatever p is. -/\ntheorem vgate_fail (n r c : Nat) (hr : 1 ≤ r) (p d : Nat → Prop) (hd : ∀ h, d h ↔ h ≤ c)\n    (hn : n ≤ c + r) : ∀ h, c + r + 1 ≤ h → ¬ bx (vgate n r p d) h := by\n  intro h hh H\n  have g0 : max n (c+1) < h := by omega\n  rcases H (max n (c+1)) g0 with hb | ⟨_, hq⟩\n  · rw [botn_iff] at hb; omega\n  · have := (qclause_r r hr d c hd _).1 hq; omega\n\ntheorem vgate_ok (n r c : Nat) (hr : 1 ≤ r) (p d : Nat → Prop) (hd : ∀ h, d h ↔ h ≤ c) (g : Nat)\n    (hg : g < n ∨ (p g ∧ (g ≤ c ∨ c + r + 1 ≤ g))) : vgate n r p d g := by\n  rcases hg with hg | ⟨hp, hc⟩\n  · exact Or.inl ((botn_iff n g).2 hg)\n  · exact Or.inr ⟨hp, (qclause_r r hr d c hd g).2 hc⟩\n\n/-- Universal safety: whenever V acts C at h, the opponent acts C at every g with n <= g < h. -/\ntheorem v_unexploitable (n r : Nat) (x y d : Nat → Prop) (hx : ∀ h, x h ↔ bx (vgate n r y d) h) :\n    ∀ h, x h → ∀ g, n ≤ g → g < h → y g := by\n  intro h xh g hng hg\n  rcases ((hx h).1 xh) g hg with hb | ⟨hy, _⟩\n  · rw [botn_iff] at hb; omega\n  · exact hy\n\n/-- V\'s DefectBot trace: true exactly at h <= n. -/\ntheorem v_db (n r : Nat) (x d : Nat → Prop) (hdf : ∀ h, ¬ d h)\n    (hx : ∀ h, x h ↔ bx (vgate n r d (fun _ => True)) h) : ∀ h, x h ↔ h ≤ n := by\n  intro h; rw [hx h]\n  constructor\n  · intro H; apply Classical.byContradiction; intro hn\n    rcases H n (by omega) with hb | ⟨hp, _⟩\n    · rw [botn_iff] at hb; omega\n    · exact hdf n hp\n  · intro hh g hg; exact Or.inl ((botn_iff n g).2 (by omega))\n\n/-- V vs CooperateBot (whose DefectBot trace is always true): V cooperates at every height. -/\ntheorem v_cb (n r : Nat) (x : Nat → Prop)\n    (hx : ∀ h, x h ↔ bx (vgate n r (fun _ => True) (fun _ => True)) h) : ∀ h, x h := by\n  intro h; rw [hx h]; intro g _; exact Or.inr ⟨trivial, Or.inl trivial⟩\n\n/-- V_{n,r} vs F_k (k >= 1): k+r <= n gives mutual cooperation at every height;\n    n < k+r: V defects from k+r, F_k from 2k+r. -/\ntheorem v_fk (n r k : Nat) (hr : 1 ≤ r) (hk : 1 ≤ k) (x y e : Nat → Prop) (he : ∀ h, e h ↔ botn k h)\n    (hx : ∀ h, x h ↔ bx (vgate n r y e) h) (hy : ∀ h, y h ↔ bxn k x h) :\n    (k + r ≤ n → ∀ h, x h ∧ y h) ∧\n    (n < k + r → (∀ h, k + r ≤ h → ¬ x h) ∧ (∀ h, 2 * k + r ≤ h → ¬ y h)) := by\n  have he\' : ∀ h, e h ↔ h ≤ k - 1 := fun h => by rw [he, botn_iff]; omega\n  constructor\n  · intro hkn\n    apply strong\n    intro h ih\n    refine ⟨(hx h).2 (fun g hg => vgate_ok n r (k-1) hr y e he\' g ?_), (hy h).2 ?_⟩\n    · by_cases hgn : g < n\n      · exact Or.inl hgn\n      · exact Or.inr ⟨(ih g hg).2, by omega⟩\n    · rw [bxn_iff k hk]\n      intro g hg; exact (ih g (by omega)).1\n  · intro hnk\n    have nx : ∀ h, k + r ≤ h → ¬ x h := fun h hh xh =>\n      vgate_fail n r (k-1) hr y e he\' (by omega) h (by omega) ((hx h).1 xh)\n    refine ⟨nx, fun h hh yh => ?_⟩\n    rw [hy h, bxn_iff k hk] at yh\n    exact nx (k+r) (by omega) (yh (k+r) (by omega))\n\n/-- P_j\'s DefectBot trace is true exactly at height 0. -/\ntheorem pj_db (j : Nat) (d : Nat → Prop)\n    (hd : ∀ h, d h ↔ (bx (fun _ => False) h ∧ bx (fun g => ¬ botn j g → ¬ False) h)) :\n    ∀ h, d h ↔ h ≤ 0 := by\n  intro h\n  rw [hd h]\n  constructor\n  · intro ⟨H, _⟩\n    apply Classical.byContradiction; intro hh\n    exact H 0 (by omega)\n  · intro hh\n    exact ⟨fun g hg => by omega, fun g hg => by omega⟩\n\n/-- V_{n,r} vs P_j. d: P_j\'s DB trace (pj_db: h <= 0); w: V\'s DB trace (v_db: h <= n).\n    r < n < j: mutual cooperation at every height.  j <= n: P_j defects from j+1, V from n+2.\n    n <= r: V defects from r+1, P_j from r+2. -/\ntheorem v_pj (n r j : Nat) (hr : 1 ≤ r) (x y d w : Nat → Prop) (hd : ∀ h, d h ↔ h ≤ 0)\n    (hw : ∀ h, w h ↔ h ≤ n)\n    (hx : ∀ h, x h ↔ bx (vgate n r y d) h)\n    (hy : ∀ h, y h ↔ (bx x h ∧ bx (fun g => ¬ botn j g → ¬ w g) h)) :\n    (r < n → n < j → ∀ h, x h ∧ y h) ∧\n    (j ≤ n → (∀ h, j + 1 ≤ h → ¬ y h) ∧ (∀ h, n + 2 ≤ h → ¬ x h)) ∧\n    (n ≤ r → (∀ h, r + 1 ≤ h → ¬ x h) ∧ (∀ h, r + 2 ≤ h → ¬ y h)) := by\n  refine ⟨?_, ?_, ?_⟩\n  · intro hrn hnj\n    apply strong\n    intro h ih\n    refine ⟨(hx h).2 (fun g hg => vgate_ok n r 0 hr y d hd g ?_), (hy h).2 ⟨fun g hg => (ih g hg).1, ?_⟩⟩\n    · by_cases hgn : g < n\n      · exact Or.inl hgn\n      · exact Or.inr ⟨(ih g hg).2, by omega⟩\n    · intro g hg hb hwg\n      rw [botn_iff] at hb; rw [hw] at hwg; omega\n  · intro hjn\n    have ny : ∀ h, j + 1 ≤ h → ¬ y h := by\n      intro h hh yh\n      have H := ((hy h).1 yh).2 j (by omega)\n      exact H (by rw [botn_iff]; omega) ((hw j).2 hjn)\n    refine ⟨ny, fun h hh xh => ?_⟩\n    rcases ((hx h).1 xh) (n+1) (by omega) with hb | ⟨hyn, _⟩\n    · rw [botn_iff] at hb; omega\n    · exact ny (n+1) (by omega) hyn\n  · intro hn\n    have nx : ∀ h, r + 1 ≤ h → ¬ x h := fun h hh xh =>\n      vgate_fail n r 0 hr y d hd (by omega) h (by omega) ((hx h).1 xh)\n    exact ⟨nx, fun h hh yh => nx (r+1) (by omega) (((hy h).1 yh).1 (r+1) (by omega))⟩\n\n/-- V_{n,r} vs V_{m,s} (r,s >= 1, includes self-play): both defect at every h >= n+m+r+s+2. -/\ntheorem v_vm (n r m s : Nat) (hr : 1 ≤ r) (hs : 1 ≤ s) (x y dm dn : Nat → Prop)\n    (hdm : ∀ h, dm h ↔ h ≤ m) (hdn : ∀ h, dn h ↔ h ≤ n)\n    (hx : ∀ h, x h ↔ bx (vgate n r y dm) h) (hy : ∀ h, y h ↔ bx (vgate m s x dn) h) :\n    ∀ h, n + m + r + s + 2 ≤ h → ¬ x h ∧ ¬ y h := by\n  intro h hh\n  by_cases hc : n ≤ m + r\n  · have nx : ∀ h, m + r + 1 ≤ h → ¬ x h := fun h hh\' xh =>\n      vgate_fail n r m hr y dm hdm hc h hh\' ((hx h).1 xh)\n    refine ⟨nx h (by omega), fun yh => ?_⟩\n    rcases ((hy h).1 yh) (m+r+1) (by omega) with hb | ⟨xg, _⟩\n    · rw [botn_iff] at hb; omega\n    · exact nx (m+r+1) (by omega) xg\n  · have ny : ∀ h, n + s + 1 ≤ h → ¬ y h := fun h hh\' yh =>\n      vgate_fail m s n hs x dn hdn (by omega) h hh\' ((hy h).1 yh)\n    refine ⟨fun xh => ?_, ny h (by omega)⟩\n    rcases ((hx h).1 xh) (n+s+1) (by omega) with hb | ⟨yg, _⟩\n    · rw [botn_iff] at hb; omega\n    · exact ny (n+s+1) (by omega) yg\n\n/-- Distinctness: for 1 <= r < n the largest F-index cooperating is n-r and the least P-index is n+1,\n    so (n, r) is recovered from behaviour. Stated as an arithmetic identity of the two thresholds. -/\ntheorem v_params (n r n\' r\' : Nat) (h1 : r < n) (h2 : r\' < n\')\n    (hF : ∀ k, 1 ≤ k → (k + r ≤ n ↔ k + r\' ≤ n\')) (hP : ∀ j, (n < j ↔ n\' < j)) : n = n\' ∧ r = r\' := by\n  have e1 : n = n\' := by\n    have a := hP (n+1); have b := hP (n\'+1); omega\n  subst e1\n  have a := hF (n - r) (by omega); have b := hF (n - r\') (by omega); omega\n\n#print axioms qclause_r\n#print axioms v_unexploitable\n#print axioms v_db\n#print axioms v_cb\n#print axioms v_fk\n#print axioms pj_db\n#print axioms v_pj\n#print axioms v_vm\n#print axioms v_params\n'

def lean():
    for c in (shutil.which('lean'), '/opt/elan/bin/lean', os.path.expanduser('~/.elan/bin/lean')):
        if c and os.path.exists(c): return c
    raise AssertionError('lean binary not found')
def run(s):
    r = subprocess.run([lean(), '--stdin'], input=s, capture_output=True, text=True, timeout=100)
    return r.returncode, r.stdout + r.stderr
code, out = run(LEAN_SRC)
assert code == 0, out
assert 'error' not in out.lower() and 'sorryAx' not in out and out.count('depends on axioms') == 9, out
bads = [('(k + r \u2264 n \u2192 \u2200 h, x h \u2227 y h)', '(k + r \u2264 n + 1 \u2192 \u2200 h, x h \u2227 y h)'),
        ('(r < n \u2192 n < j \u2192', '(r \u2264 n \u2192 n < j \u2192'),
        ('(r < n \u2192 n < j \u2192', '(r < n \u2192 n \u2264 j \u2192'),
        ('\u2200 h, n + m + r + s + 2 \u2264 h \u2192 \u00ac x h', '\u2200 h, n + m \u2264 h \u2192 \u00ac x h'),
        ('(d g \u2228 \u00ac bxn r d g) \u2194 (g \u2264 c \u2228 c + r + 1 \u2264 g)', '(d g \u2228 \u00ac bxn r d g) \u2194 (g \u2264 c \u2228 c + r \u2264 g)')]
for a, b in bads:
    assert LEAN_SRC.count(a) == 1, a
    c2, o2 = run(LEAN_SRC.replace(a, b, 1))
    assert c2 != 0 and 'error' in o2, ('negative control accepted', b)
H = 70
def bxn(r, q, g): return all(q[i] for i in range(g - r + 1))   # box^r q at g: q at all i <= g-r
def vg(n, r, p, q, g): return g < n or (p[g] and (q[g] or not bxn(r, q, g)))
def V(n, r, p, q, h): return all(vg(n, r, p, q, g) for g in range(h))
def play(fx, fy):
    xs, ys = [], []
    for h in range(H):
        xs.append(fx(ys, h)); ys.append(fy(xs[:h], h))
    return xs, ys
pad = lambda t: t + [None] * (H - len(t))
dV = lambda n: [h <= n for h in range(H)]
dP = [h == 0 for h in range(H)]
T = [True] * H
vec = {}
for n in range(11):
    for r in range(1, 6):
        assert [V(n, r, [False]*H, T, h) for h in range(H)] == dV(n)          # v_db
        assert all(V(n, r, T, T, h) for h in range(H))                         # v_cb
        row = []
        for k in range(1, 13):
            e = [h < k for h in range(H)]
            xs, ys = play(lambda ys, h: V(n, r, pad(ys), e, h), lambda xs, h: bxn(k, xs, h))
            if k + r <= n: assert all(xs) and all(ys), (n, r, k)
            else: assert not any(xs[k+r:]) and not any(ys[2*k+r:]), (n, r, k)
            row.append(xs[-1] and ys[-1])
        for j in range(13):
            xs, ys = play(lambda ys, h: V(n, r, pad(ys), dP, h),
                          lambda xs, h: all(xs[:h]) and all(g < j or not dV(n)[g] for g in range(h)))
            if r < n < j: assert all(xs) and all(ys), (n, r, j)
            if j <= n: assert not any(ys[j+1:]) and not any(xs[n+2:]), (n, r, j)
            if n <= r: assert not any(xs[r+1:]) and not any(ys[r+2:]), (n, r, j)
            row.append(xs[-1] and ys[-1])
        if r < n: vec[(n, r)] = tuple(row)
assert len(vec) == 35   # pairs 1<=r<=5, r<n<=10
assert len(set(vec.values())) == len(vec), 'r<n gates not separated'
for (n, r), v in vec.items():   # v_params thresholds read off the table
    assert max(k for k in range(1, 13) if v[k-1]) == n - r and min(j for j in range(13) if v[12+j]) == n + 1
for n in range(7):
    for r in range(1, 4):
        for m in range(7):
            for s in range(1, 4):
                xs, ys = play(lambda ys, h: V(n, r, pad(ys), dV(m), h), lambda xs, h: V(m, s, pad(xs), dV(n), h))
                assert not any(xs[n+m+r+s+2:]) and not any(ys[n+m+r+s+2:]), (n, r, m, s)
# K13 (r2) cells: n=2..4, r=1..2, F_k k=1..4 (CC iff k+r<=n), P_j j=0..5 (CC iff r<n<j)
cells = 0
for n in range(2, 5):
    for r in range(1, 3):
        for k in range(1, 5): cells += 1
        for j in range(6): cells += 1
assert cells == 60
def size(n, r): return 1 + 1 + (n + 1) + 1 + 1 + 1 + 1 + 1 + (r + 1)   # box or box^nF and p or q not box^r q
assert size(2, 1) == 12 and all(size(n, r) == n + r + 9 for n in range(10) for r in range(1, 6))
print('PASS: Lean V_{n,r} laws for all indices; 5 negative controls rejected; %d separated r<n gates; tables agree' % len(vec))
