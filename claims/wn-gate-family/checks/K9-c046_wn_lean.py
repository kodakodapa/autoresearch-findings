"""C046 r1: Lean proof, for ALL n, of the gate family W_n(X) = box(box^n F | (p & (q | ~box q))),
p = "X coops W_n", q = "X coops DefectBot" (AST size n+10; W_2 is K6's size-12 witness W).
Semantics: closed GL fixed points are letter-free, hence decided by height on the chain
(Boolos, Logic of Provability ch. 7): box phi at h iff phi at all g<h. Opponent traces p,q are
ARBITRARY functions Nat->Prop in w_gate/w_unexploitable, so they cover every modal opponent.
Theorems (each for any solution of the height equations; no uniqueness assumption):
  w_gate: W_n coops at h  ->  opponent coops at every g with n<=g<h      (any opponent)
  w_unexploitable: W_n eventually coops -> opponent eventually coops     (any opponent)
  w_db: vs DefectBot W_n coops exactly at h<=n;   w_cb: vs CooperateBot coops everywhere
  w_self, w_self_db: vs itself both copies coop exactly at h<=n+1 (defect at the tail)
  w_fb: vs FairBot, n>=2 -> mutual coop everywhere; n<2 -> W_n defects h>=2, FB defects h>=3
So for every n>=2, W_n is unexploitable, coops with FB and CB and defects against itself.
This script: (1) runs the embedded Lean with `lean --stdin`, asserts success and no sorryAx;
(2) negative controls (W_1 cooperates with FB; self-coop up to n+2; gate from g>=n-1) must be
rejected; (3) explicit height tables for n<=12 (heights 0..59) agree, plus 3000 random opponent
traces confirm w_gate; (4) AST size of W_n equals n+10.
"""
import subprocess, shutil, os, random
LEAN_SRC = '/- Height semantics of closed GL fixed points on the chain 0<1<2<...:\n   a world of height h sees exactly heights g<h, so box phi holds at h iff phi holds at all g<h.\n   Gate agent W_n(X) = box( box^n False  or  (p and (q or not box q)) ),\n   p = "X cooperates with W_n", q = "X cooperates with DefectBot". W_2 is K6\'s W (size 12).\n   gate n p q is the formula under the outer box; W_n\'s action is bx (gate n p q). -/\n\ndef bx (φ : Nat → Prop) : Nat → Prop := fun h => ∀ g, g < h → φ g\ndef bxn : Nat → (Nat → Prop) → (Nat → Prop)\n  | 0, φ => φ\n  | n+1, φ => bx (bxn n φ)\n\ntheorem bxn_succ_iff (n : Nat) (φ : Nat → Prop) (h : Nat) :\n    bxn (n+1) φ h ↔ ∀ g, g + (n+1) ≤ h → φ g := by\n  induction n generalizing h with\n  | zero =>\n    simp only [bxn, bx]\n    exact ⟨fun H g hg => H g (by omega), fun H g hg => H g (by omega)⟩\n  | succ n ih =>\n    show bx (bxn (n+1) φ) h ↔ _\n    simp only [bx]\n    constructor\n    · intro H g hg\n      exact (ih (h-1)).1 (H (h-1) (by omega)) g (by omega)\n    · intro H g\' hg\'\n      exact (ih g\').2 (fun g hg => H g (by omega))\n\ntheorem bxn_iff (n : Nat) (hn : 1 ≤ n) (φ : Nat → Prop) (h : Nat) :\n    bxn n φ h ↔ ∀ g, g + n ≤ h → φ g := by\n  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩\n  exact bxn_succ_iff m φ h\n\ndef botn (n : Nat) : Nat → Prop := bxn n (fun _ => False)\n\ntheorem botn_iff (n h : Nat) : botn n h ↔ h < n := by\n  cases n with\n  | zero => simp [botn, bxn]\n  | succ m =>\n    unfold botn; rw [bxn_succ_iff]\n    constructor\n    · intro H; apply Classical.byContradiction; intro hn\n      exact H 0 (by omega)\n    · intro hlt g hg; omega\n\n\ndef gate (n : Nat) (p q : Nat → Prop) : Nat → Prop :=\n  fun g => botn n g ∨ (p g ∧ (q g ∨ ¬ bx q g))\n\n/-- Universal unexploitability, per height: against ANY opponent traces p, q, if W_n\n    cooperates at h then the opponent cooperated at every g with n <= g < h. -/\ntheorem w_gate (n : Nat) (p q x : Nat → Prop) (hx : ∀ h, x h ↔ bx (gate n p q) h) :\n    ∀ h g, x h → n ≤ g → g < h → p g := by\n  intro h g xh hng hgh\n  rcases ((hx h).1 xh) g hgh with hb | ⟨hp, _⟩\n  · rw [botn_iff] at hb; omega\n  · exact hp\n\n/-- Tail form: if W_n eventually always cooperates, so does the opponent. -/\ntheorem w_unexploitable (n : Nat) (p q x : Nat → Prop) (hx : ∀ h, x h ↔ bx (gate n p q) h) :\n    (∃ H, ∀ h, H ≤ h → x h) → ∃ H, ∀ g, H ≤ g → p g := by\n  intro ⟨H, hH⟩\n  exact ⟨n + H, fun g hg => w_gate n p q x hx (g+1) g (hH (g+1) (by omega)) (by omega) (by omega)⟩\n\n/-- W_n against DefectBot (p = q = False): cooperates exactly at heights <= n. -/\ntheorem w_db (n : Nat) (d : Nat → Prop)\n    (hd : ∀ h, d h ↔ bx (gate n (fun _ => False) (fun _ => False)) h) : ∀ h, d h ↔ h ≤ n := by\n  intro h\n  rw [hd h]\n  constructor\n  · intro H\n    apply Classical.byContradiction; intro hlt\n    rcases H n (by omega) with hb | ⟨hf, _⟩\n    · rw [botn_iff] at hb; omega\n    · exact hf\n  · intro hle g hg\n    exact Or.inl ((botn_iff n g).2 (by omega))\n\n/-- W_n against CooperateBot (p = q = True): cooperates at every height. -/\ntheorem w_cb (n : Nat) (x : Nat → Prop)\n    (hx : ∀ h, x h ↔ bx (gate n (fun _ => True) (fun _ => True)) h) : ∀ h, x h := by\n  intro h\n  exact (hx h).2 (fun g _ => Or.inr ⟨trivial, Or.inl trivial⟩)\n\n/-- W_n against itself: both copies cooperate exactly at heights <= n+1, so they defect at the tail.\n    d is W_n\'s DefectBot trace (the q-input each copy reads). Holds for ANY solution x, y. -/\ntheorem w_self (n : Nat) (x y d : Nat → Prop) (hd : ∀ h, d h ↔ h ≤ n)\n    (hx : ∀ h, x h ↔ bx (gate n y d) h) (hy : ∀ h, y h ↔ bx (gate n x d) h) :\n    ∀ h, (x h ↔ h ≤ n+1) ∧ (y h ↔ h ≤ n+1) := by\n  have step : ∀ (u v : Nat → Prop), (∀ h, u h ↔ bx (gate n v d) h) →\n      ∀ h, (∀ g, g < h → (v g ↔ g ≤ n+1)) → (u h ↔ h ≤ n+1) := by\n    intro u v hu h ih\n    rw [hu h]\n    constructor\n    · intro H\n      apply Classical.byContradiction; intro hlt\n      rcases H (n+1) (by omega) with hb | ⟨_, hq⟩\n      · rw [botn_iff] at hb; omega\n      · rcases hq with hq | hq\n        · rw [hd] at hq; omega\n        · apply hq; intro g hg; rw [hd]; omega\n    · intro hle g hg\n      by_cases hgn : g < n\n      · exact Or.inl ((botn_iff n g).2 hgn)\n      · exact Or.inr ⟨(ih g hg).2 (by omega), Or.inl ((hd g).2 (by omega))⟩\n  have key : ∀ N, ∀ h, h ≤ N → (x h ↔ h ≤ n+1) ∧ (y h ↔ h ≤ n+1) := by\n    intro N\n    induction N with\n    | zero =>\n      intro h hh\n      exact ⟨step x y hx h (fun g hg => by omega), step y x hy h (fun g hg => by omega)⟩\n    | succ N ih =>\n      intro h hh\n      exact ⟨step x y hx h (fun g hg => (ih g (by omega)).2),\n             step y x hy h (fun g hg => (ih g (by omega)).1)⟩\n  exact fun h => key h h (Nat.le_refl _)\n\n/-- W_n against FairBot FB(X) = box (X coops FB); FB\'s DefectBot trace e is box False (true only at 0).\n    If n >= 2 both cooperate at every height; if n < 2, W_n defects at every h >= 2 and FB at every h >= 3. -/\ntheorem w_fb (n : Nat) (x y e : Nat → Prop) (he : ∀ h, e h ↔ bx (fun _ => False) h)\n    (hx : ∀ h, x h ↔ bx (gate n y e) h) (hy : ∀ h, y h ↔ bx x h) :\n    (2 ≤ n → ∀ h, x h ∧ y h) ∧ (n < 2 → ∀ h, 2 ≤ h → ¬ x h ∧ (3 ≤ h → ¬ y h)) := by\n  have e1 : ¬ e 1 := fun h1 => (he 1).1 h1 0 (by omega)\n  have be1 : bx e 1 := by\n    intro g hg\n    have : g = 0 := by omega\n    subst this\n    exact (he 0).2 (fun g hg => absurd hg (Nat.not_lt_zero _))\n  constructor\n  · intro hn\n    have key : ∀ N, ∀ h, h ≤ N → x h ∧ y h := by\n      intro N\n      induction N with\n      | zero =>\n        intro h hh\n        have h0 : h = 0 := by omega\n        subst h0\n        exact ⟨(hx 0).2 (fun g hg => absurd hg (Nat.not_lt_zero _)),\n               (hy 0).2 (fun g hg => absurd hg (Nat.not_lt_zero _))⟩\n      | succ N ih =>\n        intro h hh\n        have xh : x h := by\n          apply (hx h).2\n          intro g hg\n          by_cases hgn : g < n\n          · exact Or.inl ((botn_iff n g).2 hgn)\n          · refine Or.inr ⟨(ih g (by omega)).2, Or.inr ?_⟩\n            intro hb; exact e1 (hb 1 (by omega))\n        exact ⟨xh, (hy h).2 (fun g hg => by\n          by_cases hgh : g ≤ N\n          · exact (ih g hgh).1\n          · have : g = h := by omega\n            omega)⟩\n    exact fun h => key h h (Nat.le_refl _)\n  · intro hn\n    have nx : ∀ h, 2 ≤ h → ¬ x h := by\n      intro h hh xh\n      rcases ((hx h).1 xh) 1 (by omega) with hb | ⟨_, hq⟩\n      · rw [botn_iff] at hb; omega\n      · rcases hq with hq | hq\n        · exact e1 hq\n        · exact hq be1\n    intro h hh\n    exact ⟨nx h hh, fun h3 yh => nx 2 (by omega) ((hy h).1 yh 2 (by omega))⟩\n\n/-- Self-play with W_n\'s own DefectBot trace plugged in. -/\ntheorem w_self_db (n : Nat) (x y d : Nat → Prop)\n    (hd : ∀ h, d h ↔ bx (gate n (fun _ => False) (fun _ => False)) h)\n    (hx : ∀ h, x h ↔ bx (gate n y d) h) (hy : ∀ h, y h ↔ bx (gate n x d) h) :\n    ∀ h, (x h ↔ h ≤ n+1) ∧ (y h ↔ h ≤ n+1) :=\n  w_self n x y d (w_db n d hd) hx hy\n\n#print axioms w_self_db\n#print axioms w_gate\n#print axioms w_unexploitable\n#print axioms w_db\n#print axioms w_cb\n#print axioms w_self\n#print axioms w_fb\n'
def lean():
    for c in (shutil.which('lean'), '/opt/elan/bin/lean', os.path.expanduser('~/.elan/bin/lean')):
        if c and os.path.exists(c): return c
    raise AssertionError('lean binary not found')
def run(s):
    r = subprocess.run([lean(), '--stdin'], input=s, capture_output=True, text=True, timeout=100)
    return r.returncode, r.stdout + r.stderr
code, out = run(LEAN_SRC)
assert code == 0, out
assert 'sorry' not in out and 'error' not in out.lower(), out
assert out.count('axioms') == 7 and 'sorryAx' not in out, out
bads = [('(2 \u2264 n \u2192 \u2200 h, x h \u2227 y h)', '(1 \u2264 n \u2192 \u2200 h, x h \u2227 y h)'),
        ('\u2200 h, (x h \u2194 h \u2264 n+1) \u2227 (y h \u2194 h \u2264 n+1) := by', '\u2200 h, (x h \u2194 h \u2264 n+2) \u2227 (y h \u2194 h \u2264 n+2) := by'),
        ('\u2200 h g, x h \u2192 n \u2264 g \u2192', '\u2200 h g, x h \u2192 n \u2264 g + 1 \u2192')]
for a, b in bads:
    assert LEAN_SRC.count(a) >= 1, a
    c2, o2 = run(LEAN_SRC.replace(a, b, 1))
    assert c2 != 0, ('negative control accepted', b)
H = 60
def W(n, p, q, h):   # W_n's action at height h given opponent traces p,q (lists)
    return all(g < n or (p[g] and (q[g] or not all(q[:g]))) for g in range(h))
for n in range(13):
    d = [];  [d.append(W(n, [False]*H, [False]*H, h)) for h in range(H)]
    assert d == [h <= n for h in range(H)], n
    assert all(W(n, [True]*H, [True]*H, h) for h in range(H))
    x = []
    for h in range(H): x.append(W(n, x + [None]*(H-len(x)), d, h))   # symmetric self-play
    assert x == [h <= n+1 for h in range(H)], n
    e = [h == 0 for h in range(H)]                                     # FB vs DB = box F
    xs, ys = [], []
    for h in range(H):
        xs.append(W(n, ys + [None]*(H-len(ys)), e, h)); ys.append(all(xs[:h]))
    if n >= 2: assert all(xs) and all(ys), n
    else: assert not any(xs[2:]) and not any(ys[3:]) and xs[1] and ys[2], n
rng = random.Random(46)
for _ in range(3000):
    n = rng.randrange(6); p = [rng.random() < .8 for _ in range(30)]; q = [rng.random() < .5 for _ in range(30)]
    for h in range(30):
        if W(n, p, q, h): assert all(p[g] for g in range(n, h))
def size(s):   # AST nodes: atoms p,q,F and each of ~ [] & | count one
    return s.count('p') + s.count('q') + s.count('F') + s.count('~') + s.count('[]') + s.count('&') + s.count('|')
for n in range(13):
    Wn = '[](' + '[]'*n + 'F|(p&(q|~[]q)))'
    assert size(Wn) == n + 10
assert '[](' + '[]'*2 + 'F|(p&(q|~[]q)))' == '[]([][]F|(p&(q|~[]q)))'   # K6's W
print('PASS Lean proof of the W_n gate family for all n; 3 negative controls rejected; tables n<=12 agree')
