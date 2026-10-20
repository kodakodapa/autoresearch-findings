"""r1 cross-review of r2's K12 (generalized Hobson bots), all indices.
Height-chain semantics of closed GL fixed points: box(phi) holds at height h
iff phi holds at every g<h; box^n F holds iff h<n.  Prov_n(z)=box(box^n F | z).
H_{a,b} = ~Prov_a(p) & Prov_b(p); graded FairBot F_c = Prov_c(p). True = action 1.
(1) Lean 4 core proves, for EVERY solution x,y of the simultaneous equations:
    hob_eq   : a<b, a<d: H_{a,b} vs H_{a,d}: both play 1 exactly at heights > a;
    hob_tail : a != c (any b,d): both play 2 at every height >= some T;
    hob_fair : H_{a,b} vs F_c (any a,b,c): both play 2 from some height on.
    No sorryAx; two false variants are rejected.
(2) Independent recurrence: all a<b<=12, c<d<=12 and c<=12, 80 heights, tail
    equals K12's law and is constant over the last 20 heights.
Self-contained; stdlib + lean binary only.
"""
import subprocess, shutil, os
LEAN_SRC = "def bx (φ : Nat → Prop) : Nat → Prop := fun h => ∀ g, g < h → φ g\ndef bxn : Nat → (Nat → Prop) → (Nat → Prop)\n  | 0, φ => φ\n  | n+1, φ => bx (bxn n φ)\n\ntheorem bxn_succ_iff (n : Nat) (φ : Nat → Prop) (h : Nat) :\n    bxn (n+1) φ h ↔ ∀ g, g + (n+1) ≤ h → φ g := by\n  induction n generalizing h with\n  | zero =>\n    simp only [bxn, bx]\n    exact ⟨fun H g hg => H g (by omega), fun H g hg => H g (by omega)⟩\n  | succ n ih =>\n    show bx (bxn (n+1) φ) h ↔ _\n    simp only [bx]\n    constructor\n    · intro H g hg\n      exact (ih (h-1)).1 (H (h-1) (by omega)) g (by omega)\n    · intro H g' hg'\n      exact (ih g').2 (fun g hg => H g (by omega))\n\ndef botn (n : Nat) : Nat → Prop := bxn n (fun _ => False)\n\ntheorem botn_iff (n h : Nat) : botn n h ↔ h < n := by\n  cases n with\n  | zero => simp [botn, bxn]\n  | succ m =>\n    unfold botn; rw [bxn_succ_iff]\n    constructor\n    · intro H; apply Classical.byContradiction; intro hn\n      exact H 0 (by omega)\n    · intro hlt g hg; omega\n\n/-- Prov_{PA+n}(z) = box(box^n F ∨ z) on the height chain. -/\ndef PB (n : Nat) (z : Nat → Prop) : Nat → Prop := bx (fun g => botn n g ∨ z g)\n\ntheorem PB_iff (n : Nat) (z : Nat → Prop) (h : Nat) :\n    PB n z h ↔ ∀ g, n ≤ g → g < h → z g := by\n  unfold PB bx\n  constructor\n  · intro H g h1 h2\n    rcases H g h2 with hb | hz\n    · rw [botn_iff] at hb; omega\n    · exact hz\n  · intro H g hg\n    by_cases hgn : g < n\n    · exact Or.inl ((botn_iff n g).2 hgn)\n    · exact Or.inr (H g (by omega) hg)\n\n/-- Hobson bot H_{a,b} = ¬Prov_a(p) ∧ Prov_b(p). -/\ndef Hob (a b : Nat) (z : Nat → Prop) (h : Nat) : Prop := ¬ PB a z h ∧ PB b z h\n\ntheorem hob_low (a b : Nat) (x z : Nat → Prop) (hx : ∀ h, x h ↔ Hob a b z h) :\n    ∀ h, h ≤ a → ¬ x h := by\n  intro h hh H\n  exact ((hx h).1 H).1 ((PB_iff a z h).2 (fun g h1 h2 => by omega))\n\n/-- Equal weak grades: both play action 1 exactly at heights > a. -/\ntheorem hob_eq (a b d : Nat) (hab : a < b) (had : a < d) (x y : Nat → Prop)\n    (hx : ∀ h, x h ↔ Hob a b y h) (hy : ∀ h, y h ↔ Hob a d x h) :\n    ∀ h, (x h ↔ a < h) ∧ (y h ↔ a < h) := by\n  intro h\n  induction h using Nat.strongRecOn with\n  | _ h ih =>\n    constructor\n    · constructor\n      · intro H; apply Classical.byContradiction; intro hn\n        exact hob_low a b x y hx h (by omega) H\n      · intro hah\n        refine (hx h).2 ⟨?_, ?_⟩\n        · intro P; have := (PB_iff a y h).1 P a (Nat.le_refl a) hah\n          have := ((ih a hah).2).1 this; omega\n        · exact (PB_iff b y h).2 (fun g h1 h2 => ((ih g h2).2).2 (by omega))\n    · constructor\n      · intro H; apply Classical.byContradiction; intro hn\n        exact hob_low a d y x hy h (by omega) H\n      · intro hah\n        refine (hy h).2 ⟨?_, ?_⟩\n        · intro P; have := (PB_iff a x h).1 P a (Nat.le_refl a) hah\n          have := ((ih a hah).1).1 this; omega\n        · exact (PB_iff d x h).2 (fun g h1 h2 => ((ih g h2).1).2 (by omega))\n\n/-- Unequal weak grades a < c: both eventually play action 2 forever. -/\ntheorem hob_neq (a b c d : Nat) (hac : a < c) (x y : Nat → Prop)\n    (hx : ∀ h, x h ↔ Hob a b y h) (hy : ∀ h, y h ↔ Hob c d x h) :\n    ∃ T, ∀ h, T ≤ h → ¬ x h ∧ ¬ y h := by\n  have Y0 := hob_low c d y x hy\n  -- for h > a, x h iff Prov_b(y)\n  have Xmono : ∀ t, a < t → ¬ x t → ∀ h, t ≤ h → ¬ x h := by\n    intro t hat hnt h hth H\n    apply hnt; refine (hx t).2 ⟨?_, ?_⟩\n    · intro P; exact Y0 a (by omega) ((PB_iff a y t).1 P a (Nat.le_refl a) hat)\n    · exact (PB_iff b y t).2 (fun g h1 h2 => (PB_iff b y h).1 ((hx h).1 H).2 g h1 (by omega))\n  have ex : ∃ t, a < t ∧ ¬ x t := by\n    apply Classical.byContradiction; intro hne\n    have allx : ∀ t, a < t → x t := fun t ht =>\n      Classical.byContradiction (fun hn => hne ⟨t, ht, hn⟩)\n    have noy : ∀ h, ¬ y h := by\n      intro h H\n      exact ((hy h).1 H).1 ((PB_iff c x h).2 (fun g h1 h2 => allx g (by omega)))\n    have := allx (b + a + 1) (by omega)\n    have hb := ((hx _).1 this).2\n    exact noy (b + a) ((PB_iff b y _).1 hb (b + a) (by omega) (by omega))\n  rcases ex with ⟨t, hat, hnt⟩\n  refine ⟨t + d + 1, fun h hh => ⟨Xmono t hat hnt h (by omega), ?_⟩⟩\n  intro H\n  exact Xmono t hat hnt (t + d) (by omega) ((PB_iff d x h).1 ((hy h).1 H).2 (t + d) (by omega) (by omega))\n\n/-- Hobson bot vs graded FairBot Prov_c(p): eventually mutual action 2. -/\ntheorem hob_fair (a b c : Nat) (x y : Nat → Prop)\n    (hx : ∀ h, x h ↔ Hob a b y h) (hy : ∀ h, y h ↔ PB c x h) :\n    ∃ T, ∀ h, T ≤ h → ¬ x h ∧ ¬ y h := by\n  have Ymono : ∀ t, ¬ y t → ∀ h, t ≤ h → ¬ y h := by\n    intro t hnt h hth H; apply hnt\n    exact (hy t).2 ((PB_iff c x t).2 (fun g h1 h2 => (PB_iff c x h).1 ((hy h).1 H) g h1 (by omega)))\n  have ex : ∃ t, ¬ y t := by\n    apply Classical.byContradiction; intro hne\n    have ally : ∀ t, y t := fun t => Classical.byContradiction (fun hn => hne ⟨t, hn⟩)\n    have nox : ∀ h, ¬ x h := fun h H =>\n      ((hx h).1 H).1 ((PB_iff a y h).2 (fun g _ _ => ally g))\n    exact nox c ((PB_iff c x (c+1)).1 ((hy _).1 (ally (c+1))) c (Nat.le_refl c) (by omega))\n  rcases ex with ⟨t, hnt⟩\n  have Xlate : ∀ h, t + b < h → ¬ x h := fun h hh H =>\n    Ymono t hnt (t + b) (by omega) ((PB_iff b y h).1 ((hx h).1 H).2 (t + b) (by omega) hh)\n  refine ⟨t + b + c + 2, fun h hh => ⟨Xlate h (by omega), ?_⟩⟩\n  intro H\n  exact Xlate (t + b + c + 1) (by omega) ((PB_iff c x h).1 ((hy h).1 H) (t + b + c + 1) (by omega) (by omega))\n\n\n/-- Any distinct weak grades, either order. -/\ntheorem hob_tail (a b c d : Nat) (hac : a ≠ c) (x y : Nat → Prop)\n    (hx : ∀ h, x h ↔ Hob a b y h) (hy : ∀ h, y h ↔ Hob c d x h) :\n    ∃ T, ∀ h, T ≤ h → ¬ x h ∧ ¬ y h := by\n  rcases Nat.lt_or_gt_of_ne hac with h1 | h1\n  · exact hob_neq a b c d h1 x y hx hy\n  · rcases hob_neq c d a b h1 y x hy hx with ⟨T, hT⟩\n    exact ⟨T, fun h hh => ⟨(hT h hh).2, (hT h hh).1⟩⟩\n\n#print axioms hob_eq\n#print axioms hob_tail\n#print axioms hob_neq\n#print axioms hob_fair\n"
def lean():
    for c in (shutil.which('lean'), '/opt/elan/bin/lean', os.path.expanduser('~/.elan/bin/lean')):
        if c and os.path.exists(c): return c
    raise AssertionError('lean binary not found')
def run_lean(src):
    r = subprocess.run([lean(), '--stdin'], input=src, capture_output=True, text=True, timeout=100)
    return r.returncode, r.stdout + r.stderr
rc, out = run_lean(LEAN_SRC)
assert rc == 0, out
assert 'sorryAx' not in out and 'error' not in out, out
for t in ('hob_eq', 'hob_tail', 'hob_fair'):
    assert "'%s' depends on axioms: [propext, Classical.choice, Quot.sound]" % t in out or \
           "'%s' depends on axioms: [propext, Quot.sound, Classical.choice]" % t in out, (t, out)
# negative controls: false strengthenings must fail
bad1 = LEAN_SRC.replace("∀ h, (x h ↔ a < h) ∧ (y h ↔ a < h)", "∀ h, (x h ↔ a ≤ h) ∧ (y h ↔ a < h)")
bad2 = LEAN_SRC.replace("refine ⟨t + d + 1,", "refine ⟨0,")
for b in (bad1, bad2):
    assert b != LEAN_SRC
    rc2, out2 = run_lean(b)
    assert rc2 != 0, 'false variant accepted'
print('Lean: hob_eq, hob_tail, hob_fair proved; 2 false variants rejected')

def P(a, z, h): return all(z[g] for g in range(a, h))
def run(A, B, HH=80):
    x, y = [], []
    for h in range(HH):
        x.append(A(x, y, h)); y.append(B(y, x, h))
    return x, y
def Hb(a, b): return lambda own, opp, h: (not P(a, opp, h)) and P(b, opp, h)
def Fc(c): return lambda own, opp, h: P(c, opp, h)
N = 12; cells = 0
for a in range(N):
    for b in range(a + 1, N + 1):
        for c in range(N):
            for d in range(c + 1, N + 1):
                x, y = run(Hb(a, b), Hb(c, d))
                assert x[-20:] == [x[-1]] * 20 and y[-20:] == [y[-1]] * 20
                assert (x[-1], y[-1]) == (a == c, a == c), (a, b, c, d)
                if a == c:
                    assert all(x[h] == (h > a) and y[h] == (h > a) for h in range(80))
                cells += 1
        for c in range(N + 1):
            x, y = run(Hb(a, b), Fc(c))
            assert x[-20:] == [x[-1]] * 20 and y[-20:] == [y[-1]] * 20
            assert (x[-1], y[-1]) == (False, False), (a, b, c)
            cells += 1
assert cells == 78 * 78 + 78 * 13, cells
print('recurrence cells', cells)
print('PASS')
