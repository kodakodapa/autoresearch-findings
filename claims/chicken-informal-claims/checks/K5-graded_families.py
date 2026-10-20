"""All-index graded CarefulBot/BoldBot height laws, Lean 4 core.
Inputs are all natural indices and heights. No external data or Python packages.
PB n p h = forall g<h, g<n or p(g), equivalent to box(box^n False or p).
Theorems hold for every solution of the simultaneous height equations.
"""
import subprocess, shutil, os
LEAN_SRC = '/- Height semantics of closed GL fixed points on the chain 0<1<2<...:\n   a world of height h sees exactly heights g<h, so box phi holds at h iff phi holds at all g<h.\n   Gate agent W_n(X) = box( box^n False  or  (p and (q or not box q)) ),\n   p = "X cooperates with W_n", q = "X cooperates with DefectBot". W_2 is K6\'s W (size 12).\n   gate n p q is the formula under the outer box; W_n\'s action is bx (gate n p q). -/\n\ndef bx (φ : Nat → Prop) : Nat → Prop := fun h => ∀ g, g < h → φ g\ndef bxn : Nat → (Nat → Prop) → (Nat → Prop)\n  | 0, φ => φ\n  | n+1, φ => bx (bxn n φ)\n\ntheorem bxn_succ_iff (n : Nat) (φ : Nat → Prop) (h : Nat) :\n    bxn (n+1) φ h ↔ ∀ g, g + (n+1) ≤ h → φ g := by\n  induction n generalizing h with\n  | zero =>\n    simp only [bxn, bx]\n    exact ⟨fun H g hg => H g (by omega), fun H g hg => H g (by omega)⟩\n  | succ n ih =>\n    show bx (bxn (n+1) φ) h ↔ _\n    simp only [bx]\n    constructor\n    · intro H g hg\n      exact (ih (h-1)).1 (H (h-1) (by omega)) g (by omega)\n    · intro H g\' hg\'\n      exact (ih g\').2 (fun g hg => H g (by omega))\n\ntheorem bxn_iff (n : Nat) (hn : 1 ≤ n) (φ : Nat → Prop) (h : Nat) :\n    bxn n φ h ↔ ∀ g, g + n ≤ h → φ g := by\n  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩\n  exact bxn_succ_iff m φ h\n\ndef botn (n : Nat) : Nat → Prop := bxn n (fun _ => False)\n\ntheorem botn_iff (n h : Nat) : botn n h ↔ h < n := by\n  cases n with\n  | zero => simp [botn, bxn]\n  | succ m =>\n    unfold botn; rw [bxn_succ_iff]\n    constructor\n    · intro H; apply Classical.byContradiction; intro hn\n      exact H 0 (by omega)\n    · intro hlt g hg; omega\n\n\ndef PB (n : Nat) (p : Nat → Prop) (h : Nat) : Prop :=\n  ∀ g, g < h → (g < n ∨ p g)\n\ntheorem bold_step (n m h : Nat) (y : Nat → Prop)\n    (ih : ∀ g, g < h → (y g ↔ g ≤ m ∨ n < m)) :\n    PB n (fun g => ¬ y g) h ↔ h ≤ n ∨ m < n := by\n  constructor\n  · intro hb\n    by_cases hn : h ≤ n\n    · exact Or.inl hn\n    · have hn\' : n < h := by omega\n      have hy := hb n hn\'\n      rcases hy with bad | ny\n      · omega\n      · have nm : ¬ n ≤ m := fun le => ny ((ih n hn\').2 (Or.inl le))\n        exact Or.inr (by omega)\n  · intro hh g gh\n    by_cases gn : g < n\n    · exact Or.inl gn\n    · right\n      intro yg\n      have yy := (ih g gh).1 yg\n      omega\n\ntheorem bold_all (n m : Nat) (x y : Nat → Prop)\n    (hx : ∀ h, x h ↔ PB n (fun g => ¬ y g) h)\n    (hy : ∀ h, y h ↔ PB m (fun g => ¬ x g) h) :\n    ∀ h, (x h ↔ h ≤ n ∨ m < n) ∧ (y h ↔ h ≤ m ∨ n < m) := by\n  intro h\n  induction h using Nat.strongRecOn with\n  | ind h ih =>\n    exact ⟨(hx h).trans (bold_step n m h y (fun g gh => (ih g gh).2)),\n      (hy h).trans (bold_step m n h x (fun g gh => (ih g gh).1))⟩\n\ntheorem careful_all (n m : Nat) (x y : Nat → Prop)\n    (hx : ∀ h, x h ↔ ¬ PB n y h)\n    (hy : ∀ h, y h ↔ ¬ PB m x h) :\n    ∀ h, (x h ↔ n < h ∧ n ≤ m) ∧ (y h ↔ m < h ∧ m ≤ n) := by\n  classical\n  have hnx : ∀ h, (¬ x h) ↔ PB n (fun g => ¬ ¬ y g) h := by\n    intro h\n    simp only [Classical.not_not]\n    exact not_congr (hx h) |>.trans (Classical.not_not)\n  have hny : ∀ h, (¬ y h) ↔ PB m (fun g => ¬ ¬ x g) h := by\n    intro h\n    simp only [Classical.not_not]\n    exact not_congr (hy h) |>.trans (Classical.not_not)\n  intro h\n  have hh := bold_all n m (fun g => ¬ x g) (fun g => ¬ y g) hnx hny h\n  constructor\n  · have := not_congr hh.1\n    simp only [Classical.not_not] at this\n    constructor\n    · intro xh\n      have := this.mp xh\n      omega\n    · intro cond\n      apply this.mpr\n      omega\n  · have := not_congr hh.2\n    simp only [Classical.not_not] at this\n    constructor\n    · intro yh\n      have := this.mp yh\n      omega\n    · intro cond\n      apply this.mpr\n      omega\n\n#print axioms bold_all\n#print axioms careful_all\n\n\ntheorem prov_bridge (n : Nat) (p : Nat → Prop) (h : Nat) :\n    bx (fun g => botn n g ∨ p g) h ↔ PB n p h := by\n  simp only [bx, PB, botn_iff]\n\n#print axioms prov_bridge\n'
lean = shutil.which('lean') or '/opt/elan/bin/lean'
assert os.path.isfile(lean), 'Lean toolchain required'
def run(source):
    return subprocess.run([lean, '--stdin'], input=source, text=True, capture_output=True, timeout=50)
r = run(LEAN_SRC)
assert r.returncode == 0, r.stdout+r.stderr
assert 'sorryAx' not in r.stdout and 'error' not in r.stdout.lower(), r.stdout
assert r.stdout.count('depends on axioms') == 3, r.stdout
# Mutation control: reversed strict tie behavior must not be accepted.
bad = LEAN_SRC.replace('h ≤ n ∨ m < n', 'h ≤ n ∨ m ≤ n')
r_bad = run(bad)
assert r_bad.returncode != 0, 'false tie law accepted'
# Independent finite recurrence audit: simultaneous updates use earlier heights only.
for n in range(16):
    for m in range(16):
        for careful in [False,True]:
            x,y=[],[]
            for h in range(40):
                if careful:
                    a=not all(g<n or y[g] for g in range(h))
                    b=not all(g<m or x[g] for g in range(h))
                    expected=(n<h and n<=m,m<h and m<=n)
                else:
                    a=all(g<n or not y[g] for g in range(h))
                    b=all(g<m or not x[g] for g in range(h))
                    expected=(h<=n or m<n,h<=m or n<m)
                assert (a,b)==expected,(n,m,h,careful)
                x.append(a);y.append(b)
print('PASS: all-index Lean laws, boxed-formula bridge, negative control, 20480 recurrence cells')
