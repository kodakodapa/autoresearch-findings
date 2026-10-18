"""C046 r1: Lean proof that PrudentBot_j and FairBot_k cooperate iff k <= j, for ALL j>=0, k>=1.
Semantics: closed GL fixed points are letter-free, so on the height chain box(phi) holds at h
iff phi holds at every g<h (Boolos, Logic of Provability ch. 7). F_k(X)=box^k(X coops F_k);
P_j(X)=box(X coops P_j) & box(~box^j F -> ~(X coops DB)).  The Lean theorem holds for ANY
x,y,q satisfying the height equations, so no uniqueness assumption is used.
This script: (1) runs the embedded Lean source with `lean --stdin`, asserts success and that no
theorem depends on sorryAx; (2) negative control: a false variant (cooperation when j<k) must be
rejected by Lean; (3) re-solves P_j vs F_k for j,k<=8 with an explicit height table and checks
the theorem's predictions (cooperate everywhere iff k<=j; else both defect above j+k, exact threshold).
"""
import subprocess, shutil, os
LEAN_SRC = '/- Height semantics of closed GL fixed points on the chain 0<1<2<...:\n   a world of height h sees exactly heights g<h, so box phi holds at h iff phi holds at all g<h.\n   FairBot_k:  F_k(X)  = box^k (X coops F_k)\n   PrudentBot_j: P_j(X) = box (X coops P_j) and box (not box^j False -> not (X coops DB))\n   Here x h = "P_j cooperates with F_k at height h", y h = "F_k cooperates with P_j",\n   q h = "F_k cooperates with DefectBot" (the q-atom P_j reads). -/\n\ndef bx (φ : Nat → Prop) : Nat → Prop := fun h => ∀ g, g < h → φ g\ndef bxn : Nat → (Nat → Prop) → (Nat → Prop)\n  | 0, φ => φ\n  | n+1, φ => bx (bxn n φ)\n\ntheorem bxn_succ_iff (n : Nat) (φ : Nat → Prop) (h : Nat) :\n    bxn (n+1) φ h ↔ ∀ g, g + (n+1) ≤ h → φ g := by\n  induction n generalizing h with\n  | zero =>\n    simp only [bxn, bx]\n    exact ⟨fun H g hg => H g (by omega), fun H g hg => H g (by omega)⟩\n  | succ n ih =>\n    show bx (bxn (n+1) φ) h ↔ _\n    simp only [bx]\n    constructor\n    · intro H g hg\n      exact (ih (h-1)).1 (H (h-1) (by omega)) g (by omega)\n    · intro H g\' hg\'\n      exact (ih g\').2 (fun g hg => H g (by omega))\n\ntheorem bxn_iff (n : Nat) (hn : 1 ≤ n) (φ : Nat → Prop) (h : Nat) :\n    bxn n φ h ↔ ∀ g, g + n ≤ h → φ g := by\n  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩\n  exact bxn_succ_iff m φ h\n\ndef botn (n : Nat) : Nat → Prop := bxn n (fun _ => False)\n\ntheorem botn_iff (n h : Nat) : botn n h ↔ h < n := by\n  cases n with\n  | zero => simp [botn, bxn]\n  | succ m =>\n    unfold botn; rw [bxn_succ_iff]\n    constructor\n    · intro H; apply Classical.byContradiction; intro hn\n      exact H 0 (by omega)\n    · intro hlt g hg; omega\n\n/-- Main theorem: for all j,k >= 1, P_j and F_k cooperate at every height when k <= j,\n    and both defect at every height above j+k when j < k. Holds for ANY x,y,q satisfying\n    the fixed-point equations (uniqueness is not needed). -/\ntheorem pj_fk (j k : Nat) (hk : 1 ≤ k) (x y q : Nat → Prop)\n    (hq : ∀ h, q h ↔ bxn k (fun _ => False) h)\n    (hx : ∀ h, x h ↔ (bx y h ∧ bx (fun g => ¬ botn j g → ¬ q g) h))\n    (hy : ∀ h, y h ↔ bxn k x h) :\n    (k ≤ j → ∀ h, x h ∧ y h) ∧ (j < k → ∀ h, j + k < h → ¬ x h ∧ ¬ y h) := by\n  have hq\' : ∀ g, q g ↔ g < k := fun g => by rw [hq]; exact botn_iff k g\n  constructor\n  · intro hkj\n    have guard : ∀ h, bx (fun g => ¬ botn j g → ¬ q g) h := by\n      intro h g _ hnb hqg\n      rw [botn_iff] at hnb; rw [hq\'] at hqg; omega\n    have key : ∀ n, ∀ h, h ≤ n → x h ∧ y h := by\n      intro n\n      induction n with\n      | zero =>\n        intro h hh\n        have h0 : h = 0 := by omega\n        subst h0\n        have x0 : x 0 := (hx 0).2 ⟨fun g hg => absurd hg (Nat.not_lt_zero _), guard 0⟩\n        refine ⟨x0, (hy 0).2 ((bxn_iff k hk x 0).2 ?_)⟩\n        intro g hg; have : g = 0 := by omega\n        subst this; exact x0\n      | succ n ih =>\n        intro h hh\n        by_cases hle : h ≤ n\n        · exact ih h hle\n        · have xh : x h := (hx h).2 ⟨fun g hg => (ih g (by omega)).2, guard h⟩\n          refine ⟨xh, (hy h).2 ((bxn_iff k hk x h).2 ?_)⟩\n          intro g hg\n          by_cases hgn : g ≤ n\n          · exact (ih g hgn).1\n          · have : g = h := by omega\n            subst this; exact xh\n    exact fun h => key h h (Nat.le_refl _)\n  · intro hjk\n    have nx : ∀ h, j < h → ¬ x h := by\n      intro h hjh hxh\n      have := ((hx h).1 hxh).2 j hjh\n      apply this\n      · rw [botn_iff]; omega\n      · rw [hq\']; exact hjk\n    intro h hh\n    refine ⟨nx h (by omega), ?_⟩\n    intro hyh\n    have := (bxn_iff k hk x h).1 ((hy h).1 hyh) (j+1) (by omega)\n    exact nx (j+1) (by omega) this\n\n/-- P_j defects against CooperateBot (q is constantly true) for every j. -/\ntheorem pj_cb (j : Nat) (x q : Nat → Prop) (hq : ∀ h, q h)\n    (hx : ∀ h, x h ↔ (bx (fun _ => True) h ∧ bx (fun g => ¬ botn j g → ¬ q g) h)) :\n    ∀ h, j < h → ¬ x h := by\n  intro h hjh hxh\n  exact ((hx h).1 hxh).2 j hjh (by rw [botn_iff]; omega) (hq j)\n\n#print axioms pj_fk\n#print axioms pj_cb\n'
def lean():
    for c in (shutil.which('lean'), '/opt/elan/bin/lean', os.path.expanduser('~/.elan/bin/lean')):
        if c and os.path.exists(c): return c
    raise AssertionError('lean binary not found')
def run(src):
    r = subprocess.run([lean(), '--stdin'], input=src, capture_output=True, text=True, timeout=100)
    return r.returncode, r.stdout + r.stderr
code, out = run(LEAN_SRC)
assert code == 0, out
assert 'sorry' not in out and "error" not in out.lower(), out
assert out.count('depends on axioms') == 2 and 'sorryAx' not in out, out
bad = LEAN_SRC.replace('(k \u2264 j \u2192 \u2200 h, x h \u2227 y h)', '(j < k \u2192 \u2200 h, x h \u2227 y h)')
assert bad != LEAN_SRC
code2, out2 = run(bad)
assert code2 != 0, 'negative control was accepted'
def play(j, k, H=40):
    x, y = [], []
    for h in range(H):
        q = lambda g: g < k                    # F_k vs DB = box^k F: true iff height < k
        botj = lambda g: g < j                 # box^j F at g
        x.append(all(y[g] for g in range(h)) and all(botj(g) or not q(g) for g in range(h)))
        y.append(all(x[g] for g in range(h - k + 1)))
    return x, y
for j in range(0, 9):
    for k in range(1, 9):
        x, y = play(j, k)
        if k <= j: assert all(x) and all(y), (j, k)
        else:
            assert not any(x[j+k+1:]) and not any(y[j+k+1:]), (j, k)
            assert y[j+k] and x[j], (j, k)       # threshold is exact
print('PASS Lean proof of P_j/F_k for all j,k; negative control rejected; table j<=8,k<=8 agrees')
