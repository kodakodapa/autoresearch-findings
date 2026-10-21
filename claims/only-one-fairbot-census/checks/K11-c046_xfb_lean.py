"""C046 r1: Lean 4 core proof that X = [](p | (q & []F)) (size 7) behaves exactly like FairBot []p.
Height semantics: []phi at h iff phi at all g < h; p = opponent's move against me, q = opponent's
move against DefectBot (the opponent's DefectBot trace). The opponent is ANY causal operator on
(my moves, my DefectBot trace): its move at h depends only on inputs below h. X differs from
FairBot only on inputs with p(0)=F, q(0)=T, which no opponent produces: its height-0 move is the same
against every agent and against DefectBot. Theorem X_same_as_FairBot: in any fixed point of X vs Op
and any fixed point of FairBot vs Op, all moves coincide at every height. Bridge assumed (standard,
as in prior runs): modal game fixed points are letter-free, so play is the height-chain trace.
Negative controls: three mutations must be rejected by Lean.
"""
import subprocess, shutil, os, hashlib
LEAN = "-- Height semantics; opponent = any causal operator on (my moves, my DefectBot trace).\ndef Causal (Op : (Nat → Prop) → (Nat → Prop) → Nat → Prop) : Prop :=\n  ∀ x x' y y' h, (∀ g, g < h → ((x g ↔ x' g) ∧ (y g ↔ y' g))) → (Op x y h ↔ Op x' y' h)\n\n-- X = box (p ∨ (q ∧ box ⊥)),  FairBot = box p\ndef Xop (p q : Nat → Prop) (h : Nat) : Prop := ∀ g, g < h → (p g ∨ (q g ∧ g = 0))\ndef FBop (p : Nat → Prop) (h : Nat) : Prop := ∀ g, g < h → p g\n\ntheorem db_trace_same (h : Nat) : Xop (fun _ => False) (fun _ => False) h ↔ FBop (fun _ => False) h := by\n  unfold Xop FBop\n  constructor\n  · intro H g hg; rcases H g hg with h1 | ⟨h2, _⟩ <;> assumption\n  · intro H g hg; exact Or.inl (H g hg)\n\ntheorem opp_first_move (Op : (Nat → Prop) → (Nat → Prop) → Nat → Prop) (hc : Causal Op)\n    (x y : Nat → Prop) : Op x y 0 ↔ Op (fun _ => False) (fun _ => False) 0 :=\n  hc _ _ _ _ 0 (fun g hg => absurd hg (Nat.not_lt_zero g))\n\n/-- In any fixed point of X vs Op and any fixed point of FairBot vs Op, both agents and the\nopponent make the same move at every height. -/\ntheorem X_same_as_FairBot (Op : (Nat → Prop) → (Nat → Prop) → Nat → Prop) (hc : Causal Op)\n    (a b a' b' : Nat → Prop)\n    (ha : ∀ h, a h ↔ Xop b (Op (fun _ => False) (fun _ => False)) h)\n    (hb : ∀ h, b h ↔ Op a (Xop (fun _ => False) (fun _ => False)) h)\n    (ha' : ∀ h, a' h ↔ FBop b' h)\n    (hb' : ∀ h, b' h ↔ Op a' (FBop (fun _ => False)) h) :\n    ∀ h, (a h ↔ a' h) ∧ (b h ↔ b' h) := by\n  have hb0 : Op (fun _ => False) (fun _ => False) 0 → b 0 := fun d =>\n    (hb 0).2 ((opp_first_move Op hc _ _).2 d)\n  have P : ∀ n, ∀ g, g < n → ((a g ↔ a' g) ∧ (b g ↔ b' g)) := by\n    intro n\n    induction n with\n    | zero => intro g hg; exact absurd hg (Nat.not_lt_zero g)\n    | succ n ih =>\n      intro g hg\n      rcases Nat.lt_succ_iff_lt_or_eq.mp hg with hlt | heq\n      · exact ih g hlt\n      · subst heq\n        have hbb : b g ↔ b' g := by\n          rw [hb g, hb' g]\n          exact hc _ _ _ _ g (fun k hk => ⟨(ih k hk).1, db_trace_same k⟩)\n        refine ⟨?_, hbb⟩\n        rw [ha g, ha' g]\n        unfold Xop FBop\n        constructor\n        · intro H k hk\n          rcases H k hk with h1 | ⟨h2, h3⟩\n          · exact ((ih k hk).2).1 h1\n          · subst h3; exact ((ih 0 hk).2).1 (hb0 h2)\n        · intro H k hk\n          exact Or.inl (((ih k hk).2).2 (H k hk))\n  intro h\n  exact P (h+1) h (Nat.lt_succ_self h)\n\n#print axioms X_same_as_FairBot\n"
assert hashlib.sha256(LEAN.encode()).hexdigest() == '4fd5852537bb7529273a6896b72529ff9457ed349e41afea8e3dffb8aa9a7171'
binary = next((p for p in (shutil.which('lean'), '/opt/elan/bin/lean', os.path.expanduser('~/.elan/bin/lean')) if p and os.path.exists(p)), None)
assert binary, 'lean missing'
def run(src):
    return subprocess.run([binary, '--stdin'], input=src, text=True, capture_output=True, timeout=100)
r = run(LEAN)
assert r.returncode == 0, r.stdout + r.stderr
assert 'sorryAx' not in r.stdout and "'X_same_as_FairBot' depends on axioms" in r.stdout, r.stdout
mutations = [
    ("(p g ∨ (q g ∧ g = 0))", "(p g ∨ (q g ∧ g = 1))"),
    ("(p g ∨ (q g ∧ g = 0))", "(p g ∨ q g)"),
    ("(∀ g, g < h → ((x g ↔ x' g)", "(∀ g, g ≤ h → ((x g ↔ x' g)"),
]
for a, b in mutations:
    assert LEAN.count(a) == 1, a
    m = run(LEAN.replace(a, b))
    assert m.returncode != 0, ('mutation accepted', b)
print('PASS: X_same_as_FairBot proved (no sorry); 3 mutations rejected')
