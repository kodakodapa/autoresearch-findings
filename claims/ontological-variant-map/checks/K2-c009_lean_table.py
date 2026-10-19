"""C009 table proofs (Lean 4 core, no Mathlib, lean --stdin). Full-property constant-domain shallow
embedding (as in c009_calib_scott.py; Scott essence essS = phi(x) and Goedel's clause).
Key lemma haec_ess: the haecceity (y = x and u = v) is a Scott essence of x at v, so NE_isolated:
an NE-being at v sees only v. Hence, using no A3/A4:
A125_isolated_succ (any frame, A1 A2 A5): every world sees a world v with R v u <-> u = v;
A125_sym_iso / A125_sym_collapse (symmetric frames, A1 A2 A5): R w v <-> v = w, modal collapse;
A1235_sym_god (symmetric, A1 A2 A3 A5, no A4): G-like being at every world and box-exists-G;
A1235_euclid_box (euclidean, A1 A2 A3 A5, no A4): box-exists-G at every world;
majority_model: one reflexive world, three individuals, Pos = majority: A1 A2 A4 A5 hold and no
G-like being exists (A3 cannot be dropped). Also contains the calibration theorems.
Asserts lean exit 0, no sorry, no axiom decls, every #print axioms within
{propext, Classical.choice, Quot.sound}; the explicit models use no axioms (majority: only std)."""
import os, re, shutil, subprocess
LEAN = r"""/-
Shallow embedding of higher-order modal logic in Lean 4 core (no Mathlib).
Worlds: a type W. Accessibility: R : W → W → Prop. Constant (possibilist)
domain: a type D, the same at every world. Properties: D → W → Prop
(all intensional properties, no restriction). Positivity: world-dependent
Pos : (D → W → Prop) → W → Prop. Axioms are hypotheses, never `axiom`s.
-/
namespace Onto

variable {W D : Type}

abbrev Prp (W D : Type) := D → W → Prop

def box (R : W → W → Prop) (p : W → Prop) (w : W) : Prop := ∀ v, R w v → p v
def neg (φ : Prp W D) : Prp W D := fun x w => ¬ φ x w
/-- box ∀x (φ x → ψ x), evaluated at w -/
def entails (R : W → W → Prop) (φ ψ : Prp W D) (w : W) : Prop :=
  ∀ v, R w v → ∀ x, φ x v → ψ x v
/-- Gödel 1970 essence: no φ(x) conjunct -/
def essG (R : W → W → Prop) (φ : Prp W D) (x : D) (w : W) : Prop :=
  ∀ ψ : Prp W D, ψ x w → entails R φ ψ w
/-- Scott's essence: φ(x) ∧ Gödel's clause -/
def essS (R : W → W → Prop) (φ : Prp W D) (x : D) (w : W) : Prop :=
  φ x w ∧ essG R φ x w
/-- necessary existence relative to an essence notion -/
def NE (R : W → W → Prop) (ess : Prp W D → D → W → Prop) : Prp W D :=
  fun x w => ∀ φ, ess φ x w → ∀ v, R w v → ∃ y, φ y v
def God (Pos : Prp W D → W → Prop) : Prp W D := fun x w => ∀ φ, Pos φ w → φ x w

def A1 (Pos : Prp W D → W → Prop) : Prop := ∀ φ w, Pos (neg φ) w ↔ ¬ Pos φ w
def A2 (R : W → W → Prop) (Pos : Prp W D → W → Prop) : Prop :=
  ∀ φ ψ w, Pos φ w → entails R φ ψ w → Pos ψ w
def A3 (Pos : Prp W D → W → Prop) : Prop := ∀ w, Pos (God Pos) w
def A4 (R : W → W → Prop) (Pos : Prp W D → W → Prop) : Prop :=
  ∀ φ w, Pos φ w → box R (Pos φ) w
def A5 (R : W → W → Prop) (Pos : Prp W D → W → Prop) (ess : Prp W D → D → W → Prop) : Prop :=
  ∀ w, Pos (NE R ess) w

/-! ## Q1: Gödel's 1970 essence makes A1, A2, A5 unsatisfiable on every frame -/

/-- At a dead-end world A1 and A2 already clash (any frame, any essence). -/
theorem deadend_clash {R : W → W → Prop} {Pos : Prp W D → W → Prop}
    (h1 : A1 Pos) (h2 : A2 R Pos) (w : W) (hd : ∀ v, ¬ R w v) : False := by
  let φ : Prp W D := fun _ _ => True
  have vac : ∀ χ ψ : Prp W D, entails R χ ψ w := fun _ _ v hv => absurd hv (hd v)
  by_cases hp : Pos φ w
  · exact (h1 φ w).mp (h2 φ (neg φ) w hp (vac _ _)) hp
  · exact hp (h2 (neg φ) φ w ((h1 φ w).mpr hp) (vac _ _))

/-- The empty property is a Gödel essence of every individual. -/
theorem empty_essG (R : W → W → Prop) (x : D) (w : W) :
    essG R (fun _ _ => False) x w := fun _ _ _ _ _ h => False.elim h

/-- At a world with a successor, nothing has Gödel-NE. -/
theorem NE_essG_empty (R : W → W → Prop) (u : W) (hs : ∃ v, R u v) (x : D) :
    ¬ NE R (essG R) x u := by
  intro h
  obtain ⟨v, hv⟩ := hs
  obtain ⟨_, hy⟩ := h _ (empty_essG R x u) v hv
  exact hy

theorem godel1970_inconsistent {R : W → W → Prop} {Pos : Prp W D → W → Prop}
    (h1 : A1 Pos) (h2 : A2 R Pos) (h5 : A5 R Pos (essG R)) (w : W) : False := by
  by_cases hs : ∀ u, R w u → ∃ v, R u v
  · let N : Prp W D := NE R (essG R)
    have hent : entails R N (neg N) w :=
      fun u hu x hx => absurd hx (NE_essG_empty R u (hs u hu) x)
    exact (h1 _ w).mp (h2 _ _ w (h5 w) hent) (h5 w)
  · apply Classical.byContradiction
    intro _
    apply hs
    intro u hu
    apply Classical.byContradiction
    intro hn
    exact deadend_clash h1 h2 u (fun v hv => hn ⟨v, hv⟩)

/-- Unsatisfiable on all frames: any model has no worlds. -/
theorem godel1970_no_model (W D : Type) (R : W → W → Prop) (Pos : Prp W D → W → Prop)
    (h1 : A1 Pos) (h2 : A2 R Pos) (h5 : A5 R Pos (essG R)) : ¬ Nonempty W :=
  fun ⟨w⟩ => godel1970_inconsistent h1 h2 h5 w

/-! ## Q2: Scott's variant -/

section Scott
variable {R : W → W → Prop} {Pos : Prp W D → W → Prop}

/-- T1: positive properties are possibly exemplified (any frame). -/
theorem T1 (h1 : A1 Pos) (h2 : A2 R Pos) {φ : Prp W D} {w : W} (hp : Pos φ w) :
    ∃ v, R w v ∧ ∃ x, φ x v := by
  apply Classical.byContradiction
  intro hn
  have hent : entails R φ (neg φ) w := fun v hv x hx _ => hn ⟨v, hv, x, hx⟩
  exact (h1 φ w).mp (h2 _ _ w hp hent) hp

/-- T2: being God-like is a (Scott) essence of any God-like being (any frame). -/
theorem T2 (h1 : A1 Pos) (h4 : A4 R Pos) {x : D} {w : W} (hg : God Pos x w) :
    essS R (God Pos) x w := by
  refine ⟨hg, fun ψ hψ v hv y hgy => ?_⟩
  by_cases hP : Pos ψ w
  · exact hgy ψ (h4 ψ w hP v hv)
  · exact absurd hψ (hg _ ((h1 ψ w).mpr hP))

/-- Any frame: A1+A2 force seriality. -/
theorem scott_serial (h1 : A1 Pos) (h2 : A2 R Pos) (w : W) : ∃ v, R w v :=
  Classical.byContradiction fun hn => deadend_clash h1 h2 w (fun v hv => hn ⟨v, hv⟩)

/-! ## Round 5: any frame, symmetric frames, an S4 countermodel -/

/-- Any frame (A1, A4, A5): a God-like being at w makes ∃G necessary at w. -/
theorem god_box_god (h1 : A1 Pos) (h4 : A4 R Pos) (h5 : A5 R Pos (essS R))
    {x : D} {w : W} (hg : God Pos x w) : box R (fun u => ∃ y, God Pos y u) w :=
  fun u hu => (hg _ (h5 w)) (God Pos) (T2 h1 h4 hg) u hu

/-- Any frame (A1, A2, A4, A5): a world with a God-like being sees exactly itself. -/
theorem god_world_isolated (h1 : A1 Pos) (h2 : A2 R Pos) (h4 : A4 R Pos)
    (h5 : A5 R Pos (essS R)) {x : D} {w : W} (hg : God Pos x w) (v : W) :
    R w v ↔ v = w := by
  have iso : ∀ u, R w u → u = w := fun u hu => by
    obtain ⟨y, hy⟩ := god_box_god h1 h4 h5 hg u hu
    exact (T2 h1 h4 hg).2 (fun _ t => t = w) rfl u hu y hy
  constructor
  · exact iso v
  · intro hv; subst hv
    obtain ⟨u, hu⟩ := scott_serial h1 h2 v
    exact (iso u hu) ▸ hu

/-- Any frame: modal collapse at every world that has a God-like being. -/
theorem god_world_collapse (h1 : A1 Pos) (h2 : A2 R Pos) (h4 : A4 R Pos)
    (h5 : A5 R Pos (essS R)) {x : D} {w : W} (hg : God Pos x w)
    (Q : W → Prop) (hQ : Q w) : box R Q w :=
  fun v hv => ((god_world_isolated h1 h2 h4 h5 hg v).mp hv) ▸ hQ

/-- Any frame (A1–A3): possibly a God-like being exists. -/
theorem possibly_god (h1 : A1 Pos) (h2 : A2 R Pos) (h3 : A3 Pos) (w : W) :
    ∃ v, R w v ∧ ∃ x, God Pos x v := T1 h1 h2 (h3 w)

/-- Symmetric frames (no reflexivity or transitivity assumed): A1–A5 give a
    God-like being at every world, and every world sees exactly itself. -/
theorem scott_symmetric (hsym : ∀ a b, R a b → R b a)
    (h1 : A1 Pos) (h2 : A2 R Pos) (h3 : A3 Pos) (h4 : A4 R Pos) (h5 : A5 R Pos (essS R))
    (w : W) : (∃ x, God Pos x w) ∧ ∀ v, R w v ↔ v = w := by
  obtain ⟨v, hv, x, hx⟩ := possibly_god h1 h2 h3 w
  have hwv : w = v := (god_world_isolated h1 h2 h4 h5 hx w).mp (hsym w v hv)
  subst hwv
  exact ⟨⟨x, hx⟩, god_world_isolated h1 h2 h4 h5 hx⟩


/-- Symmetric frames: □∃G at every world. -/
theorem scott_symmetric_box (hsym : ∀ a b, R a b → R b a)
    (h1 : A1 Pos) (h2 : A2 R Pos) (h3 : A3 Pos) (h4 : A4 R Pos) (h5 : A5 R Pos (essS R))
    (w : W) : box R (fun u => ∃ y, God Pos y u) w :=
  fun u _ => (scott_symmetric hsym h1 h2 h3 h4 h5 u).1

/-- Symmetric frames: modal collapse at every world. -/
theorem scott_symmetric_collapse (hsym : ∀ a b, R a b → R b a)
    (h1 : A1 Pos) (h2 : A2 R Pos) (h3 : A3 Pos) (h4 : A4 R Pos) (h5 : A5 R Pos (essS R))
    (Q : W → Prop) (w : W) (hQ : Q w) : box R Q w :=
  fun v hv => (((scott_symmetric hsym h1 h2 h3 h4 h5 w).2 v).mp hv) ▸ hQ

/-- Euclidean frames (K5, KD45, S5): □∃G at every world. -/
theorem T3_euclid (heuc : ∀ a b c, R a b → R a c → R b c)
    (h1 : A1 Pos) (h2 : A2 R Pos) (h3 : A3 Pos) (h4 : A4 R Pos) (h5 : A5 R Pos (essS R))
    (w : W) : box R (fun u => ∃ y, God Pos y u) w := by
  intro u hu
  obtain ⟨v, hv, x, hx⟩ := T1 h1 h2 (h3 w)
  have hne : NE R (essS R) x v := hx _ (h5 v)
  exact hne (God Pos) (T2 h1 h4 hx) u (heuc w v u hv hu)

/-- Reflexive point: failure of ∃G gives failure of □∃G (used for the S4 model). -/
theorem refl_box_fail (hr : R w w) (hn : ¬ ∃ y, God Pos y w) :
    ¬ box R (fun u => ∃ y, God Pos y u) w := fun hb => hn (hb w hr)


/-! ## New in this run: the haecceity of x at v is a Scott essence (full properties) -/

theorem haec_ess (R : W → W → Prop) (x : D) (v : W) :
    essS R (fun y u => y = x ∧ u = v) x v :=
  ⟨⟨rfl, rfl⟩, fun ψ hψ u _ y hy => by
    obtain ⟨h1, h2⟩ := hy
    subst h1; subst h2; exact hψ⟩

/-- A necessary existent at v sees at most v (only the essence clause of NE is used). -/
theorem NE_isolated {x : D} {v : W} (hne : NE R (essS R) x v) (u : W) (hu : R v u) :
    u = v := by
  obtain ⟨y, hy⟩ := hne _ (haec_ess R x v) u hu
  exact hy.2

/-- Any frame, A1 A2 A5 only: every world sees a world that sees exactly itself. -/
theorem A125_isolated_succ (h1 : A1 Pos) (h2 : A2 R Pos) (h5 : A5 R Pos (essS R)) (w : W) :
    ∃ v, R w v ∧ ∀ u, R v u ↔ u = v := by
  obtain ⟨v, hv, x, hx⟩ := T1 h1 h2 (h5 w)
  refine ⟨v, hv, fun u => ⟨NE_isolated hx u, fun h => ?_⟩⟩
  subst h
  obtain ⟨t, ht⟩ := scott_serial h1 h2 u
  have e := NE_isolated hx t ht
  subst e
  exact ht

/-- Symmetric frames, A1 A2 A5 only: every world sees exactly itself. -/
theorem A125_sym_iso (hsym : ∀ a b, R a b → R b a)
    (h1 : A1 Pos) (h2 : A2 R Pos) (h5 : A5 R Pos (essS R)) (w : W) :
    ∀ v, R w v ↔ v = w := by
  obtain ⟨v, hv, hiso⟩ := A125_isolated_succ h1 h2 h5 w
  have e : w = v := (hiso w).mp (hsym w v hv)
  subst e
  exact hiso

/-- Symmetric frames, A1 A2 A5 only: modal collapse. -/
theorem A125_sym_collapse (hsym : ∀ a b, R a b → R b a)
    (h1 : A1 Pos) (h2 : A2 R Pos) (h5 : A5 R Pos (essS R))
    (Q : W → Prop) (w : W) (hQ : Q w) : box R Q w :=
  fun v hv => ((A125_sym_iso hsym h1 h2 h5 w v).mp hv) ▸ hQ

/-- Symmetric frames, A1 A2 A3 A5 (no A4): a God-like being at every world, and □∃G. -/
theorem A1235_sym_god (hsym : ∀ a b, R a b → R b a)
    (h1 : A1 Pos) (h2 : A2 R Pos) (h3 : A3 Pos) (h5 : A5 R Pos (essS R)) (w : W) :
    (∃ x, God Pos x w) ∧ box R (fun u => ∃ y, God Pos y u) w := by
  have g : ∀ t : W, ∃ x, God Pos x t := fun t => by
    obtain ⟨v, hv, x, hx⟩ := T1 h1 h2 (h3 t)
    have e := (A125_sym_iso hsym h1 h2 h5 t v).mp hv
    subst e
    exact ⟨x, hx⟩
  exact ⟨g w, fun u _ => g u⟩


/-- Euclidean frames (K5, KD45), A1 A2 A3 A5 (no A4): □∃G at every world. -/
theorem A1235_euclid_box (heuc : ∀ a b c, R a b → R a c → R b c)
    (h1 : A1 Pos) (h2 : A2 R Pos) (h3 : A3 Pos) (h5 : A5 R Pos (essS R)) (w : W) :
    box R (fun u => ∃ y, God Pos y u) w := by
  obtain ⟨v0, hv0, hiso⟩ := A125_isolated_succ h1 h2 h5 w
  have only : ∀ u, R w u → u = v0 := fun u hu => (hiso u).mp (heuc w v0 u hv0 hu)
  intro u hu
  obtain ⟨v, hv, x, hx⟩ := T1 h1 h2 (h3 w)
  have e1 := only u hu
  have e2 := only v hv
  subst e1; subst e2
  exact ⟨x, hx⟩

end Scott

/-- An S4 (reflexive, transitive, not symmetric) Scott model: worlds Bool,
    R a b := a = b ∨ b = true; one individual; Pos φ w := φ () true.
    At `false`: possibly a God-like being exists, but none exists, and the true
    proposition (· = false) is not necessary. So Scott's ∃G and collapse fail on S4. -/
theorem scott_S4_model :
    ∃ (R : Bool → Bool → Prop) (Pos : Prp Bool Unit → Bool → Prop),
      (∀ a, R a a) ∧ (∀ a b c, R a b → R b c → R a c) ∧ ¬ (∀ a b, R a b → R b a) ∧
      A1 Pos ∧ A2 R Pos ∧ A3 Pos ∧ A4 R Pos ∧ A5 R Pos (essS R) ∧
      (∃ v, R false v ∧ ∃ y, God Pos y v) ∧
      ¬ (∃ y, God Pos y false) ∧
      ¬ box R (fun w : Bool => w = false) false := by
  refine ⟨fun a b => a = b ∨ b = true, fun φ _ => φ () true, fun _ => Or.inl rfl,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b c hab hbc
    cases hbc with
    | inr h => exact Or.inr h
    | inl h => exact h ▸ hab
  · intro h
    cases h false true (Or.inr rfl) with
    | inl h => exact Bool.noConfusion h
    | inr h => exact Bool.noConfusion h
  · intro φ w; exact Iff.rfl
  · intro φ ψ w hp hent; exact hent true (Or.inr rfl) () hp
  · intro w φ hp; exact hp
  · intro φ w hp v _; exact hp
  · intro w φ hess v hv
    -- Pos reads positivity at `true`, and `true` sees only itself.
    cases hv with
    | inl h => exact h ▸ ⟨(), hess.1⟩
    | inr h => exact h ▸ ⟨(), hess.1⟩
  · exact ⟨true, Or.inr rfl, (), fun φ hp => hp⟩
  · intro ⟨y, hy⟩; exact Bool.noConfusion (hy (fun _ w => w = true) rfl)
  · intro h; exact Bool.noConfusion (h true (Or.inr rfl))

/-- A KD45 (serial, transitive, euclidean, not reflexive) Scott model: worlds Bool,
    every world sees only `true`; one individual; Pos φ w := φ () true.
    □∃G holds everywhere, but at `false` no God-like being exists and the true
    proposition (· = false) is not necessary: no collapse, no T-axiom conclusion. -/
theorem scott_KD45_model :
    ∃ (R : Bool → Bool → Prop) (Pos : Prp Bool Unit → Bool → Prop),
      (∀ a, ∃ b, R a b) ∧ (∀ a b c, R a b → R b c → R a c) ∧
      (∀ a b c, R a b → R a c → R b c) ∧ ¬ R false false ∧
      A1 Pos ∧ A2 R Pos ∧ A3 Pos ∧ A4 R Pos ∧ A5 R Pos (essS R) ∧
      (∀ w, box R (fun u => ∃ y, God Pos y u) w) ∧
      ¬ (∃ y, God Pos y false) ∧
      (fun w : Bool => w = false) false ∧ ¬ box R (fun w : Bool => w = false) false := by
  refine ⟨fun _ b => b = true, fun φ _ => φ () true, fun _ => ⟨true, rfl⟩,
    fun _ _ _ _ h => h, fun _ _ _ hb hc => hb ▸ hc, Bool.noConfusion,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_⟩
  · intro φ w; exact Iff.rfl
  · intro φ ψ w hp hent; exact hent true rfl () hp
  · intro w φ hp; exact hp
  · intro φ w hp v _; exact hp
  · intro w φ hess v hv; subst hv; exact ⟨(), hess.1⟩
  · intro w u hu; subst hu; exact ⟨(), fun φ hp => hp⟩
  · intro ⟨y, hy⟩; exact Bool.noConfusion (hy (fun _ w => w = true) rfl)
  · intro h; exact Bool.noConfusion (h true rfl)
/-- A non-degenerate model: one world, two individuals (Bool); Pos = true of `false`.
    Exactly one individual is God-like there. -/
theorem scott_consistent_two :
    ∃ (R : Unit → Unit → Prop) (Pos : Prp Unit Bool → Unit → Prop),
      (∀ a, R a a) ∧ (∀ a b, R a b → R b a) ∧ (∀ a b c, R a b → R b c → R a c) ∧
      A1 Pos ∧ A2 R Pos ∧ A3 Pos ∧ A4 R Pos ∧ A5 R Pos (essS R) ∧
      God Pos false () ∧ ¬ God Pos true () := by
  refine ⟨fun _ _ => True, fun φ w => φ false w, fun _ => trivial, fun _ _ _ => trivial,
    fun _ _ _ _ _ => trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro φ w; exact Iff.rfl
  · intro φ ψ w hp hent; exact hent w trivial false hp
  · intro w φ hp; exact hp
  · intro φ w hp v _; cases v; cases w; exact hp
  · intro w φ hess v _; cases v; cases w; exact ⟨false, hess.1⟩
  · intro φ hp; exact hp
  · intro hg; exact Bool.noConfusion (hg (fun x _ => x = false) rfl)

/-- Majority model: one reflexive world, three individuals, φ positive iff at least two of
    the three individuals have φ. A1 A2 A4 A5 hold, no God-like being exists. -/
def maj (φ : Prp Unit (Fin 3)) (w : Unit) : Prop :=
  (φ 0 w ∧ φ 1 w) ∨ (φ 0 w ∧ φ 2 w) ∨ (φ 1 w ∧ φ 2 w)

theorem majority_model :
    (∀ a : Unit, (fun _ _ => True : Unit → Unit → Prop) a a) ∧
    A1 maj ∧ A2 (fun _ _ => True) maj ∧ A4 (fun _ _ => True) maj ∧
    A5 (fun _ _ => True) maj (essS (fun _ _ => True)) ∧ ¬ ∃ x, God maj x () := by
  refine ⟨fun _ => trivial, ?_, ?_, ?_, ?_, ?_⟩
  · intro φ w
    unfold maj neg
    by_cases a : φ 0 w <;> by_cases b : φ 1 w <;> by_cases c : φ 2 w <;> simp only [a, b, c] <;> simp
  · intro φ ψ w hp hent
    have h := fun x => hent w trivial x
    unfold maj at *
    rcases hp with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
    · exact Or.inl ⟨h _ a, h _ b⟩
    · exact Or.inr (Or.inl ⟨h _ a, h _ b⟩)
    · exact Or.inr (Or.inr ⟨h _ a, h _ b⟩)
  · intro φ w hp v _; cases v; cases w; exact hp
  · intro w
    have ne : ∀ x : Fin 3, NE (fun _ _ => True) (essS (fun _ _ => True)) x w :=
      fun x φ hess v _ => by cases v; cases w; exact ⟨x, hess.1⟩
    exact Or.inl ⟨ne 0, ne 1⟩
  · intro ⟨x, hx⟩
    have h01 := hx (fun y _ => y = 0 ∨ y = 1) (Or.inl ⟨Or.inl rfl, Or.inr rfl⟩)
    have h02 := hx (fun y _ => y = 0 ∨ y = 2) (Or.inr (Or.inl ⟨Or.inl rfl, Or.inr rfl⟩))
    have h12 := hx (fun y _ => y = 1 ∨ y = 2) (Or.inr (Or.inr ⟨Or.inl rfl, Or.inr rfl⟩))
    revert h01 h02 h12
    match x with
    | 0 => decide
    | 1 => decide
    | 2 => decide
end Onto

#print axioms Onto.godel1970_no_model
#print axioms Onto.scott_serial
#print axioms Onto.scott_symmetric
#print axioms Onto.scott_symmetric_box
#print axioms Onto.scott_symmetric_collapse
#print axioms Onto.T3_euclid
#print axioms Onto.refl_box_fail
#print axioms Onto.god_world_collapse
#print axioms Onto.A125_isolated_succ
#print axioms Onto.A125_sym_iso
#print axioms Onto.A125_sym_collapse
#print axioms Onto.A1235_sym_god
#print axioms Onto.A1235_euclid_box
#print axioms Onto.majority_model
#print axioms Onto.scott_S4_model
#print axioms Onto.scott_KD45_model
#print axioms Onto.scott_consistent_two
"""
NAMES = ['Onto.godel1970_no_model', 'Onto.scott_serial', 'Onto.scott_symmetric', 'Onto.scott_symmetric_box', 'Onto.scott_symmetric_collapse', 'Onto.T3_euclid', 'Onto.refl_box_fail', 'Onto.god_world_collapse', 'Onto.A125_isolated_succ', 'Onto.A125_sym_iso', 'Onto.A125_sym_collapse', 'Onto.A1235_sym_god', 'Onto.A1235_euclid_box', 'Onto.majority_model', 'Onto.scott_S4_model', 'Onto.scott_KD45_model', 'Onto.scott_consistent_two']
ZERO = ['Onto.refl_box_fail', 'Onto.scott_S4_model', 'Onto.scott_KD45_model', 'Onto.scott_consistent_two']
exe = shutil.which("lean")
if exe is None:
    for c in ("/opt/elan/bin/lean", "/opt/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean"):
        if os.path.isfile(c):
            exe = c
            break
assert exe, "lean not found"
p = subprocess.run([exe, "--stdin"], input=LEAN, capture_output=True, text=True, timeout=110)
out = p.stdout + p.stderr
print(out)
assert p.returncode == 0, "lean exit %d" % p.returncode
assert "error" not in out
assert "declaration uses 'sorry'" not in out and "sorryAx" not in out
assert "sorry" not in LEAN
assert not re.search(r"(?m)^\s*axiom\s", LEAN), "no axiom declarations allowed"
STD = {"propext", "Classical.choice", "Quot.sound"}
def axioms(name):
    if re.search(r"'" + re.escape(name) + r"' does not depend on any axioms", out):
        return set()
    m = re.search(r"'" + re.escape(name) + r"' depends on axioms: \[([^\]]*)\]", out)
    assert m, "no #print axioms line for " + name
    return {a.strip() for a in m.group(1).split(",")}
for n in NAMES:
    assert axioms(n) <= STD, n
for n in ZERO:
    assert axioms(n) == set(), n
assert "Onto.A1235_sym_god" in NAMES and "Onto.A125_sym_collapse" in NAMES and "Onto.A1235_euclid_box" in NAMES
print("PASS: %d theorems, A4-free symmetric/euclidean results, majority countermodel" % len(NAMES))
