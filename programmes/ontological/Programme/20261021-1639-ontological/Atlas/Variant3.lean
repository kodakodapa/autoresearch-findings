import Notes.HOMLinHOL

/- Parameterized literal expansion of Notes.GoedelVariantHOML3 PInc/Ess/E.
   The two guards separately cover actualist, mixed, and possibilist quantifiers.
   No frame postulate or positivity constant from Notes is used. -/
namespace Programme.«20261021-1639-ontological».Atlas.Variant3
universe u v
variable {W : Type u} {D : Type v}
abbrev Property (W : Type u) (D : Type v) := D → W → Prop
def neg (p : Property W D) : Property W D := fun x w => ¬ p x w
def bot : Property W D := fun _ _ => False
def inc (R : W → W → Prop) (A : D → W → Prop) (p q : Property W D) (w : W) :=
  ∀ v, R w v → p ≠ bot ∧ ∀ y, A y v → p y v → q y v
def ess (R : W → W → Prop) (A : D → W → Prop) (p : Property W D) (x : D) (w : W) :=
  ∀ q : Property W D, q x w → inc R A p q w
def ne (R : W → W → Prop) (A B : D → W → Prop) : Property W D :=
  fun x w => ∀ p, ess R A p x w → ∀ v, R w v → ∃ y, B y v ∧ p y v

structure Axioms (R : W → W → Prop) (A B : D → W → Prop)
    (P : Property W D → W → Prop) : Prop where
  ax2a : ∀ p w, (P p w ∨ P (neg p) w) ∧ ¬ (P p w ∧ P (neg p) w)
  ax3 : ∀ w, P (ne R A B) w
  ax4 : ∀ p q w, P p w → inc R A p q w → P q w

/-- P52's world-collapse conclusion, even for arbitrary independent quantifier guards. -/
theorem worlds_subsingleton [Nonempty D] (R : W → W → Prop) (A B : D → W → Prop)
    (P : Property W D → W → Prop) (h : Axioms R A B P) :
    ∀ a b : W, a = b := by
  classical
  intro a b
  apply Classical.byContradiction
  intro hab
  let d : D := Classical.choice inferInstance
  let s : Property W D := fun _ w => w = a
  have hs : s ≠ bot := by
    intro he; have ht : s d a := rfl; rw [he] at ht; exact ht
  have hns : neg s ≠ bot := by
    intro he; have ht : neg s d b := Ne.symm hab; rw [he] at ht; exact ht
  have notbot (w : W) : ¬ P bot w := by
    intro hb
    have hp : ∃ p : Property W D, P p w ∧ p ≠ bot := by
      rcases (h.ax2a s w).1 with hp | hp
      · exact ⟨s, hp, hs⟩
      · exact ⟨neg s, hp, hns⟩
    obtain ⟨p, hp, hn⟩ := hp
    have ht : P (neg bot) w := h.ax4 p (neg bot) w hp
      (fun _ _ => ⟨hn, fun _ _ _ hf => hf⟩)
    exact (h.ax2a bot w).2 ⟨hb, ht⟩
  have hne : ne R A B ≠ bot := by
    intro he; exact notbot a (he ▸ h.ax3 a)
  have successor (w : W) : ∃ v, R w v ∧ ∃ x, A x v ∧ ne R A B x v := by
    apply Classical.byContradiction
    intro hn
    have hp : P (neg (ne R A B)) w := h.ax4 _ _ w (h.ax3 w) (by
      intro v hv
      exact ⟨hne, fun x hx he => (hn ⟨v, hv, x, hx, he⟩).elim⟩)
    exact (h.ax2a _ w).2 ⟨h.ax3 w, hp⟩
  obtain ⟨t, _, x, _, hx⟩ := successor a
  let singleton : Property W D := fun y v => y = x ∧ v = t
  have hsingle : ess R A singleton x t := by
    intro q hq v hv
    refine ⟨?_, ?_⟩
    · intro he
      have ht : singleton x t := ⟨rfl, rfl⟩
      rw [he] at ht
      exact ht
    · intro y _ hy
      rcases hy with ⟨rfl, rfl⟩
      exact hq
  have only (v : W) (hv : R t v) : v = t := (hx singleton hsingle v hv).choose_spec.2.2
  obtain ⟨v, hv, _, _, _⟩ := successor t
  have htt : R t t := only v hv ▸ hv
  have other : ∃ c : W, c ≠ t := by
    by_cases hat : a = t
    · exact ⟨b, fun hbt => hab (hat.trans hbt.symm)⟩
    · exact ⟨a, hat⟩
  obtain ⟨c, hc⟩ := other
  let away : Property W D := fun _ v => v ≠ t
  have haway : ess R A away x t := by
    intro q _ v hv
    refine ⟨?_, ?_⟩
    · intro he
      have ht : away d c := hc
      rw [he] at ht
      exact ht
    · intro _ _ ha
      exact (ha (only v hv)).elim
  obtain ⟨y, _, hy⟩ := hx away haway t htt
  exact hy rfl

theorem frame_reflexive [Nonempty D] (R : W → W → Prop) (A B : D → W → Prop)
    (P : Property W D → W → Prop) (h : Axioms R A B P) : ∀ w, R w w := by
  classical
  intro w
  apply Classical.byContradiction
  intro hn
  have hinc : inc R A (ne R A B) (neg (ne R A B)) w := by
    intro v hv
    exact (hn (worlds_subsingleton R A B P h v w ▸ hv)).elim
  exact (h.ax2a _ w).2 ⟨h.ax3 w, h.ax4 _ _ w (h.ax3 w) hinc⟩

/-- The actualist clause of P52 fails for the three-axiom subset. -/
theorem empty_actuality_countermodel :
    ∃ (R : Unit → Unit → Prop) (actual : Unit → Unit → Prop)
      (P : Property Unit Unit → Unit → Prop),
      Axioms R actual actual P ∧ (∀ w, R w w) ∧ (∀ x w, ¬ actual x w) := by
  classical
  let R : Unit → Unit → Prop := fun _ _ => True
  let actual : Unit → Unit → Prop := fun _ _ => False
  let P : Property Unit Unit → Unit → Prop := fun p _ => ¬ p () ()
  refine ⟨R, actual, P, ⟨?_, ?_, ?_⟩, fun _ => True.intro, fun _ _ h => h⟩
  · intro p w
    exact ⟨Classical.em (p () ()) |>.symm.imp id (fun hp hn => hn hp),
      fun ⟨hn, hnn⟩ => hnn hn⟩
  · intro w hne
    have he : ess R actual (fun _ _ => True) () () := by
      intro q _ v _
      refine ⟨?_, fun _ hf => hf.elim⟩
      intro eq
      have ht : (fun (_ : Unit) (_ : Unit) => True) () () := True.intro
      rw [eq] at ht
      exact ht
    obtain ⟨y, hy, _⟩ := hne (fun _ _ => True) he () True.intro
    exact hy
  · intro p q w hp hi
    have eq : p = bot := by
      funext x v
      cases x; cases v
      exact propext ⟨fun ht => hp ht, fun hf => hf.elim⟩
    exact ((hi () True.intro).1 eq).elim

#print axioms worlds_subsingleton
#print axioms frame_reflexive
#print axioms empty_actuality_countermodel
theorem ax4_of_ax2a_ax1gen {W : Type u} {E : Type v} (R : W → W → Prop) (q r : E → W → Prop)
    (P : (E → W → Prop) → W → Prop) (hqr : ∀ y v, q y v → r y v)
    (Ax2a : ∀ φ w, (P φ w ∨ P (fun x v => ¬ φ x v) w) ∧ ¬ (P φ w ∧ P (fun x v => ¬ φ x v) w))
    (Ax1Gen : ∀ (Φ : (E → W → Prop) → W → Prop) (φ : E → W → Prop) w,
      (∀ ψ, Φ ψ w → P ψ w) →
      (∀ v, R w v → ∀ z, q z v → (φ z v ↔ ∀ ψ, Φ ψ v → ψ z v)) → P φ w) :
    ∀ (φ ψ : E → W → Prop) w, P φ w →
      (∀ v, R w v → (φ ≠ fun _ _ => False) ∧ ∀ y, r y v → φ y v → ψ y v) → P ψ w := by
  intro φ ψ w hφ hinc
  refine Classical.byContradiction fun hψ => ?_
  have hnψ : P (fun x v => ¬ ψ x v) w := (Ax2a ψ w).1.resolve_left hψ
  have hbot : P (fun _ _ => False) w := by
    refine Ax1Gen (fun χ _ => χ = φ ∨ χ = (fun x v => ¬ ψ x v)) _ w ?_ ?_
    · rintro χ (rfl | rfl)
      · exact hφ
      · exact hnψ
    · intro v hv z hz
      refine ⟨False.elim, fun h => ?_⟩
      exact h (fun x v => ¬ ψ x v) (Or.inr rfl) ((hinc v hv).2 z (hqr z v hz) (h φ (Or.inl rfl)))
  have htop : P (fun x v => ¬ (fun (_ : E) (_ : W) => False) x v) w :=
    Ax1Gen (fun _ _ => False) _ w (fun _ h => h.elim)
      (fun _ _ _ _ => ⟨fun _ _ h => h.elim, fun _ h => h⟩)
  exact (Ax2a _ w).2 ⟨hbot, htop⟩


-- Q is the conjunction guard; A is the inclusion guard. Q implies A in
-- the actualist, possibilist, and Anderson Notes variants.
def Ax1Gen (R : W → W → Prop) (Q : D → W → Prop)
    (P : Property W D → W → Prop) : Prop :=
  ∀ (F : Property W D → W → Prop) p w,
    (∀ q, F q w → P q w) →
    (∀ v, R w v → ∀ x, Q x v → (p x v ↔ ∀ q, F q v → q x v)) → P p w

theorem worlds_subsingleton_of_ax1gen [Nonempty D]
    (R : W → W → Prop) (Q A B : D → W → Prop)
    (P : Property W D → W → Prop) (hQA : ∀ x w, Q x w → A x w)
    (h2 : ∀ p w, (P p w ∨ P (neg p) w) ∧ ¬ (P p w ∧ P (neg p) w))
    (h3 : ∀ w, P (ne R A B) w) (h1 : Ax1Gen R Q P) :
    (∀ w v : W, w = v) ∧ (∀ w, R w w) := by
  have h : Axioms R A B P :=
    ⟨h2, h3, ax4_of_ax2a_ax1gen R Q A P hQA h2 h1⟩
  exact ⟨worlds_subsingleton R A B P h, frame_reflexive R A B P h⟩

#print axioms ax4_of_ax2a_ax1gen
#print axioms worlds_subsingleton_of_ax1gen
end Programme.«20261021-1639-ontological».Atlas.Variant3
