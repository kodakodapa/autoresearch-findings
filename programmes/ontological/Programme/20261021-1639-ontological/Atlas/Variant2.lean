import Notes.HOMLinHOL

/- Literal parameterized expansions of GoedelVariantHOML2*. Full property and
higher-predicate domains; the guard A selects the ConjOfPropsFrom/PInc domain,
B the E existential domain. No Notes postulate is used. -/
namespace Programme.«20261021-1639-ontological».Atlas.Variant2
universe u v
variable {W : Type u} {D : Type v}
abbrev Property (W : Type u) (D : Type v) := D → W → Prop
def bot : Property W D := fun _ _ => False
def neg (p : Property W D) : Property W D := fun x w => ¬ p x w
def God (P : Property W D → W → Prop) (x : D) (w : W) := ∀ p, P p w → p x w
def Ess (R : W → W → Prop) (A : Property W D) (p : Property W D) (x : D) (w : W) :=
  p x w ∧ ∀ q : Property W D, q x w → ∀ v, R w v → ∀ y, A y v → p y v → q y v
def NE (R : W → W → Prop) (A B : Property W D) : Property W D :=
  fun x w => ∀ p, Ess R A p x w → ∀ v, R w v → ∃ y, B y v ∧ p y v
structure Core (R : W → W → Prop) (A : Property W D)
    (P : Property W D → W → Prop) : Prop where
  ax2a : ∀ p w, (P p w ∨ P (neg p) w) ∧ ¬ (P p w ∧ P (neg p) w)
  ax1Gen : ∀ (s : Property W D → W → Prop) p w,
    (∀ q, s q w → P q w) →
    (∀ v, R w v → ∀ y, A y v → (p y v ↔ ∀ q, s q v → q y v)) → P p w

variable (R : W → W → Prop) (A : Property W D) (P : Property W D → W → Prop)
variable (h : Core R A P)
include R A P h

theorem not_positive_bot (w : W) : ¬ P bot w := by
  have ht : P (neg bot) w := h.ax1Gen (fun _ _ => False) (neg bot) w
    (fun _ hf => hf.elim) (fun _ _ _ _ => ⟨fun _ _ hf => hf.elim, fun _ hf => hf⟩)
  exact fun hb => (h.ax2a bot w).2 ⟨hb, ht⟩

theorem frame_reflexive (w : W) : R w w := by
  classical
  apply Classical.byContradiction
  intro hn
  apply not_positive_bot R A P h w
  apply h.ax1Gen (fun q v => v ≠ w ∧ q = bot) bot w
  · exact fun _ hq => (hq.1 rfl).elim
  · intro v hv y _
    exact ⟨fun hf => hf.elim, fun hh => hh bot ⟨fun he => hn (he ▸ hv), rfl⟩⟩

theorem god_everywhere (w : W) : ∃ x, A x w ∧ God P x w := by
  classical
  apply Classical.byContradiction
  intro hn
  apply not_positive_bot R A P h w
  apply h.ax1Gen (fun q v => (v = w ∧ P q w) ∨ (v ≠ w ∧ q = bot)) bot w
  · intro q hq
    exact hq.elim And.right (fun hh => (hh.1 rfl).elim)
  · intro v _ y hy
    refine ⟨fun hf => hf.elim, ?_⟩
    intro hh
    by_cases hv : v = w
    · subst v
      exact hn ⟨y, hy, fun q hq => hh q (Or.inl ⟨rfl, hq⟩)⟩
    · exact hh bot (Or.inr ⟨hv, rfl⟩)

omit P h in
/-- The singleton essence used in P69, with no positivity or frame assumptions. -/
theorem singleton_essence (x : D) (w : W) :
    Ess R A (fun y v => y = x ∧ v = w) x w := by
  refine ⟨⟨rfl, rfl⟩, ?_⟩
  intro q hq v _ y _ hy
  rcases hy with ⟨rfl, rfl⟩
  exact hq

theorem identity_of_ax3 (B : Property W D) (ax3 : ∀ w, P (NE R A B) w) :
    ∀ w v, R w v ↔ v = w := by
  intro w v
  refine ⟨?_, fun hv => hv ▸ frame_reflexive R A P h w⟩
  intro hv
  obtain ⟨x, _, hx⟩ := god_everywhere R A P h w
  obtain ⟨y, _, hy⟩ := hx (NE R A B) (ax3 w) _ (singleton_essence R A x w) v hv
  exact hy.2

theorem identity_of_ax2b
    (ax2b : ∀ p w, P p w → ∀ v, R w v → P p v) :
    ∀ w v, R w v ↔ v = w := by
  intro w v
  refine ⟨?_, fun hv => hv ▸ frame_reflexive R A P h w⟩
  intro hv
  have hp : P (fun _ t => t = w) w := by
    apply h.ax1Gen (fun q t => t ≠ w ∧ q = bot) _ w
    · exact fun _ hh => (hh.1 rfl).elim
    · intro t _ y _
      refine ⟨?_, ?_⟩
      · intro ht q hh
        exact (hh.1 ht).elim
      · intro hh
        apply Classical.byContradiction
        intro ht
        exact hh bot ⟨ht, rfl⟩
  obtain ⟨x, _, hx⟩ := god_everywhere R A P h v
  exact hx _ (ax2b _ w hp v hv)

theorem modal_collapse_of_ax3 (B : Property W D) (ax3 : ∀ w, P (NE R A B) w) :
    ∀ (p : W → Prop) w, p w → ∀ v, R w v → p v := by
  intro p w hp v hv
  exact (identity_of_ax3 R A P h B ax3 w v).1 hv ▸ hp

theorem necessary_existence (w : W) : ∀ v, R w v → ∃ x, A x v ∧ God P x v :=
  fun v _ => god_everywhere R A P h v

/-- Matches Th3 in both variant-2 S4 files, without even a frame assumption. -/
theorem th3 (w : W) :
    (∃ v, R w v ∧ ∃ x, A x v ∧ God P x v) →
    ∀ v, R w v → ∃ x, A x v ∧ God P x v :=
  fun _ => necessary_existence R A P h w

/-- Ax3 supplies existence in B as well, including mixed actualist existence. -/
theorem god_everywhere_B (B : Property W D) (ax3 : ∀ w, P (NE R A B) w)
    (w : W) : ∃ x, B x w ∧ God P x w := by
  obtain ⟨x, _, hx⟩ := god_everywhere R A P h w
  obtain ⟨y, hy, he⟩ := hx (NE R A B) (ax3 w) _
    (singleton_essence R A x w) w (frame_reflexive R A P h w)
  exact ⟨y, hy, he.1.symm ▸ hx⟩

theorem monotheism (w : W) (x y : D) (hx : God P x w) (hy : God P y w) : x = y := by
  let p : Property W D := fun z _ => z = x
  have hp : P p w := (h.ax2a p w).1.elim id
    (fun hn => False.elim (hx (neg p) hn rfl))
  exact (hy p hp).symm

#print axioms god_everywhere_B
#print axioms monotheism
#print axioms frame_reflexive
#print axioms god_everywhere
#print axioms singleton_essence
#print axioms identity_of_ax3
#print axioms identity_of_ax2b
#print axioms modal_collapse_of_ax3
#print axioms necessary_existence
#print axioms th3
end Programme.«20261021-1639-ontological».Atlas.Variant2
