import Programme.«20261024-1110-proof-complexity».Haken

namespace Programme.«20261031-2024-proof-complexity».BitClauseBridge

/-- Sum over valid completions only. No uniformity or division is used. -/
def mass {α : Type} (Ω : List α) (w : α → Rat) (event : α → Bool) : Rat :=
  (Ω.map fun a => if event a then w a else 0).sum

theorem mass_zero {α : Type} (Ω : List α) (w : α → Rat) (event : α → Bool)
    (h : ∀ a ∈ Ω, event a = true → w a = 0) : mass Ω w event = 0 := by
  induction Ω with
  | nil => rfl
  | cons a rest ih =>
    have ha : (if event a then w a else 0) = 0 := by
      cases he : event a with
      | false => simp [he]
      | true => simp [he, h a (by simp) he]
    have hr := ih (fun b hb => h b (by simp [hb]))
    simpa [mass, ha, Rat.zero_add] using hr

theorem mass_nonneg {α : Type} (Ω : List α) (w : α → Rat) (event : α → Bool)
    (h : ∀ a ∈ Ω, 0 ≤ w a) : 0 ≤ mass Ω w event := by
  induction Ω with
  | nil => exact Rat.le_refl
  | cons a rest ih =>
    have ha : 0 ≤ (if event a then w a else 0) := by
      cases event a <;> simp [h a (by simp)]
    exact Rat.add_nonneg ha (ih (fun b hb => h b (by simp [hb])))

/-- Splitting any event on one bit preserves its mass. -/
theorem mass_split {α : Type} (Ω : List α) (w : α → Rat) (event bit : α → Bool) :
    mass Ω w event = mass Ω w (fun a => event a && bit a) +
      mass Ω w (fun a => event a && !bit a) := by
  induction Ω with
  | nil => simp [mass, Rat.zero_add]
  | cons a rest ih =>
    have split (v : Rat) (e b : Bool) :
        (if e then v else 0) = (if e && b then v else 0) +
          (if e && !b then v else 0) := by
      cases e <;> cases b <;> simp [Rat.zero_add, Rat.add_zero]
    change (if event a then w a else 0) + mass rest w event =
      ((if event a && bit a then w a else 0) + mass rest w (fun x => event x && bit x)) +
      ((if event a && !bit a then w a else 0) + mass rest w (fun x => event x && !bit x))
    rw [split (w a) (event a) (bit a), ih]
    simp [Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]

/-- A split implication's falsifying event has zero mass, including every
additional multiplier event, if full-word violations have zero weight. -/
theorem split_implication_zero {α β ι : Type} (Ω : List α) (w : α → Rat)
    (guard multiplier : α → Bool) (output : α → β) (target : β)
    (bits : β → ι → Bool) (i : ι)
    (vanish : ∀ a ∈ Ω, guard a = true → output a ≠ target → w a = 0) :
    mass Ω w (fun a => multiplier a && guard a &&
      (bits (output a) i != bits target i)) = 0 := by
  apply mass_zero
  intro a ha he
  have hg : guard a = true := by
    cases hm : multiplier a <;> cases h : guard a <;> simp_all
  apply vanish a ha hg
  intro eq
  simp [eq] at he

/-- Excluding invalid codes before summation annihilates their events and
all multiples, regardless of whether the range size is a power of two. -/
theorem invalid_code_zero {α : Type} (Ω : List α) (w : α → Rat)
    (valid invalid multiplier : α → Bool)
    (hv : ∀ a ∈ Ω, valid a = true)
    (disjoint : ∀ a, valid a = true → invalid a = false) :
    mass Ω w (fun a => multiplier a && invalid a) = 0 := by
  apply mass_zero
  intro a ha he
  have hi := disjoint a (hv a ha)
  simp [hi] at he

#print axioms split_implication_zero
#print axioms mass_nonneg
#print axioms mass_split
#print axioms invalid_code_zero
end Programme.«20261031-2024-proof-complexity».BitClauseBridge
