import Programme.«20261031-2024-proof-complexity».LocalMoments

namespace Programme.«20261031-2024-proof-complexity».FilteredMoments
open Programme.«20261031-2024-proof-complexity».BitClauseBridge Programme.«20261031-2024-proof-complexity».LocalMoments

/-- Context costs are explicit: only contexts within the budget have tables.
Completions are total assignments, but agreement is required only on the context. -/
structure Tables (budget : Nat) where
  cost : List Nat → Nat
  completion : (s : List Nat) → cost s ≤ budget → List (Nat → Bool)
  weight : (s : List Nat) → cost s ≤ budget → (Nat → Bool) → Rat
  positive : ∀ s hs a, a ∈ completion s hs → 0 ≤ weight s hs a
  normalized : ∀ s hs, mass (completion s hs) (weight s hs) (fun _ => true) = 1
  restrict : ∀ s t, cost s ≤ budget → cost t ≤ budget → (Nat → Bool) → (Nat → Bool)
  agrees : ∀ s t hs ht, (∀ i ∈ s, i ∈ t) →
    ∀ a ∈ completion t ht, ∀ i ∈ s, restrict s t hs ht a i = a i
  marginal : ∀ s t hs ht, (∀ i ∈ s, i ∈ t) →
    Marginal (completion s hs) (completion t ht) (restrict s t hs ht)
      (weight s hs) (weight t ht)

def Supported (s : List Nat) (event : (Nat → Bool) → Bool) : Prop :=
  ∀ a b, (∀ i ∈ s, a i = b i) → event a = event b

def evaluate {d : Nat} (T : Tables d) (s : List Nat) (hs : T.cost s ≤ d)
    (event : (Nat → Bool) → Bool) : Rat :=
  mass (T.completion s hs) (T.weight s hs) event

/-- A supported event may be evaluated in any larger admitted context. -/
theorem consistency {d : Nat} (T : Tables d) (s t : List Nat)
    (hs : T.cost s ≤ d) (ht : T.cost t ≤ d)
    (inc : ∀ i ∈ s, i ∈ t) (event : (Nat → Bool) → Bool)
    (support : Supported s event) :
    evaluate T s hs event = evaluate T t ht event := by
  unfold evaluate
  rw [event_consistency _ _ _ _ _ (T.marginal s t hs ht inc) event]
  apply mass_congr
  intro a ha
  exact support _ _ (T.agrees s t hs ht inc a ha)

/-- The filtered tables give normalized positive event functionals with
Boolean splitting, at every admitted context. -/
theorem local_laws {d : Nat} (T : Tables d) (s : List Nat)
    (hs : T.cost s ≤ d) (event bit : (Nat → Bool) → Bool) :
    evaluate T s hs (fun _ => true) = 1 ∧
    0 ≤ evaluate T s hs event ∧
    evaluate T s hs event = evaluate T s hs (fun a => event a && bit a) +
      evaluate T s hs (fun a => event a && !bit a) := by
  exact ⟨T.normalized s hs, mass_nonneg _ _ _ (T.positive s hs), mass_split _ _ _ _⟩

/-- Full-word soundness in an admitted joint context yields every bitwise
clause-multiplier equation in that context. -/
theorem admitted_split_zero {d : Nat} (T : Tables d) (s : List Nat)
    (hs : T.cost s ≤ d) {β ι : Type} (guard multiplier : (Nat → Bool) → Bool)
    (output : (Nat → Bool) → β) (target : β) (bits : β → ι → Bool) (i : ι)
    (vanish : ∀ a ∈ T.completion s hs, guard a = true →
      output a ≠ target → T.weight s hs a = 0) :
    evaluate T s hs (fun a => multiplier a && guard a &&
      (bits (output a) i != bits target i)) = 0 := by
  exact split_implication_zero _ _ _ _ _ _ _ _ vanish

#print axioms consistency
#print axioms local_laws
#print axioms admitted_split_zero
end Programme.«20261031-2024-proof-complexity».FilteredMoments
