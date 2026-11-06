import Programme.«20261031-2024-proof-complexity».FilteredMoments

namespace Programme.«20261031-2024-proof-complexity».IndicatorTables
open Programme.«20261031-2024-proof-complexity».BitClauseBridge Programme.«20261031-2024-proof-complexity».LocalMoments

/-- A rational functional; positivity is required separately only on admitted cells. -/
structure Functional (Ω : Type) where
  eval : (Ω → Rat) → Rat
  zero : eval (fun _ => 0) = 0
  add : ∀ f g, eval (fun x => f x + g x) = eval f + eval g
  unit : eval (fun _ => 1) = 1

def total {α Ω : Type} (xs : List α) (f : α → Ω → Rat) : Ω → Rat :=
  fun x => (xs.map (fun a => f a x)).sum

theorem eval_total {α Ω : Type} (E : Functional Ω) (xs : List α)
    (f : α → Ω → Rat) :
    E.eval (total xs f) = (xs.map (fun a => E.eval (f a))).sum := by
  induction xs with
  | nil => exact E.zero
  | cons a xs ih =>
    change E.eval (fun x => f a x + total xs f x) = _
    rw [E.add, ih]
    rfl

/-- Partition indicators can be functions on source assignments; no source
probability distribution or positivity on arbitrary functions is assumed. -/
structure Partition {Ω α : Type} (E : Functional Ω) (cells : List α) where
  indicator : α → Ω → Rat
  partition : total cells indicator = fun _ => 1
  positive : ∀ a ∈ cells, 0 ≤ E.eval (indicator a)

def weights {Ω α : Type} {E : Functional Ω} {cells : List α}
    (P : Partition E cells) : α → Rat := fun a => E.eval (P.indicator a)

theorem normalized {Ω α : Type} (E : Functional Ω) (cells : List α)
    (P : Partition E cells) : mass cells (weights P) (fun _ => true) = 1 := by
  have h := eval_total E cells P.indicator
  rw [P.partition, E.unit] at h
  simpa [mass, weights] using h.symm

/-- A pointwise indicator refinement is sufficient to construct the actual
finite marginal witness consumed by K11. -/
def marginal_of_refinement {Ω α β : Type} (E : Functional Ω)
    (coarse : List α) (fine : List β)
    (P : Partition E coarse) (Q : Partition E fine)
    (restrict : β → α) (fiber : α → List β)
    (partition : fine = coarse.flatMap fiber)
    (projects : ∀ a ∈ coarse, ∀ b ∈ fiber a, restrict b = a)
    (refines : ∀ a ∈ coarse, P.indicator a = total (fiber a) Q.indicator) :
    Marginal coarse fine restrict (weights P) (weights Q) := by
  refine ⟨fiber, partition, projects, ?_⟩
  intro a ha
  change E.eval (P.indicator a) = _
  rw [refines a ha, eval_total]
  simp [mass, weights]

/-- Indicator conjunctions with pointwise partitions/refinements yield
positive normalized completion tables and event consistency. -/
theorem completion_laws {Ω α β : Type} (E : Functional Ω)
    (coarse : List α) (fine : List β)
    (P : Partition E coarse) (Q : Partition E fine)
    (restrict : β → α) (fiber : α → List β)
    (partition : fine = coarse.flatMap fiber)
    (projects : ∀ a ∈ coarse, ∀ b ∈ fiber a, restrict b = a)
    (refines : ∀ a ∈ coarse, P.indicator a = total (fiber a) Q.indicator)
    (event : α → Bool) :
    mass coarse (weights P) (fun _ => true) = 1 ∧
    (∀ a ∈ coarse, 0 ≤ (weights P) a) ∧
    mass coarse (weights P) event = mass fine (weights Q) (fun b => event (restrict b)) := by
  exact ⟨normalized E coarse P, P.positive,
    event_consistency coarse fine restrict (weights P) (weights Q)
      (marginal_of_refinement E coarse fine P Q restrict fiber partition projects refines) event⟩

#print axioms marginal_of_refinement
#print axioms completion_laws
end Programme.«20261031-2024-proof-complexity».IndicatorTables
