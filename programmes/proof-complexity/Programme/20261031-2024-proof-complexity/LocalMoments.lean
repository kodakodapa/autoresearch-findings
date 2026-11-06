import Programme.«20261031-2024-proof-complexity».BitClauseBridge

namespace Programme.«20261031-2024-proof-complexity».LocalMoments
open Programme.«20261031-2024-proof-complexity».BitClauseBridge

theorem mass_append {α : Type} (a b : List α) (w : α → Rat) (e : α → Bool) :
    mass (a ++ b) w e = mass a w e + mass b w e := by
  simp [mass, List.map_append, List.sum_append]

theorem mass_congr {α : Type} (a : List α) (w : α → Rat) (e f : α → Bool)
    (h : ∀ x ∈ a, e x = f x) : mass a w e = mass a w f := by
  induction a with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simpa [mass, hx] using congrArg (fun z => (if f x then w x else 0) + z) ht

/-- A finite marginal table: the fine list is partitioned into coarse fibers.
Lists count multiplicities, so no hidden nodup assumption is needed. -/
structure Marginal {α β : Type} (coarse : List α) (fine : List β)
    (restrict : β → α) (wc : α → Rat) (wf : β → Rat) where
  fiber : α → List β
  partition : fine = coarse.flatMap fiber
  projects : ∀ a ∈ coarse, ∀ b ∈ fiber a, restrict b = a
  weights : ∀ a ∈ coarse, wc a = mass (fiber a) wf (fun _ => true)

/-- Marginal consistency makes the mass of every coarse event independent
of whether it is evaluated in the coarse or the fine completion table. -/
theorem event_consistency {α β : Type} (coarse : List α) (fine : List β)
    (restrict : β → α) (wc : α → Rat) (wf : β → Rat)
    (h : Marginal coarse fine restrict wc wf) (event : α → Bool) :
    mass coarse wc event = mass fine wf (fun b => event (restrict b)) := by
  rw [h.partition]
  have main : ∀ cs : List α,
      (∀ a ∈ cs, ∀ b ∈ h.fiber a, restrict b = a) →
      (∀ a ∈ cs, wc a = mass (h.fiber a) wf (fun _ => true)) →
      mass cs wc event = mass (cs.flatMap h.fiber) wf (fun b => event (restrict b)) := by
    intro cs
    induction cs with
    | nil => intro _ _; rfl
    | cons a rest ih =>
      intro hp hw
      have fiber_eq : mass (h.fiber a) wf (fun b => event (restrict b)) =
          (if event a then wc a else 0) := by
        rw [mass_congr (h.fiber a) wf _ (fun _ => event a)
          (fun b hb => congrArg event (hp a (by simp) b hb))]
        cases he : event a with
        | false =>
          simp only [he, Bool.false_eq_true, ↓reduceIte]
          exact mass_zero _ _ _ (by intro b hb he; contradiction)
        | true => simpa [he] using (hw a (by simp)).symm
      have tail := ih (fun b hb => hp b (by simp [hb]))
        (fun b hb => hw b (by simp [hb]))
      simp only [List.flatMap_cons, mass_append]
      change (if event a then wc a else 0) + mass rest wc event = _
      rw [fiber_eq, tail]
  exact main coarse h.projects h.weights

#print axioms event_consistency
end Programme.«20261031-2024-proof-complexity».LocalMoments
