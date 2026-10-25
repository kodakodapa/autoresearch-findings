import Programme.«20261021-1639-ontological».Atlas.V2DeepFull

/- Four-menu T corollary requested in th P367. Uses the already checked
   chain and dead-end deletions of K72, not the S5 existence deletions. -/
namespace Programme.«20261021-1639-ontological».Atlas.V2DeepT
open Programme.«20261021-1639-ontological».Deep Programme.«20261021-1639-ontological».Deep.Henkin Programme.«20261021-1639-ontological».Atlas.HenkinScott
open Programme.«20261021-1639-ontological».Atlas.SymmetricModels Programme.«20261021-1639-ontological».Atlas.ScottBridge
open Programme.«20261021-1639-ontological».Atlas.ScottDeep Programme.«20261021-1639-ontological».Atlas.V2Deep Programme.«20261021-1639-ontological».Atlas.V2DeepTable
open Programme.«20261021-1639-ontological».Atlas.SymmetricFinite Programme.«20261021-1639-ontological».Atlas.HenkinMinimal
open Programme.«20261021-1639-ontological».Atlas.V2DeepFull

theorem T_iff (s : Menu → Prop) (a : Bool) :
    Consequence s a tT ↔ s .gen ∧ s .complement := by
  classical
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · apply Classical.byContradiction
      intro hn
      obtain ⟨h1, h2, hb, h3, h4, hno, _, _⟩ := deep_drop_ax1gen_full a (emptyAssignment _)
      apply hno
      apply h Bool (fullModel chainM) (emptyAssignment _)
      intro i hi
      cases i with
      | gen => exact False.elim (hn hi)
      | complement => exact h2
      | rigid => exact hb
      | nepos => exact h3
    · apply Classical.byContradiction
      intro hn
      obtain ⟨h1, hg, hb, h3, h4, _, hno⟩ := deep_drop_ax2a_T a (emptyAssignment _)
      apply hno
      apply h Unit (fullModel deadM) (emptyAssignment _)
      intro i hi
      cases i with
      | gen => exact hg
      | complement => exact False.elim (hn hi)
      | rigid => exact hb
      | nepos => exact h3
  · rintro ⟨hg, h2⟩ W m ρ h
    exact (deep_v2 a ρ (h .gen hg) (h .complement h2)).1

/-- The empty frame is symmetric, so an Ax2a deletion for T can be symmetric. -/
theorem symmetric_T_deletion (a : Bool) :
    (∀ w v, deadM.rel w v → deadM.rel v w) ∧
    DeepValid (fullModel deadM) (emptyAssignment _) tAx1 ∧
    DeepValid (fullModel deadM) (emptyAssignment _) (tAx1Gen a) ∧
    DeepValid (fullModel deadM) (emptyAssignment _) tA4 ∧
    DeepValid (fullModel deadM) (emptyAssignment _) (tA5 a) ∧
    DeepValid (fullModel deadM) (emptyAssignment _) (tAx4 a) ∧
    ¬ DeepValid (fullModel deadM) (emptyAssignment _) tAx2a ∧
    ¬ DeepValid (fullModel deadM) (emptyAssignment _) tT :=
  ⟨fun _ _ h => h.elim, deep_drop_ax2a_T a (emptyAssignment _)⟩

#print axioms T_iff
#print axioms symmetric_T_deletion
end Programme.«20261021-1639-ontological».Atlas.V2DeepT
