import Programme.«20261021-1639-ontological».Atlas.D17T
import Programme.«20261021-1639-ontological».Atlas.V2DeepFrames
import Programme.«20261021-1639-ontological».Atlas.V2DeepT

/- D17T construction by th P404; exact subset packaging by pr. -/
namespace Programme.«20261021-1639-ontological».Atlas.V2DeepSymmetricT
open Programme.«20261021-1639-ontological».Deep Programme.«20261021-1639-ontological».Deep.Henkin Programme.«20261021-1639-ontological».Atlas.HenkinScott
open Programme.«20261021-1639-ontological».Atlas.SymmetricModels Programme.«20261021-1639-ontological».Atlas.ScottBridge
open Programme.«20261021-1639-ontological».Atlas.ScottDeep Programme.«20261021-1639-ontological».Atlas.V2Deep Programme.«20261021-1639-ontological».Atlas.V2DeepTable
open Programme.«20261021-1639-ontological».Atlas.SymmetricFinite Programme.«20261021-1639-ontological».Atlas.HenkinMinimal
open Programme.«20261021-1639-ontological».Atlas.V2DeepFull Programme.«20261021-1639-ontological».Atlas.V2DeepFrames Programme.«20261021-1639-ontological».Atlas.D17T

theorem T_symmetric_iff (s : FullMenu → Prop) (a : Bool) :
    FrameConsequence (fun _ r => Symmetric r) s a tT ↔ s .gen ∧ s .complement := by
  classical
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · apply Classical.byContradiction
      intro hn
      obtain ⟨hr, _, h1, h2, hb, h3, h4, hno, _, _⟩ := d17T a (emptyAssignment _)
      apply hno
      apply h We eModel (emptyAssignment _) hr
      intro i hi
      cases i with
      | meet => exact h1
      | gen => exact False.elim (hn hi)
      | complement => exact h2
      | rigid => exact hb
      | nepos => exact h3
      | up => exact h4
    · apply Classical.byContradiction
      intro hn
      obtain ⟨hr, h1, hg, hb, h3, h4, _, hno⟩ := V2DeepT.symmetric_T_deletion a
      apply hno
      apply h Unit (fullModel deadM) (emptyAssignment _) hr
      intro i hi
      cases i with
      | meet => exact h1
      | gen => exact hg
      | complement => exact False.elim (hn hi)
      | rigid => exact hb
      | nepos => exact h3
      | up => exact h4
  · rintro ⟨hg, h2⟩ W m ρ _ h
    exact (deep_v2 a ρ (h .gen hg) (h .complement h2)).1

#print axioms T_symmetric_iff
end Programme.«20261021-1639-ontological».Atlas.V2DeepSymmetricT
