import Programme.«20261021-1639-ontological».Atlas.D17
/- Subset packaging by pr; D17 witness by th P386. -/
namespace Programme.«20261021-1639-ontological».Atlas.V2DeepFrames
open Programme.«20261021-1639-ontological».Deep Programme.«20261021-1639-ontological».Deep.Henkin Programme.«20261021-1639-ontological».Atlas.HenkinScott
open Programme.«20261021-1639-ontological».Atlas.SymmetricModels Programme.«20261021-1639-ontological».Atlas.ScottBridge
open Programme.«20261021-1639-ontological».Atlas.ScottDeep Programme.«20261021-1639-ontological».Atlas.V2Deep Programme.«20261021-1639-ontological».Atlas.V2DeepTable
open Programme.«20261021-1639-ontological».Atlas.SymmetricFinite Programme.«20261021-1639-ontological».Atlas.HenkinMinimal
open Programme.«20261021-1639-ontological».Atlas.V2DeepFull Programme.«20261021-1639-ontological».Atlas.D17

def S5 {W : Type} (r : W → W → Prop) : Prop :=
  (∀ w, r w w) ∧ (∀ w v, r w v → r v w) ∧ (∀ w v u, r w v → r v u → r w u)
def Symmetric {W : Type} (r : W → W → Prop) : Prop := ∀ w v, r w v → r v w

def FrameConsequence (C : ∀ W : Type, (W → W → Prop) → Prop)
    (s : FullMenu → Prop) (a : Bool) (t : T [] .prop) : Prop :=
  ∀ (W : Type) (m : Henkin.Model OntConst W) (ρ : Assignment m.frame []),
    C W m.frame.rel → (∀ i, s i → DeepValid m ρ (fullAxiomTerm a i)) → DeepValid m ρ t

variable (C : ∀ W : Type, (W → W → Prop) → Prop)
  (hu : ∀ (W : Type) (r : W → W → Prop), (∀ w v, r w v) → C W r)

include hu in
theorem necessary_iff (s : FullMenu → Prop) (a : Bool) :
    FrameConsequence C s a (tNecEx a) ↔ s .gen ∧ s .complement := by
  classical
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · apply Classical.byContradiction
      intro hn
      obtain ⟨hr, h2, hb, h3, hno, _⟩ := deep_drop_ax1gen a (emptyAssignment _)
      obtain ⟨h1, h4⟩ := free_ax14 a (emptyAssignment _)
      apply hno
      apply h Unit (fullModel freeM) (emptyAssignment _) (hu _ _ hr)
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
      obtain ⟨hr, hg, hb, h3, _, hno, _⟩ := deep_drop_ax2a a (emptyAssignment _)
      obtain ⟨h1, h4⟩ := allPos_ax14 a (emptyAssignment _)
      apply hno
      apply h Bool (fullModel allPosM) (emptyAssignment _) (hu _ _ hr)
      intro i hi
      cases i with
      | meet => exact h1
      | gen => exact hg
      | complement => exact False.elim (hn hi)
      | rigid => exact hb
      | nepos => exact h3
      | up => exact h4
  · rintro ⟨hg, h2⟩ W m ρ _ h
    exact (deep_v2 a ρ (h .gen hg) (h .complement h2)).2

include hu in
theorem collapse_iff (s : FullMenu → Prop) (a : Bool) :
    FrameConsequence C s a tMC ↔ s .gen ∧ s .complement ∧ s .rigid := by
  classical
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · apply Classical.byContradiction
      intro hn
      obtain ⟨hr, h1, h2, hb, h3, h4, hno, _, _⟩ := d17 a (emptyAssignment _)
      apply hno
      apply h Wd dModel (emptyAssignment _) (hu _ _ hr)
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
      obtain ⟨hr, hg, hb, h3, _, _, hno⟩ := deep_drop_ax2a a (emptyAssignment _)
      obtain ⟨h1, h4⟩ := allPos_ax14 a (emptyAssignment _)
      apply hno
      apply h Bool (fullModel allPosM) (emptyAssignment _) (hu _ _ hr)
      intro i hi
      cases i with
      | meet => exact h1
      | gen => exact hg
      | complement => exact False.elim (hn hi)
      | rigid => exact hb
      | nepos => exact h3
      | up => exact h4
    · apply Classical.byContradiction
      intro hn
      obtain ⟨hr, hg, h2, h3, _, _, hno⟩ := deep_cw a (emptyAssignment _)
      obtain ⟨h1, h4⟩ := cw_ax14 a (emptyAssignment _)
      apply hno
      apply h _ cantorCWModel (emptyAssignment _) (hu _ _ hr)
      intro i hi
      cases i with
      | meet => exact h1
      | gen => exact hg
      | complement => exact h2
      | rigid => exact False.elim (hn hi)
      | nepos => exact h3
      | up => exact h4
  · rintro ⟨hg, h2, hb⟩ W m ρ _ h
    exact deep_v2_mc a ρ (h .gen hg) (h .complement h2) (h .rigid hb)


theorem collapse_S5_iff (s : FullMenu → Prop) (a : Bool) :
    FrameConsequence (fun _ r => S5 r) s a tMC ↔ s .gen ∧ s .complement ∧ s .rigid :=
  collapse_iff _ (fun _ _ h => ⟨fun w => h w w, fun _ _ _ => h _ _, fun _ _ _ _ _ => h _ _⟩) s a

theorem necessary_S5_iff (s : FullMenu → Prop) (a : Bool) :
    FrameConsequence (fun _ r => S5 r) s a (tNecEx a) ↔ s .gen ∧ s .complement :=
  necessary_iff _ (fun _ _ h => ⟨fun w => h w w, fun _ _ _ => h _ _, fun _ _ _ _ _ => h _ _⟩) s a

theorem collapse_symmetric_iff (s : FullMenu → Prop) (a : Bool) :
    FrameConsequence (fun _ r => Symmetric r) s a tMC ↔ s .gen ∧ s .complement ∧ s .rigid :=
  collapse_iff _ (fun _ _ h _ _ _ => h _ _) s a

theorem necessary_symmetric_iff (s : FullMenu → Prop) (a : Bool) :
    FrameConsequence (fun _ r => Symmetric r) s a (tNecEx a) ↔ s .gen ∧ s .complement :=
  necessary_iff _ (fun _ _ h _ _ _ => h _ _) s a

#print axioms collapse_S5_iff
#print axioms necessary_S5_iff
#print axioms collapse_symmetric_iff
#print axioms necessary_symmetric_iff
end Programme.«20261021-1639-ontological».Atlas.V2DeepFrames
