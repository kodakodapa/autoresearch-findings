/- Rebased from th P348; subset packaging and T deletion added by pr. -/
import Programme.«20261021-1639-ontological».Atlas.V2DeepTable

/-! Deep variant-2 table over the full six-axiom menu {Ax1, Ax1Gen, Ax2a, Ax2b, Ax3, Ax4}.
* `tAx1`: `∀P Q. 𝒫P → 𝒫Q → 𝒫(λx. P x ∧ Q x)`; `bridge_Ax1`.
* `tAx4 a := tA2 a` (variant-2 Ax4 is Scott's A2); `bridge_Ax4`.
* Every deletion witness of V2DeepTable / V2Deep also validates deep Ax1 and Ax4, except
  `antiM` (fails Ax4); `chainM` replaces it for the Ax1Gen deletion of MC:
  frame `w ↦ true` (non-symmetric), one entity, rigid principal positivity at `((), true)`. -/

namespace Programme.«20261021-1639-ontological».Atlas.V2DeepFull
open Programme.«20261021-1639-ontological».Deep Programme.«20261021-1639-ontological».Deep.Henkin Programme.«20261021-1639-ontological».Atlas.HenkinScott
open Programme.«20261021-1639-ontological».Atlas.SymmetricModels Programme.«20261021-1639-ontological».Atlas.ScottBridge
open Programme.«20261021-1639-ontological».Atlas.ScottDeep Programme.«20261021-1639-ontological».Atlas.V2Deep Programme.«20261021-1639-ontological».Atlas.V2DeepTable
open Programme.«20261021-1639-ontological».Atlas.SymmetricFinite Programme.«20261021-1639-ontological».Atlas.HenkinMinimal

variable {W : Type} {m : Henkin.Model OntConst W} {gm : GModel W (m.frame.D .entity)}

def tAx1 : T [] .prop :=
  .all (a := Property) (.all (a := Property) (.imp (pos v1) (.imp (pos v0)
    (pos (.lam (conj (.app v2 v0) (.app v1 v0)))))))
def tAx4 (a : Bool) : T [] .prop := tA2 a

theorem bridge_Ax1 (hp : Presents m gm) (ρ : Assignment m.frame []) :
    DeepValid m ρ tAx1 ↔ HenkinVariant2.Ax1 gm := by
  rw [deepValid_iff]
  simp only [tAx1, sem_all, sem_imp, sem_conj, sem_pos hp, img_lam, sem_app, tr_v0, tr_v1, tr_v2]
  constructor
  · intro h p q w hpa hqa hpw hqw
    obtain ⟨P, rfl⟩ := (hp.2.1 p).2 hpa
    obtain ⟨Q, rfl⟩ := (hp.2.1 q).2 hqa
    exact h w P Q hpw hqw
  · intro h w P Q hpw hqw
    exact h _ _ w ((hp.2.1 _).1 ⟨P, rfl⟩) ((hp.2.1 _).1 ⟨Q, rfl⟩) hpw hqw

theorem bridge_Ax4 (hp : Presents m gm) (a : Bool) (ρ : Assignment m.frame []) :
    DeepValid m ρ (tAx4 a) ↔ HenkinVariant2.Ax4 gm a := bridge_A2 hp a ρ

/-! ### Ax1 and Ax4 on the existing witnesses. -/

theorem allPos_ax14 (a : Bool) (ρ : Assignment (fullModel allPosM).frame []) :
    DeepValid (fullModel allPosM) ρ tAx1 ∧ DeepValid (fullModel allPosM) ρ (tAx4 a) := by
  have hp := full_presentation allPosM
  exact ⟨(bridge_Ax1 hp ρ).2 fun _ _ _ _ _ _ _ => trivial,
    (bridge_Ax4 hp a ρ).2 fun _ _ _ _ _ _ _ => trivial⟩

theorem free_ax14 (a : Bool) (ρ : Assignment (fullModel freeM).frame []) :
    DeepValid (fullModel freeM) ρ tAx1 ∧ DeepValid (fullModel freeM) ρ (tAx4 a) := by
  have hp := full_presentation freeM
  refine ⟨(bridge_Ax1 hp ρ).2 fun p q w _ _ hp' hq' => FreeUltra.U_good.2.2.2 _ _ hp' hq',
    (bridge_Ax4 hp a ρ).2 fun p q w _ _ hp' hsub => ?_⟩
  exact FreeUltra.U_good.2.2.1 _ _ hp' fun n hn => hsub w trivial n (fun _ => trivial) hn

theorem cw_ax14 (a : Bool) (ρ : Assignment cantorCWModel.frame []) :
    DeepValid cantorCWModel ρ tAx1 ∧ DeepValid cantorCWModel ρ (tAx4 a) := by
  have hp := cantorCW_presentation
  obtain ⟨-, -, -, -, h1, h4, -⟩ := HenkinVariant2.cw_props a
  exact ⟨(bridge_Ax1 hp ρ).2 h1, (bridge_Ax4 hp a ρ).2 h4⟩

theorem swap_ax14 (a : Bool) (ρ : Assignment swapModel.frame []) :
    DeepValid swapModel ρ tAx1 ∧ DeepValid swapModel ρ (tAx4 a) := by
  obtain ⟨hp, -, -, -, -, -, -, h1, h4, -⟩ := closed_swap a
  exact ⟨(bridge_Ax1 hp ρ).2 h1, (bridge_Ax4 hp a ρ).2 h4⟩

/-- `antiM` fails deep Ax4: `⊥` is positive, `⊤` is not. -/
theorem anti_not_ax4 (a : Bool) (ρ : Assignment (fullModel antiM).frame []) :
    ¬ DeepValid (fullModel antiM) ρ (tAx4 a) := by
  have hp := full_presentation antiM
  intro h
  exact ((bridge_Ax4 hp a ρ).1 h HenkinVariant2.botP (fun _ _ => True) true trivial trivial
    (fun h => h) (fun _ _ _ _ h => h.elim)) trivial

/-! ### New Ax1Gen deletion for MC keeping all five other axioms. -/

/-- Worlds `false → true`, `true → true`; one entity; `𝒫 p :⇔ p () true`. -/
def chainM : Programme.«20261021-1639-ontological».Countermodels.Tests.Model Bool Unit :=
  ⟨fun _ v => v = true, fun _ _ => True, fun p _ => p () true⟩

theorem deep_drop_ax1gen_full (a : Bool) (ρ : Assignment (fullModel chainM).frame []) :
    DeepValid (fullModel chainM) ρ tAx1 ∧ DeepValid (fullModel chainM) ρ tAx2a ∧
    DeepValid (fullModel chainM) ρ tA4 ∧ DeepValid (fullModel chainM) ρ (tA5 a) ∧
    DeepValid (fullModel chainM) ρ (tAx4 a) ∧
    ¬ DeepValid (fullModel chainM) ρ tT ∧ ¬ DeepValid (fullModel chainM) ρ tMC ∧
    ¬ DeepValid (fullModel chainM) ρ (tAx1Gen a) := by
  have hp := full_presentation chainM
  have nT : ¬ DeepValid (fullModel chainM) ρ tT := fun h =>
    Bool.noConfusion ((bridge_T hp ρ).1 h (fun w => w = true) trivial false fun _ hv => hv)
  refine ⟨(bridge_Ax1 hp ρ).2 fun _ _ _ _ _ hp' hq' => ⟨hp', hq'⟩,
    (bridge_Ax2a hp ρ).2 fun p _ _ =>
      ⟨(Classical.em (p () true)).elim Or.inl fun h => Or.inr h, fun ⟨h, hn⟩ => hn h⟩,
    (bridge_A4 hp ρ).2 fun _ _ _ h _ _ => h, (bridge_A5 hp a ρ).2 fun _ => ?_,
    (bridge_Ax4 hp a ρ).2 fun _ _ _ _ _ hp' hsub => hsub true rfl () (fun _ => trivial) hp',
    nT, fun h => Bool.noConfusion ((bridge_MC hp ρ).1 h (fun w => w = false) trivial false rfl
      true rfl), fun h => nT (deep_v2 a ρ h ((bridge_Ax2a hp ρ).2 fun p _ _ =>
      ⟨(Classical.em (p () true)).elim Or.inl fun h => Or.inr h, fun ⟨h, hn⟩ => hn h⟩)).1⟩
  intro p _ hess v hv
  cases hv
  exact ⟨(), fun _ => trivial, hess.1⟩

#print axioms bridge_Ax1
#print axioms bridge_Ax4
#print axioms allPos_ax14
#print axioms free_ax14
#print axioms cw_ax14
#print axioms swap_ax14
#print axioms anti_not_ax4
#print axioms deep_drop_ax1gen_full


/-- All-positive dead-end model supplies the missing Ax2a deletion for T. -/
def deadM : Programme.«20261021-1639-ontological».Countermodels.Tests.Model Unit Unit :=
  ⟨fun _ _ => False, fun _ _ => True, fun _ _ => True⟩

theorem deep_drop_ax2a_T (a : Bool) (ρ : Assignment (fullModel deadM).frame []) :
    DeepValid (fullModel deadM) ρ tAx1 ∧
    DeepValid (fullModel deadM) ρ (tAx1Gen a) ∧
    DeepValid (fullModel deadM) ρ tA4 ∧ DeepValid (fullModel deadM) ρ (tA5 a) ∧
    DeepValid (fullModel deadM) ρ (tAx4 a) ∧
    ¬ DeepValid (fullModel deadM) ρ tAx2a ∧ ¬ DeepValid (fullModel deadM) ρ tT := by
  have hp := full_presentation deadM
  exact ⟨(bridge_Ax1 hp ρ).2 fun _ _ _ _ _ _ _ => trivial,
    (bridge_Ax1Gen hp a ρ).2 fun _ _ _ _ _ _ _ => trivial,
    (bridge_A4 hp ρ).2 fun _ _ _ _ _ _ => trivial,
    (bridge_A5 hp a ρ).2 fun _ => trivial,
    (bridge_Ax4 hp a ρ).2 fun _ _ _ _ _ _ _ => trivial,
    fun h => ((bridge_Ax2a hp ρ).1 h HenkinVariant2.botP () trivial).2 ⟨trivial, trivial⟩,
    fun h => (bridge_T hp ρ).1 h (fun _ => False) trivial () (fun _ hr => hr.elim)⟩

inductive FullMenu where
  | meet | gen | complement | rigid | nepos | up
  deriving DecidableEq

def fullAxiomTerm (a : Bool) : FullMenu → T [] .prop
  | .meet => tAx1
  | .gen => tAx1Gen a
  | .complement => tAx2a
  | .rigid => tA4
  | .nepos => tA5 a
  | .up => tAx4 a

def FullConsequence (s : FullMenu → Prop) (a : Bool) (t : T [] .prop) : Prop :=
  ∀ (W : Type) (m : Henkin.Model OntConst W) (ρ : Assignment m.frame []),
    (∀ i, s i → DeepValid m ρ (fullAxiomTerm a i)) → DeepValid m ρ t

theorem necessary_iff (s : FullMenu → Prop) (a : Bool) :
    FullConsequence s a (tNecEx a) ↔ s .gen ∧ s .complement := by
  classical
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · apply Classical.byContradiction
      intro hn
      obtain ⟨_, h2, hb, h3, hno, _⟩ := deep_drop_ax1gen a (emptyAssignment _)
      obtain ⟨h1, h4⟩ := free_ax14 a (emptyAssignment _)
      apply hno
      apply h Unit (fullModel freeM) (emptyAssignment _)
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
      obtain ⟨_, hg, hb, h3, _, hno, _⟩ := deep_drop_ax2a a (emptyAssignment _)
      obtain ⟨h1, h4⟩ := allPos_ax14 a (emptyAssignment _)
      apply hno
      apply h Bool (fullModel allPosM) (emptyAssignment _)
      intro i hi
      cases i with
      | meet => exact h1
      | gen => exact hg
      | complement => exact False.elim (hn hi)
      | rigid => exact hb
      | nepos => exact h3
      | up => exact h4
  · rintro ⟨hg, h2⟩ W m ρ h
    exact (deep_v2 a ρ (h .gen hg) (h .complement h2)).2

theorem collapse_iff (s : FullMenu → Prop) (a : Bool) :
    FullConsequence s a tMC ↔ s .gen ∧ s .complement ∧ s .rigid := by
  classical
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · apply Classical.byContradiction
      intro hn
      obtain ⟨h1, h2, hb, h3, h4, _, hno, _⟩ := deep_drop_ax1gen_full a (emptyAssignment _)
      apply hno
      apply h Bool (fullModel chainM) (emptyAssignment _)
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
      obtain ⟨_, hg, hb, h3, _, _, hno⟩ := deep_drop_ax2a a (emptyAssignment _)
      obtain ⟨h1, h4⟩ := allPos_ax14 a (emptyAssignment _)
      apply hno
      apply h Bool (fullModel allPosM) (emptyAssignment _)
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
      obtain ⟨_, hg, h2, h3, _, _, hno⟩ := deep_cw a (emptyAssignment _)
      obtain ⟨h1, h4⟩ := cw_ax14 a (emptyAssignment _)
      apply hno
      apply h _ cantorCWModel (emptyAssignment _)
      intro i hi
      cases i with
      | meet => exact h1
      | gen => exact hg
      | complement => exact h2
      | rigid => exact False.elim (hn hi)
      | nepos => exact h3
      | up => exact h4
  · rintro ⟨hg, h2, hb⟩ W m ρ h
    exact deep_v2_mc a ρ (h .gen hg) (h .complement h2) (h .rigid hb)

theorem T_iff (s : FullMenu → Prop) (a : Bool) :
    FullConsequence s a tT ↔ s .gen ∧ s .complement := by
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
      | meet => exact h1
      | gen => exact False.elim (hn hi)
      | complement => exact h2
      | rigid => exact hb
      | nepos => exact h3
      | up => exact h4
    · apply Classical.byContradiction
      intro hn
      obtain ⟨h1, hg, hb, h3, h4, _, hno⟩ := deep_drop_ax2a_T a (emptyAssignment _)
      apply hno
      apply h Unit (fullModel deadM) (emptyAssignment _)
      intro i hi
      cases i with
      | meet => exact h1
      | gen => exact hg
      | complement => exact False.elim (hn hi)
      | rigid => exact hb
      | nepos => exact h3
      | up => exact h4
  · rintro ⟨hg, h2⟩ W m ρ h
    exact (deep_v2 a ρ (h .gen hg) (h .complement h2)).1

#print axioms deep_drop_ax2a_T
#print axioms necessary_iff
#print axioms collapse_iff
#print axioms T_iff
end Programme.«20261021-1639-ontological».Atlas.V2DeepFull
