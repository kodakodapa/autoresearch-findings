/- Rebased from th P326. Uniform actualist/possibilist guards; four-axiom menu only. -/
import Programme.«20261021-1639-ontological».Atlas.V2Deep
import Programme.«20261021-1639-ontological».Atlas.FreeUltra

/-! Deep variant-2 deletion witnesses (closed K36 models, full carriers via `trivSym`).
* `deep_drop_ax2a`: two-world S5, all-positive: deep Ax1Gen, Ax2b (`tA4`), Ax3 (`tA5`) valid,
  deep Ax2a, `□∃ᵍ G` and MC not valid.
* `deep_drop_ax1gen`: one world, ℕ entities, free-ultrafilter positivity: deep Ax2a, Ax2b, Ax3
  valid, deep `□∃ᵍ G` not valid, hence (by `deep_v2`) deep Ax1Gen not valid.
Both directions of each failure go through the presentation bridges; no interface hypothesis. -/

namespace Programme.«20261021-1639-ontological».Atlas.V2DeepTable
open Programme.«20261021-1639-ontological».Deep Programme.«20261021-1639-ontological».Deep.Henkin Programme.«20261021-1639-ontological».Atlas.HenkinScott
open Programme.«20261021-1639-ontological».Atlas.SymmetricModels Programme.«20261021-1639-ontological».Atlas.ScottBridge
open Programme.«20261021-1639-ontological».Atlas.ScottDeep Programme.«20261021-1639-ontological».Atlas.V2Deep
open Programme.«20261021-1639-ontological».Atlas.SymmetricFinite Programme.«20261021-1639-ontological».Atlas.HenkinMinimal

def allPosM : Programme.«20261021-1639-ontological».Countermodels.Tests.Model Bool Unit := ⟨fun _ _ => True, fun _ _ => True, fun _ _ => True⟩
def freeM : Programme.«20261021-1639-ontological».Countermodels.Tests.Model Unit Nat :=
  ⟨fun _ _ => True, fun _ _ => True, fun p w => FreeUltra.U (fun n => p n w)⟩

theorem deep_drop_ax2a (a : Bool) (ρ : Assignment (fullModel allPosM).frame []) :
    (∀ w v, (fullModel allPosM).frame.rel w v) ∧
    DeepValid (fullModel allPosM) ρ (tAx1Gen a) ∧ DeepValid (fullModel allPosM) ρ tA4 ∧
    DeepValid (fullModel allPosM) ρ (tA5 a) ∧ ¬ DeepValid (fullModel allPosM) ρ tAx2a ∧
    ¬ DeepValid (fullModel allPosM) ρ (tNecEx a) ∧ ¬ DeepValid (fullModel allPosM) ρ tMC := by
  have hp := full_presentation allPosM
  refine ⟨fun w v => (hp.2.2.1 w v).2 trivial,
    (bridge_Ax1Gen hp a ρ).2 fun _ _ _ _ _ _ _ => trivial,
    (bridge_A4 hp ρ).2 fun _ _ _ _ _ _ => trivial, (bridge_A5 hp a ρ).2 fun _ => trivial,
    fun h => ((bridge_Ax2a hp ρ).1 h HenkinVariant2.botP false trivial).2 ⟨trivial, trivial⟩,
    fun h => ?_, fun h => ?_⟩
  · obtain ⟨x, _, hg⟩ := (bridge_NecEx hp a ρ).1 h false false trivial
    exact hg HenkinVariant2.botP trivial trivial
  · exact Bool.noConfusion ((bridge_MC hp ρ).1 h (fun w => w = false) trivial false rfl true trivial)

theorem free_ax2a : HenkinVariant2.Ax2a (full freeM) := by
  intro p w _
  refine ⟨FreeUltra.U_ultra _, fun ⟨hp, hn⟩ => ?_⟩
  exact FreeUltra.U_good.2.1 (FreeUltra.U_good.2.2.1 _ _ (FreeUltra.U_good.2.2.2 _ _ hp hn)
    (fun _ h => h.2 h.1))

theorem deep_drop_ax1gen (a : Bool) (ρ : Assignment (fullModel freeM).frame []) :
    (∀ w v, (fullModel freeM).frame.rel w v) ∧
    DeepValid (fullModel freeM) ρ tAx2a ∧ DeepValid (fullModel freeM) ρ tA4 ∧
    DeepValid (fullModel freeM) ρ (tA5 a) ∧ ¬ DeepValid (fullModel freeM) ρ (tNecEx a) ∧
    ¬ DeepValid (fullModel freeM) ρ (tAx1Gen a) := by
  have hp := full_presentation freeM
  have d2 := (bridge_Ax2a hp ρ).2 free_ax2a
  have nne : ¬ DeepValid (fullModel freeM) ρ (tNecEx a) := fun h => by
    obtain ⟨x, _, hg⟩ := (bridge_NecEx hp a ρ).1 h () () trivial
    exact hg (fun n _ => n ≠ x) trivial (FreeUltra.U_frechet _ (PrincipalAxis.cof_ne x)) rfl
  refine ⟨fun w v => (hp.2.2.1 w v).2 trivial, d2,
    (bridge_A4 hp ρ).2 fun p w _ hp' v _ => by cases w; cases v; exact hp', ?_, nne,
    fun h => nne (deep_v2 a ρ h d2).2⟩
  refine (bridge_A5 hp a ρ).2 fun w => ?_
  apply FreeUltra.U_good.2.2.1 _ _ FreeUltra.U_good.1
  intro n _ p _ hp' v _
  cases w; cases v
  exact ⟨n, fun _ => trivial, hp'.1⟩

#print axioms deep_drop_ax2a
#print axioms deep_drop_ax1gen

/-- Rigid principal positivity at `((), true)`, two worlds, one entity: deep Ax2a and Ax2b
(`tA4`) valid, deep `□∃ᵍ G`, MC and Ax1Gen not valid. With `deep_drop_ax2a` and `deep_cw` this
makes `{Ax1Gen, Ax2a, Ax2b}` a minimal deep collapse set. -/
def rigidM : Programme.«20261021-1639-ontological».Countermodels.Tests.Model Bool Unit := ⟨fun _ _ => True, fun _ _ => True, fun p _ => p () true⟩

theorem deep_drop_ax1gen_mc (a : Bool) (ρ : Assignment (fullModel rigidM).frame []) :
    (∀ w v, (fullModel rigidM).frame.rel w v) ∧
    DeepValid (fullModel rigidM) ρ tAx2a ∧ DeepValid (fullModel rigidM) ρ tA4 ∧
    ¬ DeepValid (fullModel rigidM) ρ (tNecEx a) ∧ ¬ DeepValid (fullModel rigidM) ρ tMC ∧
    ¬ DeepValid (fullModel rigidM) ρ (tAx1Gen a) := by
  have hp := full_presentation rigidM
  have d2 := (bridge_Ax2a hp ρ).2 fun p _ _ =>
    ⟨Classical.em (p () true), fun ⟨h, hn⟩ => hn h⟩
  have nne : ¬ DeepValid (fullModel rigidM) ρ (tNecEx a) := fun h => by
    obtain ⟨x, _, hg⟩ := (bridge_NecEx hp a ρ).1 h true false trivial
    exact Bool.noConfusion (hg (fun _ v => v = true) trivial rfl)
  exact ⟨fun w v => (hp.2.2.1 w v).2 trivial, d2,
    (bridge_A4 hp ρ).2 fun _ _ _ h _ _ => h, nne,
    fun h => Bool.noConfusion ((bridge_MC hp ρ).1 h (fun w => w = true) trivial true rfl false trivial),
    fun h => nne (deep_v2 a ρ h d2).2⟩

#print axioms deep_drop_ax1gen_mc

/-- Rigid anti-principal positivity `𝒫 p :⇔ ¬ p () true`, two worlds, one entity: necessary
existence (NE) is empty at every world, hence positive, so deep Ax2a, Ax2b and Ax3 are valid while
deep `□∃ᵍ G`, MC and Ax1Gen are not. So `{Ax1Gen, Ax2a, Ax2b}` is the unique minimal deep MC set. -/
def antiM : Programme.«20261021-1639-ontological».Countermodels.Tests.Model Bool Unit := ⟨fun _ _ => True, fun _ _ => True, fun p _ => ¬ p () true⟩

theorem deep_drop_ax1gen_mc3 (a : Bool) (ρ : Assignment (fullModel antiM).frame []) :
    (∀ w v, (fullModel antiM).frame.rel w v) ∧
    DeepValid (fullModel antiM) ρ tAx2a ∧ DeepValid (fullModel antiM) ρ tA4 ∧
    DeepValid (fullModel antiM) ρ (tA5 a) ∧
    ¬ DeepValid (fullModel antiM) ρ (tNecEx a) ∧ ¬ DeepValid (fullModel antiM) ρ tMC ∧
    ¬ DeepValid (fullModel antiM) ρ (tAx1Gen a) := by
  have hp := full_presentation antiM
  have d2 := (bridge_Ax2a hp ρ).2 fun p _ _ =>
    ⟨(Classical.em (p () true)).elim (fun h => Or.inr fun hn => hn h) Or.inl,
      fun ⟨h, hn⟩ => hn h⟩
  have nne : ¬ DeepValid (fullModel antiM) ρ (tNecEx a) := fun h => by
    obtain ⟨x, _, hg⟩ := (bridge_NecEx hp a ρ).1 h true true trivial
    exact hg HenkinVariant2.botP trivial (fun h => h)
  refine ⟨fun w v => (hp.2.2.1 w v).2 trivial, d2,
    (bridge_A4 hp ρ).2 fun _ _ _ h _ _ => h, (bridge_A5 hp a ρ).2 fun _ hne => ?_, nne,
    fun h => Bool.noConfusion ((bridge_MC hp ρ).1 h (fun w => w = true) trivial true rfl false trivial),
    fun h => nne (deep_v2 a ρ h d2).2⟩
  obtain ⟨y, _, hy⟩ := hne (fun _ v => v = true) trivial
    ⟨rfl, fun q _ hq v _ y _ hv => by cases y; cases hv; exact hq⟩ false trivial
  exact Bool.noConfusion hy

#print axioms deep_drop_ax1gen_mc3
/-- Exactly the four deep axioms audited here; Ax1 and Ax4 are outside this menu. -/
inductive Menu where
  | gen | complement | rigid | nepos
  deriving DecidableEq

def axiomTerm (a : Bool) : Menu → T [] .prop
  | .gen => tAx1Gen a
  | .complement => tAx2a
  | .rigid => tA4
  | .nepos => tA5 a

def Consequence (s : Menu → Prop) (a : Bool) (t : T [] .prop) : Prop :=
  ∀ (W : Type) (m : Henkin.Model OntConst W) (ρ : Assignment m.frame []),
    (∀ i, s i → DeepValid m ρ (axiomTerm a i)) → DeepValid m ρ t

def emptyAssignment (m : Henkin.Model OntConst W) : Assignment m.frame [] :=
  fun v => nomatch v

/-- Exact necessary-existence classification of all sixteen subsets, arbitrary frames. -/
theorem necessary_iff (s : Menu → Prop) (a : Bool) :
    Consequence s a (tNecEx a) ↔ s .gen ∧ s .complement := by
  classical
  constructor
  · intro h
    constructor
    · apply Classical.byContradiction
      intro hn
      obtain ⟨_, h2, hb, h3, hne, _⟩ := deep_drop_ax1gen a (emptyAssignment _)
      apply hne
      apply h Unit (fullModel freeM) (emptyAssignment _)
      intro i hi
      cases i with
      | gen => exact False.elim (hn hi)
      | complement => exact h2
      | rigid => exact hb
      | nepos => exact h3
    · apply Classical.byContradiction
      intro hn
      obtain ⟨_, hg, hb, h3, _, hne, _⟩ := deep_drop_ax2a a (emptyAssignment _)
      apply hne
      apply h Bool (fullModel allPosM) (emptyAssignment _)
      intro i hi
      cases i with
      | gen => exact hg
      | complement => exact False.elim (hn hi)
      | rigid => exact hb
      | nepos => exact h3
  · rintro ⟨hg, h2⟩ W m ρ h
    exact (deep_v2 a ρ (h .gen hg) (h .complement h2)).2

/-- Exact modal-collapse classification of all sixteen subsets, arbitrary frames. -/
theorem collapse_iff (s : Menu → Prop) (a : Bool) :
    Consequence s a tMC ↔ s .gen ∧ s .complement ∧ s .rigid := by
  classical
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · apply Classical.byContradiction
      intro hn
      obtain ⟨_, h2, hb, h3, _, hmc, _⟩ := deep_drop_ax1gen_mc3 a (emptyAssignment _)
      apply hmc
      apply h Bool (fullModel antiM) (emptyAssignment _)
      intro i hi
      cases i with
      | gen => exact False.elim (hn hi)
      | complement => exact h2
      | rigid => exact hb
      | nepos => exact h3
    · apply Classical.byContradiction
      intro hn
      obtain ⟨_, hg, hb, h3, _, _, hmc⟩ := deep_drop_ax2a a (emptyAssignment _)
      apply hmc
      apply h Bool (fullModel allPosM) (emptyAssignment _)
      intro i hi
      cases i with
      | gen => exact hg
      | complement => exact False.elim (hn hi)
      | rigid => exact hb
      | nepos => exact h3
    · apply Classical.byContradiction
      intro hn
      obtain ⟨_, hg, h2, h3, _, _, hmc⟩ := deep_cw a (emptyAssignment _)
      apply hmc
      apply h _ cantorCWModel (emptyAssignment _)
      intro i hi
      cases i with
      | gen => exact hg
      | complement => exact h2
      | rigid => exact False.elim (hn hi)
      | nepos => exact h3
  · rintro ⟨hg, h2, hb⟩ W m ρ h
    exact deep_v2_mc a ρ (h .gen hg) (h .complement h2) (h .rigid hb)

#print axioms necessary_iff
#print axioms collapse_iff
end Programme.«20261021-1639-ontological».Atlas.V2DeepTable
