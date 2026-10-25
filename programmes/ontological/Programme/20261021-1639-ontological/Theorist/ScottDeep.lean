import Programme.«20261021-1639-ontological».Theorist.ScottBridge
import Programme.«20261021-1639-ontological».Theorist.SymmetricFinite

/-! Scott's axioms in plain deep Henkin semantics (K36 closed models), no interface.
(1) Every closed model has a canonical presentation `canon m`, which satisfies Clo3; with the
    bridges of ScottBridge, `deep_mc_scott`: in every definably closed extensional Henkin model on
    a symmetric frame, deep validity of A1a, A1b, A2, A3, A4, A5 implies deep validity of modal
    collapse (`∀p. p → □p`), both guard regimes.
(2) `deep_drop_*`: each of the six is independent of the other five plus collapse, witnessed by
    closed Henkin models on S5 frames (the K49 witnesses, closed by P252/P267). -/

namespace Programme.«20261021-1639-ontological».Theorist.ScottDeep
open Programme.«20261021-1639-ontological».Deep Programme.«20261021-1639-ontological».Deep.Henkin Programme.«20261021-1639-ontological».Theorist.HenkinScott
open Programme.«20261021-1639-ontological».Theorist.HenkinMinimal Programme.«20261021-1639-ontological».Theorist.SymmetricModels
open Programme.«20261021-1639-ontological».Theorist.SymmetricFinite Programme.«20261021-1639-ontological».Theorist.ScottBridge

variable {W : Type} (m : Henkin.Model OntConst W)

def img (P : m.frame.D Property) : m.frame.D .entity → W → Prop :=
  fun x => m.frame.truth (m.frame.app P x)

/-- Canonical truth-image presentation of a closed model. -/
def canon : GModel W (m.frame.D .entity) where
  rel := m.frame.rel
  actual x w := m.frame.truth (m.frame.app (m.interp OntConst.actual) x) w
  adm f := ∃ P, img m P = f
  admP p := ∃ q, m.frame.truth q = p
  positive f w := ∃ P, img m P = f ∧ m.frame.truth (m.frame.app (m.interp OntConst.positive) P) w

theorem img_inj (P Q : m.frame.D Property) (h : img m P = img m Q) : P = Q :=
  m.frame.ext P Q fun x => m.frame.truth_inj _ _ (congrFun h x)

theorem canon_presents : Presents m (canon m) :=
  ⟨fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl,
    fun P _ => ⟨fun h => ⟨P, rfl, h⟩, fun ⟨Q, hQ, h⟩ => img_inj m Q P hQ ▸ h⟩⟩

variable {m} {gm : GModel W (m.frame.D .entity)}

/-- The four closure facts of `Clo3` are denotations of definable terms. -/
theorem clo3_of_presents (hp : Presents m gm) (a : Bool) (ρ : Assignment m.frame []) :
    Clo3 gm a := by
  refine ⟨fun p ha => ?_, fun s ha => ?_, ?_, ?_⟩
  · obtain ⟨P, rfl⟩ := (hp.2.1 p).2 ha
    refine (hp.2.1 _).1 ⟨translate m.frame m.interp
      (.lam (neg (.app v1 v0)) : T [Property] Property) (push ρ P), ?_⟩
    rw [img_lam]; funext x w
    simp only [sem_neg, sem_app, tr_v0, tr_v1]
  · obtain ⟨q, rfl⟩ := (hp.1 s).2 ha
    exact (hp.2.1 _).1 ⟨translate m.frame m.interp
      (.lam v1 : T [.prop] Property) (push ρ q), by rw [img_lam]; rfl⟩
  · exact (hp.2.1 _).1 ⟨_, img_NE hp a ρ⟩
  · exact (hp.2.1 _).1 ⟨_, img_G hp ρ⟩

/-- K49 in deep Henkin semantics: Scott's six axioms force collapse on symmetric frames in every
definably closed extensional Henkin model. -/
theorem deep_mc_scott (a : Bool) (ρ : Assignment m.frame [])
    (symm : ∀ w v, m.frame.rel w v → m.frame.rel v w)
    (h1a : DeepValid m ρ tA1a) (h1b : DeepValid m ρ tA1b) (h2 : DeepValid m ρ (tA2 a))
    (h3 : DeepValid m ρ tA3) (h4 : DeepValid m ρ tA4) (h5 : DeepValid m ρ (tA5 a)) :
    DeepValid m ρ tMC := by
  have hp := canon_presents m
  exact (bridge_MC hp ρ).2 (mcAdm_scott (canon m) a (clo3_of_presents hp a ρ) symm
    ((bridge_A1a hp ρ).1 h1a) ((bridge_A1b hp ρ).1 h1b) ((bridge_A2 hp a ρ).1 h2)
    ((bridge_A3 hp ρ).1 h3) ((bridge_A4 hp ρ).1 h4) ((bridge_A5 hp a ρ).1 h5))

/-- Deep validity profile of a closed model, read through any presentation. -/
theorem profile (hp : Presents m gm) (a : Bool) (ρ : Assignment m.frame []) :
    (DeepValid m ρ tA1a ↔ A1a gm) ∧ (DeepValid m ρ tA1b ↔ A1b gm) ∧
    (DeepValid m ρ (tA2 a) ↔ A2 gm a) ∧ (DeepValid m ρ tA3 ↔ A3 gm) ∧
    (DeepValid m ρ tA4 ↔ A4 gm) ∧ (DeepValid m ρ (tA5 a) ↔ A5 gm a) ∧
    (DeepValid m ρ tMC ↔ MCadm gm) :=
  ⟨bridge_A1a hp ρ, bridge_A1b hp ρ, bridge_A2 hp a ρ, bridge_A3 hp ρ, bridge_A4 hp ρ,
    bridge_A5 hp a ρ, bridge_MC hp ρ⟩

/-- Deletion statement: a closed model on a symmetric frame validating five of the six deep
axioms, not the sixth, and not deep collapse. -/
def Drop (m : Henkin.Model OntConst W) (a : Bool) (ρ : Assignment m.frame [])
    (d1a d1b d2 d3 d4 d5 : Bool) : Prop :=
  (∀ w v, m.frame.rel w v → m.frame.rel v w) ∧
  (DeepValid m ρ tA1a ↔ d1a = true) ∧ (DeepValid m ρ tA1b ↔ d1b = true) ∧
  (DeepValid m ρ (tA2 a) ↔ d2 = true) ∧ (DeepValid m ρ tA3 ↔ d3 = true) ∧
  (DeepValid m ρ tA4 ↔ d4 = true) ∧ (DeepValid m ρ (tA5 a) ↔ d5 = true) ∧
  ¬ DeepValid m ρ tMC

theorem deep_drop_A1a (a : Bool) (ρ) : Drop (fullModel ScottTable.allPos) a ρ false true true true true true := by
  obtain ⟨hp, -, sy, n1a, h1b, h2, h3, h4, h5, nmc⟩ := closed_drop_A1a a
  obtain ⟨b1a, b1b, b2, b3, b4, b5, bmc⟩ := profile hp a ρ
  exact ⟨sy, b1a.trans (iff_of_false n1a (by simp)), b1b.trans (iff_of_true h1b rfl),
    b2.trans (iff_of_true h2 rfl), b3.trans (iff_of_true h3 rfl), b4.trans (iff_of_true h4 rfl),
    b5.trans (iff_of_true h5 rfl), fun h => nmc (bmc.1 h)⟩

theorem deep_drop_A2 (a : Bool) (ρ) : Drop (fullModel ScottTable.twoPos) a ρ true true false true true true := by
  obtain ⟨hp, -, sy, h1a, h1b, n2, h3, h4, h5, nmc⟩ := closed_drop_A2 a
  obtain ⟨b1a, b1b, b2, b3, b4, b5, bmc⟩ := profile hp a ρ
  exact ⟨sy, b1a.trans (iff_of_true h1a rfl), b1b.trans (iff_of_true h1b rfl),
    b2.trans (iff_of_false n2 (by simp)), b3.trans (iff_of_true h3 rfl), b4.trans (iff_of_true h4 rfl),
    b5.trans (iff_of_true h5 rfl), fun h => nmc (bmc.1 h)⟩

theorem deep_drop_A5 (a : Bool) (ρ) : Drop (fullModel ScottTable.princ) a ρ true true true true true false := by
  obtain ⟨hp, -, sy, h1a, h1b, h2, h3, h4, n5, nmc⟩ := closed_drop_A5 a
  obtain ⟨b1a, b1b, b2, b3, b4, b5, bmc⟩ := profile hp a ρ
  exact ⟨sy, b1a.trans (iff_of_true h1a rfl), b1b.trans (iff_of_true h1b rfl),
    b2.trans (iff_of_true h2 rfl), b3.trans (iff_of_true h3 rfl), b4.trans (iff_of_true h4 rfl),
    b5.trans (iff_of_false n5 (by simp)), fun h => nmc (bmc.1 h)⟩

theorem deep_drop_A1b (a : Bool) (ρ) : Drop cantorModel a ρ true false true true true true := by
  obtain ⟨hp, -, sy, h1a, n1b, h2, h3, h4, h5, nmc⟩ := closed_drop_A1b a
  obtain ⟨b1a, b1b, b2, b3, b4, b5, bmc⟩ := profile hp a ρ
  exact ⟨sy, b1a.trans (iff_of_true h1a rfl), b1b.trans (iff_of_false n1b (by simp)),
    b2.trans (iff_of_true h2 rfl), b3.trans (iff_of_true h3 rfl), b4.trans (iff_of_true h4 rfl),
    b5.trans (iff_of_true h5 rfl), fun h => nmc (bmc.1 h)⟩

theorem deep_drop_A4 (a : Bool) (ρ) : Drop cantorCWModel a ρ true true true true false true := by
  obtain ⟨hp, -, sy, h1a, h1b, h2, h3, n4, h5, nmc⟩ := closed_drop_A4 a
  obtain ⟨b1a, b1b, b2, b3, b4, b5, bmc⟩ := profile hp a ρ
  exact ⟨sy, b1a.trans (iff_of_true h1a rfl), b1b.trans (iff_of_true h1b rfl),
    b2.trans (iff_of_true h2 rfl), b3.trans (iff_of_true h3 rfl), b4.trans (iff_of_false n4 (by simp)),
    b5.trans (iff_of_true h5 rfl), fun h => nmc (bmc.1 h)⟩

theorem deep_drop_A3 (a : Bool) (ρ) : Drop ternModel a ρ true true true false true true := by
  obtain ⟨hp, -, sy, h1a, h1b, h2, n3, h4, h5, nmc⟩ := closed_drop_A3 a
  obtain ⟨b1a, b1b, b2, b3, b4, b5, bmc⟩ := profile hp a ρ
  exact ⟨sy, b1a.trans (iff_of_true h1a rfl), b1b.trans (iff_of_true h1b rfl),
    b2.trans (iff_of_true h2 rfl), b3.trans (iff_of_false n3 (by simp)), b4.trans (iff_of_true h4 rfl),
    b5.trans (iff_of_true h5 rfl), fun h => nmc (bmc.1 h)⟩

#print axioms canon_presents
#print axioms clo3_of_presents
#print axioms deep_mc_scott
#print axioms profile
#print axioms deep_drop_A1a
#print axioms deep_drop_A2
#print axioms deep_drop_A5
#print axioms deep_drop_A1b
#print axioms deep_drop_A4
#print axioms deep_drop_A3
end Programme.«20261021-1639-ontological».Theorist.ScottDeep
