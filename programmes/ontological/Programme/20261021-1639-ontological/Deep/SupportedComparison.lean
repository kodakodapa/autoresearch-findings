import Programme.«20261021-1639-ontological».Deep.SupportedFrame
import Programme.«20261021-1639-ontological».Theorist.SymmetricModels

/-! A truth-image comparison, not an identification of all higher carriers. -/
namespace Programme.«20261021-1639-ontological».Deep.CantorSupport
open Programme.«20261021-1639-ontological».Theorist.SymmetricModels

theorem supported_cantor_image (p : World → Prop) :
    (∃ q : supportedFrame.D .prop, supportedFrame.truth q = p) ↔
    (∃ q : cantorModel.frame.D .prop, cantorModel.frame.truth q = p) := by
  exact (frame_prop_exact p).trans (cantor_presentation.1 p).symm

noncomputable def toClosed (p : supportedFrame.D .prop) : cantorModel.frame.D .prop :=
  cantorModel.frame.reify (supportedFrame.truth p)

noncomputable def fromClosed (p : cantorModel.frame.D .prop) : supportedFrame.D .prop :=
  supportedFrame.reify (cantorModel.frame.truth p)

theorem toClosed_truth (p : supportedFrame.D .prop) :
    cantorModel.frame.truth (toClosed p) = supportedFrame.truth p :=
  cantorModel.frame.reify_spec _ ((supported_cantor_image _).mp ⟨p, rfl⟩)

theorem fromClosed_truth (p : cantorModel.frame.D .prop) :
    supportedFrame.truth (fromClosed p) = cantorModel.frame.truth p :=
  supportedFrame.reify_spec _ ((supported_cantor_image _).mpr ⟨p, rfl⟩)

theorem from_to (p : supportedFrame.D .prop) : fromClosed (toClosed p) = p := by
  apply supportedFrame.truth_inj
  rw [fromClosed_truth, toClosed_truth]

theorem to_from (p : cantorModel.frame.D .prop) : toClosed (fromClosed p) = p := by
  apply cantorModel.frame.truth_inj
  rw [toClosed_truth, fromClosed_truth]

/-- Any proposition quantifier whose body depends on the truth image transports. -/
theorem forall_truth_transport (F : (World → Prop) → Prop) :
    (∀ p : supportedFrame.D .prop, F (supportedFrame.truth p)) ↔
    (∀ p : cantorModel.frame.D .prop, F (cantorModel.frame.truth p)) := by
  constructor
  · intro h p
    have hp := h (fromClosed p)
    rwa [fromClosed_truth] at hp
  · intro h p
    have hp := h (toClosed p)
    rwa [toClosed_truth] at hp

/-- The K53 noncollapse proposition persists in the definably closed construction. -/
theorem closed_noncollapse : ∃ p : cantorModel.frame.D .prop, ∃ w,
    cantorModel.frame.truth p w ∧
      ¬ (∀ v, cantorModel.frame.rel w v → cantorModel.frame.truth p v) := by
  obtain ⟨p, w, hp, hn⟩ := frame_noncollapse
  refine ⟨toClosed p, w, ?_, ?_⟩
  · rw [toClosed_truth]; exact hp
  · intro h
    apply hn
    intro v _
    have hv := h v True.intro
    rw [toClosed_truth] at hv
    exact hv

#print axioms supported_cantor_image
#print axioms toClosed_truth
#print axioms fromClosed_truth
#print axioms from_to
#print axioms to_from
#print axioms forall_truth_transport
#print axioms closed_noncollapse
end Programme.«20261021-1639-ontological».Deep.CantorSupport
