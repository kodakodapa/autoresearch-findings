import Programme.«20261021-1639-ontological».Deep.SupportedArrows
import Programme.«20261021-1639-ontological».Deep.Henkin

namespace Programme.«20261021-1639-ontological».Deep.CantorSupport

/-- Total selectors are arbitrary off their representable domains. -/
noncomputable def selectSupported (A : Type) (P : A → Prop) (h : ∃ x, P x) :
    A → {x // P x} := by
  classical
  exact fun x => if hx : P x then ⟨x, hx⟩ else ⟨Classical.choose h, Classical.choose_spec h⟩

theorem selectSupported_val (P : A → Prop) (h : ∃ x, P x) (x : A) (hx : P x) :
    (selectSupported A P h x).val = x := by
  simp [selectSupported, hx]

noncomputable def supportedFrame : Henkin.Frame World where
  D := fun a => (typedCarrier a).D
  nonempty := fun a => (typedCarrier a).inhabited
  app := fun f x => f.val x
  ext := fun f g h => Subtype.ext (funext h)
  truth := fun p => p.val
  truth_inj := fun _ _ h => Subtype.ext h
  abstract := fun {a b} f => selectSupported _ _ (by
    obtain ⟨g⟩ := (arrowCarrier (typedCarrier a) (typedCarrier b)).inhabited
    exact ⟨g.val, g.property⟩) f
  abstract_spec := by
    intro a b f hf x
    obtain ⟨g, hg⟩ := hf
    have hfg : g.val = f := funext hg
    have hp : ∃ n, Supported (arrowAction (typedCarrier a).action
        (typedCarrier b).action).toMaskAction n f := hfg ▸ g.property
    exact congrFun (selectSupported_val _ _ f hp) x
  reify := selectSupported _ _ ⟨fun _ => False, 0, fun _ _ => rfl⟩
  reify_spec := by
    intro p hp
    obtain ⟨q, hq⟩ := hp
    exact selectSupported_val _ _ p (hq ▸ q.property)
  rel := fun _ _ => True

abbrev SProp := propCarrier.D

/-- Constants and logical operators have supported outputs. -/
def constantProp (p : Prop) : SProp := ⟨fun _ => p, 0, fun _ _ => rfl⟩

def impProp (p q : SProp) : SProp := ⟨fun w => p.val w → q.val w, by
  obtain ⟨n, hn⟩ := p.property
  obtain ⟨m, hm⟩ := q.property
  refine ⟨max n m, ?_⟩
  intro s hs
  funext w
  have hp := congrFun (support_mono _ (Nat.le_max_left n m) hn s hs) w
  have hq := congrFun (support_mono _ (Nat.le_max_right n m) hm s hs) w
  change (p.val (flipBy s w) → q.val (flipBy s w)) = (p.val w → q.val w)
  change p.val (flipBy s w) = p.val w at hp
  change q.val (flipBy s w) = q.val w at hq
  rw [hp, hq]⟩

def boxProp (p : SProp) : SProp := constantProp (∀ w, p.val w)

/-- The supported arrow condition provides the joint covariance quantification needs. -/
theorem arrow_covariant (a : SupportedCarrier)
    (f : SupportedArrow a.action propCarrier.action) (n : Nat)
    (hf : Supported (arrowAction a.action propCarrier.action).toMaskAction n f.val) :
    Covariant a.action.toMaskAction n (fun x => (f.val x).val) := by
  intro s hs x w
  have h := application_equivariant a.action propCarrier.action s f.val x
  rw [hf s hs] at h
  have hv := congrArg (fun p : SProp => p.val (flipBy s w)) h
  change (f.val (a.action.act s x)).val (flipBy s w) =
    (f.val x).val (flipBy s (flipBy s w)) at hv
  rw [flipBy_involutive] at hv
  exact Iff.of_eq hv

def allProp (a : SupportedCarrier) (f : SupportedArrow a.action propCarrier.action) :
    SProp := ⟨fun w => ∀ x, (f.val x).val w, by
  obtain ⟨n, hn⟩ := f.property
  exact ⟨n, (proposition_supported_iff _ _).mpr
    (based_all_of_covariant _ n _ (arrow_covariant a f n hn))⟩⟩

theorem frame_prop_exact (p : World → Prop) :
    (∃ q : supportedFrame.D .prop, supportedFrame.truth q = p) ↔ ∃ n, Based n p := by
  constructor
  · rintro ⟨q, rfl⟩
    exact typed_prop_based q
  · rintro ⟨n, hn⟩
    exact ⟨⟨p, n, (proposition_supported_iff n p).mpr hn⟩, rfl⟩

/-- Quantification is represented for supported higher-order families. -/
theorem frame_all_representable (a : Ty) (f : supportedFrame.D (.arr a .prop)) :
    ∃ p : supportedFrame.D .prop,
      supportedFrame.truth p = fun w => ∀ x, supportedFrame.truth (supportedFrame.app f x) w :=
  ⟨allProp (typedCarrier a) f, rfl⟩

/-- Necessity positivity is invariant under arbitrary binary masks. -/
theorem necessary_positive_invariant (s : World) (p : SProp) :
    (∀ w, (propCarrier.action.act s p).val w) ↔ ∀ w, p.val w := by
  constructor
  · intro h w
    have hh := h (flipBy s w)
    change p.val (flipBy s (flipBy s w)) at hh
    simpa only [flipBy_involutive] using hh
  · intro h w
    exact h (flipBy s w)

/-- Any finite assignment has a common support bound. This does not bound
all elements of any quantified carrier. -/
theorem assignment_supported {Γ : List Ty} (ρ : Henkin.Assignment supportedFrame Γ) :
    ∃ n, ∀ {a} (v : Var Γ a),
      Supported (typedCarrier a).action.toMaskAction n (ρ v) := by
  induction Γ with
  | nil => exact ⟨0, fun v => nomatch v⟩
  | cons a Γ ih =>
    obtain ⟨n, hn⟩ := typed_finite_support a (ρ Var.here)
    obtain ⟨m, hm⟩ := ih (fun v => ρ (.there v))
    refine ⟨max n m, ?_⟩
    intro b v
    cases v with
    | here => exact support_mono _ (Nat.le_max_left n m) hn
    | there v => exact support_mono _ (Nat.le_max_right n m) (hm v)

theorem frame_imp_representable (p q : supportedFrame.D .prop) :
    ∃ r : supportedFrame.D .prop,
      supportedFrame.truth r = fun w => supportedFrame.truth p w → supportedFrame.truth q w :=
  ⟨impProp p q, rfl⟩

theorem frame_box_representable (p : supportedFrame.D .prop) :
    ∃ q : supportedFrame.D .prop,
      supportedFrame.truth q = fun w => ∀ v, supportedFrame.rel w v → supportedFrame.truth p v := by
  refine ⟨boxProp p, ?_⟩
  funext w
  apply propext
  exact ⟨fun h v _ => h v, fun h v => h v True.intro⟩

theorem frame_equal_representable {a : Ty} (x y : supportedFrame.D a) :
    ∃ p : supportedFrame.D .prop, supportedFrame.truth p = fun _ => x = y :=
  ⟨constantProp (x = y), rfl⟩

/-- A coordinate proposition is admitted and falsifies modal collapse.
This is a statement about the frame, not yet Model.closed. -/
theorem frame_noncollapse : ∃ p : supportedFrame.D .prop, ∃ w,
    supportedFrame.truth p w ∧
      ¬ (∀ v, supportedFrame.rel w v → supportedFrame.truth p v) := by
  let p : SProp := ⟨fun w => w 0 = false, 1,
    (proposition_supported_iff 1 _).mpr (coordinate_based 0)⟩
  refine ⟨p, fun _ => false, rfl, ?_⟩
  intro h
  have bad := h (fun _ => true) True.intro
  change true = false at bad
  cases bad

#print axioms assignment_supported
#print axioms frame_imp_representable
#print axioms frame_box_representable
#print axioms frame_equal_representable
#print axioms frame_noncollapse
#print axioms supportedFrame
#print axioms frame_prop_exact
#print axioms arrow_covariant
#print axioms frame_all_representable
#print axioms necessary_positive_invariant
end Programme.«20261021-1639-ontological».Deep.CantorSupport
