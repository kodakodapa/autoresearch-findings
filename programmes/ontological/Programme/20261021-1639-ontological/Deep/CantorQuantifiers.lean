import Programme.«20261021-1639-ontological».Deep.CantorSupport

namespace Programme.«20261021-1639-ontological».Deep.CantorSupport

/-- A carrier action by Boolean masks. This interface does not assume that
carrier elements have a common support bound. -/
structure MaskAction (A : Type) where
  act : World → A → A
  involutive : ∀ s x, act s (act s x) = x

/-- Joint covariance of a predicate family under all masks fixing a prefix.
This is stronger than requiring each separate section to be finitely based. -/
def Covariant (a : MaskAction A) (n : Nat) (f : A → World → Prop) : Prop :=
  ∀ s, (∀ k, k < n → s k = false) → ∀ x v,
    f (a.act s x) (flipBy s v) ↔ f x v

theorem flipBy_involutive (s v : World) : flipBy s (flipBy s v) = v := by
  funext k
  simp only [flipBy]
  cases v k <;> cases s k <;> rfl

/-- Higher-order universal quantification preserves a common symmetry support,
although its bound variable ranges over elements with arbitrarily large support. -/
theorem based_all_of_covariant (a : MaskAction A) (n : Nat)
    (f : A → World → Prop) (hf : Covariant a n f) :
    Based n (fun v => ∀ x, f x v) := by
  apply (based_iff_all_tail_flips n _).mpr
  intro s hs v
  constructor
  · intro h x
    exact (hf s hs x v).mp (h (a.act s x))
  · intro h x
    have hx := (hf s hs (a.act s x) v).mpr (h (a.act s x))
    simpa only [a.involutive] using hx

theorem based_exists_of_covariant (a : MaskAction A) (n : Nat)
    (f : A → World → Prop) (hf : Covariant a n f) :
    Based n (fun v => ∃ x, f x v) := by
  apply (based_iff_all_tail_flips n _).mpr
  intro s hs v
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨a.act s x, ?_⟩
    apply (hf s hs (a.act s x) v).mp
    simpa only [a.involutive] using hx
  · rintro ⟨x, hx⟩
    exact ⟨a.act s x, (hf s hs x v).mpr hx⟩

/-- Pointwise finite support is insufficient for quantifier closure: every
coordinate has finite support, but their universal intersection is a singleton. -/
theorem coordinate_based (k : Nat) : Based (k + 1) (fun v => v k = false) := by
  intro v w h
  change (v k = false ↔ w k = false)
  rw [h k (Nat.lt_succ_self k)]

theorem all_coordinates_not_based (n : Nat) :
    ¬ Based n (fun v : World => ∀ k, v k = false) := by
  intro h
  let z : World := fun _ => false
  let t : World := fun k => if k = n then true else false
  have ht : ∀ k, t k = false := (h z t (by
    intro k hk
    have hn : k ≠ n := Nat.ne_of_lt hk
    simp [z, t, hn])).mp (fun _ => rfl)
  have bad := ht n
  simp [t] at bad

/-- No mask action can make the coordinate family jointly covariant with a
finite support. In particular, adjoining a rigid coordinate enumerator to a
finitely-based model destroys definable-term closure. -/
theorem coordinates_not_covariant (a : MaskAction Nat) (n : Nat) :
    ¬ Covariant a n (fun k v => v k = false) := by
  intro h
  exact all_coordinates_not_based n (based_all_of_covariant a n _ h)

/-- Covariance is stable under logical implication. -/
theorem covariant_imp (a : MaskAction A) {n : Nat}
    {f g : A → World → Prop} (hf : Covariant a n f) (hg : Covariant a n g) :
    Covariant a n (fun x v => f x v → g x v) := by
  intro s hs x v
  change (f (a.act s x) (flipBy s v) → g (a.act s x) (flipBy s v)) ↔
    (f x v → g x v)
  rw [hf s hs x v, hg s hs x v]

/-- Universal accessibility preserves covariance by reindexing all worlds. -/
theorem covariant_box (a : MaskAction A) {n : Nat}
    {f : A → World → Prop} (hf : Covariant a n f) :
    Covariant a n (fun x _ => ∀ v, f x v) := by
  intro s hs x v
  constructor
  · intro h w
    exact (hf s hs x w).mp (h (flipBy s w))
  · intro h w
    have hw := (hf s hs x (flipBy s w)).mpr (h (flipBy s w))
    simpa only [flipBy_involutive] using hw

/-- Primitive intensional identity is invariant under the injective carrier action. -/
theorem action_equal_iff (a : MaskAction A) (s : World) (x y : A) :
    a.act s x = a.act s y ↔ x = y := by
  constructor
  · intro h
    have hh := congrArg (a.act s) h
    simpa only [a.involutive] using hh
  · intro h
    rw [h]

#print axioms based_all_of_covariant
#print axioms based_exists_of_covariant
#print axioms coordinate_based
#print axioms all_coordinates_not_based
#print axioms coordinates_not_covariant
#print axioms covariant_imp
#print axioms covariant_box
#print axioms action_equal_iff
end Programme.«20261021-1639-ontological».Deep.CantorSupport
