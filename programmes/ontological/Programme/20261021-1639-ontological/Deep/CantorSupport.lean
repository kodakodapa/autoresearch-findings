namespace Programme.«20261021-1639-ontological».Deep.CantorSupport

abbrev World := Nat → Bool

def Based (n : Nat) (p : World → Prop) : Prop :=
  ∀ v w, (∀ k, k < n → v k = w k) → (p v ↔ p w)

/-- A tail property, invariant under any change at finitely many coordinates. -/
def EventuallyFalse (v : World) : Prop :=
  ∃ n, ∀ k, n ≤ k → v k = false

theorem eventuallyFalse_of_tail_agreement {v w : World} {n : Nat}
    (h : ∀ k, n ≤ k → v k = w k) :
    EventuallyFalse v → EventuallyFalse w := by
  rintro ⟨m, hm⟩
  refine ⟨max n m, ?_⟩
  intro k hk
  rw [← h k (Nat.le_trans (Nat.le_max_left n m) hk)]
  exact hm k (Nat.le_trans (Nat.le_max_right n m) hk)

theorem eventuallyFalse_tail_invariant {v w : World} {n : Nat}
    (h : ∀ k, n ≤ k → v k = w k) :
    EventuallyFalse v ↔ EventuallyFalse w :=
  ⟨eventuallyFalse_of_tail_agreement h,
    eventuallyFalse_of_tail_agreement (fun k hk => (h k hk).symm)⟩

theorem eventuallyFalse_not_based (n : Nat) : ¬ Based n EventuallyFalse := by
  intro h
  let z : World := fun _ => false
  let t : World := fun k => if k < n then false else true
  have hz : EventuallyFalse z := ⟨0, fun _ _ => rfl⟩
  have ht : EventuallyFalse t := (h z t (by
    intro k hk
    simp [z, t, hk])).mp hz
  obtain ⟨m, hm⟩ := ht
  have hh := hm (max n m) (Nat.le_max_right n m)
  have hn : ¬ max n m < n := Nat.not_lt.mpr (Nat.le_max_left n m)
  simp [t, hn] at hh

/-- A finite bit-flip mask is false beyond a bound. -/
def FiniteMask (s : World) : Prop := ∃ n, ∀ k, n ≤ k → s k = false

def flipBy (s v : World) : World := fun k => Bool.xor (v k) (s k)

theorem eventuallyFalse_finite_flip_invariant (s : World) (hs : FiniteMask s)
    (v : World) : EventuallyFalse (flipBy s v) ↔ EventuallyFalse v := by
  obtain ⟨n, hn⟩ := hs
  apply eventuallyFalse_tail_invariant (n := n)
  intro k hk
  simp [flipBy, hn k hk]

/-- Full masks fixing an initial segment do characterize finitely based sets.
The masks are deliberately NOT restricted to finite support. -/
theorem based_iff_all_tail_flips (n : Nat) (p : World → Prop) :
    Based n p ↔ ∀ s : World, (∀ k, k < n → s k = false) →
      ∀ v, p (flipBy s v) ↔ p v := by
  constructor
  · intro hp s hs v
    apply hp
    intro k hk
    simp [flipBy, hs k hk]
  · intro hp v w hvw
    let s : World := fun k => Bool.xor (v k) (w k)
    have hs : ∀ k, k < n → s k = false := by
      intro k hk
      simp [s, hvw k hk]
    have hflip : flipBy s v = w := by
      funext k
      simp only [flipBy, s]
      cases v k <;> cases w k <;> rfl
    have h := hp s hs v
    rw [hflip] at h
    exact h.symm

#print axioms eventuallyFalse_finite_flip_invariant
#print axioms eventuallyFalse_not_based
#print axioms based_iff_all_tail_flips
end Programme.«20261021-1639-ontological».Deep.CantorSupport
