import Programme.«20261021-1639-ontological».Atlas.Scott

/- D7 finite witnesses, adapted from th, P110. Shared parameterized definitions. -/
namespace Programme.«20261021-1639-ontological».Atlas.ScottTable
open Programme.«20261021-1639-ontological».Countermodels.Tests Programme.«20261021-1639-ontological».Countermodels.Scott Programme.«20261021-1639-ontological».Atlas.Scott
variable {W E : Type} (m : Model W E) (a : Bool)
def A3 : Prop := ∀ w, m.positive (G m) w
def A4 : Prop := ∀ p w, m.positive p w → ∀ v, m.rel w v → m.positive p v
def A5 : Prop := ∀ w, m.positive (NE m a) w
def Poss : Prop := ∀ w, ∃ v, m.rel w v ∧ ∃ x, guard m a x v ∧ G m x v
def Mono : Prop := ∀ w x y, G m x w → G m y w → x = y

/-- Universal two-world frame. -/
def univ2 (act : Unit → Bool → Prop) (pos : (Unit → Bool → Prop) → Bool → Prop) :
    Model Bool Unit := ⟨fun _ _ => True, act, pos⟩

theorem univ2_s5 (act pos) : S5 (univ2 act pos) :=
  ⟨⟨fun _ => trivial, fun _ _ _ _ _ => trivial⟩, fun _ _ _ => trivial⟩

theorem univ2_not_mc (act pos) : ¬ MC (univ2 act pos) := by
  intro h
  exact Bool.false_ne_true (h (fun w => w = false) false rfl true trivial).symm

/-- In `univ2`, NE holds nowhere: a singleton essence is not instantiated at the other world. -/
theorem univ2_not_NE (act pos) (a : Bool) (x : Unit) (w : Bool) :
    ¬ NE (univ2 act pos) a x w := by
  intro h
  have hess : Ess (univ2 act pos) a (fun _ v => v = w) x w := by
    refine ⟨rfl, ?_⟩
    intro q hq v _ y _ hy
    cases x; cases y; subst hy; exact hq
  obtain ⟨_, _, hy⟩ := h _ hess (!w) trivial
  cases w <;> cases hy

/-! ### Drop A1a: everything positive. -/
def allPos : Model Bool Unit := univ2 (fun _ _ => True) (fun _ _ => True)

theorem allPos_noG (x : Unit) (w : Bool) : ¬ G allPos x w :=
  fun h => h (fun _ _ => False) trivial

theorem drop_A1a (a : Bool) :
    S5 allPos ∧ ¬ A1a allPos ∧ A1b allPos ∧ A2 allPos a ∧ A3 allPos ∧ A4 allPos ∧
      A5 allPos a ∧ ¬ T3 allPos a ∧ ¬ MC allPos ∧ ¬ Poss allPos a := by
  refine ⟨univ2_s5 _ _, fun h => h (fun _ _ => True) false trivial trivial,
    fun _ _ _ => trivial, fun _ _ _ _ _ => trivial, fun _ => trivial,
    fun _ _ _ _ _ => trivial, fun _ => trivial, ?_, univ2_not_mc _ _, ?_⟩
  · intro h; obtain ⟨x, _, hx⟩ := h false false trivial; exact allPos_noG x false hx
  · intro h; obtain ⟨_, _, x, _, hx⟩ := h false; exact allPos_noG x _ hx

/-! ### Drop A2: positive = {∅, {(a,0)}} at both worlds. -/
def twoPos : Model Bool Unit := univ2 (fun _ _ => True)
  (fun p _ => (∀ x v, ¬ p x v) ∨ (∀ x v, p x v ↔ v = false))

theorem twoPos_noG (x : Unit) (w : Bool) : ¬ G twoPos x w :=
  fun h => h (fun _ _ => False) (Or.inl fun _ _ h => h)

theorem drop_A2 (a : Bool) :
    S5 twoPos ∧ A1a twoPos ∧ A1b twoPos ∧ ¬ A2 twoPos a ∧ A3 twoPos ∧ A4 twoPos ∧
      A5 twoPos a ∧ ¬ T3 twoPos a ∧ ¬ MC twoPos ∧ ¬ Poss twoPos a := by
  refine ⟨univ2_s5 _ _, ?_, ?_, ?_, ?_, fun _ _ h _ _ => h, ?_, ?_, univ2_not_mc _ _, ?_⟩
  · intro p w hn hp
    rcases hn with hn | hn <;> rcases hp with hp | hp
    · exact hn () false (hp () false)
    · exact hn () true (fun h => Bool.noConfusion ((hp () true).1 h))
    · exact Bool.noConfusion ((hn () true).1 (hp () true))
    · exact (hn () false).2 rfl ((hp () false).2 rfl)
  · intro p w hp
    classical
    by_cases h0 : p () false <;> by_cases h1 : p () true
    · exact Or.inl fun x v hv => by cases x; cases v <;> simp_all
    · exact (hp (Or.inr fun x v => by cases x; cases v <;> simp_all)).elim
    · right; intro x v; cases x; cases v <;> simp_all
    · exact (hp (Or.inl fun x v => by cases x; cases v <;> simp_all)).elim
  · intro h
    rcases h (fun _ _ => False) (fun _ _ => True) false (Or.inl fun _ _ h => h)
      (fun _ _ _ _ _ => trivial) with h' | h'
    · exact h' () false trivial
    · exact Bool.false_ne_true ((h' () true).1 trivial).symm
  · intro w
    left; intro x v hx; exact twoPos_noG x v hx
  · intro w; left; intro x v hx; exact univ2_not_NE _ _ a x v hx
  · intro h; obtain ⟨x, _, hx⟩ := h false false trivial; exact twoPos_noG x false hx
  · intro h; obtain ⟨_, _, x, _, hx⟩ := h false; exact twoPos_noG x _ hx

/-! ### Drop A5: principal ultrafilter at (a,0); a actual only at world 0. -/
def princ : Model Bool Unit := univ2 (fun _ v => v = false) (fun p _ => p () false)

theorem drop_A5 (a : Bool) :
    S5 princ ∧ A1a princ ∧ A1b princ ∧ A2 princ a ∧ A3 princ ∧ A4 princ ∧
      ¬ A5 princ a ∧ ¬ T3 princ a ∧ ¬ MC princ := by
  refine ⟨univ2_s5 _ _, fun _ _ hn hp => hn hp, fun _ _ h => h, ?_,
    fun _ _ hp => hp, fun _ _ h _ _ => h, ?_, ?_, univ2_not_mc _ _⟩
  · intro p q w hp h; exact h false trivial () (fun _ => rfl) hp
  · intro h
    have hne : NE princ a () false := h true
    have hess : Ess princ a (fun _ v => v = false) () false := by
      refine ⟨rfl, ?_⟩
      intro q hq v _ y _ hy; cases y; subst hy; exact hq
    obtain ⟨_, _, hy⟩ := hne _ hess true trivial
    cases hy
  · intro h
    obtain ⟨x, _, hx⟩ := h false true trivial
    have := hx (fun _ v => v = false) rfl
    cases this

/-! ### Drop A3: the majority model (one world, three entities, positive = at least two). -/
def maj : Model Unit (Fin 3) :=
  ⟨fun _ _ => True, fun _ _ => True,
   fun p _ => (p 0 () ∧ p 1 ()) ∨ (p 0 () ∧ p 2 ()) ∨ (p 1 () ∧ p 2 ())⟩

theorem fin3_cases (x : Fin 3) : x = 0 ∨ x = 1 ∨ x = 2 := by
  match x with
  | 0 => simp
  | 1 => simp
  | 2 => simp

theorem maj_noG (x : Fin 3) (w : Unit) : ¬ G maj x w := by
  intro h
  rcases fin3_cases x with rfl | rfl | rfl
  · exact absurd (h (fun y _ => y ≠ 0) (Or.inr (Or.inr ⟨by decide, by decide⟩))) (by simp)
  · exact absurd (h (fun y _ => y ≠ 1) (Or.inr (Or.inl ⟨by decide, by decide⟩))) (by simp)
  · exact absurd (h (fun y _ => y ≠ 2) (Or.inl ⟨by decide, by decide⟩)) (by simp)

theorem drop_A3 (a : Bool) :
    S5 maj ∧ A1a maj ∧ A1b maj ∧ A2 maj a ∧ ¬ A3 maj ∧ A4 maj ∧ A5 maj a ∧
      ¬ T3 maj a ∧ ¬ Poss maj a := by
  refine ⟨⟨⟨fun _ => trivial, fun _ _ _ _ _ => trivial⟩, fun _ _ _ => trivial⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p w hn hp
    rcases hn with ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩ <;>
      rcases hp with ⟨g0, g1⟩ | ⟨g0, g1⟩ | ⟨g0, g1⟩ <;> simp_all
  · intro p w hp
    classical
    by_cases h0 : p 0 () <;> by_cases h1 : p 1 () <;> by_cases h2 : p 2 () <;>
      simp_all [maj]
  · intro p q w hp h
    have h' : ∀ y, p y () → q y () := fun y => h () trivial y (fun _ => trivial)
    rcases hp with ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩
    · exact Or.inl ⟨h' _ h0, h' _ h1⟩
    · exact Or.inr (Or.inl ⟨h' _ h0, h' _ h1⟩)
    · exact Or.inr (Or.inr ⟨h' _ h0, h' _ h1⟩)
  · intro h
    rcases h () with ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨h0, _⟩
    · exact maj_noG 0 () h0
    · exact maj_noG 0 () h0
    · exact maj_noG 1 () h0
  · intro _ _ h _ _; exact h
  · intro w
    have hne : ∀ x, NE maj a x () := by
      intro x p hp v _
      exact ⟨x, fun _ => trivial, hp.1⟩
    exact Or.inl ⟨hne 0, hne 1⟩
  · intro h; obtain ⟨x, _, hx⟩ := h () () trivial; exact maj_noG x () hx
  · intro h; obtain ⟨_, _, x, _, hx⟩ := h (); exact maj_noG x () hx

/-! ### Drop A1b: one world, two entities, only ⊤ positive; both entities are God-like. -/
def topOnly : Model Unit Bool :=
  ⟨fun _ _ => True, fun _ _ => True, fun p _ => ∀ x v, p x v⟩

theorem drop_A1b (a : Bool) :
    S5 topOnly ∧ A1a topOnly ∧ ¬ A1b topOnly ∧ A2 topOnly a ∧ A3 topOnly ∧ A4 topOnly ∧
      A5 topOnly a ∧ ¬ Mono topOnly := by
  refine ⟨⟨⟨fun _ => trivial, fun _ _ _ _ _ => trivial⟩, fun _ _ _ => trivial⟩,
    ?_, ?_, ?_, ?_, fun _ _ h _ _ => h, ?_, ?_⟩
  · intro p w hn hp; exact hn true () (hp true ())
  · intro h
    have := h (fun x _ => x = true) () (fun hp => Bool.false_ne_true (hp false ()))
    exact this true () rfl
  · intro p q w hp h x v; cases v; exact h () trivial x (fun _ => trivial) (hp x ())
  · intro w x v p hp; exact hp x v
  · intro w x v p hp u _; cases u; exact ⟨x, fun _ => trivial, hp.1⟩
  · intro h
    exact Bool.false_ne_true (h () false true (fun p hp => hp false ()) (fun p hp => hp true ()))

#print axioms drop_A1a
#print axioms drop_A2
#print axioms drop_A5
#print axioms drop_A3
#print axioms drop_A1b
end Programme.«20261021-1639-ontological».Atlas.ScottTable
