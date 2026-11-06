/-!
# Small transversals of a family of small sets (hitting-set tree)

The sunflower-free counting step of Jukna's criterion for monotone (real) circuits: for a list `F`
of sets each of size `≤ d`, there are at most `d ^ b` hitting sets of size `≤ b` that every
duplicate-free hitting set of size `≤ b` contains one of. Proof: the branching tree that picks the
first member of `F` not yet hit and branches on its `≤ d` elements, to depth `b`.
-/

namespace Programme.«20261025-0459b-proof-complexity».Transversal

/-- `S` meets every member of `F`. -/
def hits (S : List Nat) (F : List (List Nat)) : Prop := ∀ A ∈ F, ∃ x ∈ A, x ∈ S

instance (S : List Nat) (F : List (List Nat)) : Decidable (hits S F) := by
  unfold hits; infer_instance

/-- The hitting-set tree from partial set `P` with depth budget `b`. -/
def tree (F : List (List Nat)) : Nat → List Nat → List (List Nat)
  | b, P =>
    match F.find? (fun A => !A.any (fun x => decide (x ∈ P))) with
    | none => [P]
    | some A =>
      match b with
      | 0 => []
      | b + 1 => A.flatMap fun x => tree F b (x :: P)

theorem find_none {F : List (List Nat)} {P : List Nat}
    (h : F.find? (fun A => !A.any (fun x => decide (x ∈ P))) = none) : hits P F := by
  intro A hA
  have := List.find?_eq_none.1 h A hA
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_eq_false, List.any_eq_true,
    decide_eq_true_eq] at this
  exact this

theorem find_some {F : List (List Nat)} {P A : List Nat}
    (h : F.find? (fun A => !A.any (fun x => decide (x ∈ P))) = some A) :
    A ∈ F ∧ ∀ x ∈ A, x ∉ P := by
  refine ⟨List.mem_of_find?_eq_some h, ?_⟩
  have := List.find?_some h
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_false, decide_eq_true_eq] at this
  exact this

theorem sum_map_le {A : List Nat} {g : Nat → Nat} {c : Nat} (h : ∀ x ∈ A, g x ≤ c) :
    (A.map g).sum ≤ A.length * c := by
  induction A with
  | nil => simp
  | cons a A ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    have := h a (by simp); have := ih (fun x hx => h x (by simp [hx])); omega

theorem tree_length (F : List (List Nat)) (d : Nat) (hd : 1 ≤ d) (hF : ∀ A ∈ F, A.length ≤ d) :
    ∀ b P, (tree F b P).length ≤ d ^ b := by
  intro b
  induction b with
  | zero =>
    intro P; unfold tree
    split
    · simp
    · simp
  | succ b ih =>
    intro P; unfold tree
    split
    · simp; exact Nat.one_le_pow _ _ hd
    · rename_i A hA
      have hA' := hF A (find_some hA).1
      simp only [List.length_flatMap]
      calc (A.map fun x => (tree F b (x :: P)).length).sum
          ≤ A.length * d ^ b := sum_map_le (fun x _ => ih (x :: P))
        _ ≤ d * d ^ b := Nat.mul_le_mul_right _ hA'
        _ = d ^ (b + 1) := by rw [Nat.pow_succ, Nat.mul_comm]

/-- Every leaf of the tree hits `F`, extends `P`, and adds at most `b` elements. -/
theorem tree_mem (F : List (List Nat)) :
    ∀ b P, ∀ X ∈ tree F b P, hits X F ∧ (∀ x ∈ P, x ∈ X) ∧ X.length ≤ P.length + b := by
  intro b
  induction b with
  | zero =>
    intro P X hX; unfold tree at hX
    split at hX
    · rename_i h; simp at hX; subst hX; exact ⟨find_none h, fun x hx => hx, by omega⟩
    · simp at hX
  | succ b ih =>
    intro P X hX; unfold tree at hX
    split at hX
    · rename_i h; simp at hX; subst hX; exact ⟨find_none h, fun x hx => hx, by omega⟩
    · simp only [List.mem_flatMap] at hX
      obtain ⟨x, _, hX⟩ := hX
      obtain ⟨h1, h2, h3⟩ := ih (x :: P) X hX
      refine ⟨h1, fun y hy => h2 y (by simp [hy]), ?_⟩
      simp at h3; omega

theorem filter_le {p q : Nat → Bool} (hqp : ∀ y, q y = true → p y = true) :
    ∀ S : List Nat, (S.filter q).length ≤ (S.filter p).length
  | [] => by simp
  | a :: S => by
    have := filter_le hqp S
    rw [List.filter_cons, List.filter_cons]
    cases hpa : p a <;> cases hqa : q a <;> simp <;> first | omega | (have := hqp a hqa; simp_all)

theorem filter_lt_gen {S : List Nat} {p q : Nat → Bool} (hqp : ∀ y, q y = true → p y = true)
    {x : Nat} (hx : x ∈ S) (hp : p x = true) (hq : q x = false) :
    (S.filter q).length < (S.filter p).length := by
  induction S with
  | nil => simp at hx
  | cons a S ih =>
    have hle : (S.filter q).length ≤ (S.filter p).length := filter_le hqp S
    rw [List.filter_cons, List.filter_cons]
    by_cases ha : a = x
    · subst ha; simp only [hp, hq]; simp; omega
    · have := ih ((List.mem_cons.1 hx).resolve_left (Ne.symm ha))
      cases hpa : p a <;> cases hqa : q a <;> simp <;> first | omega | (have := hqp a hqa; simp_all)

theorem filter_lt {S P : List Nat} {x : Nat} (hx : x ∈ S) (hxP : x ∉ P) :
    (S.filter fun y => decide (y ∉ x :: P)).length < (S.filter fun y => decide (y ∉ P)).length :=
  filter_lt_gen (fun y hy => by simp at hy ⊢; exact hy.2) hx (by simp [hxP]) (by simp)

/-- Every hitting set `S ⊇ P` with at most `b` elements outside `P` contains a leaf. -/
theorem tree_cover (F : List (List Nat)) :
    ∀ b P (S : List Nat), hits S F → (∀ x ∈ P, x ∈ S) →
      (S.filter fun y => decide (y ∉ P)).length ≤ b → ∃ X ∈ tree F b P, ∀ x ∈ X, x ∈ S := by
  intro b
  induction b with
  | zero =>
    intro P S hS hP hb
    unfold tree
    split
    · exact ⟨P, by simp, hP⟩
    · rename_i A hA
      obtain ⟨hAF, hAP⟩ := find_some hA
      obtain ⟨x, hxA, hxS⟩ := hS A hAF
      have := filter_lt hxS (hAP x hxA); omega
  | succ b ih =>
    intro P S hS hP hb
    unfold tree
    split
    · exact ⟨P, by simp, hP⟩
    · rename_i A hA
      obtain ⟨hAF, hAP⟩ := find_some hA
      obtain ⟨x, hxA, hxS⟩ := hS A hAF
      have hlt := filter_lt hxS (hAP x hxA)
      obtain ⟨X, hX, hXS⟩ := ih (x :: P) S hS
        (by intro y hy; simp at hy; rcases hy with rfl | hy; exact hxS; exact hP y hy) (by omega)
      exact ⟨X, List.mem_flatMap.2 ⟨x, hxA, hX⟩, hXS⟩

/-- **Hitting-set tree.** For sets of size `≤ d` (`d ≥ 1`) there is a list of at most `d ^ b`
hitting sets, each of length `≤ b`, such that every hitting set `S` whose duplicate-free part has
at most `b` elements contains one of them. -/
theorem transversals (F : List (List Nat)) (d b : Nat) (hd : 1 ≤ d) (hF : ∀ A ∈ F, A.length ≤ d) :
    ∃ T : List (List Nat), T.length ≤ d ^ b ∧ (∀ X ∈ T, hits X F ∧ X.length ≤ b) ∧
      ∀ S : List Nat, hits S F → S.Nodup → S.length ≤ b → ∃ X ∈ T, ∀ x ∈ X, x ∈ S := by
  refine ⟨tree F b [], tree_length F d hd hF b [], fun X hX => ?_, fun S hS _ hb => ?_⟩
  · obtain ⟨h1, _, h3⟩ := tree_mem F b [] X hX; exact ⟨h1, by simpa using h3⟩
  · exact tree_cover F b [] S hS (by simp) (Nat.le_trans (List.length_filter_le _ _) hb)

end Programme.«20261025-0459b-proof-complexity».Transversal
