/-!
# Ben-Sasson–Wigderson size–width relation (core Lean 4)

For a CNF `F` over a duplicate-free variable list `X` (`|X| = N`) whose clauses have width
`≤ w₀`, and any resolution refutation `π` of `F` (the `Refutation` type of `Work.Haken`,
weakening built into the resolution rule), if

  `fat · (2N - d)^b < (2N)^b`,  `fat` = number of lines of `π` with more than `d` literals,

then `F` has a refutation of width `≤ w₀ + d + b` (`Der`, with weakening).
Contrapositive: if `F` has no refutation of width `w₀ + d + b`, then
`(2N)^b ≤ |π| · (2N - d)^b`, i.e. `|π| ≥ (1 + d/(2N-d))^b`; with `d = b = k` this is
`exp(Ω(k²/N))`, the general (DAG-like) Ben-Sasson–Wigderson bound (JACM 2001, Thm 3.5).

The proof follows BSW: pick the literal `ℓ` occurring in the most fat clauses, set it true
(the number of fat clauses drops by a factor `1 - d/2N`), recurse on both restrictions, and glue.
Restrictions are applied to the fixed refutation `π`; the width-bounded refutations are
built as `Der` derivations.

The basic definitions `Lit`, `Clause`, `CNF`, `IsResolvent`, `Refutation` are literally those of
`Work.Haken` (agent pr), restated here because that file is not yet in the library.
-/

set_option linter.unusedSectionVars false

namespace Programme.«20261024-1110-proof-complexity».BSW

/-! ## Resolution (as in `Work.Haken`) -/

structure Lit (V : Type) where
  var : V
  pos : Bool
deriving DecidableEq, Repr

abbrev Clause (V : Type) := List (Lit V)
abbrev CNF (V : Type) := List (Clause V)

def IsResolvent {V} (A B C : Clause V) : Prop :=
  ∃ x, ⟨x, true⟩ ∈ A ∧ ⟨x, false⟩ ∈ B ∧
    (∀ l ∈ A, l ≠ ⟨x, true⟩ → l ∈ C) ∧ (∀ l ∈ B, l ≠ ⟨x, false⟩ → l ∈ C)

structure Refutation {V} (F : CNF V) where
  steps : List (Clause V)
  derived : ∀ k (hk : k < steps.length), steps[k] ∈ F ∨
    ∃ a b, ∃ (ha : a < k) (hb : b < k),
      IsResolvent (steps[a]'(Nat.lt_trans ha hk)) (steps[b]'(Nat.lt_trans hb hk)) steps[k]
  empty_mem : ([] : Clause V) ∈ steps

variable {V : Type} [DecidableEq V]

def Lit.neg (l : Lit V) : Lit V := ⟨l.var, !l.pos⟩

@[simp] theorem Lit.neg_neg (l : Lit V) : l.neg.neg = l := by
  cases l; simp [Lit.neg]

theorem Lit.neg_inj {l m : Lit V} (h : l.neg = m.neg) : l = m := by
  have := congrArg Lit.neg h; simpa using this

@[simp] theorem Lit.neg_var (l : Lit V) : l.neg.var = l.var := rfl

/-! ## Width over a variable list -/

/-- All `2|X|` literals over `X`. -/
def lits (X : List V) : List (Lit V) := X.flatMap fun x => [⟨x, true⟩, ⟨x, false⟩]

theorem mem_lits {X : List V} {l : Lit V} : l ∈ lits X ↔ l.var ∈ X := by
  constructor
  · intro h
    obtain ⟨x, hx, h⟩ := List.mem_flatMap.mp h
    simp at h; rcases h with rfl | rfl <;> exact hx
  · intro h
    apply List.mem_flatMap.mpr
    refine ⟨l.var, h, ?_⟩
    cases l with | mk v p => cases p <;> simp

theorem length_lits (X : List V) : (lits X).length = 2 * X.length := by
  induction X with
  | nil => rfl
  | cons x X ih =>
    simp only [lits, List.flatMap_cons, List.length_append, List.length_cons] at *
    rw [ih]; simp; omega

theorem nodup_lits {X : List V} (hX : X.Nodup) : (lits X).Nodup := by
  induction X with
  | nil => simp [lits]
  | cons x X ih =>
    rw [List.nodup_cons] at hX
    simp only [lits, List.flatMap_cons]
    rw [List.nodup_append]
    refine ⟨by simp, ih hX.2, ?_⟩
    intro a ha b hb hab
    subst hab
    have : a.var ∈ X := mem_lits.mp hb
    simp at ha; rcases ha with rfl | rfl <;> exact hX.1 this

/-- Width of a clause: the number of distinct literals over `X` it contains. -/
def wd (X : List V) (C : Clause V) : Nat := (lits X).countP fun l => decide (l ∈ C)

theorem wd_mono {X : List V} {C D : Clause V} (h : ∀ l ∈ C, l ∈ D) : wd X C ≤ wd X D := by
  unfold wd
  apply List.countP_mono_left
  intro l _ hl; simp at hl ⊢; exact h l hl

theorem countP_eq_le_one {α} [DecidableEq α] (l : List α) (x : α) (hl : l.Nodup) :
    l.countP (fun y => decide (y = x)) ≤ 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    rw [List.countP_cons]
    by_cases hax : a = x
    · subst hax
      have : l.countP (fun y => decide (y = a)) = 0 := by
        rw [List.countP_eq_zero]; intro y hy; simp; intro e; subst e; exact hl.1 hy
      simp [this]
    · have := ih hl.2; simp [hax]; omega

theorem countP_or_le {α} (l : List α) (p q : α → Bool) :
    l.countP (fun x => p x || q x) ≤ l.countP p + l.countP q := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.countP_cons]
    cases p a <;> cases q a <;> simp <;> omega

theorem wd_cons {X : List V} (hX : X.Nodup) (l : Lit V) (D : Clause V) :
    wd X (l :: D) ≤ wd X D + 1 := by
  unfold wd
  have h0 := List.countP_mono_left (l := lits X)
      (p := fun m => decide (m ∈ l :: D)) (q := fun m => decide (m ∈ D) || decide (m = l))
      (by intro m _ hm; simp at hm ⊢; rcases hm with h | h <;> simp [h])
  have h1 := countP_or_le (lits X) (fun m => decide (m ∈ D)) (fun m => decide (m = l))
  have h2 := countP_eq_le_one (lits X) l (nodup_lits hX)
  omega

/-- A clause is admissible at width `W`: variables in `X`, at most `W` literals. -/
def OK (X : List V) (W : Nat) (C : Clause V) : Prop := (∀ l ∈ C, l.var ∈ X) ∧ wd X C ≤ W

/-- Width-`W` derivability from the axiom set `Ax` (resolution and weakening). -/
inductive Der (Ax : Clause V → Prop) (X : List V) (W : Nat) : Clause V → Prop
  | ax {C} : Ax C → OK X W C → Der Ax X W C
  | res {A B C} (l : Lit V) : Der Ax X W A → Der Ax X W B → l ∈ A → l.neg ∈ B →
      (∀ m ∈ A, m ≠ l → m ∈ C) → (∀ m ∈ B, m ≠ l.neg → m ∈ C) → OK X W C → Der Ax X W C
  | weak {A C} : Der Ax X W A → (∀ m ∈ A, m ∈ C) → OK X W C → Der Ax X W C

def Lit.eval (a : V → Bool) (l : Lit V) : Bool := if l.pos then a l.var else !a l.var

def Clause.eval (a : V → Bool) (C : Clause V) : Bool := C.any (Lit.eval a)

/-- Soundness of `Der`: an assignment satisfying all axioms satisfies every derived clause.
(So `Der`-unrefutability at width `W` is a real, checkable property.) -/
theorem Der.sound {Ax : Clause V → Prop} {X : List V} {W : Nat} {C : Clause V}
    (a : V → Bool) (hAx : ∀ D, Ax D → D.eval a = true) (h : Der Ax X W C) : C.eval a = true := by
  induction h with
  | ax hax _ => exact hAx _ hax
  | @res A B C l _ _ hlA hlB hA hB _ ihA ihB =>
    unfold Clause.eval at *
    rw [List.any_eq_true] at ihA ihB ⊢
    obtain ⟨m, hm, hma⟩ := ihA
    obtain ⟨m', hm', hma'⟩ := ihB
    by_cases e : m = l
    · subst e
      by_cases e' : m' = m.neg
      · subst e'; cases m with | mk v p => cases p <;> simp [Lit.eval, Lit.neg] at hma hma' <;> simp_all
      · exact ⟨m', hB m' hm' e', hma'⟩
    · exact ⟨m, hA m hm e, hma⟩
  | weak _ hAC _ ih =>
    unfold Clause.eval at *
    rw [List.any_eq_true] at ih ⊢
    obtain ⟨m, hm, hma⟩ := ih
    exact ⟨m, hAC m hm, hma⟩

/-! ## Restrictions -/

/-- `ρ` (a list of literals set true) satisfies `C`. -/
def Sat (ρ C : Clause V) : Prop := ∃ l ∈ C, l ∈ ρ

instance (ρ C : Clause V) : Decidable (Sat ρ C) := inferInstanceAs (Decidable (∃ l ∈ C, l ∈ ρ))

/-- `C|ρ`: drop literals falsified by `ρ` and literals outside `X`. -/
def restr (X : List V) (ρ C : Clause V) : Clause V :=
  C.filter fun l => decide (l.var ∈ X) && !decide (l.neg ∈ ρ)

theorem mem_restr {X : List V} {ρ C : Clause V} {l : Lit V} :
    l ∈ restr X ρ C ↔ l ∈ C ∧ l.var ∈ X ∧ l.neg ∉ ρ := by
  simp [restr]

/-- The axioms of `F|ρ`. -/
def AxR (F : CNF V) (X : List V) (ρ : Clause V) (D : Clause V) : Prop :=
  ∃ C ∈ F, ¬ Sat ρ C ∧ D = restr X ρ C

theorem ok_restr {X : List V} {ρ C : Clause V} {W : Nat} (h : wd X C ≤ W) :
    OK X W (restr X ρ C) :=
  ⟨fun l hl => (mem_restr.mp hl).2.1,
   Nat.le_trans (wd_mono fun l hl => (mem_restr.mp hl).1) h⟩

theorem ok_cons {X : List V} (hX : X.Nodup) {W : Nat} {D : Clause V} {l : Lit V}
    (h : OK X W D) (hl : l.var ∈ X) : OK X (W + 1) (l :: D) := by
  refine ⟨?_, Nat.le_trans (wd_cons hX l D) (by have := h.2; omega)⟩
  intro m hm
  rcases List.mem_cons.mp hm with rfl | hm
  · exact hl
  · exact h.1 m hm

/-- Lifting: a width-`W` refutation of `F|ρ,ℓ` gives a width-`(W+1)` derivation of `¬ℓ` from `F|ρ`
(more generally `D ↦ ¬ℓ ∨ D`). -/
theorem lift {X : List V} (hX : X.Nodup) {F : CNF V} {w0 W : Nat}
    (hF : ∀ C ∈ F, wd X C ≤ w0) (hw : w0 ≤ W + 1) {ρ : Clause V} {ℓ : Lit V} (hℓ : ℓ.var ∈ X)
    {D : Clause V} (h : Der (AxR F X (ℓ :: ρ)) X W D) :
    Der (AxR F X ρ) X (W + 1) (ℓ.neg :: D) := by
  induction h with
  | @ax D hax hok =>
    obtain ⟨C, hC, hs, rfl⟩ := hax
    have hs' : ¬ Sat ρ C := fun ⟨l, hl, hlρ⟩ => hs ⟨l, hl, List.mem_cons_of_mem _ hlρ⟩
    refine Der.weak (A := restr X ρ C) (Der.ax ⟨C, hC, hs', rfl⟩ (ok_restr (Nat.le_trans (hF C hC) hw)))
      ?_ (ok_cons hX hok hℓ)
    intro m hm
    obtain ⟨hmC, hmX, hmρ⟩ := mem_restr.mp hm
    by_cases e : m = ℓ.neg
    · rw [e]; exact List.mem_cons_self
    · apply List.mem_cons_of_mem
      apply mem_restr.mpr
      refine ⟨hmC, hmX, ?_⟩
      intro h'
      rcases List.mem_cons.mp h' with h' | h'
      · apply e; rw [← h']; simp
      · exact hmρ h'
  | @res A B C l _ _ hlA hlB hA hB hok ihA ihB =>
    refine Der.res l ihA ihB (List.mem_cons_of_mem _ hlA) (List.mem_cons_of_mem _ hlB) ?_ ?_
      (ok_cons hX hok hℓ)
    · intro m hm hne
      rcases List.mem_cons.mp hm with rfl | hm
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hA m hm hne)
    · intro m hm hne
      rcases List.mem_cons.mp hm with rfl | hm
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hB m hm hne)
  | @weak A C _ hAC hok ih =>
    refine Der.weak ih ?_ (ok_cons hX hok hℓ)
    intro m hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (hAC m hm)

/-- Gluing: from `F|ρ ⊢ ¬ℓ` and a refutation of `F|ρ,¬ℓ`, both in width `W ≥ w₀`, refute `F|ρ`. -/
theorem glue {X : List V} {F : CNF V} {w0 W : Nat}
    (hF : ∀ C ∈ F, wd X C ≤ w0) (hw : w0 ≤ W) {ρ : Clause V} {ℓ : Lit V}
    (hn : Der (AxR F X ρ) X W [ℓ.neg]) {D : Clause V} (h : Der (AxR F X (ℓ.neg :: ρ)) X W D) :
    Der (AxR F X ρ) X W D := by
  induction h with
  | @ax D hax hok =>
    obtain ⟨C, hC, hs, rfl⟩ := hax
    have hs' : ¬ Sat ρ C := fun ⟨l, hl, hlρ⟩ => hs ⟨l, hl, List.mem_cons_of_mem _ hlρ⟩
    have hR : Der (AxR F X ρ) X W (restr X ρ C) :=
      Der.ax ⟨C, hC, hs', rfl⟩ (ok_restr (Nat.le_trans (hF C hC) hw))
    have key : ∀ m ∈ restr X ρ C, m ≠ ℓ → m ∈ restr X (ℓ.neg :: ρ) C := by
      intro m hm hne
      obtain ⟨hmC, hmX, hmρ⟩ := mem_restr.mp hm
      refine mem_restr.mpr ⟨hmC, hmX, ?_⟩
      intro h'
      rcases List.mem_cons.mp h' with h' | h'
      · exact hne (Lit.neg_inj h')
      · exact hmρ h'
    by_cases hl : ℓ ∈ restr X ρ C
    · refine Der.res ℓ hR hn hl List.mem_cons_self key ?_ hok
      intro m hm hne; simp at hm; exact absurd hm hne
    · exact Der.weak hR (fun m hm => key m hm (fun e => hl (e ▸ hm))) hok
  | @res A B C l _ _ hlA hlB hA hB hok ihA ihB => exact Der.res l ihA ihB hlA hlB hA hB hok
  | @weak A C _ hAC hok ih => exact Der.weak ih hAC hok

/-- Restricting a refutation: every line of `π` is satisfied by `ρ`, or its restriction is
derivable from `F|ρ` in any width `W` that bounds all unsatisfied restricted lines. -/
theorem base {X : List V} {F : CNF V} (π : Refutation F) {ρ : Clause V} {W : Nat}
    (hcons : ∀ l ∈ ρ, l.neg ∉ ρ)
    (hW : ∀ C ∈ π.steps, ¬ Sat ρ C → wd X (restr X ρ C) ≤ W) :
    ∀ k (hk : k < π.steps.length),
      Sat ρ π.steps[k] ∨ Der (AxR F X ρ) X W (restr X ρ π.steps[k]) := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
  intro hk
  by_cases hs : Sat ρ π.steps[k]
  · exact Or.inl hs
  right
  have hok : OK X W (restr X ρ π.steps[k]) :=
    ⟨fun l hl => (mem_restr.mp hl).2.1, hW _ (List.getElem_mem hk) hs⟩
  rcases π.derived k hk with hax | ⟨a, b, ha, hb, x, hxA, hxB, hA, hB⟩
  · exact Der.ax ⟨_, hax, hs, rfl⟩ hok
  · generalize π.steps[k] = C at hs hok hA hB
    generalize hAe : π.steps[a]'(Nat.lt_trans ha hk) = A at hxA hA
    generalize hBe : π.steps[b]'(Nat.lt_trans hb hk) = B at hxB hB
    have ihA := ih a ha (Nat.lt_trans ha hk); rw [hAe] at ihA
    have ihB := ih b hb (Nat.lt_trans hb hk); rw [hBe] at ihB
    -- subset lemmas
    have subA : ⟨x, false⟩ ∈ ρ → ∀ m ∈ restr X ρ A, m ∈ restr X ρ C := by
      intro hxρ m hm
      obtain ⟨hmA, hmX, hmρ⟩ := mem_restr.mp hm
      have hne : m ≠ ⟨x, true⟩ := by intro e; subst e; exact hmρ hxρ
      exact mem_restr.mpr ⟨hA m hmA hne, hmX, hmρ⟩
    have subB : ⟨x, true⟩ ∈ ρ → ∀ m ∈ restr X ρ B, m ∈ restr X ρ C := by
      intro hxρ m hm
      obtain ⟨hmB, hmX, hmρ⟩ := mem_restr.mp hm
      have hne : m ≠ ⟨x, false⟩ := by intro e; subst e; exact hmρ hxρ
      exact mem_restr.mpr ⟨hB m hmB hne, hmX, hmρ⟩
    have nsA : ⟨x, true⟩ ∉ ρ → ¬ Sat ρ A := by
      intro hxρ ⟨m, hmA, hmρ⟩
      have hne : m ≠ ⟨x, true⟩ := by intro e; subst e; exact hxρ hmρ
      exact hs ⟨m, hA m hmA hne, hmρ⟩
    have nsB : ⟨x, false⟩ ∉ ρ → ¬ Sat ρ B := by
      intro hxρ ⟨m, hmB, hmρ⟩
      have hne : m ≠ ⟨x, false⟩ := by intro e; subst e; exact hxρ hmρ
      exact hs ⟨m, hB m hmB hne, hmρ⟩
    by_cases h1 : (⟨x, true⟩ : Lit V) ∈ ρ
    · have h2 : (⟨x, false⟩ : Lit V) ∉ ρ := hcons _ h1
      exact Der.weak ((ihB).resolve_left (nsB h2)) (subB h1) hok
    by_cases h2 : (⟨x, false⟩ : Lit V) ∈ ρ
    · exact Der.weak ((ihA).resolve_left (nsA h1)) (subA h2) hok
    have dA := (ihA).resolve_left (nsA h1)
    have dB := (ihB).resolve_left (nsB h2)
    by_cases hx : x ∈ X
    · refine Der.res ⟨x, true⟩ dA dB (mem_restr.mpr ⟨hxA, hx, h2⟩)
        (mem_restr.mpr ⟨hxB, hx, h1⟩) ?_ ?_ hok
      · intro m hm hne
        obtain ⟨hmA, hmX, hmρ⟩ := mem_restr.mp hm
        exact mem_restr.mpr ⟨hA m hmA hne, hmX, hmρ⟩
      · intro m hm hne
        obtain ⟨hmB, hmX, hmρ⟩ := mem_restr.mp hm
        exact mem_restr.mpr ⟨hB m hmB hne, hmX, hmρ⟩
    · refine Der.weak dA ?_ hok
      intro m hm
      obtain ⟨hmA, hmX, hmρ⟩ := mem_restr.mp hm
      have hne : m ≠ ⟨x, true⟩ := by intro e; subst e; exact hx hmX
      exact mem_restr.mpr ⟨hA m hmA hne, hmX, hmρ⟩

/-! ## Counting -/

theorem double_count {α β} (l₁ : List α) (l₂ : List β) (R : α → β → Bool) :
    (l₁.map fun a => l₂.countP (R a)).sum = (l₂.map fun b => l₁.countP (fun a => R a b)).sum := by
  induction l₁ with
  | nil =>
    simp only [List.map_nil, List.sum_nil, List.countP_nil]
    induction l₂ with
    | nil => rfl
    | cons b l₂ ih => simp only [List.map_cons, List.sum_cons, ← ih]; rfl
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.countP_cons, ih]
    clear ih
    induction l₂ with
    | nil => simp
    | cons b l₂ ih2 =>
      simp only [List.countP_cons, List.map_cons, List.sum_cons]
      cases R a b <;> simp at ih2 ⊢ <;> omega

theorem countP_mul_le_sum {α} (l : List α) (P : α → Bool) (g : α → Nat) (c : Nat)
    (h : ∀ x ∈ l, P x = true → c ≤ g x) : l.countP P * c ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.countP_cons, List.map_cons, List.sum_cons]
    have ih' := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    by_cases hp : P a = true
    · have := h a (List.mem_cons_self) hp
      simp [hp, Nat.add_mul]; omega
    · simp [hp]; omega

theorem sum_le_countP_mul {α} (l : List α) (P : α → Bool) (g : α → Nat) (c : Nat)
    (h0 : ∀ x ∈ l, P x = false → g x = 0) (hc : ∀ x ∈ l, g x ≤ c) :
    (l.map g).sum ≤ l.countP P * c := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.countP_cons, List.map_cons, List.sum_cons]
    have ih' := ih (fun x hx => h0 x (List.mem_cons_of_mem _ hx))
      (fun x hx => hc x (List.mem_cons_of_mem _ hx))
    have ha := hc a List.mem_cons_self
    cases hp : P a
    · have := h0 a List.mem_cons_self hp; simp; omega
    · simp [Nat.add_mul]; omega

theorem countP_add_le {α} (l : List α) (p q r : α → Bool) (hp : ∀ x ∈ l, p x = true → r x = true)
    (hq : ∀ x ∈ l, q x = true → r x = true) (hpq : ∀ x ∈ l, p x = true → q x = true → False) :
    l.countP p + l.countP q ≤ l.countP r := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.countP_cons]
    have := ih (fun x hx => hp x (List.mem_cons_of_mem _ hx))
      (fun x hx => hq x (List.mem_cons_of_mem _ hx)) (fun x hx => hpq x (List.mem_cons_of_mem _ hx))
    have h1 := hp a List.mem_cons_self
    have h2 := hq a List.mem_cons_self
    have h3 := hpq a List.mem_cons_self
    cases ep : p a <;> cases eq : q a <;> cases er : r a <;> simp_all <;> omega

theorem exists_max {α} (l : List α) (g : α → Nat) (hl : l ≠ []) :
    ∃ x ∈ l, ∀ y ∈ l, g y ≤ g x := by
  induction l with
  | nil => exact absurd rfl hl
  | cons a t ih =>
    by_cases ht : t = []
    · subst ht; exact ⟨a, List.mem_cons_self, by simp⟩
    obtain ⟨x, hx, hmax⟩ := ih ht
    by_cases hc : g a ≤ g x
    · refine ⟨x, List.mem_cons_of_mem _ hx, ?_⟩
      intro y hy; rcases List.mem_cons.mp hy with rfl | hy
      · exact hc
      · exact hmax y hy
    · refine ⟨a, List.mem_cons_self, ?_⟩
      intro y hy; rcases List.mem_cons.mp hy with rfl | hy
      · exact Nat.le_refl _
      · have := hmax y hy; omega

/-- The ratio `(u - d)/u` is monotone in `u`, so the BSW hypothesis survives shrinking `u`. -/
theorem cond_mono {f u u' d b : Nat} (hu : u' ≤ u) (hu' : 0 < u') (h : f * (u - d) ^ b < u ^ b) :
    f * (u' - d) ^ b < u' ^ b := by
  have base : (u' - d) * u ≤ (u - d) * u' := by
    by_cases h1 : u' ≤ d
    · have : u' - d = 0 := by omega
      simp [this]
    · obtain ⟨e, rfl⟩ : ∃ e, u' = d + e := ⟨u' - d, by omega⟩
      obtain ⟨g, rfl⟩ : ∃ g, u = d + e + g := ⟨u - (d + e), by omega⟩
      have e1 : d + e - d = e := by omega
      have e2 : d + e + g - d = e + g := by omega
      rw [e1, e2]
      have : e * g ≤ g * (d + e) := by
        rw [Nat.mul_comm e g]; exact Nat.mul_le_mul_left g (by omega)
      calc e * (d + e + g) = e * (d + e) + e * g := by rw [Nat.mul_add]
        _ ≤ e * (d + e) + g * (d + e) := by omega
        _ = (e + g) * (d + e) := by rw [Nat.add_mul]
  have hpow : ((u' - d) * u) ^ b ≤ ((u - d) * u') ^ b := Nat.pow_le_pow_left base b
  rw [Nat.mul_pow, Nat.mul_pow] at hpow
  have h0 : 0 < u' ^ b := Nat.pow_pos hu'
  have : f * (u' - d) ^ b * u ^ b < u' ^ b * u ^ b := by
    calc f * (u' - d) ^ b * u ^ b = f * ((u' - d) ^ b * u ^ b) := Nat.mul_assoc _ _ _
      _ ≤ f * ((u - d) ^ b * u' ^ b) := Nat.mul_le_mul_left _ hpow
      _ = f * (u - d) ^ b * u' ^ b := (Nat.mul_assoc _ _ _).symm
      _ < u ^ b * u' ^ b := Nat.mul_lt_mul_of_pos_right h h0
      _ = u' ^ b * u ^ b := Nat.mul_comm _ _
  exact Nat.lt_of_mul_lt_mul_right this

theorem arith_step {u d b f fA c : Nat} (hb : b ≠ 0) (hfA : fA + c ≤ f)
    (hs : f * (d + 1) ≤ u * c) (hc : f * (u - d) ^ b < u ^ b) :
    fA * (u - d) ^ (b - 1) < u ^ (b - 1) := by
  have hlin : u * fA ≤ f * (u - d) := by
    have e1 : u * fA + u * c ≤ u * f := by rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ hfA
    have e2 : f * (d + 1) = f * d + f := Nat.mul_succ f d
    have e3 : f * (u - d) = f * u - f * d := Nat.mul_sub f u d
    have e4 : u * f = f * u := Nat.mul_comm u f
    omega
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have : fA * (u - d) ^ b' * u < u ^ b' * u := by
    calc fA * (u - d) ^ b' * u = (u * fA) * (u - d) ^ b' := by
          rw [Nat.mul_comm u fA]; exact Nat.mul_right_comm _ _ _
      _ ≤ (f * (u - d)) * (u - d) ^ b' := Nat.mul_le_mul_right _ hlin
      _ = f * (u - d) ^ (b' + 1) := by rw [Nat.mul_assoc, Nat.pow_succ, Nat.mul_comm (u - d)]
      _ < u ^ (b' + 1) := hc
      _ = u ^ b' * u := Nat.pow_succ u b'
  exact Nat.lt_of_mul_lt_mul_right this

/-! ## The BSW recursion -/

section Main
variable (X : List V) {F : CNF V} (π : Refutation F) (d : Nat)

/-- Number of literals over `X` left unassigned by `ρ`. -/
def unas (X : List V) (ρ : Clause V) : Nat :=
  (lits X).countP fun l => decide (l ∉ ρ ∧ l.neg ∉ ρ)

/-- Line `C` is fat under `ρ`: not satisfied, restriction wider than `d`. -/
def IsFat (X : List V) (d : Nat) (ρ C : Clause V) : Bool :=
  decide (¬ Sat ρ C ∧ d < wd X (restr X ρ C))

def fat (ρ : Clause V) : Nat := π.steps.countP (IsFat X d ρ)

/-- Number of fat lines whose restriction contains `ℓ`. -/
def cnt (ρ : Clause V) (ℓ : Lit V) : Nat :=
  π.steps.countP fun C => IsFat X d ρ C && decide (ℓ ∈ restr X ρ C)

theorem lit_unas {X : List V} {ρ C : Clause V} (hs : ¬ Sat ρ C) {l : Lit V} (hl : l ∈ restr X ρ C) :
    l ∉ ρ ∧ l.neg ∉ ρ := by
  obtain ⟨hlC, _, hlρ⟩ := mem_restr.mp hl
  exact ⟨fun h => hs ⟨l, hlC, h⟩, hlρ⟩

theorem wd_restr_le_unas {X : List V} {ρ C : Clause V} (hs : ¬ Sat ρ C) : wd X (restr X ρ C) ≤ unas X ρ := by
  unfold wd unas
  apply List.countP_mono_left
  intro l _ hl
  have := lit_unas hs (of_decide_eq_true hl)
  simp [this]

theorem cnt_zero {ρ : Clause V} {ℓ : Lit V} (h : ¬ (ℓ ∉ ρ ∧ ℓ.neg ∉ ρ)) : cnt X π d ρ ℓ = 0 := by
  unfold cnt
  rw [List.countP_eq_zero]
  intro C _ hC
  simp only [Bool.and_eq_true, decide_eq_true_eq, IsFat] at hC
  exact h (lit_unas hC.1.1 hC.2)

theorem sum_cnt (ρ : Clause V) :
    fat X π d ρ * (d + 1) ≤ ((lits X).map (cnt X π d ρ)).sum := by
  unfold cnt
  rw [double_count]
  unfold fat
  apply countP_mul_le_sum
  intro C _ hC
  have hC' := hC
  simp only [IsFat, decide_eq_true_eq] at hC'
  have e : (lits X).countP (fun ℓ => IsFat X d ρ C && decide (ℓ ∈ restr X ρ C)) = wd X (restr X ρ C) := by
    unfold wd; apply List.countP_congr; intro ℓ _; simp [hC]
  rw [e]; omega

theorem fat_mono (ρ : Clause V) (ℓ : Lit V) : fat X π d (ℓ :: ρ) ≤ fat X π d ρ := by
  unfold fat
  apply List.countP_mono_left
  intro C _ hC
  simp only [IsFat, decide_eq_true_eq] at hC ⊢
  refine ⟨fun ⟨l, hl, hlρ⟩ => hC.1 ⟨l, hl, List.mem_cons_of_mem _ hlρ⟩, ?_⟩
  refine Nat.lt_of_lt_of_le hC.2 (wd_mono ?_)
  intro m hm
  obtain ⟨h1, h2, h3⟩ := mem_restr.mp hm
  exact mem_restr.mpr ⟨h1, h2, fun h => h3 (List.mem_cons_of_mem _ h)⟩

theorem fat_cnt (ρ : Clause V) (ℓ : Lit V) : fat X π d (ℓ :: ρ) + cnt X π d ρ ℓ ≤ fat X π d ρ := by
  unfold fat cnt
  apply countP_add_le
  · intro C _ hC
    simp only [IsFat, decide_eq_true_eq] at hC ⊢
    refine ⟨fun ⟨l, hl, hlρ⟩ => hC.1 ⟨l, hl, List.mem_cons_of_mem _ hlρ⟩, ?_⟩
    refine Nat.lt_of_lt_of_le hC.2 (wd_mono ?_)
    intro m hm
    obtain ⟨h1, h2, h3⟩ := mem_restr.mp hm
    exact mem_restr.mpr ⟨h1, h2, fun h => h3 (List.mem_cons_of_mem _ h)⟩
  · intro C _ hC
    simp only [Bool.and_eq_true] at hC; exact hC.1
  · intro C _ h1 h2
    simp only [IsFat, decide_eq_true_eq, Bool.and_eq_true] at h1 h2
    exact h1.1 ⟨ℓ, (mem_restr.mp h2.2).1, List.mem_cons_self⟩

theorem unas_lt {X : List V} {ρ : Clause V} {ℓ : Lit V} (hℓ : ℓ ∈ lits X) (hu : ℓ ∉ ρ ∧ ℓ.neg ∉ ρ) :
    unas X (ℓ :: ρ) < unas X ρ := by
  unfold unas
  have := countP_add_le (lits X) (fun l => decide (l ∉ ℓ :: ρ ∧ l.neg ∉ ℓ :: ρ))
    (fun l => decide (l = ℓ)) (fun l => decide (l ∉ ρ ∧ l.neg ∉ ρ))
    (by intro l _ h; simp only [decide_eq_true_eq, List.mem_cons, not_or] at h ⊢; exact ⟨h.1.2, h.2.2⟩)
    (by intro l _ h; simp only [decide_eq_true_eq] at h ⊢; subst h; exact hu)
    (by intro l _ h1 h2; simp only [decide_eq_true_eq, List.mem_cons, not_or] at h1 h2; exact h1.1.1 h2)
  have : 0 < (lits X).countP (fun l => decide (l = ℓ)) :=
    List.countP_pos_iff.mpr ⟨ℓ, hℓ, by simp⟩
  omega

theorem cons_ok {ρ : Clause V} {ℓ : Lit V} (hcons : ∀ l ∈ ρ, l.neg ∉ ρ) (hu : ℓ ∉ ρ ∧ ℓ.neg ∉ ρ) :
    ∀ l ∈ ℓ :: ρ, l.neg ∉ ℓ :: ρ := by
  have hne : ∀ l : Lit V, l.neg ≠ l := by intro l h; cases l; simp [Lit.neg] at h
  intro l hl h
  rcases List.mem_cons.mp hl with rfl | hl
  · rcases List.mem_cons.mp h with h | h
    · exact hne _ h
    · exact hu.2 h
  · rcases List.mem_cons.mp h with h | h
    · apply hu.2; rw [← h]; simp; exact hl
    · exact hcons l hl h

theorem fat_zero_of_unas {ρ : Clause V} (h : unas X ρ ≤ d) : fat X π d ρ = 0 := by
  unfold fat
  rw [List.countP_eq_zero]
  intro C _ hC
  simp only [IsFat, decide_eq_true_eq] at hC
  have := wd_restr_le_unas (X := X) hC.1
  omega

theorem main (hX : X.Nodup) {w0 : Nat} (hF : ∀ C ∈ F, wd X C ≤ w0) :
    ∀ u (ρ : Clause V) b, unas X ρ = u → (∀ l ∈ ρ, l.neg ∉ ρ) →
      (fat X π d ρ = 0 ∨ fat X π d ρ * (u - d) ^ b < u ^ b) →
      Der (AxR F X ρ) X (w0 + d + b) [] := by
  intro u
  induction u using Nat.strongRecOn with
  | _ u ih =>
  intro ρ b hu hcons hcond
  by_cases hf : fat X π d ρ = 0
  · -- no fat lines: the restricted refutation itself has width `≤ d`
    have hW : ∀ C ∈ π.steps, ¬ Sat ρ C → wd X (restr X ρ C) ≤ w0 + d + b := by
      intro C hC hs
      unfold fat at hf
      have := (List.countP_eq_zero.mp hf) C hC
      simp only [IsFat, decide_eq_true_eq] at this
      have h2 : ¬ d < wd X (restr X ρ C) := fun h => this ⟨hs, h⟩
      exact Nat.le_trans (Nat.le_of_not_lt h2) (by omega)
    obtain ⟨k, hk, hke⟩ := List.mem_iff_getElem.mp π.empty_mem
    have := base π hcons hW k hk
    rw [hke] at this
    rcases this with ⟨l, hl, _⟩ | hd
    · simp at hl
    · simpa [restr] using hd
  have hc := hcond.resolve_left hf
  have hb : b ≠ 0 := by intro hb; subst hb; simp at hc; exact hf hc
  have hsum := sum_cnt X π d ρ
  have hne : lits X ≠ [] := by
    intro h; rw [h, List.map_nil, List.sum_nil] at hsum
    exact hf (Nat.eq_zero_of_le_zero (Nat.le_trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos d)) hsum))
  obtain ⟨ℓ, hℓ, hmax⟩ := exists_max (lits X) (cnt X π d ρ) hne
  have hsum2 : ((lits X).map (cnt X π d ρ)).sum ≤ u * cnt X π d ρ ℓ := by
    rw [← hu]
    apply sum_le_countP_mul
    · intro x _ hx; apply cnt_zero; simpa using hx
    · exact hmax
  have hfpos : 1 ≤ fat X π d ρ := by omega
  have hcntpos : 0 < cnt X π d ρ ℓ := by
    rcases Nat.eq_zero_or_pos (cnt X π d ρ ℓ) with h | h
    · rw [h] at hsum2
      have : fat X π d ρ * (d + 1) ≥ 1 := Nat.le_trans hfpos (Nat.le_mul_of_pos_right _ (by omega))
      omega
    · exact h
  have hfree : ℓ ∉ ρ ∧ ℓ.neg ∉ ρ := by
    apply Classical.byContradiction; intro h
    have := cnt_zero X π d (ρ := ρ) h; omega
  have hvar : ℓ.var ∈ X := mem_lits.mp hℓ
  -- branch A: set `ℓ` true
  have hA : Der (AxR F X ρ) X (w0 + d + b) [ℓ.neg] := by
    have huA := unas_lt hℓ hfree
    rw [hu] at huA
    have hcA := arith_step hb (fat_cnt X π d ρ ℓ) (Nat.le_trans hsum hsum2) hc
    have hcondA : fat X π d (ℓ :: ρ) = 0 ∨
        fat X π d (ℓ :: ρ) * (unas X (ℓ :: ρ) - d) ^ (b - 1) < unas X (ℓ :: ρ) ^ (b - 1) := by
      rcases Nat.eq_zero_or_pos (unas X (ℓ :: ρ)) with h0 | h0
      · exact Or.inl (fat_zero_of_unas X π d (by omega))
      · exact Or.inr (cond_mono (Nat.le_of_lt huA) h0 hcA)
    have dA := ih _ huA (ℓ :: ρ) (b - 1) rfl (cons_ok hcons hfree) hcondA
    have := lift hX hF (W := w0 + d + (b - 1)) (by omega) hvar dA
    have e : w0 + d + (b - 1) + 1 = w0 + d + b := by omega
    rw [e] at this
    exact this
  -- branch B: set `ℓ` false
  have hfreeN : ℓ.neg ∉ ρ ∧ ℓ.neg.neg ∉ ρ := by simp [hfree]
  have huB := unas_lt (ℓ := ℓ.neg) (mem_lits.mpr hvar) hfreeN
  rw [hu] at huB
  have hcondB : fat X π d (ℓ.neg :: ρ) = 0 ∨
      fat X π d (ℓ.neg :: ρ) * (unas X (ℓ.neg :: ρ) - d) ^ b < unas X (ℓ.neg :: ρ) ^ b := by
    rcases Nat.eq_zero_or_pos (unas X (ℓ.neg :: ρ)) with h0 | h0
    · exact Or.inl (fat_zero_of_unas X π d (by omega))
    · refine Or.inr (cond_mono (Nat.le_of_lt huB) h0 ?_)
      exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (fat_mono X π d ρ ℓ.neg)) hc
  have dB := ih _ huB (ℓ.neg :: ρ) b rfl (cons_ok hcons hfreeN) hcondB
  exact glue hF (by omega) hA dB

end Main

/-! ## The size–width relation -/

theorem der_mono_ax {Ax Ax' : Clause V → Prop} {X : List V} {W : Nat} {C : Clause V}
    (hA : ∀ D, Ax D → Ax' D) (h : Der Ax X W C) : Der Ax' X W C := by
  induction h with
  | ax hax hok => exact Der.ax (hA _ hax) hok
  | res l _ _ hlA hlB hA' hB' hok ihA ihB => exact Der.res l ihA ihB hlA hlB hA' hB' hok
  | weak _ hAC hok ih => exact Der.weak ih hAC hok

theorem restr_nil {X : List V} {C : Clause V} (h : ∀ l ∈ C, l.var ∈ X) : restr X [] C = C := by
  unfold restr
  rw [List.filter_eq_self]
  intro l hl; simp [h l hl]

theorem axR_nil {F : CNF V} {X : List V} (hF : ∀ C ∈ F, ∀ l ∈ C, l.var ∈ X) (D : Clause V) :
    AxR F X [] D → D ∈ F := by
  rintro ⟨C, hC, _, rfl⟩
  rw [restr_nil (hF C hC)]; exact hC

theorem wd_restr_nil (X : List V) (C : Clause V) : wd X (restr X [] C) = wd X C := by
  unfold wd
  apply List.countP_congr
  intro l hl
  have := mem_lits.mp hl
  simp [mem_restr, this]

/-- Width-bounded refutations in the `Refutation` format are `Der` refutations. -/
theorem der_of_refutation {X : List V} {F : CNF V} (hF : ∀ C ∈ F, ∀ l ∈ C, l.var ∈ X)
    (π : Refutation F) {W : Nat} (hW : ∀ C ∈ π.steps, wd X C ≤ W) : Der (· ∈ F) X W [] := by
  obtain ⟨k, hk, hke⟩ := List.mem_iff_getElem.mp π.empty_mem
  have := base π (ρ := []) (by simp) (fun C hC _ => by rw [wd_restr_nil]; exact hW C hC) k hk
  rw [hke] at this
  rcases this with ⟨l, hl, _⟩ | hd
  · simp at hl
  · exact der_mono_ax (axR_nil hF) (by simpa [restr] using hd)

/-- **Ben-Sasson–Wigderson, width from size.** If at most `f` lines of a refutation of `F` have
more than `d` literals and `f (2N-d)^b < (2N)^b` (`N = |X|`), then `F` has a resolution
refutation of width `≤ w₀ + d + b`. -/
theorem bsw_width {X : List V} (hX : X.Nodup) {F : CNF V} {w0 : Nat} (hF : ∀ C ∈ F, OK X w0 C)
    (π : Refutation F) (d b : Nat)
    (h : π.steps.countP (fun C => decide (d < wd X C)) * (2 * X.length - d) ^ b
      < (2 * X.length) ^ b) :
    Der (· ∈ F) X (w0 + d + b) [] := by
  have hu : unas X [] = 2 * X.length := by
    unfold unas; rw [← length_lits X, List.countP_eq_length]; intro l _; simp
  have hfat : fat X π d [] = π.steps.countP (fun C => decide (d < wd X C)) := by
    unfold fat; apply List.countP_congr; intro C _
    simp [IsFat, Sat, wd_restr_nil]
  have := main X π d hX (w0 := w0) (fun C hC => (hF C hC).2) _ [] b hu (by simp)
    (Or.inr (by rw [hfat]; exact h))
  exact der_mono_ax (axR_nil fun C hC => (hF C hC).1) this

/-- **Ben-Sasson–Wigderson size–width relation** (general, DAG-like resolution): if `F` (clauses of
width `≤ w₀` over the `N` variables `X`) has no refutation of width `≤ w₀ + d + b`, then every
resolution refutation of `F` has size `S` with `(2N)^b ≤ S · (2N - d)^b`. -/
theorem bsw_size {X : List V} (hX : X.Nodup) {F : CNF V} {w0 : Nat} (hF : ∀ C ∈ F, OK X w0 C)
    (d b : Nat) (hW : ¬ Der (· ∈ F) X (w0 + d + b) []) (π : Refutation F) :
    (2 * X.length) ^ b ≤ π.steps.length * (2 * X.length - d) ^ b := by
  apply Nat.le_of_not_lt
  intro hlt
  apply hW
  apply bsw_width hX hF π d b
  exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ List.countP_le_length) hlt

/-- The symmetric case `d = b = k`: no refutation of width `w₀ + 2k` forces size
`S ≥ (2N/(2N-k))^k ≥ exp(k²/(2N))`. -/
theorem bsw_size_sq {X : List V} (hX : X.Nodup) {F : CNF V} {w0 : Nat} (hF : ∀ C ∈ F, OK X w0 C)
    (k : Nat) (hW : ¬ Der (· ∈ F) X (w0 + 2 * k) []) (π : Refutation F) :
    (2 * X.length) ^ k ≤ π.steps.length * (2 * X.length - k) ^ k :=
  bsw_size hX hF k k (by rw [Nat.add_assoc, ← Nat.two_mul]; exact hW) π

end Programme.«20261024-1110-proof-complexity».BSW

#print axioms Programme.«20261024-1110-proof-complexity».BSW.bsw_size
#print axioms Programme.«20261024-1110-proof-complexity».BSW.bsw_size_sq
#print axioms Programme.«20261024-1110-proof-complexity».BSW.der_of_refutation
#print axioms Programme.«20261024-1110-proof-complexity».BSW.Der.sound
