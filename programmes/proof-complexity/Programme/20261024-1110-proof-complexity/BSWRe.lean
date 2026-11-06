import Programme.«20261024-1110-proof-complexity».Haken

/-!
# Ben-Sasson–Wigderson size–width relation: an independent reproof (core Lean 4)

Reproof of th's K11 (`Work.BSW.bsw_size`) over K1's `Refutation` type (`Work.Haken`). The
width notions `lits`, `wd`, `OK`, `Der` are restated with the same definitions as in K11's
statement; the proof is written from scratch.

Proof. A restriction `ρ` is a consistent list of literals set true. `restr X ρ C` keeps the
literals of `C` over `X` that `ρ` does not falsify. The restricted refutation `π|ρ` is a
width-`W` derivation from the restricted axioms as soon as every unsatisfied line has
restricted width `≤ W` (`base`). Otherwise pick the literal `ℓ` lying in the most fat lines
(restricted width `> d`), refute `F|ℓ` at width `W` and `F|¬ℓ` at width `W+1`
(outer induction on `b`, inner induction on the number of unassigned variables), and glue.
-/

namespace Programme.«20261024-1110-proof-complexity».BSWR

open Programme.«20261024-1110-proof-complexity».Haken

variable {V : Type} [DecidableEq V]

/-! ## Width-bounded resolution (definitions as in K11's statement) -/

def neg (l : Lit V) : Lit V := ⟨l.var, !l.pos⟩

def lits (X : List V) : List (Lit V) := X.flatMap fun x => [⟨x, true⟩, ⟨x, false⟩]

def wd (X : List V) (C : Clause V) : Nat := (lits X).countP fun l => decide (l ∈ C)

def OK (X : List V) (W : Nat) (C : Clause V) : Prop := (∀ l ∈ C, l.var ∈ X) ∧ wd X C ≤ W

/-- Width-`W` derivability from the axiom set `Ax` (resolution and weakening). -/
inductive Der (Ax : Clause V → Prop) (X : List V) (W : Nat) : Clause V → Prop
  | ax {C} : Ax C → OK X W C → Der Ax X W C
  | res {A B C} (l : Lit V) : Der Ax X W A → Der Ax X W B → l ∈ A → neg l ∈ B →
      (∀ m ∈ A, m ≠ l → m ∈ C) → (∀ m ∈ B, m ≠ neg l → m ∈ C) → OK X W C → Der Ax X W C
  | weak {A C} : Der Ax X W A → (∀ m ∈ A, m ∈ C) → OK X W C → Der Ax X W C

/-! ## Literals and width -/

theorem neg_neg (l : Lit V) : neg (neg l) = l := by
  cases l with | mk x p => cases p <;> rfl

theorem neg_ne (l : Lit V) : neg l ≠ l := by
  cases l with | mk x p => cases p <;> simp [neg]

theorem mem_lits {X : List V} {l : Lit V} : l ∈ lits X ↔ l.var ∈ X := by
  cases l with
  | mk x p =>
    simp only [lits, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro ⟨y, hy, h | h⟩ <;> cases h <;> exact hy
    · intro hx; exact ⟨x, hx, by cases p <;> simp⟩

theorem length_lits (X : List V) : (lits X).length = 2 * X.length := by
  induction X with
  | nil => rfl
  | cons x X ih =>
    simp only [lits, List.flatMap_cons, List.length_append, List.length_cons, List.length_nil] at *
    omega

theorem wd_mono {X : List V} {C D : Clause V} (h : ∀ l ∈ C, l ∈ D) : wd X C ≤ wd X D := by
  unfold wd
  apply List.countP_mono_left
  intro l _ hl
  simp only [decide_eq_true_eq] at *
  exact h l hl

theorem count_lits_le {X : List V} (hX : X.Nodup) (l : Lit V) :
    (lits X).countP (fun m => decide (m = l)) ≤ 1 := by
  induction X with
  | nil => simp [lits]
  | cons x X ih =>
    have hx : x ∉ X := (List.nodup_cons.mp hX).1
    have ih := ih (List.nodup_cons.mp hX).2
    have e : lits (x :: X) = ⟨x, true⟩ :: ⟨x, false⟩ :: lits X := rfl
    rw [e, List.countP_cons, List.countP_cons]
    by_cases hv : l.var = x
    · have h0 : (lits X).countP (fun m => decide (m = l)) = 0 := by
        rw [List.countP_eq_zero]
        intro m hm h
        simp only [decide_eq_true_eq] at h
        subst h
        exact hx (hv ▸ mem_lits.mp hm)
      cases l with
      | mk y p =>
        simp only at hv; subst hv
        cases p <;> simp [h0]
    · have h1 : ¬ (⟨x, true⟩ : Lit V) = l := fun h => hv (h ▸ rfl)
      have h2 : ¬ (⟨x, false⟩ : Lit V) = l := fun h => hv (h ▸ rfl)
      simp [h1, h2]; exact ih

theorem wd_cons {X : List V} (hX : X.Nodup) (l : Lit V) (C : Clause V) :
    wd X (l :: C) ≤ wd X C + 1 := by
  unfold wd
  have e : (lits X).countP (fun m => decide (m ∈ l :: C))
      = (lits X).countP (fun m => decide (m ∈ C) || decide (m = l)) := by
    apply List.countP_congr
    intro m _
    simp [List.mem_cons, or_comm]
  rw [e]
  have := countP_or_le (lits X) (fun m => decide (m ∈ C)) (fun m => decide (m = l))
  have := count_lits_le hX l
  omega

theorem ok_cons {X : List V} (hX : X.Nodup) {W : Nat} {l : Lit V} {C : Clause V}
    (hl : l.var ∈ X) (h : OK X W C) : OK X (W + 1) (l :: C) := by
  refine ⟨?_, ?_⟩
  · intro m hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hl
    · exact h.1 m hm
  · have := wd_cons hX l C; have := h.2; omega

/-! ## Restrictions -/

def sat (ρ C : Clause V) : Bool := C.any fun l => decide (l ∈ ρ)

def restr (X : List V) (ρ C : Clause V) : Clause V :=
  C.filter fun l => decide (l.var ∈ X) && !decide (neg l ∈ ρ)

def Cons (ρ : Clause V) : Prop := ∀ l ∈ ρ, neg l ∉ ρ

/-- The axioms of `F|ρ`. -/
def Ax (F : CNF V) (X : List V) (ρ : Clause V) (E : Clause V) : Prop :=
  ∃ D ∈ F, sat ρ D = false ∧ E = restr X ρ D

theorem sat_false {ρ C : Clause V} : sat ρ C = false ↔ ∀ l ∈ C, l ∉ ρ := by
  unfold sat
  constructor
  · intro h l hl hr
    have : C.any (fun l => decide (l ∈ ρ)) = true := List.any_eq_true.mpr ⟨l, hl, by simpa using hr⟩
    rw [h] at this; exact Bool.noConfusion this
  · intro h
    cases e : C.any (fun l => decide (l ∈ ρ)) with
    | false => rfl
    | true =>
      obtain ⟨l, hl, hr⟩ := List.any_eq_true.mp e
      exact absurd (by simpa using hr) (h l hl)

theorem mem_restr {X : List V} {ρ C : Clause V} {l : Lit V} :
    l ∈ restr X ρ C ↔ l ∈ C ∧ l.var ∈ X ∧ neg l ∉ ρ := by
  simp [restr, List.mem_filter]

theorem restr_sub {X : List V} {ρ C : Clause V} : ∀ l ∈ restr X ρ C, l ∈ C :=
  fun _ h => (mem_restr.mp h).1

theorem ok_restr {X : List V} {ρ C : Clause V} {W : Nat} (h : wd X (restr X ρ C) ≤ W) :
    OK X W (restr X ρ C) := ⟨fun _ hl => (mem_restr.mp hl).2.1, h⟩

theorem cons_cons {ρ : Clause V} {ℓ : Lit V} (hc : Cons ρ) (h1 : ℓ ∉ ρ) (h2 : neg ℓ ∉ ρ) :
    Cons (ℓ :: ρ) := by
  intro l hl
  rcases List.mem_cons.mp hl with rfl | hl
  · intro h
    rcases List.mem_cons.mp h with h | h
    · exact neg_ne l h
    · exact h2 h
  · intro h
    rcases List.mem_cons.mp h with h | h
    · apply h2; rw [← h, neg_neg]; exact hl
    · exact hc l hl h

/-! ## Base case: the restricted refutation -/

theorem base {F : CNF V} {X : List V} {w0 W : Nat} (hF : ∀ C ∈ F, OK X w0 C) (hw : w0 ≤ W)
    (π : Refutation F) {ρ : Clause V} (hc : Cons ρ)
    (hW : ∀ C ∈ π.steps, sat ρ C = false → wd X (restr X ρ C) ≤ W) :
    Der (Ax F X ρ) X W [] := by
  have key : ∀ k (hk : k < π.steps.length), sat ρ (π.steps[k]) = false →
      Der (Ax F X ρ) X W (restr X ρ π.steps[k]) := by
    intro k
    induction k using Nat.strongRecOn with
    | _ k ih =>
      intro hk hs
      have hok : OK X W (restr X ρ π.steps[k]) := ok_restr (hW _ (List.getElem_mem hk) hs)
      have hsC := sat_false.mp hs
      rcases π.derived k hk with hax | ⟨a, b, ha, hb, x, hxA, hxB, hA, hB⟩
      · exact Der.ax ⟨_, hax, hs, rfl⟩ hok
      · have hak : a < π.steps.length := Nat.lt_trans ha hk
        have hbk : b < π.steps.length := Nat.lt_trans hb hk
        by_cases h1 : (⟨x, true⟩ : Lit V) ∈ ρ
        · -- the positive pivot is true: `π.steps[b]|ρ` already lies inside `π.steps[k]|ρ`
          have hn : (⟨x, false⟩ : Lit V) ∉ ρ := hc _ h1
          have hsB : sat ρ π.steps[b] = false := by
            apply sat_false.mpr
            intro l hl
            by_cases e : l = ⟨x, false⟩
            · rw [e]; exact hn
            · exact hsC l (hB l hl e)
          refine Der.weak (ih b hb hbk hsB) ?_ hok
          intro m hm
          obtain ⟨hm1, hm2, hm3⟩ := mem_restr.mp hm
          have : m ≠ ⟨x, false⟩ := by rintro rfl; exact hm3 h1
          exact mem_restr.mpr ⟨hB m hm1 this, hm2, hm3⟩
        by_cases h2 : (⟨x, false⟩ : Lit V) ∈ ρ
        · have hsA : sat ρ π.steps[a] = false := by
            apply sat_false.mpr
            intro l hl
            by_cases e : l = ⟨x, true⟩
            · rw [e]; exact h1
            · exact hsC l (hA l hl e)
          refine Der.weak (ih a ha hak hsA) ?_ hok
          intro m hm
          obtain ⟨hm1, hm2, hm3⟩ := mem_restr.mp hm
          have : m ≠ ⟨x, true⟩ := by rintro rfl; exact hm3 h2
          exact mem_restr.mpr ⟨hA m hm1 this, hm2, hm3⟩
        have hsA : sat ρ π.steps[a] = false := by
          apply sat_false.mpr
          intro l hl
          by_cases e : l = ⟨x, true⟩
          · rw [e]; exact h1
          · exact hsC l (hA l hl e)
        have hsB : sat ρ π.steps[b] = false := by
          apply sat_false.mpr
          intro l hl
          by_cases e : l = ⟨x, false⟩
          · rw [e]; exact h2
          · exact hsC l (hB l hl e)
        by_cases hx : x ∈ X
        · refine Der.res ⟨x, true⟩ (ih a ha hak hsA) (ih b hb hbk hsB)
            (mem_restr.mpr ⟨hxA, hx, h2⟩) (mem_restr.mpr ⟨hxB, hx, h1⟩) ?_ ?_ hok
          · intro m hm hne
            obtain ⟨hm1, hm2, hm3⟩ := mem_restr.mp hm
            exact mem_restr.mpr ⟨hA m hm1 hne, hm2, hm3⟩
          · intro m hm hne
            obtain ⟨hm1, hm2, hm3⟩ := mem_restr.mp hm
            exact mem_restr.mpr ⟨hB m hm1 hne, hm2, hm3⟩
        · refine Der.weak (ih a ha hak hsA) ?_ hok
          intro m hm
          obtain ⟨hm1, hm2, hm3⟩ := mem_restr.mp hm
          have : m ≠ ⟨x, true⟩ := by rintro rfl; exact hx hm2
          exact mem_restr.mpr ⟨hA m hm1 this, hm2, hm3⟩
  obtain ⟨k, hk, e⟩ := List.mem_iff_getElem.mp π.empty_mem
  have := key k hk (by rw [e]; rfl)
  rw [e] at this
  exact this

/-! ## Gluing the two branches -/

theorem der_mono {Ax Ax' : Clause V → Prop} {X : List V} {W : Nat}
    (h : ∀ C, Ax C → OK X W C → Der Ax' X W C) {D : Clause V} (hD : Der Ax X W D) :
    Der Ax' X W D := by
  induction hD with
  | ax hC hok => exact h _ hC hok
  | res l _ _ h1 h2 h3 h4 hok ihA ihB => exact Der.res l ihA ihB h1 h2 h3 h4 hok
  | weak _ h1 hok ih => exact Der.weak ih h1 hok

/-- A width-`W` refutation of `F|ℓ` gives a width-`(W+1)` derivation of `¬ℓ` from `F|ρ`. -/
theorem lift_neg {F : CNF V} {X : List V} (hX : X.Nodup) {w0 W : Nat} (hF : ∀ C ∈ F, OK X w0 C)
    (hw : w0 ≤ W) {ρ : Clause V} {ℓ : Lit V} (hℓ : ℓ.var ∈ X) {D : Clause V}
    (hD : Der (Ax F X (ℓ :: ρ)) X W D) : Der (Ax F X ρ) X (W + 1) (neg ℓ :: D) := by
  have hnℓ : (neg ℓ).var ∈ X := hℓ
  induction hD with
  | @ax E hE hok =>
    obtain ⟨C, hC, hs, rfl⟩ := hE
    have hs' : sat ρ C = false := by
      apply sat_false.mpr
      intro l hl hr
      exact sat_false.mp hs l hl (List.mem_cons_of_mem _ hr)
    have hokC : OK X (W + 1) (restr X ρ C) :=
      ok_restr (Nat.le_trans (wd_mono restr_sub) (Nat.le_trans (hF C hC).2 (by omega)))
    refine Der.weak (Der.ax ⟨C, hC, hs', rfl⟩ hokC) ?_ (ok_cons hX hnℓ hok)
    intro m hm
    obtain ⟨hm1, hm2, hm3⟩ := mem_restr.mp hm
    by_cases e : m = neg ℓ
    · rw [e]; exact List.mem_cons_self
    · apply List.mem_cons_of_mem
      refine mem_restr.mpr ⟨hm1, hm2, ?_⟩
      intro h
      rcases List.mem_cons.mp h with h | h
      · apply e; rw [← h, neg_neg]
      · exact hm3 h
  | res l _ _ h1 h2 h3 h4 hok ihA ihB =>
    refine Der.res l ihA ihB (List.mem_cons_of_mem _ h1) (List.mem_cons_of_mem _ h2) ?_ ?_
      (ok_cons hX hnℓ hok)
    · intro m hm hne
      rcases List.mem_cons.mp hm with rfl | hm
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (h3 m hm hne)
    · intro m hm hne
      rcases List.mem_cons.mp hm with rfl | hm
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (h4 m hm hne)
  | weak _ h1 hok ih =>
    refine Der.weak ih ?_ (ok_cons hX hnℓ hok)
    intro m hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (h1 m hm)

theorem glue {F : CNF V} {X : List V} (hX : X.Nodup) {w0 W : Nat} (hF : ∀ C ∈ F, OK X w0 C)
    (hw : w0 ≤ W) {ρ : Clause V} {ℓ : Lit V} (hℓ : ℓ.var ∈ X) (hu : neg ℓ ∉ ρ)
    (h1 : Der (Ax F X (ℓ :: ρ)) X W []) (h2 : Der (Ax F X (neg ℓ :: ρ)) X (W + 1) []) :
    Der (Ax F X ρ) X (W + 1) [] := by
  have hn : Der (Ax F X ρ) X (W + 1) [neg ℓ] := lift_neg hX hF hw hℓ h1
  refine der_mono ?_ h2
  intro E hE hok
  obtain ⟨C, hC, hs, rfl⟩ := hE
  have hs' : sat ρ C = false := by
    apply sat_false.mpr
    intro l hl hr
    exact sat_false.mp hs l hl (List.mem_cons_of_mem _ hr)
  have hokC : OK X (W + 1) (restr X ρ C) :=
    ok_restr (Nat.le_trans (wd_mono restr_sub) (Nat.le_trans (hF C hC).2 (by omega)))
  have hax : Der (Ax F X ρ) X (W + 1) (restr X ρ C) := Der.ax ⟨C, hC, hs', rfl⟩ hokC
  -- every literal of `C|ρ` other than `ℓ` survives in `C|(¬ℓ, ρ)`
  have hkeep : ∀ m ∈ restr X ρ C, m ≠ ℓ → m ∈ restr X (neg ℓ :: ρ) C := by
    intro m hm hne
    obtain ⟨hm1, hm2, hm3⟩ := mem_restr.mp hm
    refine mem_restr.mpr ⟨hm1, hm2, ?_⟩
    intro h
    rcases List.mem_cons.mp h with h | h
    · apply hne
      have := congrArg neg h
      rwa [neg_neg, neg_neg] at this
    · exact hm3 h
  by_cases hm : ℓ ∈ restr X ρ C
  · refine Der.res ℓ hax hn hm List.mem_cons_self hkeep ?_ hok
    intro m hm' hne
    rcases List.mem_cons.mp hm' with rfl | h
    · exact absurd rfl hne
    · exact absurd h List.not_mem_nil
  · refine Der.weak hax ?_ hok
    intro m h
    exact hkeep m h (by rintro rfl; exact hm h)

/-! ## Counting fat lines -/

theorem countP_add_le' {α} (l : List α) (p q r : α → Bool)
    (hp : ∀ x ∈ l, p x = true → r x = true ∧ q x = false) (hq : ∀ x ∈ l, q x = true → r x = true) :
    l.countP p + l.countP q ≤ l.countP r := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.countP_cons]
    have ih := ih (fun x hx => hp x (List.mem_cons_of_mem _ hx))
      (fun x hx => hq x (List.mem_cons_of_mem _ hx))
    have ha := hp a List.mem_cons_self
    have hb := hq a List.mem_cons_self
    cases hpa : p a <;> cases hqa : q a <;> cases hra : r a <;> simp_all <;> omega

theorem countP_lt {α} (l : List α) (p q : α → Bool) (h : ∀ x ∈ l, p x = true → q x = true)
    {y : α} (hy : y ∈ l) (hq : q y = true) (hp : p y = false) : l.countP p < l.countP q := by
  induction l with
  | nil => exact absurd hy List.not_mem_nil
  | cons a l ih =>
    simp only [List.countP_cons]
    have hle : l.countP p ≤ l.countP q :=
      List.countP_mono_left (fun x hx hpx => h x (List.mem_cons_of_mem _ hx) hpx)
    rcases List.mem_cons.mp hy with rfl | hy
    · simp [hq, hp]; omega
    · have := ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) hy
      have := h a List.mem_cons_self
      cases hpa : p a <;> cases hqa : q a <;> simp_all <;> omega

theorem exists_max {α} (l : List α) (g : α → Nat) (hl : l ≠ []) :
    ∃ y ∈ l, ∀ x ∈ l, g x ≤ g y := by
  induction l with
  | nil => exact absurd rfl hl
  | cons a l ih =>
    by_cases h : l = []
    · subst h; exact ⟨a, List.mem_cons_self, by simp⟩
    · obtain ⟨y, hy, hmax⟩ := ih h
      by_cases hay : g y ≤ g a
      · refine ⟨a, List.mem_cons_self, ?_⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact Nat.le_refl _
        · exact Nat.le_trans (hmax x hx) hay
      · refine ⟨y, List.mem_cons_of_mem _ hy, ?_⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · omega
        · exact hmax x hx

section counting

variable (X : List V) (d : Nat)

def isFat (ρ C : Clause V) : Bool := !sat ρ C && decide (d < wd X (restr X ρ C))

def fat (L : List (Clause V)) (ρ : Clause V) : Nat := L.countP (isFat X d ρ)

def cnt (L : List (Clause V)) (ρ : Clause V) (ℓ : Lit V) : Nat :=
  L.countP fun C => isFat X d ρ C && decide (ℓ ∈ restr X ρ C)

/-- Number of variables of `X` left unassigned by `ρ`. -/
def unas (ρ : Clause V) : Nat :=
  X.countP fun x => !decide ((⟨x, true⟩ : Lit V) ∈ ρ) && !decide ((⟨x, false⟩ : Lit V) ∈ ρ)

end counting

theorem sat_cons_false {ρ C : Clause V} {ℓ : Lit V} (h : sat (ℓ :: ρ) C = false) : sat ρ C = false :=
  sat_false.mpr fun l hl hr => sat_false.mp h l hl (List.mem_cons_of_mem _ hr)

theorem restr_cons_sub {X : List V} {ρ C : Clause V} {ℓ : Lit V} :
    ∀ m ∈ restr X (ℓ :: ρ) C, m ∈ restr X ρ C := by
  intro m hm
  obtain ⟨h1, h2, h3⟩ := mem_restr.mp hm
  exact mem_restr.mpr ⟨h1, h2, fun h => h3 (List.mem_cons_of_mem _ h)⟩

theorem isFat_cons {X : List V} {d : Nat} {ρ C : Clause V} {ℓ : Lit V}
    (h : isFat X d (ℓ :: ρ) C = true) : isFat X d ρ C = true ∧ decide (ℓ ∈ restr X ρ C) = false := by
  simp only [isFat, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  obtain ⟨hs, hw⟩ := h
  refine ⟨?_, ?_⟩
  · simp only [isFat, sat_cons_false hs, Bool.not_false, Bool.true_and, decide_eq_true_eq]
    exact Nat.lt_of_lt_of_le hw (wd_mono restr_cons_sub)
  · simp only [decide_eq_false_iff_not]
    intro hm
    exact sat_false.mp hs ℓ (mem_restr.mp hm).1 List.mem_cons_self

theorem fat_cons_le (X : List V) (d : Nat) (L : List (Clause V)) (ρ : Clause V) (ℓ : Lit V) :
    fat X d L (ℓ :: ρ) + cnt X d L ρ ℓ ≤ fat X d L ρ := by
  unfold fat cnt
  apply countP_add_le'
  · intro C _ h
    have := isFat_cons h
    simp [this.1, this.2]
  · intro C _ h
    simp only [Bool.and_eq_true] at h
    exact h.1

theorem fat_cons_le' (X : List V) (d : Nat) (L : List (Clause V)) (ρ : Clause V) (ℓ : Lit V) :
    fat X d L (ℓ :: ρ) ≤ fat X d L ρ := by
  have := fat_cons_le X d L ρ ℓ; omega

/-- Double counting: some literal lies in many fat lines. -/
theorem many {X : List V} {d : Nat} {L : List (Clause V)} {ρ : Clause V}
    (hf : 0 < fat X d L ρ) :
    ∃ ℓ ∈ lits X, fat X d L ρ * (d + 1) ≤ cnt X d L ρ ℓ * (2 * X.length) ∧ 0 < cnt X d L ρ ℓ := by
  have hsum : fat X d L ρ * (d + 1) ≤ ((lits X).map fun ℓ => cnt X d L ρ ℓ).sum := by
    unfold cnt
    rw [double_count (lits X) L (fun ℓ C => isFat X d ρ C && decide (ℓ ∈ restr X ρ C))]
    apply countP_mul_le_sum
    intro C _ hC
    have e : (lits X).countP (fun ℓ => isFat X d ρ C && decide (ℓ ∈ restr X ρ C))
        = wd X (restr X ρ C) := by
      unfold wd; apply List.countP_congr; intro ℓ _; simp [hC]
    rw [e]
    simp only [isFat, Bool.and_eq_true, decide_eq_true_eq] at hC
    exact hC.2
  have hne : lits X ≠ [] := by
    intro h
    have h0 : ((lits X).map fun ℓ => cnt X d L ρ ℓ).sum = 0 := by rw [h]; rfl
    have : 0 < fat X d L ρ * (d + 1) := Nat.mul_pos hf (Nat.succ_pos d)
    omega
  obtain ⟨ℓ, hℓ, hmax⟩ := exists_max (lits X) (cnt X d L ρ) hne
  have hle := sum_le_length_mul (lits X) (cnt X d L ρ) (cnt X d L ρ ℓ) hmax
  rw [length_lits] at hle
  refine ⟨ℓ, hℓ, ?_, ?_⟩
  · rw [Nat.mul_comm (cnt X d L ρ ℓ)]; exact Nat.le_trans hsum hle
  · apply Nat.pos_of_ne_zero
    intro h0
    have h3 := Nat.le_trans hsum hle
    rw [h0, Nat.mul_zero] at h3
    have : 0 < fat X d L ρ * (d + 1) := Nat.mul_pos hf (Nat.succ_pos d)
    omega

/-- A literal lying in a fat line is unassigned and over `X`. -/
theorem cnt_pos {X : List V} {d : Nat} {L : List (Clause V)} {ρ : Clause V} {ℓ : Lit V}
    (h : 0 < cnt X d L ρ ℓ) : ℓ.var ∈ X ∧ ℓ ∉ ρ ∧ neg ℓ ∉ ρ := by
  unfold cnt at h
  obtain ⟨C, _, hC⟩ := List.countP_pos_iff.mp h
  simp only [isFat, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hC
  obtain ⟨⟨hs, _⟩, hm⟩ := hC
  obtain ⟨h1, h2, h3⟩ := mem_restr.mp hm
  exact ⟨h2, sat_false.mp hs ℓ h1, h3⟩

theorem unas_lt {X : List V} {ρ : Clause V} {ℓ : Lit V} (hℓ : ℓ.var ∈ X) (h1 : ℓ ∉ ρ)
    (h2 : neg ℓ ∉ ρ) : unas X (ℓ :: ρ) < unas X ρ := by
  unfold unas
  apply countP_lt X _ _ _ hℓ
  · cases ℓ with
    | mk x p => cases p <;> simp_all [neg]
  · cases ℓ with
    | mk x p => cases p <;> simp
  · intro y _ h
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, List.mem_cons,
      not_or] at h ⊢
    exact ⟨h.1.2, h.2.2⟩

/-! ## The induction -/

theorem step_arith {f f' c N d b : Nat} (hf' : f' + c ≤ f) (hc : f * (d + 1) ≤ c * N)
    (hlt : f * (N - d) ^ (b + 1) < N ^ (b + 1)) : f' * (N - d) ^ b < N ^ b := by
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp at hlt
    · exact h
  rcases Nat.eq_zero_or_pos f with hf0 | hfp
  · have : f' = 0 := by omega
    subst this; rw [Nat.zero_mul]; exact Nat.pow_pos hN
  -- `f' * N ≤ f * (N - d)`
  have h1 : f' * N ≤ f * (N - d) := by
    have hcf : c ≤ f := by omega
    have : f * (d + 1) ≤ f * N := Nat.le_trans hc (Nat.mul_le_mul_right N hcf)
    have hd : d ≤ N := by
      have := Nat.le_of_mul_le_mul_left this hfp; omega
    have e : f * (N - d) = f * N - f * d := Nat.mul_sub f N d
    have : f' * N ≤ (f - c) * N := Nat.mul_le_mul_right N (by omega)
    rw [Nat.sub_mul] at this
    have : f * d ≤ c * N := Nat.le_trans (Nat.mul_le_mul_left f (Nat.le_succ d)) hc
    rw [e]; omega
  apply Nat.lt_of_mul_lt_mul_left (a := N)
  calc N * (f' * (N - d) ^ b) = (f' * N) * (N - d) ^ b := by
        rw [Nat.mul_comm f' N, Nat.mul_assoc]
    _ ≤ (f * (N - d)) * (N - d) ^ b := Nat.mul_le_mul_right _ h1
    _ = f * (N - d) ^ (b + 1) := by rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm (N - d)]
    _ < N ^ (b + 1) := hlt
    _ = N * N ^ b := by rw [Nat.pow_succ, Nat.mul_comm]

theorem main {F : CNF V} {X : List V} (hX : X.Nodup) {w0 : Nat} (hF : ∀ C ∈ F, OK X w0 C)
    (π : Refutation F) (d : Nat) :
    ∀ b u (ρ : Clause V), unas X ρ ≤ u → Cons ρ →
      fat X d π.steps ρ * (2 * X.length - d) ^ b < (2 * X.length) ^ b →
      Der (Ax F X ρ) X (w0 + d + b) [] := by
  intro b
  have hbase : ∀ b (ρ : Clause V), Cons ρ → fat X d π.steps ρ = 0 →
      Der (Ax F X ρ) X (w0 + d + b) [] := by
    intro b ρ hc h0
    refine base hF (by omega) π hc ?_
    intro C hC hs
    have := (List.countP_eq_zero.mp h0) C hC
    simp only [isFat, hs, Bool.not_false, Bool.true_and, decide_eq_true_eq] at this
    omega
  induction b with
  | zero =>
    intro u ρ _ hc hlt
    simp at hlt
    exact hbase 0 ρ hc hlt
  | succ b ihb =>
    intro u
    induction u with
    | zero =>
      intro ρ hu hc hlt
      rcases Nat.eq_zero_or_pos (fat X d π.steps ρ) with h0 | hf
      · exact hbase _ ρ hc h0
      · obtain ⟨ℓ, _, _, hcnt⟩ := many hf
        obtain ⟨hℓ, h1, h2⟩ := cnt_pos hcnt
        have := unas_lt hℓ h1 h2
        omega
    | succ u ihu =>
      intro ρ hu hc hlt
      rcases Nat.eq_zero_or_pos (fat X d π.steps ρ) with h0 | hf
      · exact hbase _ ρ hc h0
      · obtain ⟨ℓ, _, hmany, hcnt⟩ := many hf
        obtain ⟨hℓ, h1, h2⟩ := cnt_pos hcnt
        -- branch `ℓ = 1`: one less in `b`
        have hd1 : Der (Ax F X (ℓ :: ρ)) X (w0 + d + b) [] :=
          ihb (unas X (ℓ :: ρ)) (ℓ :: ρ) (Nat.le_refl _) (cons_cons hc h1 h2)
            (step_arith (fat_cons_le X d π.steps ρ ℓ) hmany hlt)
        -- branch `ℓ = 0`: one less unassigned variable
        have hn1 : neg ℓ ∉ ρ := h2
        have hn2 : neg (neg ℓ) ∉ ρ := by rw [neg_neg]; exact h1
        have hlt2 : unas X (neg ℓ :: ρ) < unas X ρ := unas_lt (ℓ := neg ℓ) hℓ hn1 hn2
        have hd2 : Der (Ax F X (neg ℓ :: ρ)) X (w0 + d + (b + 1)) [] :=
          ihu (neg ℓ :: ρ) (by omega) (cons_cons hc hn1 hn2)
            (Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (fat_cons_le' X d π.steps ρ (neg ℓ))) hlt)
        exact glue (W := w0 + d + b) hX hF (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)) hℓ h2 hd1 hd2

/-! ## Main theorems -/

/-- Back from `F|∅` to `F`. -/
theorem der_nil {F : CNF V} {X : List V} {w0 W : Nat} (hF : ∀ C ∈ F, OK X w0 C) (hw : w0 ≤ W)
    {D : Clause V} (h : Der (Ax F X []) X W D) : Der (· ∈ F) X W D := by
  refine der_mono ?_ h
  intro E hE hok
  obtain ⟨C, hC, _, rfl⟩ := hE
  have hokC : OK X W C := ⟨(hF C hC).1, Nat.le_trans (hF C hC).2 hw⟩
  refine Der.weak (Der.ax hC hokC) ?_ hok
  intro m hm
  exact mem_restr.mpr ⟨hm, (hF C hC).1 m hm, List.not_mem_nil⟩

/-- Ben-Sasson–Wigderson, width form: few fat lines give a narrow refutation. -/
theorem bsw_width {X : List V} (hX : X.Nodup) {F : CNF V} {w0 : Nat} (hF : ∀ C ∈ F, OK X w0 C)
    (π : Refutation F) (d b : Nat)
    (h : fat X d π.steps [] * (2 * X.length - d) ^ b < (2 * X.length) ^ b) :
    Der (· ∈ F) X (w0 + d + b) [] :=
  der_nil hF (by omega)
    (main hX hF π d b (unas X []) [] (Nat.le_refl _) (fun _ h => absurd h List.not_mem_nil) h)

/-- Ben-Sasson–Wigderson, size form (K11's statement over K1's `Refutation` type). -/
theorem bsw_size {X : List V} (hX : X.Nodup) {F : CNF V} {w0 : Nat} (hF : ∀ C ∈ F, OK X w0 C)
    (d b : Nat) (hW : ¬ Der (· ∈ F) X (w0 + d + b) []) (π : Refutation F) :
    (2 * X.length) ^ b ≤ π.steps.length * (2 * X.length - d) ^ b := by
  apply Nat.le_of_not_lt
  intro hlt
  apply hW
  apply bsw_width hX hF π d b
  exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ List.countP_le_length) hlt

end Programme.«20261024-1110-proof-complexity».BSWR

#print axioms Programme.«20261024-1110-proof-complexity».BSWR.bsw_size
