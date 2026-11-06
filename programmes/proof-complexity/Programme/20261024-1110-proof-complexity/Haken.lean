/-!
# Haken's exponential lower bound for the pigeonhole principle (core Lean 4)

Resolution refutations of CNFs, the pigeonhole formula `PHP n` (pigeons `0..n`, holes `0..n-1`),
and a proof, for every `n`, that every resolution refutation of `PHP n` has at least
`(72/71)^(4*(n/12))` clauses (stated over `Nat`: `72^(4*(n/12)) ≤ 71^(4*(n/12)) * size`).

The proof follows Haken (1985) in the critical-assignment / measure form of Beame–Pitassi:
a restriction by a partial matching `M` is applied semantically (to critical assignments
extending `M`), the clause of medium measure is shown to have many "free monotone variables",
and a greedy choice of matching edges kills a `1/72` fraction of the big clauses per step.
-/

namespace Programme.«20261024-1110-proof-complexity».Haken

open Classical

/-! ## Generic list counting lemmas -/

theorem countP_or_le {α} (l : List α) (p q : α → Bool) :
    l.countP (fun x => p x || q x) ≤ l.countP p + l.countP q := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.countP_cons]
    cases p a <;> cases q a <;> simp <;> omega

theorem countP_split {α} (l : List α) (p q : α → Bool) :
    l.countP p = l.countP (fun x => p x && q x) + l.countP (fun x => p x && !q x) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.countP_cons]
    cases p a <;> cases q a <;> simp <;> omega

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

theorem sum_le_length_mul {α} (l : List α) (g : α → Nat) (c : Nat)
    (h : ∀ x ∈ l, g x ≤ c) : (l.map g).sum ≤ l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    have := h a List.mem_cons_self
    have := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    omega

theorem sum_map_mul {α} (l : List α) (g : α → Nat) (r : Nat) :
    (l.map fun x => r * g x).sum = r * (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, Nat.mul_add]

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
      have e : (List.map (fun b => List.countP (fun a => R a b) l + if R a b = true then 1 else 0) l₂).sum
          = (List.map (fun b => List.countP (fun a => R a b) l) l₂).sum + List.countP (R a) l₂ := by
        clear ih2
        induction l₂ with
        | nil => simp
        | cons c l₃ ih3 => simp only [List.map_cons, List.sum_cons, List.countP_cons, ih3]; omega
      rw [e]; omega

theorem nodup_filter {α} {l : List α} (p : α → Bool) (h : l.Nodup) : (l.filter p).Nodup :=
  List.Pairwise.sublist List.filter_sublist h

/-- An injection from a duplicate-free list into the elements of `B` satisfying `Q`. -/
theorem length_le_countP_of_inj {α β} (l : List α) (B : List β) (Q : β → Bool) (g : α → β)
    (hl : l.Nodup) (hmem : ∀ a ∈ l, g a ∈ B ∧ Q (g a) = true)
    (hinj : ∀ a ∈ l, ∀ b ∈ l, g a = g b → a = b) : l.length ≤ B.countP Q := by
  induction l generalizing Q with
  | nil => simp
  | cons a l ih =>
    have hl' : l.Nodup := (List.pairwise_cons.mp hl).2
    have hna : ∀ b ∈ l, a ≠ b := (List.pairwise_cons.mp hl).1
    have h1 := ih (fun y => Q y && !decide (y = g a)) hl'
      (fun b hb => by
        refine ⟨(hmem b (List.mem_cons_of_mem _ hb)).1, ?_⟩
        simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
        refine ⟨(hmem b (List.mem_cons_of_mem _ hb)).2, fun e => hna b hb ?_⟩
        exact (hinj b (List.mem_cons_of_mem _ hb) a List.mem_cons_self e).symm)
      (fun x hx y hy e => hinj x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy) e)
    have h2 := countP_split B Q (fun y => decide (y = g a))
    have h3 : 0 < B.countP (fun y => Q y && decide (y = g a)) :=
      List.countP_pos_iff.mpr ⟨g a, (hmem a List.mem_cons_self).1, by
        simp [(hmem a List.mem_cons_self).2]⟩
    simp only [List.length_cons]; omega

theorem countP_le_one_of_nodup {α} (l : List α) (P : α → Bool) (x : α) (hl : l.Nodup)
    (h : ∀ y, P y = true → y = x) : l.countP P ≤ 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hl' : l.Nodup := (List.pairwise_cons.mp hl).2
    have hna : ∀ b ∈ l, a ≠ b := (List.pairwise_cons.mp hl).1
    simp only [List.countP_cons]
    by_cases hp : P a = true
    · have hax := h a hp
      have : l.countP P = 0 := by
        rw [List.countP_eq_zero]
        intro b hb hpb
        exact hna b hb (hax.trans (h b hpb).symm)
      simp [hp, this]
    · simp [hp]; exact ih hl'

/-- Removing the first coordinates of a list `M` from `range m` removes at most `M.length`. -/
theorem free_count (m : Nat) (M : List (Nat × Nat)) :
    m ≤ (List.range m).countP (fun p => decide (∀ e ∈ M, e.1 ≠ p)) + M.length := by
  induction M with
  | nil => simp
  | cons e M ih =>
    have h2 := countP_split (List.range m) (fun p => decide (∀ e ∈ M, e.1 ≠ p))
      (fun p => decide (e.1 ≠ p))
    have h3 : (List.range m).countP (fun p => decide (∀ e ∈ M, e.1 ≠ p) && !decide (e.1 ≠ p)) ≤ 1 :=
      countP_le_one_of_nodup _ _ e.1 List.nodup_range (fun y hy => by simp at hy; exact hy.2.symm)
    have h4 : (List.range m).countP (fun p => decide (∀ e ∈ M, e.1 ≠ p) && decide (e.1 ≠ p))
        = (List.range m).countP (fun p => decide (∀ e' ∈ e :: M, e'.1 ≠ p)) := by
      apply List.countP_congr; intro x _; simp; exact And.comm
    simp only [List.length_cons]; omega

/-! ## Resolution -/

/-- A literal: a variable with a polarity (`pos = true` means the variable, `false` its negation). -/
structure Lit (V : Type) where
  var : V
  pos : Bool
deriving DecidableEq, Repr

abbrev Clause (V : Type) := List (Lit V)
abbrev CNF (V : Type) := List (Clause V)

def Lit.eval {V} (a : V → Bool) (l : Lit V) : Bool := if l.pos then a l.var else !a l.var

def Clause.eval {V} (a : V → Bool) (C : Clause V) : Bool := C.any (Lit.eval a)

/-- `C` is a resolvent of `A` and `B` on some variable `x` (`x ∈ A`, `¬x ∈ B`), possibly weakened:
every other literal of `A` and of `B` occurs in `C`. -/
def IsResolvent {V} (A B C : Clause V) : Prop :=
  ∃ x, ⟨x, true⟩ ∈ A ∧ ⟨x, false⟩ ∈ B ∧
    (∀ l ∈ A, l ≠ ⟨x, true⟩ → l ∈ C) ∧ (∀ l ∈ B, l ≠ ⟨x, false⟩ → l ∈ C)

/-- A resolution refutation of `F`: a list of clauses, each an axiom of `F` or a resolvent of two
earlier clauses, containing the empty clause. Its size is `steps.length`. -/
structure Refutation {V} (F : CNF V) where
  steps : List (Clause V)
  derived : ∀ k (hk : k < steps.length), steps[k] ∈ F ∨
    ∃ a b, ∃ (ha : a < k) (hb : b < k),
      IsResolvent (steps[a]'(Nat.lt_trans ha hk)) (steps[b]'(Nat.lt_trans hb hk)) steps[k]
  empty_mem : ([] : Clause V) ∈ steps

theorem resolvent_sound {V} {A B C : Clause V} (h : IsResolvent A B C) (a : V → Bool)
    (hC : C.eval a = false) : A.eval a = false ∨ B.eval a = false := by
  obtain ⟨x, hA, hB, hAC, hBC⟩ := h
  unfold Clause.eval at *
  rw [List.any_eq_false] at hC
  cases hx : a x
  · left
    rw [List.any_eq_false]
    intro l hl
    by_cases e : l = ⟨x, true⟩
    · subst e; simp [Lit.eval, hx]
    · exact hC l (hAC l hl e)
  · right
    rw [List.any_eq_false]
    intro l hl
    by_cases e : l = ⟨x, false⟩
    · subst e; simp [Lit.eval, hx]
    · exact hC l (hBC l hl e)

/-! ## The pigeonhole formula: pigeons `0..n`, holes `0..n-1`, variable `(p, h)` = "p sits in h". -/

def pigeonAx (n p : Nat) : Clause (Nat × Nat) := (List.range n).map fun h => ⟨(p, h), true⟩

def holeAx (p q h : Nat) : Clause (Nat × Nat) := [⟨(p, h), false⟩, ⟨(q, h), false⟩]

/-- `PHP n` : `n+1` pigeons, `n` holes. Pigeon axioms for `p ≤ n`; hole axioms for `h < n`, `p < q ≤ n`. -/
def PHP (n : Nat) : CNF (Nat × Nat) :=
  (List.range (n + 1)).map (pigeonAx n) ++
  (List.range n).flatMap fun h => (List.range (n + 1)).flatMap fun p =>
    ((List.range (n + 1)).filter (fun q => p < q)).map fun q => holeAx p q h

theorem mem_PHP {n : Nat} {C : Clause (Nat × Nat)} (hC : C ∈ PHP n) :
    (∃ p, p ≤ n ∧ C = pigeonAx n p) ∨ (∃ p q h, p < q ∧ q ≤ n ∧ h < n ∧ C = holeAx p q h) := by
  unfold PHP at hC
  rcases List.mem_append.mp hC with h | h
  · left
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
    exact ⟨p, by simp at hp; omega, rfl⟩
  · right
    obtain ⟨h0, hh, h⟩ := List.mem_flatMap.mp h
    obtain ⟨p, _, h⟩ := List.mem_flatMap.mp h
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
    simp at hq hh
    exact ⟨p, q, h0, hq.2, by omega, hh, rfl⟩

/-! ## Critical assignments and partial matchings -/

/-- `f` is an `i`-critical matching: pigeons `≠ i` go bijectively to the holes `0..n-1`. -/
structure Crit (n i : Nat) (f : Nat → Nat) : Prop where
  lt : ∀ p, p ≤ n → p ≠ i → f p < n
  inj : ∀ p q, p ≤ n → q ≤ n → p ≠ i → q ≠ i → f p = f q → p = q
  surj : ∀ h, h < n → ∃ p, p ≤ n ∧ p ≠ i ∧ f p = h

/-- The truth assignment of an `i`-critical matching `f`. -/
def val (n i : Nat) (f : Nat → Nat) : Nat × Nat → Bool :=
  fun v => decide (v.1 ≤ n ∧ v.1 ≠ i ∧ f v.1 = v.2)

def Ext (M : List (Nat × Nat)) (f : Nat → Nat) : Prop := ∀ e ∈ M, f e.1 = e.2
def FreeP (M : List (Nat × Nat)) (p : Nat) : Prop := ∀ e ∈ M, e.1 ≠ p
def FreeH (M : List (Nat × Nat)) (h : Nat) : Prop := ∀ e ∈ M, e.2 ≠ h

/-- `M` is a partial matching inside the board such that every free pigeon has a critical
matching extending `M`. -/
def Good (n : Nat) (M : List (Nat × Nat)) : Prop :=
  (∀ e ∈ M, e.1 ≤ n ∧ e.2 < n) ∧ ∀ i, i ≤ n → FreeP M i → ∃ f, Crit n i f ∧ Ext M f

/-- Pigeon `i` is free and some `i`-critical matching extending `M` falsifies `C`. -/
def Fals (n : Nat) (M : List (Nat × Nat)) (C : Clause (Nat × Nat)) (i : Nat) : Prop :=
  i ≤ n ∧ FreeP M i ∧ ∃ f, Crit n i f ∧ Ext M f ∧ C.eval (val n i f) = false

/-- The measure: number of free pigeons whose critical matchings (extending `M`) falsify `C`. -/
noncomputable def mu (n : Nat) (M : List (Nat × Nat)) (C : Clause (Nat × Nat)) : Nat :=
  (List.range (n + 1)).countP fun i => decide (Fals n M C i)

noncomputable def freeCount (n : Nat) (M : List (Nat × Nat)) : Nat :=
  (List.range (n + 1)).countP fun i => decide (FreeP M i)

theorem crit_base (n i : Nat) (hi : i ≤ n) : Crit n i (fun q => if q < i then q else q - 1) where
  lt p hp hpi := by split <;> omega
  inj p q hp hq hpi hqi e := by split at e <;> split at e <;> omega
  surj h hh := by
    by_cases hhi : h < i
    · exact ⟨h, by omega, by omega, by simp [hhi]⟩
    · exact ⟨h + 1, by omega, by omega, by simp; omega⟩

theorem good_nil (n : Nat) : Good n [] :=
  ⟨by simp, fun i hi _ => ⟨_, crit_base n i hi, by simp [Ext]⟩⟩

theorem good_cons {n : Nat} {M : List (Nat × Nat)} {a h : Nat} (hM : Good n M) (ha : a ≤ n)
    (hh : h < n) (hfa : FreeP M a) (hfh : FreeH M h) : Good n ((a, h) :: M) := by
  refine ⟨?_, ?_⟩
  · intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨ha, hh⟩
    · exact hM.1 e he
  · intro i hi hfi
    have hia : a ≠ i := hfi (a, h) List.mem_cons_self
    have hfi' : FreeP M i := fun e he => hfi e (List.mem_cons_of_mem _ he)
    obtain ⟨f, hf, hext⟩ := hM.2 i hi hfi'
    obtain ⟨p, hp, hpi, hph⟩ := hf.surj h hh
    have hpM : FreeP M p := by
      intro e he hep
      have := hM.1 e he
      have : f e.1 = e.2 := hext e he
      exact hfh e he (by rw [← this, hep, hph])
    by_cases hpa : p = a
    · subst hpa
      refine ⟨f, hf, ?_⟩
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact hph
      · exact hext e he
    · let g : Nat → Nat := fun q => if q = a then h else if q = p then f a else f q
      have hfa_lt : f a < n := hf.lt a ha hia
      refine ⟨g, ⟨?_, ?_, ?_⟩, ?_⟩
      · intro q hq hqi
        simp only [g]
        split
        · exact hh
        · split
          · exact hfa_lt
          · exact hf.lt q hq hqi
      · intro q₁ q₂ hq₁ hq₂ hq₁i hq₂i e
        simp only [g] at e
        have key : ∀ x y, x ≤ n → y ≤ n → x ≠ i → y ≠ i → f x = f y → x = y :=
          fun x y hx hy hxi hyi => hf.inj x y hx hy hxi hyi
        by_cases h1 : q₁ = a <;> by_cases h2 : q₂ = a <;> by_cases h3 : q₁ = p <;>
          by_cases h4 : q₂ = p <;> simp only [h1, h2, h3, h4, hpa, Ne.symm hpa, ite_true, ite_false] at e <;>
          first
          | omega
          | (have := key _ _ hq₁ hq₂ hq₁i hq₂i e; omega)
          | (have := key _ _ hp hq₂ hpi hq₂i (hph.trans e); omega)
          | (have := key _ _ hq₁ hp hq₁i hpi (e.trans hph.symm); omega)
          | (have := key _ _ ha hq₂ (Ne.symm hia |>.symm) hq₂i e; omega)
          | (have := key _ _ hq₁ ha hq₁i (Ne.symm hia |>.symm) e; omega)
          | (have := key _ _ ha hp (Ne.symm hia |>.symm) hpi e.symm; omega)
          | (have := key _ _ ha hp (Ne.symm hia |>.symm) hpi e; omega)
          | (have := key _ _ ha hp (Ne.symm hia |>.symm) hpi (e.symm.trans hph.symm); omega)
          | (have := key _ _ ha hp (Ne.symm hia |>.symm) hpi (e.trans hph.symm); omega)
      · intro h' hh'
        obtain ⟨q, hq, hqi, hqh⟩ := hf.surj h' hh'
        by_cases hqa : q = a
        · subst hqa
          exact ⟨p, hp, hpi, by simp [g, hpa, hqh]⟩
        · by_cases hqp : q = p
          · subst hqp
            exact ⟨a, ha, hia, by simp [g]; omega⟩
          · exact ⟨q, hq, hqi, by simp [g, hqa, hqp, hqh]⟩
      · intro e he
        rcases List.mem_cons.mp he with rfl | he
        · simp [g]
        · have hea : e.1 ≠ a := fun x => hfa e he x
          have hep : e.1 ≠ p := fun x => hpM e he x
          simp [g, hea, hep, hext e he]

/-! ## The measure -/

theorem eval_false_iff {a : Nat × Nat → Bool} {C : Clause (Nat × Nat)} :
    C.eval a = false ↔ ∀ l ∈ C, l.eval a = false := by
  unfold Clause.eval; rw [List.any_eq_false]; simp

theorem fals_free {n M C i} (h : Fals n M C i) : FreeP M i := h.2.1

theorem mu_sub {n : Nat} {M : List (Nat × Nat)} {A B C : Clause (Nat × Nat)}
    (h : IsResolvent A B C) : mu n M C ≤ mu n M A + mu n M B := by
  unfold mu
  refine Nat.le_trans (List.countP_mono_left (q := fun i => decide (Fals n M A i) ||
    decide (Fals n M B i)) ?_) (countP_or_le _ _ _)
  intro i _ hi
  simp only [decide_eq_true_eq] at hi
  obtain ⟨hin, hfree, f, hf, hext, hC⟩ := hi
  rcases resolvent_sound h _ hC with hA | hB
  · simp only [Bool.or_eq_true, decide_eq_true_eq]; exact Or.inl ⟨hin, hfree, f, hf, hext, hA⟩
  · simp only [Bool.or_eq_true, decide_eq_true_eq]; exact Or.inr ⟨hin, hfree, f, hf, hext, hB⟩

theorem mu_axiom {n : Nat} {M : List (Nat × Nat)} {C : Clause (Nat × Nat)} (hC : C ∈ PHP n) :
    mu n M C ≤ 1 := by
  rcases mem_PHP hC with ⟨p, hp, rfl⟩ | ⟨p, q, h, hpq, hq, hh, rfl⟩
  · apply countP_le_one_of_nodup _ _ p List.nodup_range
    intro i hi
    simp only [decide_eq_true_eq] at hi
    obtain ⟨_, _, f, hf, _, hC⟩ := hi
    apply Classical.byContradiction
    intro hip
    have hlt := hf.lt p hp (Ne.symm hip)
    have := (eval_false_iff.mp hC) ⟨(p, f p), true⟩
      (List.mem_map.mpr ⟨f p, List.mem_range.mpr hlt, rfl⟩)
    simp [Lit.eval, val, hp, Ne.symm hip] at this
  · apply Nat.le_trans (Nat.le_of_eq ?_) (Nat.zero_le 1)
    rw [mu, List.countP_eq_zero]
    intro i _ hi
    simp only [decide_eq_true_eq] at hi
    obtain ⟨_, _, f, hf, _, hC⟩ := hi
    have h1 := (eval_false_iff.mp hC) ⟨(p, h), false⟩ (by simp [holeAx])
    have h2 := (eval_false_iff.mp hC) ⟨(q, h), false⟩ (by simp [holeAx])
    simp [Lit.eval, val] at h1 h2
    have := hf.inj p q (by omega) h2.1 h1.2.1 h2.2.1 (h1.2.2.trans h2.2.2.symm)
    omega

theorem freeCount_ge (n : Nat) (M : List (Nat × Nat)) : n + 1 - M.length ≤ freeCount n M := by
  have := free_count (n + 1) M
  have e : freeCount n M = (List.range (n + 1)).countP (fun p => decide (∀ e ∈ M, e.1 ≠ p)) := by
    unfold freeCount FreeP; apply List.countP_congr; intro x _; simp only [decide_eq_true_eq]
  omega

theorem mu_le_free (n : Nat) (M : List (Nat × Nat)) (C : Clause (Nat × Nat)) :
    mu n M C ≤ freeCount n M := by
  apply List.countP_mono_left
  intro i _ hi
  simp only [decide_eq_true_eq] at hi ⊢
  exact hi.2.1

theorem mu_empty {n : Nat} {M : List (Nat × Nat)} (hM : Good n M) : mu n M [] = freeCount n M := by
  apply List.countP_congr
  intro i hi
  have hin : i ≤ n := by simp at hi; omega
  simp only [decide_eq_true_eq]
  constructor
  · exact fun h => h.2.1
  · intro h
    obtain ⟨f, hf, hext⟩ := hM.2 i hin h
    exact ⟨hin, h, f, hf, hext, rfl⟩

/-- Some clause of the refutation has measure between `s` and `2s-2`. -/
theorem mid {n : Nat} (R : Refutation (PHP n)) (M : List (Nat × Nat)) {s : Nat} (hs : 2 ≤ s)
    (hbot : s ≤ mu n M []) : ∃ C ∈ R.steps, s ≤ mu n M C ∧ mu n M C ≤ 2 * s - 2 := by
  have key : ∀ k (hk : k < R.steps.length), s ≤ mu n M R.steps[k] →
      ∃ C ∈ R.steps, s ≤ mu n M C ∧ mu n M C ≤ 2 * s - 2 := by
    intro k
    induction k using Nat.strongRecOn with
    | _ k ih =>
      intro hk hsk
      rcases R.derived k hk with hax | ⟨a, b, ha, hb, hres⟩
      · have := mu_axiom (M := M) hax; omega
      · by_cases hA : s ≤ mu n M (R.steps[a]'(Nat.lt_trans ha hk))
        · exact ih a ha _ hA
        · by_cases hB : s ≤ mu n M (R.steps[b]'(Nat.lt_trans hb hk))
          · exact ih b hb _ hB
          · have := mu_sub (n := n) (M := M) hres
            exact ⟨_, List.getElem_mem hk, hsk, by omega⟩
  obtain ⟨k, hk, hke⟩ := List.mem_iff_getElem.mp R.empty_mem
  exact key k hk (by rw [hke]; exact hbot)

/-! ## Medium clauses are wide -/

/-- `v = (p, h)` occurs in the monotone translation of `C`: `x_{p,h} ∈ C` or `¬x_{k,h} ∈ C`, `k ≠ p`. -/
def InV (C : Clause (Nat × Nat)) (v : Nat × Nat) : Prop :=
  ⟨v, true⟩ ∈ C ∨ ∃ k, k ≠ v.1 ∧ ⟨(k, v.2), false⟩ ∈ C

def grid (n : Nat) : List (Nat × Nat) :=
  (List.range (n + 1)).flatMap fun p => (List.range n).map fun h => (p, h)

/-- Number of free variables in the monotone translation of `C`. -/
noncomputable def vsize (n : Nat) (M : List (Nat × Nat)) (C : Clause (Nat × Nat)) : Nat :=
  (grid n).countP fun v => decide (FreeP M v.1 ∧ FreeH M v.2 ∧ InV C v)

theorem swap {n : Nat} {M : List (Nat × Nat)} {C : Clause (Nat × Nat)} {i j : Nat} {f : Nat → Nat}
    (hM : Good n M) (hf : Crit n i f) (hext : Ext M f) (hC : C.eval (val n i f) = false)
    (hi : i ≤ n) (hfi : FreeP M i) (hj : j ≤ n) (hfj : FreeP M j)
    (hnj : ¬ Fals n M C j) (hij : j ≠ i) : InV C (i, f j) ∧ FreeH M (f j) ∧ f j < n := by
  have hfjn : f j < n := hf.lt j hj hij
  refine ⟨?_, ?_, hfjn⟩
  · let g : Nat → Nat := fun q => if q = i then f j else f q
    have hg : Crit n j g := by
      refine ⟨?_, ?_, ?_⟩
      · intro q hq hqj
        simp only [g]; split
        · exact hfjn
        · exact hf.lt q hq (by assumption)
      · intro q₁ q₂ hq₁ hq₂ hq₁j hq₂j e
        simp only [g] at e
        by_cases h1 : q₁ = i <;> by_cases h2 : q₂ = i <;> simp only [h1, h2, ite_true, ite_false] at e
        · omega
        · have := hf.inj j q₂ hj hq₂ hij h2 e; omega
        · have := hf.inj q₁ j hq₁ hj h1 hij e; omega
        · exact hf.inj q₁ q₂ hq₁ hq₂ h1 h2 e
      · intro h' hh'
        obtain ⟨q, hq, hqi, hqh⟩ := hf.surj h' hh'
        by_cases hqj : q = j
        · subst hqj
          exact ⟨i, hi, Ne.symm hij, by simp [g, hqh]⟩
        · exact ⟨q, hq, hqj, by simp [g, hqi, hqh]⟩
    have hgext : Ext M g := by
      intro e he
      have : e.1 ≠ i := hfi e he
      simp [g, this, hext e he]
    have hCg : C.eval (val n j g) = true := by
      apply Classical.byContradiction; intro hne
      exact hnj ⟨hj, hfj, g, hg, hgext, by simpa using hne⟩
    unfold Clause.eval at hCg
    obtain ⟨l, hl, hlv⟩ := List.any_eq_true.mp hCg
    have hlf := (eval_false_iff.mp hC) l hl
    obtain ⟨⟨p, h'⟩, b⟩ := l
    by_cases hpi : p = i
    · subst hpi
      cases b
      · simp [Lit.eval, val] at hlf
      · simp [Lit.eval, val, g] at hlv
        left; rw [hlv.2.2]; exact hl
    · by_cases hpj : p = j
      · subst hpj
        cases b
        · simp [Lit.eval, val, hpi] at hlf
          right; refine ⟨p, hpi, ?_⟩; rw [← hlf.2] at hl; exact hl
        · simp [Lit.eval, val, g] at hlv
      · cases b <;> simp [Lit.eval, val, g, hpi, hpj] at hlv hlf <;> omega
  · intro e he hej
    have h1 := hM.1 e he
    have h2 : f e.1 = f j := (hext e he).trans hej
    have := hf.inj e.1 j h1.1 hj (hfi e he) hij h2
    exact hfj e he this

theorem vsize_eq (n : Nat) (M : List (Nat × Nat)) (C : Clause (Nat × Nat)) :
    vsize n M C = ((List.range (n + 1)).map fun p =>
      (List.range n).countP fun h => decide (FreeP M p ∧ FreeH M h ∧ InV C (p, h))).sum := by
  unfold vsize grid
  rw [List.countP_flatMap]
  congr 1
  apply List.map_congr_left
  intro p _
  simp only [Function.comp, List.countP_map]
  rfl

/-- A clause of measure `μ` has at least `μ * (free - μ)` free monotone variables. -/
theorem vsize_ge {n : Nat} {M : List (Nat × Nat)} (hM : Good n M) (C : Clause (Nat × Nat)) :
    mu n M C * (freeCount n M - mu n M C) ≤ vsize n M C := by
  rw [vsize_eq]
  apply countP_mul_le_sum
  intro i _ hFi
  simp only [decide_eq_true_eq] at hFi
  obtain ⟨hi, hfi, f, hf, hext, hC⟩ := hFi
  let J := (List.range (n + 1)).filter fun j => decide (FreeP M j ∧ ¬ Fals n M C j)
  have hJlen : J.length = freeCount n M - mu n M C := by
    have h1 := countP_split (List.range (n + 1)) (fun j => decide (FreeP M j))
      (fun j => decide (Fals n M C j))
    have h2 : (List.range (n + 1)).countP (fun j => decide (FreeP M j) && decide (Fals n M C j))
        = mu n M C := by
      apply List.countP_congr; intro x _
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨fun h => h.2, fun h => ⟨h.2.1, h⟩⟩
    have h3 : J.length = (List.range (n + 1)).countP
        (fun j => decide (FreeP M j) && !decide (Fals n M C j)) := by
      simp only [J, ← List.countP_eq_length_filter]
      apply List.countP_congr; intro x _
      simp
    unfold freeCount; omega
  rw [← hJlen]
  apply length_le_countP_of_inj J (List.range n) _ f (nodup_filter _ List.nodup_range)
  · intro j hj
    simp only [J, List.mem_filter, List.mem_range, decide_eq_true_eq] at hj
    have hji : j ≠ i := by
      intro e; subst e; exact hj.2.2 ⟨hi, hfi, f, hf, hext, hC⟩
    obtain ⟨h1, h2, h3⟩ := swap hM hf hext hC hi hfi (by omega) hj.2.1 hj.2.2 hji
    exact ⟨List.mem_range.mpr h3, by simp only [decide_eq_true_eq]; exact ⟨hfi, h2, h1⟩⟩
  · intro a ha b hb e
    simp only [J, List.mem_filter, List.mem_range, decide_eq_true_eq] at ha hb
    have hai : a ≠ i := by
      intro e; subst e; exact ha.2.2 ⟨hi, hfi, f, hf, hext, hC⟩
    have hbi : b ≠ i := by
      intro e; subst e; exact hb.2.2 ⟨hi, hfi, f, hf, hext, hC⟩
    exact hf.inj a b (by omega) (by omega) hai hbi e

/-! ## Restriction by a matching edge kills clauses containing it -/

theorem kill {n : Nat} {M : List (Nat × Nat)} {C : Clause (Nat × Nat)} {a h i : Nat}
    (ha : a ≤ n) (hv : InV C (a, h)) : ¬ Fals n ((a, h) :: M) C i := by
  rintro ⟨hi, hfi, f, hf, hext, hC⟩
  have hia : a ≠ i := hfi (a, h) List.mem_cons_self
  have hfa : f a = h := hext (a, h) List.mem_cons_self
  rcases hv with hpos | ⟨k, hka, hneg⟩
  · have := (eval_false_iff.mp hC) _ hpos
    simp [Lit.eval, val, ha, hia, hfa] at this
  · have := (eval_false_iff.mp hC) _ hneg
    simp [Lit.eval, val] at this
    have := hf.inj k a this.1 ha this.2.1 hia (this.2.2.trans hfa.symm)
    exact hka this

/-- A clause is big at `M`: alive (falsified by some critical matching extending `M`) and with at
least `K` free monotone variables. -/
def Big (n K : Nat) (M : List (Nat × Nat)) (C : Clause (Nat × Nat)) : Prop :=
  (∃ i, Fals n M C i) ∧ K ≤ vsize n M C

noncomputable def bigCount {n : Nat} (R : Refutation (PHP n)) (K : Nat) (M : List (Nat × Nat)) :
    Nat :=
  R.steps.countP fun C => decide (Big n K M C)

theorem big_mono {n K : Nat} {M : List (Nat × Nat)} {C : Clause (Nat × Nat)} {a h : Nat}
    (ha : a ≤ n) (hb : Big n K ((a, h) :: M) C) : Big n K M C ∧ ¬ InV C (a, h) := by
  obtain ⟨⟨i, hFi⟩, hK⟩ := hb
  refine ⟨⟨⟨i, ?_⟩, ?_⟩, fun hv => kill ha hv hFi⟩
  · obtain ⟨hi, hfi, f, hf, hext, hC⟩ := hFi
    exact ⟨hi, fun e he => hfi e (List.mem_cons_of_mem _ he), f, hf,
      fun e he => hext e (List.mem_cons_of_mem _ he), hC⟩
  · refine Nat.le_trans hK (List.countP_mono_left ?_)
    intro v _ hv
    simp only [decide_eq_true_eq] at hv ⊢
    exact ⟨fun e he => hv.1 e (List.mem_cons_of_mem _ he),
      fun e he => hv.2.1 e (List.mem_cons_of_mem _ he), hv.2.2⟩

theorem length_grid (n : Nat) : (grid n).length = (n + 1) * n := by
  unfold grid
  rw [List.length_flatMap]
  simp only [List.length_map, List.length_range]
  rw [List.map_const', List.length_range]
  generalize n + 1 = m
  induction m with
  | zero => simp
  | succ m ih => simp [List.replicate_succ, ih, Nat.succ_mul]; omega

/-- Averaging: some free variable occurs in at least a `1/r` fraction of the big clauses. -/
theorem averaging {n K r : Nat} (R : Refutation (PHP n)) (M : List (Nat × Nat))
    (hK : 1 ≤ K) (hr : 1 ≤ r) (hrK : (n + 1) * n ≤ r * K) (hS : 1 ≤ bigCount R K M) :
    ∃ a h, a ≤ n ∧ h < n ∧ FreeP M a ∧ FreeH M h ∧
      bigCount R K M ≤ r * R.steps.countP (fun C => decide (Big n K M C ∧ InV C (a, h))) := by
  let cnt : Nat × Nat → Nat := fun v =>
    R.steps.countP fun C => decide (Big n K M C ∧ (FreeP M v.1 ∧ FreeH M v.2 ∧ InV C v))
  have hsum : bigCount R K M * K ≤ ((grid n).map cnt).sum := by
    have := double_count (grid n) R.steps
      (fun v C => decide (Big n K M C ∧ (FreeP M v.1 ∧ FreeH M v.2 ∧ InV C v)))
    simp only [cnt]; rw [this]
    apply countP_mul_le_sum
    intro C _ hB
    simp only [decide_eq_true_eq] at hB
    refine Nat.le_trans hB.2 (List.countP_mono_left ?_)
    intro v _ hv
    simp only [decide_eq_true_eq] at hv ⊢
    exact ⟨hB, hv⟩
  have hex : ∃ v ∈ grid n, bigCount R K M ≤ r * cnt v := by
    apply Classical.byContradiction
    intro hne
    have hall : ∀ v ∈ grid n, r * cnt v ≤ bigCount R K M - 1 := by
      intro v hv
      have : ¬ bigCount R K M ≤ r * cnt v := fun h => hne ⟨v, hv, h⟩
      omega
    have h1 := sum_le_length_mul (grid n) (fun v => r * cnt v) _ hall
    rw [sum_map_mul, length_grid] at h1
    have h2 : r * (bigCount R K M * K) ≤ r * ((grid n).map cnt).sum := Nat.mul_le_mul_left r hsum
    have h3 : (n + 1) * n * (bigCount R K M - 1) ≤ r * K * (bigCount R K M - 1) :=
      Nat.mul_le_mul_right _ hrK
    have h4 : r * (bigCount R K M * K) = r * K * bigCount R K M := by
      rw [Nat.mul_comm (bigCount R K M) K, Nat.mul_assoc]
    have h5 : 1 ≤ r * K := Nat.mul_le_mul hr hK
    generalize r * K = X at *
    generalize ((grid n).map cnt).sum = Sm at *
    generalize (n + 1) * n = G at *
    generalize bigCount R K M = S at *
    simp only [Nat.mul_sub_one] at h3 h1
    have h6 : X ≤ X * S := Nat.le_mul_of_pos_right X hS
    omega
  obtain ⟨⟨a, h⟩, hv, hle⟩ := hex
  have hpos : 0 < cnt (a, h) := by
    have : 0 < r * cnt (a, h) := by omega
    exact Nat.pos_of_mul_pos_left this
  obtain ⟨C, _, hC⟩ := List.countP_pos_iff.mp hpos
  simp only [decide_eq_true_eq] at hC
  have hgrid : a ≤ n ∧ h < n := by
    unfold grid at hv
    simp only [List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq] at hv
    obtain ⟨p, hp, h', hh', rfl, rfl⟩ := hv
    omega
  refine ⟨a, h, hgrid.1, hgrid.2, hC.2.1, hC.2.2.1, ?_⟩
  refine Nat.le_trans hle (Nat.mul_le_mul_left r (Nat.le_of_eq (List.countP_congr ?_)))
  intro C' _
  simp only [decide_eq_true_eq]
  exact ⟨fun x => ⟨x.1, x.2.2.2⟩, fun x => ⟨x.1, hC.2.1, hC.2.2.1, x.2⟩⟩

/-- One greedy step: the number of big clauses drops by a factor `(r-1)/r`. -/
theorem step {n K r : Nat} (R : Refutation (PHP n)) {M : List (Nat × Nat)} (hM : Good n M)
    (hK : 1 ≤ K) (hr : 1 ≤ r) (hrK : (n + 1) * n ≤ r * K) (hS : 1 ≤ bigCount R K M) :
    ∃ a h, Good n ((a, h) :: M) ∧ r * bigCount R K ((a, h) :: M) ≤ (r - 1) * bigCount R K M := by
  obtain ⟨a, h, ha, hh, hfa, hfh, hle⟩ := averaging R M hK hr hrK hS
  refine ⟨a, h, good_cons hM ha hh hfa hfh, ?_⟩
  have hsplit := countP_split R.steps (fun C => decide (Big n K M C)) (fun C => decide (InV C (a, h)))
  have hk : R.steps.countP (fun C => decide (Big n K M C ∧ InV C (a, h))) =
      R.steps.countP (fun C => decide (Big n K M C) && decide (InV C (a, h))) := by
    apply List.countP_congr; intro x _; simp
  have hnew : bigCount R K ((a, h) :: M) ≤
      R.steps.countP (fun C => decide (Big n K M C) && !decide (InV C (a, h))) := by
    apply List.countP_mono_left
    intro C _ hC
    simp only [decide_eq_true_eq] at hC
    have := big_mono ha hC
    simp [this.1, this.2]
  unfold bigCount at *
  generalize R.steps.countP (fun C => decide (Big n K M C) && decide (InV C (a, h))) = Y at *
  generalize R.steps.countP (fun C => decide (Big n K M C) && !decide (InV C (a, h))) = Z at *
  generalize R.steps.countP (fun C => decide (Big n K ((a, h) :: M) C)) = W at *
  generalize R.steps.countP (fun C => decide (Big n K M C)) = X at *
  have e1 : r * W ≤ r * Z := Nat.mul_le_mul_left r hnew
  have e2 : r * X = r * Y + r * Z := by rw [hsplit, Nat.mul_add]
  rw [Nat.sub_one_mul]
  omega

/-- At every stage `|M| ≤ T` some clause of the refutation is big. -/
theorem big_exists {n T s K : Nat} (R : Refutation (PHP n)) {M : List (Nat × Nat)} (hM : Good n M)
    (hlen : M.length ≤ T) (hs : 2 ≤ s) (hsT : s ≤ n + 1 - T)
    (hK : K ≤ s * (n + 1 - T - (2 * s - 2))) : 1 ≤ bigCount R K M := by
  have hfree := freeCount_ge n M
  have hbot : s ≤ mu n M [] := by rw [mu_empty hM]; omega
  obtain ⟨C, hC, h1, h2⟩ := mid R M hs hbot
  have hw := vsize_ge hM C
  have hle := mu_le_free n M C
  have hmul : s * (n + 1 - T - (2 * s - 2)) ≤ mu n M C * (freeCount n M - mu n M C) :=
    Nat.mul_le_mul h1 (by omega)
  have halive : ∃ i, Fals n M C i := by
    have : 0 < mu n M C := by omega
    obtain ⟨i, _, hi⟩ := List.countP_pos_iff.mp this
    exact ⟨i, by simpa using hi⟩
  apply List.countP_pos_iff.mpr
  exact ⟨C, hC, by simp only [decide_eq_true_eq]; exact ⟨halive, by omega⟩⟩

theorem iterate {n T s K r : Nat} (R : Refutation (PHP n)) (hs : 2 ≤ s) (hsT : s ≤ n + 1 - T)
    (hKs : K ≤ s * (n + 1 - T - (2 * s - 2))) (hK : 1 ≤ K) (hr : 1 ≤ r)
    (hrK : (n + 1) * n ≤ r * K) :
    ∀ t, t ≤ T → ∃ M, Good n M ∧ M.length = t ∧
      r ^ t * bigCount R K M ≤ (r - 1) ^ t * bigCount R K [] := by
  intro t
  induction t with
  | zero => intro _; exact ⟨[], good_nil n, rfl, by simp⟩
  | succ t ih =>
    intro ht
    obtain ⟨M, hM, hlen, hineq⟩ := ih (by omega)
    have hS := big_exists R hM (by omega) hs hsT hKs
    obtain ⟨a, h, hM', hstep⟩ := step R hM hK hr hrK hS
    refine ⟨(a, h) :: M, hM', by simp [hlen], ?_⟩
    calc r ^ (t + 1) * bigCount R K ((a, h) :: M)
        = r ^ t * (r * bigCount R K ((a, h) :: M)) := by rw [Nat.pow_succ, Nat.mul_assoc]
      _ ≤ r ^ t * ((r - 1) * bigCount R K M) := Nat.mul_le_mul_left _ hstep
      _ = (r - 1) * (r ^ t * bigCount R K M) := by
          rw [← Nat.mul_assoc, Nat.mul_comm (r ^ t) (r - 1), Nat.mul_assoc]
      _ ≤ (r - 1) * ((r - 1) ^ t * bigCount R K []) := Nat.mul_le_mul_left _ hineq
      _ = (r - 1) ^ (t + 1) * bigCount R K [] := by rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm (r - 1)]

/-- Haken's bound, parametric form. -/
theorem haken_param {n T s K r : Nat} (R : Refutation (PHP n)) (hs : 2 ≤ s) (hsT : s ≤ n + 1 - T)
    (hKs : K ≤ s * (n + 1 - T - (2 * s - 2))) (hK : 1 ≤ K) (hr : 1 ≤ r)
    (hrK : (n + 1) * n ≤ r * K) : r ^ T ≤ (r - 1) ^ T * R.steps.length := by
  obtain ⟨M, hM, hlen, hineq⟩ := iterate R hs hsT hKs hK hr hrK T (Nat.le_refl T)
  have h1 := big_exists R hM (by omega) hs hsT hKs
  have h2 : bigCount R K [] ≤ R.steps.length := List.countP_le_length
  calc r ^ T = r ^ T * 1 := (Nat.mul_one _).symm
    _ ≤ r ^ T * bigCount R K M := Nat.mul_le_mul_left _ h1
    _ ≤ (r - 1) ^ T * bigCount R K [] := hineq
    _ ≤ (r - 1) ^ T * R.steps.length := Nat.mul_le_mul_left _ h2

/-- **Haken's theorem** (exponential resolution lower bound for the pigeonhole principle):
for every `n`, every resolution refutation of `PHP n` (`n+1` pigeons, `n` holes) has at least
`(72/71)^(4⌊n/12⌋)` clauses. -/
theorem haken (n : Nat) (R : Refutation (PHP n)) :
    72 ^ (4 * (n / 12)) ≤ 71 ^ (4 * (n / 12)) * R.steps.length := by
  by_cases hk : n / 12 = 0
  · rw [hk]
    have : 0 < R.steps.length := List.length_pos_of_mem R.empty_mem
    simp; omega
  · have k1 : 1 ≤ n / 12 := by omega
    have hn1 : n / 12 * 12 ≤ n := Nat.div_mul_le_self n 12
    have hn2 : n < (n / 12 + 1) * 12 := by omega
    generalize n / 12 = k at *
    have hKs : 8 * (k * k) ≤ 2 * k * (n + 1 - 4 * k - (2 * (2 * k) - 2)) := by
      have : 4 * k ≤ n + 1 - 4 * k - (2 * (2 * k) - 2) := by omega
      have := Nat.mul_le_mul_left (2 * k) this
      calc 8 * (k * k) = 2 * k * (4 * k) := by grind
        _ ≤ _ := this
    have hrK : (n + 1) * n ≤ 72 * (8 * (k * k)) := by
      have a1 : n + 1 ≤ 2 * k * 12 := by omega
      have a2 : n ≤ 2 * k * 12 := by omega
      have := Nat.mul_le_mul a1 a2
      calc (n + 1) * n ≤ 2 * k * 12 * (2 * k * 12) := this
        _ = 72 * (8 * (k * k)) := by grind
    have := haken_param (T := 4 * k) (s := 2 * k) (K := 8 * (k * k)) (r := 72) R
      (by omega) (by omega) hKs (by have := Nat.mul_le_mul k1 k1; omega) (by omega) hrK
    simpa using this

end Programme.«20261024-1110-proof-complexity».Haken

#print axioms Programme.«20261024-1110-proof-complexity».Haken.haken
