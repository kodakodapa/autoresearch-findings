import Programme.«20261024-1110-proof-complexity».BSW
/-!
# Width lower bound for the ordering principle `GT_n` (3-CNF version), core Lean 4

1. `no_der_of_family`: the soundness half of the Atserias–Dalmau characterisation of resolution
   width (JCSS 2008). Let `P S α` say that the assignment `α` is admissible on the variable list
   `S`. Suppose `P` is closed under shrinking `S`, never falsifies an axiom whose variables lie
   in `S`, holds for `S = []`, and extends: when `|S| ≤ W`, any one variable can be added while
   `α` is kept on `S`. Then there is no width-`W` `Der` refutation.
2. `GT3 n`: the ordering principle on the elements `0..n-1`. It has antisymmetry, totality and
   transitivity of `x a b` ("a below b"). The "no minimum" clause of each `j` is split into
   width-3 clauses through the chain variables `y j 0, …, y j n`:
   `y j 0`, `¬y j n`, and `¬y j i ∨ x i j ∨ y j (i+1)` for each `i < n` (`x j j` is omitted).
   Every clause has width `≤ 3`.
3. `gt_no_der`: for `2W + 2 < n` there is no width-`W` refutation. Duplicator keeps a linear order
   (a rank function `L`) and gives every touched element `j` a witness `w j` below it. It answers
   `x a b ↦ L a < L b` and `y j t ↦ t ≤ w j`. A newly touched element gets a fresh, untouched
   element as its witness, and that witness is moved to the bottom of the order.
4. `gt_width`: for `n ≥ 3`, every resolution refutation (`Refutation`, weakening allowed) of
   `GT3 n` has a clause with at least `(n-1)/2` distinct literals.

GT_n has polynomial-size resolution refutations (Bonet–Galesi 2001; Stålmarck 1996), so this is
the negative control for "width alone is not size": the BSW relation (`Work.BSW.bsw_size`)
with `N = Θ(n²)` gives only a constant size bound here.
-/

set_option linter.unusedSectionVars false

namespace Programme.«20261024-1110-proof-complexity».GT3
open Programme.«20261024-1110-proof-complexity».BSW

section Generic
variable {V : Type} [DecidableEq V]

theorem length_filter_le_wd (X : List V) (C : Clause V) (p : V → Bool)
    (hp : ∀ x, p x = true → (⟨x, true⟩ : Lit V) ∈ C ∨ (⟨x, false⟩ : Lit V) ∈ C) :
    (X.filter p).length ≤ wd X C := by
  induction X with
  | nil => simp
  | cons x X ih =>
    have e : wd (x :: X) C = (if (⟨x, true⟩ : Lit V) ∈ C then 1 else 0)
        + (if (⟨x, false⟩ : Lit V) ∈ C then 1 else 0) + wd X C := by
      simp only [wd, lits, List.flatMap_cons, List.cons_append, List.nil_append,
        List.countP_cons]
      simp only [decide_eq_true_eq]; omega
    rw [e, List.filter_cons]
    by_cases h : p x = true
    · rcases hp x h with h1 | h1 <;> simp [h, h1] <;> omega
    · simp [h]; omega

/-- **Atserias–Dalmau (soundness direction).** An extendable family of admissible partial
assignments that never falsifies an axiom rules out width-`W` refutations. -/
theorem no_der_of_family {Ax : Clause V → Prop} {X : List V} {W : Nat}
    (P : List V → (V → Bool) → Prop)
    (hmono : ∀ S S' α, P S α → (∀ v ∈ S', v ∈ S) → P S' α)
    (hext : ∀ S α, P S α → S.length ≤ W → ∀ v, ∃ α', P (v :: S) α' ∧ ∀ u ∈ S, α' u = α u)
    (hax : ∀ S α C, P S α → Ax C → (∀ l ∈ C, l.var ∈ S) → C.eval α = true)
    (h0 : ∃ α, P [] α) : ¬ Der Ax X W [] := by
  have key : ∀ C, Der Ax X W C → ∀ S α, P S α → (∀ l ∈ C, l.var ∈ S) → C.eval α = true := by
    intro C hC
    induction hC with
    | ax hA _ => exact fun S α hP hS => hax S α _ hP hA hS
    | @weak A C _ hAC _ ih =>
      intro S α hP hS
      have := ih S α hP (fun l hl => hS l (hAC l hl))
      unfold Clause.eval at *
      rw [List.any_eq_true] at this ⊢
      obtain ⟨m, hm, hv⟩ := this
      exact ⟨m, hAC m hm, hv⟩
    | @res A B C l _ _ hlA hlB hAC hBC hok ihA ihB =>
      intro S α hP hS
      let S0 := X.filter (fun x => C.any (fun m => decide (m.var = x)))
      have hS0 : ∀ m ∈ C, m.var ∈ S0 := by
        intro m hm
        simp only [S0, List.mem_filter, List.any_eq_true, decide_eq_true_eq]
        exact ⟨hok.1 m hm, m, hm, rfl⟩
      have hP0 : P S0 α := hmono S S0 α hP (by
        intro v hv
        simp only [S0, List.mem_filter, List.any_eq_true, decide_eq_true_eq] at hv
        obtain ⟨_, m, hm, rfl⟩ := hv
        exact hS m hm)
      have hlen : S0.length ≤ W := by
        refine Nat.le_trans (length_filter_le_wd X C _ ?_) hok.2
        intro x hx
        simp only [List.any_eq_true, decide_eq_true_eq] at hx
        obtain ⟨m, hm, rfl⟩ := hx
        cases m with | mk v p => cases p <;> simp_all
      obtain ⟨α', hP', hagree⟩ := hext S0 α hP0 hlen l.var
      -- whichever of `l`, `l.neg` is false under `α'`, its premise yields a literal of `C`
      have finish : ∀ (D : Clause V) (k : Lit V), k.var = l.var → k.eval α' = false →
          (∀ m ∈ D, m ≠ k → m ∈ C) → D.eval α' = true → C.eval α = true := by
        intro D k _ hk hDC hD
        unfold Clause.eval at *
        rw [List.any_eq_true] at hD ⊢
        obtain ⟨m, hm, hv⟩ := hD
        have hne : m ≠ k := by rintro rfl; rw [hk] at hv; exact Bool.false_ne_true hv
        have hmC := hDC m hm hne
        refine ⟨m, hmC, ?_⟩
        have := hagree m.var (hS0 m hmC)
        unfold Lit.eval at *; rw [this] at hv; exact hv
      have varsD : ∀ (D : Clause V) (k : Lit V), k.var = l.var → (∀ m ∈ D, m ≠ k → m ∈ C) →
          ∀ m ∈ D, m.var ∈ l.var :: S0 := by
        intro D k hk hDC m hm
        by_cases e : m = k
        · subst e; rw [hk]; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hS0 m (hDC m hm e))
      cases hl : l.eval α' with
      | false => exact finish A l rfl hl hAC (ihA _ α' hP' (varsD A l rfl hAC))
      | true =>
        have hn : l.neg.eval α' = false := by
          cases l with | mk v p => cases p <;> simp_all [Lit.eval, Lit.neg]
        exact finish B l.neg rfl hn hBC (ihB _ α' hP' (varsD B l.neg rfl hBC))
  intro hD
  obtain ⟨α, hα⟩ := h0
  have := key _ hD [] α hα (by simp)
  simp [Clause.eval] at this

end Generic

/-! ## The ordering principle -/

inductive GV
  | x (a b : Nat)
  | y (j t : Nat)
deriving DecidableEq, Repr

def pl (v : GV) : Lit GV := ⟨v, true⟩
def ng (v : GV) : Lit GV := ⟨v, false⟩

/-- `GT_n` in 3-CNF (Bonet–Galesi-style splitting of the "no minimum" clauses). -/
def GT3 (n : Nat) : CNF GV :=
  ((List.range n).flatMap fun a => (List.range n).flatMap fun b =>
      if a = b then [] else [[ng (.x a b), ng (.x b a)], [pl (.x a b), pl (.x b a)]]) ++
  ((List.range n).flatMap fun a => (List.range n).flatMap fun b => (List.range n).flatMap fun c =>
      if a = b ∨ b = c ∨ a = c then [] else [[ng (.x a b), ng (.x b c), pl (.x a c)]]) ++
  ((List.range n).flatMap fun j => [pl (.y j 0)] :: [ng (.y j n)] :: (List.range n).map fun i =>
      if i = j then [ng (.y j i), pl (.y j (i + 1))]
      else [ng (.y j i), pl (.x i j), pl (.y j (i + 1))])

/-- Elements an assignment to `v` touches. -/
def tv : GV → List Nat
  | .x a b => [a, b]
  | .y j _ => [j]

def touched (S : List GV) : List Nat := S.flatMap tv

theorem length_touched (S : List GV) : (touched S).length ≤ 2 * S.length := by
  induction S with
  | nil => simp [touched]
  | cons v S ih =>
    have h2 : (tv v).length ≤ 2 := by cases v <;> simp [tv]
    simp only [touched] at ih
    simp only [touched, List.flatMap_cons, List.length_append, List.length_cons]
    omega

/-- Duplicator's total assignment: rank function `L`, witness function `w`. -/
def alpha (L w : Nat → Nat) : GV → Bool
  | .x a b => decide (L a < L b)
  | .y j t => decide (t ≤ w j)

/-- Invariant: `L` is injective on `0..n-1`, and every touched element `j < n` has a witness
`w j < n`, `w j ≠ j`, ranked below `j`. -/
def Inv (n : Nat) (T : List Nat) (L w : Nat → Nat) : Prop :=
  (∀ a < n, ∀ b < n, a ≠ b → L a ≠ L b) ∧
  ∀ j ∈ T, j < n → w j < n ∧ w j ≠ j ∧ L (w j) < L j

def Adm (n : Nat) (S : List GV) (α : GV → Bool) : Prop :=
  ∃ L w, α = alpha L w ∧ Inv n (touched S) L w

theorem exists_fresh : ∀ (n : Nat) (l : List Nat), l.length < n → ∃ f < n, f ∉ l := by
  have cover : ∀ n (l : List Nat), (∀ i < n, i ∈ l) → n ≤ l.length := by
    intro n
    induction n with
    | zero => intros; exact Nat.zero_le _
    | succ n ih =>
      intro l hl
      have hn : n ∈ l := hl n (Nat.lt_succ_self n)
      have := ih (l.erase n) (fun i hi => (List.mem_erase_of_ne (by omega)).mpr (hl i (by omega)))
      rw [List.length_erase_of_mem hn] at this
      have : 0 < l.length := List.length_pos_of_mem hn
      omega
  intro n l hl
  apply Classical.byContradiction
  intro h
  have := cover n l (fun i hi => by
    apply Classical.byContradiction; intro hi'; exact h ⟨i, hi, hi'⟩)
  omega

/-- Variables all of whose touched elements are in `T` keep their value. -/
def Agree (T : List Nat) (α α' : GV → Bool) : Prop := ∀ v, (∀ e ∈ tv v, e ∈ T) → α' v = α v

theorem fix_one (n : Nat) (T : List Nat) (L w : Nat → Nat) (hI : Inv n T L w) (c : Nat)
    (hlen : T.length + 1 < n) :
    ∃ L' w', Inv n (c :: T) L' w' ∧ Agree T (alpha L w) (alpha L' w') := by
  by_cases hc : c ∈ T ∨ n ≤ c
  · refine ⟨L, w, ⟨hI.1, ?_⟩, fun _ _ => rfl⟩
    intro j hj hjn
    rcases List.mem_cons.mp hj with rfl | hj
    · rcases hc with hc | hc
      · exact hI.2 j hc hjn
      · omega
    · exact hI.2 j hj hjn
  · have hcT : c ∉ T := fun h => hc (Or.inl h)
    have hcn : c < n := by omega
    obtain ⟨f, hfn, hf⟩ := exists_fresh n (c :: T) (by simp; omega)
    have hfc : f ≠ c := fun h => hf (h ▸ List.mem_cons_self)
    have hfT : f ∉ T := fun h => hf (List.mem_cons_of_mem _ h)
    refine ⟨fun z => if z = f then 0 else L z + 1, fun z => if z = c then f else w z,
      ⟨?_, ?_⟩, ?_⟩
    · intro a ha b hb hab
      have := hI.1 a ha b hb hab
      by_cases e1 : a = f <;> by_cases e2 : b = f <;> simp [e1, e2] <;> omega
    · intro j hj hjn
      rcases List.mem_cons.mp hj with rfl | hj
      · simp [hfn, hfc, Ne.symm hfc]
      · have hjc : j ≠ c := fun h => hcT (h ▸ hj)
        have hjf : j ≠ f := fun h => hfT (h ▸ hj)
        obtain ⟨h1, h2, h3⟩ := hI.2 j hj hjn
        refine ⟨by simp [hjc, h1], by simp [hjc, h2], ?_⟩
        by_cases e : w j = f <;> simp [hjc, hjf, e] <;> omega
    · intro v hv
      cases v with
      | x a b =>
        have ha : a ≠ f := fun h => hfT (h ▸ hv a (by simp [tv]))
        have hb : b ≠ f := fun h => hfT (h ▸ hv b (by simp [tv]))
        simp [alpha, ha, hb]
      | y j t =>
        have hj : j ≠ c := fun h => hcT (h ▸ hv j (by simp [tv]))
        simp [alpha, hj]

theorem fix_all (n : Nat) : ∀ (es T : List Nat) (L w : Nat → Nat), Inv n T L w →
    T.length + es.length < n →
    ∃ L' w', Inv n (es ++ T) L' w' ∧ Agree T (alpha L w) (alpha L' w') := by
  intro es
  induction es with
  | nil => intro T L w hI _; exact ⟨L, w, hI, fun _ _ => rfl⟩
  | cons e es ih =>
    intro T L w hI hlen
    simp only [List.length_cons] at hlen
    obtain ⟨L1, w1, hI1, hA1⟩ := ih T L w hI (by omega)
    obtain ⟨L2, w2, hI2, hA2⟩ := fix_one n (es ++ T) L1 w1 hI1 e (by simp; omega)
    refine ⟨L2, w2, hI2, fun v hv => ?_⟩
    rw [hA2 v (fun x hx => List.mem_append_right _ (hv x hx)), hA1 v hv]

theorem inv_mono {n : Nat} {T T' : List Nat} {L w : Nat → Nat} (h : Inv n T L w)
    (hs : ∀ j ∈ T', j ∈ T) : Inv n T' L w :=
  ⟨h.1, fun j hj hjn => h.2 j (hs j hj) hjn⟩

theorem mem_touched {S : List GV} {v : GV} {e : Nat} (hv : v ∈ S) (he : e ∈ tv v) :
    e ∈ touched S :=
  List.mem_flatMap.mpr ⟨v, hv, he⟩

/-- No clause of `GT3 n` whose variables are all touched is falsified. -/
theorem adm_ax (n : Nat) (S : List GV) (α : GV → Bool) (C : Clause GV) (hP : Adm n S α)
    (hC : C ∈ GT3 n) (hS : ∀ l ∈ C, l.var ∈ S) : C.eval α = true := by
  obtain ⟨L, w, rfl, hinj, hw⟩ := hP
  have tj : ∀ j t, GV.y j t ∈ S → j < n → w j < n ∧ w j ≠ j ∧ L (w j) < L j :=
    fun j t h hj => hw j (mem_touched h (by simp [tv])) hj
  simp only [GT3, List.mem_append, List.mem_flatMap, List.mem_range] at hC
  rcases hC with (⟨a, ha, b, hb, hC⟩ | ⟨a, ha, b, hb, c, hc, hC⟩) | ⟨j, hj, hC⟩
  · by_cases e : a = b
    · simp [e] at hC
    · have := hinj a ha b hb e
      simp [e] at hC
      rcases hC with rfl | rfl <;>
        simp [Clause.eval, Lit.eval, alpha, pl, ng] <;> omega
  · by_cases e : a = b ∨ b = c ∨ a = c
    · simp [e] at hC
    · simp [e] at hC
      subst hC
      simp [Clause.eval, Lit.eval, alpha, pl, ng]; omega
  · simp only [List.mem_cons, List.mem_map, List.mem_range] at hC
    rcases hC with rfl | rfl | ⟨i, hi, rfl⟩
    · simp [Clause.eval, Lit.eval, alpha, pl]
    · have := tj j n (hS (ng (.y j n)) (by simp)) hj
      simp [Clause.eval, Lit.eval, alpha, ng]; omega
    · by_cases e : i = j
      · subst e
        have := tj i i (hS (ng (.y i i)) (by simp)) hj
        simp [Clause.eval, Lit.eval, alpha, pl, ng]; omega
      · have := tj j i (hS (ng (.y j i)) (by simp [e])) hj
        simp [e, Clause.eval, Lit.eval, alpha, pl, ng]
        by_cases h1 : i ≤ w j
        · by_cases h2 : i + 1 ≤ w j
          · omega
          · have : w j = i := by omega
            subst this; omega
        · omega

/-- **Width lower bound for `GT_n`:** if `2W + 2 < n`, `GT3 n` has no width-`W` resolution
refutation (any variable list `X`). -/
theorem gt_no_der (n W : Nat) (h : 2 * W + 2 < n) (X : List GV) : ¬ Der (· ∈ GT3 n) X W [] := by
  apply no_der_of_family (Adm n)
  · intro S S' α ⟨L, w, hα, hI⟩ hs
    refine ⟨L, w, hα, inv_mono hI ?_⟩
    intro j hj
    obtain ⟨v, hv, hjv⟩ := List.mem_flatMap.mp hj
    exact mem_touched (hs v hv) hjv
  · intro S α ⟨L, w, hα, hI⟩ hlen v
    have hT := length_touched S
    have htv : (tv v).length ≤ 2 := by cases v <;> simp [tv]
    obtain ⟨L', w', hI', hA⟩ := fix_all n (tv v) (touched S) L w hI (by omega)
    refine ⟨alpha L' w', ⟨L', w', rfl, ?_⟩, ?_⟩
    · simpa [touched, List.flatMap_cons] using hI'
    · intro u hu
      rw [hα]; exact hA u (fun e he => mem_touched hu he)
  · intro S α C hP hC hS; exact adm_ax n S α C hP hC hS
  · exact ⟨alpha id (fun _ => 0), id, fun _ => 0, rfl, fun a _ b _ hab => hab, by simp [touched]⟩

/-! ## Statement for `Refutation`s -/

/-- Duplicate-free list of the variables of a CNF. -/
def dd {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | a :: l => if a ∈ dd l then dd l else a :: dd l

theorem mem_dd {α : Type} [DecidableEq α] {a : α} : ∀ {l : List α}, a ∈ dd l ↔ a ∈ l
  | [] => by simp [dd]
  | b :: l => by
    have ih := @mem_dd α _ a l
    unfold dd
    by_cases h : b ∈ dd l
    · simp only [h, ite_true, ih, List.mem_cons]
      constructor
      · exact Or.inr
      · rintro (rfl | h'); exact ih.mp h; exact h'
    · simp [h, ih]

theorem nodup_dd {α : Type} [DecidableEq α] : ∀ (l : List α), (dd l).Nodup
  | [] => by simp [dd]
  | b :: l => by
    unfold dd
    by_cases h : b ∈ dd l
    · simp only [h, ite_true]; exact nodup_dd l
    · simp only [h, ite_false]; exact List.nodup_cons.mpr ⟨h, nodup_dd l⟩

def vars {V : Type} [DecidableEq V] (F : CNF V) : List V := dd (F.flatMap fun C => C.map Lit.var)

theorem vars_nodup {V : Type} [DecidableEq V] (F : CNF V) : (vars F).Nodup := nodup_dd _

theorem mem_vars {V : Type} [DecidableEq V] {F : CNF V} : ∀ C ∈ F, ∀ l ∈ C, l.var ∈ vars F := by
  intro C hC l hl
  unfold vars; rw [mem_dd]
  exact List.mem_flatMap.mpr ⟨C, hC, List.mem_map.mpr ⟨l, hl, rfl⟩⟩

/-- A duplicate-free list has at most `C.length` members of `C`. -/
theorem countP_mem_le {V : Type} [DecidableEq V] (L : List (Lit V)) (C : Clause V) (hL : L.Nodup) :
    L.countP (fun l => decide (l ∈ C)) ≤ C.length := by
    induction C generalizing L with
    | nil => simp
    | cons m C ih =>
      have h1 := ih (L.erase m) (hL.erase m)
      have h2 : L.countP (fun l => decide (l ∈ m :: C))
          ≤ (L.erase m).countP (fun l => decide (l ∈ C)) + 1 := by
        by_cases hm : m ∈ L
        · obtain ⟨s, t, rfl, hs⟩ : ∃ s t, L = s ++ m :: t ∧ m ∉ s := by
            obtain ⟨s, t, h⟩ := List.append_of_mem hm
            refine ⟨s, t, h, ?_⟩
            intro hms; subst h
            have := hL; rw [List.nodup_append] at this
            exact this.2.2 m hms m List.mem_cons_self rfl
          rw [List.erase_append_right _ hs, List.erase_cons_head]
          have hst : ∀ l ∈ s ++ t, l ≠ m := by
            intro l hl e; subst e
            rw [List.nodup_append] at hL
            rcases List.mem_append.mp hl with h | h
            · exact hs h
            · exact (List.nodup_cons.mp hL.2.1).1 h
          simp only [List.countP_append, List.countP_cons, List.mem_cons, true_or,
            decide_true, ite_true]
          have e1 : s.countP (fun l => decide (l = m ∨ l ∈ C)) = s.countP (fun l => decide (l ∈ C)) :=
            List.countP_congr (fun l hl => by
              have := hst l (List.mem_append_left _ hl); simp [this])
          have e2 : t.countP (fun l => decide (l = m ∨ l ∈ C)) = t.countP (fun l => decide (l ∈ C)) :=
            List.countP_congr (fun l hl => by
              have := hst l (List.mem_append_right _ hl); simp [this])
          rw [e1, e2]; omega
        · rw [List.erase_of_not_mem hm]
          have : L.countP (fun l => decide (l ∈ m :: C)) = L.countP (fun l => decide (l ∈ C)) :=
            List.countP_congr (fun l hl => by
              have : l ≠ m := fun e => hm (e ▸ hl)
              simp [this])
          omega
      simp only [List.length_cons]; omega

/-- Every clause of `GT3 n` has at most 3 literals over the variables of `GT3 n`
(so `GT3 n` is a 3-CNF in the sense of `Work.BSW.OK`). -/
theorem gt_ok (n : Nat) : ∀ C ∈ GT3 n, OK (vars (GT3 n)) 3 C := by
  intro C hC
  refine ⟨mem_vars C hC, ?_⟩
  have hlen : C.length ≤ 3 := by
    simp only [GT3, List.mem_append, List.mem_flatMap, List.mem_range] at hC
    rcases hC with (⟨a, _, b, _, hC⟩ | ⟨a, _, b, _, c, _, hC⟩) | ⟨j, _, hC⟩
    · by_cases e : a = b <;> simp [e] at hC; rcases hC with rfl | rfl <;> simp
    · by_cases e : a = b ∨ b = c ∨ a = c <;> simp [e] at hC; subst hC; simp
    · simp only [List.mem_cons, List.mem_map, List.mem_range] at hC
      rcases hC with rfl | rfl | ⟨i, _, rfl⟩
      · simp
      · simp
      · by_cases e : i = j <;> simp [e]
  refine Nat.le_trans ?_ hlen
  exact countP_mem_le _ C (nodup_lits (vars_nodup _))

/-- **Width lower bound for `GT_n` (3-CNF), all `n ≥ 3`:** every resolution refutation of
`GT3 n` contains a clause with at least `(n-1)/2` distinct literals. -/
theorem gt_width (n : Nat) (hn : 3 ≤ n) (π : Refutation (GT3 n)) :
    ∃ C ∈ π.steps, (n - 1) / 2 ≤ wd (vars (GT3 n)) C := by
  apply Classical.byContradiction
  intro h
  have hW : ∀ C ∈ π.steps, wd (vars (GT3 n)) C ≤ (n - 3) / 2 := by
    intro C hC
    have : ¬ (n - 1) / 2 ≤ wd (vars (GT3 n)) C := fun h' => h ⟨C, hC, h'⟩
    omega
  exact gt_no_der n ((n - 3) / 2) (by omega) _ (der_of_refutation mem_vars π hW)

/-- The library pieces compose: `gt_no_der` feeds the BSW relation for `GT3 n` (3-CNF over the
duplicate-free `vars (GT3 n)`). With `N = |vars (GT3 n)| = Θ(n²)` and `d, b = O(n)` the bound is
only a constant, as it must be, because `GT3 n` has polynomial-size refutations. -/
theorem gt_bsw (n d b : Nat) (h : 2 * (3 + d + b) + 2 < n) (π : Refutation (GT3 n)) :
    (2 * (vars (GT3 n)).length) ^ b ≤ π.steps.length * (2 * (vars (GT3 n)).length - d) ^ b :=
  bsw_size (vars_nodup _) (gt_ok n) d b (gt_no_der n _ h _) π

end Programme.«20261024-1110-proof-complexity».GT3

#print axioms Programme.«20261024-1110-proof-complexity».GT3.no_der_of_family
#print axioms Programme.«20261024-1110-proof-complexity».GT3.gt_no_der
#print axioms Programme.«20261024-1110-proof-complexity».GT3.gt_width
#print axioms Programme.«20261024-1110-proof-complexity».GT3.gt_bsw
