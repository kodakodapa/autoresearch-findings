/-!
# Counting perfect matchings through a partial matching (M4 of P88)

`arr k L`: the arrangements (duplicate-free sequences) of `k` elements of `L`. The perfect
matchings of `K_{n,n}` are `arr n (List.range n)`, `σ` matching `i ↦ σ[i]`.

`count_fitsB`: for an injective partial constraint `c` (index `i < k` ↦ required value in the
duplicate-free `L`), exactly `ff (|L| - #c) (k - #c)` arrangements meet `c`;
`pm_count`: exactly `(n - |P|)!` perfect matchings of `K_{n,n}` contain a partial matching `P`;
`arr_full`: there are `n!` of them.
-/

namespace Programme.«20261025-0805-proof-complexity».PermCount

/-- Arrangements of `k` elements of `L`. -/
def arr : Nat → List Nat → List (List Nat)
  | 0, _ => [[]]
  | k + 1, L => L.flatMap fun a => (arr k (L.erase a)).map (List.cons a)

/-- Falling factorial `a (a-1) ⋯ (a-b+1)`. -/
def ff : Nat → Nat → Nat
  | _, 0 => 1
  | a, b + 1 => a * ff (a - 1) b

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

theorem mem_arr {k : Nat} {L σ : List Nat} (h : σ ∈ arr k L) : ∀ x ∈ σ, x ∈ L := by
  induction k generalizing L σ with
  | zero => simp [arr] at h; subst h; simp
  | succ k ih =>
    simp only [arr, List.mem_flatMap, List.mem_map] at h
    obtain ⟨a, ha, τ, hτ, rfl⟩ := h
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ha
    · exact List.mem_of_mem_erase (ih hτ x hx)

theorem len_filter_flatMap (L : List Nat) (f : Nat → List (List Nat)) (q : List Nat → Bool) :
    ((L.flatMap f).filter q).length = (L.map fun a => ((f a).filter q).length).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [List.flatMap_cons, List.filter_append, ih]

theorem sum_ite (L : List Nat) (p : Nat → Bool) (c : Nat) :
    (L.map fun a => if p a then 0 else c).sum = c * (L.filter fun a => !p a).length := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons, ih, List.filter_cons]
    cases p a <;> simp [Nat.mul_add, Nat.add_comm]

/-! ## Constraints as a partial function `c : index ↦ required value` -/

def okB : Option Nat → Nat → Bool
  | none, _ => true
  | some j, a => a == j

/-- `σ` satisfies every constraint `c i = some j` (`σ[i] = j`) at its positions. -/
def fitsB (c : Nat → Option Nat) : List Nat → Bool
  | [] => true
  | a :: τ => okB (c 0) a && fitsB (fun i => c (i + 1)) τ

/-- Number of constrained indices below `k`. -/
def cnt (c : Nat → Option Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => (if c 0 = none then 0 else 1) + cnt (fun i => c (i + 1)) k

/-- Required values at indices below `k`. -/
def vals (c : Nat → Option Nat) : Nat → List Nat
  | 0 => []
  | k + 1 => (match c 0 with | none => [] | some j => [j]) ++ vals (fun i => c (i + 1)) k

theorem cnt_le (c : Nat → Option Nat) (k : Nat) : cnt c k ≤ k := by
  induction k generalizing c with
  | zero => simp [cnt]
  | succ k ih => have := ih (fun i => c (i + 1)); simp only [cnt]; split <;> omega

theorem vals_length (c : Nat → Option Nat) (k : Nat) : (vals c k).length = cnt c k := by
  induction k generalizing c with
  | zero => simp [vals, cnt]
  | succ k ih =>
    simp only [vals, cnt, List.length_append, ih]
    cases h : c 0 <;> simp

theorem mem_vals (c : Nat → Option Nat) (k a : Nat) :
    a ∈ vals c k ↔ ∃ i, i < k ∧ c i = some a := by
  induction k generalizing c with
  | zero => simp [vals]
  | succ k ih =>
    simp only [vals, List.mem_append, ih]
    constructor
    · rintro (h | ⟨i, hi, hc⟩)
      · refine ⟨0, by omega, ?_⟩
        cases h0 : c 0 <;> simp_all
      · exact ⟨i + 1, by omega, hc⟩
    · rintro ⟨i, hi, hc⟩
      cases i with
      | zero => left; simp [hc]
      | succ i => right; exact ⟨i, by omega, hc⟩

theorem vals_nodup (c : Nat → Option Nat) (k : Nat)
    (hinj : ∀ i i' j, c i = some j → c i' = some j → i = i') : (vals c k).Nodup := by
  induction k generalizing c with
  | zero => simp [vals]
  | succ k ih =>
    simp only [vals]
    have ht := ih (fun i => c (i + 1)) (fun i i' j h h' => by have := hinj _ _ _ h h'; omega)
    cases h0 : c 0 with
    | none => simpa using ht
    | some j =>
      simp only [List.singleton_append, List.nodup_cons]
      refine ⟨fun hm => ?_, ht⟩
      obtain ⟨i, -, hc⟩ := (mem_vals _ _ _).1 hm
      have := hinj _ _ _ hc h0; omega

theorem arr_length {k : Nat} {L σ : List Nat} (h : σ ∈ arr k L) : σ.length = k := by
  induction k generalizing L σ with
  | zero => simp [arr] at h; subst h; rfl
  | succ k ih =>
    simp only [arr, List.mem_flatMap, List.mem_map] at h
    obtain ⟨a, -, τ, hτ, rfl⟩ := h
    simp [ih hτ]

theorem fitsB_mem (c : Nat → Option Nat) (τ : List Nat) (h : fitsB c τ = true) (i j : Nat)
    (hc : c i = some j) (hi : i < τ.length) : j ∈ τ := by
  induction τ generalizing c i with
  | nil => simp at hi
  | cons a τ ih =>
    simp only [fitsB, Bool.and_eq_true] at h
    cases i with
    | zero => simp only [hc, okB, beq_iff_eq] at h; simp [h.1]
    | succ i =>
      exact List.mem_cons_of_mem _ (ih _ h.2 i hc (by simp at hi; omega))

theorem len_filter_map_cons (l : List (List Nat)) (a : Nat) (q : List Nat → Bool) :
    ((l.map (List.cons a)).filter q).length = (l.filter fun τ => q (a :: τ)).length := by
  induction l with
  | nil => simp
  | cons τ l ih => simp only [List.map_cons, List.filter_cons]; split <;> simp [ih]

theorem sum_single (L : List Nat) (hL : L.Nodup) (j : Nat) (hj : j ∈ L) (g : Nat → Nat) :
    (L.map fun a => if a = j then g a else 0).sum = g j := by
  induction L with
  | nil => simp at hj
  | cons b L ih =>
    simp only [List.nodup_cons] at hL
    simp only [List.map_cons, List.sum_cons]
    by_cases hb : b = j
    · subst hb
      have : (L.map fun a => if a = b then g a else 0).sum = 0 := by
        rw [List.sum_eq_zero_iff_forall_eq_nat]; intro x hx
        simp only [List.mem_map] at hx; obtain ⟨a, ha, rfl⟩ := hx
        have : a ≠ b := fun h => hL.1 (h ▸ ha)
        simp [this]
      simp [this]
    · simp only [hb, if_false, Nat.zero_add]
      exact ih hL.2 (by simp at hj; rcases hj with h | h; exact absurd h.symm hb; exact h)

theorem len_filter_split (L : List Nat) (p : Nat → Bool) :
    L.length = (L.filter p).length + (L.filter fun a => !p a).length := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.filter_cons, List.length_cons]; cases p a <;> simp <;> omega

theorem filter_not_mem_length (L R : List Nat) (hL : L.Nodup) (hR : R.Nodup) (hRL : ∀ x ∈ R, x ∈ L) :
    (L.filter fun a => !decide (a ∈ R)).length = L.length - R.length := by
  have h1 := len_filter_split L (fun a => decide (a ∈ R))
  have hp : (L.filter fun a => decide (a ∈ R)).Perm R := by
    rw [List.perm_ext_iff_of_nodup (hL.filter _) hR]
    intro x; simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨hRL x h, h⟩⟩
  rw [hp.length_eq] at h1
  omega

/-- Arrangements of `k` elements of `L` meeting the constraints `c`. -/
theorem count_fitsB (k : Nat) : ∀ (L : List Nat) (c : Nat → Option Nat), L.Nodup →
    (∀ i i' j, c i = some j → c i' = some j → i = i') → (∀ i j, c i = some j → j ∈ L) →
    (∀ i, k ≤ i → c i = none) →
    ((arr k L).filter (fitsB c)).length = ff (L.length - cnt c k) (k - cnt c k) := by
  induction k with
  | zero =>
    intro L c _ _ _ _
    simp [arr, fitsB, cnt, ff, List.filter_cons]
  | succ k ih =>
    intro L c hL hinj hval hdom
    let c' : Nat → Option Nat := fun i => c (i + 1)
    have hinj' : ∀ i i' j, c' i = some j → c' i' = some j → i = i' :=
      fun i i' j h h' => by have := hinj _ _ _ h h'; omega
    have hdom' : ∀ i, k ≤ i → c' i = none := fun i hi => hdom (i + 1) (by omega)
    have hck := cnt_le c' k
    simp only [arr]
    rw [len_filter_flatMap]
    have hc : ∀ a, (List.filter (fitsB c) (List.map (List.cons a) (arr k (L.erase a)))).length =
        ((arr k (L.erase a)).filter fun τ => okB (c 0) a && fitsB c' τ).length :=
      fun a => len_filter_map_cons _ a _
    rw [List.map_congr_left (fun a _ => hc a)]
    cases h0 : c 0 with
    | some j0 =>
      have hj0 : j0 ∈ L := hval 0 j0 h0
      have heq : ∀ a, ((arr k (L.erase a)).filter fun τ => okB (some j0) a && fitsB c' τ).length
          = if a = j0 then ((arr k (L.erase j0)).filter (fitsB c')).length else 0 := by
        intro a
        by_cases ha : a = j0
        · subst ha; simp [okB]
        · simp [okB, ha]
      simp only [heq]
      rw [sum_single L hL j0 hj0 (fun _ => ((arr k (L.erase j0)).filter (fitsB c')).length)]
      have hval' : ∀ i j, c' i = some j → j ∈ L.erase j0 := by
        intro i j hc
        have hne : j ≠ j0 := fun h => by subst h; have := hinj _ _ _ hc h0; omega
        exact (List.mem_erase_of_ne hne).2 (hval _ _ hc)
      rw [ih (L.erase j0) c' (hL.erase j0) hinj' hval' hdom', List.length_erase_of_mem hj0]
      simp only [cnt, h0, reduceCtorEq, if_false]
      have hm : 1 ≤ L.length := List.length_pos_of_mem hj0
      have e1 : L.length - 1 - cnt c' k = L.length - (1 + cnt c' k) := by omega
      have e2 : k - cnt c' k = k + 1 - (1 + cnt c' k) := by omega
      rw [e1, e2]
    | none =>
      let R := vals c' k
      have heq : ∀ a, a ∈ L → ((arr k (L.erase a)).filter fun τ => okB none a && fitsB c' τ).length
          = if decide (a ∈ R) then 0 else ff (L.length - 1 - cnt c' k) (k - cnt c' k) := by
        intro a ha
        simp only [okB, Bool.true_and]
        by_cases hR : a ∈ R
        · simp only [hR, decide_true, if_true]
          obtain ⟨i, hi, hc⟩ := (mem_vals _ _ _).1 hR
          rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
          intro τ hτ hf
          have hm := fitsB_mem c' τ hf i a hc (by rw [arr_length hτ]; exact hi)
          exact (List.Nodup.not_mem_erase hL) (mem_arr hτ a hm)
        · simp only [hR, decide_false]
          have hval' : ∀ i j, c' i = some j → j ∈ L.erase a := by
            intro i j hc
            have hne : j ≠ a := by
              intro h; subst h
              have hik : i < k := by
                rcases Nat.lt_or_ge i k with h | h
                · exact h
                · rw [hdom' i h] at hc; cases hc
              exact hR ((mem_vals _ _ _).2 ⟨i, hik, hc⟩)
            exact (List.mem_erase_of_ne hne).2 (hval _ _ hc)
          rw [ih (L.erase a) c' (hL.erase a) hinj' hval' hdom', List.length_erase_of_mem ha]
          rfl
      rw [List.map_congr_left heq, sum_ite]
      have hRL : ∀ x ∈ R, x ∈ L := by
        intro x hx; obtain ⟨i, -, hc⟩ := (mem_vals _ _ _).1 hx; exact hval _ _ hc
      rw [filter_not_mem_length L R hL (vals_nodup c' k hinj') hRL, vals_length]
      simp only [cnt, h0, if_true, Nat.zero_add]
      have e2 : k + 1 - cnt c' k = (k - cnt c' k) + 1 := by omega
      rw [e2, ff, Nat.mul_comm]
      show _ = (L.length - cnt c' k) * ff (L.length - cnt c' k - 1) _
      rw [Nat.sub_right_comm]

/-- Perfect matchings of `K_{n,n}` (as arrangements of `range n`) meeting `c`: `(n - #c)!`. -/
theorem pm_count_fn (n : Nat) (c : Nat → Option Nat)
    (hinj : ∀ i i' j, c i = some j → c i' = some j → i = i') (hval : ∀ i j, c i = some j → j < n)
    (hdom : ∀ i, n ≤ i → c i = none) :
    ((arr n (List.range n)).filter (fitsB c)).length = ff (n - cnt c n) (n - cnt c n) := by
  rw [count_fitsB n (List.range n) c List.nodup_range hinj
    (fun i j h => List.mem_range.2 (hval i j h)) hdom, List.length_range]

theorem ff_self (a : Nat) : ff a a = fact a := by
  induction a with
  | zero => rfl
  | succ a ih => simp [ff, fact, ih]

/-! ## Partial matchings as edge lists -/

/-- The constraint function of an edge list. -/
def cP : List (Nat × Nat) → Nat → Option Nat
  | [], _ => none
  | e :: P, i => if i = e.1 then some e.2 else cP P i

theorem cP_iff (P : List (Nat × Nat)) (hl : (P.map (·.1)).Nodup) (i j : Nat) :
    cP P i = some j ↔ (i, j) ∈ P := by
  induction P with
  | nil => simp [cP]
  | cons e P ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hl
    simp only [cP, List.mem_cons]
    by_cases hi : i = e.1
    · subst hi
      simp only [if_true, Option.some.injEq]
      constructor
      · rintro rfl; left; rfl
      · rintro (h | h)
        · rw [← h]
        · exact absurd ⟨(e.1, j), h, rfl⟩ hl.1
    · simp only [hi, if_false, ih hl.2]
      constructor
      · exact Or.inr
      · rintro (h | h)
        · rw [← h] at hi; exact absurd rfl hi
        · exact h

theorem fitsB_iff (c : Nat → Option Nat) (σ : List Nat) :
    fitsB c σ = true ↔ ∀ i j, i < σ.length → c i = some j → σ[i]? = some j := by
  induction σ generalizing c with
  | nil => simp [fitsB]
  | cons a τ ih =>
    simp only [fitsB, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h0, h⟩ i j hi hc
      cases i with
      | zero => rw [hc] at h0; simp only [okB, beq_iff_eq] at h0; simp [h0]
      | succ i => simp only [List.getElem?_cons_succ]; exact h i j (by simp at hi; omega) hc
    · intro h
      refine ⟨?_, fun i j hi hc => by simpa using h (i + 1) j (by simp; omega) hc⟩
      cases hc : c 0 with
      | none => rfl
      | some j => have := h 0 j (by simp) hc; simp at this; simp [okB, this]

theorem nodup_map_inj {α β : Type} [DecidableEq α] (f : α → β) (P : List α) (h : (P.map f).Nodup) {x y : α}
    (hx : x ∈ P) (hy : y ∈ P) (hxy : f x = f y) : x = y := by
  induction P with
  | nil => simp at hx
  | cons a P ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at h
    simp only [List.mem_cons] at hx hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · rfl
    · exact absurd ⟨y, hy, hxy.symm⟩ h.1
    · exact absurd ⟨x, hx, hxy⟩ h.1
    · exact ih h.2 hx hy

/-- `σ` contains every edge `(i, j)` of `P`. -/
def fitsP (P : List (Nat × Nat)) (σ : List Nat) : Bool := P.all fun e => σ[e.1]? == some e.2

/-- **M4.** For a partial matching `P` of `K_{n,n}` (lefts distinct and `< n`, rights distinct
and `< n`), exactly `(n - |P|)!` of the `n!` perfect matchings `arr n (range n)` contain `P`. -/
theorem pm_count (n : Nat) (P : List (Nat × Nat)) (hl : (P.map (·.1)).Nodup)
    (hr : (P.map (·.2)).Nodup) (hP : ∀ e ∈ P, e.1 < n ∧ e.2 < n) :
    ((arr n (List.range n)).filter (fitsP P)).length = fact (n - P.length) := by
  have hc := cP_iff P hl
  have hinj : ∀ i i' j, cP P i = some j → cP P i' = some j → i = i' := by
    intro i i' j h h'
    rw [hc] at h h'
    have := nodup_map_inj (·.2) P hr h h' rfl
    simp only [Prod.mk.injEq] at this; exact this.1
  have hdom : ∀ i, n ≤ i → cP P i = none := by
    intro i hi
    cases h : cP P i with
    | none => rfl
    | some j => have := (hP _ ((hc i j).1 h)).1; simp at this; omega
  have hcnt : cnt (cP P) n = P.length := by
    rw [← vals_length]
    have hp : (vals (cP P) n).Perm (P.map (·.2)) := by
      rw [List.perm_ext_iff_of_nodup (vals_nodup _ _ hinj) hr]
      intro j
      rw [mem_vals]
      simp only [hc, List.mem_map]
      constructor
      · rintro ⟨i, -, h⟩; exact ⟨(i, j), h, rfl⟩
      · rintro ⟨⟨i, j'⟩, h, rfl⟩; exact ⟨i, (hP _ h).1, h⟩
    rw [hp.length_eq, List.length_map]
  have hf : (arr n (List.range n)).filter (fitsP P) = (arr n (List.range n)).filter (fitsB (cP P)) := by
    apply List.filter_congr
    intro σ hσ
    have hlen := arr_length hσ
    rw [Bool.eq_iff_iff, fitsB_iff, fitsP, List.all_eq_true]
    constructor
    · intro h i j _ hij
      have := h _ ((hc i j).1 hij); simpa using this
    · intro h e he
      have := h e.1 e.2 (by rw [hlen]; exact (hP e he).1) ((hc _ _).2 he)
      simp [this]
  rw [hf, pm_count_fn n (cP P) hinj (fun i j h => (hP _ ((hc i j).1 h)).2) hdom, hcnt, ff_self]

theorem arr_full (n : Nat) : (arr n (List.range n)).length = fact n := by
  have := pm_count n [] (by simp) (by simp) (by simp)
  have h : (arr n (List.range n)).filter (fitsP []) = arr n (List.range n) :=
    List.filter_eq_self.2 (fun _ _ => rfl)
  rw [h] at this; simpa using this

end Programme.«20261025-0805-proof-complexity».PermCount

#print axioms Programme.«20261025-0805-proof-complexity».PermCount.pm_count
#print axioms Programme.«20261025-0805-proof-complexity».PermCount.arr_full
