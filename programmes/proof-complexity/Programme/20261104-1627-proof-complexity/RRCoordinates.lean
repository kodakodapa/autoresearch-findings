import Programme.«20261104-1627-proof-complexity».RowOnlyTwo

namespace Programme.«20261104-1627-proof-complexity».MatchingLabels

theorem rr_empty (n a i : Nat) : rr n [] a i =
    (List.range n).map (fun b => (1, edgeRowLabel i b a)) ++
    (List.range n).map (fun b => (-1, edgeRowLabel a b i)) := by
  have hf : freeCol [] = fun _ => true := rfl
  have hh (L : List Nat) : L.filter (fun _ => true) = L := List.filter_eq_self.mpr (by simp)
  simp [rr, cols, hf, hh, ordered, edgeRowLabel]

theorem vectorCoeff_append (u v : Vector) (g : Label) :
    vectorCoeff (u ++ v) g = vectorCoeff u g + vectorCoeff v g := by
  simp [vectorCoeff, List.filter_append, List.map_append, List.sum_append]

private theorem vc_map_indicator (L : List Nat) (f : Nat → Label)
    (g : Label) (c : Int) :
    vectorCoeff (L.map fun b => (c, f b)) g =
      c * ((L.filter fun b => f b == g).length : Int) := by
  induction L with
  | nil => simp [vectorCoeff]
  | cons b L ih =>
    by_cases h : f b = g <;> simp [vectorCoeff, h] at ih ⊢ <;>
      simp_all [Int.mul_add] <;> omega

private theorem range_count (n b : Nat) :
    ((List.range n).filter (fun x => x == b)).length = if b < n then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih]
    by_cases he : n = b
    · subst b; simp
    · by_cases hb : b < n
      · simp [he, hb, show b < n + 1 by omega]
      · simp [he, hb, show ¬ b < n + 1 by omega]

theorem rr_row_coefficient (n a i x b r : Nat) :
    vectorCoeff (rr n [] a i) (edgeRowLabel x b r) =
      (if x = i ∧ r = a ∧ b < n then 1 else 0) -
      (if x = a ∧ r = i ∧ b < n then 1 else 0) := by
  rw [rr_empty, vectorCoeff_append, vc_map_indicator, vc_map_indicator]
  have he (u v : Nat) :
      (fun j => edgeRowLabel u j v == edgeRowLabel x b r) =
      (fun j => if x = u ∧ r = v then j == b else false) := by
    funext j
    apply Bool.eq_iff_iff.mpr
    by_cases h : x = u ∧ r = v
    · rcases h with ⟨rfl, rfl⟩
      simp [edgeRowLabel]
    · rw [if_neg h]
      simp only [Bool.false_eq_true, iff_false, beq_iff_eq]
      intro hh
      have hh' : (u = x ∧ j = b) ∧ v = r := by
        simpa [edgeRowLabel] using hh
      exact h ⟨hh'.1.1.symm, hh'.2.symm⟩
  rw [he i a, he a i]
  have hf (L : List Nat) : L.filter (fun _ => false) = [] :=
    List.filter_eq_nil_iff.mpr (by simp)
  have hc (P : Prop) [Decidable P] :
      ((List.range n).filter (fun j => if P then j == b else false)).length =
        if P then (if b < n then 1 else 0) else 0 := by
    by_cases h : P
    · simp only [h, ite_true, range_count]
    · simp only [h, ite_false, hf, List.length_nil]
  rw [hc, hc]
  have algebra (P Q B : Prop) [Decidable P] [Decidable Q] [Decidable B] :
      (1 : Int) * (if P then (if B then (1 : Nat) else 0) else 0) +
      (-1 : Int) * (if Q then (if B then (1 : Nat) else 0) else 0) =
      (if P ∧ B then 1 else 0) - (if Q ∧ B then 1 else 0) := by
    by_cases hp : P <;> by_cases hq : Q <;> by_cases hb : B <;>
      simp only [hp,hq,hb,and_true,and_false,ite_true,ite_false] <;> decide
  simpa only [and_assoc] using algebra (x = i ∧ r = a) (x = a ∧ r = i) (b < n)

theorem rr_col_coefficient (n a i x b r : Nat) :
    vectorCoeff (rr n [] a i) (edgeColLabel x b r) = 0 := by
  rw [rr_empty, vectorCoeff_append, vc_map_indicator, vc_map_indicator]
  have he (u v : Nat) :
      (fun j => edgeRowLabel u j v == edgeColLabel x b r) = fun _ => false := by
    funext j
    simp [beq_iff_eq, edgeRowLabel, edgeColLabel]
  rw [he i a, he a i]
  omega

end Programme.«20261104-1627-proof-complexity».MatchingLabels
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.rr_row_coefficient
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.rr_col_coefficient
