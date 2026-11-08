import Programme.«20261104-1627-proof-complexity».TailWitnessBudget

namespace Programme.«20261104-1627-proof-complexity».WeightedTailSums
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261025-0459-proof-complexity».OntoLucas (bin)
open Programme.«20261104-1627-proof-complexity».BinomialTails

/-- Strictly exceeding every coordinate of E already guarantees freshness. -/
theorem row_axis (m : Nat) (N E : Matching) :
    (rows m (N ++ E)).filter (fun i => E.all fun e => e.1 < i) =
      (rows m N).filter (fun i => E.all fun e => e.1 < i) := by
  unfold rows
  rw [List.filter_filter, List.filter_filter]
  congr 1
  funext i
  by_cases h : (E.all fun e => e.1 < i) = true
  · have hf : freeRow E i = true := by
      apply List.all_eq_true.mpr
      intro e he
      have hh := of_decide_eq_true (List.all_eq_true.mp h e he)
      simp only [bne_iff_ne]
      omega
    change E.all (fun e => e.1 != i) = true at hf
    simp only [freeRow, List.all_append, h, hf, Bool.and_true]
  · have hh : (E.all fun e => e.1 < i) = false := Bool.eq_false_iff.mpr h
    simp [hh]

theorem col_axis (n : Nat) (N E : Matching) :
    (cols n (N ++ E)).filter (fun j => E.all fun e => e.2 < j) =
      (cols n N).filter (fun j => E.all fun e => e.2 < j) := by
  unfold cols
  rw [List.filter_filter, List.filter_filter]
  congr 1
  funext j
  by_cases h : (E.all fun e => e.2 < j) = true
  · have hf : freeCol E j = true := by
      apply List.all_eq_true.mpr
      intro e he
      have hh := of_decide_eq_true (List.all_eq_true.mp h e he)
      simp only [bne_iff_ne]
      omega
    change E.all (fun e => e.2 != j) = true at hf
    simp only [freeCol, List.all_append, h, hf, Bool.and_true]
  · have hh : (E.all fun e => e.2 < j) = false := Bool.eq_false_iff.mpr h
    simp [hh]

/-- Hockey-stick on an upward-closed subset, retaining original-axis weights. -/
theorem upper_filter_sum (L : List Nat) (hL : L.Pairwise (· < ·))
    (P : Nat → Bool) (hP : ∀ i j, P i = true → i < j → P j = true) (r : Nat) :
    ((L.filter P).map (fun i => (bin (tailCount L i) r : Int))).sum =
      (bin (L.filter P).length (r+1) : Int) := by
  have he (i : Nat) (hi : i ∈ L.filter P) :
      tailCount (L.filter P) i = tailCount L i := by
    unfold tailCount
    rw [List.filter_filter]
    apply congrArg (fun Q : Nat → Bool => (L.filter Q).length)
    funext j
    by_cases hij : i < j
    · have hp := hP i j (List.mem_filter.mp hi).2 hij
      simp [hij,hp]
    · simp [hij]
  have hm : (L.filter P).map (fun i => (bin (tailCount (L.filter P) i) r : Int)) =
      (L.filter P).map (fun i => (bin (tailCount L i) r : Int)) := by
    apply List.map_congr_left
    intro i hi
    rw [he i hi]
  rw [← hm]
  exact tail_sum _ (hL.filter _) r

/-- The actual outgoing row labels sum to the next binomial weight. -/
theorem row_tail_sum (m : Nat) (N E : Matching) (r : Nat) :
    (((rows m (N ++ E)).filter (fun i => E.all fun e => e.1 < i)).map
      (fun i => (bin (tailCount (rows m N) i) r : Int))).sum =
    (bin ((rows m (N ++ E)).filter (fun i => E.all fun e => e.1 < i)).length (r+1) : Int) := by
  rw [row_axis]
  apply upper_filter_sum _ (List.pairwise_lt_range.filter _)
  intro i j hi hij
  apply List.all_eq_true.mpr
  intro e he
  have := of_decide_eq_true (List.all_eq_true.mp hi e he)
  simp only [decide_eq_true_eq]
  omega

theorem col_tail_sum (n : Nat) (N E : Matching) (r : Nat) :
    (((cols n (N ++ E)).filter (fun j => E.all fun e => e.2 < j)).map
      (fun j => (bin (tailCount (cols n N) j) r : Int))).sum =
    (bin ((cols n (N ++ E)).filter (fun j => E.all fun e => e.2 < j)).length (r+1) : Int) := by
  rw [col_axis]
  apply upper_filter_sum _ (List.pairwise_lt_range.filter _)
  intro i j hi hij
  apply List.all_eq_true.mpr
  intro e he
  have := of_decide_eq_true (List.all_eq_true.mp hi e he)
  simp only [decide_eq_true_eq]
  omega

open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261029-1156-proof-complexity».StdPC

def piece (m n q : Nat) (N E : Matching) : Vector :=
  (((rows m (N ++ E)).filter fun i => E.all fun e => e.1 < i).map
    (fun i => ((bin (tailCount (rows m N) i) q : Int),
      (⟨ordered (N ++ E),true,i⟩ : Label)))) ++
  (((cols n (N ++ E)).filter fun j => E.all fun e => e.2 < j).map
    (fun j => (-(bin (tailCount (cols n N) j) q : Int),
      (⟨ordered (N ++ E),false,j⟩ : Label))))

private theorem repeated (L : List Nat) (c : Nat → Int) (v u : List Nat) :
    cf (L.map fun i => (c i,v)) u = if v.Perm u then (L.map c).sum else 0 := by
  induction L with
  | nil => simp [cf]
  | cons i L ih =>
    have hc : cf ((c i,v) :: L.map (fun i => (c i,v))) u =
        (if v.Perm u then c i else 0) + cf (L.map fun i => (c i,v)) u := by
      by_cases h : v.Perm u <;> simp [cf,h]
    simp only [List.map_cons, List.sum_cons, hc, ih]
    split <;> omega

private theorem sum_neg (L : List Int) : (L.map Neg.neg).sum = -L.sum := by
  induction L with
  | nil => rfl
  | cons a L ih => simp only [List.map_cons,List.sum_cons,ih]; omega

/-- Exact rho contribution of one intermediate matching in the all-t witness. -/
theorem piece_rho (m n q : Nat) (N E : Matching) (u : List Nat) :
    coeff (rho n (piece m n q N E)) u =
      if (mono n (N ++ E)).Perm u then
        (bin ((rows m (N ++ E)).filter (fun i => E.all fun e => e.1 < i)).length (q+1) : Int) -
        bin ((cols n (N ++ E)).filter (fun j => E.all fun e => e.2 < j)).length (q+1)
      else 0 := by
  have hp : (mono n (ordered (N ++ E))).Perm (mono n (N ++ E)) :=
    (List.mergeSort_perm (N ++ E) _).map _
  have he : (mono n (ordered (N ++ E))).Perm u ↔ (mono n (N ++ E)).Perm u :=
    ⟨fun h => hp.symm.trans h, fun h => hp.trans h⟩
  simp only [piece,rho,List.map_append,List.map_map,Function.comp_def,coeff,cf_append]
  rw [repeated,repeated]
  simp only [he]
  rw [row_tail_sum]
  have hn := sum_neg
    ((((cols n (N ++ E)).filter fun j => E.all fun e => e.2 < j)).map
      (fun j => (bin (tailCount (cols n N) j) q : Int)))
  simp only [List.map_map,Function.comp_def] at hn
  rw [hn,col_tail_sum]
  by_cases h : (mono n (N ++ E)).Perm u <;> simp [h,Int.sub_eq_add_neg]

def incoming (m n q : Nat) (N E : Matching) : Int :=
  (bin ((rows m (N ++ E)).filter (fun i => E.all fun e => e.1 < i)).length (q+1) : Int) -
  bin ((cols n (N ++ E)).filter (fun j => E.all fun e => e.2 < j)).length (q+1)

def layer (m n r q : Nat) (N : Matching) : Vector :=
  (Programme.«20261104-1627-proof-complexity».AnchoredWeights.compatible m n r N).flatMap (piece m n q N)

def incomingPoly (m n r q : Nat) (N : Matching) : Poly Nat :=
  ⟨(Programme.«20261104-1627-proof-complexity».AnchoredWeights.compatible m n r N).map fun E =>
    (incoming m n q N E, mono n (N ++ E))⟩

/-- Exact rho compression at each intermediate matching level. -/
theorem layer_rho (m n r q : Nat) (N : Matching) (u : List Nat) :
    coeff (rho n (layer m n r q N)) u = coeff (incomingPoly m n r q N) u := by
  unfold layer incomingPoly
  unfold rho coeff
  rw [List.map_flatMap]
  generalize Programme.«20261104-1627-proof-complexity».AnchoredWeights.compatible m n r N = L
  induction L with
  | nil => rfl
  | cons E L ih =>
    simp only [List.flatMap_cons,List.map_cons,cf_append]
    have hh := piece_rho m n q N E u
    change cf ((piece m n q N E).map _) u = _ at hh
    rw [hh,ih]
    have hs (a : Int × List Nat) (T : List (Int × List Nat)) :
        cf (a::T) u = (if a.2.Perm u then a.1 else 0) + cf T u := by
      by_cases h : a.2.Perm u <;> simp [cf,h]
    rw [hs]
    rfl

/-- The bottom rho boundary is exactly the conjectured anchor scalar. -/
theorem bottom_rho {m n s : Nat} {N : Matching}
    (hN : N ∈ matchings m n s) (q : Nat) (u : List Nat) :
    coeff (rho n (layer m n 0 q N)) u =
      if (mono n N).Perm u then
        (bin (m-s) (q+1) : Int) - bin (n-s) (q+1) else 0 := by
  have hlen := Programme.«20261104-1627-proof-complexity».AnchoredRhoOne.free_coordinates_length hN
  have hr : (rows m N).length = m-s := by omega
  have hc : (cols n N).length = n-s := by omega
  have hl : layer m n 0 q N = piece m n q N [] := by
    simp [layer, Programme.«20261104-1627-proof-complexity».AnchoredWeights.compatible, matchings, List.filter_cons, List.all]
  rw [hl,piece_rho]
  simp only [List.append_nil,List.all_nil]
  have fr : (rows m N).filter (fun _ => true) = rows m N :=
    List.filter_eq_self.mpr (by intros; rfl)
  have fc : (cols n N).filter (fun _ => true) = cols n N :=
    List.filter_eq_self.mpr (by intros; rfl)
  rw [fr,fc,hr,hc]

private theorem bin_one (a : Nat) : bin a 1 = a := by
  induction a with
  | zero => rfl
  | succ a ih =>
    rw [Programme.«20261027-0607-proof-complexity».Lucas.bin_succ,
      Programme.«20261025-0459-proof-complexity».OntoLucas.bin_zero, ih]
    omega

/-- The last incoming polynomial is the already certified compressed rho(z). -/
theorem incoming_zero (m n r : Nat) (N : Matching) :
    incomingPoly m n r 0 N = Programme.«20261104-1627-proof-complexity».AnchoredWeights.weighted m n (r+1) N := by
  unfold incomingPoly Programme.«20261104-1627-proof-complexity».AnchoredWeights.weighted
  simp only [Nat.add_sub_cancel]
  congr 1
  apply List.map_congr_left
  intro E _
  simp only [incoming, Programme.«20261104-1627-proof-complexity».AnchoredWeights.weight, Nat.zero_add, bin_one]

end Programme.«20261104-1627-proof-complexity».WeightedTailSums
#print axioms Programme.«20261104-1627-proof-complexity».WeightedTailSums.row_tail_sum
#print axioms Programme.«20261104-1627-proof-complexity».WeightedTailSums.col_tail_sum
#print axioms Programme.«20261104-1627-proof-complexity».TailWitnessBudget.witness_bounded

#print axioms Programme.«20261104-1627-proof-complexity».WeightedTailSums.piece_rho

#print axioms Programme.«20261104-1627-proof-complexity».WeightedTailSums.layer_rho
#print axioms Programme.«20261104-1627-proof-complexity».WeightedTailSums.bottom_rho

#print axioms Programme.«20261104-1627-proof-complexity».WeightedTailSums.incoming_zero
