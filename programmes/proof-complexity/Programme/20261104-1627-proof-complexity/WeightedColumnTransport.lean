import Programme.«20261104-1627-proof-complexity».WeightedRowTransport
import Programme.«20261104-1627-proof-complexity».ColumnMultiplicity

namespace Programme.«20261104-1627-proof-complexity».WeightedColumnTransport
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261025-0459-proof-complexity».OntoLucas (bin)
open Programme.«20261104-1627-proof-complexity».BinomialTails Programme.«20261104-1627-proof-complexity».WeightedTailSums

private theorem all_perm {α : Type} {L K : List α} (h : L.Perm K) (P : α → Bool) :
    L.all P = K.all P := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true]
  exact ⟨fun hh a ha => hh a (h.mem_iff.mpr ha),
    fun hh a ha => hh a (h.mem_iff.mp ha)⟩

theorem col_extension_weight (n : Nat) (N E : Matching) (i j q : Nat)
    (hj : E.all (fun e => e.2 < j) = true) :
    (bin (((cols n (N ++ ordered (E ++ [(i,j)]))).filter
      (fun b => (ordered (E ++ [(i,j)])).all (fun e => e.2 < b))).length) q : Int) =
    (bin (tailCount (cols n N) j) q : Int) := by
  rw [col_axis]
  have he : (fun b => (ordered (E ++ [(i,j)])).all (fun e => e.2 < b)) =
      (fun b => decide (j < b)) := by
    funext b
    rw [all_perm (show (ordered (E ++ [(i,j)])).Perm (E ++ [(i,j)]) from List.mergeSort_perm _ _)]
    by_cases hjb : j < b
    · have hE : E.all (fun e => e.2 < b) = true := by
        apply List.all_eq_true.mpr
        intro e he
        have := of_decide_eq_true (List.all_eq_true.mp hj e he)
        simp only [decide_eq_true_eq]
        omega
      simp [List.all_append,hjb,hE]
    · simp [List.all_append,hjb]
  rw [he]
  rfl

private theorem bind_congr {α β : Type} (L : List α) (f g : α → List β)
    (h : ∀ a ∈ L, f a = g a) : L.flatMap f = L.flatMap g := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    simp only [List.flatMap_cons]
    rw [h a (by simp), ih (by intro b hb; exact h b (by simp [hb]))]

/-- Weighted maximal-column transport, with the actual sorted output enumeration. -/
theorem weighted_col_enumeration (m n r q : Nat) (N : Matching) :
    ((Programme.«20261104-1627-proof-complexity».AnchoredWeights.compatible m n r N).flatMap fun E =>
      (((cols n (N ++ E)).filter (fun j => E.all (fun e => e.2 < j))).flatMap
        fun j => (rows m (N ++ E)).map fun i =>
          ((bin (tailCount (cols n N) j) q : Int), ordered (E ++ [(i,j)])))).Perm
    ((Programme.«20261104-1627-proof-complexity».AnchoredWeights.compatible m n (r+1) N).map (fun F =>
      ((bin (((cols n (N ++ F)).filter
        (fun j => F.all (fun e => e.2 < j))).length) q : Int), F))) := by
  let weight : Matching → Int × Matching := fun F =>
    ((bin (((cols n (N ++ F)).filter
      (fun j => F.all (fun e => e.2 < j))).length) q : Int), F)
  have hp := (Programme.«20261104-1627-proof-complexity».MatchingLabels.anchored_column_enumeration m n r N).map weight
  try simp only [Programme.«20261104-1627-proof-complexity».TailWitnessBudget.enumeration_eq] at hp
  change ((Programme.«20261104-1627-proof-complexity».MatchingLabels.columnExtensions m n r N).map weight).Perm
    ((Programme.«20261104-1627-proof-complexity».AnchoredWeights.compatible m n (r+1) N).map weight) at hp
  have he : (Programme.«20261104-1627-proof-complexity».MatchingLabels.columnExtensions m n r N).map weight =
      ((Programme.«20261104-1627-proof-complexity».AnchoredWeights.compatible m n r N).flatMap fun E =>
        (((cols n (N ++ E)).filter (fun j => E.all (fun e => e.2 < j))).flatMap
          fun j => (rows m (N ++ E)).map fun i =>
            ((bin (tailCount (cols n N) j) q : Int), ordered (E ++ [(i,j)])))) := by
    unfold Programme.«20261104-1627-proof-complexity».MatchingLabels.columnExtensions
    simp only [Programme.«20261104-1627-proof-complexity».TailWitnessBudget.enumeration_eq, List.map_flatMap]
    apply bind_congr
    intro E hE
    apply bind_congr
    intro j hj
    simp only [List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro i hi
    change (_, _) = (_, _)
    exact congrArg (fun c : Int => (c, ordered (E ++ [(i,j)])))
      (col_extension_weight n N E i j q (List.mem_filter.mp hj).2)
  rw [he] at hp
  exact hp

end Programme.«20261104-1627-proof-complexity».WeightedColumnTransport
#print axioms Programme.«20261104-1627-proof-complexity».WeightedColumnTransport.col_extension_weight

#print axioms Programme.«20261104-1627-proof-complexity».WeightedColumnTransport.weighted_col_enumeration
