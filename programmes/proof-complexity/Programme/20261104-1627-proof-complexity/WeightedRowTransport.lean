import Programme.«20261104-1627-proof-complexity».WeightedTailSums
import Programme.«20261104-1627-proof-complexity».AnchoredRowEnumeration

namespace Programme.«20261104-1627-proof-complexity».WeightedRowTransport
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261025-0459-proof-complexity».OntoLucas (bin)
open Programme.«20261104-1627-proof-complexity».BinomialTails Programme.«20261104-1627-proof-complexity».WeightedTailSums

theorem maximal_tail (L : List Nat) (E : Matching) (i : Nat)
    (hi : E.all (fun e => e.1 < i) = true) :
    (L.filter (fun j => (E ++ [(i,0)]).all (fun e => e.1 < j))) =
      L.filter (fun j => i < j) := by
  apply congrArg (fun P : Nat → Bool => L.filter P)
  funext j
  by_cases hij : i < j
  · have hE : E.all (fun e => e.1 < j) = true := by
      apply List.all_eq_true.mpr
      intro e he
      have := of_decide_eq_true (List.all_eq_true.mp hi e he)
      simp only [decide_eq_true_eq]
      omega
    simp [List.all_append,hij,hE]
  · simp [List.all_append,hij]

theorem row_extension_weight (m : Nat) (N E : Matching) (i j q : Nat)
    (hi : E.all (fun e => e.1 < i) = true) :
    (bin (((rows m (N ++ (E ++ [(i,j)]))).filter
      (fun a => (E ++ [(i,j)]).all (fun e => e.1 < a))).length) q : Int) =
    (bin (tailCount (rows m N) i) q : Int) := by
  rw [row_axis]
  have he : (fun a => (E ++ [(i,j)]).all (fun e => e.1 < a)) =
      (fun a => (E ++ [(i,0)]).all (fun e => e.1 < a)) := by
    funext a
    simp [List.all_append]
  rw [he, maximal_tail _ E i hi]
  rfl

private theorem bind_congr {α β : Type} (L : List α) (f g : α → List β)
    (h : ∀ a ∈ L, f a = g a) : L.flatMap f = L.flatMap g := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    simp only [List.flatMap_cons]
    rw [h a (by simp), ih (by intro b hb; exact h b (by simp [hb]))]

/-- The row-max enumeration transports the original-axis binomial coefficient exactly. -/
theorem weighted_row_enumeration (m n r q : Nat) (N : Matching) :
    ((Programme.«20261104-1627-proof-complexity».AnchoredWeights.compatible m n r N).flatMap fun E =>
      (((rows m (N ++ E)).filter (fun i => E.all (fun e => e.1 < i))).flatMap
        fun i => (cols n (N ++ E)).map fun j =>
          ((bin (tailCount (rows m N) i) q : Int), E ++ [(i,j)]))) =
    (Programme.«20261104-1627-proof-complexity».AnchoredWeights.compatible m n (r+1) N).map (fun F =>
      ((bin (((rows m (N ++ F)).filter
        (fun i => F.all (fun e => e.1 < i))).length) q : Int), F)) := by
  have hen := Programme.«20261104-1627-proof-complexity».MatchingLabels.anchored_row_enumeration m n r N
  try simp only [Programme.«20261104-1627-proof-complexity».TailWitnessBudget.enumeration_eq] at hen
  change ((Programme.«20261104-1627-proof-complexity».AnchoredWeights.compatible m n r N).flatMap _) =
    Programme.«20261104-1627-proof-complexity».AnchoredWeights.compatible m n (r+1) N at hen
  rw [← hen, List.map_flatMap]
  apply bind_congr
  intro E hE
  rw [List.map_flatMap]
  apply bind_congr
  intro i hi
  simp only [List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro j hj
  rw [row_extension_weight m N E i j q (List.mem_filter.mp hi).2]

end Programme.«20261104-1627-proof-complexity».WeightedRowTransport
#print axioms Programme.«20261104-1627-proof-complexity».WeightedRowTransport.row_extension_weight
#print axioms Programme.«20261104-1627-proof-complexity».WeightedRowTransport.weighted_row_enumeration
