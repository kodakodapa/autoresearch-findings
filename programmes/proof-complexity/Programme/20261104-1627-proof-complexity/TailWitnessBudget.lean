import Programme.«20261104-1627-proof-complexity».BinomialTails
import Programme.«20261104-1627-proof-complexity».AnchoredValidity

namespace Programme.«20261104-1627-proof-complexity».TailWitnessBudget
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261104-1627-proof-complexity».AnchoredWeights
open Programme.«20261104-1627-proof-complexity».BinomialTails

/-- The older local enumeration and the canonical enumeration agree exactly. -/
theorem enumeration_eq (m n d : Nat) :
    Programme.«20261104-1627-proof-complexity».MatchingLabels.matchings m n d = matchings m n d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    simp only [Programme.«20261104-1627-proof-complexity».MatchingLabels.matchings, matchings, ih]
    try rfl

theorem union_mem {m n s r : Nat} {N E : Matching}
    (hN : N ∈ matchings m n s) (hE : E ∈ compatible m n r N) :
    ordered (N ++ E) ∈ matchings m n (s+r) := by
  rw [← enumeration_eq] at hN ⊢
  have hh := List.mem_filter.mp hE
  rw [← enumeration_eq] at hh
  exact Programme.«20261104-1627-proof-complexity».MatchingLabels.ordered_union_mem hN hh.1 hh.2

private theorem rows_ordered (m : Nat) (M : Matching) :
    rows m (ordered M) = rows m M := by
  unfold rows
  congr 1
  funext i
  apply Bool.eq_iff_iff.mpr
  simp [freeRow, ordered, List.all_eq_true]

private theorem cols_ordered (n : Nat) (M : Matching) :
    cols n (ordered M) = cols n M := by
  unfold cols
  congr 1
  funext i
  apply Bool.eq_iff_iff.mpr
  simp [freeCol, ordered, List.all_eq_true]

/-- Every term of the all-level tail witness fits the required relation budget. -/
theorem witness_bounded {m n s t : Nat} {N : Matching}
    (hN : N ∈ matchings m n s) :
    ∀ a ∈ witness m n t N, ∃ d, d ≤ s+t-1 ∧ a.2 ∈ labels m n d := by
  intro a ha
  obtain ⟨r,hr,ha⟩ := List.mem_flatMap.mp ha
  obtain ⟨E,hE,ha⟩ := List.mem_flatMap.mp ha
  have hm := union_mem hN hE
  refine ⟨s+r+1, ?_, ?_⟩
  · have := List.mem_range.mp hr
    omega
  · have hl : labels m n (s+r+1) = (matchings m n (s+r)).flatMap (fun M =>
        (rows m M).map (fun i => (⟨M,true,i⟩ : Label)) ++
        (cols n M).map (fun j => (⟨M,false,j⟩ : Label))) := by simp [labels]
    rw [hl]
    apply List.mem_flatMap.mpr
    refine ⟨_,hm,?_⟩
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
      apply List.mem_append_left
      apply List.mem_map.mpr
      exact ⟨i, by rw [rows_ordered]; exact (List.mem_filter.mp hi).1, rfl⟩
    · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ha
      apply List.mem_append_right
      apply List.mem_map.mpr
      exact ⟨j, by rw [cols_ordered]; exact (List.mem_filter.mp hj).1, rfl⟩
end Programme.«20261104-1627-proof-complexity».TailWitnessBudget
#print axioms Programme.«20261104-1627-proof-complexity».TailWitnessBudget.witness_bounded
