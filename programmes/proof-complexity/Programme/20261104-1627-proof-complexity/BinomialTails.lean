import Programme.«20261104-1627-proof-complexity».AnchoredTwo

namespace Programme.«20261104-1627-proof-complexity».BinomialTails
open Programme.«20261025-0459-proof-complexity».OntoLucas (bin)
open Programme.«20261027-0607-proof-complexity».Lucas (bin_succ)

def tailCount (L : List Nat) (i : Nat) : Nat :=
  (L.filter (fun j => i < j)).length

/-- Hockey-stick identity with the actual free-axis tail counts. -/
theorem tail_sum (L : List Nat) (hL : L.Pairwise (· < ·)) (r : Nat) :
    (L.map (fun i => (bin (tailCount L i) r : Int))).sum =
      (bin L.length (r+1) : Int) := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    have hh := List.pairwise_cons.mp hL
    have hf : L.filter (fun j => a < j) = L := List.filter_eq_self.mpr (by
      intro j hj
      simpa using hh.1 j hj)
    have he (j : Nat) (hj : j ∈ L) : tailCount (a::L) j = tailCount L j := by
      have hn : ¬j < a := by have := hh.1 j hj; omega
      simp [tailCount,hn]
    have hm : L.map (fun i => (bin (tailCount (a::L) i) r : Int)) =
        L.map (fun i => (bin (tailCount L i) r : Int)) := by
      apply List.map_congr_left
      intro j hj
      rw [he j hj]
    simp only [List.map_cons, List.sum_cons]
    rw [hm, ih hh.2]
    have hu : tailCount (a::L) a = L.length := by simp [tailCount,hf]
    rw [hu]
    simp only [List.length_cons, bin_succ, Int.natCast_add]

/-- Cutting an increasing axis above a mark preserves the tail of every surviving mark. -/
theorem tailCount_filter (L : List Nat) (a i : Nat) (hai : a < i) :
    tailCount (L.filter (fun j => a < j)) i = tailCount L i := by
  unfold tailCount
  rw [List.filter_filter]
  have hp : (fun j => decide (i < j) && decide (a < j)) =
      (fun j => decide (i < j)) := by
    funext j
    by_cases hij : i < j
    · have haj : a < j := by omega
      simp [hij,haj]
    · simp [hij]
  rw [hp]

/-- The outgoing coefficients from any intermediate maximal mark sum to its incoming one. -/
theorem filtered_tail_sum (L : List Nat) (hL : L.Pairwise (· < ·)) (a r : Nat) :
    ((L.filter (fun i => a < i)).map
      (fun i => (bin (tailCount L i) r : Int))).sum =
      (bin (tailCount L a) (r+1) : Int) := by
  have h := tail_sum (L.filter (fun i => a < i)) (hL.filter _) r
  have hm : (L.filter (fun i => a < i)).map
      (fun i => (bin (tailCount (L.filter (fun j => a < j)) i) r : Int)) =
      (L.filter (fun i => a < i)).map (fun i => (bin (tailCount L i) r : Int)) := by
    apply List.map_congr_left
    intro i hi
    have hai : a < i := by simpa using (List.mem_filter.mp hi).2
    rw [tailCount_filter L a i hai]
  rw [hm] at h
  exact h
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261104-1627-proof-complexity».AnchoredWeights

/-- P396's explicit vector, with all intermediate matching levels included. -/
def witness (m n t : Nat) (N : Matching) : Vector :=
  (List.range (t-1)).flatMap fun r =>
    (compatible m n r N).flatMap fun E =>
      (((rows m (N ++ E)).filter fun i => E.all fun e => e.1 < i).map
        (fun i => ((bin (tailCount (rows m N) i) (t-1-r) : Int),
          (⟨ordered (N ++ E),true,i⟩ : Label)))) ++
      (((cols n (N ++ E)).filter fun j => E.all fun e => e.2 < j).map
        (fun j => (-(bin (tailCount (cols n N) j) (t-1-r) : Int),
          (⟨ordered (N ++ E),false,j⟩ : Label))))

end Programme.«20261104-1627-proof-complexity».BinomialTails
#print axioms Programme.«20261104-1627-proof-complexity».BinomialTails.tail_sum
#print axioms Programme.«20261104-1627-proof-complexity».BinomialTails.filtered_tail_sum
