import Programme.«20261104-1627-proof-complexity».HoleProjection

namespace Programme.«20261104-1627-proof-complexity».HoleGenerators
open Programme.«20261104-1627-proof-complexity».MatchingLabels Programme.«20261104-1627-proof-complexity».HoleProjection

theorem cols_succ (n : Nat) (N : Matching) :
    cols (n+1) N = cols n N ++ (if freeCol N n then [n] else []) := by
  simp only [cols, List.range_succ, List.filter_append]
  cases h : freeCol N n <;> simp [h]

theorem appended_last_block (n b : Nat) (N : Matching) (r : Bool) (a : Nat) :
    holeBlock n ⟨ordered (N ++ [(b,n)]),r,a⟩ = 3 := by
  have hu : usesHole n ⟨ordered (N ++ [(b,n)]),r,a⟩ = true := by
    simp only [usesHole, List.any_eq_true]
    refine ⟨(b,n), ?_, by simp⟩
    simp [ordered]
  simp [holeBlock, hu]

theorem splitHole_append (n b : Nat) (u v : Vector) :
    splitHole n b (u ++ v) = splitHole n b u ++ splitHole n b v := by
  exact List.filter_append _ _

/-- Extra rr terms all contain the new hole in their base. -/
theorem rr_first_block (n : Nat) (N : Matching) (a b : Nat) :
    splitHole n 1 (rr (n+1) N a b) = splitHole n 1 (rr n N a b) := by
  unfold rr
  rw [cols_succ]
  simp only [List.map_append, splitHole_append]
  have extra (c : Int) (j r : Nat) :
      splitHole n 1 ((if freeCol N n then [n] else []).map
        fun i => (c, (⟨ordered (N ++ [(j,i)]),true,r⟩ : Label))) = [] := by
    cases h : freeCol N n <;> simp [splitHole, appended_last_block, h]
  rw [extra, extra]
  simp


theorem rc_first_block (m n : Nat) (N : Matching) (i j : Nat) :
    splitHole n 1 (rc m (n+1) N i j) = splitHole n 1 (rc m n N i j) := by
  unfold rc
  rw [cols_succ, List.filter_append, List.map_append]
  simp only [splitHole_append]
  have extra : splitHole n 1
      (((if freeCol N n then [n] else []).filter (· != j)).map
        fun b => (-1, (⟨ordered (N ++ [(i,b)]),false,j⟩ : Label))) = [] := by
    cases h : freeCol N n <;> by_cases hj : n = j <;>
      simp [splitHole, appended_last_block, h, hj]
  rw [extra]
  simp

private theorem cols_add_last {n : Nat} {N : Matching} {j : Nat}
    (hj : j ∈ cols n N) : j ∈ cols (n+1) N := by
  simp only [cols, List.mem_filter, List.mem_range] at hj ⊢
  exact ⟨by omega, hj.2⟩

theorem rr_lift_mem {m n d : Nat} {N : Matching} {a b : Nat}
    (hd : 2 ≤ d) (hN : N ∈ matchings m n (d-2))
    (ha : a ∈ rows m N) (hb : b ∈ rows m N) (hab : a < b) :
    rr (n+1) N a b ∈ syzygies m (n+1) d := by
  simp only [syzygies, show ¬d < 2 by omega, ↓reduceIte,
    List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filter]
  exact Or.inl ⟨N, matching_add_hole N hN,
    Or.inl (Or.inl ⟨a, ha, b, ⟨hb, by simpa using hab⟩, rfl⟩)⟩

theorem cc_lift_mem {m n d : Nat} {N : Matching} {a b : Nat}
    (hd : 2 ≤ d) (hN : N ∈ matchings m n (d-2))
    (ha : a ∈ cols n N) (hb : b ∈ cols n N) (hab : a < b) :
    cc m N a b ∈ syzygies m (n+1) d := by
  simp only [syzygies, show ¬d < 2 by omega, ↓reduceIte,
    List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filter]
  exact Or.inl ⟨N, matching_add_hole N hN,
    Or.inl (Or.inr ⟨a, cols_add_last ha, b,
      ⟨cols_add_last hb, by simpa using hab⟩, rfl⟩)⟩

theorem rc_lift_mem {m n d : Nat} {N : Matching} {i j : Nat}
    (hd : 2 ≤ d) (hN : N ∈ matchings m n (d-2))
    (hi : i ∈ rows m N) (hj : j ∈ cols n N) :
    rc m (n+1) N i j ∈ syzygies m (n+1) d := by
  simp only [syzygies, show ¬d < 2 by omega, ↓reduceIte,
    List.mem_append, List.mem_flatMap, List.mem_map]
  exact Or.inl ⟨N, matching_add_hole N hN,
    Or.inr ⟨i, hi, j, cols_add_last hj, rfl⟩⟩

end Programme.«20261104-1627-proof-complexity».HoleGenerators
#print axioms Programme.«20261104-1627-proof-complexity».HoleGenerators.rr_first_block

#print axioms Programme.«20261104-1627-proof-complexity».HoleGenerators.rc_first_block
#print axioms Programme.«20261104-1627-proof-complexity».HoleGenerators.rr_lift_mem
#print axioms Programme.«20261104-1627-proof-complexity».HoleGenerators.cc_lift_mem
#print axioms Programme.«20261104-1627-proof-complexity».HoleGenerators.rc_lift_mem
