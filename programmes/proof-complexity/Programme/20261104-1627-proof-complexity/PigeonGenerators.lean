import Programme.«20261104-1627-proof-complexity».PigeonProjection

namespace Programme.«20261104-1627-proof-complexity».MatchingLabels

theorem rows_succ (m : Nat) (N : Matching) :
    rows (m+1) N = rows m N ++ (if freeRow N m then [m] else []) := by
  simp only [rows, List.range_succ, List.filter_append]
  cases h : freeRow N m <;> simp [h]

theorem appended_last_block (m b : Nat) (N : Matching) (r : Bool) (a : Nat) :
    pigeonBlock m ⟨ordered (N ++ [(m,b)]),r,a⟩ = 3 := by
  have hu : usesPigeon m ⟨ordered (N ++ [(m,b)]),r,a⟩ = true := by
    simp only [usesPigeon, List.any_eq_true]
    refine ⟨(m,b), ?_, by simp⟩
    simp [ordered]
  simp [pigeonBlock, hu]

theorem splitPigeon_append (m b : Nat) (u v : Vector) :
    splitPigeon m b (u ++ v) = splitPigeon m b u ++ splitPigeon m b v := by
  exact List.filter_append _ _

/-- Extra cc terms all contain the new pigeon in their base. -/
theorem cc_first_block (m : Nat) (N : Matching) (a b : Nat) :
    splitPigeon m 1 (cc (m+1) N a b) = splitPigeon m 1 (cc m N a b) := by
  unfold cc
  rw [rows_succ]
  simp only [List.map_append, splitPigeon_append]
  have extra (c : Int) (j r : Nat) :
      splitPigeon m 1 ((if freeRow N m then [m] else []).map
        fun i => (c, (⟨ordered (N ++ [(i,j)]),false,r⟩ : Label))) = [] := by
    cases h : freeRow N m <;> simp [splitPigeon, appended_last_block, h]
  rw [extra, extra]
  simp

/-- Extra rc terms all contain the new pigeon in their base. -/
theorem rc_first_block (m n : Nat) (N : Matching) (i j : Nat) :
    splitPigeon m 1 (rc (m+1) n N i j) = splitPigeon m 1 (rc m n N i j) := by
  unfold rc
  rw [rows_succ, List.filter_append, List.map_append]
  simp only [splitPigeon_append]
  have extra : splitPigeon m 1
      (((if freeRow N m then [m] else []).filter (· != i)).map
        fun a => (1, (⟨ordered (N ++ [(a,j)]),true,i⟩ : Label))) = [] := by
    cases h : freeRow N m <;> by_cases hi : m = i <;>
      simp [splitPigeon, appended_last_block, h, hi]
  rw [extra]
  simp

private theorem rows_add_last {m : Nat} {N : Matching} {i : Nat}
    (hi : i ∈ rows m N) : i ∈ rows (m+1) N := by
  simp only [rows, List.mem_filter, List.mem_range] at hi ⊢
  exact ⟨by omega, hi.2⟩

theorem rr_lift_mem {m n d : Nat} {N : Matching} {a b : Nat}
    (hd : 2 ≤ d) (hN : N ∈ matchings m n (d-2))
    (ha : a ∈ rows m N) (hb : b ∈ rows m N) (hab : a < b) :
    rr n N a b ∈ syzygies (m+1) n d := by
  simp only [syzygies, show ¬d < 2 by omega, ↓reduceIte,
    List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filter]
  exact Or.inl ⟨N, matching_add_last N hN,
    Or.inl (Or.inl ⟨a, rows_add_last ha, b, ⟨rows_add_last hb, by simpa using hab⟩, rfl⟩)⟩

theorem cc_lift_mem {m n d : Nat} {N : Matching} {a b : Nat}
    (hd : 2 ≤ d) (hN : N ∈ matchings m n (d-2))
    (ha : a ∈ cols n N) (hb : b ∈ cols n N) (hab : a < b) :
    cc (m+1) N a b ∈ syzygies (m+1) n d := by
  simp only [syzygies, show ¬d < 2 by omega, ↓reduceIte,
    List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filter]
  exact Or.inl ⟨N, matching_add_last N hN,
    Or.inl (Or.inr ⟨a, ha, b, ⟨hb, by simpa using hab⟩, rfl⟩)⟩

theorem rc_lift_mem {m n d : Nat} {N : Matching} {i j : Nat}
    (hd : 2 ≤ d) (hN : N ∈ matchings m n (d-2))
    (hi : i ∈ rows m N) (hj : j ∈ cols n N) :
    rc (m+1) n N i j ∈ syzygies (m+1) n d := by
  simp only [syzygies, show ¬d < 2 by omega, ↓reduceIte,
    List.mem_append, List.mem_flatMap, List.mem_map]
  exact Or.inl ⟨N, matching_add_last N hN,
    Or.inr ⟨i, rows_add_last hi, j, hj, rfl⟩⟩

/-- The board-dependent ordinary generator families preserve G1. -/
theorem ordinary_first_blocks (m n : Nat) (N : Matching) (a b : Nat) :
    splitPigeon m 1 (cc (m+1) N a b) = splitPigeon m 1 (cc m N a b) ∧
    splitPigeon m 1 (rc (m+1) n N a b) = splitPigeon m 1 (rc m n N a b) :=
  ⟨cc_first_block m N a b, rc_first_block m n N a b⟩

end Programme.«20261104-1627-proof-complexity».MatchingLabels
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.cc_first_block
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.rc_first_block

#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.rr_lift_mem
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.cc_lift_mem
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.rc_lift_mem

#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.ordinary_first_blocks
