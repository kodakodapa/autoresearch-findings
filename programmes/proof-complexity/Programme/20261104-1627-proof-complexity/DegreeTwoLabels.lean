import Programme.«20261104-1627-proof-complexity».MatchingLabels

namespace Programme.«20261104-1627-proof-complexity».MatchingLabels

def edgeRowLabel (a b i : Nat) : Label := ⟨[(a,b)], true, i⟩
def edgeColLabel (a b j : Nat) : Label := ⟨[(a,b)], false, j⟩

theorem matchings_one (m n : Nat) : matchings m n 1 =
    (List.range m).flatMap (fun a => (List.range n).map (fun b => [(a,b)])) := by
  have hc : freeCol [] = fun _ => true := rfl
  have hf (L : List Nat) : L.filter (fun _ => true) = L := List.filter_eq_self.mpr (by simp)
  simp [matchings, rows, cols, freeRow, hc, hf]

theorem matching_one_cases {m n : Nat} {M : Matching}
    (h : M ∈ matchings m n 1) :
    ∃ a < m, ∃ b < n, M = [(a,b)] := by
  rw [matchings_one] at h
  obtain ⟨a, ha, hh⟩ := List.mem_flatMap.mp h
  obtain ⟨b, hb, he⟩ := List.mem_map.mp hh
  exact ⟨a, List.mem_range.mp ha, b, List.mem_range.mp hb, he.symm⟩

theorem label_two_cases {m n : Nat} {g : Label}
    (h : g ∈ labels m n 2) :
    (∃ a < m, ∃ b < n, ∃ i < m, a ≠ i ∧ g = edgeRowLabel a b i) ∨
    (∃ a < m, ∃ b < n, ∃ j < n, b ≠ j ∧ g = edgeColLabel a b j) := by
  change g ∈ (matchings m n 1).flatMap (fun M =>
    (rows m M).map (fun i => ⟨M,true,i⟩) ++
    (cols n M).map (fun j => ⟨M,false,j⟩)) at h
  obtain ⟨M, hM, hg⟩ := List.mem_flatMap.mp h
  obtain ⟨a, ha, b, hb, rfl⟩ := matching_one_cases hM
  rcases List.mem_append.mp hg with hr | hc
  · obtain ⟨i, hi, he⟩ := List.mem_map.mp hr
    have hh := List.mem_filter.mp hi
    have hn : a ≠ i := by simpa [freeRow] using hh.2
    exact Or.inl ⟨a,ha,b,hb,i,List.mem_range.mp hh.1,hn,he.symm⟩
  · obtain ⟨j, hj, he⟩ := List.mem_map.mp hc
    have hh := List.mem_filter.mp hj
    have hn : b ≠ j := by simpa [freeCol] using hh.2
    exact Or.inr ⟨a,ha,b,hb,j,List.mem_range.mp hh.1,hn,he.symm⟩

 theorem edgeRowLabel_mem {m n a b i : Nat}
    (ha : a < m) (hb : b < n) (hi : i < m) (hne : a ≠ i) :
    edgeRowLabel a b i ∈ labels m n 2 := by
  apply List.mem_flatMap.mpr
  refine ⟨[(a,b)], ?_, ?_⟩
  · rw [matchings_one]
    exact List.mem_flatMap.mpr ⟨a,List.mem_range.mpr ha,
      List.mem_map.mpr ⟨b,List.mem_range.mpr hb,rfl⟩⟩
  · apply List.mem_append_left
    apply List.mem_map.mpr
    refine ⟨i, ?_, rfl⟩
    exact List.mem_filter.mpr ⟨List.mem_range.mpr hi, by simp [freeRow, hne]⟩

 theorem edgeColLabel_mem {m n a b j : Nat}
    (ha : a < m) (hb : b < n) (hj : j < n) (hne : b ≠ j) :
    edgeColLabel a b j ∈ labels m n 2 := by
  apply List.mem_flatMap.mpr
  refine ⟨[(a,b)], ?_, ?_⟩
  · rw [matchings_one]
    exact List.mem_flatMap.mpr ⟨a,List.mem_range.mpr ha,
      List.mem_map.mpr ⟨b,List.mem_range.mpr hb,rfl⟩⟩
  · apply List.mem_append_right
    apply List.mem_map.mpr
    refine ⟨j, ?_, rfl⟩
    exact List.mem_filter.mpr ⟨List.mem_range.mpr hj, by simp [freeCol, hne]⟩

 theorem label_two_iff {m n : Nat} {g : Label} :
    g ∈ labels m n 2 ↔
    (∃ a < m, ∃ b < n, ∃ i < m, a ≠ i ∧ g = edgeRowLabel a b i) ∨
    (∃ a < m, ∃ b < n, ∃ j < n, b ≠ j ∧ g = edgeColLabel a b j) := by
  constructor
  · exact label_two_cases
  · rintro (⟨a,ha,b,hb,i,hi,hne,rfl⟩ | ⟨a,ha,b,hb,j,hj,hne,rfl⟩)
    · exact edgeRowLabel_mem ha hb hi hne
    · exact edgeColLabel_mem ha hb hj hne

end Programme.«20261104-1627-proof-complexity».MatchingLabels
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.label_two_cases
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.edgeRowLabel_mem
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.edgeColLabel_mem

#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.label_two_iff
