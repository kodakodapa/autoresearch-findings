import Programme.«20261104-1627-proof-complexity».HoleRestriction

namespace Programme.«20261104-1627-proof-complexity».MatchingLabels

theorem freeRow_push (h i : Nat) (M : Matching) :
    freeRow (pushMatching h M) i = freeRow M i := by
  simp [freeRow, pushMatching, List.all_map, Function.comp_def]

theorem freeCol_push (h j : Nat) (M : Matching) :
    freeCol (pushMatching h M) (omitHole h j) = freeCol M j := by
  simp only [freeCol, pushMatching, List.all_map]
  congr 1
  funext e
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_apply, bne_iff_ne]
  exact not_congr (omitHole_injective h).eq_iff

theorem rows_push (m h : Nat) (M : Matching) :
    rows m (pushMatching h M) = rows m M := by
  unfold rows
  congr 1
  funext i
  exact freeRow_push h i M

theorem cols_push_mem {n h j : Nat} (M : Matching)
    (hj : j ∈ cols n M) : omitHole h j ∈ cols (n+1) (pushMatching h M) := by
  simp only [cols, List.mem_filter, List.mem_range] at hj ⊢
  exact ⟨omitHole_lt hj.1, by simpa only [freeCol_push] using hj.2⟩

theorem matching_push_mem {m n d : Nat} (h : Nat) (M : Matching)
    (hM : M ∈ matchings m n d) :
    pushMatching h M ∈ matchings m (n+1) d := by
  induction d generalizing M with
  | zero =>
    simp only [matchings, List.mem_singleton] at hM ⊢
    subst M
    rfl
  | succ d ih =>
    simp only [matchings, List.mem_flatMap, List.mem_map] at hM ⊢
    obtain ⟨N, hN, i, hi, j, hj, rfl⟩ := hM
    refine ⟨pushMatching h N, ih N hN, i, ?_, omitHole h j,
      cols_push_mem N hj, ?_⟩
    · rw [List.mem_filter] at hi ⊢
      refine ⟨by rw [rows_push]; exact hi.1, ?_⟩
      simpa [pushMatching, List.all_map, Function.comp_def] using hi.2
    · simp [pushMatching]

def pushLabel (h : Nat) (g : Label) : Label :=
  ⟨pushMatching h g.base, g.isRow,
    if g.isRow then g.mark else omitHole h g.mark⟩

theorem label_push_mem {m n d : Nat} (h : Nat) (g : Label)
    (hg : g ∈ labels m n d) : pushLabel h g ∈ labels m (n+1) d := by
  by_cases hd : d = 0
  · simp [labels, hd] at hg
  · simp only [labels, hd, ↓reduceIte, List.mem_flatMap,
      List.mem_append, List.mem_map] at hg ⊢
    obtain ⟨M, hM, hg | hg⟩ := hg
    · obtain ⟨i, hi, rfl⟩ := hg
      refine ⟨pushMatching h M, matching_push_mem h M hM, Or.inl ?_⟩
      exact ⟨i, by rw [rows_push]; exact hi, rfl⟩
    · obtain ⟨j, hj, rfl⟩ := hg
      refine ⟨pushMatching h M, matching_push_mem h M hM, Or.inr ?_⟩
      exact ⟨omitHole h j, cols_push_mem M hj, rfl⟩

def zeroExtendCoordinates (h : Nat) (v : Matching → Int) : Matching → Int :=
  fun M => if M.all (fun e => e.2 != h) then v (pullMatching h M) else 0

theorem zeroExtend_push (h : Nat) (v : Matching → Int) (M : Matching) :
    zeroExtendCoordinates h v (pushMatching h M) = v M := by
  have ha : (pushMatching h M).all (fun e => e.2 != h) = true := by
    rw [List.all_eq_true]
    intro e he
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
    simpa only [bne_iff_ne] using omitHole_ne h a.2
  simp only [zeroExtendCoordinates, ha, ↓reduceIte, pull_push]

/-- Exact integer adjunction on the enumerated omission image. The passage
from this image sum to the whole large board still needs image coverage. -/
theorem pairing_omission_image (m n d h : Nat) (x z : Matching → Int) :
    ((matchings m n d).map (fun M => restrictCoordinates h x M * z M)).sum =
    (((matchings m n d).map (pushMatching h)).map
      (fun M => x M * zeroExtendCoordinates h z M)).sum := by
  simp only [List.map_map, Function.comp_def, zeroExtend_push,
    restrictCoordinates]

end Programme.«20261104-1627-proof-complexity».MatchingLabels
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.matching_push_mem

#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.label_push_mem

#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.zeroExtend_push
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.pairing_omission_image
