import Programme.«20261104-1627-proof-complexity».MatchingReduction

namespace Programme.«20261104-1627-proof-complexity».BoardCollisions
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261104-1627-proof-complexity».MatchingReduction

theorem collision_mem {n k i i' j : Nat} (hi : i < n+k)
    (hi' : i' < n+k) (hj : j < n) (h : i < i') :
    prod2 (var n i j) (var n i' j) ∈ ontoFPHP n k := by
  simp only [ontoFPHP, List.mem_append]
  apply Or.inl; apply Or.inr
  simp only [collAx, List.mem_flatMap, List.mem_range]
  refine ⟨j, hj, i, hi, ?_⟩
  simp only [List.mem_filterMap]
  exact ⟨i', List.mem_range.mpr hi', by simp [h]⟩

theorem functional_mem {n k i j j' : Nat} (hi : i < n+k)
    (hj : j < n) (hj' : j' < n) (h : j < j') :
    prod2 (var n i j) (var n i j') ∈ ontoFPHP n k := by
  simp only [ontoFPHP, List.mem_append]
  apply Or.inr
  simp only [funcAx, List.mem_flatMap, List.mem_range]
  refine ⟨i, hi, j, hj, ?_⟩
  simp only [List.mem_filterMap]
  exact ⟨j', List.mem_range.mpr hj', by simp [h]⟩

/-- Distinct safe board variables cannot decode to the same pigeon or hole. -/
theorem safe_coordinates {n k : Nat} {s : List Nat}
    (hs : Safe (ontoFPHP n k) s) {x y : Nat}
    (hx : x ∈ s) (hy : y ∈ s) (hxb : x < (n+k)*n)
    (hyb : y < (n+k)*n) (hne : x ≠ y) :
    x / n ≠ y / n ∧ x % n ≠ y % n := by
  have hn : 0 < n := by
    cases n with
    | zero => simp at hxb
    | succ n => omega
  have hxq : x / n < n+k := (Nat.div_lt_iff_lt_mul hn).mpr hxb
  have hyq : y / n < n+k := (Nat.div_lt_iff_lt_mul hn).mpr hyb
  have hxr := Nat.mod_lt x hn
  have hyr := Nat.mod_lt y hn
  have ex : var n (x/n) (x%n) = x := by
    unfold var
    simpa [Nat.mul_comm] using Nat.div_add_mod x n
  have ey : var n (y/n) (y%n) = y := by
    unfold var
    simpa [Nat.mul_comm] using Nat.div_add_mod y n
  constructor
  · intro heq
    have hrem : x % n ≠ y % n := by
      intro h
      apply hne
      rw [← ex, ← ey, heq, h]
    rcases Nat.lt_or_gt_of_ne hrem with h | h
    · have hm := functional_mem hxq hxr hyr h
      rw [← heq] at ey
      rw [ex, ey] at hm
      exact hs x hx y hy hm
    · have hm := functional_mem hyq hyr hxr h
      rw [heq] at ex
      rw [ey, ex] at hm
      exact hs y hy x hx hm
  · intro heq
    have hquo : x / n ≠ y / n := by
      intro h
      apply hne
      rw [← ex, ← ey, heq, h]
    rcases Nat.lt_or_gt_of_ne hquo with h | h
    · have hm := collision_mem hxq hyq hxr h
      rw [heq] at hm ex
      rw [ex, ey] at hm
      exact hs x hx y hy hm
    · have hm := collision_mem hyq hxq hyr h
      rw [← heq] at hm ey
      rw [ey, ex] at hm
      exact hs y hy x hx hm

end Programme.«20261104-1627-proof-complexity».BoardCollisions
#print axioms Programme.«20261104-1627-proof-complexity».BoardCollisions.safe_coordinates
