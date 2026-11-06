import Programme.«20261104-1627-proof-complexity».FilteredLabels

namespace Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261029-1156-proof-complexity».StdPC

/-- The filtered relation-space decomposition, with the homogeneous kernel
contribution written as its negative lower image. Raw W only. -/
theorem filtered_decomposition {p m n D : Nat} (hD : 0 < D)
    (P : Poly Nat) (hP : P.deg < D) :
    W p m n D P ↔ ∃ lo hi : Vector,
      bounded m n (D-1) lo ∧ Kernel p m n D hi ∧
      PEq p P ((relations m n lo).sub (rho n hi)) := by
  constructor
  · intro hW
    rcases filtered_kernel_split hD P hP hW with ⟨lo, hi, hlo, hhi, he⟩
    refine ⟨lo, hi, hlo, hhi, ?_⟩
    intro u
    have hk := hhi.2 u
    have hs := he u
    have hr := relations_coeff m n hi u
    change (p : Int) ∣ coeff P u -
      cf ((relations m n lo).terms ++ negT (rho n hi).terms) u
    rw [cf_append, cf_negT]
    have hz : (p : Int) ∣ coeff (top m n hi) u := by
      simpa [coeff, cf] using hk
    have hh := Int.dvd_add hs hz
    change (p : Int) ∣ coeff P u -
      (coeff (relations m n lo) u + -coeff (rho n hi) u)
    rw [show coeff P u - (coeff (relations m n lo) u + coeff (relations m n hi) u) +
      coeff (top m n hi) u = coeff P u -
      (coeff (relations m n lo) u + -coeff (rho n hi) u) by omega] at hh
    exact hh
  · rintro ⟨lo, hi, hlo, hhi, he⟩
    refine ⟨lo ++ hi, ?_, ?_⟩
    · intro t ht
      rcases List.mem_append.mp ht with ht | ht
      · rcases hlo t ht with ⟨d, hd, hg⟩
        exact ⟨d, by omega, hg⟩
      · exact ⟨D, Nat.le_refl _, hhi.1 t ht⟩
    · intro u
      change (p : Int) ∣ coeff P u - coeff (relations m n (lo ++ hi)) u
      rw [relations_append]
      have hs := he u
      change (p : Int) ∣ coeff P u -
        cf ((relations m n lo).terms ++ negT (rho n hi).terms) u at hs
      rw [cf_append, cf_negT] at hs
      have hk := hhi.2 u
      have hz : (p : Int) ∣ coeff (top m n hi) u := by
        simpa [coeff, cf] using hk
      have hh := Int.dvd_sub hs hz
      rw [relations_coeff m n hi u]
      change (p : Int) ∣ coeff P u -
        (coeff (relations m n lo) u + (coeff (top m n hi) u - coeff (rho n hi) u))
      have heq : coeff P u - (cf (relations m n lo).terms u + -cf (rho n hi).terms u) -
        coeff (top m n hi) u = coeff P u -
        (coeff (relations m n lo) u + (coeff (top m n hi) u - coeff (rho n hi) u)) := by
          change coeff P u - (coeff (relations m n lo) u + -coeff (rho n hi) u) - _ = _
          omega
      rw [heq] at hh
      exact hh

end Programme.«20261104-1627-proof-complexity».MatchingLabels
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.filtered_decomposition
