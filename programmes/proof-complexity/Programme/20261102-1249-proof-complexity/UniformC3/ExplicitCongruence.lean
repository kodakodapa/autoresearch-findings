import Programme.«20261102-1249-proof-complexity».UniformC3.FactorCongruence

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Programme.«20261102-1249-proof-complexity».UniformC3.Block
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem explicit_common_congruence {p : Nat} (hp : 2 ≤ p) {M : Matrix}
    (hF : Feasible (capacity p) M) (ht : total M = p) :
    Cong p (explicitValue p M) (commonValue p) := by
  have hb := boundary_cases hF
  rcases hb with h | h | h | h | h | h | h | h | h | h
  · rcases h with ⟨hu,hv,hs,ht',hw⟩
    have h0 := hF 0
    have h1 := hF 1
    have h2 := hF 2
    have htotal := ht
    simp [capacity,rc,cc,total,hu,hv,hs,ht',hw] at h0 h1 h2 htotal
    have e0 : p-1-rc M 0 = (M 1 0+M 1 1)-1 := by
      simp only [rc,hu,hv,hs,ht',hw]; omega
    have e1 : p-1-rc M 1 = (M 0 0+M 0 1)-1 := by
      simp only [rc,hu,hv,hs,ht',hw]; omega
    have e2 : p-1-cc M 0 = (M 0 1+M 1 1)-1 := by
      simp only [cc,hu,hv,hs,ht',hw]; omega
    have e3 : p-1-cc M 1 = (M 0 0+M 1 0)-1 := by
      simp only [cc,hu,hv,hs,ht',hw]; omega
    have hsign : sign ((M 0 0+M 0 1)) * sign ((M 0 0+M 1 0)) = sign (M 0 1+M 1 0) * (1 : Int) := by
      simpa [sign] using sign_pair (M 0 0) (M 0 1) (M 1 0) 0 0
    have f0 : fac ((M 0 0+M 0 1)) = (((M 0 0+M 0 1) : Nat) : Int) * fac (((M 0 0+M 0 1))-1) :=
      factorial_drop ((M 0 0+M 0 1)) (by omega)
    have f1 : fac ((M 0 0+M 1 0)) = (((M 0 0+M 1 0) : Nat) : Int) * fac (((M 0 0+M 1 0))-1) :=
      factorial_drop ((M 0 0+M 1 0)) (by omega)
    have hval : explicitValue p M = -sign (M 0 1+M 1 0) * fac (p-2) * numerator p M * fac ((M 1 0+M 1 1)-1) * fac ((M 0 0+M 0 1)-1) * fac ((M 0 1+M 1 1)-1) * fac ((M 0 0+M 1 0)-1) := by
      unfold explicitValue
      rw [ite_eq_left ⟨hF,ht⟩,e0,e1,e2,e3]
      rfl
    have he : explicitValue p M - (fac (p-2) * (sign ((M 0 0+M 0 1)) * sign ((M 0 0+M 1 0)) * fac ((M 0 0+M 0 1)) * fac ((M 1 0+M 1 1)-1) * fac ((M 0 0+M 1 0)) * fac ((M 0 1+M 1 1)-1))) = (p : Int) * (-sign (M 0 1+M 1 0) * fac (p-2) * (M 0 0 : Int) * fac ((M 1 0+M 1 1)-1) * fac ((M 0 0+M 0 1)-1) * fac ((M 0 1+M 1 1)-1) * fac ((M 0 0+M 1 0)-1)) := by
      rw [hval,hsign,f0,f1]
      simp only [numerator,rc,cc,hu,hv,hs,ht',hw]
      simp
      have hz : (M 0 0 : Int)+M 0 1+M 1 0+M 1 1 = (p : Int) := by omega
      grind only
    have hc : Cong p (explicitValue p M) (fac (p-2) * (sign ((M 0 0+M 0 1)) * sign ((M 0 0+M 1 0)) * fac ((M 0 0+M 0 1)) * fac ((M 1 0+M 1 1)-1) * fac ((M 0 0+M 1 0)) * fac ((M 0 1+M 1 1)-1))) := by
      unfold Cong; rw [he]; exact Int.dvd_mul_right _ _
    exact cong_trans hc (main_pair hp ((M 0 0+M 0 1)) ((M 1 0+M 1 1)-1) ((M 0 0+M 1 0)) ((M 0 1+M 1 1)-1) (by omega) (by omega))
  · rcases h with ⟨hu,hv,hs,ht',hw⟩
    have h0 := hF 0
    have h1 := hF 1
    have h2 := hF 2
    have htotal := ht
    simp [capacity,rc,cc,total,hu,hv,hs,ht',hw] at h0 h1 h2 htotal
    have e0 : p-1-rc M 0 = (M 1 0+M 1 1)-1 := by
      simp only [rc,hu,hv,hs,ht',hw]; omega
    have e1 : p-1-rc M 1 = (M 0 0+M 0 1) := by
      simp only [rc,hu,hv,hs,ht',hw]; omega
    have e2 : p-1-cc M 0 = (M 0 1+M 1 1) := by
      simp only [cc,hu,hv,hs,ht',hw]; omega
    have e3 : p-1-cc M 1 = (M 0 0+M 1 0) := by
      simp only [cc,hu,hv,hs,ht',hw]; omega
    have hsign : sign ((M 0 0+M 0 1)) * sign ((M 0 0+M 1 0)) = sign (M 0 1+M 1 0) * (1 : Int) := by
      simpa [sign] using sign_pair (M 0 0) (M 0 1) (M 1 0) 0 0
    have f0 : fac ((M 1 0+M 1 1)) = (((M 1 0+M 1 1) : Nat) : Int) * fac (((M 1 0+M 1 1))-1) :=
      factorial_drop ((M 1 0+M 1 1)) (by omega)
    have hval : explicitValue p M = -sign (M 0 1+M 1 0) * fac (p-2) * numerator p M * fac ((M 1 0+M 1 1)-1) * fac ((M 0 0+M 0 1)) * fac ((M 0 1+M 1 1)) * fac ((M 0 0+M 1 0)) := by
      unfold explicitValue
      rw [ite_eq_left ⟨hF,ht⟩,e0,e1,e2,e3]
      rfl
    have he : explicitValue p M = fac (p-2) * (sign ((M 0 0+M 0 1)) * sign ((M 0 0+M 1 0)) * fac ((M 0 0+M 0 1)) * fac ((M 1 0+M 1 1)) * fac ((M 0 0+M 1 0)) * fac ((M 0 1+M 1 1))) := by
      rw [hval,hsign,f0]
      simp only [numerator,rc,cc,hu,hv,hs,ht',hw]
      simp [fac,sign,Int.mul_assoc,Int.mul_comm,Int.mul_left_comm,Int.neg_mul,Int.mul_neg]
      try grind only
    exact cong_eq he (main_pair hp ((M 0 0+M 0 1)) ((M 1 0+M 1 1)) ((M 0 0+M 1 0)) ((M 0 1+M 1 1)) (by omega) (by omega))
  · rcases h with ⟨hu,hv,hs,ht',hw⟩
    have h0 := hF 0
    have h1 := hF 1
    have h2 := hF 2
    have htotal := ht
    simp [capacity,rc,cc,total,hu,hv,hs,ht',hw] at h0 h1 h2 htotal
    have e0 : p-1-rc M 0 = (M 1 0+M 1 1) := by
      simp only [rc,hu,hv,hs,ht',hw]; omega
    have e1 : p-1-rc M 1 = (M 0 0+M 0 1)-1 := by
      simp only [rc,hu,hv,hs,ht',hw]; omega
    have e2 : p-1-cc M 0 = (M 0 1+M 1 1) := by
      simp only [cc,hu,hv,hs,ht',hw]; omega
    have e3 : p-1-cc M 1 = (M 0 0+M 1 0) := by
      simp only [cc,hu,hv,hs,ht',hw]; omega
    have hsign : sign ((M 0 0+M 0 1)) * sign ((M 0 0+M 1 0)) = sign (M 0 1+M 1 0) * (1 : Int) := by
      simpa [sign] using sign_pair (M 0 0) (M 0 1) (M 1 0) 0 0
    have f0 : fac ((M 0 0+M 0 1)) = (((M 0 0+M 0 1) : Nat) : Int) * fac (((M 0 0+M 0 1))-1) :=
      factorial_drop ((M 0 0+M 0 1)) (by omega)
    have hval : explicitValue p M = -sign (M 0 1+M 1 0) * fac (p-2) * numerator p M * fac ((M 1 0+M 1 1)) * fac ((M 0 0+M 0 1)-1) * fac ((M 0 1+M 1 1)) * fac ((M 0 0+M 1 0)) := by
      unfold explicitValue
      rw [ite_eq_left ⟨hF,ht⟩,e0,e1,e2,e3]
      rfl
    have he : explicitValue p M = fac (p-2) * (sign ((M 0 0+M 0 1)) * sign ((M 0 0+M 1 0)) * fac ((M 0 0+M 0 1)) * fac ((M 1 0+M 1 1)) * fac ((M 0 0+M 1 0)) * fac ((M 0 1+M 1 1))) := by
      rw [hval,hsign,f0]
      simp only [numerator,rc,cc,hu,hv,hs,ht',hw]
      simp [fac,sign,Int.mul_assoc,Int.mul_comm,Int.mul_left_comm,Int.neg_mul,Int.mul_neg]
      try grind only
    exact cong_eq he (main_pair hp ((M 0 0+M 0 1)) ((M 1 0+M 1 1)) ((M 0 0+M 1 0)) ((M 0 1+M 1 1)) (by omega) (by omega))
  · rcases h with ⟨hu,hv,hs,ht',hw⟩
    have h0 := hF 0
    have h1 := hF 1
    have h2 := hF 2
    have htotal := ht
    simp [capacity,rc,cc,total,hu,hv,hs,ht',hw] at h0 h1 h2 htotal
    have e0 : p-1-rc M 0 = (M 1 0+M 1 1) := by
      simp only [rc,hu,hv,hs,ht',hw]; omega
    have e1 : p-1-rc M 1 = (M 0 0+M 0 1) := by
      simp only [rc,hu,hv,hs,ht',hw]; omega
    have e2 : p-1-cc M 0 = (M 0 1+M 1 1)-1 := by
      simp only [cc,hu,hv,hs,ht',hw]; omega
    have e3 : p-1-cc M 1 = (M 0 0+M 1 0) := by
      simp only [cc,hu,hv,hs,ht',hw]; omega
    have hsign : sign ((M 0 0+M 0 1)) * sign ((M 0 0+M 1 0)) = sign (M 0 1+M 1 0) * (1 : Int) := by
      simpa [sign] using sign_pair (M 0 0) (M 0 1) (M 1 0) 0 0
    have f0 : fac ((M 0 1+M 1 1)) = (((M 0 1+M 1 1) : Nat) : Int) * fac (((M 0 1+M 1 1))-1) :=
      factorial_drop ((M 0 1+M 1 1)) (by omega)
    have hval : explicitValue p M = -sign (M 0 1+M 1 0) * fac (p-2) * numerator p M * fac ((M 1 0+M 1 1)) * fac ((M 0 0+M 0 1)) * fac ((M 0 1+M 1 1)-1) * fac ((M 0 0+M 1 0)) := by
      unfold explicitValue
      rw [ite_eq_left ⟨hF,ht⟩,e0,e1,e2,e3]
      rfl
    have he : explicitValue p M = fac (p-2) * (sign ((M 0 0+M 0 1)) * sign ((M 0 0+M 1 0)) * fac ((M 0 0+M 0 1)) * fac ((M 1 0+M 1 1)) * fac ((M 0 0+M 1 0)) * fac ((M 0 1+M 1 1))) := by
      rw [hval,hsign,f0]
      simp only [numerator,rc,cc,hu,hv,hs,ht',hw]
      simp [fac,sign,Int.mul_assoc,Int.mul_comm,Int.mul_left_comm,Int.neg_mul,Int.mul_neg]
      try grind only
    exact cong_eq he (main_pair hp ((M 0 0+M 0 1)) ((M 1 0+M 1 1)) ((M 0 0+M 1 0)) ((M 0 1+M 1 1)) (by omega) (by omega))
  · rcases h with ⟨hu,hv,hs,ht',hw⟩
    have h0 := hF 0
    have h1 := hF 1
    have h2 := hF 2
    have htotal := ht
    simp [capacity,rc,cc,total,hu,hv,hs,ht',hw] at h0 h1 h2 htotal
    have e0 : p-1-rc M 0 = (M 1 0+M 1 1) := by
      simp only [rc,hu,hv,hs,ht',hw]; omega
    have e1 : p-1-rc M 1 = (M 0 0+M 0 1) := by
      simp only [rc,hu,hv,hs,ht',hw]; omega
    have e2 : p-1-cc M 0 = (M 0 1+M 1 1) := by
      simp only [cc,hu,hv,hs,ht',hw]; omega
    have e3 : p-1-cc M 1 = (M 0 0+M 1 0)-1 := by
      simp only [cc,hu,hv,hs,ht',hw]; omega
    have hsign : sign ((M 0 0+M 0 1)) * sign ((M 0 0+M 1 0)) = sign (M 0 1+M 1 0) * (1 : Int) := by
      simpa [sign] using sign_pair (M 0 0) (M 0 1) (M 1 0) 0 0
    have f0 : fac ((M 0 0+M 1 0)) = (((M 0 0+M 1 0) : Nat) : Int) * fac (((M 0 0+M 1 0))-1) :=
      factorial_drop ((M 0 0+M 1 0)) (by omega)
    have hval : explicitValue p M = -sign (M 0 1+M 1 0) * fac (p-2) * numerator p M * fac ((M 1 0+M 1 1)) * fac ((M 0 0+M 0 1)) * fac ((M 0 1+M 1 1)) * fac ((M 0 0+M 1 0)-1) := by
      unfold explicitValue
      rw [ite_eq_left ⟨hF,ht⟩,e0,e1,e2,e3]
      rfl
    have he : explicitValue p M = fac (p-2) * (sign ((M 0 0+M 0 1)) * sign ((M 0 0+M 1 0)) * fac ((M 0 0+M 0 1)) * fac ((M 1 0+M 1 1)) * fac ((M 0 0+M 1 0)) * fac ((M 0 1+M 1 1))) := by
      rw [hval,hsign,f0]
      simp only [numerator,rc,cc,hu,hv,hs,ht',hw]
      simp [fac,sign,Int.mul_assoc,Int.mul_comm,Int.mul_left_comm,Int.neg_mul,Int.mul_neg]
      try grind only
    exact cong_eq he (main_pair hp ((M 0 0+M 0 1)) ((M 1 0+M 1 1)) ((M 0 0+M 1 0)) ((M 0 1+M 1 1)) (by omega) (by omega))
  · rcases h with ⟨hu,hv,hs,ht',hw⟩
    have h0 := hF 0
    have h1 := hF 1
    have h2 := hF 2
    have htotal := ht
    simp [capacity,rc,cc,total,hu,hv,hs,ht',hw] at h0 h1 h2 htotal
    have e0 : p-1-rc M 0 = (M 1 0+M 1 1) := by
      simp only [rc,hu,hv,hs,ht',hw]; omega
    have e1 : p-1-rc M 1 = (M 0 0+M 0 1) := by
      simp only [rc,hu,hv,hs,ht',hw]; omega
    have e2 : p-1-cc M 0 = (M 0 1+M 1 1) := by
      simp only [cc,hu,hv,hs,ht',hw]; omega
    have e3 : p-1-cc M 1 = (M 0 0+M 1 0) := by
      simp only [cc,hu,hv,hs,ht',hw]; omega
    have hsign : sign ((M 0 0+M 0 1)) * sign ((M 0 0+M 1 0)) = sign (M 0 1+M 1 0) * (1 : Int) := by
      simpa [sign] using sign_pair (M 0 0) (M 0 1) (M 1 0) 0 0
    have f0 : fac (p-1) = ((p-1 : Nat) : Int) * fac ((p-1)-1) :=
      factorial_drop (p-1) (by omega)
    have hval : explicitValue p M = -sign (M 0 1+M 1 0) * fac (p-2) * numerator p M * fac ((M 1 0+M 1 1)) * fac ((M 0 0+M 0 1)) * fac ((M 0 1+M 1 1)) * fac ((M 0 0+M 1 0)) := by
      unfold explicitValue
      rw [ite_eq_left ⟨hF,ht⟩,e0,e1,e2,e3]
      rfl
    have he : explicitValue p M = -fac (p-1) * (sign ((M 0 0+M 0 1)) * sign ((M 0 0+M 1 0)) * fac ((M 0 0+M 0 1)) * fac ((M 1 0+M 1 1)) * fac ((M 0 0+M 1 0)) * fac ((M 0 1+M 1 1))) := by
      rw [hval,hsign,f0]
      simp only [numerator,rc,cc,hu,hv,hs,ht',hw]
      rw [show p-1-1=p-2 by omega]
      simp [fac,sign,Int.mul_assoc,Int.mul_comm,Int.mul_left_comm,Int.neg_mul,Int.mul_neg]
    exact cong_eq he (diagonal_pair p ((M 0 0+M 0 1)) ((M 1 0+M 1 1)) ((M 0 0+M 1 0)) ((M 0 1+M 1 1)) (by omega) (by omega))
  · rcases h with ⟨hu,hv,hs,ht',hw⟩
    have h0 := hF 0
    have h1 := hF 1
    have h2 := hF 2
    have htotal := ht
    simp [capacity,rc,cc,total,hu,hv,hs,ht',hw] at h0 h1 h2 htotal
    have e0 : p-1-rc M 0 = (M 1 0+M 1 1) := by
      simp only [rc,hu,hv,hs,ht',hw]; omega
    have e1 : p-1-rc M 1 = (M 0 0+M 0 1)+1 := by
      simp only [rc,hu,hv,hs,ht',hw]; omega
    have e2 : p-1-cc M 0 = (M 0 1+M 1 1) := by
      simp only [cc,hu,hv,hs,ht',hw]; omega
    have e3 : p-1-cc M 1 = (M 0 0+M 1 0)+1 := by
      simp only [cc,hu,hv,hs,ht',hw]; omega
    have hsign : sign ((M 0 0+M 0 1)+1) * sign ((M 0 0+M 1 0)+1) = sign (M 0 1+M 1 0) * (1 : Int) := by
      simpa [sign] using sign_pair (M 0 0) (M 0 1) (M 1 0) 1 1
    have hval : explicitValue p M = -sign (M 0 1+M 1 0) * fac (p-2) * numerator p M * fac ((M 1 0+M 1 1)) * fac ((M 0 0+M 0 1)+1) * fac ((M 0 1+M 1 1)) * fac ((M 0 0+M 1 0)+1) := by
      unfold explicitValue
      rw [ite_eq_left ⟨hF,ht⟩,e0,e1,e2,e3]
      rfl
    have he : explicitValue p M = fac (p-2) * (sign ((M 0 0+M 0 1)+1) * sign ((M 0 0+M 1 0)+1) * fac ((M 0 0+M 0 1)+1) * fac ((M 1 0+M 1 1)) * fac ((M 0 0+M 1 0)+1) * fac ((M 0 1+M 1 1))) := by
      rw [hval,hsign]
      simp only [numerator,rc,cc,hu,hv,hs,ht',hw]
      simp [fac,sign,Int.mul_assoc,Int.mul_comm,Int.mul_left_comm,Int.neg_mul,Int.mul_neg]
    exact cong_eq he (main_pair hp ((M 0 0+M 0 1)+1) ((M 1 0+M 1 1)) ((M 0 0+M 1 0)+1) ((M 0 1+M 1 1)) (by omega) (by omega))
  · rcases h with ⟨hu,hv,hs,ht',hw⟩
    have h0 := hF 0
    have h1 := hF 1
    have h2 := hF 2
    have htotal := ht
    simp [capacity,rc,cc,total,hu,hv,hs,ht',hw] at h0 h1 h2 htotal
    have e0 : p-1-rc M 0 = (M 1 0+M 1 1) := by
      simp only [rc,hu,hv,hs,ht',hw]; omega
    have e1 : p-1-rc M 1 = (M 0 0+M 0 1)+1 := by
      simp only [rc,hu,hv,hs,ht',hw]; omega
    have e2 : p-1-cc M 0 = (M 0 1+M 1 1)+1 := by
      simp only [cc,hu,hv,hs,ht',hw]; omega
    have e3 : p-1-cc M 1 = (M 0 0+M 1 0) := by
      simp only [cc,hu,hv,hs,ht',hw]; omega
    have hsign : sign ((M 0 0+M 0 1)+1) * sign ((M 0 0+M 1 0)) = sign (M 0 1+M 1 0) * (-1 : Int) := by
      simpa [sign] using sign_pair (M 0 0) (M 0 1) (M 1 0) 1 0
    have hval : explicitValue p M = -sign (M 0 1+M 1 0) * fac (p-2) * numerator p M * fac ((M 1 0+M 1 1)) * fac ((M 0 0+M 0 1)+1) * fac ((M 0 1+M 1 1)+1) * fac ((M 0 0+M 1 0)) := by
      unfold explicitValue
      rw [ite_eq_left ⟨hF,ht⟩,e0,e1,e2,e3]
      rfl
    have he : explicitValue p M = fac (p-2) * (sign ((M 0 0+M 0 1)+1) * sign ((M 0 0+M 1 0)) * fac ((M 0 0+M 0 1)+1) * fac ((M 1 0+M 1 1)) * fac ((M 0 0+M 1 0)) * fac ((M 0 1+M 1 1)+1)) := by
      rw [hval,hsign]
      simp only [numerator,rc,cc,hu,hv,hs,ht',hw]
      simp [fac,sign,Int.mul_assoc,Int.mul_comm,Int.mul_left_comm,Int.neg_mul,Int.mul_neg]
    exact cong_eq he (main_pair hp ((M 0 0+M 0 1)+1) ((M 1 0+M 1 1)) ((M 0 0+M 1 0)) ((M 0 1+M 1 1)+1) (by omega) (by omega))
  · rcases h with ⟨hu,hv,hs,ht',hw⟩
    have h0 := hF 0
    have h1 := hF 1
    have h2 := hF 2
    have htotal := ht
    simp [capacity,rc,cc,total,hu,hv,hs,ht',hw] at h0 h1 h2 htotal
    have e0 : p-1-rc M 0 = (M 1 0+M 1 1)+1 := by
      simp only [rc,hu,hv,hs,ht',hw]; omega
    have e1 : p-1-rc M 1 = (M 0 0+M 0 1) := by
      simp only [rc,hu,hv,hs,ht',hw]; omega
    have e2 : p-1-cc M 0 = (M 0 1+M 1 1) := by
      simp only [cc,hu,hv,hs,ht',hw]; omega
    have e3 : p-1-cc M 1 = (M 0 0+M 1 0)+1 := by
      simp only [cc,hu,hv,hs,ht',hw]; omega
    have hsign : sign ((M 0 0+M 0 1)) * sign ((M 0 0+M 1 0)+1) = sign (M 0 1+M 1 0) * (-1 : Int) := by
      simpa [sign] using sign_pair (M 0 0) (M 0 1) (M 1 0) 0 1
    have hval : explicitValue p M = -sign (M 0 1+M 1 0) * fac (p-2) * numerator p M * fac ((M 1 0+M 1 1)+1) * fac ((M 0 0+M 0 1)) * fac ((M 0 1+M 1 1)) * fac ((M 0 0+M 1 0)+1) := by
      unfold explicitValue
      rw [ite_eq_left ⟨hF,ht⟩,e0,e1,e2,e3]
      rfl
    have he : explicitValue p M = fac (p-2) * (sign ((M 0 0+M 0 1)) * sign ((M 0 0+M 1 0)+1) * fac ((M 0 0+M 0 1)) * fac ((M 1 0+M 1 1)+1) * fac ((M 0 0+M 1 0)+1) * fac ((M 0 1+M 1 1))) := by
      rw [hval,hsign]
      simp only [numerator,rc,cc,hu,hv,hs,ht',hw]
      simp [fac,sign,Int.mul_assoc,Int.mul_comm,Int.mul_left_comm,Int.neg_mul,Int.mul_neg]
    exact cong_eq he (main_pair hp ((M 0 0+M 0 1)) ((M 1 0+M 1 1)+1) ((M 0 0+M 1 0)+1) ((M 0 1+M 1 1)) (by omega) (by omega))
  · rcases h with ⟨hu,hv,hs,ht',hw⟩
    have h0 := hF 0
    have h1 := hF 1
    have h2 := hF 2
    have htotal := ht
    simp [capacity,rc,cc,total,hu,hv,hs,ht',hw] at h0 h1 h2 htotal
    have e0 : p-1-rc M 0 = (M 1 0+M 1 1)+1 := by
      simp only [rc,hu,hv,hs,ht',hw]; omega
    have e1 : p-1-rc M 1 = (M 0 0+M 0 1) := by
      simp only [rc,hu,hv,hs,ht',hw]; omega
    have e2 : p-1-cc M 0 = (M 0 1+M 1 1)+1 := by
      simp only [cc,hu,hv,hs,ht',hw]; omega
    have e3 : p-1-cc M 1 = (M 0 0+M 1 0) := by
      simp only [cc,hu,hv,hs,ht',hw]; omega
    have hsign : sign ((M 0 0+M 0 1)) * sign ((M 0 0+M 1 0)) = sign (M 0 1+M 1 0) * (1 : Int) := by
      simpa [sign] using sign_pair (M 0 0) (M 0 1) (M 1 0) 0 0
    have hval : explicitValue p M = -sign (M 0 1+M 1 0) * fac (p-2) * numerator p M * fac ((M 1 0+M 1 1)+1) * fac ((M 0 0+M 0 1)) * fac ((M 0 1+M 1 1)+1) * fac ((M 0 0+M 1 0)) := by
      unfold explicitValue
      rw [ite_eq_left ⟨hF,ht⟩,e0,e1,e2,e3]
      rfl
    have he : explicitValue p M = fac (p-2) * (sign ((M 0 0+M 0 1)) * sign ((M 0 0+M 1 0)) * fac ((M 0 0+M 0 1)) * fac ((M 1 0+M 1 1)+1) * fac ((M 0 0+M 1 0)) * fac ((M 0 1+M 1 1)+1)) := by
      rw [hval,hsign]
      simp only [numerator,rc,cc,hu,hv,hs,ht',hw]
      simp [fac,sign,Int.mul_assoc,Int.mul_comm,Int.mul_left_comm,Int.neg_mul,Int.mul_neg]
    exact cong_eq he (main_pair hp ((M 0 0+M 0 1)) ((M 1 0+M 1 1)+1) ((M 0 0+M 1 0)) ((M 0 1+M 1 1)+1) (by omega) (by omega))

#print axioms explicit_common_congruence
end Programme.«20261102-1249-proof-complexity».UniformC3.Block
