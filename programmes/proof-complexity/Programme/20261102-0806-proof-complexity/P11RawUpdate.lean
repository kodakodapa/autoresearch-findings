import Programme.«20261102-0806-proof-complexity».P11Candidate

namespace Programme.«20261102-0806-proof-complexity».P11RawUpdate
open Programme.«20261102-0806-proof-complexity».P11Candidate

theorem count_extend (g : List Nat) {i j : Nat} (hj : j < 21) (a b : Nat) :
    count ((i * 21 + j) :: g) a b = count g a b +
      (if pigeonClass i = a ∧ j / 10 = b then 1 else 0) := by
  have hd : (i * 21 + j) / 21 = i := by omega
  have hm : (i * 21 + j) % 21 = j := by omega
  simp only [count, List.filter_cons, hd, hm]
  split <;> simp_all <;> omega

#print axioms count_extend
end Programme.«20261102-0806-proof-complexity».P11RawUpdate
