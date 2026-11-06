import Programme.«20261102-1249-proof-complexity».UniformC3.ExplicitFormula

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Programme.«20261102-1249-proof-complexity».UniformC3.Block

theorem boundary_cases {p : Nat} {M : Matrix} (h : Feasible (capacity p) M) :
    (M 0 2=0 ∧ M 1 2=0 ∧ M 2 0=0 ∧ M 2 1=0 ∧ M 2 2=0) ∨
    (M 0 2=1 ∧ M 1 2=0 ∧ M 2 0=0 ∧ M 2 1=0 ∧ M 2 2=0) ∨
    (M 0 2=0 ∧ M 1 2=1 ∧ M 2 0=0 ∧ M 2 1=0 ∧ M 2 2=0) ∨
    (M 0 2=0 ∧ M 1 2=0 ∧ M 2 0=1 ∧ M 2 1=0 ∧ M 2 2=0) ∨
    (M 0 2=0 ∧ M 1 2=0 ∧ M 2 0=0 ∧ M 2 1=1 ∧ M 2 2=0) ∨
    (M 0 2=0 ∧ M 1 2=0 ∧ M 2 0=0 ∧ M 2 1=0 ∧ M 2 2=1) ∨
    (M 0 2=1 ∧ M 1 2=0 ∧ M 2 0=1 ∧ M 2 1=0 ∧ M 2 2=0) ∨
    (M 0 2=1 ∧ M 1 2=0 ∧ M 2 0=0 ∧ M 2 1=1 ∧ M 2 2=0) ∨
    (M 0 2=0 ∧ M 1 2=1 ∧ M 2 0=1 ∧ M 2 1=0 ∧ M 2 2=0) ∨
    (M 0 2=0 ∧ M 1 2=1 ∧ M 2 0=0 ∧ M 2 1=1 ∧ M 2 2=0) := by
  have hr := (h 2).1
  have hc := (h 2).2
  simp only [capacity,rc,cc,ite_eq_left] at hr hc
  omega

def jCore (p : Nat) (M : Matrix) : Int :=
  if rc M 2 ≤ 1 ∧ cc M 2 ≤ 1 then numerator p M else 0

def phi (p : Nat) (M : Matrix) : Int := (-1 : Int)^(M 0 1 + M 1 0) * jCore p M

theorem phi_row {p : Nat} (hp : 2 ≤ p) {M : Matrix}
    (hF : Feasible (capacity p) M) (ht : total M = p-1)
    (i : Ix) (hi : rc M i < capacity p i) :
    sum3 (fun j => phi p (inc M i j)) = 0 := by
  have hb := boundary_cases hF
  have h0 := hF 0
  have h1 := hF 1
  have h2 := hF 2
  rcases fin3_cases i with rfl | rfl | rfl <;>
    rcases hb with h | h | h | h | h | h | h | h | h | h <;>
    rcases h with ⟨hu,hv,hs,ht',hw⟩ <;>
    simp only [capacity,rc,cc,total,hu,hv,hs,ht',hw] at hi ht h0 h1 h2 <;>
    simp only [sum3,phi,jCore,numerator,inc,rc,cc,hu,hv,hs,ht',hw] <;>
    simp [Nat.add_assoc,Int.pow_succ] <;> try omega
  all_goals first
    | (have hz : (M 0 0 : Int) + M 0 1 + M 1 0 + M 1 1 = ((p-1 : Nat) : Int) := by omega
       rw [← hz]
       simp only [Int.mul_add,Int.mul_neg]
       omega)
    | grind


def transpose (M : Matrix) : Matrix := fun i j => M j i

theorem rc_transpose (M : Matrix) (i : Ix) : rc (transpose M) i = cc M i := rfl
theorem cc_transpose (M : Matrix) (i : Ix) : cc (transpose M) i = rc M i := rfl

theorem total_transpose (M : Matrix) : total (transpose M) = total M := by
  simp only [total,rc,transpose]; omega

theorem feasible_transpose {p : Nat} {M : Matrix} (h : Feasible (capacity p) M) :
    Feasible (capacity p) (transpose M) := fun i => ⟨(h i).2,(h i).1⟩

theorem phi_transpose (p : Nat) (M : Matrix) : phi p (transpose M) = phi p M := by
  by_cases hb : rc M 2 ≤ 1 ∧ cc M 2 ≤ 1
  · have hb' : cc M 2 ≤ 1 ∧ rc M 2 ≤ 1 := ⟨hb.2,hb.1⟩
    have hR := hb.1; have hC := hb.2
    simp only [rc,cc] at hR hC
    have hpats :
      (M 0 2=0 ∧ M 1 2=0 ∧ M 2 0=0 ∧ M 2 1=0 ∧ M 2 2=0) ∨
      (M 0 2=1 ∧ M 1 2=0 ∧ M 2 0=0 ∧ M 2 1=0 ∧ M 2 2=0) ∨
      (M 0 2=0 ∧ M 1 2=1 ∧ M 2 0=0 ∧ M 2 1=0 ∧ M 2 2=0) ∨
      (M 0 2=0 ∧ M 1 2=0 ∧ M 2 0=1 ∧ M 2 1=0 ∧ M 2 2=0) ∨
      (M 0 2=0 ∧ M 1 2=0 ∧ M 2 0=0 ∧ M 2 1=1 ∧ M 2 2=0) ∨
      (M 0 2=0 ∧ M 1 2=0 ∧ M 2 0=0 ∧ M 2 1=0 ∧ M 2 2=1) ∨
      (M 0 2=1 ∧ M 1 2=0 ∧ M 2 0=1 ∧ M 2 1=0 ∧ M 2 2=0) ∨
      (M 0 2=1 ∧ M 1 2=0 ∧ M 2 0=0 ∧ M 2 1=1 ∧ M 2 2=0) ∨
      (M 0 2=0 ∧ M 1 2=1 ∧ M 2 0=1 ∧ M 2 1=0 ∧ M 2 2=0) ∨
      (M 0 2=0 ∧ M 1 2=1 ∧ M 2 0=0 ∧ M 2 1=1 ∧ M 2 2=0) := by omega
    rcases hpats with h | h | h | h | h | h | h | h | h | h <;>
      rcases h with ⟨hu,hv,hs,ht,hw⟩ <;>
      simp [phi,jCore,numerator,rc,cc,transpose,hu,hv,hs,ht,hw,Nat.add_comm,Int.mul_comm]
  · have hb' : ¬(cc M 2 ≤ 1 ∧ rc M 2 ≤ 1) := by omega
    simp [phi,jCore,rc_transpose,cc_transpose,hb,hb']

theorem inc_transpose (M : Matrix) (i j : Ix) :
    transpose (inc M i j) = inc (transpose M) j i := by
  funext r c
  simp [transpose,inc,and_comm]

theorem phi_col {p : Nat} (hp : 2 ≤ p) {M : Matrix}
    (hF : Feasible (capacity p) M) (ht : total M = p-1)
    (j : Ix) (hj : cc M j < capacity p j) :
    sum3 (fun i => phi p (inc M i j)) = 0 := by
  have h := phi_row hp (feasible_transpose hF) (by rw [total_transpose]; exact ht) j hj
  simpa only [← inc_transpose,phi_transpose] using h

theorem rc_inc (M : Matrix) (i j r : Ix) :
    rc (inc M i j) r = rc M r + if r=i then 1 else 0 := by
  rcases fin3_cases j with rfl | rfl | rfl <;>
    by_cases h : r=i <;> simp [rc,inc,h] <;> omega

theorem cc_inc (M : Matrix) (i j c : Ix) :
    cc (inc M i j) c = cc M c + if c=j then 1 else 0 := by
  rcases fin3_cases i with rfl | rfl | rfl <;>
    by_cases h : c=j <;> simp [cc,inc,h] <;> omega

theorem total_inc (M : Matrix) (i j : Ix) : total (inc M i j) = total M + 1 := by
  simp only [total,rc_inc]
  rcases fin3_cases i with rfl | rfl | rfl <;> simp <;> omega

theorem feasible_inc {p : Nat} {M : Matrix} (hF : Feasible (capacity p) M)
    (i j : Ix) (hi : rc M i < capacity p i) (hj : cc M j < capacity p j) :
    Feasible (capacity p) (inc M i j) := by
  intro r
  rw [rc_inc,cc_inc]
  constructor
  · by_cases h : r=i
    · subst r; simp; omega
    · rw [ite_eq_right h]; simp; exact (hF r).1
  · by_cases h : r=j
    · subst r; simp; omega
    · rw [ite_eq_right h]; simp; exact (hF r).2

theorem phi_bad_col {p : Nat} (hp : 2 ≤ p) {M : Matrix} (ht : total M = p)
    (j : Ix) (hj : capacity p j < cc M j) : phi p M = 0 := by
  unfold total rc at ht
  rcases fin3_cases j with rfl | rfl | rfl
  · have hz : M 0 1=0 ∧ M 0 2=0 ∧ M 1 1=0 ∧ M 1 2=0 ∧ M 2 1=0 ∧ M 2 2=0 := by
      simp [capacity,cc] at hj; omega
    rcases hz with ⟨h01,h02,h11,h12,h21,h22⟩
    simp [phi,jCore,numerator,rc,cc,h01,h02,h11,h12,h21,h22]
    grind
  · have hz : M 0 0=0 ∧ M 0 2=0 ∧ M 1 0=0 ∧ M 1 2=0 ∧ M 2 0=0 ∧ M 2 2=0 := by
      simp [capacity,cc] at hj; omega
    rcases hz with ⟨h00,h02,h10,h12,h20,h22⟩
    simp [phi,jCore,numerator,rc,cc,h00,h02,h10,h12,h20,h22]
  · have h : ¬cc M 2 ≤ 1 := by simpa [capacity] using Nat.not_le.mpr hj
    simp [phi,jCore,h]

#print axioms phi_row
#print axioms phi_col
end Programme.«20261102-1249-proof-complexity».UniformC3.Block
