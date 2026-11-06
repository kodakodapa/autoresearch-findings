import Programme.«20261102-1249-proof-complexity».UniformC3.ExplicitAlgebra

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Programme.«20261102-1249-proof-complexity».UniformC3.Block

def prod3 (f : Ix → Int) := f 0 * f 1 * f 2

def weight (p : Nat) (M : Matrix) : Int :=
  prod3 (fun i => (factorial (capacity p i - rc M i) : Int)) *
  prod3 (fun j => (factorial (capacity p j - cc M j) : Int))

theorem factorial_drop (n : Nat) (hn : 0 < n) :
    (factorial n : Int) = (n : Int) * factorial (n-1) := by
  cases n with
  | zero => omega
  | succ n => simp [factorial]

theorem prod_factorial_drop (q : Ix → Nat) (i : Ix) (hi : 0 < q i) :
    (q i : Int) * prod3 (fun r => (factorial (q r - if r=i then 1 else 0) : Int)) =
      prod3 (fun r => (factorial (q r) : Int)) := by
  have h := factorial_drop (q i) hi
  rcases fin3_cases i with rfl | rfl | rfl <;>
    simp [prod3,h,Int.mul_assoc,Int.mul_comm,Int.mul_left_comm]

theorem weight_inc {p : Nat} {M : Matrix} (i j : Ix)
    (hi : rc M i < capacity p i) (hj : cc M j < capacity p j) :
    ((capacity p i - rc M i : Nat) : Int) * ((capacity p j - cc M j : Nat) : Int) *
      weight p (inc M i j) = weight p M := by
  have hr := prod_factorial_drop (fun r => capacity p r - rc M r) i (by omega)
  have hc := prod_factorial_drop (fun c => capacity p c - cc M c) j (by omega)
  have er : ∀ r, capacity p r - rc (inc M i j) r =
      (capacity p r - rc M r) - if r=i then 1 else 0 := by
    intro r; rw [rc_inc]; omega
  have ec : ∀ c, capacity p c - cc (inc M i j) c =
      (capacity p c - cc M c) - if c=j then 1 else 0 := by
    intro c; rw [cc_inc]; omega
  unfold weight
  simp only [er,ec]
  rw [← hr,← hc]
  simp [Int.mul_assoc,Int.mul_comm,Int.mul_left_comm]

theorem explicit_eq {p : Nat} {M : Matrix} (hF : Feasible (capacity p) M) (ht : total M = p) :
    explicitValue p M = -(factorial (p-2) : Int) * weight p M * phi p M := by
  have hR : rc M 2 ≤ 1 := by simpa [capacity] using (hF 2).1
  have hC : cc M 2 ≤ 1 := by simpa [capacity] using (hF 2).2
  have fr : factorial (1-rc M 2) = 1 := by
    have h : rc M 2 = 0 ∨ rc M 2 = 1 := by omega
    rcases h with h | h <;> simp [h,factorial]
  have fc : factorial (1-cc M 2) = 1 := by
    have h : cc M 2 = 0 ∨ cc M 2 = 1 := by omega
    rcases h with h | h <;> simp [h,factorial]
  simp [explicitValue,hF,ht,weight,prod3,capacity,phi,jCore,hR,hC,fr,fc,
    Int.mul_assoc,Int.mul_comm,Int.mul_left_comm,Int.neg_mul,Int.mul_neg]

theorem explicit_transpose (p : Nat) (M : Matrix) :
    explicitValue p (transpose M) = explicitValue p M := by
  by_cases hF : Feasible (capacity p) M
  · by_cases ht : total M = p
    · rw [explicit_eq (feasible_transpose hF) (by rw [total_transpose]; exact ht),explicit_eq hF ht,
        phi_transpose]
      simp [weight,rc_transpose,cc_transpose,Int.mul_comm]
    · simp [explicitValue,total_transpose,ht]
  · have hf : ¬Feasible (capacity p) (transpose M) := by
      intro h
      apply hF
      intro i
      exact ⟨(h i).2,(h i).1⟩
    simp [explicitValue,hF,hf]

theorem weighted_term {p : Nat} (hp : 2 ≤ p) {M : Matrix}
    (hF : Feasible (capacity p) M) (ht : total M = p-1)
    (i j : Ix) (hi : rc M i < capacity p i) :
    ((capacity p i : Int)-rc M i) * (((capacity p j : Int)-cc M j) * explicitValue p (inc M i j)) =
      -(factorial (p-2) : Int) * weight p M * phi p (inc M i j) := by
  have htop : total (inc M i j) = p := by rw [total_inc,ht]; omega
  by_cases hj : cc M j < capacity p j
  · have hw := weight_inc i j hi hj
    have eri : ((capacity p i - rc M i : Nat) : Int) = (capacity p i : Int)-rc M i := by omega
    have ecj : ((capacity p j - cc M j : Nat) : Int) = (capacity p j : Int)-cc M j := by omega
    rw [eri,ecj] at hw
    rw [explicit_eq (feasible_inc hF i j hi hj) htop]
    rw [← hw]
    simp [Int.mul_assoc,Int.mul_comm,Int.mul_left_comm]
  · have he : cc M j = capacity p j := by have := (hF j).2; omega
    have hb : capacity p j < cc (inc M i j) j := by rw [cc_inc]; simp; omega
    rw [phi_bad_col hp htop j hb,he]
    simp

theorem explicit_row {p : Nat} (hp : 2 ≤ p) {M : Matrix}
    (hF : Feasible (capacity p) M) (ht : total M = p-1) (i : Ix) :
    sum3 (fun j => ((capacity p j : Int)-cc M j) * explicitValue p (inc M i j)) = 0 := by
  by_cases hi : rc M i < capacity p i
  · have he : ((capacity p i : Int)-rc M i) *
        sum3 (fun j => ((capacity p j : Int)-cc M j) * explicitValue p (inc M i j)) = 0 := by
      unfold sum3
      simp only [Int.mul_add,weighted_term hp hF ht i _ hi]
      have h := phi_row hp hF ht i hi
      unfold sum3 at h
      rw [← Int.mul_add,← Int.mul_add,h,Int.mul_zero]
    have hn : (capacity p i : Int)-rc M i ≠ 0 := by omega
    exact (Int.mul_eq_zero.mp he).resolve_left hn
  · have he : rc M i = capacity p i := by have := (hF i).1; omega
    have hz : ∀ j : Ix, explicitValue p (inc M i j) = 0 := by
      intro j
      have hf : ¬Feasible (capacity p) (inc M i j) := by
        intro h
        have hh := (h i).1
        rw [rc_inc] at hh
        simp only [ite_eq_left] at hh
        omega
      simp [explicitValue,hf]
    simp [sum3,hz]

theorem explicit_col {p : Nat} (hp : 2 ≤ p) {M : Matrix}
    (hF : Feasible (capacity p) M) (ht : total M = p-1) (j : Ix) :
    sum3 (fun i => ((capacity p i : Int)-rc M i) * explicitValue p (inc M i j)) = 0 := by
  have h := explicit_row hp (feasible_transpose hF) (by rw [total_transpose]; exact ht) j
  simpa only [cc_transpose,← inc_transpose,explicit_transpose] using h

#print axioms explicit_row
#print axioms explicit_col
end Programme.«20261102-1249-proof-complexity».UniformC3.Block
