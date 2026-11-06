import Programme.«20261101-0614-proof-complexity».Composition
namespace Programme.«20261101-0614-proof-complexity».Composition
private theorem band_lt (s t b : Nat) (hst : s < t) (hb : b ≤ s) :
    s*(s+1)+2*b < t*(t+1) := by
  have h₁ : (s+1)*(s+2) ≤ t*(t+1) :=
    Nat.mul_le_mul hst (by omega)
  have h₂ : s*(s+1)+2*b < (s+1)*(s+2) := by
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul,
      Nat.mul_succ] at *
    omega
  omega

theorem pair_injective {a b c d : Nat} (h : pair a b = pair c d) :
    a = c ∧ b = d := by
  have hs : a+b = c+d := by
    rcases Nat.lt_trichotomy (a+b) (c+d) with hl | he | hr
    · have hh := band_lt (a+b) (c+d) b hl (by omega)
      unfold pair at h
      omega
    · exact he
    · have hh := band_lt (c+d) (a+b) d hr (by omega)
      unfold pair at h
      omega
  unfold pair at h
  rw [hs] at h
  constructor <;> omega
#print axioms pair_injective
end Programme.«20261101-0614-proof-complexity».Composition
