import Programme.«20261027-0607-proof-complexity».Lucas
import Programme.«20261026-1402-proof-complexity».Ext1Exact

/-! Reproof of K7 (`Ext1Exact.f3_exact`, exact PC degree 3 over `Z/3` for `ontoFPHP n (3 c)`,
`3 ∤ c`, `n ≥ 3`) by a different route: th's peeling chain (`Peel.pc_degree_ge_p`, via windows,
flag lemma and S_j) specialised at `p = 3` through `Lucas.pc_degree_exact`, in place of the
library's explicit level-1 operator `Ext1.no_deg2`. -/

namespace Programme.«20261027-0607-proof-complexity».K7Reproof

open Programme.«20261026-1402-proof-complexity»

theorem isPrime3 : Programme.«20261027-0607-proof-complexity».Peel.IsPrime 3 := by
  refine ⟨by decide, fun a ha => ?_⟩
  have hle : a ≤ 3 := Nat.le_of_dvd (by decide) ha
  have : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by omega
  rcases this with h | h | h | h <;> subst h
  · exact absurd ha (by decide)
  · exact Or.inl rfl
  · exact absurd ha (by decide)
  · exact Or.inr rfl

theorem f3_exact : type_of% @Ext1Exact.f3_exact := by
  intro c n D hc hn
  exact Programme.«20261027-0607-proof-complexity».Lucas.pc_degree_exact isPrime3 hc n (by omega) D

example : type_of% @f3_exact = type_of% @Ext1Exact.f3_exact := rfl

end Programme.«20261027-0607-proof-complexity».K7Reproof

#print axioms Programme.«20261027-0607-proof-complexity».K7Reproof.f3_exact
