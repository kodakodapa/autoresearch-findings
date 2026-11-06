import Programme.«20261104-1627-proof-complexity».MatchingSquareFree
namespace Programme.«20261104-1627-proof-complexity».ForbiddenClassification
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261104-1627-proof-complexity».MatchingReduction

theorem forbidden_coordinates {n k u w : Nat} (hn : 0 < n)
    (h : prod2 u w ∈ ontoFPHP n k) :
    u ≠ w ∧ (u/n = w/n ∨ u%n = w%n) := by
  simp only [ontoFPHP, List.mem_append] at h
  rcases h with ((h | h) | h) | h
  · obtain ⟨i,hi,he⟩ := List.mem_map.mp h
    have hh := congrArg Poly.terms he
    simp [sumOne, prod2] at hh
  · obtain ⟨j,hj,he⟩ := List.mem_map.mp h
    have hh := congrArg Poly.terms he
    simp [sumOne, prod2] at hh
  · obtain ⟨j,hj,h⟩ := List.mem_flatMap.mp h
    obtain ⟨i,hi,h⟩ := List.mem_flatMap.mp h
    obtain ⟨i',hi',he⟩ := List.mem_filterMap.mp h
    split at he <;> simp_all only [Option.some.injEq, reduceCtorEq]
    have hh := congrArg Poly.terms he
    simp only [prod2, List.cons.injEq, Prod.mk.injEq, true_and] at hh
    obtain ⟨hu,hw,_⟩ := hh.1
    subst u; subst w
    have hjb := List.mem_range.mp hj
    simp only [var]
    have hmod (a : Nat) : (a*n+j)%n = j := by simp [Nat.add_mod, Nat.mod_eq_of_lt hjb]
    refine ⟨?_, Or.inr (by rw [hmod, hmod])⟩
    intro heq
    have : i*n = i'*n := by omega
    have : i = i' := Nat.eq_of_mul_eq_mul_right hn this
    omega
  · obtain ⟨i,hi,h⟩ := List.mem_flatMap.mp h
    obtain ⟨j,hj,h⟩ := List.mem_flatMap.mp h
    obtain ⟨j',hj',he⟩ := List.mem_filterMap.mp h
    split at he <;> simp_all only [Option.some.injEq, reduceCtorEq]
    have hh := congrArg Poly.terms he
    simp only [prod2, List.cons.injEq, Prod.mk.injEq, true_and] at hh
    obtain ⟨hu,hw,_⟩ := hh.1
    subst u; subst w
    have hjb := List.mem_range.mp hj
    have hjb' := List.mem_range.mp hj'
    simp only [var]
    have hdiv (a : Nat) (ha : a < n) : (i*n+a)/n = i := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt ha]; omega
    exact ⟨by omega, Or.inl (by rw [hdiv j hjb, hdiv j' hjb'])⟩
theorem safe_of_coordinates {n k : Nat} (hn : 0 < n) (s : List Nat)
    (hs : ∀ u ∈ s, ∀ w ∈ s, u ≠ w → u/n ≠ w/n ∧ u%n ≠ w%n) :
    Safe (ontoFPHP n k) s := by
  intro u hu w hw h
  obtain ⟨hne,hcoord⟩ := forbidden_coordinates hn h
  obtain ⟨hr,hc⟩ := hs u hu w hw hne
  exact hcoord.elim hr hc
end Programme.«20261104-1627-proof-complexity».ForbiddenClassification
#print axioms Programme.«20261104-1627-proof-complexity».ForbiddenClassification.forbidden_coordinates

#print axioms Programme.«20261104-1627-proof-complexity».ForbiddenClassification.safe_of_coordinates
