import Programme.«20261104-1627-proof-complexity».LabelDecomposition

namespace Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261029-1156-proof-complexity».StdPC

theorem matching_length {m n d : Nat} {M : Matching}
    (h : M ∈ matchings m n d) : M.length = d := by
  induction d generalizing M with
  | zero => simpa [matchings] using h
  | succ d ih =>
    simp only [matchings, List.mem_flatMap, List.mem_map] at h
    rcases h with ⟨N, hN, i, _, j, _, rfl⟩
    simp [ih hN]

theorem label_length {m n d : Nat} {g : Label}
    (h : g ∈ labels m n d) : g.base.length = d - 1 := by
  unfold labels at h
  split at h
  · simp at h
  · rcases List.mem_flatMap.mp h with ⟨M, hM, hg⟩
    rcases List.mem_append.mp hg with hg | hg
    · rcases List.mem_map.mp hg with ⟨i, _, rfl⟩
      exact matching_length hM
    · rcases List.mem_map.mp hg with ⟨j, _, rfl⟩
      exact matching_length hM

theorem top_terms_length {m n d : Nat} (hd : 0 < d) {v : Vector}
    (hv : valid m n d v) :
    ∀ t ∈ (top m n v).terms, t.2.length = d := by
  intro t ht
  rcases List.mem_flatMap.mp ht with ⟨a, ha, ht⟩
  rcases List.mem_map.mp ht with ⟨b, hb, rfl⟩
  have hl := label_length (hv a ha)
  unfold topLabel at hb
  split at hb <;>
    rcases List.mem_map.mp hb with ⟨j, _, rfl⟩ <;>
    simp [mono, hl] <;> omega

theorem rho_terms_length {m n d : Nat} {v : Vector}
    (hv : valid m n d v) :
    ∀ t ∈ (rho n v).terms, t.2.length = d - 1 := by
  intro t ht
  rcases List.mem_map.mp ht with ⟨a, ha, rfl⟩
  simp [mono, label_length (hv a ha)]

/-- Coefficients outside the syntactic support degree vanish exactly. -/
theorem coeff_zero_of_lengths (P : Poly Nat) (u : List Nat)
    (h : ∀ t ∈ P.terms, t.2.length ≠ u.length) : coeff P u = 0 := by
  have hf : (P.terms.filter fun t => decide (t.2.Perm u)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro t ht
    exact fun hp => h t ht (of_decide_eq_true hp).length_eq
  simp [coeff, cf, hf]

/-- A homogeneous level-d combination which equals a polynomial of smaller
syntactic degree has zero top part, coefficientwise modulo p. -/
theorem extract_top {p m n d : Nat} (hd : 0 < d)
    (v : Vector) (hv : valid m n d v) (P : Poly Nat)
    (hP : P.deg < d) (heq : PEq p P (relations m n v)) :
    Kernel p m n d v := by
  refine ⟨hv, fun u => ?_⟩
  have hz : coeff (⟨[]⟩ : Poly Nat) u = 0 := by simp [coeff, cf]
  rw [hz]
  by_cases hu : u.length = d
  · have hPc : coeff P u = 0 := by
      apply coeff_zero_of_lengths
      intro t ht he
      have hb := (deg_le_iff P P.deg).mp (Nat.le_refl _) t ht
      omega
    have hr : coeff (rho n v) u = 0 := by
      apply coeff_zero_of_lengths
      intro t ht he
      have hb := rho_terms_length hv t ht
      omega
    have he := heq u
    rw [hPc, relations_coeff, hr] at he
    have he' : (p : Int) ∣ -coeff (top m n v) u := by simpa using he
    simpa using Int.dvd_neg.mp he'
  · have ht : coeff (top m n v) u = 0 := by
      apply coeff_zero_of_lengths
      intro t ht he
      exact hu (he.symm.trans (top_terms_length hd hv t ht))
    simp [ht]

/-- Exact homogeneous part of the filtered-span decomposition. -/
theorem lower_degree_iff_kernel {p m n d : Nat} (hd : 0 < d)
    (v : Vector) (hv : valid m n d v) :
    (∃ P : Poly Nat, P.deg < d ∧ PEq p P (relations m n v)) ↔
      Kernel p m n d v := by
  constructor
  · rintro ⟨P, hP, heq⟩
    exact extract_top hd v hv P hP heq
  · intro hk
    refine ⟨(⟨[]⟩ : Poly Nat).sub (rho n v), ?_, ?_⟩
    · have hb : (rho n v).deg ≤ d - 1 := by
        rw [deg_le_iff]
        intro t ht
        exact Nat.le_of_eq (rho_terms_length hv t ht)
      have hz : (⟨[]⟩ : Poly Nat).deg ≤ d - 1 := by
        rw [deg_le_iff]
        simp
      have hdg := deg_sub (⟨[]⟩ : Poly Nat) (rho n v) (d - 1) hz hb
      omega
    · have he := ((kernel_iff_lower p m n d v).mp hk).2
      intro u
      have hh := Int.dvd_neg.mpr (he u)
      simpa [Int.neg_sub] using hh

end Programme.«20261104-1627-proof-complexity».MatchingLabels
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.extract_top
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.lower_degree_iff_kernel
