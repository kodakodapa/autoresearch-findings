import Programme.«20261031-2024-proof-complexity».IterCone

namespace Programme.«20261031-2024-proof-complexity».NativeIter

theorem negative_event {F d} (event : List Lit)
    (hc : forbid event ∈ F) (hd : event.length ≤ d) :
    Cone F d (fun a => -conjunction event a) := by
  have h := equation_event event (-1) hc hd
  simpa only [Rat.neg_mul, Rat.one_mul] using h

/-- Descending elimination uses only addition of certificates. In particular it
never multiplies a derived equation by a word indicator. -/
theorem negative_offdiagonal (n b x v : Nat) (hx : x < n)
    (hv : v < 2^b) (hne : v ≠ x) :
    Cone (cnfAt n b) (2*b) (fun a => -conjunction (word b x v) a) := by
  by_cases hl : v < x
  · exact negative_event _ (low_mem n b x v hx hl) (by simp [word]; omega)
  · by_cases hr : n ≤ v
    · exact negative_event _ (domain_mem n b x v hx hv hr) (by simp [word]; omega)
    · have hxv : x < v := by omega
      apply pair_eliminate b x v (by omega) hv (high_mem n b x v hx (by omega) hxv)
      intro u hu hune
      exact negative_offdiagonal n b v u (by omega) hu hune
termination_by n-x
decreasing_by omega

/-- An all-size native clause-product SA upper bound, including zero-bit words.
The bound counts formal products before Boolean reduction. -/
theorem refutes_cnfAt (n b : Nat) (hn : 0 < n) :
    Refutes (cnfAt n b) (2*b) := by
  have hall : ∀ v ∈ List.range (2^b),
      Cone (cnfAt n b) (2*b) (fun a => -conjunction (word b 0 v) a) := by
    intro v hv
    by_cases hzero : v = 0
    · subst v
      exact negative_event _ (root_mem n b hn) (by simp [word]; omega)
    · exact negative_offdiagonal n b 0 v hn (List.mem_range.mp hv) hzero
  have hs := cone_sum (List.range (2^b)) (fun v a => -conjunction (word b 0 v) a) hall
  have he : (fun a => ((List.range (2^b)).map
      (fun v => -conjunction (word b 0 v) a)).sum) = (fun _ => (-1 : Rat)) := by
    funext a
    rw [sum_neg, word_partition]
  rw [he] at hs
  exact hs

theorem refutes_native_iter (n : Nat) (hn : 2 ≤ n) :
    Refutes (cnf n) (2 * bits n) :=
  refutes_cnfAt n (bits n) (by omega)

#print axioms refutes_cnfAt
#print axioms refutes_native_iter
end Programme.«20261031-2024-proof-complexity».NativeIter
