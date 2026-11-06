import Programme.«20261101-0614-proof-complexity».SingletonEquations

namespace Programme.«20261101-0614-proof-complexity».SingletonAssemble
open Programme.«20261031-2024-proof-complexity».NativeIter
open Programme.«20261101-0614-proof-complexity».SingletonData Programme.«20261101-0614-proof-complexity».SignedDual

noncomputable def dual (hp : ∀ m ∈ FiniteWords.words (FiniteWords.alphabet vars) 3,
    0 ≤ score weights m) : ConeDual.Certificate (Singleton.cnf 2 3) 3 :=
  certificate vars samples SingletonSupport.supported SingletonSupport.normalized
    SingletonSupport.cnf_supported
    (by
      intro m hm hd
      rw [samples, eval_score]
      apply Rat.mul_nonneg
      · exact Rat.intCast_nonneg.mpr
          (hp m (FiniteWords.supported_mem_words hm hd))
      · decide +kernel)
    (by
      intro c hc m hm hd
      rw [samples, eval_score]
      have he := SingletonEquations.equations c hc m
        (FiniteWords.supported_mem_words hm (by omega))
      rw [he]
      simp)

#print axioms dual
end Programme.«20261101-0614-proof-complexity».SingletonAssemble
