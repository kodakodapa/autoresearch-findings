import Programme.«20261031-2024-proof-complexity».IterLower

namespace Programme.«20261101-0614-proof-complexity».IterLowerReproof
open Programme.«20261031-2024-proof-complexity».NativeIter

/-- Re-establish the lower half on the canonical cone, using the library's
filtered assignment but directly inducting over a purported certificate. -/
theorem no_refutation_below_native_iter (n d : Nat) (hn : 2 ≤ n)
    (hd : d < 2 * bits n) : ¬ Refutes (cnf n) d := by
  have hs : SatisfiesAt (cnf n) d witness :=
    witness_filtered n (bits n) d hn (native_capacity n hn) hd
  have nonnegative : ∀ {f}, Cone (cnf n) d f → 0 ≤ f witness := by
    intro f hf
    induction hf with
    | positive m hm hlen => exact conjunction_nonneg m witness
    | equation c m r hc had =>
      have hc0 := hs c hc (by have := had.2; omega)
      have hprod := conjunction_append_zero m (falsity c) witness hc0
      change 0 ≤ r * conjunction (m ++ falsity c) witness
      rw [hprod]
      simp
    | zero => exact Rat.le_refl
    | add hf hg ihf ihg => exact Rat.add_nonneg ihf ihg
    | scale r hr hf ih => exact Rat.mul_nonneg hr ih
  intro h
  have absurd : (0 : Rat) ≤ -1 := nonnegative h
  contradiction

#print axioms no_refutation_below_native_iter
end Programme.«20261101-0614-proof-complexity».IterLowerReproof
