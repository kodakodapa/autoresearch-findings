import Programme.«20261026-1402-proof-complexity».Ext1
import Programme.«20261025-0459-proof-complexity».OntoLucas

/-!
# Exact PC degree 3 over `Z/3` for onto-FPHP when `3 ∥ k`

For `k = 3c` with `3 ∤ c` and every `n ≥ 3`: `ontoFPHP n k` has a degree-`D` `PPCRefutation 3` iff
`D ≥ 3`. Lower bound: `Work.Ext1.no_deg2`. Upper bound: the library's binomial refutation
`OntoLucas.ontoFPHP_upper` at `t = 3`, since `C(n+3c,3) - C(n,3) ≡ c` mod 3 is a unit.
-/

namespace Programme.«20261026-1402-proof-complexity».Ext1Exact

open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-0459-proof-complexity».OntoLucas (bin bin3 ontoFPHP_upper)

theorem bin_step (n : Nat) : ∀ c : Nat, ∃ Q : Int, ((bin (n + 3 * c) 3 : Nat) : Int) - (bin n 3 : Nat) = c + 3 * Q := by
  intro c
  induction c with
  | zero => exact ⟨0, by simp⟩
  | succ c ih =>
    obtain ⟨Q, hQ⟩ := ih
    refine ⟨Q + bin (n + 3 * c) 2 + bin (n + 3 * c) 1, ?_⟩
    rw [show n + 3 * (c + 1) = (n + 3 * c) + 3 by omega, bin3]
    push_cast; omega

theorem unit3 (c : Nat) (hc : ¬ 3 ∣ c) (Q : Int) : (3 : Int) ∣ (c : Int) * ((c : Int) + 3 * Q) - 1 := by
  obtain ⟨m, r, hr, rfl⟩ : ∃ m r, r < 3 ∧ c = 3 * m + r := ⟨c / 3, c % 3, Nat.mod_lt _ (by omega), by omega⟩
  have hr' : r = 1 ∨ r = 2 := by
    rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2) with h | h | h
    · exact absurd ⟨m, by omega⟩ hc
    · exact Or.inl h
    · exact Or.inr h
  rcases hr' with rfl | rfl
  · exact ⟨3 * (m : Int) * m + 2 * m + (3 * m + 1) * Q, by push_cast; grind⟩
  · exact ⟨3 * (m : Int) * m + 4 * m + 1 + (3 * m + 2) * Q, by push_cast; grind⟩

/-- **Exact degree.** For `3 ∤ c` and `n ≥ 3`, onto-FPHP^{n+3c}_n has a degree-`D` `PPCRefutation 3`
iff `3 ≤ D`. -/
theorem f3_exact (c n D : Nat) (hc : ¬ 3 ∣ c) (hn : 3 ≤ n) :
    PPCRefutation 3 (ontoFPHP n (3 * c)) D ↔ 3 ≤ D := by
  constructor
  · intro h
    apply Classical.byContradiction; intro hD
    exact Programme.«20261026-1402-proof-complexity».Ext1.no_deg2 (by decide) (by decide) ⟨c, rfl⟩ n hn
      (Programme.«20261025-0459-proof-complexity».OntoPCLower.PPCDerivable.mono (by omega) h)
  · intro hD
    obtain ⟨Q, hQ⟩ := bin_step n c
    exact Programme.«20261025-0459-proof-complexity».OntoPCLower.PPCDerivable.mono hD
      (ontoFPHP_upper 3 n (3 * c) 3 (by decide) (by omega) ⟨c, by rw [hQ]; exact unit3 c hc Q⟩)

end Programme.«20261026-1402-proof-complexity».Ext1Exact

#print axioms Programme.«20261026-1402-proof-complexity».Ext1Exact.f3_exact
