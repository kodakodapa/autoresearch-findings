import Programme.«20261024-1633-proof-complexity».CliqueColour
import Programme.«20261024-1633-proof-complexity».CPRange

/-!
# Range-bounded interpolants for clique–colouring

`cc_interp` (K15) for tree-like cutting planes in which every line has weight `≤ W`: the monotone
real formula now has every subformula of range at most `2W`, the hypothesis the approximation
method for monotone real formulas needs.
-/

namespace Programme.«20261024-1633-proof-complexity».CCRange

open Programme.«20261024-1110-proof-complexity».Haken (Lit Clause CNF Lit.eval Clause.eval)
open Programme.«20261024-1633-proof-complexity».CP Programme.«20261024-1633-proof-complexity».CPInterp Programme.«20261024-1633-proof-complexity».CPRange Programme.«20261024-1633-proof-complexity».CliqueColour

/-- Every tree-like CP refutation of `CC m k` with `s` nodes and every line of weight `≤ W` yields a
monotone real formula on the graph variables, `≤ s (2k + 6)` gates, every subformula of range
`≤ 2W`, that is `≥ 1` on graphs with a `k`-clique and `≤ 0` on `(k-1)`-colourable graphs. -/
theorem cc_range (m k : Nat) (Rf : BRefutation (CC m k)) :
    ∃ f t, RCR (shared isR isQ) (2 * Rf.W) f t ∧ t ≤ Rf.size * (2 * k + 6) ∧
      (∀ α β : V → Bool, (∀ v, α v = true → β v = true) → f α ≤ f β) ∧
      ∀ β, (HasClique m k β → 1 ≤ f β) ∧ (Colourable m k β → f β ≤ 0) := by
  have hQR : ∀ v, isR v = true → isQ v = false := by intro v; cases v <;> simp [isR, isQ]
  obtain ⟨f, t, r, ht, hmono, hloc, hsep⟩ :=
    interp_range (A m k) (B m k) isR isQ (k + 2) (hwA m k) hQR (hA m k) (hB m k) (hneg m k) Rf
  refine ⟨f, t, r, by omega, hmono, fun β => ⟨fun hc => ?_, fun hc => ?_⟩⟩
  · obtain ⟨β', hag, hsat⟩ := sat_B m k β hc
    rw [← hloc β' β hag]
    have h2 := (hsep β').2
    by_cases h : 1 ≤ f β'
    · exact h
    · exact absurd hsat (h2 (by omega))
  · obtain ⟨β', hag, hsat⟩ := sat_A m k β hc
    rw [← hloc β' β hag]
    have h1 := (hsep β').1
    by_cases h : f β' ≤ 0
    · exact h
    · exact absurd hsat (h1 (by omega))

end Programme.«20261024-1633-proof-complexity».CCRange

