/-!
# Bottleneck lemma for subadditive complexity measures

Abstract core of the Haken / Beame–Pitassi argument: in any derivation (a sequence of
lines, each an axiom or derived from two earlier lines) and any measure `μ` with
`μ ≤ 1` on axioms and `μ line ≤ μ a + μ b` on derived lines, if some line has `μ > t`
(with `t ≥ 1`) then some line has `t < μ ≤ 2 t`.

Stated over line indices, so it applies to any `Refutation` type whose lines are
indexed by `Nat` with parents at smaller indices.
-/

namespace Programme.«20261024-1110-proof-complexity».Bottleneck

/-- Line `i` of a derivation is justified: either an axiom with `μ ≤ 1`, or the
measure is bounded by the sum at two strictly earlier lines. -/
def Subadditive (μ : Nat → Nat) (i : Nat) : Prop :=
  μ i ≤ 1 ∨ ∃ a b, a < i ∧ b < i ∧ μ i ≤ μ a + μ b

theorem below_or_bottleneck (μ : Nat → Nat) (t : Nat) (ht : 1 ≤ t)
    (h : ∀ i, Subadditive μ i) :
    ∀ i, μ i ≤ t ∨ ∃ j, j ≤ i ∧ t < μ j ∧ μ j ≤ 2 * t := by
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
    rcases h i with hax | ⟨a, b, ha, hb, hle⟩
    · exact Or.inl (Nat.le_trans hax ht)
    · rcases ih a ha with ha' | ⟨j, hj, hj1, hj2⟩
      · rcases ih b hb with hb' | ⟨j, hj, hj1, hj2⟩
        · by_cases hc : μ i ≤ t
          · exact Or.inl hc
          · exact Or.inr ⟨i, Nat.le_refl i, Nat.lt_of_not_le hc, by omega⟩
        · exact Or.inr ⟨j, by omega, hj1, hj2⟩
      · exact Or.inr ⟨j, by omega, hj1, hj2⟩

/-- **Bottleneck lemma.** If every line up to `L` is justified (axioms `μ ≤ 1`,
derived lines subadditive over earlier lines) and line `L` has `μ L > t ≥ 1`, then
some line `j ≤ L` has `t < μ j ≤ 2 t`. -/
theorem bottleneck (μ : Nat → Nat) (t L : Nat) (ht : 1 ≤ t)
    (h : ∀ i, i ≤ L → Subadditive μ i) (hL : t < μ L) :
    ∃ j, j ≤ L ∧ t < μ j ∧ μ j ≤ 2 * t := by
  -- truncate the measure beyond `L` so the global hypothesis holds
  let ν : Nat → Nat := fun i => if i ≤ L then μ i else 0
  have hν : ∀ i, Subadditive ν i := by
    intro i
    by_cases hi : i ≤ L
    · rcases h i hi with hax | ⟨a, b, ha, hb, hle⟩
      · exact Or.inl (by simp [ν, hi, hax])
      · refine Or.inr ⟨a, b, ha, hb, ?_⟩
        have ha' : a ≤ L := by omega
        have hb' : b ≤ L := by omega
        simp [ν, hi, ha', hb', hle]
    · exact Or.inl (by simp [ν, hi])
  rcases below_or_bottleneck ν t ht hν L with hle | ⟨j, hj, hj1, hj2⟩
  · have : ν L = μ L := by simp [ν]
    omega
  · have hjL : j ≤ L := hj
    have : ν j = μ j := by simp [ν, hjL]
    exact ⟨j, hj, by omega, by omega⟩

end Programme.«20261024-1110-proof-complexity».Bottleneck
