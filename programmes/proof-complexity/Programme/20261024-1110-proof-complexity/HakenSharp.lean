import Programme.«20261024-1110-proof-complexity».Haken

/-!
# Haken's bound with a sharper constant

Same `Refutation` type and formula as `Work.Haken.haken` (K1); only the parameters fed to
`Work.Haken.haken_param` change: `T = 2⌊n/6⌋` restriction steps, `s = ⌊n/6⌋`, and averaging
ratio `r = 18` (instead of `T = 4⌊n/12⌋`, `r = 72`). Result: every refutation of `PHP n` has at
least `(18/17)^(2⌊n/6⌋) ≈ e^{n/52.5}` clauses, for every `n`.
-/

namespace Programme.«20261024-1110-proof-complexity».HakenSharp

open Programme.«20261024-1110-proof-complexity».Haken

/-- For `n ≥ 1` a refutation of `PHP n` has at least two clauses (`[]` is not an axiom). -/
theorem two_le_length {n : Nat} (hn : 1 ≤ n) (R : Refutation (PHP n)) : 2 ≤ R.steps.length := by
  have h0 : 0 < R.steps.length := List.length_pos_of_mem R.empty_mem
  apply Classical.byContradiction
  intro hlt
  have h1 : R.steps.length = 1 := by omega
  have hmem : R.steps[0]'h0 = [] := by
    obtain ⟨k, hk, hkk⟩ := List.getElem_of_mem R.empty_mem
    have : k = 0 := by omega
    subst this; exact hkk
  rcases R.derived 0 h0 with hax | ⟨a, b, ha, _, _⟩
  · rw [hmem] at hax
    rcases mem_PHP hax with ⟨p, _, hp⟩ | ⟨p, q, h, _, _, _, hp⟩
    · unfold pigeonAx at hp
      have : ((List.range n).map fun h => (⟨(p, h), true⟩ : Lit (Nat × Nat))).length = 0 := by
        rw [← hp]; rfl
      simp at this; omega
    · simp [holeAx] at hp
  · omega

theorem hrK (m j : Nat) (hj : j < 6) (hm : 1 ≤ m) :
    (6 * m + j + 1) * (6 * m + j) ≤ 18 * (m * (2 * m + j + 3)) := by
  have e1 : (6 * m + j + 1) * (6 * m + j) = 36 * (m * m) + 12 * (m * j) + 6 * m + j * j + j := by
    grind
  have e2 : 18 * (m * (2 * m + j + 3)) = 36 * (m * m) + 18 * (m * j) + 54 * m := by grind
  rw [e1, e2]
  have : j * j ≤ 5 * j := Nat.mul_le_mul_right j (by omega)
  have : 1 * m ≤ m * j + m := by omega
  omega

/-- **Haken's theorem, sharper constant**: for every `n`, every resolution refutation of `PHP n`
(`n+1` pigeons, `n` holes; K1's `Refutation` type) with `S` clauses has
`18^(2⌊n/6⌋) ≤ 17^(2⌊n/6⌋) · S`, i.e. `S ≥ (18/17)^(2⌊n/6⌋)`. -/
theorem haken_sharp (n : Nat) (R : Refutation (PHP n)) :
    18 ^ (2 * (n / 6)) ≤ 17 ^ (2 * (n / 6)) * R.steps.length := by
  have hpos : 0 < R.steps.length := List.length_pos_of_mem R.empty_mem
  have hdm : n / 6 * 6 ≤ n := Nat.div_mul_le_self n 6
  have hdm2 : n < (n / 6 + 1) * 6 := by omega
  by_cases h0 : n / 6 = 0
  · rw [h0]; simp; omega
  by_cases h1 : n / 6 = 1
  · rw [h1]
    have := two_le_length (n := n) (by omega) R
    have : 17 ^ 2 * 2 ≤ 17 ^ 2 * R.steps.length := Nat.mul_le_mul_left _ this
    simp at this ⊢; omega
  obtain ⟨j, hj, hn⟩ : ∃ j, j < 6 ∧ n = 6 * (n / 6) + j := ⟨n % 6, Nat.mod_lt _ (by omega), by omega⟩
  generalize n / 6 = m at *
  subst hn
  have hm : 2 ≤ m := by omega
  have hsub : 6 * m + j + 1 - 2 * m - (2 * m - 2) = 2 * m + j + 3 := by omega
  have hKs : m * (2 * m + j + 3) ≤ m * (6 * m + j + 1 - 2 * m - (2 * m - 2)) := by rw [hsub]; exact Nat.le_refl _
  have hK1 : 1 ≤ m * (2 * m + j + 3) := Nat.mul_le_mul (by omega : 1 ≤ m) (by omega : 1 ≤ 2 * m + j + 3)
  have := haken_param (T := 2 * m) (s := m) (K := m * (2 * m + j + 3)) (r := 18) R
    (by omega) (by omega) hKs hK1 (by omega) (hrK m j hj (by omega))
  simpa using this

end Programme.«20261024-1110-proof-complexity».HakenSharp

#print axioms Programme.«20261024-1110-proof-complexity».HakenSharp.haken_sharp
