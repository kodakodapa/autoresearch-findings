import Programme.«20261024-1110-proof-complexity».Haken
/-!
# Every resolution refutation of `PHP n` contains a clause with a large monotone closure

The monotone closure of a clause `C` (Beame–Pitassi) is the set of pairs `(i, l)`, `i ≤ n`, `l < n`,
with `x_{i,l} ∈ C` or `¬x_{j,l} ∈ C` for some `j ≠ i` (`InV C (i, l)`). We prove that every
refutation of `PHP n` (`n ≥ 1`) contains a clause `C` with `9 · |C⁺| ≥ 2 (n+1)²`.
Proof: the medium-measure lemma (`mid`, or `mid1` for `n ≤ 2`) and the swap count `vsize_ge`
of `Work.Haken`, at the empty restriction.
-/

namespace Programme.«20261024-1110-proof-complexity».Haken

open Classical

/-- `|C⁺|`: the number of pairs `(i, l)`, `i ≤ n`, `l < n`, in the monotone closure of `C`. -/
noncomputable def mclos (n : Nat) (C : Clause (Nat × Nat)) : Nat :=
  (grid n).countP fun v => decide (InV C v)

/-- Variant of `mid` with threshold `s ≥ 1`: some clause has measure in `[s, 2s-1]`. -/
theorem mid1 {n : Nat} (R : Refutation (PHP n)) (M : List (Nat × Nat)) {s : Nat} (hs : 1 ≤ s)
    (hbot : s ≤ mu n M []) : ∃ C ∈ R.steps, s ≤ mu n M C ∧ mu n M C ≤ 2 * s - 1 := by
  have key : ∀ k (hk : k < R.steps.length), s ≤ mu n M R.steps[k] →
      ∃ C ∈ R.steps, s ≤ mu n M C ∧ mu n M C ≤ 2 * s - 1 := by
    intro k
    induction k using Nat.strongRecOn with
    | _ k ih =>
      intro hk hsk
      rcases R.derived k hk with hax | ⟨a, b, ha, hb, hres⟩
      · have := mu_axiom (M := M) hax
        exact ⟨_, List.getElem_mem hk, hsk, by omega⟩
      · by_cases hA : s ≤ mu n M (R.steps[a]'(Nat.lt_trans ha hk))
        · exact ih a ha _ hA
        · by_cases hB : s ≤ mu n M (R.steps[b]'(Nat.lt_trans hb hk))
          · exact ih b hb _ hB
          · have := mu_sub (n := n) (M := M) hres
            exact ⟨_, List.getElem_mem hk, hsk, by omega⟩
  obtain ⟨k, hk, hke⟩ := List.mem_iff_getElem.mp R.empty_mem
  exact key k hk (by rw [hke]; exact hbot)

theorem freeCount_nil (n : Nat) : freeCount n [] = n + 1 := by
  have h1 := freeCount_ge n []
  have h2 : freeCount n [] ≤ n + 1 := by
    unfold freeCount
    exact Nat.le_trans (List.countP_le_length) (by simp)
  simp at h1; omega

theorem vsize_nil (n : Nat) (C : Clause (Nat × Nat)) : vsize n [] C = mclos n C := by
  unfold vsize mclos
  apply List.countP_congr
  intro v _
  simp [FreeP, FreeH]

/-- `(3a ≥ N, 3a ≤ 2N) → 2N² ≤ 9 a (N - a)`. -/
theorem quad {a N : Nat} (h1 : N ≤ 3 * a) (h2 : 3 * a ≤ 2 * N) : 2 * (N * N) ≤ 9 * (a * (N - a)) := by
  obtain ⟨b, rfl⟩ : ∃ b, N = a + b := ⟨N - a, by omega⟩
  rw [Nat.add_sub_cancel_left]
  obtain ⟨x, hx⟩ : ∃ x, x = 2 * a - b := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = 2 * b - a := ⟨_, rfl⟩
  have ha : 3 * a = 2 * x + y := by omega
  have hb : 3 * b = x + 2 * y := by omega
  have hN : a + b = x + y := by omega
  have e1 : 9 * (a * b) = (2 * x + y) * (x + 2 * y) := by
    rw [← ha, ← hb, Nat.mul_mul_mul_comm]
  have e2 : (2 * x + y) * (x + 2 * y) = 2 * ((x + y) * (x + y)) + x * y := by
    have c : y * x = x * y := Nat.mul_comm _ _
    simp only [Nat.two_mul, Nat.add_mul, Nat.mul_add, c]
    omega
  rw [hN, e1, e2]
  exact Nat.le_add_right _ _

/-- Every resolution refutation of `PHP n`, `n ≥ 1`, has a clause `C` with `9 |C⁺| ≥ 2 (n+1)²`. -/
theorem wide_mclos (n : Nat) (hn : 1 ≤ n) (R : Refutation (PHP n)) :
    ∃ C ∈ R.steps, 2 * ((n + 1) * (n + 1)) ≤ 9 * mclos n C := by
  have hbot : mu n [] [] = n + 1 := by rw [mu_empty (good_nil n), freeCount_nil]
  have key : ∀ C, (n + 1) ≤ 3 * mu n [] C → 3 * mu n [] C ≤ 2 * (n + 1) →
      2 * ((n + 1) * (n + 1)) ≤ 9 * mclos n C := by
    intro C h1 h2
    have := vsize_ge (good_nil n) C
    rw [freeCount_nil, vsize_nil] at this
    have := quad h1 h2
    have := Nat.mul_le_mul_left 9 ‹mu n [] C * (n + 1 - mu n [] C) ≤ mclos n C›
    omega
  by_cases h3 : 3 ≤ n
  · obtain ⟨C, hC, h1, h2⟩ := mid R [] (s := (n + 3) / 3) (by omega) (by rw [hbot]; omega)
    exact ⟨C, hC, key C (by omega) (by omega)⟩
  · obtain ⟨C, hC, h1, h2⟩ := mid1 R [] (s := 1) (Nat.le_refl _) (by rw [hbot]; omega)
    exact ⟨C, hC, key C (by omega) (by omega)⟩

end Programme.«20261024-1110-proof-complexity».Haken

#print axioms Programme.«20261024-1110-proof-complexity».Haken.wide_mclos
