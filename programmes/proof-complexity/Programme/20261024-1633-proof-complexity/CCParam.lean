import Programme.«20261024-1633-proof-complexity».CCLower

/-!
# Parameter choice for the clique–colouring approximation bound

From `cc_lower` (K25) with `p = 2ℓ`, `B ≤ (2ℓ²)^ℓ` (the Erdős–Rado value `ℓ!(2ℓ-1)^ℓ` satisfies
this), `q = k-1 ≥ 64ℓ⁴`, `m ≥ 64ℓ⁴k + ℓ`, the positive ratio `|Ks|/c₁ ≥ ((m-ℓ)/k)^{ℓ+1}` (pr's `pos_ratio`) and the negative
masses `c₂ = C^{2ℓ}q^{m-2ℓ}`, `N₀ = q^m - C q^{m-1}` with `C ≤ ℓ²`, `2C ≤ q`:
every bounded tree-like CP refutation of `CC m k` has `2^{4ℓ} ≤ 18 s (2k+6) (W+1)²`.
This is the known Bonet–Pitassi–Raz 1997 bound (bounded coefficients), `2^{Ω(k^{1/4})}`.
-/

namespace Programme.«20261024-1633-proof-complexity».CCParam

open Programme.«20261024-1633-proof-complexity».RealApprox Programme.«20261024-1633-proof-complexity».Pluck Programme.«20261024-1633-proof-complexity».CP Programme.«20261024-1633-proof-complexity».CPRange Programme.«20261024-1633-proof-complexity».CliqueColour Programme.«20261024-1633-proof-complexity».CCApprox Programme.«20261024-1633-proof-complexity».CCLower

theorem cancel_left {a b c : Nat} (hc : 0 < c) (h : c * a ≤ c * b) : a ≤ b :=
  Nat.le_of_mul_le_mul_left h hc

/-- Negative side: `q^m ≤ C q^{m-1} + L C^p q^{m-p}` with `2C ≤ q` gives `q^p ≤ 2 L C^p`. -/
theorem neg_arith (q C p m L : Nat) (hq : 0 < q) (h2C : 2 * C ≤ q) (hp : 1 ≤ p) (hpm : p ≤ m)
    (h : q ^ m ≤ C * q ^ (m - 1) + L * (C ^ p * q ^ (m - p))) : q ^ p ≤ 2 * L * C ^ p := by
  have e1 : q ^ m = q ^ (m - 1) * q := by
    rw [← Nat.pow_succ]; congr 1; omega
  have e2 : q ^ m = q ^ p * q ^ (m - p) := by
    rw [← Nat.pow_add]; congr 1; omega
  have h1 : 2 * (C * q ^ (m - 1)) ≤ q ^ m := by
    rw [e1, ← Nat.mul_assoc, Nat.mul_comm (2 * C), ]
    exact Nat.mul_le_mul_left _ h2C
  have h2 : q ^ m ≤ 2 * L * C ^ p * q ^ (m - p) := by
    have : 2 * q ^ m ≤ q ^ m + 2 * (L * (C ^ p * q ^ (m - p))) := by omega
    have e : 2 * (L * (C ^ p * q ^ (m - p))) = 2 * L * C ^ p * q ^ (m - p) := by
      simp only [Nat.mul_assoc]
    omega
  rw [e2] at h2
  have hpos : 0 < q ^ (m - p) := Nat.pow_pos hq
  exact Nat.le_of_mul_le_mul_right h2 hpos

/-- `(2WB+1)^2 ≤ 9 (W+1)^2 B^2` for `B ≥ 1`. -/
theorem gate_bound (W B : Nat) (hB : 1 ≤ B) : (2 * W * B + 1) ^ 2 ≤ 9 * ((W + 1) ^ 2 * B ^ 2) := by
  have : 2 * W * B + 1 ≤ 3 * ((W + 1) * B) := by
    have : 1 ≤ (W + 1) * B := by simpa using Nat.mul_le_mul (show 1 ≤ W + 1 by omega) hB
    have e : 3 * ((W + 1) * B) = 2 * W * B + (W * B + 3 * B) := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_assoc]; omega
    have : 1 ≤ W * B + 3 * B := by omega
    omega
  have := Nat.pow_le_pow_left this 2
  rw [Nat.mul_pow, Nat.mul_pow] at this
  simpa using this

theorem pow4 (ℓ : Nat) : (64 * ℓ ^ 4) ^ ℓ = 16 ^ ℓ * (2 * ℓ * ℓ) ^ (2 * ℓ) := by
  have e : (2 * ℓ * ℓ) ^ (2 * ℓ) = (4 * ℓ ^ 4) ^ ℓ := by
    rw [Nat.pow_mul]
    congr 1
    rw [Nat.mul_pow, Nat.mul_pow, Nat.mul_assoc, ← Nat.pow_add]
  rw [e, ← Nat.mul_pow]; congr 1; omega

/-- Main arithmetic: with `T = s (2k+6) (W+1)^2`, `L = s (2k+6) (2WB+1)^2`, either disjunct of
`cc_lower` under the stated parameters gives `2^{4ℓ} ≤ 18 T`. -/
theorem param_arith (m M k ℓ B s W Ks c₁ C : Nat) (hℓ : 2 ≤ ℓ) (hB1 : 1 ≤ B)
    (hB : B ≤ (2 * ℓ * ℓ) ^ ℓ) (hk : 64 * ℓ ^ 4 ≤ k - 1) (hm : 64 * ℓ ^ 4 * k ≤ M) (hMm : M ≤ m)
    (hc1 : 1 ≤ c₁) (hratio : c₁ * M ^ (ℓ + 1) ≤ Ks * k ^ (ℓ + 1)) (hC : C ≤ ℓ * ℓ)
    (hcase : Ks ≤ s * (2 * k + 6) * (2 * W * B + 1) ^ 2 * c₁ ∨
      (k - 1) ^ m - C * (k - 1) ^ (m - 1) ≤
        s * (2 * k + 6) * (2 * W * B + 1) ^ 2 * (C ^ (2 * ℓ) * (k - 1) ^ (m - 2 * ℓ))) :
    2 ^ (4 * ℓ) ≤ 18 * (s * (2 * k + 6) * (W + 1) ^ 2) := by
  generalize hT : s * (2 * k + 6) * (W + 1) ^ 2 = T
  generalize hL : s * (2 * k + 6) * (2 * W * B + 1) ^ 2 = L at hcase
  generalize hY : (2 * ℓ * ℓ) ^ (2 * ℓ) = Y
  have hLT : L ≤ 9 * T * Y := by
    rw [← hL, ← hT, ← hY]
    have hB2 : B ^ 2 ≤ (2 * ℓ * ℓ) ^ (2 * ℓ) := by
      rw [show (2 * ℓ * ℓ) ^ (2 * ℓ) = ((2 * ℓ * ℓ) ^ ℓ) ^ 2 by rw [← Nat.pow_mul, Nat.mul_comm ℓ 2]]
      exact Nat.pow_le_pow_left hB 2
    have := Nat.mul_le_mul_left (s * (2 * k + 6)) (Nat.le_trans (gate_bound W B hB1)
      (Nat.mul_le_mul_left 9 (Nat.mul_le_mul_left ((W + 1) ^ 2) hB2)))
    refine Nat.le_trans this (Nat.le_of_eq ?_)
    simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have hYpos : 0 < Y := by rw [← hY]; exact Nat.pow_pos (by
    have : 0 < 2 * ℓ := by omega
    exact Nat.mul_pos this (by omega))
  have h16 : 2 ^ (4 * ℓ) = 16 ^ ℓ := by rw [Nat.pow_mul]
  have hX := pow4 ℓ
  rw [hY] at hX
  have hl4 : 1 ≤ ℓ ^ 4 := Nat.pow_pos (by omega)
  have hk1 : 1 ≤ k := by omega
  rcases hcase with hA | hNeg
  · -- positive side: (64ℓ⁴)^{ℓ+1} ≤ L
    have h1 : c₁ * ((64 * ℓ ^ 4) ^ (ℓ + 1) * k ^ (ℓ + 1)) ≤ c₁ * (L * k ^ (ℓ + 1)) := by
      have a : (64 * ℓ ^ 4) ^ (ℓ + 1) * k ^ (ℓ + 1) ≤ M ^ (ℓ + 1) := by
        rw [← Nat.mul_pow]; exact Nat.pow_le_pow_left hm _
      have b : Ks * k ^ (ℓ + 1) ≤ L * c₁ * k ^ (ℓ + 1) := Nat.mul_le_mul_right _ hA
      have := Nat.le_trans (Nat.mul_le_mul_left c₁ a) (Nat.le_trans hratio b)
      refine Nat.le_trans this (Nat.le_of_eq ?_)
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have h2 := cancel_left (by omega) h1
    have h3 := Nat.le_of_mul_le_mul_right h2 (Nat.pow_pos hk1)
    -- (64ℓ⁴)^{ℓ+1} = 64ℓ⁴ · 16^ℓ · Y ≥ 16^ℓ · Y
    rw [Nat.pow_succ, hX] at h3
    have h4 : 16 ^ ℓ * Y * 1 ≤ L := Nat.le_trans (Nat.mul_le_mul_left _ (by omega)) h3
    have h5 : Y * 16 ^ ℓ ≤ Y * (9 * T) := by
      rw [Nat.mul_one] at h4
      have := Nat.le_trans h4 hLT
      refine Nat.le_trans (Nat.le_of_eq (Nat.mul_comm _ _)) (Nat.le_trans this (Nat.le_of_eq ?_))
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have := cancel_left hYpos h5
    omega
  · -- negative side: q^{2ℓ} ≤ 2 L C^{2ℓ}
    have hq : 0 < k - 1 := by omega
    have h2C : 2 * C ≤ k - 1 := by
      have : ℓ * ℓ ≤ ℓ ^ 4 := by
        have : ℓ ^ 4 = (ℓ * ℓ) * (ℓ * ℓ) := by simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.mul_assoc]
        rw [this]; exact Nat.le_mul_of_pos_right _ (Nat.mul_pos (by omega) (by omega))
      omega
    have hm2 : 2 * ℓ ≤ m := by
      have : k ≤ 64 * ℓ ^ 4 * k := Nat.le_mul_of_pos_left _ (by omega)
      have : ℓ ≤ ℓ ^ 4 := by
        have := Nat.pow_le_pow_right (show 1 ≤ ℓ by omega) (show 1 ≤ 4 by omega)
        simpa using this
      omega
    have h1 := neg_arith (k - 1) C (2 * ℓ) m L hq h2C (by omega) hm2 (by omega)
    -- (64ℓ⁴)^{2ℓ} ≤ q^{2ℓ} ≤ 2 L C^{2ℓ} ≤ 2 L ℓ^{4ℓ}
    have hCp : C ^ (2 * ℓ) ≤ (ℓ * ℓ) ^ (2 * ℓ) := Nat.pow_le_pow_left hC _
    have hqX : (64 * ℓ ^ 4) ^ (2 * ℓ) ≤ (k - 1) ^ (2 * ℓ) := Nat.pow_le_pow_left hk _
    -- (64ℓ⁴)^{2ℓ} = 16^ℓ · 16^ℓ · Y · Y / ... use (64ℓ⁴)^{2ℓ} = ((64ℓ⁴)^ℓ)^2
    have e : (64 * ℓ ^ 4) ^ (2 * ℓ) = (16 ^ ℓ * Y) * (16 ^ ℓ * Y) := by
      rw [Nat.mul_comm 2 ℓ, Nat.pow_mul, hX, Nat.pow_two]
    have hZ : (ℓ * ℓ) ^ (2 * ℓ) ≤ Y := by
      rw [← hY]; apply Nat.pow_le_pow_left
      exact Nat.mul_le_mul_right _ (by omega)
    have h2 : (16 ^ ℓ * Y) * (16 ^ ℓ * Y) ≤ 2 * (9 * T * Y) * Y := by
      rw [← e]
      refine Nat.le_trans hqX (Nat.le_trans h1 ?_)
      exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 hLT) (Nat.le_trans hCp hZ)
    have h3 : (Y * Y) * (16 ^ ℓ * 16 ^ ℓ) ≤ (Y * Y) * (18 * T) := by
      refine Nat.le_trans (Nat.le_of_eq ?_) (Nat.le_trans h2 (Nat.le_of_eq ?_))
      · simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      · simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have h4 := cancel_left (Nat.mul_pos hYpos hYpos) h3
    have : 16 ^ ℓ ≤ 16 ^ ℓ * 16 ^ ℓ := Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega))
    omega

/-- The parametrised bound: under `cc_lower`'s counting hypotheses with `p = 2ℓ`,
`c₂ = C^{2ℓ}(k-1)^{m-2ℓ}`, `N₀ = (k-1)^m - C(k-1)^{m-1}`, every bounded tree-like CP
refutation of `CC m k` has `2^{4ℓ} ≤ 18 s (2k+6) (W+1)^2`. -/
theorem cc_param (m k ℓ B : Nat) (hℓ : 2 ≤ ℓ) (hB1 : 1 ≤ B) (hB : B ≤ (2 * ℓ * ℓ) ^ ℓ)
    (hSF : SF (2 * ℓ) ℓ B) (hk : 64 * ℓ ^ 4 ≤ k - 1) (hm : 64 * ℓ ^ 4 * k + ℓ ≤ m)
    (Rf : BRefutation (CC m k))
    (Ks : List (List Nat)) (hKs : ∀ K ∈ Ks, K.Nodup ∧ K.length = k ∧ ∀ x ∈ K, x < m) (c₁ : Nat)
    (hc1 : 1 ≤ c₁) (hratio : c₁ * (m - ℓ) ^ (ℓ + 1) ≤ Ks.length * k ^ (ℓ + 1))
    (hpos : ∀ Ts : List (List Nat), (∀ T ∈ Ts, T.Nodup ∧ (∀ i ∈ T, i < m) ∧ ℓ + 1 ≤ T.length) →
      (Ks.filter fun K => Ts.any fun T => T.all fun i => decide (i ∈ K)).length ≤ Ts.length * c₁)
    (μ : ((Nat → Nat) → Nat) → Nat)
    (hmono : ∀ f g : (Nat → Nat) → Nat, (∀ c, f c ≤ g c) → μ f ≤ μ g)
    (hadd : ∀ f g : (Nat → Nat) → Nat, μ (fun c => f c + g c) ≤ μ f + μ g)
    (hzero : μ (fun _ => 0) = 0) (C : Nat) (hC : C ≤ ℓ * ℓ)
    (hneg : ∀ ev, Ev (2 * ℓ) ℓ m ev → μ (hit ev) ≤ C ^ (2 * ℓ) * (k - 1) ^ (m - 2 * ℓ))
    (hrb : ∀ S : List Nat, S.Nodup → S.length ≤ ℓ → (∀ x ∈ S, x < m) →
      (k - 1) ^ m - C * (k - 1) ^ (m - 1) ≤ μ (rbw m k S)) :
    2 ^ (4 * ℓ) ≤ 18 * (Rf.size * (2 * k + 6) * (Rf.W.toNat + 1) ^ 2) :=
  param_arith m (m - ℓ) k ℓ B Rf.size Rf.W.toNat Ks.length c₁ C hℓ hB1 hB hk (by omega) (by omega)
    hc1 hratio hC
    (cc_lower m k (2 * ℓ) ℓ B (by omega) hℓ hB1 hSF Rf Ks hKs c₁ hpos μ hmono hadd hzero _ _ hneg hrb)

end Programme.«20261024-1633-proof-complexity».CCParam
