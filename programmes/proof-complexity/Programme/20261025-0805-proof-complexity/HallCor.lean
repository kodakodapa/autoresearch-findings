import Programme.«20261025-0805-proof-complexity».MPluck
import Programme.«20261025-0805-proof-complexity».PermCount

/-!
# Explicit form of the Hall-formula CP lower bound (pr, round 13)

`hall_cor` is pure arithmetic: its hypothesis is the conclusion of `Work.HallCP.hall_cp`
(K17) at `p = t (2^ℓ - 1)` with `t = (ℓ+1)(log₂ n + 1)`; it eliminates the disjunction and
bounds `thr p ℓ`, giving an explicit lower bound on the number of lines `s`.
-/

namespace Programme.«20261025-0805-proof-complexity».HallCor

open Programme.«20261025-0805-proof-complexity».MPluck (thr)

/-- `(a-b)^b (a-b)! ≤ a!`. -/
theorem pow_fact_le : ∀ (b a : Nat), b ≤ a →
    (a - b) ^ b * Programme.«20261025-0805-proof-complexity».PermCount.fact (a - b) ≤ Programme.«20261025-0805-proof-complexity».PermCount.fact a
  | 0, a, _ => by simp
  | b + 1, a, h => by
    obtain ⟨c, rfl⟩ : ∃ c, a = c + 1 := ⟨a - 1, by omega⟩
    have ih := pow_fact_le b c (by omega)
    have e : c + 1 - (b + 1) = c - b := by omega
    rw [e, Nat.pow_succ]
    show (c - b) ^ b * (c - b) * Programme.«20261025-0805-proof-complexity».PermCount.fact (c - b) ≤ (c + 1) * Programme.«20261025-0805-proof-complexity».PermCount.fact c
    calc (c - b) ^ b * (c - b) * Programme.«20261025-0805-proof-complexity».PermCount.fact (c - b)
        = (c - b) * ((c - b) ^ b * Programme.«20261025-0805-proof-complexity».PermCount.fact (c - b)) := by
          rw [Nat.mul_comm ((c - b) ^ b) (c - b), Nat.mul_assoc]
      _ ≤ (c + 1) * Programme.«20261025-0805-proof-complexity».PermCount.fact c :=
          Nat.mul_le_mul (by omega) ih

theorem pfact_pos : ∀ n, 0 < Programme.«20261025-0805-proof-complexity».PermCount.fact n
  | 0 => by decide
  | n + 1 => Nat.mul_pos (Nat.succ_pos n) (pfact_pos n)

theorem sfact_le : ∀ a, Programme.«20261024-1633-proof-complexity».Sunflower.fact a ≤ a ^ a
  | 0 => by decide
  | a + 1 => by
    show (a + 1) * Programme.«20261024-1633-proof-complexity».Sunflower.fact a ≤ (a + 1) ^ (a + 1)
    rw [Nat.pow_succ, Nat.mul_comm ((a+1)^a)]
    exact Nat.mul_le_mul_left _ (Nat.le_trans (sfact_le a) (Nat.pow_le_pow_left (by omega) a))

/-- `M^k (M+k) ≤ (M+1)^k M`. -/
theorem bern (M : Nat) : ∀ k, M ^ k * (M + k) ≤ (M + 1) ^ k * M
  | 0 => by simp
  | k + 1 => by
    have ih := bern M k
    calc M ^ (k + 1) * (M + (k + 1)) = M * (M ^ k * (M + k)) + M ^ k * M := by
            rw [Nat.pow_succ, ← Nat.add_assoc, Nat.mul_add, Nat.mul_one, Nat.mul_comm M (M ^ k * _),
              Nat.mul_assoc, Nat.mul_assoc, Nat.mul_comm (M + k) M]
      _ ≤ M * ((M + 1) ^ k * M) + (M + 1) ^ k * M :=
            Nat.add_le_add (Nat.mul_le_mul_left _ ih)
              (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) k))
      _ = (M + 1) ^ (k + 1) * M := by
            rw [Nat.pow_succ, Nat.mul_comm ((M + 1) ^ k) (M + 1), Nat.mul_assoc, Nat.add_mul, Nat.one_mul]

/-- `2^t (2^ℓ-1)^{t(2^ℓ-1)} ≤ 2^{ℓ t (2^ℓ-1)}`. -/
theorem two_pow_gain (ℓ t : Nat) (hℓ : 1 ≤ ℓ) :
    2 ^ t * (2 ^ ℓ - 1) ^ (t * (2 ^ ℓ - 1)) ≤ 2 ^ (ℓ * (t * (2 ^ ℓ - 1))) := by
  have h2 : 2 ≤ 2 ^ ℓ := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by decide) hℓ
  generalize hM : 2 ^ ℓ - 1 = M
  have hM1 : 1 ≤ M := by omega
  have hN : 2 ^ ℓ = M + 1 := by omega
  have hb := bern M M
  have hb2 : 2 * M ^ M ≤ (M + 1) ^ M := by
    have : M ^ M * (M + M) = (2 * M ^ M) * M := by
      rw [← Nat.two_mul, Nat.mul_comm 2 (M ^ M), Nat.mul_assoc]
    rw [this] at hb
    exact Nat.le_of_mul_le_mul_right hb (by omega)
  calc 2 ^ t * M ^ (t * M) = (2 * M ^ M) ^ t := by
          rw [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_comm M t]
    _ ≤ ((M + 1) ^ M) ^ t := Nat.pow_le_pow_left hb2 t
    _ = 2 ^ (ℓ * (t * M)) := by
          rw [← Nat.pow_mul, Nat.pow_mul 2 ℓ, hN, Nat.mul_comm M t]

/-- The disjunction of K17 at `p = t (2^ℓ-1)`, `t = (ℓ+1)(log₂ n+1)`, collapses to
`(n-ℓ)^{ℓ+1} ≤ 2^{4ℓ+3} E`. -/
theorem hall_cor0 (n ℓ E : Nat) (hℓ : 1 ≤ ℓ) (hℓn : ℓ < n)
    (h : Programme.«20261025-0805-proof-complexity».PermCount.fact n ≤ E * Programme.«20261025-0805-proof-complexity».PermCount.fact (n - (ℓ + 1)) ∨
      2 ^ (ℓ * ((ℓ + 1) * (n.log2 + 1) * (2 ^ ℓ - 1))) ≤
        2 ^ (4 * ℓ + 3) * E * (2 ^ ℓ - 1) ^ ((ℓ + 1) * (n.log2 + 1) * (2 ^ ℓ - 1))) :
    (n - ℓ) ^ (ℓ + 1) ≤ 2 ^ (4 * ℓ + 3) * E := by
  rcases h with h | h
  · have h1 := pow_fact_le (ℓ + 1) n (by omega)
    have h2 : (n - (ℓ + 1)) ^ (ℓ + 1) * Programme.«20261025-0805-proof-complexity».PermCount.fact (n - (ℓ + 1)) ≤
        E * Programme.«20261025-0805-proof-complexity».PermCount.fact (n - (ℓ + 1)) := Nat.le_trans h1 h
    have h3 := Nat.le_of_mul_le_mul_right h2 (pfact_pos _)
    -- `(n-ℓ)^{ℓ+1} ≤ 2^{ℓ+1} (n-ℓ-1)^{ℓ+1}` since `n-ℓ ≤ 2(n-ℓ-1)` or `n-ℓ = 1`
    by_cases he : n - ℓ = 1
    · rw [he, Nat.one_pow]
      have : 0 < E := by
        rcases Nat.eq_zero_or_pos E with h0 | h0
        · rw [h0, Nat.zero_mul] at h; exact absurd h (Nat.not_le.2 (pfact_pos n))
        · exact h0
      exact Nat.le_trans this (Nat.le_mul_of_pos_left _ (Nat.pow_pos (by decide)))
    · have hle : n - ℓ ≤ 2 * (n - (ℓ + 1)) := by omega
      calc (n - ℓ) ^ (ℓ + 1) ≤ (2 * (n - (ℓ + 1))) ^ (ℓ + 1) := Nat.pow_le_pow_left hle _
        _ = 2 ^ (ℓ + 1) * (n - (ℓ + 1)) ^ (ℓ + 1) := Nat.mul_pow _ _ _
        _ ≤ 2 ^ (4 * ℓ + 3) * E :=
            Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) (by omega)) h3
  · generalize ht : (ℓ + 1) * (n.log2 + 1) = t at h
    have hg := two_pow_gain ℓ t hℓ
    have hpos : 0 < (2 ^ ℓ - 1) ^ (t * (2 ^ ℓ - 1)) := by
      apply Nat.pow_pos
      have : 2 ^ 1 ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by decide) hℓ
      rw [Nat.pow_one] at this; omega
    have h4 : 2 ^ t ≤ 2 ^ (4 * ℓ + 3) * E :=
      Nat.le_of_mul_le_mul_right (Nat.le_trans hg h) hpos
    calc (n - ℓ) ^ (ℓ + 1) ≤ n ^ (ℓ + 1) := Nat.pow_le_pow_left (by omega) _
      _ ≤ (2 ^ (n.log2 + 1)) ^ (ℓ + 1) := Nat.pow_le_pow_left (Nat.le_of_lt Nat.lt_log2_self) _
      _ = 2 ^ t := by rw [← Nat.pow_mul, ← ht, Nat.mul_comm]
      _ ≤ _ := h4

theorem thr_le (p ℓ : Nat) (hp : 1 ≤ p) :
    thr p ℓ + 1 ≤ 2 * ((3 * ℓ) ^ (3 * ℓ) * (p * (2 * ℓ + 1) ^ (2 * ℓ)) ^ (3 * ℓ)) := by
  have h1 : thr p ℓ ≤ (3 * ℓ) ^ (3 * ℓ) * (p * (2 * ℓ + 1) ^ (2 * ℓ)) ^ (3 * ℓ) :=
    Nat.mul_le_mul_right _ (sfact_le _)
  have h2 : 1 ≤ thr p ℓ := Nat.mul_pos
    (Programme.«20261024-1633-proof-complexity».Sunflower.fact_pos _)
    (Nat.pow_pos (Nat.mul_pos hp (Nat.pow_pos (by omega))))
  omega

/-- Explicit form: hypothesis = conclusion of K17 (`hall_cp`) at `p = t(2^ℓ-1)`,
`t = (ℓ+1)(log₂ n + 1)`. -/
theorem hall_cor (n ℓ s : Nat) (hℓ : 1 ≤ ℓ) (hℓn : ℓ < n)
    (h : Programme.«20261025-0805-proof-complexity».PermCount.fact n ≤ s * (2 * n + 7) *
        (ℓ * (thr ((ℓ + 1) * (n.log2 + 1) * (2 ^ ℓ - 1)) ℓ + 1) ^ 2) *
        Programme.«20261025-0805-proof-complexity».PermCount.fact (n - (ℓ + 1)) ∨
      2 ^ (ℓ * ((ℓ + 1) * (n.log2 + 1) * (2 ^ ℓ - 1))) ≤ 2 ^ (4 * ℓ + 3) *
        (s * (2 * n + 7) * (ℓ * (thr ((ℓ + 1) * (n.log2 + 1) * (2 ^ ℓ - 1)) ℓ + 1) ^ 2)) *
        (2 ^ ℓ - 1) ^ ((ℓ + 1) * (n.log2 + 1) * (2 ^ ℓ - 1))) :
    (n - ℓ) ^ (ℓ + 1) ≤ 2 ^ (4 * ℓ + 5) * s * (2 * n + 7) * ℓ *
      ((3 * ℓ) ^ (3 * ℓ) * ((ℓ + 1) * (n.log2 + 1) * 2 ^ ℓ * (2 * ℓ + 1) ^ (2 * ℓ)) ^ (3 * ℓ)) ^ 2 := by
  have h0 := hall_cor0 n ℓ _ hℓ hℓn h
  generalize hp : (ℓ + 1) * (n.log2 + 1) * (2 ^ ℓ - 1) = p at h0
  have hp1 : 1 ≤ p := by
    rw [← hp]
    have : 2 ^ 1 ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by decide) hℓ
    rw [Nat.pow_one] at this
    exact Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  have hpq : p ≤ (ℓ + 1) * (n.log2 + 1) * 2 ^ ℓ := by rw [← hp]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have ht := thr_le p ℓ hp1
  have hX : (3 * ℓ) ^ (3 * ℓ) * (p * (2 * ℓ + 1) ^ (2 * ℓ)) ^ (3 * ℓ) ≤
      (3 * ℓ) ^ (3 * ℓ) * ((ℓ + 1) * (n.log2 + 1) * 2 ^ ℓ * (2 * ℓ + 1) ^ (2 * ℓ)) ^ (3 * ℓ) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.mul_le_mul_right _ hpq) _)
  generalize (3 * ℓ) ^ (3 * ℓ) * ((ℓ + 1) * (n.log2 + 1) * 2 ^ ℓ * (2 * ℓ + 1) ^ (2 * ℓ)) ^ (3 * ℓ) = Y at hX ⊢
  have hT : (thr p ℓ + 1) ^ 2 ≤ 4 * Y ^ 2 := by
    calc (thr p ℓ + 1) ^ 2 ≤ (2 * Y) ^ 2 := Nat.pow_le_pow_left (Nat.le_trans ht (by omega)) 2
      _ = 4 * Y ^ 2 := by rw [Nat.mul_pow]
  calc (n - ℓ) ^ (ℓ + 1) ≤ 2 ^ (4 * ℓ + 3) * (s * (2 * n + 7) * (ℓ * (thr p ℓ + 1) ^ 2)) := h0
    _ ≤ 2 ^ (4 * ℓ + 3) * (s * (2 * n + 7) * (ℓ * (4 * Y ^ 2))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hT))
    _ = 2 ^ (4 * ℓ + 5) * s * (2 * n + 7) * ℓ * Y ^ 2 := by
        rw [show 2 ^ (4 * ℓ + 5) = 2 ^ (4 * ℓ + 3) * 4 by
          rw [show 4 * ℓ + 5 = (4 * ℓ + 3) + 2 by omega, Nat.pow_add]]
        generalize 2 ^ (4 * ℓ + 3) = A
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

end Programme.«20261025-0805-proof-complexity».HallCor

#print axioms Programme.«20261025-0805-proof-complexity».HallCor.hall_cor
