import Programme.«20261025-0459b-proof-complexity».VApprox
import Programme.«20261024-1633-proof-complexity».CCCount
import Programme.«20261024-1633-proof-complexity».CCArith
import Programme.«20261024-1633-proof-complexity».CCAssembly

/-!
# Tree-like cutting planes for clique–colouring, arbitrary coefficients, `2^{Ω(m^{1/4})}`

Counting (M6) and assembly (M7) on top of `Work.VApprox.cc_vapprox` (M5).

* `neg_count`: if every colouring making `S` rainbow (`|S| ≤ 2L`) fits a merge list of `Er`
  (each `Valid`, length `L`), then `q^m ≤ |Er| q^(m-L) + C(2L,2) q^(m-1)` (library `choice_term`,
  `rb_count`).
* `cc_val`: for `L ≥ 1`, `32L² ≤ k-1`, `8L²k + L ≤ m`, every tree-like CP refutation
  `Refutation (CC m k)` (integer coefficients of any size) with `s` nodes has `2^(L-1) ≤ s(2k+5)`.
-/

namespace Programme.«20261025-0459b-proof-complexity».CCVal

open Programme.«20261025-0459b-proof-complexity».VSwitch
open Programme.«20261024-1633-proof-complexity».KSub (ch)
open Programme.«20261024-1633-proof-complexity».Colour (tot tot_sum tot_one ind choice_term ch2
  le_sum_of_mem)
open Programme.«20261024-1633-proof-complexity».CP (Refutation)
open Programme.«20261024-1633-proof-complexity».CliqueColour (CC)

theorem ch2_le : ∀ n, ch2 n ≤ n * n
  | 0 => Nat.le_refl _
  | n+1 => by
    have := ch2_le n
    show ch2 n + n ≤ (n+1) * (n+1)
    rw [Nat.add_mul, Nat.mul_add]; omega

/-- Colouring side of the count. -/
theorem neg_count (q m L : Nat) (hq : 0 < q) (S : List Nat) (hS : S.Nodup)
    (hSl : S.length ≤ 2 * L) (hSm : ∀ x ∈ S, x < m) (Er : List (List (Nat × Nat)))
    (hEr : ∀ τ ∈ Er, Valid τ ∧ (∀ e ∈ τ, e.1 < m ∧ e.2 < m) ∧ τ.length = L)
    (hit : ∀ c : Nat → Nat, (∀ i, i < m → c i < q) → rb c S → ∃ τ ∈ Er, cons c τ) :
    q ^ m ≤ Er.length * q ^ (m - L) + ch2 (2 * L) * q ^ (m - 1) := by
  let c0 : Nat → Nat := fun _ => 0
  let f : (Nat → Nat) → Nat := fun c => (Er.map (fun τ => ind τ c)).sum
  have h := Programme.«20261024-1633-proof-complexity».CCArith.rb_count q (2 * L) m hq S hS hSl
    hSm f (fun c hc hr => by
      obtain ⟨τ, hτ, hct⟩ := hit c hc hr
      have := le_sum_of_mem (fun τ => ind τ c) Er τ hτ
      have h1 : ind τ c = 1 := if_pos hct
      simp only [f]; omega) c0
  have hB : tot q (List.range m) f c0 ≤ Er.length * q ^ (m - L) := by
    simp only [f]
    rw [tot_sum]
    apply Programme.«20261024-1633-proof-complexity».Colour.sum_le
    intro τ hτ
    obtain ⟨⟨hnd, hx⟩, hr, hl⟩ := hEr τ hτ
    have := choice_term q hq (List.range m) List.nodup_range τ
      (fun e he => List.mem_range.mpr (hr e he).1) hnd hx c0
    rwa [List.length_range, hl] at this
  omega

theorem cancel {a b c : Nat} (hc : 0 < c) (h : a * c ≤ b * c) : a ≤ b :=
  Nat.le_of_mul_le_mul_right h hc

/-- Main theorem: tree-like CP, arbitrary coefficients, no weight bound. -/
theorem cc_val (m k L : Nat) (hL : 1 ≤ L) (hk : 32 * L ^ 2 ≤ k - 1) (hm : 8 * L ^ 2 * k + L ≤ m)
    (Rf : Refutation (CC m k)) : 2 ^ (L - 1) ≤ Rf.size * (2 * k + 5) := by
  obtain ⟨A, Er, Ed, hEr, hEd, gEr, gEd, gA, gpos, gneg⟩ := VApprox.cc_vapprox m k L hL Rf
  generalize ht : Rf.size * (2 * k + 5) = t at hEr hEd
  have hL2 : 1 ≤ L ^ 2 := Nat.pow_pos hL
  have hkL : L ≤ k := by
    have : L ≤ L ^ 2 := by rw [Nat.pow_two]; exact Nat.le_mul_of_pos_left _ hL
    omega
  have hkm : k ≤ m := by
    have : k ≤ 8 * L ^ 2 * k := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have e2 : 2 ^ L = 2 * 2 ^ (L - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  by_cases hall : ∀ K : List Nat, K.Nodup → K.length = k → (∀ x ∈ K, x < m) →
      ∃ R ∈ Ed, ∀ x ∈ R, x ∈ K
  · -- clique side: every k-set contains a member of `Ed`
    obtain ⟨l, rfl⟩ : ∃ l, L = l + 1 := ⟨L - 1, by omega⟩
    have h1 := Programme.«20261024-1633-proof-complexity».CCCount.pos_final m k l hkL Ed
      (fun T hT => ⟨(gEd T hT).1, (gEd T hT).2.1, (gEd T hT).2.2⟩) hall
    have h2 := Programme.«20261024-1633-proof-complexity».CCArith.pos_ratio m k l hkL
    have hch : 0 < ch m k :=
      Programme.«20261024-1633-proof-complexity».CCAssembly.ch_pos ch (fun n => by cases n <;> rfl)
        (fun _ _ => rfl) m k hkm
    -- (m-l)^L ≤ |Ed| k^L
    have h3 : (m - l) ^ (l + 1) * ch m k ≤ (Ed.length * k ^ (l + 1)) * ch m k := by
      calc (m - l) ^ (l + 1) * ch m k
          ≤ (m - l) ^ (l + 1) * (Ed.length * ch (m - (l + 1)) (k - (l + 1))) :=
            Nat.mul_le_mul_left _ h1
        _ = Ed.length * (ch (m - (l + 1)) (k - (l + 1)) * (m - l) ^ (l + 1)) := by
            simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        _ ≤ Ed.length * (ch m k * k ^ (l + 1)) := Nat.mul_le_mul_left _ h2
        _ = (Ed.length * k ^ (l + 1)) * ch m k := by
            simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have h4 := cancel hch h3
    generalize hX : 4 * (l + 1) ^ 2 * k = X
    have hXpos : 0 < X := by rw [← hX]; exact Nat.mul_pos (Nat.mul_pos (by omega) hL2) (by omega)
    have h5 : (2 * X) ^ (l + 1) ≤ (m - l) ^ (l + 1) := by
      apply Nat.pow_le_pow_left
      rw [← hX]
      have : 2 * (4 * (l + 1) ^ 2 * k) = 8 * (l + 1) ^ 2 * k := by
        simp only [← Nat.mul_assoc]
      omega
    have h6 : Ed.length * k ^ (l + 1) ≤ t * X ^ (l + 1) := by
      rw [← hX]
      calc Ed.length * k ^ (l + 1) ≤ t * (4 * (l + 1) * (l + 1)) ^ (l + 1) * k ^ (l + 1) :=
            Nat.mul_le_mul_right _ hEd
        _ = t * (4 * (l + 1) ^ 2 * k) ^ (l + 1) := by
            rw [Nat.mul_assoc t, ← Nat.mul_pow, Nat.pow_two, Nat.mul_assoc 4]
    have h7 : 2 ^ (l + 1) * X ^ (l + 1) ≤ t * X ^ (l + 1) := by
      rw [← Nat.mul_pow]; exact Nat.le_trans h5 (Nat.le_trans h4 h6)
    have h8 := cancel (Nat.pow_pos hXpos) h7
    simp only [Nat.add_sub_cancel] at e2 ⊢
    omega
  · -- colouring side: some k-clique avoids `Ed`, so an entry of value ≥ 1 exists
    obtain ⟨K, hK, hKl, hKm, hno⟩ : ∃ K : List Nat, K.Nodup ∧ K.length = k ∧
        (∀ x ∈ K, x < m) ∧ ¬ ∃ R ∈ Ed, ∀ x ∈ R, x ∈ K := by
      apply Classical.byContradiction
      intro hn
      apply hall
      intro K h1 h2 h3
      apply Classical.byContradiction
      intro h4
      exact hn ⟨K, h1, h2, h3, h4⟩
    obtain ⟨e, he, hv, _⟩ := gpos K hK hKl hKm hno
    have hq : 0 < k - 1 := by omega
    have h1 := neg_count (k - 1) m L hq e.1 (gA e he).1 (gA e he).2.1 (gA e he).2.2 Er gEr
      (fun c hc hr => by
        apply Classical.byContradiction
        intro hn
        have := gneg c hc hn e he hr
        omega)
    generalize hq' : k - 1 = q at h1 hk hq
    -- 2 C(2L,2) q^(m-1) ≤ q^m
    have hC : 2 * ch2 (2 * L) ≤ q := by
      have := ch2_le (2 * L)
      have e : 2 * L * (2 * L) = 4 * (L * L) := by rw [Nat.mul_mul_mul_comm]
      rw [Nat.pow_two] at hk
      omega
    have em : q ^ m = q * q ^ (m - 1) := by rw [← Nat.pow_succ']; congr 1; omega
    have hc2 : 2 * (ch2 (2 * L) * q ^ (m - 1)) ≤ q ^ m := by
      rw [em, ← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ hC
    have eL : q ^ m = q ^ L * q ^ (m - L) := by rw [← Nat.pow_add]; congr 1; omega
    have h2 : q ^ L * q ^ (m - L) ≤ (2 * Er.length) * q ^ (m - L) := by
      rw [← eL, Nat.mul_assoc]; omega
    have h3 := cancel (Nat.pow_pos hq) h2
    generalize hY : 4 * L * (4 * L) = Y at hEr
    have hYpos : 0 < Y := by rw [← hY]; exact Nat.mul_pos (by omega) (by omega)
    have h4 : 2 ^ L * Y ^ L ≤ (2 * t) * Y ^ L := by
      rw [← Nat.mul_pow]
      calc (2 * Y) ^ L ≤ q ^ L := by
            apply Nat.pow_le_pow_left
            rw [← hY]
            have : 4 * L * (4 * L) = 16 * (L * L) := by rw [Nat.mul_mul_mul_comm]
            rw [Nat.pow_two] at hk
            omega
        _ ≤ 2 * Er.length := h3
        _ ≤ 2 * (t * Y ^ L) := Nat.mul_le_mul_left _ hEr
        _ = (2 * t) * Y ^ L := by rw [Nat.mul_assoc]
    have h5 := cancel (Nat.pow_pos hYpos) h4
    omega

end Programme.«20261025-0459b-proof-complexity».CCVal

#print axioms Programme.«20261025-0459b-proof-complexity».CCVal.cc_val
