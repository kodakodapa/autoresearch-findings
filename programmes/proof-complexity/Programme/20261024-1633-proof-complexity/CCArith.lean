import Programme.«20261024-1633-proof-complexity».KSub
import Programme.«20261024-1633-proof-complexity».Colour
import Programme.«20261024-1633-proof-complexity».CCCount

/-!
# Arithmetic glue for the clique–colouring counting bound

* `rb_count`: for `|S| ≤ ℓ`, at least `q^m - C(ℓ,2) q^(m-1)` of the `q`-colourings of `0..m-1`
  make `S` rainbow; stated for any functional `f` that is `≥ 1` on those colourings
  (th's `rbw m k S` with `q = k-1`), as `q^m ≤ tot q (range m) f c + C(ℓ,2) q^(m-1)`.
* `ch_ff`: `C(m,k) · k^{(j)} = m^{(j)} · C(m-j, k-j)` for `j ≤ k` (falling factorials `ff`).
* `pos_ratio`: `C(m-ℓ-1, k-ℓ-1) (m-ℓ)^(ℓ+1) ≤ C(m,k) k^(ℓ+1)` for `ℓ+1 ≤ k`.
* `neg_ratio`: if `q^m ≤ C(ℓ,2) q^(m-1) + X C(ℓ,2)^p q^(m-p)`, `0 < q`, `2 C(ℓ,2) ≤ q`, `1 ≤ m`, `p ≤ m`,
  then `q^p ≤ 2 X C(ℓ,2)^p`.
-/

namespace Programme.«20261024-1633-proof-complexity».CCArith

open Programme.«20261024-1633-proof-complexity».KSub Programme.«20261024-1633-proof-complexity».Colour

/-- Rainbow count: all but `C(ℓ,2) q^(m-1)` colourings make `S` rainbow. -/
theorem rb_count (q ℓ m : Nat) (hq : 0 < q) (S : List Nat) (hS : S.Nodup) (hSl : S.length ≤ ℓ)
    (hSm : ∀ x ∈ S, x < m) (f : (Nat → Nat) → Nat)
    (hf : ∀ c : Nat → Nat, (∀ i, i < m → c i < q) → rb c S → 1 ≤ f c) (c : Nat → Nat) :
    q ^ m ≤ tot q (List.range m) f c + ch2 ℓ * q ^ (m - 1) := by
  have hV : (List.range m).Nodup := List.nodup_range
  let fS : (Nat → Nat) → Nat := fun c => if rb c [] ∧ ∀ S' ∈ [S], ¬ rb c S' then 1 else 0
  have hpt : tot q (List.range m) (fun _ => 1) c ≤
      tot q (List.range m) (fun c => f c + fS c) c := by
    apply Programme.«20261024-1633-proof-complexity».CCCount.tot_mono_on
    intro c' hc' _
    by_cases hr : rb c' S
    · have := hf c' (fun i hi => hc' i (List.mem_range.mpr hi)) hr
      omega
    · have h1 : fS c' = 1 := by
        simp only [fS]
        rw [ite_eq_left ⟨Programme.«20261024-1633-proof-complexity».CCCount.rb_nil c', fun S' hS' => by
          rw [List.mem_singleton] at hS'; subst hS'; exact hr⟩]
      omega
  rw [tot_one, tot_add, List.length_range] at hpt
  have hA : tot q (List.range m) fS c ≤ ch2 ℓ * q ^ (m - 1) := by
    have := petal_count q ℓ hq [] (List.range m) [S] hV
      (fun S' hS' => by
        rw [List.mem_singleton] at hS'; subst hS'
        exact ⟨hS, hSl, fun x hx => List.mem_range.mpr (hSm x hx)⟩)
      (List.pairwise_singleton _ _) c
    rw [List.length_range, List.length_singleton, Nat.pow_one] at this
    exact this
  omega

/-- Falling factorial `n (n-1) ⋯ (n-j+1)`. -/
def ff : Nat → Nat → Nat
  | _, 0 => 1
  | n, j+1 => n * ff (n - 1) j

theorem ch_zero_succ (k : Nat) : ch 0 (k+1) = 0 := rfl

theorem ch_lt : ∀ n k, n < k → ch n k = 0
  | 0, 0, h => absurd h (Nat.lt_irrefl 0)
  | 0, _+1, _ => rfl
  | _+1, 0, h => absurd h (Nat.not_lt_zero _)
  | n+1, k+1, h => by
    simp only [ch]; rw [ch_lt n (k+1) (by omega), ch_lt n k (by omega)]

/-- Absorption: `C(n+1, j+1) (j+1) = (n+1) C(n, j)`. -/
theorem ch_absorb : ∀ n j, ch (n+1) (j+1) * (j+1) = (n+1) * ch n j
  | 0, 0 => rfl
  | 0, j+1 => by simp [ch]
  | n+1, 0 => by
    simp only [ch]
    have h := ch_absorb n 0
    simp only [ch] at h
    rw [Nat.mul_one] at h ⊢; rw [Nat.mul_one]
    omega
  | n+1, j+1 => by
    -- C(n+2,j+2)(j+2) = C(n+1,j+2)(j+2) + C(n+1,j+1)(j+1) + C(n+1,j+1)
    have e : ch (n+1+1) (j+1+1) = ch (n+1) (j+1+1) + ch (n+1) (j+1) := rfl
    have h1 := ch_absorb n (j+1)
    have h2 := ch_absorb n j
    have e2 : ch (n+1) (j+1) = ch n (j+1) + ch n j := rfl
    rw [e, Nat.add_mul, h1]
    have : ch (n+1) (j+1) * (j+1+1) = ch (n+1) (j+1) * (j+1) + ch (n+1) (j+1) := by
      rw [Nat.mul_succ]
    rw [this, h2, e2]
    simp only [Nat.succ_mul, Nat.mul_add]
    omega

theorem ch_ff : ∀ j m k, j ≤ k → ch m k * ff k j = ff m j * ch (m - j) (k - j)
  | 0, m, k, _ => by simp [ff]
  | j+1, m, k, h => by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    cases m with
    | zero => simp [ff, ch]
    | succ m' =>
      have ih := ch_ff j m' k' (by omega)
      have ha := ch_absorb m' k'
      simp only [ff, Nat.add_sub_cancel]
      have e1 : m' + 1 - (j + 1) = m' - j := by omega
      have e2 : k' + 1 - (j + 1) = k' - j := by omega
      rw [e1, e2, ← Nat.mul_assoc, ha, Nat.mul_assoc, ih, Nat.mul_assoc]

theorem ff_le : ∀ n j, ff n j ≤ n ^ j
  | _, 0 => by simp [ff]
  | n, j+1 => by
    simp only [ff, Nat.pow_succ]
    have := ff_le (n - 1) j
    have h2 : (n - 1) ^ j ≤ n ^ j := Nat.pow_le_pow_left (by omega) j
    rw [Nat.mul_comm (n ^ j) n]
    exact Nat.mul_le_mul_left n (Nat.le_trans this h2)

theorem ff_ge : ∀ n j, (n + 1 - j) ^ j ≤ ff n j
  | _, 0 => by simp [ff]
  | n, j+1 => by
    simp only [ff, Nat.pow_succ]
    cases n with
    | zero => simp
    | succ n' =>
      have := ff_ge n' j
      have e : n' + 1 + 1 - (j + 1) = n' + 1 - j := by omega
      rw [e, Nat.add_sub_cancel, Nat.mul_comm]
      exact Nat.mul_le_mul (by omega) this

/-- Positive-side ratio: `C(m,k) / C(m-ℓ-1, k-ℓ-1) ≥ ((m-ℓ)/k)^(ℓ+1)`. -/
theorem pos_ratio (m k ℓ : Nat) (hk : ℓ + 1 ≤ k) :
    ch (m - (ℓ + 1)) (k - (ℓ + 1)) * (m - ℓ) ^ (ℓ + 1) ≤ ch m k * k ^ (ℓ + 1) := by
  have h := ch_ff (ℓ + 1) m k hk
  have h1 := ff_ge m (ℓ + 1)
  have h2 := ff_le k (ℓ + 1)
  have e : m + 1 - (ℓ + 1) = m - ℓ := by omega
  rw [e] at h1
  calc ch (m - (ℓ + 1)) (k - (ℓ + 1)) * (m - ℓ) ^ (ℓ + 1)
      ≤ ch (m - (ℓ + 1)) (k - (ℓ + 1)) * ff m (ℓ + 1) := Nat.mul_le_mul_left _ h1
    _ = ch m k * ff k (ℓ + 1) := by rw [h, Nat.mul_comm]
    _ ≤ ch m k * k ^ (ℓ + 1) := Nat.mul_le_mul_left _ h2

/-- Negative-side ratio: from the colouring count to `q^p ≤ 2 X C(ℓ,2)^p`. -/
theorem neg_ratio (q ℓ p m X : Nat) (hq0 : 0 < q) (hq : 2 * ch2 ℓ ≤ q) (hm : 1 ≤ m) (hp : p ≤ m)
    (h : q ^ m ≤ ch2 ℓ * q ^ (m - 1) + X * (ch2 ℓ ^ p * q ^ (m - p))) :
    q ^ p ≤ 2 * X * ch2 ℓ ^ p := by
  have qpos := hq0
  have em : q ^ m = q * q ^ (m - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  have h1 : 2 * (ch2 ℓ * q ^ (m - 1)) ≤ q ^ m := by
    rw [em, ← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ hq
  have h2 : q ^ m ≤ 2 * (X * (ch2 ℓ ^ p * q ^ (m - p))) := by omega
  have ep : q ^ m = q ^ p * q ^ (m - p) := by rw [← Nat.pow_add]; congr 1; omega
  rw [ep] at h2
  have hpos : 0 < q ^ (m - p) := Nat.pow_pos qpos
  have h3 : q ^ p * q ^ (m - p) ≤ (2 * X * ch2 ℓ ^ p) * q ^ (m - p) := by
    calc q ^ p * q ^ (m - p) ≤ 2 * (X * (ch2 ℓ ^ p * q ^ (m - p))) := h2
      _ = (2 * X * ch2 ℓ ^ p) * q ^ (m - p) := by
        simp only [Nat.mul_assoc]
  exact Nat.le_of_mul_le_mul_right h3 hpos

end Programme.«20261024-1633-proof-complexity».CCArith

#print axioms Programme.«20261024-1633-proof-complexity».CCArith.rb_count
#print axioms Programme.«20261024-1633-proof-complexity».CCArith.ch_ff
#print axioms Programme.«20261024-1633-proof-complexity».CCArith.pos_ratio
#print axioms Programme.«20261024-1633-proof-complexity».CCArith.neg_ratio
