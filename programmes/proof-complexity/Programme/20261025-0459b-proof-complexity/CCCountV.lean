import Programme.«20261024-1633-proof-complexity».KSub
import Programme.«20261024-1633-proof-complexity».Colour
import Programme.«20261024-1633-proof-complexity».CCArith
import Programme.«20261024-1633-proof-complexity».CCAssembly

/-!
# Counting for the value-free approximation of clique–colouring (th's module M6)

Interface of th's plan (P17). The hypotheses are exactly the conclusion of th's
`Work.VApprox.cc_vapprox` (K5), with `VSwitch.Valid`, `VSwitch.cons` and `VSwitch.rb` written out
by their defining equations (`rb` is `Colour.rb`), so this file does not depend on th's package.

* `cc_count`: either the drop events `Ed` (sets of `≥ L` vertices) cover all `k`-subsets of
  `range m`, giving `C(m,k) ≤ |Ed| C(m-L,k-L)`, or some entry of value `≥ 1` exists and every
  `(k-1)`-colouring making it rainbow fits a rise event (an `L`-merge list), giving
  `(k-1)^m ≤ |Er| (k-1)^(m-L) + C(2L,2) (k-1)^(m-1)`.
* `cc_count_arith`: with `|Ed| ≤ t (4L²)^L`, `|Er| ≤ t (16L²)^L`, `32L² ≤ k-1`, `8L²k + L ≤ m`,
  either case gives `2^(L-1) ≤ t`.
* `cc_from_approx`: the two combined; applied to `cc_vapprox` with `t = s (2k+5)` it gives
  `2^(L-1) ≤ s (2k+5)` for every tree-like CP refutation of `CC m k`.
-/

namespace Programme.«20261025-0459b-proof-complexity».CCCountV

open Programme.«20261024-1633-proof-complexity»
open Programme.«20261024-1633-proof-complexity».CCAssembly (ch_pos ch2_le)

/-- The counting step. -/
theorem cc_count (m k L : Nat) (hL : 1 ≤ L) (hk : L + 1 ≤ k)
    (Er : List (List (Nat × Nat))) (Ed : List (List Nat)) (A : List (List Nat × Int))
    (hEr : ∀ τ ∈ Er, ((τ.map Prod.fst).Nodup ∧ ∀ e ∈ τ, ∀ e' ∈ τ, e.1 ≠ e'.2) ∧
      (∀ e ∈ τ, e.1 < m ∧ e.2 < m) ∧ τ.length = L)
    (hEd : ∀ R ∈ Ed, R.Nodup ∧ L ≤ R.length ∧ ∀ x ∈ R, x < m)
    (hA : ∀ e ∈ A, e.1.Nodup ∧ e.1.length ≤ 2 * L ∧ ∀ x ∈ e.1, x < m)
    (hpos : ∀ K : List Nat, K.Nodup → K.length = k → (∀ x ∈ K, x < m) →
      (¬ ∃ R ∈ Ed, ∀ x ∈ R, x ∈ K) → ∃ e ∈ A, 1 ≤ e.2 ∧ ∀ x ∈ e.1, x ∈ K)
    (hneg : ∀ c : Nat → Nat, (∀ i, i < m → c i < k - 1) →
      (¬ ∃ τ ∈ Er, ∀ e ∈ τ, c e.1 = c e.2) → ∀ e ∈ A, Colour.rb c e.1 → e.2 ≤ 0) :
    KSub.ch m k ≤ Ed.length * KSub.ch (m - L) (k - L) ∨
      (k - 1) ^ m ≤ Er.length * (k - 1) ^ (m - L) + Colour.ch2 (2 * L) * (k - 1) ^ (m - 1) := by
  have hq : 0 < k - 1 := by omega
  by_cases hall : ∀ K ∈ KSub.ksub (List.range m) k, ∃ R ∈ Ed, ∀ x ∈ R, x ∈ K
  · left
    have hf : (KSub.ksub (List.range m) k).filter (fun K => Ed.any fun T => KSub.sub T K) =
        KSub.ksub (List.range m) k := by
      apply List.filter_eq_self.2
      intro K hK
      obtain ⟨R, hR, hRK⟩ := hall K hK
      simp only [List.any_eq_true]
      exact ⟨R, hR, KSub.sub_iff.2 hRK⟩
    have := KSub.pos_count (List.range m) List.nodup_range k (L - 1) Ed
      (fun R hR => ⟨(hEd R hR).1, fun i hi => List.mem_range.2 ((hEd R hR).2.2 i hi),
        by have := (hEd R hR).2.1; omega⟩) (by omega)
    rw [hf, KSub.ksub_length, List.length_range] at this
    have e : L - 1 + 1 = L := by omega
    rw [e] at this
    exact this
  · right
    obtain ⟨K, hK, hnK⟩ : ∃ K ∈ KSub.ksub (List.range m) k, ¬ ∃ R ∈ Ed, ∀ x ∈ R, x ∈ K :=
      Classical.byContradiction fun hc => hall fun K hK =>
        Classical.byContradiction fun h => hc ⟨K, hK, h⟩
    obtain ⟨hs, hl⟩ := KSub.mem_ksub hK
    obtain ⟨e, he, hv, -⟩ := hpos K (hs.nodup List.nodup_range) hl
      (fun x hx => List.mem_range.1 (hs.subset hx)) (fun ⟨R, hR, h⟩ => hnK ⟨R, hR, h⟩)
    obtain ⟨hen, hel, hem⟩ := hA e he
    let f : (Nat → Nat) → Nat := fun c => (Er.map fun τ => Colour.ind τ c).sum
    have h1 := CCArith.rb_count (k - 1) (2 * L) m hq e.1 hen hel hem f
      (fun c hc hr => by
        by_cases hx : ∃ τ ∈ Er, ∀ e ∈ τ, c e.1 = c e.2
        · obtain ⟨τ, hτ, hτc⟩ := hx
          have := Colour.le_sum_of_mem (fun τ => Colour.ind τ c) Er τ hτ
          have e1 : Colour.ind τ c = 1 := by unfold Colour.ind; rw [if_pos hτc]
          simp only [f]; omega
        · have := hneg c hc hx e he hr; omega) (fun _ => 0)
    have h2 : Colour.tot (k - 1) (List.range m) f (fun _ => 0) ≤
        Er.length * (k - 1) ^ (m - L) := by
      simp only [f]
      rw [Colour.tot_sum]
      apply Colour.sum_le
      intro τ hτ
      obtain ⟨⟨hnd, hx⟩, hr, hlen⟩ := hEr τ hτ
      have := Colour.choice_term (k - 1) hq (List.range m) List.nodup_range τ
        (fun e he => List.mem_range.2 (hr e he).1) hnd hx (fun _ => 0)
      rwa [List.length_range, hlen] at this
    omega

/-- Arithmetic: either case of `cc_count` gives `2^(L-1) ≤ t`. -/
theorem cc_count_arith (m k L t nEr nEd : Nat) (hL : 1 ≤ L) (hk : 32 * L ^ 2 ≤ k - 1)
    (hm : 8 * L ^ 2 * k + L ≤ m) (hEd : nEd ≤ t * (4 * L ^ 2) ^ L)
    (hEr : nEr ≤ t * (16 * L ^ 2) ^ L)
    (hcase : KSub.ch m k ≤ nEd * KSub.ch (m - L) (k - L) ∨
      (k - 1) ^ m ≤ nEr * (k - 1) ^ (m - L) + Colour.ch2 (2 * L) * (k - 1) ^ (m - 1)) :
    2 ^ (L - 1) ≤ t := by
  have c0 : ∀ n, KSub.ch n 0 = 1 := fun n => by cases n <;> rfl
  have cS : ∀ n j, KSub.ch (n+1) (j+1) = KSub.ch n (j+1) + KSub.ch n j := fun _ _ => rfl
  have hL2 : 1 ≤ L ^ 2 := Nat.pow_pos (by omega)
  have hLL : L ≤ L ^ 2 := by rw [Nat.pow_two]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hk1 : 1 ≤ k := by omega
  have e2 : 2 ^ L = 2 * 2 ^ (L - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  rcases hcase with hA | hB
  · -- positive: (m-L+1)^L ≤ nEd k^L, and m-L+1 ≥ 8L²k
    have hr := CCArith.pos_ratio m k (L - 1) (by omega)
    have e : L - 1 + 1 = L := by omega
    rw [e, show m - (L - 1) = m - L + 1 by omega] at hr
    have hkm : k ≤ m := by
      have : k ≤ 8 * L ^ 2 * k := Nat.le_mul_of_pos_left _ (by omega)
      omega
    have hc : 0 < KSub.ch (m - L) (k - L) := ch_pos _ c0 cS _ _ (by omega)
    -- c (m-L+1)^L ≤ C(m,k) k^L ≤ nEd c k^L
    have h1 : KSub.ch (m - L) (k - L) * (m - L + 1) ^ L ≤
        KSub.ch (m - L) (k - L) * (nEd * k ^ L) := by
      refine Nat.le_trans hr (Nat.le_trans (Nat.mul_le_mul_right _ hA) (Nat.le_of_eq ?_))
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have h2 := Nat.le_of_mul_le_mul_left h1 hc
    have h3 : (8 * L ^ 2 * k) ^ L ≤ (m - L + 1) ^ L := Nat.pow_le_pow_left (by omega) _
    have h4 : 2 ^ L * (4 * L ^ 2 * k) ^ L ≤ t * (4 * L ^ 2 * k) ^ L := by
      rw [← Nat.mul_pow, show 2 * (4 * L ^ 2 * k) = 8 * L ^ 2 * k by
        simp only [← Nat.mul_assoc]]
      refine Nat.le_trans h3 (Nat.le_trans h2 ?_)
      rw [Nat.mul_pow (4 * L ^ 2) k L, ← Nat.mul_assoc]
      exact Nat.mul_le_mul_right _ hEd
    have hp : 0 < (4 * L ^ 2 * k) ^ L := Nat.pow_pos (Nat.mul_pos (by omega) (by omega))
    have := Nat.le_of_mul_le_mul_right h4 hp
    omega
  · -- negative: q^L ≤ 2 nEr, q ≥ 32L²
    have hq : 0 < k - 1 := by omega
    have hc2 : Colour.ch2 (2 * L) ≤ 2 * L * (2 * L) := ch2_le _ rfl (fun _ => rfl) _
    have h2C : 2 * Colour.ch2 (2 * L) ≤ k - 1 := by
      have : 2 * L * (2 * L) = 4 * L ^ 2 := by rw [Nat.pow_two]; simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      omega
    have hLm : L ≤ m := by
      have : k ≤ 8 * L ^ 2 * k := Nat.le_mul_of_pos_left _ (by omega)
      omega
    have em1 : (k - 1) ^ m = (k - 1) ^ (m - 1) * (k - 1) := by
      rw [← Nat.pow_succ]; congr 1; omega
    have emL : (k - 1) ^ m = (k - 1) ^ L * (k - 1) ^ (m - L) := by
      rw [← Nat.pow_add]; congr 1; omega
    have h1 : 2 * (Colour.ch2 (2 * L) * (k - 1) ^ (m - 1)) ≤ (k - 1) ^ m := by
      rw [em1, ← Nat.mul_assoc, Nat.mul_comm _ (k - 1)]
      exact Nat.mul_le_mul_right _ h2C
    have h2 : (k - 1) ^ L * (k - 1) ^ (m - L) ≤ (2 * nEr) * (k - 1) ^ (m - L) := by
      rw [← emL, Nat.mul_assoc]; omega
    have h3 := Nat.le_of_mul_le_mul_right h2 (Nat.pow_pos hq)
    have h4 : (32 * L ^ 2) ^ L ≤ (k - 1) ^ L := Nat.pow_le_pow_left hk _
    have h5 : 2 ^ L * (16 * L ^ 2) ^ L ≤ (2 * t) * (16 * L ^ 2) ^ L := by
      rw [← Nat.mul_pow, show 2 * (16 * L ^ 2) = 32 * L ^ 2 by rw [← Nat.mul_assoc]]
      refine Nat.le_trans h4 (Nat.le_trans h3 ?_)
      rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left 2 hEr
    have := Nat.le_of_mul_le_mul_right h5 (Nat.pow_pos (Nat.mul_pos (by omega) hL2))
    omega

/-- `cc_count` and `cc_count_arith` combined, stated on the conclusion of th's `cc_vapprox`
(with `t = s (2k+5)` there). -/
theorem cc_from_approx (m k L t : Nat) (hL : 1 ≤ L) (hk : 32 * L ^ 2 ≤ k - 1)
    (hm : 8 * L ^ 2 * k + L ≤ m)
    (h : ∃ (A : List (List Nat × Int)) (Er : List (List (Nat × Nat))) (Ed : List (List Nat)),
      Er.length ≤ t * (4 * L * (4 * L)) ^ L ∧
      Ed.length ≤ t * (4 * L * L) ^ L ∧
      (∀ τ ∈ Er, ((τ.map Prod.fst).Nodup ∧ ∀ e ∈ τ, ∀ e' ∈ τ, e.1 ≠ e'.2) ∧
        (∀ e ∈ τ, e.1 < m ∧ e.2 < m) ∧ τ.length = L) ∧
      (∀ R ∈ Ed, R.Nodup ∧ L ≤ R.length ∧ ∀ x ∈ R, x < m) ∧
      (∀ e ∈ A, e.1.Nodup ∧ e.1.length ≤ 2 * L ∧ ∀ x ∈ e.1, x < m) ∧
      (∀ K : List Nat, K.Nodup → K.length = k → (∀ x ∈ K, x < m) →
        (¬ ∃ R ∈ Ed, ∀ x ∈ R, x ∈ K) → ∃ e ∈ A, 1 ≤ e.2 ∧ ∀ x ∈ e.1, x ∈ K) ∧
      (∀ c : Nat → Nat, (∀ i, i < m → c i < k - 1) → (¬ ∃ τ ∈ Er, ∀ e ∈ τ, c e.1 = c e.2) →
        ∀ e ∈ A, Colour.rb c e.1 → e.2 ≤ 0)) :
    2 ^ (L - 1) ≤ t := by
  obtain ⟨A, Er, Ed, hEr, hEd, hEr', hEd', hA, hpos, hneg⟩ := h
  have hL2 : L ≤ L ^ 2 := by rw [Nat.pow_two]; exact Nat.le_mul_of_pos_right _ (by omega)
  have e1 : 4 * L * (4 * L) = 16 * L ^ 2 := by
    rw [Nat.pow_two]; simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have e2 : 4 * L * L = 4 * L ^ 2 := by rw [Nat.pow_two, Nat.mul_assoc]
  rw [e1] at hEr; rw [e2] at hEd
  exact cc_count_arith m k L t Er.length Ed.length hL hk hm hEd hEr
    (cc_count m k L hL (by omega) Er Ed A hEr' hEd' hA hpos hneg)

end Programme.«20261025-0459b-proof-complexity».CCCountV

#print axioms Programme.«20261025-0459b-proof-complexity».CCCountV.cc_count
#print axioms Programme.«20261025-0459b-proof-complexity».CCCountV.cc_count_arith
#print axioms Programme.«20261025-0459b-proof-complexity».CCCountV.cc_from_approx
