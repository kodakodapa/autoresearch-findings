import Programme.«20261025-0459b-proof-complexity».ApproxRC
import Programme.«20261024-1633-proof-complexity».CCApprox
import Programme.«20261024-1633-proof-complexity».CCAssembly
import Programme.«20261024-1633-proof-complexity».Sunflower
import Programme.«20261024-1633-proof-complexity».KSub
import Programme.«20261024-1633-proof-complexity».Colour
import Programme.«20261024-1633-proof-complexity».CCArith

/-!
# Tree-like cutting planes with arbitrary coefficients: clique–colouring

`cc_closed` (K1) needs every line of weight `≤ W`. Here the weight bound is gone: from
`CliqueColour.cc_interp` (any tree-like CP refutation `Refutation (CC m k)`, arbitrary integer
coefficients) and the value-independent approximation `Work.ApproxRC.approx1`, the counting of
`CCLower`/`CCParam` goes through with `L = s (2k+5) ℓ (B+1)^2` in place of `s (2k+6) (2WB+1)^2`.

`cc_unb`: for `ℓ ≥ 2`, `64ℓ⁴ ≤ k-1`, `64ℓ⁴k + ℓ ≤ m`, every tree-like CP refutation of `CC m k`
with `s` nodes has `2^{4ℓ} ≤ 18 s (2k+6) (ℓ+1)^2`. Known result (Pudlák 1997 for general CP via
monotone real circuits; this is the tree-like case, with a weaker exponent), formalised here.
-/

set_option linter.unusedVariables false

namespace Programme.«20261025-0459b-proof-complexity».CCUnb

open Programme.«20261024-1110-proof-complexity».Haken (Lit Clause CNF Lit.eval Clause.eval)
open Programme.«20261024-1633-proof-complexity».RealApprox
open Programme.«20261024-1633-proof-complexity».Pluck
open Programme.«20261024-1633-proof-complexity».CP
open Programme.«20261024-1633-proof-complexity».CPInterp
open Programme.«20261024-1633-proof-complexity».CliqueColour
open Programme.«20261024-1633-proof-complexity».CCApprox (emb inA hin clique_pos colour_neg)
open Programme.«20261024-1633-proof-complexity».CCLower (hit rbw mu_sum sum_le_len le_sum_mem)
open Programme.«20261024-1633-proof-complexity».CCParam (param_arith)
open Programme.«20261024-1633-proof-complexity».CCAssembly (fact_le fact_pos ch_pos ch2_le)

/-- **Approximation step, arbitrary coefficients.** -/
theorem cc_approx1 (m k p ℓ B : Nat) (hp : 1 ≤ p) (hℓ : 2 ≤ ℓ) (hB : 1 ≤ B)
    (hSF : SF (p + 1) ℓ B) (Rf : Refutation (CC m k)) :
    ∃ pe : List (List Nat), ∃ ne : List (List Nat × List (List Nat)),
      pe.length ≤ Rf.size * (2 * k + 5) * (ℓ * (B + 1) ^ 2) ∧
      ne.length ≤ Rf.size * (2 * k + 5) * (ℓ * (B + 1) ^ 2) ∧
      (∀ T ∈ pe, T.Nodup ∧ ℓ + 1 ≤ T.length ∧ ∀ x ∈ T, x < m) ∧ (∀ ev ∈ ne, Ev p ℓ m ev) ∧
      ((∀ K : List Nat, K.Nodup → K.length = k → (∀ x ∈ K, x < m) →
          ∃ T ∈ pe, ∀ i ∈ T, i ∈ K) ∨
       ∃ S : List Nat, S.Nodup ∧ S.length ≤ ℓ ∧ (∀ x ∈ S, x < m) ∧
          ∀ c : Nat → Nat, (∀ i, i < m → c i < k - 1) → clq (negG c) S →
            ∃ ev ∈ ne, clq (negG c) ev.1 ∧ ∀ S' ∈ ev.2, ¬ clq (negG c) S') := by
  obtain ⟨f, t, r, ht, _, hsep⟩ := cc_interp m k Rf
  have hin' : ∀ u, shared isR isQ u = true → Inv ℓ m (inA m u) ∧ (inA m u).ents.length ≤ B ∧
      (∀ K, val (emb m (posG K)) u ≤ eval (inA m u) (posG K)) ∧
      (∀ c, eval (inA m u) (negG c) ≤ val (emb m (negG c)) u) := by
    intro u hu
    obtain ⟨h1, _, _, h4, h5, h6⟩ := hin m ℓ B hℓ hB u hu
    exact ⟨h1, h4, h5, h6⟩
  obtain ⟨a, pe, ne, ha2, _, ha5, ha6, ha7, ha8, ha9, ha10⟩ :=
    Programme.«20261025-0459b-proof-complexity».ApproxRC.approx1 (shared isR isQ) p ℓ m B hp (by omega) hSF (emb m) (inA m) hin' r
  have hmul : t * (ℓ * (B + 1) ^ 2) ≤ Rf.size * (2 * k + 5) * (ℓ * (B + 1) ^ 2) :=
    Nat.mul_le_mul_right _ ht
  refine ⟨pe, ne, Nat.le_trans ha5 hmul, Nat.le_trans ha6 hmul, ha7, ha8, ?_⟩
  have neg_err : ∀ c : Nat → Nat, (∀ i, i < m → c i < k - 1) → 1 ≤ eval a (negG c) →
      ∃ ev ∈ ne, clq (negG c) ev.1 ∧ ∀ S' ∈ ev.2, ¬ clq (negG c) S' := by
    intro c hc h1
    rcases ha10 c with h | h
    · have := (hsep (emb m (negG c))).2 (colour_neg m k c hc); omega
    · exact h
  by_cases hb : 1 ≤ a.base
  · refine Or.inr ⟨[], List.nodup_nil, by simp, by simp, fun c hc _ => neg_err c hc ?_⟩
    exact Int.le_trans hb (evalL_base _ _ _)
  · by_cases he : ∃ e ∈ a.ents, 1 ≤ e.2
    · obtain ⟨e, he, h1⟩ := he
      obtain ⟨hn, hl, hv, _⟩ := ha2 e he
      exact Or.inr ⟨e.1, hn, hl, hv, fun c hc hS =>
        neg_err c hc (Int.le_trans h1 (evalL_ent _ _ _ e he hS))⟩
    · left
      intro K hK hl hm
      rcases ha9 K with h | h
      · have h1 := (hsep (emb m (posG K))).1 (clique_pos m k K hK hl hm)
        have h2 : eval a (posG K) ≤ 0 := by
          apply eval_le_of_cover
          intro x hx _
          rcases List.mem_cons.1 hx with h' | h'
          · subst h'; show a.base ≤ 0; omega
          · have : ¬ 1 ≤ x.2 := fun h'' => he ⟨x, h', h''⟩
            omega
        omega
      · exact h

/-- **Counting form, arbitrary coefficients** (as `CCLower.cc_lower`, with `L = s(2k+5)ℓ(B+1)^2`). -/
theorem cc_lower1 (m k p ℓ B : Nat) (hp : 1 ≤ p) (hℓ : 2 ≤ ℓ) (hB : 1 ≤ B) (hSF : SF (p + 1) ℓ B)
    (Rf : Refutation (CC m k))
    (Ks : List (List Nat)) (hKs : ∀ K ∈ Ks, K.Nodup ∧ K.length = k ∧ ∀ x ∈ K, x < m) (c₁ : Nat)
    (hpos : ∀ Ts : List (List Nat), (∀ T ∈ Ts, T.Nodup ∧ (∀ i ∈ T, i < m) ∧ ℓ + 1 ≤ T.length) →
      (Ks.filter fun K => Ts.any fun T => T.all fun i => decide (i ∈ K)).length ≤ Ts.length * c₁)
    (μ : ((Nat → Nat) → Nat) → Nat)
    (hmono : ∀ f g : (Nat → Nat) → Nat, (∀ c, f c ≤ g c) → μ f ≤ μ g)
    (hadd : ∀ f g : (Nat → Nat) → Nat, μ (fun c => f c + g c) ≤ μ f + μ g)
    (hzero : μ (fun _ => 0) = 0) (c₂ N₀ : Nat)
    (hneg : ∀ ev, Ev p ℓ m ev → μ (hit ev) ≤ c₂)
    (hrb : ∀ S : List Nat, S.Nodup → S.length ≤ ℓ → (∀ x ∈ S, x < m) → N₀ ≤ μ (rbw m k S)) :
    Ks.length ≤ Rf.size * (2 * k + 5) * (ℓ * (B + 1) ^ 2) * c₁ ∨
    N₀ ≤ Rf.size * (2 * k + 5) * (ℓ * (B + 1) ^ 2) * c₂ := by
  obtain ⟨pe, ne, hpe, hne, hpe', hne', hcase⟩ := cc_approx1 m k p ℓ B hp hℓ hB hSF Rf
  rcases hcase with hall | ⟨S, hSn, hSl, hSm, hS⟩
  · left
    have hf : (Ks.filter fun K => pe.any fun T => T.all fun i => decide (i ∈ K)) = Ks := by
      apply List.filter_eq_self.2
      intro K hK
      obtain ⟨hn, hl, hm⟩ := hKs K hK
      obtain ⟨T, hT, hTK⟩ := hall K hn hl hm
      simp only [List.any_eq_true, List.all_eq_true, decide_eq_true_eq]
      exact ⟨T, hT, hTK⟩
    have := hpos pe (fun T hT => ⟨(hpe' T hT).1, (hpe' T hT).2.2, (hpe' T hT).2.1⟩)
    rw [hf] at this
    exact Nat.le_trans this (Nat.mul_le_mul_right _ hpe)
  · right
    have hpt : ∀ c, rbw m k S c ≤ (ne.map fun ev => hit ev c).sum := by
      intro c
      unfold rbw
      split
      · rename_i h
        obtain ⟨ev, hev, h1, h2⟩ := hS c h.1 h.2
        have := le_sum_mem (fun ev => hit ev c) ne ev hev
        have e : hit ev c = 1 := by unfold hit; rw [if_pos ⟨h1, h2⟩]
        omega
      · exact Nat.zero_le _
    have h1 := Nat.le_trans (hrb S hSn hSl hSm) (hmono _ _ hpt)
    have h2 := mu_sum μ hmono hadd hzero hit ne
    have h3 := sum_le_len (fun ev => μ (hit ev)) c₂ ne (fun ev hev => hneg ev (hne' ev hev))
    exact Nat.le_trans h1 (Nat.le_trans h2 (Nat.le_trans h3 (Nat.mul_le_mul_right _ hne)))

/-- `ℓ (B+1)^2 ≤ (2ℓB+1)^2` for `B ≥ 1`. -/
theorem gate_le (ℓ B : Nat) (hB : 1 ≤ B) : ℓ * (B + 1) ^ 2 ≤ (2 * ℓ * B + 1) ^ 2 := by
  have h1 : (B + 1) ^ 2 ≤ 4 * B ^ 2 := by
    have : B + 1 ≤ 2 * B := by omega
    have := Nat.pow_le_pow_left this 2
    rw [Nat.mul_pow] at this; simpa using this
  have h2 : ℓ * (4 * B ^ 2) ≤ (2 * ℓ * B) ^ 2 := by
    rw [Nat.mul_pow, Nat.mul_pow]
    have : ℓ ≤ ℓ ^ 2 := by
      rcases Nat.eq_zero_or_pos ℓ with h | h
      · subst h; simp
      · rw [Nat.pow_two]; exact Nat.le_mul_of_pos_left _ h
    have := Nat.mul_le_mul_right (4 * B ^ 2) this
    refine Nat.le_trans this (Nat.le_of_eq ?_)
    simp only [show (2:Nat) ^ 2 = 4 by rfl, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have h3 : (2 * ℓ * B) ^ 2 ≤ (2 * ℓ * B + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  exact Nat.le_trans (Nat.mul_le_mul_left _ h1) (Nat.le_trans h2 h3)

/-- **Parametrised bound, arbitrary coefficients.** -/
theorem cc_param1 (m k ℓ B : Nat) (hℓ : 2 ≤ ℓ) (hB1 : 1 ≤ B) (hB : B ≤ (2 * ℓ * ℓ) ^ ℓ)
    (hSF : SF (2 * ℓ + 1) ℓ B) (hk : 64 * ℓ ^ 4 ≤ k - 1) (hm : 64 * ℓ ^ 4 * k + ℓ ≤ m)
    (Rf : Refutation (CC m k))
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
    2 ^ (4 * ℓ) ≤ 18 * (Rf.size * (2 * k + 6) * (ℓ + 1) ^ 2) := by
  have hL : Rf.size * (2 * k + 5) * (ℓ * (B + 1) ^ 2) ≤
      Rf.size * (2 * k + 6) * (2 * ℓ * B + 1) ^ 2 :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (gate_le ℓ B hB1)
  have hcase := cc_lower1 m k (2 * ℓ) ℓ B (by omega) hℓ hB1 hSF Rf Ks hKs c₁ hpos μ hmono hadd
    hzero _ _ hneg hrb
  apply param_arith m (m - ℓ) k ℓ B Rf.size ℓ Ks.length c₁ C hℓ hB1 hB hk (by omega) (by omega)
    hc1 hratio hC
  rcases hcase with h | h
  · exact Or.inl (Nat.le_trans h (Nat.mul_le_mul_right _ hL))
  · exact Or.inr (Nat.le_trans h (Nat.mul_le_mul_right _ hL))

open Programme.«20261024-1633-proof-complexity» in
/-- **Tree-like cutting planes, arbitrary coefficients, clique–colouring.** For `ℓ ≥ 2`,
`64ℓ⁴ ≤ k-1`, `64ℓ⁴k + ℓ ≤ m`, every tree-like CP refutation of `CC m k` (`CP.Refutation`, integer
coefficients of any size) with `s` nodes has `2^{4ℓ} ≤ 18 s (2k+6) (ℓ+1)^2`. -/
theorem cc_unb (m k ℓ : Nat) (hℓ : 2 ≤ ℓ) (hk : 64 * ℓ ^ 4 ≤ k - 1)
    (hm : 64 * ℓ ^ 4 * k + ℓ ≤ m) (Rf : Refutation (CC m k)) :
    2 ^ (4 * ℓ) ≤ 18 * (Rf.size * (2 * k + 6) * (ℓ + 1) ^ 2) := by
  have f0 : Sunflower.fact 0 = 1 := rfl
  have fS : ∀ n, Sunflower.fact (n+1) = (n+1) * Sunflower.fact n := fun _ => rfl
  have c0 : ∀ n, KSub.ch n 0 = 1 := fun n => by cases n <;> rfl
  have cS : ∀ n j, KSub.ch (n+1) (j+1) = KSub.ch n (j+1) + KSub.ch n j := fun _ _ => rfl
  have d0 : Colour.ch2 0 = 0 := rfl
  have dS : ∀ n, Colour.ch2 (n+1) = Colour.ch2 n + n := fun _ => rfl
  have clq_rb : ∀ (c : Nat → Nat) (S : List Nat), clq (negG c) S ↔ Colour.rb c S := by
    intro c S; unfold Colour.rb clq negG; simp
  have hl4 : ℓ ≤ ℓ ^ 4 := by
    have := Nat.pow_le_pow_right (show 1 ≤ ℓ by omega) (show 1 ≤ 4 by omega); simpa using this
  have hkℓ : ℓ + 1 ≤ k := by omega
  have hq : 0 < k - 1 := by omega
  have hkm : k ≤ m := by
    have : k ≤ 64 * ℓ ^ 4 * k := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hB : Sunflower.fact ℓ * (2 * ℓ) ^ ℓ ≤ (2 * ℓ * ℓ) ^ ℓ := by
    have e : (2 * ℓ * ℓ) ^ ℓ = ℓ ^ ℓ * (2 * ℓ) ^ ℓ := by
      rw [← Nat.mul_pow, Nat.mul_comm ℓ (2 * ℓ)]
    rw [e]
    exact Nat.mul_le_mul_right _ (fact_le _ f0 fS ℓ)
  have hB1 : 1 ≤ Sunflower.fact ℓ * (2 * ℓ) ^ ℓ :=
    Nat.mul_pos (fact_pos _ f0 fS ℓ) (Nat.pow_pos (by omega))
  have hSF : SF (2 * ℓ + 1) ℓ (Sunflower.fact ℓ * (2 * ℓ) ^ ℓ) := fun F h1 h2 h3 =>
    Sunflower.sunflower_sets (2 * ℓ + 1) ℓ F h1 h2 (by simpa using h3)
  have hKs : ∀ K ∈ KSub.ksub (List.range m) k, K.Nodup ∧ K.length = k ∧ ∀ x ∈ K, x < m := by
    intro K hK
    obtain ⟨hs, hl⟩ := KSub.mem_ksub hK
    exact ⟨hs.nodup List.nodup_range, hl, fun x hx => List.mem_range.1 (hs.subset hx)⟩
  have hratio : KSub.ch (m - (ℓ + 1)) (k - (ℓ + 1)) * (m - ℓ) ^ (ℓ + 1)
      ≤ (KSub.ksub (List.range m) k).length * k ^ (ℓ + 1) := by
    rw [KSub.ksub_length, List.length_range]; exact CCArith.pos_ratio m k ℓ hkℓ
  have hpos : ∀ Ts : List (List Nat), (∀ T ∈ Ts, T.Nodup ∧ (∀ i ∈ T, i < m) ∧ ℓ + 1 ≤ T.length) →
      ((KSub.ksub (List.range m) k).filter fun K =>
        Ts.any fun T => T.all fun i => decide (i ∈ K)).length
        ≤ Ts.length * KSub.ch (m - (ℓ + 1)) (k - (ℓ + 1)) := by
    intro Ts hT
    have := KSub.pos_count (List.range m) List.nodup_range k ℓ Ts
      (fun T h => ⟨(hT T h).1, fun i hi => List.mem_range.2 ((hT T h).2.1 i hi), (hT T h).2.2⟩) hkℓ
    simpa [KSub.sub] using this
  have hneg : ∀ ev, Ev (2 * ℓ) ℓ m ev →
      Colour.tot (k - 1) (List.range m) (hit ev) (fun _ => 0)
        ≤ Colour.ch2 ℓ ^ (2 * ℓ) * (k - 1) ^ (m - 2 * ℓ) := by
    intro ev h
    obtain ⟨hl, hS, hpw⟩ := h
    have := Colour.petal_count (k - 1) ℓ hq ev.1 (List.range m) ev.2 List.nodup_range
      (fun S h => ⟨(hS S h).1, (hS S h).2.1, fun x hx => List.mem_range.2 ((hS S h).2.2 x hx)⟩)
      hpw (fun _ => 0)
    rw [hl, List.length_range] at this
    refine Nat.le_trans (Nat.le_of_eq ?_) this
    have e : hit ev = fun c => if Colour.rb c ev.1 ∧ ∀ S ∈ ev.2, ¬ Colour.rb c S then 1 else 0 := by
      funext c; unfold hit; simp only [clq_rb]
    rw [e]
  have hrb : ∀ S : List Nat, S.Nodup → S.length ≤ ℓ → (∀ x ∈ S, x < m) →
      (k - 1) ^ m - Colour.ch2 ℓ * (k - 1) ^ (m - 1)
        ≤ Colour.tot (k - 1) (List.range m) (rbw m k S) (fun _ => 0) := by
    intro S hS hSl hSm
    have := CCArith.rb_count (k - 1) ℓ m hq S hS hSl hSm (rbw m k S)
      (fun c hc hr => by unfold rbw; rw [if_pos ⟨hc, (clq_rb c S).2 hr⟩]; exact Nat.le_refl 1) (fun _ => 0)
    omega
  exact cc_param1 m k ℓ _ hℓ hB1 hB hSF hk hm Rf (KSub.ksub (List.range m) k) hKs _
    (ch_pos _ c0 cS _ _ (by omega)) hratio hpos
    (fun f => Colour.tot (k - 1) (List.range m) f (fun _ => 0))
    (fun f g h => Colour.tot_mono _ _ f g h _) (fun f g => Nat.le_of_eq (Colour.tot_add _ _ f g _))
    (by rw [Colour.tot_const]; simp) (Colour.ch2 ℓ) (ch2_le _ d0 dS ℓ) hneg hrb

end Programme.«20261025-0459b-proof-complexity».CCUnb

#print axioms Programme.«20261025-0459b-proof-complexity».CCUnb.cc_unb
