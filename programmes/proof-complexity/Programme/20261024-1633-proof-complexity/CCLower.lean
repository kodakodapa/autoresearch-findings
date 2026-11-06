import Programme.«20261024-1633-proof-complexity».CCApprox

/-!
# Counting form of the approximation bound for clique–colouring

`cc_approx` (K23) gives error lists `pe`, `ne` of length `≤ L = s (2k+6) (2WB+1)^2`. Here the two
counting steps are taken as hypotheses, in the form of pr's lemmas:
* positive side: a list `Ks` of `k`-sets of vertices `< m` such that any list `Ts` of sets of size
  `≥ ℓ+1` is contained in at most `|Ts| c₁` members of `Ks` (pr's `pos_count` with
  `Ks = ksub (range m) k`, `c₁ = ch (m-ℓ-1) (k-ℓ-1)`);
* negative side: a monotone subadditive functional `μ` on functions of colourings (pr's
  `tot q V · c₀`), every pluck event hit by `μ`-mass `≤ c₂` (pr's `petal_count`), and every small
  `S` rainbow, on proper `(k-1)`-colourings, with `μ`-mass `≥ N₀`.
Conclusion: `|Ks| ≤ L c₁` or `N₀ ≤ L c₂`. This is the known Bonet–Pitassi–Raz bound for tree-like
CP with bounded coefficients, before choosing parameters.
-/

namespace Programme.«20261024-1633-proof-complexity».CCLower

open Programme.«20261024-1633-proof-complexity».RealApprox Programme.«20261024-1633-proof-complexity».Pluck Programme.«20261024-1633-proof-complexity».CP Programme.«20261024-1633-proof-complexity».CPRange Programme.«20261024-1633-proof-complexity».CliqueColour Programme.«20261024-1633-proof-complexity».CCApprox

/-- Union bound for a monotone subadditive functional. -/
theorem mu_sum {β : Type} (μ : ((Nat → Nat) → Nat) → Nat)
    (hmono : ∀ f g : (Nat → Nat) → Nat, (∀ c, f c ≤ g c) → μ f ≤ μ g)
    (hadd : ∀ f g : (Nat → Nat) → Nat, μ (fun c => f c + g c) ≤ μ f + μ g)
    (hzero : μ (fun _ => 0) = 0) (g : β → (Nat → Nat) → Nat) :
    ∀ L : List β, μ (fun c => (L.map fun b => g b c).sum) ≤ (L.map fun b => μ (g b)).sum
  | [] => by simp [hzero]
  | b :: L => by
    simp only [List.map_cons, List.sum_cons]
    exact Nat.le_trans (hadd _ _) (Nat.add_le_add_left (mu_sum μ hmono hadd hzero g L) _)

theorem sum_le_len {β : Type} (h : β → Nat) (c : Nat) :
    ∀ L : List β, (∀ b ∈ L, h b ≤ c) → (L.map h).sum ≤ L.length * c
  | [], _ => by simp
  | b :: L, hL => by
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    have := sum_le_len h c L (fun b' hb' => hL b' (List.mem_cons_of_mem _ hb'))
    have := hL b (by simp)
    omega

theorem le_sum_mem {β : Type} (h : β → Nat) :
    ∀ L : List β, ∀ b ∈ L, h b ≤ (L.map h).sum
  | [], _, hb => by simp at hb
  | x :: L, b, hb => by
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 hb with rfl | hb
    · omega
    · have := le_sum_mem h L b hb; omega

/-- Indicator that an event hits the colouring `c`: core rainbow, no petal rainbow. -/
def hit (ev : List Nat × List (List Nat)) (c : Nat → Nat) : Nat :=
  if clq (negG c) ev.1 ∧ ∀ S' ∈ ev.2, ¬ clq (negG c) S' then 1 else 0

/-- Indicator that `c` is a proper `(k-1)`-colouring of the vertices `< m` making `S` rainbow. -/
def rbw (m k : Nat) (S : List Nat) (c : Nat → Nat) : Nat :=
  if (∀ i, i < m → c i < k - 1) ∧ clq (negG c) S then 1 else 0

theorem cc_lower (m k p ℓ B : Nat) (hp : 2 ≤ p) (hℓ : 2 ≤ ℓ) (hB : 1 ≤ B) (hSF : SF p ℓ B)
    (Rf : BRefutation (CC m k))
    (Ks : List (List Nat)) (hKs : ∀ K ∈ Ks, K.Nodup ∧ K.length = k ∧ ∀ x ∈ K, x < m) (c₁ : Nat)
    (hpos : ∀ Ts : List (List Nat), (∀ T ∈ Ts, T.Nodup ∧ (∀ i ∈ T, i < m) ∧ ℓ + 1 ≤ T.length) →
      (Ks.filter fun K => Ts.any fun T => T.all fun i => decide (i ∈ K)).length ≤ Ts.length * c₁)
    (μ : ((Nat → Nat) → Nat) → Nat)
    (hmono : ∀ f g : (Nat → Nat) → Nat, (∀ c, f c ≤ g c) → μ f ≤ μ g)
    (hadd : ∀ f g : (Nat → Nat) → Nat, μ (fun c => f c + g c) ≤ μ f + μ g)
    (hzero : μ (fun _ => 0) = 0) (c₂ N₀ : Nat)
    (hneg : ∀ ev, Ev p ℓ m ev → μ (hit ev) ≤ c₂)
    (hrb : ∀ S : List Nat, S.Nodup → S.length ≤ ℓ → (∀ x ∈ S, x < m) → N₀ ≤ μ (rbw m k S)) :
    Ks.length ≤ Rf.size * (2 * k + 6) * (2 * Rf.W.toNat * B + 1) ^ 2 * c₁ ∨
    N₀ ≤ Rf.size * (2 * k + 6) * (2 * Rf.W.toNat * B + 1) ^ 2 * c₂ := by
  obtain ⟨pe, ne, hpe, hne, hpe', hne', hcase⟩ := cc_approx m k p ℓ B hp hℓ hB hSF Rf
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

end Programme.«20261024-1633-proof-complexity».CCLower
