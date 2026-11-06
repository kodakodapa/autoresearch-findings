import Programme.«20261024-1633-proof-complexity».CCParam

/-!
# Closed assembly of the tree-like CP* clique–colouring bound, peer lemmas as hypotheses

`cc_assembly` takes pr's definitions (`Sunflower.fact`, `KSub.ch`, `KSub.ksub`, `KSub.sub`,
`Colour.ch2`, `Colour.tot`, `Colour.rb`) as parameters, fixed by their defining equations, and
pr's lemmas (K16 `sunflower_sets`; K20 `mem_ksub`, `ksub_length`, `pos_count`; K17 `petal_count`,
`tot_mono`, `tot_add`, `tot_const`; K26 `rb_count`, `pos_ratio`) as hypotheses, each stated
verbatim up to these parameters. Once those modules are in `/library`, each hypothesis is the lemma
of the same name and each equation is `rfl`. Known result (Bonet–Pitassi–Raz 1997), not new.
-/

set_option linter.unusedVariables false

namespace Programme.«20261024-1633-proof-complexity».CCAssembly

open Programme.«20261024-1633-proof-complexity».RealApprox Programme.«20261024-1633-proof-complexity».Pluck Programme.«20261024-1633-proof-complexity».CP Programme.«20261024-1633-proof-complexity».CPRange Programme.«20261024-1633-proof-complexity».CliqueColour Programme.«20261024-1633-proof-complexity».CCLower Programme.«20261024-1633-proof-complexity».CCParam

theorem fact_le (fact : Nat → Nat) (f0 : fact 0 = 1) (fS : ∀ n, fact (n+1) = (n+1) * fact n) :
    ∀ n, fact n ≤ n ^ n
  | 0 => by rw [f0]; decide
  | n+1 => by
    rw [fS, Nat.pow_succ, Nat.mul_comm ((n+1)^n)]
    exact Nat.mul_le_mul_left _ (Nat.le_trans (fact_le fact f0 fS n) (Nat.pow_le_pow_left (by omega) n))

theorem fact_pos (fact : Nat → Nat) (f0 : fact 0 = 1) (fS : ∀ n, fact (n+1) = (n+1) * fact n) :
    ∀ n, 0 < fact n
  | 0 => by rw [f0]; decide
  | n+1 => by rw [fS]; exact Nat.mul_pos (Nat.succ_pos n) (fact_pos fact f0 fS n)

theorem ch_pos (ch : Nat → Nat → Nat) (c0 : ∀ n, ch n 0 = 1)
    (cS : ∀ n j, ch (n+1) (j+1) = ch n (j+1) + ch n j) : ∀ n j, j ≤ n → 0 < ch n j
  | n, 0, _ => by rw [c0]; decide
  | 0, _+1, h => by omega
  | n+1, j+1, h => by rw [cS]; have := ch_pos ch c0 cS n j (by omega); omega

theorem ch2_le (ch2 : Nat → Nat) (d0 : ch2 0 = 0) (dS : ∀ n, ch2 (n+1) = ch2 n + n) :
    ∀ n, ch2 n ≤ n * n
  | 0 => by rw [d0]; decide
  | n+1 => by
    rw [dS]; have := ch2_le ch2 d0 dS n
    have : (n+1) * (n+1) = n * n + 2 * n + 1 := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]; omega
    omega

/-- **Assembly.** For `ℓ ≥ 2`, `k-1 ≥ 64ℓ⁴`, `m ≥ 64ℓ⁴k + ℓ`, given pr's definitions and lemmas
as hypotheses, every tree-like CP refutation of `CC m k` with `s` nodes and line weights `≤ W`
has `2^{4ℓ} ≤ 18 s (2k+6) (W+1)^2`. -/
theorem cc_assembly
    (fact : Nat → Nat) (f0 : fact 0 = 1) (fS : ∀ n, fact (n+1) = (n+1) * fact n)
    (ch : Nat → Nat → Nat) (c0 : ∀ n, ch n 0 = 1)
    (cS : ∀ n j, ch (n+1) (j+1) = ch n (j+1) + ch n j)
    (ch2 : Nat → Nat) (d0 : ch2 0 = 0) (dS : ∀ n, ch2 (n+1) = ch2 n + n)
    (ksub : List Nat → Nat → List (List Nat)) (sub : List Nat → List Nat → Bool)
    (hsub : ∀ T K, sub T K = T.all fun i => decide (i ∈ K))
    (tot : Nat → List Nat → ((Nat → Nat) → Nat) → (Nat → Nat) → Nat)
    (rb : (Nat → Nat) → List Nat → Prop) [∀ c S, Decidable (rb c S)]
    (hrbd : ∀ c S, rb c S ↔ ∀ a ∈ S, ∀ b ∈ S, a ≠ b → c a ≠ c b)
    -- K16
    (sunflower_sets : ∀ (p ℓ : Nat) (F : List (List Nat)),
      (∀ S ∈ F, S.length ≤ ℓ) → F.Pairwise (fun S T => ∃ y, ¬ (y ∈ S ↔ y ∈ T)) →
      fact ℓ * (p-1)^ℓ < F.length →
      ∃ G : List (List Nat), G.length = p ∧ (∀ S ∈ G, S ∈ F) ∧
        G.Pairwise (fun S T => ∃ y, ¬ (y ∈ S ↔ y ∈ T)) ∧
        G.Pairwise (fun S T => ∀ y, y ∈ S → y ∈ T → ∀ R ∈ G, y ∈ R))
    -- K20
    (mem_ksub : ∀ {V : List Nat} {k : Nat} {K : List Nat}, K ∈ ksub V k →
      K.Sublist V ∧ K.length = k)
    (ksub_length : ∀ (V : List Nat) (k : Nat), (ksub V k).length = ch V.length k)
    (pos_count : ∀ (V : List Nat) (hV : V.Nodup) (k ℓ : Nat) (Ts : List (List Nat))
      (hTs : ∀ T ∈ Ts, T.Nodup ∧ (∀ i ∈ T, i ∈ V) ∧ ℓ + 1 ≤ T.length) (hk : ℓ + 1 ≤ k),
      ((ksub V k).filter (fun K => Ts.any fun T => sub T K)).length
        ≤ Ts.length * ch (V.length - (ℓ + 1)) (k - (ℓ + 1)))
    -- K17 and its `tot` lemmas
    (tot_mono : ∀ (q : Nat) (W : List Nat) (f g : (Nat → Nat) → Nat), (∀ c, f c ≤ g c) →
      ∀ c, tot q W f c ≤ tot q W g c)
    (tot_add : ∀ (q : Nat) (W : List Nat) (f g : (Nat → Nat) → Nat),
      ∀ c, tot q W (fun c => f c + g c) c = tot q W f c + tot q W g c)
    (tot_const : ∀ (q : Nat) (W : List Nat) (k : Nat),
      ∀ c, tot q W (fun _ => k) c = q ^ W.length * k)
    (petal_count : ∀ (q ℓ : Nat) (hq : 0 < q) (Y V : List Nat) (Ss : List (List Nat))
      (hV : V.Nodup) (hS : ∀ S ∈ Ss, S.Nodup ∧ S.length ≤ ℓ ∧ ∀ x ∈ S, x ∈ V)
      (hsf : Ss.Pairwise (fun S T => ∀ x, x ∈ S → x ∈ T → x ∈ Y)) (c : Nat → Nat),
      tot q V (fun c => if rb c Y ∧ ∀ S ∈ Ss, ¬ rb c S then 1 else 0) c
        ≤ ch2 ℓ ^ Ss.length * q ^ (V.length - Ss.length))
    -- K26
    (rb_count : ∀ (q ℓ m : Nat) (hq : 0 < q) (S : List Nat) (hS : S.Nodup) (hSl : S.length ≤ ℓ)
      (hSm : ∀ x ∈ S, x < m) (f : (Nat → Nat) → Nat)
      (hf : ∀ c : Nat → Nat, (∀ i, i < m → c i < q) → rb c S → 1 ≤ f c) (c : Nat → Nat),
      q ^ m ≤ tot q (List.range m) f c + ch2 ℓ * q ^ (m - 1))
    (pos_ratio : ∀ (m k ℓ : Nat) (hk : ℓ + 1 ≤ k),
      ch (m - (ℓ + 1)) (k - (ℓ + 1)) * (m - ℓ) ^ (ℓ + 1) ≤ ch m k * k ^ (ℓ + 1))
    (m k ℓ : Nat) (hℓ : 2 ≤ ℓ) (hk : 64 * ℓ ^ 4 ≤ k - 1) (hm : 64 * ℓ ^ 4 * k + ℓ ≤ m)
    (Rf : BRefutation (CC m k)) :
    2 ^ (4 * ℓ) ≤ 18 * (Rf.size * (2 * k + 6) * (Rf.W.toNat + 1) ^ 2) := by
  have clq_rb : ∀ (c : Nat → Nat) (S : List Nat), clq (negG c) S ↔ rb c S := by
    intro c S; rw [hrbd]; unfold clq negG; simp
  have hl4 : ℓ ≤ ℓ ^ 4 := by
    have := Nat.pow_le_pow_right (show 1 ≤ ℓ by omega) (show 1 ≤ 4 by omega); simpa using this
  have hkℓ : ℓ + 1 ≤ k := by omega
  have hkm : k ≤ m := by
    have : k ≤ 64 * ℓ ^ 4 * k := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hq : 0 < k - 1 := by omega
  have hB : fact ℓ * (2 * ℓ - 1) ^ ℓ ≤ (2 * ℓ * ℓ) ^ ℓ := by
    have e : (2 * ℓ * ℓ) ^ ℓ = ℓ ^ ℓ * (2 * ℓ) ^ ℓ := by
      rw [← Nat.mul_pow, Nat.mul_comm ℓ (2 * ℓ)]
    rw [e]
    exact Nat.mul_le_mul (fact_le fact f0 fS ℓ) (Nat.pow_le_pow_left (by omega) ℓ)
  have hB1 : 1 ≤ fact ℓ * (2 * ℓ - 1) ^ ℓ :=
    Nat.mul_pos (fact_pos fact f0 fS ℓ) (Nat.pow_pos (by omega))
  have hSF : SF (2 * ℓ) ℓ (fact ℓ * (2 * ℓ - 1) ^ ℓ) := fun F h1 h2 h3 =>
    sunflower_sets (2 * ℓ) ℓ F h1 h2 h3
  have hKs : ∀ K ∈ ksub (List.range m) k, K.Nodup ∧ K.length = k ∧ ∀ x ∈ K, x < m := by
    intro K hK
    obtain ⟨hs, hl⟩ := mem_ksub hK
    exact ⟨hs.nodup List.nodup_range, hl, fun x hx => List.mem_range.1 (hs.subset hx)⟩
  have hratio : ch (m - (ℓ + 1)) (k - (ℓ + 1)) * (m - ℓ) ^ (ℓ + 1)
      ≤ (ksub (List.range m) k).length * k ^ (ℓ + 1) := by
    rw [ksub_length, List.length_range]; exact pos_ratio m k ℓ hkℓ
  have hpos : ∀ Ts : List (List Nat), (∀ T ∈ Ts, T.Nodup ∧ (∀ i ∈ T, i < m) ∧ ℓ + 1 ≤ T.length) →
      ((ksub (List.range m) k).filter fun K => Ts.any fun T => T.all fun i => decide (i ∈ K)).length
        ≤ Ts.length * ch (m - (ℓ + 1)) (k - (ℓ + 1)) := by
    intro Ts hT
    have := pos_count (List.range m) List.nodup_range k ℓ Ts
      (fun T h => ⟨(hT T h).1, fun i hi => List.mem_range.2 ((hT T h).2.1 i hi), (hT T h).2.2⟩) hkℓ
    simpa [hsub] using this
  have hneg : ∀ ev, Ev (2 * ℓ) ℓ m ev →
      tot (k - 1) (List.range m) (hit ev) (fun _ => 0) ≤ ch2 ℓ ^ (2 * ℓ) * (k - 1) ^ (m - 2 * ℓ) := by
    intro ev h
    obtain ⟨hl, hS, hpw⟩ := h
    have := petal_count (k - 1) ℓ hq ev.1 (List.range m) ev.2 List.nodup_range
      (fun S h => ⟨(hS S h).1, (hS S h).2.1, fun x hx => List.mem_range.2 ((hS S h).2.2 x hx)⟩)
      hpw (fun _ => 0)
    rw [hl, List.length_range] at this
    refine Nat.le_trans (Nat.le_of_eq ?_) this
    have e : hit ev = fun c => if rb c ev.1 ∧ ∀ S ∈ ev.2, ¬ rb c S then 1 else 0 := by
      funext c; unfold hit; simp only [clq_rb]
    rw [e]
  have hrb : ∀ S : List Nat, S.Nodup → S.length ≤ ℓ → (∀ x ∈ S, x < m) →
      (k - 1) ^ m - ch2 ℓ * (k - 1) ^ (m - 1) ≤ tot (k - 1) (List.range m) (rbw m k S) (fun _ => 0) := by
    intro S hS hSl hSm
    have := rb_count (k - 1) ℓ m hq S hS hSl hSm (rbw m k S)
      (fun c hc hr => by unfold rbw; rw [if_pos ⟨hc, (clq_rb c S).2 hr⟩]; exact Nat.le_refl 1) (fun _ => 0)
    omega
  exact cc_param m k ℓ _ hℓ hB1 hB hSF hk hm Rf (ksub (List.range m) k) hKs _
    (ch_pos ch c0 cS _ _ (by omega)) hratio hpos (fun f => tot (k - 1) (List.range m) f (fun _ => 0))
    (fun f g h => tot_mono _ _ f g h _) (fun f g => Nat.le_of_eq (tot_add _ _ f g _))
    (by rw [tot_const]; simp) (ch2 ℓ) (ch2_le ch2 d0 dS ℓ) hneg hrb

end Programme.«20261024-1633-proof-complexity».CCAssembly
