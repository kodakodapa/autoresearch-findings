import Programme.«20261025-0459b-proof-complexity».Pluck1
import Programme.«20261024-1633-proof-complexity».ApproxRCR

/-!
# The approximation method on arbitrary monotone real formulas

`ApproxRCR.approx` needs every subformula to have range `≤ R` (it closes approximators per value
class). With the value-independent closing `Work.Pluck1.close1`, the same gate-by-gate argument
works for every monotone real formula `CPInterp.RC` (unbounded integer gates): each approximator
has at most `B` entries, and a formula with `s` gates yields at most `s ℓ (B+1)^2` positive error
sets and at most `s ℓ (B+1)^2` pluck events. Known argument (Razborov; Pudlák 1997 for real
gates), formalised here.
-/

namespace Programme.«20261025-0459b-proof-complexity».ApproxRC

open Programme.«20261024-1633-proof-complexity».RealApprox
open Programme.«20261024-1633-proof-complexity».Pluck
open Programme.«20261024-1633-proof-complexity».CP
open Programme.«20261024-1633-proof-complexity».CPInterp
open Programme.«20261024-1633-proof-complexity».ApproxRCR (nub mem_nub nodup_nub ns_nub nubE nubE_eval comb_len)
open Programme.«20261025-0459b-proof-complexity».Pluck1

theorem wt_le (ℓ : Nat) : ∀ l : List (List Nat × Int), (∀ e ∈ l, e.1.length ≤ ℓ) →
    wt l ≤ ℓ * l.length
  | [], _ => by simp [wt]
  | e :: l, h => by
    have := wt_le ℓ l (fun e he => h e (List.mem_cons_of_mem _ he))
    have := h e (List.mem_cons_self ..)
    simp only [wt, List.map_cons, List.sum_cons, List.length_cons, Nat.mul_succ] at *
    omega

/-- Finishing a gate: dedup vertices, trim to sets of size `≤ ℓ`, close. -/
theorem finish1 (p ℓ m B : Nat) (hp : 1 ≤ p) (hSF : SF (p + 1) ℓ B) (c : Approx)
    (hc : ∀ e ∈ c.ents, ns e.1 ∧ ∀ x ∈ e.1, x < m) :
    ∃ b : Approx, ∃ pe : List (List Nat), ∃ ne : List (List Nat × List (List Nat)),
      Inv ℓ m b ∧ b.ents.length ≤ B ∧
      pe.length ≤ c.ents.length ∧ ne.length ≤ ℓ * c.ents.length ∧
      (∀ T ∈ pe, T.Nodup ∧ ℓ + 1 ≤ T.length ∧ ∀ x ∈ T, x < m) ∧ (∀ ev ∈ ne, Ev p ℓ m ev) ∧
      (∀ K, eval c (posG K) ≤ eval b (posG K) ∨ ∃ T ∈ pe, ∀ i ∈ T, i ∈ K) ∧
      (∀ G, eval b G ≤ eval c G ∨ ∃ ev ∈ ne, clq G ev.1 ∧ ∀ S ∈ ev.2, ¬ clq G S) := by
  have h1 : ∀ e ∈ (nubE c).ents, e.1.Nodup ∧ ns e.1 ∧ (∀ x ∈ e.1, x < m) := by
    intro e he
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    obtain ⟨hn, hm⟩ := hc e0 he0
    exact ⟨nodup_nub _, ns_nub hn, fun x hx => hm x (mem_nub.1 hx)⟩
  let c3 := trim ℓ (nubE c)
  have h3 : ∀ e ∈ c3.ents, e ∈ (nubE c).ents ∧ e.1.length ≤ ℓ := by
    intro e he
    have h' := List.mem_filter.1 he
    exact ⟨h'.1, by simpa using h'.2⟩
  have hI3 : Inv ℓ m c3 := by
    intro e he
    obtain ⟨hm, hl⟩ := h3 e he
    obtain ⟨hn, hns, hv⟩ := h1 e hm
    exact ⟨hn, hl, hv, hns⟩
  obtain ⟨b, evs, _, hb2, hb3, hb4, hb5, hb6, hb7⟩ :=
    close1 p ℓ m B hp hSF (wt c3.ents + 1) c3 (Nat.lt_succ_self _) hI3
  have hlen3 : c3.ents.length ≤ c.ents.length := by
    have a2 : c3.ents.length ≤ (nubE c).ents.length := List.length_filter_le _ _
    have a3 : (nubE c).ents.length = c.ents.length := List.length_map _
    omega
  have hw3 : wt c3.ents ≤ ℓ * c3.ents.length := wt_le ℓ _ (fun e he => (h3 e he).2)
  let pe := ((nubE c).ents.filter fun e => decide (ℓ < e.1.length)).map Prod.fst
  refine ⟨b, pe, evs, hb2, hb3, ?_, ?_, ?_, hb5, ?_, ?_⟩
  · have a1 := List.length_filter_le (fun e : List Nat × Int => decide (ℓ < e.1.length))
      (nubE c).ents
    have a3 : (nubE c).ents.length = c.ents.length := List.length_map _
    simp only [pe, List.length_map]
    omega
  · exact Nat.le_trans hb4 (Nat.le_trans hw3 (Nat.mul_le_mul_left _ hlen3))
  · intro T hT
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hT
    have := List.mem_filter.1 he
    have hl : ℓ < e.1.length := by simpa using this.2
    obtain ⟨hn, _, hv⟩ := h1 e this.1
    exact ⟨hn, hl, hv⟩
  · intro K
    by_cases h : ∃ T ∈ pe, ∀ i ∈ T, i ∈ K
    · exact Or.inr h
    · left
      have ht : eval (nubE c) (posG K) ≤ eval c3 (posG K) := by
        apply trim_ge
        intro e he hcl
        apply Nat.le_of_not_lt
        intro hl
        apply h
        refine ⟨e.1, List.mem_map.2 ⟨e, List.mem_filter.2 ⟨he, by simpa using hl⟩, rfl⟩, ?_⟩
        exact (clq_posG (h1 e he).2.1).1 hcl
      rw [nubE_eval c] at ht
      exact Int.le_trans ht (hb6 _)
  · intro G
    rcases hb7 G with h | h
    · left
      have := trim_le ℓ (nubE c) G
      rw [nubE_eval] at this
      exact Int.le_trans h this
    · exact Or.inr h

theorem ent_ns {ℓ m : Nat} {a : Approx} (hI : Inv ℓ m a) :
    ∀ e ∈ ent a, ns e.1 ∧ ∀ x ∈ e.1, x < m := by
  intro e he
  rcases List.mem_cons.1 he with h | h
  · subst h; exact ⟨ns_nil, by simp⟩
  · obtain ⟨_, _, hv, hns⟩ := hI e h
    exact ⟨hns, hv⟩

/-- **Approximation, arbitrary monotone real formulas.** Let `f` be a monotone real formula
(`RC P f s`, gates arbitrary monotone `ℤ → ℤ`, `ℤ × ℤ → ℤ`) read on graphs through `emb`, with
input approximators `inA` that are exact enough on the test graphs. Given `SF (p+1) ℓ B`
(`p, ℓ ≥ 1`), there are an approximator `a` of `f` with at most `B` entries and lists `pe`
(sets of size `> ℓ`) and `ne` (events), each of length at most `s ℓ (B+1)^2`, such that on every
clique graph `posG K` either `f ≤ a` or `K` contains a set of `pe`, and on every colouring graph
`negG c` either `a ≤ f` or some event of `ne` has its core rainbow and no petal rainbow. -/
theorem approx1 {V : Type} (P : V → Bool) (p ℓ m B : Nat) (hp : 1 ≤ p) (hℓ : 1 ≤ ℓ)
    (hSF : SF (p + 1) ℓ B)
    (emb : (Nat → Nat → Bool) → V → Bool) (inA : V → Approx)
    (hin : ∀ u, P u = true → Inv ℓ m (inA u) ∧ (inA u).ents.length ≤ B ∧
      (∀ K, val (emb (posG K)) u ≤ eval (inA u) (posG K)) ∧
      (∀ c, eval (inA u) (negG c) ≤ val (emb (negG c)) u)) :
    ∀ {f : (V → Bool) → Int} {s : Nat}, RC P f s →
    ∃ a : Approx, ∃ pe : List (List Nat), ∃ ne : List (List Nat × List (List Nat)),
      Inv ℓ m a ∧ a.ents.length ≤ B ∧
      pe.length ≤ s * (ℓ * (B + 1) ^ 2) ∧ ne.length ≤ s * (ℓ * (B + 1) ^ 2) ∧
      (∀ T ∈ pe, T.Nodup ∧ ℓ + 1 ≤ T.length ∧ ∀ x ∈ T, x < m) ∧ (∀ ev ∈ ne, Ev p ℓ m ev) ∧
      (∀ K, f (emb (posG K)) ≤ eval a (posG K) ∨ ∃ T ∈ pe, ∀ i ∈ T, i ∈ K) ∧
      (∀ c, eval a (negG c) ≤ f (emb (negG c)) ∨
        ∃ ev ∈ ne, clq (negG c) ev.1 ∧ ∀ S ∈ ev.2, ¬ clq (negG c) S) := by
  have hQ2 : (B + 1) ^ 2 ≤ ℓ * (B + 1) ^ 2 := Nat.le_mul_of_pos_left _ hℓ
  have hQ : B ≤ (B + 1) ^ 2 := by
    rw [Nat.pow_two]; exact Nat.le_trans (Nat.le_succ _) (Nat.le_mul_of_pos_left _ (by omega))
  intro f s hf
  induction hf with
  | const k =>
    refine ⟨constA k, [], [], fun e he => by simp [constA] at he, by simp [constA], by simp,
      by simp, by simp, by simp,
      fun K => Or.inl (Int.le_of_eq (const_eval k _).symm),
      fun c => Or.inl (Int.le_of_eq (const_eval k _))⟩
  | inp u hu =>
    obtain ⟨h1, h4, h5, h6⟩ := hin u hu
    exact ⟨inA u, [], [], h1, h4, by simp, by simp, by simp, by simp,
      fun K => Or.inl (h5 K), fun c => Or.inl (h6 c)⟩
  | @gate1 f s g hg _ ih =>
    obtain ⟨a, pe, ne, ha2, ha4, ha5, ha6, ha7, ha8, ha9, ha10⟩ := ih
    have hc : ∀ e ∈ (amap g a).ents, ns e.1 ∧ ∀ x ∈ e.1, x < m := by
      intro e he
      obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
      obtain ⟨_, _, hv, hns⟩ := ha2 e0 he0
      exact ⟨hns, hv⟩
    obtain ⟨b, pe', ne', hb2, hb4, hb5, hb6, hb7, hb8, hb9, hb10⟩ :=
      finish1 p ℓ m B hp hSF (amap g a) hc
    have hl : (amap g a).ents.length = a.ents.length := List.length_map _
    have hlb : ℓ * (amap g a).ents.length ≤ ℓ * (B + 1) ^ 2 :=
      Nat.mul_le_mul_left _ (by omega)
    refine ⟨b, pe ++ pe', ne ++ ne', hb2, hb4, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [List.length_append, Nat.succ_mul]; omega
    · rw [List.length_append, Nat.succ_mul]; omega
    · intro T hT
      rcases List.mem_append.1 hT with h | h
      · exact ha7 T h
      · exact hb7 T h
    · intro ev hev
      rcases List.mem_append.1 hev with h | h
      · exact ha8 ev h
      · exact hb8 ev h
    · intro K
      rcases ha9 K with h | ⟨T, hT, hK⟩
      · rcases hb9 K with h' | ⟨T, hT, hK⟩
        · left
          rw [amap_eval g hg] at h'
          exact Int.le_trans (hg _ _ h) h'
        · exact Or.inr ⟨T, List.mem_append.2 (Or.inr hT), hK⟩
      · exact Or.inr ⟨T, List.mem_append.2 (Or.inl hT), hK⟩
    · intro c
      rcases ha10 c with h | ⟨ev, hev, hE⟩
      · rcases hb10 (negG c) with h' | ⟨ev, hev, hE⟩
        · left
          rw [amap_eval g hg] at h'
          exact Int.le_trans h' (hg _ _ h)
        · exact Or.inr ⟨ev, List.mem_append.2 (Or.inr hev), hE⟩
      · exact Or.inr ⟨ev, List.mem_append.2 (Or.inl hev), hE⟩
  | @gate2 f h s t g hg _ _ ih1 ih2 =>
    obtain ⟨a, pe, ne, ha2, ha4, ha5, ha6, ha7, ha8, ha9, ha10⟩ := ih1
    obtain ⟨a', pe', ne', ha2', ha4', ha5', ha6', ha7', ha8', ha9', ha10'⟩ := ih2
    have ea := ent_ns ha2
    have ea' := ent_ns ha2'
    have hc : ∀ e ∈ (comb g a a').ents, ns e.1 ∧ ∀ x ∈ e.1, x < m := by
      intro x hx
      obtain ⟨e, he, e', he', rfl⟩ := mem_comb hx
      obtain ⟨n1, v1⟩ := ea e he
      obtain ⟨n2, v2⟩ := ea' e' he'
      refine ⟨ns_append n1 n2, fun x hx => ?_⟩
      rcases List.mem_append.1 hx with hx | hx
      · exact v1 x hx
      · exact v2 x hx
    obtain ⟨b, qe, qn, hb2, hb4, hb5, hb6, hb7, hb8, hb9, hb10⟩ :=
      finish1 p ℓ m B hp hSF (comb g a a') hc
    have hl : (comb g a a').ents.length ≤ (B + 1) ^ 2 := by
      have : (comb g a a').ents.length = (a.ents.length + 1) * (a'.ents.length + 1) := by
        simp only [comb]; rw [comb_len]; rfl
      rw [this, Nat.pow_two]
      exact Nat.mul_le_mul (by omega) (by omega)
    have hlb : ℓ * (comb g a a').ents.length ≤ ℓ * (B + 1) ^ 2 := Nat.mul_le_mul_left _ hl
    have hns : ∀ e ∈ ent a, ns e.1 := fun e he => (ea e he).1
    have hns' : ∀ e ∈ ent a', ns e.1 := fun e he => (ea' e he).1
    refine ⟨b, pe ++ pe' ++ qe, ne ++ ne' ++ qn, hb2, hb4, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.length_append, Nat.add_mul, Nat.one_mul]; omega
    · simp only [List.length_append, Nat.add_mul, Nat.one_mul]; omega
    · intro T hT
      simp only [List.mem_append] at hT
      rcases hT with (h | h) | h
      · exact ha7 T h
      · exact ha7' T h
      · exact hb7 T h
    · intro ev hev
      simp only [List.mem_append] at hev
      rcases hev with (h | h) | h
      · exact ha8 ev h
      · exact ha8' ev h
      · exact hb8 ev h
    · intro K
      rcases ha9 K with h1 | ⟨T, hT, hK⟩
      · rcases ha9' K with h2 | ⟨T, hT, hK⟩
        · rcases hb9 K with h3 | ⟨T, hT, hK⟩
          · left
            rw [comb_pos g hg K a a' hns hns'] at h3
            exact Int.le_trans (hg _ _ _ _ h1 h2) h3
          · exact Or.inr ⟨T, by simp [hT], hK⟩
        · exact Or.inr ⟨T, by simp [hT], hK⟩
      · exact Or.inr ⟨T, by simp [hT], hK⟩
    · intro c
      rcases ha10 c with h1 | ⟨ev, hev, hE⟩
      · rcases ha10' c with h2 | ⟨ev, hev, hE⟩
        · rcases hb10 (negG c) with h3 | ⟨ev, hev, hE⟩
          · left
            exact Int.le_trans h3 (Int.le_trans (comb_le g hg a a' _) (hg _ _ _ _ h1 h2))
          · exact Or.inr ⟨ev, by simp [hev], hE⟩
        · exact Or.inr ⟨ev, by simp [hev], hE⟩
      · exact Or.inr ⟨ev, by simp [hev], hE⟩

end Programme.«20261025-0459b-proof-complexity».ApproxRC

#print axioms Programme.«20261025-0459b-proof-complexity».ApproxRC.approx1
