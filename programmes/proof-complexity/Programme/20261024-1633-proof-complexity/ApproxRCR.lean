import Programme.«20261024-1633-proof-complexity».Pluck
import Programme.«20261024-1633-proof-complexity».CPRange

/-!
# The approximation method on range-bounded monotone real formulas

Every subformula of a formula of type `Work.CPRange.RCR P R` (K19) gets an approximator
(`Work.RealApprox.Approx`). Gates are approximated as follows:
* unary gate `g`: `amap g` (exact), then `finish`;
* binary gate `φ`: `comb φ` (never overshoots; exact on clique graphs `posG K`), then `finish`;
* `finish`: remove duplicate vertices inside each entry set (`nubE`, exact), `trim ℓ` (positive
  errors: the deleted sets of size `> ℓ`), `drop` (exact), `close` (K21; negative errors: the
  pluck events).

The base of every approximator is the value of its subformula at the all-false assignment and all
entry values are at most its value at the all-true assignment, so after `drop` all values lie in
`(f ⊥, f ⊥ + R]` and `class_count` bounds the size by `R B`. Main result: `approx`, an
approximator of the output, a list of positive error sets and a list of pluck events, each list of
length at most `s (R B + 1)^2` for a formula with `s` gates. This is the known approximation
argument (Razborov; Pudlák's real gates; Bonet–Pitassi–Raz), not a new result.
-/

namespace Programme.«20261024-1633-proof-complexity».ApproxRCR

open Programme.«20261024-1633-proof-complexity».RealApprox Programme.«20261024-1633-proof-complexity».Pluck Programme.«20261024-1633-proof-complexity».CP Programme.«20261024-1633-proof-complexity».CPInterp Programme.«20261024-1633-proof-complexity».CPRange

/-! ## Removing duplicate vertices -/

def nub : List Nat → List Nat
  | [] => []
  | x :: l => if x ∈ nub l then nub l else x :: nub l

theorem mem_nub {x : Nat} : ∀ {l : List Nat}, x ∈ nub l ↔ x ∈ l
  | [] => by simp [nub]
  | y :: l => by
    have ih := @mem_nub x l
    unfold nub
    split
    · rename_i h
      rw [ih, List.mem_cons]
      constructor
      · exact Or.inr
      · rintro (rfl | hx)
        · exact ih.1 h
        · exact hx
    · rw [List.mem_cons, ih, List.mem_cons]

theorem nodup_nub : ∀ l : List Nat, (nub l).Nodup
  | [] => by simp [nub]
  | y :: l => by
    have ih := nodup_nub l
    unfold nub
    split
    · exact ih
    · rename_i h
      exact List.nodup_cons.2 ⟨h, ih⟩

theorem ns_nub {S : List Nat} (h : ns S) : ns (nub S) := by
  intro i hi
  obtain ⟨j, hj, hji⟩ := h i (mem_nub.1 hi)
  exact ⟨j, mem_nub.2 hj, hji⟩

def nubE (a : Approx) : Approx := ⟨a.base, a.ents.map fun e => (nub e.1, e.2)⟩

theorem evalL_nub (G : Nat → Nat → Bool) (v₀ : Int) : ∀ l : List (List Nat × Int),
    evalL G v₀ (l.map fun e => (nub e.1, e.2)) = evalL G v₀ l
  | [] => rfl
  | e :: l => by
    have ih := evalL_nub G v₀ l
    have hc : clq G (nub e.1) ↔ clq G e.1 := clq_congr (fun y => mem_nub)
    simp only [List.map_cons, evalL, ih]
    by_cases h : clq G e.1
    · rw [if_pos (hc.2 h), if_pos h]
    · rw [if_neg (fun h' => h (hc.1 h')), if_neg h]

theorem nubE_eval (a : Approx) (G : Nat → Nat → Bool) : eval (nubE a) G = eval a G :=
  evalL_nub G a.base a.ents

/-! ## Finishing a gate: dedup, trim, drop, close -/

theorem finish (p ℓ m B R : Nat) (hp : 2 ≤ p) (hSF : SF p ℓ B) (top : Int) (c : Approx)
    (hc : ∀ e ∈ c.ents, ns e.1 ∧ (∀ x ∈ e.1, x < m) ∧ e.2 ≤ top) (hR : top ≤ c.base + R) :
    ∃ b : Approx, ∃ pe : List (List Nat), ∃ ne : List (List Nat × List (List Nat)),
      b.base = c.base ∧ Inv ℓ m b ∧ (∀ e ∈ b.ents, e.2 ≤ top) ∧ b.ents.length ≤ R * B ∧
      pe.length ≤ c.ents.length ∧ ne.length ≤ c.ents.length ∧
      (∀ T ∈ pe, T.Nodup ∧ ℓ + 1 ≤ T.length ∧ ∀ x ∈ T, x < m) ∧ (∀ ev ∈ ne, Ev p ℓ m ev) ∧
      (∀ K, eval c (posG K) ≤ eval b (posG K) ∨ ∃ T ∈ pe, ∀ i ∈ T, i ∈ K) ∧
      (∀ G, eval b G ≤ eval c G ∨ ∃ ev ∈ ne, clq G ev.1 ∧ ∀ S ∈ ev.2, ¬ clq G S) := by
  -- entries of the deduplicated approximator
  have h1 : ∀ e ∈ (nubE c).ents, e.1.Nodup ∧ ns e.1 ∧ (∀ x ∈ e.1, x < m) ∧ e.2 ≤ top := by
    intro e he
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    obtain ⟨hn, hm, ht⟩ := hc e0 he0
    exact ⟨nodup_nub _, ns_nub hn, fun x hx => hm x (mem_nub.1 hx), ht⟩
  let c3 := drop (trim ℓ (nubE c))
  have h3 : ∀ e ∈ c3.ents, e ∈ (nubE c).ents ∧ e.1.length ≤ ℓ ∧ c.base < e.2 := by
    intro e he
    have := List.mem_filter.1 he
    have h' := List.mem_filter.1 this.1
    exact ⟨h'.1, by simpa using h'.2, of_decide_eq_true this.2⟩
  have hI3 : Inv ℓ m c3 := by
    intro e he
    obtain ⟨hm, hl, _⟩ := h3 e he
    obtain ⟨hn, hns, hv, _⟩ := h1 e hm
    exact ⟨hn, hl, hv, hns⟩
  obtain ⟨b, evs, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8⟩ :=
    close p ℓ m B hp hSF c3.ents.length c3 (Nat.le_refl _) hI3
  have hval : ∀ e ∈ b.ents, c.base < e.2 ∧ e.2 ≤ top := by
    intro e he
    obtain ⟨e', he', heq⟩ := hb3 e he
    obtain ⟨hm, _, hlt⟩ := h3 e' he'
    rw [← heq]
    exact ⟨hlt, (h1 e' hm).2.2.2⟩
  have hlen3 : c3.ents.length ≤ c.ents.length := by
    have a1 : c3.ents.length ≤ (trim ℓ (nubE c)).ents.length := List.length_filter_le _ _
    have a2 : (trim ℓ (nubE c)).ents.length ≤ (nubE c).ents.length := List.length_filter_le _ _
    have a3 : (nubE c).ents.length = c.ents.length := List.length_map _
    omega
  let pe := ((nubE c).ents.filter fun e => decide (ℓ < e.1.length)).map Prod.fst
  refine ⟨b, pe, evs, hb1, hb2, fun e he => (hval e he).2, ?_, ?_, ?_, ?_, hb6, ?_, ?_⟩
  · apply class_count B c.base R b.ents
    · intro e he
      have := hval e he
      exact ⟨this.1, Int.le_trans this.2 hR⟩
    · exact hb4
  · have a1 := List.length_filter_le (fun e : List Nat × Int => decide (ℓ < e.1.length))
      (nubE c).ents
    have a3 : (nubE c).ents.length = c.ents.length := List.length_map _
    simp only [pe, List.length_map]
    omega
  · have : evs.length ≤ evs.length * (p - 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  · intro T hT
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hT
    have := List.mem_filter.1 he
    have hl : ℓ < e.1.length := by simpa using this.2
    obtain ⟨hn, _, hv, _⟩ := h1 e this.1
    exact ⟨hn, hl, hv⟩
  · intro K
    by_cases h : ∃ T ∈ pe, ∀ i ∈ T, i ∈ K
    · exact Or.inr h
    · left
      have ht : eval (nubE c) (posG K) ≤ eval (trim ℓ (nubE c)) (posG K) := by
        apply trim_ge
        intro e he hcl
        apply Nat.le_of_not_lt
        intro hl
        apply h
        refine ⟨e.1, List.mem_map.2 ⟨e, List.mem_filter.2 ⟨he, by simpa using hl⟩, rfl⟩, ?_⟩
        exact (clq_posG (h1 e he).2.1).1 hcl
      rw [← nubE_eval c, ← drop_eval (trim ℓ (nubE c))] at *
      exact Int.le_trans ht (hb7 _)
  · intro G
    rcases hb8 G with h | h
    · left
      have := trim_le ℓ (nubE c) G
      rw [drop_eval, nubE_eval] at *
      exact Int.le_trans h this
    · exact Or.inr h

/-! ## The approximation theorem -/

theorem comb_len {X Y Z : Type} (L : List Y) (h : X → Y → Z) : ∀ l : List X,
    (l.flatMap fun e => L.map (h e)).length = l.length * L.length
  | [] => by simp
  | e :: l => by
    rw [List.flatMap_cons, List.length_append, List.length_map, comb_len L h l, List.length_cons,
      Nat.succ_mul, Nat.add_comm]

theorem ent_ok {ℓ m : Nat} {a : Approx} {top : Int} (hI : Inv ℓ m a) (hb : a.base ≤ top)
    (ht : ∀ e ∈ a.ents, e.2 ≤ top) : ∀ e ∈ ent a, ns e.1 ∧ (∀ x ∈ e.1, x < m) ∧ e.2 ≤ top := by
  intro e he
  rcases List.mem_cons.1 he with h | h
  · subst h; exact ⟨ns_nil, by simp, hb⟩
  · obtain ⟨_, _, hv, hns⟩ := hI e h
    exact ⟨hns, hv, ht e h⟩

/-- **Approximation.** Let `f` be a monotone real formula with `s` gates in which every subformula
has range at most `R` (`RCR`), read on graphs through `emb`, with input approximators `inA` that
are exact enough on the test graphs. Given the sunflower lemma `SF p ℓ B`, there are an
approximator `a` of `f` with at most `R B` entries and lists `pe` (sets of size `> ℓ`) and `ne`
(pluck events), each of length at most `s (R B + 1)^2`, such that on every clique graph `posG K`
either `f ≤ a` or `K` contains a set of `pe`, and on every colouring graph `negG c` either
`a ≤ f` or some event of `ne` has its core rainbow and no petal rainbow. -/
theorem approx {V : Type} (P : V → Bool) (p ℓ m B R : Nat) (hp : 2 ≤ p) (hSF : SF p ℓ B)
    (emb : (Nat → Nat → Bool) → V → Bool) (inA : V → Approx)
    (hin : ∀ u, P u = true → Inv ℓ m (inA u) ∧ (inA u).base = val (fun _ => false) u ∧
      (∀ e ∈ (inA u).ents, e.2 ≤ val (fun _ => true) u) ∧ (inA u).ents.length ≤ R * B ∧
      (∀ K, val (emb (posG K)) u ≤ eval (inA u) (posG K)) ∧
      (∀ c, eval (inA u) (negG c) ≤ val (emb (negG c)) u)) :
    ∀ {f : (V → Bool) → Int} {s : Nat}, RCR P (R : Int) f s →
    ∃ a : Approx, ∃ pe : List (List Nat), ∃ ne : List (List Nat × List (List Nat)),
      a.base = f (fun _ => false) ∧ Inv ℓ m a ∧ (∀ e ∈ a.ents, e.2 ≤ f (fun _ => true)) ∧
      a.ents.length ≤ R * B ∧
      pe.length ≤ s * (R * B + 1) ^ 2 ∧ ne.length ≤ s * (R * B + 1) ^ 2 ∧
      (∀ T ∈ pe, T.Nodup ∧ ℓ + 1 ≤ T.length ∧ ∀ x ∈ T, x < m) ∧ (∀ ev ∈ ne, Ev p ℓ m ev) ∧
      (∀ K, f (emb (posG K)) ≤ eval a (posG K) ∨ ∃ T ∈ pe, ∀ i ∈ T, i ∈ K) ∧
      (∀ c, eval a (negG c) ≤ f (emb (negG c)) ∨
        ∃ ev ∈ ne, clq (negG c) ev.1 ∧ ∀ S ∈ ev.2, ¬ clq (negG c) S) := by
  have hQ : R * B ≤ (R * B + 1) ^ 2 := by
    rw [Nat.pow_two]; exact Nat.le_trans (Nat.le_succ _) (Nat.le_mul_of_pos_left _ (by omega))
  intro f s hf
  induction hf with
  | const k _ =>
    refine ⟨constA k, [], [], rfl, fun e he => by simp [constA] at he,
      fun e he => by simp [constA] at he, by simp [constA], by simp, by simp, by simp, by simp,
      fun K => Or.inl (Int.le_of_eq (const_eval k _).symm),
      fun c => Or.inl (Int.le_of_eq (const_eval k _))⟩
  | inp u hu _ =>
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hin u hu
    exact ⟨inA u, [], [], h2, h1, h3, h4, by simp, by simp, by simp, by simp,
      fun K => Or.inl (h5 K), fun c => Or.inl (h6 c)⟩
  | @gate1 f s g hg hf hrng ih =>
    obtain ⟨a, pe, ne, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10⟩ := ih
    have hmono : f (fun _ => false) ≤ f (fun _ => true) :=
      hf.toRC.mono (fun _ h => by simp at h)
    have hc : ∀ e ∈ (amap g a).ents, ns e.1 ∧ (∀ x ∈ e.1, x < m) ∧
        e.2 ≤ g (f (fun _ => true)) := by
      intro e he
      obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
      obtain ⟨_, _, hv, hns⟩ := ha2 e0 he0
      exact ⟨hns, hv, hg _ _ (ha3 e0 he0)⟩
    have hR : g (f (fun _ => true)) ≤ (amap g a).base + R := by
      have := hrng (fun _ => true) (fun _ => false)
      show _ ≤ g a.base + R
      rw [ha1]; simp only at this; omega
    obtain ⟨b, pe', ne', hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10⟩ :=
      finish p ℓ m B R hp hSF _ (amap g a) hc hR
    have hl : (amap g a).ents.length = a.ents.length := List.length_map _
    refine ⟨b, pe ++ pe', ne ++ ne', by rw [hb1]; show g a.base = _; rw [ha1], hb2, hb3, hb4, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  | @gate2 f h s t g hg hf hh hrng ih1 ih2 =>
    obtain ⟨a, pe, ne, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10⟩ := ih1
    obtain ⟨a', pe', ne', ha1', ha2', ha3', ha4', ha5', ha6', ha7', ha8', ha9', ha10'⟩ := ih2
    have hmono : f (fun _ => false) ≤ f (fun _ => true) :=
      hf.toRC.mono (fun _ h => by simp at h)
    have hmono' : h (fun _ => false) ≤ h (fun _ => true) :=
      hh.toRC.mono (fun _ h => by simp at h)
    have ea := ent_ok ha2 (ha1 ▸ hmono) ha3
    have ea' := ent_ok ha2' (ha1' ▸ hmono') ha3'
    have hc : ∀ e ∈ (comb g a a').ents, ns e.1 ∧ (∀ x ∈ e.1, x < m) ∧
        e.2 ≤ g (f (fun _ => true)) (h (fun _ => true)) := by
      intro x hx
      obtain ⟨e, he, e', he', rfl⟩ := mem_comb hx
      obtain ⟨n1, v1, t1⟩ := ea e he
      obtain ⟨n2, v2, t2⟩ := ea' e' he'
      refine ⟨ns_append n1 n2, fun x hx => ?_, hg _ _ _ _ t1 t2⟩
      rcases List.mem_append.1 hx with hx | hx
      · exact v1 x hx
      · exact v2 x hx
    have hR : g (f (fun _ => true)) (h (fun _ => true)) ≤ (comb g a a').base + R := by
      have := hrng (fun _ => true) (fun _ => false)
      show _ ≤ g a.base a'.base + R
      rw [ha1, ha1']; simp only at this; omega
    obtain ⟨b, qe, qn, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10⟩ :=
      finish p ℓ m B R hp hSF _ (comb g a a') hc hR
    have hl : (comb g a a').ents.length ≤ (R * B + 1) ^ 2 := by
      have : (comb g a a').ents.length = (a.ents.length + 1) * (a'.ents.length + 1) := by
        simp only [comb]; rw [comb_len]; rfl
      rw [this, Nat.pow_two]
      exact Nat.mul_le_mul (by omega) (by omega)
    have hns : ∀ e ∈ ent a, ns e.1 := fun e he => (ea e he).1
    have hns' : ∀ e ∈ ent a', ns e.1 := fun e he => (ea' e he).1
    refine ⟨b, pe ++ pe' ++ qe, ne ++ ne' ++ qn, by rw [hb1]; show g a.base a'.base = _; rw [ha1, ha1'], hb2, hb3, hb4,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
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

end Programme.«20261024-1633-proof-complexity».ApproxRCR
