import Programme.«20261025-0805-proof-complexity».MPluck
import Programme.«20261025-0459b-proof-complexity».CPDagPr

/-!
# Approximating monotone real circuits by matching approximators (M2 → M6 of P88)

Gate by gate over a monotone real circuit (`Programme.«20261025-0459b-proof-complexity».CPDagPr.MC`): combine the approximators of the
inputs (`Work.MApprox.comb`/`amap`, exact on every graph), drop non-matchings and entries with more
than `ℓ` edges (`finish0`), then close (`Work.MPluck.mclose`). Errors:
* positive (on the perfect matchings `pmG σ`, `σ` duplicate-free): `σ` contains a partial matching
  with more than `ℓ` edges from a list `pe`;
* negative (on every graph `H`): one of the pluck events `ne` has its inner edges present in `H`
  and none of its petals.
Each gate adds at most `ℓ (B+1)^2` errors of each kind, `B = thr p ℓ`.
-/

set_option linter.unusedVariables false

namespace Programme.«20261025-0805-proof-complexity».MCircuit

open Programme.«20261025-0805-proof-complexity».MApprox
open Programme.«20261025-0805-proof-complexity».MPluck
open Programme.«20261025-0805-proof-complexity».PermCount (fitsP)
open Programme.«20261025-0459b-proof-complexity».CPDagPr (MC)
open Programme.«20261024-1633-proof-complexity».CP (val)

abbrev EvT := List Nat × List (Nat × Nat) × List (List (Nat × Nat))

/-- `a` approximates the gate `f` up to the errors `pe` (positive) and `ne` (negative). -/
def MGood {V : Type} (n ℓ B : Nat) (emb : (Nat → Nat → Bool) → V → Bool)
    (pe : List (List (Nat × Nat))) (ne : List EvT) (f : (V → Bool) → Int) (a : MA) : Prop :=
  MInv n ℓ a ∧ a.ents.length ≤ B ∧
  (∀ σ : List Nat, σ.Nodup → f (emb (pmG σ)) ≤ eval a (pmG σ) ∨ ∃ P ∈ pe, fitsP P σ = true) ∧
  (∀ H, eval a H ≤ f (emb H) ∨ ∃ ev ∈ ne, pres H ev.2.1 ∧ ∀ P ∈ ev.2.2, ¬ pres H P)

theorem MGood.mono {V : Type} {n ℓ B : Nat} {emb : (Nat → Nat → Bool) → V → Bool}
    {pe pe' : List (List (Nat × Nat))} {ne ne' : List EvT}
    {f : (V → Bool) → Int} {a : MA} (h : MGood n ℓ B emb pe ne f a)
    (hp : ∀ T ∈ pe, T ∈ pe') (hn : ∀ ev ∈ ne, ev ∈ ne') : MGood n ℓ B emb pe' ne' f a := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, fun σ hσ => ?_, fun H => ?_⟩
  · rcases h3 σ hσ with h | ⟨T, hT, hK⟩
    · exact Or.inl h
    · exact Or.inr ⟨T, hp T hT, hK⟩
  · rcases h4 H with h | ⟨ev, hev, hE⟩
    · exact Or.inl h
    · exact Or.inr ⟨ev, hn ev hev, hE⟩

/-- Entries of `ent a` (including the base) are duplicate-free and bounded. -/
theorem ent_ok {n ℓ : Nat} {a : MA} (h : MInv n ℓ a) :
    ∀ e ∈ ent a, e.1.Nodup ∧ ∀ x ∈ e.1, x.1 < n ∧ x.2 < n := by
  intro e he
  rcases List.mem_cons.1 he with rfl | he
  · simp
  · exact ⟨(h e he).1, (h e he).2.2.2⟩

/-- Finishing a gate: drop, trim and close. -/
theorem finishM (p ℓ n : Nat) (hp : 1 ≤ p) (c : MA)
    (hc : ∀ e ∈ c.ents, e.1.Nodup ∧ ∀ x ∈ e.1, x.1 < n ∧ x.2 < n) :
    ∃ b : MA, ∃ pe' : List (List (Nat × Nat)), ∃ ne' : List EvT,
      MInv n ℓ b ∧ b.ents.length ≤ thr p ℓ ∧ pe'.length ≤ c.ents.length ∧
      ne'.length ≤ ℓ * c.ents.length ∧
      (∀ P ∈ pe', isM P = true ∧ ℓ < P.length ∧ ∀ x ∈ P, x.1 < n ∧ x.2 < n) ∧
      (∀ ev ∈ ne', MEv p ℓ n ev) ∧
      (∀ σ : List Nat, σ.Nodup → eval c (pmG σ) ≤ eval b (pmG σ) ∨ ∃ P ∈ pe', fitsP P σ = true) ∧
      (∀ H, eval b H ≤ eval c H ∨ ∃ ev ∈ ne', pres H ev.2.1 ∧ ∀ P ∈ ev.2.2, ¬ pres H P) := by
  let d := trim ℓ (dropM c)
  have hdsub : d.ents.Sublist c.ents := List.filter_sublist.trans List.filter_sublist
  have hdI : MInv n ℓ d := by
    intro e he
    have h1 := List.mem_filter.1 he
    have h2 := List.mem_filter.1 h1.1
    have h3 := hc e h2.1
    exact ⟨h3.1, h2.2, by simpa using h1.2, h3.2⟩
  obtain ⟨b, evs, b1, b2, b3, b4, b5, b6, b7⟩ := mclose p ℓ n hp (wt d.ents + 1) d (by omega) hdI
  obtain ⟨f1, f2⟩ := finish0 ℓ c fun e he => (hc e he).1
  have hwd : wt d.ents ≤ ℓ * d.ents.length := wt_le n ℓ d.ents fun e he => (hdI e he).2.2.1
  have hdl : d.ents.length ≤ c.ents.length := hdsub.length_le
  refine ⟨b, longM ℓ c, evs, b2, b3, longM_length ℓ c, ?_, ?_, b5, ?_, ?_⟩
  · exact Nat.le_trans b4 (Nat.le_trans hwd (Nat.mul_le_mul_left _ hdl))
  · intro P hP
    obtain ⟨h1, h2⟩ := longM_mem hP
    refine ⟨h1, h2, ?_⟩
    simp only [longM, List.mem_map, List.mem_filter] at hP
    obtain ⟨e, ⟨he, _⟩, rfl⟩ := hP
    exact (hc e he).2
  · intro σ hσ
    rcases f2 σ hσ with h | h
    · exact Or.inl (Int.le_trans h (b6 _))
    · exact Or.inr h
  · intro H
    rcases b7 H with h | h
    · exact Or.inl (Int.le_trans h (f1 H))
    · exact Or.inr h

/-- **Approximation of monotone real circuits.** For a monotone real circuit `fs` there are
error lists `pe`, `ne`, each of length at most `|fs| ℓ (B+1)^2` (`B = thr p ℓ`), and for every
gate `f ∈ fs` an approximator with at most `B` entries that is `MGood` up to them. -/
theorem mapproxC {V : Type} (Q : V → Bool) (p ℓ n : Nat) (hp : 1 ≤ p) (hℓ : 1 ≤ ℓ)
    (emb : (Nat → Nat → Bool) → V → Bool) (inA : V → MA)
    (hin : ∀ u, Q u = true → MInv n ℓ (inA u) ∧ (inA u).ents.length ≤ thr p ℓ ∧
      (∀ σ : List Nat, σ.Nodup → val (emb (pmG σ)) u ≤ eval (inA u) (pmG σ)) ∧
      (∀ H, eval (inA u) H ≤ val (emb H) u)) :
    ∀ {fs : List ((V → Bool) → Int)}, MC Q fs →
    ∃ pe : List (List (Nat × Nat)), ∃ ne : List EvT,
      pe.length ≤ fs.length * (ℓ * (thr p ℓ + 1) ^ 2) ∧
      ne.length ≤ fs.length * (ℓ * (thr p ℓ + 1) ^ 2) ∧
      (∀ P ∈ pe, isM P = true ∧ ℓ < P.length ∧ ∀ x ∈ P, x.1 < n ∧ x.2 < n) ∧
      (∀ ev ∈ ne, MEv p ℓ n ev) ∧
      ∀ f ∈ fs, ∃ a, MGood n ℓ (thr p ℓ) emb pe ne f a := by
  intro fs hfs
  generalize hBd : thr p ℓ = B at hin ⊢
  have hQ2 : (B + 1) ^ 2 ≤ ℓ * (B + 1) ^ 2 := Nat.le_mul_of_pos_left _ hℓ
  have hQ : B ≤ (B + 1) ^ 2 := by
    rw [Nat.pow_two]; exact Nat.le_trans (Nat.le_succ _) (Nat.le_mul_of_pos_left _ (by omega))
  have free : ∀ {fs : List ((V → Bool) → Int)} {g : (V → Bool) → Int} {pe ne} (a : MA),
      pe.length ≤ fs.length * (ℓ * (B + 1) ^ 2) → ne.length ≤ fs.length * (ℓ * (B + 1) ^ 2) →
      (∀ f ∈ fs, ∃ a, MGood n ℓ B emb pe ne f a) → MGood n ℓ B emb pe ne g a →
      pe.length ≤ (fs ++ [g]).length * (ℓ * (B + 1) ^ 2) ∧
      ne.length ≤ (fs ++ [g]).length * (ℓ * (B + 1) ^ 2) ∧
      ∀ f ∈ fs ++ [g], ∃ a, MGood n ℓ B emb pe ne f a := by
    intro fs g pe ne a h1 h2 h3 h4
    refine ⟨?_, ?_, fun f hf => ?_⟩
    · simp only [List.length_append, List.length_singleton, Nat.add_mul, Nat.one_mul]; omega
    · simp only [List.length_append, List.length_singleton, Nat.add_mul, Nat.one_mul]; omega
    · rcases List.mem_append.1 hf with e | e
      · exact h3 f e
      · simp at e; subst e; exact ⟨a, h4⟩
  induction hfs with
  | nil => exact ⟨[], [], by simp, by simp, by simp, by simp, by simp⟩
  | const k _ ih =>
    obtain ⟨pe, ne, h1, h2, h3, h4, h5⟩ := ih
    obtain ⟨g1, g2, g3⟩ := free (g := fun _ => k) (constA k) h1 h2 h5
      ⟨fun e he => by simp [constA] at he, by simp [constA],
        fun σ _ => Or.inl (Int.le_of_eq (const_eval k _).symm),
        fun H => Or.inl (Int.le_of_eq (const_eval k _))⟩
    exact ⟨pe, ne, g1, g2, h3, h4, g3⟩
  | inp u hu _ ih =>
    obtain ⟨pe, ne, h1, h2, h3, h4, h5⟩ := ih
    obtain ⟨i1, i4, i5, i6⟩ := hin u hu
    obtain ⟨g1, g2, g3⟩ := free (g := fun β => val β u) (inA u) h1 h2 h5
      ⟨i1, i4, fun σ hσ => Or.inl (i5 σ hσ), fun H => Or.inl (i6 H)⟩
    exact ⟨pe, ne, g1, g2, h3, h4, g3⟩
  | @gate1 fs f g hg _ hf ih =>
    obtain ⟨pe, ne, h1, h2, h3, h4, h5⟩ := ih
    obtain ⟨a, ha2, ha4, ha9, ha10⟩ := h5 f hf
    have hc : ∀ e ∈ (amap g a).ents, e.1.Nodup ∧ ∀ x ∈ e.1, x.1 < n ∧ x.2 < n := by
      intro e he
      obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
      exact ⟨(ha2 e0 he0).1, (ha2 e0 he0).2.2.2⟩
    obtain ⟨b, pe', ne', hb2, hb4, hb5, hb6, hb7, hb8, hb9, hb10⟩ := finishM p ℓ n hp (amap g a) hc
    rw [hBd] at hb4
    have hl : (amap g a).ents.length = a.ents.length := List.length_map _
    have hlb : ℓ * (amap g a).ents.length ≤ ℓ * (B + 1) ^ 2 :=
      Nat.mul_le_mul_left _ (by rw [hl]; omega)
    have sp : ∀ T ∈ pe, T ∈ pe ++ pe' := fun T hT => List.mem_append_left _ hT
    have sn : ∀ ev ∈ ne, ev ∈ ne ++ ne' := fun ev hev => List.mem_append_left _ hev
    refine ⟨pe ++ pe', ne ++ ne', ?_, ?_, ?_, ?_, fun f' hf' => ?_⟩
    · have : pe'.length ≤ ℓ * (B + 1) ^ 2 := by
        have : (amap g a).ents.length ≤ ℓ * (amap g a).ents.length := Nat.le_mul_of_pos_left _ hℓ
        omega
      simp only [List.length_append, List.length_singleton, Nat.add_mul, Nat.one_mul]; omega
    · simp only [List.length_append, List.length_singleton, Nat.add_mul, Nat.one_mul]; omega
    · intro T hT
      rcases List.mem_append.1 hT with h | h
      · exact h3 T h
      · exact hb7 T h
    · intro ev hev
      rcases List.mem_append.1 hev with h | h
      · exact h4 ev h
      · exact hb8 ev h
    rcases List.mem_append.1 hf' with e | e
    · obtain ⟨a', ga⟩ := h5 f' e; exact ⟨a', ga.mono sp sn⟩
    simp at e; subst e
    refine ⟨b, hb2, hb4, fun σ hσ => ?_, fun H => ?_⟩
    · rcases ha9 σ hσ with h | ⟨T, hT, hK⟩
      · rcases hb9 σ hσ with h' | ⟨T, hT, hK⟩
        · left
          rw [amap_eval g hg] at h'
          exact Int.le_trans (hg _ _ h) h'
        · exact Or.inr ⟨T, List.mem_append.2 (Or.inr hT), hK⟩
      · exact Or.inr ⟨T, List.mem_append.2 (Or.inl hT), hK⟩
    · rcases ha10 H with h | ⟨ev, hev, hE⟩
      · rcases hb10 H with h' | ⟨ev, hev, hE⟩
        · left
          rw [amap_eval g hg] at h'
          exact Int.le_trans h' (hg _ _ h)
        · exact Or.inr ⟨ev, List.mem_append.2 (Or.inr hev), hE⟩
      · exact Or.inr ⟨ev, List.mem_append.2 (Or.inl hev), hE⟩
  | @gate2 fs f h g hg _ hf hh ih =>
    obtain ⟨pe, ne, h1, h2, h3, h4, h5⟩ := ih
    obtain ⟨a, ha2, ha4, ha9, ha10⟩ := h5 f hf
    obtain ⟨a', ha2', ha4', ha9', ha10'⟩ := h5 h hh
    have hc : ∀ e ∈ (comb g a a').ents, e.1.Nodup ∧ ∀ x ∈ e.1, x.1 < n ∧ x.2 < n := by
      intro x hx
      obtain ⟨e, he, e', he', rfl⟩ := mem_comb (List.mem_cons_of_mem _ hx)
      obtain ⟨n1, v1⟩ := ent_ok ha2 e he
      obtain ⟨n2, v2⟩ := ent_ok ha2' e' he'
      refine ⟨nodup_uni n1 n2, fun x hx => ?_⟩
      rcases mem_uni.1 hx with hx | hx
      · exact v1 x hx
      · exact v2 x hx
    obtain ⟨b, qe, qn, hb2, hb4, hb5, hb6, hb7, hb8, hb9, hb10⟩ := finishM p ℓ n hp (comb g a a') hc
    rw [hBd] at hb4
    have hl : (comb g a a').ents.length ≤ (B + 1) ^ 2 := by
      have := comb_len g a a'
      rw [Nat.pow_two]
      have : (a.ents.length + 1) * (a'.ents.length + 1) ≤ (B + 1) * (B + 1) :=
        Nat.mul_le_mul (by omega) (by omega)
      omega
    have hlb : ℓ * (comb g a a').ents.length ≤ ℓ * (B + 1) ^ 2 := Nat.mul_le_mul_left _ hl
    have sp : ∀ T ∈ pe, T ∈ pe ++ qe := fun T hT => List.mem_append_left _ hT
    have sn : ∀ ev ∈ ne, ev ∈ ne ++ qn := fun ev hev => List.mem_append_left _ hev
    refine ⟨pe ++ qe, ne ++ qn, ?_, ?_, ?_, ?_, fun f' hf' => ?_⟩
    · simp only [List.length_append, List.length_singleton, Nat.add_mul, Nat.one_mul]; omega
    · simp only [List.length_append, List.length_singleton, Nat.add_mul, Nat.one_mul]; omega
    · intro T hT
      rcases List.mem_append.1 hT with h | h
      · exact h3 T h
      · exact hb7 T h
    · intro ev hev
      rcases List.mem_append.1 hev with h | h
      · exact h4 ev h
      · exact hb8 ev h
    rcases List.mem_append.1 hf' with e | e
    · obtain ⟨a'', ga⟩ := h5 f' e; exact ⟨a'', ga.mono sp sn⟩
    simp at e; subst e
    refine ⟨b, hb2, hb4, fun σ hσ => ?_, fun H => ?_⟩
    · rcases ha9 σ hσ with h1 | ⟨T, hT, hK⟩
      · rcases ha9' σ hσ with h2 | ⟨T, hT, hK⟩
        · rcases hb9 σ hσ with h3 | ⟨T, hT, hK⟩
          · left
            rw [comb_eval g hg] at h3
            exact Int.le_trans (hg _ _ _ _ h1 h2) h3
          · exact Or.inr ⟨T, List.mem_append.2 (Or.inr hT), hK⟩
        · exact Or.inr ⟨T, List.mem_append.2 (Or.inl hT), hK⟩
      · exact Or.inr ⟨T, List.mem_append.2 (Or.inl hT), hK⟩
    · rcases ha10 H with h1 | ⟨ev, hev, hE⟩
      · rcases ha10' H with h2 | ⟨ev, hev, hE⟩
        · rcases hb10 H with h3 | ⟨ev, hev, hE⟩
          · left
            rw [comb_eval g hg] at h3
            exact Int.le_trans h3 (hg _ _ _ _ h1 h2)
          · exact Or.inr ⟨ev, List.mem_append.2 (Or.inr hev), hE⟩
        · exact Or.inr ⟨ev, List.mem_append.2 (Or.inl hev), hE⟩
      · exact Or.inr ⟨ev, List.mem_append.2 (Or.inl hev), hE⟩

end Programme.«20261025-0805-proof-complexity».MCircuit

#print axioms Programme.«20261025-0805-proof-complexity».MCircuit.mapproxC
