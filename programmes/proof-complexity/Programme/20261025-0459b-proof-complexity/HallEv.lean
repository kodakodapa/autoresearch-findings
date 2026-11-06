import Programme.«20261025-0459b-proof-complexity».HallEnd

/-!
# Rise events of the matching pluck, on Hall-violator graphs (M3 in pr's event shape)

`Ev p ℓ n (C, I, Ps)` restates pr's `Work.MPluck.MEv` (P108) with `isM P = true` unfolded:
`p` petals `P ⊇ I`, bounded duplicate-free matchings on `[n]`, `I` inside the core `C`
(coordinates `2i`, `2j+1`), every edge of `P \ I` with an endpoint outside `C`, two petals
sharing coordinates only inside `C`.

`hall_event`: at most a `(1 - 2^{-ℓ})^p` fraction of the assignments on the `2n` coordinates
make `I` present and every petal absent in `negG α`. Proof: residual petals
`Q = P \ I`, residues `R = vs P \ C`, base = the other coordinates `< 2n`; then
`Work.HallEnd.hall_rise_on`.
-/

namespace Programme.«20261025-0459b-proof-complexity».HallEv

open Programme.«20261025-0459b-proof-complexity».Indep Programme.«20261025-0459b-proof-complexity».AsgPerm Programme.«20261025-0459b-proof-complexity».HallRise Programme.«20261025-0459b-proof-complexity».HallEnd

def vs (P : List (Nat × Nat)) : List Nat := P.flatMap fun e => [2 * e.1, 2 * e.2 + 1]

theorem mem_vs {P : List (Nat × Nat)} {x : Nat} :
    x ∈ vs P ↔ ∃ e ∈ P, x = 2 * e.1 ∨ x = 2 * e.2 + 1 := by
  simp [vs, List.mem_flatMap, eq_comm]

def Ev (p ℓ n : Nat) (ev : List Nat × List (Nat × Nat) × List (List (Nat × Nat))) : Prop :=
  ev.2.2.length = p ∧ ev.1.length ≤ 2 * ℓ ∧
  (∀ e ∈ ev.2.1, 2 * e.1 ∈ ev.1 ∧ 2 * e.2 + 1 ∈ ev.1) ∧
  (∀ P ∈ ev.2.2, P.Nodup ∧ ((P.map (·.1)).Nodup ∧ (P.map (·.2)).Nodup) ∧ P.length ≤ ℓ ∧
    (∀ x ∈ P, x.1 < n ∧ x.2 < n) ∧
    (∀ e ∈ ev.2.1, e ∈ P) ∧ (∃ e ∈ P, e ∉ ev.2.1) ∧
    (∀ e ∈ P, e ∉ ev.2.1 → 2 * e.1 ∉ ev.1 ∨ 2 * e.2 + 1 ∉ ev.1)) ∧
  ev.2.2.Pairwise (fun P Q => ∀ x, x ∈ vs P → x ∈ vs Q → x ∈ ev.1)

/-- Residual edges. -/
def resQ (I P : List (Nat × Nat)) : List (Nat × Nat) := P.filter fun e => decide (e ∉ I)

/-- Residue coordinates. -/
def resR (C : List Nat) (P : List (Nat × Nat)) : List Nat := (vs P).filter fun y => decide (y ∉ C)

def pet (C : List Nat) (I : List (Nat × Nat)) (P : List (Nat × Nat)) : Petal :=
  ⟨resQ I P, resR C P⟩

def bse (n : Nat) (C : List Nat) (Ps : List (List (Nat × Nat))) : List Nat :=
  (List.range (2 * n)).filter fun y => decide (y ∉ Ps.flatMap (resR C))

theorem inj_on {f : Nat × Nat → Nat} : ∀ {P : List (Nat × Nat)}, (P.map f).Nodup →
    ∀ e ∈ P, ∀ e' ∈ P, f e = f e' → e = e'
  | [], _, e, he, _, _, _ => by simp at he
  | a :: P, h, e, he, e', he', hf => by
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.1 he with h1 | t1 <;> rcases List.mem_cons.1 he' with h2 | t2
    · rw [h1, h2]
    · subst h1; exact absurd (by rw [hf]; exact List.mem_map_of_mem t2) h.1
    · subst h2; exact absurd (by rw [← hf]; exact List.mem_map_of_mem t1) h.1
    · exact inj_on h.2 e t1 e' t2 hf

theorem vs_nodup : ∀ {P : List (Nat × Nat)}, P.Nodup → (P.map (·.1)).Nodup →
    (P.map (·.2)).Nodup → (vs P).Nodup
  | [], _, _, _ => by simp [vs]
  | a :: P, h0, h1, h2 => by
    rw [List.map_cons, List.nodup_cons] at h1 h2
    rw [List.nodup_cons] at h0
    have ih := vs_nodup h0.2 h1.2 h2.2
    have hv : vs (a :: P) = [2 * a.1, 2 * a.2 + 1] ++ vs P := by simp [vs]
    rw [hv, List.nodup_append]
    refine ⟨by simp; omega, ih, ?_⟩
    intro x hx y hy hxy
    subst hxy
    obtain ⟨e, he, hx'⟩ := mem_vs.1 hy
    simp at hx
    rcases hx with rfl | rfl <;> rcases hx' with h | h
    · exact h1.1 (List.mem_map.2 ⟨e, he, by omega⟩)
    · omega
    · omega
    · exact h2.1 (List.mem_map.2 ⟨e, he, by omega⟩)

theorem mem_resR {C : List Nat} {P : List (Nat × Nat)} {y : Nat} :
    y ∈ resR C P ↔ y ∈ vs P ∧ y ∉ C := by
  simp [resR]

theorem flat_pet (C : List Nat) (I : List (Nat × Nat)) (Ps : List (List (Nat × Nat))) :
    (Ps.map (pet C I)).flatMap Petal.R = Ps.flatMap (resR C) := by
  simp [pet, List.flatMap_map]

theorem nodup_flat {n p ℓ : Nat} {C : List Nat} {I : List (Nat × Nat)}
    {Ps : List (List (Nat × Nat))} (hev : Ev p ℓ n (C, I, Ps)) :
    (Ps.flatMap (resR C)).Nodup := by
  obtain ⟨_, _, _, hP, hpw⟩ := hev
  unfold List.Nodup
  rw [List.pairwise_flatMap]
  refine ⟨fun P hm => ?_, ?_⟩
  · obtain ⟨h0, ⟨h1, h2⟩, _⟩ := hP P hm
    exact (vs_nodup h0 h1 h2).filter _
  · refine hpw.imp ?_
    intro P Q h x hx y hy hxy
    subst hxy
    rw [mem_resR] at hx hy
    exact hx.2 (h x hx.1 hy.1)

theorem hall_event (p ℓ n : Nat) (C : List Nat) (I : List (Nat × Nat))
    (Ps : List (List (Nat × Nat))) (hev : Ev p ℓ n (C, I, Ps)) (U : List Nat) (hU : U.Nodup)
    (hUn : ∀ y, y ∈ U ↔ y < 2 * n) :
    cnt (asg U) (fun α => pres (negG α) I ∧ ∀ P ∈ Ps, ¬pres (negG α) P) * 2 ^ (ℓ * p) ≤
      2 ^ U.length * (2 ^ ℓ - 1) ^ p := by
  have hfl := nodup_flat hev
  obtain ⟨hlen, _, hI, hP, _⟩ := hev
  have hR2n : ∀ y ∈ Ps.flatMap (resR C), y < 2 * n := by
    intro y hy
    obtain ⟨P, hm, hy⟩ := List.mem_flatMap.1 hy
    obtain ⟨e, he, hx⟩ := mem_vs.1 (mem_resR.1 hy).1
    have := ((hP P hm).2.2.2.1 e he)
    omega
  have hnd : (bse n C Ps ++ (Ps.map (pet C I)).flatMap Petal.R).Nodup := by
    rw [flat_pet, List.nodup_append]
    refine ⟨List.nodup_range.filter _, hfl, ?_⟩
    intro x hx y hy hxy
    subst hxy
    simp only [bse, List.mem_filter, List.mem_range, decide_eq_true_eq] at hx
    exact hx.2 hy
  have hmem : ∀ y, y ∈ U ↔ y ∈ bse n C Ps ++ (Ps.map (pet C I)).flatMap Petal.R := by
    intro y
    rw [hUn, flat_pet, List.mem_append]
    constructor
    · intro hy
      by_cases h : y ∈ Ps.flatMap (resR C)
      · exact Or.inr h
      · left; simp only [bse, List.mem_filter, List.mem_range, decide_eq_true_eq]; exact ⟨hy, h⟩
    · rintro (h | h)
      · simp only [bse, List.mem_filter, List.mem_range, decide_eq_true_eq] at h; exact h.1
      · exact hR2n y h
  have hok : ∀ Q ∈ Ps.map (pet C I), Ok ℓ (bse n C Ps) Q := by
    intro Q hQ
    obtain ⟨P, hm, rfl⟩ := List.mem_map.1 hQ
    obtain ⟨h0, ⟨h1, h2⟩, hl, hn, _, _, hout⟩ := hP P hm
    have hsub : ∀ e ∈ resQ I P, e ∈ P ∧ e ∉ I := by intro e he; simpa [resQ] using he
    have hcoord : ∀ e ∈ P, ∀ y, (y = 2 * e.1 ∨ y = 2 * e.2 + 1) →
        y ∈ bse n C Ps ∨ y ∈ resR C P := by
      intro e he y hy
      by_cases hc : y ∈ C
      · left
        simp only [bse, List.mem_filter, List.mem_range, decide_eq_true_eq]
        refine ⟨by have := hn e he; omega, fun hf => ?_⟩
        obtain ⟨P', _, hr⟩ := List.mem_flatMap.1 hf
        exact (mem_resR.1 hr).2 hc
      · right; exact mem_resR.2 ⟨mem_vs.2 ⟨e, he, hy⟩, hc⟩
    refine ⟨h0.filter _, (vs_nodup h0 h1 h2).filter _, ?_, ?_, ?_, ?_, ?_⟩
    · exact Nat.le_trans (List.length_filter_le _ _) hl
    · intro e he e' he' h; exact inj_on h1 e (hsub e he).1 e' (hsub e' he').1 h
    · intro e he e' he' h; exact inj_on h2 e (hsub e he).1 e' (hsub e' he').1 h
    · intro e he
      exact ⟨hcoord e (hsub e he).1 _ (Or.inl rfl), hcoord e (hsub e he).1 _ (Or.inr rfl)⟩
    · intro e he
      obtain ⟨heP, heI⟩ := hsub e he
      rcases hout e heP heI with h | h
      · exact Or.inl (mem_resR.2 ⟨mem_vs.2 ⟨e, heP, Or.inl rfl⟩, h⟩)
      · exact Or.inr (mem_resR.2 ⟨mem_vs.2 ⟨e, heP, Or.inr rfl⟩, h⟩)
  have h := hall_rise_on ℓ U (bse n C Ps) (Ps.map (pet C I)) hU hnd hmem hok
  rw [List.length_map, hlen] at h
  refine Nat.le_trans (Nat.mul_le_mul_right _ (cnt_mono fun α _ hα => ?_)) h
  intro Q hQ hpQ
  obtain ⟨P, hm, rfl⟩ := List.mem_map.1 hQ
  apply hα.2 P hm
  intro e he
  by_cases hi : e ∈ I
  · exact hα.1 e hi
  · exact hpQ e (by simp [pet, resQ, he, hi])

end Programme.«20261025-0459b-proof-complexity».HallEv
