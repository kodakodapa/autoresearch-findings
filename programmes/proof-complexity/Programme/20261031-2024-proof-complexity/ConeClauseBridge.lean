import Programme.«20261031-2024-proof-complexity».ConeGuard

namespace Programme.«20261031-2024-proof-complexity».NativeIter

/-- Clause replacement may reorder or remove duplicate literals, but must not
increase the formal clause length. -/
theorem conjunction_of_same_members {c e : List Lit}
    (h : ∀ l, l ∈ c ↔ l ∈ e) (a : Assignment) :
    conjunction c a = conjunction e a := by
  have he : c.all (holds a) = e.all (holds a) := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true]
    constructor
    · intro hc l hl; exact hc l ((h l).mpr hl)
    · intro hc l hl; exact hc l ((h l).mp hl)
  simp only [conjunction, he]

theorem cone_clause_replace {F G : List Clause} {d : Nat}
    (clauses : ∀ c ∈ F, ∃ e ∈ G, e.length ≤ c.length ∧
      ∀ l, l ∈ e ↔ l ∈ c) {f} (hf : Cone F d f) : Cone G d f := by
  induction hf with
  | positive m hm hd => exact Cone.positive m hm hd
  | equation c m r hc hd =>
    obtain ⟨e, he, hlen, hmem⟩ := clauses c hc
    have ha : Admitted d e m := ⟨hd.1, by have := hd.2; omega⟩
    have hh := Cone.equation e m r he ha
    have hfals : ∀ l, l ∈ falsity e ↔ l ∈ falsity c := by
      intro l
      simp only [falsity, List.mem_map]
      constructor
      · rintro ⟨v,hv,rfl⟩; exact ⟨v,(hmem v).mp hv,rfl⟩
      · rintro ⟨v,hv,rfl⟩; exact ⟨v,(hmem v).mpr hv,rfl⟩
    have eqf : (fun a => r * conjunction (m ++ falsity e) a) =
        (fun a => r * conjunction (m ++ falsity c) a) := by
      funext a
      have heq := conjunction_of_same_members (c := m ++ falsity e)
        (e := m ++ falsity c) (fun l => by
          simp only [List.mem_append]; rw [hfals l]) a
      rw [heq]
    rw [eqf] at hh
    exact hh
  | zero => exact Cone.zero
  | add _ _ ih jh => exact Cone.add ih jh
  | scale r hr _ ih => exact Cone.scale r hr ih

private theorem dedup_loop_length (xs acc : List Lit) :
    (List.eraseDupsBy.loop (fun x y : Lit => x == y) xs acc).length ≤
      xs.length + acc.length := by
  induction xs generalizing acc with
  | nil => simp [List.eraseDupsBy.loop]
  | cons x xs ih =>
    simp only [List.eraseDupsBy.loop]
    split
    · have h := ih acc; simp only [List.length_cons]; omega
    · have h := ih (x :: acc); simp only [List.length_cons] at *; omega

theorem cone_eraseDups {F : List Clause} {d f} (hf : Cone F d f) :
    Cone ((F.map List.eraseDups).eraseDups) d f := by
  apply cone_clause_replace (F := F) (d := d) _ hf
  intro c hc
  refine ⟨c.eraseDups, ?_, ?_, ?_⟩
  · simp only [List.mem_eraseDups, List.mem_map]
    exact ⟨c,hc,rfl⟩
  · simpa [List.eraseDups, List.eraseDupsBy] using dedup_loop_length c []
  · intro l; simp

/-- The guarded-clause transport accepts the generator's deduplicated clauses. -/
theorem cone_guard_of_dedup_clauses {F G d} (l : Lit)
    (clauses : ∀ c ∈ F, (c ++ [neg l]).eraseDups ∈ G)
    {f} (hf : Cone F d f) :
    Cone G (d+1) (fun a => conjunction [l] a * f a) := by
  let H := F.map (fun c => c ++ [neg l])
  have hh : Cone H (d+1) (fun a => conjunction [l] a * f a) :=
    cone_guard_of_clauses l (by
      intro c hc
      exact List.mem_map.mpr ⟨c,hc,rfl⟩) hf
  apply cone_clause_replace (F := H) _ hh
  intro c hc
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hc
  refine ⟨(e ++ [neg l]).eraseDups, clauses e he, ?_, ?_⟩
  · simpa [List.eraseDups, List.eraseDupsBy] using
      dedup_loop_length (e ++ [neg l]) []
  · intro v; simp

#print axioms cone_clause_replace
#print axioms cone_eraseDups
#print axioms cone_guard_of_dedup_clauses
end Programme.«20261031-2024-proof-complexity».NativeIter
