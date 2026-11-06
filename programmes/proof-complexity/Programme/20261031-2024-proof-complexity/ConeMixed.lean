import Programme.«20261031-2024-proof-complexity».ConeIdentify

namespace Programme.«20261031-2024-proof-complexity».NativeIter

/-- An unguarded equation can be multiplied by a guard at cost one,
including repeated or identified multiplier variables. -/
theorem equation_guard_plain {G d} (c m : List Lit) (r : Rat) (l : Lit)
    (hc : c ∈ G) (hd : m.length + c.length ≤ d) :
    Cone G (d+1) (fun a => conjunction [l] a *
      (r * conjunction (m ++ falsity c) a)) := by
  have h := equation_cell (F := G) (d := d+1) c (l :: m) r hc
    (by simp only [List.length_cons]; omega)
  have he : (fun a => r * conjunction ((l :: m) ++ falsity c) a) =
      (fun a => conjunction [l] a * (r * conjunction (m ++ falsity c) a)) := by
    funext a
    change r * conjunction ([l] ++ (m ++ falsity c)) a = _
    rw [conjunction_mul, ← Rat.mul_assoc, Rat.mul_comm r (conjunction [l] a),
      Rat.mul_assoc]
  rw [he] at h
  exact h

/-- Each source clause may be present unguarded, or with the negated guard.
Both cases accept literal deduplication and arbitrary variable identification. -/
theorem cone_identify_mixed_guard {F G d} (ρ : Var → Var) (l : Lit)
    (clauses : ∀ c ∈ F,
      (renameClause ρ c).eraseDups ∈ G ∨
      (renameClause ρ c ++ [neg l]).eraseDups ∈ G)
    {f} (hf : Cone F d f) :
    Cone G (d+1) (fun a => conjunction [l] a * f (fun v => a (ρ v))) := by
  let H := F.map (renameClause ρ)
  have hh : Cone H d (fun a => f (fun v => a (ρ v))) :=
    cone_identify ρ (by intro c hc; exact List.mem_map.mpr ⟨c,hc,rfl⟩) hf
  apply cone_guard l (fun c hc m hd r => ?_) hh
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hc
  rcases clauses e he with hp | hg
  · let J := [renameClause ρ e]
    have hj : Cone J (d+1) (fun a => conjunction [l] a *
        (r * conjunction (m ++ falsity (renameClause ρ e)) a)) :=
      equation_guard_plain _ m r l (by simp [J]) hd.2
    have hk := cone_eraseDups hj
    apply cone_clause_replace (F := ((J.map List.eraseDups).eraseDups)) _ hk
    intro c hc
    have hc' : c = (renameClause ρ e).eraseDups := by
      simpa [J] using hc
    subst c
    exact ⟨_, hp, Nat.le_refl _, fun _ => Iff.rfl⟩
  · let J := [renameClause ρ e]
    have hj : Cone J d (fun a => r * conjunction (m ++ falsity (renameClause ρ e)) a) :=
      Cone.equation _ m r (by simp [J]) hd
    apply cone_guard_of_dedup_clauses l _ hj
    intro c hc
    have hc' : c = renameClause ρ e := by simpa [J] using hc
    subst c
    exact hg

#print axioms equation_guard_plain
#print axioms cone_identify_mixed_guard
end Programme.«20261031-2024-proof-complexity».NativeIter
