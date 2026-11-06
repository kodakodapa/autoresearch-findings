import Programme.«20261031-2024-proof-complexity».ConeRename
import Programme.«20261031-2024-proof-complexity».ConeClauseBridge

namespace Programme.«20261031-2024-proof-complexity».NativeIter

/-- A cell either vanishes or has a repetition-free representative no longer
than the original literal list. -/
theorem cell_normalize (m : List Lit) :
    conjunction m = (fun _ => 0) ∨
    ∃ q, Multiplier q ∧ q.length ≤ m.length ∧ conjunction q = conjunction m := by
  induction m with
  | nil => exact Or.inr ⟨[], by simp [Multiplier], by simp, rfl⟩
  | cons l m ih =>
    have happ : conjunction (l :: m) =
        (fun a => conjunction [l] a * conjunction m a) :=
      funext (conjunction_mul [l] m)
    rcases ih with hz | ⟨q,hq,hlen,heq⟩
    · left; rw [happ, hz]; funext a; simp
    · by_cases hv : l.1 ∈ q.map Prod.fst
      · obtain ⟨k,hk,hkv⟩ := List.mem_map.mp hv
        by_cases hs : k.2 = l.2
        · have hkl : k = l := Prod.ext hkv hs
          subst k
          right
          refine ⟨q,hq,by simp; omega,?_⟩
          rw [happ, ← heq]
          funext a
          by_cases ha : q.all (holds a) = true
          · have hl := List.all_eq_true.mp ha l hk
            simp [conjunction, ha, hl]
          · have ha' : q.all (holds a) = false := Bool.eq_false_iff.mpr ha
            simp [conjunction, ha']
        · left
          rw [happ, ← heq]
          funext a
          by_cases ha : q.all (holds a) = true
          · have hk' := List.all_eq_true.mp ha k hk
            have hl : holds a l = false := by
              unfold holds at *
              cases h : a l.1 <;> cases hkb : k.2 <;> cases hlb : l.2 <;> simp_all
            simp [conjunction, hl]
          · have ha' : q.all (holds a) = false := Bool.eq_false_iff.mpr ha
            simp [conjunction, ha']
      · right
        refine ⟨l :: q, ?_, by simp; omega, ?_⟩
        · simpa [Multiplier, List.nodup_cons] using And.intro hv hq
        · rw [happ, ← heq]
          exact funext (conjunction_mul [l] q)

theorem positive_cell {F d} (m : List Lit) (hd : m.length ≤ d) :
    Cone F d (conjunction m) := by
  rcases cell_normalize m with hz | ⟨q,hq,hlen,heq⟩
  · rw [hz]; exact Cone.zero
  · rw [← heq]; exact Cone.positive q hq (by omega)

/-- Equation multipliers can identify variables as well: normalize the multiplier
before testing formal degree. -/
theorem equation_cell {F d} (c m : List Lit) (r : Rat)
    (hc : c ∈ F) (hd : m.length + c.length ≤ d) :
    Cone F d (fun a => r * conjunction (m ++ falsity c) a) := by
  rcases cell_normalize m with hz | ⟨q,hq,hlen,heq⟩
  · have he : (fun a => r * conjunction (m ++ falsity c) a) = (fun _ => 0) := by
      funext a
      rw [conjunction_mul, hz]
      simp
    rw [he]; exact Cone.zero
  · have hh := Cone.equation (d := d) c q r hc ⟨hq, by omega⟩
    have he : (fun a => r * conjunction (q ++ falsity c) a) =
        (fun a => r * conjunction (m ++ falsity c) a) := by
      funext a
      rw [conjunction_mul, conjunction_mul, heq]
    rw [he] at hh
    exact hh

/-- Arbitrary variable maps preserve the cone when renamed clauses are present.
No injectivity or bounded-support extension is required. -/
theorem cone_identify (ρ : Var → Var) {F G d}
    (clauses : ∀ c ∈ F, renameClause ρ c ∈ G) {f} (hf : Cone F d f) :
    Cone G d (fun a => f (fun v => a (ρ v))) := by
  induction hf with
  | positive m hm hd =>
    have h := positive_cell (F := G) (d := d) (renameClause ρ m)
      (by simpa [renameClause] using hd)
    have he := funext (conjunction_rename ρ m)
    rw [he] at h
    exact h
  | equation c m r hc hd =>
    have h := equation_cell (F := G) (d := d) (renameClause ρ c)
      (renameClause ρ m) r (clauses c hc) (by simpa [renameClause] using hd.2)
    have he : (fun a => r * conjunction (renameClause ρ m ++ falsity (renameClause ρ c)) a) =
        (fun a => r * conjunction (m ++ falsity c) (fun v => a (ρ v))) := by
      funext a
      rw [falsity_rename]
      have happ : renameClause ρ m ++ renameClause ρ (falsity c) =
          renameClause ρ (m ++ falsity c) := by simp [renameClause]
      rw [happ, conjunction_rename]
    rw [he] at h
    exact h
  | zero => exact Cone.zero
  | add _ _ ih jh => exact Cone.add ih jh
  | scale r hr _ ih => exact Cone.scale r hr ih

theorem refutes_identify (ρ : Var → Var) {F G d}
    (clauses : ∀ c ∈ F, renameClause ρ c ∈ G) (hf : Refutes F d) : Refutes G d :=
  cone_identify ρ clauses hf

/-- Identification followed by deduplicated clause guarding. -/
theorem cone_identify_guard {F G d} (ρ : Var → Var) (l : Lit)
    (clauses : ∀ c ∈ F, (renameClause ρ c ++ [neg l]).eraseDups ∈ G)
    {f} (hf : Cone F d f) :
    Cone G (d+1) (fun a => conjunction [l] a * f (fun v => a (ρ v))) := by
  let H := F.map (renameClause ρ)
  have hh : Cone H d (fun a => f (fun v => a (ρ v))) :=
    cone_identify ρ (by intro c hc; exact List.mem_map.mpr ⟨c,hc,rfl⟩) hf
  apply cone_guard_of_dedup_clauses l _ hh
  intro c hc
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hc
  exact clauses e he

#print axioms cone_identify_guard
#print axioms cone_identify
#print axioms refutes_identify
end Programme.«20261031-2024-proof-complexity».NativeIter
