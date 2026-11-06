import Programme.«20261031-2024-proof-complexity».NativeIter

namespace Programme.«20261031-2024-proof-complexity».NativeIter

def renameLit (ρ : Var → Var) (l : Lit) : Lit := (ρ l.1, l.2)
def renameClause (ρ : Var → Var) (c : Clause) : Clause := c.map (renameLit ρ)

theorem conjunction_rename (ρ : Var → Var) (m : List Lit) (a : Assignment) :
    conjunction (renameClause ρ m) a = conjunction m (fun v => a (ρ v)) := by
  unfold conjunction renameClause
  rw [List.all_map]
  rfl

theorem multiplier_rename (ρ : Var → Var) (hρ : Function.Injective ρ)
    {m : List Lit} (hm : Multiplier m) : Multiplier (renameClause ρ m) := by
  change ((m.map (renameLit ρ)).map Prod.fst).Nodup
  have he : (m.map (renameLit ρ)).map Prod.fst = (m.map Prod.fst).map ρ := by
    simp [List.map_map, Function.comp_def, renameLit]
  rw [he]
  exact List.Pairwise.map ρ (fun a b hab he => hab (hρ he)) hm

theorem falsity_rename (ρ : Var → Var) (c : Clause) :
    falsity (renameClause ρ c) = renameClause ρ (falsity c) := by
  simp [falsity, renameClause, List.map_map, Function.comp_def, neg, renameLit]

/-- Injective variable renaming preserves the formal degree and every cone generator. -/
theorem cone_rename (ρ : Var → Var) (hρ : Function.Injective ρ) {F G d}
    (clauses : ∀ c ∈ F, renameClause ρ c ∈ G) {f} (hf : Cone F d f) :
    Cone G d (fun a => f (fun v => a (ρ v))) := by
  induction hf with
  | positive m hm hd =>
    have h := Cone.positive (F := G) (d := d) (renameClause ρ m)
      (multiplier_rename ρ hρ hm) (by simpa [renameClause] using hd)
    have he : conjunction (renameClause ρ m) =
        (fun a => conjunction m (fun v => a (ρ v))) := funext (conjunction_rename ρ m)
    rw [he] at h
    exact h
  | equation c m r hc hd =>
    have ha : Admitted d (renameClause ρ c) (renameClause ρ m) := by
      exact ⟨multiplier_rename ρ hρ hd.1, by simpa [renameClause] using hd.2⟩
    have h := Cone.equation (renameClause ρ c) (renameClause ρ m) r (clauses c hc) ha
    have he : (fun a => r * conjunction (renameClause ρ m ++ falsity (renameClause ρ c)) a) =
        (fun a => r * conjunction (m ++ falsity c) (fun v => a (ρ v))) := by
      funext a
      rw [falsity_rename]
      have happ : renameClause ρ m ++ renameClause ρ (falsity c) =
          renameClause ρ (m ++ falsity c) := by simp [renameClause]
      rw [happ]
      rw [conjunction_rename]
    rw [he] at h
    exact h
  | zero => exact Cone.zero
  | add _ _ ih jh => exact Cone.add ih jh
  | scale r hr _ ih => exact Cone.scale r hr ih

theorem refutes_rename (ρ : Var → Var) (hρ : Function.Injective ρ) {F G d}
    (clauses : ∀ c ∈ F, renameClause ρ c ∈ G) (hf : Refutes F d) : Refutes G d :=
  cone_rename ρ hρ clauses hf

#print axioms cone_rename
#print axioms refutes_rename
end Programme.«20261031-2024-proof-complexity».NativeIter
