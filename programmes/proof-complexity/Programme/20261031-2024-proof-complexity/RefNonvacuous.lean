import Programme.«20261031-2024-proof-complexity».RefCNFExact

namespace Programme.«20261031-2024-proof-complexity».RefNonvacuous
open Programme.«20261024-1110-proof-complexity».Haken
open Programme.«20261031-2024-proof-complexity».RefUnary Programme.«20261031-2024-proof-complexity».RefCNF Programme.«20261031-2024-proof-complexity».RefCNFExact

/-- A fixed empty input clause witnesses satisfiability for every positive block bound. -/
theorem model_of_empty {n s : Nat} (F : CNF (Fin n)) (hs : 0 < s)
    (he : ([] : Clause (Fin n)) ∈ F) : Nonempty (Model F s) := by
  classical
  obtain ⟨j,hj⟩ := List.mem_iff_getElem.mp he
  let val : Var n F.length s → Prop
    | .enable _ => True
    | .weak _ a => F[a] = []
    | _ => False
  refine ⟨{ value := val
            root := ⟨s-1,by omega⟩
            root_last := by simp; omega
            left_copy := ?_
            right_copy := ?_
            weak_copy := ?_
            must_resolve := ?_
            must_left := ?_
            must_right := ?_
            must_weaken := ?_
            enable_left := ?_
            enable_right := ?_
            root_empty := ?_
            root_enabled := True.intro }⟩
  · intro b a x l hba hne hb hx; exact False.elim hx
  · intro b a x l hba hne hb hx; exact False.elim hx
  · intro b a l hl hb ha
    change F[a] = [] at ha
    simpa [ha] using hl
  · intro b hb hd; exact False.elim hd
  · intro b hb hd; exact False.elim hd
  · intro b hb hd; exact False.elim hd
  · intro b hb hd
    exact ⟨⟨j, hj.1⟩,hj.2⟩
  · intro b a hba hb ha; trivial
  · intro b a hba hb ha; trivial
  · intro l hl; exact hl

theorem satisfiable_of_empty {n s : Nat} (F : CNF (Fin n)) (hs : 0 < s)
    (he : ([] : Clause (Fin n)) ∈ F) :
    ∃ a : Var n F.length s → Bool, ∀ C ∈ refCNF F s, Clause.eval a C = true := by
  obtain ⟨M⟩ := model_of_empty F hs he
  exact satisfies_of_model M

#print axioms model_of_empty
#print axioms satisfiable_of_empty
end Programme.«20261031-2024-proof-complexity».RefNonvacuous
