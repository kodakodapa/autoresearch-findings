import Programme.«20261031-2024-proof-complexity».RefCNF
namespace Programme.«20261031-2024-proof-complexity».RefCNFExact
open Programme.«20261024-1110-proof-complexity».Haken
open Programme.«20261031-2024-proof-complexity».RefUnary Programme.«20261031-2024-proof-complexity».RefCNF

theorem implication_complete {V : Type} (a : V → Bool) (neg pos : List V)
    (h : (∀ v ∈ neg, a v = true) → ∃ v ∈ pos, a v = true) :
    Clause.eval a (implication neg pos) = true := by
  classical
  by_cases hn : ∀ v ∈ neg, a v = true
  · obtain ⟨v,hv,ht⟩ := h hn
    exact List.any_eq_true.mpr ⟨⟨v,true⟩,List.mem_append_right _
      (List.mem_map.mpr ⟨v,hv,rfl⟩),by simpa [Lit.eval]⟩
  · have hex : ∃ v ∈ neg, a v ≠ true := by simpa using hn
    obtain ⟨v,hv,ht⟩ := hex
    apply List.any_eq_true.mpr
    refine ⟨⟨v,false⟩,List.mem_append_left _ (List.mem_map.mpr ⟨v,hv,rfl⟩),?_⟩
    cases he : a v <;> simp_all [Lit.eval]

theorem satisfies_of_model {n s : Nat} {F : CNF (Fin n)} (M : Model F s) :
    ∃ a : Var n F.length s → Bool, ∀ C ∈ refCNF F s, Clause.eval a C = true := by
  classical
  let a : Var n F.length s → Bool := fun v => decide (M.value v)
  have av (v) : a v = true ↔ M.value v := by simp [a]
  have hs : 0 < s := by have := M.root.isLt; omega
  have er : (⟨s-1,by omega⟩ : Fin s) = M.root := by
    apply Fin.ext; change s-1 = M.root.val; have := M.root_last; omega
  refine ⟨a,?_⟩
  intro C hC
  simp only [refCNF,dite_eq_left hs] at hC
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hC
  have hv : Valid F i := of_decide_eq_true (List.mem_filter.mp hi).2
  rw [er]
  cases i with
  | leftCopy b c x l =>
    apply implication_complete
    simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,
      exists_eq_left,av, and_imp]
    exact M.left_copy b c x l hv.1 hv.2
  | rightCopy b c x l =>
    apply implication_complete
    simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,
      exists_eq_left,av, and_imp]
    exact M.right_copy b c x l hv.1 hv.2
  | weakCopy b c l =>
    apply implication_complete
    simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,
      exists_eq_left,av, and_imp]
    exact M.weak_copy b c l hv
  | resolve b =>
    apply implication_complete
    intro h
    obtain ⟨x,hx⟩ := M.must_resolve b ((av _).mp (h _ (by simp)))
      ((av _).mp (h _ (by simp)))
    exact ⟨_,List.mem_map.mpr ⟨x,by simp,rfl⟩,(av _).mpr hx⟩
  | pointLeft b =>
    apply implication_complete
    intro h
    obtain ⟨c,hcb,hc⟩ := M.must_left b ((av _).mp (h _ (by simp)))
      ((av _).mp (h _ (by simp)))
    exact ⟨_,List.mem_map.mpr ⟨c,by simp [hcb],rfl⟩,(av _).mpr hc⟩
  | pointRight b =>
    apply implication_complete
    intro h
    obtain ⟨c,hcb,hc⟩ := M.must_right b ((av _).mp (h _ (by simp)))
      ((av _).mp (h _ (by simp)))
    exact ⟨_,List.mem_map.mpr ⟨c,by simp [hcb],rfl⟩,(av _).mpr hc⟩
  | weaken b =>
    apply implication_complete
    intro h
    have hb : M.value (.enable b) := (av _).mp (h _ (by simp))
    by_cases hd : M.value (.derived b)
    · exact ⟨_,by simp,(av _).mpr hd⟩
    · obtain ⟨c,hc⟩ := M.must_weaken b hb hd
      exact ⟨_,by simp,(av _).mpr hc⟩
  | enableLeft b c =>
    apply implication_complete
    simpa [av] using M.enable_left b c hv
  | enableRight b c =>
    apply implication_complete
    simpa [av] using M.enable_right b c hv
  | empty l =>
    apply implication_complete
    simpa [av] using M.root_empty l
  | enabled =>
    apply implication_complete
    simpa [av] using M.root_enabled

theorem satisfiable_iff_model {n s : Nat} (F : CNF (Fin n)) :
    (∃ a : Var n F.length s → Bool, ∀ C ∈ refCNF F s, Clause.eval a C = true) ↔
      Nonempty (Model F s) := by
  constructor
  · rintro ⟨a,ha⟩; exact model_of_satisfies a ha
  · rintro ⟨M⟩; exact satisfies_of_model M
#print axioms satisfies_of_model
#print axioms satisfiable_iff_model
end Programme.«20261031-2024-proof-complexity».RefCNFExact
