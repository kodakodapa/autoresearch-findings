import Programme.«20261031-2024-proof-complexity».RefUnary

namespace Programme.«20261031-2024-proof-complexity».RefCNF
open Programme.«20261024-1110-proof-complexity».Haken
open Programme.«20261031-2024-proof-complexity».RefUnary

inductive Index (n m s : Nat) where
  | leftCopy (b a : Fin s) (x : Fin n) (l : Lit (Fin n))
  | rightCopy (b a : Fin s) (x : Fin n) (l : Lit (Fin n))
  | weakCopy (b : Fin s) (a : Fin m) (l : Lit (Fin n))
  | resolve (b : Fin s)
  | pointLeft (b : Fin s)
  | pointRight (b : Fin s)
  | weaken (b : Fin s)
  | enableLeft (b a : Fin s)
  | enableRight (b a : Fin s)
  | empty (l : Lit (Fin n))
  | enabled

def literals (n : Nat) : List (Lit (Fin n)) :=
  (List.finRange n).flatMap fun x => [⟨x,true⟩,⟨x,false⟩]

theorem mem_literals {n : Nat} (l : Lit (Fin n)) : l ∈ literals n := by
  rcases l with ⟨x,p⟩
  cases p <;> simp [literals]

def indices (n m s : Nat) : List (Index n m s) :=
  ((List.finRange s).flatMap fun b => (List.finRange s).flatMap fun a =>
    (List.finRange n).flatMap fun x => (literals n).flatMap fun l =>
      [.leftCopy b a x l,.rightCopy b a x l]) ++
  ((List.finRange s).flatMap fun b => (List.finRange m).flatMap fun a =>
    (literals n).map fun l => .weakCopy b a l) ++
  ((List.finRange s).flatMap fun b => [.resolve b,.pointLeft b,.pointRight b,.weaken b]) ++
  ((List.finRange s).flatMap fun b => (List.finRange s).flatMap fun a =>
    [.enableLeft b a,.enableRight b a]) ++
  ((literals n).map .empty) ++ [.enabled]

theorem mem_indices {n m s : Nat} (i : Index n m s) : i ∈ indices n m s := by
  cases i <;> simp [indices, mem_literals]

def Valid {n s : Nat} (F : CNF (Fin n)) : Index n F.length s → Prop
  | .leftCopy b a x l => a.val < b.val ∧ l ≠ ⟨x,true⟩
  | .rightCopy b a x l => a.val < b.val ∧ l ≠ ⟨x,false⟩
  | .weakCopy _ a l => l ∈ F[a]
  | .enableLeft b a => a.val < b.val
  | .enableRight b a => a.val < b.val
  | _ => True

instance {n s : Nat} (F : CNF (Fin n)) (i : Index n F.length s) :
    Decidable (Valid F i) := by
  cases i <;> dsimp [Valid] <;> infer_instance

/-- Clause with the negative literals listed first, followed by positive literals. -/
def implication {V : Type} (neg pos : List V) : Clause V :=
  neg.map (fun v => ⟨v,false⟩) ++ pos.map (fun v => ⟨v,true⟩)

def clause {n s : Nat} {F : CNF (Fin n)} (root : Fin s) :
    Index n F.length s → Clause (Var n F.length s)
  | .leftCopy b a x l => implication [.enable b,.res b x,.left b a,.lit a l] [.lit b l]
  | .rightCopy b a x l => implication [.enable b,.res b x,.right b a,.lit a l] [.lit b l]
  | .weakCopy b a l => implication [.enable b,.weak b a] [.lit b l]
  | .resolve b => implication [.enable b,.derived b]
      ((List.finRange n).map fun x => .res b x)
  | .pointLeft b => implication [.enable b,.derived b]
      (((List.finRange s).filter fun a => a.val < b.val).map fun a => .left b a)
  | .pointRight b => implication [.enable b,.derived b]
      (((List.finRange s).filter fun a => a.val < b.val).map fun a => .right b a)
  | .weaken b => implication [.enable b]
      (.derived b :: ((List.finRange F.length).map fun a => .weak b a))
  | .enableLeft b a => implication [.enable b,.left b a] [.enable a]
  | .enableRight b a => implication [.enable b,.right b a] [.enable a]
  | .empty l => implication [.lit root l] []
  | .enabled => implication [] [.enable root]

/-- The actual finite CNF of Definition 2.4, with input variables specialized to F.
Zero blocks give the empty clause. All other roots are the final block. -/
def refCNF {n : Nat} (F : CNF (Fin n)) (s : Nat) : CNF (Var n F.length s) :=
  if hs : 0 < s then
    ((indices n F.length s).filter (fun i => decide (Valid F i))).map
      (clause (F := F) ⟨s-1,by omega⟩)
  else [[]]

/-- Satisfaction of a positive/negative clause implies its implication reading. -/
theorem implication_sound {V : Type} (a : V → Bool) (neg pos : List V)
    (h : Clause.eval a (implication neg pos) = true)
    (hn : ∀ v ∈ neg, a v = true) : ∃ v ∈ pos, a v = true := by
  obtain ⟨l,hl,ht⟩ := List.any_eq_true.mp h
  rcases List.mem_append.mp hl with hl | hl
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hl
    simp [Lit.eval,hn v hv] at ht
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hl
    exact ⟨v,hv,by simpa [Lit.eval] using ht⟩



theorem model_of_satisfies {n s : Nat} {F : CNF (Fin n)}
    (a : Var n F.length s → Bool)
    (hsat : ∀ C ∈ refCNF F s, Clause.eval a C = true) : Nonempty (Model F s) := by
  classical
  have hs : 0 < s := by
    by_cases hp : 0 < s
    · exact hp
    · have := hsat [] (by simp [refCNF,hp])
      simp [Clause.eval] at this
  let root : Fin s := ⟨s-1,by omega⟩
  have hi : ∀ i : Index n F.length s, Valid F i →
      Clause.eval a (clause root i) = true := by
    intro i hv
    apply hsat
    simp only [refCNF,dite_eq_left hs]
    apply List.mem_map.mpr
    exact ⟨i,List.mem_filter.mpr ⟨mem_indices i,by simpa⟩,rfl⟩
  refine ⟨{
    value := fun v => a v = true
    left_copy := ?_
    right_copy := ?_
    weak_copy := ?_
    must_resolve := ?_
    must_left := ?_
    must_right := ?_
    must_weaken := ?_
    enable_left := ?_
    enable_right := ?_
    root := root
    root_last := by dsimp [root]; omega
    root_empty := ?_
    root_enabled := ?_
  }⟩
  · intro b c x l hcb hne hb hx hc hl
    have h := implication_sound a _ _ (hi (.leftCopy b c x l) ⟨hcb,hne⟩)
      (by intro v hv; simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
          rcases hv with rfl | rfl | rfl | rfl <;> assumption)
    simpa using h
  · intro b c x l hcb hne hb hx hc hl
    have h := implication_sound a _ _ (hi (.rightCopy b c x l) ⟨hcb,hne⟩)
      (by intro v hv; simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
          rcases hv with rfl | rfl | rfl | rfl <;> assumption)
    simpa using h
  · intro b c l hmem hb hc
    have h := implication_sound a _ _ (hi (.weakCopy b c l) hmem)
      (by intro v hv; simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
          rcases hv with rfl | rfl <;> assumption)
    simpa using h
  · intro b hb hd
    have h := implication_sound a _ _ (hi (.resolve b) trivial)
      (by intro v hv; simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
          rcases hv with rfl | rfl <;> assumption)
    obtain ⟨v,hv,ht⟩ := h
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp hv
    exact ⟨x,ht⟩
  · intro b hb hd
    have h := implication_sound a _ _ (hi (.pointLeft b) trivial)
      (by intro v hv; simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
          rcases hv with rfl | rfl <;> assumption)
    obtain ⟨v,hv,ht⟩ := h
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hv
    exact ⟨c,(List.mem_filter.mp hc).2 |> of_decide_eq_true,ht⟩
  · intro b hb hd
    have h := implication_sound a _ _ (hi (.pointRight b) trivial)
      (by intro v hv; simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
          rcases hv with rfl | rfl <;> assumption)
    obtain ⟨v,hv,ht⟩ := h
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hv
    exact ⟨c,(List.mem_filter.mp hc).2 |> of_decide_eq_true,ht⟩
  · intro b hb hd
    have h := implication_sound a _ _ (hi (.weaken b) trivial)
      (by simpa using hb)
    obtain ⟨v,hv,ht⟩ := h
    rcases List.mem_cons.mp hv with hv | hv
    · subst v; exact False.elim (hd ht)
    · obtain ⟨c,_,rfl⟩ := List.mem_map.mp hv
      exact ⟨c,ht⟩
  · intro b c hcb hb hc
    have h := implication_sound a _ _ (hi (.enableLeft b c) hcb)
      (by intro v hv; simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
          rcases hv with rfl | rfl <;> assumption)
    simpa using h
  · intro b c hcb hb hc
    have h := implication_sound a _ _ (hi (.enableRight b c) hcb)
      (by intro v hv; simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
          rcases hv with rfl | rfl <;> assumption)
    simpa using h
  · intro l hl
    have h := implication_sound a _ _ (hi (.empty l) trivial) (by simpa using hl)
    simp at h
  · have h := implication_sound a _ _ (hi .enabled trivial) (by simp)
    simpa using h

/-- For every n,s and input CNF, absence of a size-at-most-s library resolution
refutation implies unsatisfiability of the finite unary-relativized Ref CNF. -/
theorem refCNF_unsat {n s : Nat} (F : CNF (Fin n))
    (h : ¬ ∃ R : Refutation F, R.steps.length ≤ s) :
    ¬ ∃ a : Var n F.length s → Bool, ∀ C ∈ refCNF F s, Clause.eval a C = true := by
  rintro ⟨a,ha⟩
  exact unsat_of_no_short_refutation F h (model_of_satisfies a ha)

#print axioms model_of_satisfies
#print axioms refCNF_unsat
end Programme.«20261031-2024-proof-complexity».RefCNF
