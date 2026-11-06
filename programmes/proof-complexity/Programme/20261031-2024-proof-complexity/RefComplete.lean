import Programme.«20261031-2024-proof-complexity».RefCNFExact

namespace Programme.«20261031-2024-proof-complexity».RefComplete
open Programme.«20261024-1110-proof-complexity».Haken
open Programme.«20261031-2024-proof-complexity».RefUnary Programme.«20261031-2024-proof-complexity».RefCNF Programme.«20261031-2024-proof-complexity».RefCNFExact

/-- Explicitly selected justification for a block. -/
abbrev Reason (n m s : Nat) := Sum (Fin m) (Fin n × Fin s × Fin s)

def Spec {n s : Nat} (F : CNF (Fin n)) (L : List (Clause (Fin n)))
    (hlen : L.length = s) (b : Fin s) : Reason n F.length s → Prop
  | .inl j => L[b.val]'(by omega) = F[j]
  | .inr (x,a,c) => a.val < b.val ∧ c.val < b.val ∧
      (∀ l ∈ L[a.val]'(by omega), l ≠ ⟨x,true⟩ → l ∈ L[b.val]'(by omega)) ∧
      (∀ l ∈ L[c.val]'(by omega), l ≠ ⟨x,false⟩ → l ∈ L[b.val]'(by omega))

theorem reason_exists {n s : Nat} {F : CNF (Fin n)}
    {L : List (Clause (Fin n))} (hlen : L.length = s) (hg : Good F L) (b : Fin s) :
    ∃ r, Spec F L hlen b r := by
  rcases hg b.val (by omega) with h | ⟨a,c,ha,hc,x,hx,hneg,hleft,hright⟩
  · obtain ⟨j,hj,he⟩ := List.mem_iff_getElem.mp h
    exact ⟨.inl ⟨j,hj⟩,he.symm⟩
  · exact ⟨.inr (x,⟨a,by omega⟩,⟨c,by omega⟩),ha,hc,hleft,hright⟩

def valuation {n m s : Nat} (L : Fin s → Clause (Fin n))
    (r : Fin s → Reason n m s) : Var n m s → Prop
  | .enable _ => True
  | .lit b l => l ∈ L b
  | .derived b => ∃ t, r b = .inr t
  | .weak b j => r b = .inl j
  | .res b x => ∃ a c, r b = .inr (x,a,c)
  | .left b a => ∃ x c, r b = .inr (x,a,c)
  | .right b c => ∃ x a, r b = .inr (x,a,c)

theorem model_of_good {n s : Nat} {F : CNF (Fin n)}
    {L : List (Clause (Fin n))} (hlen : L.length = s) (hg : Good F L)
    (root : Fin s) (hlast : root.val + 1 = s)
    (he : L[root.val]'(by omega) = []) : Nonempty (Model F s) := by
  classical
  let r := fun b => Classical.choose (reason_exists hlen hg b)
  have spec (b) : Spec F L hlen b (r b) := Classical.choose_spec (reason_exists hlen hg b)
  let val := valuation (fun b : Fin s => L[b.val]'(by omega)) r
  refine ⟨{ value := val, root := root, root_last := hlast,
            root_enabled := True.intro,
            left_copy := ?_, right_copy := ?_, weak_copy := ?_,
            must_resolve := ?_, must_left := ?_, must_right := ?_, must_weaken := ?_,
            enable_left := ?_, enable_right := ?_, root_empty := ?_ }⟩
  · intro b a x l hba hne hb hx ha hl
    obtain ⟨a',c,hr⟩ := hx
    obtain ⟨x',c',hr'⟩ := ha
    have eq := hr.symm.trans hr'
    cases eq
    have hs := spec b
    rw [hr] at hs
    exact hs.2.2.1 l hl hne
  · intro b c x l hbc hne hb hx hc hl
    obtain ⟨a,c',hr⟩ := hx
    obtain ⟨x',a',hr'⟩ := hc
    have eq := hr.symm.trans hr'
    cases eq
    have hs := spec b
    rw [hr] at hs
    exact hs.2.2.2 l hl hne
  · intro b j l hl hb hj
    have hs := spec b
    change r b = .inl j at hj
    rw [hj] at hs
    change L[b.val]'(by omega) = F[j] at hs
    change l ∈ L[b.val]'(by omega)
    rw [hs]; exact hl
  · intro b hb hd
    obtain ⟨⟨x,a,c⟩,hr⟩ := hd
    exact ⟨x,a,c,hr⟩
  · intro b hb hd
    obtain ⟨⟨x,a,c⟩,hr⟩ := hd
    have hs := spec b
    rw [hr] at hs
    exact ⟨a,hs.1,x,c,hr⟩
  · intro b hb hd
    obtain ⟨⟨x,a,c⟩,hr⟩ := hd
    have hs := spec b
    rw [hr] at hs
    exact ⟨c,hs.2.1,x,a,hr⟩
  · intro b hb hd
    cases hr : r b with
    | inl j => exact ⟨j,hr⟩
    | inr t => exact False.elim (hd ⟨t,hr⟩)
  · intro b a hba hb ha; trivial
  · intro b a hba hb ha; trivial
  · intro l hl
    change l ∈ L[root.val]'(by omega) at hl
    simp [he] at hl

theorem good_take {n : Nat} {F : CNF (Fin n)} {L : List (Clause (Fin n))}
    (hg : Good F L) (t : Nat) : Good F (L.take t) := by
  intro k hk
  have hkL : k < L.length := by
    have hh : (L.take t).length ≤ L.length := by simp only [List.length_take]; exact Nat.min_le_right _ _
    exact Nat.lt_of_lt_of_le hk hh
  rcases hg k hkL with h | ⟨a,b,ha,hb,hr⟩
  · left; simpa using h
  · right
    exact ⟨a,b,ha,hb,by simpa using hr⟩

theorem pad {n : Nat} {F : CNF (Fin n)} {L : List (Clause (Fin n))}
    (hg : Good F L) (root : Fin L.length) (hr : root.val + 1 = L.length)
    (he : L[root.val] = []) : ∀ t, ∃ K : List (Clause (Fin n)),
      K.length = L.length + t ∧ Good F K ∧
      ∃ j : Fin K.length, j.val + 1 = K.length ∧ K[j.val] = [] := by
  intro t
  induction t with
  | zero => exact ⟨L,by omega,hg,root,hr,he⟩
  | succ t ih =>
    obtain ⟨K,hk,hgood,j,hj,hempty⟩ := ih
    have hlegal : Legal F K [] := hempty ▸ legal_previous hgood j.val j.isLt
    refine ⟨K ++ [[]],by simp [hk]; omega,good_append hgood hlegal,
      ⟨K.length,by simp⟩,by simp,?_⟩
    simp

/-- Every library refutation fitting the block bound has a semantic Ref model. -/
theorem model_of_refutation {n s : Nat} {F : CNF (Fin n)}
    (R : Refutation F) (hs : R.steps.length ≤ s) : Nonempty (Model F s) := by
  obtain ⟨j,hj,he⟩ := List.mem_iff_getElem.mp R.empty_mem
  let L := R.steps.take (j+1)
  have hlen : L.length = j+1 := by simp [L,List.length_take,Nat.min_eq_left (by omega : j+1 ≤ R.steps.length)]
  have hg : Good F L := good_take R.derived (j+1)
  have hempty : L[j]'(by omega) = [] := by simpa [L] using he
  obtain ⟨K,hK,hgood,r,hr,hroot⟩ := pad hg ⟨j,by omega⟩ (by change j+1 = L.length; omega) hempty (s-L.length)
  have hKs : K.length = s := by omega
  exact model_of_good hKs hgood ⟨r.val,by omega⟩ (by change r.val+1 = s; omega) hroot

/-- Exact correctness for the fixed-input formula and total library line count. -/
theorem satisfiable_iff_short_refutation {n s : Nat} (F : CNF (Fin n)) :
    (∃ a : Var n F.length s → Bool, ∀ C ∈ refCNF F s, Clause.eval a C = true) ↔
      ∃ R : Refutation F, R.steps.length ≤ s := by
  rw [satisfiable_iff_model]
  constructor
  · rintro ⟨M⟩
    obtain ⟨R,hR⟩ := extract M
    exact ⟨R,Nat.le_of_eq hR⟩
  · rintro ⟨R,hR⟩
    exact model_of_refutation R hR

#print axioms model_of_refutation
#print axioms satisfiable_iff_short_refutation
end Programme.«20261031-2024-proof-complexity».RefComplete
