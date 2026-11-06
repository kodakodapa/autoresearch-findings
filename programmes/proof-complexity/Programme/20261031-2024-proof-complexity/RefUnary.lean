import Programme.«20261024-1110-proof-complexity».Haken

/-! Def. 2.4 of Arteche--Atserias--de Rezende--Khaniki, arXiv:2506.16956v2.
Blocks are zero based; block s-1 is the root. Formula literals use Fin n.
The input-literal variables are specialized to the fixed input CNF F.
`Model` is the conjunction of the eleven displayed clause families, with finite
positive disjunctions represented by bounded existentials. No uniqueness or
pivot-presence conditions are added. -/
namespace Programme.«20261031-2024-proof-complexity».RefUnary
open Programme.«20261024-1110-proof-complexity».Haken

inductive Var (n m s : Nat) where
  | enable : Fin s → Var n m s
  | derived : Fin s → Var n m s
  | weak : Fin s → Fin m → Var n m s
  | lit : Fin s → Lit (Fin n) → Var n m s
  | res : Fin s → Fin n → Var n m s
  | left : Fin s → Fin s → Var n m s
  | right : Fin s → Fin s → Var n m s

/-- A truth assignment satisfying exactly the eleven families of Def. 2.4,
after specializing the input-literal variables to F. -/
structure Model {n : Nat} (F : CNF (Fin n)) (s : Nat) where
  value : Var n F.length s → Prop
  left_copy : ∀ (b a : Fin s) (x : Fin n) (l : Lit (Fin n)),
    a.val < b.val → l ≠ ⟨x,true⟩ →
    value (.enable b) → value (.res b x) → value (.left b a) →
    value (.lit a l) → value (.lit b l)
  right_copy : ∀ (b a : Fin s) (x : Fin n) (l : Lit (Fin n)),
    a.val < b.val → l ≠ ⟨x,false⟩ →
    value (.enable b) → value (.res b x) → value (.right b a) →
    value (.lit a l) → value (.lit b l)
  weak_copy : ∀ (b : Fin s) (a : Fin F.length) (l : Lit (Fin n)),
    l ∈ F[a] → value (.enable b) → value (.weak b a) → value (.lit b l)
  must_resolve : ∀ b, value (.enable b) → value (.derived b) →
    ∃ x, value (.res b x)
  must_left : ∀ b, value (.enable b) → value (.derived b) →
    ∃ a, a.val < b.val ∧ value (.left b a)
  must_right : ∀ b, value (.enable b) → value (.derived b) →
    ∃ a, a.val < b.val ∧ value (.right b a)
  must_weaken : ∀ b, value (.enable b) → ¬ value (.derived b) →
    ∃ a, value (.weak b a)
  enable_left : ∀ b a, a.val < b.val → value (.enable b) →
    value (.left b a) → value (.enable a)
  enable_right : ∀ b a, a.val < b.val → value (.enable b) →
    value (.right b a) → value (.enable a)
  root : Fin s
  root_last : root.val + 1 = s
  root_empty : ∀ l, ¬ value (.lit root l)
  root_enabled : value (.enable root)

/-- Every enabled block contains a literal true under any satisfying input assignment. -/
theorem enabled_true {n s : Nat} {F : CNF (Fin n)} (M : Model F s)
    (a : Fin n → Bool) (hF : ∀ C ∈ F, Clause.eval a C = true)
    (b : Fin s) (hb : M.value (.enable b)) :
    ∃ l, M.value (.lit b l) ∧ Lit.eval a l = true := by
  classical
  have go : ∀ k, ∀ (b : Fin s), b.val = k → M.value (.enable b) →
      ∃ l, M.value (.lit b l) ∧ Lit.eval a l = true := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro b hbk hb
      by_cases hd : M.value (.derived b)
      · obtain ⟨x,hx⟩ := M.must_resolve b hb hd
        cases ha : a x with
        | false =>
          obtain ⟨c,hcb,hc⟩ := M.must_left b hb hd
          obtain ⟨l,hl,ht⟩ := ih c.val (by omega) c rfl
            (M.enable_left b c hcb hb hc)
          have hne : l ≠ ⟨x,true⟩ := by
            intro e; subst l; simp [Lit.eval,ha] at ht
          exact ⟨l,M.left_copy b c x l hcb hne hb hx hc hl,ht⟩
        | true =>
          obtain ⟨c,hcb,hc⟩ := M.must_right b hb hd
          obtain ⟨l,hl,ht⟩ := ih c.val (by omega) c rfl
            (M.enable_right b c hcb hb hc)
          have hne : l ≠ ⟨x,false⟩ := by
            intro e; subst l; simp [Lit.eval,ha] at ht
          exact ⟨l,M.right_copy b c x l hcb hne hb hx hc hl,ht⟩
      · obtain ⟨j,hj⟩ := M.must_weaken b hb hd
        have ht := hF F[j] (List.getElem_mem j.isLt)
        obtain ⟨l,hl,ht⟩ := List.any_eq_true.mp ht
        exact ⟨l,M.weak_copy b j l hl hb hj,ht⟩
  exact go b.val b rfl hb

/-- Sanity direction: a model of Ref_s(F) excludes every satisfying assignment of F. -/
theorem model_implies_unsat {n s : Nat} {F : CNF (Fin n)} (M : Model F s) :
    ¬ ∃ a : Fin n → Bool, ∀ C ∈ F, Clause.eval a C = true := by
  rintro ⟨a,ha⟩
  obtain ⟨l,hl,_⟩ := enabled_true M a ha M.root M.root_enabled
  exact M.root_empty l hl

/-- One legal next clause in the library convention. -/
def Legal {n : Nat} (F : CNF (Fin n)) (L : List (Clause (Fin n)))
    (C : Clause (Fin n)) : Prop :=
  C ∈ F ∨ ∃ a b, ∃ (ha : a < L.length) (hb : b < L.length),
    IsResolvent L[a] L[b] C

def Good {n : Nat} (F : CNF (Fin n)) (L : List (Clause (Fin n))) : Prop :=
  ∀ k (hk : k < L.length), L[k] ∈ F ∨
    ∃ a b, ∃ (ha : a < k) (hb : b < k),
      IsResolvent (L[a]'(Nat.lt_trans ha hk)) (L[b]'(Nat.lt_trans hb hk)) L[k]

theorem legal_previous {n : Nat} {F : CNF (Fin n)}
    {L : List (Clause (Fin n))} (h : Good F L) (k : Nat) (hk : k < L.length) :
    Legal F L L[k] := by
  rcases h k hk with h | ⟨a,b,ha,hb,hr⟩
  · exact Or.inl h
  · exact Or.inr ⟨a,b,Nat.lt_trans ha hk,Nat.lt_trans hb hk,hr⟩

theorem good_append {n : Nat} {F : CNF (Fin n)}
    {L : List (Clause (Fin n))} {C : Clause (Fin n)}
    (h : Good F L) (hc : Legal F L C) : Good F (L ++ [C]) := by
  intro k hk
  by_cases hkl : k < L.length
  · rcases h k hkl with h | ⟨a,b,ha,hb,hr⟩
    · left; simpa [List.getElem_append_left hkl] using h
    · right
      refine ⟨a,b,ha,hb,?_⟩
      simpa [List.getElem_append_left hkl,
        List.getElem_append_left (Nat.lt_trans ha hkl),
        List.getElem_append_left (Nat.lt_trans hb hkl)] using hr
  · have ek : k = L.length := by simp only [List.length_append,List.length_singleton] at hk; omega
    subst k
    rcases hc with hc | ⟨a,b,ha,hb,hr⟩
    · left; simpa using hc
    · right
      refine ⟨a,b,ha,hb,?_⟩
      simpa [List.getElem_append_left ha,List.getElem_append_left hb] using hr

/-- Eliminate missing pivots by reusing a parent, otherwise take a resolvent. -/
theorem normalize {n : Nat} {F : CNF (Fin n)} {L : List (Clause (Fin n))}
    (hg : Good F L) (i j : Nat) (hi : i < L.length) (hj : j < L.length)
    (x : Fin n) (P : Lit (Fin n) → Prop)
    (hl : ∀ l ∈ L[i], l ≠ ⟨x,true⟩ → P l)
    (hr : ∀ l ∈ L[j], l ≠ ⟨x,false⟩ → P l) :
    ∃ C, Legal F L C ∧ ∀ l ∈ C, P l := by
  classical
  by_cases hp : (⟨x,true⟩ : Lit (Fin n)) ∈ L[i]
  · by_cases hn : (⟨x,false⟩ : Lit (Fin n)) ∈ L[j]
    · let C := (L[i].filter (fun l => l != ⟨x,true⟩)) ++
        (L[j].filter (fun l => l != ⟨x,false⟩))
      refine ⟨C,Or.inr ⟨i,j,hi,hj,x,hp,hn,?_,?_⟩,?_⟩
      · intro l hm hne
        apply List.mem_append_left
        exact List.mem_filter.mpr ⟨hm,by simpa using hne⟩
      · intro l hm hne
        apply List.mem_append_right
        exact List.mem_filter.mpr ⟨hm,by simpa using hne⟩
      · intro l hm
        rcases List.mem_append.mp hm with hm | hm
        · obtain ⟨hm,he⟩ := List.mem_filter.mp hm
          exact hl l hm (by simpa using he)
        · obtain ⟨hm,he⟩ := List.mem_filter.mp hm
          exact hr l hm (by simpa using he)
    · exact ⟨L[j],legal_previous hg j hj,fun l hm => hr l hm (by intro e; subst l; exact hn hm)⟩
  · exact ⟨L[i],legal_previous hg i hi,fun l hm => hl l hm (by intro e; subst l; exact hp hm)⟩


theorem input_nonempty {n s : Nat} {F : CNF (Fin n)} (M : Model F s) : F ≠ [] := by
  intro e
  apply model_implies_unsat M
  exact ⟨fun _ => false,by simp [e]⟩

/-- A prefix can be normalized without adding any blocks. Disabled blocks are
filled with an input axiom; copies reuse the earlier clause's justification. -/
theorem normalized_prefix {n s : Nat} {F : CNF (Fin n)} (M : Model F s) :
    ∀ t, t ≤ s → ∃ L : List (Clause (Fin n)), ∃ hlen : L.length = t, Good F L ∧
      ∀ (b : Fin s) (hb : b.val < t), M.value (.enable b) →
        ∀ l ∈ L[b.val]'(by omega), M.value (.lit b l) := by
  classical
  intro t
  induction t with
  | zero =>
    intro _
    exact ⟨[],rfl,(by intro k hk; simp at hk),(by intro b hb; omega)⟩
  | succ t ih =>
    intro hts
    obtain ⟨L,hlen,hgood,hsub⟩ := ih (by omega)
    let b : Fin s := ⟨t,by omega⟩
    have choose : ∃ C, Legal F L C ∧
        (M.value (.enable b) → ∀ l ∈ C, M.value (.lit b l)) := by
      by_cases he : M.value (.enable b)
      · by_cases hd : M.value (.derived b)
        · obtain ⟨x,hx⟩ := M.must_resolve b he hd
          obtain ⟨a,hab,ha⟩ := M.must_left b he hd
          obtain ⟨c,hcb,hc⟩ := M.must_right b he hd
          have hat : a.val < t := hab
          have hct : c.val < t := hcb
          obtain ⟨C,hC,hP⟩ := normalize hgood a.val c.val (by omega) (by omega)
            x (fun l => M.value (.lit b l))
            (fun l hl hne => M.left_copy b a x l hab hne he hx ha
              (hsub a hat (M.enable_left b a hab he ha) l hl))
            (fun l hl hne => M.right_copy b c x l hcb hne he hx hc
              (hsub c hct (M.enable_right b c hcb he hc) l hl))
          exact ⟨C,hC,fun _ => hP⟩
        · obtain ⟨j,hj⟩ := M.must_weaken b he hd
          exact ⟨F[j],Or.inl (List.getElem_mem j.isLt),
            fun _ l hl => M.weak_copy b j l hl he hj⟩
      · have hex : ∃ C, C ∈ F := by
          have hne := input_nonempty M
          cases F with
          | nil => exact False.elim (hne rfl)
          | cons C Cs => exact ⟨C,by simp⟩
        obtain ⟨C,hC⟩ := hex
        exact ⟨C,Or.inl hC,fun h => False.elim (he h)⟩
    obtain ⟨C,hC,hsubC⟩ := choose
    refine ⟨L ++ [C],by simp [hlen],good_append hgood hC,?_⟩
    intro a hat hea l hl
    by_cases halt : a.val < t
    · apply hsub a halt hea l
      simpa [List.getElem_append_left (show a.val < L.length by omega)] using hl
    · have eat : a.val = t := by omega
      have eab : a = b := Fin.ext eat
      subst a
      apply hsubC hea l
      simpa [b,← hlen] using hl

/-- A satisfying unary-relativized assignment yields a library resolution
refutation with exactly s lines (and therefore with at most s lines). -/
theorem extract {n s : Nat} {F : CNF (Fin n)} (M : Model F s) :
    ∃ R : Refutation F, R.steps.length = s := by
  classical
  obtain ⟨L,hlen,hgood,hsub⟩ := normalized_prefix M s (Nat.le_refl s)
  have hr : M.root.val < L.length := by omega
  have hempty : L[M.root.val] = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro l hl
    exact M.root_empty l (hsub M.root M.root.isLt M.root_enabled l hl)
  exact ⟨⟨L,hgood,hempty ▸ List.getElem_mem hr⟩,hlen⟩

/-- Sanity theorem for all input sizes and all block bounds, using the canonical
library Refutation type. -/
theorem unsat_of_no_short_refutation {n s : Nat} (F : CNF (Fin n))
    (h : ¬ ∃ R : Refutation F, R.steps.length ≤ s) : ¬ Nonempty (Model F s) := by
  rintro ⟨M⟩
  obtain ⟨R,hR⟩ := extract M
  exact h ⟨R,Nat.le_of_eq hR⟩

#print axioms extract
#print axioms unsat_of_no_short_refutation
end Programme.«20261031-2024-proof-complexity».RefUnary
