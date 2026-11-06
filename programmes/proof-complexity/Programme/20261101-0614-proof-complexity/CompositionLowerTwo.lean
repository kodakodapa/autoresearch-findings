import Programme.«20261101-0614-proof-complexity».FamilyRestriction

namespace Programme.«20261101-0614-proof-complexity».CompositionLowerTwo
open Programme.«20261031-2024-proof-complexity».NativeIter
open Programme.«20261101-0614-proof-complexity».Composition

noncomputable def witness (v : Var) : Bool :=
  if v.1 = 0 then (decode v.2).2 == 0
  else if v.1 = 1 then (decode (decode v.2).2).2 == 1
  else true

@[simp] theorem witness_f (a y : Nat) : witness (fVar a y) = (y == 0) := by
  simp [witness, fVar, decode_pair]
@[simp] theorem witness_s (y x z : Nat) : witness (sVar y x z) = (z == 1) := by
  simp [witness, sVar, decode_pair]

theorem singleton_lower (N d : Nat) (hN : 2 ≤ N) (hd : d < 3) :
    ¬ Refutes (cnf 1 N 2) d := by
  apply no_refutation_of_filtered_assignment (a := witness)
  intro c hc hlen
  simp only [Programme.«20261101-0614-proof-complexity».Composition.cnf, List.mem_eraseDups, List.mem_append, List.mem_flatMap,
    List.mem_range, List.mem_map] at hc
  rcases hc with ((⟨a,ha,hc⟩ | ⟨y,hy,x,hx,hc⟩) | ⟨y,hy,x,hx,hc⟩) |
    ⟨y,hy,e,he,a,ha,rfl⟩
  · have ha0 : a = 0 := by omega
    subst a
    have hn : N ≠ 1 := by omega
    simp only [onehot, ite_eq_right hn, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, List.mem_flatMap, List.mem_map,
      List.mem_filter, List.mem_range] at hc
    rcases hc with rfl | ⟨i,hi,j,⟨hj,hij⟩,rfl⟩
    · cases N with
      | zero => omega
      | succ n => simp [List.range_succ_eq_map, falsity, conjunction, neg, holds, pos]
    · have hj0 : j ≠ 0 := by
        have hij' : i < j := of_decide_eq_true hij
        omega
      simp [falsity, conjunction, neg, holds, minus, hj0]
  · simp [onehot, List.range_succ] at hc
    rcases hc with rfl | rfl
    all_goals simp [falsity, conjunction, neg, holds, pos, minus]
  · simp [onehot] at hc
  · have ha0 : a = 0 := by omega
    subst a
    simp [events, List.range_succ] at he
    rcases he with rfl | rfl | rfl
    all_goals simp [eventClause, pos, minus] at hlen ⊢
    all_goals simp [falsity, conjunction, neg, holds,] at hlen ⊢
    all_goals omega

/-- The exact conjecture in P164. -/
theorem lower (M N d : Nat) (hM : 1 ≤ M) (hMN : M < N) (hd : d < 3) :
    ¬ Refutes (cnf M N 2) d := by
  induction M generalizing N with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero => exact singleton_lower N d (by omega) hd
    | succ m =>
      cases N with
      | zero => omega
      | succ n =>
        intro hr
        exact ih n (by omega) (by omega)
          (refutes_restrict (m+1) n 2 d (by omega) (by omega) (by omega) hr)

#print axioms singleton_lower
#print axioms lower
end Programme.«20261101-0614-proof-complexity».CompositionLowerTwo
