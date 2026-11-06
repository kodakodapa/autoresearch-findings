import Programme.«20261101-1618-proof-complexity».UnaryIterLinear
import Programme.«20261031-2024-proof-complexity».IterCone

namespace Programme.«20261101-1618-proof-complexity».UnaryIterLinear
open Programme.«20261031-2024-proof-complexity».NativeIter
open Programme.«20261101-1618-proof-complexity».ClauseLinear

private theorem cone_sum {F d} (l : List Nat) (f : Nat → Assignment → Rat)
    (h : ∀ v ∈ l, Programme.«20261101-1618-proof-complexity».ClauseLinear.Cone F d (f v)) :
    Programme.«20261101-1618-proof-complexity».ClauseLinear.Cone F d (fun a => (l.map (fun v => f v a)).sum) := by
  induction l with
  | nil => exact .zero
  | cons v l ih => exact .add (h v (by simp)) (ih (by intro w hw; exact h w (by simp [hw])))

private theorem clause_one {F : List Clause} {c : Clause} (h : c ∈ F) :
    Programme.«20261101-1618-proof-complexity».ClauseLinear.Cone F 1 (slack c) := by
  have hh : Programme.«20261101-1618-proof-complexity».ClauseLinear.Cone F 1 (fun a => conjunction [] a * slack c a) :=
    .clause c [] h (by simp [Multiplier]) (by decide)
  simpa [conjunction, Rat.one_mul] using hh

private theorem row_mem {L x : Nat} (hx : x < L) :
    ((List.range L).map fun z => ((x,z),true)) ∈ cnf L := by
  simp only [cnf, List.mem_append]
  left; left; left
  apply List.mem_flatMap.mpr
  exact ⟨x, List.mem_range.mpr hx, by simp⟩

private theorem down_mem {L x z : Nat} (hx : x < L) (hz : z < x) :
    [((x,z),false)] ∈ cnf L := by
  simp only [cnf, List.mem_append]
  left; right
  exact List.mem_flatMap.mpr ⟨x, List.mem_range.mpr hx,
    List.mem_map.mpr ⟨z, List.mem_range.mpr hz, rfl⟩⟩

private theorem up_mem {L x z : Nat} (hx : x < L) (hz : z < L) (h : x < z) :
    [((x,z),false),((z,z),false)] ∈ cnf L := by
  simp only [cnf, List.mem_append]
  right
  exact List.mem_flatMap.mpr ⟨x, List.mem_range.mpr hx,
    List.mem_map.mpr ⟨z, List.mem_filter.mpr ⟨List.mem_range.mpr hz, by simpa using h⟩, rfl⟩⟩

private theorem diagonal (L x : Nat) (hx : x < L)
    (ih : ∀ z, x < z → z < L → Programme.«20261101-1618-proof-complexity».ClauseLinear.Cone (cnf L) 1
      (fun a => literal ((z,z),true) a - 1)) :
    Programme.«20261101-1618-proof-complexity».ClauseLinear.Cone (cnf L) 1 (fun a => literal ((x,x),true) a - 1) := by
  have hn : ∀ z < L, z ≠ x → Programme.«20261101-1618-proof-complexity».ClauseLinear.Cone (cnf L) 1
      (fun a => -literal ((x,z),true) a) := by
    intro z hz hne
    by_cases hzx : z < x
    · have h := clause_one (down_mem hx hzx)
      have he : slack [((x,z),false)] = (fun a => -literal ((x,z),true) a) := by
        funext a
        cases ha : a (x,z) <;> simp [slack, literal, holds, ha, Rat.add_zero, Rat.zero_add, Rat.sub_self, Rat.sub_eq_add_neg, Rat.add_neg_cancel]
      rwa [he] at h
    · have hxz : x < z := by omega
      have h := Programme.«20261101-1618-proof-complexity».ClauseLinear.Cone.add (clause_one (up_mem hx hz hxz)) (ih z hxz hz)
      have he : (fun a => slack [((x,z),false),((z,z),false)] a +
          (literal ((z,z),true) a - 1)) = (fun a => -literal ((x,z),true) a) := by
        funext a
        cases ha : a (x,z) <;> cases hb : a (z,z) <;>
          simp [slack, literal, holds, ha, hb, Rat.add_zero, Rat.zero_add, Rat.sub_self, Rat.sub_eq_add_neg, Rat.add_neg_cancel, Rat.add_assoc]
      rwa [he] at h
  have hs := cone_sum ((List.range L).filter (· != x))
    (fun z a => -literal ((x,z),true) a) (by
      intro z hz
      obtain ⟨hz, hne⟩ := List.mem_filter.mp hz
      exact hn z (List.mem_range.mp hz) (by simpa using hne))
  have h := Programme.«20261101-1618-proof-complexity».ClauseLinear.Cone.add (clause_one (row_mem hx)) hs
  have he : (fun a => slack ((List.range L).map fun z => ((x,z),true)) a +
      (((List.range L).filter (· != x)).map fun z => -literal ((x,z),true) a).sum) =
      (fun a => literal ((x,x),true) a - 1) := by
    funext a
    simp only [slack, List.map_map, Function.comp_def, sum_neg]
    have hp := sum_filter_one (List.range L) (fun z => literal ((x,z),true) a)
      x List.nodup_range (List.mem_range.mpr hx)
    rw [← hp]
    simp only [Rat.sub_eq_add_neg]
    generalize (((List.range L).filter (· != x)).map
      (fun z => literal ((x,z),true) a)).sum = s
    generalize literal ((x,x),true) a = t
    rw [Rat.add_assoc s t (-1), Rat.add_comm s (t + -1),
      Rat.add_assoc, Rat.add_neg_cancel, Rat.add_zero]
  rwa [he] at h

 theorem refutes_pos (L : Nat) (hL : 0 < L) : Programme.«20261101-1618-proof-complexity».ClauseLinear.Refutes (cnf L) 1 := by
  have hd : ∀ x, x < L → Programme.«20261101-1618-proof-complexity».ClauseLinear.Cone (cnf L) 1
      (fun a => literal ((x,x),true) a - 1) := by
    intro x hx
    have hall : ∀ k x, L - x = k → x < L → Programme.«20261101-1618-proof-complexity».ClauseLinear.Cone (cnf L) 1
        (fun a => literal ((x,x),true) a - 1) := by
      intro k
      induction k using Nat.strongRecOn with
      | ind k ih =>
        intro x he hx
        apply diagonal L x hx
        intro z hxz hz
        exact ih (L-z) (by omega) z rfl hz
    exact hall (L-x) x rfl hx
  have hr : [((0,0),false)] ∈ cnf L := by simp [cnf]
  have h := Programme.«20261101-1618-proof-complexity».ClauseLinear.Cone.add (hd 0 hL) (clause_one hr)
  have he : (fun a => (literal ((0,0),true) a - 1) + slack [((0,0),false)] a) =
      (fun _ => (-1 : Rat)) := by
    funext a
    cases ha : a (0,0) <;> simp [slack, literal, holds, ha, Rat.add_zero, Rat.zero_add, Rat.sub_self, Rat.sub_eq_add_neg, Rat.add_neg_cancel]
  rwa [he] at h

/-- Exact formal clause-linear degree for the unary Iter CNF above. -/
theorem exact_pos (L : Nat) (hL : 0 < L) :
    Programme.«20261101-1618-proof-complexity».ClauseLinear.Refutes (cnf L) 1 ∧
      ∀ d < 1, ¬ Programme.«20261101-1618-proof-complexity».ClauseLinear.Refutes (cnf L) d := by
  refine ⟨refutes_pos L hL, ?_⟩
  intro d hd
  have he : d = 0 := by omega
  subst d
  exact Programme.«20261101-1618-proof-complexity».ClauseLinear.no_degree_zero _

#print axioms exact_pos
#print axioms refutes_pos
end Programme.«20261101-1618-proof-complexity».UnaryIterLinear
