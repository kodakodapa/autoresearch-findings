import Programme.«20261101-1618-proof-complexity».UnaryIterUniform

namespace Programme.«20261101-1618-proof-complexity».LossyOne
open Programme.«20261031-2024-proof-complexity».NativeIter
open Programme.«20261101-1618-proof-complexity».ClauseLinear

-- Disjoint variable blocks for the source length-one instance.
def f (a k : Nat) : Var := (0, 2^a * (2*k+1))
def h (y a : Nat) : Var := (1, 2^y * (2*a+1))
def s (y : Nat) : Var := (2,y)
def onehot (row : List Var) : List Clause :=
  [row.map (fun v => (v,true))] ++ row.flatMap fun v =>
    (row.filter (fun w => v != w)).map fun w => [(v,false),(w,false)]
/-- Source unary Lossy(Iter), length one. Duplicate pair clauses are harmless. -/
def cnf (m N : Nat) : List Clause :=
  ((List.range m).flatMap fun a => onehot ((List.range N).map (f a))) ++
  ((List.range N).flatMap fun y => onehot ((List.range m).map (h y))) ++
  ((List.range N).map fun y => [(s y,true)]) ++
  ((List.range N).flatMap fun y => (List.range m).flatMap fun a =>
    (((List.range N).filter (· != y)).map fun k =>
      [(s y,false),(h y a,false),(f a k,false)]))

private theorem clause_one {F : List Clause} {c : Clause} (hc : c ∈ F) :
    Programme.«20261101-1618-proof-complexity».ClauseLinear.Cone F 1 (slack c) := by
  have hh := Programme.«20261101-1618-proof-complexity».ClauseLinear.Cone.clause (d := 1) c [] hc
    (by simp [Multiplier]) (by decide)
  simpa [conjunction, Rat.one_mul] using hh

private theorem cone_sum {F d} (l : List Nat) (g : Nat → Assignment → Rat)
    (hg : ∀ v ∈ l, Programme.«20261101-1618-proof-complexity».ClauseLinear.Cone F d (g v)) :
    Programme.«20261101-1618-proof-complexity».ClauseLinear.Cone F d (fun a => (l.map (fun v => g v a)).sum) := by
  induction l with
  | nil => exact .zero
  | cons v l ih => exact .add (hg v (by simp)) (ih (by intro w hw; exact hg w (by simp [hw])))

private theorem row_mem {N} :
    ((List.range N).map fun k => (f 0 k,true)) ∈ cnf 1 N := by
  simp [cnf, onehot]

private theorem h_mem {N y} (hy : y < N) : [(h y 0,true)] ∈ cnf 1 N := by
  simp only [cnf, List.mem_append]
  left; left; right
  exact List.mem_flatMap.mpr ⟨y, List.mem_range.mpr hy, by simp [onehot]⟩

private theorem s_mem {N y} (hy : y < N) : [(s y,true)] ∈ cnf 1 N := by
  simp only [cnf, List.mem_append]
  left; right
  exact List.mem_map.mpr ⟨y, List.mem_range.mpr hy, rfl⟩

private theorem guard_mem {N y k} (hy : y < N) (hk : k < N) (hne : k ≠ y) :
    [(s y,false),(h y 0,false),(f 0 k,false)] ∈ cnf 1 N := by
  simp only [cnf, List.mem_append]
  right
  apply List.mem_flatMap.mpr
  refine ⟨y, List.mem_range.mpr hy, ?_⟩
  simp only [List.range_one, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  exact List.mem_map.mpr ⟨k, List.mem_filter.mpr
    ⟨List.mem_range.mpr hk, by simpa using hne⟩, rfl⟩

private theorem negative {N y k} (hy : y < N) (hk : k < N) (hne : k ≠ y) :
    Programme.«20261101-1618-proof-complexity».ClauseLinear.Cone (cnf 1 N) 1 (fun a => -literal (f 0 k,true) a) := by
  have hh := Programme.«20261101-1618-proof-complexity».ClauseLinear.Cone.add
    (Programme.«20261101-1618-proof-complexity».ClauseLinear.Cone.add (clause_one (guard_mem hy hk hne))
      (clause_one (h_mem hy))) (clause_one (s_mem hy))
  have he : (fun a => (slack [(s y,false),(h y 0,false),(f 0 k,false)] a +
      slack [(h y 0,true)] a) + slack [(s y,true)] a) =
      (fun a => -literal (f 0 k,true) a) := by
    funext a
    cases hs : a (s y) <;> cases hh : a (h y 0) <;> cases hf : a (f 0 k) <;>
      simp [slack, literal, holds, hs, hh, hf, Rat.add_zero, Rat.zero_add, Rat.sub_self, Rat.sub_eq_add_neg, Rat.add_neg_cancel, Rat.add_assoc, Rat.neg_add_cancel]
  rwa [he] at hh

private theorem force {N y} (hy : y < N) :
    Programme.«20261101-1618-proof-complexity».ClauseLinear.Cone (cnf 1 N) 1 (fun a => literal (f 0 y,true) a - 1) := by
  have hn := cone_sum ((List.range N).filter (· != y))
    (fun k a => -literal (f 0 k,true) a) (by
      intro k hk
      obtain ⟨hk, hne⟩ := List.mem_filter.mp hk
      exact negative hy (List.mem_range.mp hk) (by simpa using hne))
  have hh := Programme.«20261101-1618-proof-complexity».ClauseLinear.Cone.add (clause_one (row_mem (N := N))) hn
  have he : (fun a => slack ((List.range N).map fun k => (f 0 k,true)) a +
      (((List.range N).filter (· != y)).map fun k => -literal (f 0 k,true) a).sum) =
      (fun a => literal (f 0 y,true) a - 1) := by
    funext a
    simp only [slack, List.map_map, Function.comp_def, sum_neg]
    have hp := sum_filter_one (List.range N) (fun k => literal (f 0 k,true) a)
      y List.nodup_range (List.mem_range.mpr hy)
    rw [← hp]
    simp only [Rat.sub_eq_add_neg]
    generalize (((List.range N).filter (· != y)).map
      (fun k => literal (f 0 k,true) a)).sum = t
    generalize literal (f 0 y,true) a = u
    rw [Rat.add_assoc t u (-1), Rat.add_comm t (u + -1),
      Rat.add_assoc, Rat.add_neg_cancel, Rat.add_zero]
  rwa [he] at hh

 theorem refutes (N : Nat) (hN : 1 < N) : Programme.«20261101-1618-proof-complexity».ClauseLinear.Refutes (cnf 1 N) 1 := by
  have hp : [(f 0 0,false),(f 0 1,false)] ∈ cnf 1 N := by
    simp only [cnf, List.mem_append]
    left; left; left
    apply List.mem_flatMap.mpr
    refine ⟨0, by simp, ?_⟩
    simp only [onehot, List.mem_append]
    right
    apply List.mem_flatMap.mpr
    refine ⟨f 0 0, List.mem_map.mpr ⟨0, List.mem_range.mpr (by omega), rfl⟩, ?_⟩
    apply List.mem_map.mpr
    refine ⟨f 0 1, List.mem_filter.mpr ⟨List.mem_map.mpr
      ⟨1, List.mem_range.mpr hN, rfl⟩, by decide⟩, rfl⟩
  have hh := Programme.«20261101-1618-proof-complexity».ClauseLinear.Cone.add
    (Programme.«20261101-1618-proof-complexity».ClauseLinear.Cone.add (force (N := N) (y := 0) (by omega))
      (force (N := N) (y := 1) hN)) (clause_one hp)
  have he : (fun a => (literal (f 0 0,true) a - 1 +
      (literal (f 0 1,true) a - 1)) + slack [(f 0 0,false),(f 0 1,false)] a) =
      (fun _ => (-1 : Rat)) := by
    funext a
    cases ha : a (f 0 0) <;> cases hb : a (f 0 1) <;>
      simp [slack, literal, holds, ha, hb, Rat.add_zero, Rat.zero_add, Rat.sub_self, Rat.sub_eq_add_neg, Rat.add_neg_cancel, Rat.add_assoc, Rat.neg_add_cancel]
  rwa [he] at hh

 theorem exact_degree (N : Nat) (hN : 1 < N) :
    Programme.«20261101-1618-proof-complexity».ClauseLinear.Refutes (cnf 1 N) 1 ∧
      ∀ d < 1, ¬ Programme.«20261101-1618-proof-complexity».ClauseLinear.Refutes (cnf 1 N) d := by
  refine ⟨refutes N hN, ?_⟩
  intro d hd
  have : d = 0 := by omega
  subst d
  exact no_degree_zero _

#print axioms exact_degree
end Programme.«20261101-1618-proof-complexity».LossyOne
