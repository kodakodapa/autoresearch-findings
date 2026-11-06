import Programme.«20261101-1618-proof-complexity».ClauseLinear

namespace Programme.«20261101-1618-proof-complexity».UnaryIterLinear
open Programme.«20261031-2024-proof-complexity».NativeIter
open Programme.«20261101-1618-proof-complexity».ClauseLinear

/-- Unary one-hot Iter, with variables (row, output). -/
def cnf (L : Nat) : List Clause :=
  let rows := (List.range L).flatMap fun x =>
    [((List.range L).map fun z => ((x,z),true))] ++
    (List.range L).flatMap fun z =>
      (((List.range L).filter fun w => z < w).map fun w =>
        [((x,z),false),((x,w),false)])
  let down := (List.range L).flatMap fun x =>
    (List.range x).map fun z => [((x,z),false)]
  let up := (List.range L).flatMap fun x =>
    (((List.range L).filter fun z => x < z).map fun z =>
      [((x,z),false),((z,z),false)])
  rows ++ [[((0,0),false)]] ++ down ++ up

/-- The length-one boundary already has a degree-one certificate. -/
theorem refutes_one : Programme.«20261101-1618-proof-complexity».ClauseLinear.Refutes (cnf 1) 1 := by
  have hp : Programme.«20261101-1618-proof-complexity».ClauseLinear.Cone (cnf 1) 1
      (fun a => conjunction [] a * slack [((0,0),true)] a) :=
    .clause _ [] (by decide) (by simp [Multiplier]) (by decide)
  have hn : Programme.«20261101-1618-proof-complexity».ClauseLinear.Cone (cnf 1) 1
      (fun a => conjunction [] a * slack [((0,0),false)] a) :=
    .clause _ [] (by decide) (by simp [Multiplier]) (by decide)
  have h := Programme.«20261101-1618-proof-complexity».ClauseLinear.Cone.add hp hn
  have he : (fun a : Assignment =>
      conjunction [] a * slack [((0,0),true)] a +
      conjunction [] a * slack [((0,0),false)] a) = (fun _ => (-1 : Rat)) := by
    funext a
    cases ha : a (0,0) <;>
      simp [conjunction, slack, literal, holds, ha, Rat.add_zero, Rat.zero_add, Rat.sub_self, Rat.sub_eq_add_neg, Rat.add_neg_cancel]
  rw [he] at h
  exact h

theorem exact_one : Programme.«20261101-1618-proof-complexity».ClauseLinear.Refutes (cnf 1) 1 ∧
    ∀ d < 1, ¬ Programme.«20261101-1618-proof-complexity».ClauseLinear.Refutes (cnf 1) d := by
  refine ⟨refutes_one, ?_⟩
  intro d hd
  have : d = 0 := by omega
  subst d
  exact no_degree_zero _

#print axioms exact_one
end Programme.«20261101-1618-proof-complexity».UnaryIterLinear
