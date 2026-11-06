import Programme.«20261101-0614-proof-complexity».SingletonSupport
namespace Programme.«20261101-0614-proof-complexity».SingletonEquations
open Programme.«20261031-2024-proof-complexity».NativeIter
open Programme.«20261101-0614-proof-complexity».SingletonData Programme.«20261101-0614-proof-complexity».SignedDual
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def clauses : List Clause := [
  [((0,0),true), ((0,1),true)],
  [((0,0),false), ((0,1),false)],
  [((1,0),true), ((1,1),true), ((1,2),true)],
  [((1,0),false), ((1,1),false)],
  [((1,0),false), ((1,2),false)],
  [((1,1),false), ((1,2),false)],
  [((1,3),true), ((1,4),true), ((1,5),true)],
  [((1,3),false), ((1,4),false)],
  [((1,3),false), ((1,5),false)],
  [((1,4),false), ((1,5),false)],
  [((1,6),true), ((1,7),true), ((1,8),true)],
  [((1,6),false), ((1,7),false)],
  [((1,6),false), ((1,8),false)],
  [((1,7),false), ((1,8),false)],
  [((1,0),false), ((0,0),true)],
  [((1,3),false), ((0,0),true)],
  [((1,6),false), ((0,0),true)],
  [((1,7),false), ((0,0),true)],
  [((1,1),false), ((1,4),false), ((0,0),true)],
  [((1,2),false), ((1,8),false), ((0,0),true)],
  [((1,5),false), ((1,8),false), ((0,0),true)],
  [((2,0),true), ((2,1),true), ((2,2),true)],
  [((2,0),false), ((2,1),false)],
  [((2,0),false), ((2,2),false)],
  [((2,1),false), ((2,2),false)],
  [((2,3),true), ((2,4),true), ((2,5),true)],
  [((2,3),false), ((2,4),false)],
  [((2,3),false), ((2,5),false)],
  [((2,4),false), ((2,5),false)],
  [((2,6),true), ((2,7),true), ((2,8),true)],
  [((2,6),false), ((2,7),false)],
  [((2,6),false), ((2,8),false)],
  [((2,7),false), ((2,8),false)],
  [((2,0),false), ((0,1),true)],
  [((2,3),false), ((0,1),true)],
  [((2,6),false), ((0,1),true)],
  [((2,7),false), ((0,1),true)],
  [((2,1),false), ((2,4),false), ((0,1),true)],
  [((2,2),false), ((2,8),false), ((0,1),true)],
  [((2,5),false), ((2,8),false), ((0,1),true)]]

theorem cnf_eq : Singleton.cnf 2 3 = clauses := by decide +kernel
theorem test00 : (FiniteWords.words (FiniteWords.alphabet vars) 1).all
    (fun m => decide (score weights (m ++ falsity [((0,0),true), ((0,1),true)]) = 0)) = true := by decide +kernel
theorem test01 : (FiniteWords.words (FiniteWords.alphabet vars) 1).all
    (fun m => decide (score weights (m ++ falsity [((0,0),false), ((0,1),false)]) = 0)) = true := by decide +kernel
theorem test02 : (FiniteWords.words (FiniteWords.alphabet vars) 0).all
    (fun m => decide (score weights (m ++ falsity [((1,0),true), ((1,1),true), ((1,2),true)]) = 0)) = true := by decide +kernel
theorem test03 : (FiniteWords.words (FiniteWords.alphabet vars) 1).all
    (fun m => decide (score weights (m ++ falsity [((1,0),false), ((1,1),false)]) = 0)) = true := by decide +kernel
theorem test04 : (FiniteWords.words (FiniteWords.alphabet vars) 1).all
    (fun m => decide (score weights (m ++ falsity [((1,0),false), ((1,2),false)]) = 0)) = true := by decide +kernel
theorem test05 : (FiniteWords.words (FiniteWords.alphabet vars) 1).all
    (fun m => decide (score weights (m ++ falsity [((1,1),false), ((1,2),false)]) = 0)) = true := by decide +kernel
theorem test06 : (FiniteWords.words (FiniteWords.alphabet vars) 0).all
    (fun m => decide (score weights (m ++ falsity [((1,3),true), ((1,4),true), ((1,5),true)]) = 0)) = true := by decide +kernel
theorem test07 : (FiniteWords.words (FiniteWords.alphabet vars) 1).all
    (fun m => decide (score weights (m ++ falsity [((1,3),false), ((1,4),false)]) = 0)) = true := by decide +kernel
theorem test08 : (FiniteWords.words (FiniteWords.alphabet vars) 1).all
    (fun m => decide (score weights (m ++ falsity [((1,3),false), ((1,5),false)]) = 0)) = true := by decide +kernel
theorem test09 : (FiniteWords.words (FiniteWords.alphabet vars) 1).all
    (fun m => decide (score weights (m ++ falsity [((1,4),false), ((1,5),false)]) = 0)) = true := by decide +kernel
theorem test10 : (FiniteWords.words (FiniteWords.alphabet vars) 0).all
    (fun m => decide (score weights (m ++ falsity [((1,6),true), ((1,7),true), ((1,8),true)]) = 0)) = true := by decide +kernel
theorem test11 : (FiniteWords.words (FiniteWords.alphabet vars) 1).all
    (fun m => decide (score weights (m ++ falsity [((1,6),false), ((1,7),false)]) = 0)) = true := by decide +kernel
theorem test12 : (FiniteWords.words (FiniteWords.alphabet vars) 1).all
    (fun m => decide (score weights (m ++ falsity [((1,6),false), ((1,8),false)]) = 0)) = true := by decide +kernel
theorem test13 : (FiniteWords.words (FiniteWords.alphabet vars) 1).all
    (fun m => decide (score weights (m ++ falsity [((1,7),false), ((1,8),false)]) = 0)) = true := by decide +kernel
theorem test14 : (FiniteWords.words (FiniteWords.alphabet vars) 1).all
    (fun m => decide (score weights (m ++ falsity [((1,0),false), ((0,0),true)]) = 0)) = true := by decide +kernel
theorem test15 : (FiniteWords.words (FiniteWords.alphabet vars) 1).all
    (fun m => decide (score weights (m ++ falsity [((1,3),false), ((0,0),true)]) = 0)) = true := by decide +kernel
theorem test16 : (FiniteWords.words (FiniteWords.alphabet vars) 1).all
    (fun m => decide (score weights (m ++ falsity [((1,6),false), ((0,0),true)]) = 0)) = true := by decide +kernel
theorem test17 : (FiniteWords.words (FiniteWords.alphabet vars) 1).all
    (fun m => decide (score weights (m ++ falsity [((1,7),false), ((0,0),true)]) = 0)) = true := by decide +kernel
theorem test18 : (FiniteWords.words (FiniteWords.alphabet vars) 0).all
    (fun m => decide (score weights (m ++ falsity [((1,1),false), ((1,4),false), ((0,0),true)]) = 0)) = true := by decide +kernel
theorem test19 : (FiniteWords.words (FiniteWords.alphabet vars) 0).all
    (fun m => decide (score weights (m ++ falsity [((1,2),false), ((1,8),false), ((0,0),true)]) = 0)) = true := by decide +kernel
theorem test20 : (FiniteWords.words (FiniteWords.alphabet vars) 0).all
    (fun m => decide (score weights (m ++ falsity [((1,5),false), ((1,8),false), ((0,0),true)]) = 0)) = true := by decide +kernel
theorem test21 : (FiniteWords.words (FiniteWords.alphabet vars) 0).all
    (fun m => decide (score weights (m ++ falsity [((2,0),true), ((2,1),true), ((2,2),true)]) = 0)) = true := by decide +kernel
theorem test22 : (FiniteWords.words (FiniteWords.alphabet vars) 1).all
    (fun m => decide (score weights (m ++ falsity [((2,0),false), ((2,1),false)]) = 0)) = true := by decide +kernel
theorem test23 : (FiniteWords.words (FiniteWords.alphabet vars) 1).all
    (fun m => decide (score weights (m ++ falsity [((2,0),false), ((2,2),false)]) = 0)) = true := by decide +kernel
theorem test24 : (FiniteWords.words (FiniteWords.alphabet vars) 1).all
    (fun m => decide (score weights (m ++ falsity [((2,1),false), ((2,2),false)]) = 0)) = true := by decide +kernel
theorem test25 : (FiniteWords.words (FiniteWords.alphabet vars) 0).all
    (fun m => decide (score weights (m ++ falsity [((2,3),true), ((2,4),true), ((2,5),true)]) = 0)) = true := by decide +kernel
theorem test26 : (FiniteWords.words (FiniteWords.alphabet vars) 1).all
    (fun m => decide (score weights (m ++ falsity [((2,3),false), ((2,4),false)]) = 0)) = true := by decide +kernel
theorem test27 : (FiniteWords.words (FiniteWords.alphabet vars) 1).all
    (fun m => decide (score weights (m ++ falsity [((2,3),false), ((2,5),false)]) = 0)) = true := by decide +kernel
theorem test28 : (FiniteWords.words (FiniteWords.alphabet vars) 1).all
    (fun m => decide (score weights (m ++ falsity [((2,4),false), ((2,5),false)]) = 0)) = true := by decide +kernel
theorem test29 : (FiniteWords.words (FiniteWords.alphabet vars) 0).all
    (fun m => decide (score weights (m ++ falsity [((2,6),true), ((2,7),true), ((2,8),true)]) = 0)) = true := by decide +kernel
theorem test30 : (FiniteWords.words (FiniteWords.alphabet vars) 1).all
    (fun m => decide (score weights (m ++ falsity [((2,6),false), ((2,7),false)]) = 0)) = true := by decide +kernel
theorem test31 : (FiniteWords.words (FiniteWords.alphabet vars) 1).all
    (fun m => decide (score weights (m ++ falsity [((2,6),false), ((2,8),false)]) = 0)) = true := by decide +kernel
theorem test32 : (FiniteWords.words (FiniteWords.alphabet vars) 1).all
    (fun m => decide (score weights (m ++ falsity [((2,7),false), ((2,8),false)]) = 0)) = true := by decide +kernel
theorem test33 : (FiniteWords.words (FiniteWords.alphabet vars) 1).all
    (fun m => decide (score weights (m ++ falsity [((2,0),false), ((0,1),true)]) = 0)) = true := by decide +kernel
theorem test34 : (FiniteWords.words (FiniteWords.alphabet vars) 1).all
    (fun m => decide (score weights (m ++ falsity [((2,3),false), ((0,1),true)]) = 0)) = true := by decide +kernel
theorem test35 : (FiniteWords.words (FiniteWords.alphabet vars) 1).all
    (fun m => decide (score weights (m ++ falsity [((2,6),false), ((0,1),true)]) = 0)) = true := by decide +kernel
theorem test36 : (FiniteWords.words (FiniteWords.alphabet vars) 1).all
    (fun m => decide (score weights (m ++ falsity [((2,7),false), ((0,1),true)]) = 0)) = true := by decide +kernel
theorem test37 : (FiniteWords.words (FiniteWords.alphabet vars) 0).all
    (fun m => decide (score weights (m ++ falsity [((2,1),false), ((2,4),false), ((0,1),true)]) = 0)) = true := by decide +kernel
theorem test38 : (FiniteWords.words (FiniteWords.alphabet vars) 0).all
    (fun m => decide (score weights (m ++ falsity [((2,2),false), ((2,8),false), ((0,1),true)]) = 0)) = true := by decide +kernel
theorem test39 : (FiniteWords.words (FiniteWords.alphabet vars) 0).all
    (fun m => decide (score weights (m ++ falsity [((2,5),false), ((2,8),false), ((0,1),true)]) = 0)) = true := by decide +kernel
theorem equations : ∀ c ∈ Singleton.cnf 2 3,
    ∀ m ∈ FiniteWords.words (FiniteWords.alphabet vars) (3-c.length),
      score weights (m ++ falsity c) = 0 := by
  intro c hc m hm
  rw [cnf_eq] at hc
  simp only [clauses, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst c; exact of_decide_eq_true (List.all_eq_true.mp test00 m hm)
  · subst c; exact of_decide_eq_true (List.all_eq_true.mp test01 m hm)
  · subst c; exact of_decide_eq_true (List.all_eq_true.mp test02 m hm)
  · subst c; exact of_decide_eq_true (List.all_eq_true.mp test03 m hm)
  · subst c; exact of_decide_eq_true (List.all_eq_true.mp test04 m hm)
  · subst c; exact of_decide_eq_true (List.all_eq_true.mp test05 m hm)
  · subst c; exact of_decide_eq_true (List.all_eq_true.mp test06 m hm)
  · subst c; exact of_decide_eq_true (List.all_eq_true.mp test07 m hm)
  · subst c; exact of_decide_eq_true (List.all_eq_true.mp test08 m hm)
  · subst c; exact of_decide_eq_true (List.all_eq_true.mp test09 m hm)
  · subst c; exact of_decide_eq_true (List.all_eq_true.mp test10 m hm)
  · subst c; exact of_decide_eq_true (List.all_eq_true.mp test11 m hm)
  · subst c; exact of_decide_eq_true (List.all_eq_true.mp test12 m hm)
  · subst c; exact of_decide_eq_true (List.all_eq_true.mp test13 m hm)
  · subst c; exact of_decide_eq_true (List.all_eq_true.mp test14 m hm)
  · subst c; exact of_decide_eq_true (List.all_eq_true.mp test15 m hm)
  · subst c; exact of_decide_eq_true (List.all_eq_true.mp test16 m hm)
  · subst c; exact of_decide_eq_true (List.all_eq_true.mp test17 m hm)
  · subst c; exact of_decide_eq_true (List.all_eq_true.mp test18 m hm)
  · subst c; exact of_decide_eq_true (List.all_eq_true.mp test19 m hm)
  · subst c; exact of_decide_eq_true (List.all_eq_true.mp test20 m hm)
  · subst c; exact of_decide_eq_true (List.all_eq_true.mp test21 m hm)
  · subst c; exact of_decide_eq_true (List.all_eq_true.mp test22 m hm)
  · subst c; exact of_decide_eq_true (List.all_eq_true.mp test23 m hm)
  · subst c; exact of_decide_eq_true (List.all_eq_true.mp test24 m hm)
  · subst c; exact of_decide_eq_true (List.all_eq_true.mp test25 m hm)
  · subst c; exact of_decide_eq_true (List.all_eq_true.mp test26 m hm)
  · subst c; exact of_decide_eq_true (List.all_eq_true.mp test27 m hm)
  · subst c; exact of_decide_eq_true (List.all_eq_true.mp test28 m hm)
  · subst c; exact of_decide_eq_true (List.all_eq_true.mp test29 m hm)
  · subst c; exact of_decide_eq_true (List.all_eq_true.mp test30 m hm)
  · subst c; exact of_decide_eq_true (List.all_eq_true.mp test31 m hm)
  · subst c; exact of_decide_eq_true (List.all_eq_true.mp test32 m hm)
  · subst c; exact of_decide_eq_true (List.all_eq_true.mp test33 m hm)
  · subst c; exact of_decide_eq_true (List.all_eq_true.mp test34 m hm)
  · subst c; exact of_decide_eq_true (List.all_eq_true.mp test35 m hm)
  · subst c; exact of_decide_eq_true (List.all_eq_true.mp test36 m hm)
  · subst c; exact of_decide_eq_true (List.all_eq_true.mp test37 m hm)
  · subst c; exact of_decide_eq_true (List.all_eq_true.mp test38 m hm)
  · subst c; exact of_decide_eq_true (List.all_eq_true.mp test39 m hm)

#print axioms equations
end Programme.«20261101-0614-proof-complexity».SingletonEquations
