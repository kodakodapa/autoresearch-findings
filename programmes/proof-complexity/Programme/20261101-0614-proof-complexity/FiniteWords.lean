import Programme.«20261101-0614-proof-complexity».SignedDual

namespace Programme.«20261101-0614-proof-complexity».FiniteWords
open Programme.«20261031-2024-proof-complexity».NativeIter

def words (alphabet : List α) : Nat → List (List α)
  | 0 => [[]]
  | n+1 => [[]] ++ alphabet.flatMap (fun a => (words alphabet n).map (a :: ·))

theorem mem_words {alphabet : List α} {m : List α} {d : Nat}
    (hm : ∀ a ∈ m, a ∈ alphabet) (hd : m.length ≤ d) : m ∈ words alphabet d := by
  induction d generalizing m with
  | zero =>
    have : m = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst m
    simp [words]
  | succ d ih =>
    cases m with
    | nil => simp [words]
    | cons a m =>
      apply List.mem_append.mpr
      right
      apply List.mem_flatMap.mpr
      refine ⟨a, hm a (by simp), List.mem_map.mpr ⟨m, ?_, rfl⟩⟩
      apply ih
      · intro b hb
        exact hm b (by simp [hb])
      · simp only [List.length_cons] at hd
        omega

def alphabet (vars : List Var) : List Lit :=
  vars.flatMap fun v => [(v,false),(v,true)]

theorem mem_alphabet {vars : List Var} {l : Lit} (hl : l.1 ∈ vars) :
    l ∈ alphabet vars := by
  apply List.mem_flatMap.mpr
  refine ⟨l.1, hl, ?_⟩
  rcases l with ⟨v,b⟩
  cases b <;> simp

theorem supported_mem_words {vars : List Var} {m : List Lit} {d : Nat}
    (hm : ∀ l ∈ m, l.1 ∈ vars) (hd : m.length ≤ d) :
    m ∈ words (alphabet vars) d :=
  mem_words (fun l hl => mem_alphabet (hm l hl)) hd

#print axioms supported_mem_words
end Programme.«20261101-0614-proof-complexity».FiniteWords
