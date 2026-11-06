import Programme.«20261101-0614-proof-complexity».Singleton

namespace Programme.«20261101-0614-proof-complexity».SingletonTwo
open Programme.«20261031-2024-proof-complexity».NativeIter
open Programme.«20261101-0614-proof-complexity»

def witness (v : Var) : Bool := if v.1 = 0 then v.2 == 0 else v.2 % 2 == 1

theorem block_filtered (y : Nat) (c : Clause) (hc : c ∈ UnaryIter.cnf 2)
    (hlen : (Singleton.image 2 y c).length ≤ 2) :
    conjunction (falsity (Singleton.image 2 y c)) witness = 0 := by
  simp [UnaryIter.cnf, UnaryIter.raw, UnaryIter.row, List.range_succ] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [Singleton.image, Singleton.structural, UnaryIter.row,
    UnaryIter.minus, List.range_succ, renameClause, renameLit, Singleton.block,
    conjunction, falsity, holds, neg, witness, Singleton.outer] at hlen ⊢
  simp [List.eraseDups_cons, List.filter_nil] at hlen

theorem lower (N d : Nat) (hN : 2 ≤ N) (hd : d < 3) : ¬ Refutes (Singleton.cnf N 2) d := by
  apply no_refutation_of_filtered_assignment (a := witness)
  intro c hc hlen
  rw [Singleton.generator_spec] at hc
  rcases hc with (rfl | ⟨y,hy,z,hz,rfl⟩) | ⟨y,hy,t,ht,rfl⟩
  · cases N with
    | zero => omega
    | succ N =>
      simp [List.range_succ_eq_map, Singleton.outer, falsity, conjunction, holds,
        neg, witness]
  · obtain ⟨hz,hyz⟩ := hz
    have hz0 : z ≠ 0 := by omega
    simp [falsity, conjunction, Singleton.outer, neg, holds, witness, hz0]
  · exact block_filtered y t ht (by omega)

theorem exact_degree (N : Nat) (hN : 2 ≤ N) :
    Refutes (Singleton.cnf N 2) 3 ∧ ∀ d < 3, ¬ Refutes (Singleton.cnf N 2) d :=
  ⟨Singleton.upper N 2 hN (by decide), fun d hd => lower N d hN hd⟩

#print axioms exact_degree
end Programme.«20261101-0614-proof-complexity».SingletonTwo
