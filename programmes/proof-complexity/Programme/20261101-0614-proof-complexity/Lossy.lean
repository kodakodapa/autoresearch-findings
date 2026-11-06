import Programme.«20261031-2024-proof-complexity».NativeIter

namespace Programme.«20261101-0614-proof-complexity».Lossy
open Programme.«20261031-2024-proof-complexity».NativeIter

def var (tag i u v : Nat) : Var := (tag + 3 * ((i+u)*(i+u+1)/2+u), v)
def row (tag i u size : Nat) : Clause :=
  (List.range size).map fun v => (var tag i u v, true)
def pairs (tag i u size : Nat) : List Clause :=
  (List.range size).flatMap fun v =>
    ((List.range size).filter fun w => v < w).map fun w =>
      [(var tag i u v, false), (var tag i u w, false)]
def block (tag i u size : Nat) : List Clause := row tag i u size :: pairs tag i u size

def raw (N L : Nat) : List Clause :=
  ((List.range N).flatMap fun i =>
    ((List.range L).flatMap fun u => block 0 i u L) ++
    ((List.range L).flatMap fun u => block 1 i u (N/2))) ++
  ((List.range (N/2)).flatMap fun j => block 2 j 0 N) ++
  ((List.range N).flatMap fun i => (List.range (N/2)).flatMap fun j =>
    ((List.range N).filter fun k => k ≠ i).flatMap fun k =>
      [[(var 0 i 0 0,false), (var 1 i 0 j,false), (var 2 j 0 k,false)]] ++
      ((List.range L).flatMap fun u =>
        ((List.range u).map fun v =>
          [(var 0 i u v,false), (var 1 i v j,false), (var 2 j 0 k,false)]) ++
        (((List.range L).filter fun v => u < v).map fun v =>
          [(var 0 i u v,false), (var 0 i v v,false),
           (var 1 i v j,false), (var 2 j 0 k,false)])))
def cnf (N L : Nat) : List Clause := raw N L

/-- Exact clause-set specification, with zero-based pointer values and indices.
Tags 0,1,2 represent s,h,g; this is a variable renaming, not clause reduction. -/
theorem generator_spec (N L : Nat) (c : Clause) : c ∈ cnf N L ↔
    (∃ i < N, (∃ u < L, c ∈ block 0 i u L) ∨
                 (∃ u < L, c ∈ block 1 i u (N/2))) ∨
    (∃ j < N/2, c ∈ block 2 j 0 N) ∨
    (∃ i < N, ∃ j < N/2, ∃ k, (k < N ∧ k ≠ i) ∧
      (c = [(var 0 i 0 0,false), (var 1 i 0 j,false), (var 2 j 0 k,false)] ∨
       ∃ u < L,
        (∃ v < u, [(var 0 i u v,false), (var 1 i v j,false), (var 2 j 0 k,false)] = c) ∨
        (∃ v, (v < L ∧ u < v) ∧ [(var 0 i u v,false), (var 0 i v v,false),
           (var 1 i v j,false), (var 2 j 0 k,false)] = c))) := by
  simp [cnf, raw, List.mem_flatMap, List.mem_map, List.mem_filter, or_assoc]

def assignment (zero : Nat) : Assignment := fun x => x.1 % 3 != zero && x.2 == 0

@[simp] theorem assignment_var (zero tag i u v : Nat) :
    assignment zero (var tag i u v) = (tag % 3 != zero && v == 0) := by
  simp [assignment, var, Nat.add_mod, Nat.mul_mod]

 theorem block_satisfied (zero tag i u size d : Nat) (hs : 0 < size)
    (hz : tag % 3 = zero → d < size) (c : Clause) (hc : c ∈ block tag i u size)
    (hd : c.length ≤ d) : conjunction (falsity c) (assignment zero) = 0 := by
  simp only [block, List.mem_cons] at hc
  rcases hc with rfl | hc
  · have ht : tag % 3 ≠ zero := by
      intro h; have := hz h
      simp only [row, List.length_map, List.length_range] at hd
      omega
    simp [conjunction, falsity, row, List.all_eq_true, neg, holds, ht, hs]
  · simp only [pairs, List.mem_flatMap, List.mem_map, List.mem_filter,
      List.mem_range] at hc
    obtain ⟨v, hv, w, ⟨hw, hvw⟩, rfl⟩ := hc
    simp only [decide_eq_true_eq] at hvw
    have hw0 : w ≠ 0 := by omega
    simp [conjunction, falsity, neg, holds, hw0]

theorem filtered (N L d zero : Nat) (hN : 4 ≤ N) (hL : 1 ≤ L)
    (hz : zero = 0 ∨ zero = 2) (hdeg : d < if zero = 0 then L else N) :
    SatisfiesAt (cnf N L) d (assignment zero) := by
  intro c hc hd
  simp only [cnf, raw, List.mem_append, List.mem_flatMap, List.mem_range] at hc
  rcases hc with (⟨i, hi, hc⟩ | ⟨j, hj, hc⟩) | ⟨i, hi, j, hj, k, hk, hc⟩
  · rcases hc with ⟨u, hu, hc⟩ | ⟨u, hu, hc⟩
    · apply block_satisfied zero 0 i u L d (by omega) _ c hc hd
      rcases hz with rfl | rfl <;> simp_all
    · apply block_satisfied zero 1 i u (N/2) d (by omega) _ c hc hd
      rcases hz with rfl | rfl <;> simp
  · apply block_satisfied zero 2 j 0 N d (by omega) _ c hc hd
    rcases hz with rfl | rfl <;> simp_all
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_flatMap, List.mem_map, List.mem_range, List.mem_filter] at hc
    rcases hc with rfl | ⟨u, hu, hc⟩
    · rcases hz with rfl | rfl <;> simp [conjunction, falsity, neg, holds]
    · rcases hc with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩
      · rcases hz with rfl | rfl <;> simp [conjunction, falsity, neg, holds]
      · rcases hz with rfl | rfl <;> simp [conjunction, falsity, neg, holds]

theorem lower (N L d : Nat) (hN : 4 ≤ N) (hL : 1 ≤ L)
    (hd : d < max N L) : ¬ Refutes (cnf N L) d := by
  by_cases h : d < L
  · apply no_refutation_of_filtered_assignment
    exact filtered N L d 0 hN hL (Or.inl rfl) (by simpa using h)
  · apply no_refutation_of_filtered_assignment
    exact filtered N L d 2 hN hL (Or.inr rfl) (by simp; omega)

#print axioms lower
end Programme.«20261101-0614-proof-complexity».Lossy
