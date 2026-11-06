import Programme.«20261031-2024-proof-complexity».IterCone

namespace Programme.«20261101-0614-proof-complexity».UnaryIter
open Programme.«20261031-2024-proof-complexity».NativeIter

/-- One-hot row; `(x,z)` is Python variable `1+x*L+z`. -/
def row (L x : Nat) : Clause := (List.range L).map fun z => ((x,z), true)

/-- Exactly the ordered clauses of `th.checks.unary_iter_certificates.cnf`,
before its final duplicate removal. -/
def raw (L : Nat) : List Clause :=
  ((List.range L).flatMap fun x =>
    [row L x] ++ (List.range L).flatMap fun z =>
      (((List.range L).filter fun t => z < t).map fun t =>
        [((x,z),false), ((x,t),false)])) ++
  [[((0,0),false)]] ++
  ((List.range L).flatMap fun x =>
    (List.range x).map fun z => [((x,z),false)]) ++
  ((List.range L).flatMap fun x =>
    (((List.range L).filter fun z => x < z).map fun z =>
      [((x,z),false), ((z,z),false)]))

def cnf (L : Nat) : List Clause := (raw L).eraseDups

/-- Clause-set bridge to the explicit Python generator specification.
Positive `(x,z)` translates to `1+x*L+z`, negative to its negation. -/
theorem generator_spec (L : Nat) (c : Clause) : c ∈ cnf L ↔
    (((∃ x, x < L ∧ (c = row L x ∨
        ∃ z, z < L ∧ ∃ t, (t < L ∧ z < t) ∧
          c = [((x,z),false), ((x,t),false)])) ∨ c = [((0,0),false)]) ∨
      (∃ x, x < L ∧ ∃ z, z < x ∧ c = [((x,z),false)])) ∨
    (∃ x, x < L ∧ ∃ z, (z < L ∧ x < z) ∧
      c = [((x,z),false), ((z,z),false)]) := by
  simp [cnf, raw, List.mem_flatMap, List.mem_map, List.mem_filter, eq_comm, or_assoc]

def Negative (c : Clause) : Prop := c ≠ [] ∧ ∀ l ∈ c, l.2 = false

theorem clauses (L : Nat) (c : Clause) (hc : c ∈ cnf L) :
    (∃ x < L, c = row L x) ∨ Negative c := by
  simp only [cnf, raw, List.mem_eraseDups, List.mem_append,
    List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_map, List.mem_filter, List.mem_range] at hc
  rcases hc with ((⟨x, hx, hc⟩ | hc) | hc) | hc
  · rcases hc with hc | ⟨z, hz, t, ht, rfl⟩
    · exact Or.inl ⟨x, hx, hc⟩
    · right; simp [Negative]
  · subst c; right; simp [Negative]
  · obtain ⟨x, hx, z, hz, rfl⟩ := hc
    right; simp [Negative]
  · obtain ⟨x, hx, z, hz, rfl⟩ := hc
    right; simp [Negative]

theorem negative_zero (c : Clause) (hc : Negative c) :
    conjunction (falsity c) (fun _ => false) = 0 := by
  obtain ⟨hne, hneg⟩ := hc
  cases c with
  | nil => exact False.elim (hne rfl)
  | cons l ls =>
    have hl := hneg l (by simp)
    simp [conjunction, falsity, neg, holds, hl]

theorem lower (L d : Nat) (hd : d < L) : ¬ Refutes (cnf L) d := by
  apply no_refutation_of_filtered_assignment (a := fun _ => false)
  intro c hc hlen
  rcases clauses L c hc with ⟨x, hx, rfl⟩ | hneg
  · simp only [row, List.length_map, List.length_range] at hlen
    omega
  · exact negative_zero c hneg

#print axioms lower
end Programme.«20261101-0614-proof-complexity».UnaryIter
