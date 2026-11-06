import Programme.«20261101-0614-proof-complexity».Composition
namespace Programme.«20261101-0614-proof-complexity».Composition
open Programme.«20261031-2024-proof-complexity».NativeIter
open Programme.«20261101-0614-proof-complexity».RestrictionTarget

def structural (M N L : Nat) : List Clause :=
  (List.range M).flatMap (fun a => onehot N (fVar a)) ++
  (List.range N).flatMap (fun y =>
    (List.range L).flatMap (fun x => onehot L (sVar y x))) ++
  (List.range N).flatMap (fun y =>
    (List.range L).flatMap (fun x => onehot M (gVar y x)))

theorem event_mem (M N L y x a : Nat) (c : Clause)
    (hy : y < N) (ha : a < M) (he : (x,c) ∈ events L y) :
    eventClause M y x a c ∈ cnf M N L := by
  simp only [cnf, List.mem_eraseDups, List.mem_append]
  right
  exact List.mem_flatMap.mpr ⟨y, List.mem_range.mpr hy,
    List.mem_flatMap.mpr ⟨(x,c), he, List.mem_map.mpr ⟨a, List.mem_range.mpr ha, rfl⟩⟩⟩

theorem clauses_of_structural (ρ : Substitution) (M N L : Nat)
    (hs : RestrictionSpec ρ M N) (hM : 1 ≤ M)
    (hstruct : ∀ c ∈ structural (M+1) (N+1) L,
      ∀ t, clause ρ c = some t → t ∈ cnf M N L) :
    ∀ c ∈ cnf (M+1) (N+1) L, ∀ t,
      clause ρ c = some t → t ∈ cnf M N L := by
  intro c hc t ht
  simp only [cnf, List.mem_eraseDups, List.mem_append] at hc
  rcases hc with hc | hc
  · exact hstruct c (by simpa only [structural, List.mem_append] using hc) t ht
  · rcases List.mem_flatMap.mp hc with ⟨y, hy, hc⟩
    rcases List.mem_flatMap.mp hc with ⟨⟨x,e⟩, he, hc⟩
    rcases List.mem_map.mp hc with ⟨a, ha, rfl⟩
    have hy' := List.mem_range.mp hy
    have ha' := List.mem_range.mp ha
    by_cases hyN : y = N
    · subst y
      rw [deleted_event ρ M N x a e hs hM] at ht
      contradiction
    · have hylt : y < N := by omega
      by_cases haM : a = M
      · subst a
        rw [deleted_input_event ρ M N y x e hs hM hylt] at ht
        contradiction
      · have halt : a < M := by omega
        rw [retained_iter_event ρ M N L y x a e hs hM halt hylt he] at ht
        cases ht
        exact event_mem M N L y x a e hylt halt he

theorem refutes_of_structural (ρ : Substitution) (M N L d : Nat)
    (hs : RestrictionSpec ρ M N) (hM : 1 ≤ M)
    (hstruct : ∀ c ∈ structural (M+1) (N+1) L,
      ∀ t, clause ρ c = some t → t ∈ cnf M N L)
    (hf : Refutes (cnf (M+1) (N+1) L) d) : Refutes (cnf M N L) d :=
  Programme.«20261101-0614-proof-complexity».«th-split».RestrictionBridge.transport ρ _ _ d
    (clauses_of_structural ρ M N L hs hM hstruct) hf
#print axioms refutes_of_structural
end Programme.«20261101-0614-proof-complexity».Composition
