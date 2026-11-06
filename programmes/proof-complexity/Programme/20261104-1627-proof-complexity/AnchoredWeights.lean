import Programme.«20261104-1627-proof-complexity».HomogeneousLabels

namespace Programme.«20261104-1627-proof-complexity».AnchoredWeights
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261029-1156-proof-complexity».StdPC

/-- The actual signed number of permitted final marks above E. -/
def weight (m n : Nat) (N E : Matching) : Int :=
  (((rows m (N ++ E)).filter fun i => E.all fun e => e.1 < i).length : Int) -
  (((cols n (N ++ E)).filter fun j => E.all fun e => e.2 < j).length : Int)

def compatible (m n q : Nat) (N : Matching) : List Matching :=
  (matchings m n q).filter fun E => E.all fun e => freeRow N e.1 && freeCol N e.2

/-- A polynomial with one weighted term for each compatible partial matching. -/
def weighted (m n t : Nat) (N : Matching) : Poly Nat :=
  ⟨(compatible m n (t-1) N).map fun E => (weight m n N E, mono n (N ++ E))⟩

private theorem repeated (L : List Nat) (a : Int) (v u : List Nat) :
    cf (L.map fun _ => (a,v)) u = if v.Perm u then (L.length : Int)*a else 0 := by
  induction L with
  | nil => simp [cf]
  | cons x L ih =>
    by_cases h : v.Perm u <;> simp [cf, h, Int.add_mul, Int.add_comm] at ih ⊢ <;> exact ih

/-- Exact integer compression of rho; no modulus or matching hypothesis. -/
theorem rho_weighted_coeff (m n t : Nat) (N : Matching) (u : List Nat) :
    coeff (rho n (z m n t N)) u = coeff (weighted m n t N) u := by
  have piece (E : Matching) :
      cf (((((rows m (N ++ E)).filter fun i => E.all fun e => e.1 < i).map
        (fun i => (1, (⟨ordered (N ++ E),true,i⟩ : Label)))) ++
      (((cols n (N ++ E)).filter fun j => E.all fun e => e.2 < j).map
        (fun j => (-1, (⟨ordered (N ++ E),false,j⟩ : Label))))).map
        (fun a : Int × Label => (a.1, mono n a.2.base))) u =
      cf [(weight m n N E, mono n (N ++ E))] u := by
    simp only [List.map_append, List.map_map, Function.comp_def, cf_append]
    rw [repeated, repeated]
    have hp : (mono n (ordered (N ++ E))).Perm (mono n (N ++ E)) :=
      (List.mergeSort_perm (N ++ E) _).map _
    have he : (mono n (ordered (N ++ E))).Perm u ↔ (mono n (N ++ E)).Perm u :=
      ⟨fun h => hp.symm.trans h, fun h => hp.trans h⟩
    by_cases h : (mono n (N ++ E)).Perm u <;> simp [he, h, cf, weight, Int.sub_eq_add_neg]
  change cf _ u = cf _ u
  unfold rho z weighted compatible
  rw [List.map_flatMap]
  generalize ((matchings m n (t-1)).filter fun E =>
    E.all fun e => freeRow N e.1 && freeCol N e.2) = L
  induction L with
  | nil => simp [cf]
  | cons E L ih =>
    simp only [List.flatMap_cons, List.map_cons, cf_append]
    rw [piece]
    have addcf (a : Int × List Nat) (T : List (Int × List Nat)) :
        cf (a :: T) u = cf [a] u + cf T u := by
      simpa using cf_append [a] T u
    rw [addcf, ih]
    by_cases h : (mono n (N ++ E)).Perm u <;> simp [cf, h]

/-- Every compressed term has exactly the expected homogeneous length. -/
theorem weighted_terms_length {m n s t : Nat} {N : Matching}
    (hN : N ∈ matchings m n s) (a : Int × List Nat)
    (ha : a ∈ (weighted m n t N).terms) : a.2.length = s + (t-1) := by
  obtain ⟨E,hE,rfl⟩ := List.mem_map.mp ha
  have hl := matching_length (List.mem_filter.mp hE).1
  simp [mono, matching_length hN, hl]

theorem weighted_degree_le {m n s t : Nat} {N : Matching}
    (hN : N ∈ matchings m n s) : (weighted m n t N).deg ≤ s + (t-1) := by
  apply (deg_le_iff _ _).mpr
  intro a ha
  have h := weighted_terms_length hN a ha
  omega

end Programme.«20261104-1627-proof-complexity».AnchoredWeights
#print axioms Programme.«20261104-1627-proof-complexity».AnchoredWeights.rho_weighted_coeff
#print axioms Programme.«20261104-1627-proof-complexity».AnchoredWeights.weighted_terms_length
#print axioms Programme.«20261104-1627-proof-complexity».AnchoredWeights.weighted_degree_le
