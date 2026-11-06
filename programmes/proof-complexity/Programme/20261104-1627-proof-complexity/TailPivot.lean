import Programme.«20261104-1627-proof-complexity».TailCoordinates

namespace Programme.«20261104-1627-proof-complexity».TailPivot
open Programme.«20261104-1627-proof-complexity».MatchingLabels

theorem uses_ordered (w : Nat) (N : Matching) (r : Bool) (a : Nat) :
    usesPigeon w ⟨ordered N,r,a⟩ = N.any (fun e => e.1 == w) := by
  apply Bool.eq_iff_iff.mpr
  simp only [usesPigeon, List.any_eq_true]
  constructor <;> rintro ⟨e,he,hw⟩
  · exact ⟨e, (List.mem_mergeSort).mp he, hw⟩
  · exact ⟨e, (List.mem_mergeSort).mpr he, hw⟩

/-- The actual row pivot terms of an rc generator marked by the last pigeon. -/
def pivotRows (m n : Nat) (N : Matching) (j : Nat) : Vector :=
  ((rows (m+1) N).filter (· != m)).map
    (fun a => (1, ⟨ordered (N ++ [(a,j)]),true,m⟩))

def incidentColumns (m n : Nat) (N : Matching) (j : Nat) : Vector :=
  ((cols n N).filter (· != j)).map
    (fun b => (-1, ⟨ordered (N ++ [(m,b)]),false,j⟩))

theorem rc_parts (m n : Nat) (N : Matching) (j : Nat) :
    rc (m+1) n N m j = pivotRows m n N j ++ incidentColumns m n N j := rfl

theorem pivotRows_block (m n : Nat) (N : Matching) (j : Nat)
    (hN : N.any (fun e => e.1 == m) = false) :
    ∀ t ∈ pivotRows m n N j, pigeonBlock m t.2 = 2 := by
  intro t ht
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp ht
  have ham : a ≠ m := by simpa using (List.mem_filter.mp ha).2
  simp [pigeonBlock, uses_ordered, List.any_append, hN, ham]

theorem incidentColumns_block (m n : Nat) (N : Matching) (j : Nat) :
    ∀ t ∈ incidentColumns m n N j, pigeonBlock m t.2 = 3 := by
  intro t ht
  obtain ⟨b,_,rfl⟩ := List.mem_map.mp ht
  simp [pigeonBlock, uses_ordered, List.any_append]

private theorem split_all (w b : Nat) (v : Vector)
    (h : ∀ t ∈ v, pigeonBlock w t.2 = b) : splitPigeon w b v = v := by
  apply List.filter_eq_self.mpr
  intro t ht
  simpa using h t ht

private theorem split_none (w b c : Nat) (v : Vector) (hne : c ≠ b)
    (h : ∀ t ∈ v, pigeonBlock w t.2 = c) : splitPigeon w b v = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro t ht
  simp [h t ht, hne]

theorem rc_pivot_split (m n : Nat) (N : Matching) (j : Nat)
    (hN : N.any (fun e => e.1 == m) = false) :
    splitPigeon m 2 (rc (m+1) n N m j) = pivotRows m n N j := by
  rw [rc_parts]
  change (pivotRows m n N j ++ incidentColumns m n N j).filter _ = _
  rw [List.filter_append]
  change splitPigeon m 2 (pivotRows m n N j) ++
    splitPigeon m 2 (incidentColumns m n N j) = _
  rw [split_all _ _ _ (pivotRows_block m n N j hN),
    split_none m 2 3 _ (by decide) (incidentColumns_block m n N j), List.append_nil]

theorem rc_incident_split (m n : Nat) (N : Matching) (j : Nat)
    (hN : N.any (fun e => e.1 == m) = false) :
    splitPigeon m 3 (rc (m+1) n N m j) = incidentColumns m n N j := by
  rw [rc_parts]
  change (pivotRows m n N j ++ incidentColumns m n N j).filter _ = _
  rw [List.filter_append]
  change splitPigeon m 3 (pivotRows m n N j) ++
    splitPigeon m 3 (incidentColumns m n N j) = _
  rw [split_none m 3 2 _ (by decide) (pivotRows_block m n N j hN),
    split_all _ _ _ (incidentColumns_block m n N j), List.nil_append]

/-- These pivots are literal tail vectors: no first-block repair is required. -/
theorem rc_tail_support (m n : Nat) (N : Matching) (j : Nat)
    (hN : N.any (fun e => e.1 == m) = false) :
    ∀ t ∈ rc (m+1) n N m j, pigeonBlock m t.2 ≠ 1 := by
  rw [rc_parts]
  intro t ht
  rcases List.mem_append.mp ht with ht | ht
  · rw [pivotRows_block m n N j hN t ht]; decide
  · rw [incidentColumns_block m n N j t ht]; decide

/-- With a valid base and fresh marks this is an enumerated, not abstract, pivot. -/
theorem rc_enumerated {m n e : Nat} {N : Matching} {j : Nat}
    (hN : N ∈ matchings (m+1) n e)
    (hm : m ∈ rows (m+1) N) (hj : j ∈ cols n N) :
    rc (m+1) n N m j ∈ syzygies (m+1) n (e+2) := by
  unfold syzygies
  apply List.mem_append_left
  rw [if_neg (by omega : ¬ e+2 < 2)]
  apply List.mem_flatMap.mpr
  refine ⟨N, by simpa using hN, ?_⟩
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  exact ⟨m, hm, List.mem_map.mpr ⟨j, hj, rfl⟩⟩

end Programme.«20261104-1627-proof-complexity».TailPivot
#print axioms Programme.«20261104-1627-proof-complexity».TailPivot.rc_pivot_split
#print axioms Programme.«20261104-1627-proof-complexity».TailPivot.rc_incident_split

#print axioms Programme.«20261104-1627-proof-complexity».TailPivot.rc_enumerated
#print axioms Programme.«20261104-1627-proof-complexity».TailPivot.rc_tail_support
