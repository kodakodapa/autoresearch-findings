import Programme.«20261104-1627-proof-complexity».TailPivot
import Programme.«20261104-1627-proof-complexity».MixedAggregate
import Programme.«20261104-1627-proof-complexity».OrderedExtension

namespace Programme.«20261104-1627-proof-complexity».TailWeighted
open Programme.«20261104-1627-proof-complexity».MatchingLabels Programme.«20261104-1627-proof-complexity».TailPivot Programme.«20261104-1627-proof-complexity».TailCoordinates

/-- A finite list of actual weighted last-pigeon rc pivots. -/
abbrev Data := List (Int × Matching × Nat)

def corrections (m n : Nat) (L : Data) : List (Int × Vector) :=
  L.map fun t => (t.1, rc (m+1) n t.2.1 m t.2.2)

def rowCorrections (m n : Nat) (L : Data) : List (Int × Vector) :=
  L.map fun t => (t.1, pivotRows m n t.2.1 t.2.2)

def residual (m n : Nat) (v : Vector) (L : Data) : Vector :=
  v ++ (combine (corrections m n L)).map (fun t => (-t.1,t.2))

private theorem split_combine (m b : Nat) (C : List (Int × Vector)) :
    splitPigeon m b (combine C) =
      combine (C.map fun t => (t.1, splitPigeon m b t.2)) := by
  induction C with
  | nil => rfl
  | cons t C ih =>
    simp only [combine, List.flatMap_cons, List.map_cons, splitPigeon,
      List.filter_append] at ih ⊢
    rw [ih]
    congr 1
    induction t.2 with
    | nil => rfl
    | cons s ss ih =>
      simp only [List.map_cons, List.filter_cons]
      split <;> simp_all

theorem weighted_pivot_split (m n : Nat) (L : Data)
    (h : ∀ t ∈ L, t.2.1.any (fun e => e.1 == m) = false) :
    splitPigeon m 2 (combine (corrections m n L)) =
      combine (rowCorrections m n L) := by
  rw [split_combine]
  congr 1
  simp only [corrections, rowCorrections, List.map_map]
  apply List.map_congr_left
  intro t ht
  simp only [Function.comp_apply]
  rw [rc_pivot_split m n t.2.1 t.2.2 (h t ht)]

theorem corrections_enumerated {m n e : Nat} {L : Data}
    (h : ∀ t ∈ L, t.2.1 ∈ matchings (m+1) n e ∧
      m ∈ rows (m+1) t.2.1 ∧ t.2.2 ∈ cols n t.2.1) :
    ∀ t ∈ corrections m n L, t.2 ∈ syzygies (m+1) n (e+2) := by
  intro t ht
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
  exact rc_enumerated (h s hs).1 (h s hs).2.1 (h s hs).2.2

theorem residual_kernel {p m n e : Nat} {v : Vector} {L : Data}
    (hv : Kernel p (m+1) n (e+2) v)
    (h : ∀ t ∈ L, t.2.1 ∈ matchings (m+1) n e ∧
      m ∈ rows (m+1) t.2.1 ∧ t.2.2 ∈ cols n t.2.1) :
    Kernel p (m+1) n (e+2) (residual m n v L) := by
  apply kernel_append hv
  have hk : Kernel p (m+1) n (e+2) (combine (corrections m n L)) := by
    apply kernel_combine
    intro t ht
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
    exact rc_kernel (h s hs).1 (h s hs).2.1 (h s hs).2.2
  simpa only [Int.neg_one_mul] using kernel_scale hk (-1)

/-- The finite pivot equation is the substantive remaining hypothesis. -/
theorem residual_pivot_zero {p m n : Nat} {v : Vector} {L : Data}
    (havoid : ∀ t ∈ L, t.2.1.any (fun e => e.1 == m) = false)
    (he : ∀ g, (p : Int) ∣ vectorCoeff (splitPigeon m 2 v) g -
      vectorCoeff (combine (rowCorrections m n L)) g) :
    ∀ g, (p : Int) ∣ vectorCoeff (splitPigeon m 2 (residual m n v L)) g := by
  intro g
  have hn (a : Vector) :
      splitPigeon m 2 (a.map fun t => (-t.1,t.2)) =
      (splitPigeon m 2 a).map (fun t => (-t.1,t.2)) := by
    induction a with
    | nil => rfl
    | cons t a ih =>
      simp only [List.map_cons, splitPigeon, List.filter_cons] at ih ⊢
      split <;> simp_all
  change (p : Int) ∣ vectorCoeff
    ((v ++ (combine (corrections m n L)).map fun t => (-t.1,t.2)).filter _) g
  rw [List.filter_append]
  change (p : Int) ∣ vectorCoeff (splitPigeon m 2 v ++
    splitPigeon m 2 ((combine (corrections m n L)).map fun t => (-t.1,t.2))) g
  rw [hn, weighted_pivot_split m n L havoid, vectorCoeff_append]
  have hh := Programme.«20261104-1627-proof-complexity».MixedAggregate.coeff_scale
    (combine (rowCorrections m n L)) (-1) g
  simp only [Int.neg_one_mul] at hh
  rw [hh]
  exact he g


theorem residual_tail_support {m n : Nat} {v : Vector} {L : Data}
    (hs : ∀ t ∈ v, pigeonBlock m t.2 ≠ 1)
    (ha : ∀ t ∈ L, t.2.1.any (fun e => e.1 == m) = false) :
    ∀ t ∈ residual m n v L, pigeonBlock m t.2 ≠ 1 := by
  intro t ht
  rcases List.mem_append.mp ht with ht | ht
  · exact hs t ht
  · obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
    obtain ⟨c,hc,hs⟩ := List.mem_flatMap.mp hs
    obtain ⟨a,haL,rfl⟩ := List.mem_map.mp hc
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hs
    exact rc_tail_support m n a.2.1 a.2.2 (ha a haL) u hu

/-- Given a solution to the finite pivot equation, the actual incident remainder
is a kernel on the original board and at the original degree. -/
theorem incident_remainder_kernel {p m n e : Nat} {v : Vector} {L : Data}
    (hv : Kernel p (m+1) n (e+2) v)
    (hs : ∀ t ∈ v, pigeonBlock m t.2 ≠ 1)
    (h : ∀ t ∈ L, t.2.1 ∈ matchings (m+1) n e ∧
      m ∈ rows (m+1) t.2.1 ∧ t.2.2 ∈ cols n t.2.1)
    (ha : ∀ t ∈ L, t.2.1.any (fun e => e.1 == m) = false)
    (he : ∀ g, (p : Int) ∣ vectorCoeff (splitPigeon m 2 v) g -
      vectorCoeff (combine (rowCorrections m n L)) g) :
    Kernel p (m+1) n (e+2) (splitPigeon m 3 (residual m n v L)) :=
  incident_kernel (residual_kernel hv h) (residual_tail_support hs ha)
    (residual_pivot_zero ha he)

end Programme.«20261104-1627-proof-complexity».TailWeighted
#print axioms Programme.«20261104-1627-proof-complexity».TailWeighted.weighted_pivot_split
#print axioms Programme.«20261104-1627-proof-complexity».TailWeighted.residual_kernel
#print axioms Programme.«20261104-1627-proof-complexity».TailWeighted.residual_pivot_zero

#print axioms Programme.«20261104-1627-proof-complexity».TailWeighted.incident_remainder_kernel
