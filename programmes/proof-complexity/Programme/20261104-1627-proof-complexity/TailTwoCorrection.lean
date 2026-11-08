import Programme.«20261104-1627-proof-complexity».TailGlobalImage
import Programme.«20261104-1627-proof-complexity».MixedAggregate
import Programme.«20261104-1627-proof-complexity».AnchoredValidity
namespace Programme.«20261104-1627-proof-complexity».IncidentSection
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261104-1627-proof-complexity».MixedAggregate

def twoCorrection (m n : Nat) (a b : Nat → Int) : List (Int × Vector) :=
  ((List.range m).map fun i => (-a i, rr n [] i m)) ++
  ((List.range n).map fun j => (b j, rc (m+1) n [] m j))

private theorem sum_single (k x : Nat) (f : Nat → Int) :
    ((List.range k).map fun i => if x = i then f i else 0).sum =
      if x < k then f x else 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ,List.map_append,List.sum_append,ih]
    by_cases he : x = k
    · subst x; simp
    · by_cases hx : x < k
      · simp [he,hx,show x < k+1 by omega]
      · simp [he,hx,show ¬ x < k+1 by omega]

theorem twoCorrection_coordinate {m n i j : Nat} (hi : i < m) (hj : j < n)
    (a b : Nat → Int) :
    vectorCoeff (combine (twoCorrection m n a b)) ⟨[(i,j)],true,m⟩ = a i + b j := by
  rw [coeff_combine]
  simp only [twoCorrection,List.map_append,List.sum_append,List.map_map]
  have hr (k : Nat) :
      -a k * vectorCoeff (rr n [] k m) ⟨[(i,j)],true,m⟩ =
      if i = k then a k else 0 := by
    change -a k * vectorCoeff (rr n [] k m) (edgeRowLabel i j m) = _
    rw [rr_row_coefficient]
    by_cases he : i = k
    · subst k; simp [hj,show i ≠ m by omega]
    · simp [he,hj,show i ≠ m by omega]
  have hc (k : Nat) :
      b k * vectorCoeff (rc (m+1) n [] m k) ⟨[(i,j)],true,m⟩ =
      if j = k then b k else 0 := by
    change b k * vectorCoeff (rc (m+1) n [] m k) (edgeRowLabel i j m) = _
    rw [rc_row_coefficient]
    by_cases he : j = k <;> simp [he,show i < m+1 by omega,show i ≠ m by omega]
  change ((List.range m).map fun k => -a k * vectorCoeff (rr n [] k m) ⟨[(i,j)],true,m⟩).sum +
    ((List.range n).map fun k => b k * vectorCoeff (rc (m+1) n [] m k) ⟨[(i,j)],true,m⟩).sum = _
  simp only [hr,hc]
  rw [sum_single,sum_single,if_pos hi,if_pos hj]

theorem twoCorrection_member (m n : Nat) (a b : Nat → Int) :
    ∀ t ∈ twoCorrection m n a b, t.2 ∈ syzygies (m+1) n 2 := by
  intro t ht
  rcases List.mem_append.mp ht with ht | ht
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ht
    have hi' := List.mem_range.mp hi
    simp only [syzygies,show ¬(2 < 2) by omega, ↓reduceIte]
    apply List.mem_append_left
    apply List.mem_flatMap.mpr
    refine ⟨[],by simp [matchings],?_⟩
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_flatMap.mpr
    refine ⟨i,?_,?_⟩
    · simpa [rows,freeRow] using (show i < m+1 by omega)
    · apply List.mem_map.mpr
      refine ⟨m,?_,rfl⟩
      simp [rows,freeRow,hi']
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ht
    have hj' := List.mem_range.mp hj
    simp only [syzygies,show ¬(2 < 2) by omega, ↓reduceIte]
    apply List.mem_append_left
    apply List.mem_flatMap.mpr
    refine ⟨[],by simp [matchings],?_⟩
    apply List.mem_append_right
    apply List.mem_flatMap.mpr
    refine ⟨m,by simp [rows,freeRow],?_⟩
    apply List.mem_map.mpr
    exact ⟨j,by simpa [cols,freeCol] using hj',rfl⟩
/-- Actual enumerated corrections cancel every degree-two block-two coordinate
while preserving Kernel. -/
theorem tail_two_correction {p m n : Nat} (hn : 2 < n)
    {v : Vector} (hv : Kernel p (m+1) n 2 v)
    (ht : ∀ t ∈ v, pigeonBlock m t.2 ≠ 1) :
    ∃ C : List (Int × Vector),
      (∀ t ∈ C, t.2 ∈ syzygies (m+1) n 2) ∧
      Kernel p (m+1) n 2 (v ++ (combine C).map (fun t => (-t.1,t.2))) ∧
      ∀ i, i < m → ∀ j, j < n →
        (p : Int) ∣ vectorCoeff
          (v ++ (combine C).map (fun t => (-t.1,t.2))) ⟨[(i,j)],true,m⟩ := by
  obtain ⟨a,b,hab⟩ := tail_two_row_col hn hv ht
  let C := twoCorrection m n a b
  have hC := twoCorrection_member m n a b
  refine ⟨C,hC,?_,?_⟩
  · have hk := kernel_scale (kernel_combine C (fun t ht =>
        syzygies_sound p (m+1) n 2 t.2 (hC t ht))) (-1)
    have he : ((combine C).map fun t => ((-1 : Int)*t.1,t.2)) =
        ((combine C).map fun t => (-t.1,t.2)) := by simp
    rw [he] at hk
    exact kernel_append hv hk
  · intro i hi j hj
    have he : ((combine C).map fun t => (-t.1,t.2)) =
        ((combine C).map fun t => ((-1 : Int)*t.1,t.2)) := by simp
    rw [vectorCoeff_append,he,coeff_scale]
    have hc := twoCorrection_coordinate hi hj a b
    change vectorCoeff (combine C) _ = _ at hc
    rw [hc]
    simpa only [Int.neg_mul,Int.one_mul,Int.sub_eq_add_neg] using hab i hi j hj

end Programme.«20261104-1627-proof-complexity».IncidentSection
#print axioms Programme.«20261104-1627-proof-complexity».IncidentSection.twoCorrection_coordinate
#print axioms Programme.«20261104-1627-proof-complexity».IncidentSection.twoCorrection_member
#print axioms Programme.«20261104-1627-proof-complexity».IncidentSection.tail_two_correction
