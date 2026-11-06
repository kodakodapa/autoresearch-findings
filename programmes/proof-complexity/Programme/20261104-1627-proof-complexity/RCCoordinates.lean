import Programme.«20261104-1627-proof-complexity».RRCoordinates

namespace Programme.«20261104-1627-proof-complexity».MatchingLabels

private theorem vc_cons_rc (a : Int × Label) (v : Vector) (g : Label) :
    vectorCoeff (a :: v) g = (if a.2 = g then a.1 else 0) + vectorCoeff v g := by
  by_cases h : a.2 = g <;> simp [vectorCoeff, h]

private theorem vc_select (L : List Nat) (f : Nat → Label) (g : Label)
    (c : Int) (x : Nat) (P : Prop) [Decidable P]
    (hf : ∀ k, f k = g ↔ k = x ∧ P) :
    vectorCoeff (L.map fun k => (c, f k)) g =
      if P then c * ((L.filter (· == x)).length : Int) else 0 := by
  induction L with
  | nil => simp [vectorCoeff]
  | cons k L ih =>
    rw [List.map_cons, vc_cons_rc, ih]
    by_cases hp : P <;> by_cases hk : k = x <;>
      simp [hf, hp, hk, Int.mul_add] <;> omega

private theorem range_count_rc (n b : Nat) :
    ((List.range n).filter (fun x => x == b)).length = if b < n then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih]
    by_cases he : n = b
    · subst b; simp
    · by_cases hb : b < n
      · simp [he, hb, show b < n + 1 by omega]
      · simp [he, hb, show ¬ b < n + 1 by omega]

private theorem select_range (N x y : Nat) :
    (((List.range N).filter (· != y)).filter (· == x)).length =
      if x < N ∧ x ≠ y then 1 else 0 := by
  rw [List.filter_filter]
  by_cases h : x = y
  · subst y
    have he : (fun a => a == x && a != x) = fun _ => false := by
      funext a
      by_cases ha : a = x <;> simp [ha]
    simp [he]
  · have he : (fun a => a == x && a != y) = fun a => a == x := by
      funext a
      by_cases ha : a = x <;> simp [ha,h]
    simp [he, range_count_rc, h]

theorem rc_empty (m n i j : Nat) : rc m n [] i j =
    ((List.range m).filter (· != i)).map (fun a => (1, edgeRowLabel a j i)) ++
    ((List.range n).filter (· != j)).map (fun b => (-1, edgeColLabel i b j)) := by
  have hr : freeRow [] = fun _ => true := rfl
  have hc : freeCol [] = fun _ => true := rfl
  have hh (L : List Nat) : L.filter (fun _ => true) = L := List.filter_eq_self.mpr (by simp)
  simp [rc, rows, cols, hr, hc, hh, ordered, edgeRowLabel, edgeColLabel]

theorem rc_row_coefficient (m n i j a b r : Nat) :
    vectorCoeff (rc m n [] i j) (edgeRowLabel a b r) =
      if b = j ∧ r = i ∧ a < m ∧ a ≠ i then 1 else 0 := by
  rw [rc_empty, vectorCoeff_append]
  rw [vc_select _ _ _ 1 a (b = j ∧ r = i) (by
    intro k
    simp [edgeRowLabel]
    omega)]
  rw [vc_select _ _ _ (-1) 0 False (by
    intro k
    simp [edgeColLabel, edgeRowLabel])]
  rw [select_range]
  by_cases hb : b = j <;> by_cases hr : r = i <;>
    by_cases ha : a < m <;> by_cases hai : a = i <;> simp [hb,hr,ha,hai]

theorem rc_col_coefficient (m n i j a b r : Nat) :
    vectorCoeff (rc m n [] i j) (edgeColLabel a b r) =
      if a = i ∧ r = j ∧ b < n ∧ b ≠ j then -1 else 0 := by
  rw [rc_empty, vectorCoeff_append]
  rw [vc_select _ _ _ 1 0 False (by
    intro k
    simp [edgeColLabel, edgeRowLabel])]
  rw [vc_select _ _ _ (-1) b (a = i ∧ r = j) (by
    intro k
    simp [edgeColLabel]
    omega)]
  simp only [ite_false, Int.zero_add]
  rw [select_range]
  by_cases ha : a = i <;> by_cases hr : r = j <;>
    by_cases hb : b < n <;> by_cases hbj : b = j <;> simp [ha,hr,hb,hbj]

 theorem rc_mem_syzygies {m n i j : Nat} (hi : i < m) (hj : j < n) :
    rc m n [] i j ∈ syzygies m n 2 := by
  have hr : freeRow [] = fun _ => true := rfl
  have hc : freeCol [] = fun _ => true := rfl
  simp [syzygies, matchings, rows, cols, hr, hc]
  exact Or.inr (Or.inr (Or.inl ⟨i,hi,j,hj,rfl⟩))

 theorem rc_valid {m n i j : Nat} (hi : i < m) (hj : j < n) :
    valid m n 2 (rc m n [] i j) := by
  intro t ht
  rw [rc_empty] at ht
  rcases List.mem_append.mp ht with ht | ht
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp ht
    obtain ⟨ha,hai⟩ := List.mem_filter.mp ha
    have ha' := List.mem_range.mp ha
    have hai' : a ≠ i := by simpa using hai
    exact (label_two_iff).mpr (Or.inl ⟨a,ha',j,hj,i,hi,hai',rfl⟩)
  · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ht
    obtain ⟨hb,hbj⟩ := List.mem_filter.mp hb
    have hb' := List.mem_range.mp hb
    have hbj' : b ≠ j := by simpa using hbj
    exact (label_two_iff).mpr (Or.inr ⟨i,hi,b,hb',j,hj,hbj',rfl⟩)

end Programme.«20261104-1627-proof-complexity».MatchingLabels
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.rc_row_coefficient
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.rc_col_coefficient

#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.rc_mem_syzygies
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.rc_valid
