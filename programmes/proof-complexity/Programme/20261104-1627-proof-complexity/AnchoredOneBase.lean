import Programme.«20261104-1627-proof-complexity».KernelLinear
import Programme.«20261104-1627-proof-complexity».RectangularOne

namespace Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261029-1156-proof-complexity».StdPC

private theorem cf_flat_cons (B : List Nat) (f : Nat → Int × List Nat)
    (g : Nat → List (Int × List Nat)) (u : List Nat) :
    cf (B.flatMap fun b => f b :: g b) u =
      cf (B.map f) u + cf (B.flatMap g) u := by
  induction B with
  | nil => simp [cf]
  | cons b B ih =>
    simp only [List.flatMap_cons, List.map_cons, List.cons_append, cf_append]
    by_cases h : (f b).2.Perm u <;> simp [cf, h] at ih ⊢ <;> omega

private theorem cf_grid (A B : List Nat) (f : Nat → Nat → List Nat) (u : List Nat) :
    cf (A.flatMap fun a => B.map fun b => ((1 : Int), f a b)) u =
    cf (B.flatMap fun b => A.map fun a => ((1 : Int), f a b)) u := by
  induction A with
  | nil =>
    have hz : B.flatMap (fun _ => ([] : List (Int × List Nat))) = [] := by
      induction B <;> simp_all
    simp [hz, cf]
  | cons a A ih =>
    simp only [List.flatMap_cons, List.map_cons, cf_append]
    rw [cf_flat_cons, ih]

private theorem cf_negative (L : List (Int × List Nat)) (u : List Nat) :
    cf (L.map fun t => (-t.1,t.2)) u = -cf L u := by
  induction L with
  | nil => simp [cf]
  | cons t L ih =>
    by_cases h : t.2.Perm u <;> simp [cf, h] at ih ⊢ <;> omega

private theorem rows_ordered (m : Nat) (N : Matching) : rows m (ordered N) = rows m N := by
  unfold rows
  congr 1
  funext i
  apply Bool.eq_iff_iff.mpr
  simp [freeRow, ordered, List.all_eq_true]

private theorem cols_ordered (n : Nat) (N : Matching) : cols n (ordered N) = cols n N := by
  unfold cols
  congr 1
  funext i
  apply Bool.eq_iff_iff.mpr
  simp [freeCol, ordered, List.all_eq_true]

private theorem z_base_expansion (m n : Nat) (N : Matching) : z m n 1 N =
    (rows m N).map (fun i => (1,⟨ordered N,true,i⟩)) ++
    (cols n N).map (fun j => (-1,⟨ordered N,false,j⟩)) := by
  simp only [z, Nat.sub_self, matchings, List.filter_cons, List.all_nil,
    Bool.true_eq, ↓reduceIte, List.filter_nil, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]
  simp [rows, cols]

theorem z_base_one_top_zero (m n : Nat) (N : Matching) (u : List Nat) :
    coeff (top m n (z m n 1 N)) u = 0 := by
  rw [z_base_expansion, top_append_coeff]
  simp [top, topLabel, rows_ordered, cols_ordered, coeff,
    List.flatMap_map, List.map_map, Function.comp_def]
  have hg := cf_grid (rows m N) (cols n N)
    (fun i j => (i*n+j) :: mono n (ordered N)) u
  have hn := cf_negative ((cols n N).flatMap fun j =>
    (rows m N).map fun i => ((1 : Int), (i*n+j) :: mono n (ordered N))) u
  simp only [List.map_flatMap, List.map_map] at hn
  simp only [Function.comp_def, Int.reduceNeg] at hn
  omega

theorem z_base_one_kernel {m n e : Nat} (p : Nat) (N : Matching)
    (hN : ordered N ∈ matchings m n e) :
    Kernel p m n (e+1) (z m n 1 N) := by
  refine ⟨?_, ?_⟩
  · intro a ha
    rw [z_base_expansion] at ha
    unfold labels
    simp only [Nat.add_sub_cancel, Nat.add_eq_zero_iff, Nat.one_ne_zero,
      and_false, ↓reduceIte]
    apply List.mem_flatMap.mpr
    refine ⟨ordered N, hN, ?_⟩
    rw [rows_ordered, cols_ordered]
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
      exact List.mem_append_left _ (List.mem_map.mpr ⟨i,hi,rfl⟩)
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
      exact List.mem_append_right _ (List.mem_map.mpr ⟨j,hj,rfl⟩)
  · intro u
    rw [z_base_one_top_zero]
    simp [coeff, cf]

end Programme.«20261104-1627-proof-complexity».MatchingLabels
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.z_base_one_top_zero

#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.z_base_one_kernel
