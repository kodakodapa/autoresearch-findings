import Programme.«20261104-1627-proof-complexity».AnchoredOneBase

namespace Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261029-1156-proof-complexity».StdPC

theorem mono_ordered_perm (n : Nat) (N : Matching) :
    (mono n (ordered N)).Perm (mono n N) := by
  exact (List.mergeSort_perm N _).map _

theorem rows_ordered_eq (m : Nat) (N : Matching) : rows m (ordered N) = rows m N := by
  unfold rows
  congr 1
  funext i
  apply Bool.eq_iff_iff.mpr
  simp [freeRow, ordered, List.all_eq_true]

theorem cols_ordered_eq (n : Nat) (N : Matching) : cols n (ordered N) = cols n N := by
  unfold cols
  congr 1
  funext i
  apply Bool.eq_iff_iff.mpr
  simp [freeCol, ordered, List.all_eq_true]

theorem rows_extend (m : Nat) (N : Matching) (a b : Nat) :
    rows m (ordered (N ++ [(a,b)])) = (rows m N).filter (· != a) := by
  rw [rows_ordered_eq]
  unfold rows
  rw [List.filter_filter]
  congr 1
  funext i
  simp [freeRow, List.all_append, Bool.and_comm, bne_comm]

theorem cols_extend (n : Nat) (N : Matching) (a b : Nat) :
    cols n (ordered (N ++ [(a,b)])) = (cols n N).filter (· != b) := by
  rw [cols_ordered_eq]
  unfold cols
  rw [List.filter_filter]
  congr 1
  funext j
  simp [freeCol, List.all_append, Bool.and_comm, bne_comm]

theorem extension_mono_perm (n : Nat) (N : Matching) (a b c d : Nat) :
    ((c*n+d) :: mono n (ordered (N ++ [(a,b)]))).Perm
      ((a*n+b) :: (c*n+d) :: mono n N) := by
  have h := (mono_ordered_perm n (N ++ [(a,b)])).cons (c*n+d)
  simp only [mono, List.map_append, List.map_cons, List.map_nil] at h
  exact h.trans ((List.perm_append_comm).cons _ |>.trans (List.Perm.swap _ _ _))

private theorem cf_map_congr_perm {α : Type} (L : List α)
    (f g : α → List Nat) (u : List Nat) (h : ∀ x, (f x).Perm (g x)) :
    cf (L.map fun x => ((1 : Int), f x)) u =
      cf (L.map fun x => ((1 : Int), g x)) u := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    have he : (f x).Perm u ↔ (g x).Perm u :=
      ⟨fun hh => (h x).symm.trans hh, fun hh => (h x).trans hh⟩
    by_cases hh : (g x).Perm u <;> simp [cf, he, hh] at ih ⊢ <;> exact ih

private theorem cf_flat_congr {α : Type} (L : List α)
    (f g : α → List (Int × List Nat)) (u : List Nat)
    (h : ∀ x, cf (f x) u = cf (g x) u) :
    cf (L.flatMap f) u = cf (L.flatMap g) u := by
  induction L with
  | nil => rfl
  | cons x L ih => simp only [List.flatMap_cons, cf_append, h, ih]

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

theorem rc_top_zero (m n : Nat) (N : Matching) (i j : Nat) (u : List Nat) :
    coeff (top m n (rc m n N i j)) u = 0 := by
  rw [rc, top_append_coeff]
  simp only [top, List.flatMap_map, topLabel, ↓reduceIte, List.map_map,
    Function.comp_def, Int.one_mul, Int.neg_mul, Int.reduceNeg, coeff]
  simp only [cols_extend, rows_extend, Bool.false_eq_true, ↓reduceIte,
    List.map_map, Function.comp_def, Int.reduceNeg]
  have hr := cf_flat_congr ((rows m N).filter (· != i))
    (fun a => ((cols n N).filter (· != j)).map fun b =>
      ((1 : Int), (i*n+b) :: mono n (ordered (N ++ [(a,j)]))))
    (fun a => ((cols n N).filter (· != j)).map fun b =>
      ((1 : Int), (a*n+j) :: (i*n+b) :: mono n N)) u
    (fun a => cf_map_congr_perm _ _ _ u (fun b => extension_mono_perm n N a j i b))
  have hc := cf_flat_congr ((cols n N).filter (· != j))
    (fun b => ((rows m N).filter (· != i)).map fun a =>
      ((1 : Int), (a*n+j) :: mono n (ordered (N ++ [(i,b)]))))
    (fun b => ((rows m N).filter (· != i)).map fun a =>
      ((1 : Int), (a*n+j) :: (i*n+b) :: mono n N)) u
    (fun b => cf_map_congr_perm _ _ _ u (fun a =>
      (extension_mono_perm n N i b a j).trans (List.Perm.swap _ _ _)))
  have hg := cf_grid ((rows m N).filter (· != i)) ((cols n N).filter (· != j))
    (fun a b => (a*n+j) :: (i*n+b) :: mono n N) u
  have hn := cf_negative (((cols n N).filter (· != j)).flatMap fun b =>
    ((rows m N).filter (· != i)).map fun a =>
      ((1 : Int), (a*n+j) :: mono n (ordered (N ++ [(i,b)])))) u
  simp only [List.map_flatMap, List.map_map, Function.comp_def, Int.reduceNeg] at hn
  omega

end Programme.«20261104-1627-proof-complexity».MatchingLabels
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.extension_mono_perm

#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.rc_top_zero
