import Programme.«20261104-1627-proof-complexity».ColumnMultiplicity
import Programme.«20261104-1627-proof-complexity».AnchoredRowEnumeration

namespace Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261029-1156-proof-complexity».StdPC

private theorem cf_bind_congr {α : Type} (L : List α)
    (f g : α → List (Int × List Nat)) (u : List Nat)
    (h : ∀ x, cf (f x) u = cf (g x) u) :
    cf (L.flatMap f) u = cf (L.flatMap g) u := by
  induction L with
  | nil => rfl
  | cons x L ih => simp only [List.flatMap_cons, cf_append, h, ih]

private theorem cf_map_perm {α : Type} (L : List α) (c : Int)
    (f g : α → List Nat) (u : List Nat) (h : ∀ x, (f x).Perm (g x)) :
    cf (L.map fun x => (c,f x)) u = cf (L.map fun x => (c,g x)) u := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    have he : (f x).Perm u ↔ (g x).Perm u :=
      ⟨fun hh => (h x).symm.trans hh, fun hh => (h x).trans hh⟩
    by_cases hh : (g x).Perm u <;> simp [cf, he, hh] at ih ⊢ <;> exact ih

private theorem extend_anchor_perm (n : Nat) (N E : Matching) (i j : Nat) :
    ((i*n+j)::mono n (ordered (N++E))).Perm (mono n (N++(E++[(i,j)]))) := by
  have h := (mono_ordered_perm n (N++E)).cons (i*n+j)
  simp only [mono, List.map_append, List.map_cons, List.map_nil] at h ⊢
  have hp : ([i*n+j] ++ (mono n N ++ mono n E)).Perm ((mono n N ++ mono n E) ++ [i*n+j]) := List.perm_append_comm
  simpa [mono, List.append_assoc] using h.trans hp

private theorem cf_negate (L : List (Int × List Nat)) (u : List Nat) :
    cf (L.map fun t => (-t.1,t.2)) u = -cf L u := by
  induction L with
  | nil => rfl
  | cons t L ih =>
    by_cases h : t.2.Perm u <;> simp [cf, h] at ih ⊢ <;> omega

private theorem z_piece (m n : Nat) (N E : Matching) (u : List Nat) :
    coeff (top m n (
      ((rows m (N++E)).filter fun i => E.all fun e => e.1 < i).map
        (fun i => (1,⟨ordered (N++E),true,i⟩)) ++
      ((cols n (N++E)).filter fun j => E.all fun e => e.2 < j).map
        (fun j => (-1,⟨ordered (N++E),false,j⟩)))) u =
    cf ((((rows m (N++E)).filter fun i => E.all fun e => e.1 < i).flatMap
      fun i => (cols n (N++E)).map fun j => E++[(i,j)]).map
        fun F => ((1 : Int), mono n (N++F))) u -
    cf ((((cols n (N++E)).filter fun j => E.all fun e => e.2 < j).flatMap
      fun j => (rows m (N++E)).map fun i => ordered (E++[(i,j)])).map
        fun F => ((1 : Int), mono n (N++F))) u := by
  rw [top_append_coeff]
  simp only [top, List.flatMap_map, topLabel, ↓reduceIte, List.map_map,
    Function.comp_def, Int.one_mul, Int.neg_mul, Int.reduceNeg, coeff,
    rows_ordered_eq, cols_ordered_eq, List.map_flatMap, Bool.false_eq_true]
  have hr := cf_bind_congr ((rows m (N++E)).filter fun i => E.all fun e => e.1 < i)
    _ _ u (fun i => cf_map_perm (cols n (N++E)) 1 _ _ u
      (fun j => extend_anchor_perm n N E i j))
  have hc := cf_bind_congr ((cols n (N++E)).filter fun j => E.all fun e => e.2 < j)
    _ _ u (fun j => cf_map_perm (rows m (N++E)) (-1) _ _ u
      (fun i => (extend_anchor_perm n N E i j).trans (by
        simpa only [mono, List.map_append] using
          ((List.Perm.refl (mono n N)).append (mono_ordered_perm n (E++[(i,j)]))).symm)))
  have hn := cf_negate ((((cols n (N++E)).filter fun j => E.all fun e => e.2 < j).flatMap
    fun j => (rows m (N++E)).map fun i => ((1 : Int),mono n (N++ordered (E++[(i,j)]))))) u
  simp only [List.map_flatMap, List.map_map, Function.comp_def, Int.reduceNeg] at hn
  simp only [mono, List.map_append] at hr hc hn ⊢
  omega

private theorem top_bind_coeff {α : Type} (L : List α) (f : α → Vector)
    (m n : Nat) (u : List Nat) :
    coeff (top m n (L.flatMap f)) u =
      (L.map fun x => coeff (top m n (f x)) u).sum := by
  induction L with
  | nil => rfl
  | cons x L ih => simp only [List.flatMap_cons, top_append_coeff, List.map_cons, List.sum_cons, ih]

private theorem cf_bind_sum {α : Type} (L : List α) (f : α → List (Int × List Nat))
    (u : List Nat) : cf (L.flatMap f) u = (L.map fun x => cf (f x) u).sum := by
  induction L with
  | nil => rfl
  | cons x L ih => simp only [List.flatMap_cons, cf_append, List.map_cons, List.sum_cons, ih]

private theorem cf_of_perm {L K : List (Int × List Nat)} (h : L.Perm K) (u : List Nat) :
    cf L u = cf K u := by
  have hp : ((L.filter fun t => decide (t.2.Perm u)).map Prod.fst).Perm
      ((K.filter fun t => decide (t.2.Perm u)).map Prod.fst) := (h.filter _).map _
  have hs : ∀ {a b : List Int}, a.Perm b → a.sum = b.sum := by
    intro a b hp
    induction hp with
    | nil => rfl
    | cons x hp ih => simp only [List.sum_cons, ih]
    | swap x y l => simp only [List.sum_cons]; omega
    | trans hp hq ih ij => exact ih.trans ij
  exact hs hp

theorem z_top_zero (m n t : Nat) (N : Matching) (u : List Nat) :
    coeff (top m n (z m n (t+1) N)) u = 0 := by
  let L := (matchings m n t).filter (compatible N)
  let R := fun E : Matching =>
    ((rows m (N++E)).filter fun i => E.all fun e => e.1 < i).flatMap
      fun i => (cols n (N++E)).map fun j => E++[(i,j)]
  let C := fun E : Matching =>
    ((cols n (N++E)).filter fun j => E.all fun e => e.2 < j).flatMap
      fun j => (rows m (N++E)).map fun i => ordered (E++[(i,j)])
  let f := fun F : Matching => ((1 : Int),mono n (N++F))
  have he : (L.flatMap R).Perm (L.flatMap C) := by
    change (L.flatMap R).Perm (columnExtensions m n t N)
    rw [show L.flatMap R = (matchings m n (t+1)).filter (compatible N) from
      anchored_row_enumeration m n t N]
    exact (anchored_column_enumeration m n t N).symm
  have hc := cf_of_perm (he.map f) u
  rw [List.map_flatMap, List.map_flatMap, cf_bind_sum, cf_bind_sum] at hc
  unfold z
  simp only [Nat.add_sub_cancel]
  rw [top_bind_coeff]
  have hz : ∀ E : Matching,
      coeff (top m n (
        ((rows m (N++E)).filter fun i => E.all fun e => e.1 < i).map
          (fun i => (1,⟨ordered (N++E),true,i⟩)) ++
        ((cols n (N++E)).filter fun j => E.all fun e => e.2 < j).map
          (fun j => (-1,⟨ordered (N++E),false,j⟩)))) u =
      cf ((R E).map f) u - cf ((C E).map f) u := fun E => z_piece m n N E u
  simp only [hz]
  change (L.map fun E => cf ((R E).map f) u - cf ((C E).map f) u).sum = 0
  have hs : ∀ (B : List Matching),
      (B.map fun E => cf ((R E).map f) u - cf ((C E).map f) u).sum =
      (B.map fun E => cf ((R E).map f) u).sum -
      (B.map fun E => cf ((C E).map f) u).sum := by
    intro B
    induction B with
    | nil => rfl
    | cons E B ih => simp only [List.map_cons, List.sum_cons, ih]; omega
  rw [hs, hc, Int.sub_self]

end Programme.«20261104-1627-proof-complexity».MatchingLabels
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.z_top_zero

