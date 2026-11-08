import Programme.«20261104-1627-proof-complexity».WeightedColumnTransport
import Programme.«20261104-1627-proof-complexity».AnchoredCancellation

namespace Programme.«20261104-1627-proof-complexity».WeightedTopTransport
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261029-1156-proof-complexity».StdPC
open Programme.«20261025-0459-proof-complexity».OntoLucas (bin)
open Programme.«20261104-1627-proof-complexity».BinomialTails Programme.«20261104-1627-proof-complexity».WeightedTailSums

private theorem cf_bind {α : Type} (L : List α) (f : α → List (Int × List Nat)) (u : List Nat) :
    cf (L.flatMap f) u = (L.map fun x => cf (f x) u).sum := by
  induction L with
  | nil => rfl
  | cons x L ih => simp only [List.flatMap_cons, cf_append, List.map_cons, List.sum_cons, ih]

private theorem cf_cons (a : Int × List Nat) (L : List (Int × List Nat)) (u : List Nat) :
    cf (a::L) u = (if a.2.Perm u then a.1 else 0) + cf L u := by
  by_cases h : a.2.Perm u <;> simp [cf,h]

private theorem cf_map_perm {α : Type} (L : List α) (c : α → Int)
    (f g : α → List Nat) (u : List Nat) (h : ∀ x, (f x).Perm (g x)) :
    cf (L.map fun x => (c x,f x)) u = cf (L.map fun x => (c x,g x)) u := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    have he : (f x).Perm u ↔ (g x).Perm u :=
      ⟨fun hh => (h x).symm.trans hh, fun hh => (h x).trans hh⟩
    simp only [List.map_cons,cf_cons,he,ih]

private theorem extend_perm (n : Nat) (N E : Matching) (i j : Nat) :
    ((i*n+j)::mono n (ordered (N++E))).Perm (mono n (N++(E++[(i,j)]))) := by
  have h : ((i*n+j)::mono n (ordered (N++E))).Perm ((i*n+j)::mono n (N++E)) :=
    (Programme.«20261104-1627-proof-complexity».MatchingLabels.mono_ordered_perm n (N++E)).cons (i*n+j)
  simp only [mono, List.map_append, List.map_cons, List.map_nil] at h ⊢
  have hp : ([i*n+j] ++ (mono n N ++ mono n E)).Perm ((mono n N ++ mono n E) ++ [i*n+j]) := List.perm_append_comm
  simpa [mono, List.append_assoc] using h.trans hp

def rowTerms (m n q : Nat) (N E : Matching) : List (Int × Matching) :=
  ((rows m (N++E)).filter fun i => E.all fun e => e.1 < i).flatMap fun i =>
    (cols n (N++E)).map fun j => ((bin (tailCount (rows m N) i) q : Int),E++[(i,j)])
def colTerms (m n q : Nat) (N E : Matching) : List (Int × Matching) :=
  ((cols n (N++E)).filter fun j => E.all fun e => e.2 < j).flatMap fun j =>
    (rows m (N++E)).map fun i => ((bin (tailCount (cols n N) j) q : Int),ordered (E++[(i,j)]))
def observe (n : Nat) (N : Matching) (a : Int × Matching) : Int × List Nat :=
  (a.1,mono n (N++a.2))

private theorem cf_neg (L : List (Int × List Nat)) (u : List Nat) :
    cf (L.map fun a => (-a.1,a.2)) u = -cf L u := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [List.map_cons,cf_cons,cf_cons,ih]
    split <;> omega

 theorem piece_top (m n q : Nat) (N E : Matching) (u : List Nat) :
    coeff (top m n (piece m n q N E)) u =
    cf ((rowTerms m n q N E).map (observe n N)) u -
    cf ((colTerms m n q N E).map (observe n N)) u := by
  have rows_eq : rows m (ordered (N++E)) = rows m (N++E) := Programme.«20261104-1627-proof-complexity».MatchingLabels.rows_ordered_eq m (N++E)
  have cols_eq : cols n (ordered (N++E)) = cols n (N++E) := Programme.«20261104-1627-proof-complexity».MatchingLabels.cols_ordered_eq n (N++E)
  have hrow (i : Nat) := cf_map_perm (cols n (N++E))
    (fun _ => (bin (tailCount (rows m N) i) q : Int)) _ _ u
    (fun j => extend_perm n N E i j)
  have hcol (j : Nat) := cf_map_perm (rows m (N++E))
    (fun _ => -(bin (tailCount (cols n N) j) q : Int)) _ _ u
    (fun i => (extend_perm n N E i j).trans (by
      simpa only [mono, List.map_append] using
        ((List.Perm.refl (mono n N)).append
          (show (mono n (ordered (E++[(i,j)]))).Perm (mono n (E++[(i,j)])) from
            Programme.«20261104-1627-proof-complexity».MatchingLabels.mono_ordered_perm n (E++[(i,j)]))).symm))
  simp only [piece,top,List.flatMap_append,List.flatMap_map,topLabel,
    Bool.false_eq_true,↓reduceIte,List.map_map,Function.comp_def,Int.mul_one,
    rows_eq,cols_eq,
    coeff,cf_append, rowTerms,colTerms,List.map_flatMap,observe]
  rw [cf_bind,cf_bind,cf_bind,cf_bind]
  simp only [hrow,hcol]
  have hn (j : Nat) := cf_neg
    ((rows m (N++E)).map fun i =>
      ((bin (tailCount (cols n N) j) q : Int),mono n (N++ordered (E++[(i,j)])))) u
  simp only [List.map_map,Function.comp_def] at hn
  simp only [mono,List.map_append] at hn ⊢
  simp only [hn]
  have hs (L : List Nat) (f : Nat → Int) : (L.map fun j => -f j).sum = -(L.map f).sum := by
    induction L with
    | nil => rfl
    | cons a L ih => simp only [List.map_cons,List.sum_cons,ih]; omega
  rw [hs]
  omega

private theorem cf_of_perm {L K : List (Int × List Nat)} (h : L.Perm K) (u : List Nat) :
    cf L u = cf K u := by
  have hp := ((h.filter (fun t => decide (t.2.Perm u))).map Prod.fst)
  have hs {a b : List Int} (hp : a.Perm b) : a.sum = b.sum := by
    induction hp with
    | nil => rfl
    | cons x hp ih => simp only [List.sum_cons,ih]
    | swap x y l => simp only [List.sum_cons]; omega
    | trans hp hq ih ij => exact ih.trans ij
  exact hs hp

private theorem sum_sub {α : Type} (L : List α) (f g : α → Int) :
    (L.map fun a => f a-g a).sum = (L.map f).sum - (L.map g).sum := by
  induction L with
  | nil => rfl
  | cons a L ih => simp only [List.map_cons,List.sum_cons,ih]; omega

private theorem cf_difference {α : Type} (L : List α) (a b : α → Int)
    (f : α → List Nat) (u : List Nat) :
    cf (L.map fun x => (a x-b x,f x)) u =
      cf (L.map fun x => (a x,f x)) u - cf (L.map fun x => (b x,f x)) u := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    simp only [List.map_cons,cf_cons,ih]
    split <;> omega

/-- Exact adjacent-level top transport, for every board, anchor and weight. -/
theorem layer_top (m n r q : Nat) (N : Matching) (u : List Nat) :
    coeff (top m n (layer m n r (q+1) N)) u =
      coeff (incomingPoly m n (r+1) q N) u := by
  let L := Programme.«20261104-1627-proof-complexity».AnchoredWeights.compatible m n r N
  let K := Programme.«20261104-1627-proof-complexity».AnchoredWeights.compatible m n (r+1) N
  let a := fun F : Matching => (bin (((rows m (N++F)).filter
    (fun i => F.all (fun e => e.1 < i))).length) (q+1) : Int)
  let b := fun F : Matching => (bin (((cols n (N++F)).filter
    (fun j => F.all (fun e => e.2 < j))).length) (q+1) : Int)
  have hr := congrArg (fun T : List (Int × Matching) => cf (T.map (observe n N)) u)
    (Programme.«20261104-1627-proof-complexity».WeightedRowTransport.weighted_row_enumeration m n r (q+1) N)
  have hc := cf_of_perm
    ((Programme.«20261104-1627-proof-complexity».WeightedColumnTransport.weighted_col_enumeration m n r (q+1) N).map (observe n N)) u
  change cf ((L.flatMap (rowTerms m n (q+1) N)).map (observe n N)) u =
    cf ((K.map fun F => (a F,F)).map (observe n N)) u at hr
  change cf ((L.flatMap (colTerms m n (q+1) N)).map (observe n N)) u =
    cf ((K.map fun F => (b F,F)).map (observe n N)) u at hc
  simp only [List.map_flatMap,cf_bind,List.map_map,Function.comp_def,observe] at hr hc
  have ht : coeff (top m n (L.flatMap (piece m n (q+1) N))) u =
      (L.map fun E => coeff (top m n (piece m n (q+1) N E)) u).sum := by
    induction L with
    | nil => rfl
    | cons E L ih =>
      have ha (v w : Vector) : coeff (top m n (v++w)) u =
          coeff (top m n v) u + coeff (top m n w) u := by
        simp only [top,List.flatMap_append,coeff,cf_append]
      simp only [List.flatMap_cons,ha,List.map_cons,List.sum_cons,ih]
  change coeff (top m n (L.flatMap (piece m n (q+1) N))) u = _
  rw [ht]
  simp only [piece_top]
  rw [sum_sub]
  rw [hr,hc]
  exact (cf_difference K a b (fun F => mono n (N++F)) u).symm

end Programme.«20261104-1627-proof-complexity».WeightedTopTransport
#print axioms Programme.«20261104-1627-proof-complexity».WeightedTopTransport.piece_top

#print axioms Programme.«20261104-1627-proof-complexity».WeightedTopTransport.layer_top
