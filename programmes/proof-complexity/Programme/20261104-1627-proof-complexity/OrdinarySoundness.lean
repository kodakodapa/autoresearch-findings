import Programme.«20261104-1627-proof-complexity».OrderedExtension

namespace Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261029-1156-proof-complexity».StdPC

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


private theorem cf_cons_term (t : Int × List Nat) (L : List (Int × List Nat)) (u : List Nat) :
    cf (t :: L) u = (if t.2.Perm u then t.1 else 0) + cf L u := by
  by_cases h : t.2.Perm u <;> simp [cf, h]

private theorem cf_offdiag (B : List Nat) (f : Nat → Nat → List Nat) (u : List Nat) :
    cf (B.flatMap fun a => (B.filter (· != a)).map fun b => ((1 : Int), f a b)) u =
    cf (B.flatMap fun b => (B.filter (· != b)).map fun a => ((1 : Int), f a b)) u := by
  have grid : ∀ A C : List Nat,
      cf (A.flatMap fun a => (C.filter (· != a)).map fun b => ((1 : Int), f a b)) u =
      cf (C.flatMap fun b => (A.filter (· != b)).map fun a => ((1 : Int), f a b)) u := by
    intro A
    induction A with
    | nil =>
      intro C
      have hz : C.flatMap (fun _ => ([] : List (Int × List Nat))) = [] := by
        induction C <;> simp_all
      simp [hz, cf]
    | cons a A ih =>
      intro C
      simp only [List.flatMap_cons, cf_append]
      rw [ih]
      induction C with
      | nil => simp [cf]
      | cons b C ihC =>
        by_cases h : b = a
        · subst b
          simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true,
            ↓reduceIte, List.map_cons, List.flatMap_cons, cf_append] at ihC ⊢
          omega
        · have h' : a ≠ b := Ne.symm h
          have hb : (b != a) = true := by simpa using h
          have ha : (a != b) = true := by simpa using h'
          simp only [List.filter_cons, hb, ha, ↓reduceIte, List.map_cons,
            List.flatMap_cons, cf_cons_term, cf_append] at ihC ⊢
          omega
  exact grid B B

 theorem rr_top_zero (m n : Nat) (N : Matching) (a b : Nat) (u : List Nat) :
    coeff (top m n (rr n N a b)) u = 0 := by
  rw [rr, top_append_coeff]
  simp only [top, List.flatMap_map, topLabel, Bool.false_eq_true, ↓reduceIte, List.map_map,
    Function.comp_def, Int.one_mul, Int.neg_mul, Int.reduceNeg, coeff,
    cols_extend]
  have hr := cf_flat_congr (cols n N)
    (fun j => ((cols n N).filter (· != j)).map fun k =>
      ((1 : Int), (a*n+k) :: mono n (ordered (N ++ [(b,j)]))))
    (fun j => ((cols n N).filter (· != j)).map fun k =>
      ((1 : Int), (b*n+j) :: (a*n+k) :: mono n N)) u
    (fun j => cf_map_congr_perm _ _ _ u (fun k => extension_mono_perm n N b j a k))
  have hc := cf_flat_congr (cols n N)
    (fun k => ((cols n N).filter (· != k)).map fun j =>
      ((1 : Int), (b*n+j) :: mono n (ordered (N ++ [(a,k)]))))
    (fun k => ((cols n N).filter (· != k)).map fun j =>
      ((1 : Int), (b*n+j) :: (a*n+k) :: mono n N)) u
    (fun k => cf_map_congr_perm _ _ _ u (fun j =>
      (extension_mono_perm n N a k b j).trans (List.Perm.swap _ _ _)))
  have hg := cf_offdiag (cols n N)
    (fun j k => (b*n+j) :: (a*n+k) :: mono n N) u
  have hn := cf_negative ((cols n N).flatMap fun k =>
    ((cols n N).filter (· != k)).map fun j =>
      ((1 : Int), (b*n+j) :: mono n (ordered (N ++ [(a,k)])))) u
  simp only [List.map_flatMap, List.map_map, Function.comp_def, Int.reduceNeg] at hn
  omega
 theorem cc_top_zero (m n : Nat) (N : Matching) (a b : Nat) (u : List Nat) :
    coeff (top m n (cc m N a b)) u = 0 := by
  rw [cc, top_append_coeff]
  simp only [top, List.flatMap_map, topLabel, Bool.false_eq_true, ↓reduceIte, List.map_map,
    Function.comp_def, Int.one_mul, Int.neg_mul, Int.reduceNeg, coeff,
    rows_extend]
  have hr := cf_flat_congr (rows m N)
    (fun j => ((rows m N).filter (· != j)).map fun k =>
      ((1 : Int), (k*n+a) :: mono n (ordered (N ++ [(j,b)]))))
    (fun j => ((rows m N).filter (· != j)).map fun k =>
      ((1 : Int), (j*n+b) :: (k*n+a) :: mono n N)) u
    (fun j => cf_map_congr_perm _ _ _ u (fun k => extension_mono_perm n N j b k a))
  have hc := cf_flat_congr (rows m N)
    (fun k => ((rows m N).filter (· != k)).map fun j =>
      ((1 : Int), (j*n+b) :: mono n (ordered (N ++ [(k,a)]))))
    (fun k => ((rows m N).filter (· != k)).map fun j =>
      ((1 : Int), (j*n+b) :: (k*n+a) :: mono n N)) u
    (fun k => cf_map_congr_perm _ _ _ u (fun j =>
      (extension_mono_perm n N k a j b).trans (List.Perm.swap _ _ _)))
  have hg := cf_offdiag (rows m N)
    (fun j k => (j*n+b) :: (k*n+a) :: mono n N) u
  have hn := cf_negative ((rows m N).flatMap fun k =>
    ((rows m N).filter (· != k)).map fun j =>
      ((1 : Int), (j*n+b) :: mono n (ordered (N ++ [(k,a)])))) u
  simp only [List.map_flatMap, List.map_map, Function.comp_def, Int.reduceNeg] at hn
  omega

theorem rr_kernel {p m n e : Nat} {N : Matching}
    (hN : N ∈ matchings m n e) {a b : Nat}
    (ha : a ∈ rows m N) (hb : b ∈ rows m N) (hne : a ≠ b) :
    Kernel p m n (e+2) (rr n N a b) := by
  refine ⟨rr_valid hN ha hb hne, ?_⟩
  intro u
  rw [rr_top_zero]
  simp [coeff, cf]

theorem cc_kernel {p m n e : Nat} {N : Matching}
    (hN : N ∈ matchings m n e) {a b : Nat}
    (ha : a ∈ cols n N) (hb : b ∈ cols n N) (hne : a ≠ b) :
    Kernel p m n (e+2) (cc m N a b) := by
  refine ⟨cc_valid hN ha hb hne, ?_⟩
  intro u
  rw [cc_top_zero]
  simp [coeff, cf]

end Programme.«20261104-1627-proof-complexity».MatchingLabels
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.rr_top_zero

#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.cc_top_zero
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.rr_kernel
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.cc_kernel
