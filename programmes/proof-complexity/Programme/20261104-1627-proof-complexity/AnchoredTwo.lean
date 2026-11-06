import Programme.«20261104-1627-proof-complexity».AnchoredWeights
import Programme.«20261104-1627-proof-complexity».AnchoredRhoOne
import Programme.«20261027-0607-proof-complexity».Lucas
import Programme.«20261104-1627-proof-complexity».DegreeTwoLabels

namespace Programme.«20261104-1627-proof-complexity».AnchoredTwo
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261029-1156-proof-complexity».StdPC
open Programme.«20261104-1627-proof-complexity».AnchoredWeights

def upper (L : List Nat) (i : Nat) : Int := (L.filter (fun j => i < j)).length

theorem singleton_weight (m n : Nat) (N : Matching) (i j : Nat) :
    weight m n N [(i,j)] = upper (rows m N) i - upper (cols n N) j := by
  have hr : (rows m (N ++ [(i,j)])).filter (fun a => [(i,j)].all fun e => e.1 < a) =
      (rows m N).filter (fun a => i < a) := by
    unfold rows
    rw [List.filter_filter, List.filter_filter]
    congr 1
    funext a
    by_cases h : i < a
    · have hn : i ≠ a := by omega
      simp [freeRow, List.all_append, h, hn]
    · simp [freeRow, List.all_append, h]
  have hc : (cols n (N ++ [(i,j)])).filter (fun a => [(i,j)].all fun e => e.2 < a) =
      (cols n N).filter (fun a => j < a) := by
    unfold cols
    rw [List.filter_filter, List.filter_filter]
    congr 1
    funext a
    by_cases h : j < a
    · have hn : j ≠ a := by omega
      simp [freeCol, List.all_append, h, hn]
    · simp [freeCol, List.all_append, h]
  unfold weight
  rw [hr, hc]
  rfl

theorem compatible_one (m n : Nat) (N : Matching) :
    compatible m n 1 N = (rows m N).flatMap fun i => (cols n N).map fun j => [(i,j)] := by
  unfold compatible
  rw [matchings_one, List.filter_flatMap]
  unfold rows cols
  generalize List.range m = A
  induction A with
  | nil => simp
  | cons i A ih =>
    simp only [List.flatMap_cons, List.filter_cons]
    rw [List.filter_map]
    by_cases h : freeRow N i = true
    · simp [h, ih, Function.comp_def]
    · have hf : freeRow N i = false := Bool.eq_false_iff.mpr h
      simp [hf, ih]

/-- Concrete proposed t=2 certificate, on the unextended anchor. -/
def witness (m n : Nat) (N : Matching) : Vector :=
  (rows m N).map (fun i => (upper (rows m N) i, ⟨N,true,i⟩)) ++
  (cols n N).map (fun j => (-upper (cols n N) j, ⟨N,false,j⟩))

theorem witness_valid {m n s : Nat} {N : Matching}
    (hN : N ∈ matchings m n s) : valid m n (s+1) (witness m n N) := by
  intro a ha
  have hm : N ∈ matchings m n (s+1-1) := by simpa using hN
  have he : labels m n (s+1) = (matchings m n s).flatMap (fun M =>
      (rows m M).map (fun i => (⟨M,true,i⟩ : Label)) ++
      (cols n M).map (fun j => (⟨M,false,j⟩ : Label))) := by simp [labels]
  rw [he]
  apply List.mem_flatMap.mpr
  refine ⟨N,hN,?_⟩
  rcases List.mem_append.mp ha with h | h
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp h
    exact List.mem_append_left _ (List.mem_map.mpr ⟨i,hi,rfl⟩)
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp h
    exact List.mem_append_right _ (List.mem_map.mpr ⟨j,hj,rfl⟩)

private theorem cf_cons (a : Int × List Nat) (L : List (Int × List Nat)) (u : List Nat) :
    cf (a :: L) u = (if a.2.Perm u then a.1 else 0) + cf L u := by
  by_cases h : a.2.Perm u <;> simp [cf,h]

private theorem cf_grid (A B : List Nat) (f : Nat → Nat → Int × List Nat) (u : List Nat) :
    cf (A.flatMap fun a => B.map fun b => f a b) u =
      cf (B.flatMap fun b => A.map fun a => f a b) u := by
  have split (g : Nat → Int × List Nat) (h : Nat → List (Int × List Nat)) :
      cf (B.flatMap fun b => g b :: h b) u =
        cf (B.map g) u + cf (B.flatMap h) u := by
    induction B with
    | nil => simp [cf]
    | cons b B ih =>
      simp only [List.flatMap_cons, List.map_cons, List.cons_append, cf_append, cf_cons] at *
      omega
  induction A with
  | nil =>
    have hz : B.flatMap (fun _ => ([] : List (Int × List Nat))) = [] := by
      induction B <;> simp_all
    simp [hz,cf]
  | cons a A ih =>
    simp only [List.flatMap_cons, List.map_cons, cf_append]
    rw [split, ih]

private theorem cf_map_perm {α : Type} (L : List α) (c : α → Int)
    (f g : α → List Nat) (u : List Nat) (h : ∀ a, (f a).Perm (g a)) :
    cf (L.map fun a => (c a,f a)) u = cf (L.map fun a => (c a,g a)) u := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    have he : (f a).Perm u ↔ (g a).Perm u :=
      ⟨fun hh => (h a).symm.trans hh, fun hh => (h a).trans hh⟩
    simp only [List.map_cons, cf_cons, he, ih]

private theorem cf_flat {α : Type} (L : List α)
    (f g : α → List (Int × List Nat)) (u : List Nat)
    (h : ∀ a, cf (f a) u = cf (g a) u) :
    cf (L.flatMap f) u = cf (L.flatMap g) u := by
  induction L with
  | nil => rfl
  | cons a L ih => simp only [List.flatMap_cons, cf_append, h, ih]

private theorem cf_sub_grid (A B : List Nat) (a b : Nat → Int)
    (f : Nat → Nat → List Nat) (u : List Nat) :
    cf (A.flatMap fun i => B.map fun j => (a i - b j, f i j)) u =
      cf (A.flatMap fun i => B.map fun j => (a i, f i j)) u +
      cf (A.flatMap fun i => B.map fun j => (-b j, f i j)) u := by
  induction A with
  | nil => simp [cf]
  | cons i A ih =>
    simp only [List.flatMap_cons, cf_append]
    have hs : cf (B.map fun j => (a i-b j,f i j)) u =
        cf (B.map fun j => (a i,f i j)) u + cf (B.map fun j => (-b j,f i j)) u := by
      clear ih
      induction B with
      | nil => simp [cf]
      | cons j B ihB =>
        simp only [List.map_cons, cf_cons]
        by_cases hh : (f i j).Perm u <;> simp only [hh, ite_true, ite_false] <;> omega
    rw [hs,ih]
    omega

theorem witness_top (m n : Nat) (N : Matching) (u : List Nat) :
    coeff (top m n (witness m n N)) u = coeff (weighted m n 2 N) u := by
  have hw : (weighted m n 2 N).terms =
      (rows m N).flatMap fun i => (cols n N).map fun j =>
        (upper (rows m N) i - upper (cols n N) j, mono n (N ++ [(i,j)])) := by
    change ((compatible m n (2-1) N).map _ ) = _
    rw [show 2-1=1 by rfl, compatible_one, List.map_flatMap]
    simp only [List.map_map, Function.comp_def, singleton_weight]
  rw [show coeff (weighted m n 2 N) u = cf (weighted m n 2 N).terms u by rfl,hw]
  rw [cf_sub_grid]
  have hr := cf_flat (rows m N)
    (fun i => (cols n N).map fun j => (upper (rows m N) i, (i*n+j)::mono n N))
    (fun i => (cols n N).map fun j => (upper (rows m N) i, mono n (N++[(i,j)]))) u
    (fun i => cf_map_perm _ _ _ _ u (fun j => by
      simp only [mono, List.map_append, List.map_cons, List.map_nil]
      simpa only [List.singleton_append, mono] using (List.perm_append_comm (l₁ := [i*n+j]) (l₂ := mono n N))))
  have hc := cf_flat (cols n N)
    (fun j => (rows m N).map fun i => (-upper (cols n N) j, (i*n+j)::mono n N))
    (fun j => (rows m N).map fun i => (-upper (cols n N) j, mono n (N++[(i,j)]))) u
    (fun j => cf_map_perm _ _ _ _ u (fun i => by
      simp only [mono, List.map_append, List.map_cons, List.map_nil]
      simpa only [List.singleton_append, mono] using (List.perm_append_comm (l₁ := [i*n+j]) (l₂ := mono n N))))
  have hg := cf_grid (rows m N) (cols n N)
    (fun i j => (-upper (cols n N) j, mono n (N++[(i,j)]))) u
  simp only [witness, top, List.flatMap_append, List.flatMap_map, topLabel,
    Bool.false_eq_true, ↓reduceIte, List.map_map, Function.comp_def, Int.mul_one,
    coeff, cf_append]
  rw [hr,hc,hg]


open Programme.«20261025-0459-proof-complexity».OntoLucas (bin bin_zero)
open Programme.«20261027-0607-proof-complexity».Lucas (bin_succ)

private theorem bin_one (n : Nat) : bin n 1 = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [bin_succ,bin_zero,ih]; omega

theorem upper_sum (L : List Nat) (hL : L.Pairwise (· < ·)) :
    (L.map (upper L)).sum = (bin L.length 2 : Int) := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    have hh := List.pairwise_cons.mp hL
    have hf : L.filter (fun j => a < j) = L := List.filter_eq_self.mpr (by
      intro j hj
      simpa using hh.1 j hj)
    have he (j : Nat) (hj : j ∈ L) : upper (a::L) j = upper L j := by
      have hn : ¬j < a := by have := hh.1 j hj; omega
      simp [upper,hn]
    have hm : L.map (upper (a::L)) = L.map (upper L) := List.map_congr_left he
    simp only [List.map_cons, List.sum_cons]
    rw [hm, ih hh.2]
    have hu : upper (a::L) a = (L.length : Int) := by simp [upper,hf]
    rw [hu]
    simp only [List.length_cons, bin_succ, bin_one, Int.natCast_add, Nat.reduceAdd]

private theorem cf_repeated (L : List Nat) (c : Nat → Int) (v u : List Nat) :
    cf (L.map fun i => (c i,v)) u = if v.Perm u then (L.map c).sum else 0 := by
  induction L with
  | nil => simp [cf]
  | cons i L ih =>
    simp only [List.map_cons, List.sum_cons, cf_cons]
    by_cases h : v.Perm u <;> simp [h,ih]

private theorem sum_neg (L : List Int) : (L.map Neg.neg).sum = -L.sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons,List.sum_cons,ih]; omega

theorem witness_rho {m n s : Nat} {N : Matching}
    (hN : N ∈ matchings m n s) (u : List Nat) :
    coeff (rho n (witness m n N)) u =
      if (mono n N).Perm u then (bin (m-s) 2 : Int) - bin (n-s) 2 else 0 := by
  have hr := upper_sum (rows m N) (List.pairwise_lt_range.filter _)
  have hc := upper_sum (cols n N) (List.pairwise_lt_range.filter _)
  have hl := Programme.«20261104-1627-proof-complexity».AnchoredRhoOne.free_coordinates_length hN
  have hrl : (rows m N).length = m-s := by omega
  have hcl : (cols n N).length = n-s := by omega
  rw [hrl] at hr
  rw [hcl] at hc
  simp only [witness,rho,List.map_append,List.map_map,Function.comp_def,coeff,cf_append]
  rw [cf_repeated,cf_repeated]
  have hn : ((cols n N).map (fun j => -upper (cols n N) j)).sum =
      -((cols n N).map (upper (cols n N))).sum := by
    simpa only [List.map_map,Function.comp_def] using sum_neg ((cols n N).map (upper (cols n N)))
  by_cases h : (mono n N).Perm u <;> simp [h,hn,hr,hc,Int.sub_eq_add_neg]


/-- A bounded relation witness proves the anchored identity at t=2. -/
theorem anchored_identity_two {p m n s : Nat} {N : Matching}
    (hN : N ∈ matchings m n s) :
    W p m n (s+1) ((rho n (z m n 2 N)).sub
      ⟨[((bin (m-s) 2 : Int) - bin (n-s) 2, mono n N)]⟩) := by
  refine ⟨witness m n N, ?_, ?_⟩
  · intro a ha
    exact ⟨s+1,Nat.le_refl _,witness_valid hN a ha⟩
  · intro u
    have ht := witness_top m n N u
    have hr := witness_rho hN u
    have hz := rho_weighted_coeff m n 2 N u
    have he := relations_coeff m n (witness m n N) u
    change (p : Int) ∣ coeff ((rho n (z m n 2 N)).sub
      ⟨[((bin (m-s) 2 : Int) - bin (n-s) 2, mono n N)]⟩) u -
      coeff (relations m n (witness m n N)) u
    rw [he,ht,hr]
    simp only [Poly.sub, coeff, cf_append, List.map_cons, List.map_nil]
    change (p : Int) ∣ cf (rho n (z m n 2 N)).terms u +
      cf [(-((bin (m-s) 2 : Int) - bin (n-s) 2),mono n N)] u -
      (cf (weighted m n 2 N).terms u -
        if (mono n N).Perm u then (bin (m-s) 2 : Int)-bin (n-s) 2 else 0)
    change cf (rho n (z m n 2 N)).terms u = cf (weighted m n 2 N).terms u at hz
    rw [hz]
    have cancel (a b : Int) : a + -b - (a-b) = 0 := by omega
    by_cases h : (mono n N).Perm u <;> simp [cf,h,cancel]



end Programme.«20261104-1627-proof-complexity».AnchoredTwo
#print axioms Programme.«20261104-1627-proof-complexity».AnchoredTwo.singleton_weight
#print axioms Programme.«20261104-1627-proof-complexity».AnchoredTwo.compatible_one
#print axioms Programme.«20261104-1627-proof-complexity».AnchoredTwo.witness_valid

#print axioms Programme.«20261104-1627-proof-complexity».AnchoredTwo.witness_top
#print axioms Programme.«20261104-1627-proof-complexity».AnchoredTwo.upper_sum
#print axioms Programme.«20261104-1627-proof-complexity».AnchoredTwo.witness_rho
#print axioms Programme.«20261104-1627-proof-complexity».AnchoredTwo.anchored_identity_two
