import Programme.«20261104-1627-proof-complexity».LprimeResidueLift

/-! Integer aggregation and matrix image, using peer matching-enumeration uniqueness.
No field duality or Lprime theorem is asserted. -/
namespace Programme.«20261104-1627-proof-complexity».LprimeStages
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261029-1156-proof-complexity».StdPC

private theorem sum_zero (L : List Label) : (L.map fun _ => (0 : Int)).sum = 0 := by
  induction L with
  | nil => rfl
  | cons x xs ih => simpa using ih

private theorem sum_add (L : List Label) (f g : Label → Int) :
    (L.map fun x => f x + g x).sum = (L.map f).sum + (L.map g).sum := by
  induction L with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons]; rw [ih]; omega

private theorem sum_delta (L : List Label) (hL : L.Nodup)
    (g : Label) (hg : g ∈ L) (z : Int) (w : Label → Int) :
    (L.map fun h => (if g = h then z else 0) * w h).sum = z * w g := by
  induction L with
  | nil => simp at hg
  | cons h hs ih =>
    have hd := List.nodup_cons.mp hL
    by_cases he : g = h
    · subst g
      have hz : (hs.map fun x => (if h = x then z else 0) * w x).sum = 0 := by
        have : ∀ x ∈ hs, (if h = x then z else 0) * w x = 0 := by
          intro x hx
          have hn : h ≠ x := fun he => hd.1 (he ▸ hx)
          simp [hn]
        have he : (hs.map fun x => (if h = x then z else 0) * w x) = hs.map (fun _ => (0 : Int)) := by
          apply List.map_congr_left
          exact this
        rw [he, sum_zero]
      simp [hz]
    · have hg' : g ∈ hs := (List.mem_cons.mp hg).resolve_left he
      simp only [List.map_cons, List.sum_cons, ite_eq_right he, Int.zero_mul, Int.zero_add]
      exact ih hd.2 hg'

/-- Group any supported raw list over a duplicate-free list of labels. -/
theorem grouped_sum (L : List Label) (hL : L.Nodup)
    (a : Vector) (ha : ∀ t ∈ a, t.2 ∈ L) (w : Label → Int) :
    (a.map fun t => t.1 * w t.2).sum =
      (L.map fun g => aggregate a g * w g).sum := by
  induction a with
  | nil => simp [aggregate, sum_zero]
  | cons t ts ih =>
    have ht := ha t List.mem_cons_self
    have hs := ih (fun s h => ha s (List.mem_cons_of_mem t h))
    simp only [List.map_cons, List.sum_cons]
    have he : (L.map fun g => aggregate (t :: ts) g * w g) =
        L.map (fun g => (if t.2 = g then t.1 else 0) * w g + aggregate ts g * w g) := by
      apply List.map_congr_left
      intro g hg
      rw [aggregate_cons, Int.add_mul]
    rw [he, sum_add, sum_delta L hL t.2 ht t.1 w, hs]

private theorem scaled_coeff (a : Int) (L : List (Int × List Nat)) (u : List Nat) :
    cf (L.map fun b => (a*b.1,b.2)) u = a * cf L u := by
  induction L with
  | nil => simp [cf]
  | cons b L ih =>
    by_cases h : b.2.Perm u <;> simp [cf, h] at ih ⊢ <;> simp_all [Int.mul_add]

/-- The ordinary polynomial top map is linear in raw entries. -/
theorem top_coeff_sum (m n : Nat) (a : Vector) (u : List Nat) :
    coeff (top m n a) u =
      (a.map fun t => t.1 * coeff (topLabel m n t.2) u).sum := by
  induction a with
  | nil => simp [top, coeff, cf]
  | cons t ts ih =>
    have he : coeff (top m n (t::ts)) u =
        t.1 * coeff (topLabel m n t.2) u + coeff (top m n ts) u := by
      change cf (_ ++ _) _ = _
      rw [cf_append, scaled_coeff]
      rfl
    simpa only [List.map_cons, List.sum_cons, ih] using he

/-- The remaining concrete premise is precisely label-enumeration Nodup. -/
theorem aggregation_of_nodup (m n d : Nat) (hL : (labels m n d).Nodup) :
    AggregationObligation m n d := by
  intro a M
  unfold topCoordinates matrixCoordinates entry
  rw [top_coeff_sum]
  have he := grouped_sum (labels m n d) hL a.val a.property
    (fun g => coeff (topLabel m n g) (mono n M.val))
  simpa using he

theorem matrixImage_of_nodup (p m n d : Nat) (hL : (labels m n d).Nodup) :
    MatrixImageObligation p m n d :=
  matrixImage_of_aggregation p m n d (aggregation_of_nodup m n d hL)

private def blockLabels (m n : Nat) (M : Matching) : List Label :=
  (rows m M).map (fun i => ⟨M,true,i⟩) ++
    (cols n M).map (fun j => ⟨M,false,j⟩)

private theorem block_base {m n : Nat} {M : Matching} {g : Label}
    (hg : g ∈ blockLabels m n M) : g.base = M := by
  rcases List.mem_append.mp hg with hr | hc
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr
    rfl
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hc
    rfl

private theorem block_nodup (m n : Nat) (M : Matching) :
    (blockLabels m n M).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨?_, ?_, ?_⟩
  · apply (List.nodup_range.filter (freeRow M)).map
    intro a b hab he
    exact hab (congrArg Label.mark he)
  · apply (List.nodup_range.filter (freeCol M)).map
    intro a b hab he
    exact hab (congrArg Label.mark he)
  · intro x hx y hy he
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hy
    have hf := congrArg Label.isRow he
    contradiction

private theorem blocks_nodup (m n : Nat) (L : List Matching) (hL : L.Nodup) :
    (L.flatMap (blockLabels m n)).Nodup := by
  induction L with
  | nil => simp
  | cons M Ms ih =>
    have hd := List.nodup_cons.mp hL
    rw [List.flatMap_cons, List.nodup_append]
    refine ⟨block_nodup m n M, ih hd.2, ?_⟩
    intro x hx y hy he
    obtain ⟨N,hN,hy⟩ := List.mem_flatMap.mp hy
    have hb : M = N := (block_base hx).symm.trans ((congrArg Label.base he).trans (block_base hy))
    exact hd.1 (hb ▸ hN)

/-- Uses the peer's matching-enumeration uniqueness theorem. -/
theorem labels_nodup (m n d : Nat) : (labels m n d).Nodup := by
  unfold labels
  split
  · simp
  · exact blocks_nodup m n (matchings m n (d-1)) (matchings_nodup m n (d-1))

theorem aggregation (m n d : Nat) : AggregationObligation m n d :=
  aggregation_of_nodup m n d (labels_nodup m n d)

theorem matrixImage (p m n d : Nat) : MatrixImageObligation p m n d :=
  matrixImage_of_nodup p m n d (labels_nodup m n d)

end Programme.«20261104-1627-proof-complexity».LprimeStages
#print axioms Programme.«20261104-1627-proof-complexity».LprimeStages.grouped_sum
#print axioms Programme.«20261104-1627-proof-complexity».LprimeStages.aggregation_of_nodup
#print axioms Programme.«20261104-1627-proof-complexity».LprimeStages.matrixImage_of_nodup

#print axioms Programme.«20261104-1627-proof-complexity».LprimeStages.labels_nodup
#print axioms Programme.«20261104-1627-proof-complexity».LprimeStages.aggregation
#print axioms Programme.«20261104-1627-proof-complexity».LprimeStages.matrixImage
