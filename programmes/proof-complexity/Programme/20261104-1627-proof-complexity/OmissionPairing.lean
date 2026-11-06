import Programme.«20261104-1627-proof-complexity».OmissionCoverage

namespace Programme.«20261104-1627-proof-complexity».MatchingLabels

private theorem nodup_bind {α β : Type} (l : List α) (f : α → List β)
    (hl : l.Nodup) (hf : ∀ a ∈ l, (f a).Nodup)
    (sep : ∀ a ∈ l, ∀ b ∈ l, ∀ x ∈ f a, ∀ y ∈ f b, x = y → a = b) :
    (l.flatMap f).Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    rw [List.flatMap_cons, List.nodup_append]
    refine ⟨hf a (by simp), ih hl.2 (by intro b hb; exact hf b (by simp [hb]))
      (by intro b hb c hc x hx y hy he; exact sep b (by simp [hb]) c (by simp [hc]) x hx y hy he), ?_⟩
    intro x hx y hy he
    obtain ⟨b, hb, hy⟩ := List.mem_flatMap.mp hy
    have hab := sep a (by simp) b (by simp [hb]) x hx y hy he
    subst b
    exact hl.1 hb

private theorem nodup_map_inj {α β : Type} (l : List α) (f : α → β)
    (hl : l.Nodup) (hf : Function.Injective f) : (l.map f).Nodup := by
  exact hl.map f (by intro a b hab he; exact hab (hf he))

theorem matchings_nodup (m n d : Nat) : (matchings m n d).Nodup := by
  induction d with
  | zero => simp [matchings]
  | succ d ih =>
    unfold matchings
    apply nodup_bind _ _ ih
    · intro M hM
      apply nodup_bind _ _
        (((List.nodup_range).filter _).filter _)
      · intro i hi
        apply nodup_map_inj _ _ (List.nodup_range.filter _)
        intro j k he
        have ht := List.append_inj_right' he (by simp)
        simpa using ht
      · intro i hi k hk x hx y hy he
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
        obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hy
        have ht := List.append_inj_right' he (by simp)
        have hp : (i,j) = (k,l) := by simpa using ht
        exact congrArg Prod.fst hp
    · intro M hM N hN x hx y hy he
      obtain ⟨i, hi, hx⟩ := List.mem_flatMap.mp hx
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
      obtain ⟨a, ha, hy⟩ := List.mem_flatMap.mp hy
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hy
      exact List.append_inj_left' he (by simp)


theorem omission_enumeration_perm (m n d h : Nat) (hh : h ≤ n) :
    ((matchings m n d).map (pushMatching h)).Perm
      ((matchings m (n+1) d).filter (fun M => M.all (fun e => e.2 != h))) := by
  apply (List.perm_ext_iff_of_nodup
    (nodup_map_inj _ _ (matchings_nodup m n d) (pushMatching_injective h))
    ((matchings_nodup m (n+1) d).filter _)).mpr
  intro M
  simp only [List.mem_map, List.mem_filter, List.all_eq_true, bne_iff_ne]
  constructor
  · rintro ⟨N, hN, rfl⟩
    refine ⟨matching_push_mem h N hN, ?_⟩
    intro e he
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
    exact omitHole_ne h a.2
  · rintro ⟨hM, ha⟩
    exact matching_omission_coverage hh M hM ha

private theorem sum_perm_int {a b : List Int} (hp : a.Perm b) : a.sum = b.sum := by
  induction hp with
  | nil => rfl
  | cons x hp ih => simp only [List.sum_cons, ih]
  | swap x y l => simp only [List.sum_cons]; omega
  | trans hp hq ih ij => exact ih.trans ij

private theorem sum_filter_zero (l : List Matching) (h : Nat)
    (x z : Matching → Int) :
    ((l.filter (fun M => M.all (fun e => e.2 != h))).map
      (fun M => x M * zeroExtendCoordinates h z M)).sum =
    (l.map (fun M => x M * zeroExtendCoordinates h z M)).sum := by
  induction l with
  | nil => rfl
  | cons M l ih =>
    by_cases ha : M.all (fun e => e.2 != h) = true
    · simp only [List.filter_cons, ha, ↓reduceIte, List.map_cons, List.sum_cons, ih]
    · have hf : M.all (fun e => e.2 != h) = false := Bool.eq_false_iff.mpr ha
      simp only [List.filter_cons, hf, Bool.false_eq_true, ↓reduceIte,
        List.map_cons, List.sum_cons, zeroExtendCoordinates, Int.mul_zero, Int.zero_add] at *
      simpa only [hf, Bool.false_eq_true, ↓reduceIte, Int.mul_zero, Int.zero_add] using ih

theorem pairing_omission (m n d h : Nat) (hh : h ≤ n) (x z : Matching → Int) :
    ((matchings m n d).map (fun M => restrictCoordinates h x M * z M)).sum =
    ((matchings m (n+1) d).map
      (fun M => x M * zeroExtendCoordinates h z M)).sum := by
  rw [pairing_omission_image]
  exact (sum_perm_int ((omission_enumeration_perm m n d h hh).map _)).trans
    (sum_filter_zero _ h x z)

end Programme.«20261104-1627-proof-complexity».MatchingLabels
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.matchings_nodup

#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.omission_enumeration_perm
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.pairing_omission
