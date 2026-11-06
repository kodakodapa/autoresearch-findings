import Programme.«20261104-1627-proof-complexity».AnchoredValidity

namespace Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261029-1156-proof-complexity».StdPC

private theorem sum_add (L : List Label) (f g : Label → Int) :
    (L.map (fun x => f x + g x)).sum = (L.map f).sum + (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons]; rw [ih]; omega

private theorem sum_zeros (L : List Label) : (L.map (fun _ => (0 : Int))).sum = 0 := by
  induction L with
  | nil => rfl
  | cons a L ih => simpa using ih

private theorem indicator_sum (L : List Label) (hL : L.Nodup)
    (g : Label) (hg : g ∈ L) (c : Int) :
    (L.map (fun x => if g = x then c else 0)).sum = c := by
  induction L with
  | nil => simp at hg
  | cons a L ih =>
    have hn := List.nodup_cons.mp hL
    by_cases h : g = a
    · subst g
      have hz : (L.map (fun x => if a = x then c else 0)).sum = 0 := by
        have he : L.map (fun x => if a = x then c else 0) = L.map (fun _ => (0 : Int)) := by
          apply List.map_congr_left
          intro x hx
          have : a ≠ x := by intro he; subst x; exact hn.1 hx
          simp [this]
        rw [he]
        exact sum_zeros L
      simp [hz]
    · have hg' : g ∈ L := (List.mem_cons.mp hg).resolve_left h
      simp only [List.map_cons, List.sum_cons, h, ↓reduceIte, Int.zero_add]
      exact ih hn.2 hg'

private theorem aggregate_sum (L : List Label) (hL : L.Nodup)
    (v : Vector) (hv : ∀ t ∈ v, t.2 ∈ L) (F : Label → Int) :
    (v.map (fun t => t.1 * F t.2)).sum =
      (L.map (fun g => vectorCoeff v g * F g)).sum := by
  induction v with
  | nil =>
    simp only [List.map_nil, List.sum_nil, vectorCoeff, List.filter_nil, Int.zero_mul]
    exact (sum_zeros L).symm
  | cons t v ih =>
    have hc (g : Label) : vectorCoeff (t::v) g =
        (if t.2 = g then t.1 else 0) + vectorCoeff v g := by
      by_cases h : t.2 = g <;> simp [vectorCoeff, h]
    simp only [List.map_cons, List.sum_cons]
    rw [ih (by intro a ha; exact hv a (by simp [ha]))]
    simp only [hc, Int.add_mul]
    rw [sum_add]
    congr 1
    have he : (L.map (fun g => (if t.2 = g then t.1 else 0) * F g)) =
        L.map (fun g => if t.2 = g then t.1 * F t.2 else 0) := by
      apply List.map_congr_left
      intro g hg
      by_cases h : t.2 = g <;> simp [h]
    rw [he, indicator_sum L hL t.2 (hv t (by simp))]

private theorem top_as_sum (m n : Nat) (v : Vector) (u : List Nat) :
    coeff (top m n v) u =
      (v.map (fun t => t.1 * coeff (topLabel m n t.2) u)).sum := by
  induction v with
  | nil => simp [top, coeff, cf]
  | cons t v ih =>
    rw [show t::v = [t] ++ v from rfl, top_append_coeff, ih]
    simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, Int.add_zero]
    congr 1
    have hs := top_scale_coeff m n t.1 [(1,t.2)] u
    simpa [top, coeff, cf] using hs

private theorem dedup_nodup (L : List Label) : L.eraseDups.Nodup := by
  cases L with
  | nil => simp
  | cons a L =>
    rw [List.eraseDups_cons, List.nodup_cons]
    constructor
    · simp only [List.mem_eraseDups, List.mem_filter]
      intro h
      simpa using h.2
    · exact dedup_nodup (L.filter fun b => !b == a)
termination_by L.length
decreasing_by have := List.length_filter_le (fun b => !b == a) L; simp_all; omega

theorem top_aggregate_expansion {m n d : Nat} {v : Vector}
    (hv : valid m n d v) (u : List Nat) :
    coeff (top m n v) u = ((labels m n d).eraseDups.map
      (fun g => vectorCoeff v g * coeff (topLabel m n g) u)).sum := by
  rw [top_as_sum]
  apply aggregate_sum ((labels m n d).eraseDups) _ v _ (fun g => coeff (topLabel m n g) u)
  · exact dedup_nodup _
  · intro t ht
    exact List.mem_eraseDups.mpr (hv t ht)

private theorem dvd_sum {p : Int} (L : List Label) (F : Label → Int)
    (h : ∀ g ∈ L, p ∣ F g) : p ∣ (L.map F).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Int.dvd_add (h a (by simp)) (ih (by intro g hg; exact h g (by simp [hg])))

theorem kernel_of_aggregate_zero {p m n d : Nat} {v : Vector}
    (hv : valid m n d v) (hz : ∀ g, (p : Int) ∣ vectorCoeff v g) :
    Kernel p m n d v := by
  refine ⟨hv, ?_⟩
  intro u
  change (p : Int) ∣ coeff (top m n v) u - 0
  rw [Int.sub_zero, top_aggregate_expansion hv]
  apply dvd_sum
  intro g hg
  obtain ⟨a, ha⟩ := hz g
  exact ⟨a * coeff (topLabel m n g) u, by rw [ha]; simp [Int.mul_assoc]⟩

private theorem sum_sub (L : List Label) (f g : Label → Int) :
    (L.map (fun x => f x - g x)).sum = (L.map f).sum - (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons]; rw [ih]; omega

theorem top_aggregate_congruent {p m n d : Nat} {v w : Vector}
    (hv : valid m n d v) (hw : valid m n d w)
    (he : ∀ g, (p : Int) ∣ vectorCoeff v g - vectorCoeff w g) :
    PEq p (top m n v) (top m n w) := by
  intro u
  rw [top_aggregate_expansion hv, top_aggregate_expansion hw, ← sum_sub]
  apply dvd_sum
  intro g hg
  obtain ⟨a, ha⟩ := he g
  refine ⟨a * coeff (topLabel m n g) u, ?_⟩
  rw [← Int.sub_mul, ha, Int.mul_assoc]

theorem kernel_of_aggregate_congruent {p m n d : Nat} {v w : Vector}
    (hv : Kernel p m n d v) (hw : valid m n d w)
    (he : ∀ g, (p : Int) ∣ vectorCoeff v g - vectorCoeff w g) :
    Kernel p m n d w := by
  refine ⟨hw, ?_⟩
  have ht := top_aggregate_congruent hv.1 hw he
  intro u
  have hh := Int.dvd_sub (hv.2 u) (ht u)
  have hzero : coeff (⟨[]⟩ : Programme.«20261024-1633-proof-complexity».NS.Poly Nat) u = 0 := rfl
  rw [hzero] at hh ⊢
  have heq : coeff (top m n v) u - 0 -
      (coeff (top m n v) u - coeff (top m n w) u) = coeff (top m n w) u - 0 := by omega
  rw [heq] at hh
  exact hh

/-- Delete block one, retaining the original integer entries in blocks two and three. -/
def tailPigeon (m : Nat) (v : Vector) : Vector :=
  splitPigeon m 2 v ++ splitPigeon m 3 v

theorem tailPigeon_valid {m n d : Nat} (a : Nat) {v : Vector}
    (hv : valid m n d v) : valid m n d (tailPigeon a v) := by
  intro t ht
  rcases List.mem_append.mp ht with ht | ht
  · exact splitPigeon_valid a 2 hv t ht
  · exact splitPigeon_valid a 3 hv t ht

theorem tailPigeon_support (m : Nat) (v : Vector) :
    ∀ t ∈ tailPigeon m v, pigeonBlock m t.2 = 2 ∨ pigeonBlock m t.2 = 3 := by
  intro t ht
  rcases List.mem_append.mp ht with ht | ht
  · exact Or.inl (by simpa using (List.mem_filter.mp ht).2)
  · exact Or.inr (by simpa using (List.mem_filter.mp ht).2)

theorem tailPigeon_congruent {p m : Nat} {v : Vector}
    (hz : ∀ g, (p : Int) ∣ vectorCoeff (splitPigeon m 1 v) g) :
    ∀ g, (p : Int) ∣ vectorCoeff v g - vectorCoeff (tailPigeon m v) g := by
  intro g
  have hs := vectorCoeff_splitPigeon m v g
  rw [tailPigeon, vectorCoeff_append]
  have he : vectorCoeff v g - (vectorCoeff (splitPigeon m 2 v) g +
      vectorCoeff (splitPigeon m 3 v) g) = vectorCoeff (splitPigeon m 1 v) g := by omega
  rw [he]
  exact hz g

theorem tailPigeon_kernel {p m n d : Nat} {v : Vector}
    (hv : Kernel p (m+1) n d v)
    (hz : ∀ g, (p : Int) ∣ vectorCoeff (splitPigeon m 1 v) g) :
    Kernel p (m+1) n d (tailPigeon m v) :=
  kernel_of_aggregate_congruent hv (tailPigeon_valid m hv.1) (tailPigeon_congruent hz)

/-- The first-block step with an actual, literally tail-supported residual. -/
theorem first_block_tail_residual {p m n d : Nat} {v : Vector}
    (hv : Kernel p (m+1) n d v) (hs : Spanning p m n d) :
    ∃ (C : List (Int × Vector)) (w : Vector),
      (∀ t ∈ C, t.2 ∈ syzygies (m+1) n d) ∧
      Kernel p (m+1) n d w ∧
      (∀ t ∈ w, pigeonBlock m t.2 = 2 ∨ pigeonBlock m t.2 = 3) ∧
      ∀ g, (p : Int) ∣ vectorCoeff v g - vectorCoeff (combine C) g - vectorCoeff w g := by
  obtain ⟨C,hC,hk,hz⟩ := first_block_residual_sound hv hs
  let r := v ++ (combine C).map (fun t => (-t.1,t.2))
  refine ⟨C, tailPigeon m r, hC, tailPigeon_kernel hk hz, tailPigeon_support m r, ?_⟩
  intro g
  have he := tailPigeon_congruent hz g
  have hn : vectorCoeff r g = vectorCoeff v g - vectorCoeff (combine C) g := by
    dsimp [r]
    rw [vectorCoeff_append]
    have hm : ((combine C).map (fun t => (-t.1,t.2))) =
        ((combine C).map (fun t => ((-1 : Int)*t.1,t.2))) := by simp
    rw [hm, vectorCoeff_scale]
    simp [Int.sub_eq_add_neg]
  rw [hn] at he
  exact he

end Programme.«20261104-1627-proof-complexity».MatchingLabels
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.top_aggregate_expansion
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.kernel_of_aggregate_zero

#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.top_aggregate_congruent
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.tailPigeon_kernel
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.first_block_tail_residual
