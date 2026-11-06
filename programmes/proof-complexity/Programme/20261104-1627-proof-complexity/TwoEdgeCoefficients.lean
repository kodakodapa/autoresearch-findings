import Programme.«20261104-1627-proof-complexity».DegreeTwoLabels

namespace Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261029-1156-proof-complexity».StdPC

private theorem pair_perm (x y a b : Nat) :
    [x,y].Perm [a,b] ↔ (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by
  constructor
  · intro h
    have hx := h.mem_iff.mp (show x ∈ [x,y] by simp)
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · have hy := List.Perm.cons_inv h
      exact Or.inl ⟨rfl, by simpa using hy⟩
    · have hy := List.Perm.cons_inv (h.trans (List.Perm.swap _ _ _))
      exact Or.inr ⟨rfl, by simpa using hy⟩
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · exact List.Perm.refl _
    · exact List.Perm.swap _ _ _

private theorem code_eq {n x y a b : Nat} (hn : 0 < n)
    (hy : y < n) (hb : b < n) :
    x*n+y = a*n+b ↔ x = a ∧ y = b := by
  constructor
  · intro h
    have hd := congrArg (· / n) h
    have hm := congrArg (· % n) h
    simp [Nat.add_div, Nat.add_mod, Nat.mod_eq_of_lt hy, Nat.mod_eq_of_lt hb,
      Nat.div_eq_of_lt hy, Nat.div_eq_of_lt hb, Nat.not_le_of_lt hy,
      Nat.not_le_of_lt hb, hn] at hd hm
    exact ⟨hd,hm⟩
  · rintro ⟨rfl,rfl⟩; rfl

private theorem cf_choices (L : List Nat) (f : Nat → List Nat) (u : List Nat)
    (q r : Nat) (A B : Prop) [Decidable A] [Decidable B] (hqr : q ≠ r)
    (h : ∀ x ∈ L, (f x).Perm u ↔ (x = q ∧ A) ∨ (x = r ∧ B)) :
    cf (L.map fun x => (1,f x)) u =
      (if A then ((L.filter (· == q)).length : Int) else 0) +
      (if B then ((L.filter (· == r)).length : Int) else 0) := by
  induction L with
  | nil => simp [cf]
  | cons x L ih =>
    have hx := h x List.mem_cons_self
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    have hc : cf ((1,f x) :: L.map (fun x => (1,f x))) u =
        (if (f x).Perm u then 1 else 0) + cf (L.map fun x => (1,f x)) u := by
      by_cases hp : (f x).Perm u <;> simp [cf,hp]
    rw [List.map_cons, hc, ht]
    by_cases hq : x = q <;> by_cases hr : x = r
    · exact False.elim (hqr (hq.symm.trans hr))
    · subst x
      have hx' : (f q).Perm u ↔ A := by simpa [hqr] using hx
      by_cases hA : A <;> by_cases hB : B <;> simp [hx',hA,hB,hqr,Int.add_assoc,Int.add_comm,Int.add_left_comm]
    · subst x
      have hrq : r ≠ q := Ne.symm hqr
      have hx' : (f r).Perm u ↔ B := by simpa [hrq] using hx
      by_cases hA : A <;> by_cases hB : B <;> simp [hx',hA,hB,hrq,Int.add_assoc,Int.add_comm,Int.add_left_comm]
    · have hx' : ¬ (f x).Perm u := by simpa [hq,hr] using hx
      simp [hx',hq,hr]

private theorem filtered_range (N q : Nat) (P : Nat → Bool) (hq : q < N) :
    (((List.range N).filter P).filter (· == q)).length = if P q then 1 else 0 := by
  induction N with
  | zero => omega
  | succ N ih =>
    by_cases he : q = N
    · subst q
      have hz : ((List.range N).filter P).filter (· == N) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro a ha
        have hb := List.mem_range.mp (List.mem_filter.mp ha).1
        simp only [beq_iff_eq, Bool.not_eq_true]
        omega
      rw [List.range_succ, List.filter_append, List.filter_append, List.length_append, hz]
      simp; split <;> simp_all
    · have hh : q < N := by omega
      rw [List.range_succ, List.filter_append, List.filter_append, List.length_append, ih hh]
      have hnq : N ≠ q := Ne.symm he
      by_cases hp : P N <;> simp [hp,hnq]

theorem topLabel_two_row {m n : Nat} (hn : 0 < n)
    (c d r a b i j : Nat) (hd : d < n) (hb : b < n) (hj : j < n)
    (hai : a ≠ i) (hbj : b ≠ j) :
    coeff (topLabel m n (edgeRowLabel c d r)) [a*n+b,i*n+j] =
      (if edgeRowLabel c d r = edgeRowLabel a b i then 1 else 0) +
      (if edgeRowLabel c d r = edgeRowLabel i j a then 1 else 0) := by
  change cf (((List.range n).filter (freeCol [(c,d)])).map
    fun x => (1,[r*n+x,c*n+d])) [a*n+b,i*n+j] = _
  have hh : ∀ x ∈ (List.range n).filter (freeCol [(c,d)]),
      [r*n+x,c*n+d].Perm [a*n+b,i*n+j] ↔
        (x = j ∧ edgeRowLabel c d r = edgeRowLabel a b i) ∨
        (x = b ∧ edgeRowLabel c d r = edgeRowLabel i j a) := by
    intro x hx
    have hx' := List.mem_range.mp (List.mem_filter.mp hx).1
    rw [pair_perm, code_eq hn hx' hb, code_eq hn hd hj,
      code_eq hn hx' hj, code_eq hn hd hb]
    simp only [edgeRowLabel, Label.mk.injEq, List.cons.injEq, Prod.mk.injEq,
      List.nil_eq, and_true, true_and]
    constructor
    · rintro (⟨⟨h1,h2⟩,h3,h4⟩ | ⟨⟨h1,h2⟩,h3,h4⟩)
      · exact Or.inr ⟨h2,⟨h3,h4⟩,h1⟩
      · exact Or.inl ⟨h2,⟨h3,h4⟩,h1⟩
    · rintro (⟨h2,⟨h3,h4⟩,h1⟩ | ⟨h2,⟨h3,h4⟩,h1⟩)
      · exact Or.inr ⟨⟨h1,h2⟩,h3,h4⟩
      · exact Or.inl ⟨⟨h1,h2⟩,h3,h4⟩
  rw [cf_choices _ _ _ j b _ _ (Ne.symm hbj) hh,
    filtered_range n j _ hj, filtered_range n b _ hb]
  have base_col {c d r a b i : Nat}
      (h : edgeRowLabel c d r = edgeRowLabel a b i) : d = b := by
    have hh := congrArg Label.base h
    have hh' : c = a ∧ d = b := by simpa [edgeRowLabel] using hh
    exact hh'.2
  by_cases h1 : edgeRowLabel c d r = edgeRowLabel a b i <;>
    by_cases h2 : edgeRowLabel c d r = edgeRowLabel i j a
  · exact False.elim (hbj ((base_col h1).symm.trans (base_col h2)))
  · simp only [if_pos h1, if_neg h2]
    have hdb := base_col h1
    simp [freeCol,hdb,hbj,Ne.symm hbj]
  · simp only [if_neg h1, if_pos h2]
    have hdj := base_col h2
    simp [freeCol,hdj,hbj,Ne.symm hbj]
  · simp [h1,h2]

theorem topLabel_two_col {m n : Nat} (hn : 0 < n)
    (c d r a b i j : Nat) (hc : c < m) (hd : d < n) (hr : r < n) (ha : a < m) (hi : i < m) (hb : b < n) (hj : j < n)
    (hai : a ≠ i) (hbj : b ≠ j) :
    coeff (topLabel m n (edgeColLabel c d r)) [a*n+b,i*n+j] =
      (if edgeColLabel c d r = edgeColLabel a b j then 1 else 0) +
      (if edgeColLabel c d r = edgeColLabel i j b then 1 else 0) := by
  change cf (((List.range m).filter (freeRow [(c,d)])).map
    fun x => (1,[x*n+r,c*n+d])) [a*n+b,i*n+j] = _
  have hh : ∀ x ∈ (List.range m).filter (freeRow [(c,d)]),
      [x*n+r,c*n+d].Perm [a*n+b,i*n+j] ↔
        (x = i ∧ edgeColLabel c d r = edgeColLabel a b j) ∨
        (x = a ∧ edgeColLabel c d r = edgeColLabel i j b) := by
    intro x hx
    have hx' := List.mem_range.mp (List.mem_filter.mp hx).1
    rw [pair_perm, code_eq hn hr hb, code_eq hn hd hj,
      code_eq hn hr hj, code_eq hn hd hb]
    simp only [edgeColLabel, Label.mk.injEq, List.cons.injEq, Prod.mk.injEq,
      List.nil_eq, and_true, true_and]
    constructor
    · rintro (⟨⟨h1,h2⟩,h3,h4⟩ | ⟨⟨h1,h2⟩,h3,h4⟩)
      · exact Or.inr ⟨h1,⟨h3,h4⟩,h2⟩
      · exact Or.inl ⟨h1,⟨h3,h4⟩,h2⟩
    · rintro (⟨h1,⟨h3,h4⟩,h2⟩ | ⟨h1,⟨h3,h4⟩,h2⟩)
      · exact Or.inr ⟨⟨h1,h2⟩,h3,h4⟩
      · exact Or.inl ⟨⟨h1,h2⟩,h3,h4⟩
  rw [cf_choices _ _ _ i a _ _ (Ne.symm hai) hh,
    filtered_range m i _ hi, filtered_range m a _ ha]
  have base_row {c d r a b i : Nat}
      (h : edgeColLabel c d r = edgeColLabel a b i) : c = a := by
    have hh := congrArg Label.base h
    have hh' : c = a ∧ d = b := by simpa [edgeColLabel] using hh
    exact hh'.1
  by_cases h1 : edgeColLabel c d r = edgeColLabel a b j <;>
    by_cases h2 : edgeColLabel c d r = edgeColLabel i j b
  · exact False.elim (hai ((base_row h1).symm.trans (base_row h2)))
  · simp only [if_pos h1, if_neg h2]
    have hca := base_row h1
    simp [freeRow,hca,hai,Ne.symm hai]
  · simp only [if_neg h1, if_pos h2]
    have hci := base_row h2
    simp [freeRow,hci,hai,Ne.symm hai]
  · simp [h1,h2]

private theorem cf_scale_two (c : Int) (L : List (Int × List Nat)) (u : List Nat) :
    cf (L.map fun t => (c*t.1,t.2)) u = c * cf L u := by
  induction L with
  | nil => simp [cf]
  | cons t L ih =>
    by_cases h : t.2.Perm u <;> simp [cf,h] at ih ⊢ <;> simp_all [Int.mul_add]

private theorem vc_cons_two (t : Int × Label) (v : Vector) (g : Label) :
    vectorCoeff (t::v) g = (if t.2 = g then t.1 else 0) + vectorCoeff v g := by
  by_cases h : t.2 = g <;> simp [vectorCoeff,h]

theorem top_two_edges {m n : Nat} (hn : 0 < n)
  (v : Vector) (hv : valid m n 2 v)
  (a b i j : Nat) (ha : a < m) (hb : b < n)
  (hi : i < m) (hj : j < n) (hai : a ≠ i) (hbj : b ≠ j) :
  coeff (top m n v) [a*n+b,i*n+j] =
    vectorCoeff v (edgeRowLabel a b i) +
    vectorCoeff v (edgeRowLabel i j a) +
    vectorCoeff v (edgeColLabel a b j) +
    vectorCoeff v (edgeColLabel i j b) := by
  induction v with
  | nil => simp [top,coeff,cf,vectorCoeff]
  | cons t v ih =>
    have ht := ih (fun u hu => hv u (List.mem_cons_of_mem t hu))
    have hc : coeff (top m n (t::v)) [a*n+b,i*n+j] =
        t.1 * coeff (topLabel m n t.2) [a*n+b,i*n+j] +
        coeff (top m n v) [a*n+b,i*n+j] := by
      change cf (_ ++ _) _ = _
      rw [cf_append,cf_scale_two]
      rfl
    rw [hc,ht,vc_cons_two,vc_cons_two,vc_cons_two,vc_cons_two]
    rcases label_two_cases (hv t List.mem_cons_self) with
      ⟨c,hc,d,hd,r,hr,hcr,hg⟩ | ⟨c,hc,d,hd,r,hr,hdr,hg⟩
    · rw [hg,topLabel_two_row hn c d r a b i j hd hb hj hai hbj]
      have hz1 : edgeRowLabel c d r ≠ edgeColLabel a b j := by simp [edgeRowLabel,edgeColLabel]
      have hz2 : edgeRowLabel c d r ≠ edgeColLabel i j b := by simp [edgeRowLabel,edgeColLabel]
      simp only [if_neg hz1,if_neg hz2,Int.zero_add]
      by_cases h1 : edgeRowLabel c d r = edgeRowLabel a b i <;>
        by_cases h2 : edgeRowLabel c d r = edgeRowLabel i j a <;>
        simp only [h1,h2, ite_true, ite_false] <;> simp_all only [Int.mul_add,Int.mul_one,Int.mul_zero,Int.add_zero,Int.zero_add] <;> simp <;> omega
    · rw [hg,topLabel_two_col hn c d r a b i j hc hd hr ha hi hb hj hai hbj]
      have hz1 : edgeColLabel c d r ≠ edgeRowLabel a b i := by simp [edgeRowLabel,edgeColLabel]
      have hz2 : edgeColLabel c d r ≠ edgeRowLabel i j a := by simp [edgeRowLabel,edgeColLabel]
      simp only [if_neg hz1,if_neg hz2,Int.zero_add]
      by_cases h1 : edgeColLabel c d r = edgeColLabel a b j <;>
        by_cases h2 : edgeColLabel c d r = edgeColLabel i j b <;>
        simp only [h1,h2, ite_true, ite_false] <;> simp_all only [Int.mul_add,Int.mul_one,Int.mul_zero,Int.add_zero,Int.zero_add] <;> simp <;> omega

/-- The concrete matching coefficient equations forced by the kernel. -/
theorem kernel_two_equations {p m n : Nat} (hn : 0 < n)
    (v : Vector) (hv : Kernel p m n 2 v)
    (a b i j : Nat) (ha : a < m) (hb : b < n)
    (hi : i < m) (hj : j < n) (hai : a ≠ i) (hbj : b ≠ j) :
    (p : Int) ∣ vectorCoeff v (edgeRowLabel a b i) +
      vectorCoeff v (edgeRowLabel i j a) +
      vectorCoeff v (edgeColLabel a b j) +
      vectorCoeff v (edgeColLabel i j b) := by
  have h := hv.2 [a*n+b,i*n+j]
  rw [top_two_edges hn v hv.1 a b i j ha hb hi hj hai hbj] at h
  simpa [coeff,cf] using h

end Programme.«20261104-1627-proof-complexity».MatchingLabels
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.top_two_edges

#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.kernel_two_equations
