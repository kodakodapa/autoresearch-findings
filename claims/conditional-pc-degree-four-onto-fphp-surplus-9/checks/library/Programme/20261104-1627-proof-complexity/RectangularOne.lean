import Programme.«20261104-1627-proof-complexity».SpanningOne

namespace Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261029-1156-proof-complexity».StdPC

def rowLabel (i : Nat) : Label := ⟨[], true, i⟩
def colLabel (j : Nat) : Label := ⟨[], false, j⟩

theorem labels_one (m n : Nat) : labels m n 1 =
    (List.range m).map rowLabel ++ (List.range n).map colLabel := by
  have hr : freeRow [] = fun _ => true := rfl
  have hc : freeCol [] = fun _ => true := rfl
  have hf (L : List Nat) : L.filter (fun _ => true) = L := List.filter_eq_self.mpr (by simp)
  have hf (L : List Nat) : L.filter (fun _ => true) = L := List.filter_eq_self.mpr (by simp)
  simp [labels, matchings, rows, cols, hr, hc, hf]
  rfl

theorem label_one_cases {m n : Nat} {g : Label} (hg : g ∈ labels m n 1) :
    (∃ i, i < m ∧ g = rowLabel i) ∨ (∃ j, j < n ∧ g = colLabel j) := by
  rw [labels_one] at hg
  rcases List.mem_append.mp hg with h | h
  · rcases List.mem_map.mp h with ⟨i, hi, rfl⟩
    exact Or.inl ⟨i, List.mem_range.mp hi, rfl⟩
  · rcases List.mem_map.mp h with ⟨j, hj, rfl⟩
    exact Or.inr ⟨j, List.mem_range.mp hj, rfl⟩

theorem vc_cons' (a : Int × Label) (v : Vector) (g : Label) :
    vectorCoeff (a :: v) g = (if a.2 = g then a.1 else 0) + vectorCoeff v g := by
  by_cases h : a.2 = g <;> simp [vectorCoeff, h]

private theorem cf_singletons (L : List Nat) (x : Nat) :
    cf (L.map fun y => (1, [y])) [x] = (L.filter (· == x)).length := by
  induction L with
  | nil => simp [cf]
  | cons y L ih =>
    by_cases h : y = x
    · subst y; simp [cf] at ih ⊢; omega
    · simp [cf, h] at ih ⊢; exact ih

private theorem cf_scaled (a : Int) (L : List (Int × List Nat)) (u : List Nat) :
    cf (L.map fun b => (a*b.1,b.2)) u = a * cf L u := by
  induction L with
  | nil => simp [cf]
  | cons b L ih =>
    by_cases h : b.2.Perm u <;> simp [cf, h] at ih ⊢ <;> simp_all [Int.mul_add]

private theorem cf_indicator (L : List Nat) (f : Nat → Nat) (x q : Nat)
    (h : ∀ y ∈ L, f y = x ↔ y = q) :
    cf (L.map fun y => (1, [f y])) [x] =
      ((L.filter (· == q)).length : Int) := by
  induction L with
  | nil => simp [cf]
  | cons y L ih =>
    have hy := h y List.mem_cons_self
    have ht : ∀ z ∈ L, f z = x ↔ z = q :=
      fun z hz => h z (List.mem_cons_of_mem y hz)
    have hi := ih ht
    by_cases he : y = q
    · subst y
      have hf : f q = x := hy.mpr rfl
      simp [cf, hf] at hi ⊢
      omega
    · have hf : f y ≠ x := fun hh => he (hy.mp hh)
      simpa [cf, hf, he] using hi

private theorem range_filter_single (N q : Nat) (hq : q < N) :
    ((List.range N).filter (· == q)).length = 1 := by
  induction N with
  | zero => omega
  | succ N ih =>
    rw [List.range_succ, List.filter_append, List.length_append]
    by_cases he : q = N
    · subst q
      have hz : (List.range N).filter (· == N) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro a ha
        simp only [beq_iff_eq, Bool.not_eq_true]
        have := List.mem_range.mp ha
        omega
      simp [hz]
    · have hh : q < N := by omega
      simp [ih hh, show N ≠ q by omega]

theorem topLabel_row_edge {m n : Nat} (hn : 0 < n)
    (a i j : Nat) (hj : j < n) :
    coeff (topLabel m n (rowLabel a)) [i*n+j] = if a = i then 1 else 0 := by
  have hc : freeCol [] = fun _ => true := rfl
  have hf (L : List Nat) : L.filter (fun _ => true) = L := List.filter_eq_self.mpr (by simp)
  simp [topLabel, rowLabel, cols, hc, hf, mono, coeff]
  change cf ((List.range n).map fun b => (1, [a*n+b])) [i*n+j] = _
  have h : ∀ b ∈ List.range n, a*n+b = i*n+j ↔ b = j ∧ a = i := by
    intro b hb
    have hb' := List.mem_range.mp hb
    constructor
    · intro he
      have hd := congrArg (fun x => x / n) he
      have hm := congrArg (fun x => x % n) he
      simp [Nat.add_div, Nat.add_mod, Nat.mod_eq_of_lt hb', Nat.mod_eq_of_lt hj,
        Nat.mul_div_cancel, Nat.div_eq_of_lt hb', Nat.div_eq_of_lt hj, Nat.not_le_of_lt hb', Nat.not_le_of_lt hj, hn, Nat.ne_of_gt hn] at hd hm
      exact ⟨hm, hd⟩
    · rintro ⟨rfl, rfl⟩; rfl
  by_cases ha : a = i
  · rw [if_pos ha, cf_indicator (List.range n) (fun b => a*n+b) (i*n+j) j
      (fun b hb => by simpa [ha] using h b hb), range_filter_single n j hj]
    rfl
  · rw [if_neg ha]
    have hz : ∀ b ∈ List.range n, a*n+b ≠ i*n+j := by
      intro b hb he; exact ha ((h b hb).mp he).2
    generalize heL : List.range n = L at *
    clear h heL
    induction L with
    | nil => simp [cf]
    | cons b L ih =>
      have hb := hz b List.mem_cons_self
      have ht := ih (fun c hc => hz c (List.mem_cons_of_mem b hc))
      simpa [cf, hb] using ht

theorem topLabel_col_edge {m n : Nat} (hn : 0 < n)
    (b i j : Nat) (hi : i < m) (hb : b < n) (hj : j < n) :
    coeff (topLabel m n (colLabel b)) [i*n+j] = if b = j then 1 else 0 := by
  have hr : freeRow [] = fun _ => true := rfl
  have hf (L : List Nat) : L.filter (fun _ => true) = L := List.filter_eq_self.mpr (by simp)
  simp [topLabel, colLabel, rows, hr, hf, mono, coeff]
  have h : ∀ a ∈ List.range m, a*n+b = i*n+j ↔ a = i ∧ b = j := by
    intro a ha
    constructor
    · intro he
      have hd := congrArg (fun x => x / n) he
      have hm := congrArg (fun x => x % n) he
      simp [Nat.add_div, Nat.add_mod, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hj,
        Nat.div_eq_of_lt hb, Nat.div_eq_of_lt hj, Nat.not_le_of_lt hb,
        Nat.not_le_of_lt hj, hn] at hd hm
      exact ⟨hd, hm⟩
    · rintro ⟨rfl, rfl⟩; rfl
  by_cases he : b = j
  · rw [if_pos he, cf_indicator (List.range m) (fun a => a*n+b) (i*n+j) i
      (fun a ha => by simpa [he] using h a ha), range_filter_single m i hi]
    rfl
  · rw [if_neg he]
    have hz : ∀ a ∈ List.range m, a*n+b ≠ i*n+j := by
      intro a ha hh; exact he ((h a ha).mp hh).2
    generalize heL : List.range m = L at *
    clear h heL
    induction L with
    | nil => simp [cf]
    | cons a L ih =>
      have ha := hz a List.mem_cons_self
      have ht := ih (fun c hc => hz c (List.mem_cons_of_mem a hc))
      simpa [cf, ha] using ht

theorem top_one_edge {m n : Nat} (hn : 0 < n)
    (v : Vector) (hv : valid m n 1 v)
    (i j : Nat) (hi : i < m) (hj : j < n) :
    coeff (top m n v) [i*n+j] =
      vectorCoeff v (rowLabel i) + vectorCoeff v (colLabel j) := by
  induction v with
  | nil => simp [top, coeff, cf, vectorCoeff]
  | cons a v ih =>
    have ha := label_one_cases (hv a List.mem_cons_self)
    have ht := ih (fun t ht => hv t (List.mem_cons_of_mem a ht))
    have he : coeff (top m n (a::v)) [i*n+j] =
        a.1 * coeff (topLabel m n a.2) [i*n+j] + coeff (top m n v) [i*n+j] := by
      change cf (_ ++ _) _ = _
      rw [cf_append, cf_scaled]
      rfl
    rw [he, ht, vc_cons', vc_cons']
    rcases ha with ⟨b, hb, hg⟩ | ⟨b, hb, hg⟩
    · rw [hg, topLabel_row_edge hn b i j hj]
      by_cases hh : b = i <;> simp [rowLabel, colLabel, hh] <;> omega
    · rw [hg, topLabel_col_edge hn b i j hi hb hj]
      by_cases hh : b = j <;> simp [rowLabel, colLabel, hh] <;> omega

private theorem vc_append (u v : Vector) (g : Label) :
    vectorCoeff (u ++ v) g = vectorCoeff u g + vectorCoeff v g := by
  simp [vectorCoeff, List.filter_append, List.map_append, List.sum_append]

private theorem vc_map (L : List Nat) (f : Nat → Label) (g : Label) (c : Int) :
    vectorCoeff (L.map fun i => (c, f i)) g =
      c * ((L.filter fun i => f i == g).length : Int) := by
  induction L with
  | nil => simp [vectorCoeff]
  | cons i L ih =>
    rw [List.map_cons, vc_cons', ih]
    by_cases h : f i = g <;> simp [h, Int.mul_add] <;> omega

private theorem z_one (m n : Nat) : z m n 1 [] =
    (List.range m).map (fun i => (1,rowLabel i)) ++
    (List.range n).map (fun j => (-1,colLabel j)) := by
  have hr : freeRow [] = fun _ => true := rfl
  have hc : freeCol [] = fun _ => true := rfl
  have hf (L : List Nat) : L.filter (fun _ => true) = L := List.filter_eq_self.mpr (by simp)
  simp only [z, Nat.sub_self]
  simp only [matchings, List.filter_cons, List.all_nil, Bool.true_eq, ↓reduceIte, List.filter_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append]
  simp [rows, cols, hr, hc, hf, ordered, rowLabel, colLabel]

private theorem row_beq (a b : Nat) : (rowLabel a == rowLabel b) = (a == b) := by
  apply Bool.eq_iff_iff.mpr
  simp [rowLabel]
private theorem col_beq (a b : Nat) : (colLabel a == colLabel b) = (a == b) := by
  apply Bool.eq_iff_iff.mpr
  simp [colLabel]
private theorem row_col_beq (a b : Nat) : (rowLabel a == colLabel b) = false := by
  simp [beq_iff_eq, rowLabel, colLabel]
private theorem col_row_beq (a b : Nat) : (colLabel a == rowLabel b) = false := by
  simp [beq_iff_eq, rowLabel, colLabel]

private theorem z_row {m n : Nat} (i : Nat) (hi : i < m) :
    vectorCoeff (z m n 1 []) (rowLabel i) = 1 := by
  rw [z_one, vc_append, vc_map, vc_map]
  simp only [row_beq, col_row_beq]
  have hf : (List.range n).filter (fun _ => false) = [] := List.filter_eq_nil_iff.mpr (by simp)
  simp [range_filter_single m i hi, hf]

private theorem z_col {m n : Nat} (j : Nat) (hj : j < n) :
    vectorCoeff (z m n 1 []) (colLabel j) = -1 := by
  rw [z_one, vc_append, vc_map, vc_map]
  simp only [col_beq, row_col_beq]
  have hf : (List.range m).filter (fun _ => false) = [] := List.filter_eq_nil_iff.mpr (by simp)
  simp [range_filter_single n j hj, hf]

private theorem vc_combine_single (c : Int) (v : Vector) (g : Label) :
    vectorCoeff (combine [(c,v)]) g = c * vectorCoeff v g := by
  simp only [combine, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  induction v with
  | nil => simp [vectorCoeff]
  | cons a v ih =>
    rw [List.map_cons, vc_cons', vc_cons', ih]
    by_cases h : a.2 = g <;> simp [h, Int.mul_add]

private theorem vc_outside {m n : Nat} (v : Vector) (hv : valid m n 1 v)
    (g : Label) (hg : g ∉ labels m n 1) : vectorCoeff v g = 0 := by
  induction v with
  | nil => simp [vectorCoeff]
  | cons a v ih =>
    have hn : a.2 ≠ g := fun he => hg (he ▸ hv a List.mem_cons_self)
    rw [vc_cons', if_neg hn, ih (fun t ht => hv t (List.mem_cons_of_mem a ht))]
    simp

theorem spanning_one {p m n : Nat} (hm : 0 < m) (hn : 0 < n) :
    Spanning p m n 1 := by
  intro v hv
  have he : ∀ i : Fin m, ∀ j : Fin n,
      (p : Int) ∣ topOne (fun i => vectorCoeff v (rowLabel i))
        (fun j => vectorCoeff v (colLabel j)) i j := by
    intro i j
    have h := hv.2 [i.val*n+j.val]
    rw [top_one_edge hn v hv.1 i j i.isLt j.isLt] at h
    simpa [topOne, coeff, cf] using h
  obtain ⟨c, ha, hb⟩ := kernel_one_span hm hn _ _ he
  refine ⟨[(c,z m n 1 [])], ?_, ?_⟩
  · intro t ht
    have ht' : t = (c,z m n 1 []) := by simpa using ht
    subst t
    simp [syzygies, matchings]
  · intro g
    rw [vc_combine_single]
    by_cases hg : g ∈ labels m n 1
    · rcases label_one_cases hg with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
      · rw [z_row i hi, Int.mul_one]
        exact ha ⟨i,hi⟩
      · rw [z_col j hj]
        simpa using hb ⟨j,hj⟩
    · rw [vc_outside v hv.1 g hg]
      have hz : valid m n 1 (z m n 1 []) := by
        intro a ha
        rw [z_one] at ha
        rw [labels_one]
        rcases List.mem_append.mp ha with ha | ha
        · rcases List.mem_map.mp ha with ⟨i, hi, rfl⟩
          exact List.mem_append_left _ (List.mem_map.mpr ⟨i,hi,rfl⟩)
        · rcases List.mem_map.mp ha with ⟨j, hj, rfl⟩
          exact List.mem_append_right _ (List.mem_map.mpr ⟨j,hj,rfl⟩)
      rw [vc_outside _ hz g hg]
      simp

end Programme.«20261104-1627-proof-complexity».MatchingLabels
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.topLabel_row_edge


#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.top_one_edge

#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.spanning_one
