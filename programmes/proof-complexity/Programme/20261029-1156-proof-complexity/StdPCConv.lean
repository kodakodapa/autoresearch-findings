import Programme.«20261029-1156-proof-complexity».StdPC

/-!
# Audit (b): library `PPCRefutation` gives a standard polynomial calculus refutation

`ppc_refutes`: for `p ≥ 2`, every `PPCRefutation p A D` (semantic lines on the Boolean cube, read
mod `p`) gives `Work.StdPC.Refutes p A D` (syntactic polynomials over `F_p` with Boolean axioms
`x² - x`). With `Work.StdPC.refutes_ppc` the two notions of degree-`D` refutability coincide.

Proof. Invariant: every semantic line `g` has a derived standard line `Q` with `Q ≡ g` mod `p` on
the cube. The only nontrivial rule is `mul`, where `g` is represented by some `R` of degree
`≤ D - 1` (`CubeDeg`) and we must derive `R` itself. `der_of_cube`: if `Q` is derived and `R` (of
degree `≤ D`) agrees with `Q` mod `p` on the cube, then `R` is derived. For this,
1. `der_of_ml`: each monomial `m` of `R - Q` is reduced to its multilinear form `dd m` inside
   `Der` (multiples of Boolean axioms, all of degree `≤ |m| ≤ D`);
2. `cf_ml_dvd`: a multilinear term list that vanishes mod `p` on the cube has every coefficient
   `≡ 0` mod `p` (evaluate at the indicator of a shortest monomial with a nonzero coefficient),
   so it equals `0` in `F_p[x]`.
-/

namespace Programme.«20261029-1156-proof-complexity».StdPCConv

open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261024-1633-proof-complexity».PCTseitin
open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261029-1156-proof-complexity».StdPC

/-! ## Coefficients -/

theorem cf_nil (m : List Nat) : cf [] m = 0 := by simp [cf]

theorem cf_cons (t : Int × List Nat) (L : List (Int × List Nat)) (m : List Nat) :
    cf (t :: L) m = (if t.2.Perm m then t.1 else 0) + cf L m := by
  by_cases h : t.2.Perm m <;> simp [cf, List.filter_cons, h]

theorem cf_scale (w : Int) (L : List (Int × List Nat)) (m : List Nat) :
    cf (L.map fun t => (w * t.1, t.2)) m = w * cf L m := by
  induction L with
  | nil => simp [cf_nil]
  | cons t L ih =>
    rw [List.map_cons, cf_cons, cf_cons, ih]
    split <;> simp [Int.mul_add]

theorem cf_lc (u v : Int) (P Q : Poly Nat) (m : List Nat) :
    cf (lc u v P Q).terms m = u * cf P.terms m + v * cf Q.terms m := by
  simp only [lc]; rw [cf_append, cf_scale, cf_scale]

theorem peq_of_cf {p : Nat} {P Q : Poly Nat} (h : ∀ m, cf P.terms m = cf Q.terms m) : PEq p P Q :=
  fun m => by unfold coeff; rw [h m, Int.sub_self]; exact Int.dvd_zero _

/-! ## Degrees -/

theorem foldr_max_le (L : List Nat) (D : Nat) : L.foldr max 0 ≤ D ↔ ∀ x ∈ L, x ≤ D := by
  induction L with
  | nil => simp
  | cons x L ih => simp [ih, Nat.max_le]

theorem deg_le (P : Poly Nat) (D : Nat) : P.deg ≤ D ↔ ∀ t ∈ P.terms, t.2.length ≤ D := by
  unfold Poly.deg; rw [foldr_max_le]; simp only [List.mem_map]
  constructor
  · intro h t ht; exact h _ ⟨t, ht, rfl⟩
  · rintro h _ ⟨t, ht, rfl⟩; exact h t ht

theorem der_deg {p D : Nat} {A : List (Poly Nat)} {P : Poly Nat} (h : Der p A D P) : P.deg ≤ D := by
  induction h with
  | ax _ _ hd => exact hd
  | bool x hD => rw [deg_le]; intro t ht; simp [boolAx] at ht; rcases ht with h | h <;> simp [h] <;> omega
  | lin u v P Q _ _ ihP ihQ =>
    rw [deg_le] at *; intro t ht
    simp only [lc, List.mem_append, List.mem_map] at ht
    rcases ht with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩
    · exact ihP s hs
    · exact ihQ s hs
  | mul x P _ hd _ =>
    rw [deg_le]; intro t ht
    simp only [Poly.mulVar, List.mem_map] at ht
    obtain ⟨s, hs, rfl⟩ := ht
    have := (deg_le P (D - 1)).mp (by omega) s hs
    simp; omega
  | eq _ _ _ _ hd _ => exact hd

/-! ## Binomials `l₁ - l₂` -/

/-- The binomial `l₁ - l₂` (two monomials). -/
def bin (l₁ l₂ : List Nat) : Poly Nat := ⟨[(1, l₁), (-1, l₂)]⟩

theorem deg_bin {l₁ l₂ : List Nat} {D : Nat} (h1 : l₁.length ≤ D) (h2 : l₂.length ≤ D) :
    (bin l₁ l₂).deg ≤ D := by
  rw [deg_le]; intro t ht; simp [bin] at ht; rcases ht with h | h <;> rw [h] <;> assumption

theorem cf_bin (l₁ l₂ m : List Nat) :
    cf (bin l₁ l₂).terms m = (if l₁.Perm m then 1 else 0) - (if l₂.Perm m then 1 else 0) := by
  simp only [bin, cf_cons, cf_nil]; split <;> split <;> simp

variable {p D : Nat} {A : List (Poly Nat)}

/-- The zero line `0·P₀ + 0·P₀`. -/
theorem cf_zero (P₀ : Poly Nat) (m : List Nat) : cf (lc 0 0 P₀ P₀).terms m = 0 := by
  rw [cf_lc]; simp

theorem der_bin_self {P₀ : Poly Nat} (h0 : Der p A D P₀) {l : List Nat} (hl : l.length ≤ D) :
    Der p A D (bin l l) :=
  Der.eq _ _ (Der.lin 0 0 _ _ h0 h0) (peq_of_cf fun m => by rw [cf_zero, cf_bin]; simp)
    (deg_bin hl hl)

theorem der_bin_perm {l₁ l₂ l₁' l₂' : List Nat} (h : Der p A D (bin l₁ l₂)) (h1 : l₁.Perm l₁')
    (h2 : l₂.Perm l₂') : Der p A D (bin l₁' l₂') := by
  have hd := (deg_le _ _).mp (der_deg h)
  refine Der.eq _ _ h (peq_of_cf fun m => ?_) (deg_bin ?_ ?_)
  · rw [cf_bin, cf_bin]
    have e1 : l₁.Perm m ↔ l₁'.Perm m := ⟨fun h => h1.symm.trans h, fun h => h1.trans h⟩
    have e2 : l₂.Perm m ↔ l₂'.Perm m := ⟨fun h => h2.symm.trans h, fun h => h2.trans h⟩
    simp only [e1, e2]
  · rw [← h1.length_eq]; exact hd (1, l₁) (by simp [bin])
  · rw [← h2.length_eq]; exact hd (-1, l₂) (by simp [bin])

theorem der_bin_trans {a b c : List Nat} (h1 : Der p A D (bin a b)) (h2 : Der p A D (bin b c)) :
    Der p A D (bin a c) := by
  have d1 := (deg_le _ _).mp (der_deg h1)
  have d2 := (deg_le _ _).mp (der_deg h2)
  refine Der.eq _ _ (Der.lin 1 1 _ _ h1 h2) (peq_of_cf fun m => ?_)
    (deg_bin (d1 (1, a) (by simp [bin])) (d2 (-1, c) (by simp [bin])))
  rw [cf_lc, cf_bin, cf_bin, cf_bin]; split <;> split <;> split <;> simp

theorem der_bin_mul {l₁ l₂ : List Nat} (x : Nat) (h : Der p A D (bin l₁ l₂))
    (h1 : l₁.length + 1 ≤ D) (h2 : l₂.length + 1 ≤ D) : Der p A D (bin (x :: l₁) (x :: l₂)) :=
  Der.mul x _ h (by
    have := deg_bin (D := D - 1) (l₁ := l₁) (l₂ := l₂) (by omega) (by omega); omega)

/-- `x·x·m - x·m` is derivable when `|m| + 2 ≤ D`. -/
theorem der_bool (x : Nat) : ∀ m : List Nat, m.length + 2 ≤ D →
    Der p A D (bin (x :: x :: m) (x :: m))
  | [], hD => Der.bool x (by simpa using hD)
  | y :: m, hD => by
    have ih := der_bool x m (by simp at hD; omega)
    have := der_bin_mul y ih (by simp at hD ⊢; omega) (by simp at hD ⊢; omega)
    refine der_bin_perm this ?_ ?_
    · exact (List.Perm.swap x y (x :: m)).trans (List.Perm.cons x (List.Perm.swap x y m))
    · exact List.Perm.swap x y m

/-! ## Multilinearisation of a monomial -/

/-- Remove repeated variables (keep the last occurrence). -/
def dd : List Nat → List Nat
  | [] => []
  | x :: m => if x ∈ m then dd m else x :: dd m

theorem mem_dd {x : Nat} : ∀ {m : List Nat}, x ∈ dd m ↔ x ∈ m
  | [] => by simp [dd]
  | y :: m => by
    unfold dd; split
    · rw [mem_dd]; constructor
      · exact fun h => List.mem_cons_of_mem _ h
      · intro h; rcases List.mem_cons.mp h with rfl | h
        · assumption
        · exact h
    · simp [mem_dd]

theorem nodup_dd : ∀ m : List Nat, (dd m).Nodup
  | [] => by simp [dd]
  | y :: m => by
    unfold dd; split
    · exact nodup_dd m
    · rename_i h; exact List.nodup_cons.mpr ⟨fun h' => h (mem_dd.mp h'), nodup_dd m⟩

theorem length_dd : ∀ m : List Nat, (dd m).length ≤ m.length
  | [] => by simp [dd]
  | y :: m => by
    unfold dd; split
    · have := length_dd m; simp; omega
    · have := length_dd m; simp; omega

/-- `m - dd m` is derivable when `|m| ≤ D`. -/
theorem der_dd {P₀ : Poly Nat} (h0 : Der p A D P₀) : ∀ m : List Nat, m.length ≤ D →
    Der p A D (bin m (dd m))
  | [], _ => der_bin_self h0 (by simp)
  | x :: m, hD => by
    have hm : m.length ≤ D := by simp at hD; omega
    have ih := der_dd h0 m hm
    unfold dd; split
    · rename_i hx
      have hp := List.perm_cons_erase hx
      have hl : (m.erase x).length + 2 ≤ D := by
        rw [List.length_erase_of_mem hx]; simp at hD
        have : m.length ≥ 1 := List.length_pos_of_mem hx; omega
      have hb := der_bin_perm (der_bool (p := p) (A := A) x (m.erase x) hl)
        (List.Perm.cons x hp).symm hp.symm
      exact der_bin_trans hb ih
    · have := length_dd m
      exact der_bin_mul x ih (by simp at hD; omega) (by simp at hD; omega)

/-! ## Reducing a whole term list to its multilinear form -/

/-- Multilinearise every monomial. -/
def ML (L : List (Int × List Nat)) : List (Int × List Nat) := L.map fun t => (t.1, dd t.2)

theorem der_of_ml : ∀ (L K : List (Int × List Nat)), (∀ t ∈ K ++ L, t.2.length ≤ D) →
    Der p A D ⟨K ++ ML L⟩ → Der p A D ⟨K ++ L⟩
  | [], K, _, h => by simpa [ML] using h
  | t :: L, K, hD, h => by
    have ht : t.2.length ≤ D := hD t (by simp)
    have hB := der_dd h t.2 ht
    have hX := Der.lin 1 t.1 _ _ h hB
    have hd : ∀ s ∈ (K ++ [t]) ++ ML L, s.2.length ≤ D := by
      intro s hs
      simp only [List.mem_append, List.mem_singleton, ML, List.mem_map] at hs
      rcases hs with (hs | rfl) | ⟨r, hr, rfl⟩
      · exact hD s (by simp [hs])
      · exact ht
      · exact Nat.le_trans (length_dd _) (hD r (by simp [hr]))
    have hY : Der p A D ⟨(K ++ [t]) ++ ML L⟩ :=
      Der.eq _ _ hX (peq_of_cf fun m => by
        rw [cf_lc, cf_bin]
        simp only [ML, List.map_cons, cf_append, cf_cons, cf_nil]
        split <;> split <;> simp <;> omega) ((deg_le _ _).mpr hd)
    have := der_of_ml L (K ++ [t]) (by
      intro s hs
      simp only [List.mem_append, List.mem_singleton] at hs
      rcases hs with (hs | rfl) | hs
      · exact hD s (by simp [hs])
      · exact ht
      · exact hD s (by simp [hs])) hY
    simpa using this

/-! ## Values -/

theorem monoEval_cons (a : Nat → Bool) (x : Nat) (m : List Nat) :
    monoEval a (x :: m) = (if a x then 1 else 0) * monoEval a m := by
  simp [monoEval]

theorem monoEval_dd (a : Nat → Bool) : ∀ m : List Nat, monoEval a (dd m) = monoEval a m
  | [] => rfl
  | x :: m => by
    unfold dd; split
    · rename_i hx
      rw [monoEval_dd a m, monoEval_cons, monoEval_perm a (List.perm_cons_erase hx), monoEval_cons]
      cases a x <;> simp
    · rw [monoEval_cons, monoEval_cons, monoEval_dd a m]

theorem ev_ML (a : Nat → Bool) (L : List (Int × List Nat)) : ev a (ML L) = ev a L := by
  induction L with
  | nil => rfl
  | cons t L ih =>
    simp only [ML, List.map_cons] at *
    rw [ev_cons, ev_cons, ih, monoEval_dd]

/-! ## Uniqueness of multilinear representatives -/

theorem perm_of_sub : ∀ (l m : List Nat), l.Nodup → m.Nodup → (∀ x ∈ l, x ∈ m) →
    m.length ≤ l.length → l.Perm m
  | [], m, _, _, _, hl => by
    have : m = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hl)
    subst this; exact List.Perm.refl _
  | x :: l, m, hn, hm, hs, hl => by
    have hx : x ∈ m := hs x (by simp)
    have hn' := List.nodup_cons.mp hn
    have ih := perm_of_sub l (m.erase x) hn'.2 (hm.erase x) (fun y hy => by
      rw [hm.mem_erase_iff]
      exact ⟨fun h => hn'.1 (h ▸ hy), hs y (List.mem_cons_of_mem _ hy)⟩) (by
      rw [List.length_erase_of_mem hx]; simp at hl; omega)
    exact (List.Perm.cons x ih).trans (List.perm_cons_erase hx).symm

theorem cf_eq_zero {L : List (Int × List Nat)} {m : List Nat} (h : ∀ t ∈ L, ¬ t.2.Perm m) :
    cf L m = 0 := by
  unfold cf
  rw [List.filter_eq_nil_iff.mpr (fun t ht => by simpa using h t ht)]; rfl

theorem cf_filter_of {L : List (Int × List Nat)} {m : List Nat} (q : Int × List Nat → Bool)
    (h : ∀ t ∈ L, t.2.Perm m → q t = true) : cf (L.filter q) m = cf L m := by
  unfold cf; rw [List.filter_filter]
  congr 2
  apply List.filter_congr
  intro t ht
  by_cases h1 : t.2.Perm m
  · simp [h1, h t ht h1]
  · simp [h1]

theorem ev_zero (a : Nat → Bool) : ∀ S : List (Int × List Nat), (∀ t ∈ S, monoEval a t.2 = 0) →
    ev a S = 0
  | [], _ => rfl
  | t :: S, h => by
    rw [ev_cons, h t (by simp), ev_zero a S (fun s hs => h s (by simp [hs]))]; simp

theorem monoEval_eq_zero (a : Nat → Bool) {x : Nat} : ∀ {l : List Nat}, x ∈ l → a x = false →
    monoEval a l = 0
  | y :: l, hx, ha => by
    rw [monoEval_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · simp [ha]
    · rw [monoEval_eq_zero a hx ha]; simp

theorem monoEval_eq_one (a : Nat → Bool) : ∀ {l : List Nat}, (∀ x ∈ l, a x = true) →
    monoEval a l = 1
  | [], _ => rfl
  | y :: l, h => by
    rw [monoEval_cons, monoEval_eq_one a (fun x hx => h x (by simp [hx])), h y (by simp)]; rfl

/-- A term list with multilinear monomials that vanishes mod `p` on the cube has every
coefficient `≡ 0` mod `p`. -/
theorem cf_ml_dvd {p : Int} {L : List (Int × List Nat)} (hL : ∀ t ∈ L, t.2.Nodup)
    (hv : ∀ a, p ∣ ev a L) : ∀ n m, m.length ≤ n → p ∣ cf L m := by
  intro n
  induction n with
  | zero =>
    intro m hm
    have : m = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    by_cases hn : ([] : List Nat).Nodup
    · have := hv (fun _ => false)
      rw [ev_split _ (fun s => decide (s.2.Perm [])), ev_same _ [] _ (fun s hs => by
        simpa using (List.mem_filter.mp hs).2)] at this
      rw [ev_zero _ _ (fun s hs => by
        have h1 := (List.mem_filter.mp hs)
        have : s.2 ≠ [] := fun h => by simp [h] at h1
        obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil s.2 this
        exact monoEval_eq_zero _ hx rfl)] at this
      simpa [cf, monoEval] using this
    · exact absurd List.nodup_nil hn
  | succ n ih =>
    intro m hm
    by_cases hn : m.Nodup
    · let a : Nat → Bool := fun x => decide (x ∈ m)
      let q1 : Int × List Nat → Bool := fun s => decide (s.2.Perm m)
      let q2 : Int × List Nat → Bool := fun s => s.2.all fun x => decide (x ∈ m)
      have h := hv a
      rw [ev_split a q1, ev_same a m _ (fun s hs => by simpa [q1] using (List.mem_filter.mp hs).2),
        monoEval_eq_one a (fun x hx => by simp [a, hx]), Int.mul_one,
        ev_split a q2 (L.filter fun t => !q1 t)] at h
      rw [ev_zero a ((L.filter fun t => !q1 t).filter fun t => !q2 t) (fun s hs => by
        have h2 := (List.mem_filter.mp hs).2
        simp only [q2, Bool.not_eq_true', List.all_eq_false] at h2
        obtain ⟨x, hx, hxm⟩ := h2
        exact monoEval_eq_zero a hx (by simp [a, hxm])), Int.add_zero] at h
      have hS : p ∣ ev a ((L.filter fun t => !q1 t).filter q2) := by
        apply ev_dvd p a _ _ (Nat.le_refl _)
        intro m'
        by_cases hx : ∃ t ∈ (L.filter fun t => !q1 t).filter q2, t.2.Perm m'
        · obtain ⟨t, ht, htm⟩ := hx
          have ht1 := List.mem_filter.mp ht
          have ht2 := List.mem_filter.mp ht1.1
          have hsub : ∀ x ∈ m', x ∈ m := fun x hx' => by
            have := ht1.2; simp only [q2, List.all_eq_true, decide_eq_true_eq] at this
            exact this x (htm.mem_iff.mpr hx')
          have hnp : ¬ m'.Perm m := fun h' => by
            have := ht2.2; simp only [q1, Bool.not_eq_true', decide_eq_false_iff_not] at this
            exact this (htm.trans h')
          have hnd : m'.Nodup := htm.nodup_iff.mp (hL t ht2.1)
          have hlt : m'.length < m.length := by
            apply Nat.lt_of_not_le; intro hle
            exact hnp (perm_of_sub m' m hnd hn hsub hle)
          rw [cf_filter_of q2 (fun s _ hs => by
              simp only [q2, List.all_eq_true, decide_eq_true_eq]
              exact fun x hx' => hsub x (hs.mem_iff.mp hx')),
            cf_filter_of (fun t => !q1 t) (fun s _ hs => by
              simp only [q1, Bool.not_eq_true', decide_eq_false_iff_not]
              exact fun h' => hnp (hs.symm.trans h'))]
          exact ih m' (by omega)
        · rw [cf_eq_zero (fun t ht h' => hx ⟨t, ht, h'⟩)]; exact Int.dvd_zero _
      have : p ∣ ((L.filter q1).map (·.1)).sum := by
        have := Int.dvd_sub h hS; simpa using this
      exact this
    · rw [cf_eq_zero (fun t ht h' => hn (h'.nodup_iff.mp (hL t ht)))]; exact Int.dvd_zero _

/-! ## Deriving every low-degree polynomial that agrees with a derived line -/

/-- If some line is derivable, every polynomial of degree `≤ D` vanishing mod `p` on the cube
is derivable. -/
theorem der_of_zero {P₀ R : Poly Nat} (h0 : Der p A D P₀) (hR : R.deg ≤ D)
    (hv : ∀ a, (p : Int) ∣ R.eval a) : Der p A D R := by
  have hRd := (deg_le _ _).mp hR
  have hM : Der p A D ⟨[] ++ ML R.terms⟩ := by
    refine Der.eq _ _ (Der.lin 0 0 _ _ h0 h0) (fun m => ?_) ((deg_le _ _).mpr ?_)
    · unfold coeff; rw [cf_zero]
      have := cf_ml_dvd (p := (p : Int)) (L := ML R.terms)
        (fun t ht => by
          simp only [ML, List.mem_map] at ht; obtain ⟨s, _, rfl⟩ := ht; exact nodup_dd _)
        (fun a => by rw [ev_ML]; exact hv a) _ m (Nat.le_refl _)
      simp only [List.nil_append]
      exact Int.dvd_sub (Int.dvd_zero _) this
    · intro t ht
      simp only [List.nil_append, ML, List.mem_map] at ht
      obtain ⟨s, hs, rfl⟩ := ht
      exact Nat.le_trans (length_dd _) (hRd s hs)
  have := der_of_ml R.terms [] (by simpa using hRd) hM
  simpa using this

/-- If `Q` is derivable and `R` has degree `≤ D` and agrees with `Q` mod `p` on the cube,
then `R` is derivable. -/
theorem der_of_cube {Q R : Poly Nat} (hQ : Der p A D Q) (hR : R.deg ≤ D)
    (hv : ∀ a, (p : Int) ∣ R.eval a - Q.eval a) : Der p A D R := by
  have hQd := (deg_le _ _).mp (der_deg hQ)
  have hRd := (deg_le _ _).mp hR
  have hS : Der p A D (lc 1 (-1) R Q) := der_of_zero hQ ((deg_le _ _).mpr (by
      intro t ht
      simp only [lc, List.mem_append, List.mem_map] at ht
      rcases ht with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩
      · exact hRd s hs
      · exact hQd s hs))
    (fun a => by rw [eval_lc]; have := hv a; simpa [Int.sub_eq_add_neg] using this)
  exact Der.eq _ _ (Der.lin 1 1 _ _ hQ hS) (peq_of_cf fun m => by
    rw [cf_lc, cf_lc]; omega) hR

/-! ## Translation -/

/-- Every `PPCDerivable` line is represented mod `p` on the cube by a standard derived line. -/
theorem ppc_std {g : (Nat → Bool) → Int} (h : PPCDerivable p A D g) :
    ∃ Q, Der p A D Q ∧ ∀ a, (p : Int) ∣ Q.eval a - g a := by
  induction h with
  | ax P hP hd => exact ⟨P, Der.ax P hP hd, fun a => by rw [Int.sub_self]; exact Int.dvd_zero _⟩
  | lin f g u v _ _ ihf ihg =>
    obtain ⟨Qf, hf, ef⟩ := ihf
    obtain ⟨Qg, hg, eg⟩ := ihg
    refine ⟨lc u v Qf Qg, Der.lin u v _ _ hf hg, fun a => ?_⟩
    rw [eval_lc]
    have : u * Qf.eval a + v * Qg.eval a - (u * f a + v * g a) =
        u * (Qf.eval a - f a) + v * (Qg.eval a - g a) := by
      rw [Int.mul_sub, Int.mul_sub]; omega
    rw [this]; exact Int.dvd_add (dvd_mul_of u (ef a)) (dvd_mul_of v (eg a))
  | mul x g d _ hc hd ih =>
    obtain ⟨Qg, hg, eg⟩ := ih
    obtain ⟨R, hR, eR⟩ := hc
    have hRder : Der p A D R := der_of_cube hg (by omega) (fun a => by
      have := Int.dvd_sub (eR a) (eg a)
      rwa [show R.eval a - g a - (Qg.eval a - g a) = R.eval a - Qg.eval a by omega] at this)
    refine ⟨R.mulVar x, Der.mul x R hRder (by omega), fun a => ?_⟩
    rw [eval_mulVar]
    have : (if a x = true then 1 else 0) * R.eval a - xv x a * g a = xv x a * (R.eval a - g a) := by
      unfold xv; rw [Int.mul_sub]
    rw [this]; exact dvd_mul_of _ (eR a)
  | congr f g _ hfg ih =>
    obtain ⟨Q, hQ, eQ⟩ := ih
    refine ⟨Q, hQ, fun a => ?_⟩
    have := Int.dvd_sub (eQ a) (hfg a)
    rwa [show Q.eval a - g a - (f a - g a) = Q.eval a - f a by omega] at this

/-- **Audit (b).** Every library `PPCRefutation p A D` gives a standard degree-`D` polynomial
calculus refutation of `A` over `F_p` with Boolean axioms (`Work.StdPC.Refutes p A D`). -/
theorem ppc_refutes (h : PPCRefutation p A D) : Refutes p A D := by
  obtain ⟨Q, hQ, eQ⟩ := ppc_std h
  exact der_of_cube hQ (by rw [deg_one]; exact Nat.zero_le _) (fun a => by
    rw [eval_one]; have := Int.dvd_neg.mpr (eQ a); rwa [Int.neg_sub] at this)

/-- With `Work.StdPC.refutes_ppc`: for `p > 1` the two notions of degree-`D` refutation agree. -/
theorem refutes_iff {p D : Nat} {A : List (Poly Nat)} (hp : 1 < p) :
    Refutes p A D ↔ PPCRefutation p A D :=
  ⟨refutes_ppc hp, ppc_refutes⟩

end Programme.«20261029-1156-proof-complexity».StdPCConv

#print axioms Programme.«20261029-1156-proof-complexity».StdPCConv.ppc_refutes
#print axioms Programme.«20261029-1156-proof-complexity».StdPCConv.refutes_iff
