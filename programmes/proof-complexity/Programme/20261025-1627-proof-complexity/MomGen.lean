import Programme.«20261025-1627-proof-complexity».OntoExt2

/-!
# Generic moment functionals over subsets of size `≤ d`

`sumW N d W g = ∑_{S} W S · cf g S`, the sum over strictly decreasing lists `S` of variables `< N`
with `|S| ≤ d` (`Subs N d`). On a monomial it reads off `W` at the canonical form of its variable
set: `sumW N d W (monoEval · xs) = W (canon N xs)`, where `canon N xs` lists the members of `xs`
below `N` in decreasing order. `canon` depends only on the member set, so moment values are
automatically symmetric.
-/

namespace Programme.«20261025-1627-proof-complexity».MomGen

open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261024-1633-proof-complexity».PCTseitin
open Programme.«20261025-0459-proof-complexity».FinDiff
open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-1627-proof-complexity».PCCertCore (cf_mono sameSet sameSet_iff)
open Programme.«20261025-1627-proof-complexity».DesignExt
open Programme.«20261025-1627-proof-complexity».OntoExt2 (SN dt_supp)

def Subs : Nat → Nat → List (List Nat)
  | 0, _ => [[]]
  | _ + 1, 0 => [[]]
  | N + 1, d + 1 => Subs N (d + 1) ++ (Subs N d).map (N :: ·)

def canon : Nat → List Nat → List Nat
  | 0, _ => []
  | N + 1, xs => if N ∈ xs then N :: canon N xs else canon N xs

theorem subs_prop : ∀ (N d : Nat) (S : List Nat), S ∈ Subs N d →
    S.Nodup ∧ (∀ x ∈ S, x < N) ∧ S.length ≤ d := by
  intro N
  induction N with
  | zero => intro d S h; simp [Subs] at h; subst h; simp
  | succ N ih =>
    intro d S h
    cases d with
    | zero => simp [Subs] at h; subst h; simp
    | succ d =>
      simp only [Subs, List.mem_append, List.mem_map] at h
      rcases h with h | ⟨S', hS', rfl⟩
      · obtain ⟨a, b, c⟩ := ih _ S h
        exact ⟨a, fun x hx => by have := b x hx; omega, c⟩
      · obtain ⟨a, b, c⟩ := ih _ S' hS'
        refine ⟨List.nodup_cons.mpr ⟨fun hm => by have := b N hm; omega, a⟩, ?_, by simp; omega⟩
        intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · omega
        · have := b x hx; omega

theorem mem_canon : ∀ (N : Nat) (xs : List Nat) (x : Nat), x ∈ canon N xs ↔ x ∈ xs ∧ x < N := by
  intro N
  induction N with
  | zero => intro xs x; simp [canon]
  | succ N ih =>
    intro xs x
    unfold canon
    by_cases h : N ∈ xs
    · rw [if_pos h, List.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨a, b⟩)
        · exact ⟨h, by omega⟩
        · exact ⟨a, by omega⟩
      · rintro ⟨a, b⟩
        by_cases hx : x = N
        · exact Or.inl hx
        · exact Or.inr ⟨a, by omega⟩
    · rw [if_neg h, ih]
      constructor
      · rintro ⟨a, b⟩; exact ⟨a, by omega⟩
      · rintro ⟨a, b⟩
        refine ⟨a, ?_⟩
        by_cases hx : x = N
        · subst hx; exact absurd a h
        · omega

theorem canon_nodup : ∀ (N : Nat) (xs : List Nat), (canon N xs).Nodup := by
  intro N
  induction N with
  | zero => intro xs; simp [canon]
  | succ N ih =>
    intro xs
    unfold canon
    split
    · refine List.nodup_cons.mpr ⟨fun hm => ?_, ih xs⟩
      have := ((mem_canon N xs N).mp hm).2; omega
    · exact ih xs

/-- `canon` depends only on membership below `N`. -/
theorem canon_congr : ∀ (N : Nat) (xs ys : List Nat), (∀ x, x < N → (x ∈ xs ↔ x ∈ ys)) →
    canon N xs = canon N ys := by
  intro N
  induction N with
  | zero => intro xs ys _; rfl
  | succ N ih =>
    intro xs ys h
    have h' : ∀ x, x < N → (x ∈ xs ↔ x ∈ ys) := fun x hx => h x (by omega)
    have hN := h N (by omega)
    unfold canon
    by_cases hx : N ∈ xs
    · rw [if_pos hx, if_pos (hN.mp hx), ih xs ys h']
    · rw [if_neg hx, if_neg (fun hy => hx (hN.mpr hy)), ih xs ys h']

theorem nodup_len : ∀ (l m : List Nat), l.Nodup → (∀ x ∈ l, x ∈ m) → l.length ≤ m.length := by
  intro l
  induction l with
  | nil => intro m _ _; simp
  | cons x l ih =>
    intro m hl hs
    rw [List.nodup_cons] at hl
    have hx : x ∈ m := hs x List.mem_cons_self
    have h1 := ih (m.erase x) hl.2 (fun y hy => by
      have hyx : y ≠ x := fun h => hl.1 (h ▸ hy)
      exact (List.mem_erase_of_ne hyx).mpr (hs y (List.mem_cons_of_mem _ hy)))
    rw [List.length_erase_of_mem hx] at h1
    have : 0 < m.length := List.length_pos_of_mem hx
    simp; omega

theorem canon_length_le (N : Nat) (xs : List Nat) : (canon N xs).length ≤ xs.length :=
  nodup_len _ _ (canon_nodup N xs) (fun x hx => ((mem_canon N xs x).mp hx).1)

theorem lsum_zero (L : List (List Nat)) (f : List Nat → Int) (h : ∀ S ∈ L, f S = 0) :
    (L.map f).sum = 0 := by
  induction L with
  | nil => rfl
  | cons S L ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [h S List.mem_cons_self, ih (fun T hT => h T (List.mem_cons_of_mem _ hT))]; rfl

/-- Exactly one subset in `Subs N d` has the member set of `ys`: `canon N ys`. -/
theorem count : ∀ (N d : Nat) (W : List Nat → Int) (ys : List Nat), (∀ x ∈ ys, x < N) →
    (canon N ys).length ≤ d →
    ((Subs N d).map fun S => W S * (if sameSet S ys then 1 else 0)).sum = W (canon N ys) := by
  intro N
  induction N with
  | zero =>
    intro d W ys hy _
    have : ys = [] := by
      cases ys with
      | nil => rfl
      | cons y ys => have := hy y List.mem_cons_self; omega
    subst this
    simp [Subs, canon, sameSet]
  | succ N ih =>
    intro d W ys hy hl
    cases d with
    | zero =>
      have hc : canon (N + 1) ys = [] := List.eq_nil_of_length_eq_zero (by omega)
      have hys : ys = [] := by
        cases ys with
        | nil => rfl
        | cons y ys =>
          have h1 := (mem_canon (N + 1) (y :: ys) y).mpr ⟨List.mem_cons_self, hy y List.mem_cons_self⟩
          rw [hc] at h1; simp at h1
      subst hys
      simp [Subs, canon, sameSet] at hc ⊢
      rw [hc]
    | succ d =>
      simp only [Subs, List.map_append, List.sum_append, List.map_map]
      by_cases hN : N ∈ ys
      · have hc : canon (N + 1) ys = N :: canon N ys := by simp only [canon, if_pos hN]
        have h1 : ((Subs N (d + 1)).map fun S => W S * (if sameSet S ys then 1 else 0)).sum = 0 := by
          apply lsum_zero
          intro S hS
          have := (subs_prop N _ S hS).2.1
          have hf : sameSet S ys = false := by
            cases h : sameSet S ys
            · rfl
            · have := this N (((sameSet_iff S ys).mp h N).mpr hN); omega
          simp [hf]
        let ys' := ys.filter (fun x => x != N)
        have hmem' : ∀ x, x ∈ ys' ↔ x ∈ ys ∧ x ≠ N := by intro x; simp [ys']
        have hy' : ∀ x ∈ ys', x < N := by
          intro x hx; have := (hmem' x).mp hx; have := hy x this.1; omega
        have hcc : canon N ys' = canon N ys :=
          canon_congr N ys' ys (fun x hx => by rw [hmem']; constructor <;> intro h <;> (try exact h.1) <;> exact ⟨h, by omega⟩)
        have h2 : ((Subs N d).map ((fun S => W S * (if sameSet S ys then 1 else 0)) ∘ (N :: ·))).sum =
            ((Subs N d).map fun S => W (N :: S) * (if sameSet S ys' then 1 else 0)).sum := by
          congr 1
          apply List.map_congr_left
          intro S hS
          have hSN : ∀ x ∈ S, x < N := (subs_prop N d S hS).2.1
          have : sameSet (N :: S) ys = sameSet S ys' := by
            apply Bool.eq_iff_iff.mpr
            rw [sameSet_iff, sameSet_iff]
            constructor
            · intro h x
              rw [hmem']
              constructor
              · intro hx; have := hSN x hx
                exact ⟨(h x).mp (List.mem_cons_of_mem _ hx), by omega⟩
              · rintro ⟨a, b⟩
                have := (h x).mpr a
                simp only [List.mem_cons] at this
                rcases this with rfl | h; · exact absurd rfl b
                exact h
            · intro h x
              simp only [List.mem_cons]
              constructor
              · rintro (rfl | hx)
                · exact hN
                · exact ((hmem' x).mp ((h x).mp hx)).1
              · intro hx
                by_cases hxN : x = N
                · exact Or.inl hxN
                · exact Or.inr ((h x).mpr ((hmem' x).mpr ⟨hx, hxN⟩))
          simp only [Function.comp, this]
        rw [h1, h2, ih d (fun S => W (N :: S)) ys' hy' (by rw [hcc]; rw [hc] at hl; simp at hl; omega), hcc, hc]
        simp
      · have hc : canon (N + 1) ys = canon N ys := by simp only [canon, if_neg hN]
        have h2 : ((Subs N d).map ((fun S => W S * (if sameSet S ys then 1 else 0)) ∘ (N :: ·))).sum = 0 := by
          apply lsum_zero
          intro S _
          have hf : sameSet (N :: S) ys = false := by
            cases h : sameSet (N :: S) ys
            · rfl
            · exact absurd (((sameSet_iff _ ys).mp h N).mp List.mem_cons_self) hN
          simp [Function.comp, hf]
        have hy' : ∀ x ∈ ys, x < N := by
          intro x hx; have := hy x hx
          have : x ≠ N := fun h => hN (h ▸ hx)
          omega
        rw [h2, ih (d + 1) W ys hy' (by rw [hc] at hl; exact hl), hc]
        simp

/-! ## Monomials depend only on their member set -/

theorem monoEval_all (a : Nat → Bool) (xs : List Nat) :
    monoEval a xs = if xs.all a then 1 else 0 := by
  induction xs with
  | nil => simp [monoEval]
  | cons x xs ih =>
    have : monoEval a (x :: xs) = (if a x then 1 else 0) * monoEval a xs := by simp [monoEval]
    rw [this, ih]
    cases h : a x <;> simp [h]

theorem monoEval_congr (a : Nat → Bool) (xs ys : List Nat) (h : ∀ x, x ∈ xs ↔ x ∈ ys) :
    monoEval a xs = monoEval a ys := by
  rw [monoEval_all, monoEval_all]
  have : xs.all a = ys.all a := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true]
    constructor
    · intro h1 x hx; exact h1 x ((h x).mpr hx)
    · intro h1 x hx; exact h1 x ((h x).mp hx)
  rw [this]

theorem monoEval_canon (N : Nat) (a : Nat → Bool) (xs : List Nat) (hx : ∀ x ∈ xs, x < N) :
    monoEval a xs = monoEval a (canon N xs) :=
  monoEval_congr a _ _ (fun x => by rw [mem_canon]; constructor <;> intro h <;> (try exact h.1) <;> exact ⟨h, hx x h⟩)

theorem monoEval_zero {N : Nat} {a : Nat → Bool} (ha : SN N a) (xs : List Nat) (x : Nat) (hx : x ∈ xs)
    (hxN : N ≤ x) : monoEval a xs = 0 := by
  rw [monoEval_all]
  have : xs.all a = false := by
    cases h : xs.all a
    · rfl
    · have := (List.all_eq_true.mp h) x hx; rw [ha x hxN] at this; cases this
  rw [this]; rfl

/-! ## The functional -/

def sumW (N d : Nat) (W : List Nat → Int) (g : (Nat → Bool) → Int) : Int :=
  ((Subs N d).map fun S => W S * cf g S).sum

theorem lsum_lin (L : List (List Nat)) (A B C : List Nat → Int) (s t : Int)
    (h : ∀ S ∈ L, A S = s * B S + t * C S) :
    (L.map A).sum = s * (L.map B).sum + t * (L.map C).sum := by
  induction L with
  | nil => simp
  | cons S L ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [h S List.mem_cons_self, ih (fun T hT => h T (List.mem_cons_of_mem _ hT))]
    grind

theorem sumW_lin (N d : Nat) (W : List Nat → Int) (f g : (Nat → Bool) → Int) (s t : Int) :
    sumW N d W (fun a => s * f a + t * g a) = s * sumW N d W f + t * sumW N d W g := by
  unfold sumW
  exact lsum_lin _ _ _ _ s t (fun S _ => by rw [cf_lin]; grind)

theorem lsum_dvd (p : Int) (L : List (List Nat)) (A : List Nat → Int) (h : ∀ S ∈ L, p ∣ A S) :
    p ∣ (L.map A).sum := by
  induction L with
  | nil => exact ⟨0, by simp⟩
  | cons S L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Int.dvd_add (h S List.mem_cons_self) (ih (fun T hT => h T (List.mem_cons_of_mem _ hT)))

theorem lsum_sub (L : List (List Nat)) (A B : List Nat → Int) :
    (L.map A).sum - (L.map B).sum = (L.map fun S => A S - B S).sum := by
  induction L with
  | nil => simp
  | cons S L ih => simp only [List.map_cons, List.sum_cons]; rw [← ih]; omega

def sumWFn (p N d : Nat) (W : List Nat → Int) : Fn p (SN N) where
  E := sumW N d W
  lin f g s t := by rw [sumW_lin, Int.sub_self]; exact ⟨0, by simp⟩
  congr f g h := by
    unfold sumW
    rw [lsum_sub]
    apply lsum_dvd
    intro S _
    rw [← Int.mul_sub]
    exact dvd_cmul _ (cf_congr p f g h S)
  supp f g h := by
    unfold sumW
    congr 1
    apply List.map_congr_left
    intro S hS
    have := dt_supp N f g h S (subs_prop N d S hS).2.1 z0 (fun _ _ => rfl)
    unfold cf; rw [this]

/-- **Moments of monomials.** -/
theorem sumW_mono (N d : Nat) (W : List Nat → Int) (xs : List Nat) (hx : ∀ x ∈ xs, x < N)
    (hl : (canon N xs).length ≤ d) :
    sumW N d W (fun a => monoEval a xs) = W (canon N xs) := by
  have e : (fun a => monoEval a xs) = fun a => monoEval a (canon N xs) := by
    funext a; exact monoEval_canon N a xs hx
  rw [e]
  unfold sumW
  have e2 : ((Subs N d).map fun S => W S * cf (fun a => monoEval a (canon N xs)) S) =
      ((Subs N d).map fun S => W S * (if sameSet S (canon N xs) then 1 else 0)) := by
    apply List.map_congr_left
    intro S hS
    rw [cf_mono _ (canon_nodup N xs) S (subs_prop N d S hS).1]
  rw [e2]
  have hcc : canon N (canon N xs) = canon N xs :=
    canon_congr N _ _ (fun x hxN => by rw [mem_canon]; constructor <;> intro h <;> (try exact h.1) <;> exact ⟨h, hxN⟩)
  have := count N d W (canon N xs) (fun x hx => ((mem_canon N xs x).mp hx).2) (by rw [hcc]; exact hl)
  rw [this, hcc]

end Programme.«20261025-1627-proof-complexity».MomGen
