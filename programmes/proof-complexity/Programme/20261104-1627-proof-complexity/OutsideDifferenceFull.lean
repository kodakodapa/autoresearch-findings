import Programme.«20261104-1627-proof-complexity».OutsideDifference
namespace Programme.«20261104-1627-proof-complexity».OutsideDifference
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261025-0459-proof-complexity».MatchQuot
open Programme.«20261025-1627-proof-complexity».NoDrop
open Programme.«20261104-1627-proof-complexity».SupportedCertificates

theorem diff_zero (x : Nat) (P : Poly Nat) (h : P.deg = 0) : diff x P = ⟨[]⟩ := by
  have hf : P.terms.filter (fun t => x ∈ t.2) = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro t ht
    obtain ⟨ht, hx⟩ := List.mem_filter.mp ht
    have hd := (deg_le_iff P 0).mp (by omega) t ht
    have he : t.2 = [] := by cases he : t.2 with | nil => rfl | cons y ys => simp [he] at hd
    simpa [he] using hx
  simp [diff, hf]

theorem filter_sum_zero {α : Type} (L : List α) (b : α → Bool) (f : α → Int)
    (h : ∀ e ∈ L, b e ≠ true → f e = 0) :
    ((L.filter b).map f).sum = (L.map f).sum := by
  induction L with
  | nil => simp
  | cons e L ih =>
    have hh := ih (fun u hu => h u (by simp [hu]))
    cases hb : b e <;> simp_all

theorem nsIn_difference_full {p D : Nat} {B : Nat → Bool} {A : List (Poly Nat)}
    (hA : ∀ P ∈ A, Supported B P)
    {x : Nat} (hx : B x = false) {f : (Nat → Bool) → Int}
    (hf : NSIn p A D f) :
    NSIn p A (D-1) (fun a => f (set a x true) - f (set a x false)) := by
  obtain ⟨L, hL, he⟩ := hf
  refine ⟨(L.filter (fun e => e.2.deg < D)).map (fun e => (diff x e.1, e.2)), ?_, ?_⟩
  · intro e he
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp he
    obtain ⟨hu, hd⟩ := List.mem_filter.mp hu
    exact ⟨(hL u hu).1, diff_budget x u.1 u.2 D (hL u hu).2 (by simpa using hd)⟩
  · intro a ha
    have ht := he (set a x true) (good_set hA hx a ha true)
    have hf := he (set a x false) (good_set hA hx a ha false)
    have hs : ((L.map (fun e => (diff x e.1, e.2))).map
        (fun e => e.1.eval a * e.2.eval a)).sum =
        (L.map (fun e => e.1.eval (set a x true) * e.2.eval (set a x true))).sum -
        (L.map (fun e => e.1.eval (set a x false) * e.2.eval (set a x false))).sum := by
      rw [List.map_map]
      have hax := fun e (he : e ∈ L) b => ax_set (hA e.2 (hL e he).1) hx a b
      have point : ∀ e ∈ L,
          (diff x e.1).eval a * e.2.eval a =
          e.1.eval (set a x true) * e.2.eval (set a x true) -
          e.1.eval (set a x false) * e.2.eval (set a x false) := by
        intro e he
        rw [diff_eval, hax e he true, hax e he false, Int.sub_mul]
      have eq : (L.map ((fun e => e.1.eval a * e.2.eval a) ∘
          (fun e => (diff x e.1, e.2)))) = L.map (fun e =>
          e.1.eval (set a x true) * e.2.eval (set a x true) -
          e.1.eval (set a x false) * e.2.eval (set a x false)) := by
        apply List.map_congr_left
        exact point
      rw [eq]
      clear eq point hax ht hf he hL
      induction L with
      | nil => simp
      | cons e L ih => simp only [List.map_cons, List.sum_cons]; rw [ih]; omega
    have hfilter : (((L.filter (fun e => e.2.deg < D)).map (fun e => (diff x e.1, e.2))).map
        (fun e => e.1.eval a * e.2.eval a)).sum =
        ((L.map (fun e => (diff x e.1, e.2))).map (fun e => e.1.eval a * e.2.eval a)).sum := by
      simp only [List.map_map]
      apply filter_sum_zero
      intro e he hn
      have hb := (hL e he).2
      have hd : e.1.deg = 0 := by
        have hh : ¬ e.2.deg < D := by simpa using hn
        omega
      change (diff x e.1).eval a * e.2.eval a = 0
      rw [diff_zero x e.1 hd]
      simp [Poly.eval]
    rw [hfilter, hs]
    have hh := Int.dvd_sub ht hf
    have eq : ((L.map (fun e => e.1.eval (set a x true) * e.2.eval (set a x true))).sum - f (set a x true)) -
        ((L.map (fun e => e.1.eval (set a x false) * e.2.eval (set a x false))).sum - f (set a x false)) =
        (L.map (fun e => e.1.eval (set a x true) * e.2.eval (set a x true))).sum -
        (L.map (fun e => e.1.eval (set a x false) * e.2.eval (set a x false))).sum -
        (f (set a x true) - f (set a x false)) := by omega
    rw [eq] at hh
    exact hh

theorem nsIn_differences_full {p D : Nat} {B : Nat → Bool} {A : List (Poly Nat)}
    (hA : ∀ P ∈ A, Supported B P) (s : List Nat)
    (hs : ∀ x ∈ s, B x = false)
    {f : (Nat → Bool) → Int} (hf : NSIn p A D f) :
    NSIn p A (D-s.length) (differences s f) := by
  induction s generalizing D f with
  | nil => simpa [differences] using hf
  | cons x xs ih =>
    have hh := nsIn_difference_full hA (hs x (by simp)) hf
    have hr := ih (D := D-1) (fun y hy => hs y (by simp [hy])) hh
    simpa [differences, Nat.sub_sub, Nat.add_comm] using hr

theorem nsIn_coefficient_full {p D : Nat} {B : Nat → Bool} {A : List (Poly Nat)}
    (hA : ∀ P ∈ A, Supported B P) (s : List Nat)
    (hs : ∀ x ∈ s, B x = false)
    {f : (Nat → Bool) → Int} (hf : NSIn p A D f) :
    NSIn p A (D-s.length) (coefficient B s f) := by
  apply Programme.«20261104-1627-proof-complexity».OffboardSections.nsIn_pull
    (Programme.«20261104-1627-proof-complexity».OffboardSections.sectionSubst B (fun _ => false))
    (fun a ha => good_section hA _ a ha)
  · intro P hP a
    apply eval_agree (hA P hP)
    intro x hx
    simp [Programme.«20261104-1627-proof-complexity».OffboardSections.pull_section, hx]
  · exact nsIn_differences_full hA s hs hf

end Programme.«20261104-1627-proof-complexity».OutsideDifference
#print axioms Programme.«20261104-1627-proof-complexity».OutsideDifference.nsIn_difference_full

#print axioms Programme.«20261104-1627-proof-complexity».OutsideDifference.nsIn_differences_full
#print axioms Programme.«20261104-1627-proof-complexity».OutsideDifference.nsIn_coefficient_full
