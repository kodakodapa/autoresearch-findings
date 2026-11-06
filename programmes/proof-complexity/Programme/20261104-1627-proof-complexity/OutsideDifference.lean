import Programme.«20261104-1627-proof-complexity».SupportedCertificates
namespace Programme.«20261104-1627-proof-complexity».OutsideDifference
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261025-0459-proof-complexity».MatchQuot
open Programme.«20261025-1627-proof-complexity».NoDrop
open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261104-1627-proof-complexity».SupportedCertificates

def set (a : Nat → Bool) (x : Nat) (b : Bool) : Nat → Bool :=
  fun y => if y = x then b else a y

def diff (x : Nat) (P : Poly Nat) : Poly Nat :=
  ⟨(P.terms.filter (fun t => x ∈ t.2)).map
    (fun t => (t.1, t.2.filter (fun y => y != x)))⟩

theorem mono_set (a : Nat → Bool) (x : Nat) (m : List Nat) (b : Bool) :
    monoEval (set a x b) m =
      (if x ∈ m then (if b then 1 else 0) else 1) *
        monoEval a (m.filter (fun y => y != x)) := by
  induction m with
  | nil => simp [monoEval]
  | cons y m ih =>
    by_cases hy : y = x
    · subst y
      cases b <;> simp [Programme.«20261025-1627-proof-complexity».NoDrop.monoEval_cons, Programme.«20261024-1633-proof-complexity».PCTseitin.xv, set, ih]
    · cases b <;> cases ha : a y <;>
        simp [Programme.«20261025-1627-proof-complexity».NoDrop.monoEval_cons, Programme.«20261024-1633-proof-complexity».PCTseitin.xv, set, hy, Ne.symm hy, ih, ha] <;> split <;> simp_all

theorem diff_eval (x : Nat) (P : Poly Nat) (a : Nat → Bool) :
    (diff x P).eval a = P.eval (set a x true) - P.eval (set a x false) := by
  unfold diff Poly.eval
  rw [List.map_map]
  generalize P.terms = T
  induction T with
  | nil => simp
  | cons t T ih =>
    by_cases hx : x ∈ t.2
    · simp [hx, mono_set, ih]
      omega
    · simp [hx, mono_set, ih]
      omega

theorem erase_length (x : Nat) (m : List Nat) (hx : x ∈ m) :
    (m.filter (fun y => y != x)).length + 1 ≤ m.length := by
  induction m with
  | nil => simp at hx
  | cons y m ih =>
    by_cases hy : y = x
    · subst y
      simpa using Nat.add_le_add_right (List.length_filter_le (fun y => y != x) m) 1
    · have hm : x ∈ m := by simpa [hy, Ne.symm hy] using hx
      simpa [hy] using Nat.add_le_add_right (ih hm) 1

theorem diff_budget (x : Nat) (g A : Poly Nat) (D : Nat)
    (h : g.deg + A.deg ≤ D) (hA : A.deg < D) :
    (diff x g).deg + A.deg ≤ D-1 := by
  have hd : (diff x g).deg ≤ D-1-A.deg := by
    apply (deg_le_iff _ _).mpr
    intro t ht
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
    obtain ⟨hu, hx⟩ := List.mem_filter.mp hu
    have hx' : x ∈ u.2 := by simpa using hx
    have hl := erase_length x u.2 hx'
    have hg := (deg_le_iff g g.deg).mp (Nat.le_refl _) u hu
    dsimp
    omega
  omega

theorem ax_set {B : Nat → Bool} {P : Poly Nat} (hP : Supported B P)
    {x : Nat} (hx : B x = false) (a : Nat → Bool) (b : Bool) :
    P.eval (set a x b) = P.eval a := by
  apply eval_agree hP
  intro y hy
  have hne : y ≠ x := by intro he; subst y; simp_all
  simp [set, hne]

theorem good_set {B : Nat → Bool} {A : List (Poly Nat)}
    (hA : ∀ P ∈ A, Supported B P) {x : Nat} (hx : B x = false)
    (a : Nat → Bool) (ha : Good A a) (b : Bool) : Good A (set a x b) := by
  intro u v huv ht
  have hu : B u = true := hA _ huv (1,[u,v]) (by simp [prod2]) u (by simp)
  have hv : B v = true := hA _ huv (1,[u,v]) (by simp [prod2]) v (by simp)
  have hux : u ≠ x := by intro he; subst u; simp_all
  have hvx : v ≠ x := by intro he; subst v; simp_all
  apply ha u v huv
  simpa [set, hux, hvx] using ht

theorem nsIn_difference {p D : Nat} {B : Nat → Bool} {A : List (Poly Nat)}
    (hA : ∀ P ∈ A, Supported B P) (hdeg : ∀ P ∈ A, P.deg < D)
    {x : Nat} (hx : B x = false) {f : (Nat → Bool) → Int}
    (hf : NSIn p A D f) :
    NSIn p A (D-1) (fun a => f (set a x true) - f (set a x false)) := by
  obtain ⟨L, hL, he⟩ := hf
  refine ⟨L.map (fun e => (diff x e.1, e.2)), ?_, ?_⟩
  · intro e he
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp he
    exact ⟨(hL u hu).1, diff_budget x u.1 u.2 D (hL u hu).2 (hdeg _ (hL u hu).1)⟩
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
    rw [hs]
    have hh := Int.dvd_sub ht hf
    have eq : ((L.map (fun e => e.1.eval (set a x true) * e.2.eval (set a x true))).sum - f (set a x true)) -
        ((L.map (fun e => e.1.eval (set a x false) * e.2.eval (set a x false))).sum - f (set a x false)) =
        (L.map (fun e => e.1.eval (set a x true) * e.2.eval (set a x true))).sum -
        (L.map (fun e => e.1.eval (set a x false) * e.2.eval (set a x false))).sum -
        (f (set a x true) - f (set a x false)) := by omega
    rw [eq] at hh
    exact hh
def differences : List Nat → ((Nat → Bool) → Int) → ((Nat → Bool) → Int)
  | [], f => f
  | x :: xs, f => differences xs (fun a => f (set a x true) - f (set a x false))

theorem nsIn_differences {p D : Nat} {B : Nat → Bool} {A : List (Poly Nat)}
    (hA : ∀ P ∈ A, Supported B P) (s : List Nat)
    (hs : ∀ x ∈ s, B x = false)
    (hdeg : ∀ P ∈ A, P.deg + s.length ≤ D)
    {f : (Nat → Bool) → Int} (hf : NSIn p A D f) :
    NSIn p A (D-s.length) (differences s f) := by
  induction s generalizing D f with
  | nil => simpa [differences] using hf
  | cons x xs ih =>
    have hh := nsIn_difference hA
      (fun P hP => by have := hdeg P hP; simp only [List.length_cons] at this; omega)
      (hs x (by simp)) hf
    have hr := ih (D := D-1) (fun y hy => hs y (by simp [hy]))
      (fun P hP => by have := hdeg P hP; simp only [List.length_cons] at this; omega) hh
    simpa [differences, Nat.sub_sub, Nat.add_comm] using hr

/-- Boolean support coefficient: difference in each selected variable, then zero all outside variables. -/
def coefficient (B : Nat → Bool) (s : List Nat) (f : (Nat → Bool) → Int) :
    (Nat → Bool) → Int :=
  fun a => differences s f
    (Programme.«20261025-0459-proof-complexity».OntoSubst.pull
      (Programme.«20261104-1627-proof-complexity».OffboardSections.sectionSubst B (fun _ => false)) a)

theorem nsIn_coefficient {p D : Nat} {B : Nat → Bool} {A : List (Poly Nat)}
    (hA : ∀ P ∈ A, Supported B P) (s : List Nat)
    (hs : ∀ x ∈ s, B x = false)
    (hdeg : ∀ P ∈ A, P.deg + s.length ≤ D)
    {f : (Nat → Bool) → Int} (hf : NSIn p A D f) :
    NSIn p A (D-s.length) (coefficient B s f) := by
  apply Programme.«20261104-1627-proof-complexity».OffboardSections.nsIn_pull
    (Programme.«20261104-1627-proof-complexity».OffboardSections.sectionSubst B (fun _ => false))
    (fun a ha => good_section hA _ a ha)
  · intro P hP a
    apply eval_agree (hA P hP)
    intro x hx
    simp [Programme.«20261104-1627-proof-complexity».OffboardSections.pull_section, hx]
  · exact nsIn_differences hA s hs hdeg hf

end Programme.«20261104-1627-proof-complexity».OutsideDifference
#print axioms Programme.«20261104-1627-proof-complexity».OutsideDifference.nsIn_difference

#print axioms Programme.«20261104-1627-proof-complexity».OutsideDifference.nsIn_differences
#print axioms Programme.«20261104-1627-proof-complexity».OutsideDifference.nsIn_coefficient
