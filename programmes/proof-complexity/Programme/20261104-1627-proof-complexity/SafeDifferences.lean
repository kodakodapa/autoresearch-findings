import Programme.«20261104-1627-proof-complexity».MatchingTestPoints
import Programme.«20261104-1627-proof-complexity».OutsideDifference

namespace Programme.«20261104-1627-proof-complexity».SafeDifferences
open Classical
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261025-0459-proof-complexity».MatchQuot
open Programme.«20261104-1627-proof-complexity».MatchingReduction Programme.«20261104-1627-proof-complexity».MatchingTestPoints Programme.«20261104-1627-proof-complexity».OutsideDifference

def Below (s : List Nat) (a : Nat → Bool) : Prop :=
  ∀ x, a x = true → x ∈ s

theorem good_below {A : List (Poly Nat)} {s : List Nat}
    (hs : Safe A s) {a : Nat → Bool} (ha : Below s a) : Good A a := by
  intro u v huv h
  exact hs u (ha u h.1) v (ha v h.2) huv

theorem differences_congruence {p : Nat} {A : List (Poly Nat)}
    {f g : (Nat → Bool) → Int}
    (h : ∀ a, Good A a → (p : Int) ∣ f a - g a)
    {s : List Nat} (hs : Safe A s) (u : List Nat)
    (hu : ∀ x ∈ u, x ∈ s) {a : Nat → Bool} (ha : Below s a) :
    (p : Int) ∣ differences u f a - differences u g a := by
  have general : ∀ u (f g : (Nat → Bool) → Int),
      (∀ a, Below s a → (p : Int) ∣ f a - g a) →
      (∀ x ∈ u, x ∈ s) → ∀ a, Below s a →
      (p : Int) ∣ differences u f a - differences u g a := by
    intro u
    induction u with
    | nil => intro f g h hu a ha; exact h a ha
    | cons x xs ih =>
      intro f g h hu a ha
      apply ih _ _ _ (fun y hy => hu y (by simp [hy])) a ha
      intro b hb
      have hb' : ∀ c, Below s (set b x c) := by
        intro c y hy
        by_cases he : y = x
        · subst y; exact hu x (by simp)
        · exact hb y (by simpa [OutsideDifference.set, he] using hy)
      have ht := h (set b x true) (hb' true)
      have hf := h (set b x false) (hb' false)
      have hh := Int.dvd_sub ht hf
      have he : f (set b x true) - g (set b x true) -
          (f (set b x false) - g (set b x false)) =
          f (set b x true) - f (set b x false) -
          (g (set b x true) - g (set b x false)) := by omega
      rw [he] at hh
      exact hh
  exact general u f g (fun a ha => h a (good_below hs ha)) hu a ha

def derived : List Nat → Poly Nat → Poly Nat
  | [], P => P
  | x :: xs, P => derived xs (diff x P)

theorem derived_eval (s : List Nat) (P : Poly Nat) (a : Nat → Bool) :
    (derived s P).eval a = differences s P.eval a := by
  induction s generalizing P with
  | nil => rfl
  | cons x xs ih =>
    rw [derived, ih]
    simp only [diff_eval]
    rfl

/-- Each chosen variable is removed, with all its repetitions removed at once. -/
def selected : List Nat → List Nat → Bool
  | [], t => t.isEmpty
  | x :: xs, t => decide (x ∈ t) && selected xs (t.filter (fun y => y != x))

def coefficient (s : List Nat) (P : Poly Nat) : Int :=
  (P.terms.map (fun t => t.1 * if selected s t.2 then 1 else 0)).sum

theorem selected_iff (s t : List Nat) (hs : s.Nodup) :
    selected s t = true ↔ ∀ y, y ∈ s ↔ y ∈ t := by
  induction s generalizing t with
  | nil =>
    simp only [selected, List.isEmpty_iff, List.mem_nil_iff, false_iff]
    exact List.eq_nil_iff_forall_not_mem
  | cons x xs ih =>
    obtain ⟨hx, hxs⟩ := List.nodup_cons.mp hs
    rw [selected, Bool.and_eq_true, decide_eq_true_eq, ih _ hxs]
    constructor
    · rintro ⟨hxt, h⟩ y
      constructor
      · intro hy
        rcases List.mem_cons.mp hy with he | hy
        · simpa [he] using hxt
        · exact (List.mem_filter.mp ((h y).mp hy)).1
      · intro hy
        by_cases he : y = x
        · simp [he]
        · exact List.mem_cons.mpr (Or.inr ((h y).mpr
            (List.mem_filter.mpr ⟨hy, by simpa using he⟩)))
    · intro h
      refine ⟨(h x).mp (by simp), ?_⟩
      intro y
      constructor
      · intro hy
        apply List.mem_filter.mpr
        refine ⟨(h y).mp (by simp [hy]), ?_⟩
        have he : y ≠ x := by intro he; subst y; exact hx hy
        simpa using he
      · intro hy
        obtain ⟨hyt, hyx⟩ := List.mem_filter.mp hy
        have he : y ≠ x := by simpa using hyx
        rcases List.mem_cons.mp ((h y).mpr hyt) with he' | hy'
        · exact False.elim (he he')
        · exact hy'

theorem coefficient_diff (s : List Nat) (x : Nat) (P : Poly Nat) :
    coefficient s (diff x P) = coefficient (x :: s) P := by
  classical
  unfold coefficient diff
  rw [List.map_map]
  generalize P.terms = T
  induction T with
  | nil => simp
  | cons t T ih =>
    by_cases hx : x ∈ t.2 <;> simp [hx, selected, ih]

theorem coefficient_eval (s : List Nat) (P : Poly Nat) :
    coefficient s P = (derived s P).eval (fun _ => false) := by
  induction s generalizing P with
  | nil =>
    unfold coefficient derived Poly.eval
    apply congrArg List.sum
    apply List.map_congr_left
    intro t ht
    cases ht' : t.2 with
    | nil => simp [selected, monoEval_all, ht', List.forall_mem_cons]
    | cons x xs =>
      have hn : ¬ (∀ y ∈ x :: xs, False) := by
        intro h; have := h x (by simp); contradiction
      simp only [selected, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
        Int.mul_zero, monoEval_all]
      rw [if_neg hn, Int.mul_zero]
  | cons x xs ih => rw [← coefficient_diff, ih]; rfl

theorem coefficient_congruence {p : Nat} {A : List (Poly Nat)}
    {P Q : Poly Nat}
    (h : ∀ a, Good A a → (p : Int) ∣ P.eval a - Q.eval a)
    {s : List Nat} (hs : Safe A s) :
    (p : Int) ∣ coefficient s P - coefficient s Q := by
  rw [coefficient_eval, coefficient_eval, derived_eval, derived_eval]
  exact differences_congruence h hs s (fun _ hx => hx) (by intro x hx; simp at hx)

theorem support_coefficient_congruence {p : Nat} {A : List (Poly Nat)}
    {P Q : Poly Nat}
    (h : ∀ a, Good A a → (p : Int) ∣ P.eval a - Q.eval a)
    {s : List Nat} (hs : Safe A s) (hn : s.Nodup) :
    (p : Int) ∣
      (P.terms.map (fun t => t.1 * if ∀ y, y ∈ s ↔ y ∈ t.2 then 1 else 0)).sum -
      (Q.terms.map (fun t => t.1 * if ∀ y, y ∈ s ↔ y ∈ t.2 then 1 else 0)).sum := by
  classical
  simpa only [coefficient, selected_iff s _ hn] using coefficient_congruence h hs

end Programme.«20261104-1627-proof-complexity».SafeDifferences
#print axioms Programme.«20261104-1627-proof-complexity».SafeDifferences.coefficient_congruence
#print axioms Programme.«20261104-1627-proof-complexity».SafeDifferences.support_coefficient_congruence
