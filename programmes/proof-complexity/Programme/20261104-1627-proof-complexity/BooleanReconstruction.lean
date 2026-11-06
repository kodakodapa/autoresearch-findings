import Programme.«20261104-1627-proof-complexity».OutsideDifferenceFull
namespace Programme.«20261104-1627-proof-complexity».BooleanReconstruction
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261024-1633-proof-complexity».PCTseitin
open Programme.«20261025-0459-proof-complexity».MatchQuot
open Programme.«20261025-1627-proof-complexity».NoDrop
open Programme.«20261025-0459-proof-complexity».OntoSubst
open Programme.«20261104-1627-proof-complexity».OutsideDifference Programme.«20261104-1627-proof-complexity».SupportedCertificates
abbrev Fn := (Nat → Bool) → Int
def expand : List Nat → Fn → List (List Nat × Fn)
  | [], f => [([], f)]
  | x :: xs, f => expand xs (fun a => f (Programme.«20261104-1627-proof-complexity».OutsideDifference.set a x false)) ++
      (expand xs (fun a => f (Programme.«20261104-1627-proof-complexity».OutsideDifference.set a x true) - f (Programme.«20261104-1627-proof-complexity».OutsideDifference.set a x false))).map
        (fun e => (x :: e.1, e.2))
theorem reconstruction (s : List Nat) (f : Fn) (a : Nat → Bool) :
    ((expand s f).map (fun e => monoEval a e.1 * e.2 a)).sum = f a := by
  induction s generalizing f with
  | nil => simp [expand, monoEval]
  | cons x xs ih =>
    simp only [expand, List.map_append, List.sum_append, List.map_map]
    rw [ih]
    have he : ((expand xs (fun a => f (Programme.«20261104-1627-proof-complexity».OutsideDifference.set a x true) - f (Programme.«20261104-1627-proof-complexity».OutsideDifference.set a x false))).map
        ((fun (e : List Nat × Fn) => monoEval a e.1 * e.2 a) ∘ (fun e => (x :: e.1, e.2)))).sum =
        xv x a * ((expand xs (fun a => f (Programme.«20261104-1627-proof-complexity».OutsideDifference.set a x true) - f (Programme.«20261104-1627-proof-complexity».OutsideDifference.set a x false))).map
          (fun e => monoEval a e.1 * e.2 a)).sum := by
      generalize expand xs (fun a => f (Programme.«20261104-1627-proof-complexity».OutsideDifference.set a x true) - f (Programme.«20261104-1627-proof-complexity».OutsideDifference.set a x false)) = L
      induction L with
      | nil => simp
      | cons e L h => simp [Programme.«20261025-1627-proof-complexity».NoDrop.monoEval_cons, Int.mul_assoc, Int.mul_add, h]
    rw [he, ih]
    have hs : Programme.«20261104-1627-proof-complexity».OutsideDifference.set a x (a x) = a := by funext y; by_cases h : y = x <;> simp [Programme.«20261104-1627-proof-complexity».OutsideDifference.set, h]
    cases h : a x
    · have hz : Programme.«20261104-1627-proof-complexity».OutsideDifference.set a x false = a := by simpa [h] using hs
      simp [xv, h, hz]
    · have hz : Programme.«20261104-1627-proof-complexity».OutsideDifference.set a x true = a := by simpa [h] using hs
      simp [xv, h, hz]
      omega
theorem nsIn_zero {p D : Nat} {B : Nat → Bool} {A : List (Poly Nat)}
    (hA : ∀ P ∈ A, Supported B P) {x : Nat} (hx : B x = false)
    {f : Fn} (hf : NSIn p A D f) : NSIn p A D (fun a => f (Programme.«20261104-1627-proof-complexity».OutsideDifference.set a x false)) := by
  have hp : ∀ a, pull (fun y => if y = x then Lit.const false else .var y) a = Programme.«20261104-1627-proof-complexity».OutsideDifference.set a x false := by
    intro a; funext y; by_cases hy : y = x <;> simp [pull, Programme.«20261104-1627-proof-complexity».OutsideDifference.set, hy, Lit.val]
  have hh := Programme.«20261104-1627-proof-complexity».OffboardSections.nsIn_pull
    (fun y => if y = x then Lit.const false else .var y)
    (fun a ha => by rw [hp]; exact good_set hA hx a ha false)
    (fun P hP a => by rw [hp]; exact ax_set (hA P hP) hx a false) hf
  simpa only [hp] using hh
theorem leaf_budget {p D : Nat} {B : Nat → Bool} {A : List (Poly Nat)}
    (hA : ∀ P ∈ A, Supported B P) (s : List Nat)
    (hs : ∀ x ∈ s, B x = false) {f : Fn} (hf : NSIn p A D f) :
    ∀ e ∈ expand s f, NSIn p A (D-e.1.length) e.2 := by
  induction s generalizing D f with
  | nil => intro e he; simp [expand] at he; subst e; simpa using hf
  | cons x xs ih =>
    intro e he
    have hx := hs x (by simp)
    have hxs : ∀ y ∈ xs, B y = false := fun y hy => hs y (by simp [hy])
    rcases List.mem_append.mp he with he | he
    · exact ih hxs (nsIn_zero hA hx hf) e he
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp he
      have hh := ih (D := D-1) hxs (nsIn_difference_full hA hx hf) u hu
      simpa [Nat.sub_sub, Nat.add_comm] using hh
end Programme.«20261104-1627-proof-complexity».BooleanReconstruction
#print axioms Programme.«20261104-1627-proof-complexity».BooleanReconstruction.reconstruction
#print axioms Programme.«20261104-1627-proof-complexity».BooleanReconstruction.leaf_budget
