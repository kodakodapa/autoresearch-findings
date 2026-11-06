import Programme.«20261025-1627-proof-complexity».K5Chk
import Programme.«20261026-1402-proof-complexity».ExtLemma

/-!
# The library K5 design is self-balanced up to level 3 in matching coordinates

`D = Wt sup` is the `ℤ₁₅ × ℤ₇`-invariant weight of the library K5 design (run 1627, `K5Defs`,
`K5Chk`, `K5Lem.lin_all`). In the coordinates of `ExtLemma.Bal` (canonical matchings, line sums
over free cells) it is a unit design of degree 4 at `(n, k) = (7, 8)`:
`D [] = 1` and `Bal 2 7 8 D D e` for every `e ≤ 3`.
-/

namespace Programme.«20261027-1434-proof-complexity».K5Bal

open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261026-1402-proof-complexity».ExtLemma
open Programme.«20261025-1627-proof-complexity».K5Defs
open Programme.«20261025-1627-proof-complexity».MomGen (canon)
open Programme.«20261025-0459-proof-complexity».OntoSubst (rsum_congr)

/-- The K5 design as a function on lists. -/
def D : List Nat → Int := Wt sup

theorem D_nil : D [] = 1 := chk_W0

theorem matchB_isMatch {l : List Nat} (h : matchB l = true) : isMatch 7 l = true := by
  rw [isMatch_iff]
  intro v hv w hw
  unfold matchB at h
  rw [List.all_eq_true] at h
  have h1 := h v hv
  rw [Bool.and_eq_true, List.all_eq_true] at h1
  have h2 := h1.2 w hw
  unfold cfl
  by_cases e : v = w
  · subst e; simp
  · have h3 : v / 7 ≠ w / 7 ∧ v % 7 ≠ w % 7 := by
      simp only [Bool.or_eq_true, beq_iff_eq, e, false_or, Bool.and_eq_true, bne_iff_ne] at h2
      exact h2
    simp [e, h3.1, h3.2]

/-- One term of a line sum equals the corresponding `Wt` term. -/
theorem term (g : List Nat) (hg : ∀ x ∈ g, x < 105) (x : Nat) (hx : x < 105) :
    (if isMatch 7 (x :: g) then D (canon ((7 + 8) * 7) (x :: g)) else 0) = Wt sup (x :: g) := by
  have hall : ∀ y ∈ x :: g, y < (7 + 8) * 7 := by
    intro y hy; rcases List.mem_cons.mp hy with rfl | hy
    · exact hx
    · exact hg y hy
  by_cases hm : isMatch 7 (x :: g) = true
  · rw [if_pos hm]
    exact Wt_congr sup (fun y => mem_canon' hall y)
  · rw [if_neg hm]
    have : matchB (x :: g) = false := by
      cases e : matchB (x :: g)
      · rfl
      · exact absurd (matchB_isMatch e) hm
    exact (Wt_nm sup this).symm

theorem row_eq (g : List Nat) (hg : ∀ x ∈ g, x < 105) (i : Nat) (hi : i < 15) :
    rowS 7 8 D g i - D g = pigS sup i g := by
  unfold rowS lineS pigS
  rw [rsum_congr 7 _ (fun j => Wt sup ((i * 7 + j) :: g)) (fun t ht => by
    rw [term g hg _ (by show _ * 7 + _ < 105; omega)]; rfl)]
  rfl

theorem col_eq (g : List Nat) (hg : ∀ x ∈ g, x < 105) (j : Nat) (hj : j < 7) :
    colS 7 8 D g j - D g = holS sup j g := by
  unfold colS lineS holS
  rw [rsum_congr (7 + 8) _ (fun i => Wt sup ((i * 7 + j) :: g)) (fun t ht => by
    rw [term g hg _ (by show _ * 7 + _ < 105; omega)]; rfl)]
  rfl

/-- **The K5 design is a unit degree-4 design in matching coordinates.** -/
theorem d_bal (e : Nat) (he : e ≤ 3) : Bal 2 7 8 D D e := by
  intro g hg hl
  have hlt : ∀ x ∈ g, x < 105 := fun x hx => CM_lt hg hx
  obtain ⟨h1, h2⟩ := lin_all sup chk_all chk_empty g hlt (by omega)
  refine ⟨fun i hi _ => ?_, fun j hj _ => ?_⟩
  · rw [row_eq g hlt i hi]; exact h1 i hi
  · rw [col_eq g hlt j hj]; exact h2 j hj

theorem d_design : D [] = 1 ∧ ∀ e ≤ 3, Bal 2 7 8 D D e := ⟨D_nil, d_bal⟩

end Programme.«20261027-1434-proof-complexity».K5Bal

#print axioms Programme.«20261027-1434-proof-complexity».K5Bal.d_design
