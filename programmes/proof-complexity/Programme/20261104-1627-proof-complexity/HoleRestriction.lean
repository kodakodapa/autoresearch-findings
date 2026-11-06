import Programme.«20261104-1627-proof-complexity».MatchingLabels

namespace Programme.«20261104-1627-proof-complexity».MatchingLabels

/-- Increasing injection from the board with hole h deleted. -/
def omitHole (h j : Nat) : Nat := if j < h then j else j + 1

def closeHole (h j : Nat) : Nat := if j < h then j else j - 1

theorem omitHole_ne (h j : Nat) : omitHole h j ≠ h := by
  unfold omitHole
  split <;> omega

theorem close_omit (h j : Nat) : closeHole h (omitHole h j) = j := by
  unfold omitHole closeHole
  split <;> (try split) <;> omega

theorem omit_close (h j : Nat) (hj : j ≠ h) :
    omitHole h (closeHole h j) = j := by
  unfold omitHole closeHole
  split <;> (try split) <;> omega

theorem omitHole_injective (h : Nat) : Function.Injective (omitHole h) := by
  intro a b hab
  have := congrArg (closeHole h) hab
  simpa only [close_omit] using this

theorem omitHole_lt {n h j : Nat} (hj : j < n) : omitHole h j < n + 1 := by
  unfold omitHole
  split <;> omega

def pushMatching (h : Nat) (M : Matching) : Matching :=
  M.map fun e => (e.1, omitHole h e.2)

def pullMatching (h : Nat) (M : Matching) : Matching :=
  M.map fun e => (e.1, closeHole h e.2)

theorem pull_push (h : Nat) (M : Matching) :
    pullMatching h (pushMatching h M) = M := by
  simp only [pullMatching, pushMatching, List.map_map]
  induction M with
  | nil => rfl
  | cons e M ih => simpa [close_omit] using congrArg (List.cons e) ih

theorem push_pull (h : Nat) (M : Matching)
    (ha : ∀ e ∈ M, e.2 ≠ h) : pushMatching h (pullMatching h M) = M := by
  simp only [pullMatching, pushMatching, List.map_map]
  induction M with
  | nil => rfl
  | cons e M ih =>
    simp only [List.map_cons, Function.comp_apply]
    rw [omit_close h e.2 (ha e (by simp))]
    exact congrArg (List.cons e) (ih (by intro a hab; exact ha a (by simp [hab])))

theorem pushMatching_injective (h : Nat) : Function.Injective (pushMatching h) := by
  intro M N he
  have := congrArg (pullMatching h) he
  simpa only [pull_push] using this

/-- Variable renaming must recompute the row stride, not merely filter codes.
The zero-width case is excluded in the compatibility theorem below. -/
def pushCode (n h x : Nat) : Nat := (x / n) * (n + 1) + omitHole h (x % n)

theorem pushCode_edge {n : Nat} (hn : 0 < n) (h i j : Nat) (hj : j < n) :
    pushCode n h (i*n+j) = i*(n+1)+omitHole h j := by
  have hd : (i*n+j) / n = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right j i hn, Nat.div_eq_of_lt hj]
    simp
  simp [pushCode, hd, Nat.add_mod, Nat.mod_eq_of_lt hj]

theorem mono_push {n : Nat} (hn : 0 < n) (h : Nat) (M : Matching)
    (hb : ∀ e ∈ M, e.2 < n) :
    mono (n+1) (pushMatching h M) = (mono n M).map (pushCode n h) := by
  simp only [mono, pushMatching, List.map_map]
  apply List.map_congr_left
  intro e he
  exact (pushCode_edge hn h e.1 e.2 (hb e he)).symm

/-- Restriction of matching-coordinate functions along the actual omission
injection. These are coordinates, not primal label-kernel vectors. -/
def restrictCoordinates {A : Type} (h : Nat) (v : Matching → A) : Matching → A :=
  fun M => v (pushMatching h M)

/-- Concrete top image on enumerated matching coordinates. -/
def TopImage (p m n d : Nat) (v : Matching → Int) : Prop :=
  ∃ a : Vector, valid m n d a ∧ ∀ M ∈ matchings m n d,
    (p : Int) ∣ v M - Programme.«20261029-1156-proof-complexity».StdPC.coeff
      (top m n a) (mono n M)

/-- The hole-avoidance obligation. It is defined, not assumed or proved.
Unlike Kernel, this is a local-to-global assertion about the top image. -/
def Lprime (p m n d : Nat) : Prop :=
  2*d < n → ∀ v : Matching → Int,
    (∀ h, h < n → TopImage p m (n-1) d (restrictCoordinates h v)) →
    TopImage p m n d v

end Programme.«20261104-1627-proof-complexity».MatchingLabels
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.pull_push
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.push_pull
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.mono_push
