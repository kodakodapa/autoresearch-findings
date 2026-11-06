import Programme.«20261104-1627-proof-complexity».MatchingLabels

namespace Programme.«20261104-1627-proof-complexity».RectangularReconstruction

def dot (L : List Nat) (f g : Nat → Int) : Int :=
  (L.map fun j => f j * g j).sum

private theorem dot_add (L : List Nat) (f g h : Nat → Int) :
    dot L f (fun j => g j + h j) = dot L f g + dot L f h := by
  induction L with
  | nil => simp [dot]
  | cons a L ih =>
    simp only [dot, List.map_cons, List.sum_cons] at ih ⊢
    rw [Int.mul_add, ih]; omega

private theorem dot_sub (L : List Nat) (f g h : Nat → Int) :
    dot L f (fun j => g j - h j) = dot L f g - dot L f h := by
  induction L with
  | nil => simp [dot]
  | cons a L ih =>
    simp only [dot, List.map_cons, List.sum_cons] at ih ⊢
    rw [Int.mul_sub, ih]; omega

private theorem dot_scale (L : List Nat) (f g : Nat → Int) (c : Int) :
    dot L f (fun j => c * g j) = c * dot L f g := by
  induction L with
  | nil => simp [dot]
  | cons a L ih =>
    simp only [dot, List.map_cons, List.sum_cons] at ih ⊢
    rw [show f a * (c * g a) = c * (f a * g a) by
      rw [← Int.mul_assoc, Int.mul_comm (f a) c, Int.mul_assoc], ih, Int.mul_add]

private theorem dot_zero (L : List Nat) (f : Nat → Int) : dot L f (fun _ => 0) = 0 := by
  induction L with
  | nil => rfl
  | cons a L ih => simpa [dot] using ih

private theorem dot_dvd (L : List Nat) (p : Int) (f g : Nat → Int)
    (h : ∀ j ∈ L, p ∣ g j) : p ∣ dot L f g := by
  induction L with
  | nil => simp [dot]
  | cons a L ih =>
    have hm : p ∣ f a * g a := by
      obtain ⟨b, hb⟩ := h a (by simp)
      refine ⟨f a * b, ?_⟩
      rw [hb, ← Int.mul_assoc, Int.mul_comm (f a) p, Int.mul_assoc]
    exact Int.dvd_add hm (ih (fun j hj => h j (by simp [hj])))

-- Adapted from Peer.pr.ReconstructionChecker with an arbitrary rectangular P.
/-- An executable finite check of the integer matrix factorization modulo p.
P has output rows and label columns. S has output rows and generator columns; A has equation rows and label columns.
C has generator rows and label columns; H has output rows and equation columns. -/
def check (p outputs labels generators equations : Nat)
    (P S C H A : Nat → Nat → Int) : Bool :=
  (List.range outputs).all fun i => (List.range labels).all fun j =>
    (P i j -
      (dot (List.range generators) (S i) (fun k => C k j) +
       dot (List.range equations) (H i) (fun k => A k j))) % (p : Int) == 0

/-- The checked factorization reconstructs every kernel vector, not just ranks. -/
theorem check_sound {p o l s a : Nat} (P S C H A : Nat → Nat → Int)
    (hc : check p o l s a P S C H A = true) (x : Nat → Int)
    (hx : ∀ k, k < a → (p : Int) ∣ dot (List.range l) x (A k)) :
    ∀ i, i < o → (p : Int) ∣ dot (List.range l) x (P i) -
      dot (List.range s) (S i) (fun k => dot (List.range l) x (C k)) := by
  intro i hi
  have hentry : ∀ j ∈ List.range l, (p : Int) ∣
      P i j -
      (dot (List.range s) (S i) (fun k => C k j) +
       dot (List.range a) (H i) (fun k => A k j)) := by
    intro j hj
    have h := List.all_eq_true.mp (List.all_eq_true.mp hc i (List.mem_range.mpr hi)) j hj
    exact Int.dvd_of_emod_eq_zero (by simpa using h)
  have hd := dot_dvd (List.range l) (p : Int) x _ hentry
  rw [dot_sub, dot_add] at hd
  have commute (K : List Nat) (U V : Nat → Nat → Int) :
      dot (List.range l) x (fun j => dot K (U i) (fun k => V k j)) =
      dot K (U i) (fun k => dot (List.range l) x (V k)) := by
    induction K with
    | nil => simpa [dot] using dot_zero (List.range l) x
    | cons k K ih =>
      change dot (List.range l) x (fun j => U i k * V k j + dot K (U i) (fun k => V k j)) = _
      rw [dot_add, dot_scale, ih]
      rfl
  rw [commute (List.range s) S C, commute (List.range a) H A] at hd
  have hz : (p : Int) ∣ dot (List.range a) (H i) (fun k => dot (List.range l) x (A k)) :=
    dot_dvd _ _ _ _ (fun k hk => hx k (List.mem_range.mp hk))
  have hh := Int.dvd_add hd hz
  have he : dot (List.range l) x (P i) -
      (dot (List.range s) (S i) (fun k => dot (List.range l) x (C k)) +
       dot (List.range a) (H i) (fun k => dot (List.range l) x (A k))) +
       dot (List.range a) (H i) (fun k => dot (List.range l) x (A k)) =
       dot (List.range l) x (P i) - dot (List.range s) (S i) (fun k => dot (List.range l) x (C k)) := by omega
  rw [he] at hh
  exact hh

end Programme.«20261104-1627-proof-complexity».RectangularReconstruction
#print axioms Programme.«20261104-1627-proof-complexity».RectangularReconstruction.check_sound
