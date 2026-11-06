import Programme.«20261104-1627-proof-complexity».RectangularReconstruction

namespace Programme.«20261104-1627-proof-complexity».RectangularSparse
open RectangularReconstruction
-- Sparse dot lemma adapted from Peer.pr.SparseReconstruction.
abbrev Sparse := List (Nat × Int)
def value (v : Sparse) (j : Nat) : Int :=
  (v.map fun a => if a.1 = j then a.2 else 0).sum
def pairing (v : Sparse) (f : Nat → Int) : Int :=
  (v.map fun a => a.2 * f a.1).sum

theorem dot_value (n : Nat) (v : Sparse) (f : Nat → Int)
    (hv : ∀ a ∈ v, a.1 < n) :
    dot (List.range n) f (value v) = pairing v f := by
  induction v with
  | nil =>
    simp only [value, List.map_nil, List.sum_nil, pairing]
    induction n with
    | zero => rfl
    | succ n ih => simpa [dot, List.range_succ, List.map_append, List.sum_append, value] using ih
  | cons a v ih =>
    have ha : a.1 < n := hv a (by simp)
    have hv' : ∀ b ∈ v, b.1 < n := fun b hb => hv b (by simp [hb])
    have split : dot (List.range n) f (value (a :: v)) =
        dot (List.range n) f (fun j => if a.1 = j then a.2 else 0) +
        dot (List.range n) f (value v) := by
      generalize List.range n = L
      induction L with
      | nil => rfl
      | cons j L hj =>
        simp only [dot, List.map_cons, List.sum_cons, value] at hj ⊢
        rw [Int.mul_add, hj]
        omega
    have single : dot (List.range n) f (fun j => if a.1 = j then a.2 else 0) =
        a.2 * f a.1 := by
      have aux (L : List Nat) (hn : L.Nodup) (hm : a.1 ∈ L) :
          dot L f (fun j => if a.1 = j then a.2 else 0) = a.2 * f a.1 := by
        induction L with
        | nil => simp at hm
        | cons j L hj =>
          have hd := List.nodup_cons.mp hn
          by_cases h : a.1 = j
          · have hz : dot L f (fun j => if a.1 = j then a.2 else 0) = 0 := by
              unfold dot
              have eq : (L.map fun j => f j * (if a.1 = j then a.2 else 0)) =
                  L.map (fun _ => (0 : Int)) := by
                apply List.map_congr_left
                intro k hk
                have ne : a.1 ≠ k := fun e => hd.1 (h ▸ e ▸ hk)
                simp [ne]
              rw [eq]
              have zs (K : List Nat) : (K.map (fun _ => (0 : Int))).sum = 0 := by
                induction K with
                | nil => rfl
                | cons k K ih => simpa using ih
              exact zs L
            change f j * (if a.1 = j then a.2 else 0) + dot L f (fun k => if a.1 = k then a.2 else 0) = _
            rw [hz]
            simp [h, Int.mul_comm]
          · have hm' : a.1 ∈ L := (List.mem_cons.mp hm).resolve_left h
            simpa [dot, h] using hj hd.2 hm'
      exact aux _ List.nodup_range (List.mem_range.mpr ha)
    rw [split, single, ih hv']
    rfl

theorem dot_comm (L : List Nat) (f g : Nat → Int) : dot L f g = dot L g f := by
  unfold dot
  congr 1
  apply List.map_congr_left
  intro j _
  exact Int.mul_comm _ _

def check (p o l s a : Nat) (P G T : Nat → Nat → Int)
    (C H : Nat → Sparse) : Bool :=
  (List.range o).all fun i => (List.range l).all fun j =>
    (P i j - (pairing (C j) (G i) + pairing (H i) (fun k => T k j))) % (p : Int) == 0

theorem check_sound {p o l s a : Nat} (P G T : Nat → Nat → Int)
    (C H : Nat → Sparse)
    (hC : ∀ j, j < l → ∀ z ∈ C j, z.1 < s)
    (hH : ∀ i, i < o → ∀ z ∈ H i, z.1 < a)
    (hc : check p o l s a P G T C H = true) (x : Nat → Int)
    (hx : ∀ k, k < a → (p : Int) ∣ dot (List.range l) x (T k)) :
    ∀ i, i < o → (p : Int) ∣ dot (List.range l) x (P i) -
      dot (List.range s) (G i) (fun k => dot (List.range l) x (fun j => value (C j) k)) := by
  apply RectangularReconstruction.check_sound P G (fun k j => value (C j) k)
    (fun i k => value (H i) k) T ?_ x hx
  apply List.all_eq_true.mpr
  intro i hi
  apply List.all_eq_true.mpr
  intro j hj
  have h := List.all_eq_true.mp (List.all_eq_true.mp hc i hi) j hj
  rw [dot_comm (List.range a) (fun k => value (H i) k) (fun k => T k j)]
  simpa only [dot_value s (C j) (G i) (hC j (List.mem_range.mp hj)),
    dot_value a (H i) (fun k => T k j) (hH i (List.mem_range.mp hi))] using h
end Programme.«20261104-1627-proof-complexity».RectangularSparse
#print axioms Programme.«20261104-1627-proof-complexity».RectangularSparse.check_sound
