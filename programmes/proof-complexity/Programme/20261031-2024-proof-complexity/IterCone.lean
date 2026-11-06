import Programme.«20261031-2024-proof-complexity».IterAdmission

namespace Programme.«20261031-2024-proof-complexity».NativeIter

def other (b x z : Nat) (a : Assignment) : Rat :=
  if (word b x z).all (holds a) then 0 else 1

theorem conjunction_mul (l m : List Lit) (a : Assignment) :
    conjunction (l ++ m) a = conjunction l a * conjunction m a := by
  simp only [conjunction, List.all_append]
  cases l.all (holds a) <;> cases m.all (holds a) <;>
    simp [Rat.mul_zero, Rat.mul_one]

theorem sum_filter_one (l : List Nat) (f : Nat → Rat) (z : Nat)
    (hd : l.Nodup) (hz : z ∈ l) :
    ((l.filter (· != z)).map f).sum + f z = (l.map f).sum := by
  induction l with
  | nil => simp at hz
  | cons v l ih =>
    obtain ⟨hv, hl⟩ := List.nodup_cons.mp hd
    by_cases he : v = z
    · subst v
      have hh : l.filter (· != z) = l := by
        apply List.filter_eq_self.mpr
        intro v hvm
        have hn : v ≠ z := by intro h; subst v; exact hv hvm
        simpa using hn
      simp [hh, Rat.add_comm]
    · have hz' : z ∈ l := by simpa [Ne.symm he] using hz
      have hh := ih hl hz'
      have ht : (v != z) = true := by simpa using he
      simp only [List.filter_cons, ht, List.map_cons, List.sum_cons, ↓reduceIte]
      rw [Rat.add_assoc, hh]

theorem other_partition (b x z : Nat) (a : Assignment) (hz : z < 2^b) :
    (((List.range (2^b)).filter (· != z)).map
      (fun v => conjunction (word b x v) a)).sum = other b x z a := by
  have h := sum_filter_one (List.range (2^b))
    (fun v => conjunction (word b x v) a) z List.nodup_range (List.mem_range.mpr hz)
  rw [word_partition] at h
  apply Rat.add_right_cancel (conjunction (word b x z) a)
  rw [h]
  simp only [other, conjunction]
  cases (word b x z).all (holds a) <;> simp [Rat.add_zero, Rat.zero_add]

theorem cone_sum {F d} (l : List Nat) (f : Nat → Assignment → Rat)
    (h : ∀ v ∈ l, Cone F d (f v)) :
    Cone F d (fun a => (l.map (fun v => f v a)).sum) := by
  induction l with
  | nil => exact Cone.zero
  | cons v l ih =>
    exact Cone.add (h v (by simp)) (ih (by intro w hw; exact h w (by simp [hw])))

theorem sum_neg (l : List Nat) (f : Nat → Rat) :
    (l.map fun v => -f v).sum = -(l.map f).sum := by
  induction l with
  | nil => simp
  | cons v l ih => simp only [List.map_cons, List.sum_cons, ih, Rat.neg_add]

theorem neg_other_cone {F d} (b x z : Nat) (hz : z < 2^b)
    (h : ∀ v < 2^b, v ≠ z → Cone F d (fun a => -conjunction (word b x v) a)) :
    Cone F d (fun a => -other b x z a) := by
  have hh := cone_sum ((List.range (2^b)).filter (· != z))
    (fun v a => -conjunction (word b x v) a) (by
      intro v hv
      obtain ⟨hv, hn⟩ := List.mem_filter.mp hv
      exact h v (List.mem_range.mp hv) (by simpa using hn))
  have he : (fun a => (((List.range (2^b)).filter (· != z)).map
      (fun v => -conjunction (word b x v) a)).sum) = (fun a => -other b x z a) := by
    funext a
    rw [sum_neg, other_partition b x z a hz]
  rw [he] at hh
  exact hh

theorem sum_mul_right (l : List Nat) (f : Nat → Rat) (r : Rat) :
    (l.map fun v => f v * r).sum = (l.map f).sum * r := by
  induction l with
  | nil => simp [Rat.zero_mul]
  | cons v l ih => simp only [List.map_cons, List.sum_cons, ih, Rat.add_mul]

theorem sum_mul_left (l : List Nat) (f : Nat → Rat) (r : Rat) :
    (l.map fun v => r * f v).sum = r * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons v l ih => simp only [List.map_cons, List.sum_cons, ih, Rat.mul_add]

theorem other_pair_cone {F} (b x z : Nat) (hxz : x ≠ z)
    (hv : z < 2^b) : Cone F (2*b) (fun a => other b x z a * other b z z a) := by
  let l := (List.range (2^b)).filter (· != z)
  have hh := cone_sum (F := F) l (fun u a =>
      (l.map fun v => conjunction (word b x u ++ word b z v) a).sum) (by
    intro u _
    exact cone_sum l (fun v => conjunction (word b x u ++ word b z v))
      (by intro v _; exact positive_pair b x z u v hxz))
  have he : (fun a => (l.map fun u =>
      (l.map fun v => conjunction (word b x u ++ word b z v) a).sum).sum) =
      (fun a => other b x z a * other b z z a) := by
    funext a
    simp only [conjunction_mul]
    simp only [sum_mul_left]
    rw [sum_mul_right]
    simp only [l, other_partition b x z a hv, other_partition b z z a hv]
  rw [he] at hh
  exact hh

theorem pair_eliminate {F} (b x z : Nat) (hxz : x ≠ z) (hz : z < 2^b)
    (he : forbid (word b x z ++ word b z z) ∈ F)
    (h : ∀ v < 2^b, v ≠ z → Cone F (2*b) (fun a => -conjunction (word b z v) a)) :
    Cone F (2*b) (fun a => -conjunction (word b x z) a) := by
  have hpair := equation_event (d := 2*b) (word b x z ++ word b z z) (-1) he (by
    simp [word]; omega)
  have hc := Cone.add (Cone.add hpair (other_pair_cone (F := F) b x z hxz hz))
    (neg_other_cone b z z hz h)
  have hid : (fun a => (-1 * conjunction (word b x z ++ word b z z) a +
      other b x z a * other b z z a) + -other b z z a) =
      (fun a => -conjunction (word b x z) a) := by
    funext a
    rw [conjunction_mul]
    simp only [conjunction, other]
    cases (word b x z).all (holds a) <;> cases (word b z z).all (holds a) <;>
      simp [Rat.mul_zero, Rat.mul_one,
        Rat.add_zero, Rat.zero_add, Rat.add_neg_cancel]
  rw [hid] at hc
  exact hc

#print axioms pair_eliminate
end Programme.«20261031-2024-proof-complexity».NativeIter
