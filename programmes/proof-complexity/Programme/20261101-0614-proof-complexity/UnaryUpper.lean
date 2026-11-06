import Programme.«20261101-0614-proof-complexity».UnaryRow

namespace Programme.«20261101-0614-proof-complexity».UnaryIter
open Programme.«20261031-2024-proof-complexity».NativeIter

theorem low_mem (L x z : Nat) (hx : x < L) (hz : z < x) :
    [minus x z] ∈ cnf L := by
  simp only [cnf, raw, List.mem_eraseDups, List.mem_append]
  apply Or.inl; apply Or.inr
  exact List.mem_flatMap.mpr ⟨x, List.mem_range.mpr hx,
    List.mem_map.mpr ⟨z, List.mem_range.mpr hz, rfl⟩⟩

theorem high_mem (L x z : Nat) (hx : x < L) (hz : z < L) (hxz : x < z) :
    [minus x z, minus z z] ∈ cnf L := by
  simp only [cnf, raw, List.mem_eraseDups, List.mem_append]
  apply Or.inr
  exact List.mem_flatMap.mpr ⟨x, List.mem_range.mpr hx,
    List.mem_map.mpr ⟨z,
      List.mem_filter.mpr ⟨List.mem_range.mpr hz, by simpa using hxz⟩, rfl⟩⟩

theorem root_mem (L : Nat) : [minus 0 0] ∈ cnf L := by
  simp only [cnf, raw, List.mem_eraseDups, List.mem_append]
  exact Or.inl (Or.inl (Or.inr (by simp [minus])))

theorem unit_negative {F d} (x z : Nat) (hc : [minus x z] ∈ F) (hd : 1 ≤ d) :
    Cone F d (fun a => -val x z a) := by
  have he := Cone.equation [minus x z] [] (-1) hc
    (show Admitted d [minus x z] [] from ⟨by simp [Multiplier], by simpa using hd⟩)
  simpa [falsity, minus, neg, val, pos, Rat.neg_mul, Rat.one_mul] using he

theorem eliminate {F d} (x z : Nat) (hxz : x ≠ z) (hd : 2 ≤ d)
    (hc : [minus x z, minus z z] ∈ F)
    (hz : Cone F d (fun a => val z z a - 1)) :
    Cone F d (fun a => -val x z a) := by
  have he := Cone.equation [minus x z, minus z z] [] (-1) hc
    (show Admitted d [minus x z, minus z z] [] from
      ⟨by simp [Multiplier], by simpa using hd⟩)
  have hp : Cone F d (conjunction [minus x z, minus z z]) := by
    apply Cone.positive
    · simp [Multiplier, minus, hxz]
    · simpa using hd
  have hsum := Cone.add (Cone.add he hp) hz
  have hid : (fun a =>
      (-1 * conjunction ([] ++ falsity [minus x z, minus z z]) a +
        conjunction [minus x z, minus z z] a) + (val z z a - 1)) =
      (fun a => -val x z a) := by
    funext a
    cases h : a (x,z) <;> cases h' : a (z,z) <;>
      simp [conjunction, falsity, minus, pos, neg, holds, val, h, h', Rat.zero_add, Rat.add_zero, Rat.sub_eq_add_neg, Rat.add_neg_cancel]
  rw [hid] at hsum
  exact hsum

theorem cancel_row (s v : Rat) : (s + v - 1) + -s = v - 1 := by
  simp only [Rat.sub_eq_add_neg]
  calc
    (s + v + -1) + -s = (s + -s) + (v + -1) := by
      simp only [Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]
    _ = v + -1 := by rw [Rat.add_neg_cancel, Rat.zero_add]

/-- Descending induction adds certificates; it never multiplies a derived line. -/
theorem diagonal (L x : Nat) (hL : 2 ≤ L) (hx : x < L) :
    Cone (cnf L) L (fun a => val x x a - 1) := by
  have off : ∀ z < L, z ≠ x → Cone (cnf L) L (fun a => -val x z a) := by
    intro z hz hzx
    by_cases hlow : z < x
    · exact unit_negative x z (low_mem L x z hx hlow) (by omega)
    · have hxz : x < z := by omega
      exact eliminate x z (by omega) hL (high_mem L x z hx hz hxz)
        (diagonal L z hL hz)
  let l := (List.range L).filter (· != x)
  have hneg := cone_sum (F := cnf L) (d := L) l (fun z a => -val x z a) (by
    intro z hz
    obtain ⟨hz, hzx⟩ := List.mem_filter.mp hz
    exact off z (List.mem_range.mp hz) (by simpa using hzx))
  have hsum := Cone.add (row_linear L x hx) hneg
  have hid : (fun a => (total x (List.range L) a - 1) +
      (l.map fun z => -val x z a).sum) = (fun a => val x x a - 1) := by
    funext a
    rw [sum_neg]
    have hh := sum_filter_one (List.range L) (fun z => val x z a) x
      List.nodup_range (List.mem_range.mpr hx)
    change (total x (List.range L) a - 1) + -(l.map (fun z => val x z a)).sum = _
    change (l.map (fun z => val x z a)).sum + val x x a = total x (List.range L) a at hh
    rw [← hh, cancel_row]
  rw [hid] at hsum
  exact hsum
termination_by L-x
decreasing_by omega

theorem upper (L : Nat) (hL : 2 ≤ L) : Refutes (cnf L) L := by
  have hsum := Cone.add (diagonal L 0 hL (by omega))
    (unit_negative 0 0 (root_mem L) (by omega : 1 ≤ L))
  have hid : (fun a => (val 0 0 a - 1) + -val 0 0 a) = (fun _ => (-1 : Rat)) := by
    funext a
    cases h : a (0,0) <;> simp [val, conjunction, pos, holds, h, Rat.zero_add, Rat.add_zero, Rat.sub_eq_add_neg, Rat.add_neg_cancel]
  rw [hid] at hsum
  exact hsum

theorem exact_degree (L : Nat) (hL : 2 ≤ L) :
    Refutes (cnf L) L ∧ ∀ d < L, ¬ Refutes (cnf L) d :=
  ⟨upper L hL, fun d hd => lower L d hd⟩

#print axioms upper
#print axioms exact_degree
end Programme.«20261101-0614-proof-complexity».UnaryIter
