import Programme.«20261031-2024-proof-complexity».NativeIter

namespace Programme.«20261031-2024-proof-complexity».NativeIter

theorem word_succ (b x v : Nat) :
    word (b+1) x v = word b x v ++ [((x,b), v.testBit b)] := by
  simp [word, List.range_succ, List.map_append]

theorem word_high (b x v : Nat) : word b x (2^b+v) = word b x v := by
  unfold word
  apply List.map_congr_left
  intro j hj
  have hj' : j < b := List.mem_range.mp hj
  rw [Nat.testBit_two_pow_add_gt hj']

theorem word_pair (b x v : Nat) (a : Assignment) (hv : v < 2^b) :
    conjunction (word (b+1) x v) a +
      conjunction (word (b+1) x (2^b+v)) a = conjunction (word b x v) a := by
  rw [word_succ, word_succ, word_high]
  have h0 := Nat.testBit_lt_two_pow hv
  have h1 : (2^b+v).testBit b = true := by
    rw [Nat.testBit_two_pow_add_eq, h0]; rfl
  simp only [h0, h1, conjunction, List.all_append, List.all_cons, List.all_nil,
    Bool.and_true]
  cases hh : (word b x v).all (holds a) <;>
    cases ha : a (x,b) <;> simp [holds, ha, Rat.add_zero, Rat.zero_add]

theorem sum_map_pair (l : List Nat) (f g : Nat → Rat) :
    (l.map f).sum + (l.map g).sum = (l.map fun v => f v + g v).sum := by
  induction l with
  | nil => simp [Rat.add_zero]
  | cons v l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [← ih]
    rw [Rat.add_assoc (f v), ← Rat.add_assoc (l.map f).sum,
      Rat.add_comm (l.map f).sum (g v), Rat.add_assoc (g v),
      ← Rat.add_assoc (f v)]

theorem word_partition (b x : Nat) (a : Assignment) :
    ((List.range (2^b)).map fun v => conjunction (word b x v) a).sum = 1 := by
  induction b with
  | zero => simp [word, conjunction, Rat.add_zero]
  | succ b ih =>
    rw [Nat.pow_succ]
    have he : 2^b * 2 = 2^b + 2^b := by omega
    rw [he, List.range_add, List.map_append, List.sum_append, List.map_map,
      sum_map_pair]
    have hmap : (List.range (2^b)).map (fun v =>
        conjunction (word (b+1) x v) a + conjunction (word (b+1) x (2^b+v)) a) =
        (List.range (2^b)).map (fun v => conjunction (word b x v) a) := by
      apply List.map_congr_left
      intro v hv
      exact word_pair b x v a (List.mem_range.mp hv)
    change (List.map (fun v => conjunction (word (b+1) x v) a +
      conjunction (word (b+1) x (2^b+v)) a) (List.range (2^b))).sum = 1
    rw [hmap, ih]

#print axioms word_partition
end Programme.«20261031-2024-proof-complexity».NativeIter
