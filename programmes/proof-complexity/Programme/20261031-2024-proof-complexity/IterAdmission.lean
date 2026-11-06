import Programme.«20261031-2024-proof-complexity».WordPartition

namespace Programme.«20261031-2024-proof-complexity».NativeIter

theorem eraseDups_length_le (l : List Lit) : l.eraseDups.length ≤ l.length := by
  cases l with
  | nil => simp
  | cons a l =>
    rw [List.eraseDups_cons, List.length_cons]
    have hlen := List.length_filter_le (p := fun b => !(b == a)) (l := l)
    have hh := eraseDups_length_le (l.filter fun b => !(b == a))
    simp only [List.length_cons]
    omega
termination_by l.length
decreasing_by
  have := List.length_filter_le (p := fun b => !(b == a)) (l := l)
  simp only [List.length_cons]
  omega

theorem conjunction_forbid (event : List Lit) (a : Assignment) :
    conjunction (falsity (forbid event)) a = conjunction event a := by
  have hn (l : Lit) : neg (neg l) = l := by cases l; simp [neg]
  have ha : (falsity (forbid event)).all (holds a) = event.all (holds a) := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true, falsity, forbid, List.mem_map, List.mem_eraseDups]
    constructor
    · intro h l hl
      have hh := h (neg (neg l)) ⟨neg l, ⟨l, hl, rfl⟩, rfl⟩
      simpa only [hn] using hh
    · intro h l ⟨j, ⟨k, hk, hj⟩, hl⟩
      subst j; subst l
      simpa only [hn] using h k hk
  simp only [conjunction, ha]

theorem equation_event {F d} (event : List Lit) (r : Rat)
    (hc : forbid event ∈ F) (hd : event.length ≤ d) :
    Cone F d (fun a => r * conjunction event a) := by
  have hh : Admitted d (forbid event) [] := by
    constructor
    · simp [Multiplier]
    · have := eraseDups_length_le (event.map neg)
      simp only [List.length_map] at this
      simp only [List.length_nil, Nat.zero_add, forbid]
      omega
  have hh := Cone.equation (forbid event) [] r hc hh
  simpa only [List.nil_append, conjunction_forbid] using hh

theorem word_multiplier (b x v : Nat) : Multiplier (word b x v) := by
  unfold Multiplier word
  simp only [List.map_map]
  apply List.Pairwise.map (R := fun i j : Nat => i ≠ j) _ _ List.nodup_range
  intro i j hij h
  exact hij (Prod.mk.inj h).2

theorem pair_multiplier (b x z u v : Nat) (hxz : x ≠ z) :
    Multiplier (word b x u ++ word b z v) := by
  unfold Multiplier
  rw [List.map_append, List.nodup_append]
  refine ⟨word_multiplier b x u, word_multiplier b z v, ?_⟩
  intro a ha c hc he
  simp only [word, List.map_map, List.mem_map] at ha hc
  obtain ⟨i, _, rfl⟩ := ha
  obtain ⟨j, _, rfl⟩ := hc
  exact hxz (Prod.mk.inj he).1

theorem positive_pair {F} (b x z u v : Nat) (hxz : x ≠ z) :
    Cone F (2*b) (conjunction (word b x u ++ word b z v)) := by
  apply Cone.positive _ (pair_multiplier b x z u v hxz)
  simp [word, List.length_append, List.length_map, List.length_range]
  omega

theorem root_mem (n b : Nat) (hn : 0 < n) : forbid (word b 0 0) ∈ cnfAt n b := by
  simp only [cnfAt, List.mem_eraseDups, List.mem_append, List.mem_map]
  apply Or.inr
  refine ⟨word b 0 0, ?_, rfl⟩
  apply List.mem_flatMap.mpr
  refine ⟨0, List.mem_range.mpr hn, ?_⟩
  simp

theorem low_mem (n b x z : Nat) (hx : x < n) (hz : z < x) :
    forbid (word b x z) ∈ cnfAt n b := by
  simp only [cnfAt, List.mem_eraseDups, List.mem_append, List.mem_map]
  apply Or.inr
  refine ⟨word b x z, List.mem_flatMap.mpr ⟨x, List.mem_range.mpr hx, ?_⟩, rfl⟩
  apply List.mem_append.mpr; left
  apply List.mem_append.mpr; right
  exact List.mem_map.mpr ⟨z, List.mem_range.mpr hz, rfl⟩

theorem high_mem (n b x z : Nat) (hx : x < n) (hz : z < n) (hxz : x < z) :
    forbid (word b x z ++ word b z z) ∈ cnfAt n b := by
  simp only [cnfAt, List.mem_eraseDups, List.mem_append, List.mem_map]
  apply Or.inr
  refine ⟨word b x z ++ word b z z,
    List.mem_flatMap.mpr ⟨x, List.mem_range.mpr hx, ?_⟩, rfl⟩
  apply List.mem_append.mpr; right
  apply List.mem_map.mpr
  exact ⟨z, List.mem_filter.mpr ⟨List.mem_range.mpr hz, by simpa using hxz⟩, rfl⟩

theorem domain_mem (n b x z : Nat) (hx : x < n) (hz : z < 2^b) (hnz : n ≤ z) :
    forbid (word b x z) ∈ cnfAt n b := by
  simp only [cnfAt, List.mem_eraseDups, List.mem_append]
  apply Or.inl
  apply List.mem_flatMap.mpr
  refine ⟨x, List.mem_range.mpr hx, List.mem_map.mpr ?_⟩
  exact ⟨z, List.mem_filter.mpr ⟨List.mem_range.mpr hz, by simpa using hnz⟩, rfl⟩

#print axioms equation_event
#print axioms positive_pair
end Programme.«20261031-2024-proof-complexity».NativeIter
