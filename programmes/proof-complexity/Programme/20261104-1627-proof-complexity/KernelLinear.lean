import Programme.«20261104-1627-proof-complexity».PigeonCancellation

namespace Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261029-1156-proof-complexity».StdPC

private theorem scaled_cf (a : Int) (L : List (Int × List Nat)) (u : List Nat) :
    cf (L.map fun t => (a*t.1,t.2)) u = a * cf L u := by
  induction L with
  | nil => simp [cf]
  | cons t L ih =>
    by_cases h : t.2.Perm u <;> simp [cf, h, Int.mul_add] at ih ⊢ <;> exact ih

theorem top_append_coeff (m n : Nat) (v w : Vector) (u : List Nat) :
    coeff (top m n (v ++ w)) u = coeff (top m n v) u + coeff (top m n w) u := by
  simp [top, coeff, List.flatMap_append, cf_append]

theorem top_scale_coeff (m n : Nat) (a : Int) (v : Vector) (u : List Nat) :
    coeff (top m n (v.map fun t => (a*t.1,t.2))) u = a * coeff (top m n v) u := by
  induction v with
  | nil => simp [top, coeff, cf]
  | cons t v ih =>
    simp only [List.map_cons, top, List.flatMap_cons, coeff, cf_append] at ih ⊢
    rw [scaled_cf, scaled_cf]
    rw [Int.mul_assoc, ih, Int.mul_add]

theorem kernel_append {p m n d : Nat} {v w : Vector}
    (hv : Kernel p m n d v) (hw : Kernel p m n d w) :
    Kernel p m n d (v ++ w) := by
  refine ⟨?_, ?_⟩
  · intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact hv.1 t ht
    · exact hw.1 t ht
  · intro u
    have h := Int.dvd_add (hv.2 u) (hw.2 u)
    change (p : Int) ∣ coeff (top m n (v ++ w)) u - 0
    rw [top_append_coeff]
    simpa [coeff, cf] using h

theorem kernel_scale {p m n d : Nat} {v : Vector}
    (hv : Kernel p m n d v) (a : Int) :
    Kernel p m n d (v.map fun t => (a*t.1,t.2)) := by
  refine ⟨?_, ?_⟩
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
    exact hv.1 s hs
  · intro u
    have h0 : (p : Int) ∣ coeff (top m n v) u := by simpa [coeff, cf] using hv.2 u
    change (p : Int) ∣ coeff (top m n (v.map fun t => (a*t.1,t.2))) u - 0
    rw [top_scale_coeff, Int.sub_zero]
    obtain ⟨b, hb⟩ := h0
    refine ⟨a*b, ?_⟩
    rw [hb]
    simp [Int.mul_assoc, Int.mul_comm]

theorem kernel_combine {p m n d : Nat} (c : List (Int × Vector))
    (hc : ∀ t ∈ c, Kernel p m n d t.2) : Kernel p m n d (combine c) := by
  induction c with
  | nil => exact ⟨by simp [valid, combine], by intro u; simp [combine, top, coeff, cf]⟩
  | cons t c ih =>
    exact kernel_append (kernel_scale (hc t (by simp)) t.1)
      (ih (by intro s hs; exact hc s (by simp [hs])))

/-- Residual kernel preservation requires soundness of the generators actually used. -/
theorem first_block_kernel_residual {p m n d : Nat} {v : Vector}
    (hv : Kernel p (m+1) n d v) (hs : Spanning p m n d)
    (sound : ∀ u ∈ syzygies (m+1) n d, Kernel p (m+1) n d u) :
    ∃ C : List (Int × Vector),
      (∀ t ∈ C, t.2 ∈ syzygies (m+1) n d) ∧
      Kernel p (m+1) n d (v ++ (combine C).map (fun t => (-t.1,t.2))) ∧
      ∀ g, (p : Int) ∣ vectorCoeff (splitPigeon m 1
        (v ++ (combine C).map (fun t => (-t.1,t.2)))) g := by
  obtain ⟨C, hC, he⟩ := first_block_residual hv hs
  refine ⟨C, hC, ?_, he⟩
  have hk := kernel_scale (kernel_combine C (fun t ht => sound t.2 (hC t ht))) (-1)
  have hn : ((combine C).map fun t => ((-1 : Int)*t.1,t.2)) =
      ((combine C).map fun t => (-t.1,t.2)) := by simp
  rw [hn] at hk
  exact kernel_append hv hk
end Programme.«20261104-1627-proof-complexity».MatchingLabels
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.kernel_combine
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.first_block_kernel_residual
