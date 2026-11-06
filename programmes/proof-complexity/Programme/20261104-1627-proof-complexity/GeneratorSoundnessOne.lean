import Programme.«20261104-1627-proof-complexity».KernelLinear
import Programme.«20261104-1627-proof-complexity».RectangularOne

namespace Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261029-1156-proof-complexity».StdPC

private theorem cf_flat_cons (B : List Nat) (f : Nat → Int × List Nat)
    (g : Nat → List (Int × List Nat)) (u : List Nat) :
    cf (B.flatMap fun b => f b :: g b) u =
      cf (B.map f) u + cf (B.flatMap g) u := by
  induction B with
  | nil => simp [cf]
  | cons b B ih =>
    simp only [List.flatMap_cons, List.map_cons, List.cons_append, cf_append]
    by_cases h : (f b).2.Perm u <;> simp [cf, h] at ih ⊢ <;> omega

private theorem cf_grid (A B : List Nat) (f : Nat → Nat → List Nat) (u : List Nat) :
    cf (A.flatMap fun a => B.map fun b => ((1 : Int), f a b)) u =
    cf (B.flatMap fun b => A.map fun a => ((1 : Int), f a b)) u := by
  induction A with
  | nil =>
    have hz : B.flatMap (fun _ => ([] : List (Int × List Nat))) = [] := by
      induction B <;> simp_all
    simp [hz, cf]
  | cons a A ih =>
    simp only [List.flatMap_cons, List.map_cons, cf_append]
    rw [cf_flat_cons, ih]

private theorem cf_negative (L : List (Int × List Nat)) (u : List Nat) :
    cf (L.map fun t => (-t.1,t.2)) u = -cf L u := by
  induction L with
  | nil => simp [cf]
  | cons t L ih =>
    by_cases h : t.2.Perm u <;> simp [cf, h] at ih ⊢ <;> omega

private theorem z_one_expansion (m n : Nat) : z m n 1 [] =
    (List.range m).map (fun i => (1,rowLabel i)) ++
    (List.range n).map (fun j => (-1,colLabel j)) := by
  have hr : freeRow [] = fun _ => true := rfl
  have hc : freeCol [] = fun _ => true := rfl
  have hf (L : List Nat) : L.filter (fun _ => true) = L :=
    List.filter_eq_self.mpr (by simp)
  simp only [z, Nat.sub_self]
  simp only [matchings, List.filter_cons, List.all_nil, Bool.true_eq,
    ↓reduceIte, List.filter_nil, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.nil_append]
  simp [rows, cols, hr, hc, hf, ordered, rowLabel, colLabel]

theorem z_one_top_zero (m n : Nat) (u : List Nat) :
    coeff (top m n (z m n 1 [])) u = 0 := by
  rw [z_one_expansion, top_append_coeff]
  have hr : freeRow [] = fun _ => true := rfl
  have hc : freeCol [] = fun _ => true := rfl
  have hf (L : List Nat) : L.filter (fun _ => true) = L :=
    List.filter_eq_self.mpr (by simp)
  simp [top, topLabel, rowLabel, colLabel, rows, cols, hr, hc, hf, mono,
    coeff, List.flatMap_map, List.map_map, Function.comp_def]
  have hg := cf_grid (List.range m) (List.range n) (fun i j => [i*n+j]) u
  have hn := cf_negative ((List.range n).flatMap fun j =>
    (List.range m).map fun i => ((1 : Int), [i*n+j])) u
  simp only [List.map_flatMap, List.map_map] at hn
  simp only [Function.comp_def, Int.reduceNeg] at hn
  omega

theorem z_one_kernel (p m n : Nat) : Kernel p m n 1 (z m n 1 []) := by
  refine ⟨?_, ?_⟩
  · intro a ha
    rw [z_one_expansion] at ha
    rw [labels_one]
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
      exact List.mem_append_left _ (List.mem_map.mpr ⟨i,hi,rfl⟩)
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
      exact List.mem_append_right _ (List.mem_map.mpr ⟨j,hj,rfl⟩)
  · intro u
    rw [z_one_top_zero]
    simp [coeff, cf]

theorem syzygies_one_sound (p m n : Nat) :
    ∀ v ∈ syzygies m n 1, Kernel p m n 1 v := by
  intro v hv
  have he : syzygies m n 1 = [z m n 1 []] := by simp [syzygies, matchings]
  rw [he] at hv
  have : v = z m n 1 [] := by simpa using hv
  subst v
  exact z_one_kernel p m n

/-- Degree-one cancellation no longer assumes generator soundness. -/
theorem first_block_kernel_residual_one {p m n : Nat} {v : Vector}
    (hv : Kernel p (m+1) n 1 v) (hs : Spanning p m n 1) :
    ∃ C : List (Int × Vector),
      (∀ t ∈ C, t.2 ∈ syzygies (m+1) n 1) ∧
      Kernel p (m+1) n 1 (v ++ (combine C).map (fun t => (-t.1,t.2))) ∧
      ∀ g, (p : Int) ∣ vectorCoeff (splitPigeon m 1
        (v ++ (combine C).map (fun t => (-t.1,t.2)))) g := by
  exact first_block_kernel_residual hv hs (syzygies_one_sound p (m+1) n)

end Programme.«20261104-1627-proof-complexity».MatchingLabels
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.z_one_top_zero
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.syzygies_one_sound

#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.first_block_kernel_residual_one
