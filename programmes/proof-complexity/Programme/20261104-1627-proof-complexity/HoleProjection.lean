/- Mirror label projection for P623. Proofs adapted from the canonical
PigeonProjection module; no variable-code or Kernel transport is asserted. -/
import Programme.«20261104-1627-proof-complexity».PigeonKernel

namespace Programme.«20261104-1627-proof-complexity».HoleProjection
open Programme.«20261104-1627-proof-complexity».MatchingLabels


def usesHole (w : Nat) (g : Label) : Bool := g.base.any fun e => e.2 == w

def holeBlock (w : Nat) (g : Label) : Nat :=
  if usesHole w g then 3 else if (!g.isRow) && g.mark == w then 2 else 1

def splitHole (w b : Nat) (v : Vector) : Vector :=
  v.filter fun t => holeBlock w t.2 == b

theorem matching_drop_hole {m n d : Nat} (M : Matching)
    (hM : M ∈ matchings m (n+1) d) (ha : ∀ e ∈ M, e.2 ≠ n) :
    M ∈ matchings m n d := by
  induction d generalizing M with
  | zero => simpa only [matchings] using hM
  | succ d ih =>
    simp only [matchings, List.mem_flatMap, List.mem_map] at hM ⊢
    obtain ⟨N,hN,i,hi,j,hj,rfl⟩ := hM
    refine ⟨N, ih N hN (by intro e he; exact ha e (List.mem_append_left _ he)),
      i,hi,j,?_,rfl⟩
    have hjn : j ≠ n := ha (i,j) (by simp)
    simp only [cols, List.mem_filter, List.mem_range] at hj ⊢
    exact ⟨by omega, hj.2⟩

theorem matching_add_hole {m n d : Nat} (M : Matching)
    (hM : M ∈ matchings m n d) : M ∈ matchings m (n+1) d := by
  induction d generalizing M with
  | zero => simpa only [matchings] using hM
  | succ d ih =>
    simp only [matchings, List.mem_flatMap, List.mem_map] at hM ⊢
    obtain ⟨N,hN,i,hi,j,hj,rfl⟩ := hM
    refine ⟨N,ih N hN,i,hi,j,?_,rfl⟩
    simp only [cols, List.mem_filter, List.mem_range] at hj ⊢
    exact ⟨by omega,hj.2⟩

theorem label_drop_hole {m n d : Nat} (g : Label)
    (hg : g ∈ labels m (n+1) d) (hb : holeBlock n g = 1) :
    g ∈ labels m n d := by
  have hu : usesHole n g = false := by
    unfold holeBlock at hb
    split at hb <;> simp_all
  have ha : ∀ e ∈ g.base, e.2 ≠ n := by
    intro e he heq
    have : usesHole n g = true := by
      simp only [usesHole, List.any_eq_true]
      exact ⟨e, he, by simp [heq]⟩
    simp_all
  have hm : g.isRow = false → g.mark ≠ n := by
    intro hr heq
    simp [holeBlock, hu, hr, heq] at hb
  unfold labels at hg ⊢
  split at hg
  · contradiction
  · rename_i hd
    rw [if_neg hd]
    simp only [List.mem_flatMap, List.mem_append, List.mem_map] at hg ⊢
    obtain ⟨M, hM, hg⟩ := hg
    rcases hg with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
    · refine ⟨M, matching_drop_hole M hM ha, Or.inl ⟨i, ?_, rfl⟩⟩
      exact hi
    · refine ⟨M, matching_drop_hole M hM ha, Or.inr ⟨j, ?_, rfl⟩⟩
      simp only [cols, List.mem_filter, List.mem_range] at hj ⊢
      exact ⟨by have := hm rfl; simp only at this; omega, hj.2⟩

theorem splitHole_one_valid {m n d : Nat} {v : Vector}
    (hv : valid m (n+1) d v) : valid m n d (splitHole n 1 v) := by
  intro t ht
  obtain ⟨ht, hb⟩ := List.mem_filter.mp ht
  exact label_drop_hole t.2 (hv t ht) (by simpa using hb)

theorem label_add_hole {m n d : Nat} (g : Label)
    (hg : g ∈ labels m n d) :
    g ∈ labels m (n+1) d ∧ holeBlock n g = 1 := by
  unfold labels at hg
  split at hg
  · contradiction
  · rename_i hd
    simp only [List.mem_flatMap, List.mem_append, List.mem_map] at hg
    obtain ⟨M, hM, hg⟩ := hg
    have hu : usesHole n (⟨M,true,0⟩ : Label) = false := by
      apply Bool.eq_false_iff.mpr
      intro h
      obtain ⟨e, he, hm⟩ := List.any_eq_true.mp h
      have he' := matching_cols_lt hM e he
      simp only [beq_iff_eq] at hm
      omega
    have hu' (b : Bool) (i : Nat) : usesHole n (⟨M,b,i⟩ : Label) = false := hu
    rcases hg with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
    · have him : i < m := List.mem_range.mp (List.mem_filter.mp hi).1
      constructor
      · simp only [labels, hd, ↓reduceIte, List.mem_flatMap, List.mem_append, List.mem_map]
        refine ⟨M, matching_add_hole M hM, Or.inl ⟨i, ?_, rfl⟩⟩
        exact hi
      · simp [holeBlock, hu']
    · constructor
      · simp only [labels, hd, ↓reduceIte, List.mem_flatMap, List.mem_append, List.mem_map]
        refine ⟨M, matching_add_hole M hM, Or.inr ⟨j, ?_, rfl⟩⟩
        simp only [cols, List.mem_filter, List.mem_range] at hj ⊢
        exact ⟨by omega, hj.2⟩
      · have hjn : j < n := List.mem_range.mp (List.mem_filter.mp hj).1
        simp [holeBlock, hu', show j ≠ n by omega]

/-- The first block is precisely the original smaller-board label set. -/
theorem label_first_hole_iff {m n d : Nat} (g : Label) :
    (g ∈ labels m (n+1) d ∧ holeBlock n g = 1) ↔
      g ∈ labels m n d := by
  exact ⟨fun h => label_drop_hole g h.1 h.2, label_add_hole g⟩

end Programme.«20261104-1627-proof-complexity».HoleProjection
#print axioms Programme.«20261104-1627-proof-complexity».HoleProjection.splitHole_one_valid
#print axioms Programme.«20261104-1627-proof-complexity».HoleProjection.label_first_hole_iff
