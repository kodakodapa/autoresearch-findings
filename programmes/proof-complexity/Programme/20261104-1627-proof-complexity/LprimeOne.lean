import Programme.«20261104-1627-proof-complexity».RectangularOne
import Programme.«20261104-1627-proof-complexity».DegreeTwoLabels
import Programme.«20261104-1627-proof-complexity».HoleRestriction
import Programme.«20261104-1627-proof-complexity».LprimeResidueLift

namespace Programme.«20261104-1627-proof-complexity».LprimeOne
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261104-1627-proof-complexity».LprimeStages
open Programme.«20261029-1156-proof-complexity».StdPC

private theorem aggregate_eq (a : Vector) (g : Label) : aggregate a g = vectorCoeff a g := by
  induction a with
  | nil => simp [aggregate, vectorCoeff]
  | cons t ts ih =>
    rw [aggregate_cons, vc_cons', ih]

private theorem singleton_mem {m n i j : Nat} (hi : i < m) (hj : j < n) :
    [(i,j)] ∈ matchings m n 1 := by
  rw [matchings_one]
  exact List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi,
    List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩⟩

/-- Exact characterization on actual matching coordinates, for every modulus. -/
theorem topImage_one_iff {p m n : Nat} (hn : 0 < n) (v : Matching → Int) :
    TopImage p m n 1 v ↔ ∃ a b : Nat → Int,
      ∀ i, i < m → ∀ j, j < n → (p : Int) ∣ v [(i,j)] - (a i + b j) := by
  constructor
  · rintro ⟨w, hw, he⟩
    refine ⟨fun i => vectorCoeff w (rowLabel i), fun j => vectorCoeff w (colLabel j), ?_⟩
    intro i hi j hj
    have h := he [(i,j)] (singleton_mem hi hj)
    simpa only [mono, List.map_cons, List.map_nil, top_one_edge hn w hw i j hi hj] using h
  · rintro ⟨a,b,he⟩
    let f : Label → Int := fun g => if g.isRow then a g.mark else b g.mark
    let w := rawLift (labels m n 1) f
    have hw : valid m n 1 w := rawLift_support _ _
    refine ⟨w, hw, ?_⟩
    intro M hM
    obtain ⟨i,hi,j,hj,rfl⟩ := matching_one_cases hM
    have hr : rowLabel i ∈ labels m n 1 := by simp [labels_one, rowLabel, hi]
    have hc : colLabel j ∈ labels m n 1 := by simp [labels_one, colLabel, hj]
    have hwr : vectorCoeff w (rowLabel i) = a i := by
      rw [← aggregate_eq, rawLift_coordinates _ _ _ hr]; rfl
    have hwc : vectorCoeff w (colLabel j) = b j := by
      rw [← aggregate_eq, rawLift_coordinates _ _ _ hc]; rfl
    simpa only [mono, List.map_cons, List.map_nil, top_one_edge hn w hw i j hi hj,
      hwr, hwc] using he i hi j hj

private theorem close_lt {n h j : Nat} (hj : j < n) (hh : h < n) (hne : j ≠ h) :
    closeHole h j < n-1 := by
  unfold closeHole
  split <;> omega

/-- Degree-one hole avoidance, including empty pigeon boards and all moduli. -/
theorem lprime_one (p m n : Nat) : Lprime p m n 1 := by
  intro hn v hv
  have hn' : 2 < n := by omega
  apply (topImage_one_iff (by omega) v).mpr
  by_cases hm : m = 0
  · exact ⟨fun _ => 0, fun _ => 0, by intro i hi; omega⟩
  refine ⟨fun i => v [(i,0)], fun j => v [(0,j)] - v [(0,0)], ?_⟩
  intro i hi j hj
  let h := if j = 1 then 2 else 1
  have hh : h < n := by dsimp [h]; split <;> omega
  have h0 : 0 ≠ h := by dsimp [h]; split <;> omega
  have hjh : j ≠ h := by dsimp [h]; split <;> omega
  obtain ⟨a,b,hab⟩ := (topImage_one_iff (by omega) (restrictCoordinates h v)).mp (hv h hh)
  have local_eq (i : Nat) (hi : i < m) (j : Nat) (hj : j < n) (hne : j ≠ h) :
      (p : Int) ∣ v [(i,j)] - (a i + b (closeHole h j)) := by
    have he := hab i hi (closeHole h j) (close_lt hj hh hne)
    simpa only [restrictCoordinates, pushMatching, List.map_cons, List.map_nil,
      omit_close h j hne] using he
  have h1 := local_eq i hi j hj hjh
  have h2 := local_eq i hi 0 (by omega) h0
  have h3 := local_eq 0 (by omega) j hj hjh
  have h4 := local_eq 0 (by omega) 0 (by omega) h0
  have hd := Int.dvd_add (Int.dvd_sub (Int.dvd_sub h1 h2) h3) h4
  have he : (v [(i,j)] - (a i + b (closeHole h j)) -
      (v [(i,0)] - (a i + b (closeHole h 0))) -
      (v [(0,j)] - (a 0 + b (closeHole h j))) +
      (v [(0,0)] - (a 0 + b (closeHole h 0)))) =
      v [(i,j)] - (v [(i,0)] + (v [(0,j)] - v [(0,0)])) := by omega
  rw [he] at hd
  exact hd

end Programme.«20261104-1627-proof-complexity».LprimeOne
#print axioms Programme.«20261104-1627-proof-complexity».LprimeOne.topImage_one_iff
#print axioms Programme.«20261104-1627-proof-complexity».LprimeOne.lprime_one
