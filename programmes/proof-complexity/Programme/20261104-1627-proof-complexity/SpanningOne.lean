import Programme.«20261104-1627-proof-complexity».HomogeneousLabels

namespace Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261029-1156-proof-complexity».StdPC

private def r : Label := ⟨[], true, 0⟩
private def c : Label := ⟨[], false, 0⟩

private theorem labels11 : labels 1 1 1 = [r,c] := by decide

private theorem z11 : z 1 1 1 [] = [(1,r),(-1,c)] := by
  simp [z, matchings, rows, cols, freeRow, freeCol, ordered, r, c, List.filter_cons, List.all_nil, List.flatMap_cons]

private theorem vc_cons (a : Int × Label) (v : Vector) (g : Label) :
    vectorCoeff (a :: v) g = (if a.2 = g then a.1 else 0) + vectorCoeff v g := by
  by_cases h : a.2 = g <;> simp [vectorCoeff, h]

private theorem edge_coeff (v : Vector) (hv : valid 1 1 1 v) :
    coeff (top 1 1 v) [0] = vectorCoeff v r + vectorCoeff v c := by
  induction v with
  | nil => simp [top, coeff, cf, vectorCoeff]
  | cons a v ih =>
    have ha := hv a List.mem_cons_self
    rw [labels11] at ha
    have hv' : valid 1 1 1 v := fun t ht => hv t (List.mem_cons_of_mem a ht)
    have hi := ih hv'
    rcases List.mem_cons.mp ha with ha | ha
    · have he : a.2 = r := ha
      rcases a with ⟨a,g⟩
      dsimp at he
      subst g
      simp [top, topLabel, r, c, cols, rows, freeRow, freeCol, mono,
        coeff, cf, vectorCoeff, List.filter_cons] at hi ⊢
      omega
    · have he : a.2 = c := by simpa using ha
      rcases a with ⟨a,g⟩
      dsimp at he
      subst g
      simp [top, topLabel, r, c, cols, rows, freeRow, freeCol, mono,
        coeff, cf, vectorCoeff, List.filter_cons] at hi ⊢
      omega

private theorem outside_coeff (v : Vector) (hv : valid 1 1 1 v)
    (g : Label) (hr : g ≠ r) (hc : g ≠ c) : vectorCoeff v g = 0 := by
  induction v with
  | nil => simp [vectorCoeff]
  | cons a v ih =>
    rw [vc_cons]
    have ha := hv a List.mem_cons_self
    rw [labels11] at ha
    have hne : a.2 ≠ g := by
      intro he
      rw [he] at ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      exact ha.elim hr hc
    rw [ite_eq_right hne, ih (fun t ht => hv t (List.mem_cons_of_mem a ht))]
    simp

/-- The actual degree-one square spanning assertion in the label interface.
This includes arbitrary raw-vector presentations, not just edge coordinates. -/
theorem square_one (p : Nat) : Square p 1 := by
  change Spanning p 1 1 1
  intro v hv
  let a := vectorCoeff v r
  refine ⟨[(a, z 1 1 1 [])], ?_, ?_⟩
  · intro t ht
    have he : t = (a, z 1 1 1 []) := by simpa using ht
    subst t
    change z 1 1 1 [] ∈ syzygies 1 1 1
    simp [syzygies, matchings]
  · intro g
    have hk := hv.2 [0]
    rw [edge_coeff v hv.1] at hk
    simp only [coeff, cf, List.filter_nil, List.map_nil, List.sum_nil, Int.sub_zero] at hk
    by_cases hr : g = r
    · subst g
      simp [combine, z11, vectorCoeff, a, r, c]
    · by_cases hc : g = c
      · subst g
        simpa [combine, z11, vectorCoeff, r, c, a, Int.sub_neg, Int.add_comm] using hk
      · rw [outside_coeff v hv.1 g hr hc]
        have hrg : r ≠ g := Ne.symm hr
        have hcg : c ≠ g := Ne.symm hc
        simp [combine, z11, vectorCoeff, hrg, hcg]

end Programme.«20261104-1627-proof-complexity».MatchingLabels
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.square_one
