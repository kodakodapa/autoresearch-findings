import Programme.«20261104-1627-proof-complexity».MixedAggregate
import Programme.«20261104-1627-proof-complexity».ReconstructionChecker
import Programme.«20261104-1627-proof-complexity».AnchoredValidity

namespace Programme.«20261104-1627-proof-complexity».IndexedCombination
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261104-1627-proof-complexity».ReconstructionChecker
open Programme.«20261104-1627-proof-complexity».MixedAggregate

def witness (G : List Vector) (w : Nat → Int) : List (Int × Vector) :=
  (List.range G.length).map fun k => (w k, G[k]?.getD [])

theorem coefficient (G : List Vector) (w : Nat → Int) (g : Label) :
    vectorCoeff (combine (witness G w)) g =
      dot (List.range G.length) (fun k => vectorCoeff (G[k]?.getD []) g) w := by
  rw [coeff_combine]
  simp only [witness, List.map_map, Function.comp_def, dot]
  congr 1
  apply List.map_congr_left
  intro k _
  exact Int.mul_comm _ _

theorem member (G : List Vector) (w : Nat → Int) :
    ∀ t ∈ witness G w, t.2 ∈ G := by
  intro t ht
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ht
  have h : k < G.length := List.mem_range.mp hk
  simp only [List.getElem?_eq_getElem h, Option.getD_some]
  exact List.getElem_mem h

private theorem outside {m n d : Nat} {v : Vector} (hv : valid m n d v)
    {g : Label} (hg : g ∉ labels m n d) : vectorCoeff v g = 0 := by
  induction v with
  | nil => simp [vectorCoeff]
  | cons a v ih =>
    have hn : a.2 ≠ g := by
      intro he
      exact hg (he ▸ hv a (by simp))
    have hv' : valid m n d v := by
      intro t ht
      exact hv t (by simp [ht])
    simpa [vectorCoeff, hn] using ih hv'

/-- Finite coordinate reconstruction supplies the raw Spanning witness, including
its required vanishing on every label outside the enumeration. -/
theorem spanning_of_coordinates {p m n d : Nat}
    (h : ∀ v, Kernel p m n d v → ∃ w : Nat → Int,
      ∀ g ∈ labels m n d, (p : Int) ∣ vectorCoeff v g -
        dot (List.range (syzygies m n d).length)
          (fun k => vectorCoeff ((syzygies m n d)[k]?.getD []) g) w) :
    Spanning p m n d := by
  intro v hv
  obtain ⟨w, hw⟩ := h v hv
  let c := witness (syzygies m n d) w
  have hc : ∀ t ∈ c, t.2 ∈ syzygies m n d := member _ _
  have hk : Kernel p m n d (combine c) :=
    kernel_combine c (fun t ht => syzygies_sound p m n d t.2 (hc t ht))
  refine ⟨c, hc, ?_⟩
  intro g
  by_cases hg : g ∈ labels m n d
  · rw [show vectorCoeff (combine c) g = _ from coefficient _ _ g]
    exact hw g hg
  · rw [outside hv.1 hg, outside hk.1 hg]
    simp

end Programme.«20261104-1627-proof-complexity».IndexedCombination
#print axioms Programme.«20261104-1627-proof-complexity».IndexedCombination.coefficient
#print axioms Programme.«20261104-1627-proof-complexity».IndexedCombination.member

#print axioms Programme.«20261104-1627-proof-complexity».IndexedCombination.spanning_of_coordinates
