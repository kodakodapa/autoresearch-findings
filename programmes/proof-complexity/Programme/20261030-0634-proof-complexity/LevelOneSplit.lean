import Programme.«20261026-1402-proof-complexity».ExtLin
import Programme.«20261030-0634-proof-complexity».LevelOne

namespace Programme.«20261030-0634-proof-complexity».LevelOneSplit
open Programme.«20261026-1402-proof-complexity».ExtLemma
open Programme.«20261026-1402-proof-complexity».ExtLin

/-- A fixed unit-balanced input separates the scalar and zero-link parts of EXT. -/
theorem ext1_iff_unit_kernel (p n k : Nat) (w : List Nat → Int)
    (hw : Bal p n k w (fun _ => 1) 0) :
    EXT p n k 1 ↔
      (∃ y, Bal p n k y w 1) ∧
      (∀ f : List Nat → Int, Bal p n k f (fun _ => 0) 0 →
        ∃ y, Bal p n k y f 1) := by
  rw [Programme.«20261030-0634-proof-complexity».LevelOne.ext1_iff_scalar]
  constructor
  · intro h
    exact ⟨h w 1 hw, fun f hf => h f 0 hf⟩
  · rintro ⟨⟨u, hu⟩, hz⟩ f s hf
    have hg : Bal p n k (fun g => f g + (-s) * w g) (fun _ => 0) 0 := by
      have ht := Bal_add hf (Bal_smul (-s) hw)
      apply Bal_congr ht
      intro g _ _
      have he : (0 : Int) - (s + -s * 1) = 0 := by omega
      rw [he]
      exact ⟨0, by omega⟩
    obtain ⟨v, hv⟩ := hz _ hg
    refine ⟨fun g => v g + s * u g, ?_⟩
    apply Bal_congr (Bal_add hv (Bal_smul s hu))
    intro g _ _
    have he : f g - (f g + -s * w g + s * w g) = 0 := by rw [Int.neg_mul]; omega
    rw [he]
    exact ⟨0, by omega⟩

#print axioms ext1_iff_unit_kernel
end Programme.«20261030-0634-proof-complexity».LevelOneSplit
