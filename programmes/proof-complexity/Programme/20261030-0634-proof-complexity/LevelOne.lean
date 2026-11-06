import Programme.«20261026-1402-proof-complexity».ExtLemma

namespace Programme.«20261030-0634-proof-complexity».LevelOne
open Programme.«20261026-1402-proof-complexity».ExtLemma

/-- Level one needs only a scalar common predecessor. -/
theorem ext1_iff_scalar (p n k : Nat) :
    EXT p n k 1 ↔
      ∀ (f : List Nat → Int) (s : Int),
        Bal p n k f (fun _ => s) 0 → ∃ y, Bal p n k y f 1 := by
  constructor
  · intro h f s hb
    apply h f (fun _ => s)
    intro e he
    have hz : e = 0 := by omega
    subst e
    exact hb
  · intro h f c hb
    apply h f (c [])
    intro g hg hlen
    have he : g = [] := List.eq_nil_of_length_eq_zero hlen
    subst g
    exact hb 0 rfl [] hg rfl

#print axioms ext1_iff_scalar
end Programme.«20261030-0634-proof-complexity».LevelOne
