import Programme.«20261028-0841-proof-complexity».L3.Main
import Programme.«20261025-1627-proof-complexity».OntoQ7

/-! Level 3 over `Z/2`: `Hard 2 l 4` for every `l ≥ 3`, from `Work.L3.Main.no_deg4` and blow-up. -/

namespace Programme.«20261028-0841-proof-complexity».L3.Q7
open Programme.«20261025-1627-proof-complexity».OntoQ7

theorem hard3 : Hard 2 3 4 := ⟨7, fun n hn => by simpa using Programme.«20261028-0841-proof-complexity».L3.Main.no_deg4 n hn⟩

/-- For every `l ≥ 3`, for all large `n`, onto-FPHP^{n+2^l}_n has no degree-4 PC refutation over `Z/2`. -/
theorem hard_ge3 (l : Nat) (hl : 3 ≤ l) : Hard 2 l 4 :=
  hard_mono_l (by decide) (by decide) hl hard3

end Programme.«20261028-0841-proof-complexity».L3.Q7

#print axioms Programme.«20261028-0841-proof-complexity».L3.Q7.hard_ge3
