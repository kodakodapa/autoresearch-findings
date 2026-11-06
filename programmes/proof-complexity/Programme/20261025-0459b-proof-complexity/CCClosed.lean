import Programme.«20261024-1633-proof-complexity».CCAssembly
import Programme.«20261024-1633-proof-complexity».Sunflower
import Programme.«20261024-1633-proof-complexity».KSub
import Programme.«20261024-1633-proof-complexity».Colour
import Programme.«20261024-1633-proof-complexity».CCArith

/-!
# Closed tree-like CP* lower bound for clique–colouring

`cc_closed` instantiates `CCAssembly.cc_assembly` with the promoted library definitions
(`Sunflower.fact`, `KSub.ch`, `KSub.ksub`, `KSub.sub`, `Colour.ch2`, `Colour.tot`, `Colour.rb`)
and lemmas (`sunflower_sets`, `mem_ksub`, `ksub_length`, `pos_count`, `tot_mono`, `tot_add`,
`tot_const`, `petal_count`, `rb_count`, `pos_ratio`). No counting hypotheses remain.
Formalisation of a known result (Bonet–Pitassi–Raz 1997, tree-like CP with bounded coefficients).
-/

namespace Programme.«20261025-0459b-proof-complexity».CCClosed

open Programme.«20261024-1633-proof-complexity».CPRange
open Programme.«20261024-1633-proof-complexity».CliqueColour

/-- For `ℓ ≥ 2`, `64ℓ⁴ ≤ k-1`, `64ℓ⁴k + ℓ ≤ m`, every tree-like CP refutation of `CC m k` with
`s` nodes and all line weights `≤ W` has `2^{4ℓ} ≤ 18 s (2k+6) (W+1)^2`. -/
theorem cc_closed (m k ℓ : Nat) (hℓ : 2 ≤ ℓ) (hk : 64 * ℓ ^ 4 ≤ k - 1)
    (hm : 64 * ℓ ^ 4 * k + ℓ ≤ m) (Rf : BRefutation (CC m k)) :
    2 ^ (4 * ℓ) ≤ 18 * (Rf.size * (2 * k + 6) * (Rf.W.toNat + 1) ^ 2) :=
  Programme.«20261024-1633-proof-complexity».CCAssembly.cc_assembly
    Programme.«20261024-1633-proof-complexity».Sunflower.fact rfl (fun _ => rfl)
    Programme.«20261024-1633-proof-complexity».KSub.ch (fun n => by cases n <;> rfl) (fun _ _ => rfl)
    Programme.«20261024-1633-proof-complexity».Colour.ch2 rfl (fun _ => rfl)
    Programme.«20261024-1633-proof-complexity».KSub.ksub
    Programme.«20261024-1633-proof-complexity».KSub.sub (fun _ _ => rfl)
    Programme.«20261024-1633-proof-complexity».Colour.tot
    Programme.«20261024-1633-proof-complexity».Colour.rb (fun _ _ => Iff.rfl)
    Programme.«20261024-1633-proof-complexity».Sunflower.sunflower_sets
    Programme.«20261024-1633-proof-complexity».KSub.mem_ksub
    Programme.«20261024-1633-proof-complexity».KSub.ksub_length
    Programme.«20261024-1633-proof-complexity».KSub.pos_count
    Programme.«20261024-1633-proof-complexity».Colour.tot_mono
    Programme.«20261024-1633-proof-complexity».Colour.tot_add
    Programme.«20261024-1633-proof-complexity».Colour.tot_const
    Programme.«20261024-1633-proof-complexity».Colour.petal_count
    Programme.«20261024-1633-proof-complexity».CCArith.rb_count
    Programme.«20261024-1633-proof-complexity».CCArith.pos_ratio
    m k ℓ hℓ hk hm Rf

end Programme.«20261025-0459b-proof-complexity».CCClosed

#print axioms Programme.«20261025-0459b-proof-complexity».CCClosed.cc_closed
