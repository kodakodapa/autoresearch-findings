import Programme.«20261025-0459-proof-complexity».OntoLucas
import Programme.«20261025-1627-proof-complexity».CertF2_54

/-!
# Over `Z/2`: the PC degree of onto-FPHP is exactly 2 at `k = 2` and exactly 4 at `k = 4` (all `n ≥ 5`)

`Work.CertF2_54.no_refutation` (onto-FPHP^{5+4}_5 has no degree-3 PC refutation over `Z/2`) is a
kernel-checked bitset R-operator certificate (`Work.PCCertF2.Cert.sound`). It discharges the
hypothesis of `Programme.«20261025-0459-proof-complexity».OntoLucas.f2_k4_exact_of`; with `Programme.«20261025-0459-proof-complexity».OntoLucas.f2_k2_exact` this gives the
strict step `l = 1 → 2` of the `Z/2` plateau for `k = 2^l`, for every `n ≥ 5`. Blow-up
(`Programme.«20261025-0459-proof-complexity».OntoBlowup.ontoFPHP_lift`) carries the lower bound to every multiple `k = 4c`, `n ≥ 5c`.
-/

namespace Programme.«20261025-1627-proof-complexity».OntoF2K4

open Programme.«20261025-0459-proof-complexity».OntoFPHP

/-- For `n ≥ 5`: onto-FPHP^{n+4}_n has a degree-`D` PC refutation over `Z/2` iff `D ≥ 4`. -/
theorem f2_k4_exact (n D : Nat) (hn : 5 ≤ n) : PPCRefutation 2 (ontoFPHP n 4) D ↔ 4 ≤ D :=
  Programme.«20261025-0459-proof-complexity».OntoLucas.f2_k4_exact_of Programme.«20261025-1627-proof-complexity».CertF2_54.no_refutation n D hn

/-- For `c ≥ 1`, `n ≥ 5c`, `D ≤ 3`: onto-FPHP^{n+4c}_n has no degree-`D` PC refutation over `Z/2`. -/
theorem f2_deg4 (c n D : Nat) (hc : 0 < c) (hn : c * 5 ≤ n) (hD : D ≤ 3) :
    ¬ PPCRefutation 2 (ontoFPHP n (c * 4)) D := fun h =>
  Programme.«20261025-0459-proof-complexity».OntoBlowup.ontoFPHP_lift 2 c 5 4 3 hc (by decide) (by decide) Programme.«20261025-1627-proof-complexity».CertF2_54.no_refutation n hn
    (Programme.«20261025-0459-proof-complexity».OntoPCLower.PPCDerivable.mono hD h)

/-- The `Z/2` plateau for `k = 2^l` at `l = 1, 2`: for every `n ≥ 5` and `D`, onto-FPHP^{n+2}_n is
refutable in degree `D` iff `D ≥ 2`, and onto-FPHP^{n+4}_n iff `D ≥ 4`. -/
theorem f2_plateau (n D : Nat) (hn : 5 ≤ n) :
    (PPCRefutation 2 (ontoFPHP n 2) D ↔ 2 ≤ D) ∧ (PPCRefutation 2 (ontoFPHP n 4) D ↔ 4 ≤ D) :=
  ⟨Programme.«20261025-0459-proof-complexity».OntoLucas.f2_k2_exact n D (by omega), f2_k4_exact n D hn⟩

end Programme.«20261025-1627-proof-complexity».OntoF2K4

#print axioms Programme.«20261025-1627-proof-complexity».OntoF2K4.f2_k4_exact
#print axioms Programme.«20261025-1627-proof-complexity».OntoF2K4.f2_deg4
#print axioms Programme.«20261025-1627-proof-complexity».OntoF2K4.f2_plateau
