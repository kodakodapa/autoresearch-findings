import Programme.«20261025-0459-proof-complexity».OntoLucas
import Programme.«20261025-1627-proof-complexity».CertF3_59

/-!
# Over `Z/3`: the PC degree of onto-FPHP is exactly 3 at `k = 3` and at least 4 at `k = 9` (all `n ≥ 5`)

`Work.CertF3_59.no_refutation` (onto-FPHP^{5+9}_5 has no degree-3 PC refutation over `Z/3`) is a
kernel-checked bit-sliced R-operator certificate (`Work.PCCertF3.Cert.sound`). It discharges the
hypothesis of `Programme.«20261025-0459-proof-complexity».OntoLucas.f3_sep_of`; with `Programme.«20261025-0459-proof-complexity».OntoLucas.f3_k3_exact` this gives a strict step
`l = 1 → 2` of the `Z/3` plateau for `k = 3^l`, for every `n ≥ 5`. Blow-up
(`Programme.«20261025-0459-proof-complexity».OntoBlowup.ontoFPHP_lift`) carries the lower bound to every multiple `k = 9c`, `n ≥ 5c`.
-/

namespace Programme.«20261025-1627-proof-complexity».OntoF3K9

open Programme.«20261025-0459-proof-complexity».OntoFPHP

/-- For `n ≥ 5`: onto-FPHP^{n+3}_n has a degree-3 PC refutation over `Z/3`, onto-FPHP^{n+9}_n none. -/
theorem f3_sep (n : Nat) (hn : 5 ≤ n) :
    PPCRefutation 3 (ontoFPHP n 3) 3 ∧ ¬ PPCRefutation 3 (ontoFPHP n 9) 3 :=
  Programme.«20261025-0459-proof-complexity».OntoLucas.f3_sep_of Programme.«20261025-1627-proof-complexity».CertF3_59.no_refutation n hn

/-- For `c ≥ 1`, `n ≥ 5c`, `D ≤ 3`: onto-FPHP^{n+9c}_n has no degree-`D` PC refutation over `Z/3`. -/
theorem f3_deg4 (c n D : Nat) (hc : 0 < c) (hn : c * 5 ≤ n) (hD : D ≤ 3) :
    ¬ PPCRefutation 3 (ontoFPHP n (c * 9)) D := fun h =>
  Programme.«20261025-0459-proof-complexity».OntoBlowup.ontoFPHP_lift 3 c 5 9 3 hc (by decide) (by decide) Programme.«20261025-1627-proof-complexity».CertF3_59.no_refutation n hn
    (Programme.«20261025-0459-proof-complexity».OntoPCLower.PPCDerivable.mono hD h)

/-- The `Z/3` plateau for `k = 3^l` at `l = 1, 2`: for every `n ≥ 5` and `D`, onto-FPHP^{n+3}_n is
refutable in degree `D` iff `D ≥ 3`, and onto-FPHP^{n+9}_n only if `D ≥ 4`. -/
theorem f3_plateau (n D : Nat) (hn : 5 ≤ n) :
    (PPCRefutation 3 (ontoFPHP n 3) D ↔ 3 ≤ D) ∧ (PPCRefutation 3 (ontoFPHP n 9) D → 4 ≤ D) :=
  ⟨Programme.«20261025-0459-proof-complexity».OntoLucas.f3_k3_exact n D (by omega), fun h => by
    apply Classical.byContradiction; intro hD
    exact f3_deg4 1 n D (by decide) (by omega) (by omega) (by simpa using h)⟩

end Programme.«20261025-1627-proof-complexity».OntoF3K9

#print axioms Programme.«20261025-1627-proof-complexity».OntoF3K9.f3_sep
#print axioms Programme.«20261025-1627-proof-complexity».OntoF3K9.f3_deg4
#print axioms Programme.«20261025-1627-proof-complexity».OntoF3K9.f3_plateau
