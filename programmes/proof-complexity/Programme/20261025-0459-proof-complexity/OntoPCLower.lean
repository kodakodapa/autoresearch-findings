import Programme.«20261025-0459-proof-complexity».OntoBlowup
import Programme.«20261025-0459-proof-complexity».Cert3_33
import Programme.«20261025-0459-proof-complexity».Cert2_44

/-!
# All-`n` PC degree lower bounds for onto-FPHP from fixed-`n` certificates

`Work.Cert3_33.no_refutation` (onto-FPHP^{3+3}_3, no degree-2 refutation over `Z/3`) and
`Work.Cert2_44.no_refutation` (onto-FPHP^{4+4}_4, no degree-2 refutation over `Z/2`) are
kernel-checked R-operator certificates (`Work.PCCert2.Cert.sound`). Restriction and blow-up
(`Work.OntoBlowup.ontoFPHP_lift`) carry them to every `n ≥ c·n₀` at `k = c·k₀`, and degree
monotonicity to every `D ≤ 2`.
-/

namespace Programme.«20261025-0459-proof-complexity».OntoPCLower

open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261025-0459-proof-complexity».OntoFPHP

/-- A degree-`D` derivation is a degree-`D'` derivation for `D ≤ D'`. -/
theorem PPCDerivable.mono {p D D' : Nat} {A : List (Poly Nat)} (hD : D ≤ D')
    {g : (Nat → Bool) → Int} (h : PPCDerivable p A D g) : PPCDerivable p A D' g := by
  induction h with
  | ax P hP hd => exact PPCDerivable.ax P hP (Nat.le_trans hd hD)
  | lin f g u v _ _ ihf ihg => exact PPCDerivable.lin f g u v ihf ihg
  | mul x g d _ hc hd ih => exact PPCDerivable.mul x g d ih hc (Nat.le_trans hd hD)
  | congr f g _ hfg ih => exact PPCDerivable.congr f g ih hfg

/-- Over `Z/3`: for `c ≥ 1` and `n ≥ 3c`, onto-FPHP^{n+3c}_n has no PC refutation of degree `≤ 2`. -/
theorem f3_deg3 (c n D : Nat) (hc : 0 < c) (hn : c * 3 ≤ n) (hD : D ≤ 2) :
    ¬ PPCRefutation 3 (ontoFPHP n (c * 3)) D := fun h =>
  Programme.«20261025-0459-proof-complexity».OntoBlowup.ontoFPHP_lift 3 c 3 3 2 hc (by decide) (by decide) Programme.«20261025-0459-proof-complexity».Cert3_33.no_refutation n hn
    (PPCDerivable.mono hD h)

/-- Over `Z/2`: for `c ≥ 1` and `n ≥ 4c`, onto-FPHP^{n+4c}_n has no PC refutation of degree `≤ 2`. -/
theorem f2_deg3 (c n D : Nat) (hc : 0 < c) (hn : c * 4 ≤ n) (hD : D ≤ 2) :
    ¬ PPCRefutation 2 (ontoFPHP n (c * 4)) D := fun h =>
  Programme.«20261025-0459-proof-complexity».OntoBlowup.ontoFPHP_lift 2 c 4 4 2 hc (by decide) (by decide) Programme.«20261025-0459-proof-complexity».Cert2_44.no_refutation n hn
    (PPCDerivable.mono hD h)

end Programme.«20261025-0459-proof-complexity».OntoPCLower

#print axioms Programme.«20261025-0459-proof-complexity».OntoPCLower.f3_deg3
#print axioms Programme.«20261025-0459-proof-complexity».OntoPCLower.f2_deg3
