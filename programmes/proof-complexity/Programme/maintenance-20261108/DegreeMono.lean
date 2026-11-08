import Programme.«20261025-0459-proof-complexity».OntoFPHP
import Programme.«20261029-1156-proof-complexity».StdPC
import Programme.«20261027-0607-proof-complexity».Lucas
import Programme.«20261102-1249-proof-complexity».UniformC3.Unconditional
import Programme.«20261028-0841-proof-complexity».L3.Main

/-!
# Degree monotonicity of polynomial calculus (library maintenance, T166 addendum)

A derivation whose lines respect the degree bound `D` also respects any `D' ≥ D`: every rule's
side condition (`P.deg ≤ D`, `d + 1 ≤ D`, `2 ≤ D`, …) only gets weaker. So a lower bound at one
degree excludes refutations of every smaller degree.

* `PPCDerivable.mono`, `PPCRefutation.mono`: for `OntoFPHP.PPCDerivable` (cube polynomial calculus).
* `StdPC.Der.mono`, `StdPC.Refutes.mono`: for standard polynomial calculus over `F_p`.
* Corollaries of the published theorems, stated for every degree `≤ p` (resp. `≤ 4`):
  `uniform_no_degree_le_p`, `uniform_no_standard_degree_le_p`, `no_deg_le4`, and the same as
  lower bounds on the degree of any refutation. `Lucas.pc_degree_exact` is already an `↔` for
  every `D` and needs no corollary.
-/

namespace Programme.«maintenance-20261108».DegreeMono

open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261025-0459-proof-complexity».OntoFPHP (PPCDerivable PPCRefutation ontoFPHP)
open Programme.«20261027-0607-proof-complexity».Peel (IsPrime)

/-- Degree monotonicity of cube polynomial calculus. -/
theorem PPCDerivable.mono {p D D' : Nat} {A : List (Poly Nat)} {f : (Nat → Bool) → Int}
    (hD : D ≤ D') (h : PPCDerivable p A D f) : PPCDerivable p A D' f := by
  induction h with
  | ax P hP hd => exact .ax P hP (Nat.le_trans hd hD)
  | lin f g u v _ _ ihf ihg => exact .lin f g u v ihf ihg
  | mul x g d _ hc hd ih => exact .mul x g d ih hc (Nat.le_trans hd hD)
  | congr f g _ hfg ih => exact .congr f g ih hfg

theorem PPCRefutation.mono {p D D' : Nat} {A : List (Poly Nat)} (hD : D ≤ D')
    (h : PPCRefutation p A D) : PPCRefutation p A D' :=
  PPCDerivable.mono hD h

namespace StdPC
open Programme.«20261029-1156-proof-complexity».StdPC (Der Refutes)

/-- Degree monotonicity of standard polynomial calculus over `F_p`. -/
theorem Der.mono {p D D' : Nat} {A : List (Poly Nat)} {P : Poly Nat}
    (hD : D ≤ D') (h : Der p A D P) : Der p A D' P := by
  induction h with
  | ax P hP hd => exact .ax P hP (Nat.le_trans hd hD)
  | bool x h2 => exact .bool x (Nat.le_trans h2 hD)
  | lin u v P Q _ _ ihP ihQ => exact .lin u v P Q ihP ihQ
  | mul x P _ hd ih => exact .mul x P ih (Nat.le_trans hd hD)
  | eq P Q _ hPQ hd ih => exact .eq P Q ih hPQ (Nat.le_trans hd hD)

theorem Refutes.mono {p D D' : Nat} {A : List (Poly Nat)} (hD : D ≤ D')
    (h : Refutes p A D) : Refutes p A D' :=
  Der.mono hD h

end StdPC

open Programme.«20261029-1156-proof-complexity».StdPC (Refutes)

/-- Uniform C3: no cube-PC refutation over `Z/p` of any degree `≤ p`. -/
theorem uniform_no_degree_le_p {p : Nat} (hp : IsPrime p) (c n : Nat) (hn : 2*p-1 ≤ n)
    {D : Nat} (hD : D ≤ p) : ¬ PPCRefutation p (ontoFPHP n (c*p*p)) D := fun h =>
  Programme.«20261102-1249-proof-complexity».UniformC3.uniform_no_degree_p_unconditional
    hp c n hn (PPCRefutation.mono hD h)

/-- Uniform C3: every cube-PC refutation over `Z/p` has degree `> p`. -/
theorem uniform_degree_gt_p {p : Nat} (hp : IsPrime p) (c n : Nat) (hn : 2*p-1 ≤ n)
    {D : Nat} (h : PPCRefutation p (ontoFPHP n (c*p*p)) D) : p < D :=
  Nat.lt_of_not_le fun hD => uniform_no_degree_le_p hp c n hn hD h

/-- Uniform C3: no standard PC refutation over `F_p` of any degree `≤ p`. -/
theorem uniform_no_standard_degree_le_p {p : Nat} (hp : IsPrime p) (c n : Nat)
    (hn : 2*p-1 ≤ n) {D : Nat} (hD : D ≤ p) : ¬ Refutes p (ontoFPHP n (c*p*p)) D := fun h =>
  Programme.«20261102-1249-proof-complexity».UniformC3.uniform_no_standard_degree_p_unconditional
    hp c n hn (StdPC.Refutes.mono hD h)

/-- Uniform C3: every standard PC refutation over `F_p` has degree `> p`. -/
theorem uniform_standard_degree_gt_p {p : Nat} (hp : IsPrime p) (c n : Nat) (hn : 2*p-1 ≤ n)
    {D : Nat} (h : Refutes p (ontoFPHP n (c*p*p)) D) : p < D :=
  Nat.lt_of_not_le fun hD => uniform_no_standard_degree_le_p hp c n hn hD h

/-- L3: no cube-PC refutation of onto-FPHP^(n+8)_n over `Z/2` of any degree `≤ 4`, `n ≥ 7`. -/
theorem no_deg_le4 (n : Nat) (hn : 7 ≤ n) {D : Nat} (hD : D ≤ 4) :
    ¬ PPCRefutation 2 (ontoFPHP n 8) D := fun h =>
  Programme.«20261028-0841-proof-complexity».L3.Main.no_deg4 n hn (PPCRefutation.mono hD h)

/-- L3: every cube-PC refutation of onto-FPHP^(n+8)_n over `Z/2` (`n ≥ 7`) has degree `≥ 5`. -/
theorem deg_ge5 (n : Nat) (hn : 7 ≤ n) {D : Nat} (h : PPCRefutation 2 (ontoFPHP n 8) D) :
    5 ≤ D :=
  Nat.lt_of_not_le fun hD => no_deg_le4 n hn hD h

end Programme.«maintenance-20261108».DegreeMono

#print axioms Programme.«maintenance-20261108».DegreeMono.PPCDerivable.mono
#print axioms Programme.«maintenance-20261108».DegreeMono.PPCRefutation.mono
#print axioms Programme.«maintenance-20261108».DegreeMono.StdPC.Der.mono
#print axioms Programme.«maintenance-20261108».DegreeMono.StdPC.Refutes.mono
#print axioms Programme.«maintenance-20261108».DegreeMono.uniform_no_degree_le_p
#print axioms Programme.«maintenance-20261108».DegreeMono.uniform_degree_gt_p
#print axioms Programme.«maintenance-20261108».DegreeMono.uniform_no_standard_degree_le_p
#print axioms Programme.«maintenance-20261108».DegreeMono.uniform_standard_degree_gt_p
#print axioms Programme.«maintenance-20261108».DegreeMono.no_deg_le4
#print axioms Programme.«maintenance-20261108».DegreeMono.deg_ge5
