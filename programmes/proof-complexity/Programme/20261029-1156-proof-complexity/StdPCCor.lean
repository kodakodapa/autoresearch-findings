import Programme.«20261029-1156-proof-complexity».StdPC
import Programme.«20261025-0459-proof-complexity».OntoPCLower
import Programme.«20261025-0459-proof-complexity».OntoSubst
import Programme.«20261025-1627-proof-complexity».OntoQ7
import Programme.«20261028-0841-proof-complexity».L3.Q7
import Programme.«20261027-0607-proof-complexity».Peel
import Programme.«20261027-0607-proof-complexity».P5Main
import Programme.«20261027-0607-proof-complexity».P7Main

/-!
# The library's onto-FPHP lower bounds, restated for standard polynomial calculus

Each statement below is a library `¬ PPCRefutation` theorem pushed through `Work.StdPC.not_refutes`:
it says that there is no standard (syntactic, Boolean axioms `x² - x`, coefficients mod `p`)
degree-`D` polynomial calculus refutation `Refutes p (ontoFPHP n k) D`.
`refutes_sanity` shows the standard calculus is not vacuous: it refutes `ontoFPHP 1 1` over `F_2`
in degree 1.
-/

namespace Programme.«20261029-1156-proof-complexity».StdPCCor

open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261029-1156-proof-complexity».StdPC

/-- `Hard` for standard PC: for all large `n`, onto-FPHP^{n+p^l}_n has no standard degree-`D`
refutation over `F_p`. -/
def SHard (p l D : Nat) : Prop := ∃ N, ∀ n, N ≤ n → ¬ Refutes p (ontoFPHP n (p ^ l)) D

theorem shard_of_hard {p l D : Nat} (hp : 1 < p)
    (h : Programme.«20261025-1627-proof-complexity».OntoQ7.Hard p l D) : SHard p l D :=
  let ⟨N, hN⟩ := h; ⟨N, fun n hn => not_refutes hp (hN n hn)⟩

/-- Level 3 over `F_2` (library `L3.Q7.hard_ge3`), standard PC. -/
theorem std_hard_ge3 (l : Nat) (hl : 3 ≤ l) : SHard 2 l 4 :=
  shard_of_hard (by decide) (Programme.«20261028-0841-proof-complexity».L3.Q7.hard_ge3 l hl)

/-- Level 2 over `F_2` and `F_3` (library `OntoQ7.q7_facts`), standard PC. -/
theorem std_hard_ge2 (l : Nat) (hl : 2 ≤ l) : SHard 2 l 3 ∧ SHard 3 l 3 :=
  let h := (Programme.«20261025-1627-proof-complexity».OntoQ7.q7_facts).2.2.2 l hl
  ⟨shard_of_hard (by decide) h.1, shard_of_hard (by decide) h.2⟩

/-- `k = 8` over `F_2`, `n ≥ 7`: no standard degree-4 refutation. -/
theorem std_no_deg4_k8 (n : Nat) (hn : 7 ≤ n) : ¬ Refutes 2 (ontoFPHP n 8) 4 :=
  not_refutes (by decide) (Programme.«20261028-0841-proof-complexity».L3.Main.no_deg4 n hn)

/-- `k = 25` over `F_5`, `n ≥ 9`: no standard degree-5 refutation. -/
theorem std_no_deg5_k25 (n : Nat) (hn : 9 ≤ n) : ¬ Refutes 5 (ontoFPHP n 25) 5 :=
  not_refutes (by decide) (Programme.«20261027-0607-proof-complexity».P5Main.no_deg5_k25 n hn)

/-- `k = 49` over `F_7`, `n ≥ 13`: no standard degree-7 refutation. -/
theorem std_no_deg7_k49 (n : Nat) (hn : 13 ≤ n) : ¬ Refutes 7 (ontoFPHP n 49) 7 :=
  not_refutes (by decide) (Programme.«20261027-0607-proof-complexity».P7.no_deg7 n hn)

/-- Prime `p`, `p ∣ k`, `n ≥ 2p - 3`: no standard refutation of degree `< p`. -/
theorem std_lower_p {p k : Nat} (hp : Programme.«20261027-0607-proof-complexity».Peel.IsPrime p)
    (hk : p ∣ k) (n : Nat) (hn : 2 * p - 3 ≤ n) (D : Nat) (hD : D < p) :
    ¬ Refutes p (ontoFPHP n k) D := fun h =>
  Programme.«20261027-0607-proof-complexity».Peel.pc_degree_ge_p hp hk n hn
    (Programme.«20261025-0459-proof-complexity».OntoPCLower.PPCDerivable.mono (by omega)
      (refutes_ppc (by have := hp.1; omega) h))

/-! ## Non-vacuity -/

theorem coeff_one_mod2 : PEq 2
    (lc 1 (-1) (lc 1 1 (sumOne (fun j => var 1 0 j) 1) (sumOne (fun j => var 1 1 j) 1))
      (sumOne (fun i => var 1 i 0) 2)) Poly.one := by
  intro m
  rcases m with _ | ⟨a, _ | ⟨b, m⟩⟩
  · decide
  · rcases a with _ | _ | a <;> simp [coeff, cf, lc, sumOne, linTerms, var, Poly.one, List.filter_cons]
  · simp [coeff, cf, lc, sumOne, linTerms, var, Poly.one, List.filter_cons]

/-- The standard calculus refutes onto-FPHP^2_1 over `F_2` in degree 1
(sum of pigeon axioms minus the hole axiom is the constant `-1 ≡ 1`). -/
theorem refutes_sanity : Refutes 2 (ontoFPHP 1 1) 1 := by
  have m0 : sumOne (fun j => var 1 0 j) 1 ∈ ontoFPHP 1 1 :=
    Programme.«20261025-0459-proof-complexity».OntoSubst.mem_pig (by decide)
  have m1 : sumOne (fun j => var 1 1 j) 1 ∈ ontoFPHP 1 1 :=
    Programme.«20261025-0459-proof-complexity».OntoSubst.mem_pig (by decide)
  have mh : sumOne (fun i => var 1 i 0) (1 + 1) ∈ ontoFPHP 1 1 :=
    Programme.«20261025-0459-proof-complexity».OntoSubst.mem_hole (by decide)
  have d0 := Der.ax (p := 2) (D := 1) _ m0 (sumOne_deg _ _)
  have d1 := Der.ax (p := 2) (D := 1) _ m1 (sumOne_deg _ _)
  have dh := Der.ax (p := 2) (D := 1) _ mh (sumOne_deg _ _)
  exact Der.eq _ _ (Der.lin 1 (-1) _ _ (Der.lin 1 1 _ _ d0 d1) dh) coeff_one_mod2 (by decide)

end Programme.«20261029-1156-proof-complexity».StdPCCor

#print axioms Programme.«20261029-1156-proof-complexity».StdPCCor.std_hard_ge3
#print axioms Programme.«20261029-1156-proof-complexity».StdPCCor.std_hard_ge2
#print axioms Programme.«20261029-1156-proof-complexity».StdPCCor.std_no_deg4_k8
#print axioms Programme.«20261029-1156-proof-complexity».StdPCCor.std_no_deg5_k25
#print axioms Programme.«20261029-1156-proof-complexity».StdPCCor.std_no_deg7_k49
#print axioms Programme.«20261029-1156-proof-complexity».StdPCCor.std_lower_p
#print axioms Programme.«20261029-1156-proof-complexity».StdPCCor.refutes_sanity
