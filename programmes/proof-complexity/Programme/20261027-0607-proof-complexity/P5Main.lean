import Programme.«20261027-0607-proof-complexity».P5Check
import Programme.«20261027-0607-proof-complexity».PeelV

/-!
# Conjecture V at `p = 5`: no degree-5 PC refutation of onto-FPHP^{n+25}_n over `Z/5`

th's unit degree-5 design for `ontoFPHP 9 25` over `Z/5` (K21, P65), invariant under a group of
order prime to 5, is the class function `Work.P5.T`. `Work.P5.bal_of_enum` reduces `Bal 5 9 25 T T e`
(`e ≤ 4`) to the reduced equations at every class-count matrix, and `Work.P5.enum_all` checks
those by kernel evaluation. With `T [] = 1`, `Work.PeelV.no_deg_p_of_design` (`n₀ = 9 = 2p - 1`)
gives the bound for every `n ≥ 9`.
-/

namespace Programme.«20261027-0607-proof-complexity».P5Main

open Programme.«20261025-0459-proof-complexity».OntoFPHP (ontoFPHP PPCRefutation)
open Programme.«20261026-1402-proof-complexity».ExtLemma (Bal)
open Programme.«20261027-0607-proof-complexity».Peel (IsPrime)

theorem look0 : Programme.«20261027-0607-proof-complexity».P5.look 0 = 1 := by decide +kernel

/-- A unit degree-5 design for `ontoFPHP 9 25` over `Z/5`. -/
theorem design_exists : ∃ E : List Nat → Int, E [] = 1 ∧ ∀ e ≤ 4, Bal 5 9 25 E E e :=
  ⟨Programme.«20261027-0607-proof-complexity».P5.T, by simp [Programme.«20261027-0607-proof-complexity».P5.T, Programme.«20261027-0607-proof-complexity».P5.hkey, look0],
    fun e he => Programme.«20261027-0607-proof-complexity».P5.bal_of_enum Programme.«20261027-0607-proof-complexity».P5.enum_all e he⟩

theorem prime5 : IsPrime 5 := ⟨by decide, fun a ha => by
  have := Nat.le_of_dvd (by decide) ha
  rcases (show a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 by omega) with h | h | h | h | h | h <;>
    subst h <;> simp_all <;> omega⟩

/-- **For every `n ≥ 9`, onto-FPHP with `n + 25` pigeons and `n` holes (functional encoding) has no
degree-5 polynomial calculus refutation over `Z/5`.** -/
theorem no_deg5_k25 (n : Nat) (hn : 9 ≤ n) : ¬ PPCRefutation 5 (ontoFPHP n 25) 5 := by
  obtain ⟨E, h1, hE⟩ := design_exists
  exact Programme.«20261027-0607-proof-complexity».PeelV.no_deg_p_of_design prime5 (by decide) (by decide) (fun e he => hE e (by omega))
    (by rw [h1]; decide) n hn

end Programme.«20261027-0607-proof-complexity».P5Main

#print axioms Programme.«20261027-0607-proof-complexity».P5Main.design_exists
#print axioms Programme.«20261027-0607-proof-complexity».P5Main.no_deg5_k25
