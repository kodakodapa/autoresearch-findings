import Programme.«20261027-1434-proof-complexity».Peel3
import Programme.«20261027-1434-proof-complexity».Ext278c

/-!
# The `l = 3` step over `Z/2` from a run of the level-3 checker

`Peel3.run3` is a kernel-evaluable checker of level-3 zero-link peeling certificates over th's RRR
and `T ⊗ R` generators (`Gen3`, `Gen3T`). A successful run from the empty mask that finalises
every canonical 3-matching (`covA`) proves that every zero-link function on 3-matchings is a level-3
span of self-balanced generators, hence `EXT 2 7 8 3` (`Ext278c.ext3_of_z3`), hence that
`ontoFPHP n 8` has no degree-4 `PPCRefutation 2` for every `n ≥ 7` (`Ext278b.hard_of_ext3`).
-/

namespace Programme.«20261027-1434-proof-complexity».Ext278d

open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261026-1402-proof-complexity».ExtLemma
open Programme.«20261026-1402-proof-complexity».ExtLin
open Programme.«20261027-1434-proof-complexity».Peel3

theorem g3_sb3 (g : List Nat → Int) (hg : G3 g) : InSpan 2 7 8 3 Programme.«20261027-1434-proof-complexity».Ext278c.SB3 g := by
  obtain ⟨x, hv, rfl⟩ := hg
  exact InSpan.gen (GS.bal x hv 3 (by omega))

/-- The parametric level-3 generators: self-balanced at every level `e ≤ 3`, and on canonical
3-matchings equal to the number of occurrences of the code in their explicit support list. -/
theorem gen3_spec (x : GS) (hv : x.valid = true) :
    (∀ e ≤ 3, Bal 2 7 8 x.fn x.fn e) ∧
      ∀ m, CM 7 8 m → m.length = 3 → x.fn m = ((x.supp.count (Programme.«20261027-1434-proof-complexity».Code3.code3 m) : Nat) : Int) :=
  ⟨fun e he => GS.bal x hv e he, fun m hm hl => GS.count x hv hm hl⟩

/-- Every zero-link function is a level-3 span of self-balanced functions, from a checked run. -/
theorem z3_of_run (ss : List Step3) (P : Nat) (hr : run3 0 ss = some P) (hc : ∀ a < 105, covA P a = true)
    (z : List Nat → Int) (hz : Bal 2 7 8 z (fun _ => 0) 2) : InSpan 2 7 8 3 Programme.«20261027-1434-proof-complexity».Ext278c.SB3 z :=
  Programme.«20261027-1434-proof-complexity».Ext278c.span_mono g3_sb3 (span_of_cov (run3_sound ss hr (state_init z hz)) hc)

/-- **The `l = 3` step from a checked level-3 certificate run.** -/
theorem hard_of_run (ss : List Step3) (P : Nat) (hr : run3 0 ss = some P) (hc : ∀ a < 105, covA P a = true)
    (n : Nat) (hn : 7 ≤ n) : ¬ PPCRefutation 2 (ontoFPHP n 8) 4 :=
  Programme.«20261027-1434-proof-complexity».Ext278c.hard_of_z3 (z3_of_run ss P hr hc) n hn

end Programme.«20261027-1434-proof-complexity».Ext278d

#print axioms Programme.«20261027-1434-proof-complexity».Ext278d.hard_of_run
#print axioms Programme.«20261027-1434-proof-complexity».Ext278d.gen3_spec
