import Programme.«20261030-0634-proof-complexity».P3Table
import Programme.«20261030-0634-proof-complexity».FactorUnit
import Programme.«20261027-0607-proof-complexity».K7Reproof
namespace Programme.«20261030-0634-proof-complexity».P3Top
open Programme.«20261030-0634-proof-complexity».P3Table
open Programme.«20261026-1402-proof-complexity».ExtLemma
open Programme.«20261025-1627-proof-complexity».OntoExt2 (var_lt)
open Programme.«20261027-0607-proof-complexity».Peel (IsPrime)
open Programme.«20261025-0459-proof-complexity».OntoFPHP (ontoFPHP)
open Programme.«20261025-0459-proof-complexity».OntoFPHP (PPCRefutation)
theorem top_of_checks (checks : ∀ a b : Fin 70, Check a b) : Bal 3 5 9 U (fun _ => -1) 2 := by
  intro g hg hl
  obtain ⟨a,b,rfl⟩ : ∃ a b, g = [a,b] := by
    match g, hl with
    | [a,b], _ => exact ⟨a,b,rfl⟩
  have ha : a < 70 := CM_lt hg (by simp)
  have hb : b < 70 := CM_lt hg (by simp)
  have hne : a ≠ b := (List.nodup_cons.mp (CM_nodup hg)).1 ∘ (by intro h; simpa using h)
  obtain ⟨hr,hc⟩ := checks ⟨a,ha⟩ ⟨b,hb⟩ hne hg.2
  constructor
  · intro i hi hf
    change (3 : Int) ∣ rowS 5 9 U [a,b] i + 1
    unfold rowS
    rw [raw_line _ hg _ _ (fun j hj => var_lt 5 9 i j hi hj) (notin_of_pfree hf)]
    exact hr ⟨i,hi⟩ hf
  · intro j hj hf
    change (3 : Int) ∣ colS 5 9 U [a,b] j + 1
    unfold colS
    rw [raw_line _ hg _ _ (fun i hi => var_lt 5 9 i j hi hj)
      (fun i _ => notin_of_hfree hf i hj)]
    exact hc ⟨j,hj⟩ hf

#print axioms top_of_checks
end Programme.«20261030-0634-proof-complexity».P3Top
