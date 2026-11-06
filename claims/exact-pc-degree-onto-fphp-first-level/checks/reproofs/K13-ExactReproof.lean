import Work.Alias
import Peer.th.Lucas
import Work.LowerReproof
namespace Work.ExactReproof
open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-0459-proof-complexity».OntoPCLower
open Programme.«20261025-0459-proof-complexity».OntoLucas
open Peer.th.Peel (IsPrime)

theorem bridge {p c : Nat} (hp : IsPrime p) (hc : ¬ p ∣ c) (n : Nat)
    (hn : 2*p-3 ≤ n) (D : Nat) :
    PPCRefutation p (ontoFPHP n (p*c)) D ↔ p ≤ D := by
  by_cases h : p ≤ D
  · have upper : PPCRefutation p (ontoFPHP n (p*c)) p :=
      ontoFPHP_upper p n (p*c) p hp.1 (by have := hp.1; omega)
        (Peer.th.Lucas.unit_c hp hc n)
    exact ⟨fun _ => h, fun _ => PPCDerivable.mono h upper⟩
  · have low := Work.LowerReproof.bridge hp (show p ∣ p*c from ⟨c, rfl⟩) n hn
    have no : ¬ PPCRefutation p (ontoFPHP n (p*c)) D :=
      fun ref => low (PPCDerivable.mono (by omega) ref)
    exact ⟨fun ref => False.elim (no ref), fun hpD => False.elim (h hpD)⟩

example : type_of% @bridge = type_of% @Peer.th.Lucas.pc_degree_exact := rfl
end Work.ExactReproof
#print axioms Work.ExactReproof.bridge

example : type_of% @Work.ExactReproof.bridge = type_of% @Work.Lucas.pc_degree_exact := rfl
