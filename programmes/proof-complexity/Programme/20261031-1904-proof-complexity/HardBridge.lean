import Programme.«20261029-1156-proof-complexity».StdPCCor
import Programme.«20261029-1156-proof-complexity».StdPCConv

namespace Programme.«20261031-1904-proof-complexity».HardBridge
open Programme.«20261029-1156-proof-complexity».StdPCCor
open Programme.«20261029-1156-proof-complexity».StdPCConv
open Programme.«20261025-1627-proof-complexity».OntoQ7

theorem shard_iff_hard {p l D : Nat} (hp : 1 < p) :
    SHard p l D ↔ Hard p l D := by
  constructor
  · rintro ⟨N, hN⟩
    exact ⟨N, fun n hn h => hN n hn ((refutes_iff hp).mpr h)⟩
  · exact shard_of_hard hp

theorem std_q7_iff {p : Nat} (hp : 1 < p) :
    (∀ D, ∃ l, SHard p l D) ↔ Q7 p := by
  unfold Q7
  simp only [shard_iff_hard hp]
end Programme.«20261031-1904-proof-complexity».HardBridge

#print axioms Programme.«20261031-1904-proof-complexity».HardBridge.shard_iff_hard
#print axioms Programme.«20261031-1904-proof-complexity».HardBridge.std_q7_iff
