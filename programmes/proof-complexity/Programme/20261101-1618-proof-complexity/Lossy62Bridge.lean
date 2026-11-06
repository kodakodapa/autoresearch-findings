import Programme.«20261101-1618-proof-complexity».Lossy62Check0
import Programme.«20261101-1618-proof-complexity».Lossy62Check1
import Programme.«20261101-1618-proof-complexity».Lossy62Check2
import Programme.«20261101-1618-proof-complexity».Lossy62Check3
import Programme.«20261101-1618-proof-complexity».Lossy62Check4
import Programme.«20261101-1618-proof-complexity».Lossy62Check5
import Programme.«20261101-1618-proof-complexity».Lossy62Check6
import Programme.«20261101-1618-proof-complexity».Lossy62Check7
import Programme.«20261101-1618-proof-complexity».Lossy62Check8
import Programme.«20261101-1618-proof-complexity».Lossy62Check9
import Programme.«20261101-1618-proof-complexity».Lossy62Check10
import Programme.«20261101-1618-proof-complexity».Lossy62Check11
import Programme.«20261101-1618-proof-complexity».Lossy62Check12
import Programme.«20261101-1618-proof-complexity».Lossy62Check13
import Programme.«20261101-1618-proof-complexity».Lossy62Check14
import Programme.«20261101-1618-proof-complexity».Lossy62Check15
import Programme.«20261101-1618-proof-complexity».Lossy62Check16
import Programme.«20261101-1618-proof-complexity».Lossy62Check17
import Programme.«20261101-1618-proof-complexity».Lossy62Check18
import Programme.«20261101-1618-proof-complexity».Lossy62Check19
import Programme.«20261101-1618-proof-complexity».Lossy62Check20
import Programme.«20261101-1618-proof-complexity».Lossy62Check21
import Programme.«20261101-1618-proof-complexity».Lossy62Check22
import Programme.«20261101-1618-proof-complexity».Lossy62Check23
import Programme.«20261101-1618-proof-complexity».Lossy62Check24
namespace Programme.«20261101-1618-proof-complexity».Lossy62Bridge
open Programme.«20261101-1618-proof-complexity».Lossy62Data
abbrev translated := Programme.«20261101-1618-proof-complexity».Lossy62Data.translated
theorem forward : covered translated source = true := by
  change covered Programme.«20261101-1618-proof-complexity».Lossy62Data.translated source = true
  rw [tparts]
  simp only [covered, List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨Programme.«20261101-1618-proof-complexity».Lossy62Check0.forward, Programme.«20261101-1618-proof-complexity».Lossy62Check1.forward⟩, Programme.«20261101-1618-proof-complexity».Lossy62Check2.forward⟩, Programme.«20261101-1618-proof-complexity».Lossy62Check3.forward⟩, Programme.«20261101-1618-proof-complexity».Lossy62Check4.forward⟩, Programme.«20261101-1618-proof-complexity».Lossy62Check5.forward⟩, Programme.«20261101-1618-proof-complexity».Lossy62Check6.forward⟩, Programme.«20261101-1618-proof-complexity».Lossy62Check7.forward⟩, Programme.«20261101-1618-proof-complexity».Lossy62Check8.forward⟩, Programme.«20261101-1618-proof-complexity».Lossy62Check9.forward⟩, Programme.«20261101-1618-proof-complexity».Lossy62Check10.forward⟩, Programme.«20261101-1618-proof-complexity».Lossy62Check11.forward⟩, Programme.«20261101-1618-proof-complexity».Lossy62Check12.forward⟩, Programme.«20261101-1618-proof-complexity».Lossy62Check13.forward⟩, Programme.«20261101-1618-proof-complexity».Lossy62Check14.forward⟩, Programme.«20261101-1618-proof-complexity».Lossy62Check15.forward⟩, Programme.«20261101-1618-proof-complexity».Lossy62Check16.forward⟩, Programme.«20261101-1618-proof-complexity».Lossy62Check17.forward⟩, Programme.«20261101-1618-proof-complexity».Lossy62Check18.forward⟩, Programme.«20261101-1618-proof-complexity».Lossy62Check19.forward⟩
theorem backward : covered source translated = true := by
  rw [sparts]
  simp only [covered, List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨Programme.«20261101-1618-proof-complexity».Lossy62Check0.backward, Programme.«20261101-1618-proof-complexity».Lossy62Check1.backward⟩, Programme.«20261101-1618-proof-complexity».Lossy62Check2.backward⟩, Programme.«20261101-1618-proof-complexity».Lossy62Check3.backward⟩, Programme.«20261101-1618-proof-complexity».Lossy62Check4.backward⟩, Programme.«20261101-1618-proof-complexity».Lossy62Check5.backward⟩, Programme.«20261101-1618-proof-complexity».Lossy62Check6.backward⟩, Programme.«20261101-1618-proof-complexity».Lossy62Check7.backward⟩, Programme.«20261101-1618-proof-complexity».Lossy62Check8.backward⟩, Programme.«20261101-1618-proof-complexity».Lossy62Check9.backward⟩, Programme.«20261101-1618-proof-complexity».Lossy62Check10.backward⟩, Programme.«20261101-1618-proof-complexity».Lossy62Check11.backward⟩, Programme.«20261101-1618-proof-complexity».Lossy62Check12.backward⟩, Programme.«20261101-1618-proof-complexity».Lossy62Check13.backward⟩, Programme.«20261101-1618-proof-complexity».Lossy62Check14.backward⟩, Programme.«20261101-1618-proof-complexity».Lossy62Check15.backward⟩, Programme.«20261101-1618-proof-complexity».Lossy62Check16.backward⟩, Programme.«20261101-1618-proof-complexity».Lossy62Check17.backward⟩, Programme.«20261101-1618-proof-complexity».Lossy62Check18.backward⟩, Programme.«20261101-1618-proof-complexity».Lossy62Check19.backward⟩, Programme.«20261101-1618-proof-complexity».Lossy62Check20.backward⟩, Programme.«20261101-1618-proof-complexity».Lossy62Check21.backward⟩, Programme.«20261101-1618-proof-complexity».Lossy62Check22.backward⟩, Programme.«20261101-1618-proof-complexity».Lossy62Check23.backward⟩, Programme.«20261101-1618-proof-complexity».Lossy62Check24.backward⟩
theorem equivalent (d : Nat) :
    Programme.«20261101-1618-proof-complexity».ClauseLinear.Refutes translated d ↔
    Programme.«20261101-1618-proof-complexity».ClauseLinear.Refutes (Programme.«20261101-1618-proof-complexity».LossySource.cnf 3 6 2) d :=
  Programme.«20261101-1618-proof-complexity».LossyPresentation.refutes_reverse_coverage
    (covered_sound forward) (covered_sound backward)
#print axioms equivalent
end Programme.«20261101-1618-proof-complexity».Lossy62Bridge
