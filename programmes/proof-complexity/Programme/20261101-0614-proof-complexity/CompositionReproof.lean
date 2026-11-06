import Programme.«20261101-0614-proof-complexity».BridgeReproof
import Programme.«20261101-0614-proof-complexity».CompositionTransport

namespace Programme.«20261101-0614-proof-complexity».CompositionReproof
open Programme.«20261031-2024-proof-complexity».NativeIter
open Programme.«20261101-0614-proof-complexity».RestrictionTarget
open Programme.«20261101-0614-proof-complexity».Composition

-- Reassemble transport from the checked local residual identities and our own
-- clause-product substitution bridge, without either author transport theorem.
theorem transport (ρ : Substitution) (M N L d : Nat)
    (hs : RestrictionSpec ρ M N) (hM : 1 ≤ M)
    (hstruct : ∀ c ∈ structural (M+1) (N+1) L,
      ∀ t, clause ρ c = some t → t ∈ cnf M N L)
    (hf : Refutes (cnf (M+1) (N+1) L) d) : Refutes (cnf M N L) d := by
  apply Programme.«20261101-0614-proof-complexity».BridgeReproof.transport ρ _ _ d ?_ hf
  intro c hc t ht
  have residual := event_residuals ρ M N L hs hM
  simp only [Programme.«20261101-0614-proof-complexity».Composition.cnf, List.mem_eraseDups, List.mem_append] at hc ⊢
  rcases hc with hc | hc
  · have mem : c ∈ structural (M+1) (N+1) L := by
      simpa only [structural, List.mem_append] using hc
    have result := hstruct c mem t ht
    simpa only [Programme.«20261101-0614-proof-complexity».Composition.cnf, List.mem_eraseDups, List.mem_append] using result
  · rcases List.mem_flatMap.mp hc with ⟨y,hy,hc⟩
    rcases List.mem_flatMap.mp hc with ⟨⟨x,e⟩,he,hc⟩
    rcases List.mem_map.mp hc with ⟨a,ha,rfl⟩
    have hy' := List.mem_range.mp hy
    have ha' := List.mem_range.mp ha
    have yn : y < N := by
      by_cases hn : y < N
      · exact hn
      have : y = N := by omega
      subst y
      rw [residual.1 x a e] at ht
      contradiction
    have am : a < M := by
      by_cases hn : a < M
      · exact hn
      have : a = M := by omega
      subst a
      rw [residual.2.1 y x e yn] at ht
      contradiction
    rw [residual.2.2 y x a e am yn he] at ht
    cases ht
    right
    exact List.mem_flatMap.mpr ⟨y,List.mem_range.mpr yn,
      List.mem_flatMap.mpr ⟨(x,e),he,List.mem_map.mpr ⟨a,List.mem_range.mpr am,rfl⟩⟩⟩

#print axioms transport
end Programme.«20261101-0614-proof-complexity».CompositionReproof
