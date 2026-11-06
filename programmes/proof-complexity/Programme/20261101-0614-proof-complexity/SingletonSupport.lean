import Programme.«20261101-0614-proof-complexity».SingletonData

namespace Programme.«20261101-0614-proof-complexity».SingletonSupport
open Programme.«20261031-2024-proof-complexity».NativeIter
open Programme.«20261101-0614-proof-complexity».SingletonData Programme.«20261101-0614-proof-complexity».SignedDual
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem point_supported (mask : Nat) (v : Var) (hv : v ∉ vars) : point mask v = false := by
  rcases v with ⟨x,y⟩
  by_cases h0 : x = 0
  · subst x
    have hy : ¬ y < 2 := by
      simp [vars] at hv
      omega
    simp [point, hy]
  · by_cases h1 : x = 1
    · subst x
      have hy : ¬ y < 9 := by
        simp [vars] at hv
        omega
      simp [point, hy]
    · by_cases h2 : x = 2
      · subst x
        have hy : ¬ y < 9 := by
          simp [vars] at hv
          omega
        simp [point, hy]
      · have hx : ¬ x ≤ 2 := by omega
        simp [point, h0, hx]

theorem supported : Supported vars samples := by
  intro s hs v hv
  obtain ⟨⟨w,mask⟩,_,rfl⟩ := List.mem_map.mp hs
  exact point_supported mask v hv

theorem normalized : evaluate samples (fun _ => 1) = 1 := by
  change evaluate samples (conjunction []) = 1
  rw [samples, eval_score]
  decide +kernel

theorem cnf_supported : ∀ c ∈ Singleton.cnf 2 3, ∀ l ∈ c, l.1 ∈ vars := by
  decide +kernel

#print axioms normalized
#print axioms supported
#print axioms cnf_supported
end Programme.«20261101-0614-proof-complexity».SingletonSupport
