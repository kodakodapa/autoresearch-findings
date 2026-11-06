import Programme.«20261104-1627-proof-complexity».MatchingReduction

namespace Programme.«20261104-1627-proof-complexity».ReducedCertificates
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261025-0459-proof-complexity».MatchQuot
open Programme.«20261025-1627-proof-complexity».NoDrop
open Programme.«20261104-1627-proof-complexity».MatchingReduction

/-- Canonical NS certificates can have all multiplier supports reduced independently. -/
theorem reduced_certificate_iff (p D : Nat) (A : List (Poly Nat))
    (f : (Nat → Bool) → Int) :
    NSIn p A D f ↔
      ∃ L : List (Poly Nat × Poly Nat),
        (∀ e ∈ L, e.2 ∈ A ∧ e.1.deg + e.2.deg ≤ D ∧
          ∀ t ∈ e.1.terms, t.2.Nodup ∧ Safe A t.2) ∧
        ∀ a, Good A a →
          (p : Int) ∣ (L.map fun e => e.1.eval a * e.2.eval a).sum - f a := by
  constructor
  · rintro ⟨L, hL, heval⟩
    refine ⟨L.map (fun e => (reduce A e.1, e.2)), ?_, ?_⟩
    · intro e he
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp he
      have h := hL b hb
      exact ⟨h.1, Nat.le_trans (Nat.add_le_add_right (deg_reduce A b.1) _) h.2,
        support_reduce A b.1⟩
    · intro a ha
      have eq : ((L.map fun e => (reduce A e.1, e.2)).map
          fun e => e.1.eval a * e.2.eval a).sum =
          (L.map fun e => e.1.eval a * e.2.eval a).sum := by
        rw [List.map_map]
        congr 1
        apply List.map_congr_left
        intro e _
        exact congrArg (fun z : Int => z * e.2.eval a) (eval_reduce A e.1 a ha)
      rw [eq]
      exact heval a ha
  · rintro ⟨L, hL, heval⟩
    exact ⟨L, fun e he => ⟨(hL e he).1, (hL e he).2.1⟩, heval⟩

end Programme.«20261104-1627-proof-complexity».ReducedCertificates
#print axioms Programme.«20261104-1627-proof-complexity».ReducedCertificates.reduced_certificate_iff
