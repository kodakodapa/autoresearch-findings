import Work.ExactReproof
namespace Work.SeparationReproof
open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Peer.th.Peel (IsPrime)
theorem bridge {p q c : Nat} (hp : IsPrime p) (hq : IsPrime q)
    (hc : ¬ p ∣ c) (hqk : ¬ q ∣ p*c) (n : Nat) (hn : 2*p-3 ≤ n) :
    (∀ D, PPCRefutation p (ontoFPHP n (p*c)) D ↔ p ≤ D) ∧
      PPCRefutation q (ontoFPHP n (p*c)) 1 := by
  refine ⟨fun D => Work.ExactReproof.bridge hp hc n hn D, ?_⟩
  have hg : Nat.gcd (p*c) q = 1 := by
    rcases hq.2 _ (Nat.gcd_dvd_right (p*c) q) with h | h
    · exact h
    · exact False.elim (hqk (h ▸ Nat.gcd_dvd_left (p*c) q))
  obtain ⟨a,b,hab⟩ := Peer.th.Peel.bezout (p*c) q
  rw [hg] at hab
  have hu : ∃ u : Int, (q : Int) ∣ u * (p*c : Nat) - 1 := by
    refine ⟨a, -b, ?_⟩
    rw [Int.mul_neg, Int.mul_comm (q : Int) b]
    push_cast at hab ⊢
    omega
  have hcpos : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · exact False.elim (hc (h ▸ Nat.dvd_zero p))
    · exact h
  exact ontoFPHP_deg1 q n (p*c)
    (Nat.mul_pos (by have := hp.1; omega) hcpos) hu
example : type_of% @bridge = type_of% @Work.Lucas.separation := rfl
end Work.SeparationReproof
#print axioms Work.SeparationReproof.bridge
