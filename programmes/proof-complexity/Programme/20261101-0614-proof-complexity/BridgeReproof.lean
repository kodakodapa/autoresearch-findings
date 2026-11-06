import Programme.«20261101-0614-proof-complexity».ConeRestrictionReproof
import Programme.«20261101-0614-proof-complexity».RestrictionTarget

namespace Programme.«20261101-0614-proof-complexity».BridgeReproof
open Programme.«20261031-2024-proof-complexity».NativeIter
open Programme.«20261101-0614-proof-complexity».RestrictionTarget

-- Independent syntactic bridge; length is obtained from the separately reproved word facts.
theorem commute (ρ : Substitution) (c : Clause) :
    Programme.«20261101-0614-proof-complexity».ConeRestriction.word ρ (falsity c) = (clause ρ c).map falsity := by
  induction c with
  | nil => rfl
  | cons l ls ih =>
    obtain ⟨v,b⟩ := l
    cases hv : ρ v with
    | inl a =>
      cases a <;> cases b <;>
        simp_all [clause, literal, falsity, neg, Programme.«20261101-0614-proof-complexity».ConeRestriction.word]
    | inr w =>
      simp only [clause, literal, hv, falsity, List.map_cons, neg,
        Programme.«20261101-0614-proof-complexity».ConeRestriction.word]
      change Option.map (fun x => (w, !b) :: x) (Programme.«20261101-0614-proof-complexity».ConeRestriction.word ρ (falsity ls)) = _
      rw [ih]
      cases clause ρ ls <;> rfl

theorem transport : TransportPrinciple := by
  intro ρ F G d clauses proof
  apply Programme.«20261101-0614-proof-complexity».ConeRestrictionReproof.refutes (ρ := ρ) (F := F) (G := G) (d := d) ?_ proof
  intro c hc
  cases ht : clause ρ c with
  | none =>
    left
    rw [commute, ht]
    rfl
  | some t =>
    right
    have hw : Programme.«20261101-0614-proof-complexity».ConeRestriction.word ρ (falsity c) = some (falsity t) := by
      rw [commute, ht]; rfl
    refine ⟨t, clauses c hc t ht, hw, ?_⟩
    have hlen := (Programme.«20261101-0614-proof-complexity».ConeRestrictionReproof.word_facts ρ (falsity c)).1 (falsity t) hw
    simpa [falsity] using hlen

#print axioms transport
end Programme.«20261101-0614-proof-complexity».BridgeReproof
