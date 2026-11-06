import Programme.«20261101-0614-proof-complexity».RestrictionTarget
import Programme.«20261101-0614-proof-complexity».ConeRestriction

namespace Programme.«20261101-0614-proof-complexity».«th-split».RestrictionBridge
open Programme.«20261031-2024-proof-complexity».NativeIter
open Programme.«20261101-0614-proof-complexity».RestrictionTarget

theorem clause_word (ρ : Substitution) (c : Clause) :
    Programme.«20261101-0614-proof-complexity».ConeRestriction.word ρ (falsity c) =
      (clause ρ c).map falsity := by
  induction c with
  | nil => rfl
  | cons l c ih =>
    cases l with
    | mk v s =>
      cases hs : ρ v with
      | inl b =>
        cases b <;> cases s <;>
          simp_all [clause, literal, falsity, neg, Programme.«20261101-0614-proof-complexity».ConeRestriction.word]
      | inr w =>
        simp only [clause, literal, hs, falsity, List.map_cons,
          Programme.«20261101-0614-proof-complexity».ConeRestriction.word, neg] at *
        rw [ih]
        cases clause ρ c <;> rfl

theorem clause_length (ρ : Substitution) (c t : Clause)
    (h : clause ρ c = some t) : t.length ≤ c.length := by
  have hw : Programme.«20261101-0614-proof-complexity».ConeRestriction.word ρ (falsity c) = some (falsity t) := by
    rw [clause_word, h]; rfl
  simpa [falsity] using Programme.«20261101-0614-proof-complexity».ConeRestriction.word_length ρ _ _ hw

theorem transport : TransportPrinciple := by
  intro ρ F G d h hf
  apply Programme.«20261101-0614-proof-complexity».ConeRestriction.refutes (ρ := ρ) (F := F) (G := G) ?_ hf
  intro c hc
  cases ht : clause ρ c with
  | none =>
    left
    rw [clause_word, ht]; rfl
  | some t =>
    right
    refine ⟨t, h c hc t ht, ?_, clause_length ρ c t ht⟩
    rw [clause_word, ht]; rfl

#print axioms transport
end Programme.«20261101-0614-proof-complexity».«th-split».RestrictionBridge
