import Programme.«20261101-0614-proof-complexity».ConeRestriction
import Programme.«20261101-0614-proof-complexity».RestrictionTarget

namespace Programme.«20261101-0614-proof-complexity».«pr-split».RestrictionBridge
open Programme.«20261031-2024-proof-complexity».NativeIter
open Programme.«20261101-0614-proof-complexity».RestrictionTarget

 theorem clause_length (ρ : Substitution) (c t : Clause)
    (h : clause ρ c = some t) : t.length ≤ c.length := by
  induction c generalizing t with
  | nil => simp [clause] at h; subst t; simp
  | cons l c ih =>
    simp only [clause] at h
    cases hl : literal ρ l with
    | inl b =>
      cases b with
      | false => simp only [hl] at h; have := ih t h; simp; omega
      | true => simp [hl] at h
    | inr k =>
      simp only [hl] at h
      cases hc : clause ρ c with
      | none => simp [hc] at h
      | some s =>
        simp only [hc, Option.map_some, Option.some.injEq] at h
        subst t
        have := ih s hc
        simp; omega

 theorem clause_word (ρ : Substitution) (c : Clause) :
    ConeRestriction.word ρ (falsity c) = (clause ρ c).map falsity := by
  induction c with
  | nil => rfl
  | cons l c ih =>
    rcases l with ⟨v,b⟩
    cases hs : ρ v with
    | inl a =>
      cases a <;> cases b <;>
        simp_all [falsity, neg, ConeRestriction.word, clause, literal]
    | inr w =>
      change ConeRestriction.word ρ ((v, !b) :: falsity c) = _
      simp only [ConeRestriction.word, hs, clause, literal]
      rw [ih]
      cases clause ρ c <;> rfl

 theorem transport : TransportPrinciple := by
  intro ρ F G d h hf
  apply ConeRestriction.refutes (ρ := ρ) (F := F) (G := G) (d := d) ?_ hf
  intro c hc
  rw [clause_word]
  cases ht : clause ρ c with
  | none => exact Or.inl rfl
  | some t =>
    exact Or.inr ⟨t, h c hc t ht, rfl, clause_length ρ c t ht⟩

#print axioms transport
end Programme.«20261101-0614-proof-complexity».«pr-split».RestrictionBridge
