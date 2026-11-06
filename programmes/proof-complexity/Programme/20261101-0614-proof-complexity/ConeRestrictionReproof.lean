import Programme.«20261101-0614-proof-complexity».ConeRestriction

namespace Programme.«20261101-0614-proof-complexity».ConeRestrictionReproof
open Programme.«20261031-2024-proof-complexity».NativeIter
open Programme.«20261101-0614-proof-complexity».ConeRestriction hiding word

/-- Own combined fact about the restricted Peer.pr.ConeRestriction.word: length bound and evaluation. -/
theorem word_facts (ρ : Substitution) (m : List Lit) :
    (∀ q, Programme.«20261101-0614-proof-complexity».ConeRestriction.word ρ m = some q → q.length ≤ m.length) ∧
    (∀ a, conjunction m (assignment ρ a) =
      (Programme.«20261101-0614-proof-complexity».ConeRestriction.word ρ m).elim 0 (fun q => conjunction q a)) := by
  induction m with
  | nil => exact ⟨by intro q h; simp [Programme.«20261101-0614-proof-complexity».ConeRestriction.word] at h; subst h; simp, by intro a; simp [Programme.«20261101-0614-proof-complexity».ConeRestriction.word, conjunction]⟩
  | cons l ls ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rcases hs : ρ l.1 with b | v
    · by_cases hb : b = l.2
      · refine ⟨fun q h => ?_, fun a => ?_⟩
        · simp [Programme.«20261101-0614-proof-complexity».ConeRestriction.word, hs, hb] at h; have := ih1 q h; simp; omega
        · rw [show conjunction (l :: ls) (assignment ρ a) = conjunction [l] (assignment ρ a) * conjunction ls (assignment ρ a) from conjunction_mul [l] ls _, ih2]
          simp [Programme.«20261101-0614-proof-complexity».ConeRestriction.word, hs, hb, conjunction, holds, assignment]
      · refine ⟨fun q h => ?_, fun a => ?_⟩
        · simp [Programme.«20261101-0614-proof-complexity».ConeRestriction.word, hs, hb] at h
        · rw [show conjunction (l :: ls) (assignment ρ a) = conjunction [l] (assignment ρ a) * conjunction ls (assignment ρ a) from conjunction_mul [l] ls _, ih2]
          simp [Programme.«20261101-0614-proof-complexity».ConeRestriction.word, hs, hb, conjunction, holds, assignment]
    · refine ⟨fun q h => ?_, fun a => ?_⟩
      · simp only [Programme.«20261101-0614-proof-complexity».ConeRestriction.word, hs] at h
        cases ht : Programme.«20261101-0614-proof-complexity».ConeRestriction.word ρ ls with
        | none => simp [ht] at h
        | some t =>
          simp [ht] at h; subst h; have := ih1 t ht; simp; omega
      · rw [show conjunction (l :: ls) (assignment ρ a) = conjunction [l] (assignment ρ a) * conjunction ls (assignment ρ a) from conjunction_mul [l] ls _, ih2]
        cases ht : Programme.«20261101-0614-proof-complexity».ConeRestriction.word ρ ls with
        | none => simp [Programme.«20261101-0614-proof-complexity».ConeRestriction.word, hs, ht]
        | some t =>
          simp only [Programme.«20261101-0614-proof-complexity».ConeRestriction.word, hs, ht, Option.map_some, Option.elim_some]
          rw [show (v, l.2) :: t = [(v, l.2)] ++ t from rfl, conjunction_mul]
          simp [conjunction, holds, assignment, hs]

theorem zero_mult {F d} (ρ : Substitution) (r : Rat) (x y : List Lit)
    (h : ∀ a, conjunction x (assignment ρ a) = 0) :
    Cone F d (fun a => r * conjunction (x ++ y) (assignment ρ a)) := by
  have : (fun a => r * conjunction (x ++ y) (assignment ρ a)) = fun _ => 0 := by
    funext a; rw [conjunction_mul, h]; simp
  rw [this]; exact Cone.zero

theorem zero_mult' {F d} (ρ : Substitution) (r : Rat) (x y : List Lit)
    (h : ∀ a, conjunction y (assignment ρ a) = 0) :
    Cone F d (fun a => r * conjunction (x ++ y) (assignment ρ a)) := by
  have : (fun a => r * conjunction (x ++ y) (assignment ρ a)) = fun _ => 0 := by
    funext a; rw [conjunction_mul, h]; simp
  rw [this]; exact Cone.zero

theorem cone' {ρ : Substitution} {F G d} (cl : Clauses ρ F G)
    {f} (hf : Cone F d f) : Cone G d (fun a => f (assignment ρ a)) := by
  induction hf with
  | positive m _ hd =>
    have ⟨h1, h2⟩ := word_facts ρ m
    have : (fun a => conjunction m (assignment ρ a)) =
        fun a => (Programme.«20261101-0614-proof-complexity».ConeRestriction.word ρ m).elim 0 (fun q => conjunction q a) := funext h2
    rw [this]
    cases hw : Programme.«20261101-0614-proof-complexity».ConeRestriction.word ρ m with
    | none => exact Cone.zero
    | some q => exact positive_cell q (Nat.le_trans (h1 q hw) hd)
  | equation c m r hc hd =>
    have ⟨h1, h2⟩ := word_facts ρ m
    have ⟨h3, h4⟩ := word_facts ρ (falsity c)
    rcases cl c hc with hz | ⟨e, he, ht, hl⟩
    · exact zero_mult' ρ r _ _ (fun a => by rw [h4 a, hz]; rfl)
    · cases hw : Programme.«20261101-0614-proof-complexity».ConeRestriction.word ρ m with
      | none => exact zero_mult ρ r _ _ (fun a => by rw [h2 a, hw]; rfl)
      | some q =>
        have : (fun a => r * conjunction (m ++ falsity c) (assignment ρ a)) =
            fun a => r * conjunction (q ++ falsity e) a := by
          funext a
          rw [conjunction_mul, conjunction_mul, h2 a, h4 a, hw, ht]; rfl
        rw [this]
        have := h1 q hw
        have := hd.2
        exact equation_cell e q r he (by omega)
  | zero => exact Cone.zero
  | add _ _ ih jh => exact Cone.add ih jh
  | scale r hr _ ih => exact Cone.scale r hr ih

theorem refutes {ρ : Substitution} {F G d} (cl : Clauses ρ F G)
    (hf : Refutes F d) : Refutes G d := cone' cl hf

#print axioms refutes
end Programme.«20261101-0614-proof-complexity».ConeRestrictionReproof
