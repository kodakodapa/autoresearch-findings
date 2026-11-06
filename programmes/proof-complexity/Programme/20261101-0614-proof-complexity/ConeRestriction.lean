import Programme.«20261031-2024-proof-complexity».ConeIdentify

namespace Programme.«20261101-0614-proof-complexity».ConeRestriction
open Programme.«20261031-2024-proof-complexity».NativeIter

/-- A source variable is fixed to a Boolean or mapped to a target variable. -/
abbrev Substitution := Var → Bool ⊕ Var

def assignment (ρ : Substitution) (a : Assignment) (v : Var) : Bool :=
  match ρ v with
  | .inl b => b
  | .inr w => a w

/-- Restrict a literal product: `none` denotes the zero function. -/
def word (ρ : Substitution) : List Lit → Option (List Lit)
  | [] => some []
  | l :: ls => match ρ l.1 with
    | .inl b => if b = l.2 then word ρ ls else none
    | .inr v => (word ρ ls).map ((v,l.2) :: ·)

theorem word_length (ρ : Substitution) (m q : List Lit)
    (h : word ρ m = some q) : q.length ≤ m.length := by
  induction m generalizing q with
  | nil => simp [word] at h; subst q; simp
  | cons l ls ih =>
    simp only [word] at h
    cases hs : ρ l.1 with
    | inl b =>
      simp only [hs] at h
      split at h
      · have := ih q h; simp; omega
      · contradiction
    | inr v =>
      simp only [hs] at h
      cases ht : word ρ ls with
      | none => simp [ht] at h
      | some t =>
        simp only [ht, Option.map_some, Option.some.injEq] at h
        subst q
        have := ih t ht
        simp; omega

theorem word_eval (ρ : Substitution) (m : List Lit) (a : Assignment) :
    conjunction m (assignment ρ a) =
      match word ρ m with
      | none => 0
      | some q => conjunction q a := by
  induction m with
  | nil => rfl
  | cons l ls ih =>
    have hc : conjunction (l :: ls) (assignment ρ a) =
        conjunction [l] (assignment ρ a) * conjunction ls (assignment ρ a) :=
      conjunction_mul [l] ls _
    rw [hc, ih]
    cases hs : ρ l.1 with
    | inl b =>
      by_cases hb : b = l.2
      · simp [word, hs, hb, conjunction, holds, assignment]
      · simp [word, hs, hb, conjunction, holds, assignment]
    | inr v =>
      cases ht : word ρ ls with
      | none => simp [word, hs, ht]
      | some q =>
        simp only [word, hs, ht, Option.map_some]
        have he : conjunction [l] (assignment ρ a) = conjunction [(v,l.2)] a := by
          simp [conjunction, holds, assignment, hs]
        rw [he]
        exact (conjunction_mul [(v,l.2)] q a).symm

/-- Clause bookkeeping for constant substitution. A clause either becomes true,
or its residual falsity product is exactly that of a target clause. -/
def Clauses (ρ : Substitution) (F G : List Clause) : Prop :=
  ∀ c ∈ F, word ρ (falsity c) = none ∨
    ∃ e ∈ G, word ρ (falsity c) = some (falsity e) ∧ e.length ≤ c.length

theorem cone {ρ : Substitution} {F G d} (clauses : Clauses ρ F G)
    {f} (hf : Cone F d f) : Cone G d (fun a => f (assignment ρ a)) := by
  induction hf with
  | positive m hm hd =>
    cases ht : word ρ m with
    | none =>
      have he : (fun a => conjunction m (assignment ρ a)) = (fun _ => 0) := by
        funext a; simpa [ht] using word_eval ρ m a
      rw [he]; exact Cone.zero
    | some q =>
      have he : (fun a => conjunction m (assignment ρ a)) = conjunction q := by
        funext a; simpa [ht] using word_eval ρ m a
      rw [he]
      exact positive_cell q (Nat.le_trans (word_length ρ m q ht) hd)
  | equation c m r hc hd =>
    rcases clauses c hc with hz | ⟨e,he,ht,hlen⟩
    · have hz' (a) : conjunction (falsity c) (assignment ρ a) = 0 := by
        simpa [hz] using word_eval ρ (falsity c) a
      have heq : (fun a => r * conjunction (m ++ falsity c) (assignment ρ a)) =
          (fun _ => 0) := by
        funext a; rw [conjunction_mul, hz']; simp
      rw [heq]; exact Cone.zero
    · cases hm : word ρ m with
      | none =>
        have hm' (a) : conjunction m (assignment ρ a) = 0 := by
          simpa [hm] using word_eval ρ m a
        have heq : (fun a => r * conjunction (m ++ falsity c) (assignment ρ a)) =
            (fun _ => 0) := by
          funext a; rw [conjunction_mul, hm']; simp
        rw [heq]; exact Cone.zero
      | some q =>
        have heq : (fun a => r * conjunction (m ++ falsity c) (assignment ρ a)) =
            (fun a => r * conjunction (q ++ falsity e) a) := by
          funext a
          rw [conjunction_mul, conjunction_mul, word_eval ρ m, word_eval ρ (falsity c)]
          simp [hm, ht]
        rw [heq]
        exact equation_cell e q r he (by have := word_length ρ m q hm; have := hd.2; omega)
  | zero => exact Cone.zero
  | add _ _ ih jh => exact Cone.add ih jh
  | scale r hr _ ih => exact Cone.scale r hr ih

theorem refutes {ρ : Substitution} {F G d} (clauses : Clauses ρ F G)
    (hf : Refutes F d) : Refutes G d := cone clauses hf

#print axioms refutes
end Programme.«20261101-0614-proof-complexity».ConeRestriction
