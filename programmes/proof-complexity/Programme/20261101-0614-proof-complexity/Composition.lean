import Programme.«20261101-0614-proof-complexity».«th-split».RestrictionBridge
namespace Programme.«20261101-0614-proof-complexity».Composition
open Programme.«20261031-2024-proof-complexity».NativeIter
open Programme.«20261101-0614-proof-complexity».RestrictionTarget

/-- Fixed arithmetic coordinate code; injectivity is not needed by the local lemmas below. -/
def pair (a b : Nat) : Nat := (a+b)*(a+b+1)+2*b
def fVar (a y : Nat) : Var := (0, pair a y)
def sVar (y x z : Nat) : Var := (1, pair y (pair x z))
def gVar (y x a : Nat) : Var := (2, pair y (pair x a))
def pos (v : Var) : Lit := (v,true)
def minus (v : Var) : Lit := (v,false)
/-- Singleton rows are substituted true. -/
def onehot (n : Nat) (v : Nat → Var) : List Clause :=
  if n = 1 then [] else
  [(List.range n).map (fun i => pos (v i))] ++
  (List.range n).flatMap (fun i =>
    ((List.range n).filter (i < ·)).map (fun j => [minus (v i), minus (v j)]))
def events (L y : Nat) : List (Nat × Clause) :=
  [(0,[minus (sVar y 0 0)])] ++
  (List.range L).flatMap (fun x => (List.range x).map (fun z =>
    (x,[minus (sVar y x z)]))) ++
  (List.range L).flatMap (fun x =>
    ((List.range L).filter (x < ·)).map (fun z =>
      (x,[minus (sVar y x z), minus (sVar y z z)])))
def eventClause (M y x a : Nat) (c : Clause) : Clause :=
  c ++ (if M = 1 then [] else [minus (gVar y x a)]) ++ [pos (fVar a y)]
/-- General candidate unary rwPHP(Iter), using canonical native clauses. -/
def cnf (M N L : Nat) : List Clause :=
  ((List.range M).flatMap (fun a => onehot N (fVar a)) ++
   (List.range N).flatMap (fun y =>
     (List.range L).flatMap (fun x => onehot L (sVar y x))) ++
   (List.range N).flatMap (fun y =>
     (List.range L).flatMap (fun x => onehot M (gVar y x))) ++
   (List.range N).flatMap (fun y =>
     (events L y).flatMap (fun e =>
       (List.range M).map (fun a => eventClause M y e.1 a e.2)))).eraseDups
/-- Clause-level specification of a matched-pair substitution.
Existence and the structural-clause proof are separate obligations. -/
structure RestrictionSpec (ρ : Substitution) (M N : Nat) : Prop where
  keptF : ∀ a y, a < M → y < N → ρ (fVar a y) = .inr (fVar a y)
  keptS : ∀ y x z, y < N → ρ (sVar y x z) = .inr (sVar y x z)
  keptG : ∀ y x a, y < N → a < M →
    ρ (gVar y x a) = if M = 1 then .inl true else .inr (gVar y x a)
  removedInput : ∀ y x, y < N → ρ (gVar y x M) = .inl false
  removedG : ∀ x a, ρ (gVar N x a) = .inl (a == M)
  removedF : ρ (fVar M N) = .inl true

theorem clause_append (ρ : Substitution) (c t : Clause) :
    clause ρ (c ++ t) = (clause ρ c).bind (fun s => (clause ρ t).map (s ++ ·)) := by
  induction c with
  | nil => simp [clause]
  | cons l c ih =>
    simp only [List.cons_append, clause]
    cases literal ρ l with
    | inl b => cases b <;> simp [ih]
    | inr k => rw [ih]; cases clause ρ c <;> cases clause ρ t <;> rfl

theorem fixed_clause (ρ : Substitution) (c : Clause)
    (hc : ∀ l ∈ c, ρ l.1 = .inr l.1) : clause ρ c = some c := by
  induction c with
  | nil => rfl
  | cons l c ih =>
    simp only [clause, literal, hc l (by simp)]
    rw [ih (fun k hk => hc k (by simp [hk]))]; rfl

/-- Deleted-block events are true, independently of their S literals. -/
theorem deleted_event (ρ : Substitution) (M N x a : Nat) (c : Clause)
    (hs : RestrictionSpec ρ M N) (hM : 1 ≤ M) :
    clause ρ (eventClause (M+1) N x a c) = none := by
  have hn : M+1 ≠ 1 := by omega
  have hz : M ≠ 0 := by omega
  by_cases he : a = M
  · subst a
    simp only [eventClause, ite_eq_right hn, clause_append]
    simp [clause, literal, minus, pos, hs.removedG, hs.removedF]
  · have hb : (a == M) = false := by exact beq_eq_false_iff_ne.mpr he
    simp only [eventClause, ite_eq_right hn, clause_append]
    simp [clause, literal, minus, pos, hs.removedG, hb]

theorem deleted_input_event (ρ : Substitution) (M N y x : Nat) (c : Clause)
    (hs : RestrictionSpec ρ M N) (hM : 1 ≤ M) (hy : y < N) :
    clause ρ (eventClause (M+1) y x M c) = none := by
  have hn : M+1 ≠ 1 := by omega
  simp only [eventClause, ite_eq_right hn, clause_append]
  simp [clause, literal, minus, hs.removedInput y x hy]

/-- Includes the singleton G coordinate being substituted true. -/
theorem retained_event (ρ : Substitution) (M N y x a : Nat) (c : Clause)
    (hs : RestrictionSpec ρ M N) (hM : 1 ≤ M) (ha : a < M) (hy : y < N)
    (hc : ∀ l ∈ c, ρ l.1 = .inr l.1) :
    clause ρ (eventClause (M+1) y x a c) = some (eventClause M y x a c) := by
  have hn : M+1 ≠ 1 := by omega
  have hfix := fixed_clause ρ c hc
  simp only [eventClause, ite_eq_right hn, clause_append, hfix]
  by_cases hm : M = 1 <;>
    simp [clause, literal, minus, pos, hs.keptF a y ha hy, hs.keptG y x a hy ha, hm]
theorem events_fixed (ρ : Substitution) (M N L y x : Nat) (c : Clause)
    (hs : RestrictionSpec ρ M N) (hy : y < N) (he : (x,c) ∈ events L y) :
    ∀ l ∈ c, ρ l.1 = .inr l.1 := by
  have hl (u v : Nat) : ρ (minus (sVar y u v)).1 = .inr (minus (sVar y u v)).1 :=
    hs.keptS y u v hy
  simp only [events, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatMap, List.mem_map] at he
  rcases he with (he | ⟨u, _, v, _, he⟩) | ⟨u, _, v, _, he⟩
  · cases he; simpa using hl 0 0
  · cases he; simpa using hl x v
  · cases he; intro l hlit
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlit
    rcases hlit with rfl | rfl
    · exact hl x v
    · exact hl v v

/-- All retained Iter event clauses have the exact residual target clause. -/
theorem retained_iter_event (ρ : Substitution) (M N L y x a : Nat) (c : Clause)
    (hs : RestrictionSpec ρ M N) (hM : 1 ≤ M) (ha : a < M) (hy : y < N)
    (he : (x,c) ∈ events L y) :
    clause ρ (eventClause (M+1) y x a c) = some (eventClause M y x a c) :=
  retained_event ρ M N y x a c hs hM ha hy (events_fixed ρ M N L y x c hs hy he)

theorem event_residuals (ρ : Substitution) (M N L : Nat)
    (hs : RestrictionSpec ρ M N) (hM : 1 ≤ M) :
    (∀ x a c, clause ρ (eventClause (M+1) N x a c) = none) ∧
    (∀ y x c, y < N → clause ρ (eventClause (M+1) y x M c) = none) ∧
    (∀ y x a c, a < M → y < N → (x,c) ∈ events L y →
      clause ρ (eventClause (M+1) y x a c) = some (eventClause M y x a c)) := by
  exact ⟨fun x a c => deleted_event ρ M N x a c hs hM,
    fun y x c hy => deleted_input_event ρ M N y x c hs hM hy,
    fun y x a c ha hy he => retained_iter_event ρ M N L y x a c hs hM ha hy he⟩
#print axioms event_residuals
#print axioms deleted_event
#print axioms deleted_input_event
#print axioms retained_iter_event
end Programme.«20261101-0614-proof-complexity».Composition
