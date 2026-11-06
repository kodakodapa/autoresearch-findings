import Programme.«20261031-2024-proof-complexity».IterCone

namespace Programme.«20261031-2024-proof-complexity».NativeIter

/-- Multiplying a positive cell by a literal costs at most one formal degree.
Repeated variables are absorbed; contradictory literals give the zero function. -/
theorem positive_guard {F d} (m : List Lit) (hm : Multiplier m)
    (hd : m.length ≤ d) (l : Lit) :
    Cone F (d+1) (fun a => conjunction [l] a * conjunction m a) := by
  by_cases hv : l.1 ∈ m.map Prod.fst
  · obtain ⟨k, hk, he⟩ := List.mem_map.mp hv
    by_cases hs : k.2 = l.2
    · have hkl : k = l := Prod.ext he hs
      subst k
      have hid : (fun a => conjunction [l] a * conjunction m a) = conjunction m := by
        funext a
        by_cases ha : m.all (holds a) = true
        · have hl := List.all_eq_true.mp ha l hk
          simp [conjunction, ha, hl]
        · have ha' : m.all (holds a) = false := Bool.eq_false_iff.mpr ha
          simp [conjunction, ha']
      rw [hid]
      exact Cone.positive m hm (by omega)
    · have hid : (fun a => conjunction [l] a * conjunction m a) = (fun _ => 0) := by
        funext a
        by_cases ha : m.all (holds a) = true
        · have hk' := List.all_eq_true.mp ha k hk
          have hl : holds a l = false := by
            unfold holds at *
            cases h : a l.1 <;> cases hkb : k.2 <;> cases hlb : l.2 <;>
              simp_all
          simp [conjunction, hl]
        · have ha' : m.all (holds a) = false := Bool.eq_false_iff.mpr ha
          simp [conjunction, ha']
      rw [hid]
      exact Cone.zero
  · have hm' : Multiplier (l :: m) := by
      simpa [Multiplier, List.nodup_cons] using And.intro hv hm
    have hp := Cone.positive (F := F) (d := d+1) (l :: m) hm' (by simp; omega)
    have hid : conjunction (l :: m) =
        (fun a => conjunction [l] a * conjunction m a) := by
      funext a
      exact conjunction_mul [l] m a
    rw [hid] at hp
    exact hp

/-- Guarded transport only needs to check the source equation generators.
The callback includes the signed coefficient, so no positivity premise is hidden. -/
theorem cone_guard {F G d} (l : Lit)
    (equations : ∀ c ∈ F, ∀ m, Admitted d c m → ∀ r : Rat,
      Cone G (d+1) (fun a => conjunction [l] a *
        (r * conjunction (m ++ falsity c) a)))
    {f} (hf : Cone F d f) :
    Cone G (d+1) (fun a => conjunction [l] a * f a) := by
  induction hf with
  | positive m hm hd => exact positive_guard m hm hd l
  | equation c m r hc hd => exact equations c hc m hd r
  | zero => simpa using (Cone.zero (F := G) (d := d+1))
  | add hf hg ih jh =>
    simpa only [Rat.mul_add] using Cone.add ih jh
  | @scale g r hr hf ih =>
    have he : (fun a => conjunction [l] a * (r * g a)) =
        (fun a => r * (conjunction [l] a * g a)) := by
      funext a
      rw [← Rat.mul_assoc, Rat.mul_comm (conjunction [l] a) r, Rat.mul_assoc]
    rw [he]
    exact Cone.scale r hr ih

/-- Adjoining the negated guard to every source clause transports the entire
cone, with one unit of formal degree overhead. Clauses here retain list syntax. -/
theorem cone_guard_of_clauses {F G d} (l : Lit)
    (clauses : ∀ c ∈ F, c ++ [neg l] ∈ G)
    {f} (hf : Cone F d f) :
    Cone G (d+1) (fun a => conjunction [l] a * f a) := by
  apply cone_guard l (fun c hc m hd r => ?_) hf
  have ha : Admitted (d+1) (c ++ [neg l]) m := by
    refine ⟨hd.1, ?_⟩
    simp only [List.length_append, List.length_singleton]
    have := hd.2
    omega
  have h := Cone.equation (c ++ [neg l]) m r (clauses c hc) ha
  have he : (fun a => r * conjunction (m ++ falsity (c ++ [neg l])) a) =
      (fun a => conjunction [l] a * (r * conjunction (m ++ falsity c) a)) := by
    funext a
    have hn : neg (neg l) = l := by cases l; simp [neg]
    simp only [falsity, List.map_append, List.map_cons, List.map_nil, hn,
      ← List.append_assoc, conjunction_mul]
    rw [← Rat.mul_assoc]
    exact Rat.mul_comm _ _
  rw [he] at h
  exact h

/-- Two opposite guarded contradictions combine to a refutation. -/
theorem refutes_of_opposite_guards {G d} (l : Lit)
    (h : Cone G d (fun a => conjunction [l] a * (-1)))
    (hn : Cone G d (fun a => conjunction [neg l] a * (-1))) : Refutes G d := by
  have hh := Cone.add h hn
  have he : (fun a => conjunction [l] a * (-1) +
      conjunction [neg l] a * (-1)) = (fun _ => -1) := by
    funext a
    rcases l with ⟨v, b⟩
    cases ha : a v <;> cases b <;> simp [conjunction, holds, neg, ha, Rat.add_zero, Rat.zero_add]
  rw [he] at hh
  exact hh

#print axioms positive_guard
#print axioms cone_guard
#print axioms cone_guard_of_clauses
#print axioms refutes_of_opposite_guards
end Programme.«20261031-2024-proof-complexity».NativeIter
