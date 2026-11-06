import Programme.«20261101-1618-proof-complexity».ClauseLinear
import Programme.«20261031-2024-proof-complexity».ConeIdentify

namespace Programme.«20261101-1618-proof-complexity».ClauseLinear
open Programme.«20261031-2024-proof-complexity».NativeIter

theorem positive_cell {F d} (m : List Lit) (hd : m.length ≤ d) :
    Cone F d (conjunction m) := by
  rcases cell_normalize m with hz | ⟨q,hq,hlen,heq⟩
  · rw [hz]; exact .zero
  · rw [← heq]; exact .positive q hq (by omega)

theorem clause_cell {F d} (c m : List Lit) (hc : c ∈ F)
    (hd : m.length + 1 ≤ d) :
    Cone F d (fun a => conjunction m a * slack c a) := by
  rcases cell_normalize m with hz | ⟨q,hq,hlen,heq⟩
  · simp only [hz, Rat.zero_mul]; exact .zero
  · rw [← heq]; exact .clause c q hc hq (by omega)

/-- Conditioning by any literal cell increases formal degree by at most its length. -/
theorem condition {F d f} (m : List Lit) (hf : Cone F d f) :
    Cone F (d + m.length) (fun a => conjunction m a * f a) := by
  induction hf with
  | positive q hq hd =>
    have hh := positive_cell (F := F) (d := d + m.length) (m ++ q) (by simp; omega)
    have he : conjunction (m ++ q) = (fun a => conjunction m a * conjunction q a) :=
      funext (conjunction_mul m q)
    rwa [he] at hh
  | clause c q hc hq hd =>
    have hh := clause_cell (F := F) (d := d + m.length) c (m ++ q) hc (by simp; omega)
    simpa only [conjunction_mul, Rat.mul_assoc] using hh
  | zero => simpa using (Cone.zero (F := F) (d := d + m.length))
  | add _ _ ih jh => simpa only [Rat.mul_add] using Cone.add ih jh
  | @scale f r hr _ ih =>
    have he : (fun a => conjunction m a * (r * f a)) =
        (fun a => r * (conjunction m a * f a)) := by
      funext a
      rw [← Rat.mul_assoc, Rat.mul_comm (conjunction m a) r, Rat.mul_assoc]
    rw [he]
    exact .scale r hr ih

/-- Opposite conditioned contradictions discharge a Boolean case split. -/
theorem split {F d} (l : Lit)
    (hp : Cone F d (fun a => -conjunction [l] a))
    (hn : Cone F d (fun a => -conjunction [neg l] a)) : Refutes F d := by
  have hh := Cone.add hp hn
  have he : (fun a => -conjunction [l] a + -conjunction [neg l] a) =
      (fun _ => (-1 : Rat)) := by
    funext a
    rcases l with ⟨v,b⟩
    cases ha : a v <;> cases b <;>
      simp [conjunction, holds, neg, ha, Rat.add_zero, Rat.zero_add]
  rwa [he] at hh

#print axioms condition
#print axioms split
end Programme.«20261101-1618-proof-complexity».ClauseLinear
