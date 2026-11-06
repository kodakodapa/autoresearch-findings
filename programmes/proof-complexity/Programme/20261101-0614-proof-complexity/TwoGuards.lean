import Programme.«20261031-2024-proof-complexity».ConeMixed

namespace Programme.«20261101-0614-proof-complexity».TwoGuards
open Programme.«20261031-2024-proof-complexity».NativeIter

/-- Two guarded contradictions suffice when a clause covers their guards. -/
theorem refutes_of_covering_guards {G d} (l k : Lit)
    (hne : l.1 ≠ k.1) (hd : 2 ≤ d) (hc : [l,k] ∈ G)
    (hl : Cone G d (fun a => conjunction [l] a * (-1)))
    (hk : Cone G d (fun a => conjunction [k] a * (-1))) : Refutes G d := by
  have hp : Cone G d (conjunction [l,k]) :=
    Cone.positive [l,k] (by simp [Multiplier, hne]) (by simpa using hd)
  have he := Cone.equation [l,k] [] (-1) hc
    (show Admitted d [l,k] [] from ⟨by simp [Multiplier], by simpa using hd⟩)
  have hs := Cone.add (Cone.add (Cone.add hl hk) hp) he
  have hi : (fun a => ((conjunction [l] a * (-1) + conjunction [k] a * (-1)) +
      conjunction [l,k] a) + (-1 * conjunction ([] ++ falsity [l,k]) a)) =
      (fun _ => (-1 : Rat)) := by
    funext a
    rcases l with ⟨v,b⟩
    rcases k with ⟨w,c⟩
    cases hv : a v <;> cases hw : a w <;> cases b <;> cases c <;>
      simp [conjunction, holds, falsity, neg, hv, hw, Rat.add_zero, Rat.zero_add,
        Rat.add_assoc, Rat.neg_add_cancel]
  rw [hi] at hs
  exact hs

#print axioms refutes_of_covering_guards
end Programme.«20261101-0614-proof-complexity».TwoGuards
