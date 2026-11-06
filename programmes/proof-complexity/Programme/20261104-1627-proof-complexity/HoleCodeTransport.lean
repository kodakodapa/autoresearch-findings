import Programme.«20261104-1627-proof-complexity».HoleRestriction

namespace Programme.«20261104-1627-proof-complexity».HoleCodeTransport
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261029-1156-proof-complexity».StdPC

 theorem pushCode_injective {n h : Nat} (hn : 0 < n) :
    Function.Injective (pushCode n h) := by
  intro x y he
  have hx : omitHole h (x % n) < n+1 := omitHole_lt (Nat.mod_lt x hn)
  have hy : omitHole h (y % n) < n+1 := omitHole_lt (Nat.mod_lt y hn)
  have hd := congrArg (fun z => z / (n+1)) he
  have hm := congrArg (fun z => z % (n+1)) he
  simp only [pushCode] at hd hm
  have divcode (z : Nat) : pushCode n h z / (n+1) = z/n := by
    unfold pushCode
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega)]
    rw [Nat.div_eq_of_lt (omitHole_lt (Nat.mod_lt z hn))]
    simp
  have modcode (z : Nat) : pushCode n h z % (n+1) = omitHole h (z%n) := by
    unfold pushCode
    rw [Nat.add_comm, Nat.add_mul_mod_self_right]
    exact Nat.mod_eq_of_lt (omitHole_lt (Nat.mod_lt z hn))
  change pushCode n h x / (n+1) = pushCode n h y / (n+1) at hd
  rw [divcode, divcode] at hd
  change pushCode n h x % (n+1) = pushCode n h y % (n+1) at hm
  rw [modcode, modcode] at hm
  have hr := omitHole_injective h hm
  have hxx := Nat.mod_add_div x n
  have hyy := Nat.mod_add_div y n
  rw [hd, hr] at hxx
  omega

end Programme.«20261104-1627-proof-complexity».HoleCodeTransport
#print axioms Programme.«20261104-1627-proof-complexity».HoleCodeTransport.pushCode_injective
