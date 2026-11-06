import Programme.«20261026-1402-proof-complexity».ExtLemma

namespace Programme.«20261102-0806-proof-complexity».P11Swap

/-- Exchange the two ten-hole classes in a base-eleven row type. -/
def swap (x : Nat) : Nat := (x / 11 % 11) + 11 * (x % 11) + 121 * (x / 121)

theorem swap_involutive (x : Nat) : swap (swap x) = x := by
  have digits (y : Nat) : y = y % 11 + 11 * (y / 11 % 11) + 121 * (y / 121) := by
    have h := Nat.mod_add_div y 11
    have h' := Nat.mod_add_div (y / 11) 11
    have h'' : y / 11 / 11 = y / 121 := by rw [Nat.div_div_eq_div_mul]
    omega
  have lo : swap x / 121 = x / 121 := by
    unfold swap
    have h0 := Nat.mod_lt x (by decide : 0 < 11)
    have h1 := Nat.mod_lt (x / 11) (by decide : 0 < 11)
    omega
  have mid : swap x / 11 % 11 = x % 11 := by
    have := digits (swap x)
    have hs : swap x = (x / 11 % 11) + 11 * (x % 11) + 121 * (x / 121) := rfl
    have h0 := Nat.mod_lt (x / 11) (by decide : 0 < 11)
    have h1 := Nat.mod_lt (swap x) (by decide : 0 < 11)
    omega
  have low : swap x % 11 = x / 11 % 11 := by
    have := digits (swap x)
    have hs : swap x = (x / 11 % 11) + 11 * (x % 11) + 121 * (x / 121) := rfl
    omega
  rw [swap, low, mid, lo]
  have := digits x
  omega

theorem map_swap_involutive (xs : List Nat) : (xs.map swap).map swap = xs := by
  simp [List.map_map, Function.comp_def, swap_involutive]

/-- Sorting/encoding of pigeon classes is an explicit parameter. -/
def orbitKey (encode : List Nat → Nat) (xs : List Nat) : Nat :=
  min (encode xs) (encode (xs.map swap))

theorem orbitKey_swap (encode : List Nat → Nat) (xs : List Nat) :
    orbitKey encode (xs.map swap) = orbitKey encode xs := by
  simp only [orbitKey, map_swap_involutive]
  exact Nat.min_comm _ _

theorem table_swap (encode : List Nat → Nat) (table : Nat → Int) (xs : List Nat) :
    table (orbitKey encode (xs.map swap)) = table (orbitKey encode xs) := by
  rw [orbitKey_swap]

#print axioms swap_involutive
#print axioms orbitKey_swap
#print axioms table_swap
end Programme.«20261102-0806-proof-complexity».P11Swap
