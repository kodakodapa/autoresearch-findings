import Programme.«20261027-1434-proof-complexity».Ext278d

/-!
# Splitting a large `kx` step of `Peel3.run3`

A `kx` step with thousands of generators exhausts kernel memory when `decide` evaluates
`bv (suppL gs)` in one go. `Part gs N` records that every generator of `gs` is valid and that the
XOR mask of its support list is `N`; parts combine by `++` and `^^^`, so each part's mask is a
separate kernel computation and the step itself only compares literals.
-/

namespace Programme.«20261028-0841-proof-complexity».L3.Big

open Programme.«20261027-1434-proof-complexity».Peel3
open Programme.«20261027-1434-proof-complexity».F2Lin
open Programme.«20261027-1434-proof-complexity».Code3

theorem bv_append : ∀ (L1 L2 : List Nat), bv (L1 ++ L2) = bv L1 ^^^ bv L2
  | [], L2 => by simp [bv]
  | c :: L1, L2 => by
    simp only [List.cons_append, bv, bv_append L1 L2]
    rw [Nat.xor_assoc, Nat.xor_comm (bv L2), ← Nat.xor_assoc]

def Part (gs : List GS) (N : Nat) : Prop := gs.all GS.valid = true ∧ bv (suppL gs) = N

theorem part_of (gs : List GS) (N : Nat) (h : (gs.all GS.valid && bv (suppL gs) == N) = true) :
    Part gs N := by
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h

theorem part_append {g1 g2 : List GS} {N1 N2 : Nat} (h1 : Part g1 N1) (h2 : Part g2 N2) :
    Part (g1 ++ g2) (N1 ^^^ N2) := by
  refine ⟨by rw [List.all_append, h1.1, h2.1]; rfl, ?_⟩
  have e : suppL (g1 ++ g2) = suppL g1 ++ suppL g2 := List.flatMap_append ..
  rw [e, bv_append, h1.2, h2.2]

theorem kx_step {gs : List GS} {N : Nat} (P a b c : Nat) (h : Part gs N)
    (hc : (okPt a b c && (((N ^^^ 2 ^ r3 a b c) &&& P) == 0 && N.testBit (r3 a b c))) = true) :
    step3 P (.kx gs a b c) = some (P ||| 2 ^ r3 a b c) := by
  simp only [Bool.and_eq_true] at hc
  have hx : chkX P (r3 a b c) (suppL gs) = true := by
    unfold chkX; rw [h.2]; simp only [Bool.and_eq_true]; exact hc.2
  simp [step3, hc.1, h.1, hx]

theorem run_one {P P' : Nat} {s : Step3} (h : step3 P s = some P') : run3 P [s] = some P' := by
  simp [run3, h]

theorem kx_run {gs : List GS} {N : Nat} (P P' a b c : Nat) (h : Part gs N)
    (hc : (okPt a b c && (((N ^^^ 2 ^ r3 a b c) &&& P) == 0 && N.testBit (r3 a b c))) = true)
    (hP : ((P ||| 2 ^ r3 a b c) == P') = true) : run3 P [.kx gs a b c] = some P' := by
  rw [run_one (kx_step P a b c h hc), beq_iff_eq.mp hP]

end Programme.«20261028-0841-proof-complexity».L3.Big
