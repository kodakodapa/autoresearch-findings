import Programme.«20261025-0459-proof-complexity».OntoSubst

/-!
# Parity of linear forms through big-number XOR

A linear form over `Z/2` on coordinates `c < M` is a list `L` of coordinates (a multiset).
`bv L` is its parity vector, `⨁_{c ∈ L} 2^c`, computed by the kernel with GMP arithmetic.
`ev_bv`: `∑_{c ∈ L} F c ≡ evB F M (bv L)` mod 2, so `bv L = 0` gives `2 ∣ ∑_{c ∈ L} F c`.
-/

namespace Programme.«20261027-1434-proof-complexity».F2Lin

open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-0459-proof-complexity».OntoSubst (rsum_congr rsum_zero)

def ev (F : Nat → Int) (L : List Nat) : Int := (L.map F).sum

def bv : List Nat → Nat
  | [] => 0
  | c :: L => bv L ^^^ 2 ^ c

def evB (F : Nat → Int) (M B : Nat) : Int := rsum M (fun c => if B.testBit c then F c else 0)

theorem rsum_sub2 (M : Nat) (f g : Nat → Int) : rsum M f - rsum M g = rsum M (fun t => f t - g t) := by
  induction M with
  | zero => rfl
  | succ M ih => show rsum M f + f M - (rsum M g + g M) = rsum M (fun t => f t - g t) + (f M - g M); omega

theorem rsum_single (M c : Nat) (hc : c < M) (G : Nat → Int) (h : ∀ t < M, t ≠ c → G t = 0) :
    rsum M G = G c := by
  induction M with
  | zero => omega
  | succ M ih =>
    show rsum M G + G M = G c
    by_cases e : c = M
    · subst e
      have : rsum c G = 0 := by
        rw [rsum_congr c G (fun _ => 0) (fun t ht => h t (by omega) (by omega))]
        clear ih h hc; induction c with
        | zero => rfl
        | succ c ih => show rsum c (fun _ => (0:Int)) + 0 = 0; rw [ih]; rfl
      omega
    · rw [ih (by omega) (fun t ht hne => h t (by omega) hne), h M (by omega) (fun h' => e h'.symm)]; omega

theorem evB_xor (F : Nat → Int) (M B c : Nat) (hc : c < M) :
    (2 : Int) ∣ evB F M (B ^^^ 2 ^ c) - evB F M B - F c := by
  unfold evB
  rw [rsum_sub2, rsum_single M c hc]
  · simp only [Nat.testBit_xor, Nat.testBit_two_pow_self, ]
    cases B.testBit c <;> simp <;> exact ⟨-F c, by omega⟩
  · intro t _ hne
    have : (2 ^ c).testBit t = false := by
      rw [Nat.testBit_two_pow]; simp [Ne.symm hne]
    simp [Nat.testBit_xor, this]

theorem evB_zero (F : Nat → Int) (M : Nat) : evB F M 0 = 0 :=
  rsum_zero M _ (fun t _ => by simp)

theorem ev_bv (F : Nat → Int) (M : Nat) : ∀ L : List Nat, (∀ c ∈ L, c < M) →
    (2 : Int) ∣ ev F L - evB F M (bv L)
  | [], _ => by rw [show bv [] = 0 from rfl, evB_zero]; exact ⟨0, by simp [ev]⟩
  | c :: L, h => by
    have ih := ev_bv F M L (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have hx := evB_xor F M (bv L) c (h c List.mem_cons_self)
    have e : ev F (c :: L) = F c + ev F L := by simp [ev]
    rw [e]; show (2 : Int) ∣ F c + ev F L - evB F M (bv L ^^^ 2 ^ c)
    have := Int.dvd_sub ih hx
    rwa [show ev F L - evB F M (bv L) - (evB F M (bv L ^^^ 2 ^ c) - evB F M (bv L) - F c) =
      F c + ev F L - evB F M (bv L ^^^ 2 ^ c) by omega] at this

/-- A form with zero parity vector evaluates to an even number. -/
theorem ev_even {F : Nat → Int} {M : Nat} {L : List Nat} (hL : ∀ c ∈ L, c < M) (h0 : bv L = 0) :
    (2 : Int) ∣ ev F L := by
  have := ev_bv F M L hL
  rwa [h0, evB_zero, Int.sub_zero] at this

end Programme.«20261027-1434-proof-complexity».F2Lin

#print axioms Programme.«20261027-1434-proof-complexity».F2Lin.ev_even
