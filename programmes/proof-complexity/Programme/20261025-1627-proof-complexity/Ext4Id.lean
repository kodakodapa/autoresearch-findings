import Programme.«20261025-1627-proof-complexity».Ext4Alg
set_option linter.unusedVariables false

namespace Programme.«20261025-1627-proof-complexity».Ext4Alg

variable {p : Nat}

open Programme.«20261025-0459-proof-complexity».OntoFPHP

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem pig_ident4 (n : Nat) (c : Int) (y : Nat → Int) (z : Nat → Nat → Int) (t : Nat → Nat → Nat → Int)
    (hzs : ∀ v w, z v w = z w v) (ht12 : ∀ u v w, t u v w = t v u w) (ht23 : ∀ u v w, t u v w = t u w v)
    (hzc : ∀ a a' b, b < n → a ≠ a' → z (var n a b) (var n a' b) = 0)
    (htc12 : ∀ a a' b x, b < n → a ≠ a' → t (var n a b) (var n a' b) x = 0)
    (htc13 : ∀ a a' b x, b < n → a ≠ a' → t (var n a b) x (var n a' b) = 0)
    (htc23 : ∀ a a' b x, b < n → a ≠ a' → t x (var n a b) (var n a' b) = 0)
    (a0 a1 a2 i b0 b1 b2 : Nat) (hr0 : a0 ≠ a1) (hr1 : a0 ≠ a2) (hr2 : a1 ≠ a2) (hr3 : a0 ≠ i) (hr4 : a1 ≠ i) (hr5 : a2 ≠ i) (hc0 : b0 ≠ b1) (hc1 : b0 ≠ b2) (hc2 : b1 ≠ b2)
    (hb0 : b0 < n) (hb1 : b1 < n) (hb2 : b2 < n) :
    RP3 n c y z t a0 a1 a2 i b0 b1 b2 + RP2 n c y z t a0 a1 i a2 b0 b1 b2 + RP3 n c y z t a0 a2 a1 i b0 b2 b1 + RP2 n c y z t a0 a2 i a1 b0 b2 b1 + RP1 n c y z t a0 i a1 a2 b0 b1 b2 + RP1 n c y z t a0 i a2 a1 b0 b2 b1 + RP3 n c y z t a1 a0 a2 i b1 b0 b2 + RP2 n c y z t a1 a0 i a2 b1 b0 b2 + RP3 n c y z t a1 a2 a0 i b1 b2 b0 + RP2 n c y z t a1 a2 i a0 b1 b2 b0 + RP1 n c y z t a1 i a0 a2 b1 b0 b2 + RP1 n c y z t a1 i a2 a0 b1 b2 b0 + RP3 n c y z t a2 a0 a1 i b2 b0 b1 + RP2 n c y z t a2 a0 i a1 b2 b0 b1 + RP3 n c y z t a2 a1 a0 i b2 b1 b0 + RP2 n c y z t a2 a1 i a0 b2 b1 b0 + RP1 n c y z t a2 i a0 a1 b2 b0 b1 + RP1 n c y z t a2 i a1 a0 b2 b1 b0 + RP0 n c y z t i a0 a1 a2 b0 b1 b2 + RP0 n c y z t i a0 a2 a1 b0 b2 b1 + RP0 n c y z t i a1 a0 a2 b1 b0 b2 + RP0 n c y z t i a1 a2 a0 b1 b2 b0 + RP0 n c y z t i a2 a0 a1 b2 b0 b1 + RP0 n c y z t i a2 a1 a0 b2 b1 b0 -
      S4 n c y z t a0 a1 a2 i b0 b1 b2 b0 - S4 n c y z t a0 a1 a2 i b0 b1 b2 b1 - S4 n c y z t a0 a1 a2 i b0 b1 b2 b2 = M4 n * t (var n a0 b0) (var n a1 b1) (var n a2 b2) := by
  have hr0' := Ne.symm hr0; have hr1' := Ne.symm hr1; have hr2' := Ne.symm hr2; have hr3' := Ne.symm hr3; have hr4' := Ne.symm hr4; have hr5' := Ne.symm hr5; have hc0' := Ne.symm hc0; have hc1' := Ne.symm hc1; have hc2' := Ne.symm hc2;
  unfold RP0 RP1 RP2 RP3 S4 Gp4
  simp only [hzc, htc12, htc13, htc23, hb0, hb1, hb2, hr0, hr1, hr2, hr3, hr4, hr5, hr0', hr1', hr2', hr3', hr4', hr5', hc0, hc1, hc2, hc0', hc1', hc2', hzs, ht12, ht23, ne_eq, not_false_eq_true, Int.mul_zero, Int.add_zero, Int.zero_add]
  unfold G0 G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 M4
  clear hzc htc12 htc13 htc23 hzs ht12 ht23
  grind

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem hole_ident4 (n : Nat) (c : Int) (y : Nat → Int) (z : Nat → Nat → Int) (t : Nat → Nat → Nat → Int)
    (hzs : ∀ v w, z v w = z w v) (ht12 : ∀ u v w, t u v w = t v u w) (ht23 : ∀ u v w, t u v w = t u w v)
    (hzr : ∀ a b b', b < n → b' < n → b ≠ b' → z (var n a b) (var n a b') = 0)
    (htr12 : ∀ a b b' x, b < n → b' < n → b ≠ b' → t (var n a b) (var n a b') x = 0)
    (htr13 : ∀ a b b' x, b < n → b' < n → b ≠ b' → t (var n a b) x (var n a b') = 0)
    (htr23 : ∀ a b b' x, b < n → b' < n → b ≠ b' → t x (var n a b) (var n a b') = 0)
    (a0 a1 a2 b0 b1 b2 j : Nat) (hr0 : a0 ≠ a1) (hr1 : a0 ≠ a2) (hr2 : a1 ≠ a2) (hc0 : b0 ≠ b1) (hc1 : b0 ≠ b2) (hc2 : b1 ≠ b2) (hc3 : b0 ≠ j) (hc4 : b1 ≠ j) (hc5 : b2 ≠ j)
    (hb0 : b0 < n) (hb1 : b1 < n) (hb2 : b2 < n) (hj : j < n) :
    RH3 n c y z t a0 a1 a2 b0 b1 b2 j + RH2 n c y z t a0 a1 a2 b0 b1 j b2 + RH3 n c y z t a0 a2 a1 b0 b2 b1 j + RH2 n c y z t a0 a2 a1 b0 b2 j b1 + RH1 n c y z t a0 a1 a2 b0 j b1 b2 + RH1 n c y z t a0 a2 a1 b0 j b2 b1 + RH3 n c y z t a1 a0 a2 b1 b0 b2 j + RH2 n c y z t a1 a0 a2 b1 b0 j b2 + RH3 n c y z t a1 a2 a0 b1 b2 b0 j + RH2 n c y z t a1 a2 a0 b1 b2 j b0 + RH1 n c y z t a1 a0 a2 b1 j b0 b2 + RH1 n c y z t a1 a2 a0 b1 j b2 b0 + RH3 n c y z t a2 a0 a1 b2 b0 b1 j + RH2 n c y z t a2 a0 a1 b2 b0 j b1 + RH3 n c y z t a2 a1 a0 b2 b1 b0 j + RH2 n c y z t a2 a1 a0 b2 b1 j b0 + RH1 n c y z t a2 a0 a1 b2 j b0 b1 + RH1 n c y z t a2 a1 a0 b2 j b1 b0 + RH0 n c y z t a0 a1 a2 j b0 b1 b2 + RH0 n c y z t a0 a2 a1 j b0 b2 b1 + RH0 n c y z t a1 a0 a2 j b1 b0 b2 + RH0 n c y z t a1 a2 a0 j b1 b2 b0 + RH0 n c y z t a2 a0 a1 j b2 b0 b1 + RH0 n c y z t a2 a1 a0 j b2 b1 b0 -
      S4 n c y z t a0 a1 a2 a0 b0 b1 b2 j - S4 n c y z t a0 a1 a2 a1 b0 b1 b2 j - S4 n c y z t a0 a1 a2 a2 b0 b1 b2 j = M4 n * t (var n a0 b0) (var n a1 b1) (var n a2 b2) := by
  have hr0' := Ne.symm hr0; have hr1' := Ne.symm hr1; have hr2' := Ne.symm hr2; have hc0' := Ne.symm hc0; have hc1' := Ne.symm hc1; have hc2' := Ne.symm hc2; have hc3' := Ne.symm hc3; have hc4' := Ne.symm hc4; have hc5' := Ne.symm hc5;
  unfold RH0 RH1 RH2 RH3 S4 Gp4
  simp only [hzr, htr12, htr13, htr23, hb0, hb1, hb2, hj, hr0, hr1, hr2, hr0', hr1', hr2', hc0, hc1, hc2, hc3, hc4, hc5, hc0', hc1', hc2', hc3', hc4', hc5', hzs, ht12, ht23, ne_eq, not_false_eq_true, Int.mul_zero, Int.add_zero, Int.zero_add]
  unfold G0 G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 M4
  clear hzr htr12 htr13 htr23 hzs ht12 ht23
  grind

theorem pig_total (n : Nat) (c : Int) (y : Nat → Int) (z : Nat → Nat → Int) (t : Nat → Nat → Nat → Int)
    (hzs : ∀ v w, z v w = z w v) (ht12 : ∀ u v w, t u v w = t v u w) (ht23 : ∀ u v w, t u v w = t u w v)
    (hzc : ∀ a a' b, b < n → a ≠ a' → z (var n a b) (var n a' b) = 0)
    (htc12 : ∀ a a' b x, b < n → a ≠ a' → t (var n a b) (var n a' b) x = 0)
    (htc13 : ∀ a a' b x, b < n → a ≠ a' → t (var n a b) x (var n a' b) = 0)
    (htc23 : ∀ a a' b x, b < n → a ≠ a' → t x (var n a b) (var n a' b) = 0)
    (P : Nat)
    (hR1 : ∀ i < P, (p : Int) ∣ rsum n (fun j => y (var n i j)) - c)
    (hR2a : ∀ v, ∀ i < P, (p : Int) ∣ rsum n (fun j => z (var n i j) v) - y v)
    (hR2b : ∀ v, ∀ i < P, (p : Int) ∣ rsum n (fun j => z v (var n i j)) - y v)
    (hR3a : ∀ v w, ∀ i < P, (p : Int) ∣ rsum n (fun j => t (var n i j) v w) - z v w)
    (hR3b : ∀ v w, ∀ i < P, (p : Int) ∣ rsum n (fun j => t v (var n i j) w) - z v w)
    (hR3c : ∀ v w, ∀ i < P, (p : Int) ∣ rsum n (fun j => t v w (var n i j)) - z v w)
    (a0 a1 a2 i b0 b1 b2 : Nat) (ha0 : a0 < P) (ha1 : a1 < P) (ha2 : a2 < P) (hi : i < P)
    (hr0 : a0 ≠ a1) (hr1 : a0 ≠ a2) (hr2 : a1 ≠ a2) (hr3 : a0 ≠ i) (hr4 : a1 ≠ i) (hr5 : a2 ≠ i) (hc0 : b0 ≠ b1) (hc1 : b0 ≠ b2) (hc2 : b1 ≠ b2)
    (hb0 : b0 < n) (hb1 : b1 < n) (hb2 : b2 < n) :
    (p : Int) ∣ rsum n (fun j => S4 n c y z t a0 a1 a2 i b0 b1 b2 j) - (S4 n c y z t a0 a1 a2 i b0 b1 b2 b0 + S4 n c y z t a0 a1 a2 i b0 b1 b2 b1 + S4 n c y z t a0 a1 a2 i b0 b1 b2 b2 + M4 n * t (var n a0 b0) (var n a1 b1) (var n a2 b2)) := by
  have hsum : rsum n (fun j => S4 n c y z t a0 a1 a2 i b0 b1 b2 j) = rsum n (fun j => Gp4 n c y z t a0 a1 a2 i b0 b1 b2 j) + rsum n (fun j => Gp4 n c y z t a0 a1 i a2 b0 b1 j b2) + rsum n (fun j => Gp4 n c y z t a0 a2 a1 i b0 b2 b1 j) + rsum n (fun j => Gp4 n c y z t a0 a2 i a1 b0 b2 j b1) + rsum n (fun j => Gp4 n c y z t a0 i a1 a2 b0 j b1 b2) + rsum n (fun j => Gp4 n c y z t a0 i a2 a1 b0 j b2 b1) + rsum n (fun j => Gp4 n c y z t a1 a0 a2 i b1 b0 b2 j) + rsum n (fun j => Gp4 n c y z t a1 a0 i a2 b1 b0 j b2) + rsum n (fun j => Gp4 n c y z t a1 a2 a0 i b1 b2 b0 j) + rsum n (fun j => Gp4 n c y z t a1 a2 i a0 b1 b2 j b0) + rsum n (fun j => Gp4 n c y z t a1 i a0 a2 b1 j b0 b2) + rsum n (fun j => Gp4 n c y z t a1 i a2 a0 b1 j b2 b0) + rsum n (fun j => Gp4 n c y z t a2 a0 a1 i b2 b0 b1 j) + rsum n (fun j => Gp4 n c y z t a2 a0 i a1 b2 b0 j b1) + rsum n (fun j => Gp4 n c y z t a2 a1 a0 i b2 b1 b0 j) + rsum n (fun j => Gp4 n c y z t a2 a1 i a0 b2 b1 j b0) + rsum n (fun j => Gp4 n c y z t a2 i a0 a1 b2 j b0 b1) + rsum n (fun j => Gp4 n c y z t a2 i a1 a0 b2 j b1 b0) + rsum n (fun j => Gp4 n c y z t i a0 a1 a2 j b0 b1 b2) + rsum n (fun j => Gp4 n c y z t i a0 a2 a1 j b0 b2 b1) + rsum n (fun j => Gp4 n c y z t i a1 a0 a2 j b1 b0 b2) + rsum n (fun j => Gp4 n c y z t i a1 a2 a0 j b1 b2 b0) + rsum n (fun j => Gp4 n c y z t i a2 a0 a1 j b2 b0 b1) + rsum n (fun j => Gp4 n c y z t i a2 a1 a0 j b2 b1 b0) := by
    unfold S4; simp only [rsum_add]
  have s0 := posP3 n c y z t P hR1 hR2a hR2b hR3a hR3b hR3c a0 a1 a2 i b0 b1 b2 ha0 ha1 ha2 hi
  have s1 := posP2 n c y z t P hR1 hR2a hR2b hR3a hR3b hR3c a0 a1 i a2 b0 b1 b2 ha0 ha1 hi ha2
  have s2 := posP3 n c y z t P hR1 hR2a hR2b hR3a hR3b hR3c a0 a2 a1 i b0 b2 b1 ha0 ha2 ha1 hi
  have s3 := posP2 n c y z t P hR1 hR2a hR2b hR3a hR3b hR3c a0 a2 i a1 b0 b2 b1 ha0 ha2 hi ha1
  have s4 := posP1 n c y z t P hR1 hR2a hR2b hR3a hR3b hR3c a0 i a1 a2 b0 b1 b2 ha0 hi ha1 ha2
  have s5 := posP1 n c y z t P hR1 hR2a hR2b hR3a hR3b hR3c a0 i a2 a1 b0 b2 b1 ha0 hi ha2 ha1
  have s6 := posP3 n c y z t P hR1 hR2a hR2b hR3a hR3b hR3c a1 a0 a2 i b1 b0 b2 ha1 ha0 ha2 hi
  have s7 := posP2 n c y z t P hR1 hR2a hR2b hR3a hR3b hR3c a1 a0 i a2 b1 b0 b2 ha1 ha0 hi ha2
  have s8 := posP3 n c y z t P hR1 hR2a hR2b hR3a hR3b hR3c a1 a2 a0 i b1 b2 b0 ha1 ha2 ha0 hi
  have s9 := posP2 n c y z t P hR1 hR2a hR2b hR3a hR3b hR3c a1 a2 i a0 b1 b2 b0 ha1 ha2 hi ha0
  have s10 := posP1 n c y z t P hR1 hR2a hR2b hR3a hR3b hR3c a1 i a0 a2 b1 b0 b2 ha1 hi ha0 ha2
  have s11 := posP1 n c y z t P hR1 hR2a hR2b hR3a hR3b hR3c a1 i a2 a0 b1 b2 b0 ha1 hi ha2 ha0
  have s12 := posP3 n c y z t P hR1 hR2a hR2b hR3a hR3b hR3c a2 a0 a1 i b2 b0 b1 ha2 ha0 ha1 hi
  have s13 := posP2 n c y z t P hR1 hR2a hR2b hR3a hR3b hR3c a2 a0 i a1 b2 b0 b1 ha2 ha0 hi ha1
  have s14 := posP3 n c y z t P hR1 hR2a hR2b hR3a hR3b hR3c a2 a1 a0 i b2 b1 b0 ha2 ha1 ha0 hi
  have s15 := posP2 n c y z t P hR1 hR2a hR2b hR3a hR3b hR3c a2 a1 i a0 b2 b1 b0 ha2 ha1 hi ha0
  have s16 := posP1 n c y z t P hR1 hR2a hR2b hR3a hR3b hR3c a2 i a0 a1 b2 b0 b1 ha2 hi ha0 ha1
  have s17 := posP1 n c y z t P hR1 hR2a hR2b hR3a hR3b hR3c a2 i a1 a0 b2 b1 b0 ha2 hi ha1 ha0
  have s18 := posP0 n c y z t P hR1 hR2a hR2b hR3a hR3b hR3c i a0 a1 a2 b0 b1 b2 hi ha0 ha1 ha2
  have s19 := posP0 n c y z t P hR1 hR2a hR2b hR3a hR3b hR3c i a0 a2 a1 b0 b2 b1 hi ha0 ha2 ha1
  have s20 := posP0 n c y z t P hR1 hR2a hR2b hR3a hR3b hR3c i a1 a0 a2 b1 b0 b2 hi ha1 ha0 ha2
  have s21 := posP0 n c y z t P hR1 hR2a hR2b hR3a hR3b hR3c i a1 a2 a0 b1 b2 b0 hi ha1 ha2 ha0
  have s22 := posP0 n c y z t P hR1 hR2a hR2b hR3a hR3b hR3c i a2 a0 a1 b2 b0 b1 hi ha2 ha0 ha1
  have s23 := posP0 n c y z t P hR1 hR2a hR2b hR3a hR3b hR3c i a2 a1 a0 b2 b1 b0 hi ha2 ha1 ha0
  have hid := pig_ident4 n c y z t hzs ht12 ht23 hzc htc12 htc13 htc23 a0 a1 a2 i b0 b1 b2 hr0 hr1 hr2 hr3 hr4 hr5 hc0 hc1 hc2 hb0 hb1 hb2
  rw [hsum]
  have hT := Int.dvd_add (Int.dvd_add (Int.dvd_add (Int.dvd_add (Int.dvd_add (Int.dvd_add (Int.dvd_add (Int.dvd_add (Int.dvd_add (Int.dvd_add (Int.dvd_add (Int.dvd_add (Int.dvd_add (Int.dvd_add (Int.dvd_add (Int.dvd_add (Int.dvd_add (Int.dvd_add (Int.dvd_add (Int.dvd_add (Int.dvd_add (Int.dvd_add (Int.dvd_add (s0) s1) s2) s3) s4) s5) s6) s7) s8) s9) s10) s11) s12) s13) s14) s15) s16) s17) s18) s19) s20) s21) s22) s23
  refine (Int.dvd_iff_dvd_of_dvd_sub ?_).mp hT
  refine ⟨0, ?_⟩
  generalize M4 n * t (var n a0 b0) (var n a1 b1) (var n a2 b2) = X at hid ⊢
  omega

theorem hole_total (n : Nat) (c : Int) (y : Nat → Int) (z : Nat → Nat → Int) (t : Nat → Nat → Nat → Int)
    (hzs : ∀ v w, z v w = z w v) (ht12 : ∀ u v w, t u v w = t v u w) (ht23 : ∀ u v w, t u v w = t u w v)
    (hzr : ∀ a b b', b < n → b' < n → b ≠ b' → z (var n a b) (var n a b') = 0)
    (htr12 : ∀ a b b' x, b < n → b' < n → b ≠ b' → t (var n a b) (var n a b') x = 0)
    (htr13 : ∀ a b b' x, b < n → b' < n → b ≠ b' → t (var n a b) x (var n a b') = 0)
    (htr23 : ∀ a b b' x, b < n → b' < n → b ≠ b' → t x (var n a b) (var n a b') = 0)
    (k : Nat) (hk : (p : Int) ∣ (k : Int))
    (hC1 : ∀ j < n, (p : Int) ∣ rsum (n + k) (fun i => y (var n i j)) - c)
    (hC2a : ∀ v, ∀ j < n, (p : Int) ∣ rsum (n + k) (fun i => z (var n i j) v) - y v)
    (hC2b : ∀ v, ∀ j < n, (p : Int) ∣ rsum (n + k) (fun i => z v (var n i j)) - y v)
    (hC3a : ∀ v w, ∀ j < n, (p : Int) ∣ rsum (n + k) (fun i => t (var n i j) v w) - z v w)
    (hC3b : ∀ v w, ∀ j < n, (p : Int) ∣ rsum (n + k) (fun i => t v (var n i j) w) - z v w)
    (hC3c : ∀ v w, ∀ j < n, (p : Int) ∣ rsum (n + k) (fun i => t v w (var n i j)) - z v w)
    (a0 a1 a2 b0 b1 b2 j : Nat)
    (hr0 : a0 ≠ a1) (hr1 : a0 ≠ a2) (hr2 : a1 ≠ a2) (hc0 : b0 ≠ b1) (hc1 : b0 ≠ b2) (hc2 : b1 ≠ b2) (hc3 : b0 ≠ j) (hc4 : b1 ≠ j) (hc5 : b2 ≠ j)
    (hb0 : b0 < n) (hb1 : b1 < n) (hb2 : b2 < n) (hj : j < n) :
    (p : Int) ∣ rsum (n + k) (fun i => S4 n c y z t a0 a1 a2 i b0 b1 b2 j) - (S4 n c y z t a0 a1 a2 a0 b0 b1 b2 j + S4 n c y z t a0 a1 a2 a1 b0 b1 b2 j + S4 n c y z t a0 a1 a2 a2 b0 b1 b2 j + M4 n * t (var n a0 b0) (var n a1 b1) (var n a2 b2)) := by
  have hsum : rsum (n + k) (fun i => S4 n c y z t a0 a1 a2 i b0 b1 b2 j) = rsum (n + k) (fun i => Gp4 n c y z t a0 a1 a2 i b0 b1 b2 j) + rsum (n + k) (fun i => Gp4 n c y z t a0 a1 i a2 b0 b1 j b2) + rsum (n + k) (fun i => Gp4 n c y z t a0 a2 a1 i b0 b2 b1 j) + rsum (n + k) (fun i => Gp4 n c y z t a0 a2 i a1 b0 b2 j b1) + rsum (n + k) (fun i => Gp4 n c y z t a0 i a1 a2 b0 j b1 b2) + rsum (n + k) (fun i => Gp4 n c y z t a0 i a2 a1 b0 j b2 b1) + rsum (n + k) (fun i => Gp4 n c y z t a1 a0 a2 i b1 b0 b2 j) + rsum (n + k) (fun i => Gp4 n c y z t a1 a0 i a2 b1 b0 j b2) + rsum (n + k) (fun i => Gp4 n c y z t a1 a2 a0 i b1 b2 b0 j) + rsum (n + k) (fun i => Gp4 n c y z t a1 a2 i a0 b1 b2 j b0) + rsum (n + k) (fun i => Gp4 n c y z t a1 i a0 a2 b1 j b0 b2) + rsum (n + k) (fun i => Gp4 n c y z t a1 i a2 a0 b1 j b2 b0) + rsum (n + k) (fun i => Gp4 n c y z t a2 a0 a1 i b2 b0 b1 j) + rsum (n + k) (fun i => Gp4 n c y z t a2 a0 i a1 b2 b0 j b1) + rsum (n + k) (fun i => Gp4 n c y z t a2 a1 a0 i b2 b1 b0 j) + rsum (n + k) (fun i => Gp4 n c y z t a2 a1 i a0 b2 b1 j b0) + rsum (n + k) (fun i => Gp4 n c y z t a2 i a0 a1 b2 j b0 b1) + rsum (n + k) (fun i => Gp4 n c y z t a2 i a1 a0 b2 j b1 b0) + rsum (n + k) (fun i => Gp4 n c y z t i a0 a1 a2 j b0 b1 b2) + rsum (n + k) (fun i => Gp4 n c y z t i a0 a2 a1 j b0 b2 b1) + rsum (n + k) (fun i => Gp4 n c y z t i a1 a0 a2 j b1 b0 b2) + rsum (n + k) (fun i => Gp4 n c y z t i a1 a2 a0 j b1 b2 b0) + rsum (n + k) (fun i => Gp4 n c y z t i a2 a0 a1 j b2 b0 b1) + rsum (n + k) (fun i => Gp4 n c y z t i a2 a1 a0 j b2 b1 b0) := by
    unfold S4; simp only [rsum_add]
  have s0 := posH3 n c y z t k hk a0 a1 a2 b0 b1 b2 j
  have s1 := posH2 n c y z t k hk hC1 hC2a hC2b hC3a hC3b hC3c a0 a1 a2 b0 b1 j b2 hb0 hb1 hj hb2
  have s2 := posH3 n c y z t k hk a0 a2 a1 b0 b2 b1 j
  have s3 := posH2 n c y z t k hk hC1 hC2a hC2b hC3a hC3b hC3c a0 a2 a1 b0 b2 j b1 hb0 hb2 hj hb1
  have s4 := posH1 n c y z t k hk hC1 hC2a hC2b hC3a hC3b hC3c a0 a1 a2 b0 j b1 b2 hb0 hj hb1 hb2
  have s5 := posH1 n c y z t k hk hC1 hC2a hC2b hC3a hC3b hC3c a0 a2 a1 b0 j b2 b1 hb0 hj hb2 hb1
  have s6 := posH3 n c y z t k hk a1 a0 a2 b1 b0 b2 j
  have s7 := posH2 n c y z t k hk hC1 hC2a hC2b hC3a hC3b hC3c a1 a0 a2 b1 b0 j b2 hb1 hb0 hj hb2
  have s8 := posH3 n c y z t k hk a1 a2 a0 b1 b2 b0 j
  have s9 := posH2 n c y z t k hk hC1 hC2a hC2b hC3a hC3b hC3c a1 a2 a0 b1 b2 j b0 hb1 hb2 hj hb0
  have s10 := posH1 n c y z t k hk hC1 hC2a hC2b hC3a hC3b hC3c a1 a0 a2 b1 j b0 b2 hb1 hj hb0 hb2
  have s11 := posH1 n c y z t k hk hC1 hC2a hC2b hC3a hC3b hC3c a1 a2 a0 b1 j b2 b0 hb1 hj hb2 hb0
  have s12 := posH3 n c y z t k hk a2 a0 a1 b2 b0 b1 j
  have s13 := posH2 n c y z t k hk hC1 hC2a hC2b hC3a hC3b hC3c a2 a0 a1 b2 b0 j b1 hb2 hb0 hj hb1
  have s14 := posH3 n c y z t k hk a2 a1 a0 b2 b1 b0 j
  have s15 := posH2 n c y z t k hk hC1 hC2a hC2b hC3a hC3b hC3c a2 a1 a0 b2 b1 j b0 hb2 hb1 hj hb0
  have s16 := posH1 n c y z t k hk hC1 hC2a hC2b hC3a hC3b hC3c a2 a0 a1 b2 j b0 b1 hb2 hj hb0 hb1
  have s17 := posH1 n c y z t k hk hC1 hC2a hC2b hC3a hC3b hC3c a2 a1 a0 b2 j b1 b0 hb2 hj hb1 hb0
  have s18 := posH0 n c y z t k hk hC1 hC2a hC2b hC3a hC3b hC3c a0 a1 a2 j b0 b1 b2 hj hb0 hb1 hb2
  have s19 := posH0 n c y z t k hk hC1 hC2a hC2b hC3a hC3b hC3c a0 a2 a1 j b0 b2 b1 hj hb0 hb2 hb1
  have s20 := posH0 n c y z t k hk hC1 hC2a hC2b hC3a hC3b hC3c a1 a0 a2 j b1 b0 b2 hj hb1 hb0 hb2
  have s21 := posH0 n c y z t k hk hC1 hC2a hC2b hC3a hC3b hC3c a1 a2 a0 j b1 b2 b0 hj hb1 hb2 hb0
  have s22 := posH0 n c y z t k hk hC1 hC2a hC2b hC3a hC3b hC3c a2 a0 a1 j b2 b0 b1 hj hb2 hb0 hb1
  have s23 := posH0 n c y z t k hk hC1 hC2a hC2b hC3a hC3b hC3c a2 a1 a0 j b2 b1 b0 hj hb2 hb1 hb0
  have hid := hole_ident4 n c y z t hzs ht12 ht23 hzr htr12 htr13 htr23 a0 a1 a2 b0 b1 b2 j hr0 hr1 hr2 hc0 hc1 hc2 hc3 hc4 hc5 hb0 hb1 hb2 hj
  rw [hsum]
  have hT := Int.dvd_add (Int.dvd_add (Int.dvd_add (Int.dvd_add (Int.dvd_add (Int.dvd_add (Int.dvd_add (Int.dvd_add (Int.dvd_add (Int.dvd_add (Int.dvd_add (Int.dvd_add (Int.dvd_add (Int.dvd_add (Int.dvd_add (Int.dvd_add (Int.dvd_add (Int.dvd_add (Int.dvd_add (Int.dvd_add (Int.dvd_add (Int.dvd_add (Int.dvd_add (s0) s1) s2) s3) s4) s5) s6) s7) s8) s9) s10) s11) s12) s13) s14) s15) s16) s17) s18) s19) s20) s21) s22) s23
  refine (Int.dvd_iff_dvd_of_dvd_sub ?_).mp hT
  refine ⟨0, ?_⟩
  generalize M4 n * t (var n a0 b0) (var n a1 b1) (var n a2 b2) = X at hid ⊢
  omega

end Programme.«20261025-1627-proof-complexity».Ext4Alg
