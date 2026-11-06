import Programme.«20261025-1627-proof-complexity».OntoExt2

/-!
# Degree-3 extension for onto-FPHP: the algebra

Abstract moments `c`, `y v`, `z v w` (to be read off a degree-2 design). The level-3 moment of a
3-matching `{(a₁,b₁),(a₂,b₂),(a₃,b₃)}` is `u · S3`, where `S3` sums the per-ordering term `Gp` over
the six orderings of the edges and `u · 6n(n-1)(n-2)(n-3)(n-4) ≡ 1`. The six summation lemmas use
only the row sums `∑_j y(i,j) ≡ c`, `∑_j z(v,(i,j)) ≡ y v` (pigeon side) and the column sums
(hole side, with `p ∣ k`); the closing identities `pig_ident`, `hole_ident` are exact.
-/

namespace Programme.«20261025-1627-proof-complexity».Ext3Alg

open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-0459-proof-complexity».OntoSubst (rsum_congr)
open Programme.«20261025-1627-proof-complexity».DesignExt (dvd_cmul)

variable {p : Nat}

def H0 (n : Nat) : Int := (n : Int) * ((n : Int) - 1)
def H1 (n : Nat) : Int := -3 * (n : Int) * ((n : Int) - 2) * ((n : Int) - 3)
def H2 (n : Nat) : Int := -6 * (n : Int) * ((n : Int) - 2)
def H3 (n : Nat) : Int := 3 * ((n : Int) - 2) * ((n : Int) - 2) * ((n : Int) * (n : Int) - 4 * (n : Int) + 1)
def H4 (n : Nat) : Int := 6 * ((n : Int) - 2) * ((n : Int) * (n : Int) - 4 * (n : Int) + 2)
def H5 (n : Nat) : Int := 6 * ((n : Int) - 2)
def H6 (n : Nat) : Int := 6 * ((n : Int) - 2) * ((n : Int) - 2)
def M3 (n : Nat) : Int :=
  6 * (n : Int) * ((n : Int) - 1) * ((n : Int) - 2) * ((n : Int) - 3) * ((n : Int) - 4)

/-- Per-ordering term for the ordered edges `(a₁,b₁), (a₂,b₂), (·,b₃)`. -/
def Gp (n : Nat) (c : Int) (y : Nat → Int) (z : Nat → Nat → Int) (a1 a2 b1 b2 b3 : Nat) : Int :=
  H0 n * c + H1 n * y (var n a1 b1) + H2 n * y (var n a1 b2) + H3 n * z (var n a1 b1) (var n a2 b2) +
    H4 n * z (var n a1 b1) (var n a2 b3) + H5 n * z (var n a1 b2) (var n a2 b1) +
    H6 n * z (var n a1 b2) (var n a2 b3)

/-- Sum over the six orderings of the edges `(a₁,b₁), (a₂,b₂), (a₃,b₃)`. -/
def S3 (n : Nat) (c : Int) (y : Nat → Int) (z : Nat → Nat → Int) (a1 a2 a3 b1 b2 b3 : Nat) : Int :=
  Gp n c y z a1 a2 b1 b2 b3 + Gp n c y z a1 a3 b1 b3 b2 + Gp n c y z a2 a1 b2 b1 b3 +
    Gp n c y z a2 a3 b2 b3 b1 + Gp n c y z a3 a1 b3 b1 b2 + Gp n c y z a3 a2 b3 b2 b1

theorem S3_swap12 (n : Nat) (c : Int) (y : Nat → Int) (z : Nat → Nat → Int) (a1 a2 a3 b1 b2 b3 : Nat) :
    S3 n c y z a1 a2 a3 b1 b2 b3 = S3 n c y z a2 a1 a3 b2 b1 b3 := by
  unfold S3; omega

theorem S3_swap23 (n : Nat) (c : Int) (y : Nat → Int) (z : Nat → Nat → Int) (a1 a2 a3 b1 b2 b3 : Nat) :
    S3 n c y z a1 a2 a3 b1 b2 b3 = S3 n c y z a1 a3 a2 b1 b3 b2 := by
  unfold S3; omega

/-! ## Sums -/

theorem rsum_k4 (m : Nat) (K A1 A2 A3 A4 : Int) (f1 f2 f3 f4 : Nat → Int) :
    rsum m (fun j => K + A1 * f1 j + A2 * f2 j + A3 * f3 j + A4 * f4 j) =
      (m : Int) * K + A1 * rsum m f1 + A2 * rsum m f2 + A3 * rsum m f3 + A4 * rsum m f4 := by
  induction m with
  | zero => simp [rsum]
  | succ m ih => simp only [rsum, ih]; push_cast; grind

theorem rsum_k2 (m : Nat) (K A1 A2 : Int) (f1 f2 : Nat → Int) :
    rsum m (fun j => K + A1 * f1 j + A2 * f2 j) = (m : Int) * K + A1 * rsum m f1 + A2 * rsum m f2 := by
  induction m with
  | zero => simp [rsum]
  | succ m ih => simp only [rsum, ih]; push_cast; grind

theorem rsum_k6 (m : Nat) (K A1 A2 A3 A4 A5 A6 : Int) (f1 f2 f3 f4 f5 f6 : Nat → Int) :
    rsum m (fun j => K + A1 * f1 j + A2 * f2 j + A3 * f3 j + A4 * f4 j + A5 * f5 j + A6 * f6 j) =
      (m : Int) * K + A1 * rsum m f1 + A2 * rsum m f2 + A3 * rsum m f3 + A4 * rsum m f4 +
        A5 * rsum m f5 + A6 * rsum m f6 := by
  induction m with
  | zero => simp [rsum]
  | succ m ih => simp only [rsum, ih]; push_cast; grind

theorem lin2_dvd (P K A1 A2 s1 s2 v1 v2 : Int) (h1 : P ∣ s1 - v1) (h2 : P ∣ s2 - v2) :
    P ∣ (K + A1 * s1 + A2 * s2) - (K + A1 * v1 + A2 * v2) := by
  have e : (K + A1 * s1 + A2 * s2) - (K + A1 * v1 + A2 * v2) = A1 * (s1 - v1) + A2 * (s2 - v2) := by grind
  rw [e]; exact Int.dvd_add (dvd_cmul _ h1) (dvd_cmul _ h2)

theorem lin6_dvd (P K A1 A2 A3 A4 A5 A6 s1 s2 s3 s4 s5 s6 v1 v2 v3 v4 v5 v6 : Int) (h1 : P ∣ s1 - v1)
    (h2 : P ∣ s2 - v2) (h3 : P ∣ s3 - v3) (h4 : P ∣ s4 - v4) (h5 : P ∣ s5 - v5) (h6 : P ∣ s6 - v6) :
    P ∣ (K + A1 * s1 + A2 * s2 + A3 * s3 + A4 * s4 + A5 * s5 + A6 * s6) -
      (K + A1 * v1 + A2 * v2 + A3 * v3 + A4 * v4 + A5 * v5 + A6 * v6) := by
  have e : (K + A1 * s1 + A2 * s2 + A3 * s3 + A4 * s4 + A5 * s5 + A6 * s6) -
      (K + A1 * v1 + A2 * v2 + A3 * v3 + A4 * v4 + A5 * v5 + A6 * v6) =
      A1 * (s1 - v1) + A2 * (s2 - v2) + A3 * (s3 - v3) + A4 * (s4 - v4) + A5 * (s5 - v5) + A6 * (s6 - v6) := by
    grind
  rw [e]
  exact Int.dvd_add (Int.dvd_add (Int.dvd_add (Int.dvd_add (Int.dvd_add (dvd_cmul _ h1) (dvd_cmul _ h2))
    (dvd_cmul _ h3)) (dvd_cmul _ h4)) (dvd_cmul _ h5)) (dvd_cmul _ h6)

theorem lin4_dvd (P K A1 A2 A3 A4 s1 s2 s3 s4 v1 v2 v3 v4 : Int) (h1 : P ∣ s1 - v1) (h2 : P ∣ s2 - v2)
    (h3 : P ∣ s3 - v3) (h4 : P ∣ s4 - v4) :
    P ∣ (K + A1 * s1 + A2 * s2 + A3 * s3 + A4 * s4) - (K + A1 * v1 + A2 * v2 + A3 * v3 + A4 * v4) := by
  have e : (K + A1 * s1 + A2 * s2 + A3 * s3 + A4 * s4) - (K + A1 * v1 + A2 * v2 + A3 * v3 + A4 * v4) =
      A1 * (s1 - v1) + A2 * (s2 - v2) + A3 * (s3 - v3) + A4 * (s4 - v4) := by grind
  rw [e]
  exact Int.dvd_add (Int.dvd_add (Int.dvd_add (dvd_cmul _ h1) (dvd_cmul _ h2)) (dvd_cmul _ h3)) (dvd_cmul _ h4)

theorem rsum_ext_dvd (m : Nat) (f g : Nat → Int) (X : Int) (h : ∀ j < m, f j = g j)
    (hg : (p : Int) ∣ rsum m g - X) : (p : Int) ∣ rsum m f - X := by
  rw [rsum_congr m f g h]; exact hg

section
variable (n : Nat) (c : Int) (y : Nat → Int) (z : Nat → Nat → Int)

/-! Pigeon side: the new edge is `(i, j)`, `j` summed over `n` holes. -/

theorem pos3 (P : Nat) (hR2 : ∀ v, ∀ i < P, (p : Int) ∣ rsum n (fun j => z v (var n i j)) - y v)
    (a1 a2 b1 b2 : Nat) (ha2 : a2 < P) :
    (p : Int) ∣ rsum n (fun j => Gp n c y z a1 a2 b1 b2 j) -
      ((n : Int) * (H0 n * c + H1 n * y (var n a1 b1) + H2 n * y (var n a1 b2) +
        H3 n * z (var n a1 b1) (var n a2 b2) + H5 n * z (var n a1 b2) (var n a2 b1)) +
        H4 n * y (var n a1 b1) + H6 n * y (var n a1 b2)) := by
  apply rsum_ext_dvd n _ (fun j => (H0 n * c + H1 n * y (var n a1 b1) + H2 n * y (var n a1 b2) +
        H3 n * z (var n a1 b1) (var n a2 b2) + H5 n * z (var n a1 b2) (var n a2 b1)) +
      H4 n * z (var n a1 b1) (var n a2 j) + H6 n * z (var n a1 b2) (var n a2 j)) _ (fun j _ => by unfold Gp; grind)
  rw [rsum_k2]
  exact lin2_dvd p _ _ _ _ _ _ _ (hR2 _ a2 ha2) (hR2 _ a2 ha2)

theorem pos1 (hzs : ∀ v w, z v w = z w v) (P : Nat) (hR1 : ∀ i < P, (p : Int) ∣ rsum n (fun j => y (var n i j)) - c)
    (hR2 : ∀ v, ∀ i < P, (p : Int) ∣ rsum n (fun j => z v (var n i j)) - y v)
    (i a1 b1 b2 : Nat) (hi : i < P) (ha1 : a1 < P) :
    (p : Int) ∣ rsum n (fun j => Gp n c y z i a1 j b1 b2) -
      ((n : Int) * (H0 n * c + H2 n * y (var n i b1) + H6 n * z (var n i b1) (var n a1 b2)) +
        H1 n * c + H3 n * y (var n a1 b1) + H4 n * y (var n a1 b2) + H5 n * y (var n i b1)) := by
  apply rsum_ext_dvd n _ (fun j => (H0 n * c + H2 n * y (var n i b1) + H6 n * z (var n i b1) (var n a1 b2)) +
      H1 n * y (var n i j) + H3 n * z (var n a1 b1) (var n i j) + H4 n * z (var n a1 b2) (var n i j) +
      H5 n * z (var n i b1) (var n a1 j)) _ (fun j _ => by
        unfold Gp; rw [hzs (var n i j) (var n a1 b1), hzs (var n i j) (var n a1 b2)]; grind)
  rw [rsum_k4]
  exact lin4_dvd p _ _ _ _ _ _ _ _ _ _ _ _ _ (hR1 i hi) (hR2 _ i hi) (hR2 _ i hi) (hR2 _ a1 ha1)

theorem pos2 (hzs : ∀ v w, z v w = z w v) (P : Nat) (hR1 : ∀ i < P, (p : Int) ∣ rsum n (fun j => y (var n i j)) - c)
    (hR2 : ∀ v, ∀ i < P, (p : Int) ∣ rsum n (fun j => z v (var n i j)) - y v)
    (a1 i b1 b2 : Nat) (hi : i < P) (ha1 : a1 < P) :
    (p : Int) ∣ rsum n (fun j => Gp n c y z a1 i b1 j b2) -
      ((n : Int) * (H0 n * c + H1 n * y (var n a1 b1) + H4 n * z (var n a1 b1) (var n i b2)) +
        H2 n * c + H3 n * y (var n a1 b1) + H5 n * y (var n i b1) + H6 n * y (var n i b2)) := by
  apply rsum_ext_dvd n _ (fun j => (H0 n * c + H1 n * y (var n a1 b1) + H4 n * z (var n a1 b1) (var n i b2)) +
      H2 n * y (var n a1 j) + H3 n * z (var n a1 b1) (var n i j) + H5 n * z (var n i b1) (var n a1 j) +
      H6 n * z (var n i b2) (var n a1 j)) _ (fun j _ => by
        unfold Gp; rw [hzs (var n a1 j) (var n i b1), hzs (var n a1 j) (var n i b2)]; grind)
  rw [rsum_k4]
  exact lin4_dvd p _ _ _ _ _ _ _ _ _ _ _ _ _ (hR1 a1 ha1) (hR2 _ i hi) (hR2 _ a1 ha1) (hR2 _ a1 ha1)

/-! Hole side: the new edge is `(i, j)`, `i` summed over `n + k` pigeons; `p ∣ k`. -/

theorem dvd_k (k : Nat) (hk : (p : Int) ∣ (k : Int)) (K X : Int) (h : (p : Int) ∣ X - (((n + k : Nat) : Int) * K)) :
    (p : Int) ∣ X - (n : Int) * K := by
  have e : X - (n : Int) * K = (X - (((n + k : Nat) : Int) * K)) + (k : Int) * K := by push_cast; grind
  rw [e]; exact Int.dvd_add h (by obtain ⟨q, hq⟩ := hk; exact ⟨q * K, by rw [hq]; grind⟩)

theorem dvd_k' (k : Nat) (hk : (p : Int) ∣ (k : Int)) (K R X : Int)
    (h : (p : Int) ∣ X - (((n + k : Nat) : Int) * K + R)) : (p : Int) ∣ X - ((n : Int) * K + R) := by
  have e : X - ((n : Int) * K + R) = (X - (((n + k : Nat) : Int) * K + R)) + (k : Int) * K := by push_cast; grind
  rw [e]; exact Int.dvd_add h (by obtain ⟨q, hq⟩ := hk; exact ⟨q * K, by rw [hq]; grind⟩)

theorem pos3h (k : Nat) (hk : (p : Int) ∣ (k : Int)) (a1 a2 b1 b2 j : Nat) :
    (p : Int) ∣ rsum (n + k) (fun _ => Gp n c y z a1 a2 b1 b2 j) - (n : Int) * Gp n c y z a1 a2 b1 b2 j := by
  apply dvd_k n k hk
  rw [Programme.«20261025-1627-proof-complexity».OntoExt2.rsum_const, Int.sub_self]; exact ⟨0, by simp⟩

theorem pos1h (hzs : ∀ v w, z v w = z w v) (k : Nat) (hk : (p : Int) ∣ (k : Int))
    (hC1 : ∀ j < n, (p : Int) ∣ rsum (n + k) (fun i => y (var n i j)) - c)
    (hC2 : ∀ v, ∀ j < n, (p : Int) ∣ rsum (n + k) (fun i => z v (var n i j)) - y v)
    (a1 j b1 b2 : Nat) (hj : j < n) (hb1 : b1 < n) :
    (p : Int) ∣ rsum (n + k) (fun i => Gp n c y z i a1 j b1 b2) -
      ((n : Int) * (H0 n * c) + (H1 n * c + H2 n * c + H3 n * y (var n a1 b1) + H4 n * y (var n a1 b2) +
        H5 n * y (var n a1 j) + H6 n * y (var n a1 b2))) := by
  apply dvd_k' n k hk
  apply rsum_ext_dvd (n + k) _ (fun i => H0 n * c + H1 n * y (var n i j) + H2 n * y (var n i b1) +
      H3 n * z (var n a1 b1) (var n i j) + H4 n * z (var n a1 b2) (var n i j) +
      H5 n * z (var n a1 j) (var n i b1) + H6 n * z (var n a1 b2) (var n i b1)) _ (fun i _ => by
    unfold Gp
    rw [hzs (var n i j) (var n a1 b1), hzs (var n i j) (var n a1 b2), hzs (var n i b1) (var n a1 j),
      hzs (var n i b1) (var n a1 b2)])
  rw [rsum_k6]
  have := lin6_dvd p (((n + k : Nat) : Int) * (H0 n * c)) (H1 n) (H2 n) (H3 n) (H4 n) (H5 n) (H6 n) _ _ _ _ _ _ c c
    (y (var n a1 b1)) (y (var n a1 b2)) (y (var n a1 j)) (y (var n a1 b2)) (hC1 j hj) (hC1 b1 hb1)
    (hC2 (var n a1 b1) j hj) (hC2 (var n a1 b2) j hj) (hC2 (var n a1 j) b1 hb1) (hC2 (var n a1 b2) b1 hb1)
  refine (Int.dvd_iff_dvd_of_dvd_sub ?_).mp this
  exact ⟨0, by grind⟩

theorem pos2h (k : Nat) (hk : (p : Int) ∣ (k : Int))
    (hC1 : ∀ j < n, (p : Int) ∣ rsum (n + k) (fun i => y (var n i j)) - c)
    (hC2 : ∀ v, ∀ j < n, (p : Int) ∣ rsum (n + k) (fun i => z v (var n i j)) - y v)
    (a1 b1 j b2 : Nat) (hj : j < n) (hb2 : b2 < n) (hb1 : b1 < n) :
    (p : Int) ∣ rsum (n + k) (fun i => Gp n c y z a1 i b1 j b2) -
      ((n : Int) * (H0 n * c + H1 n * y (var n a1 b1) + H2 n * y (var n a1 j)) +
        (H3 n * y (var n a1 b1) + H4 n * y (var n a1 b1) + H5 n * y (var n a1 j) + H6 n * y (var n a1 j))) := by
  apply dvd_k' n k hk
  apply rsum_ext_dvd (n + k) _ (fun i => (H0 n * c + H1 n * y (var n a1 b1) + H2 n * y (var n a1 j)) +
      H3 n * z (var n a1 b1) (var n i j) + H4 n * z (var n a1 b1) (var n i b2) +
      H5 n * z (var n a1 j) (var n i b1) + H6 n * z (var n a1 j) (var n i b2)) _ (fun i _ => by unfold Gp; grind)
  rw [rsum_k4]
  have := lin4_dvd p (((n + k : Nat) : Int) * (H0 n * c + H1 n * y (var n a1 b1) + H2 n * y (var n a1 j))) (H3 n) (H4 n) (H5 n) (H6 n) _ _ _ _ _ _ _ _ (hC2 (var n a1 b1) j hj) (hC2 (var n a1 b1) b2 hb2)
    (hC2 (var n a1 j) b1 hb1) (hC2 (var n a1 j) b2 hb2)
  refine (Int.dvd_iff_dvd_of_dvd_sub ?_).mp this
  exact ⟨0, by grind⟩

end

/-! ## Closing identities (exact) -/

/-- Right-hand sides of the summation lemmas. -/
def R3 (n : Nat) (c : Int) (y : Nat → Int) (z : Nat → Nat → Int) (a1 a2 b1 b2 : Nat) : Int :=
  (n : Int) * (H0 n * c + H1 n * y (var n a1 b1) + H2 n * y (var n a1 b2) +
    H3 n * z (var n a1 b1) (var n a2 b2) + H5 n * z (var n a1 b2) (var n a2 b1)) +
    H4 n * y (var n a1 b1) + H6 n * y (var n a1 b2)
def R1 (n : Nat) (c : Int) (y : Nat → Int) (z : Nat → Nat → Int) (i a1 b1 b2 : Nat) : Int :=
  (n : Int) * (H0 n * c + H2 n * y (var n i b1) + H6 n * z (var n i b1) (var n a1 b2)) +
    H1 n * c + H3 n * y (var n a1 b1) + H4 n * y (var n a1 b2) + H5 n * y (var n i b1)
def R2 (n : Nat) (c : Int) (y : Nat → Int) (z : Nat → Nat → Int) (a1 i b1 b2 : Nat) : Int :=
  (n : Int) * (H0 n * c + H1 n * y (var n a1 b1) + H4 n * z (var n a1 b1) (var n i b2)) +
    H2 n * c + H3 n * y (var n a1 b1) + H5 n * y (var n i b1) + H6 n * y (var n i b2)
def R1h (n : Nat) (c : Int) (y : Nat → Int) (a1 j b1 b2 : Nat) : Int :=
  (n : Int) * (H0 n * c) + (H1 n * c + H2 n * c + H3 n * y (var n a1 b1) + H4 n * y (var n a1 b2) +
    H5 n * y (var n a1 j) + H6 n * y (var n a1 b2))
def R2h (n : Nat) (c : Int) (y : Nat → Int) (a1 b1 j : Nat) : Int :=
  (n : Int) * (H0 n * c + H1 n * y (var n a1 b1) + H2 n * y (var n a1 j)) +
    (H3 n * y (var n a1 b1) + H4 n * y (var n a1 b1) + H5 n * y (var n a1 j) + H6 n * y (var n a1 j))

theorem pig_ident (n : Nat) (c : Int) (y : Nat → Int) (z : Nat → Nat → Int) (hzs : ∀ v w, z v w = z w v)
    (hcp : ∀ a a' b, b < n → a ≠ a' → z (var n a b) (var n a' b) = 0)
    (hch : ∀ a b b', b < n → b' < n → b ≠ b' → z (var n a b) (var n a b') = 0)
    (a1 a2 i b1 b2 : Nat) (h12 : a1 ≠ a2) (h1i : a1 ≠ i) (h2i : a2 ≠ i) (hb : b1 ≠ b2) (hb1n : b1 < n) (hb2n : b2 < n) :
    R3 n c y z a1 a2 b1 b2 + R2 n c y z a1 i b1 b2 + R3 n c y z a2 a1 b2 b1 + R2 n c y z a2 i b2 b1 +
      R1 n c y z i a1 b1 b2 + R1 n c y z i a2 b2 b1 -
      S3 n c y z a1 a2 i b1 b2 b1 - S3 n c y z a1 a2 i b1 b2 b2 = M3 n * z (var n a1 b1) (var n a2 b2) := by
  have h21 := Ne.symm h12; have hi1 := Ne.symm h1i; have hi2 := Ne.symm h2i; have hb' := Ne.symm hb
  unfold R3 R2 R1 S3 Gp
  simp only [hcp _ _ b1 hb1n h12, hcp _ _ b2 hb2n h12, hcp _ _ b1 hb1n h21, hcp _ _ b2 hb2n h21, hcp _ _ b1 hb1n h1i, hcp _ _ b2 hb2n h1i, hcp _ _ b1 hb1n hi1, hcp _ _ b2 hb2n hi1, hcp _ _ b1 hb1n h2i, hcp _ _ b2 hb2n h2i, hcp _ _ b1 hb1n hi2, hcp _ _ b2 hb2n hi2]
  have := hzs (var n a1 b1) (var n a1 b2)
  have := hzs (var n a1 b1) (var n a2 b1)
  have := hzs (var n a1 b1) (var n a2 b2)
  have := hzs (var n a1 b1) (var n i b1)
  have := hzs (var n a1 b1) (var n i b2)
  have := hzs (var n a1 b2) (var n a2 b1)
  have := hzs (var n a1 b2) (var n a2 b2)
  have := hzs (var n a1 b2) (var n i b1)
  have := hzs (var n a1 b2) (var n i b2)
  have := hzs (var n a2 b1) (var n a2 b2)
  have := hzs (var n a2 b1) (var n i b1)
  have := hzs (var n a2 b1) (var n i b2)
  have := hzs (var n a2 b2) (var n i b1)
  have := hzs (var n a2 b2) (var n i b2)
  have := hzs (var n i b1) (var n i b2)
  unfold H0 H1 H2 H3 H4 H5 H6 M3
  grind

theorem hole_ident (n : Nat) (c : Int) (y : Nat → Int) (z : Nat → Nat → Int) (hzs : ∀ v w, z v w = z w v)
    (hcp : ∀ a a' b, b < n → a ≠ a' → z (var n a b) (var n a' b) = 0)
    (hch : ∀ a b b', b < n → b' < n → b ≠ b' → z (var n a b) (var n a b') = 0)
    (a1 a2 b1 b2 j : Nat) (h12 : a1 ≠ a2) (hb : b1 ≠ b2) (h1j : b1 ≠ j) (h2j : b2 ≠ j) (hb1n : b1 < n) (hb2n : b2 < n) (hjn : j < n) :
    (n : Int) * Gp n c y z a1 a2 b1 b2 j + R2h n c y a1 b1 j + (n : Int) * Gp n c y z a2 a1 b2 b1 j +
      R2h n c y a2 b2 j + R1h n c y a1 j b1 b2 + R1h n c y a2 j b2 b1 -
      S3 n c y z a1 a2 a1 b1 b2 j - S3 n c y z a1 a2 a2 b1 b2 j = M3 n * z (var n a1 b1) (var n a2 b2) := by
  have hb' := Ne.symm hb; have hj1 := Ne.symm h1j; have hj2 := Ne.symm h2j
  unfold R2h R1h S3 Gp
  simp only [hch _ _ _ hb1n hb2n hb, hch _ _ _ hb2n hb1n hb', hch _ _ _ hb1n hjn h1j, hch _ _ _ hjn hb1n hj1, hch _ _ _ hb2n hjn h2j, hch _ _ _ hjn hb2n hj2]
  have := hzs (var n a1 b1) (var n a1 b2)
  have := hzs (var n a1 b1) (var n a1 j)
  have := hzs (var n a1 b1) (var n a2 b1)
  have := hzs (var n a1 b1) (var n a2 b2)
  have := hzs (var n a1 b1) (var n a2 j)
  have := hzs (var n a1 b2) (var n a1 j)
  have := hzs (var n a1 b2) (var n a2 b1)
  have := hzs (var n a1 b2) (var n a2 b2)
  have := hzs (var n a1 b2) (var n a2 j)
  have := hzs (var n a1 j) (var n a2 b1)
  have := hzs (var n a1 j) (var n a2 b2)
  have := hzs (var n a1 j) (var n a2 j)
  have := hzs (var n a2 b1) (var n a2 b2)
  have := hzs (var n a2 b1) (var n a2 j)
  have := hzs (var n a2 b2) (var n a2 j)
  unfold H0 H1 H2 H3 H4 H5 H6 M3
  grind

end Programme.«20261025-1627-proof-complexity».Ext3Alg
