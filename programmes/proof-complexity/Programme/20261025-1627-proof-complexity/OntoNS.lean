import Programme.«20261025-0459-proof-complexity».MatchQuot
import Programme.«20261025-0459-proof-complexity».OntoLucas
import Programme.«20261025-1627-proof-complexity».OntoF2K4
import Programme.«20261025-1627-proof-complexity».OntoF3K9
import Programme.«20261025-0459-proof-complexity».OntoDeg1Lower

/-!
# Nullstellensatz refutations of onto-FPHP, and NS degree ≥ PC degree

`NSRefutation p A D`: multipliers `g_e` (polynomials) for axioms `P_e ∈ A` with
`deg g_e + deg P_e ≤ D` and `∑_e g_e P_e ≡ 1 (mod p)` at every *good* point (no pair of a
degree-2 monomial axiom `x_u x_w` both true). So the identity is read in the matching quotient,
as in the NS tables of the board (product convention `max deg(g_e P_e)`, monomial axioms implicit).
For a linear axiom the multiplier has degree `≤ D - 1` (Beame–Riis multiplier degree `D - 1`).

`ns_pc`: every such refutation gives a degree-`D` `PPCRefutation` (each `g_e P_e` by `mulMono`,
the remainder `1 - ∑ g_e P_e` by `MatchQuot.quot`). Hence all PC lower bounds proved so far are
NS lower bounds: `ns_deg1` (`p ∣ k`), `ns_f2_k4` (`𝔽_2`, `k = 4c`), `ns_f3_k9` (`𝔽_3`, `k = 9c`).
-/

namespace Programme.«20261025-1627-proof-complexity».OntoNS

open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261024-1633-proof-complexity».PCTseitin
open Programme.«20261025-0459-proof-complexity».OntoFPHP Programme.«20261025-0459-proof-complexity».OntoSubst Programme.«20261025-0459-proof-complexity».MatchQuot

/-- A degree-`D` Nullstellensatz refutation over `Z/p`, read at the good points. -/
def NSRefutation (p : Nat) (A : List (Poly Nat)) (D : Nat) : Prop :=
  ∃ L : List (Poly Nat × Poly Nat), (∀ e ∈ L, e.2 ∈ A ∧ e.1.deg + e.2.deg ≤ D) ∧
    ∀ a, Good A a → (p : Int) ∣ (L.map fun e => e.1.eval a * e.2.eval a).sum - 1

/-- `g · P` is derivable when `P ∈ A` and `deg g + deg P ≤ D`. -/
theorem mulPoly {p D : Nat} {A : List (Poly Nat)} {P : Poly Nat} (hP : P ∈ A)
    (hz : PPCDerivable p A D (fun _ => 0)) :
    ∀ T : List (Int × List Nat), (∀ t ∈ T, t.2.length + P.deg ≤ D) →
      PPCDerivable p A D (fun a => (T.map fun t => t.1 * monoEval a t.2).sum * P.eval a)
  | [], _ => of_eq hz (fun a => by simp)
  | t :: T, h => by
    have ih := mulPoly hP hz T (fun s hs => h s (by simp [hs]))
    have hm := mulMono (p := p) (D := D) hP t.2 (by have := h t (by simp); omega)
    refine of_eq (PPCDerivable.lin _ _ t.1 1 hm ih) (fun a => ?_)
    simp only [List.map_cons, List.sum_cons, Int.add_mul, Int.mul_assoc, Int.one_mul]

theorem poly_der {p D : Nat} {A : List (Poly Nat)} {P g : Poly Nat} (hP : P ∈ A)
    (hz : PPCDerivable p A D (fun _ => 0)) (hd : g.deg + P.deg ≤ D) :
    PPCDerivable p A D (fun a => g.eval a * P.eval a) :=
  mulPoly hP hz g.terms (fun t ht => by
    have := (deg_le_iff g g.deg).mp (Nat.le_refl _) t ht; omega)

/-- `∑_e g_e P_e` is derivable. -/
theorem sum_der {p D : Nat} {A : List (Poly Nat)} (hz : PPCDerivable p A D (fun _ => 0)) :
    ∀ L : List (Poly Nat × Poly Nat), (∀ e ∈ L, e.2 ∈ A ∧ e.1.deg + e.2.deg ≤ D) →
      PPCDerivable p A D (fun a => (L.map fun e => e.1.eval a * e.2.eval a).sum)
  | [], _ => of_eq hz (fun a => by simp)
  | e :: L, h => by
    have he := h e (by simp)
    have ih := sum_der hz L (fun f hf => h f (by simp [hf]))
    refine of_eq (PPCDerivable.lin _ _ 1 1 (poly_der he.1 hz he.2) ih) (fun a => ?_)
    simp

theorem cd_congr {p d : Nat} {f g : (Nat → Bool) → Int} (hf : CubeDeg p f d) (h : ∀ a, f a = g a) :
    CubeDeg p g d := by
  obtain ⟨P, hP, hPf⟩ := hf; exact ⟨P, hP, fun a => by rw [← h a]; exact hPf a⟩

/-- The degree of the product of two polynomials (as functions) is at most the sum. -/
theorem cd_prod (p : Nat) (g P : Poly Nat) :
    CubeDeg p (fun a => g.eval a * P.eval a) (g.deg + P.deg) := by
  refine ⟨⟨g.terms.flatMap fun s => P.terms.map fun t => (s.1 * t.1, s.2 ++ t.2)⟩, ?_, fun a => ⟨0, ?_⟩⟩
  · rw [deg_le_iff]
    intro t ht
    obtain ⟨s, hs, ht⟩ := List.mem_flatMap.mp ht
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ht
    have h1 := (deg_le_iff g g.deg).mp (Nat.le_refl _) s hs
    have h2 := (deg_le_iff P P.deg).mp (Nat.le_refl _) r hr
    simp only [List.length_append]; omega
  · simp only [Poly.eval]
    generalize g.terms = G
    induction G with
    | nil => simp
    | cons s G ih =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
        Int.add_mul]
      have : ((P.terms.map fun t => (s.1 * t.1, s.2 ++ t.2)).map fun t => t.1 * monoEval a t.2).sum
          = s.1 * monoEval a s.2 * (P.terms.map fun t => t.1 * monoEval a t.2).sum := by
        generalize P.terms = Q
        induction Q with
        | nil => simp
        | cons r Q ihQ =>
          simp only [List.map_cons, List.sum_cons, ihQ, monoEval_append, Int.mul_add]
          simp only [Int.mul_assoc, Int.mul_left_comm]
      rw [this]; omega

theorem cd_sum (p D : Nat) :
    ∀ L : List (Poly Nat × Poly Nat), (∀ e ∈ L, e.1.deg + e.2.deg ≤ D) →
      CubeDeg p (fun a => (L.map fun e => e.1.eval a * e.2.eval a).sum) D
  | [], _ => cd_congr (Programme.«20261025-0459-proof-complexity».OntoLucas.cd_const p D 0) (fun a => by simp)
  | e :: L, h => by
    have h1 := Programme.«20261025-0459-proof-complexity».OntoLucas.cd_mono (h e (by simp)) (cd_prod p e.1 e.2)
    have h2 := cd_sum p D L (fun f hf => h f (by simp [hf]))
    exact cd_congr (Programme.«20261025-0459-proof-complexity».OntoLucas.cd_lin 1 1 h1 h2) (fun a => by simp)

/-- NS refutations are PC refutations of the same degree. -/
theorem ns_pc_gen {p D : Nat} {A : List (Poly Nat)} (hz : PPCDerivable p A D (fun _ => 0))
    (hA : ∀ u w, prod2 u w ∈ A → u ≠ w) (h : NSRefutation p A D) : PPCRefutation p A D := by
  obtain ⟨L, hL, h1⟩ := h
  have hs := sum_der hz L hL
  have hr : PPCDerivable p A D (fun a => 1 - (L.map fun e => e.1.eval a * e.2.eval a).sum) := by
    apply quot hz hA
    · have := Programme.«20261025-0459-proof-complexity».OntoLucas.cd_lin 1 (-1) (Programme.«20261025-0459-proof-complexity».OntoLucas.cd_const p D 1)
        (cd_sum p D L (fun e he => (hL e he).2))
      exact cd_congr this (fun a => by simp; omega)
    · intro a ha
      have := Int.dvd_neg.mpr (h1 a ha); simpa [Int.neg_sub] using this
  exact of_eq (PPCDerivable.lin _ _ 1 1 hs hr) (fun a => by omega)

theorem ns_pc (p n k D : Nat) (hD : 1 ≤ D) (hnk : 0 < n + k) (h : NSRefutation p (ontoFPHP n k) D) :
    PPCRefutation p (ontoFPHP n k) D :=
  ns_pc_gen (zero_der p n k D hD hnk) (Programme.«20261025-0459-proof-complexity».OntoLucas.prod2_ne n k) h

/-! ## NS lower bounds inherited from the PC lower bounds -/

/-- Degree 0 never refutes (no axiom fits), so `ns_pc` covers every `D`. -/
theorem ns_le (p n k D : Nat) (hnk : 0 < n + k) (hpc : ¬ PPCRefutation p (ontoFPHP n k) D)
    (hD : 1 ≤ D) : ¬ NSRefutation p (ontoFPHP n k) D :=
  fun h => hpc (ns_pc p n k D hD hnk h)

/-- `p ∣ k`, `n ≥ 1`: no degree-1 NS refutation. -/
theorem ns_deg1 (p n k : Nat) (hp : 1 < p) (hn : 1 ≤ n) (hk : (p : Int) ∣ k) :
    ¬ NSRefutation p (ontoFPHP n k) 1 :=
  ns_le p n k 1 (by omega) (Programme.«20261025-0459-proof-complexity».OntoDeg1Lower.ontoFPHP_no_deg1 p n k hp hn hk) (Nat.le_refl 1)

/-- `𝔽_2`, `k = 4c`, `n ≥ 5c`: no NS refutation of degree `≤ 3`. -/
theorem ns_f2_k4 (c n D : Nat) (hc : 0 < c) (hn : c * 5 ≤ n) (hD : D ≤ 3) (hD1 : 1 ≤ D) :
    ¬ NSRefutation 2 (ontoFPHP n (c * 4)) D :=
  ns_le 2 n (c * 4) D (by omega) (Programme.«20261025-1627-proof-complexity».OntoF2K4.f2_deg4 c n D hc hn hD) hD1

/-- `𝔽_3`, `k = 9c`, `n ≥ 5c`: no NS refutation of degree `≤ 3`. -/
theorem ns_f3_k9 (c n D : Nat) (hc : 0 < c) (hn : c * 5 ≤ n) (hD : D ≤ 3) (hD1 : 1 ≤ D) :
    ¬ NSRefutation 3 (ontoFPHP n (c * 9)) D :=
  ns_le 3 n (c * 9) D (by omega) (Programme.«20261025-1627-proof-complexity».OntoF3K9.f3_deg4 c n D hc hn hD) hD1

end Programme.«20261025-1627-proof-complexity».OntoNS

#print axioms Programme.«20261025-1627-proof-complexity».OntoNS.ns_pc
#print axioms Programme.«20261025-1627-proof-complexity».OntoNS.ns_deg1
#print axioms Programme.«20261025-1627-proof-complexity».OntoNS.ns_f2_k4
#print axioms Programme.«20261025-1627-proof-complexity».OntoNS.ns_f3_k9
