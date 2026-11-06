import Programme.«20261027-0607-proof-complexity».Peel

/-!
# Conjecture V reduces to one unit degree-`p` design

At `d = p - 1` the peeling of `Work.Peel.claim` uses the unit `Units p (d + 1)` only at level `0`
(the type-`0` window has value `p!`). Replacing that window by a given `T₀` with `Wd p n k (p-1) T₀`
and `T₀(∅) ≡ 1` gives `EXT p n₀ k (p - 1)`, hence no degree-`p` refutation for every `n ≥ n₀`.
-/

namespace Programme.«20261027-0607-proof-complexity».VUnit

open Programme.«20261025-0459-proof-complexity».OntoFPHP (ontoFPHP PPCRefutation)
open Programme.«20261026-1402-proof-complexity».ExtLemma
open Programme.«20261026-1402-proof-complexity».ExtLin
open Programme.«20261027-0607-proof-complexity».SJ (RP RPGen fact SJ)
open Programme.«20261027-0607-proof-complexity».Peel

variable {p n k : Nat}

/-- Rectangle products of positive size are in the span of windows, with units only up to `d`. -/
theorem rp_span' {d j : Nat} (hk : (p : Int) ∣ k) (hn : 2 * d + 1 ≤ n) (hj1 : 1 ≤ j) (hj : j ≤ d)
    (hu : Units p d) {f : List Nat → Int} (hf : RPGen n k j f) : InSpan p n k j (Wd p n k d) f := by
  obtain ⟨P, Q, hP, hQ, rfl⟩ := hf
  obtain ⟨W, hW, hval⟩ := Programme.«20261027-0607-proof-complexity».WinMain.window (p := p) hk hn hj hP hQ
  obtain ⟨u, hu'⟩ := fact_unit hu (d - j + 1) (by omega)
  refine InSpan.congr (InSpan.smul u (InSpan.gen hW)) (fun g hg hl => ?_)
  rw [hval g hg hl]
  have : RP n j P Q g - u * ((fact (d - j + 1) : Int) * RP n j P Q g) =
      -((u * (fact (d - j + 1) : Int) - 1) * RP n j P Q g) := by
    rw [Int.sub_mul, Int.one_mul, Int.mul_assoc]; omega
  rw [this]; exact Int.dvd_neg.mpr (Int.dvd_mul_of_dvd_left hu')

/-- **Peeling with a unit design at level 0.** -/
theorem claimU {d : Nat} (hk : (p : Int) ∣ k) (hn : 2 * d + 1 ≤ n) (hu : Units p d)
    {T0 : List Nat → Int} (hT0 : Wd p n k d T0) (h1 : (p : Int) ∣ T0 [] - 1) :
    ∀ ℓ ≤ d, ∀ f, Adm p n k ℓ f → InSpan p n k ℓ (Wd p n k d) f
  | 0, _, f, _ => by
    refine InSpan.congr (InSpan.smul (f []) (InSpan.gen hT0)) (fun g _ hl => ?_)
    rw [List.eq_nil_of_length_eq_zero hl]
    have : f [] - f [] * T0 [] = -(f [] * (T0 [] - 1)) := by rw [Int.mul_sub]; omega
    rw [this]; exact Int.dvd_neg.mpr (Int.dvd_mul_of_dvd_right h1)
  | ℓ + 1, hℓ, f, ⟨c, hb, hc⟩ => by
    have ih := claimU hk hn hu hT0 h1 ℓ (by omega) c hc
    obtain ⟨T, hT, hcT⟩ := span_rep (by omega) ih
    have h1' : Bal p n k (fun g => f g + (-1) * T g) (fun g => c g + (-1) * T g) ℓ :=
      Bal_add hb (Bal_smul (-1) (hT ℓ (by omega)))
    have h2 : Bal p n k (fun g => f g + (-1) * T g) (fun _ => 0) ℓ := Bal_congr h1' (fun g hg hl => by
      have := hcT g hg hl
      rw [show (0 : Int) - (c g + -1 * T g) = -(c g - T g) by omega]; exact Int.dvd_neg.mpr this)
    obtain ⟨e, he⟩ := fact_unit hu (ℓ + 1) (by omega)
    have h3 := SJ p n k ℓ (by omega) ⟨e, he⟩ _ h2
    have h4 := span_mono (fun f' hf' => rp_span' hk hn (by omega) (by omega) hu hf') h3
    refine InSpan.congr (InSpan.add h4 (InSpan.gen hT)) (fun g _ _ => ?_)
    rw [show f g - (f g + -1 * T g + T g) = 0 by omega]; exact Int.dvd_zero _

/-- `EXT p n k d` from a unit design of degree `d + 1`, with units only up to `d`. -/
theorem ext_unit {d : Nat} (hk : (p : Int) ∣ k) (hn : 2 * d + 1 ≤ n) (hu : Units p d)
    {T0 : List Nat → Int} (hT0 : Wd p n k d T0) (h1 : (p : Int) ∣ T0 [] - 1) : EXT p n k d := by
  apply EXT_of_span (G := Wd p n k d) (fun T hT => ⟨T, hT d (Nat.le_refl d)⟩)
  intro f c hb
  apply claimU hk hn hu hT0 h1 d (Nat.le_refl d) f
  cases d with
  | zero => trivial
  | succ ℓ => exact adm_of_bal ℓ f c (hb ℓ rfl)

/-- **Conjecture V from one unit design.** For a prime `p`, `p ∣ k` and `n₀ ≥ 2p - 1`: if some
`T₀` has `Bal p n₀ k T₀ T₀ e` for every `e ≤ p - 1` and `T₀(∅) ≡ 1` mod `p`, then for every
`n ≥ n₀`, `ontoFPHP n k` has no degree-`p` `PPCRefutation p`. -/
theorem no_refutation_of_unit {p k n0 : Nat} (hp : IsPrime p) (hk : p ∣ k) (hn0 : 2 * p - 1 ≤ n0)
    (T0 : List Nat → Int) (hT0 : ∀ e ≤ p - 1, Bal p n0 k T0 T0 e) (h1 : (p : Int) ∣ T0 [] - 1)
    (n : Nat) (hn : n0 ≤ n) : ¬ PPCRefutation p (ontoFPHP n k) p := by
  have hk' : (p : Int) ∣ k := Int.natCast_dvd_natCast.mpr hk
  have hu := units_of_prime hp
  have hp2 := hp.1
  apply no_refutation_of_ext_ge (n0 := n0) (by omega) (by omega) (by omega) _ n hn
  intro d hd
  by_cases hdp : d + 2 ≤ p
  · exact ext_d hk' (by omega) (fun s h1 h2 => hu s h1 (by omega))
  · have hd' : d = p - 1 := by omega
    subst hd'
    exact ext_unit hk' (by omega) hu hT0 h1

end Programme.«20261027-0607-proof-complexity».VUnit

#print axioms Programme.«20261027-0607-proof-complexity».VUnit.no_refutation_of_unit
