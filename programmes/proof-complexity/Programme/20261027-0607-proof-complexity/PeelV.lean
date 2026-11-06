import Programme.«20261027-0607-proof-complexity».Peel
import Programme.«20261026-1402-proof-complexity».BDesMain

/-!
# Conjecture V reduced to one unit design

th's peeling (`Peer.th.Peel.claim`) uses `p!` only at level 0 (the type-0 window divided by `d!`).
Replacing that window by a given `T0 ∈ Wd p n k d` with `T0 [] ` a unit mod `p` lets the peeling run
with `Units p d` instead of `Units p (d + 1)`. At `d = p - 1` this gives: one unit degree-`p`
design at `n₀ ≥ 2p - 1` implies no degree-`p` `PPCRefutation p` of `ontoFPHP n k` for all `n ≥ n₀`.
-/

namespace Programme.«20261027-0607-proof-complexity».PeelV

open Programme.«20261025-0459-proof-complexity».OntoFPHP (ontoFPHP PPCRefutation)
open Programme.«20261026-1402-proof-complexity».ExtLemma
open Programme.«20261026-1402-proof-complexity».ExtLin
open Programme.«20261027-0607-proof-complexity».SJ (RP RPGen fact SJ)
open Programme.«20261027-0607-proof-complexity».Peel (Wd Units IsPrime fact_unit span_rep span_mono Adm adm_of_bal)

variable {p n k : Nat}

/-- Rectangle products of size `j ≥ 1` lie in the window span at level `d` when `(d-j+1)!` is a unit. -/
theorem rp_span' {d j : Nat} (hk : (p : Int) ∣ k) (hn : 2 * d + 1 ≤ n) (hj : j ≤ d)
    (hu : ∃ u : Int, (p : Int) ∣ u * (fact (d - j + 1) : Int) - 1)
    {f : List Nat → Int} (hf : RPGen n k j f) : InSpan p n k j (Wd p n k d) f := by
  obtain ⟨P, Q, hP, hQ, rfl⟩ := hf
  obtain ⟨W, hW, hval⟩ := Programme.«20261027-0607-proof-complexity».WinMain.window (p := p) hk hn hj hP hQ
  obtain ⟨u, hu'⟩ := hu
  refine InSpan.congr (InSpan.smul u (InSpan.gen hW)) (fun g hg hl => ?_)
  rw [hval g hg hl]
  have : RP n j P Q g - u * ((fact (d - j + 1) : Int) * RP n j P Q g) =
      -((u * (fact (d - j + 1) : Int) - 1) * RP n j P Q g) := by
    rw [Int.sub_mul, Int.one_mul, Int.mul_assoc]; omega
  rw [this]; exact Int.dvd_neg.mpr (Int.dvd_mul_of_dvd_left hu')

/-- **Peeling with a unit design at the top level.** -/
theorem claimV {d : Nat} (hk : (p : Int) ∣ k) (hn : 2 * d + 1 ≤ n) (hu : Units p d)
    {T0 : List Nat → Int} (hT0 : Wd p n k d T0) {u0 : Int} (hu0 : (p : Int) ∣ u0 * T0 [] - 1) :
    ∀ ℓ ≤ d, ∀ f, Adm p n k ℓ f → InSpan p n k ℓ (Wd p n k d) f
  | 0, _, f, _ => by
    refine InSpan.congr (InSpan.smul (f [] * u0) (InSpan.gen hT0)) (fun g _ hl => ?_)
    rw [List.eq_nil_of_length_eq_zero hl]
    have : f [] - f [] * u0 * T0 [] = -(f [] * (u0 * T0 [] - 1)) := by
      rw [Int.mul_sub, Int.mul_one, Int.mul_assoc]; omega
    rw [this]; exact Int.dvd_neg.mpr (Int.dvd_mul_of_dvd_right hu0)
  | ℓ + 1, hℓ, f, ⟨c, hb, hc⟩ => by
    have ih := claimV hk hn hu hT0 hu0 ℓ (by omega) c hc
    obtain ⟨T, hT, hcT⟩ := span_rep (by omega) ih
    have h1 : Bal p n k (fun g => f g + (-1) * T g) (fun g => c g + (-1) * T g) ℓ :=
      Bal_add hb (Bal_smul (-1) (hT ℓ (by omega)))
    have h2 : Bal p n k (fun g => f g + (-1) * T g) (fun _ => 0) ℓ := Bal_congr h1 (fun g hg hl => by
      have := hcT g hg hl
      rw [show (0 : Int) - (c g + -1 * T g) = -(c g - T g) by omega]; exact Int.dvd_neg.mpr this)
    have h3 := SJ p n k ℓ (by omega) (fact_unit hu (ℓ + 1) (by omega)) _ h2
    have h4 := span_mono (fun f' hf' =>
      rp_span' hk hn (by omega) (fact_unit hu (d - (ℓ + 1) + 1) (by omega)) hf') h3
    refine InSpan.congr (InSpan.add h4 (InSpan.gen hT)) (fun g _ _ => ?_)
    rw [show f g - (f g + -1 * T g + T g) = 0 by omega]; exact Int.dvd_zero _

/-- `EXT p n k d` from one unit design `T0 ∈ Wd p n k d`, with units only up to `d`. -/
theorem ext_of_design {d : Nat} (hk : (p : Int) ∣ k) (hn : 2 * d + 1 ≤ n) (hu : Units p d)
    {T0 : List Nat → Int} (hT0 : Wd p n k d T0) {u0 : Int} (hu0 : (p : Int) ∣ u0 * T0 [] - 1) :
    EXT p n k d := by
  apply EXT_of_span (G := Wd p n k d) (fun T hT => ⟨T, hT d (Nat.le_refl d)⟩)
  intro f c hb
  apply claimV hk hn hu hT0 hu0 d (Nat.le_refl d) f
  cases d with
  | zero => trivial
  | succ ℓ => exact adm_of_bal ℓ f c (hb ℓ rfl)

/-- A residue not divisible by a prime `p` is a unit mod `p`. -/
theorem unit_of_not_dvd {p : Nat} (hp : IsPrime p) {a : Int} (ha : ¬ (p : Int) ∣ a) :
    ∃ u : Int, (p : Int) ∣ u * a - 1 := by
  have hp0 : (0 : Int) < p := by have := hp.1; omega
  have hr0 : 0 ≤ a % p := Int.emod_nonneg a (by omega)
  have hrp : a % p < p := Int.emod_lt_of_pos a hp0
  have hrne : a % p ≠ 0 := fun h => ha (Int.dvd_of_emod_eq_zero h)
  obtain ⟨r, hr⟩ : ∃ r : Nat, a % p = (r : Int) := ⟨(a % p).toNat, by omega⟩
  obtain ⟨u, hu⟩ := Programme.«20261027-0607-proof-complexity».Peel.units_of_prime hp r (by omega) (by omega)
  refine ⟨u, ?_⟩
  have hd : (p : Int) ∣ a - r := by
    rw [← hr, Int.emod_def, show a - (a - (p : Int) * (a / p)) = (p : Int) * (a / p) by omega]
    exact Int.dvd_mul_right _ _
  have : u * a - 1 = (u * r - 1) + u * (a - r) := by rw [Int.mul_sub]; omega
  rw [this]; exact Int.dvd_add hu (Int.dvd_mul_of_dvd_right hd)

/-- **Conjecture V from one unit degree-`p` design.** For a prime `p` with `p ∣ k` and `n₀ ≥ 2p - 1`:
if some `T` has `Bal p n₀ k T T e` for every `e ≤ p - 1` and `T [] ≢ 0 (mod p)`, then for every
`n ≥ n₀`, `ontoFPHP n k` has no degree-`p` `PPCRefutation p`. -/
theorem no_deg_p_of_design {p k n0 : Nat} (hp : IsPrime p) (hk : p ∣ k) (hn0 : 2 * p - 1 ≤ n0)
    {T : List Nat → Int} (hT : ∀ e ≤ p - 1, Bal p n0 k T T e) (hT1 : ¬ (p : Int) ∣ T []) (n : Nat)
    (hn : n0 ≤ n) : ¬ PPCRefutation p (ontoFPHP n k) p := by
  have hp2 := hp.1
  have hk' : (p : Int) ∣ k := Int.natCast_dvd_natCast.mpr hk
  have hu := Programme.«20261027-0607-proof-complexity».Peel.units_of_prime hp
  apply no_refutation_of_ext_ge (n0 := n0) (by omega) (by omega) (by omega) _ n hn
  intro d hd
  by_cases hdp : d + 1 < p
  · exact Programme.«20261027-0607-proof-complexity».Peel.ext_d hk' (by omega) (fun s h1 h2 => hu s h1 (by omega))
  · obtain rfl : d = p - 1 := by omega
    obtain ⟨u0, hu0⟩ := unit_of_not_dvd hp hT1
    exact ext_of_design hk' (by omega) hu hT hu0

/-- Non-vacuity at `p = 2`: the library design `B` (K167) of `ontoFPHP 4 8` meets the hypothesis. -/
theorem no_deg2_k8 (n : Nat) (hn : 4 ≤ n) : ¬ PPCRefutation 2 (ontoFPHP n 8) 2 := by
  have hB := Programme.«20261026-1402-proof-complexity».BDesMain.b_design
  have hp : IsPrime 2 := ⟨Nat.le_refl 2, fun a ha => by
    have := Nat.le_of_dvd (by decide) ha
    rcases (show a = 0 ∨ a = 1 ∨ a = 2 by omega) with h | h | h <;> subst h <;> simp_all⟩
  refine no_deg_p_of_design hp (by decide) (by decide) (fun e he => hB.2 e (by omega)) ?_ n hn
  rw [hB.1]; decide

end Programme.«20261027-0607-proof-complexity».PeelV

#print axioms Programme.«20261027-0607-proof-complexity».PeelV.no_deg_p_of_design
#print axioms Programme.«20261027-0607-proof-complexity».PeelV.ext_of_design
#print axioms Programme.«20261027-0607-proof-complexity».PeelV.no_deg2_k8
