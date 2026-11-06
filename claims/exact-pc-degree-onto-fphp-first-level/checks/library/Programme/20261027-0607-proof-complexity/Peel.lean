import Programme.«20261027-0607-proof-complexity».WinMain

/-!
# Peeling: `EXT p n k d` for `d ≤ p - 2`, and PC degree `≥ p` for onto-FPHP over `F_p`, `p ∣ k`

`Wd d` = windows up to level `d` (`Bal T T e` for all `e ≤ d`), closed under sums and multiples.
`Adm ℓ f`: `f` is the top of a flag `f = c_ℓ, c_{ℓ-1}, …, c_0` with `Bal c_{e+1} c_e e`
(from `Bal f c (ℓ-1)` by the flag lemma `Work.Flag.flag`).
`claim`: every admissible `f` at level `ℓ ≤ d` is in the span of `Wd d` at level `ℓ`. Level `0`:
`f ≡ f(∅) · (type-0 window)/d!`. Step: subtract a window `T` matching the link `c`, the residual has
zero links, so by `Work.SJ.SJ` it is a span of rectangle products, each `≡` a type-`(ℓ+1)` window
(`WinMain.window`) divided by a unit factorial. Then `ExtLin.EXT_of_span`, and
`ExtLemma.no_refutation_of_ext_ge` with `D = p - 1`, `n₀ = 2p - 3`.
-/

namespace Programme.«20261027-0607-proof-complexity».Peel

open Programme.«20261025-0459-proof-complexity».OntoFPHP (rsum var ontoFPHP PPCRefutation)
open Programme.«20261026-1402-proof-complexity».ExtLemma
open Programme.«20261026-1402-proof-complexity».ExtLin
open Programme.«20261027-0607-proof-complexity».LemK (VP)
open Programme.«20261027-0607-proof-complexity».SJ (RP RPGen allT fact SJ)

variable {p n k : Nat}

def Wd (p n k d : Nat) (T : List Nat → Int) : Prop := ∀ e ≤ d, Bal p n k T T e

/-- Units mod `p` up to `t`. -/
def Units (p t : Nat) : Prop := ∀ s, 1 ≤ s → s ≤ t → ∃ e : Int, (p : Int) ∣ e * s - 1

theorem fact_unit {p t : Nat} (hu : Units p t) : ∀ s ≤ t, ∃ e : Int, (p : Int) ∣ e * (fact s : Int) - 1
  | 0, _ => ⟨1, by simp [fact]⟩
  | s + 1, hs => by
    obtain ⟨e1, h1⟩ := hu (s + 1) (by omega) hs
    obtain ⟨e2, h2⟩ := fact_unit hu s (by omega)
    refine ⟨e1 * e2, ?_⟩
    have : e1 * e2 * ((fact (s + 1) : Nat) : Int) - 1 =
        e1 * ((s + 1 : Nat) : Int) * (e2 * (fact s : Int) - 1) + (e1 * ((s + 1 : Nat) : Int) - 1) := by
      simp only [fact]; push_cast
      rw [Int.mul_sub, Int.mul_one]
      have : e1 * ((s : Int) + 1) * (e2 * (fact s : Int)) = e1 * e2 * (((s : Int) + 1) * (fact s : Int)) := by
        simp only [Int.mul_assoc, Int.mul_left_comm]
      omega
    rw [this]
    exact Int.dvd_add (Int.dvd_mul_of_dvd_right h2) h1

theorem span_rep {d ℓ : Nat} (hℓ : ℓ ≤ d) {c : List Nat → Int} (h : InSpan p n k ℓ (Wd p n k d) c) :
    ∃ T, Wd p n k d T ∧ ∀ g, CM n k g → g.length = ℓ → (p : Int) ∣ c g - T g := by
  induction h with
  | gen hf => exact ⟨_, hf, fun g _ _ => by rw [Int.sub_self]; exact Int.dvd_zero _⟩
  | add _ _ ih ih' =>
    obtain ⟨T, hT, hc⟩ := ih; obtain ⟨T', hT', hc'⟩ := ih'
    refine ⟨fun g => T g + T' g, fun e he => Bal_add (hT e he) (hT' e he), fun g hg hl => ?_⟩
    have := Int.dvd_add (hc g hg hl) (hc' g hg hl)
    rw [show ∀ a b c d : Int, a - c + (b - d) = a + b - (c + d) by intros; omega] at this; exact this
  | smul a _ ih =>
    obtain ⟨T, hT, hc⟩ := ih
    refine ⟨fun g => a * T g, fun e he => Bal_smul a (hT e he), fun g hg hl => ?_⟩
    have := Int.dvd_trans (hc g hg hl) (Int.dvd_mul_left a _)
    rw [Int.mul_sub] at this; exact this
  | congr _ hcg ih =>
    obtain ⟨T, hT, hc⟩ := ih
    refine ⟨T, hT, fun g hg hl => ?_⟩
    have := Int.dvd_add (hcg g hg hl) (hc g hg hl)
    rw [show ∀ a b c : Int, a - b + (b - c) = a - c by intros; omega] at this; exact this

theorem span_mono {e : Nat} {G G' : (List Nat → Int) → Prop} (hG : ∀ f, G f → InSpan p n k e G' f)
    {h : List Nat → Int} (hh : InSpan p n k e G h) : InSpan p n k e G' h := by
  induction hh with
  | gen hf => exact hG _ hf
  | add _ _ ih ih' => exact InSpan.add ih ih'
  | smul a _ ih => exact InSpan.smul a ih
  | congr _ hc ih => exact InSpan.congr ih hc

def Adm (p n k : Nat) : Nat → (List Nat → Int) → Prop
  | 0, _ => True
  | ℓ + 1, f => ∃ c, Bal p n k f c ℓ ∧ Adm p n k ℓ c

theorem adm_of_bal : ∀ (ℓ : Nat) (f c : List Nat → Int), Bal p n k f c ℓ → Adm p n k (ℓ + 1) f
  | 0, _, c, h => ⟨c, h, trivial⟩
  | ℓ + 1, _, c, h => by
    obtain ⟨c', hc'⟩ := Programme.«20261027-0607-proof-complexity».Flag.flag h
    exact ⟨c, h, adm_of_bal ℓ c c' hc'⟩

/-- Rectangle products are in the span of windows. -/
theorem rp_span {d j : Nat} (hk : (p : Int) ∣ k) (hn : 2 * d + 1 ≤ n) (hj : j ≤ d) (hu : Units p (d + 1))
    {f : List Nat → Int} (hf : RPGen n k j f) : InSpan p n k j (Wd p n k d) f := by
  obtain ⟨P, Q, hP, hQ, rfl⟩ := hf
  obtain ⟨W, hW, hval⟩ := Programme.«20261027-0607-proof-complexity».WinMain.window (p := p) hk hn hj hP hQ
  obtain ⟨u, hu'⟩ := fact_unit hu (d - j + 1) (by omega)
  refine InSpan.congr (InSpan.smul u (InSpan.gen hW)) (fun g hg hl => ?_)
  rw [hval g hg hl]
  have : RP n j P Q g - u * ((fact (d - j + 1) : Int) * RP n j P Q g) =
      -((u * (fact (d - j + 1) : Int) - 1) * RP n j P Q g) := by
    rw [Int.sub_mul, Int.one_mul, Int.mul_assoc]; omega
  rw [this]; exact Int.dvd_neg.mpr (Int.dvd_mul_of_dvd_left hu')

theorem VP_zero (M : Nat) (X : Nat → Bool) (P : Nat → Nat × Nat) : VP M X 0 P :=
  ⟨fun s hs => absurd hs (by omega), fun s hs => absurd hs (by omega)⟩

/-- **Peeling.** -/
theorem claim {d : Nat} (hk : (p : Int) ∣ k) (hn : 2 * d + 1 ≤ n) (hu : Units p (d + 1)) :
    ∀ ℓ ≤ d, ∀ f, Adm p n k ℓ f → InSpan p n k ℓ (Wd p n k d) f
  | 0, _, f, _ => by
    have h0 := rp_span (p := p) hk hn (Nat.zero_le d) hu (f := RP n 0 (fun _ => (0, 0)) (fun _ => (0, 0)))
      ⟨_, _, VP_zero _ _ _, VP_zero _ _ _, rfl⟩
    refine InSpan.congr (InSpan.smul (f []) h0) (fun g _ hl => ?_)
    rw [List.eq_nil_of_length_eq_zero hl]
    simp [RP, Programme.«20261027-0607-proof-complexity».SJ.jp]
  | ℓ + 1, hℓ, f, ⟨c, hb, hc⟩ => by
    have ih := claim hk hn hu ℓ (by omega) c hc
    obtain ⟨T, hT, hcT⟩ := span_rep (by omega) ih
    have h1 : Bal p n k (fun g => f g + (-1) * T g) (fun g => c g + (-1) * T g) ℓ :=
      Bal_add hb (Bal_smul (-1) (hT ℓ (by omega)))
    have h2 : Bal p n k (fun g => f g + (-1) * T g) (fun _ => 0) ℓ := Bal_congr h1 (fun g hg hl => by
      have := hcT g hg hl
      rw [show (0 : Int) - (c g + -1 * T g) = -(c g - T g) by omega]; exact Int.dvd_neg.mpr this)
    obtain ⟨e, he⟩ := fact_unit hu (ℓ + 1) (by omega)
    have h3 := SJ p n k ℓ (by omega) ⟨e, he⟩ _ h2
    have h4 := span_mono (fun f' hf' => rp_span hk hn (by omega) hu hf') h3
    refine InSpan.congr (InSpan.add h4 (InSpan.gen hT)) (fun g _ _ => ?_)
    rw [show f g - (f g + -1 * T g + T g) = 0 by omega]; exact Int.dvd_zero _

/-- **EXT up to `d`.** -/
theorem ext_d {d : Nat} (hk : (p : Int) ∣ k) (hn : 2 * d + 1 ≤ n) (hu : Units p (d + 1)) : EXT p n k d := by
  apply EXT_of_span (G := Wd p n k d) (fun T hT => ⟨T, hT d (Nat.le_refl d)⟩)
  intro f c hb
  apply claim hk hn hu d (Nat.le_refl d) f
  cases d with
  | zero => trivial
  | succ ℓ => exact adm_of_bal ℓ f c (hb ℓ rfl)

/-- **No degree-`(p-1)` refutation.** If every `1 ≤ s ≤ p - 1` is a unit mod `p` and `p ∣ k`, then for
every `n ≥ 2p - 3`, `ontoFPHP n k` has no degree-`(p-1)` `PPCRefutation p`. -/
theorem no_refutation_units {p k : Nat} (hp : 2 ≤ p) (hu : Units p (p - 1)) (hk : p ∣ k) (n : Nat)
    (hn : 2 * p - 3 ≤ n) : ¬ PPCRefutation p (ontoFPHP n k) (p - 1) := by
  have hk' : (p : Int) ∣ k := Int.natCast_dvd_natCast.mpr hk
  apply no_refutation_of_ext_ge (n0 := 2 * p - 3) (by omega) (by omega) (by omega) _ n hn
  intro d hd
  exact ext_d hk' (by omega) (fun s h1 h2 => hu s h1 (by omega))

/-! ## Primes -/

def IsPrime (p : Nat) : Prop := 2 ≤ p ∧ ∀ a, a ∣ p → a = 1 ∨ a = p

theorem bezout (a b : Nat) : ∃ x y : Int, x * a + y * b = (Nat.gcd a b : Int) := by
  induction a, b using Nat.gcd.induction with
  | H0 n => exact ⟨0, 1, by simp⟩
  | H1 m n _ ih =>
    obtain ⟨x, y, h⟩ := ih
    refine ⟨y - x * ((n / m : Nat) : Int), x, ?_⟩
    rw [Nat.gcd_rec m n, ← h]
    have e : ((n % m : Nat) : Int) + (m : Int) * ((n / m : Nat) : Int) = (n : Int) := by
      have := Nat.mod_add_div n m; exact_mod_cast this
    rw [← e, Int.sub_mul, Int.mul_add]
    have : x * ((m : Int) * ((n / m : Nat) : Int)) = x * ((n / m : Nat) : Int) * (m : Int) := by
      rw [Int.mul_comm (m : Int), Int.mul_assoc]
    omega

theorem units_of_prime {p : Nat} (hp : IsPrime p) : Units p (p - 1) := by
  intro s h1 h2
  have hg : Nat.gcd s p = 1 := by
    rcases hp.2 _ (Nat.gcd_dvd_right s p) with h | h
    · exact h
    · have := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left s p); omega
  obtain ⟨x, y, h⟩ := bezout s p
  rw [hg] at h
  refine ⟨x, ⟨-y, ?_⟩⟩
  rw [Int.mul_neg, Int.mul_comm (p : Int) y]; push_cast at h; omega

/-- **PC degree `≥ p` for onto-FPHP over `F_p` when `p ∣ k`.** For every prime `p`, every `k` with
`p ∣ k` and every `n ≥ 2p - 3`, `ontoFPHP n k` (functional encoding) has no `PPCRefutation p` of
degree `p - 1`. -/
theorem pc_degree_ge_p {p k : Nat} (hp : IsPrime p) (hk : p ∣ k) (n : Nat) (hn : 2 * p - 3 ≤ n) :
    ¬ PPCRefutation p (ontoFPHP n k) (p - 1) :=
  no_refutation_units hp.1 (units_of_prime hp) hk n hn

end Programme.«20261027-0607-proof-complexity».Peel

#print axioms Programme.«20261027-0607-proof-complexity».Peel.pc_degree_ge_p
#print axioms Programme.«20261027-0607-proof-complexity».Peel.ext_d
