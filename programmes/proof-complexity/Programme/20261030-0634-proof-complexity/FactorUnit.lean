import Programme.«20261030-0634-proof-complexity».FactorBoundary
import Programme.«20261027-0607-proof-complexity».PeelV

namespace Programme.«20261030-0634-proof-complexity».FactorUnit
open Programme.«20261026-1402-proof-complexity».SymDesign
open Programme.«20261026-1402-proof-complexity».ExtLemma
open Programme.«20261027-0607-proof-complexity».Peel (IsPrime Units units_of_prime)
open Programme.«20261025-0459-proof-complexity».OntoFPHP (ontoFPHP PPCRefutation)

/-- Each factor lies one modulus above a nonzero residue. -/
theorem ff_unit {p : Nat} (hu : Units p (p-1)) :
    ∀ r : Nat, ∀ x : Int, (p : Int) + r ≤ x → x < 2*(p : Int) →
      ∃ u : Int, (p : Int) ∣ u * ff x r - 1 := by
  intro r
  induction r with
  | zero => intro x _ _; exact ⟨1, by simp [ff]⟩
  | succ r ih =>
    intro x hlo hhi
    obtain ⟨v, hv⟩ := ih (x-1) (by omega) (by omega)
    let s := (x - (p : Int)).toNat
    have hs : (s : Int) = x - (p : Int) := Int.toNat_of_nonneg (by omega)
    obtain ⟨a, ha⟩ := hu s (by omega) (by omega)
    have hx : (p : Int) ∣ a*x - 1 := by
      have eqn : a*x-1 = (a*(s : Int)-1) + a*(p : Int) := by
        rw [hs, Int.mul_sub]; omega
      rw [eqn]
      exact Int.dvd_add ha (Int.dvd_mul_left _ _)
    refine ⟨a*v, ?_⟩
    have eqn : (a*v)*ff x (r+1)-1 =
        (a*x-1)*(v*ff (x-1) r) + (v*ff (x-1) r-1) := by
      simp only [ff, Int.sub_mul, Int.one_mul]
      simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
      omega
    rw [eqn]
    exact Int.dvd_add (Int.dvd_mul_of_dvd_left hx) hv

theorem empty_unit {p : Nat} (hp : IsPrime p) :
    ∃ u : Int, (p : Int) ∣ u * (-ff ((2*p-1 : Nat) : Int) (p-1)) - 1 := by
  obtain ⟨u, hu⟩ := ff_unit (units_of_prime hp) (p-1) ((2*p-1 : Nat) : Int)
    (by have := hp.1; omega) (by have := hp.1; omega)
  refine ⟨-u, ?_⟩
  simpa only [Int.neg_mul_neg] using hu

theorem empty_nonzero {p : Nat} (hp : IsPrime p) :
    ¬ (p : Int) ∣ -ff ((2*p-1 : Nat) : Int) (p-1) := by
  intro h
  obtain ⟨u, hu⟩ := empty_unit hp
  have h1 : (p : Int) ∣ (1 : Int) := by
    have h2 := Int.dvd_sub (Int.dvd_trans h (Int.dvd_mul_left u _)) hu
    have eqn : u * -ff ((2*p-1 : Nat) : Int) (p-1) -
        (u * -ff ((2*p-1 : Nat) : Int) (p-1) - 1) = 1 := by omega
    rw [eqn] at h2
    exact h2
  have := Int.le_of_dvd (by decide : (0 : Int) < 1) h1
  have := hp.1
  omega

/-- Precisely the top-layer construction still required for the uniform programme. -/
def TopExtension (p : Nat) : Prop :=
  ∃ U : List Nat → Int, Bal p (2*p-1) (p*p) U (fun _ => -1) (p-1)

theorem no_deg_p_of_top {p : Nat} (hp : IsPrime p) (ht : TopExtension p)
    (n : Nat) (hn : 2*p-1 ≤ n) : ¬ PPCRefutation p (ontoFPHP n (p*p)) p := by
  obtain ⟨U, hU⟩ := ht
  obtain ⟨T, hT0, hT⟩ := Programme.«20261030-0634-proof-complexity».FactorBoundary.design_of_top
    (by have := hp.1; omega : 0 < 2*p-1) (Nat.dvd_mul_right p p) U hU
  apply Programme.«20261027-0607-proof-complexity».PeelV.no_deg_p_of_design
    hp (Nat.dvd_mul_right p p) (Nat.le_refl _) hT ?_ n hn
  rw [hT0]
  exact empty_nonzero hp

#print axioms ff_unit
#print axioms empty_unit
#print axioms empty_nonzero
#print axioms no_deg_p_of_top
end Programme.«20261030-0634-proof-complexity».FactorUnit
