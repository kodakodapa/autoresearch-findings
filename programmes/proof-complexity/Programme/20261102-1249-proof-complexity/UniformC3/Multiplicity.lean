import Programme.«20261027-0607-proof-complexity».Lucas

namespace Programme.«20261102-1249-proof-complexity».UniformC3
open Programme.«20261025-0459-proof-complexity».OntoLucas (bin)
open Programme.«20261027-0607-proof-complexity».Peel (IsPrime)
open Programme.«20261027-0607-proof-complexity».Lucas (shift bin_self)

theorem bin_shift_multiple {p : Nat} (hp : IsPrime p) (a r : Nat) (hr : r < p) :
    ∀ t, (p : Int) ∣ (bin (a+t*p) r : Int) - bin a r
  | 0 => by simp
  | t+1 => by
    have h1 := bin_shift_multiple hp a r hr t
    have h2 := shift hp (a+t*p) r hr
    have h := Int.dvd_add h1 h2
    rw [show a+(t+1)*p = a+t*p+p by rw [Nat.add_mul]; omega]
    have he : ∀ x y z : Int, (x-y)+(z-x)=z-y := by intros; omega
    rwa [he] at h

/-- The precise coefficient multiplicity needed by the subset transfer. -/
theorem subset_multiplicity_congr {p : Nat} (hp : IsPrime p) (c : Nat) :
    (p : Int) ∣ (bin (c*p*p+p-1) (p-1) : Int) - 1 := by
  have hp2 := hp.1
  have h := bin_shift_multiple hp (p-1) (p-1) (by omega) (c*p)
  rw [bin_self] at h
  have he : p-1+(c*p)*p = c*p*p+p-1 := by omega
  rwa [he] at h

#print axioms subset_multiplicity_congr
end Programme.«20261102-1249-proof-complexity».UniformC3
