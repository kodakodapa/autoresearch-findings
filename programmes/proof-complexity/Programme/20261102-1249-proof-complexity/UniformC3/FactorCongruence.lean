import Programme.«20261102-1249-proof-complexity».UniformC3.ExplicitHarmonic

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Programme.«20261102-1249-proof-complexity».UniformC3.Block

abbrev Cong (p : Nat) (a b : Int) : Prop := (p : Int) ∣ a-b

theorem cong_refl (p : Nat) (a : Int) : Cong p a a := by simp [Cong]

theorem cong_trans {p : Nat} {a b c : Int} (h : Cong p a b) (h' : Cong p b c) : Cong p a c := by
  have h'' := Int.dvd_add h h'
  change (p : Int) ∣ a-c
  rwa [show a-b+(b-c)=a-c by omega] at h''

theorem cong_mul {p : Nat} {a b c d : Int} (h : Cong p a b) (h' : Cong p c d) :
    Cong p (a*c) (b*d) := by
  have he : a*c-b*d = (a-b)*c + b*(c-d) := by grind
  rw [show Cong p (a*c) (b*d) ↔ (p : Int) ∣ a*c-b*d from Iff.rfl,he]
  exact Int.dvd_add (Int.dvd_mul_of_dvd_left h) (Int.dvd_mul_of_dvd_right h')

theorem cong_scale {p : Nat} {a b : Int} (h : Cong p a b) (s : Int) : Cong p (s*a) (s*b) :=
  cong_mul (cong_refl p s) h

theorem cong_eq {p : Nat} {a b c : Int} (he : a=b) (h : Cong p b c) : Cong p a c := he ▸ h

def sign (n : Nat) : Int := (-1)^n
def fac (n : Nat) : Int := factorial n

theorem fac_succ (n : Nat) : fac (n+1) = (n+1 : Nat) * fac n := by
  simp [fac,factorial]

theorem sign_succ (n : Nat) : sign (n+1) = -sign n := by simp [sign,Int.pow_succ]

theorem sign_square (n : Nat) : sign n * sign n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sign_succ,Int.neg_mul_neg,ih]

theorem sign_add (a b : Nat) : sign (a+b) = sign a * sign b := by simp [sign,Int.pow_add]

theorem sign_pair (a b c u v : Nat) :
    sign (a+b+u) * sign (a+c+v) = sign (b+c) * sign (u+v) := by
  simp only [sign_add]
  calc
    _ = (sign a * sign a) * (sign b * sign c * (sign u * sign v)) := by
      simp [Int.mul_assoc,Int.mul_comm,Int.mul_left_comm]
    _ = _ := by rw [sign_square]; simp

/-- Signed factorial reflection; valid even for composite moduli. -/
theorem factorial_reflection (p : Nat) : ∀ r, r ≤ p-1 →
    Cong p (sign r * fac r * fac (p-1-r)) (fac (p-1)) := by
  intro r
  induction r with
  | zero => intro hr; simp [Cong,sign,fac,factorial]
  | succ r ih =>
    intro hr
    have h := ih (by omega)
    have he : p-1-r = (p-1-(r+1))+1 := by omega
    have hp : 1 ≤ p := by omega
    have hc : ((p-1-r : Nat) : Int) + (r+1 : Nat) = (p : Int) := by omega
    have hf : fac (p-1-r) = ((p-1-r : Nat) : Int) * fac (p-1-(r+1)) := by
      have h := fac_succ (p-1-(r+1))
      rwa [← he] at h
    have hd : (sign (r+1) * fac (r+1) * fac (p-1-(r+1))) -
        (sign r * fac r * fac (p-1-r)) =
        (p : Int) * (-sign r * fac r * fac (p-1-(r+1))) := by
      rw [sign_succ,fac_succ,hf]
      grind only
    have hs : Cong p (sign (r+1) * fac (r+1) * fac (p-1-(r+1)))
        (sign r * fac r * fac (p-1-r)) := by
      unfold Cong; rw [hd]; exact Int.dvd_mul_right _ _
    exact cong_trans hs h


theorem reflection_pair (p r s t u : Nat) (hrs : r+s=p-1) (htu : t+u=p-1) :
    Cong p (sign r * sign t * fac r * fac s * fac t * fac u)
      (fac (p-1) * fac (p-1)) := by
  have h1 := factorial_reflection p r (by omega)
  have h2 := factorial_reflection p t (by omega)
  rw [show p-1-r=s by omega] at h1
  rw [show p-1-t=u by omega] at h2
  simpa [Int.mul_assoc,Int.mul_comm,Int.mul_left_comm] using cong_mul h1 h2

theorem factorial_tail {p : Nat} (hp : 2 ≤ p) : Cong p (fac (p-2)) (-fac (p-1)) := by
  have he : p-1=(p-2)+1 := by omega
  have h := fac_succ (p-2)
  rw [← he] at h
  have hc : ((p-1 : Nat) : Int)+1 = (p : Int) := by omega
  have hd : fac (p-2) - (-fac (p-1)) = (p : Int)*fac (p-2) := by
    rw [h]; grind only
  unfold Cong; rw [hd]; exact Int.dvd_mul_right _ _

def commonValue (p : Nat) : Int := -(fac (p-1)*fac (p-1)*fac (p-1))

theorem main_pair {p : Nat} (hp : 2 ≤ p) (r s t u : Nat)
    (hrs : r+s=p-1) (htu : t+u=p-1) :
    Cong p (fac (p-2) * (sign r * sign t * fac r * fac s * fac t * fac u)) (commonValue p) := by
  have h1 := cong_scale (reflection_pair p r s t u hrs htu) (fac (p-2))
  have h2 := cong_mul (factorial_tail hp) (cong_refl p (fac (p-1)*fac (p-1)))
  simpa [commonValue,Int.mul_assoc,Int.neg_mul] using cong_trans h1 h2

theorem diagonal_pair (p r s t u : Nat) (hrs : r+s=p-1) (htu : t+u=p-1) :
    Cong p (-fac (p-1) * (sign r * sign t * fac r * fac s * fac t * fac u)) (commonValue p) := by
  simpa [commonValue,Int.mul_assoc,Int.neg_mul] using
    cong_scale (reflection_pair p r s t u hrs htu) (-fac (p-1))

#print axioms factorial_reflection
end Programme.«20261102-1249-proof-complexity».UniformC3.Block
