/-!
# Central binomial bound

`g a b` is the binomial coefficient $\binom{a+b}{a}$, defined by Pascal's rule (core Lean has no
`Nat.choose`). Main result `cb_bound`: $\binom{2m}{m}^2(3m+1)\le16^m$ (step 5 of the Hall plan).
-/

namespace Programme.«20261025-0459b-proof-complexity».CBinom

/-- `g a b` = number of lattice paths with `a` right and `b` up steps, i.e. `C(a+b, a)`. -/
def g : Nat → Nat → Nat
  | 0, _ => 1
  | _ + 1, 0 => 1
  | a + 1, b + 1 => g a (b + 1) + g (a + 1) b

theorem g_zero_right : ∀ a, g a 0 = 1
  | 0 => by simp [g]
  | _ + 1 => by simp [g]

theorem g_symm : ∀ a b, g a b = g b a
  | 0, 0 => rfl
  | 0, _ + 1 => by simp [g]
  | _ + 1, 0 => by simp [g]
  | a + 1, b + 1 => by
    simp only [g]; rw [g_symm a (b + 1), g_symm (a + 1) b]; omega

theorem g_one : ∀ b, g 1 b = b + 1
  | 0 => by simp [g]
  | b + 1 => by simp only [g]; rw [g_one b]; omega

/-- Absorption: `(a+1) C(a+b+1, a+1) = (a+b+1) C(a+b, a)`. -/
theorem absorb : ∀ b a, (a + 1) * g (a + 1) b = (a + b + 1) * g a b
  | 0, a => by simp [g_zero_right]
  | b + 1, 0 => by simp [g_one, g]
  | b + 1, a + 1 => by
    have ihb := absorb b (a + 1)
    have iha := absorb (b + 1) a
    have hx : g (a + 1 + 1) (b + 1) = g (a + 1) (b + 1) + g (a + 1 + 1) b := by simp [g]
    have hy : g (a + 1) (b + 1) = g a (b + 1) + g (a + 1) b := by simp [g]
    rw [hx, Nat.mul_add, ihb]
    generalize g (a + 1) (b + 1) = X at *
    generalize g a (b + 1) = Y at *
    generalize g (a + 1) b = Z at *
    subst hy
    grind

def c (m : Nat) : Nat := g m m

theorem c_succ (m : Nat) : (m + 1) * c (m + 1) = 2 * (2 * m + 1) * c m := by
  have h1 := absorb (m + 1) m
  have h2 := absorb m m
  rw [g_symm m (m + 1)] at h1
  unfold c
  have e : m + (m + 1) + 1 = 2 * (m + 1) := by omega
  rw [e] at h1
  have e2 : m + m + 1 = 2 * m + 1 := by omega
  rw [e2] at h2
  -- (m+1) c(m+1) = 2(m+1) g(m+1) m, and (m+1) g(m+1) m = (2m+1) c m
  have : (m + 1) * g (m + 1) (m + 1) = 2 * ((m + 1) * g (m + 1) m) := by
    rw [h1]; simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  rw [this, h2, Nat.mul_assoc]

theorem key (m : Nat) : 4 * (2 * m + 1) ^ 2 * (3 * m + 4) ≤ 16 * (m + 1) ^ 2 * (3 * m + 1) := by
  have : 4 * (2 * m + 1) ^ 2 * (3 * m + 4) + 4 * m = 16 * (m + 1) ^ 2 * (3 * m + 1) := by
    grind
  omega

/-- $\binom{2m}{m}^2(3m+1)\le16^m$. -/
theorem cb_bound : ∀ m, c m ^ 2 * (3 * m + 1) ≤ 16 ^ m
  | 0 => by simp [c, g]
  | m + 1 => by
    have ih := cb_bound m
    have hs := c_succ m
    have hp : 0 < (m + 1) ^ 2 := Nat.pow_pos (Nat.succ_pos m)
    refine Nat.le_of_mul_le_mul_left ?_ hp
    calc (m + 1) ^ 2 * (c (m + 1) ^ 2 * (3 * (m + 1) + 1))
        = ((m + 1) * c (m + 1)) ^ 2 * (3 * m + 4) := by
          rw [Nat.mul_pow]; simp only [Nat.mul_assoc]; congr 2
      _ = 4 * (2 * m + 1) ^ 2 * (3 * m + 4) * c m ^ 2 := by
          rw [hs, Nat.mul_pow, Nat.mul_pow]
          grind
      _ ≤ 16 * (m + 1) ^ 2 * (3 * m + 1) * c m ^ 2 := Nat.mul_le_mul_right _ (key m)
      _ = 16 * (m + 1) ^ 2 * (c m ^ 2 * (3 * m + 1)) := by
          simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ 16 * (m + 1) ^ 2 * 16 ^ m := Nat.mul_le_mul_left _ ih
      _ = (m + 1) ^ 2 * 16 ^ (m + 1) := by
          rw [Nat.pow_succ 16 m]; simp only [Nat.mul_assoc, Nat.mul_comm]

end Programme.«20261025-0459b-proof-complexity».CBinom
