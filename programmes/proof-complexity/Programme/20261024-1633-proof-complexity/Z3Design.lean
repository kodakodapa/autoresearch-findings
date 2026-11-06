import Programme.«20261024-1633-proof-complexity».NS

/-!
# Designs on `ℤ₃^N` with values in `ℤ[ω]` (the lower-bound tool for mod-3 Tseitin)

`ZW` is `ℤ[ω]` (`ω² = -1 - ω`), with only the operations needed: addition, integer scaling and
multiplication by `ω` (`rot`). `csum3 N f` sums `f` over the assignments `a : ℕ → ℕ` with
`a i ∈ {0,1,2}` for `i < N` and `a i = 0` from `N` on. `four N h S = ∑_a h(a) ω^{⟨S,a⟩}` and
`design3 N co h = ∑_S co(S) · four N h S`, where a coefficient is `0` (`none`) or `ω^k` (`some k`).

`design3_zero` (rotation lemma): if `h` depends only on coordinates in `U ⊇ supp R`,
`⟨R,a⟩ ≡ s` wherever `h(a) ≠ 0`, `co(S + R) = ω^r co(S)` for `S ⊆ U`, and `r + s ≢ 0 (mod 3)`, then
`design3 N co h = 0` (the design is fixed by multiplication by `ω^{r+s} ≠ 1`).
`design3_one`: the design of the constant `1` is `co(0) · 3^N`.
-/

namespace Programme.«20261024-1633-proof-complexity».Z3Design

open Classical

/-- `x + y ω` in `ℤ[ω]`. -/
structure ZW where
  x : Int
  y : Int

namespace ZW

def zero : ZW := ⟨0, 0⟩
def add (z w : ZW) : ZW := ⟨z.x + w.x, z.y + w.y⟩
def smul (k : Int) (z : ZW) : ZW := ⟨k * z.x, k * z.y⟩
/-- Multiplication by `ω`. -/
def rot (z : ZW) : ZW := ⟨-z.y, z.x - z.y⟩
def rotN : Nat → ZW → ZW
  | 0, z => z
  | k + 1, z => rot (rotN k z)

theorem eq_of {z w : ZW} (h1 : z.x = w.x) (h2 : z.y = w.y) : z = w := by
  cases z; cases w; simp only at h1 h2; subst h1; subst h2; rfl

theorem add_comm (z w : ZW) : z.add w = w.add z := eq_of (by simp [add]; omega) (by simp [add]; omega)
theorem add_assoc (z w u : ZW) : (z.add w).add u = z.add (w.add u) :=
  eq_of (by simp [add]; omega) (by simp [add]; omega)
theorem add_zero (z : ZW) : z.add zero = z := eq_of (by simp [add, zero]) (by simp [add, zero])
theorem zero_add (z : ZW) : zero.add z = z := eq_of (by simp [add, zero]) (by simp [add, zero])

theorem rot_add (z w : ZW) : rot (z.add w) = (rot z).add (rot w) :=
  eq_of (by simp [rot, add]; omega) (by simp [rot, add]; omega)
theorem rot_zero : rot zero = zero := eq_of (by simp [rot, zero]) (by simp [rot, zero])
theorem rot_smul (k : Int) (z : ZW) : rot (smul k z) = smul k (rot z) :=
  eq_of (by simp [rot, smul, Int.mul_neg]) (by simp [rot, smul, Int.mul_sub])
theorem rot3 (z : ZW) : rot (rot (rot z)) = z := eq_of (by simp [rot]; omega) (by simp [rot]; omega)

theorem rotN_add (k : Nat) (z w : ZW) : rotN k (z.add w) = (rotN k z).add (rotN k w) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [rotN, ih, rot_add]
theorem rotN_zero (k : Nat) : rotN k zero = zero := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [rotN, ih, rot_zero]
theorem rotN_smul (k : Nat) (j : Int) (z : ZW) : rotN k (smul j z) = smul j (rotN k z) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [rotN, ih, rot_smul]
theorem rotN_rotN (j k : Nat) (z : ZW) : rotN j (rotN k z) = rotN (j + k) z := by
  induction j with
  | zero => simp [rotN]
  | succ j ih => rw [Nat.succ_add]; simp only [rotN, ih]
theorem rotN_rot (k : Nat) (z : ZW) : rotN k (rot z) = rot (rotN k z) := by
  have := rotN_rotN k 1 z; simp only [rotN] at this; rw [this]
theorem rotN_mod (k : Nat) (z : ZW) : rotN k z = rotN (k % 3) z := by
  induction k using Nat.strongRecOn with
  | _ k ih =>
    by_cases hk : k < 3
    · rw [Nat.mod_eq_of_lt hk]
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
      have h3 : rotN (m + 3) z = rotN m z := by
        rw [← rotN_rotN]; simp only [rotN, rot3]
      rw [h3, ih m (by omega), show (m + 3) % 3 = m % 3 by omega]
theorem rotN_three (z : ZW) : rotN 3 z = z := by simp only [rotN, rot3]

/-- `z + ωz + ω²z = 0`. -/
theorem rot_sum (z : ZW) : (z.add (rot z)).add (rot (rot z)) = zero :=
  eq_of (by simp [add, rot, zero]; omega) (by simp [add, rot, zero]; omega)

/-- `ω^k z = z` with `k ≢ 0 (mod 3)` forces `z = 0`. -/
theorem rotN_fixed (k : Nat) (hk : k % 3 ≠ 0) (z : ZW) (h : rotN k z = z) : z = zero := by
  rw [rotN_mod] at h
  have : k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases this with h1 | h1 <;> rw [h1] at h <;> simp only [rotN] at h
  · have e1 := congrArg ZW.x h; have e2 := congrArg ZW.y h
    simp only [rot] at e1 e2
    exact eq_of (by simp [zero]; omega) (by simp [zero]; omega)
  · have e1 := congrArg ZW.x h; have e2 := congrArg ZW.y h
    simp only [rot] at e1 e2
    exact eq_of (by simp [zero]; omega) (by simp [zero]; omega)

end ZW

open ZW

/-! ## Sums over `{0,1,2}^N` -/

def seta (a : Nat → Nat) (i v : Nat) : Nat → Nat := fun j => if j = i then v else a j

def csum3 : Nat → ((Nat → Nat) → ZW) → ZW
  | 0, f => f (fun _ => 0)
  | N + 1, f => csum3 N (fun a => (f (seta a N 0)).add ((f (seta a N 1)).add (f (seta a N 2))))

def Valid3 (N : Nat) (a : Nat → Nat) : Prop := (∀ i, i < N → a i < 3) ∧ ∀ i, N ≤ i → a i = 0

theorem valid_seta {N : Nat} {a : Nat → Nat} (ha : Valid3 N a) {b : Nat} (hb : b < 3) :
    Valid3 (N + 1) (seta a N b) := by
  constructor
  · intro i hi; simp only [seta]; by_cases h : i = N
    · rw [ite_eq_left h]; exact hb
    · rw [ite_eq_right h]; exact ha.1 i (by omega)
  · intro i hi; simp only [seta]; rw [ite_eq_right (by omega)]; exact ha.2 i (by omega)

theorem csum3_add (N : Nat) (f g : (Nat → Nat) → ZW) :
    csum3 N (fun a => (f a).add (g a)) = (csum3 N f).add (csum3 N g) := by
  induction N generalizing f g with
  | zero => rfl
  | succ N ih =>
    simp only [csum3]
    rw [← ih]; congr 1; funext a
    apply eq_of <;> simp [ZW.add] <;> omega

theorem csum3_rotN (N k : Nat) (f : (Nat → Nat) → ZW) :
    csum3 N (fun a => rotN k (f a)) = rotN k (csum3 N f) := by
  induction N generalizing f with
  | zero => rfl
  | succ N ih =>
    simp only [csum3]
    rw [← ih]; congr 1; funext a; rw [rotN_add, rotN_add]

theorem csum3_smul (N : Nat) (k : Int) (f : (Nat → Nat) → ZW) :
    csum3 N (fun a => smul k (f a)) = smul k (csum3 N f) := by
  induction N generalizing f with
  | zero => rfl
  | succ N ih =>
    simp only [csum3]
    rw [← ih]; congr 1; funext a
    apply eq_of <;> simp [ZW.add, smul, Int.mul_add]

theorem csum3_congr (N : Nat) (f g : (Nat → Nat) → ZW)
    (h : ∀ a, Valid3 N a → f a = g a) : csum3 N f = csum3 N g := by
  induction N generalizing f g with
  | zero => exact h _ ⟨fun i hi => by omega, fun _ _ => rfl⟩
  | succ N ih =>
    simp only [csum3]
    apply ih
    intro a ha
    rw [h _ (valid_seta ha (by omega)), h _ (valid_seta ha (by omega)),
      h _ (valid_seta ha (by omega))]

theorem csum3_zero (N : Nat) : csum3 N (fun _ => zero) = zero := by
  have := csum3_smul N 0 (fun _ => zero)
  have e : smul 0 zero = zero := eq_of (by simp [smul, zero]) (by simp [smul, zero])
  have e2 : ∀ z, smul 0 z = zero := fun z => eq_of (by simp [smul, zero]) (by simp [smul, zero])
  simp only [e2] at this; exact this

theorem csum3_list {α} (N : Nat) (L : List α) (h : α → (Nat → Nat) → ZW) :
    csum3 N (fun a => L.foldr (fun i acc => (h i a).add acc) zero)
      = L.foldr (fun i acc => (csum3 N (h i)).add acc) zero := by
  induction L with
  | nil => exact csum3_zero N
  | cons x L ih => simp only [List.foldr_cons]; rw [csum3_add, ih]

/-! ## Translation invariance -/

def ashift (a R : Nat → Nat) : Nat → Nat := fun i => (a i + R i) % 3

theorem valid_ashift {N : Nat} {a R : Nat → Nat} (ha : Valid3 N a) (hR : Valid3 N R) :
    Valid3 N (ashift a R) := by
  constructor
  · intro i _; simp only [ashift]; omega
  · intro i hi; simp only [ashift, ha.2 i hi, hR.2 i hi]

theorem seta_ashift (a R : Nat → Nat) (N b : Nat) :
    ashift (seta a N b) R = seta (ashift a (seta R N 0)) N ((b + R N) % 3) := by
  funext i; simp only [ashift, seta]; by_cases h : i = N
  · rw [ite_eq_left h, ite_eq_left h, h]
  · rw [ite_eq_right h, ite_eq_right h, ite_eq_right h]

theorem csum3_shift (N : Nat) (R : Nat → Nat) (hR : Valid3 N R) (f : (Nat → Nat) → ZW) :
    csum3 N (fun a => f (ashift a R)) = csum3 N f := by
  induction N generalizing f R with
  | zero =>
    simp only [csum3]; congr 1; funext i; simp [ashift, hR.2 i (Nat.zero_le _)]
  | succ N ih =>
    simp only [csum3]
    have hR' : Valid3 N (seta R N 0) := by
      constructor
      · intro i hi; simp only [seta]; rw [ite_eq_right (by omega)]; exact hR.1 i (by omega)
      · intro i hi; simp only [seta]; by_cases h : i = N
        · rw [ite_eq_left h]
        · rw [ite_eq_right h]; exact hR.2 i (by omega)
    simp only [seta_ashift]
    have := ih (seta R N 0) hR'
      (fun a => (f (seta a N ((0 + R N) % 3))).add
        ((f (seta a N ((1 + R N) % 3))).add (f (seta a N ((2 + R N) % 3)))))
    rw [this]
    congr 1; funext a
    have hRN := hR.1 N (by omega)
    have : R N = 0 ∨ R N = 1 ∨ R N = 2 := by omega
    rcases this with h | h | h <;> rw [h] <;> (apply eq_of <;> simp [ZW.add] <;> omega)

/-- A sum fixed by multiplication by `ω^k`, `k ≢ 0`, vanishes. -/
theorem csum3_rot_zero (N k : Nat) (hk : k % 3 ≠ 0) (R : Nat → Nat) (hR : Valid3 N R)
    (f : (Nat → Nat) → ZW) (hf : ∀ a, Valid3 N a → f (ashift a R) = rotN k (f a)) :
    csum3 N f = zero := by
  have h1 := csum3_shift N R hR f
  rw [csum3_congr N _ _ hf, csum3_rotN] at h1
  exact rotN_fixed k hk _ h1

/-! ## Characters `ω^{⟨S,a⟩}` -/

def ex : Nat → (Nat → Nat) → (Nat → Nat) → Nat
  | 0, _, _ => 0
  | N + 1, S, a => S N * a N + ex N S a

theorem ex_comm (N : Nat) (S a : Nat → Nat) : ex N S a = ex N a S := by
  induction N with
  | zero => rfl
  | succ N ih => simp only [ex, ih, Nat.mul_comm]

theorem mul_mod3 (s t : Nat) : s * (t % 3) % 3 = s * t % 3 := by
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

theorem ex_ashift (N : Nat) (S a R : Nat → Nat) :
    ex N S (ashift a R) % 3 = (ex N S a + ex N S R) % 3 := by
  induction N with
  | zero => rfl
  | succ N ih =>
    simp only [ex, ashift]
    have h1 := mul_mod3 (S N) (a N + R N)
    rw [Nat.mul_add] at h1
    omega

theorem ex_seta (N i : Nat) (hi : N ≤ i) (S a : Nat → Nat) (b : Nat) :
    ex N S (seta a i b) = ex N S a := by
  induction N with
  | zero => rfl
  | succ N ih =>
    have : seta a i b N = a N := by simp only [seta]; rw [ite_eq_right (by omega)]
    simp only [ex, ih (by omega), this]

def one : ZW := ⟨1, 0⟩

/-- `∑_a ω^{⟨S,a⟩} z = 3^N z` if `S ≡ 0` on `[N]`, else `0`. -/
theorem csum3_chr (N : Nat) (S : Nat → Nat) (z : ZW) :
    csum3 N (fun a => rotN (ex N S a) z)
      = if (∀ i, i < N → S i % 3 = 0) then smul (3 ^ N) z else zero := by
  induction N generalizing z with
  | zero =>
    simp only [csum3, ex, rotN]
    rw [ite_eq_left (fun i hi => by omega)]
    exact eq_of (by simp [smul]) (by simp [smul])
  | succ N ih =>
    simp only [csum3, ex, ex_seta N N (Nat.le_refl _)]
    simp only [seta, ite_true]
    have e : ∀ a, (rotN (S N * 0 + ex N S a) z).add
        ((rotN (S N * 1 + ex N S a) z).add (rotN (S N * 2 + ex N S a) z))
        = rotN (ex N S a) ((z.add (rotN (S N) z)).add (rotN (S N * 2) z)) := by
      intro a
      rw [rotN_add, rotN_add, rotN_rotN, rotN_rotN, ZW.add_assoc]
      simp only [Nat.mul_zero, Nat.zero_add, Nat.mul_one]
      rw [Nat.add_comm (ex N S a) (S N), Nat.add_comm (ex N S a) (S N * 2)]
    simp only [e]
    rw [ih]
    by_cases hN : S N % 3 = 0
    · have h0 : (z.add (rotN (S N) z)).add (rotN (S N * 2) z) = smul 3 z := by
        rw [rotN_mod, hN, rotN_mod (S N * 2), Nat.mul_mod, hN]
        exact eq_of (by simp [ZW.add, smul, rotN]; omega) (by simp [ZW.add, smul, rotN]; omega)
      rw [h0]
      by_cases hc : ∀ i, i < N → S i % 3 = 0
      · have : ∀ i, i < N + 1 → S i % 3 = 0 := by
          intro i hi; by_cases h : i = N
          · rw [h]; exact hN
          · exact hc i (by omega)
        rw [ite_eq_left hc, ite_eq_left this]
        exact eq_of (by simp [smul, Int.pow_succ, Int.mul_assoc, Int.mul_comm])
          (by simp [smul, Int.pow_succ, Int.mul_assoc, Int.mul_comm])
      · have : ¬ ∀ i, i < N + 1 → S i % 3 = 0 := fun h => hc (fun i hi => h i (by omega))
        rw [ite_eq_right hc, ite_eq_right this]
    · have h0 : (z.add (rotN (S N) z)).add (rotN (S N * 2) z) = zero := by
        rw [rotN_mod, rotN_mod (S N * 2), Nat.mul_mod]
        have : S N % 3 = 1 ∨ S N % 3 = 2 := by omega
        rcases this with h | h <;> rw [h] <;> simp only [rotN] <;>
          exact eq_of (by simp [ZW.add, rot, zero]; omega) (by simp [ZW.add, rot, zero]; omega)
      rw [h0]
      have : ¬ ∀ i, i < N + 1 → S i % 3 = 0 := fun h => hN (h N (by omega))
      rw [ite_eq_right this]
      by_cases hc : ∀ i, i < N → S i % 3 = 0
      · rw [ite_eq_left hc]; exact eq_of (by simp [smul, zero]) (by simp [smul, zero])
      · rw [ite_eq_right hc]

theorem csum3_delta (N : Nat) (g : (Nat → Nat) → ZW) :
    csum3 N (fun S => if (∀ i, i < N → S i % 3 = 0) then g S else zero) = g (fun _ => 0) := by
  induction N generalizing g with
  | zero => simp [csum3]
  | succ N ih =>
    simp only [csum3]
    have e : ∀ a : Nat → Nat,
        ((if (∀ i, i < N + 1 → seta a N 0 i % 3 = 0) then g (seta a N 0) else zero).add
          ((if (∀ i, i < N + 1 → seta a N 1 i % 3 = 0) then g (seta a N 1) else zero).add
           (if (∀ i, i < N + 1 → seta a N 2 i % 3 = 0) then g (seta a N 2) else zero)))
        = if (∀ i, i < N → a i % 3 = 0) then g (seta a N 0) else zero := by
      intro a
      have h1 : ¬ ∀ i, i < N + 1 → seta a N 1 i % 3 = 0 := by
        intro h; have := h N (by omega); simp [seta] at this
      have h2 : ¬ ∀ i, i < N + 1 → seta a N 2 i % 3 = 0 := by
        intro h; have := h N (by omega); simp [seta] at this
      rw [ite_eq_right h1, ite_eq_right h2, ZW.add_zero, ZW.add_zero]
      have h0 : (∀ i, i < N + 1 → seta a N 0 i % 3 = 0) ↔ (∀ i, i < N → a i % 3 = 0) := by
        constructor
        · intro h i hi; have := h i (by omega); simp only [seta] at this
          rwa [ite_eq_right (by omega)] at this
        · intro h i hi; simp only [seta]; by_cases hiN : i = N
          · simp [hiN]
          · rw [ite_eq_right hiN]; exact h i (by omega)
      by_cases hc : ∀ i, i < N → a i % 3 = 0
      · rw [ite_eq_left (h0.mpr hc), ite_eq_left hc]
      · rw [ite_eq_right (fun h => hc (h0.mp h)), ite_eq_right hc]
    simp only [e]
    rw [ih (fun a => g (seta a N 0))]
    congr 1; funext i; simp [seta]

/-! ## Fourier coefficients and designs -/

/-- `ĥ(S) = ∑_a h(a) ω^{⟨S,a⟩}`. -/
def four (N : Nat) (h : (Nat → Nat) → Int) (S : Nat → Nat) : ZW :=
  csum3 N (fun a => rotN (ex N S a) ⟨h a, 0⟩)

/-- A coefficient `0` (`none`) or `ω^k` (`some k`) applied to `z`. -/
def cm : Option Nat → ZW → ZW
  | none, _ => zero
  | some k, z => rotN k z

theorem cm_add (o : Option Nat) (z w : ZW) : cm o (z.add w) = (cm o z).add (cm o w) := by
  cases o
  · simp [cm, ZW.add_zero]
  · simp [cm, rotN_add]
theorem cm_smul (o : Option Nat) (k : Int) (z : ZW) : cm o (smul k z) = smul k (cm o z) := by
  cases o
  · exact eq_of (by simp [cm, smul, zero]) (by simp [cm, smul, zero])
  · simp [cm, rotN_smul]
theorem cm_rotN (o : Option Nat) (k : Nat) (z : ZW) : cm o (rotN k z) = rotN k (cm o z) := by
  cases o
  · simp [cm, rotN_zero]
  · simp [cm, rotN_rotN, Nat.add_comm]
theorem cm_zero (o : Option Nat) : cm o zero = zero := by
  cases o
  · rfl
  · simp [cm, rotN_zero]

/-- `E_co(h) = ∑_S co(S) ĥ(S)`. -/
def design3 (N : Nat) (co : (Nat → Nat) → Option Nat) (h : (Nat → Nat) → Int) : ZW :=
  csum3 N (fun S => cm (co S) (four N h S))

theorem four_congr (N : Nat) (f g : (Nat → Nat) → Int) (h : ∀ a, Valid3 N a → f a = g a)
    (S : Nat → Nat) : four N f S = four N g S :=
  csum3_congr N _ _ (fun a ha => by rw [h a ha])

theorem design3_congr (N : Nat) (co : (Nat → Nat) → Option Nat) (f g : (Nat → Nat) → Int)
    (h : ∀ a, Valid3 N a → f a = g a) : design3 N co f = design3 N co g := by
  unfold design3; congr 1; funext S; rw [four_congr N f g h]

theorem four_add (N : Nat) (f g : (Nat → Nat) → Int) (S : Nat → Nat) :
    four N (fun a => f a + g a) S = (four N f S).add (four N g S) := by
  unfold four; rw [← csum3_add]; congr 1; funext a
  have : (⟨f a + g a, 0⟩ : ZW) = (⟨f a, 0⟩ : ZW).add ⟨g a, 0⟩ := eq_of (by simp [ZW.add]) (by simp [ZW.add])
  rw [this, rotN_add]

theorem four_smul (N : Nat) (k : Int) (f : (Nat → Nat) → Int) (S : Nat → Nat) :
    four N (fun a => k * f a) S = smul k (four N f S) := by
  unfold four; rw [← csum3_smul]; congr 1; funext a
  have : (⟨k * f a, 0⟩ : ZW) = smul k ⟨f a, 0⟩ := eq_of (by simp [smul]) (by simp [smul])
  rw [this, rotN_smul]

theorem design3_add (N : Nat) (co : (Nat → Nat) → Option Nat) (f g : (Nat → Nat) → Int) :
    design3 N co (fun a => f a + g a) = (design3 N co f).add (design3 N co g) := by
  unfold design3; rw [← csum3_add]; congr 1; funext S; rw [four_add, cm_add]

theorem design3_smul (N : Nat) (co : (Nat → Nat) → Option Nat) (k : Int) (f : (Nat → Nat) → Int) :
    design3 N co (fun a => k * f a) = smul k (design3 N co f) := by
  unfold design3; rw [← csum3_smul]; congr 1; funext S; rw [four_smul, cm_smul]

theorem design3_list {α} (N : Nat) (co : (Nat → Nat) → Option Nat) (L : List α)
    (h : α → (Nat → Nat) → Int) (hz : ∀ i ∈ L, design3 N co (h i) = zero) :
    design3 N co (fun a => (L.map fun i => h i a).sum) = zero := by
  induction L with
  | nil =>
    have := design3_smul N co 0 (fun _ => 0)
    simp only [Int.zero_mul] at this
    simp only [List.map_nil, List.sum_nil]; rw [this]
    exact eq_of (by simp [smul, zero]) (by simp [smul, zero])
  | cons x L ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [design3_add, hz x List.mem_cons_self,
      ih (fun i hi => hz i (List.mem_cons_of_mem _ hi)), ZW.add_zero]

theorem design3_one (N : Nat) (co : (Nat → Nat) → Option Nat) :
    design3 N co (fun _ => 1) = cm (co (fun _ => 0)) ⟨3 ^ N, 0⟩ := by
  unfold design3 four
  simp only [csum3_chr]
  have : (fun S => cm (co S) (if (∀ i, i < N → S i % 3 = 0) then smul (3 ^ N) ⟨1, 0⟩ else zero))
      = fun S => if (∀ i, i < N → S i % 3 = 0) then cm (co S) ⟨3 ^ N, 0⟩ else zero := by
    funext S; split
    · congr 1; exact eq_of (by simp [smul]) (by simp [smul])
    · exact cm_zero _
  rw [this, csum3_delta]

/-- Fourier coefficients vanish outside the coordinates `h` depends on. -/
theorem four_zero (N e : Nat) (he : e < N) (h : (Nat → Nat) → Int) (S : Nat → Nat)
    (hS : S e % 3 ≠ 0)
    (hh : ∀ a, Valid3 N a → h (ashift a (fun i => if i = e then 1 else 0)) = h a) :
    four N h S = zero := by
  have hR : Valid3 N (fun i => if i = e then 1 else 0) := by
    constructor
    · intro i _; show (if i = e then 1 else 0) < 3; split <;> omega
    · intro i hi; show (if i = e then 1 else 0) = 0; rw [ite_eq_right (by omega)]
  apply csum3_rot_zero N (S e) hS _ hR
  intro a ha
  rw [hh a ha, rotN_rotN, rotN_mod, rotN_mod (S e + _)]
  congr 1
  rw [ex_ashift]
  have : ex N S (fun i => if i = e then 1 else 0) = S e := by
    clear hh hS ha hR
    induction N with
    | zero => omega
    | succ N ih =>
      simp only [ex]
      by_cases h : e = N
      · subst h
        have : ex e S (fun i => if i = e then 1 else 0) = 0 := by
          have : ∀ M, M ≤ e → ex M S (fun i => if i = e then 1 else 0) = 0 := by
            intro M hM
            induction M with
            | zero => rfl
            | succ M ihM => simp only [ex]; rw [ihM (by omega), ite_eq_right (by omega)]; simp
          exact this e (Nat.le_refl _)
        rw [this, ite_eq_left rfl]; simp
      · rw [ih (by omega), ite_eq_right (by omega)]; simp
  rw [this]; omega

/-- **Rotation lemma.** -/
theorem design3_zero (N : Nat) (R : Nat → Nat) (U : Nat → Bool) (r s : Nat)
    (co : (Nat → Nat) → Option Nat) (h : (Nat → Nat) → Int)
    (hR : Valid3 N R) (hRU : ∀ i, i < N → R i ≠ 0 → U i = true) (hrs : (r + s) % 3 ≠ 0)
    (h1 : ∀ a, Valid3 N a → h a = 0 ∨ ex N R a % 3 = s % 3)
    (h2 : ∀ a, Valid3 N a → ∀ e, e < N → U e = false →
      h (ashift a (fun i => if i = e then 1 else 0)) = h a)
    (h3 : ∀ S, Valid3 N S → (∀ i, i < N → S i ≠ 0 → U i = true) →
      ∀ z, cm (co (ashift S R)) z = rotN r (cm (co S) z)) :
    design3 N co h = zero := by
  -- `ĥ(S + R) = ω^s ĥ(S)`
  have f1 : ∀ S, four N h (ashift S R) = rotN s (four N h S) := by
    intro S
    unfold four
    rw [← csum3_rotN]
    apply csum3_congr
    intro a ha
    rw [rotN_rotN]
    rcases h1 a ha with h0 | h0
    · rw [h0]
      have e : ∀ k, rotN k (⟨0, 0⟩ : ZW) = zero := fun k => rotN_zero k
      rw [e, e]
    · rw [rotN_mod, rotN_mod (s + _)]; congr 1
      rw [ex_comm, ex_ashift, ex_comm N a R, ex_comm N a S]; omega
  have key : ∀ S, Valid3 N S →
      cm (co (ashift S R)) (four N h (ashift S R)) = rotN (r + s) (cm (co S) (four N h S)) := by
    intro S hS
    by_cases hsub : ∀ i, i < N → S i ≠ 0 → U i = true
    · rw [h3 S hS hsub, f1, cm_rotN, rotN_rotN, Nat.add_comm r s]
    · have : ∃ e, e < N ∧ S e ≠ 0 ∧ U e = false := by
        apply Classical.byContradiction; intro hno; apply hsub
        intro i hi hSi
        cases hU : U i
        · exact absurd ⟨i, hi, hSi, hU⟩ hno
        · rfl
      obtain ⟨e, he, hSe, hUe⟩ := this
      have hRe : R e = 0 := by
        apply Classical.byContradiction; intro hR0
        rw [hRU e he hR0] at hUe; exact absurd hUe (by simp)
      have hS3 := hS.1 e he
      rw [four_zero N e he h S (by omega) (fun a ha => h2 a ha e he hUe),
        four_zero N e he h (ashift S R) (by simp only [ashift, hRe]; omega)
          (fun a ha => h2 a ha e he hUe), cm_zero, cm_zero, rotN_zero]
  have hd := csum3_shift N R hR (fun S => cm (co S) (four N h S))
  rw [csum3_congr N _ _ key, csum3_rotN] at hd
  exact rotN_fixed (r + s) hrs _ hd

end Programme.«20261024-1633-proof-complexity».Z3Design

#print axioms Programme.«20261024-1633-proof-complexity».Z3Design.design3_zero
#print axioms Programme.«20261024-1633-proof-complexity».Z3Design.design3_one
