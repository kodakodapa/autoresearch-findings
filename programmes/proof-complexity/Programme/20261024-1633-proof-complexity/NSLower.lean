import Programme.«20261024-1633-proof-complexity».NS

/-!
# Designs on the Boolean cube (the lower-bound tool for Nullstellensatz)

`csum N f` sums `f` over the `2^N` assignments that are `false` from `N` on; `chi N S a` is the
character `(-1)^{|S ∩ a ∩ [N]|}`; `design N c h = ∑_S c(S) ∑_a h(a) χ_S(a)` is a linear functional
on functions of the cube that depends only on their values, so it respects every pointwise
identity, in particular the (cube-semantic) Nullstellensatz identity of `Work.NS.NSRefutation`.

`design_zero` (involution lemma): if `h` depends only on coordinates in `U ⊇ R`, `h · χ_R = -σ h`
(`σ² = 1`) and `c(S ⊕ R) = σ c(S)` for every `S ⊆ U`, then `design N c h = 0` (pair `S` with
`S ⊕ R`). `design_one`: the design of the constant `1` is `c(∅) · 2^N`.
-/

namespace Programme.«20261024-1633-proof-complexity».NSLower

open Classical

/-! ## Sums over the Boolean cube `{0,1}^N` (variables `≥ N` set to `false`) -/

def setb (a : Nat → Bool) (i : Nat) (b : Bool) : Nat → Bool := fun j => if j = i then b else a j

def bxor (a R : Nat → Bool) : Nat → Bool := fun i => a i ^^ R i

def csum : Nat → ((Nat → Bool) → Int) → Int
  | 0, f => f (fun _ => false)
  | N + 1, f => csum N (fun a => f (setb a N false) + f (setb a N true))

def Valid (N : Nat) (a : Nat → Bool) : Prop := ∀ i, N ≤ i → a i = false

theorem csum_add (N : Nat) (f g : (Nat → Bool) → Int) :
    csum N (fun a => f a + g a) = csum N f + csum N g := by
  induction N generalizing f g with
  | zero => rfl
  | succ N ih =>
    simp only [csum]
    rw [← ih]; congr 1; funext a; omega

theorem csum_mul (N : Nat) (k : Int) (f : (Nat → Bool) → Int) :
    csum N (fun a => k * f a) = k * csum N f := by
  induction N generalizing f with
  | zero => rfl
  | succ N ih =>
    simp only [csum]
    rw [← ih]; congr 1; funext a; rw [Int.mul_add]

theorem csum_neg (N : Nat) (f : (Nat → Bool) → Int) :
    csum N (fun a => -f a) = -csum N f := by
  have := csum_mul N (-1) f
  simp only [Int.neg_one_mul] at this; exact this

theorem csum_congr (N : Nat) (f g : (Nat → Bool) → Int)
    (h : ∀ a, Valid N a → f a = g a) : csum N f = csum N g := by
  induction N generalizing f g with
  | zero => exact h _ (fun _ _ => rfl)
  | succ N ih =>
    simp only [csum]
    apply ih
    intro a ha
    have v : ∀ b, Valid (N + 1) (setb a N b) := by
      intro b i hi; simp only [setb]; rw [ite_eq_right (by omega)]; exact ha i (by omega)
    rw [h _ (v false), h _ (v true)]

theorem csum_list {α} (N : Nat) (L : List α) (h : α → (Nat → Bool) → Int) :
    csum N (fun a => (L.map fun i => h i a).sum) = (L.map fun i => csum N (h i)).sum := by
  induction L with
  | nil =>
    have := csum_mul N 0 (fun _ => 0)
    simp only [Int.zero_mul] at this; simpa using this
  | cons x L ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [csum_add, ih]

theorem setb_bxor (a R : Nat → Bool) (N : Nat) (b : Bool) :
    bxor (setb a N b) R = setb (bxor a (setb R N false)) N (b ^^ R N) := by
  funext i; simp only [bxor, setb]; by_cases h : i = N <;> simp [h]

/-- Translation invariance of cube sums. -/
theorem csum_bxor (N : Nat) (R : Nat → Bool) (hR : Valid N R) (f : (Nat → Bool) → Int) :
    csum N (fun a => f (bxor a R)) = csum N f := by
  induction N generalizing f R with
  | zero =>
    simp only [csum]; congr 1; funext i; simp [bxor, hR i (Nat.zero_le _)]
  | succ N ih =>
    simp only [csum]
    have hR' : Valid N (setb R N false) := by
      intro i hi; simp only [setb]; by_cases h : i = N
      · simp [h]
      · rw [ite_eq_right h]; exact hR i (by omega)
    simp only [setb_bxor]
    have := ih (setb R N false) hR'
      (fun a => f (setb a N (false ^^ R N)) + f (setb a N (true ^^ R N)))
    rw [this]
    congr 1; funext a
    cases R N <;> simp <;> omega

/-- A sum that changes sign under flipping a coordinate `e < N` vanishes. -/
theorem csum_flip_zero (N e : Nat) (he : e < N) (f : (Nat → Bool) → Int)
    (hf : ∀ a, Valid N a → f (bxor a (fun i => i == e)) = -f a) : csum N f = 0 := by
  have hv : Valid N (fun i => i == e) := by
    intro i hi; simp; omega
  have h1 := csum_bxor N _ hv f
  rw [csum_congr N _ (fun a => -f a) hf, csum_neg] at h1
  omega

theorem csum_delta (N : Nat) (g : (Nat → Bool) → Int) :
    csum N (fun S => if (∀ i, i < N → S i = false) then g S else 0) = g (fun _ => false) := by
  induction N generalizing g with
  | zero => simp [csum]
  | succ N ih =>
    simp only [csum]
    have e : ∀ a : Nat → Bool,
        ((if (∀ i, i < N + 1 → setb a N false i = false) then g (setb a N false) else 0) +
          (if (∀ i, i < N + 1 → setb a N true i = false) then g (setb a N true) else 0))
        = if (∀ i, i < N → a i = false) then g (setb a N false) else 0 := by
      intro a
      have h2 : ¬ ∀ i, i < N + 1 → setb a N true i = false := by
        intro h; have := h N (by omega); simp [setb] at this
      rw [ite_eq_right h2, Int.add_zero]
      have h1 : (∀ i, i < N + 1 → setb a N false i = false) ↔ (∀ i, i < N → a i = false) := by
        constructor
        · intro h i hi; have := h i (by omega); simp only [setb] at this
          rwa [ite_eq_right (by omega)] at this
        · intro h i hi; simp only [setb]; by_cases hiN : i = N
          · simp [hiN]
          · rw [ite_eq_right hiN]; exact h i (by omega)
      by_cases hc : ∀ i, i < N → a i = false
      · rw [ite_eq_left (h1.mpr hc), ite_eq_left hc]
      · rw [ite_eq_right (fun h => hc (h1.mp h)), ite_eq_right hc]
    simp only [e]
    rw [ih (fun a => g (setb a N false))]
    congr 1; funext i; simp [setb]

/-! ## Characters `χ_S(a) = (-1)^{|S ∩ a|}` on the first `N` coordinates -/

def sg (b : Bool) : Int := if b then -1 else 1

theorem sg_xor (b c d : Bool) : sg ((b ^^ c) && d) = sg (b && d) * sg (c && d) := by
  cases b <;> cases c <;> cases d <;> rfl

theorem sg_sq (b : Bool) : sg b * sg b = 1 := by cases b <;> rfl

def chi : Nat → (Nat → Bool) → (Nat → Bool) → Int
  | 0, _, _ => 1
  | N + 1, S, a => sg (S N && a N) * chi N S a

theorem chi_sq (N : Nat) (S a : Nat → Bool) : chi N S a * chi N S a = 1 := by
  induction N with
  | zero => rfl
  | succ N ih =>
    simp only [chi]
    have e : ∀ (x y : Int), x * x = 1 → y * y = 1 → (x * y) * (x * y) = 1 := by
      intro x y hx hy
      rw [Int.mul_assoc, Int.mul_left_comm y x y, ← Int.mul_assoc, hx, hy]; rfl
    exact e _ _ (sg_sq _) ih

theorem chi_comm (N : Nat) (S a : Nat → Bool) : chi N S a = chi N a S := by
  induction N with
  | zero => rfl
  | succ N ih => simp only [chi, ih, Bool.and_comm]

theorem chi_bxor (N : Nat) (S R a : Nat → Bool) :
    chi N (bxor S R) a = chi N S a * chi N R a := by
  induction N with
  | zero => rfl
  | succ N ih =>
    simp only [chi, ih, bxor, sg_xor]
    generalize sg (S N && a N) = x; generalize sg (R N && a N) = y
    generalize chi N S a = z; generalize chi N R a = w
    rw [Int.mul_assoc, Int.mul_assoc, Int.mul_left_comm y z w]

theorem chi_setb (N i : Nat) (hi : N ≤ i) (S a : Nat → Bool) (b : Bool) :
    chi N S (setb a i b) = chi N S a := by
  induction N with
  | zero => rfl
  | succ N ih =>
    have : setb a i b N = a N := by simp only [setb]; rw [ite_eq_right (by omega)]
    simp only [chi, ih (by omega), this]

theorem chi_single (N e : Nat) (he : e < N) (S : Nat → Bool) (hS : S e = true) :
    chi N S (fun i => i == e) = -1 := by
  induction N with
  | zero => omega
  | succ N ih =>
    simp only [chi]
    by_cases h : e = N
    · subst h
      have : chi e S (fun i => i == e) = 1 := by
        clear ih he
        have : ∀ M, M ≤ e → chi M S (fun i => i == e) = 1 := by
          intro M hM
          induction M with
          | zero => rfl
          | succ M ihM =>
            simp only [chi]; rw [ihM (by omega)]
            have : (M == e) = false := by simp; omega
            simp [this, sg]
        exact this e (Nat.le_refl _)
      simp [hS, this, sg]
    · rw [ih (by omega)]
      have : (N == e) = false := by simp; omega
      simp [this, sg]

/-- `∑_a χ_S(a) = 2^N` if `S ∩ [N] = ∅`, else `0`. -/
theorem csum_chi (N : Nat) (S : Nat → Bool) :
    csum N (chi N S) = if (∀ i, i < N → S i = false) then (2 : Int) ^ N else 0 := by
  induction N with
  | zero => simp [csum, chi]
  | succ N ih =>
    simp only [csum, chi, chi_setb N N (Nat.le_refl _)]
    have e : ∀ a, sg (S N && setb a N false N) * chi N S a +
        sg (S N && setb a N true N) * chi N S a
        = (if S N then 0 else 2) * chi N S a := by
      intro a; cases S N <;> simp [setb, sg] <;> omega
    simp only [e]
    rw [csum_mul, ih]
    by_cases hN : S N = true
    · have : ¬ ∀ i, i < N + 1 → S i = false := fun h => by simp [h N (by omega)] at hN
      rw [ite_eq_right this]; simp [hN]
    · have hN' : S N = false := by simpa using hN
      by_cases hc : ∀ i, i < N → S i = false
      · have : ∀ i, i < N + 1 → S i = false := by
          intro i hi; by_cases h : i = N
          · subst h; exact hN'
          · exact hc i (by omega)
        rw [ite_eq_left hc, ite_eq_left this, hN', Int.pow_succ]; simp [Int.mul_comm]
      · have : ¬ ∀ i, i < N + 1 → S i = false := fun h => hc (fun i hi => h i (by omega))
        rw [ite_eq_right hc, ite_eq_right this]; simp


/-! ## Designs: `E_c(h) = ∑_S c(S) ĥ(S)`, `ĥ(S) = ∑_a h(a) χ_S(a)` -/

def fourier (N : Nat) (h : (Nat → Bool) → Int) (S : Nat → Bool) : Int :=
  csum N (fun a => h a * chi N S a)

def design (N : Nat) (c : (Nat → Bool) → Int) (h : (Nat → Bool) → Int) : Int :=
  csum N (fun S => c S * fourier N h S)

theorem design_congr (N : Nat) (c f g : (Nat → Bool) → Int) (h : ∀ a, Valid N a → f a = g a) :
    design N c f = design N c g := by
  unfold design fourier
  congr 1; funext S; congr 1
  exact csum_congr N _ _ (fun a ha => by rw [h a ha])

theorem design_add (N : Nat) (c f g : (Nat → Bool) → Int) :
    design N c (fun a => f a + g a) = design N c f + design N c g := by
  unfold design fourier
  rw [← csum_add]; congr 1; funext S
  rw [← Int.mul_add, ← csum_add]; congr 2; funext a; rw [Int.add_mul]

theorem design_mul (N : Nat) (c f : (Nat → Bool) → Int) (k : Int) :
    design N c (fun a => k * f a) = k * design N c f := by
  unfold design fourier
  have e : ∀ S, c S * csum N (fun a => k * f a * chi N S a)
      = k * (c S * csum N (fun a => f a * chi N S a)) := by
    intro S
    have : (fun a => k * f a * chi N S a) = (fun a => k * (f a * chi N S a)) := by
      funext a; rw [Int.mul_assoc]
    rw [this, csum_mul, Int.mul_left_comm]
  simp only [e]; exact csum_mul N k _

theorem design_list {α} (N : Nat) (c : (Nat → Bool) → Int) (L : List α)
    (h : α → (Nat → Bool) → Int) :
    design N c (fun a => (L.map fun i => h i a).sum) = (L.map fun i => design N c (h i)).sum := by
  induction L with
  | nil =>
    have := design_mul N c (fun _ => 0) 0
    simp only [Int.zero_mul] at this; simpa using this
  | cons x L ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [design_add, ih]

theorem design_one (N : Nat) (c : (Nat → Bool) → Int) :
    design N c (fun _ => 1) = c (fun _ => false) * 2 ^ N := by
  unfold design fourier
  simp only [Int.one_mul, csum_chi]
  have : (fun S => c S * if (∀ i, i < N → S i = false) then (2 : Int) ^ N else 0)
      = fun S => if (∀ i, i < N → S i = false) then c S * 2 ^ N else 0 := by
    funext S; split <;> simp
  rw [this, csum_delta]

/-- **Involution lemma.** Let `R ⊆ U`, `σ² = 1`, `h` depend only on the coordinates in `U`,
`h · χ_R = -σ h`, and `c(S ⊕ R) = σ c(S)` for every `S ⊆ U`. Then `E_c(h) = 0`. -/
theorem design_zero (N : Nat) (R U : Nat → Bool) (σ : Int) (c h : (Nat → Bool) → Int)
    (hRv : Valid N R) (hRU : ∀ i, R i = true → U i = true) (hσ : σ * σ = 1)
    (h1 : ∀ a, Valid N a → h a * chi N R a = -σ * h a)
    (h2 : ∀ a, Valid N a → ∀ e, e < N → U e = false → h (bxor a (fun i => i == e)) = h a)
    (h3 : ∀ S, Valid N S → (∀ i, i < N → S i = true → U i = true) → c (bxor S R) = σ * c S) :
    design N c h = 0 := by
  -- `ĥ(S ⊕ R) = -σ ĥ(S)`
  have f1 : ∀ S, fourier N h (bxor S R) = -σ * fourier N h S := by
    intro S
    unfold fourier
    rw [← csum_mul]
    apply csum_congr
    intro a ha
    rw [chi_bxor, ← Int.mul_assoc, Int.mul_right_comm, h1 a ha, Int.mul_assoc]
  -- `ĥ(S) = 0` if `S` meets `[N] \ U`
  have f2 : ∀ S e, e < N → S e = true → U e = false → fourier N h S = 0 := by
    intro S e he hSe hUe
    unfold fourier
    apply csum_flip_zero N e he
    intro a ha
    rw [h2 a ha e he hUe, chi_comm N S, chi_bxor, chi_comm N (fun i => i == e),
      chi_single N e he S hSe, chi_comm]
    rw [Int.mul_neg, Int.mul_one, Int.mul_neg]
  have hval : ∀ S, Valid N S → Valid N (bxor S R) := by
    intro S hS i hi; simp [bxor, hS i hi, hRv i hi]
  have key : ∀ S, Valid N S →
      c (bxor S R) * fourier N h (bxor S R) = -(c S * fourier N h S) := by
    intro S hS
    by_cases hsub : ∀ i, i < N → S i = true → U i = true
    · rw [h3 S hS hsub, f1]
      have : σ * c S * (-σ * fourier N h S) = -((σ * σ) * (c S * fourier N h S)) := by
        rw [Int.neg_mul, Int.mul_neg]; congr 1
        rw [Int.mul_assoc, Int.mul_left_comm (c S), ← Int.mul_assoc]
      rw [this, hσ, Int.one_mul]
    · have : ∃ e, e < N ∧ S e = true ∧ U e = false := by
        apply Classical.byContradiction; intro hno; apply hsub
        intro i hi hSi
        cases hU : U i
        · exact absurd ⟨i, hi, hSi, hU⟩ hno
        · rfl
      obtain ⟨e, he, hSe, hUe⟩ := this
      have hRe : R e = false := by
        cases hR : R e
        · rfl
        · rw [hRU e hR] at hUe; exact absurd hUe (by simp)
      rw [f2 S e he hSe hUe, f2 (bxor S R) e he (by simp [bxor, hSe, hRe]) hUe]
      simp
  have hd := csum_bxor N R hRv (fun S => c S * fourier N h S)
  unfold design
  rw [csum_congr N _ (fun S => -(c S * fourier N h S)) key, csum_neg] at hd
  omega

end Programme.«20261024-1633-proof-complexity».NSLower
