import Programme.«20261024-1633-proof-complexity».NSTseitin

/-!
# Polynomial calculus degree lower bound for Tseitin formulas over odd characteristic

`PCDerivable p F D g`: the function `g` on Boolean assignments is a line of a polynomial calculus
derivation from the clause polynomials of `F` over `Z/p` in which every multiplication by a
variable is applied to a line agreeing (mod `p`, on all Boolean points) with a polynomial of
degree `≤ D - 1`, and every axiom `f_C` has `|C| ≤ D`. Lines are taken up to agreement mod `p` on
the cube (rule `congr`), so the Boolean axioms `x² - x` are built in and the degree of a line is
its multilinear degree, which never exceeds the degree of any polynomial representing it. Every
line then has multilinear degree `≤ D`, and a usual (syntactic) degree-`D` PC refutation over `F_p`
(with Boolean axioms) maps line by line to a `PCRefutation p F D` (each line to its cube function).

Theorem `tseitin_pc_lower` (Buss–Grigoriev–Impagliazzo–Pitassi 2001 / Ben-Sasson–Impagliazzo
1999 bound, with K20's expansion hypotheses): for odd `p > 1` and `2D < e`, `Tseitin n E χ` has
no `PCRefutation p` of degree `D`.

Proof (a twisted Grigoriev design). With `c = coef` (the NS design of `Work.NSTseitin`), the
invariant of a line `g` is: `p ∣ E_c(χ_{S₀} g)` for every edge set `|S₀| ≤ D`.
* axioms: `χ_{S₀} f_C` is a polynomial of degree `≤ 2D < e` times `f_C`, killed by `clause_zero`;
* linear combinations and `congr`: `E_c` is linear and depends only on values mod `p`;
* `x_v · g` with `g` of degree `≤ d ≤ D-1`: `2 x_v = 1 - χ_v`, so we need `E_c(χ_{S'} g) ≡ 0`
  for `|S'| ≤ D+1`. Write `E_c(χ_{S'} g) = ∑_S c(S ⊕ S') ĝ(S)`, `ĝ(S) ≡ 0` for `|S| > d`; if some
  `|S₁| ≤ d` has `S₁ ⊕ S'` a small boundary, then `c(S ⊕ S') = c(S ⊕ S₁) c(S₁ ⊕ S')` for `|S| ≤ d`
  (`coef_mul`, all three sets have `< e` edges) and the sum is `± E_c(χ_{S₁} g) ≡ 0`; otherwise
  every term vanishes;
* the line `1` fails at `S₀ = ∅`: `E_c(1) = ±2^N`, not divisible by odd `p > 1`.
-/

namespace Programme.«20261024-1633-proof-complexity».PCTseitin

open Classical Programme.«20261024-1110-proof-complexity».Haken
open Programme.«20261024-1110-proof-complexity».Tseitin
open Programme.«20261024-1633-proof-complexity».NS Programme.«20261024-1633-proof-complexity».NSLower Programme.«20261024-1633-proof-complexity».NSTseitin

/-! ## Polynomial calculus over `Z/p` -/

/-- `g` agrees mod `p` on every Boolean assignment with a polynomial of degree `≤ d`. -/
def CubeDeg (p : Nat) (g : (Nat → Bool) → Int) (d : Nat) : Prop :=
  ∃ Q : Poly Nat, Q.deg ≤ d ∧ ∀ a, (p : Int) ∣ Q.eval a - g a

/-- The variable `x` as a `0/1` function. -/
def xv (x : Nat) (a : Nat → Bool) : Int := if a x then 1 else 0

/-- Lines of a degree-`D` polynomial calculus derivation from `F` over `Z/p`. -/
inductive PCDerivable (p : Nat) (F : CNF Nat) (D : Nat) : ((Nat → Bool) → Int) → Prop
  | ax (C : Clause Nat) : C ∈ F → C.length ≤ D →
      PCDerivable p F D (fun a => (clausePoly C).eval a)
  | lin (f g : (Nat → Bool) → Int) (u v : Int) : PCDerivable p F D f → PCDerivable p F D g →
      PCDerivable p F D (fun a => u * f a + v * g a)
  | mul (x : Nat) (g : (Nat → Bool) → Int) (d : Nat) : PCDerivable p F D g → CubeDeg p g d →
      d + 1 ≤ D → PCDerivable p F D (fun a => xv x a * g a)
  | congr (f g : (Nat → Bool) → Int) : PCDerivable p F D g → (∀ a, (p : Int) ∣ f a - g a) →
      PCDerivable p F D f

/-- A degree-`D` polynomial calculus refutation of `F` over `Z/p`: the line `1` is derivable. -/
def PCRefutation (p : Nat) (F : CNF Nat) (D : Nat) : Prop := PCDerivable p F D (fun _ => 1)

/-! ## Divisibility of cube sums and designs -/

theorem dvd_mul_of {p b : Int} (a : Int) (h : p ∣ b) : p ∣ a * b :=
  Int.dvd_trans h (Int.dvd_mul_left a b)

theorem dvd_csum (N : Nat) (p : Int) (f : (Nat → Bool) → Int) (h : ∀ a, Valid N a → p ∣ f a) :
    p ∣ csum N f := by
  induction N generalizing f with
  | zero => exact h _ (fun _ _ => rfl)
  | succ N ih =>
    simp only [csum]
    apply ih
    intro a ha
    have v : ∀ b, Valid (N + 1) (setb a N b) := by
      intro b i hi; simp only [setb]; rw [ite_eq_right (by omega)]; exact ha i (by omega)
    exact Int.dvd_add (h _ (v false)) (h _ (v true))

theorem csum_sub (N : Nat) (f g : (Nat → Bool) → Int) :
    csum N (fun a => f a - g a) = csum N f - csum N g := by
  have h1 := csum_add N f (fun a => -g a)
  rw [csum_neg] at h1
  rw [show (fun a => f a - g a) = (fun a => f a + -g a) from by funext a; omega, h1]; omega

theorem design_zero_fun (N : Nat) (c : (Nat → Bool) → Int) : design N c (fun _ => 0) = 0 := by
  have := design_mul N c (fun _ => 0) 0
  simp only [Int.zero_mul] at this; exact this

theorem design_sub (N : Nat) (c f g : (Nat → Bool) → Int) :
    design N c (fun a => f a - g a) = design N c f - design N c g := by
  have h1 := design_add N c f (fun a => -1 * g a)
  have h2 := design_mul N c g (-1)
  rw [h2] at h1
  rw [show (fun a => f a - g a) = (fun a => f a + -1 * g a) from by funext a; omega, h1]; omega

theorem dvd_design (N : Nat) (p : Int) (c h : (Nat → Bool) → Int)
    (hh : ∀ a, Valid N a → p ∣ h a) : p ∣ design N c h := by
  unfold design fourier
  apply dvd_csum; intro S _
  apply dvd_mul_of
  apply dvd_csum; intro a ha
  exact Int.dvd_trans (hh a ha) (Int.dvd_mul_right _ _)

theorem design_dvd_congr (N : Nat) (p : Int) (c f g : (Nat → Bool) → Int)
    (h : ∀ a, Valid N a → p ∣ f a - g a) : p ∣ design N c f - design N c g := by
  rw [← design_sub]; exact dvd_design N p c _ h

/-! ## Characters as polynomials, character shifts, Fourier support -/

/-- `χ_S = ∏_{i < N, i ∈ S} (1 - 2 x_i)` as a polynomial. -/
def chiPoly : Nat → (Nat → Bool) → Poly Nat
  | 0, _ => Poly.one
  | N + 1, S => if S N then ((chiPoly N S).sub ((chiPoly N S).mulVar N)).sub
      ((chiPoly N S).mulVar N) else chiPoly N S

theorem chiPoly_eval (N : Nat) (S a : Nat → Bool) : (chiPoly N S).eval a = chi N S a := by
  induction N with
  | zero => simp [chiPoly, chi, eval_one]
  | succ N ih =>
    simp only [chiPoly, chi]
    cases hS : S N
    · simp [ih, sg]
    · simp only [ite_true, eval_sub, eval_mulVar, ih, Bool.true_and]
      cases a N <;> simp [sg] <;> omega

theorem size_succ (N : Nat) (S : Nat → Bool) :
    size (N + 1) S = size N S + (if S N then 1 else 0) := by
  unfold size; rw [List.range_succ, List.countP_append]
  cases h : S N <;> simp [h]

theorem chiPoly_deg (N : Nat) (S : Nat → Bool) : (chiPoly N S).deg ≤ size N S := by
  induction N with
  | zero => simp [chiPoly, deg_one]
  | succ N ih =>
    rw [size_succ]
    simp only [chiPoly]
    cases S N
    · simp; exact ih
    · simp only [ite_true]
      have h1 := deg_mulVar N (chiPoly N S)
      exact deg_sub _ _ _ (deg_sub _ _ _ (by omega) (by omega)) (by omega)

theorem chi_empty (N : Nat) (a : Nat → Bool) : chi N (fun _ => false) a = 1 := by
  induction N with
  | zero => rfl
  | succ N ih => simp [chi, ih, sg]

theorem chi_delta (N x : Nat) (hx : x < N) (a : Nat → Bool) :
    chi N (fun i => i == x) a = sg (a x) := by
  induction N with
  | zero => omega
  | succ N ih =>
    simp only [chi]
    by_cases h : x = N
    · subst h
      have : chi x (fun i => i == x) a = 1 := by
        have : ∀ M, M ≤ x → chi M (fun i => i == x) a = 1 := by
          intro M hM
          induction M with
          | zero => rfl
          | succ M ihM =>
            simp only [chi]; rw [ihM (by omega)]
            have : (M == x) = false := by simp; omega
            simp [this, sg]
        exact this x (Nat.le_refl _)
      simp [this]
    · rw [ih (by omega)]
      have : (N == x) = false := by simp; omega
      simp [this, sg]

theorem fourier_shift (N : Nat) (S' S : Nat → Bool) (g : (Nat → Bool) → Int) :
    fourier N (fun a => chi N S' a * g a) S = fourier N g (bxor S S') := by
  unfold fourier
  congr 1; funext a
  rw [chi_bxor]
  rw [Int.mul_comm (chi N S a), ← Int.mul_assoc, Int.mul_comm (g a)]

/-- `E_c(χ_{S'} g) = ∑_S c(S ⊕ S') ĝ(S)`. -/
theorem design_shift (N : Nat) (c : (Nat → Bool) → Int) (S' : Nat → Bool) (hS' : Valid N S')
    (g : (Nat → Bool) → Int) :
    design N c (fun a => chi N S' a * g a) = csum N (fun S => c (bxor S S') * fourier N g S) := by
  unfold design
  simp only [fourier_shift]
  have := csum_bxor N S' hS' (fun S => c (bxor S S') * fourier N g S)
  simp only [bxor_bxor] at this
  exact this

/-- A function of cube degree `≤ d` has `ĝ(S) ≡ 0` for `|S| > d`. -/
theorem fourier_support (N p d : Nat) (g : (Nat → Bool) → Int) (hg : CubeDeg p g d)
    (S : Nat → Bool) (hS : d < size N S) : (p : Int) ∣ fourier N g S := by
  obtain ⟨Q, hQd, hQ⟩ := hg
  have e1 : fourier N g S = fourier N Q.eval S + csum N (fun a => (g a - Q.eval a) * chi N S a) := by
    unfold fourier; rw [← csum_add]; congr 1; funext a; dsimp only; rw [← Int.add_mul]
    congr 1; omega
  have e2 : fourier N Q.eval S = 0 := by
    unfold fourier
    have : (fun a => Q.eval a * chi N S a)
        = fun a => (Q.terms.map fun t => t.1 * monoEval a t.2 * chi N S a).sum := by
      funext a; unfold Poly.eval; rw [sum_mul_right]
    rw [this, csum_list]
    apply sum_zero
    intro t ht
    have htd := (deg_le_iff Q Q.deg).mp (Nat.le_refl _) t ht
    have hm := countP_mem_le N t.2
    have : ∃ x, x < N ∧ S x = true ∧ x ∉ t.2 := by
      apply Classical.byContradiction; intro hno
      have : size N S ≤ (List.range N).countP (fun i => decide (i ∈ t.2)) := by
        unfold size; apply List.countP_mono_left; intro i hi hSi
        have hi' := List.mem_range.mp hi
        apply Classical.byContradiction; intro hni
        exact hno ⟨i, hi', hSi, by simpa using hni⟩
      omega
    obtain ⟨x, hx, hSx, hxm⟩ := this
    apply csum_flip_zero N x hx
    intro a _
    have hmo : monoEval (bxor a (fun i => i == x)) t.2 = monoEval a t.2 := by
      apply monoEval_congr; intro y hy
      have : (y == x) = false := by simp; intro h; exact hxm (h ▸ hy)
      simp [bxor, this]
    rw [hmo, chi_comm N S, chi_bxor, chi_comm N (fun i => i == x), chi_single N x hx S hSx,
      chi_comm]
    rw [Int.mul_neg, Int.mul_one, Int.mul_neg]
  rw [e1, e2, Int.zero_add]
  apply dvd_csum; intro a _
  exact Int.dvd_trans (Int.dvd_neg.mp (by rw [Int.neg_sub]; exact hQ a)) (Int.dvd_mul_right _ _)

theorem size_bxor (N : Nat) (X Y : Nat → Bool) : size N (bxor X Y) ≤ size N X + size N Y := by
  have h1 := size_union (n := N) X Y
  have h2 : size N (bxor X Y) ≤ size N (fun w => X w || Y w) := by
    unfold size; apply List.countP_mono_left; intro w _ h
    simp only [bxor] at h; cases hX : X w <;> cases hY : Y w <;> simp_all
  omega

theorem bxor_assoc3 (S S1 S' : Nat → Bool) : bxor (bxor S S1) (bxor S1 S') = bxor S S' := by
  funext i; simp only [bxor]; cases S i <;> cases S1 i <;> cases S' i <;> rfl

theorem valid_bxor {N : Nat} {X Y : Nat → Bool} (hX : Valid N X) (hY : Valid N Y) :
    Valid N (bxor X Y) := by
  intro i hi; simp [bxor, hX i hi, hY i hi]

/-! ## Multiplicativity of the design coefficient -/

section mul
variable {n : Nat} {E : List (Nat × Nat)} {χ : Nat → Nat}

theorem xor_set {T1 T2 X Y : Nat → Bool} (b1 : BdOf E T1 X) (b2 : BdOf E T2 Y) :
    BdOf E (fun w => T1 w != T2 w) (bxor X Y) ∧
    size n (fun w => T1 w != T2 w) ≤ size n T1 + size n T2 ∧
    psg (chT n χ (fun w => T1 w != T2 w)) = psg (chT n χ T1) * psg (chT n χ T2) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    simp only [bxor, b1 i hi, b2 i hi]
    generalize T1 (edge E i).1 = a1; generalize T1 (edge E i).2 = a2
    generalize T2 (edge E i).1 = c1; generalize T2 (edge E i).2 = c2
    cases a1 <;> cases a2 <;> cases c1 <;> cases c2 <;> rfl
  · have := size_union (n := n) T1 T2
    have : size n (fun w => T1 w != T2 w) ≤ size n (fun w => T1 w || T2 w) := by
      unfold size; apply List.countP_mono_left; intro w _ h
      cases hT1 : T1 w <;> cases hT2 : T2 w <;> simp_all
    omega
  · have hp := sum_parity3 (List.range n)
      (fun w => if (T1 w != T2 w) then χ w else 0) (fun w => if T1 w then χ w else 0)
      (fun w => if T2 w then χ w else 0) (by
        intro w _
        cases T1 w <;> cases T2 w <;> simp <;> omega)
    unfold chT
    rw [← psg_add]
    apply psg_mod; dsimp only; omega

variable (hn : 3 ≤ n) (hconn : ∀ S : Nat → Bool, 0 < size n S → size n S < n → bd E S ≠ [])
  {e : Nat}
  (hexp : ∀ S : Nat → Bool, n / 3 < size n S → size n S ≤ 2 * (n / 3) → e ≤ (bd E S).length)
include hn hconn hexp

theorem coef_mul_small {X Y : Nat → Bool} (hX : SmallBd n E X) (hY : SmallBd n E Y)
    (hc : size E.length (bxor X Y) < e) :
    SmallBd n E (bxor X Y) ∧ coef n E χ (bxor X Y) = coef n E χ X * coef n E χ Y := by
  obtain ⟨hT1, hb1⟩ := Classical.choose_spec hX
  obtain ⟨hT2, hb2⟩ := Classical.choose_spec hY
  obtain ⟨b', s', c'⟩ := xor_set (n := n) (χ := χ) hb1 hb2
  have hs : size n (fun w => Classical.choose hX w != Classical.choose hY w) ≤ n / 3 := by
    apply Classical.byContradiction; intro h
    have := hexp (fun w => Classical.choose hX w != Classical.choose hY w) (by omega) (by omega)
    rw [bd_len_eq b'] at this; unfold size at hc; omega
  have hXY : SmallBd n E (bxor X Y) := ⟨_, hs, b'⟩
  refine ⟨hXY, ?_⟩
  unfold coef
  rw [dite_eq_left hXY, dite_eq_left hX, dite_eq_left hY]
  obtain ⟨hT3, hb3⟩ := Classical.choose_spec hXY
  rw [bd_unique (by omega) hconn hT3 hs hb3 b', c']

theorem coef_mul {X Y : Nat → Bool} (hY : SmallBd n E Y) (hX : size E.length X < e)
    (hc : size E.length (bxor X Y) < e) :
    coef n E χ (bxor X Y) = coef n E χ X * coef n E χ Y := by
  by_cases hXs : SmallBd n E X
  · exact (coef_mul_small hn hconn hexp hXs hY hc).2
  · have hXY : ¬ SmallBd n E (bxor X Y) := by
      intro h
      have := (coef_mul_small (χ := χ) hn hconn hexp h hY (by rw [bxor_bxor]; exact hX)).1
      rw [bxor_bxor] at this; exact hXs this
    unfold coef; rw [dite_eq_right hXs, dite_eq_right hXY]; simp

end mul

/-! ## The invariant -/

/-- The invariant of a line `g`: `p ∣ E_c(χ_{S₀} g)` for every edge set `S₀` with `|S₀| ≤ D`. -/
def Inv (p N : Nat) (c : (Nat → Bool) → Int) (D : Nat) (g : (Nat → Bool) → Int) : Prop :=
  ∀ S0, Valid N S0 → size N S0 ≤ D → (p : Int) ∣ design N c (fun a => chi N S0 a * g a)

theorem inv_lin (p N : Nat) (c : (Nat → Bool) → Int) (D : Nat) (f g : (Nat → Bool) → Int)
    (u v : Int) (hf : Inv p N c D f) (hg : Inv p N c D g) :
    Inv p N c D (fun a => u * f a + v * g a) := by
  intro S0 hS0 hs
  have h1 := design_add N c (fun a => u * (chi N S0 a * f a)) (fun a => v * (chi N S0 a * g a))
  have h2 := design_mul N c (fun a => chi N S0 a * f a) u
  have h3 := design_mul N c (fun a => chi N S0 a * g a) v
  have e : (fun a => chi N S0 a * (u * f a + v * g a))
      = fun a => u * (chi N S0 a * f a) + v * (chi N S0 a * g a) := by
    funext a; rw [Int.mul_add, Int.mul_left_comm, Int.mul_left_comm (chi N S0 a) v]
  rw [e, h1, h2, h3]
  exact Int.dvd_add (dvd_mul_of u (hf S0 hS0 hs)) (dvd_mul_of v (hg S0 hS0 hs))

theorem inv_congr (p N : Nat) (c : (Nat → Bool) → Int) (D : Nat) (f g : (Nat → Bool) → Int)
    (hg : Inv p N c D g) (hfg : ∀ a, (p : Int) ∣ f a - g a) : Inv p N c D f := by
  intro S0 hS0 hs
  have := design_dvd_congr N p c (fun a => chi N S0 a * f a) (fun a => chi N S0 a * g a)
    (fun a _ => by rw [← Int.mul_sub]; exact dvd_mul_of _ (hfg a))
  have h := Int.dvd_add this (hg S0 hS0 hs)
  rwa [Int.sub_add_cancel] at h

theorem odd_dvd_two_mul (p : Nat) (hp : p % 2 = 1) (x : Int) (h : (p : Int) ∣ 2 * x) :
    (p : Int) ∣ x := by
  have hc : Nat.Coprime p 2 := by
    unfold Nat.Coprime; rw [Nat.gcd_comm, Nat.gcd_rec, hp]; rfl
  rw [Int.ofNat_dvd_left, Int.natAbs_mul] at h
  exact Int.ofNat_dvd_left.mpr (Nat.Coprime.dvd_of_dvd_mul_left hc h)

section main
variable {n : Nat} {E : List (Nat × Nat)} {χ : Nat → Nat}
  (hn : 3 ≤ n) (hE : ∀ p ∈ E, p.1 < n ∧ p.2 < n ∧ p.1 ≠ p.2)
  (hconn : ∀ S : Nat → Bool, 0 < size n S → size n S < n → bd E S ≠ [])
  {e : Nat}
  (hexp : ∀ S : Nat → Bool, n / 3 < size n S → size n S ≤ 2 * (n / 3) → e ≤ (bd E S).length)
include hn hE hconn hexp

theorem inv_ax (p D : Nat) (h2D : 2 * D < e) {C : Clause Nat} (hC : C ∈ Tseitin n E χ)
    (hCD : C.length ≤ D) : Inv p E.length (coef n E χ) D (fun a => (clausePoly C).eval a) := by
  intro S0 _ hs
  obtain ⟨v, hv, hCv⟩ := tseitin_mem hC
  have hdeg := chiPoly_deg E.length S0
  have h := clause_zero hn hE hconn hexp hv hCv (chiPoly E.length S0) (D := 2 * D)
    (by omega) h2D
  have e : (fun a => chi E.length S0 a * (clausePoly C).eval a)
      = fun a => (chiPoly E.length S0).eval a * (clausePoly C).eval a := by
    funext a; rw [chiPoly_eval]
  rw [e, h]; exact ⟨0, by simp⟩

omit hE in
/-- The key step: the invariant extends to `|S'| = D + 1` for lines of degree `≤ D - 1`. -/
theorem inv_high (p D d : Nat) (h2D : 2 * D < e) (hd : d + 1 ≤ D) (g : (Nat → Bool) → Int)
    (hg : CubeDeg p g d) (hinv : Inv p E.length (coef n E χ) D g) (S' : Nat → Bool)
    (hS' : Valid E.length S') (hs : size E.length S' ≤ D + 1) :
    (p : Int) ∣ design E.length (coef n E χ) (fun a => chi E.length S' a * g a) := by
  rw [design_shift E.length (coef n E χ) S' hS']
  by_cases hA : ∃ S1, Valid E.length S1 ∧ size E.length S1 ≤ d ∧ SmallBd n E (bxor S1 S')
  · obtain ⟨S1, hv1, hs1, hsm⟩ := hA
    have key : (p : Int) ∣ csum E.length (fun S => coef n E χ (bxor S S') * fourier E.length g S)
        - coef n E χ (bxor S1 S')
          * csum E.length (fun S => coef n E χ (bxor S S1) * fourier E.length g S) := by
      rw [← csum_mul, ← csum_sub]
      apply dvd_csum; intro S _
      by_cases hsS : size E.length S ≤ d
      · have := coef_mul (χ := χ) hn hconn hexp (X := bxor S S1) hsm
          (by have := size_bxor E.length S S1; omega)
          (by rw [bxor_assoc3]; have := size_bxor E.length S S'; omega)
        rw [bxor_assoc3] at this
        rw [this]
        rw [Int.mul_comm (coef n E χ (bxor S S1)) (coef n E χ (bxor S1 S')), Int.mul_assoc,
          Int.sub_self]
        exact ⟨0, by simp⟩
      · have hf := fourier_support E.length p d g hg S (by omega)
        rw [← Int.mul_assoc, ← Int.sub_mul]
        exact dvd_mul_of _ hf
    have h1 := hinv S1 hv1 (by omega)
    rw [design_shift E.length (coef n E χ) S1 hv1] at h1
    have h2 := Int.dvd_add key (dvd_mul_of (coef n E χ (bxor S1 S')) h1)
    rwa [Int.sub_add_cancel] at h2
  · apply dvd_csum; intro S hS
    by_cases hsS : size E.length S ≤ d
    · have hns : ¬ SmallBd n E (bxor S S') := fun h => hA ⟨S, hS, hsS, h⟩
      have : coef n E χ (bxor S S') = 0 := by unfold coef; rw [dite_eq_right hns]
      rw [this, Int.zero_mul]; exact ⟨0, by simp⟩
    · exact dvd_mul_of _ (fourier_support E.length p d g hg S (by omega))

omit hE in
theorem inv_mul (p D d : Nat) (hp : p % 2 = 1) (h2D : 2 * D < e) (hd : d + 1 ≤ D) (x : Nat)
    (g : (Nat → Bool) → Int) (hg : CubeDeg p g d) (hinv : Inv p E.length (coef n E χ) D g) :
    Inv p E.length (coef n E χ) D (fun a => xv x a * g a) := by
  intro S0 hS0 hs
  dsimp only
  by_cases hx : x < E.length
  · have hR : Valid E.length (fun i => i == x) := by intro i hi; simp; omega
    have hsR : size E.length (fun i => i == x) ≤ 1 := by
      have := countP_eq E.length x; unfold size; split at this <;> omega
    have hS' := valid_bxor hS0 hR
    have hsS' : size E.length (bxor S0 (fun i => i == x)) ≤ D + 1 := by
      have := size_bxor E.length S0 (fun i => i == x); omega
    have e2 : ∀ a, Valid E.length a → 2 * (chi E.length S0 a * (xv x a * g a))
        = chi E.length S0 a * g a - chi E.length (bxor S0 (fun i => i == x)) a * g a := by
      intro a _
      rw [chi_bxor, chi_delta E.length x hx]
      unfold xv sg
      cases a x
      · simp
      · simp only [ite_true]
        rw [Int.mul_neg, Int.mul_one, Int.neg_mul, Int.sub_neg, Int.one_mul, ← Int.two_mul]
    have h := design_congr E.length (coef n E χ) (fun a => 2 * (chi E.length S0 a * (xv x a * g a)))
      (fun a => chi E.length S0 a * g a - chi E.length (bxor S0 (fun i => i == x)) a * g a) e2
    rw [design_mul, design_sub] at h
    apply odd_dvd_two_mul p hp
    rw [h]
    exact Int.dvd_sub (hinv S0 hS0 hs) (inv_high hn hconn hexp p D d h2D hd g hg hinv _ hS' hsS')
  · have : design E.length (coef n E χ) (fun a => chi E.length S0 a * (xv x a * g a))
        = design E.length (coef n E χ) (fun _ => 0) := by
      apply design_congr; intro a ha
      have : a x = false := ha x (by omega)
      simp [xv, this]
    rw [this, design_zero_fun]; exact ⟨0, by simp⟩

/-- **PC degree lower bound for Tseitin over odd characteristic.** For a connected loopless graph
on `n ≥ 3` vertices whose middle-third vertex sets have `≥ e` boundary edges, any charge, and any
odd `p > 1`: no degree-`D` polynomial calculus refutation over `Z/p` exists when `2D < e`. -/
theorem tseitin_pc_lower (p : Nat) (hp : p % 2 = 1) (hp1 : 1 < p) {D : Nat} (h2D : 2 * D < e)
    (π : PCRefutation p (Tseitin n E χ) D) : False := by
  let N := E.length
  let c := coef n E χ
  have hall : ∀ g, PCDerivable p (Tseitin n E χ) D g → Inv p N c D g := by
    intro g hder
    induction hder with
    | ax C hC hCD => exact inv_ax hn hE hconn hexp p D h2D hC hCD
    | lin f g u v _ _ ihf ihg => exact inv_lin p N c D f g u v ihf ihg
    | mul x g d _ hg hd ih => exact inv_mul hn hconn hexp p D d hp h2D hd x g hg ih
    | congr f g _ hfg ih => exact inv_congr p N c D f g ih hfg
  have h1 := hall _ π (fun _ => false) (fun _ _ => rfl) (by simp [size])
  simp only [chi_empty, Int.mul_one] at h1
  rw [design_one] at h1
  have h0 : SmallBd n E (fun _ => false) :=
    ⟨fun _ => false, by simp [size], fun i _ => rfl⟩
  have hc0 : c (fun _ => false) * c (fun _ => false) = 1 := by
    simp only [c]; unfold coef; rw [dite_eq_left h0]; exact psg_sq _
  have h2 := dvd_mul_of (c (fun _ => false)) h1
  rw [← Int.mul_assoc, hc0, Int.one_mul] at h2
  have hdvd : (p : Int) ∣ ((2 ^ N : Nat) : Int) := by
    rw [Int.natCast_pow]; exact h2
  have := odd_dvd_pow p hp N (Int.ofNat_dvd.mp hdvd)
  omega

end main

end Programme.«20261024-1633-proof-complexity».PCTseitin

#print axioms Programme.«20261024-1633-proof-complexity».PCTseitin.tseitin_pc_lower
