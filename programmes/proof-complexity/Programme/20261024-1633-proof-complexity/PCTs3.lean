import Programme.«20261024-1633-proof-complexity».Ts3
import Programme.«20261024-1633-proof-complexity».PCTseitin

/-!
# Polynomial calculus degree lower bound for mod-3 Tseitin over `Z/p`, `3 ∤ p`

Theorem `ts3_pc_lower` (Buss–Grigoriev–Impagliazzo–Pitassi 2001, the `q = 3` case, PC version):
under K3's hypotheses (connected, loopless, middle-third expansion `e`), for every `p > 1` with
`3 ∤ p` (e.g. `p = 2`) and any charge, `Ts3 n E c` has no `PCRefutation p` of degree `D` with
`2D < e` (the semantic polynomial calculus of `Work.PCTseitin`).

Proof: the twisted design `Φ_{S₀}(g) = ∑_S co(S + S₀) ĝ(S)` (`ĝ` the `ℤ₃`-Fourier transform of
`g ∘ emb` in `ℤ[ω]`, `co = co3` of `Work.Ts3`). Invariant of a line `g`: `p ∣ Φ_{S₀}(g)` for all
`S₀` with `≤ D` nonzero entries.
* axioms: edge clauses vanish on `emb` points; vertex clauses by the rotation lemma with
  `U = inc v ∪ supp S₀` (`|U| ≤ 2D < e`);
* linear combinations and congruence mod `p`: `Φ` is linear;
* `x_{3i+j} · g`: `3 [a_i = j] = ∑_k ω^{k(a_i - j)}` gives
  `3 Φ_{S₀}(x g) = Φ_{S₀}(g) + ω^{2j} Φ_{S₀+2e_i}(g) + ω^j Φ_{S₀+e_i}(g)`; the shifted values are
  `≡ 0` (`inv_high3`: `ĝ(S) ≡ 0` for `|S| > d`, and `co(S + S') = co(S - S₁) co(S₁ + S')` for a
  small boundary `S₁ + S'`), and `3` is invertible mod `p`;
* the line `1` fails at `S₀ = 0`: `Φ_0(1) = 3^{|E|}`.
-/

namespace Programme.«20261024-1633-proof-complexity».PCTs3

open Classical Programme.«20261024-1110-proof-complexity».Haken
open Programme.«20261024-1110-proof-complexity».Tseitin
open Programme.«20261024-1633-proof-complexity».NS Programme.«20261024-1633-proof-complexity».Z3Design Programme.«20261024-1633-proof-complexity».Z3Design.ZW Programme.«20261024-1633-proof-complexity».Ts3
open Programme.«20261024-1633-proof-complexity».PCTseitin (CubeDeg xv PCDerivable PCRefutation dvd_mul_of)
open Programme.«20261024-1633-proof-complexity».NSTseitin (monoEval_congr clause_eval_congr countP_mem_le)

/-! ## Congruence mod `p` in `ℤ[ω]` -/

def ZC (p : Nat) (z w : ZW) : Prop := (p : Int) ∣ z.x - w.x ∧ (p : Int) ∣ z.y - w.y

theorem dvd_of_eq' {p a b : Int} (h : a = b) (hb : p ∣ b) : p ∣ a := h ▸ hb

theorem zc_refl (p : Nat) (z : ZW) : ZC p z z :=
  ⟨⟨0, by omega⟩, ⟨0, by omega⟩⟩

theorem zc_of_eq {p : Nat} {z w : ZW} (h : z = w) : ZC p z w := h ▸ zc_refl p z

theorem zc_symm {p : Nat} {z w : ZW} (h : ZC p z w) : ZC p w z :=
  ⟨dvd_of_eq' (by omega) (Int.dvd_neg.mpr h.1), dvd_of_eq' (by omega) (Int.dvd_neg.mpr h.2)⟩

theorem zc_trans {p : Nat} {z w u : ZW} (h1 : ZC p z w) (h2 : ZC p w u) : ZC p z u :=
  ⟨dvd_of_eq' (by omega) (Int.dvd_add h1.1 h2.1), dvd_of_eq' (by omega) (Int.dvd_add h1.2 h2.2)⟩

theorem zc_add {p : Nat} {z1 w1 z2 w2 : ZW} (h1 : ZC p z1 w1) (h2 : ZC p z2 w2) :
    ZC p (z1.add z2) (w1.add w2) :=
  ⟨dvd_of_eq' (by simp only [ZW.add]; omega) (Int.dvd_add h1.1 h2.1),
    dvd_of_eq' (by simp only [ZW.add]; omega) (Int.dvd_add h1.2 h2.2)⟩

theorem zc_rot {p : Nat} {z w : ZW} (h : ZC p z w) : ZC p (rot z) (rot w) :=
  ⟨dvd_of_eq' (by simp only [rot]; omega) (Int.dvd_neg.mpr h.2),
    dvd_of_eq' (by simp only [rot]; omega) (Int.dvd_sub h.1 h.2)⟩

theorem zc_rotN {p : Nat} (k : Nat) {z w : ZW} (h : ZC p z w) : ZC p (rotN k z) (rotN k w) := by
  induction k with
  | zero => exact h
  | succ k ih => exact zc_rot ih

theorem zc_smul {p : Nat} (k : Int) {z w : ZW} (h : ZC p z w) : ZC p (smul k z) (smul k w) :=
  ⟨dvd_of_eq' (by simp only [smul]; rw [Int.mul_sub]) (dvd_mul_of k h.1),
    dvd_of_eq' (by simp only [smul]; rw [Int.mul_sub]) (dvd_mul_of k h.2)⟩

theorem zc_cm {p : Nat} (o : Option Nat) {z w : ZW} (h : ZC p z w) : ZC p (cm o z) (cm o w) := by
  cases o
  · exact zc_refl p _
  · exact zc_rotN _ h

theorem zc_cm_zero {p : Nat} (o : Option Nat) {z : ZW} (h : ZC p z zero) : ZC p (cm o z) zero := by
  have := zc_cm o h; rwa [cm_zero] at this

theorem zc_csum3 (p N : Nat) (f g : (Nat → Nat) → ZW) (h : ∀ a, Valid3 N a → ZC p (f a) (g a)) :
    ZC p (csum3 N f) (csum3 N g) := by
  induction N generalizing f g with
  | zero => exact h _ ⟨fun i hi => by omega, fun _ _ => rfl⟩
  | succ N ih =>
    simp only [csum3]
    apply ih
    intro a ha
    exact zc_add (h _ (valid_seta ha (by omega)))
      (zc_add (h _ (valid_seta ha (by omega))) (h _ (valid_seta ha (by omega))))

theorem dvd_three_mul (p : Nat) (hp : p % 3 ≠ 0) (x : Int) (h : (p : Int) ∣ 3 * x) :
    (p : Int) ∣ x := by
  have hc : Nat.Coprime p 3 := by
    unfold Nat.Coprime; rw [Nat.gcd_comm, Nat.gcd_rec]
    have : p % 3 = 1 ∨ p % 3 = 2 := by omega
    rcases this with h1 | h1 <;> rw [h1] <;> rfl
  rw [Int.ofNat_dvd_left, Int.natAbs_mul] at h
  exact Int.ofNat_dvd_left.mpr (Nat.Coprime.dvd_of_dvd_mul_left hc h)

theorem zc_three (p : Nat) (hp : p % 3 ≠ 0) {z : ZW} (h : ZC p (smul 3 z) zero) : ZC p z zero :=
  ⟨dvd_of_eq' (by simp only [zero]; omega)
      (dvd_three_mul p hp z.x (dvd_of_eq' (by simp only [smul, zero]; omega) h.1)),
    dvd_of_eq' (by simp only [zero]; omega)
      (dvd_three_mul p hp z.y (dvd_of_eq' (by simp only [smul, zero]; omega) h.2))⟩

theorem smul_zero' (k : Int) : smul k zero = zero := eq_of (by simp [smul, zero]) (by simp [smul, zero])

theorem cm_csum3 (N : Nat) (o : Option Nat) (f : (Nat → Nat) → ZW) :
    cm o (csum3 N f) = csum3 N (fun a => cm o (f a)) := by
  cases o
  · simp only [cm]; exact (csum3_zero N).symm
  · simp only [cm]; exact (csum3_rotN N _ f).symm

theorem cm_comm (o1 o2 : Option Nat) (z : ZW) : cm o1 (cm o2 z) = cm o2 (cm o1 z) := by
  cases o1 <;> cases o2 <;> simp only [cm, rotN_zero, rotN_rotN, Nat.add_comm]

/-! ## Supports, shifts -/

def sz (N : Nat) (S : Nat → Nat) : Nat := (List.range N).countP (fun i => S i != 0)

def single (i k : Nat) : Nat → Nat := fun l => if l = i then k else 0

theorem valid_single {N i : Nat} (hi : i < N) {k : Nat} (hk : k < 3) : Valid3 N (single i k) := by
  constructor
  · intro l _; unfold single; split <;> omega
  · intro l hl; unfold single; rw [ite_eq_right (by omega)]

theorem sz_ashift (N : Nat) (X Y : Nat → Nat) : sz N (ashift X Y) ≤ sz N X + sz N Y := by
  have h1 := size_union (n := N) (fun i => X i != 0) (fun i => Y i != 0)
  have h2 : sz N (ashift X Y) ≤ size N (fun i => (X i != 0) || (Y i != 0)) := by
    unfold sz size; apply List.countP_mono_left; intro i _ h
    simp [ashift] at h ⊢; omega
  unfold sz at h2 ⊢; unfold size at h1 h2; omega

theorem sz_double (N : Nat) (S : Nat → Nat) : sz N (ashift S S) ≤ sz N S := by
  unfold sz; apply List.countP_mono_left; intro i _ h
  simp [ashift] at h ⊢; omega

theorem sz_single (N i k : Nat) : sz N (single i k) ≤ 1 := by
  have h : (List.range N).countP (fun l => decide (l ∈ [i])) ≤ [i].length := countP_mem_le N [i]
  have : sz N (single i k) ≤ (List.range N).countP (fun l => decide (l ∈ [i])) := by
    unfold sz; apply List.countP_mono_left; intro l _ h
    by_cases hl : l = i
    · simp [hl]
    · simp [single, hl] at h
  exact Nat.le_trans this h

theorem ashift_assoc (S R S0 : Nat → Nat) : ashift (ashift S R) S0 = ashift S (ashift S0 R) := by
  funext l; simp only [ashift]; omega

theorem ashift_swap (S R S0 : Nat → Nat) : ashift (ashift S R) S0 = ashift (ashift S S0) R := by
  funext l; simp only [ashift]; omega

theorem ashift_cancel {N : Nat} {S : Nat → Nat} (hS : Valid3 N S) (R1 R2 : Nat → Nat)
    (h : ∀ l, (R1 l + R2 l) % 3 = 0) : ashift (ashift S R2) R1 = S := by
  funext l; simp only [ashift]; have := h l
  by_cases hN : l < N
  · have := hS.1 l hN; omega
  · rw [hS.2 l (by omega)]; omega

theorem ashift_zero {N : Nat} {S : Nat → Nat} (hS : Valid3 N S) : ashift S (fun _ => 0) = S := by
  funext l; simp only [ashift]
  by_cases hN : l < N
  · have := hS.1 l hN; omega
  · rw [hS.2 l (by omega)]

theorem ex_single (N i k : Nat) (hi : i < N) (a : Nat → Nat) : ex N a (single i k) = a i * k := by
  rw [ex_eq_sum]; exact sum_single3 N i k a hi

/-! ## Fourier transforms -/

theorem four_cong (p N : Nat) (f g : (Nat → Nat) → Int)
    (h : ∀ a, Valid3 N a → (p : Int) ∣ f a - g a) (S : Nat → Nat) :
    ZC p (four N f S) (four N g S) := by
  unfold four
  apply zc_csum3; intro a ha
  apply zc_rotN
  exact ⟨h a ha, by simp⟩

theorem four_zero_fun (N : Nat) (S : Nat → Nat) : four N (fun _ => 0) S = zero := by
  unfold four; rw [← csum3_zero N]; apply csum3_congr; intro a _; exact rotN_zero _

theorem four_sum_zero {α} (N : Nat) (L : List α) (h : α → (Nat → Nat) → Int) (S : Nat → Nat)
    (hz : ∀ t ∈ L, four N (h t) S = zero) :
    four N (fun a => (L.map fun t => h t a).sum) S = zero := by
  induction L with
  | nil => exact four_zero_fun N S
  | cons x L ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [four_add, hz x List.mem_cons_self, ih (fun t ht => hz t (List.mem_cons_of_mem _ ht)),
      ZW.add_zero]

theorem emb_shift (N : Nat) (a : Nat → Nat) (ha : Valid3 N a) (e' x : Nat) (hx : x / 3 ≠ e') :
    emb (ashift a (fun i => if i = e' then 1 else 0)) x = emb a x := by
  simp only [emb, ashift, ite_eq_right hx, Nat.add_zero]
  have := ha.1 (x / 3)
  by_cases hN : x / 3 < N
  · rw [Nat.mod_eq_of_lt (this hN)]
  · rw [ha.2 _ (by omega)]

/-- A line of cube degree `≤ d` has `ĝ(S) ≡ 0` when `S` has more than `d` nonzero entries. -/
theorem four_support3 (p N d : Nat) (g : (Nat → Bool) → Int) (hg : CubeDeg p g d)
    (S : Nat → Nat) (hS : Valid3 N S) (hd : d < sz N S) :
    ZC p (four N (fun a => g (emb a)) S) zero := by
  obtain ⟨Q, _, hQ⟩ := hg
  have h0 : four N (fun a => Q.eval (emb a)) S = zero := by
    have e : (fun a => Q.eval (emb a))
        = fun a => (Q.terms.map fun t => t.1 * monoEval (emb a) t.2).sum := by
      funext a; rfl
    rw [e]
    apply four_sum_zero
    intro t ht
    have htd := (deg_le_iff Q Q.deg).mp (Nat.le_refl _) t ht
    have : ∃ e', e' < N ∧ S e' ≠ 0 ∧ e' ∉ t.2.map (· / 3) := by
      apply Classical.byContradiction; intro hno
      have h1 : sz N S ≤ (List.range N).countP (fun i => decide (i ∈ t.2.map (· / 3))) := by
        unfold sz; apply List.countP_mono_left; intro i hi hSi
        have hi' := List.mem_range.mp hi
        apply Classical.byContradiction; intro hni
        exact hno ⟨i, hi', by simpa using hSi, by simpa using hni⟩
      have h2 := countP_mem_le N (t.2.map (· / 3))
      simp only [List.length_map] at h2
      omega
    obtain ⟨e', he', hSe, hm⟩ := this
    apply four_zero N e' he' _ S (by have := hS.1 e' he'; omega)
    intro a ha
    show t.1 * monoEval (emb (ashift a _)) t.2 = t.1 * monoEval (emb a) t.2
    rw [monoEval_congr _ _ t.2
      (fun x hx => emb_shift N a ha e' x (fun h => hm (List.mem_map.mpr ⟨x, hx, h⟩)))]
  have := four_cong p N (fun a => g (emb a)) (fun a => Q.eval (emb a)) (fun a _ => by
    have := hQ (emb a); rw [← Int.neg_sub]; exact Int.dvd_neg.mpr this) S
  rw [h0] at this; exact this

theorem tri_case (b j : Nat) (hb : b < 3) (hj : j < 3) (hbj : ¬ b = j) :
    ((2 * j + b) % 3 = 1 ∧ (j + 2 * b) % 3 = 2) ∨ ((2 * j + b) % 3 = 2 ∧ (j + 2 * b) % 3 = 1) := by
  have h1 : b = 0 ∨ b = 1 ∨ b = 2 := by omega
  have h2 : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases h1 with rfl | rfl | rfl <;> rcases h2 with rfl | rfl | rfl <;>
    first | (exfalso; exact hbj rfl) | decide

theorem tri (b j E0 E1 E2 : Nat) (hb : b < 3) (hj : j < 3) (w : ZW)
    (h1 : E1 % 3 = (E0 + b * 1) % 3) (h2 : E2 % 3 = (E0 + b * 2) % 3) :
    smul 3 (rotN E0 (if b = j then w else zero))
      = (rotN E0 w).add ((rotN (2 * j) (rotN E1 w)).add (rotN j (rotN E2 w))) := by
  have r1 : rotN (2 * j) (rotN E1 w) = rotN (2 * j + b) (rotN E0 w) := by
    rw [rotN_rotN, rotN_rotN, rotN_mod, rotN_mod (2 * j + b + E0)]; congr 1; omega
  have r2 : rotN j (rotN E2 w) = rotN (j + 2 * b) (rotN E0 w) := by
    rw [rotN_rotN, rotN_rotN, rotN_mod, rotN_mod (j + 2 * b + E0)]; congr 1; omega
  rw [r1, r2]
  by_cases hbj : b = j
  · rw [ite_eq_left hbj]
    generalize rotN E0 w = z
    rw [rotN_mod (2 * j + b), rotN_mod (j + 2 * b),
      show (2 * j + b) % 3 = 0 by omega, show (j + 2 * b) % 3 = 0 by omega]
    apply eq_of <;> simp [rotN, smul, ZW.add] <;> omega
  · rw [ite_eq_right hbj, rotN_zero]
    generalize rotN E0 w = z
    have hc := tri_case b j hb hj hbj
    rw [rotN_mod (2 * j + b), rotN_mod (j + 2 * b)]
    rcases hc with ⟨c1, c2⟩ | ⟨c1, c2⟩ <;> rw [c1, c2] <;>
      apply eq_of <;> simp [rotN, rot, smul, ZW.add, zero] <;> omega

/-- `3 · \widehat{[a_i = j] h}(S) = ĥ(S) + ω^{2j} ĥ(S + e_i) + ω^j ĥ(S + 2e_i)`. -/
theorem four_ind (N i j : Nat) (hi : i < N) (hj : j < 3) (h : (Nat → Nat) → Int)
    (S : Nat → Nat) :
    smul 3 (four N (fun a => (if a i = j then 1 else 0) * h a) S)
      = (four N h S).add ((rotN (2 * j) (four N h (ashift S (single i 1)))).add
          (rotN j (four N h (ashift S (single i 2))))) := by
  unfold four
  rw [← csum3_smul, ← csum3_rotN, ← csum3_rotN, ← csum3_add, ← csum3_add]
  apply csum3_congr; intro a ha
  dsimp only
  have hw : (⟨(if a i = j then 1 else 0) * h a, 0⟩ : ZW) = if a i = j then ⟨h a, 0⟩ else zero := by
    split
    · exact eq_of (by simp) rfl
    · exact eq_of (by simp [zero]) rfl
  rw [hw]
  apply tri (a i) j (ex N S a) _ _ (ha.1 i hi) hj
  · rw [ex_comm, ex_ashift, ex_comm N a S, ex_single N i 1 hi]
  · rw [ex_comm, ex_ashift, ex_comm N a S, ex_single N i 2 hi]

/-! ## The twisted design -/

section phi
variable (n : Nat) (E : List (Nat × Nat)) (c : Nat → Nat)

/-- `Φ_{S₀}(g) = ∑_S co(S + S₀) ĝ(S)`. -/
noncomputable def Phi (S0 : Nat → Nat) (g : (Nat → Bool) → Int) : ZW :=
  csum3 E.length (fun S => cm (co3 n E c (ashift S S0)) (four E.length (fun a => g (emb a)) S))

/-- The invariant of a line. -/
def Inv3 (p D : Nat) (g : (Nat → Bool) → Int) : Prop :=
  ∀ S0, Valid3 E.length S0 → sz E.length S0 ≤ D → ZC p (Phi n E c S0 g) zero

theorem phi_lin (S0 : Nat → Nat) (f g : (Nat → Bool) → Int) (u v : Int) :
    Phi n E c S0 (fun b => u * f b + v * g b)
      = (smul u (Phi n E c S0 f)).add (smul v (Phi n E c S0 g)) := by
  unfold Phi
  rw [← csum3_smul, ← csum3_smul, ← csum3_add]
  congr 1; funext S
  rw [four_add, four_smul, four_smul, cm_add, cm_smul, cm_smul]

theorem phi_smul (S0 : Nat → Nat) (f : (Nat → Bool) → Int) (u : Int) :
    Phi n E c S0 (fun b => u * f b) = smul u (Phi n E c S0 f) := by
  unfold Phi
  rw [← csum3_smul]
  congr 1; funext S
  rw [four_smul, cm_smul]

theorem phi_cong (p : Nat) (S0 : Nat → Nat) (f g : (Nat → Bool) → Int)
    (h : ∀ b, (p : Int) ∣ f b - g b) : ZC p (Phi n E c S0 f) (Phi n E c S0 g) := by
  unfold Phi
  apply zc_csum3; intro S _
  exact zc_cm _ (four_cong p _ _ _ (fun a _ => h (emb a)) S)

theorem phi_mul (S0 : Nat → Nat) (x : Nat) (hx : x / 3 < E.length) (g : (Nat → Bool) → Int) :
    smul 3 (Phi n E c S0 (fun b => xv x b * g b))
      = (Phi n E c S0 g).add ((rotN (2 * (x % 3)) (Phi n E c (ashift S0 (single (x / 3) 2)) g)).add
          (rotN (x % 3) (Phi n E c (ashift S0 (single (x / 3) 1)) g))) := by
  have hR1 : Valid3 E.length (single (x / 3) 1) := valid_single hx (by omega)
  have hR2 : Valid3 E.length (single (x / 3) 2) := valid_single hx (by omega)
  have hf : ∀ a, Valid3 E.length a → xv x (emb a) * g (emb a)
      = (if a (x / 3) = x % 3 then 1 else 0) * g (emb a) := by
    intro a _
    unfold xv
    by_cases h : a (x / 3) = x % 3
    · have hb : emb a x = true := by simp [emb, h]
      rw [hb, ite_eq_left h]; simp
    · have hb : emb a x = false := by simp [emb, h]
      rw [hb, ite_eq_right h]; simp
  unfold Phi
  rw [← csum3_smul]
  have e0 : ∀ S, smul 3 (cm (co3 n E c (ashift S S0))
        (four E.length (fun a => xv x (emb a) * g (emb a)) S))
      = (cm (co3 n E c (ashift S S0)) (four E.length (fun a => g (emb a)) S)).add
        ((rotN (2 * (x % 3)) (cm (co3 n E c (ashift S S0))
            (four E.length (fun a => g (emb a)) (ashift S (single (x / 3) 1))))).add
         (rotN (x % 3) (cm (co3 n E c (ashift S S0))
            (four E.length (fun a => g (emb a)) (ashift S (single (x / 3) 2)))))) := by
    intro S
    rw [four_congr _ _ _ hf, ← cm_smul, four_ind _ _ _ hx (Nat.mod_lt _ (by omega)), cm_add,
      cm_add, cm_rotN, cm_rotN]
  simp only [e0]
  rw [csum3_add, csum3_add, csum3_rotN, csum3_rotN]
  have s1 : csum3 E.length (fun S => cm (co3 n E c (ashift S S0))
        (four E.length (fun a => g (emb a)) (ashift S (single (x / 3) 1))))
      = csum3 E.length (fun S => cm (co3 n E c (ashift S (ashift S0 (single (x / 3) 2))))
        (four E.length (fun a => g (emb a)) S)) := by
    rw [← csum3_shift E.length (single (x / 3) 2) hR2]
    apply csum3_congr; intro S hS
    rw [ashift_cancel hS (single (x / 3) 1) (single (x / 3) 2) (fun l => by unfold single; split <;> omega), ashift_assoc]
  have s2 : csum3 E.length (fun S => cm (co3 n E c (ashift S S0))
        (four E.length (fun a => g (emb a)) (ashift S (single (x / 3) 2))))
      = csum3 E.length (fun S => cm (co3 n E c (ashift S (ashift S0 (single (x / 3) 1))))
        (four E.length (fun a => g (emb a)) S)) := by
    rw [← csum3_shift E.length (single (x / 3) 1) hR1]
    apply csum3_congr; intro S hS
    rw [ashift_cancel hS (single (x / 3) 2) (single (x / 3) 1) (fun l => by unfold single; split <;> omega), ashift_assoc]
  rw [s1, s2]

end phi

/-! ## Multiplicativity of `co3` -/

def addT (T1 T2 : Nat → Nat) : Nat → Nat := fun w => (T1 w + T2 w) % 3

theorem small_double {n : Nat} {E : List (Nat × Nat)} {Y : Nat → Nat} (hY : SmallBd3 n E Y) :
    SmallBd3 n E (ashift Y Y) := by
  obtain ⟨T, vT, hT, hb⟩ := hY
  refine ⟨addT T T, fun w => Nat.mod_lt _ (by omega), ?_, ?_⟩
  · apply Nat.le_trans _ hT
    unfold size; apply List.countP_mono_left; intro w _ h
    simp [supp, addT] at h ⊢; omega
  · intro i hi; simp only [addT, ashift, hb i hi]; omega

theorem ashift_back {N : Nat} {X : Nat → Nat} (hX : Valid3 N X) (Y : Nat → Nat) :
    ashift (ashift X Y) (ashift Y Y) = X := by
  funext l; simp only [ashift]
  by_cases hN : l < N
  · have := hX.1 l hN; omega
  · rw [hX.2 l (by omega)]; omega

section mul
variable {n : Nat} {E : List (Nat × Nat)} {c : Nat → Nat}
  (hn : 3 ≤ n) (hconn : ∀ S : Nat → Bool, 0 < size n S → size n S < n → bd E S ≠ [])
  {e : Nat}
  (hexp : ∀ S : Nat → Bool, n / 3 < size n S → size n S ≤ 2 * (n / 3) → e ≤ (bd E S).length)
include hn hconn hexp

theorem small_add {X Y : Nat → Nat} (hX : SmallBd3 n E X) (hY : SmallBd3 n E Y)
    (hc : sz E.length (ashift X Y) < e) :
    SmallBd3 n E (ashift X Y) ∧
      ∀ z, cm (co3 n E c (ashift X Y)) z = cm (co3 n E c X) (cm (co3 n E c Y) z) := by
  obtain ⟨vT1, hT1, hb1⟩ := Classical.choose_spec hX
  obtain ⟨vT2, hT2, hb2⟩ := Classical.choose_spec hY
  have vT : ∀ w, addT (Classical.choose hX) (Classical.choose hY) w < 3 :=
    fun w => Nat.mod_lt _ (by omega)
  have hb : BdOf3 E (addT (Classical.choose hX) (Classical.choose hY)) (ashift X Y) := by
    intro i hi; simp only [addT, ashift, hb1 i hi, hb2 i hi]; omega
  have hs : size n (supp (addT (Classical.choose hX) (Classical.choose hY))) ≤ n / 3 := by
    have hu := size_union (n := n) (supp (Classical.choose hX)) (supp (Classical.choose hY))
    have : size n (supp (addT (Classical.choose hX) (Classical.choose hY)))
        ≤ size n (fun w => supp (Classical.choose hX) w || supp (Classical.choose hY) w) := by
      unfold size; apply List.countP_mono_left; intro w _ h
      simp [supp, addT] at h ⊢; omega
    apply Classical.byContradiction; intro h
    have := hexp (supp (addT (Classical.choose hX) (Classical.choose hY))) (by omega) (by omega)
    have := bd_le vT hb
    unfold sz at hc; omega
  have hXY : SmallBd3 n E (ashift X Y) := ⟨_, vT, hs, hb⟩
  refine ⟨hXY, fun z => ?_⟩
  unfold co3
  rw [dite_eq_left hXY, dite_eq_left hX, dite_eq_left hY]
  obtain ⟨vT3, hT3, hb3⟩ := Classical.choose_spec hXY
  have heq := chT3_congr n c _ _ (bd3_unique (by omega) hconn vT3 vT hT3 hs hb3 hb)
  simp only [cm, rotN_rotN]
  rw [rotN_mod, rotN_mod (_ + _)]
  congr 1
  rw [heq]
  have := sum_mod3 (List.range n) c (Classical.choose hX) (Classical.choose hY)
  unfold chT3; simp only [addT]; omega

theorem co3_mul {X Y : Nat → Nat} (hXv : Valid3 E.length X) (hY : SmallBd3 n E Y)
    (hX : sz E.length X < e) (hc : sz E.length (ashift X Y) < e) (z : ZW) :
    cm (co3 n E c (ashift X Y)) z = cm (co3 n E c X) (cm (co3 n E c Y) z) := by
  by_cases hXs : SmallBd3 n E X
  · exact (small_add hn hconn hexp hXs hY hc).2 z
  · have hXY : ¬ SmallBd3 n E (ashift X Y) := by
      intro h
      have h2 := (small_add (c := c) hn hconn hexp h (small_double hY)
        (by rw [ashift_back hXv]; exact hX)).1
      rw [ashift_back hXv] at h2; exact hXs h2
    unfold co3; rw [dite_eq_right hXs, dite_eq_right hXY]; rfl

omit hn hconn hexp in
theorem co3_none {S : Nat → Nat} (h : ¬ SmallBd3 n E S) (z : ZW) : cm (co3 n E c S) z = zero := by
  unfold co3; rw [dite_eq_right h]; rfl

/-- The key step: the invariant extends to shifts with `≤ D + 1` nonzero entries. -/
theorem inv_high3 (p D d : Nat) (h2D : 2 * D < e) (hd : d + 1 ≤ D) (g : (Nat → Bool) → Int)
    (hg : CubeDeg p g d) (hinv : Inv3 n E c p D g) (S' : Nat → Nat)
    (_hS' : Valid3 E.length S') (hs : sz E.length S' ≤ D + 1) :
    ZC p (Phi n E c S' g) zero := by
  by_cases hA : ∃ S1, Valid3 E.length S1 ∧ sz E.length S1 ≤ d ∧ SmallBd3 n E (ashift S1 S')
  · obtain ⟨S1, hv1, hs1, hsm⟩ := hA
    have h1 := hinv (ashift S1 S1) (valid_ashift hv1 hv1)
      (by have := sz_double E.length S1; omega)
    have h2 := zc_cm_zero (co3 n E c (ashift S1 S')) h1
    unfold Phi at h2 ⊢
    rw [cm_csum3] at h2
    refine zc_trans ?_ h2
    apply zc_csum3; intro S hS
    by_cases hsS : sz E.length S ≤ d
    · apply zc_of_eq
      have hm := co3_mul (c := c) hn hconn hexp (X := ashift S (ashift S1 S1))
        (valid_ashift hS (valid_ashift hv1 hv1)) hsm
        (by have := sz_ashift E.length S (ashift S1 S1); have := sz_double E.length S1; omega)
        (by
          have e1 : ashift (ashift S (ashift S1 S1)) (ashift S1 S') = ashift S S' := by
            funext l; simp only [ashift]; omega
          rw [e1]; have := sz_ashift E.length S S'; omega)
      have e1 : ashift (ashift S (ashift S1 S1)) (ashift S1 S') = ashift S S' := by
        funext l; simp only [ashift]; omega
      rw [e1] at hm
      rw [hm, cm_comm]
    · have hf := four_support3 p E.length d g hg S hS (by omega)
      exact zc_trans (zc_cm_zero _ hf) (zc_symm (zc_cm_zero _ (zc_cm_zero _ hf)))
  · unfold Phi
    rw [← csum3_zero E.length]
    apply zc_csum3; intro S hS
    by_cases hsS : sz E.length S ≤ d
    · have hns : ¬ SmallBd3 n E (ashift S S') := fun h => hA ⟨S, hS, hsS, h⟩
      rw [co3_none hns]; exact zc_refl p _
    · exact zc_cm_zero _ (four_support3 p E.length d g hg S hS (by omega))

theorem inv_mul3 (p D d : Nat) (hp : p % 3 ≠ 0) (h2D : 2 * D < e) (hd : d + 1 ≤ D) (x : Nat)
    (g : (Nat → Bool) → Int) (hg : CubeDeg p g d) (hinv : Inv3 n E c p D g) :
    Inv3 n E c p D (fun b => xv x b * g b) := by
  intro S0 hS0 hs
  by_cases hx : x / 3 < E.length
  · apply zc_three p hp
    rw [phi_mul n E c S0 x hx g]
    have z1 := inv_high3 hn hconn hexp p D d h2D hd g hg hinv (ashift S0 (single (x / 3) 2))
      (valid_ashift hS0 (valid_single hx (by omega)))
      (by have := sz_ashift E.length S0 (single (x / 3) 2); have := sz_single E.length (x / 3) 2
          omega)
    have z2 := inv_high3 hn hconn hexp p D d h2D hd g hg hinv (ashift S0 (single (x / 3) 1))
      (valid_ashift hS0 (valid_single hx (by omega)))
      (by have := sz_ashift E.length S0 (single (x / 3) 1); have := sz_single E.length (x / 3) 1
          omega)
    have := zc_add (hinv S0 hS0 hs) (zc_add (zc_rotN (2 * (x % 3)) z1) (zc_rotN (x % 3) z2))
    rwa [rotN_zero, rotN_zero, ZW.add_zero, ZW.add_zero] at this
  · have hk : ∀ a, Valid3 E.length a → xv x (emb a) * g (emb a)
        = (if x % 3 = 0 then 1 else 0) * g (emb a) := by
      intro a ha
      have h0 := ha.2 (x / 3) (by omega)
      have hb : emb a x = decide (0 = x % 3) := by unfold emb; rw [h0]
      unfold xv; rw [hb]
      by_cases h : x % 3 = 0
      · have h' : 0 = x % 3 := h.symm
        rw [decide_eq_true h']; simp [h]
      · have h' : ¬ 0 = x % 3 := fun e => h e.symm
        rw [decide_eq_false h']; simp [h]
    have : Phi n E c S0 (fun b => xv x b * g b)
        = Phi n E c S0 (fun b => (if x % 3 = 0 then 1 else 0) * g b) := by
      unfold Phi; apply csum3_congr; intro S _; rw [four_congr _ _ _ hk]
    rw [this, phi_smul]
    have := zc_smul (if x % 3 = 0 then 1 else 0) (hinv S0 hS0 hs)
    rwa [smul_zero'] at this

end mul

/-! ## Axioms and the main theorem -/

section main
variable {n : Nat} {E : List (Nat × Nat)} {c : Nat → Nat}
  (hn : 3 ≤ n) (hE : ∀ p ∈ E, p.1 < n ∧ p.2 < n ∧ p.1 ≠ p.2)
  (hconn : ∀ S : Nat → Bool, 0 < size n S → size n S < n → bd E S ≠ [])
  {e : Nat}
  (hexp : ∀ S : Nat → Bool, n / 3 < size n S → size n S ≤ 2 * (n / 3) → e ≤ (bd E S).length)
include hn hE hconn hexp

theorem ax_zero3 {v : Nat} (hv : v < n) {t : List (Nat × Nat)} (ht : t ∈ tuples (inc E v))
    (hl : lval E v t % 3 ≠ c v % 3) (S0 : Nat → Nat) (hS0 : Valid3 E.length S0)
    (hD : sz E.length S0 + (inc E v).length < e) :
    Phi n E c S0 (fun b => (clausePoly (tclause t)).eval b) = zero := by
  obtain ⟨hfst, h3⟩ := mem_tuples ht
  let U : Nat → Bool := fun i => decide (i ∈ inc E v) || (S0 i != 0)
  have hUc : (List.range E.length).countP U < e := by
    have h1 := size_union (n := E.length) (fun i => decide (i ∈ inc E v)) (fun i => S0 i != 0)
    have h2 := countP_mem_le E.length (inc E v)
    unfold size at h1; unfold sz at hD
    exact Nat.lt_of_le_of_lt (Nat.le_trans h1 (Nat.add_le_add_right h2 _)) (by omega)
  show design3 E.length (fun S => co3 n E c (ashift S S0))
    (fun a => (clausePoly (tclause t)).eval (emb a)) = zero
  apply design3_zero E.length (Rd E v) U (2 * c v) (lval E v t) _ _ (Rd_valid E v)
  · intro i hi hR
    simp only [U, Bool.or_eq_true, decide_eq_true_eq]; left
    apply Classical.byContradiction; intro h
    exact hR (by simp [Rd, h])
  · omega
  · intro a ha
    rw [tclause_eval a t h3]
    by_cases hall : ∀ q ∈ t, a q.1 = q.2
    · right
      rw [ex_Rd, ← hfst, List.map_map]
      unfold lval
      congr 2
      apply List.map_congr_left; intro q hq
      simp only [Function.comp, hall q hq]
    · left; rw [ite_eq_right hall]
  · intro a ha e' he' hUe
    have hUe' : e' ∉ inc E v := by
      intro h; simp [U, h] at hUe
    have hC : (clausePoly (tclause t)).eval (emb (ashift a (fun i => if i = e' then 1 else 0)))
        = (clausePoly (tclause t)).eval (emb a) := by
      rw [clausePoly_eval, clausePoly_eval, clause_eval_congr]
      intro l hl
      simp only [tclause, List.mem_map] at hl
      obtain ⟨q, hq, rfl⟩ := hl
      apply emb_shift E.length a ha
      rw [vx_div _ _ (h3 q hq)]
      intro h; apply hUe'; rw [← h, ← hfst]; exact List.mem_map_of_mem hq
    exact hC
  · intro S hS hSU z
    show cm (co3 n E c (ashift (ashift S (Rd E v)) S0)) z
      = rotN (2 * c v) (cm (co3 n E c (ashift S S0)) z)
    rw [ashift_swap]
    apply coef_step3 hn hE hconn hexp hv (ashift S S0) (valid_ashift hS hS0)
    · apply Nat.lt_of_le_of_lt _ hUc
      apply List.countP_mono_left; intro i hi h
      have hi' := List.mem_range.mp hi
      simp only [U, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
      by_cases hS0i : S0 i = 0
      · left
        have hSi : S i ≠ 0 := by intro h0; simp [ashift, h0, hS0i] at h
        have := hSU i hi' hSi
        simpa [U, hS0i] using this
      · right; exact hS0i
    · apply Nat.lt_of_le_of_lt _ hUc
      apply List.countP_mono_left; intro i hi h
      have hi' := List.mem_range.mp hi
      simp only [U, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
      by_cases hS0i : S0 i = 0
      · left
        by_cases hinc : i ∈ inc E v
        · exact hinc
        · exfalso
          have hR0 : Rd E v i = 0 := by simp [Rd, hinc]
          have hSi : S i = 0 := by
            apply Classical.byContradiction; intro hSi
            have := hSU i hi' hSi; simp [U, hS0i, hinc] at this
          simp [ashift, hSi, hS0i, hR0] at h
      · right; exact hS0i

theorem inv_ax3 (p D : Nat) (h2D : 2 * D < e) {C : Clause Nat} (hC : C ∈ Ts3 n E c)
    (hCD : C.length ≤ D) : Inv3 n E c p D (fun a => (clausePoly C).eval a) := by
  intro S0 hS0 hs
  rcases ts3_mem hC with ⟨j, hj, hCj⟩ | ⟨v, hv, t, ht, hl, hCt⟩
  · have : Phi n E c S0 (fun a => (clausePoly C).eval a) = zero := by
      unfold Phi; rw [← csum3_zero E.length]; apply csum3_congr; intro S _
      rw [four_congr _ _ (fun _ => 0) (fun a ha => eclause_zero ha hj hCj), four_zero_fun, cm_zero]
    rw [this]; exact zc_refl p _
  · subst hCt
    have hlen : (tclause t).length = (inc E v).length := by
      rw [← (mem_tuples ht).1]; simp [tclause]
    rw [ax_zero3 hn hE hconn hexp hv ht hl S0 hS0 (by omega)]; exact zc_refl p _

/-- **Mod-3 Tseitin is hard for polynomial calculus over `Z/p`, `3 ∤ p`.** For a connected
loopless graph on `n ≥ 3` vertices whose middle-third vertex sets have `≥ e` boundary edges, any
charge and any `p > 1` not divisible by `3` (e.g. `p = 2`): no degree-`D` polynomial calculus
refutation over `Z/p` exists when `2D < e`. -/
theorem ts3_pc_lower (p : Nat) (hp : p % 3 ≠ 0) (hp1 : 1 < p) {D : Nat} (h2D : 2 * D < e)
    (π : PCRefutation p (Ts3 n E c) D) : False := by
  have hall : ∀ g, PCDerivable p (Ts3 n E c) D g → Inv3 n E c p D g := by
    intro g hder
    induction hder with
    | ax C hC hCD => exact inv_ax3 hn hE hconn hexp p D h2D hC hCD
    | lin f g u v _ _ ihf ihg =>
      intro S0 hS0 hs
      rw [phi_lin]
      have := zc_add (zc_smul u (ihf S0 hS0 hs)) (zc_smul v (ihg S0 hS0 hs))
      rwa [smul_zero', smul_zero', ZW.add_zero] at this
    | mul x g d _ hg hd ih => exact inv_mul3 hn hconn hexp p D d hp h2D hd x g hg ih
    | congr f g _ hfg ih =>
      intro S0 hS0 hs
      exact zc_trans (phi_cong n E c p S0 f g hfg) (ih S0 hS0 hs)
  have h1 := hall _ π (fun _ => 0) ⟨fun _ _ => (by decide : 0 < 3), fun _ _ => rfl⟩
    (by unfold sz; simp)
  have hphi : Phi n E c (fun _ => 0) (fun _ => 1) = design3 E.length (co3 n E c) (fun _ => 1) := by
    unfold Phi design3; apply csum3_congr; intro S hS; rw [ashift_zero hS]
  rw [hphi, design3_one] at h1
  have hs0 : size n (supp (fun _ => 0)) = 0 :=
    List.countP_eq_zero.mpr (fun w _ => by simp [supp])
  have h0 : SmallBd3 n E (fun _ => 0) :=
    ⟨fun _ => 0, fun _ => (by decide : 0 < 3), by omega, fun i _ => rfl⟩
  have hc0 : ∀ z, cm (co3 n E c (fun _ => 0)) z = z := by
    intro z
    simp only [co3]; rw [dite_eq_left h0]
    obtain ⟨vT, hT, hb⟩ := Classical.choose_spec h0
    have := chT3_congr n c _ (fun _ => 0)
      (bd3_unique (by omega) hconn vT (fun _ => (by decide : 0 < 3)) hT (by omega) hb
        (fun i _ => rfl))
    simp only [cm]; rw [this]
    have : chT3 n c (fun _ => 0) = 0 := chT3_zero n c
    rw [this]; rfl
  rw [hc0] at h1
  have hx := h1.1
  simp only [zero, Int.sub_zero] at hx
  have hdvd : (p : Int) ∣ ((3 ^ E.length : Nat) : Int) := by
    rw [Int.natCast_pow, show ((3 : Nat) : Int) = 3 from rfl]; exact hx
  have := coprime3_dvd_pow p hp E.length (Int.ofNat_dvd.mp hdvd)
  omega

end main

end Programme.«20261024-1633-proof-complexity».PCTs3

#print axioms Programme.«20261024-1633-proof-complexity».PCTs3.ts3_pc_lower
