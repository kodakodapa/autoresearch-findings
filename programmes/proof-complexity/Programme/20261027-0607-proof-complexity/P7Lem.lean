import Programme.«20261027-0607-proof-complexity».P7Defs

/-!
# The design `T t` of `Work.P7Defs`: sums, base-7 digits and regrouping by class type

`regroup`: for a list `g` whose class counts are bounded (`Bd g`) and a sparse digit list `S` with
`spOk 0 S` and `kap g = spv S`, every sum `∑_{c<11} φ (key g c)` equals `sps S φ`. The proof writes both
sides as `∑_{i<294} μ_i φ i` and uses uniqueness of base-7 digits.
-/

namespace Programme.«20261027-0607-proof-complexity».P7

open Programme.«20261025-0459-proof-complexity».OntoFPHP (rsum rsum_comm rsum_add)
open Programme.«20261025-0459-proof-complexity».OntoSubst (rsum_congr rsum_zero)
open Programme.«20261025-1627-proof-complexity».OntoExt2 (rsum_pick)

/-! ## Sums -/

theorem rsum_shift (f : Nat → Int) : ∀ B, rsum (B + 1) f = f 0 + rsum B (fun i => f (i + 1))
  | 0 => by simp [rsum]
  | B + 1 => by
    have := rsum_shift f B
    simp only [rsum] at this ⊢; rw [this]; omega

theorem rsum_mulr (f : Nat → Int) (a : Int) : ∀ B, rsum B (fun i => a * f i) = a * rsum B f
  | 0 => by simp [rsum]
  | B + 1 => by simp only [rsum]; rw [rsum_mulr f a B, Int.mul_add]

theorem rsum_nonneg (f : Nat → Int) (h : ∀ i, 0 ≤ f i) : ∀ B, 0 ≤ rsum B f
  | 0 => by simp [rsum]
  | B + 1 => by have := rsum_nonneg f h B; have := h B; simp only [rsum]; omega

theorem rsum_ge_term (f : Nat → Int) (h : ∀ i, 0 ≤ f i) : ∀ B a, a < B → f a ≤ rsum B f
  | 0, a, ha => absurd ha (by omega)
  | B + 1, a, ha => by
    simp only [rsum]
    by_cases e : a = B
    · subst e; have := rsum_nonneg f h a; omega
    · have := rsum_ge_term f h B a (by omega); have := h B; omega

theorem nsum_cast (f : Nat → Nat) : ∀ m, (nsum m f : Int) = rsum m (fun c => (f c : Int))
  | 0 => by simp [nsum, rsum]
  | m + 1 => by simp only [nsum, rsum]; rw [Int.natCast_add, nsum_cast f m]

theorem nsum_ge (f : Nat → Nat) : ∀ m a, a < m → f a ≤ nsum m f
  | 0, a, ha => absurd ha (by omega)
  | m + 1, a, ha => by
    simp only [nsum]
    by_cases e : a = m
    · subst e; omega
    · have := nsum_ge f m a (by omega); omega

/-- Changing one term of a sum. -/
theorem nsum_upd (f f' : Nat → Nat) (a : Nat) (h : ∀ c, c ≠ a → f' c = f c) :
    ∀ m, a < m → nsum m f' + f a = nsum m f + f' a
  | 0, ha => absurd ha (by omega)
  | m + 1, ha => by
    simp only [nsum]
    by_cases e : a = m
    · subst e
      have : nsum a f' = nsum a f := by
        clear ha
        have : ∀ j, j ≤ a → nsum j f' = nsum j f := by
          intro j hj
          induction j with
          | zero => rfl
          | succ j ih => simp only [nsum]; rw [ih (by omega), h j (by omega)]
        exact this a (Nat.le_refl a)
      omega
    · have := nsum_upd f f' a h m (by omega); rw [h m (Ne.symm e)]; omega

/-! ## Sparse digit lists -/

/-- Digit `i` of a sparse list. -/
def sp (S : List (Nat × Nat)) (i : Nat) : Int := sps S (fun j => if j = i then 1 else 0)

theorem sps_cons (p : Nat × Nat) (S : List (Nat × Nat)) (f : Nat → Int) :
    sps (p :: S) f = (p.2 : Int) * f p.1 + sps S f := rfl

theorem sps_rsum : ∀ (S : List (Nat × Nat)), (∀ p ∈ S, p.1 < 294) → ∀ f : Nat → Int,
    sps S f = rsum 294 (fun i => sp S i * f i)
  | [], _, f => by simp [sps, sp, rsum_zero 294 _ (fun _ _ => rfl)]
  | p :: S, h, f => by
    have ih := sps_rsum S (fun q hq => h q (by simp [hq])) f
    have e : ∀ i, sp (p :: S) i * f i = (if i = p.1 then (p.2 : Int) * f i else 0) + sp S i * f i := by
      intro i; unfold sp; rw [sps_cons]
      by_cases hi : p.1 = i
      · subst hi; simp [Int.add_mul]
      · simp [hi, Ne.symm hi]
    rw [sps_cons, ih, rsum_congr 294 _ _ (fun i _ => e i), rsum_add, rsum_pick, if_pos (h p (by simp))]

theorem spv_eq (S : List (Nat × Nat)) : (spv S : Int) = sps S (fun i => ((7 ^ i : Nat) : Int)) := by
  induction S with
  | nil => rfl
  | cons p S ih => simp only [spv, sps, List.foldr] at ih ⊢; rw [Int.natCast_add, Int.natCast_mul, ih]

theorem spOk_low : ∀ (b : Nat) (S : List (Nat × Nat)), spOk b S = true → ∀ i, i < b → sp S i = 0
  | _, [], _, _, _ => rfl
  | b, p :: S, h, i, hi => by
    simp only [spOk, Bool.and_eq_true, decide_eq_true_eq] at h
    unfold sp; rw [sps_cons]
    have := spOk_low (p.1 + 1) S h.2 i (by omega)
    unfold sp at this; rw [this, if_neg (by omega)]; simp

theorem spOk_dig : ∀ (b : Nat) (S : List (Nat × Nat)), spOk b S = true → ∀ i, 0 ≤ sp S i ∧ sp S i < 7
  | _, [], _, i => by simp [sp, sps]
  | b, p :: S, h, i => by
    simp only [spOk, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := spOk_dig (p.1 + 1) S h.2 i
    unfold sp at ih ⊢; rw [sps_cons]
    by_cases hi : p.1 = i
    · subst hi
      have := spOk_low (p.1 + 1) S h.2 p.1 (by omega); unfold sp at this
      rw [this, if_pos rfl]; omega
    · rw [if_neg hi]; simp; omega

theorem spOk_lt : ∀ (b : Nat) (S : List (Nat × Nat)), spOk b S = true → ∀ p ∈ S, p.1 < 294
  | _, [], _, _, hp => by simp at hp
  | b, q :: S, h, p, hp => by
    simp only [spOk, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.mp hp with e | e
    · subst e; exact h.1.1.2
    · exact spOk_lt _ S h.2 p e

theorem sp_mem : ∀ (S : List (Nat × Nat)) (i : Nat), sp S i ≠ 0 → ∃ p ∈ S, p.1 = i
  | [], i, h => by simp [sp, sps] at h
  | p :: S, i, h => by
    unfold sp at h; rw [sps_cons] at h
    by_cases hi : p.1 = i
    · exact ⟨p, by simp, hi⟩
    · rw [if_neg hi] at h
      obtain ⟨q, hq, e⟩ := sp_mem S i (by unfold sp; simpa using h)
      exact ⟨q, by simp [hq], e⟩

/-! ## Uniqueness of base-7 digits -/

theorem digits_unique : ∀ (B : Nat) (a b : Nat → Int), (∀ i, 0 ≤ a i ∧ a i < 7) → (∀ i, 0 ≤ b i ∧ b i < 7) →
    rsum B (fun i => a i * ((7 ^ i : Nat) : Int)) = rsum B (fun i => b i * ((7 ^ i : Nat) : Int)) →
    ∀ i < B, a i = b i
  | 0, _, _, _, _, _, i, hi => absurd hi (by omega)
  | B + 1, a, b, ha, hb, h, i, hi => by
    have e : ∀ c : Nat → Int, rsum (B + 1) (fun i => c i * ((7 ^ i : Nat) : Int)) =
        c 0 + 7 * rsum B (fun i => c (i + 1) * ((7 ^ i : Nat) : Int)) := by
      intro c
      rw [rsum_shift, ← rsum_mulr]
      congr 1
      · simp
      · apply rsum_congr; intro j _
        rw [Nat.pow_succ, Int.natCast_mul, ← Int.mul_assoc, Int.mul_comm _ ((7 : Nat) : Int)]; rfl
    rw [e a, e b] at h
    have h0 := ha 0; have h0' := hb 0
    have hab : a 0 = b 0 := by omega
    have hr : rsum B (fun i => a (i + 1) * ((7 ^ i : Nat) : Int)) =
        rsum B (fun i => b (i + 1) * ((7 ^ i : Nat) : Int)) := by omega
    cases i with
    | zero => exact hab
    | succ i =>
      exact digits_unique B (fun i => a (i + 1)) (fun i => b (i + 1)) (fun i => ha _) (fun i => hb _) hr i
        (by omega)

/-! ## Regrouping by class type -/

/-- Count bounds of a matching. -/
def Bd (g : List Nat) : Prop := ∀ c < 11, cc g c 0 ≤ 6 ∧ cc g c 1 ≤ 6 ∧ cc g c 2 ≤ 1

theorem key_lt {g : List Nat} (hb : Bd g) {c : Nat} (hc : c < 11) : key g c < 294 := by
  have := hb c hc; unfold key; omega

theorem key_div {g : List Nat} (hb : Bd g) {c : Nat} (hc : c < 11) : key g c / 98 = (c + 5) / 6 := by
  have := hb c hc; unfold key; omega

def mu (g : List Nat) (i : Nat) : Int := rsum 11 (fun c => if key g c = i then 1 else 0)

theorem regroup_mu {g : List Nat} (hb : Bd g) (φ : Nat → Int) :
    rsum 11 (fun c => φ (key g c)) = rsum 294 (fun i => mu g i * φ i) := by
  have e : ∀ i, mu g i * φ i = rsum 11 (fun c => if i = key g c then φ i else 0) := by
    intro i; unfold mu
    rw [Int.mul_comm, ← rsum_mulr]
    apply rsum_congr; intro c _
    by_cases h : key g c = i
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [rsum_congr 294 _ _ (fun i _ => e i), ← rsum_comm]
  apply rsum_congr; intro c hc
  rw [rsum_congr 294 _ _ (fun i _ => show (if i = key g c then φ i else 0) =
      (if i = key g c then φ (key g c) else 0) by by_cases h : i = key g c <;> simp [h]),
    rsum_pick, if_pos (key_lt hb hc)]

theorem mu_dig {g : List Nat} (hb : Bd g) (i : Nat) : 0 ≤ mu g i ∧ mu g i < 7 := by
  constructor
  · exact rsum_nonneg _ (fun c => by split <;> omega) 11
  · have h1 : mu g i ≤ rsum 11 (fun c => if (c + 5) / 6 = i / 98 then 1 else 0) := by
      unfold mu
      have : ∀ m, m ≤ 11 → rsum m (fun c => if key g c = i then (1 : Int) else 0) ≤
          rsum m (fun c => if (c + 5) / 6 = i / 98 then 1 else 0) := by
        intro m hm
        induction m with
        | zero => simp [rsum]
        | succ m ih =>
          simp only [rsum]
          have := ih (by omega)
          have hk := key_div hb (c := m) (by omega)
          by_cases h : key g m = i
          · rw [if_pos h, if_pos (by rw [← hk, h])]; omega
          · rw [if_neg h]; split <;> omega
      exact this 11 (Nat.le_refl 11)
    have h2 : ∀ q : Nat, rsum 11 (fun c => if (c + 5) / 6 = q then (1 : Int) else 0) ≤ 6 := by
      intro q; simp only [rsum]
      by_cases q0 : q = 0
      · subst q0; decide
      by_cases q1 : q = 1
      · subst q1; decide
      by_cases q2 : q = 2
      · subst q2; decide
      simp [Ne.symm q0, Ne.symm q1, Ne.symm q2]
    have := h2 (i / 98); omega

theorem kap_rsum {g : List Nat} (hb : Bd g) :
    (kap g : Int) = rsum 294 (fun i => mu g i * ((7 ^ i : Nat) : Int)) := by
  unfold kap; rw [nsum_cast]; exact regroup_mu hb (fun i => ((7 ^ i : Nat) : Int))

/-- **Regrouping.** -/
theorem regroup {g : List Nat} (hb : Bd g) {S : List (Nat × Nat)} (hS : spOk 0 S = true)
    (hk : kap g = spv S) (φ : Nat → Int) : rsum 11 (fun c => φ (key g c)) = sps S φ := by
  have hlt := spOk_lt 0 S hS
  have hd : ∀ i < 294, mu g i = sp S i := by
    apply digits_unique 294 _ _ (mu_dig hb) (spOk_dig 0 S hS)
    rw [← kap_rsum hb, ← sps_rsum S hlt, ← spv_eq, hk]
  rw [regroup_mu hb, sps_rsum S hlt]
  apply rsum_congr; intro i hi; rw [hd i hi]

theorem mu_pos {g : List Nat} {c : Nat} (hc : c < 11) : 1 ≤ mu g (key g c) := by
  unfold mu
  have := rsum_ge_term (fun c' => if key g c' = key g c then (1 : Int) else 0) (fun _ => by split <;> omega) 11 c hc
  simp at this; exact this

/-- The type of every class occurs in `S`. -/
theorem key_mem {g : List Nat} (hb : Bd g) {S : List (Nat × Nat)} (hS : spOk 0 S = true)
    (hk : kap g = spv S) {c : Nat} (hc : c < 11) : ∃ p ∈ S, p.1 = key g c := by
  apply sp_mem
  have hlt := spOk_lt 0 S hS
  have hd := digits_unique 294 _ _ (mu_dig hb) (spOk_dig 0 S hS)
    (by rw [← kap_rsum hb, ← sps_rsum S hlt, ← spv_eq, hk]) (key g c) (key_lt hb hc)
  have := mu_pos (g := g) hc; omega

end Programme.«20261027-0607-proof-complexity».P7
