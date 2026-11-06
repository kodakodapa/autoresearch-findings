import Programme.«20261027-0607-proof-complexity».LocWin

/-!
# Block assignments from lists of pairs, counting, and the permanent of disjoint supports

- `fnd J q`: least `c < J` with `q c`, else `J`. `bpA J A i`: block of `i` for pairs `A c`, `c < J`
  (`J` = rest). With pairwise disjoint pairs: `bpA_iff`, `bpA_rest`, and the rest count `cnt_rest`.
- `fresh_fn`: `T` fresh distinct points outside a list.
- `cnt_filter`: the blocks of a list partition it.
- `jp_prod`: the permanent `jp j r l` of a nodup `l` of length `j` equals `∏_s ∑_{x∈l} r s x` when the
  `r s` have pairwise disjoint supports.
-/

namespace Programme.«20261027-0607-proof-complexity».Blocks

open Programme.«20261025-0459-proof-complexity».OntoFPHP (rsum var rsum_comm rsum_add)
open Programme.«20261025-0459-proof-complexity».OntoSubst (rsum_congr rsum_zero)
open Programme.«20261025-1627-proof-complexity».OntoExt2 (rsum_pick rsum_const)
open Programme.«20261025-1627-proof-complexity».OntoExt3 (rsum_sub')
open Programme.«20261027-0607-proof-complexity».LemK (rprod rprod_congr rprod_zero ls ls_congr ls_mul ls_sub ls_cons ls_nil)
open Programme.«20261027-0607-proof-complexity».SJ (jp rprod_first)

/-! ## `fnd` -/

def fnd : Nat → (Nat → Bool) → Nat
  | 0, _ => 0
  | J + 1, q => if q 0 then 0 else fnd J (fun s => q (s + 1)) + 1

theorem fnd_le : ∀ (J : Nat) (q : Nat → Bool), fnd J q ≤ J
  | 0, _ => Nat.le_refl _
  | J + 1, q => by
    unfold fnd; split
    · omega
    · have := fnd_le J (fun s => q (s + 1)); omega

theorem fnd_spec : ∀ (J : Nat) (q : Nat → Bool), fnd J q < J → q (fnd J q) = true
  | 0, _, h => absurd h (by simp [fnd])
  | J + 1, q, h => by
    unfold fnd at h ⊢; split
    · assumption
    · rename_i hq
      rw [if_neg hq] at h
      exact fnd_spec J (fun s => q (s + 1)) (by omega)

theorem fnd_min : ∀ (J : Nat) (q : Nat → Bool) (s : Nat), s < fnd J q → q s = false
  | 0, _, s, h => absurd h (by simp [fnd])
  | J + 1, q, s, h => by
    unfold fnd at h; split at h
    · omega
    · rename_i hq
      cases s with
      | zero => simpa using hq
      | succ s => exact fnd_min J (fun s => q (s + 1)) s (by omega)

theorem fnd_eq_of (J : Nat) (q : Nat → Bool) (s : Nat) (hs : s < J) (hq : q s = true) (hu : ∀ s' < J, q s' = true → s' = s) :
    fnd J q = s := by
  have h1 := fnd_le J q
  by_cases hlt : fnd J q < J
  · exact hu _ hlt (fnd_spec J q hlt)
  · have := fnd_min J q s (by omega); simp_all

theorem fnd_none (J : Nat) (q : Nat → Bool) (h : ∀ s < J, q s = false) : fnd J q = J := by
  have h1 := fnd_le J q
  by_cases hlt : fnd J q < J
  · have := fnd_spec J q hlt; rw [h _ hlt] at this; simp at this
  · omega

/-! ## Block assignment from pairs -/

def inP (A : Nat × Nat) (i : Nat) : Bool := i == A.1 || i == A.2

def bpA (J : Nat) (A : Nat → Nat × Nat) (i : Nat) : Nat := fnd J (fun c => inP (A c) i)

def DisjA (J : Nat) (A : Nat → Nat × Nat) : Prop :=
  ∀ c < J, ∀ c' < J, c ≠ c' → (A c).1 ≠ (A c').1 ∧ (A c).1 ≠ (A c').2 ∧ (A c).2 ≠ (A c').1 ∧ (A c).2 ≠ (A c').2

theorem inP_iff (A : Nat × Nat) (i : Nat) : inP A i = true ↔ i = A.1 ∨ i = A.2 := by
  simp [inP]

theorem bpA_le (J : Nat) (A : Nat → Nat × Nat) (i : Nat) : bpA J A i ≤ J := fnd_le _ _

theorem bpA_iff {J : Nat} {A : Nat → Nat × Nat} (hD : DisjA J A) {c : Nat} (hc : c < J) (i : Nat) :
    bpA J A i = c ↔ i = (A c).1 ∨ i = (A c).2 := by
  constructor
  · intro h
    have := fnd_spec J (fun c => inP (A c) i) (by unfold bpA at h; omega)
    unfold bpA at h; rw [h] at this; exact (inP_iff _ _).mp this
  · intro h
    unfold bpA
    apply fnd_eq_of J (fun c => inP (A c) i) c hc ((inP_iff _ _).mpr h)
    intro s hs hq
    have hq := (inP_iff _ _).mp hq
    by_cases hne : s = c
    · exact hne
    exfalso
    have := hD s hs c hc hne
    rcases hq with rfl | rfl <;> rcases h with h | h <;> simp_all

theorem bpA_rest {J : Nat} {A : Nat → Nat × Nat} (i : Nat) :
    bpA J A i = J ↔ ∀ c < J, i ≠ (A c).1 ∧ i ≠ (A c).2 := by
  constructor
  · intro h c hc
    have := fnd_min J (fun c => inP (A c) i) c (by unfold bpA at h; omega)
    simp only [inP, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at this; exact this
  · intro h
    apply fnd_none; intro s hs
    simp only [inP, Bool.or_eq_false_iff, beq_eq_false_iff_ne]; exact h s hs

/-- Indicator of the rest is `1 - ∑_c [i ∈ A c]`. -/
theorem ind_rest {J : Nat} {A : Nat → Nat × Nat} (hD : DisjA J A) (i : Nat) :
    (if bpA J A i = J then (1 : Int) else 0) =
      1 - rsum J (fun c => if i = (A c).1 ∨ i = (A c).2 then 1 else 0) := by
  by_cases h : bpA J A i = J
  · rw [if_pos h, rsum_zero]
    · rfl
    · intro c hc; have := (bpA_rest i).mp h c hc; rw [if_neg (by omega)]
  · rw [if_neg h]
    have hlt : bpA J A i < J := by have := bpA_le J A i; omega
    rw [rsum_congr J _ (fun c => if c = bpA J A i then 1 else 0)]
    · rw [rsum_pick, if_pos hlt]; rfl
    · intro c hc
      by_cases e : c = bpA J A i
      · rw [if_pos e, if_pos ((bpA_iff hD hc i).mp e.symm)]
      · rw [if_neg e, if_neg (fun h' => e ((bpA_iff hD hc i).mpr h').symm)]

theorem rsum_pair {N a a' : Nat} (ha : a < N) (ha' : a' < N) :
    rsum N (fun i => if i = a ∨ i = a' then (1 : Int) else 0) = if a = a' then 1 else 2 := by
  by_cases e : a = a'
  · subst e; rw [rsum_congr N _ (fun i => if i = a then 1 else 0) (fun i _ => by simp)]
    rw [rsum_pick, if_pos ha]; simp
  · rw [rsum_congr N _ (fun i => (if i = a then 1 else 0) + (if i = a' then 1 else 0))]
    · rw [rsum_add, rsum_pick, rsum_pick, if_pos ha, if_pos ha', if_neg e]; rfl
    · intro i _
      by_cases h1 : i = a <;> by_cases h2 : i = a' <;> simp [h1, h2] <;> omega

/-- **Rest count.** -/
theorem cnt_rest {J N : Nat} {A : Nat → Nat × Nat} (hD : DisjA J A) (hlt : ∀ c < J, (A c).1 < N ∧ (A c).2 < N) :
    rsum N (fun i => if bpA J A i = J then (1 : Int) else 0) =
      N - rsum J (fun c => if (A c).1 = (A c).2 then 1 else 2) := by
  rw [rsum_congr N _ _ (fun i _ => ind_rest hD i), rsum_sub', rsum_const, rsum_comm]
  rw [rsum_congr J _ _ (fun c hc => rsum_pair (hlt c hc).1 (hlt c hc).2)]
  simp

/-! ## Fresh points -/

theorem fresh_fn (L : List Nat) (N : Nat) : ∀ T, L.length + T ≤ N →
    ∃ X : Nat → Nat, (∀ t < T, X t < N ∧ X t ∉ L) ∧ ∀ t < T, ∀ t' < T, X t = X t' → t = t'
  | 0, _ => ⟨fun _ => 0, fun t ht => absurd ht (by omega), fun t ht => absurd ht (by omega)⟩
  | T + 1, h => by
    obtain ⟨X, hX, hXi⟩ := fresh_fn L N T (by omega)
    obtain ⟨x, hx, hxL⟩ := Programme.«20261026-1402-proof-complexity».RectExt.fresh
      (L ++ (List.range T).map X) N (by simp; omega)
    refine ⟨fun t => if t < T then X t else x, fun t ht => ?_, fun t ht t' ht' e => ?_⟩
    · by_cases h : t < T
      · simp only [h, if_true]; exact hX t h
      · simp only [h, if_false]; exact ⟨hx, fun m => hxL (by simp [m])⟩
    · by_cases h : t < T <;> by_cases h' : t' < T <;> simp only [h, h', if_true, if_false] at e
      · exact hXi t h t' h' e
      · exact absurd (List.mem_append_right L (List.mem_map.mpr ⟨t, by simp [h], e⟩)) hxL
      · exact absurd (List.mem_append_right L (List.mem_map.mpr ⟨t', by simp [h'], e.symm⟩)) hxL
      · omega

/-! ## Counting the blocks of a list -/

theorem cnt_filter (β : Nat → Nat) (M : Nat) : ∀ l : List Nat,
    rsum M (fun c => ((l.filter (fun v => β v == c)).length : Int)) +
      ((l.filter (fun v => decide (M ≤ β v))).length : Int) = l.length
  | [] => by simp [rsum_zero M _ (fun _ _ => rfl)]
  | v :: l => by
    have ih := cnt_filter β M l
    have e : ∀ c, (((v :: l).filter (fun v => β v == c)).length : Int) =
        ((l.filter (fun v => β v == c)).length : Int) + (if c = β v then 1 else 0) := by
      intro c; by_cases h : β v = c
      · subst h; simp [List.filter_cons]
      · simp [List.filter_cons, h, Ne.symm h]
    rw [rsum_congr M _ _ (fun c _ => e c), rsum_add, rsum_pick]
    by_cases h : β v < M
    · rw [if_pos h]; simp [List.filter_cons, show ¬ M ≤ β v by omega]; omega
    · rw [if_neg h]; simp [List.filter_cons, show M ≤ β v by omega]; omega

theorem rsum_ge_card (f : Nat → Int) : ∀ j, (∀ c < j, 1 ≤ f c) → (j : Int) ≤ rsum j f
  | 0, _ => by simp [rsum]
  | j + 1, h => by
    have := rsum_ge_card f j (fun c hc => h c (by omega)); have := h j (by omega)
    simp only [rsum]; omega

theorem rsum_eq_card (f : Nat → Int) : ∀ j, (∀ c < j, 1 ≤ f c) → rsum j f ≤ j → ∀ c < j, f c = 1
  | 0, _, _, c, hc => absurd hc (by omega)
  | j + 1, h, hs, c, hc => by
    have h1 := rsum_ge_card f j (fun c hc => h c (by omega)); have h2 := h j (by omega)
    simp only [rsum] at hs
    by_cases e : c = j
    · subst e; omega
    · exact rsum_eq_card f j (fun c hc => h c (by omega)) (by omega) c (by omega)

theorem rsum_nonneg_le (f : Nat → Int) (hf : ∀ c, 0 ≤ f c) : ∀ M j, j ≤ M → rsum j f ≤ rsum M f
  | 0, j, h => by rw [show j = 0 by omega]; exact Int.le_refl _
  | M + 1, j, h => by
    by_cases e : j = M + 1
    · subst e; exact Int.le_refl _
    · have := rsum_nonneg_le f hf M j (by omega); have := hf M; simp only [rsum]; omega

/-! ## `rprod` helpers -/

theorem rprod_one_tail (f : Nat → Int) (j : Nat) : ∀ J, j ≤ J → (∀ c, j ≤ c → c < J → f c = 1) →
    rprod J f = rprod j f
  | 0, h, _ => by rw [show j = 0 by omega]
  | J + 1, h, h1 => by
    by_cases e : j = J + 1
    · subst e; rfl
    · simp only [rprod]; rw [rprod_one_tail f j J (by omega) (fun c a b => h1 c a (by omega)), h1 J (by omega) (by omega)]
      simp

theorem mul_rprod_sub (a : Int) (u w : Nat → Int) : ∀ j, (∀ s < j, a * w s = 0) →
    a * rprod j (fun s => u s - w s) = a * rprod j u
  | 0, _ => rfl
  | j + 1, h => by
    simp only [rprod]
    have ih := mul_rprod_sub a u w j (fun s hs => h s (by omega))
    have hj := h j (by omega)
    rw [← Int.mul_assoc, ih, Int.mul_sub]
    have : a * rprod j u * w j = 0 := by rw [Int.mul_comm a, Int.mul_assoc, hj, Int.mul_zero]
    rw [this, Int.sub_zero, Int.mul_assoc]

theorem ls_erase (l : List Nat) (f : Nat → Int) (x : Nat) (hx : x ∈ l) : ls (l.erase x) f = ls l f - f x := by
  induction l with
  | nil => simp at hx
  | cons y l ih =>
    by_cases e : y = x
    · subst e; simp; omega
    · rw [List.erase_cons_tail (by simpa using e)]
      have hx' : x ∈ l := by simp at hx; rcases hx with h | h; exact absurd h.symm e; exact h
      simp only [ls_cons]; rw [ih hx']; omega

/-- **Permanent of disjoint supports.** -/
theorem jp_prod : ∀ (j : Nat) (r : Nat → Nat → Int) (l : List Nat), l.Nodup → l.length = j →
    (∀ s < j, ∀ s' < j, s ≠ s' → ∀ x, r s x * r s' x = 0) →
    jp j r l = rprod j (fun s => ls l (r s))
  | 0, _, _, _, _, _ => rfl
  | j + 1, r, l, hnd, hlen, hdis => by
    rw [rprod_first]
    unfold jp
    have step : ∀ x ∈ l, r 0 x * jp j (fun s => r (s + 1)) (l.erase x) =
        r 0 x * rprod j (fun s => ls l (r (s + 1))) := by
      intro x hx
      have hlen' : (l.erase x).length = j := by rw [List.length_erase_of_mem hx]; omega
      rw [jp_prod j (fun s => r (s + 1)) (l.erase x) (hnd.erase x) hlen'
        (fun s hs s' hs' hne y => hdis (s + 1) (by omega) (s' + 1) (by omega) (by omega) y)]
      rw [rprod_congr j _ (fun s => ls l (r (s + 1)) - r (s + 1) x) (fun s _ => ls_erase l _ x hx)]
      exact mul_rprod_sub _ _ _ j (fun s hs => hdis 0 (by omega) (s + 1) (by omega) (by omega) x)
    rw [ls_congr l _ _ step]
    have := Programme.«20261027-0607-proof-complexity».LemK.ls_mulr l (rprod j (fun s => ls l (r (s + 1)))) (r 0)
    rw [this]

/-- `ls` over a list equals `ls` over a filter when `f` vanishes off the filter. -/
theorem ls_filter (l : List Nat) (q : Nat → Bool) (f : Nat → Int) (h : ∀ x ∈ l, q x = false → f x = 0) :
    ls l f = ls (l.filter q) f := by
  induction l with
  | nil => rfl
  | cons y l ih =>
    have ih' := ih (fun x hx => h x (by simp [hx]))
    by_cases hq : q y = true
    · simp [List.filter_cons, hq, ih']
    · have := h y (by simp) (by simpa using hq)
      simp [List.filter_cons, hq, this, ih']

end Programme.«20261027-0607-proof-complexity».Blocks
