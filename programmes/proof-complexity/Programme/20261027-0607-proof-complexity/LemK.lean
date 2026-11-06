import Programme.«20261025-1627-proof-complexity».OntoExt2

/-!
# Lemma K: functions on injective tuples with vanishing slot sums

Ground set `X ⊆ [0, M)` (a Boolean predicate, read below `M`). A `j`-tuple is `u : Nat → Nat`,
valid when its first `j` values are distinct points of `X` and `u s = 0` for `s ≥ j`.
`sig M X j F u t w` is the slot-`t` sum `∑_{a ∈ X, a ∉ u(other slots)} F (u[t := a]) w`.
`KC M X j F`: every slot sum vanishes at every valid tuple (`F` takes values in functions of `w`).

`DP j P u = ∏_{s<j} ([u s = (P s).1] - [u s = (P s).2])` is the product of differences on the
pairs `P s`; `VP M X j P`: the `2j` points are distinct points of `X`.

`lemK`: if `X` has at least `2j` points and `KC M X j F`, then on valid tuples `F` is a finite sum
`∑ DP j P u * c_P w` with every `P` valid and every `c_P` a finite integer combination of the
functions `F u'` at valid tuples `u'` (`LC`). Characteristic-free; proof by induction on `j`
with one anchor point (th, Lemma K).
-/

namespace Programme.«20261027-0607-proof-complexity».LemK

open Programme.«20261025-0459-proof-complexity».OntoFPHP (rsum rsum_add rsum_comm)

/-! ## Finite sums over lists -/

def ls {α : Type} (l : List α) (f : α → Int) : Int := l.foldr (fun a s => f a + s) 0

@[simp] theorem ls_nil {α : Type} (f : α → Int) : ls [] f = 0 := rfl
@[simp] theorem ls_cons {α : Type} (a : α) (l : List α) (f : α → Int) : ls (a :: l) f = f a + ls l f := rfl

theorem ls_append {α : Type} (l l' : List α) (f : α → Int) : ls (l ++ l') f = ls l f + ls l' f := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]; omega

theorem ls_add {α : Type} (l : List α) (f g : α → Int) : ls l (fun a => f a + g a) = ls l f + ls l g := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]; omega

theorem ls_sub {α : Type} (l : List α) (f g : α → Int) : ls l (fun a => f a - g a) = ls l f - ls l g := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]; omega

theorem ls_mul {α : Type} (l : List α) (c : Int) (f : α → Int) : ls l (fun a => c * f a) = c * ls l f := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, Int.mul_add]

theorem ls_mulr {α : Type} (l : List α) (c : Int) (f : α → Int) : ls l (fun a => f a * c) = ls l f * c := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, Int.add_mul]

theorem ls_congr {α : Type} (l : List α) (f g : α → Int) (h : ∀ a ∈ l, f a = g a) : ls l f = ls l g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [ls_cons]
    rw [h a (by simp), ih (fun b hb => h b (by simp [hb]))]

theorem ls_zero {α : Type} (l : List α) (f : α → Int) (h : ∀ a ∈ l, f a = 0) : ls l f = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [ls_cons]; rw [h a (by simp), ih (fun b hb => h b (by simp [hb]))]; rfl

theorem ls_map {α β : Type} (l : List α) (g : α → β) (f : β → Int) : ls (l.map g) f = ls l (fun a => f (g a)) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem ls_flatMap {α β : Type} (l : List α) (g : α → List β) (f : β → Int) :
    ls (l.flatMap g) f = ls l (fun a => ls (g a) f) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, ls_append, ih]

theorem ls_comm {α β : Type} (l : List α) (l' : List β) (f : α → β → Int) :
    ls l (fun a => ls l' (fun b => f a b)) = ls l' (fun b => ls l (fun a => f a b)) := by
  induction l with
  | nil => simp [ls_zero]
  | cons a l ih => simp only [ls_cons]; rw [ih, ← ls_add]

theorem ls_range (M : Nat) (f : Nat → Int) : ls (List.range M) f = rsum M f := by
  induction M with
  | zero => rfl
  | succ M ih => rw [List.range_succ, ls_append, ih]; simp [rsum]

theorem ls_filter {α : Type} (l : List α) (q : α → Bool) (f : α → Int) :
    ls (l.filter q) f = ls l (fun a => if q a = true then f a else 0) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.filter_cons]
    by_cases h : q a = true
    · simp [h, ih]
    · simp [h, ih]

theorem rsum_zero (M : Nat) (f : Nat → Int) (h : ∀ t < M, f t = 0) : rsum M f = 0 := by
  induction M with
  | zero => rfl
  | succ M ih => simp only [rsum]; rw [ih (fun t ht => h t (by omega)), h M (by omega)]; rfl

theorem rsum_pick' (M x : Nat) (F : Nat → Int) (hx : x < M) :
    rsum M (fun v => if v = x then F v else 0) = F x := by
  induction M with
  | zero => omega
  | succ M ih =>
    simp only [rsum]
    by_cases h : x < M
    · rw [ih h, if_neg (by omega)]; omega
    · have : x = M := by omega
      subst this
      rw [if_pos rfl, rsum_zero]
      · omega
      · intro t ht; rw [if_neg (by omega)]

theorem rsum_congr (M : Nat) (f g : Nat → Int) (h : ∀ t < M, f t = g t) : rsum M f = rsum M g := by
  induction M with
  | zero => rfl
  | succ M ih => simp only [rsum]; rw [ih (fun t ht => h t (by omega)), h M (by omega)]

theorem rsum_sub (M : Nat) (f g : Nat → Int) : rsum M (fun t => f t - g t) = rsum M f - rsum M g := by
  induction M with
  | zero => rfl
  | succ M ih => simp only [rsum, ih]; omega

theorem rsum_mul (M : Nat) (c : Int) (f : Nat → Int) : rsum M (fun t => c * f t) = c * rsum M f := by
  induction M with
  | zero => simp [rsum]
  | succ M ih => simp only [rsum, ih, Int.mul_add]

theorem rsum_ls {α : Type} (M : Nat) (l : List α) (f : Nat → α → Int) :
    rsum M (fun t => ls l (fun a => f t a)) = ls l (fun a => rsum M (fun t => f t a)) := by
  rw [← ls_range, ls_comm]
  apply ls_congr; intro a _; rw [ls_range]

/-! ## Tuples -/

/-- `∏_{s<j} f s`. -/
def rprod : Nat → (Nat → Int) → Int
  | 0, _ => 1
  | j + 1, f => rprod j f * f j

theorem rprod_congr (j : Nat) (f g : Nat → Int) (h : ∀ s < j, f s = g s) : rprod j f = rprod j g := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [rprod]; rw [ih (fun s hs => h s (by omega)), h j (by omega)]

theorem rprod_zero (j : Nat) (f : Nat → Int) (s : Nat) (hs : s < j) (h : f s = 0) : rprod j f = 0 := by
  induction j with
  | zero => omega
  | succ j ih =>
    simp only [rprod]
    by_cases hsj : s < j
    · rw [ih hsj, Int.zero_mul]
    · have : s = j := by omega
      subst this; rw [h, Int.mul_zero]

/-- Factor out slot `t` of a product over `j+1` slots. -/
theorem rprod_ins (j t : Nat) (ht : t ≤ j) (f : Nat → Int) :
    rprod (j + 1) f = f t * rprod j (fun s => if s < t then f s else f (s + 1)) := by
  induction j generalizing t with
  | zero =>
    have : t = 0 := by omega
    subst this; simp [rprod]
  | succ j ih =>
    by_cases htj : t ≤ j
    · rw [rprod, ih t htj, rprod]
      rw [if_neg (by omega), Int.mul_assoc]
    · have : t = j + 1 := by omega
      subst this
      rw [rprod]
      rw [Int.mul_comm]
      congr 1
      apply rprod_congr; intro s hs; rw [if_pos hs]

/-- Update slot `t`. -/
def upd (u : Nat → Nat) (t a : Nat) : Nat → Nat := fun s => if s = t then a else u s

/-- Insert value `a` at slot `t` (later slots shift up). -/
def ins (t a : Nat) (v : Nat → Nat) : Nat → Nat := fun s => if s < t then v s else if s = t then a else v (s - 1)

/-- Delete slot `t` (later slots shift down). -/
def skip (t : Nat) (u : Nat → Nat) : Nat → Nat := fun s => if s < t then u s else u (s + 1)

/-- Prepend. -/
def cns (a : Nat) (v : Nat → Nat) : Nat → Nat := fun s => if s = 0 then a else v (s - 1)

/-- Valid `j`-tuple on `X`. -/
def Valid (M : Nat) (X : Nat → Bool) (j : Nat) (u : Nat → Nat) : Prop :=
  (∀ s < j, u s < M ∧ X (u s) = true) ∧ (∀ s < j, ∀ s' < j, u s = u s' → s = s') ∧ ∀ s, j ≤ s → u s = 0

/-- `a` may be placed in slot `t` of `u`. -/
def Free (j : Nat) (u : Nat → Nat) (t a : Nat) : Prop := ∀ s < j, s ≠ t → u s ≠ a

instance (j : Nat) (u : Nat → Nat) (t a : Nat) : Decidable (Free j u t a) := by
  unfold Free; exact inferInstance

variable {W : Type}

/-- Slot-`t` sum. -/
def sig (M : Nat) (X : Nat → Bool) (j : Nat) (F : (Nat → Nat) → W → Int) (u : Nat → Nat) (t : Nat) (w : W) : Int :=
  rsum M (fun a => if X a = true ∧ Free j u t a then F (upd u t a) w else 0)

/-- All slot sums vanish modulo `m` (`m = 0`: exactly). -/
def KC (m : Int) (M : Nat) (X : Nat → Bool) (j : Nat) (F : (Nat → Nat) → W → Int) : Prop :=
  ∀ u, Valid M X j u → ∀ t < j, ∀ w, m ∣ sig M X j F u t w

/-- `[x = a] - [x = a']`. -/
def dl (q : Nat × Nat) (x : Nat) : Int := (if x = q.1 then 1 else 0) - (if x = q.2 then 1 else 0)

/-- Product of differences. -/
def DP (j : Nat) (P : Nat → Nat × Nat) (u : Nat → Nat) : Int := rprod j (fun s => dl (P s) (u s))

/-- `2j` distinct points of `X`. -/
def VP (M : Nat) (X : Nat → Bool) (j : Nat) (P : Nat → Nat × Nat) : Prop :=
  (∀ s < j, (P s).1 < M ∧ X (P s).1 = true ∧ (P s).2 < M ∧ X (P s).2 = true ∧ (P s).1 ≠ (P s).2) ∧
  ∀ s < j, ∀ s' < j, s ≠ s' → (P s).1 ≠ (P s').1 ∧ (P s).1 ≠ (P s').2 ∧ (P s).2 ≠ (P s').2

/-- `c` is an integer combination of the `F u'` at valid tuples `u'`. -/
def LC (M : Nat) (X : Nat → Bool) (j : Nat) (F : (Nat → Nat) → W → Int) (c : W → Int) : Prop :=
  ∃ L : List ((Nat → Nat) × Int), (∀ q ∈ L, Valid M X j q.1) ∧ ∀ w, c w = ls L (fun q => q.2 * F q.1 w)

/-- Number of points of `X` below `M`. -/
def card (M : Nat) (X : Nat → Bool) : Int := rsum M (fun a => if X a = true then 1 else 0)

/-- `X` without `z`. -/
def del (X : Nat → Bool) (z : Nat) : Nat → Bool := fun a => X a && a != z

theorem del_iff (X : Nat → Bool) (z a : Nat) : del X z a = true ↔ X a = true ∧ a ≠ z := by
  simp [del]

/-! ## Sums over a deleted point -/

theorem rsum_del (M : Nat) (X : Nat → Bool) (z : Nat) (hz : z < M) (hX : X z = true)
    (C : Nat → Prop) [DecidablePred C] (g : Nat → Int) :
    rsum M (fun a => if del X z a = true ∧ C a then g a else 0) =
      rsum M (fun a => if X a = true ∧ C a then g a else 0) - (if C z then g z else 0) := by
  have h := rsum_pick' M z (fun a => if C a then g a else 0) hz
  rw [← h, ← rsum_sub]
  apply rsum_congr; intro a _
  by_cases haz : a = z
  · subst haz; simp [del, hX]
  · rw [if_neg haz]
    have : (del X z a = true ∧ C a) ↔ (X a = true ∧ C a) := by
      rw [del_iff]; exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, haz⟩, h.2⟩⟩
    by_cases hc : X a = true ∧ C a
    · rw [if_pos hc, if_pos (this.mpr hc)]; omega
    · rw [if_neg hc, if_neg (fun h' => hc (this.mp h'))]; omega

theorem card_del (M : Nat) (X : Nat → Bool) (z : Nat) (hz : z < M) (hX : X z = true) :
    card M (del X z) = card M X - 1 := by
  have h := rsum_del M X z hz hX (fun _ => True) (fun _ => 1)
  unfold card
  have e1 : rsum M (fun a => if del X z a = true then (1 : Int) else 0) =
      rsum M (fun a => if del X z a = true ∧ True then 1 else 0) := rsum_congr _ _ _ (fun a _ => by simp)
  have e2 : rsum M (fun a => if X a = true then (1 : Int) else 0) =
      rsum M (fun a => if X a = true ∧ True then 1 else 0) := rsum_congr _ _ _ (fun a _ => by simp)
  rw [e1, e2, h]; simp

theorem rsum_le (M : Nat) (f g : Nat → Int) (h : ∀ t < M, f t ≤ g t) : rsum M f ≤ rsum M g := by
  induction M with
  | zero => exact Int.le_refl 0
  | succ M ih => simp only [rsum]; have := ih (fun t ht => h t (by omega)); have := h M (by omega); omega

theorem card_pos (M : Nat) (X : Nat → Bool) (h : 0 < card M X) : ∃ z, z < M ∧ X z = true := by
  apply Classical.byContradiction; intro hn
  have : card M X = 0 := rsum_zero M _ (fun a ha => by
    have : ¬ X a = true := fun hx => hn ⟨a, ha, hx⟩
    simp [this])
  omega

/-- Pigeonhole: more than `2j` points of `X` leave one off the pairs of `Q`. -/
theorem fresh (M : Nat) (X : Nat → Bool) (j : Nat) (Q : Nat → Nat × Nat) (h : 2 * (j : Int) < card M X) :
    ∃ a, a < M ∧ X a = true ∧ ∀ s < j, a ≠ (Q s).1 ∧ a ≠ (Q s).2 := by
  apply Classical.byContradiction; intro hn
  have hle : card M X ≤ rsum M (fun a => rsum j (fun s => (if a = (Q s).1 then 1 else 0) + (if a = (Q s).2 then 1 else 0))) := by
    apply rsum_le; intro a ha
    by_cases hx : X a = true
    · rw [if_pos hx]
      have : ∃ s, s < j ∧ (a = (Q s).1 ∨ a = (Q s).2) := by
        apply Classical.byContradiction; intro hs
        exact hn ⟨a, ha, hx, fun s hs' => ⟨fun e => hs ⟨s, hs', Or.inl e⟩, fun e => hs ⟨s, hs', Or.inr e⟩⟩⟩
      obtain ⟨s, hs, he⟩ := this
      have key : ∀ m, s < m → 1 ≤ rsum m (fun s => (if a = (Q s).1 then (1 : Int) else 0) + (if a = (Q s).2 then 1 else 0)) := by
        intro m hm
        induction m with
        | zero => omega
        | succ m ih =>
          simp only [rsum]
          have h0 : 0 ≤ rsum m (fun s => (if a = (Q s).1 then (1 : Int) else 0) + (if a = (Q s).2 then 1 else 0)) := by
            have := rsum_le m (fun _ => 0) (fun s => (if a = (Q s).1 then (1 : Int) else 0) + (if a = (Q s).2 then 1 else 0))
              (fun t _ => by split <;> split <;> omega)
            rwa [rsum_zero m (fun _ => 0) (fun _ _ => rfl)] at this
          by_cases hsm : s < m
          · have := ih hsm; split <;> split <;> omega
          · have : s = m := by omega
            subst this
            rcases he with e | e
            · rw [if_pos e]; split <;> omega
            · rw [if_pos e]; split <;> omega
      exact key j hs
    · rw [if_neg hx]
      have := rsum_le j (fun _ => 0) (fun s => (if a = (Q s).1 then (1 : Int) else 0) + (if a = (Q s).2 then 1 else 0))
        (fun t _ => by split <;> split <;> omega)
      rwa [rsum_zero j (fun _ => 0) (fun _ _ => rfl)] at this
  have hc : rsum M (fun a => rsum j (fun s => (if a = (Q s).1 then (1 : Int) else 0) + (if a = (Q s).2 then 1 else 0))) ≤ 2 * j := by
    rw [rsum_comm]
    have : ∀ s, rsum M (fun a => (if a = (Q s).1 then (1 : Int) else 0) + (if a = (Q s).2 then 1 else 0)) ≤ 2 := by
      intro s
      rw [rsum_add]
      have e1 := Programme.«20261025-1627-proof-complexity».OntoExt2.rsum_pick M (Q s).1 (fun _ => (1 : Int))
      have e2 := Programme.«20261025-1627-proof-complexity».OntoExt2.rsum_pick M (Q s).2 (fun _ => (1 : Int))
      have e1' : rsum M (fun a => if a = (Q s).1 then (1 : Int) else 0) = if (Q s).1 < M then 1 else 0 := e1
      have e2' : rsum M (fun a => if a = (Q s).2 then (1 : Int) else 0) = if (Q s).2 < M then 1 else 0 := e2
      rw [e1', e2']; split <;> split <;> omega
    have := rsum_le j _ (fun _ => (2 : Int)) (fun s _ => this s)
    have e : rsum j (fun _ => (2 : Int)) = 2 * j := by
      rw [Programme.«20261025-1627-proof-complexity».OntoExt2.rsum_const]; omega
    omega
  omega

/-! ## Tuple identities -/

theorem ins_upd (t z t' a : Nat) (v : Nat → Nat) :
    ins t z (upd v t' a) = upd (ins t z v) (if t' < t then t' else t' + 1) a := by
  funext s; unfold ins upd
  by_cases h1 : s < t
  · by_cases h2 : t' < t
    · simp only [h1, h2, if_true]
    · simp only [h1, h2, if_true, if_false]; rw [if_neg (by omega), if_neg (by omega)]
  · by_cases h3 : s = t
    · subst h3; simp only [h1, if_true, if_false]
      by_cases h2 : t' < s
      · rw [if_pos h2, if_neg (by omega)]
      · rw [if_neg h2, if_neg (by omega)]
    · simp only [h1, h3, if_false]
      by_cases h2 : t' < t
      · rw [if_pos h2, if_neg (by omega)]
        rw [if_neg (by omega : ¬ s = t')]
      · rw [if_neg h2]
        by_cases h5 : s - 1 = t'
        · rw [if_pos h5, if_pos (by omega)]
        · rw [if_neg h5, if_neg (by omega)]

theorem upd_eq_ins (u : Nat → Nat) (s z : Nat) : upd u s z = ins s z (skip s u) := by
  funext r; unfold upd ins skip
  by_cases h1 : r < s
  · simp [h1, show r ≠ s by omega]
  · by_cases h2 : r = s
    · simp [h2]
    · simp only [h1, h2, if_false]; rw [if_neg (by omega)]; congr 1; omega

theorem skip_upd (u : Nat → Nat) (s a : Nat) : skip s (upd u s a) = skip s u := by
  funext r; unfold skip upd
  by_cases h1 : r < s
  · simp [h1, show r ≠ s by omega]
  · simp [h1, show r + 1 ≠ s by omega]

theorem cns_upd (a : Nat) (v : Nat → Nat) (s x : Nat) : cns a (upd v s x) = upd (cns a v) (s + 1) x := by
  funext r; unfold cns upd
  by_cases h : r = 0
  · simp [h]
  · simp only [h, if_false]; by_cases h2 : r - 1 = s
    · rw [if_pos h2, if_pos (by omega)]
    · rw [if_neg h2, if_neg (by omega)]

theorem cns_skip (u : Nat → Nat) : cns (u 0) (skip 0 u) = u := by
  funext r; unfold cns skip
  by_cases h : r = 0
  · simp [h]
  · simp only [h, if_false]; rw [if_neg (by omega)]; congr 1; omega

theorem skip_cns (a : Nat) (v : Nat → Nat) : skip 0 (cns a v) = v := by
  funext r; unfold cns skip; simp

theorem skip_ins (t z : Nat) (v : Nat → Nat) : skip t (ins t z v) = v := by
  funext r; unfold skip ins
  by_cases h : r < t
  · simp [h]
  · simp only [h, if_false]; rw [if_neg (by omega), if_neg (by omega)]; congr 1

/-! ## Validity -/

section
variable {M : Nat} {X : Nat → Bool}

theorem valid_ins {j t z : Nat} {v : Nat → Nat} (hv : Valid M (del X z) j v) (ht : t ≤ j)
    (hz : z < M) (hX : X z = true) : Valid M X (j + 1) (ins t z v) := by
  obtain ⟨h1, h2, h3⟩ := hv
  refine ⟨fun s hs => ?_, fun s hs s' hs' e => ?_, fun s hs => ?_⟩
  · unfold ins
    by_cases a : s < t
    · rw [if_pos a]; have := h1 s (by omega); rw [del_iff] at this; exact ⟨this.1, this.2.1⟩
    · rw [if_neg a]; by_cases b : s = t
      · rw [if_pos b]; exact ⟨hz, hX⟩
      · rw [if_neg b]; have := h1 (s - 1) (by omega); rw [del_iff] at this; exact ⟨this.1, this.2.1⟩
  · have hne : ∀ r < j, v r ≠ z := fun r hr => by have := h1 r hr; rw [del_iff] at this; exact this.2.2
    have val : ∀ r < j + 1, (r = t ∧ ins t z v r = z) ∨ (r < t ∧ ins t z v r = v r) ∨ (t < r ∧ ins t z v r = v (r - 1)) := by
      intro r hr; unfold ins
      by_cases a : r < t
      · right; left; simp [a]
      · by_cases b : r = t
        · left; simp [a, b]
        · right; right; simp [a, b]; omega
    rcases val s hs with ⟨x1, x2⟩ | ⟨x1, x2⟩ | ⟨x1, x2⟩ <;> rcases val s' hs' with ⟨y1, y2⟩ | ⟨y1, y2⟩ | ⟨y1, y2⟩ <;>
      rw [x2, y2] at e <;> (try omega)
    · exact absurd e.symm (hne _ (by omega))
    · exact absurd e.symm (hne _ (by omega))
    · exact absurd e (hne _ (by omega))
    · exact h2 _ (by omega) _ (by omega) e
    · have := h2 _ (by omega) _ (by omega) e; omega
    · exact absurd e (hne _ (by omega))
    · have := h2 _ (by omega) _ (by omega) e; omega
    · have := h2 _ (by omega) _ (by omega) e; omega
  · unfold ins; rw [if_neg (by omega), if_neg (by omega)]; exact h3 _ (by omega)

theorem valid_skip {j t : Nat} {u : Nat → Nat} (hu : Valid M X (j + 1) u) (ht : t ≤ j) :
    Valid M X j (skip t u) := by
  obtain ⟨h1, h2, h3⟩ := hu
  refine ⟨fun s hs => ?_, fun s hs s' hs' e => ?_, fun s hs => ?_⟩
  · unfold skip; split
    · exact h1 s (by omega)
    · exact h1 (s + 1) (by omega)
  · unfold skip at e
    by_cases a : s < t <;> by_cases a' : s' < t <;> simp only [a, a', if_true, if_false] at e
    · exact h2 _ (by omega) _ (by omega) e
    · have := h2 _ (by omega) _ (by omega) e; omega
    · have := h2 _ (by omega) _ (by omega) e; omega
    · have := h2 _ (by omega) _ (by omega) e; omega
  · unfold skip; rw [if_neg (by omega)]; exact h3 _ (by omega)

theorem valid_upd {j t a : Nat} {u : Nat → Nat} (hu : Valid M X j u) (ht : t < j) (ha : a < M)
    (hX : X a = true) (hf : Free j u t a) : Valid M X j (upd u t a) := by
  obtain ⟨h1, h2, h3⟩ := hu
  refine ⟨fun s hs => ?_, fun s hs s' hs' e => ?_, fun s hs => ?_⟩
  · unfold upd; split
    · exact ⟨ha, hX⟩
    · exact h1 s hs
  · unfold upd at e
    by_cases b : s = t <;> by_cases b' : s' = t <;> simp only [b, b', if_true, if_false] at e
    · omega
    · exact absurd e.symm (hf s' hs' b')
    · exact absurd e (hf s hs b)
    · exact h2 _ hs _ hs' e
  · unfold upd; rw [if_neg (by omega)]; exact h3 _ hs

theorem valid_mono {j : Nat} {X' : Nat → Bool} {u : Nat → Nat} (hu : Valid M X' j u)
    (h : ∀ a, X' a = true → X a = true) : Valid M X j u :=
  ⟨fun s hs => ⟨(hu.1 s hs).1, h _ (hu.1 s hs).2⟩, hu.2.1, hu.2.2⟩

theorem valid_del_ne {j z : Nat} {u : Nat → Nat} (hu : Valid M (del X z) j u) : ∀ s < j, u s ≠ z :=
  fun s hs => ((del_iff X z (u s)).mp (hu.1 s hs).2).2

theorem valid_del_of {j z : Nat} {u : Nat → Nat} (hu : Valid M X j u) (h : ∀ s < j, u s ≠ z) :
    Valid M (del X z) j u :=
  ⟨fun s hs => ⟨(hu.1 s hs).1, (del_iff X z _).mpr ⟨(hu.1 s hs).2, h s hs⟩⟩, hu.2.1, hu.2.2⟩

theorem valid_cns {j a : Nat} {v : Nat → Nat} (hv : Valid M (del X a) j v) (ha : a < M) (hX : X a = true) :
    Valid M X (j + 1) (cns a v) := by
  have := valid_ins (t := 0) hv (by omega) ha hX
  have e : ins 0 a v = cns a v := by funext r; unfold ins cns; simp
  rwa [e] at this

theorem valid_tail {j : Nat} {u : Nat → Nat} (hu : Valid M X (j + 1) u) :
    Valid M (del X (u 0)) j (skip 0 u) := by
  apply valid_del_of (valid_skip hu (by omega))
  intro s hs e
  unfold skip at e; rw [if_neg (by omega)] at e
  have := hu.2.1 _ (by omega) _ (by omega) e; omega

/-! ## Free slots -/

theorem free_ins {j t z t' a : Nat} {v : Nat → Nat} (ht : t ≤ j) (ht' : t' < j) :
    Free (j + 1) (ins t z v) (if t' < t then t' else t' + 1) a ↔ a ≠ z ∧ Free j v t' a := by
  unfold Free ins
  constructor
  · intro h
    refine ⟨fun e => h t (by omega) (by split <;> omega) (by simp [e]), fun s hs hst => ?_⟩
    by_cases a1 : s < t
    · have := h s (by omega) (by split <;> omega); rwa [if_pos a1] at this
    · have := h (s + 1) (by omega) (by split <;> omega)
      rwa [if_neg (by omega), if_neg (by omega), show s + 1 - 1 = s by omega] at this
  · rintro ⟨h1, h2⟩ s hs hst
    by_cases a1 : s < t
    · rw [if_pos a1]; exact h2 s (by omega) (by split at hst <;> omega)
    · rw [if_neg a1]; by_cases b : s = t
      · rw [if_pos b]; exact fun e => h1 e.symm
      · rw [if_neg b]; exact h2 (s - 1) (by omega) (by split at hst <;> omega)

theorem free_cns {j a s x : Nat} {v : Nat → Nat} (hs : s < j) :
    Free (j + 1) (cns a v) (s + 1) x ↔ x ≠ a ∧ Free j v s x := by
  unfold Free cns
  constructor
  · intro h
    refine ⟨fun e => h 0 (by omega) (by omega) (by simp [e]), fun r hr hrs => ?_⟩
    have := h (r + 1) (by omega) (by omega); simpa using this
  · rintro ⟨h1, h2⟩ r hr hrs
    by_cases b : r = 0
    · rw [if_pos b]; exact fun e => h1 e.symm
    · rw [if_neg b]; exact h2 (r - 1) (by omega) (by omega)

end

/-! ## Products of differences have vanishing slot sums -/

/-- The other factors of `DP (j+1) P` with slot `t` removed. -/
def Rst (j : Nat) (P : Nat → Nat × Nat) (u : Nat → Nat) (t : Nat) : Int :=
  rprod j (fun s => if s < t then dl (P s) (u s) else dl (P (s + 1)) (u (s + 1)))

theorem DP_split (j : Nat) (P : Nat → Nat × Nat) (u : Nat → Nat) (t : Nat) (ht : t ≤ j) :
    DP (j + 1) P u = dl (P t) (u t) * Rst j P u t := by
  unfold DP Rst; rw [rprod_ins j t ht]

theorem DP_upd (j : Nat) (P : Nat → Nat × Nat) (u : Nat → Nat) (t a : Nat) (ht : t ≤ j) :
    DP (j + 1) P (upd u t a) = dl (P t) a * Rst j P u t := by
  rw [DP_split j P _ t ht]
  unfold upd Rst; simp only [if_true]
  congr 1; apply rprod_congr; intro s _
  by_cases h : s < t
  · rw [if_pos h, if_pos h, if_neg (by omega)]
  · rw [if_neg h, if_neg h, if_neg (by omega)]

theorem Rst_zero (j : Nat) (P : Nat → Nat × Nat) (u : Nat → Nat) (t s : Nat) (ht : t ≤ j) (hs : s < j + 1) (hst : s ≠ t)
    (h : dl (P s) (u s) = 0) : Rst j P u t = 0 := by
  unfold Rst
  by_cases a : s < t
  · exact rprod_zero j _ s (by omega) (by rw [if_pos a]; exact h)
  · exact rprod_zero j _ (s - 1) (by omega) (by rw [if_neg (by omega), show s - 1 + 1 = s by omega]; exact h)

theorem dl_off (q : Nat × Nat) (x : Nat) (h1 : x ≠ q.1) (h2 : x ≠ q.2) : dl q x = 0 := by
  unfold dl; rw [if_neg h1, if_neg h2]; rfl

theorem rsum_dl (M : Nat) (C : Nat → Prop) [DecidablePred C] (q : Nat × Nat) (h1 : q.1 < M) (h2 : q.2 < M) :
    rsum M (fun a => if C a then dl q a else 0) = (if C q.1 then 1 else 0) - (if C q.2 then 1 else 0) := by
  have e : rsum M (fun a => if C a then dl q a else 0) =
      rsum M (fun a => if a = q.1 then (if C a then 1 else 0) else 0) - rsum M (fun a => if a = q.2 then (if C a then 1 else 0) else 0) := by
    rw [← rsum_sub]; apply rsum_congr; intro a _; unfold dl
    by_cases c : C a <;> by_cases e1 : a = q.1 <;> by_cases e2 : a = q.2 <;> simp_all
  rw [e, rsum_pick' M _ _ h1, rsum_pick' M _ _ h2]

/-- Disjoint pairs. -/
def Disj (j : Nat) (P : Nat → Nat × Nat) : Prop :=
  ∀ s < j, ∀ s' < j, s ≠ s' → (P s).1 ≠ (P s').1 ∧ (P s).1 ≠ (P s').2 ∧ (P s).2 ≠ (P s').2

theorem VP_disj {M : Nat} {X : Nat → Bool} {j : Nat} {P : Nat → Nat × Nat} (h : VP M X j P) : Disj j P := h.2

/-- **Slot sums of a difference product vanish** (slot `t` with both points in `Y`). -/
theorem sig_DP (M : Nat) (Y : Nat → Bool) (j : Nat) (P : Nat → Nat × Nat) (u : Nat → Nat) (t : Nat) (w : W)
    (ht : t ≤ j) (hP : Disj (j + 1) P) (hne : (P t).1 ≠ (P t).2) (h1 : (P t).1 < M) (h2 : (P t).2 < M)
    (y1 : Y (P t).1 = true) (y2 : Y (P t).2 = true) :
    sig M Y (j + 1) (fun u (_ : W) => DP (j + 1) P u) u t w = 0 := by
  unfold sig
  have e : rsum M (fun a => if Y a = true ∧ Free (j + 1) u t a then DP (j + 1) P (upd u t a) else 0) =
      rsum M (fun a => if Y a = true ∧ Free (j + 1) u t a then dl (P t) a else 0) * Rst j P u t := by
    rw [Int.mul_comm, ← rsum_mul]; apply rsum_congr; intro a _
    rw [DP_upd j P u t a ht]; split
    · rw [Int.mul_comm]
    · rw [Int.mul_zero]
  rw [e, rsum_dl M _ (P t) h1 h2]
  by_cases f1 : Free (j + 1) u t (P t).1 <;> by_cases f2 : Free (j + 1) u t (P t).2
  · simp [y1, y2, f1, f2]
  all_goals first
    | (have hr : Rst j P u t = 0 := by
        unfold Free at f1
        apply Classical.byContradiction; intro hn
        apply f1; intro s hs hst e
        exact hn (Rst_zero j P u t s ht hs hst (dl_off _ _ (by rw [e]; exact (hP t (by omega) s hs (Ne.symm hst)).1)
          (by rw [e]; exact (hP t (by omega) s hs (Ne.symm hst)).2.1)))
       rw [hr, Int.mul_zero])
    | (have hr : Rst j P u t = 0 := by
        unfold Free at f2
        apply Classical.byContradiction; intro hn
        apply f2; intro s hs hst e
        have d := hP s hs t (by omega) hst
        exact hn (Rst_zero j P u t s ht hs hst (dl_off _ _ (by rw [e]; exact Ne.symm d.2.1)
          (by rw [e]; exact Ne.symm d.2.2)))
       rw [hr, Int.mul_zero])

/-! ## Values off the deleted point determine a `KC` function -/

theorem rsum_dvd_congr (m : Int) (M : Nat) (f g : Nat → Int) (h : ∀ t < M, m ∣ f t - g t) :
    m ∣ rsum M f - rsum M g := by
  rw [← rsum_sub]
  induction M with
  | zero => exact ⟨0, by simp [rsum]⟩
  | succ M ih =>
    simp only [rsum]
    exact Int.dvd_add (ih (fun t ht => h t (by omega))) (h M (by omega))

theorem zero_of_del (m : Int) (M : Nat) (X : Nat → Bool) (j z : Nat) (hz : z < M) (hX : X z = true)
    (H : (Nat → Nat) → W → Int) (hH : KC m M X (j + 1) H)
    (h0 : ∀ u, Valid M (del X z) (j + 1) u → ∀ w, m ∣ H u w) :
    ∀ u, Valid M X (j + 1) u → ∀ w, m ∣ H u w := by
  intro u hu w
  by_cases hz' : ∃ t, t < j + 1 ∧ u t = z
  · obtain ⟨t, ht, hut⟩ := hz'
    have hs := hH u hu t ht w
    unfold sig at hs
    have e : m ∣ rsum M (fun a => if X a = true ∧ Free (j + 1) u t a then H (upd u t a) w else 0) -
        rsum M (fun a => if a = z then H u w else 0) := by
      apply rsum_dvd_congr; intro a ha
      by_cases haz : a = z
      · subst haz
        have hf : Free (j + 1) u t a := fun s hs hst e => hst (hu.2.1 s hs t ht (by rw [e, hut]))
        rw [if_pos ⟨hX, hf⟩, if_pos rfl]
        have : upd u t a = u := by funext s; unfold upd; split <;> simp_all
        rw [this, Int.sub_self]; exact Int.dvd_zero m
      · rw [if_neg haz, Int.sub_zero]; split
        · rename_i hc
          apply h0
          apply valid_del_of (valid_upd hu ht ha hc.1 hc.2)
          intro s hs e; unfold upd at e
          by_cases hst : s = t
          · rw [if_pos hst] at e; exact haz e
          · rw [if_neg hst] at e; exact hst (hu.2.1 s hs t ht (by rw [e, hut]))
        · exact Int.dvd_zero m
    rw [rsum_pick' M z (fun _ => H u w) hz] at e
    have := Int.dvd_sub hs e
    rwa [show ∀ x y : Int, x - (x - y) = y by intros; omega] at this
  · exact h0 u (valid_del_of hu (fun s hs e => hz' ⟨s, hs, e⟩)) w

/-! ## Linear combinations -/

section LCs
variable {M : Nat} {X : Nat → Bool} {j : Nat} {F : (Nat → Nat) → W → Int}

theorem LC_F {u : Nat → Nat} (hu : Valid M X j u) : LC M X j F (F u) :=
  ⟨[(u, 1)], fun q hq => by simp at hq; rw [hq]; exact hu, fun w => by simp [ls]⟩

theorem LC_zero : LC M X j F (fun _ => 0) := ⟨[], fun q hq => by simp at hq, fun w => rfl⟩

theorem LC_add {c c' : W → Int} (h : LC M X j F c) (h' : LC M X j F c') : LC M X j F (fun w => c w + c' w) := by
  obtain ⟨L, hL, he⟩ := h; obtain ⟨L', hL', he'⟩ := h'
  exact ⟨L ++ L', fun q hq => by
    rcases List.mem_append.mp hq with h | h
    · exact hL q h
    · exact hL' q h, fun w => by rw [ls_append, ← he w, ← he' w]⟩

theorem LC_smul (a : Int) {c : W → Int} (h : LC M X j F c) : LC M X j F (fun w => a * c w) := by
  obtain ⟨L, hL, he⟩ := h
  refine ⟨L.map (fun q => (q.1, a * q.2)), fun q hq => ?_, fun w => ?_⟩
  · obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq; exact hL q' hq'
  · show a * c w = _
    rw [ls_map, he w, ← ls_mul]; apply ls_congr; intro q _; simp [Int.mul_assoc]

theorem LC_sub {c c' : W → Int} (h : LC M X j F c) (h' : LC M X j F c') : LC M X j F (fun w => c w - c' w) := by
  have := LC_add h (LC_smul (-1) h')
  obtain ⟨L, hL, he⟩ := this
  exact ⟨L, hL, fun w => by rw [← he w]; show c w - c' w = c w + -1 * c' w; omega⟩

theorem LC_ls {α : Type} (l : List α) (g : α → W → Int) (h : ∀ a ∈ l, LC M X j F (g a)) :
    LC M X j F (fun w => ls l (fun a => g a w)) := by
  induction l with
  | nil => exact LC_zero
  | cons a l ih =>
    exact LC_add (h a (by simp)) (ih (fun b hb => h b (by simp [hb])))

theorem LC_ext {c c' : W → Int} (h : LC M X j F c) (e : ∀ w, c' w = c w) : LC M X j F c' := by
  obtain ⟨L, hL, he⟩ := h; exact ⟨L, hL, fun w => by rw [e, he]⟩

/-- Transitivity: a combination of values of `G`, each a combination of values of `F`. -/
theorem LC_tr {M' : Nat} {Y : Nat → Bool} {j' : Nat} {G : (Nat → Nat) → W → Int} {c : W → Int}
    (h : LC M' Y j' G c) (hG : ∀ v, Valid M' Y j' v → LC M X j F (G v)) : LC M X j F c := by
  obtain ⟨L, hL, he⟩ := h
  have : LC M X j F (fun w => ls L (fun q => q.2 * G q.1 w)) :=
    LC_ls L (fun q w => q.2 * G q.1 w) (fun q hq => LC_smul q.2 (hG q.1 (hL q hq)))
  exact LC_ext this he

end LCs

end Programme.«20261027-0607-proof-complexity».LemK
