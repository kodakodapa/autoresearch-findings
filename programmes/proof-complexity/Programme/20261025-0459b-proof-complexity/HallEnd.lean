import Programme.«20261025-0459b-proof-complexity».HallRise
import Programme.«20261025-0459b-proof-complexity».AsgPerm

/-!
# Endgame for the Hall plan (M5 of P88)

Hall-violator graphs `negG α` as in `Work.HallRise` (`α (2i)` = "`i ∈ S`", `α (2j+1)` =
"`j ∈ T`"); `viol n α` says `|T| < |S|` for `S, T ⊆ [n]`, so `negG α` restricted to `[n]×[n]` has
the Hall violator `S` (`N(S) ⊆ T`). `hall_end`: for an edge list `P` whose endpoints lie in a
duplicate-free index list `F ⊆ [n]` containing a vertex `u` that is not a right endpoint of `P`,
at least a `2^{-(2|F|+1)}` fraction of all assignments on the `2n` coordinates make `P` present
and `negG α` a violator.

Proof: fix both coordinates of every index in `F` to "in `S`" and "in `T`", except `u ∉ T`
(a `2^{-2|F|}` fraction, `fix_count`). Then `|S| - |T| = 1 + X - Y` with `X, Y` the counts over
the free indices, and swapping `2i ↔ 2i+1` for free `i` exchanges `X` and `Y` (`cnt_asg_swap`), so
`Y ≤ X` on at least half of them.
-/

namespace Programme.«20261025-0459b-proof-complexity».HallEnd

open Programme.«20261025-0459b-proof-complexity».Indep Programme.«20261025-0459b-proof-complexity».AsgPerm Programme.«20261025-0459b-proof-complexity».HallRise

def viol (n : Nat) (α : Nat → Bool) : Prop :=
  ((List.range n).filter fun j => α (2 * j + 1)).length <
    ((List.range n).filter fun i => α (2 * i)).length

instance (n : Nat) (α : Nat → Bool) : Decidable (viol n α) := by unfold viol; infer_instance

theorem viol_hall (α : Nat → Bool) (i j : Nat) (hi : α (2 * i) = true)
    (hj : α (2 * j + 1) = false) : negG α i j = false := by simp [negG, hi, hj]

/-- Both coordinates of each index of `F`. -/
def cd (F : List Nat) : List Nat := F.flatMap fun i => [2 * i, 2 * i + 1]

theorem mem_cd {F : List Nat} {y : Nat} : y ∈ cd F ↔ y / 2 ∈ F := by
  simp only [cd, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨i, hi, h | h⟩ <;> subst h
    · rw [show 2 * i / 2 = i by omega]; exact hi
    · rw [show (2 * i + 1) / 2 = i by omega]; exact hi
  · intro h; exact ⟨y / 2, h, by omega⟩

theorem cd_nodup : ∀ {F : List Nat}, F.Nodup → (cd F).Nodup
  | [], _ => List.nodup_nil
  | i :: F, h => by
    have hi := (List.nodup_cons.1 h).1
    have ih := cd_nodup (List.nodup_cons.1 h).2
    rw [show cd (i :: F) = [2 * i, 2 * i + 1] ++ cd F from rfl, List.nodup_append]
    refine ⟨by simp, ih, ?_⟩
    intro a ha b hb hab; subst hab
    rw [mem_cd] at hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact hi (by rwa [show 2 * i / 2 = i by omega] at hb)
    · exact hi (by rwa [show (2 * i + 1) / 2 = i by omega] at hb)

theorem cd_length : ∀ F : List Nat, (cd F).length = 2 * F.length
  | [] => rfl
  | i :: F => by
    rw [show cd (i :: F) = [2 * i, 2 * i + 1] ++ cd F from rfl, List.length_append, cd_length F]
    simp; omega

/-- Split a filter count along a second predicate. -/
theorem len_split (q p : Nat → Bool) : ∀ l : List Nat,
    (l.filter p).length = (l.filter fun x => q x && p x).length +
      (l.filter fun x => !q x && p x).length
  | [] => rfl
  | x :: l => by
    have ih := len_split q p l
    simp only [List.filter_cons]
    cases hq : q x <;> cases hp : p x <;> simp <;> omega

theorem len_mono (q p : Nat → Bool) : ∀ l : List Nat, (∀ x ∈ l, q x = true → p x = true) →
    (l.filter q).length ≤ (l.filter p).length
  | [], _ => Nat.le_refl _
  | x :: l, h => by
    have ih := len_mono q p l (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have hx := h x (List.mem_cons_self ..)
    simp only [List.filter_cons]
    cases hq : q x <;> cases hp : p x <;> simp_all <;> omega

theorem len_strict (q p : Nat → Bool) : ∀ l : List Nat, (∀ x ∈ l, q x = true → p x = true) →
    (∃ x ∈ l, p x = true ∧ q x = false) → (l.filter q).length < (l.filter p).length
  | [], _, ⟨_, h, _⟩ => by simp at h
  | x :: l, h, ⟨y, hy, hpy, hqy⟩ => by
    have hm := len_mono q p l (fun z hz => h z (List.mem_cons_of_mem _ hz))
    have hx := h x (List.mem_cons_self ..)
    rcases List.mem_cons.1 hy with rfl | hy
    · simp only [List.filter_cons, hpy, hqy]; simp; omega
    · have ih := len_strict q p l (fun z hz => h z (List.mem_cons_of_mem _ hz)) ⟨y, hy, hpy, hqy⟩
      simp only [List.filter_cons]
      cases hq : q x <;> cases hp : p x <;> simp_all <;> omega

/-- Forced values: every coordinate true except the right coordinate of `u`. -/
def fv (u : Nat) (y : Nat) : Bool := !(y == 2 * u + 1)

/-- Swap the two coordinates of every index outside `F`. -/
def sw (F : List Nat) (y : Nat) : Nat := if y / 2 ∈ F then y else if y % 2 = 0 then y + 1 else y - 1

theorem sw_div (F : List Nat) (y : Nat) : sw F y / 2 = y / 2 := by
  unfold sw; split
  · rfl
  · split <;> omega

theorem sw_sw (F : List Nat) (y : Nat) : sw F (sw F y) = y := by
  by_cases h : y / 2 ∈ F
  · simp [sw, h]
  · by_cases h2 : y % 2 = 0
    · have e1 : sw F y = y + 1 := by simp [sw, h, h2]
      have h' : ¬(y + 1) / 2 ∈ F := by rw [show (y + 1) / 2 = y / 2 by omega]; exact h
      rw [e1]; simp only [sw, h', ite_false]; rw [if_neg (by omega)]; omega
    · have e1 : sw F y = y - 1 := by simp [sw, h, h2]
      have h' : ¬(y - 1) / 2 ∈ F := by rw [show (y - 1) / 2 = y / 2 by omega]; exact h
      rw [e1]; simp only [sw, h', ite_false]; rw [if_pos (by omega)]; omega

/-- Free-index counts on the left (`X`) and the right (`Y`). -/
def cX (n : Nat) (F : List Nat) (α : Nat → Bool) : Nat :=
  ((List.range n).filter fun i => !decide (i ∈ F) && α (2 * i)).length

def cY (n : Nat) (F : List Nat) (α : Nat → Bool) : Nat :=
  ((List.range n).filter fun i => !decide (i ∈ F) && α (2 * i + 1)).length

theorem cX_sw (n : Nat) (F : List Nat) (α : Nat → Bool) : cX n F (fun y => α (sw F y)) = cY n F α := by
  unfold cX cY; congr 1; apply List.filter_congr; intro i _
  by_cases h : i ∈ F
  · simp [h]
  · have : sw F (2 * i) = 2 * i + 1 := by
      unfold sw; rw [if_neg (by rw [show 2 * i / 2 = i by omega]; exact h), if_pos (by omega)]
    simp [h, this]

theorem cY_sw (n : Nat) (F : List Nat) (α : Nat → Bool) : cY n F (fun y => α (sw F y)) = cX n F α := by
  unfold cX cY; congr 1; apply List.filter_congr; intro i _
  by_cases h : i ∈ F
  · simp [h]
  · have : sw F (2 * i + 1) = 2 * i := by
      unfold sw; rw [if_neg (by rw [show (2 * i + 1) / 2 = i by omega]; exact h), if_neg (by omega)]
      omega
    simp [h, this]

def fixd (F : List Nat) (u : Nat) (α : Nat → Bool) : Prop := ∀ y ∈ cd F, α y = fv u y

instance (F : List Nat) (u : Nat) (α : Nat → Bool) : Decidable (fixd F u α) := by
  unfold fixd; infer_instance

theorem fixd_sw (F : List Nat) (u : Nat) (α : Nat → Bool) :
    fixd F u (fun y => α (sw F y)) ↔ fixd F u α := by
  have : ∀ y ∈ cd F, sw F y = y := fun y hy => by unfold sw; rw [if_pos (mem_cd.1 hy)]
  unfold fixd
  exact ⟨fun h y hy => by have h1 := h y hy; simp only [this y hy] at h1; exact h1,
    fun h y hy => by show α (sw F y) = _; rw [this y hy]; exact h y hy⟩

/-- On fixed assignments with `Y ≤ X`: `P` is present and `|T| < |S|`. -/
theorem good_of (n : Nat) (P : List (Nat × Nat)) (F : List Nat) (u : Nat)
    (hF : ∀ i ∈ F, i < n) (hu : u ∈ F) (hP : ∀ e ∈ P, e.1 ∈ F ∧ e.2 ∈ F ∧ e.2 ≠ u)
    (α : Nat → Bool) (hfx : fixd F u α) (hxy : cY n F α ≤ cX n F α) :
    pres (negG α) P ∧ viol n α := by
  have hS : ∀ i ∈ F, α (2 * i) = true := fun i hi => by
    rw [hfx _ (mem_cd.2 (by rw [show 2 * i / 2 = i by omega]; exact hi))]; simp [fv]; omega
  have hT : ∀ j ∈ F, j ≠ u → α (2 * j + 1) = true := fun j hj hju => by
    rw [hfx _ (mem_cd.2 (by rw [show (2 * j + 1) / 2 = j by omega]; exact hj))]; simp [fv]; omega
  have hTu : α (2 * u + 1) = false := by
    rw [hfx _ (mem_cd.2 (by rw [show (2 * u + 1) / 2 = u by omega]; exact hu))]; simp [fv]
  refine ⟨fun e he => ?_, ?_⟩
  · obtain ⟨_, h2, h3⟩ := hP e he
    simp [negG, hT e.2 h2 h3]
  · unfold viol
    rw [len_split (fun i => decide (i ∈ F)) (fun j => α (2 * j + 1)),
      len_split (fun i => decide (i ∈ F)) (fun i => α (2 * i))]
    have hlt : ((List.range n).filter fun x => decide (x ∈ F) && α (2 * x + 1)).length <
        ((List.range n).filter fun x => decide (x ∈ F) && α (2 * x)).length := by
      apply len_strict
      · intro x _ h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢
        exact ⟨h.1, hS x h.1⟩
      · exact ⟨u, List.mem_range.2 (hF u hu), by simp [hu, hS u hu], by simp [hTu]⟩
    unfold cX cY at hxy
    omega

/-- **M5.** For `U` duplicate-free with `y ∈ U ↔ y < 2n`, an edge list `P` with endpoints in a
duplicate-free `F ⊆ [n]`, and `u ∈ F` not a right endpoint of `P`: at least `2^|U| / 2^(2|F|+1)`
assignments on `U` make every edge of `P` present in the Hall-violator graph `negG α` and have
`|T| < |S|`. -/
theorem hall_end (n : Nat) (U : List Nat) (hU : U.Nodup) (hUn : ∀ y, y ∈ U ↔ y < 2 * n)
    (P : List (Nat × Nat)) (F : List Nat) (u : Nat) (hFn : F.Nodup) (hF : ∀ i ∈ F, i < n)
    (hu : u ∈ F) (hP : ∀ e ∈ P, e.1 ∈ F ∧ e.2 ∈ F ∧ e.2 ≠ u) :
    2 ^ U.length ≤ 2 ^ (2 * F.length + 1) * cnt (asg U) (fun α => pres (negG α) P ∧ viol n α) := by
  -- the fixed fraction
  have h1 := fix_count (fv u) U (cd F) (fun _ => false) hU (cd_nodup hFn) (fun y hy => by
    have := hF _ (mem_cd.1 hy); rw [hUn]; omega)
  rw [cd_length] at h1
  change 2 ^ U.length ≤ 2 ^ (2 * F.length) * cnt (asg U) (fixd F u) at h1
  -- the swap
  have hswU : ∀ y, y ∈ U ↔ sw F y ∈ U := fun y => by
    rw [hUn, hUn]
    have := sw_div F y; constructor <;> intro <;> omega
  have hsym := cnt_asg_swap hU (sw F) (sw_sw F) hswU
    (fun α => fixd F u α ∧ ¬cY n F α ≤ cX n F α)
  simp only [fixd_sw, cX_sw, cY_sw] at hsym
  have hsplit := cnt_and (L := asg U) (P := fixd F u) (Q := fun α => cY n F α ≤ cX n F α)
  have hle : cnt (asg U) (fun α => fixd F u α ∧ ¬cX n F α ≤ cY n F α) ≤
      cnt (asg U) (fun α => fixd F u α ∧ cY n F α ≤ cX n F α) :=
    cnt_mono (fun α _ h => ⟨h.1, by omega⟩)
  have hgood : cnt (asg U) (fun α => fixd F u α ∧ cY n F α ≤ cX n F α) ≤
      cnt (asg U) (fun α => pres (negG α) P ∧ viol n α) :=
    cnt_mono (fun α _ h => good_of n P F u hF hu hP α h.1 h.2)
  rw [Nat.pow_succ]
  calc 2 ^ U.length ≤ 2 ^ (2 * F.length) * cnt (asg U) (fixd F u) := h1
    _ ≤ 2 ^ (2 * F.length) * (2 * cnt (asg U) (fun α => pres (negG α) P ∧ viol n α)) :=
      Nat.mul_le_mul_left _ (by omega)
    _ = _ := by rw [Nat.mul_assoc, Nat.mul_left_comm]

/-- **M3 on a fixed coordinate list.** `hall_rise` restated over any duplicate-free `U` with the
same coordinates as `base ++ R_1 ++ … ++ R_p` (e.g. all `y < 2n`), so that the rise bound of M3 and
the endgame count `hall_end` are over the same assignments. -/
theorem hall_rise_on (ℓ : Nat) (U base : List Nat) (Ps : List Petal) (hU : U.Nodup)
    (hnd : (base ++ Ps.flatMap Petal.R).Nodup) (hmem : ∀ y, y ∈ U ↔ y ∈ base ++ Ps.flatMap Petal.R)
    (hok : ∀ P ∈ Ps, Ok ℓ base P) :
    cnt (asg U) (fun α => ∀ P ∈ Ps, ¬pres (negG α) P.Q) * 2 ^ (ℓ * Ps.length) ≤
      2 ^ U.length * (2 ^ ℓ - 1) ^ Ps.length := by
  have hl : U.length = (base ++ Ps.flatMap Petal.R).length :=
    ((List.perm_ext_iff_of_nodup hU hnd).2 hmem).length_eq
  rw [cnt_asg_congr hU hnd hmem, hl]
  exact hall_rise ℓ base Ps hnd hok

end Programme.«20261025-0459b-proof-complexity».HallEnd
