import Programme.«20261027-0607-proof-complexity».LemK

/-!
# Lemma K, main induction (see `Work.LemK`)
-/

namespace Programme.«20261027-0607-proof-complexity».LemK

open Programme.«20261025-0459-proof-complexity».OntoFPHP (rsum rsum_add rsum_comm)

variable {W : Type}

/-- Insert pair `q` at slot `t`. -/
def insP (t : Nat) (q : Nat × Nat) (Q : Nat → Nat × Nat) : Nat → Nat × Nat :=
  fun s => if s < t then Q s else if s = t then q else Q (s - 1)

theorem DP_insP (j t : Nat) (ht : t ≤ j) (q : Nat × Nat) (Q : Nat → Nat × Nat) (u : Nat → Nat) :
    DP (j + 1) (insP t q Q) u = dl q (u t) * DP j Q (skip t u) := by
  rw [DP_split j _ u t ht]
  unfold insP Rst DP skip
  simp only [Nat.lt_irrefl, if_false, if_true]
  congr 1; apply rprod_congr; intro s _
  by_cases h : s < t
  · simp [h]
  · simp only [h, if_false]; rw [if_neg (by omega), if_neg (by omega)]; rfl

theorem VP_insP {M : Nat} {X Y : Nat → Bool} {j t z w : Nat} {Q : Nat → Nat × Nat} (ht : t ≤ j)
    (hQ : VP M Y j Q) (hY : ∀ a, Y a = true → X a = true ∧ a ≠ z) (hz : z < M) (hXz : X z = true)
    (hw : w < M) (hXw : X w = true) (hwz : w ≠ z) (hwQ : ∀ s < j, w ≠ (Q s).1 ∧ w ≠ (Q s).2) :
    VP M X (j + 1) (insP t (w, z) Q) := by
  obtain ⟨h1, h2⟩ := hQ
  have pt : ∀ s < j, ((Q s).1 < M ∧ X (Q s).1 = true ∧ (Q s).1 ≠ z) ∧ ((Q s).2 < M ∧ X (Q s).2 = true ∧ (Q s).2 ≠ z) := by
    intro s hs; obtain ⟨a1, a2, a3, a4, _⟩ := h1 s hs
    exact ⟨⟨a1, (hY _ a2).1, (hY _ a2).2⟩, ⟨a3, (hY _ a4).1, (hY _ a4).2⟩⟩
  -- every slot holds either `(w, z)` (slot `t`) or `Q r` for the matching index `r`
  have cls : ∀ s, (s = t ∧ insP t (w, z) Q s = (w, z)) ∨ (s ≠ t ∧ insP t (w, z) Q s = Q (if s < t then s else s - 1)) := by
    intro s; unfold insP
    by_cases a : s < t
    · right; simp [a]; omega
    · by_cases b : s = t
      · left; simp [a, b]
      · right; simp [a, b]
  refine ⟨fun s hs => ?_, fun s hs s' hs' hss => ?_⟩
  · rcases cls s with ⟨_, e⟩ | ⟨b, e⟩ <;> rw [e]
    · exact ⟨hw, hXw, hz, hXz, hwz⟩
    · have hr : (if s < t then s else s - 1) < j := by split <;> omega
      obtain ⟨⟨a1, a2, _⟩, ⟨a3, a4, _⟩⟩ := pt _ hr
      exact ⟨a1, a2, a3, a4, (h1 _ hr).2.2.2.2⟩
  · rcases cls s with ⟨b, e⟩ | ⟨b, e⟩ <;> rcases cls s' with ⟨b', e'⟩ | ⟨b', e'⟩ <;> rw [e, e']
    · omega
    · have hr : (if s' < t then s' else s' - 1) < j := by split <;> omega
      exact ⟨(hwQ _ hr).1, (hwQ _ hr).2, fun h => (pt _ hr).2.2.2 h.symm⟩
    · have hr : (if s < t then s else s - 1) < j := by split <;> omega
      exact ⟨fun h => (hwQ _ hr).1 h.symm, fun h => (pt _ hr).1.2.2 h, fun h => (pt _ hr).2.2.2 h⟩
    · have hr : (if s < t then s else s - 1) < j := by split <;> omega
      have hr' : (if s' < t then s' else s' - 1) < j := by split <;> omega
      have hne : (if s < t then s else s - 1) ≠ (if s' < t then s' else s' - 1) := by split <;> split <;> omega
      exact h2 _ hr _ hr' hne


/-! ## Linearity of slot sums -/

theorem rsum_mulr' (M : Nat) (c : Int) (f : Nat → Int) : rsum M (fun t => f t * c) = rsum M f * c := by
  rw [Int.mul_comm, ← rsum_mul]; apply rsum_congr; intro t _; rw [Int.mul_comm]

theorem sig_sub (M : Nat) (Y : Nat → Bool) (J : Nat) (F G : (Nat → Nat) → W → Int) (u : Nat → Nat) (t : Nat) (w : W) :
    sig M Y J (fun u w => F u w - G u w) u t w = sig M Y J F u t w - sig M Y J G u t w := by
  unfold sig; rw [← rsum_sub]; apply rsum_congr; intro a _; split
  · rfl
  · rfl

theorem sig_lsDP {β : Type} (M : Nat) (Y : Nat → Bool) (J : Nat) (B : List (β × (W → Int)))
    (D : β → (Nat → Nat) → Int) (u : Nat → Nat) (t : Nat) (w : W) :
    sig M Y J (fun u w => ls B (fun b => D b.1 u * b.2 w)) u t w =
      ls B (fun b => sig M Y J (fun u (_ : W) => D b.1 u) u t w * b.2 w) := by
  unfold sig
  have e : ∀ a, (if Y a = true ∧ Free J u t a then ls B (fun b => D b.1 (upd u t a) * b.2 w) else 0) =
      ls B (fun b => (if Y a = true ∧ Free J u t a then D b.1 (upd u t a) else 0) * b.2 w) := by
    intro a; split
    · rfl
    · rw [ls_zero]; intro b _; rw [Int.zero_mul]
  rw [rsum_congr M _ _ (fun a _ => e a), rsum_ls]
  apply ls_congr; intro b _; rw [rsum_mulr']

theorem sig_neg (M : Nat) (Y : Nat → Bool) (J : Nat) (F : (Nat → Nat) → W → Int) (u : Nat → Nat) (t : Nat) (w : W) :
    sig M Y J (fun u w => -F u w) u t w = -sig M Y J F u t w := by
  unfold sig
  have : (-rsum M (fun a => if Y a = true ∧ Free J u t a then F (upd u t a) w else 0)) =
      rsum M (fun a => (-1) * (if Y a = true ∧ Free J u t a then F (upd u t a) w else 0)) := by rw [rsum_mul]; omega
  rw [this]; apply rsum_congr; intro a _; split
  · show -F (upd u t a) w = _; omega
  · omega

theorem rsum_neg0 (M : Nat) (f : Nat → Int) (h : rsum M f = 0) : rsum M (fun a => -f a) = 0 := by
  have := rsum_mul M (-1) f; rw [h] at this
  rw [← this.trans (by omega : (-1 : Int) * 0 = 0)]; apply rsum_congr; intro a _; omega

/-- The valid tuples of `DP` vanish at any coordinate off its pairs. -/
theorem DP_off (j : Nat) (Q : Nat → Nat × Nat) (v : Nat → Nat) (s : Nat) (hs : s < j)
    (h : ∀ r < j, v s ≠ (Q r).1 ∧ v s ≠ (Q r).2) : DP j Q v = 0 :=
  rprod_zero j _ s hs (dl_off _ _ (h s hs).1 (h s hs).2)

/-! ## The induction step -/

/-- The statement of Lemma K at length `j`. -/
def LK (W : Type) (m : Int) (j : Nat) : Prop :=
  ∀ (M : Nat) (X : Nat → Bool) (F : (Nat → Nat) → W → Int), 2 * (j : Int) ≤ card M X → KC m M X j F →
    ∃ B : List ((Nat → Nat × Nat) × (W → Int)), (∀ b ∈ B, VP M X j b.1 ∧ LC M X j F b.2) ∧
      ∀ u, Valid M X j u → ∀ w, m ∣ F u w - ls B (fun b => DP j b.1 u * b.2 w)

theorem lemK_zero (m : Int) : LK W m 0 := by
  intro M X F _ _
  refine ⟨[(fun _ => (0, 0), F (fun _ => 0))], fun b hb => ?_, fun u hu w => ?_⟩
  · simp at hb; subst hb
    exact ⟨⟨fun s hs => by omega, fun s hs => by omega⟩, LC_F ⟨fun s hs => by omega, fun s hs => by omega, fun _ _ => rfl⟩⟩
  · have : u = fun _ => 0 := funext fun s => hu.2.2 s (by omega)
    subst this; simp [ls, DP, rprod]

theorem lemK_step (m : Int) (j : Nat) (ih : LK W m j) : LK W m (j + 1) := by
  intro M X F hc hK
  obtain ⟨z, hz, hXz⟩ := card_pos M X (by push_cast at hc; omega)
  have hc' : card M (del X z) = card M X - 1 := card_del M X z hz hXz
  have hdX : ∀ a, del X z a = true → X a = true := fun a h => ((del_iff X z a).mp h).1
  let G : Nat → (Nat → Nat) → W → Int := fun t v w => -F (ins t z v) w
  -- (1) the slot defects are `KC` one level down
  have hG : ∀ t ≤ j, KC m M (del X z) j (G t) := by
    intro t ht v hv t' ht' w
    have hu := valid_ins hv ht hz hXz
    have hT : (if t' < t then t' else t' + 1) < j + 1 := by split <;> omega
    have h0 := hK _ hu _ hT w
    unfold sig at h0 ⊢
    have e := rsum_mul M (-1) (fun a => if X a = true ∧ Free (j + 1) (ins t z v) (if t' < t then t' else t' + 1) a then
      F (upd (ins t z v) (if t' < t then t' else t' + 1) a) w else 0)
    have h0' : m ∣ (-1) * rsum M (fun a => if X a = true ∧ Free (j + 1) (ins t z v) (if t' < t then t' else t' + 1) a then
      F (upd (ins t z v) (if t' < t then t' else t' + 1) a) w else 0) := Int.dvd_mul_of_dvd_right h0
    rw [← e] at h0'
    refine (Int.dvd_iff_dvd_of_dvd_sub ?_).mpr h0'
    apply rsum_dvd_congr; intro a _
    rw [show G t (upd v t' a) w = -F (ins t z (upd v t' a)) w from rfl, ins_upd]
    have hiff : (del X z a = true ∧ Free j v t' a) ↔ (X a = true ∧ Free (j + 1) (ins t z v) (if t' < t then t' else t' + 1) a) := by
      rw [free_ins ht ht', del_iff]
      exact ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩
    by_cases hc1 : del X z a = true ∧ Free j v t' a
    · rw [if_pos hc1, if_pos (hiff.mp hc1)]; exact ⟨0, by omega⟩
    · rw [if_neg hc1, if_neg (fun h => hc1 (hiff.mpr h))]; exact ⟨0, by omega⟩
  have hcj : 2 * (j : Int) ≤ card M (del X z) := by push_cast at hc; omega
  have hBt : ∀ t, t ≤ j → ∃ B : List ((Nat → Nat × Nat) × (W → Int)),
      (∀ b ∈ B, VP M (del X z) j b.1 ∧ LC M (del X z) j (G t) b.2) ∧
        ∀ v, Valid M (del X z) j v → ∀ w, m ∣ G t v w - ls B (fun b => DP j b.1 v * b.2 w) :=
    fun t ht => ih M (del X z) (G t) hcj (hG t ht)
  let Bt : Nat → List ((Nat → Nat × Nat) × (W → Int)) := fun t =>
    if h : t ≤ j then Classical.choose (hBt t h) else []
  have hBt' : ∀ t (h : t ≤ j), (∀ b ∈ Bt t, VP M (del X z) j b.1 ∧ LC M (del X z) j (G t) b.2) ∧
      ∀ v, Valid M (del X z) j v → ∀ w, m ∣ G t v w - ls (Bt t) (fun b => DP j b.1 v * b.2 w) := by
    intro t h
    have e : Bt t = Classical.choose (hBt t h) := by simp only [Bt, dif_pos h]
    rw [e]; exact Classical.choose_spec (hBt t h)
  -- (2) fresh points and the correction `eps`
  have hfr : ∀ Q : Nat → Nat × Nat, ∃ a, a < M ∧ del X z a = true ∧ ∀ s < j, a ≠ (Q s).1 ∧ a ≠ (Q s).2 :=
    fun Q => fresh M (del X z) j Q (by push_cast at hc; omega)
  let wq : (Nat → Nat × Nat) → Nat := fun Q => Classical.choose (hfr Q)
  have hwq : ∀ Q, wq Q < M ∧ del X z (wq Q) = true ∧ ∀ s < j, wq Q ≠ (Q s).1 ∧ wq Q ≠ (Q s).2 :=
    fun Q => Classical.choose_spec (hfr Q)
  let Beps : List ((Nat → Nat × Nat) × (W → Int)) :=
    (List.range (j + 1)).flatMap (fun t => (Bt t).map (fun b => (insP t (wq b.1, z) b.1, b.2)))
  have hVPe : ∀ b ∈ Beps, VP M X (j + 1) b.1 ∧ LC M X (j + 1) F b.2 := by
    intro b hb
    obtain ⟨t, ht, hb'⟩ := List.mem_flatMap.mp hb
    obtain ⟨b0, hb0, rfl⟩ := List.mem_map.mp hb'
    have ht' : t ≤ j := by have := List.mem_range.mp ht; omega
    obtain ⟨hV, hL⟩ := (hBt' t ht').1 b0 hb0
    obtain ⟨w1, w2, w3⟩ := hwq b0.1
    refine ⟨VP_insP ht' hV (fun a h => (del_iff X z a).mp h) hz hXz w1 (hdX _ w2) ((del_iff X z _).mp w2).2 w3, ?_⟩
    exact LC_tr hL (fun v hv => LC_ext (LC_smul (-1) (LC_F (valid_ins hv ht' hz hXz))) (fun w => by
      show -F (ins t z v) w = -1 * F (ins t z v) w; omega))
  let eps : (Nat → Nat) → W → Int := fun u w => ls Beps (fun b => DP (j + 1) b.1 u * b.2 w)
  let ψ : (Nat → Nat) → W → Int := fun u w => F u w - eps u w
  -- (3) `ψ` has vanishing slot sums on `X \ z`
  have hψ : KC m M (del X z) (j + 1) ψ := by
    intro u hu s hs w
    show m ∣ sig M (del X z) (j + 1) (fun u w => F u w - eps u w) u s w
    rw [sig_sub]
    have h0 := hK u (valid_mono hu hdX) s hs w
    have hF : sig M (del X z) (j + 1) F u s w = sig M X (j + 1) F u s w + G s (skip s u) w := by
      unfold sig
      rw [rsum_del M X z hz hXz]
      have hfz : Free (j + 1) u s z := fun r hr _ e => valid_del_ne hu r hr e
      rw [if_pos hfz]
      show _ - F (upd u s z) w = _ + -F (ins s z (skip s u)) w
      rw [upd_eq_ins]; omega
    have hE : sig M (del X z) (j + 1) eps u s w = ls (Bt s) (fun b => DP j b.1 (skip s u) * b.2 w) := by
      show sig M (del X z) (j + 1) (fun u w => ls Beps (fun b => DP (j + 1) b.1 u * b.2 w)) u s w = _
      rw [sig_lsDP M (del X z) (j + 1) Beps (fun P u => DP (j + 1) P u)]
      show ls ((List.range (j + 1)).flatMap _) _ = _
      rw [ls_flatMap]
      have per : ∀ t ∈ List.range (j + 1),
          ls ((Bt t).map (fun b => (insP t (wq b.1, z) b.1, b.2)))
            (fun b => sig M (del X z) (j + 1) (fun u (_ : W) => DP (j + 1) b.1 u) u s w * b.2 w) =
          if t = s then ls (Bt s) (fun b => DP j b.1 (skip s u) * b.2 w) else 0 := by
        intro t ht
        have ht' : t ≤ j := by have := List.mem_range.mp ht; omega
        rw [ls_map]
        by_cases hts : t = s
        · subst hts; rw [if_pos rfl]
          apply ls_congr; intro b hb
          obtain ⟨hV, _⟩ := (hBt' t ht').1 b hb
          obtain ⟨w1, w2, w3⟩ := hwq b.1
          congr 1
          unfold sig
          have e1 : ∀ a, (if del X z a = true ∧ Free (j + 1) u t a then DP (j + 1) (insP t (wq b.1, z) b.1) (upd u t a) else 0) =
              (if del X z a = true ∧ Free (j + 1) u t a then dl (wq b.1, z) a else 0) * DP j b.1 (skip t u) := by
            intro a
            rw [DP_insP j t ht', skip_upd]
            have : upd u t a t = a := by simp [upd]
            rw [this]; split
            · rfl
            · rw [Int.zero_mul]
          rw [rsum_congr M _ _ (fun a _ => e1 a), rsum_mulr', rsum_dl M _ _ w1 hz]
          have hzf : ¬ (del X z z = true ∧ Free (j + 1) u t z) := fun h => ((del_iff X z z).mp h.1).2 rfl
          rw [if_neg hzf]
          by_cases hf : del X z (wq b.1) = true ∧ Free (j + 1) u t (wq b.1)
          · rw [if_pos hf]; omega
          · rw [if_neg hf]
            have hnf : ¬ Free (j + 1) u t (wq b.1) := fun h => hf ⟨w2, h⟩
            unfold Free at hnf
            have : ∃ r, r < j + 1 ∧ r ≠ t ∧ u r = wq b.1 := by
              apply Classical.byContradiction; intro hn
              exact hnf (fun r hr hrt e => hn ⟨r, hr, hrt, e⟩)
            obtain ⟨r, hr, hrt, hur⟩ := this
            have hr' : (if r < t then r else r - 1) < j := by split <;> omega
            have hsk : skip t u (if r < t then r else r - 1) = wq b.1 := by
              unfold skip; by_cases a : r < t
              · simp [a, hur]
              · simp only [a, if_false]; rw [if_neg (by omega), show r - 1 + 1 = r by omega, hur]
            rw [DP_off j b.1 (skip t u) _ hr' (fun q hq => by rw [hsk]; exact w3 q hq)]; omega
        · rw [if_neg hts]
          apply ls_zero; intro b hb
          obtain ⟨hV, _⟩ := (hBt' t ht').1 b hb
          obtain ⟨w1, w2, w3⟩ := hwq b.1
          have hVP := VP_insP ht' hV (fun a h => (del_iff X z a).mp h) hz hXz w1 (hdX _ w2) ((del_iff X z _).mp w2).2 w3
          have hsl : insP t (wq b.1, z) b.1 s = b.1 (if s < t then s else s - 1) := by
            unfold insP; by_cases a : s < t
            · simp [a]
            · simp [a, Ne.symm hts]
          have hr : (if s < t then s else s - 1) < j := by split <;> omega
          obtain ⟨p1, p2, p3, p4, p5⟩ := hV.1 _ hr
          rw [sig_DP M (del X z) j _ u s w (by omega) hVP.2 (by rw [hsl]; exact p5) (by rw [hsl]; exact p1)
            (by rw [hsl]; exact p3) (by rw [hsl]; exact p2) (by rw [hsl]; exact p4), Int.zero_mul]
      rw [ls_congr _ _ _ per, ls_range, rsum_pick' (j + 1) s _ hs]
    rw [hF, hE]
    have := Int.dvd_add h0 ((hBt' s (by omega)).2 (skip s u) (valid_skip hu (by omega)) w)
    rwa [show ∀ a b c : Int, a + b - c = a + (b - c) by intros; omega]
  -- slices of `ψ` along slot `0`
  let ψa : Nat → (Nat → Nat) → W → Int := fun a v w => ψ (cns a v) w
  have hψa : ∀ a, a < M → del X z a = true → KC m M (del (del X z) a) j (ψa a) := by
    intro a ha hXa v hv s hs w
    have h0 := hψ (cns a v) (valid_cns hv ha hXa) (s + 1) (by omega) w
    unfold sig at h0 ⊢
    refine (Int.dvd_iff_dvd_of_dvd_sub ?_).mpr h0
    apply rsum_dvd_congr; intro x _
    refine ⟨0, ?_⟩; rw [Int.mul_zero, Int.sub_eq_zero]
    show (if _ then ψ (cns a (upd v s x)) w else 0) = _
    rw [cns_upd]
    have hiff : (del (del X z) a x = true ∧ Free j v s x) ↔ (del X z x = true ∧ Free (j + 1) (cns a v) (s + 1) x) := by
      rw [free_cns hs, del_iff (del X z) a]
      exact ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩
    by_cases hc1 : del (del X z) a x = true ∧ Free j v s x
    · rw [if_pos hc1, if_pos (hiff.mp hc1)]
    · rw [if_neg hc1, if_neg (fun h => hc1 (hiff.mpr h))]
  have hBa : ∀ a, a < M ∧ del X z a = true → ∃ B : List ((Nat → Nat × Nat) × (W → Int)),
      (∀ b ∈ B, VP M (del (del X z) a) j b.1 ∧ LC M (del (del X z) a) j (ψa a) b.2) ∧
        ∀ v, Valid M (del (del X z) a) j v → ∀ w, m ∣ ψa a v w - ls B (fun b => DP j b.1 v * b.2 w) := by
    intro a ha
    have : card M (del (del X z) a) = card M (del X z) - 1 := card_del M (del X z) a ha.1 ha.2
    exact ih M (del (del X z) a) (ψa a) (by push_cast at hc; omega) (hψa a ha.1 ha.2)
  let Ba : Nat → List ((Nat → Nat × Nat) × (W → Int)) := fun a =>
    if h : a < M ∧ del X z a = true then Classical.choose (hBa a h) else []
  have hBa' : ∀ a (h : a < M ∧ del X z a = true),
      (∀ b ∈ Ba a, VP M (del (del X z) a) j b.1 ∧ LC M (del (del X z) a) j (ψa a) b.2) ∧
        ∀ v, Valid M (del (del X z) a) j v → ∀ w, m ∣ ψa a v w - ls (Ba a) (fun b => DP j b.1 v * b.2 w) := by
    intro a h
    have e : Ba a = Classical.choose (hBa a h) := by simp only [Ba, dif_pos h]
    rw [e]; exact Classical.choose_spec (hBa a h)
  let Bpsi : List ((Nat → Nat × Nat) × (W → Int)) :=
    ((List.range M).filter (del X z)).flatMap (fun a => (Ba a).map (fun b => (insP 0 (a, z) b.1, b.2)))
  have hVPp : ∀ b ∈ Bpsi, VP M X (j + 1) b.1 ∧ LC M X (j + 1) F b.2 := by
    intro b hb
    obtain ⟨a, ha, hb'⟩ := List.mem_flatMap.mp hb
    obtain ⟨b0, hb0, rfl⟩ := List.mem_map.mp hb'
    have ha' : a < M ∧ del X z a = true := by
      have := List.mem_filter.mp ha; exact ⟨List.mem_range.mp this.1, this.2⟩
    obtain ⟨hV, hL⟩ := (hBa' a ha').1 b0 hb0
    have hfa : ∀ s < j, a ≠ (b0.1 s).1 ∧ a ≠ (b0.1 s).2 := by
      intro s hs; obtain ⟨_, q2, _, q4, _⟩ := hV.1 s hs
      exact ⟨fun e => ((del_iff _ a _).mp q2).2 e.symm, fun e => ((del_iff _ a _).mp q4).2 e.symm⟩
    refine ⟨VP_insP (by omega) hV (fun x h => by
        have h1 := (del_iff _ a x).mp h; have h2 := (del_iff X z x).mp h1.1; exact ⟨h2.1, h2.2⟩)
      hz hXz ha'.1 (hdX _ ha'.2) ((del_iff X z _).mp ha'.2).2 hfa, ?_⟩
    apply LC_tr hL
    intro v hv
    have hu := valid_cns hv ha'.1 ha'.2
    show LC M X (j + 1) F (fun w => F (cns a v) w - ls Beps (fun b => DP (j + 1) b.1 (cns a v) * b.2 w))
    apply LC_sub (LC_F (valid_mono hu hdX))
    apply LC_ls Beps (fun b w => DP (j + 1) b.1 (cns a v) * b.2 w)
    intro b hb; exact LC_smul _ (hVPe b hb).2
  have hpsi : ∀ u, Valid M (del X z) (j + 1) u → ∀ w, m ∣ ψ u w - ls Bpsi (fun b => DP (j + 1) b.1 u * b.2 w) := by
    intro u hu w
    show m ∣ _ - ls (((List.range M).filter (del X z)).flatMap _) _
    rw [ls_flatMap, ls_filter, ls_range]
    have hu0 : u 0 < M ∧ del X z (u 0) = true := hu.1 0 (by omega)
    have per : ∀ a < M, (if del X z a = true then ls ((Ba a).map (fun b => (insP 0 (a, z) b.1, b.2)))
        (fun b => DP (j + 1) b.1 u * b.2 w) else 0) = if a = u 0 then ls (Ba (u 0)) (fun b => DP j b.1 (skip 0 u) * b.2 w) else 0 := by
      intro a _
      have hz0 : u 0 ≠ z := valid_del_ne hu 0 (by omega)
      by_cases hau : a = u 0
      · subst hau; rw [if_pos hu0.2, if_pos rfl, ls_map]
        apply ls_congr; intro b _
        rw [DP_insP j 0 (by omega)]
        simp [dl, hz0]
      · rw [if_neg hau]; split
        · rw [ls_map]; apply ls_zero; intro b _
          show DP (j + 1) (insP 0 (a, z) b.1) u * b.2 w = 0
          rw [DP_insP j 0 (by omega)]
          simp [dl, hz0, Ne.symm hau]
        · rfl
    rw [rsum_congr M _ _ per, rsum_pick' M (u 0) _ hu0.1]
    have := (hBa' (u 0) hu0).2 (skip 0 u) (valid_tail hu) w
    have e : ψa (u 0) (skip 0 u) w = ψ u w := by show ψ (cns (u 0) (skip 0 u)) w = ψ u w; rw [cns_skip]
    rwa [e] at this
  -- (4) assemble
  refine ⟨Beps ++ Bpsi, fun b hb => ?_, ?_⟩
  · rcases List.mem_append.mp hb with h | h
    · exact hVPe b h
    · exact hVPp b h
  · have hVP : ∀ b ∈ Beps ++ Bpsi, VP M X (j + 1) b.1 := fun b hb => by
      rcases List.mem_append.mp hb with h | h
      · exact (hVPe b h).1
      · exact (hVPp b h).1
    let H : (Nat → Nat) → W → Int := fun u w => F u w - ls (Beps ++ Bpsi) (fun b => DP (j + 1) b.1 u * b.2 w)
    have hHK : KC m M X (j + 1) H := by
      intro u hu t ht w
      show m ∣ sig M X (j + 1) (fun u w => F u w - ls (Beps ++ Bpsi) (fun b => DP (j + 1) b.1 u * b.2 w)) u t w
      rw [sig_sub, sig_lsDP M X (j + 1) (Beps ++ Bpsi) (fun P u => DP (j + 1) P u)]
      rw [ls_zero]
      · rw [Int.sub_zero]; exact hK u hu t ht w
      intro b hb
      obtain ⟨p1, p2, p3, p4, p5⟩ := (hVP b hb).1 t ht
      rw [sig_DP M X j b.1 u t w (by omega) (hVP b hb).2 p5 p1 p3 p2 p4, Int.zero_mul]
    have h0 : ∀ u, Valid M (del X z) (j + 1) u → ∀ w, m ∣ H u w := by
      intro u hu w
      show m ∣ F u w - ls (Beps ++ Bpsi) (fun b => DP (j + 1) b.1 u * b.2 w)
      rw [ls_append]
      have := hpsi u hu w
      show m ∣ F u w - (eps u w + _)
      rwa [show ∀ a b c : Int, a - (b + c) = a - b - c by intros; omega]
    intro u hu w
    exact zero_of_del m M X j z hz hXz H hHK h0 u hu w

/-- **Lemma K.** -/
theorem lemK (m : Int) (j : Nat) : LK W m j := by
  induction j with
  | zero => exact lemK_zero m
  | succ j ih => exact lemK_step m j ih

end Programme.«20261027-0607-proof-complexity».LemK

#print axioms Programme.«20261027-0607-proof-complexity».LemK.lemK
