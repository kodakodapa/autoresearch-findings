import Programme.«20261022-0733-ontological».Run2.AtlasFull
import Programme.«20261022-0733-ontological».Run2.TwoNeedsAx2a
-- Core proof copied from agents/th/lean/Programme/Th/MCFromTwo.lean (author: th, P278);
-- namespace changed, minimality theorem `mc_minimal` added (pr).
/-! # Modal collapse from `Ax2a`, `Ax2b` and `Ax1GenTwo` alone

Over pr's `Closed` interface (`Run2.TwoClosed`), on any frame and actuality, with nonempty
entities: `Ax2a`, `Ax2b` and `Ax1GenTwo` give modal collapse for admitted propositions.  No `Ax3`,
no `Ax4`, no `E`, no `Ax1`.  (K1's `mc` uses `Ax3` and `Ax4` through `gex`.)

Suppose `X w`, `R w v`, `¬X v`, `L = λz.X`.
* `P ⊤` at `w`: some `ψ ∈ {L, ¬L}` is positive at `w`, `ψ ≠ ⊤`.  `Φ₁ = X ? {⊤, ψ} : {⊥}` has
  conjunction `χ₁ = λz u. X u ∧ ψ z u`, positive at `w`, hence at `v` (`Ax2b`).  At `v`,
  `Φ₂ = ¬X ? {⊤, ψ} : {⊥}` gives `χ₂ = λz u. ¬X u ∧ ψ z u`.  Then `{χ₁, χ₂}` has conjunction `⊥`,
  so `P ⊥ v` against `P ⊤ v`.
* `P ⊥` at `w`: `X ? {⊥, ψ} : {⊤}` gives `P ¬L` at `w`, hence at `v`; at `v`,
  `¬X ? {⊥, ¬L} : {⊤}` gives `P L`, against `Ax2a`. -/

namespace Programme.«20261022-0733-ontological».Run2.MCFromTwo

open Programme.«20261022-0733-ontological».Run2.TwoClosed Programme.«20261022-0733-ontological».Run2.LGeneralFull

variable {W D : Type} {M : Model W D}

theorem negTop : neg (top : D → W → Prop) = bot := by
  funext x w; simp [neg, top, bot]

/-- Guarded two-member instance of `Ax1GenTwo`: on `p`-worlds the collection is `{ψ₁, ψ₂}`, elsewhere
`{q}`; any admitted `φ` that is the resulting conjunction is positive at a `p`-world `w`. -/
theorem guarded (C : Closed M) (hT : Ax1GenTwo M) {p : W → Prop} (hp : M.AS p)
    {ψ₁ ψ₂ q φ : D → W → Prop} (h1 : M.AT ψ₁) (h2 : M.AT ψ₂) (hq : M.AT q) (hφ : M.AT φ)
    (hne : ψ₁ ≠ ψ₂) {w : W} (hpw : p w) (P1 : M.P ψ₁ w) (P2 : M.P ψ₂ w)
    (hdef : ∀ z u, φ z u ↔ ((p u ∧ ψ₁ z u ∧ ψ₂ z u) ∨ (¬ p u ∧ q z u))) : M.P φ w := by
  let Φ : (D → W → Prop) → W → Prop := fun ψ u =>
    (p u ∧ (ψ = ψ₁ ∨ ψ = ψ₂)) ∨ (¬ p u ∧ ψ = q)
  have hΦ : M.AH Φ :=
    C.union _ _ (C.guard _ _ hp (C.union _ _ (C.single _ h1) (C.single _ h2)))
      (C.guard _ _ (C.negS _ hp) (C.single _ hq))
  refine hT Φ φ hΦ hφ w ⟨ψ₁, ψ₂, h1, h2, Or.inl ⟨hpw, Or.inl rfl⟩, Or.inl ⟨hpw, Or.inr rfl⟩, hne⟩
    ?_ ?_
  · intro ψ _ hψ
    rcases hψ with ⟨_, rfl | rfl⟩ | ⟨hn, _⟩
    · exact P1
    · exact P2
    · exact absurd hpw hn
  · intro u _ z _
    rw [hdef]
    by_cases hpu : p u
    · constructor
      · rintro (⟨_, a, b⟩ | ⟨hn, _⟩)
        · rintro ψ _ (⟨_, rfl | rfl⟩ | ⟨hn, _⟩)
          · exact a
          · exact b
          · exact absurd hpu hn
        · exact absurd hpu hn
      · intro hall
        exact Or.inl ⟨hpu, hall _ h1 (Or.inl ⟨hpu, Or.inl rfl⟩),
          hall _ h2 (Or.inl ⟨hpu, Or.inr rfl⟩)⟩
    · constructor
      · rintro (⟨hp', _⟩ | ⟨_, hqz⟩)
        · exact absurd hp' hpu
        · rintro ψ _ (⟨hp', _⟩ | ⟨_, rfl⟩)
          · exact absurd hp' hpu
          · exact hqz
      · intro hall
        exact Or.inr ⟨hpu, hall _ hq (Or.inr ⟨hpu, rfl⟩)⟩

/-- **Modal collapse from `Ax2a`, `Ax2b`, `Ax1GenTwo`**, any frame, no `Ax3`/`Ax4`. -/
theorem mc_of_two [Nonempty D] (C : Closed M) (h2a : Ax2a M) (h2b : Ax2b M)
    (hT : Ax1GenTwo M) : MC M := by
  intro X hX w hXw v hv
  refine Classical.byContradiction fun hXv => ?_
  obtain ⟨d⟩ := (inferInstance : Nonempty D)
  have nX : M.AS (fun u => ¬ X u) := C.negS _ hX
  let L : D → W → Prop := fun _ => X
  have hL : M.AT L := C.lift _ hX
  have hnL : M.AT (neg L) := C.neg _ hL
  have L_ne_top : L ≠ top := fun e => hXv (by have := congrFun (congrFun e d) v; simp [L, top] at this; exact this)
  have nL_ne_top : neg L ≠ top := fun e => by
    have := congrFun (congrFun e d) w; simp [L, neg, top] at this; exact this hXw
  have L_ne_bot : L ≠ bot := fun e => by
    have := congrFun (congrFun e d) w; simp [L, bot] at this; exact this hXw
  have nL_ne_bot : neg L ≠ bot := fun e => hXv (by
    have := congrFun (congrFun e d) v; simp [L, neg, bot] at this; exact this)
  rcases (h2a _ C.top w).1 with hTop | hBot
  · -- `P ⊤` at `w`
    have hTopv : M.P top v := h2b _ C.top w hTop v hv
    have hnb : ¬ M.P bot v := fun hb => (h2a _ C.top v).2 ⟨hTopv, by rw [negTop]; exact hb⟩
    obtain ⟨ψ, hψ, hPψ, hψtop⟩ : ∃ ψ, M.AT ψ ∧ M.P ψ w ∧ ψ ≠ top := by
      rcases (h2a _ hL w).1 with h | h
      · exact ⟨L, hL, h, L_ne_top⟩
      · exact ⟨neg L, hnL, h, nL_ne_top⟩
    have hPψv : M.P ψ v := h2b _ hψ w hPψ v hv
    let χ₁ : D → W → Prop := fun z u => X u ∧ ψ z u
    let χ₂ : D → W → Prop := fun z u => ¬ X u ∧ ψ z u
    have hχ₁ : M.AT χ₁ := C.conj _ _ hL hψ
    have hχ₂ : M.AT χ₂ := C.conj _ _ hnL hψ
    have P1 : M.P χ₁ w := guarded C hT hX C.top hψ C.bot hχ₁ (Ne.symm hψtop) hXw hTop hPψ
      (fun z u => by
        by_cases h : X u <;> simp [χ₁, top, bot, h])
    have P2 : M.P χ₂ v := guarded C hT nX C.top hψ C.bot hχ₂ (Ne.symm hψtop) hXv hTopv hPψv
      (fun z u => by
        by_cases h : X u <;> simp [χ₂, top, bot, h])
    have P1v : M.P χ₁ v := h2b _ hχ₁ w P1 v hv
    -- `ψ` is not `⊥`, so `χ₁ ≠ χ₂`
    have hψbot : ψ ≠ bot := fun e => hnb (e ▸ hPψv)
    obtain ⟨z, u, hzu⟩ : ∃ z u, ψ z u := by
      refine Classical.byContradiction fun hn => hψbot ?_
      funext z u; simp only [bot, eq_iff_iff, iff_false]; exact fun h => hn ⟨z, u, h⟩
    have hne : χ₁ ≠ χ₂ := fun e => by
      have := congrFun (congrFun e z) u
      by_cases h : X u <;> simp [χ₁, χ₂, h, hzu] at this
    -- `{χ₁, χ₂}` has conjunction `⊥` everywhere
    let Φ : (D → W → Prop) → W → Prop := fun χ _ => χ = χ₁ ∨ χ = χ₂
    have hΦ : M.AH Φ := C.union _ _ (C.single _ hχ₁) (C.single _ hχ₂)
    have Pb : M.P bot v := hT Φ bot hΦ C.bot v
      ⟨χ₁, χ₂, hχ₁, hχ₂, Or.inl rfl, Or.inr rfl, hne⟩
      (fun χ _ hχ => by rcases hχ with rfl | rfl; exact P1v; exact P2)
      (fun u' _ z' _ => by
        simp only [bot, false_iff]
        intro hall
        have a := hall χ₁ hχ₁ (Or.inl rfl)
        have b := hall χ₂ hχ₂ (Or.inr rfl)
        exact b.1 a.1)
    exact hnb Pb
  · -- `P ⊥` at `w`
    rw [negTop] at hBot
    have hBotv : M.P bot v := h2b _ C.bot w hBot v hv
    obtain ⟨ψ, hψ, hPψ, hψbot⟩ : ∃ ψ, M.AT ψ ∧ M.P ψ w ∧ ψ ≠ bot := by
      rcases (h2a _ hL w).1 with h | h
      · exact ⟨L, hL, h, L_ne_bot⟩
      · exact ⟨neg L, hnL, h, nL_ne_bot⟩
    have Pn : M.P (neg L) w := guarded C hT hX C.bot hψ C.top hnL (Ne.symm hψbot) hXw hBot hPψ
      (fun z u => by by_cases h : X u <;> simp [L, neg, top, bot, h])
    have Pnv : M.P (neg L) v := h2b _ hnL w Pn v hv
    have PL : M.P L v := guarded C hT nX C.bot hnL C.top hL (Ne.symm nL_ne_bot) hXv hBotv Pnv
      (fun z u => by by_cases h : X u <;> simp [L, neg, top, bot, h])
    exact (h2a _ hL v).2 ⟨PL, Pnv⟩


/-! ## Each of `Ax2a`, `Ax2b`, `Ax1GenTwo` is needed (witnesses K8 `fm`, K28 `tm`, K19 `rx`) -/

theorem mc_minimal :
    -- without `Ax2b`
    (LGenF FM.fm ∧ Closed FM.fm ∧ Ax2a FM.fm ∧ Ax1GenTwo FM.fm ∧ ¬ Ax2b FM.fm ∧ ¬ MC FM.fm) ∧
    -- without `Ax2a`
    (LGenF TwoNeedsAx2a.tm ∧ Closed TwoNeedsAx2a.tm ∧ Ax2b TwoNeedsAx2a.tm ∧
      Ax1GenTwo TwoNeedsAx2a.tm ∧ ¬ Ax2a TwoNeedsAx2a.tm ∧ ¬ MC TwoNeedsAx2a.tm) ∧
    -- without `Ax1GenTwo`
    (LGenF RigidExit.rx ∧ Closed RigidExit.rx ∧ Ax2a RigidExit.rx ∧ Ax2b RigidExit.rx ∧
      ¬ Ax1GenTwo RigidExit.rx ∧ ¬ MC RigidExit.rx) := by
  obtain ⟨l8, h2a, -, -, -, -, -, -, -, h2, -, -, -, n2b, nmc⟩ := AtlasFull.k8_full
  obtain ⟨lt, ct, -, -, t2b, -, -, -, -, -, -, -, t2, -, t2a, tmc⟩ := TwoNeedsAx2a.ax2a_needed
  obtain ⟨rl, -, -, r2a, r2b, -, -, -, rmc, -, -, r2⟩ := RigidExit.rigid_exit
  exact ⟨⟨l8, FM.closed_fm, h2a, h2, n2b, nmc⟩, ⟨lt, ct, t2b, t2, t2a, tmc⟩,
    ⟨LGeneralFullInst.Rx.lgenF_rx, LGeneral.closed_of_lgeneral rl, r2a, r2b, r2, rmc⟩⟩

end Programme.«20261022-0733-ontological».Run2.MCFromTwo

#print axioms Programme.«20261022-0733-ontological».Run2.MCFromTwo.mc_of_two
#print axioms Programme.«20261022-0733-ontological».Run2.MCFromTwo.mc_minimal
