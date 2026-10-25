import Programme.«20261022-0733-ontological».Run2.TwoClosed

/-! # `Ax1GenBox` is idle given `L` and plain `Ax4`, in closed models

th's conjecture E3 (forward half), carried over K1's Henkin-style `Model`: if every member of
`Φ` is positive at every successor, a God-like being at a successor has every member there, so
the conjunction includes `G` on actual beings, and plain `Ax4` from `P G` gives `P φ`.
Hence `L` with plain `Ax4` (K1's `Ax4`, variants 2 and 3′) implies `Ax1GenBox`, and so
`Ax1GenBoxTwo`.  Only `G` admitted is used from the closure interface. -/

namespace Programme.«20261022-0733-ontological».Run2.BoxIdle

open Programme.«20261022-0733-ontological».Run2.TwoClosed

variable {W D : Type} (M : Model W D)

/-- `□ PosProps Φ`, as in the library's `Ax1GenBox`. -/
def BoxPos (Φ : (D → W → Prop) → W → Prop) (w : W) : Prop :=
  ∀ v, M.R w v → PosProps M Φ v

/-- `Ax1GenBox` of `OpenQuestions/Ax1GenBoxVariant2.lean` over admitted carriers. -/
def Ax1GenBox : Prop := ∀ Φ φ, M.AH Φ → M.AT φ → ∀ w,
  PosProps M Φ w → BoxPos M Φ w → ConjOf M φ Φ w → M.P φ w

/-- `Ax1GenBoxTwo` of `OpenQuestions/Ax1GenTwoVariant3Plain.lean` over admitted carriers. -/
def Ax1GenBoxTwo : Prop := ∀ Φ φ, M.AH Φ → M.AT φ → ∀ w,
  TwoMembers M Φ w → PosProps M Φ w → BoxPos M Φ w → ConjOf M φ Φ w → M.P φ w

/-- `L`: God-likeness is positive everywhere. -/
def L : Prop := ∀ w, M.P (G M) w

variable {M}

theorem box_of_L (hG : M.AT (G M)) (h4 : Ax4 M) (hL : L M) : Ax1GenBox M :=
  fun Φ φ _ hφ w _ box cj =>
    h4 (G M) φ hG hφ w (hL w) fun v hv y hy hGy =>
      (cj v hv y hy).2 fun ψ hA hm => hGy ψ hA (box v hv ψ hA hm)

theorem boxTwo_of_box (h : Ax1GenBox M) : Ax1GenBoxTwo M :=
  fun Φ φ hΦ hφ w _ pos box cj => h Φ φ hΦ hφ w pos box cj

theorem boxTwo_of_L (hG : M.AT (G M)) (h4 : Ax4 M) (hL : L M) : Ax1GenBoxTwo M :=
  boxTwo_of_box (box_of_L hG h4 hL)

/-- `L_BoxTwo`: the converse, from `Ax2a` and positive `⊤` (which variants 2 and 3′ derive
from `Ax3` and `Ax4`: `pTop_v2`, `pTop_v3`). -/
theorem L_of_boxTwo [Nonempty D] (C : Closed M) (h2a : Ax2a M) (h3 : ∀ w, M.P top w)
    (h : Ax1GenBoxTwo M) : L M := fun w => by
  by_cases ht : TwoMembers M M.P w
  · exact h M.P (G M) C.pos C.god w ht (fun _ _ hψ => hψ) (fun _ _ _ _ hψ => hψ)
      (fun _ _ _ _ => Iff.rfl)
  · have one : ∀ φ, M.AT φ → M.P φ w → φ = top := fun φ hA hφ =>
      Classical.byContradiction fun hne => ht ⟨φ, top, hA, C.top, hφ, h3 w, hne⟩
    have Gw : ∀ x, G M x w := fun x φ hA hφ => by rw [one φ hA hφ]; trivial
    rcases (h2a (G M) C.god w).1 with hG | hnG
    · exact hG
    · have e := one _ (C.neg _ C.god) hnG
      have x : D := Classical.ofNonempty
      have := congrFun (congrFun e x) w
      exact absurd (Gw x) (by simpa [neg, top] using this)

/-- **Variant 3′ (and 2) over closed models**: with `Ax2a`, `Ax3` (via positive `⊤`) and plain
`Ax4`, `Ax1GenBoxTwo` holds iff `L` does, and then `Ax1GenBox` holds too. -/
theorem boxTwo_iff_L [Nonempty D] (C : Closed M) (h2a : Ax2a M) (h3 : ∀ w, M.P top w)
    (h4 : Ax4 M) : Ax1GenBoxTwo M ↔ L M :=
  ⟨L_of_boxTwo C h2a h3, boxTwo_of_L C.god h4⟩

theorem boxTwo_iff_L_v3 [Nonempty D] (C : Closed M) (hE : M.AT (E3 M)) (h2a : Ax2a M)
    (h3 : Ax3v3 M) (h4 : Ax4 M) : Ax1GenBoxTwo M ↔ L M :=
  boxTwo_iff_L C h2a (pTop_v3 hE C h3 h4) h4

theorem boxTwo_iff_L_v2 [Nonempty D] (C : Closed M) (hE : M.AT (E M)) (h2a : Ax2a M)
    (h3 : Ax3 M) (h4 : Ax4 M) : Ax1GenBoxTwo M ↔ L M :=
  boxTwo_iff_L C h2a (pTop_v2 hE C h3 h4) h4

end Programme.«20261022-0733-ontological».Run2.BoxIdle

#print axioms Programme.«20261022-0733-ontological».Run2.BoxIdle.box_of_L
#print axioms Programme.«20261022-0733-ontological».Run2.BoxIdle.boxTwo_of_L
#print axioms Programme.«20261022-0733-ontological».Run2.BoxIdle.boxTwo_iff_L_v3
#print axioms Programme.«20261022-0733-ontological».Run2.BoxIdle.boxTwo_iff_L_v2
