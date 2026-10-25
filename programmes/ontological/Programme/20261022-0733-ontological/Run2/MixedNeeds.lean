import Programme.«20261022-0733-ontological».Run2.MixedNoRigidity
import Programme.«20261022-0733-ontological».Run2.TwoNeedsAx2a

/-! # The mixed-regime equivalence (K29) needs `Ax2a` and `Ax4P` as well as `Ax3`

When every entity is actual at every world, the mixed (Anderson) essences, necessary existence and
`Ax4P` coincide with the actualist ones (`E2_eq`, `E3_eq`, `ax4P_iff`).  The two witnesses of K28
have that property, so they transfer:

* `ax2a_needed_mixed`: `TwoNeedsAx2a.tm` (FM carriers, only `⊤` positive) satisfies mixed `Ax3`
  (variant 2 and 3′), `Ax4P`, `Ax2b`, `Ax1GenTwo`, with the mixed `E` admitted, but not `Ax1Gen`
  nor `Ax2a`.
* `ax4_needed_mixed`: `TwoNeedsAx2a.anti` (full two-world S5, `P φ w :↔ ¬ φ w`) satisfies `Ax2a`,
  mixed `Ax3` (variant 2 and 3′), `Ax1GenTwo`, but not `Ax1Gen` nor `Ax4P`.

With `MixedNoRigidity.ax3_needed` each of `Ax2a`, mixed `Ax3`, `Ax4P` is needed for
`MixedNoRigidity.equivalence_v2` / `equivalence_v3`. -/

namespace Programme.«20261022-0733-ontological».Run2.MixedNeeds

open Programme.«20261022-0733-ontological».Run2.TwoClosed
open Programme.«20261022-0733-ontological».Run2.LGeneralFull (LGenF)
open Programme.«20261022-0733-ontological».Run2.TwoNeedsAx2a (tm anti)

variable {W D : Type} {M : Model W D}

theorem pInc_iff (hall : ∀ y w, M.act y w) (φ ψ : D → W → Prop) (w : W) :
    TwoClosedMixed.PIncP M φ ψ w ↔ PInc M φ ψ w :=
  ⟨fun h v hv y _ hy => h v hv y hy, fun h v hv y hy => h v hv y (hall y v) hy⟩

theorem E2_eq (hall : ∀ y w, M.act y w) : TwoClosedMixed.E2 M = E M := by
  funext x w
  apply propext
  unfold TwoClosedMixed.E2 TwoClosedMixed.NE E
  apply forall_congr'; intro φ; apply forall_congr'; intro _
  apply imp_congr_left
  unfold TwoClosedMixed.Ess2 Ess
  exact and_congr Iff.rfl (forall_congr' fun ψ => forall_congr' fun _ =>
    forall_congr' fun _ => pInc_iff hall φ ψ w)

theorem E3_eq (hall : ∀ y w, M.act y w) : TwoClosedMixed.E3 M = TwoClosed.E3 M := by
  funext x w
  apply propext
  unfold TwoClosedMixed.E3 TwoClosedMixed.NE TwoClosed.E3
  apply forall_congr'; intro φ; apply forall_congr'; intro _
  apply imp_congr_left
  unfold TwoClosedMixed.Ess3 TwoClosed.Ess3
  exact forall_congr' fun ψ => forall_congr' fun _ => forall_congr' fun _ =>
    forall_congr' fun v => forall_congr' fun _ => and_congr Iff.rfl
      ⟨fun h y _ hy => h y hy, fun h y hy => h y (hall y v) hy⟩

theorem ax4P_iff (hall : ∀ y w, M.act y w) : TwoClosedMixed.Ax4P M ↔ Ax4 M :=
  ⟨fun h φ ψ hφ hψ w hp hi => h φ ψ hφ hψ w hp ((pInc_iff hall φ ψ w).2 hi),
   fun h φ ψ hφ hψ w hp hi => h φ ψ hφ hψ w hp ((pInc_iff hall φ ψ w).1 hi)⟩

/-! ## `Ax2a` is needed (mixed) -/

theorem hall_tm : ∀ (y : Unit) w, tm.act y w := fun _ _ => trivial

/-- **`Ax2a` is needed in the mixed regime.** -/
theorem ax2a_needed_mixed :
    LGenF tm ∧ Closed tm ∧ tm.AT (TwoClosedMixed.E2 tm) ∧ tm.AT (TwoClosedMixed.E3 tm) ∧
      Ax2b tm ∧ (∀ w, tm.P (TwoClosedMixed.E2 tm) w) ∧ (∀ w, tm.P (TwoClosedMixed.E3 tm) w) ∧
      TwoClosedMixed.Ax4P tm ∧ Ax1GenTwo tm ∧ ¬ Ax1Gen tm ∧ ¬ Ax2a tm := by
  obtain ⟨hL, hC, hE, hE3, h2b, h3, h3v, h4, -, -, -, -, hT, hn, hn2a, -⟩ :=
    TwoNeedsAx2a.ax2a_needed
  rw [E2_eq hall_tm, E3_eq hall_tm]
  exact ⟨hL, hC, hE, hE3, h2b, h3, h3v, (ax4P_iff hall_tm).2 h4, hT, hn, hn2a⟩

/-! ## `Ax4P` is needed (mixed) -/

theorem hall_anti : ∀ (y : Unit) w, anti.act y w := fun _ _ => trivial

/-- **`Ax4P` is needed in the mixed regime.** -/
theorem ax4_needed_mixed :
    LGenF anti ∧ Closed anti ∧ Ax2a anti ∧ (∀ w, anti.P (TwoClosedMixed.E2 anti) w) ∧
      (∀ w, anti.P (TwoClosedMixed.E3 anti) w) ∧ Ax1GenTwo anti ∧ ¬ Ax1Gen anti ∧
      ¬ TwoClosedMixed.Ax4P anti := by
  obtain ⟨hL, hC, h2a, h3, h3v, hT, hn, hn4⟩ := TwoNeedsAx2a.ax4_needed
  rw [E2_eq hall_anti, E3_eq hall_anti, ax4P_iff hall_anti]
  exact ⟨hL, hC, h2a, h3, h3v, hT, hn, hn4⟩

end Programme.«20261022-0733-ontological».Run2.MixedNeeds

#print axioms Programme.«20261022-0733-ontological».Run2.MixedNeeds.ax2a_needed_mixed
#print axioms Programme.«20261022-0733-ontological».Run2.MixedNeeds.ax4_needed_mixed
