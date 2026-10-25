import Programme.«20261022-0733-ontological».Run2.MCFromTwo

/-! # God at every world from `Ax2a`, `Ax4`, `Ax1GenTwo` alone (no `Ax3`, no `Ax2b`)

K1's `gex` (pr, `Run2.TwoClosed`) assumes `⊤` positive, `Ax2a`, `Ax4`; K28's `pTop_of_2a4` derives
`⊤` positive from `Ax2a` and `Ax4`.  So over `Closed`, on any frame and actuality, `Ax2a`, `Ax4`,
`Ax1GenTwo` give `∃ᴱ G` at every world: K1's `Ax3` is used nowhere in K1 (equivalence: K28; MC:
`mc_of_two`; existence: here).

Each hypothesis is needed (all witnesses `LGenF` and `Closed`, every world godless):
* no `Ax2a`: `Minimal.noAx2a` (full two-world S5, everything positive);
* no `Ax4`: K28's `anti` (full two-world S5, `P φ w :↔ ¬ φ w`);
* no `Ax1GenTwo`: K19's `rx`. -/

namespace Programme.«20261022-0733-ontological».Run2.GexTwo

open Programme.«20261022-0733-ontological».Run2 Programme.«20261022-0733-ontological».Run2.TwoClosed
open Programme.«20261022-0733-ontological».Run2.LGeneralFull (LGenF)

variable {W D : Type} {M : Model W D}

/-- **`∃ᴱ G` at every world** from `Closed`, `Ax2a`, `Ax4`, `Ax1GenTwo`, any frame. -/
theorem gex_2a4 [Nonempty D] (C : Closed M) (h2a : Ax2a M) (h4 : Ax4 M) (hT : Ax1GenTwo M)
    (w : W) : ExG M w :=
  gex C h2a (TwoNeedsAx2a.pTop_of_2a4 C h2a h4) h4 hT w

/-- K1 without `Ax3`: existence and admitted modal collapse. -/
theorem k1_noAx3 [Nonempty D] (C : Closed M) (h2a : Ax2a M) (h2b : Ax2b M) (h4 : Ax4 M)
    (hT : Ax1GenTwo M) : (∀ w, ExG M w) ∧ MC M ∧ Ax1Gen M :=
  ⟨gex_2a4 C h2a h4 hT, MCFromTwo.mc_of_two C h2a h2b hT,
    (TwoNeedsAx2a.equivalence_2a4 C h2a h4).1 hT⟩

theorem closed_noAx2a : Closed Minimal.noAx2a where
  top := trivial
  bot := trivial
  neg := fun _ _ => trivial
  conj := fun _ _ _ _ => trivial
  lift := fun _ _ => trivial
  negS := fun _ _ => trivial
  god := trivial
  exG := trivial
  pos := trivial
  single := fun _ _ => trivial
  union := fun _ _ _ _ => trivial
  guard := fun _ _ _ _ => trivial
  atMost := fun _ _ _ _ => trivial

theorem two_noAx2a : Ax1GenTwo Minimal.noAx2a := fun _ _ _ _ _ _ _ _ => trivial

theorem anti_godless (w : Bool) : ¬ ExG TwoNeedsAx2a.anti w := fun ⟨_, _, hg⟩ =>
  hg bot trivial (fun h => h)

/-- **Each of `Ax2a`, `Ax4`, `Ax1GenTwo` is needed for `gex_2a4`.** -/
theorem gex_minimal :
    -- without `Ax2a`
    (LGenF Minimal.noAx2a ∧ Closed Minimal.noAx2a ∧ Ax4 Minimal.noAx2a ∧
      Ax1GenTwo Minimal.noAx2a ∧ ¬ Ax2a Minimal.noAx2a ∧ ∀ w, ¬ ExG Minimal.noAx2a w) ∧
    -- without `Ax4`
    (LGenF TwoNeedsAx2a.anti ∧ Closed TwoNeedsAx2a.anti ∧ Ax2a TwoNeedsAx2a.anti ∧
      Ax1GenTwo TwoNeedsAx2a.anti ∧ ¬ Ax4 TwoNeedsAx2a.anti ∧ ∀ w, ¬ ExG TwoNeedsAx2a.anti w) ∧
    -- without `Ax1GenTwo`
    (LGenF RigidExit.rx ∧ Closed RigidExit.rx ∧ Ax2a RigidExit.rx ∧ Ax4 RigidExit.rx ∧
      ¬ Ax1GenTwo RigidExit.rx ∧ ∀ w, ¬ ExG RigidExit.rx w) := by
  obtain ⟨-, -, -, n4, -, -, ng, n2a, -⟩ := Minimal.noAx2a_props
  obtain ⟨la, ca, a2a, -, -, a2, -, a4⟩ := TwoNeedsAx2a.ax4_needed
  obtain ⟨rl, -, -, r2a, -, -, -, -, -, -, -, r2⟩ := RigidExit.rigid_exit
  exact ⟨⟨LGeneralFullInst.lgenF_full _ (fun _ => trivial) (fun _ => trivial) (fun _ => trivial),
      closed_noAx2a, n4, two_noAx2a, n2a, ng⟩,
    ⟨la, ca, a2a, a2, a4, anti_godless⟩,
    ⟨LGeneralFullInst.Rx.lgenF_rx, LGeneral.closed_of_lgeneral rl, r2a, RigidExit.ax4, r2,
      RigidExit.godless⟩⟩

end Programme.«20261022-0733-ontological».Run2.GexTwo

#print axioms Programme.«20261022-0733-ontological».Run2.GexTwo.gex_2a4
#print axioms Programme.«20261022-0733-ontological».Run2.GexTwo.k1_noAx3
#print axioms Programme.«20261022-0733-ontological».Run2.GexTwo.gex_minimal
