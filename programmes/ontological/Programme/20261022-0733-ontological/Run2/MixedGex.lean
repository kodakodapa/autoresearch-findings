import Programme.«20261022-0733-ontological».Run2.MixedNeeds
import Programme.«20261022-0733-ontological».Run2.GexTwo
/-! # Actual God at every world in the mixed (Anderson) regime, without `Ax2b`

Copied from `agents/th/lean/Programme/Th/MixedGex.lean` (author th); only the namespace and the
`GexTwo` import changed.

Mixed regime of arXiv 2609.36279v4 (`Ax1GenTwoVariant2AndersonQuant`,
`Ax1GenTwoVariant3PlainAndersonQuant`): possibilist inclusion (`Ess2`/`Ess3`, `Ax4P`), actualist
necessary existence and conjunction clause.

* `gex_of_gen` (any regime): over `Closed`, `⊤` positive and `Ax1Gen`, a (possibilist) God-like
  being at `w` gives an *actual* one at `w`.  Witness: `Φ = {⊤}` and the admitted property
  `χ = λz. ¬ (G z ∧ ¬ ∃ᴱ G)`; every actual entity at every successor has `χ`, so `χ` is positive,
  hence true of the God-like being.
* `gex_mixed_v2`, `gex_mixed_v3`: `Closed`, possibilist `∃ y. G y` and `E` admitted, `Ax2a`,
  mixed `Ax3`, `Ax4P`, `Ax1GenTwo` give `∃ᴱ G` at every world: `Ax1Gen` from K29
  (`MixedNoRigidity`), a possibilist God from K2's `possGod`, then `gex_of_gen`.  No `Ax2b`.
* `gex_mixed_minimal`: each of `Ax2a`, mixed `Ax3`, `Ax4P`, `Ax1GenTwo` is needed; witnesses
  `noAx2a`, `ghost` (K29), `anti` (K28), `rx` (K19), all `LGenF`, every world without `∃ᴱ G`. -/

namespace Programme.«20261022-0733-ontological».Run2.MixedGex

open Programme.«20261022-0733-ontological».Run2 Programme.«20261022-0733-ontological».Run2.TwoClosed Programme.«20261022-0733-ontological».Run2.TwoClosedMixed
open Programme.«20261022-0733-ontological».Run2.LGeneralFull (LGenF)

variable {W D : Type} {M : Model W D}

/-- **A God-like being gives an actual one**, from `Ax1Gen` and `⊤` positive; any regime. -/
theorem gex_of_gen (C : Closed M) (h3 : ∀ w, M.P top w) (hG : Ax1Gen M) {w : W} {x : D}
    (hx : G M x w) : ExG M w := by
  let χ : D → W → Prop := neg (conj (G M) (fun _ => fun u => ¬ ExG M u))
  have hχ : M.AT χ := C.neg _ (C.conj _ _ C.god (C.lift _ (C.negS _ C.exG)))
  have Pχ : M.P χ w :=
    hG (fun ψ' _ => ψ' = top) χ (C.single _ C.top) hχ w
      (fun ψ _ h => by subst h; exact h3 w)
      (fun v _ z hz => ⟨fun _ ψ _ h => by subst h; trivial,
        fun _ ⟨hg, hn⟩ => hn ⟨z, hz, hg⟩⟩)
  exact Classical.byContradiction fun hn => hx χ hχ Pχ ⟨hx, hn⟩

/-- **Variant 2, mixed quantifiers**: `∃ᴱ G` at every world, no `Ax2b`, any frame. -/
theorem gex_mixed_v2 [Nonempty D] (C : Closed M) (hpg : M.AS (PExG M)) (hE : M.AT (E2 M))
    (h2a : Ax2a M) (h3 : ∀ w, M.P (E2 M) w) (h4 : Ax4P M) (hT : Ax1GenTwo M) (w : W) :
    ExG M w := by
  have hTop := pTop_of C h4 hE h3
  obtain ⟨x, hx⟩ := possGod C hpg h2a h4 hTop hT w
  exact gex_of_gen C hTop ((MixedNoRigidity.equivalence_v2 C hE h2a h3 h4).1 hT) hx

/-- **Variant 3′, mixed quantifiers**: `∃ᴱ G` at every world, no `Ax2b`, any frame. -/
theorem gex_mixed_v3 [Nonempty D] (C : Closed M) (hpg : M.AS (PExG M)) (hE : M.AT (TwoClosedMixed.E3 M))
    (h2a : Ax2a M) (h3 : ∀ w, M.P (TwoClosedMixed.E3 M) w) (h4 : Ax4P M) (hT : Ax1GenTwo M) (w : W) :
    ExG M w := by
  have hTop := pTop_of C h4 hE h3
  obtain ⟨x, hx⟩ := possGod C hpg h2a h4 hTop hT w
  exact gex_of_gen C hTop ((MixedNoRigidity.equivalence_v3 C hE h2a h3 h4).1 hT) hx

/-! ## Each hypothesis is needed -/

theorem pexg_eq {M : Model W D} (hall : ∀ y w, M.act y w) : PExG M = ExG M := by
  funext w; exact propext ⟨fun ⟨y, h⟩ => ⟨y, hall y w, h⟩, fun ⟨y, _, h⟩ => ⟨y, h⟩⟩

theorem ghost_godless (w : Unit) : ¬ ExG MixedNoRigidity.ghost w := fun ⟨_, h, _⟩ => h

/-- **Minimality.**  Each witness is `LGenF` and `Closed`, admits possibilist `∃ y. G y` and the
mixed `E` (variant 2 and 3′), satisfies the other three hypotheses in both variants, and has no
actual God-like being at any world. -/
theorem gex_mixed_minimal :
    -- without `Ax2a`
    (LGenF Minimal.noAx2a ∧ Closed Minimal.noAx2a ∧ Minimal.noAx2a.AS (PExG Minimal.noAx2a) ∧
      Minimal.noAx2a.AT (E2 Minimal.noAx2a) ∧ Minimal.noAx2a.AT (TwoClosedMixed.E3 Minimal.noAx2a) ∧
      (∀ w, Minimal.noAx2a.P (E2 Minimal.noAx2a) w) ∧
      (∀ w, Minimal.noAx2a.P (TwoClosedMixed.E3 Minimal.noAx2a) w) ∧ Ax4P Minimal.noAx2a ∧
      Ax1GenTwo Minimal.noAx2a ∧ ¬ Ax2a Minimal.noAx2a ∧ ∀ w, ¬ ExG Minimal.noAx2a w) ∧
    -- without mixed `Ax3`
    (LGenF MixedNoRigidity.ghost ∧ Closed MixedNoRigidity.ghost ∧
      Ax2a MixedNoRigidity.ghost ∧ Ax4P MixedNoRigidity.ghost ∧
      Ax1GenTwo MixedNoRigidity.ghost ∧
      ¬ (∀ w, MixedNoRigidity.ghost.P (E2 MixedNoRigidity.ghost) w) ∧
      ¬ (∀ w, MixedNoRigidity.ghost.P (TwoClosedMixed.E3 MixedNoRigidity.ghost) w) ∧
      ∀ w, ¬ ExG MixedNoRigidity.ghost w) ∧
    -- without `Ax4P`
    (LGenF TwoNeedsAx2a.anti ∧ Closed TwoNeedsAx2a.anti ∧
      Ax2a TwoNeedsAx2a.anti ∧ (∀ w, TwoNeedsAx2a.anti.P (E2 TwoNeedsAx2a.anti) w) ∧
      (∀ w, TwoNeedsAx2a.anti.P (TwoClosedMixed.E3 TwoNeedsAx2a.anti) w) ∧ Ax1GenTwo TwoNeedsAx2a.anti ∧
      ¬ Ax4P TwoNeedsAx2a.anti ∧ ∀ w, ¬ ExG TwoNeedsAx2a.anti w) ∧
    -- without `Ax1GenTwo`
    (LGenF RigidExit.rx ∧ Closed RigidExit.rx ∧ RigidExit.rx.AS (PExG RigidExit.rx) ∧
      RigidExit.rx.AT (E2 RigidExit.rx) ∧ RigidExit.rx.AT (TwoClosedMixed.E3 RigidExit.rx) ∧
      Ax2a RigidExit.rx ∧ (∀ w, RigidExit.rx.P (E2 RigidExit.rx) w) ∧
      (∀ w, RigidExit.rx.P (TwoClosedMixed.E3 RigidExit.rx) w) ∧ Ax4P RigidExit.rx ∧
      ¬ Ax1GenTwo RigidExit.rx ∧ ∀ w, ¬ ExG RigidExit.rx w) := by
  obtain ⟨nl, nc, n4, n2, n2a, ng⟩ := GexTwo.gex_minimal.1
  obtain ⟨gl, gc, g2a, -, g4, g2, -, -, gE2, gE3, -⟩ := MixedNoRigidity.ax3_needed
  obtain ⟨al, ac, a2a, a3, a3v, a2, -, a4⟩ := MixedNeeds.ax4_needed_mixed
  obtain ⟨rl, -, hall, r2a, -, r3, r3v, r4, -, rg, -, r2⟩ := RigidExit.rigid_exit
  have rc : Closed RigidExit.rx := LGeneral.closed_of_lgeneral rl
  refine ⟨⟨nl, nc, trivial, trivial, trivial, fun _ => trivial, fun _ => trivial,
      fun _ _ _ _ _ _ _ => trivial, n2, n2a, ng⟩,
    ⟨gl, gc, g2a, g4, g2, gE2, gE3, ghost_godless⟩,
    ⟨al, ac, a2a, a3, a3v, a2, a4, GexTwo.anti_godless⟩,
    ⟨LGeneralFullInst.Rx.lgenF_rx, rc, ?_, ?_, ?_, r2a, ?_, ?_, ?_, r2, rg⟩⟩
  · rw [pexg_eq hall]; exact rc.exG
  · rw [MixedNeeds.E2_eq hall]; exact LGeneral.E_adm rl
  · rw [MixedNeeds.E3_eq hall]; exact LGeneral.E3_adm rl
  · rw [MixedNeeds.E2_eq hall]; exact r3
  · rw [MixedNeeds.E3_eq hall]; exact r3v
  · exact (MixedNeeds.ax4P_iff hall).2 r4

end Programme.«20261022-0733-ontological».Run2.MixedGex

#print axioms Programme.«20261022-0733-ontological».Run2.MixedGex.gex_of_gen
#print axioms Programme.«20261022-0733-ontological».Run2.MixedGex.gex_mixed_v2
#print axioms Programme.«20261022-0733-ontological».Run2.MixedGex.gex_mixed_v3
#print axioms Programme.«20261022-0733-ontological».Run2.MixedGex.gex_mixed_minimal
