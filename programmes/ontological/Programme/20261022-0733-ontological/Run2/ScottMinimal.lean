import Programme.«20261022-0733-ontological».Run2.ScottColumn

/-! # Minimality of the Scott KB row

`ScottColumn.scott_gex_sym`: `Closed`, `E` admitted, symmetric `R`, Scott's A1 = `Ax2a`,
A2 = `Ax4`, A3 = `L`, A4 = `Ax2b`, A5 = `Ax3` give `∃ᴱ G` at every world.  Each of the six
hypotheses on the model (symmetry and the five axioms) is needed: for each, a model that is
`LGenF` (hence `Closed`, `E` admitted), keeps the other five, and has a world without `∃ᴱ G`.
The witnesses are existing ones, reused:

* no `Ax2a`: `Minimal.noAx2a` (everything positive), universal `R`;
* no `Ax4`: `Minimal.noAx4` (`P φ := ¬ φ () false`), universal `R`;
* no `L`: `Separating.maj` (one world, three entities, majority positivity);
* no `Ax2b`: `FM.gfm` (K9, S5 on FM carriers, godless world);
* no `Ax3`: `Minimal.noAx3` (`P φ := φ () true`), universal `R`;
* no symmetry: `ScottColumn.s4` (reflexive, transitive, not symmetric). -/

namespace Programme.«20261022-0733-ontological».Run2.ScottMinimal

open Programme.«20261022-0733-ontological».Run2 Programme.«20261022-0733-ontological».Run2.TwoClosed Programme.«20261022-0733-ontological».Run2.ScottColumn
open Programme.«20261022-0733-ontological».Run2.LGeneralFull (LGenF)

/-- The side conditions of `scott_gex_sym` other than the five axioms, all from `LGenF`. -/
def Side {W D : Type} (M : Model W D) : Prop :=
  LGenF M ∧ Closed M ∧ M.AT (E M)

theorem side_of {W D : Type} {M : Model W D} (h : LGenF M) : Side M :=
  ⟨h, LGeneral.closed_of_lgeneral (LGeneralFull.lgeneral_of_lgenF h),
    LGeneral.E_adm (LGeneralFull.lgeneral_of_lgenF h)⟩

theorem sym_univ {W D : Type} {M : Model W D} (h : ∀ w v, M.R w v) :
    ∀ w v, M.R w v → M.R v w := fun w v _ => h v w

/-- **Each hypothesis of `scott_gex_sym` is needed.** -/
theorem scott_minimal :
    -- no Ax2a
    (Side Minimal.noAx2a ∧ (∀ w v, Minimal.noAx2a.R w v → Minimal.noAx2a.R v w) ∧
      Ax4 Minimal.noAx2a ∧ L Minimal.noAx2a ∧ Ax2b Minimal.noAx2a ∧ Ax3 Minimal.noAx2a ∧
      ¬ Ax2a Minimal.noAx2a ∧ ∀ w, ¬ ExG Minimal.noAx2a w) ∧
    -- no Ax4
    (Side Minimal.noAx4 ∧ (∀ w v, Minimal.noAx4.R w v → Minimal.noAx4.R v w) ∧
      Ax2a Minimal.noAx4 ∧ L Minimal.noAx4 ∧ Ax2b Minimal.noAx4 ∧ Ax3 Minimal.noAx4 ∧
      ¬ Ax4 Minimal.noAx4 ∧ ∀ w, ¬ ExG Minimal.noAx4 w) ∧
    -- no L
    (Side Separating.maj ∧ (∀ w v, Separating.maj.R w v → Separating.maj.R v w) ∧
      Ax2a Separating.maj ∧ Ax4 Separating.maj ∧ Ax2b Separating.maj ∧ Ax3 Separating.maj ∧
      ¬ L Separating.maj ∧ ¬ ExG Separating.maj ()) ∧
    -- no Ax2b
    (Side FM.gfm ∧ (∀ w v, FM.gfm.R w v → FM.gfm.R v w) ∧
      Ax2a FM.gfm ∧ Ax4 FM.gfm ∧ L FM.gfm ∧ Ax3 FM.gfm ∧
      ¬ Ax2b FM.gfm ∧ ¬ ExG FM.gfm (fun _ => false)) ∧
    -- no Ax3
    (Side Minimal.noAx3 ∧ (∀ w v, Minimal.noAx3.R w v → Minimal.noAx3.R v w) ∧
      Ax2a Minimal.noAx3 ∧ Ax4 Minimal.noAx3 ∧ L Minimal.noAx3 ∧ Ax2b Minimal.noAx3 ∧
      ¬ Ax3 Minimal.noAx3 ∧ ¬ ExG Minimal.noAx3 false) ∧
    -- no symmetry
    (Side s4 ∧ Ax2a s4 ∧ Ax4 s4 ∧ L s4 ∧ Ax2b s4 ∧ Ax3 s4 ∧
      ¬ (∀ w v, s4.R w v → s4.R v w) ∧ ¬ ExG s4 true) := by
  obtain ⟨d2b, d3, _, d4, _, dl, dng, dn2a, _⟩ := Minimal.noAx2a_props
  obtain ⟨c2a, c2b, c3, _, cl, cng, cn4, _⟩ := Minimal.noAx4_props
  obtain ⟨-, m2a, m2b, m3, _, m4, _, mR, mnl, mng⟩ := Separating.majority
  obtain ⟨-, g2a, g3, _, g4, _, _, gl, _, gng, gn2b, _⟩ := AtlasFull.k9_full
  obtain ⟨a2, b2, b4, _, bl, _, bng, bn3, _⟩ := Minimal.noAx3_props
  obtain ⟨sL, -, -, -, s2a, s4', sl, s2b, s3, -, -, -, sng, -⟩ := scott_s4_gap
  refine ⟨⟨side_of (AtlasFull.lgenF_mfull _), sym_univ fun _ _ => trivial, d4, dl, d2b, d3,
      dn2a, dng⟩,
    ⟨side_of (AtlasFull.lgenF_mfull _), sym_univ fun _ _ => trivial, c2a, cl, c2b, c3, cn4, cng⟩,
    ⟨side_of AtlasFull.lgenF_maj, sym_univ mR, m2a, m4, m2b, m3, mnl, mng⟩,
    ⟨side_of LGeneralFullInst.lgenF_gfm, sym_univ fun _ _ => trivial, g2a, g4, gl, g3, gn2b, gng⟩,
    ⟨side_of (AtlasFull.lgenF_mfull _), sym_univ fun _ _ => trivial, a2, b4, bl, b2, bn3, bng⟩,
    ⟨side_of sL, s2a, s4', sl, s2b, s3, fun h => ?_, sng⟩⟩
  -- `s4` sees world `false` from `true`, but not back.
  have := h true false (Or.inl rfl)
  rcases this with h1 | h1 <;> exact Bool.noConfusion h1

end Programme.«20261022-0733-ontological».Run2.ScottMinimal

#print axioms Programme.«20261022-0733-ontological».Run2.ScottMinimal.scott_minimal
