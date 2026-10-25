import Programme.«20261022-0733-ontological».Run2.TwoNoRigidity
import Programme.«20261022-0733-ontological».Run2.AtlasFull

/-! th's `TwoNoRigidity` (E13, P200) over models closed under v4's full language (`LGenF`):
`Ax1GenTwo ↔ Ax1Gen` from `Ax2a`, `Ax3` (resp. `Ax3v3`), `Ax4`, without `Ax2b`.  The FM model
`fm` satisfies every hypothesis and refutes `Ax2b`, so the statement is strictly beyond K1. -/
namespace Programme.«20261022-0733-ontological».Run2.TwoNoRigidityFull

open Programme.«20261022-0733-ontological».Run2.TwoClosed Programme.«20261022-0733-ontological».Run2.LGeneralFull Programme.«20261022-0733-ontological».Run2.LGeneralFullBridge
open Programme.«20261022-0733-ontological».Run2.LGeneral Programme.«20261022-0733-ontological».Run2.TwoNoRigidity

/-- Full-`𝓛` form, variants 2 and 3′, any frame, any actuality, no `Ax2b`. -/
theorem equivalence_full {W D : Type} [Nonempty D] (M : Model W D) (hF : LGenF M) (h2a : Ax2a M)
    (h4 : Ax4 M) :
    (Ax3 M → (Ax1GenTwo M ↔ Ax1Gen M)) ∧ (Ax3v3 M → (Ax1GenTwo M ↔ Ax1Gen M)) := by
  have hL : LGeneral M := @lgeneral_of_lgenF W D M hF
  exact ⟨fun h3 => equivalence_v2_noRigid (closed_of_lgeneral hL) (E_adm hL) h2a h3 h4,
    fun h3 => equivalence_v3_noRigid (closed_of_lgeneral hL) (E3_adm hL) h2a h3 h4⟩

/-- Non-vacuity beyond K1: `fm` is `LGenF`, satisfies Ax2a, Ax3, Ax3v3, Ax4, refutes Ax2b. -/
theorem beyond_k1 : LGenF FM.fm ∧ Ax2a FM.fm ∧ Ax3 FM.fm ∧ Ax3v3 FM.fm ∧ Ax4 FM.fm ∧
    ¬ Ax2b FM.fm := by
  obtain ⟨h, a, b, c, d, -, -, -, -, -, -, -, -, e, -⟩ := AtlasFull.k8_full
  exact ⟨h, a, b, c, d, e⟩

end Programme.«20261022-0733-ontological».Run2.TwoNoRigidityFull

#print axioms Programme.«20261022-0733-ontological».Run2.TwoNoRigidityFull.equivalence_full
#print axioms Programme.«20261022-0733-ontological».Run2.TwoNoRigidityFull.beyond_k1
