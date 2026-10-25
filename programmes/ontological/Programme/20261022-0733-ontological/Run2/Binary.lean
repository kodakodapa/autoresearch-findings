import Programme.«20261022-0733-ontological».Run2.Principal
import Programme.«20261022-0733-ontological».Run2.LGeneralFullInst

/-! Copied from th's `Programme/Th/Binary.lean` (author th); namespace and imports changed.

# Gödel's binary conjunction axiom versus the general conjunction axiom

`Ax1Bin` is the Notes' binary `Ax1` (`P φ ∧ P ψ → P (φ ⬝ᵐ ψ)`, `Notes/GoedelVariantHOML1.lean`),
read over admitted properties.

* `bin_of_two`: over `Closed`, `Ax1GenTwo` gives `Ax1Bin` (`Φ = {φ, ψ}`).
* `rx_bin`: K19's rigid model `rx` (positivity = neighbourhood filter of the missing point `0^ω`)
  satisfies `Ax1Bin`.
* `binary_gap`: `rx` is `LGenF` and `Closed`, satisfies `Ax1Bin`, `Ax2a`, `Ax2b`, `Ax3`, `Ax3v3`,
  `Ax4` (all of variant 2 with the binary conjunction axiom), but has no actual God-like being
  at any world, no `UF` and no `Princ` at any world, and refutes `MC`, `Ax1Gen` and `Ax1GenTwo`.
  So with the binary form none of existence, principality, ultrafilter or collapse follows, and
  the binary form is strictly weaker than `Ax1GenTwo`. The model is infinite. -/

namespace Programme.«20261022-0733-ontological».Run2.Binary

open Programme.«20261022-0733-ontological».Run2 Programme.«20261022-0733-ontological».Run2.TwoClosed Programme.«20261022-0733-ontological».Run2.Ultrafilter Programme.«20261022-0733-ontological».Run2.Principal
open Programme.«20261022-0733-ontological».Run2.LGeneralFull (LGenF)

variable {W D : Type}

/-- Gödel's binary conjunction axiom, over admitted properties. -/
def Ax1Bin (M : Model W D) : Prop :=
  ∀ φ ψ, M.AT φ → M.AT ψ → ∀ w, M.P φ w → M.P ψ w → M.P (conj φ ψ) w

theorem bin_of_two {M : Model W D} (C : Closed M) (hT : Ax1GenTwo M) : Ax1Bin M :=
  fun _ _ hφ hψ _ pφ pψ => meet C hT hφ hψ pφ pψ

theorem rx_bin : Ax1Bin RigidExit.rx := by
  rintro φ ψ - - w ⟨n, hn⟩ ⟨m, hm⟩
  refine ⟨max n m, fun v hv => ⟨hn v fun i hi => hv i (by omega), hm v fun i hi => hv i (by omega)⟩⟩

theorem not_princ (w : RigidExit.Wd) : ¬ Princ RigidExit.rx w := fun h =>
  rx_not_uf w (uf_of_princ (GexTwo.gex_minimal.2.2.2.1) h)

/-- **Binary conjunction gap.** -/
theorem binary_gap :
    LGenF RigidExit.rx ∧ Closed RigidExit.rx ∧ Ax1Bin RigidExit.rx ∧
    Ax2a RigidExit.rx ∧ Ax2b RigidExit.rx ∧ Ax3 RigidExit.rx ∧ Ax3v3 RigidExit.rx ∧
    Ax4 RigidExit.rx ∧
    (∀ w, ¬ ExG RigidExit.rx w) ∧ (∀ w, ¬ UF RigidExit.rx w) ∧
    (∀ w, ¬ Princ RigidExit.rx w) ∧
    ¬ MC RigidExit.rx ∧ ¬ Ax1Gen RigidExit.rx ∧ ¬ Ax1GenTwo RigidExit.rx := by
  obtain ⟨l, -, -, h2a, h2b, h3, h3v3, h4, nmc, ng, ngen, ntwo⟩ :=
    LGeneralFullInst.rigid_exit_full
  exact ⟨l, GexTwo.gex_minimal.2.2.2.1, rx_bin, h2a, h2b, h3, h3v3, h4, ng, rx_not_uf,
    not_princ, nmc, ngen, ntwo⟩

end Programme.«20261022-0733-ontological».Run2.Binary

#print axioms Programme.«20261022-0733-ontological».Run2.Binary.bin_of_two
#print axioms Programme.«20261022-0733-ontological».Run2.Binary.rx_bin
#print axioms Programme.«20261022-0733-ontological».Run2.Binary.binary_gap
