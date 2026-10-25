import Lean
import OpenQuestions.GoedelVariantHOML3inS4oneFile
import Programme.«20261023-0556-ontological».Run6.H.TranslateS4V3

/-! # Thread H (run 6, pr): module frame axioms — `GoedelVariantHOML3inS4oneFile` (variant 3, unrestricted `Ax1Gen`)

One self-contained file, as `TranslateKB.lean`: the library's `WitnessDeep.lean` verbatim, then the
meta-program (namespace `Programme.H`), then translations of the module's theorems *with the
module's own proofs*: `MC_K` (modal collapse), `Th5_K` (`□∃ᴱG`) and `Monotheism`, which the module
proves without its frame axioms, and `Th4` (`◇∃ᴱG`), whose proof uses the module axiom `Rrefl`.

**Module frame axioms.**  A module axiom used by the proof whose image is a closed frame formula
(`Rrefl : ∀ x, x 𝗿 x`) is not read as an `𝓛`-sentence of `T`; like a frame hypothesis of the
statement (C7) it becomes a hypothesis of every derivation, lemmas included.  The output is
`N.validF : ValidV4Fs N.Fs N.T N.φ` through `GoodF.validFs` (the cut for lemmas valid on the frames
of `N.Fs`) and `sound_v4_wt_frames`; only the frame axioms the proof uses are listed (`Rtrans` is
not used).  `N.of_struct` discharges `FrameHolds R F` by the module's `Rrefl` (`frame_hold`).

**Structural image check (C8)** as in the other files: `N.struct<k>`, `N.struct_φ` by `rfl`
after δ-unfolding the module side and at most the rewrites `iff_nf`, `dia_nf`, `exAct_nf`
(identities of Lean propositions); `N.of_struct : type_of% @X` from the certificate. -/


-- [cleanup 2026-10-23] shared block (11113 lines) now imported from Programme.«20261023-0556-ontological».Run6.H.TranslateS4V3
open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.HOLX


#print axioms Programme.Run6.H.MC3K.valid
#print axioms Programme.Run6.H.MC3K.of_struct
#print axioms Programme.Run6.H.Th5V3.valid
#print axioms Programme.Run6.H.Th5V3.of_struct
#print axioms Programme.Run6.H.Mono3.valid
#print axioms Programme.Run6.H.Mono3.of_struct
#print axioms Programme.Run6.H.Th4S4.validF
#print axioms Programme.Run6.H.Th4S4.of_struct

/-! ## Th4 without reflexivity (th's ThH19, P159, copied verbatim)

In variant 3 `⊃ᴺ` is a box, so at a world without successors `G ⊃ᴺ ~G` holds vacuously and `Ax4`
carries `P G` (`L`) to `P ~G`, contradicting `Ax2a`.  The box form `Th4_box` has no
world-existential step; its translation uses Ax1Gen, Ax2a, Ax4, `∃x.⊤` (the same `T` as `Th5V3`)
and **no frame formula**. -/

namespace ThH19
theorem serial (w : i) : ∃ v, w 𝗿 v :=
  Classical.byContradiction fun h =>
    have incl : (G ⊃ᴺ ~ᵐG) w := fun v hv => (h ⟨v, hv⟩).elim
    (Ax2a G w).2 ⟨L w, Ax4 G ~ᵐG w ⟨L w, incl⟩⟩
theorem Th4_box : ⌊¬ᵐ(□(¬ᵐ(∃ᴱ x, G x)))⌋ := fun w hb =>
  have incl : (G ⊃ᴺ ~ᵐG) w := fun v hv => (hb v hv (G_ex v)).elim
  (Ax2a G w).2 ⟨L w, Ax4 G ~ᵐG w ⟨L w, incl⟩⟩
end ThH19

set_option maxHeartbeats 0 in
#deep_translate ThH19.Th4_box as Programme.Run6.H.Th4B

/-- Same theory as `Th5V3`, same sentence as `Th4S4` (which needed the frame list `[refl]`). -/
example : Programme.Run6.H.Th4B.T = Programme.Run6.H.Th5V3.T := rfl
example : Programme.Run6.H.Th4B.φ = Programme.Run6.H.Th4S4.φ := rfl

#print axioms Programme.Run6.H.Th4B.valid
#print axioms Programme.Run6.H.Th4B.of_struct
