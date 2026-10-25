import Lean
import OpenQuestions.Ax1GenTwoVariant2
import Programme.«20261023-0556-ontological».Run6.H.TranslateKBQU

/-! # Thread H (run 6, pr): frame hypotheses (C7) — `Ax1GenTwoVariant2` on symmetric frames

One self-contained file, as `TranslateTwo.lean`: the library's `WitnessDeep.lean` verbatim, then the
meta-program (namespace `Programme.H`), then translations of the module's KB theorems *with the
module's own proofs*: `Th3` (`◇∃ᴱG → □∃ᴱG`), `Th5_KB` (`□∃ᴱG`) and `MC_KB` (modal collapse), each
taking the frame hypothesis `symm : ∀ x y, x 𝗿 y → y 𝗿 x`.

**Frame hypotheses (th's C7).**  A statement hypothesis whose image is a closed frame formula
(`RelOnly`: `rel` between world variables, connectives, world quantifiers) is not read as an
`𝓛`-sentence of `T`; it stays in the derivation's hypothesis list, weakened into the world context.
For `#deep_translate X as N` the tool then adds `N.Fs` (the frame formulas), `N.Fs_ok : AllRel N.Fs`,
`N.deep : DW N.Tfull [.w] (N.Fs.map wk) (holds (emb nilR N.φ) var0)` and
`N.validF : ValidV4Fs N.Fs N.T N.φ`: `N.φ` holds at every world of every v4 `𝓛`-general model of
`N.T` with nonempty individuals whose frame satisfies every formula of `N.Fs` (`sound_v4_wt_frames`,
th's `sound_v4_wt_frame` for a list).

**Structural image check (th's C8).**  `N.struct<k> : type_of% @X = shV R existsAt P n N.ax<k> ()`
for each module axiom `X`, `N.struct_φ` for the statement, by `rfl` after δ-unfolding the module
side and at most the rewrites `↔` to two implications and `◇` to `¬□¬`; and
`N.of_struct : type_of% @Th3` (etc.) re-proved from `N.validF` through `of_validFs_full`, the
structural checks, and `frame_hold` (the module's `symm` gives `FrameHolds R F`). -/


-- [cleanup 2026-10-23] shared block (11621 lines) now imported from Programme.«20261023-0556-ontological».Run6.H.TranslateKBQU
open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.HOLX
open Programme.Run6.H Programme.H
open Programme.Run6.H.QLi
open Programme.Run6.H.QU

#print axioms Programme.Run6.H.QU.validOn_iff_QU
#print axioms Programme.Run6.H.QU.validOn_QU
#print axioms Programme.Run6.H.QU.F5_valid
#print axioms Programme.Run6.H.QU.F5_not_QL
#print axioms Programme.Run6.H.DPos.valid
#print axioms Programme.Run6.H.DRig.valid
#print axioms Programme.Run6.H.DRigN.valid

/-! ## Q_U in single-generator form (th's ThH18, P153, copied verbatim; `QU` is K17's)

`Q_U` is equivalent to `Q_C`: every world that sees `b` whose reflexive-transitive cone `R*(b)` is
uniform (all dead or all serial) has all its successors in `R*(b)`.  Hence Th3's 𝓛-validity on a
frame is equivalent to `Q_C`. -/
namespace Programme.Run6.H.QC
open Programme.Run6.H.QU (QU validOn_iff_QU)

variable {W : Type}

inductive RStar (R : W → W → Prop) (b : W) : W → Prop
  | refl : RStar R b b
  | step {x y} : RStar R b x → R x y → RStar R b y

/-- the cone of `b` is uniform: all its members dead, or all serial -/
def Unif (R : W → W → Prop) (b : W) : Prop :=
  ∀ x y, RStar R b x → RStar R b y → ((∀ z, ¬ R x z) ↔ (∀ z, ¬ R y z))

def QC (R : W → W → Prop) : Prop :=
  ∀ w b u, R w b → Unif R b → R w u → RStar R b u

theorem cone_sub {R : W → W → Prop} {B : W → Prop} (hC : ∀ x y, B x → R x y → B y)
    {b x : W} (hb : B b) (h : RStar R b x) : B x := by
  induction h with
  | refl => exact hb
  | step _ hr ih => exact hC _ _ ih hr

theorem QC_of_QU {R : W → W → Prop} (h : QU R) : QC R := by
  intro w b u hwb hU hwu
  by_cases hw : RStar R b w
  · exact .step hw hwu
  · exact h (RStar R b) (fun x y hx hr => .step hx hr) hU w b u hw hwb .refl hwu

theorem QU_of_QC {R : W → W → Prop} (h : QC R) : QU R := by
  intro B hC hU w b u _ hwb hb hwu
  exact cone_sub hC hb (h w b u hwb
    (fun x y hx hy => hU x y (cone_sub hC hb hx) (cone_sub hC hb hy)) hwu)

theorem QU_iff_QC (R : W → W → Prop) : QU R ↔ QC R := ⟨QC_of_QU, QU_of_QC⟩

/-- dead-world instance, first order: a world seeing a dead world sees nothing else. -/
theorem dead_only {R : W → W → Prop} (h : QU R) (w d u : W)
    (hwd : R w d) (hd : ∀ z, ¬ R d z) (hwu : R w u) : u = d := by
  have key : ∀ x, RStar R d x → x = d := by
    intro x hx; induction hx with
    | refl => rfl
    | step _ hr ih => subst ih; exact absurd hr (hd _)
  exact key u (QC_of_QU h w d u hwd (by
    intro x y hx hy
    rw [key x hx, key y hy]) hwu)

/-- **Th3's exact frame condition, single-generator form.** -/
theorem validOn_iff_QC (R : W → W → Prop) :
    Programme.Run6.H.QL.ValidOn R Programme.Run6.H.Th3K.T Programme.Run6.H.Th3K.φ ↔ QC R :=
  (validOn_iff_QU R).trans (QU_iff_QC R)

/-- On a frame where Th3 is 𝓛-valid, a world that sees a dead world sees nothing else. -/
theorem dead_only_of_validOn {R : W → W → Prop}
    (h : Programme.Run6.H.QL.ValidOn R Programme.Run6.H.Th3K.T Programme.Run6.H.Th3K.φ)
    (w d u : W) (hwd : R w d) (hd : ∀ z, ¬ R d z) (hwu : R w u) : u = d :=
  dead_only ((validOn_iff_QU R).1 h) w d u hwd hd hwu

end Programme.Run6.H.QC
#print axioms Programme.Run6.H.QC.validOn_iff_QC
#print axioms Programme.Run6.H.QC.QU_iff_QC
#print axioms Programme.Run6.H.QC.dead_only_of_validOn
