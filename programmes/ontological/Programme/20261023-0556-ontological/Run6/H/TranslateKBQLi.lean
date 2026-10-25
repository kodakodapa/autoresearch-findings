import Lean
import OpenQuestions.Ax1GenTwoVariant2
import Programme.«20261023-0556-ontological».Run6.H.TranslateKBQL

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


-- [cleanup 2026-10-23] shared block (11376 lines) now imported from Programme.«20261023-0556-ontological».Run6.H.TranslateKBQL
open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.HOLX
open Programme.Run6.H Programme.H

#print axioms Programme.Run6.H.QL.not_validOn
#print axioms Programme.Run6.H.QL.not_validFs

/-! ## Q_L, part (i): Th3 is valid on every `Q_L` frame (th's P131, ThH15)

`Th2ex` (`∃ᴱx.Gx → □∃ᴱy.Gy`, the module's `Th2` at an existential witness, no frame hypothesis)
is translated with the module's own proof; its theory is `Th3K.T` (`rfl`), and its image is
`th2 ψ` where `Th3K.φ = th3 ψ` for the same deep `ψ = ∃ᴱx.Gx` (`rfl`).  th's semantic step
`th3_of_th2` (ThH15, copied verbatim with renamed namespace) then gives Th3 over all 𝓛-general
models of `Th3K.T` on any `Q_L` frame. -/
namespace Programme.Run6.H.QLi
/-- th's Th2ex (P131): Th2 applied to an existential witness, no frame hypothesis. -/
theorem Th2ex : ⌊(∃ᴱ x, G x) →ᵐ □(∃ᴱ y, G y)⌋ := fun w ⟨x, _, hG⟩ => Th2 x w hG
end Programme.Run6.H.QLi
open Programme.Run6.H.QLi

set_option maxHeartbeats 0 in
#deep_translate Th2ex as Programme.Run6.H.Th2X

namespace Programme.Run6.H.QLi
open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.HOLX

variable {W : Type}

/-- The frame condition `Q_L` (th's ThH15.QL). -/
def QL (R : W → W → Prop) : Prop :=
  ∀ B : W → Prop, (∀ x y, B x → R x y → B y) →
    ∀ w b u, ¬ B w → R w b → B b → R w u → B u

def th3 (ψ : Tm [] .s) : Tm [] .s := .imp (.neg (.box (.neg ψ))) (.box ψ)
def th2 (ψ : Tm [] .s) : Tm [] .s := .imp ψ (.box ψ)

/-- The deep `∃ᴱx. G x` shared by both images. -/
def ψG : Tm [] .s :=
  (Tm.all (FTy.e.arr FTy.s) ((Tm.pos.app (Tm.var Var.zero)).imp ((Tm.var Var.zero).app (Tm.var Var.zero.succ)))).exE

theorem T_eq : Programme.Run6.H.Th2X.T = Programme.Run6.H.Th3K.T := rfl
theorem th2_eq : Programme.Run6.H.Th2X.φ = th2 ψG := rfl
theorem th3_eq : Programme.Run6.H.Th3K.φ = th3 ψG := rfl

/-- th's ThH15.th3_of_th2, verbatim. -/
theorem th3_of_th2 (M : VM W) (L : LGen M) (hQ : QL M.R) (ψ : Tm [] .s)
    (h2 : ∀ w, M.pr (L.ev (th2 ψ) ()) w) : ∀ w, M.pr (L.ev (th3 ψ) ()) w := by
  intro w
  have h2' : ∀ x, M.pr (L.ev ψ ()) x → ∀ y, M.R x y → M.pr (L.ev ψ ()) y := fun x hx =>
    (L.box ψ () x).1 ((L.imp ψ (.box ψ) () x).1 (h2 x) hx)
  show M.pr (L.ev (.imp (.neg (.box (.neg ψ))) (.box ψ)) ()) w
  rw [L.imp, L.neg, L.box, L.box]
  intro hd u hu
  have : ∃ b, M.R w b ∧ M.pr (L.ev ψ ()) b := by
    refine Classical.byContradiction fun hn => hd fun v hv => (L.neg ψ () v).2 fun hb => hn ⟨v, hv, hb⟩
  obtain ⟨b, hwb, hb⟩ := this
  by_cases hw : M.pr (L.ev ψ ()) w
  · exact h2' w hw u hu
  · exact hQ (fun x => M.pr (L.ev ψ ()) x) (fun x y hx => h2' x hx y) w b u hw hwb hb hu

/-- **Q_L (i).** On every `Q_L` frame `(W,R)`, Th3 holds at every world of every v4 𝓛-general
model of `Th3K.T` (Ax3, Ax2b, Ax2a) with nonempty individuals. -/
theorem validOn_QL {R : W → W → Prop} (hQ : QL R) :
    Programme.Run6.H.QL.ValidOn R Programme.Run6.H.Th3K.T Programme.Run6.H.Th3K.φ := by
  intro M L hR hne hT
  subst hR
  rw [th3_eq]
  refine th3_of_th2 M L hQ ψG ?_
  rw [← th2_eq]
  exact Programme.Run6.H.Th2X.valid W M L hne (by rw [T_eq]; exact hT)

theorem QL_of_symm {R : W → W → Prop} (hs : ∀ x y, R x y → R y x) : QL R :=
  fun _ cl w b _ hw hwb hb _ => absurd (cl b w hb (hs w b hwb)) hw
theorem QL_of_eucl {R : W → W → Prop} (he : ∀ x y z, R x y → R x z → R y z) : QL R :=
  fun _ cl w b u _ hwb hb hwu => cl b u hb (he w b u hwb hwu)

/-- Corollaries: symmetric (K7's frames) and Euclidean (K12's frames). -/
theorem validOn_symm {R : W → W → Prop} (hs : ∀ x y, R x y → R y x) :
    Programme.Run6.H.QL.ValidOn R Programme.Run6.H.Th3K.T Programme.Run6.H.Th3K.φ :=
  validOn_QL (QL_of_symm hs)
theorem validOn_eucl {R : W → W → Prop} (he : ∀ x y z, R x y → R x z → R y z) :
    Programme.Run6.H.QL.ValidOn R Programme.Run6.H.Th3K.T Programme.Run6.H.Th3K.φ :=
  validOn_QL (QL_of_eucl he)

end Programme.Run6.H.QLi
#print axioms Programme.Run6.H.Th2X.valid
#print axioms Programme.Run6.H.QLi.validOn_QL
#print axioms Programme.Run6.H.QLi.validOn_symm
#print axioms Programme.Run6.H.QLi.validOn_eucl
