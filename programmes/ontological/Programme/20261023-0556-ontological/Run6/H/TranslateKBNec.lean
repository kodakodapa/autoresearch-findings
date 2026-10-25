import Lean
import OpenQuestions.Ax1GenTwoVariant2
import Programme.«20261023-0556-ontological».Run6.H.TranslateKB

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


-- [cleanup 2026-10-23] shared block (10966 lines) now imported from Programme.«20261023-0556-ontological».Run6.H.TranslateKB
open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.HOLX


#print axioms Programme.Run6.H.Th3K.validF
#print axioms Programme.Run6.H.Th5K.validF
#print axioms Programme.Run6.H.MCK.validF
#print axioms Programme.Run6.H.Th3K.of_struct
#print axioms Programme.Run6.H.Th5K.of_struct
#print axioms Programme.Run6.H.MCK.of_struct

/-! ## K7 needs its symmetry hypothesis (th's conjecture P81)

th's two-world S4 model (`agents/th/lean/Programme/Run6/ThH7.lean`, verbatim below): $R=\{00,01,11\}$,
one always-actual entity, `P φ w := φ () true`. Its Ax3, Ax2b, Ax2a are exactly the sentences
`Th3K.ax0..2` read in the full structure (`hT`, by definitional unfolding of `shR`). Since the full
structure is `𝓛`-general, `of_validFs_full` would transfer `Th3K`'s conclusion to it, contradicting
`ThH7.Th3_fails` at world `false`. -/
namespace ThH7
abbrev σ := Bool → Prop
def R (w v : Bool) : Prop := w = v ∨ v = true          -- 0→0, 0→1, 1→1
def act (_ : Unit) (_ : Bool) : Prop := True
def P (φ : Unit → σ) : σ := fun _ => φ () true
def box (φ : σ) : σ := fun w => ∀ v, R w v → φ v
def dia (φ : σ) : σ := fun w => ∃ v, R w v ∧ φ v
def exE (Φ : Unit → σ) : σ := fun w => ∃ x, act x w ∧ Φ x w
def allE (Φ : Unit → σ) : σ := fun w => ∀ x, act x w → Φ x w
def G (x : Unit) : σ := fun w => ∀ φ : Unit → σ, P φ w → φ x w
def PInc (φ ψ : Unit → σ) : σ := box (allE fun y w => φ y w → ψ y w)
def Ess (φ : Unit → σ) (x : Unit) : σ := fun w => φ x w ∧ ∀ ψ : Unit → σ, ψ x w → PInc φ ψ w
def E (x : Unit) : σ := fun w => ∀ φ : Unit → σ, Ess φ x w → box (exE φ) w

theorem refl : ∀ w, R w w := fun _ => Or.inl rfl
theorem trans : ∀ u v w, R u v → R v w → R u w := by
  intro u v w h1 h2; rcases h2 with rfl | rfl
  · exact h1
  · exact Or.inr rfl
theorem not_symm : ¬ ∀ w v, R w v → R v w := fun h => by
  rcases h false true (Or.inr rfl) with h | h <;> cases h

theorem Ax2a (φ : Unit → σ) (w : Bool) : (P φ w ∨ P (fun x v => ¬ φ x v) w) ∧ ¬ (P φ w ∧ P (fun x v => ¬ φ x v) w) := by
  unfold P; exact ⟨Classical.em _, fun ⟨a, b⟩ => b a⟩
theorem Ax2b (φ : Unit → σ) (w : Bool) : P φ w → box (P φ) w := fun h _ _ => h
theorem Ax4 (φ ψ : Unit → σ) (w : Bool) : P φ w ∧ PInc φ ψ w → P ψ w :=
  fun ⟨h, hi⟩ => hi true (Or.inr rfl) () trivial h
theorem Ax1 (φ ψ : Unit → σ) (w : Bool) : P φ w ∧ P ψ w → P (fun x v => φ x v ∧ ψ x v) w := id
theorem Ax3 (w : Bool) : P E w := by
  intro φ hφ v hv
  rcases hv with rfl | rfl <;> exact ⟨(), trivial, hφ.1⟩

theorem G_true : G () true := fun _ h => h
theorem not_G_false : ¬ G () false := fun h => by
  have := h (fun _ v => v = true) rfl; cases this

theorem Th3_fails : ¬ (dia (exE G) false → box (exE G) false) := fun h => by
  obtain ⟨_, _, hg⟩ := h ⟨true, Or.inr rfl, (), trivial, G_true⟩ false (refl false)
  exact not_G_false hg
end ThH7
open Programme.Run6.H Programme.H

namespace Programme.Run6.H.NecSymm

/-- Reflexivity and transitivity as closed frame formulas. -/
def Frefl : HTerm [] .o := .all .w (.rel (.var .zero) (.var .zero))
def Ftrans : HTerm [] .o := .all .w (.all .w (.all .w
  (.imp (.rel (.var (.succ (.succ .zero))) (.var (.succ .zero)))
    (.imp (.rel (.var (.succ .zero)) (.var .zero)) (.rel (.var (.succ (.succ .zero))) (.var .zero))))))

theorem frames : FramesHold ThH7.R [Frefl, Ftrans] := by
  refine ⟨?_, ?_, trivial⟩
  · intro w _; exact ThH7.refl w
  · intro u _ v _ w _ h1 h2; exact ThH7.trans u v w h1 h2

theorem hT : ∀ ψ, Th3K.T ψ → ∀ w, shR ThH7.R ThH7.act ThH7.P ψ () w := by
  intro ψ hψ w
  have h' : ψ ∈ [Th3K.ax0, Th3K.ax1, Th3K.ax2] := hψ
  rcases List.mem_cons.1 h' with rfl | h'
  · exact ThH7.Ax3 w
  rcases List.mem_cons.1 h' with rfl | h'
  · intro φ; exact ThH7.Ax2b φ w
  rcases List.mem_cons.1 h' with rfl | h'
  · intro φ; exact ThH7.Ax2a φ w
  cases h'

/-- Over reflexive transitive frames, Th3K's theory does not give Th3: K7 needs symmetry. -/
theorem not_validFs_S4 : ¬ ValidV4Fs [Frefl, Ftrans] Th3K.T Th3K.φ := by
  intro h
  have := of_validFs_full h ThH7.R ThH7.act ThH7.P frames hT false
  apply ThH7.Th3_fails
  intro hd
  refine this (fun hn => ?_)
  obtain ⟨v, hv, x, hx, hg⟩ := hd
  exact hn v hv ⟨x, hx, fun φ hp => hg φ hp⟩

/-- Hence K7's statement without its symmetry hypothesis fails too. -/
theorem not_valid : ¬ ValidV4 Th3K.T Th3K.φ := fun h =>
  not_validFs_S4 fun W M L hne _ hT => h W M L hne hT

end Programme.Run6.H.NecSymm
#print axioms Programme.Run6.H.NecSymm.not_validFs_S4
#print axioms Programme.Run6.H.NecSymm.not_valid
