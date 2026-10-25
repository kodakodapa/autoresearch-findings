import Lean
import OpenQuestions.Ax1GenTwoVariant2
import Programme.«20261023-0556-ontological».Run6.H.TranslateKBQLi

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


-- [cleanup 2026-10-23] shared block (11457 lines) now imported from Programme.«20261023-0556-ontological».Run6.H.TranslateKBQLi
open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.HOLX
open Programme.Run6.H Programme.H
open Programme.Run6.H.QLi

#print axioms Programme.Run6.H.Th2X.valid
#print axioms Programme.Run6.H.QLi.validOn_QL
#print axioms Programme.Run6.H.QLi.validOn_symm
#print axioms Programme.Run6.H.QLi.validOn_eucl

/-! ## Q_U: the exact frame condition for Th3 (th's P140, ThH16)

th's three further one-line module lemmas (`ρ := P (λz. □⊥)`) are translated with their module
proofs and no frame formula; each theory is a sublist of `Th3K.T` and each image is th's
`sS ψG ρ`, `sR ρ`, `sRn ρ` by `rfl`, with the same `ψG` as `Th3K.φ = th3 ψG`.  th's semantic step
`th3_of_unif` (ThH16, verbatim) gives Th3 on every `Q_U` frame; K15's `QL.not_validOn` gives the
converse.  Hence `ValidOn R Th3K.T Th3K.φ ↔ QU R` for every frame. -/
namespace Programme.Run6.H.QU
theorem DeadPos : ⌊(∃ᴱ x, G x) →ᵐ ((□⊥ᵐ →ᵐ P (fun _ => □⊥ᵐ)) ∧ᵐ (P (fun _ => □⊥ᵐ) →ᵐ □⊥ᵐ))⌋ :=
  fun _ ⟨_, _, hG⟩ => ⟨fun h => PosOfGod hG h, fun h => hG _ h⟩
theorem DeadRig : ⌊P (fun _ => □⊥ᵐ) →ᵐ □(P (fun _ => □⊥ᵐ))⌋ := fun w h => Ax2b _ w h
theorem DeadRigN : ⌊¬ᵐ(P (fun _ => □⊥ᵐ)) →ᵐ □(¬ᵐ(P (fun _ => □⊥ᵐ)))⌋ := fun w h v hv hp =>
  (Ax2a (fun _ => □⊥ᵐ) v).2 ⟨hp, Ax2b _ w ((Ax2a' _ w).1 h) v hv⟩
end Programme.Run6.H.QU
open Programme.Run6.H.QU

set_option maxHeartbeats 0 in
#deep_translate DeadPos as Programme.Run6.H.DPos
set_option maxHeartbeats 0 in
#deep_translate DeadRig as Programme.Run6.H.DRig
set_option maxHeartbeats 0 in
#deep_translate DeadRigN as Programme.Run6.H.DRigN

namespace Programme.Run6.H.QU
open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.HOLX
open Programme.Run6.H.QLi (th2 th3 ψG T_eq th2_eq th3_eq)

variable {W : Type}

/-- th's ThH16.QU: `Q_L` restricted to `R`-closed uniform sets. -/
def QU (R : W → W → Prop) : Prop :=
  ∀ B : W → Prop, (∀ x y, B x → R x y → B y) →
    (∀ x y, B x → B y → ((∀ z, ¬ R x z) ↔ (∀ z, ¬ R y z))) →
    ∀ w b u, ¬ B w → R w b → B b → R w u → B u

def dead : Tm [] .s := .box .bot
def sS (ψ ρ : Tm [] .s) : Tm [] .s := .imp ψ (.and (.imp dead ρ) (.imp ρ dead))
def sR (ρ : Tm [] .s) : Tm [] .s := .imp ρ (.box ρ)
def sRn (ρ : Tm [] .s) : Tm [] .s := .imp (.neg ρ) (.box (.neg ρ))
/-- `P (λz. □⊥)` -/
def ρD : Tm [] .s := Tm.pos.app Tm.bot.box.lam

theorem pos_eq : Programme.Run6.H.DPos.φ = sS ψG ρD := rfl
theorem rig_eq : Programme.Run6.H.DRig.φ = sR ρD := rfl
theorem rign_eq : Programme.Run6.H.DRigN.φ = sRn ρD := rfl
theorem pos_ax : Programme.Run6.H.DPos.ax0 = Programme.Run6.H.Th3K.ax2 := rfl
theorem rig_ax : Programme.Run6.H.DRig.ax0 = Programme.Run6.H.Th3K.ax1 := rfl
theorem rign_ax0 : Programme.Run6.H.DRigN.ax0 = Programme.Run6.H.Th3K.ax2 := rfl
theorem rign_ax1 : Programme.Run6.H.DRigN.ax1 = Programme.Run6.H.Th3K.ax1 := rfl

/-- th's ThH16.th3_of_unif, verbatim. -/
theorem th3_of_unif (M : VM W) (L : LGen M) (hQ : QU M.R) (ψ ρ : Tm [] .s)
    (h2 : ∀ w, M.pr (L.ev (th2 ψ) ()) w) (hS : ∀ w, M.pr (L.ev (sS ψ ρ) ()) w)
    (hR : ∀ w, M.pr (L.ev (sR ρ) ()) w) (hRn : ∀ w, M.pr (L.ev (sRn ρ) ()) w) :
    ∀ w, M.pr (L.ev (th3 ψ) ()) w := by
  have cl : ∀ x, M.pr (L.ev ψ ()) x → ∀ y, M.R x y → M.pr (L.ev ψ ()) y := fun x hx =>
    (L.box ψ () x).1 ((L.imp ψ (.box ψ) () x).1 (h2 x) hx)
  have clR : ∀ x, M.pr (L.ev ρ ()) x → ∀ y, M.R x y → M.pr (L.ev ρ ()) y := fun x hx =>
    (L.box ρ () x).1 ((L.imp ρ (.box ρ) () x).1 (hR x) hx)
  have clRn : ∀ x, ¬ M.pr (L.ev ρ ()) x → ∀ y, M.R x y → ¬ M.pr (L.ev ρ ()) y := fun x hx y hy =>
    (L.neg ρ () y).1 ((L.box (.neg ρ) () x).1
      ((L.imp (.neg ρ) (.box (.neg ρ)) () x).1 (hRn x) ((L.neg ρ () x).2 hx)) y hy)
  have dd : ∀ x, M.pr (L.ev dead ()) x ↔ ∀ z, ¬ M.R x z := fun x => by
    unfold dead; rw [L.box]; exact ⟨fun h z hz => (L.bot (Γ := []) () z).1 (h z hz), fun h z hz => (h z hz).elim⟩
  have dρ : ∀ x, M.pr (L.ev ψ ()) x → (M.pr (L.ev ρ ()) x ↔ ∀ z, ¬ M.R x z) := fun x hx => by
    have h := hS x
    unfold sS at h
    rw [L.imp, L.and, L.imp, L.imp] at h
    have h := h hx
    exact ⟨fun r => (dd x).1 (h.2 r), fun d => h.1 ((dd x).2 d)⟩
  intro w
  show M.pr (L.ev (.imp (.neg (.box (.neg ψ))) (.box ψ)) ()) w
  rw [L.imp, L.neg, L.box, L.box]
  intro hd u hu
  have : ∃ b, M.R w b ∧ M.pr (L.ev ψ ()) b := by
    refine Classical.byContradiction fun hn => hd fun v hv => (L.neg ψ () v).2 fun hb => hn ⟨v, hv, hb⟩
  obtain ⟨b, hwb, hb⟩ := this
  by_cases hw : M.pr (L.ev ψ ()) w
  · exact cl w hw u hu
  · let B : W → Prop := fun v => M.pr (L.ev ψ ()) v ∧ (M.pr (L.ev ρ ()) v ↔ M.pr (L.ev ρ ()) b)
    have hBc : ∀ x y, B x → M.R x y → B y := fun x y ⟨hx, hxr⟩ hxy => by
      refine ⟨cl x hx y hxy, ?_⟩
      by_cases r : M.pr (L.ev ρ ()) x
      · exact ⟨fun _ => hxr.1 r, fun _ => clR x r y hxy⟩
      · exact ⟨fun h => (clRn x r y hxy h).elim, fun h => (r (hxr.2 h)).elim⟩
    have hBu : ∀ x y, B x → B y → ((∀ z, ¬ M.R x z) ↔ (∀ z, ¬ M.R y z)) :=
      fun x y ⟨hx, hxr⟩ ⟨hy, hyr⟩ => (dρ x hx).symm.trans (hxr.trans (hyr.symm.trans (dρ y hy)))
    exact (hQ B hBc hBu w b u (fun h => hw h.1) hwb ⟨hb, Iff.rfl⟩ hu).1

/-- **Q_U, sufficiency.** On every `Q_U` frame, Th3 holds at every world of every v4 𝓛-general
model of `Th3K.T` (Ax3, Ax2b, Ax2a) with nonempty individuals. -/
theorem validOn_QU {R : W → W → Prop} (hQ : QU R) :
    Programme.Run6.H.QL.ValidOn R Programme.Run6.H.Th3K.T Programme.Run6.H.Th3K.φ := by
  intro M L hR hne hT
  subst hR
  have h2 := Programme.Run6.H.Th2X.valid W M L hne (by rw [T_eq]; exact hT)
  have m1 : ∀ w, M.pr (L.ev Programme.Run6.H.Th3K.ax1 ()) w :=
    hT _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have m2 : ∀ w, M.pr (L.ev Programme.Run6.H.Th3K.ax2 ()) w :=
    hT _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have hS := Programme.Run6.H.DPos.valid W M L hne (by
    intro ψ hψ
    have h' : ψ ∈ [Programme.Run6.H.DPos.ax0] := hψ
    rw [List.mem_singleton] at h'; subst h'; rw [pos_ax]; exact m2)
  have hR' := Programme.Run6.H.DRig.valid W M L hne (by
    intro ψ hψ
    have h' : ψ ∈ [Programme.Run6.H.DRig.ax0] := hψ
    rw [List.mem_singleton] at h'; subst h'; rw [rig_ax]; exact m1)
  have hRn := Programme.Run6.H.DRigN.valid W M L hne (by
    intro ψ hψ
    have h' : ψ ∈ [Programme.Run6.H.DRigN.ax0, Programme.Run6.H.DRigN.ax1] := hψ
    rcases List.mem_cons.1 h' with h | h
    · subst h; rw [rign_ax0]; exact m2
    · rw [List.mem_singleton] at h; subst h; rw [rign_ax1]; exact m1)
  rw [th3_eq]
  rw [th2_eq] at h2; rw [pos_eq] at hS; rw [rig_eq] at hR'; rw [rign_eq] at hRn
  exact th3_of_unif M L hQ ψG ρD h2 hS hR' hRn

/-- **Q_U, necessity** (from K15's `QL.not_validOn`). -/
theorem QU_of_validOn {R : W → W → Prop}
    (h : Programme.Run6.H.QL.ValidOn R Programme.Run6.H.Th3K.T Programme.Run6.H.Th3K.φ) : QU R := by
  intro B hc hu w b u hw hwb hb hwu
  refine Classical.byContradiction fun hnu => ?_
  have unif : (∀ x, B x → ∃ y, R x y) ∨ (∀ x y, B x → ¬ R x y) := by
    by_cases hd : ∀ z, ¬ R b z
    · exact .inr fun x y hx hxy => (hu b x hb hx).1 hd y hxy
    · refine .inl fun x hx => Classical.byContradiction fun hn => hd ?_
      exact (hu b x hb hx).2 fun z hz => hn ⟨z, hz⟩
  exact Programme.Run6.H.QL.not_validOn R B hc unif hb hnu hwb hwu h

/-- **Th3's exact frame condition.** For every frame `(W,R)`: Th3 holds at every world of every
v4 𝓛-general model of `Th3K.T` on `(W,R)` with nonempty individuals iff `R` satisfies `Q_U`. -/
theorem validOn_iff_QU (R : W → W → Prop) :
    Programme.Run6.H.QL.ValidOn R Programme.Run6.H.Th3K.T Programme.Run6.H.Th3K.φ ↔ QU R :=
  ⟨QU_of_validOn, validOn_QU⟩

/-! ### F5 (th): `Q_U` holds, `Q_L` fails, so Th3 is 𝓛-valid on a non-`Q_L` frame. -/
def R5 : Fin 5 → Fin 5 → Prop := fun a b =>
  (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = 3) ∨ (a = 1 ∧ b = 2) ∨ (a = 3 ∧ b = 4)
instance : DecidableRel R5 := fun _ _ => by unfold R5; infer_instance

theorem F5_not_QL : ¬ Programme.Run6.H.QLi.QL R5 := fun h => by
  have := h (fun v => v = 1 ∨ v = 2) (by decide) 0 1 3 (by decide) (by decide) (by decide) (by decide)
  revert this; decide

theorem F5_QU : QU R5 := by
  intro B hc hu w b u hw hwb hb hwu
  have no : ∀ x y : Fin 5, R5 x y → (∀ z, ¬ R5 y z) → (∃ z, R5 x z) → ¬ B x := fun x y hxy hy hx hB =>
    let ⟨z, hz⟩ := hx; (hu x y hB (hc x y hB hxy)).2 hy z hz
  have n1 : ¬ B 1 := no 1 2 (by decide) (by decide) ⟨2, by decide⟩
  have n3 : ¬ B 3 := no 3 4 (by decide) (by decide) ⟨4, by decide⟩
  have key : ∀ w b u : Fin 5, R5 w b → R5 w u → b ≠ 1 → b ≠ 3 → u = b := by decide
  have := key w b u hwb hwu (fun h => n1 (h ▸ hb)) (fun h => n3 (h ▸ hb))
  exact this ▸ hb

theorem F5_valid : Programme.Run6.H.QL.ValidOn R5 Programme.Run6.H.Th3K.T Programme.Run6.H.Th3K.φ :=
  validOn_QU F5_QU

end Programme.Run6.H.QU
#print axioms Programme.Run6.H.QU.validOn_iff_QU
#print axioms Programme.Run6.H.QU.validOn_QU
#print axioms Programme.Run6.H.QU.F5_valid
#print axioms Programme.Run6.H.QU.F5_not_QL
#print axioms Programme.Run6.H.DPos.valid
#print axioms Programme.Run6.H.DRig.valid
#print axioms Programme.Run6.H.DRigN.valid
