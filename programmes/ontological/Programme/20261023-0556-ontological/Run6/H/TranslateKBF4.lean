import Lean
import OpenQuestions.Ax1GenTwoVariant2
import Programme.«20261023-0556-ontological».Run6.H.TranslateKBNec

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


-- [cleanup 2026-10-23] shared block (11062 lines) now imported from Programme.«20261023-0556-ontological».Run6.H.TranslateKBNec
open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.HOLX
open Programme.Run6.H Programme.H

#print axioms Programme.Run6.H.NecSymm.not_validFs_S4
#print axioms Programme.Run6.H.NecSymm.not_valid

/-! ## Th3 on the frame F4: shallow-valid but not 𝓛-general-valid (th's P114, ThH13)

th's `ThH13` (`agents/th/lean/Programme/Run6/ThH13.lean`, the pull-back part copied with renamed
namespace): a v4 `𝓛`-general model re-indexed along a surjective bounded morphism `f : W₄ → W₃` is
again `𝓛`-general with the same evaluation.  F4 = {01,03,31,12,21} maps onto F3 = {01,02,21,11} by
`blk` ({0}↦0, {1,2}↦1, {3}↦2).  On F3 the full model with one always-actual entity and
`P φ := φ () 1` (th's ThH12b generic model, c = 1) satisfies `Th3K.T` and refutes Th3 at 0; its
pull-back to F4 is an `𝓛`-general model on F4 refuting Th3.  Every full model on F4 satisfies Th3
(`F4_Qt`, th's ThH12.Th3_Qt). -/
namespace Programme.Run6.H.F4
open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.HOLX

variable {W₃ W₄ : Type}

/-- `M` re-indexed along `f`, with accessibility `R₄`. -/
def pull (M : VM W₃) (f : W₄ → W₃) (hf : Function.Surjective f) (R₄ : W₄ → W₄ → Prop) : VM W₄ where
  R := R₄
  C := M.C
  act y w := M.act y (f w)
  pr p w := M.pr p (f w)
  pr_inj p q h := M.pr_inj p q (funext fun v => by obtain ⟨w, rfl⟩ := hf v; exact congrFun h w)
  ap := M.ap
  ap_ext := M.ap_ext
  P := M.P

def conv (M : VM W₃) (f : W₄ → W₃) (hf : Function.Surjective f) (R₄ : W₄ → W₄ → Prop) :
    {Γ : List FTy} → VEnv (pull M f hf R₄) Γ → VEnv M Γ
  | [], _ => ()
  | _ :: _, ρ => (ρ.1, conv M f hf R₄ ρ.2)

theorem conv_get (M : VM W₃) (f : W₄ → W₃) (hf : Function.Surjective f) (R₄ : W₄ → W₄ → Prop) :
    ∀ {Γ : List FTy} {t : FTy} (i : Var Γ t) (ρ : VEnv (pull M f hf R₄) Γ),
      i.vget M (conv M f hf R₄ ρ) = i.vget (pull M f hf R₄) ρ
  | _, _, .zero, _ => rfl
  | _, _, .succ i, ρ => conv_get M f hf R₄ i ρ.2

/-- The pulled-back model is 𝓛-general, with the same evaluation function. -/
def pullL (M : VM W₃) (L : LGen M) (f : W₄ → W₃) (hf : Function.Surjective f) (R₄ : W₄ → W₄ → Prop)
    (forth : ∀ w v, R₄ w v → M.R (f w) (f v))
    (back : ∀ w v', M.R (f w) v' → ∃ v, R₄ w v ∧ f v = v') : LGen (pull M f hf R₄) where
  ev t ρ := L.ev t (conv M f hf R₄ ρ)
  var i ρ := (L.var i _).trans (conv_get M f hf R₄ i ρ)
  app F x ρ := L.app F x _
  lam t ρ x := L.lam t _ x
  top ρ w := L.top _ (f w)
  bot ρ w := L.bot _ (f w)
  neg x ρ w := L.neg x _ (f w)
  and x y ρ w := L.and x y _ (f w)
  or x y ρ w := L.or x y _ (f w)
  imp x y ρ w := L.imp x y _ (f w)
  box x ρ w := by
    show M.pr (L.ev (.box x) (conv M f hf R₄ ρ)) (f w) ↔ ∀ v, R₄ w v → M.pr (L.ev x (conv M f hf R₄ ρ)) (f v)
    rw [L.box]
    exact ⟨fun h v hv => h _ (forth w v hv),
      fun h v' hv' => by obtain ⟨v, hv, rfl⟩ := back w v' hv'; exact h v hv⟩
  all a b ρ w := L.all a b _ (f w)
  ex a b ρ w := L.ex a b _ (f w)
  allE b ρ w := L.allE b _ (f w)
  exE b ρ w := L.exE b _ (f w)
  eq a x y ρ w := L.eq a x y _ (f w)
  pos ρ := L.pos _

def R4 : Fin 4 → Fin 4 → Prop := fun a b =>
  (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = 3) ∨ (a = 3 ∧ b = 1) ∨ (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1)
instance : DecidableRel R4 := fun _ _ => by unfold R4; infer_instance

def R3 : Fin 3 → Fin 3 → Prop := fun a b =>
  (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 1) ∨ (a = 1 ∧ b = 1)
instance : DecidableRel R3 := fun _ _ => by unfold R3; infer_instance

def blk : Fin 4 → Fin 3
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 1
  | _ => 2

theorem blk_surj : Function.Surjective blk := fun b => by
  match b with
  | 0 => exact ⟨0, rfl⟩
  | 1 => exact ⟨1, rfl⟩
  | 2 => exact ⟨3, rfl⟩

theorem blk_forth : ∀ w v, R4 w v → R3 (blk w) (blk v) := by decide
theorem blk_back : ∀ w v', R3 (blk w) v' → ∃ v, R4 w v ∧ blk v = v' := by decide

/-- F4 has no quasi-terminal world seen together with another world (`Q_t`). -/
theorem F4_Qt : ∀ w c u : Fin 4, R4 w c → R4 w u → (∀ y, R4 c y → y = c) → u = c := by decide

/-! The full model on F3 (one always-actual entity, `P φ := φ () 1`), in the style of `ThH7`. -/
abbrev σ := Fin 3 → Prop
def act (_ : Unit) (_ : Fin 3) : Prop := True
def P (φ : Unit → σ) : σ := fun _ => φ () 1
def box (φ : σ) : σ := fun w => ∀ v, R3 w v → φ v
def dia (φ : σ) : σ := fun w => ∃ v, R3 w v ∧ φ v
def exE (Φ : Unit → σ) : σ := fun w => ∃ x, act x w ∧ Φ x w
def allE (Φ : Unit → σ) : σ := fun w => ∀ x, act x w → Φ x w
def G (x : Unit) : σ := fun w => ∀ φ : Unit → σ, P φ w → φ x w
def PInc (φ ψ : Unit → σ) : σ := box (allE fun y w => φ y w → ψ y w)
def Ess (φ : Unit → σ) (x : Unit) : σ := fun w => φ x w ∧ ∀ ψ : Unit → σ, ψ x w → PInc φ ψ w
def E (x : Unit) : σ := fun w => ∀ φ : Unit → σ, Ess φ x w → box (exE φ) w

theorem Ax2a (φ : Unit → σ) (w : Fin 3) :
    (P φ w ∨ P (fun x v => ¬ φ x v) w) ∧ ¬ (P φ w ∧ P (fun x v => ¬ φ x v) w) := by
  unfold P; exact ⟨Classical.em _, fun ⟨a, b⟩ => b a⟩
theorem Ax2b (φ : Unit → σ) (w : Fin 3) : P φ w → box (P φ) w := fun h _ _ => h
theorem qt : ∀ y, R3 1 y → y = 1 := by decide
theorem Ax3 (w : Fin 3) : P E w := by
  intro φ hφ v hv
  rw [qt v hv]; exact ⟨(), trivial, hφ.1⟩
theorem G_iff (w : Fin 3) : G () w ↔ w = 1 :=
  ⟨fun h => h (fun _ v => v = 1) rfl, fun h => by subst h; exact fun _ h => h⟩
theorem Th3_fails : ¬ (dia (exE G) 0 → box (exE G) 0) := fun h => by
  obtain ⟨_, _, hg⟩ := h ⟨1, by decide, (), trivial, (G_iff 1).2 rfl⟩ 2 (by decide)
  exact absurd ((G_iff 2).1 hg) (by decide)

theorem hT : ∀ ψ, Th3K.T ψ → ∀ w, shR R3 act P ψ () w := by
  intro ψ hψ w
  have h' : ψ ∈ [Th3K.ax0, Th3K.ax1, Th3K.ax2] := hψ
  rcases List.mem_cons.1 h' with rfl | h'
  · exact Ax3 w
  rcases List.mem_cons.1 h' with rfl | h'
  · intro φ; exact Ax2b φ w
  rcases List.mem_cons.1 h' with rfl | h'
  · intro φ; exact Ax2a φ w
  cases h'

/-- **F4 separation.** For every list `Fs` of frame formulas true on F4, K7's theory `Th3K.T` does
not give Th3 over v4 `𝓛`-general models whose frame satisfies `Fs`; the refuting model lives on F4
itself (pull-back of the full model on F3). -/
theorem not_validFs_F4 (Fs : List (HTerm [] .o)) (hF : FramesHold R4 Fs) :
    ¬ ValidV4Fs Fs Th3K.T Th3K.φ := by
  intro h
  have hC : Closed (fullStr R3 act P) := (full_closed_resp R3 act P).1
  have hR : Resp (fullStr R3 act P) := (full_closed_resp R3 act P).2.1
  have hE : ∀ x, (fullStr R3 act P).A .e x := fun _ => trivial
  let M := ofStr (fullStr R3 act P) hC hR
  let L := ofStr_lgen (fullStr R3 act P) hC hR hE
  have hne : Nonempty ((pull M blk blk_surj R4).C .e) := ⟨Quotient.mk (setoidT _ .e) ⟨(), hE ()⟩⟩
  have hT3 : ∀ ψ, Th3K.T ψ → ∀ v, M.pr (L.ev ψ ()) v := fun ψ hψ v =>
    (ofStr_truth _ hC hR hE ψ v).2 (by rw [eval_full_eq]; exact hT ψ hψ v)
  have h4 := h (Fin 4) (pull M blk blk_surj R4) (pullL M L blk blk_surj R4 blk_forth blk_back) hne hF
    (fun ψ hψ u => hT3 ψ hψ (blk u)) 0
  have h3 : shR R3 act P Th3K.φ () 0 := by
    have := (ofStr_truth _ hC hR hE Th3K.φ 0).1 h4
    rwa [eval_full_eq] at this
  apply Th3_fails
  intro hd
  refine h3 (fun hn => ?_)
  obtain ⟨v, hv, x, hx, hg⟩ := hd
  exact hn v hv ⟨x, hx, fun φ hp => hg φ hp⟩

/-- In particular with no frame condition beyond F4 itself: the frame formula list `[]`. -/
theorem not_valid_onF4 : ¬ ValidV4Fs [] Th3K.T Th3K.φ := not_validFs_F4 [] trivial

end Programme.Run6.H.F4
#print axioms Programme.Run6.H.F4.not_validFs_F4
#print axioms Programme.Run6.H.F4.F4_Qt
