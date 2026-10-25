import OpenQuestions.Ax1GenRigidVariant2
import Programme.«20261022-1724-ontological».Run3.WitnessDeep

/-! # Thread G (run 5, pr): `L_R` semantically, via a certified deep derivation

Lines after this header up to section `Programme.Run5.G.RigidDeep`: the library's
`Programme/20261022-1724-ontological/Run3/WitnessDeep.lean` (run 4's `VM`/`LGen`, `DC`, `DW`,
`sound_v4_wt`, `of_DC`, K1's variant-2 sentences in `𝓛`) verbatim minus its `#print`s, with the
import of `OpenQuestions.Ax1GenRigidVariant2` added for the clause-by-clause match.

`RigidDeep`: v4 sec:rigid asks that a rigid set be "given by a condition formed in 𝓛"; so
`Ax1GenR` is a schema `Ax1GenR c` over `𝓛`-conditions `c` on a property variable (`Rigid c`:
built from equations by connectives and carrier quantifiers; `rigid_ev`: world-independent).
`TR` = `Ax2a`, `Ax2b`, `Ax4`, `Ax1GenR (P ψ = ⊤)`.  `l_r`: a `DC` derivation of `P G`
(RigidHF's proof, `guard_pos` the deep `guard_pos_hf`); `l_r_valid := sound_v4_wt (of_DC l_r)`.
`RigidMatch`: in the full structure on the module's postulates each deep sentence is the
module's axiom (`match_*`), and `L_R_of_deep` re-proves the module's `L_R` through the deep route.
`genR_sound_full`/`genR_sound`: every rigid instance `Ax1GenR c` of the deep schema holds in the
full structure whenever the shallow (module) `Ax1GenR` does. -/

/-! # WitnessDeep.lean (th, run 3, round 10): target C (d) in deep form

Lines after this header: pr's `SepLS.lean` (K14 evidence; contains K8's `sep_not_valid_v4` and K12/K13's
`Canon`/`LS`) minus its final `#print`, then th's `WholeTerm.lean` section `Programme.ThWhole` (round 9:
`DG`, `DW`, `sound_v4_wt`, `of_DC`) minus `#print`s, both verbatim; then section `Programme.ThWit`:
the witness-only calculus `DG3` derives v4's separating sentence from every theory. -/

-- [cleanup 2026-10-23] shared block (7898 lines) now imported from Programme.«20261022-1724-ontological».Run3.WitnessDeep





namespace Programme.«20261023-0519-ontological».Run5.G.RigidDeep
open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.HOLX
open Programme.«20261022-1724-ontological».Run3.V4 Programme.«20261022-1724-ontological».ThWhole

/-! ## The rigid reading in `𝓛` -/

abbrev v0 : Tm (t :: Γ) t := .var .zero
abbrev v1 : Tm (u :: t :: Γ) t := .var (.succ .zero)
abbrev Pos (φ : Tm Γ tp) : Tm Γ .s := .app .pos φ
abbrev God : Tm Γ tp := Programme.«20261022-1724-ontological».Run3.K1.God
abbrev negP (φ : Tm Γ tp) : Tm Γ tp := Programme.«20261022-1724-ontological».Run3.K1.negP φ
abbrev PInc (φ ψ : Tm Γ tp) : Tm Γ .s := Programme.«20261022-1724-ontological».Run3.K1.PInc φ ψ
abbrev dAx2a : Tm [] .s := Programme.«20261022-1724-ontological».Run3.K1.Ax2a
abbrev dAx2b : Tm [] .s := Programme.«20261022-1724-ontological».Run3.K1.Ax2b
abbrev dAx4 : Tm [] .s := Programme.«20261022-1724-ontological».Run3.K1.Ax4

/-- A rigid set of properties given by an `𝓛`-condition `c` on the property variable `0`:
the term `λψ. c` of type `(e → σ) → σ`.  `PosPropsR`, `ConjR` are the module's, read at it. -/
def setOf (c : Tm [tp] .s) : Tm [] th := .lam c

def PosPropsR (Φ : Tm Γ th) : Tm Γ .s := .all tp (.imp (.app (wkL Φ) v0) (Pos v0))
def ConjR (φ : Tm Γ tp) (Φ : Tm Γ th) : Tm Γ .s :=
  .box (.allE (.and (.imp (.app (wkL φ) v0) (.all tp (.imp (.app (wkL (wkL Φ)) v0) (.app v0 v1))))
    (.imp (.all tp (.imp (.app (wkL (wkL Φ)) v0) (.app v0 v1))) (.app (wkL φ) v0))))
/-- The instance of the schema `Ax1GenR` for the condition `c`. -/
def Ax1GenR (c : Tm [tp] .s) : Tm [] .s :=
  .all tp (.imp (PosPropsR (wkL (setOf c))) (.imp (ConjR v0 (wkL (setOf c))) (Pos v0)))

/-- v4's globally positive properties `{ψ | P ψ = ⊤}`, `A(P ψ)` in the primitive equality. -/
def posGlobalC : Tm [tp] .s := .eq .s (Pos v0) .top

inductive TR : Tm [] .s → Prop
  | ax2a : TR dAx2a
  | ax2b : TR dAx2b
  | ax4 : TR dAx4
  | genR : TR (Ax1GenR posGlobalC)

abbrev PG : Tm Γ th := .lam (.eq .s (Pos v0) .top)

example : (PG : Tm [] th) = setOf posGlobalC := rfl
example : (PG : Tm [tp] th) = wkL (setOf posGlobalC) := rfl

section deriv
variable {Γ' : List FTy} {Γ : List HTy} {hs : List (HTerm Γ .o)} {r : LRen Γ' Γ} {i j : HTerm Γ .w}

open Programme.«20261022-1724-ontological».Run3.K1 (ax_at h0 h1 h2 h3 cut byCases absurd' mem_wkL)
open Programme.«20261022-1724-ontological».ThWit (L_ext)

theorem ax2a_at (φ : Tm Γ' tp) : DC TR Γ hs (Lf r
    (.and (.or (Pos φ) (Pos (negP φ))) (.neg (.and (Pos φ) (Pos (negP φ))))) i) := by
  have := L_allE (ax_at (r := r) (i := i) (hs := hs) TR.ax2a _ rfl : DC TR Γ hs (Lf r (.all tp _) i)) φ
  exact this

theorem ax2b_at (φ : Tm Γ' tp) : DC TR Γ hs (Lf r (.imp (Pos φ) (.box (Pos φ))) i) :=
  L_allE (ax_at (r := r) (i := i) (hs := hs) TR.ax2b _ rfl : DC TR Γ hs (Lf r (.all tp _) i)) φ

/-- The guarded property `λx. P ψ → ψ x`, for the property variable `ψ := 0`. -/
abbrev guard (ψ : Tm Γ' tp) : Tm Γ' tp := .lam (.imp (Pos (wkL ψ)) (.app (wkL ψ) v0))

/-- Elimination of `PG ψ`: `P ψ = ⊤` at one world gives `P ψ` at every world. -/
theorem pg_elim {ψ : Tm Γ' tp} (d : DC TR Γ hs (Lf r (.app PG ψ) i)) :
    DC TR Γ hs (Lf r (Pos ψ) j) := by
  have e := L_eqE (L_betaE d)
  exact L_rw (i := j) (x := .top) (y := Pos ψ) rfl (v0 : Tm (.s :: Γ') .s) (.symm _ e) L_topI

/-- Introduction of `PG ψ`: `P ψ` at a fresh world gives `P ψ = ⊤`. -/
theorem pg_intro {ψ : Tm Γ' tp} (d : DC TR (.w :: Γ) (hs.map wk) (Lf (shL r) (Pos ψ) var0)) :
    DC TR Γ hs (Lf r (.app PG ψ) i) :=
  L_betaI (L_eqI (L_ext L_topI (d.wk1 _)))

/-- `RigidHF.guard_pos_hf` in `𝓛`: `λx. P ψ → ψ x` is positive (`Ax2a`, `Ax2b`, `Ax4`). -/
theorem guard_pos {Δ : List FTy} {r : LRen (tp :: Δ) Γ} :
    DC TR Γ hs (Lf r (Pos (guard (v0 : Tm (tp :: Δ) tp))) i) := by
  refine byCases (Lf r (Pos v0) i) ?_ ?_
  · have a := L_allE (L_allE (ax_at (r := r) (i := i) TR.ax4 _ rfl :
      DC TR Γ (Lf r (Pos v0) i :: hs) (Lf r (.all tp _) i)) v0
      : DC TR Γ _ (Lf r (.all tp _) i)) (guard v0)
    refine .impE (L_impE (.impE (L_impE a) h0)) ?_
    exact L_boxI (L_allEI (L_impI (.impI (L_betaI (L_impI (.impI h1))))))
  · -- `¬P ψ`: then `P ¬ψ`, and `Ax4` from `¬ψ`; the inclusion holds since `P ψ` fails along `R`
    have a2 := ax2a_at (r := r) (i := i) (hs := .imp (Lf r (Pos v0) i) .bot :: hs) v0
    refine cut (.orE (L_orE (.andL (L_andE a2))) (absurd' h0 h1) h0) ?_
    have a := L_allE (L_allE (ax_at (r := r) (i := i) TR.ax4 _ rfl :
      DC TR Γ (Lf r (Pos (negP v0)) i :: .imp (Lf r (Pos v0) i) .bot :: hs) (Lf r (.all tp _) i))
      (negP v0) : DC TR Γ _ (Lf r (.all tp _) i)) (guard v0)
    refine .impE (L_impE (.impE (L_impE a) h0)) ?_
    refine L_boxI ?_
    -- at a successor `v` (variable `0`): `P ¬ψ` there, by `Ax2b`
    have pn : DC TR (.w :: Γ) (HTerm.rel (wk i) var0 :: (Lf r (Pos (negP v0)) i ::
        .imp (Lf r (Pos v0) i) .bot :: hs).map wk) (Lf (shL r) (Pos (negP v0)) var0) := by
      have m : Lf (shL (b := .w) r) (Pos (negP v0)) (wk (b := .w) i) ∈ (Lf r (Pos (negP v0)) i ::
          .imp (Lf r (Pos v0) i) .bot :: hs).map (wk (b := .w)) := by
        rw [← wk_Lf]; exact List.mem_map_of_mem (List.mem_cons_self ..)
      exact L_boxE (.impE (L_impE (ax2b_at (negP v0))) (.hyp (List.mem_cons_of_mem _ m))) h0
    refine cut pn ?_
    refine L_allEI (L_impI (.impI (L_betaI (L_impI (.impI ?_)))))
    refine .exFalso (.impE (L_negE (.andR (L_andE (ax2a_at (Γ' := .e :: tp :: Δ)
      (r := liftL (shL r)) (i := wk var0) (v1 : Tm (.e :: tp :: Δ) tp))))) (L_andI (.andI h0 (.hyp ?_))))
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (mem_wkL (List.mem_cons_self ..))))

theorem posPropsR_pg : DC TR Γ hs (Lf r (PosPropsR PG) i) :=
  L_allI (L_impI (.impI (pg_elim h0)))

/-- `ConjR G PG`: at every successor, an actual entity is God-like iff it has every globally
positive property; `←` through the guarded properties (`guard_pos`). -/
theorem conjR_god : DC TR Γ hs (Lf r (ConjR God PG) i) := by
  refine L_boxI (L_allEI (L_andI (.andI (L_impI (.impI ?_)) (L_impI (.impI ?_)))))
  · refine L_allI (L_impI (.impI ?_))
    refine .impE (L_impE (L_allE (b := .imp (Pos v0) (.app v0 (.var (.succ (.succ .zero)))))
      (L_betaE (b := .all tp (.imp (Pos v0) (.app v0 v1))) (x := v1)
        (Deriv.hyp (List.mem_cons_of_mem _ (mem_wkL (a := tp) (r := liftL (shL r))
          (φ := .app (wkL God) v0) (i := wk var0) (List.mem_cons_self ..))))) v0)) (pg_elim h0)
  · refine L_betaI (L_allI (L_impI (.impI ?_)))
    refine .impE (L_impE (L_betaE (b := .imp (Pos (wkL v0)) (.app (wkL v0) v0)) (x := v1)
      (.impE (L_impE (L_allE (b := .imp (.app PG v0) (.app v0 (.var (.succ (.succ .zero)))))
        (Deriv.hyp (List.mem_cons_of_mem _ (mem_wkL (a := tp) (r := liftL (shL r))
          (φ := .all tp (.imp (.app (wkL (wkL PG)) v0) (.app v0 v1))) (i := wk var0)
          (List.mem_cons_self ..)))) (guard v0))) (pg_intro guard_pos)))) h0

/-- **`L_R` in `𝓛`.** `P G` at every world, from `Ax2a`, `Ax2b`, `Ax4` and the `PosGlobal`
instance of `Ax1GenR`, in the certified calculus. -/
theorem l_r : DC TR Γ hs (Lf r (Pos God) i) := by
  have a := L_allE (ax_at (r := r) (i := i) (hs := hs) TR.genR _ rfl
    : DC TR Γ hs (Lf r (.all tp _) i)) God
  exact .impE (L_impE (.impE (L_impE a) posPropsR_pg)) conjR_god

end deriv

theorem l_r_dw : DW TR [.w] [] (.holds (emb nilR (Pos God)) var0) :=
  of_DC (l_r (r := nilR) (i := var0))

theorem l_r_valid : ValidV4 TR (Pos God) := sound_v4_wt l_r_dw
end Programme.«20261023-0519-ontological».Run5.G.RigidDeep

namespace Programme.«20261023-0519-ontological».Run5.G.RigidDeep
open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.HOLX

/-- Unpacked: every v4 `𝓛`-general model (nonempty individuals) of the four deep axioms has
`P G` at every world. -/
theorem l_r_semantic {W : Type} (M : VM W) (L : LGen M) (hne : Nonempty (M.C .e))
    (h2a : ∀ w, M.pr (L.ev dAx2a ()) w) (h2b : ∀ w, M.pr (L.ev dAx2b ()) w)
    (h4 : ∀ w, M.pr (L.ev dAx4 ()) w) (hR : ∀ w, M.pr (L.ev (Ax1GenR posGlobalC) ()) w) :
    ∀ w, M.pr (L.ev (Pos God : Tm [] .s) ()) w :=
  l_r_valid W M L hne fun ψ h => by cases h <;> assumption

/-! ## Rigid conditions: what `Ax1GenR` ranges over

A condition is rigid if it is built from equations by the connectives and the quantifiers over
carriers (no `□`, no actualist quantifier, no `P`, no variable of type `σ` outside an equation).
Its truth value does not depend on the world: it denotes a set of properties simpliciter. -/
inductive Rigid : {Γ : List FTy} → Tm Γ .s → Prop
  | eq {Γ} (a : FTy) (x y : Tm Γ a) : Rigid (.eq a x y)
  | top {Γ} : Rigid (Γ := Γ) .top
  | bot {Γ} : Rigid (Γ := Γ) .bot
  | neg {Γ} {x : Tm Γ .s} : Rigid x → Rigid (.neg x)
  | and {Γ} {x y : Tm Γ .s} : Rigid x → Rigid y → Rigid (.and x y)
  | or {Γ} {x y : Tm Γ .s} : Rigid x → Rigid y → Rigid (.or x y)
  | imp {Γ} {x y : Tm Γ .s} : Rigid x → Rigid y → Rigid (.imp x y)
  | all {Γ} (a : FTy) {b : Tm (a :: Γ) .s} : Rigid b → Rigid (.all a b)
  | ex {Γ} (a : FTy) {b : Tm (a :: Γ) .s} : Rigid b → Rigid (.ex a b)

theorem rigid_ev {W : Type} (M : VM W) (L : LGen M) {Γ : List FTy} {c : Tm Γ .s} (h : Rigid c) :
    ∀ (ρ : VEnv M Γ) (w v : W), M.pr (L.ev c ρ) w ↔ M.pr (L.ev c ρ) v := by
  induction h with
  | eq a x y => intro ρ w v; rw [L.eq, L.eq]
  | top => intro ρ w v; rw [L.top, L.top]
  | bot => intro ρ w v; rw [L.bot, L.bot]
  | neg _ ih => intro ρ w v; rw [L.neg, L.neg, ih ρ w v]
  | and _ _ ihx ihy => intro ρ w v; rw [L.and, L.and, ihx ρ w v, ihy ρ w v]
  | or _ _ ihx ihy => intro ρ w v; rw [L.or, L.or, ihx ρ w v, ihy ρ w v]
  | imp _ _ ihx ihy => intro ρ w v; rw [L.imp, L.imp, ihx ρ w v, ihy ρ w v]
  | all a _ ih => intro ρ w v; rw [L.all, L.all]; exact forall_congr' fun x => ih (x, ρ) w v
  | ex a _ ih => intro ρ w v; rw [L.ex, L.ex]; exact exists_congr fun x => ih (x, ρ) w v

/-- v4's `A(P ψ)`, spelled `P ψ = ⊤`, is a rigid condition. -/
theorem rigid_posGlobal : Rigid posGlobalC := .eq _ _ _

end Programme.«20261023-0519-ontological».Run5.G.RigidDeep

/-! ## Clause by clause against `OpenQuestions.Ax1GenRigidVariant2`

Over the full structure on the module's own worlds `i`, entities `e`, accessibility `R`,
actuality `existsAt` and positivity `P`, each deep sentence says what the module's axiom says. -/
namespace Programme.«20261023-0519-ontological».Run5.G.RigidMatch
open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.HOLX
open Programme.«20261023-0519-ontological».Run5.G

abbrev S : Str i e := fullStr _root_.R existsAt _root_.P

theorem match_ax2a : (∀ w, eval S RigidDeep.dAx2a () w) ↔ ∀ φ : e → σ, ⌊_root_.P φ ∨ᵉ _root_.P ~ᵐφ⌋ :=
  ⟨fun h φ w => h w φ trivial, fun h w φ _ => h φ w⟩

theorem match_ax2b : (∀ w, eval S RigidDeep.dAx2b () w) ↔ ∀ φ : e → σ, ⌊_root_.P φ →ᵐ □ _root_.P φ⌋ :=
  ⟨fun h φ w => h w φ trivial, fun h w φ _ => h φ w⟩

theorem match_ax4 : (∀ w, eval S RigidDeep.dAx4 () w) ↔
    ∀ φ ψ : e → σ, ⌊_root_.P φ ∧ᵐ (φ ⊃ᴺ ψ) →ᵐ _root_.P ψ⌋ :=
  ⟨fun h φ ψ w hw => h w φ trivial ψ trivial hw.1 hw.2, fun h w φ _ ψ _ h1 h2 => h φ ψ w ⟨h1, h2⟩⟩

/-- The deep `PosGlobal` instance of `Ax1GenR` is the module's `Ax1GenR` at `Φ := PosGlobal`. -/
theorem match_genR : (∀ w, eval S (RigidDeep.Ax1GenR RigidDeep.posGlobalC) () w) ↔
    ∀ φ : e → σ, ⌊(_root_.PosPropsR PosGlobal ∧ᵐ _root_.ConjR φ PosGlobal) →ᵐ _root_.P φ⌋ :=
  ⟨fun h φ w hw => h w φ trivial (fun ψ _ hψ => hw.1 ψ hψ) fun v hv z hz =>
      ⟨fun a ψ _ hψ => (hw.2 v hv z hz).1 a ψ hψ, fun b => (hw.2 v hv z hz).2 fun ψ hψ => b ψ trivial hψ⟩,
   fun h w φ _ hp hc => h φ w ⟨fun ψ hψ => hp ψ trivial hψ, fun v hv z hz =>
      ⟨fun a ψ hψ => (hc v hv z hz).1 a ψ trivial hψ, fun b => (hc v hv z hz).2 fun ψ _ hψ => b ψ hψ⟩⟩⟩

/-- The deep `P G` is the module's `P G`. -/
theorem match_god : eval S (RigidDeep.Pos RigidDeep.God : Tm [] .s) () = _root_.P G :=
  congrArg _root_.P (funext fun _ => funext fun _ => propext ⟨fun h φ => h φ trivial, fun h φ _ => h φ⟩)

/-- The module's `L_R` from the `PosGlobal` instance alone, obtained from the deep derivation
through `sound_v4_wt` and `valid_iff`, read in the full structure of the module's postulates. -/
theorem L_R_PosGlobal_of_deep
    (hR : ∀ φ : e → σ, ⌊(_root_.PosPropsR PosGlobal ∧ᵐ _root_.ConjR φ PosGlobal) →ᵐ _root_.P φ⌋) :
    ⌊_root_.P G⌋ := by
  intro w
  have hfc := full_closed_resp _root_.R existsAt _root_.P
  have := (valid_iff RigidDeep.TR _).1 RigidDeep.l_r_valid i e S inferInstance hfc.2.2 hfc.1 hfc.2.1
    (fun ψ h => by
      cases h
      · exact match_ax2a.2 _root_.Ax2a
      · exact match_ax2b.2 _root_.Ax2b
      · exact match_ax4.2 _root_.Ax4
      · exact match_genR.2 hR) w
  rw [match_god] at this
  exact this

/-- The module's `L_R` itself, through the deep route (`Ax1GenR` gives its `PosGlobal` instance). -/
theorem L_R_of_deep : type_of% @L_R := fun h => L_R_PosGlobal_of_deep fun φ => h PosGlobal φ

example : type_of% @L_R_of_deep = type_of% @L_R := rfl

end Programme.«20261023-0519-ontological».Run5.G.RigidMatch

/-! ## Schema soundness: every rigid instance follows from the module's `Ax1GenR` -/

namespace Programme.«20261023-0519-ontological».Run5.G.RigidDeep
open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.HOLX

/-- Evaluation commutes with renaming (any structure). -/
theorem eval_renameL {W D : Type} (S : Str W D) : ∀ {Γ Δ : List FTy} {t : FTy} (tm : Tm Γ t)
    (r : RenL Γ Δ) (ρ : Env W D Γ) (ρ' : Env W D Δ),
    (∀ {u} (v : Var Γ u), (r v).get ρ' = v.get ρ) → eval S (renameL r tm) ρ' = eval S tm ρ := by
  intro Γ Δ t tm
  induction tm generalizing Δ with
  | var i => intro r ρ ρ' h; exact h i
  | app F x ihF ihx => intro r ρ ρ' h; simp only [renameL, eval, ihF r ρ ρ' h, ihx r ρ ρ' h]
  | lam b ih => intro r ρ ρ' h; funext z; simp only [renameL, eval]
                exact ih (Δ := _ :: Δ) (liftRL r) (z, ρ) (z, ρ') fun v => by cases v <;> simp [liftRL, Var.get, h]
  | top => intro _ _ _ _; rfl
  | bot => intro _ _ _ _; rfl
  | neg x ih => intro r ρ ρ' h; simp only [renameL, eval, ih r ρ ρ' h]
  | and x y ihx ihy => intro r ρ ρ' h; simp only [renameL, eval, ihx r ρ ρ' h, ihy r ρ ρ' h]
  | or x y ihx ihy => intro r ρ ρ' h; simp only [renameL, eval, ihx r ρ ρ' h, ihy r ρ ρ' h]
  | imp x y ihx ihy => intro r ρ ρ' h; simp only [renameL, eval, ihx r ρ ρ' h, ihy r ρ ρ' h]
  | box x ih => intro r ρ ρ' h; simp only [renameL, eval, ih r ρ ρ' h]
  | all a b ih => intro r ρ ρ' h; funext w; simp only [renameL, eval]
                  refine propext (forall_congr' fun z => ?_)
                  rw [ih (Δ := _ :: Δ) (liftRL r) (z, ρ) (z, ρ') fun v => by cases v <;> simp [liftRL, Var.get, h]]
  | ex a b ih => intro r ρ ρ' h; funext w; simp only [renameL, eval]
                 refine propext (exists_congr fun z => ?_)
                 rw [ih (Δ := _ :: Δ) (liftRL r) (z, ρ) (z, ρ') fun v => by cases v <;> simp [liftRL, Var.get, h]]
  | allE b ih => intro r ρ ρ' h; funext w; simp only [renameL, eval]
                 refine propext (forall_congr' fun z => ?_)
                 rw [ih (Δ := _ :: Δ) (liftRL r) (z, ρ) (z, ρ') fun v => by cases v <;> simp [liftRL, Var.get, h]]
  | exE b ih => intro r ρ ρ' h; funext w; simp only [renameL, eval]
                refine propext (exists_congr fun z => ?_)
                rw [ih (Δ := _ :: Δ) (liftRL r) (z, ρ) (z, ρ') fun v => by cases v <;> simp [liftRL, Var.get, h]]
  | eq a x y ihx ihy => intro r ρ ρ' h; simp only [renameL, eval, ihx r ρ ρ' h, ihy r ρ ρ' h]
  | pos => intro _ _ _ _; rfl

theorem eval_wkL {W D : Type} (S : Str W D) {Γ : List FTy} {a b : FTy} (tm : Tm Γ a)
    (x : Den W D b) (ρ : Env W D Γ) : eval S (wkL (b := b) tm) (x, ρ) = eval S tm ρ :=
  eval_renameL (Δ := b :: Γ) S tm (fun v => .succ v) ρ (x, ρ) fun _ => rfl

/-- Rigid conditions are world-independent in every structure (the full-structure companion
of `rigid_ev`). -/
theorem rigid_eval {W D : Type} (S : Str W D) {Γ : List FTy} {c : Tm Γ .s} (h : Rigid c) :
    ∀ (ρ : Env W D Γ) (w v : W), eval S c ρ w ↔ eval S c ρ v := by
  induction h with
  | eq a x y => intro ρ w v; exact Iff.rfl
  | top => intro ρ w v; exact Iff.rfl
  | bot => intro ρ w v; exact Iff.rfl
  | neg _ ih => intro ρ w v; exact not_congr (ih ρ w v)
  | and _ _ ihx ihy => intro ρ w v; exact and_congr (ihx ρ w v) (ihy ρ w v)
  | or _ _ ihx ihy => intro ρ w v; exact or_congr (ihx ρ w v) (ihy ρ w v)
  | imp _ _ ihx ihy => intro ρ w v; exact imp_congr (ihx ρ w v) (ihy ρ w v)
  | all a _ ih => intro ρ w v; exact forall_congr' fun x => imp_congr Iff.rfl (ih (x, ρ) w v)
  | ex a _ ih => intro ρ w v; exact exists_congr fun x => and_congr Iff.rfl (ih (x, ρ) w v)

end Programme.«20261023-0519-ontological».Run5.G.RigidDeep

namespace Programme.«20261023-0519-ontological».Run5.G.RigidMatch
open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.HOLX
open Programme.«20261023-0519-ontological».Run5.G

/-- **Schema soundness, any full structure.**  Over the full structure on any frame `R`,
actuality `act` and positivity `P`, the shallow rigid `Ax1GenR` (`Φ` any set of properties)
implies, for every rigid `𝓛`-condition `c`, the deep instance `Ax1GenR c` at every world: take
`Φ` to be the set `c` defines (at any world, by `rigid_eval`). -/
theorem genR_sound_full {W D : Type} (R : W → W → Prop) (act : D → W → Prop) (P : Den W D th)
    (c : Tm [tp] .s) (hc : RigidDeep.Rigid c)
    (h : ∀ (Φ : Den W D tp → Prop) (φ : Den W D tp) (w : W), (∀ ψ, Φ ψ → P ψ w) →
      (∀ v, R w v → ∀ z, act z v → (φ z v ↔ ∀ ψ, Φ ψ → ψ z v)) → P φ w) :
    ∀ w, eval (fullStr R act P) (RigidDeep.Ax1GenR c) () w := by
  intro w φ _ hp hcj
  have ev : ∀ (ψ : Den W D tp) (v : W), eval (fullStr R act P)
      (.app (wkL (wkL (RigidDeep.setOf c))) RigidDeep.v0 : Tm [tp, tp] .s)
      ((ψ, (φ, ())) : Env W D [tp, tp]) v ↔ eval (fullStr R act P) c ((ψ, ()) : Env W D [tp]) w := by
    intro ψ v
    show eval (fullStr R act P) (wkL (wkL (RigidDeep.setOf c))) ((ψ, (φ, ())) : Env W D [tp, tp])
      ψ v ↔ _
    rw [RigidDeep.eval_wkL, RigidDeep.eval_wkL]
    exact RigidDeep.rigid_eval _ hc ((ψ, ()) : Env W D [tp]) v w
  refine h (fun ψ => eval (fullStr R act P) c ((ψ, ()) : Env W D [tp]) w) φ w
    (fun ψ hψ => hp ψ trivial ((ev ψ w).2 hψ)) ?_
  intro v hv z hz
  have ev3 : ∀ (ψ : Den W D tp) (u : W), eval (fullStr R act P)
      (.app (wkL (wkL (wkL (RigidDeep.setOf c)))) RigidDeep.v0 : Tm [tp, .e, tp] .s)
      ((ψ, (z, (φ, ()))) : Env W D [tp, .e, tp]) u ↔
      eval (fullStr R act P) c ((ψ, ()) : Env W D [tp]) w := by
    intro ψ u
    show eval (fullStr R act P) (wkL (wkL (wkL (RigidDeep.setOf c))))
      ((ψ, (z, (φ, ()))) : Env W D [tp, .e, tp]) ψ u ↔ _
    rw [RigidDeep.eval_wkL, RigidDeep.eval_wkL, RigidDeep.eval_wkL]
    exact RigidDeep.rigid_eval _ hc ((ψ, ()) : Env W D [tp]) u w
  have hz' := hcj v hv z hz
  exact ⟨fun hφ ψ hψ => hz'.1 hφ ψ trivial ((ev3 ψ v).2 hψ),
    fun hall => hz'.2 fun ψ _ hψ => hall ψ ((ev3 ψ v).1 hψ)⟩

/-- **Schema soundness for the module.** Every instance of the deep schema `Ax1GenR c`, `c` a
rigid `𝓛`-condition, holds at every world of the full structure on the module's postulates
whenever the module's `Ax1GenR` holds.  (The converse fails: the module's `Φ` ranges over sets
no `𝓛`-condition defines; that is the intended `𝓛`-reading.) -/
theorem genR_sound (c : Tm [tp] .s) (hc : RigidDeep.Rigid c) (h : _root_.Ax1GenR) :
    ∀ w, eval S (RigidDeep.Ax1GenR c) () w :=
  genR_sound_full _root_.R existsAt _root_.P c hc fun Φ φ w h1 h2 => h Φ φ w ⟨h1, h2⟩

end Programme.«20261023-0519-ontological».Run5.G.RigidMatch

#print axioms Programme.«20261023-0519-ontological».Run5.G.RigidDeep.l_r_valid
#print axioms Programme.«20261023-0519-ontological».Run5.G.RigidDeep.l_r_semantic
#print axioms Programme.«20261023-0519-ontological».Run5.G.RigidDeep.l_r_dw
#print axioms Programme.«20261023-0519-ontological».Run5.G.RigidDeep.rigid_ev
#print axioms Programme.«20261023-0519-ontological».Run5.G.RigidMatch.match_genR
#print axioms Programme.«20261023-0519-ontological».Run5.G.RigidMatch.L_R_PosGlobal_of_deep
#print axioms Programme.«20261023-0519-ontological».Run5.G.RigidMatch.L_R_of_deep
#print axioms Programme.«20261023-0519-ontological».Run5.G.RigidMatch.genR_sound_full
#print axioms Programme.«20261023-0519-ontological».Run5.G.RigidMatch.genR_sound
