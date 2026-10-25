import Programme.«20261022-0733-ontological».Run2.UniqueEss
import Programme.«20261022-0733-ontological».Run2.TwoClosedMixed

/-! # The `Closed` interface is implied by closure under terms of the object language `𝓛`

Owner note P91, item 1; arXiv 2609.36279v4, `def:lgeneral`.  An `𝓛`-general model is a Kripke
model with a domain `P_τ` for each type of `𝓛`, such that every term of `𝓛` with parameters from
the domains denotes in `P_τ`; quantifiers at types of `𝓛` range over the `P_τ`, and the
primitive equality at a lifted type is identity across all worlds (`sec:criterion`).

`Frag` below is a fragment of `𝓛` as a datatype: the four types `e` (individuals, `P_e = D`),
`σ` (propositions, `AS`), `τ = e → σ` (properties, `AT`) and `τ → σ` (world-dependent sets of
properties, `AH`); the lifted connectives `⊤`, `⊥`, `¬`, `∧`, `∨`, `→`, `□`; possibilist
quantifiers at all four types (ranging over the admitted carriers), actualist quantifiers at `e`;
the primitive equality at `e` and at `τ`; abstraction and application at `τ` and `τ → σ`; the
constant `P`.  Every former is one of `𝓛`'s, with `𝓛`'s semantics; there is no term of the world
type and no world parameter.  `LGeneral M` asks that every `Frag`-term with admitted parameters
denote an admitted object.  An `𝓛`-general model in the paper's sense satisfies it (it is closed
under more terms, at more types), so every result proved from `LGeneral` holds there.

Main results: `closed_of_lgeneral` (`LGeneral → Closed`), the extra closures used by K2, K3, K5,
K7 (`E`, `E₃`, `λz.z = y`, actuality, `φ y`, possibilist `∃y.Gy`), each read off a displayed term,
and the transfers of K1 (variants 2 and 3′) and K3 to every `LGeneral` model.  Every full model
is `LGeneral` (`lgeneral_full`), so the hypotheses are jointly satisfiable (`unitModel`). -/

namespace Programme.«20261022-0733-ontological».Run2.LGeneral

open Programme.«20261022-0733-ontological».Run2.TwoClosed Programme.«20261022-0733-ontological».Run2.DropDagger Programme.«20261022-0733-ontological».Run2.UniqueEss

/-- The four types of the fragment. -/
inductive Ty
  | e  -- individuals
  | s  -- propositions `σ`
  | p  -- properties `e → σ`
  | h  -- world-dependent sets of properties `(e → σ) → σ`
  deriving DecidableEq

variable {W D : Type}

/-- Carrier of each type (the full function space; admission is separate). -/
@[reducible] def Den (W D : Type) : Ty → Type
  | .e => D
  | .s => W → Prop
  | .p => D → W → Prop
  | .h => (D → W → Prop) → W → Prop

/-- de Bruijn variables. -/
inductive Var : List Ty → Ty → Type
  | zero {Γ t} : Var (t :: Γ) t
  | succ {Γ t u} : Var Γ t → Var (u :: Γ) t

/-- Terms of the fragment of `𝓛`. -/
inductive Tm : List Ty → Ty → Type
  | var {Γ t} : Var Γ t → Tm Γ t
  | appP {Γ} : Tm Γ .p → Tm Γ .e → Tm Γ .s
  | appH {Γ} : Tm Γ .h → Tm Γ .p → Tm Γ .s
  | lamP {Γ} : Tm (.e :: Γ) .s → Tm Γ .p
  | lamH {Γ} : Tm (.p :: Γ) .s → Tm Γ .h
  | top {Γ} : Tm Γ .s
  | bot {Γ} : Tm Γ .s
  | neg {Γ} : Tm Γ .s → Tm Γ .s
  | and {Γ} : Tm Γ .s → Tm Γ .s → Tm Γ .s
  | or {Γ} : Tm Γ .s → Tm Γ .s → Tm Γ .s
  | imp {Γ} : Tm Γ .s → Tm Γ .s → Tm Γ .s
  | box {Γ} : Tm Γ .s → Tm Γ .s
  /-- possibilist quantifiers, over the admitted carrier of the bound type -/
  | all {Γ} (a : Ty) : Tm (a :: Γ) .s → Tm Γ .s
  | ex {Γ} (a : Ty) : Tm (a :: Γ) .s → Tm Γ .s
  /-- actualist quantifiers at `e` -/
  | allE {Γ} : Tm (.e :: Γ) .s → Tm Γ .s
  | exE {Γ} : Tm (.e :: Γ) .s → Tm Γ .s
  /-- primitive equality at `e` and at `τ`: identity, the same at every world -/
  | eqE {Γ} : Tm Γ .e → Tm Γ .e → Tm Γ .s
  | eqP {Γ} : Tm Γ .p → Tm Γ .p → Tm Γ .s
  /-- the constant `P` -/
  | pos {Γ} : Tm Γ .h

/-- Environments: one value per variable. -/
def Env (W D : Type) : List Ty → Type
  | [] => Unit
  | t :: Γ => Den W D t × Env W D Γ

def Var.get : {Γ : List Ty} → {t : Ty} → Var Γ t → Env W D Γ → Den W D t
  | _, _, .zero, ρ => ρ.1
  | _, _, .succ i, ρ => i.get ρ.2

/-- Admission at each type. -/
def Adm (M : Model W D) : (t : Ty) → Den W D t → Prop
  | .e, _ => True
  | .s, q => M.AS q
  | .p, φ => M.AT φ
  | .h, Φ => M.AH Φ

def EnvAdm (M : Model W D) : (Γ : List Ty) → Env W D Γ → Prop
  | [], _ => True
  | t :: Γ, ρ => Adm M t ρ.1 ∧ EnvAdm M Γ ρ.2

/-- Denotation, with quantifiers over the admitted carriers (Henkin semantics). -/
def eval (M : Model W D) : {Γ : List Ty} → {t : Ty} → Tm Γ t → Env W D Γ → Den W D t
  | _, _, .var i, ρ => i.get ρ
  | _, _, .appP f a, ρ => eval M f ρ (eval M a ρ)
  | _, _, .appH F f, ρ => eval M F ρ (eval M f ρ)
  | _, _, .lamP b, ρ => fun d => eval M b (d, ρ)
  | _, _, .lamH b, ρ => fun φ => eval M b (φ, ρ)
  | _, _, .top, _ => fun _ => True
  | _, _, .bot, _ => fun _ => False
  | _, _, .neg a, ρ => fun w => ¬ eval M a ρ w
  | _, _, .and a b, ρ => fun w => eval M a ρ w ∧ eval M b ρ w
  | _, _, .or a b, ρ => fun w => eval M a ρ w ∨ eval M b ρ w
  | _, _, .imp a b, ρ => fun w => eval M a ρ w → eval M b ρ w
  | _, _, .box a, ρ => fun w => ∀ v, M.R w v → eval M a ρ v
  | _, _, .all a b, ρ => fun w => ∀ x, Adm M a x → eval M b (x, ρ) w
  | _, _, .ex a b, ρ => fun w => ∃ x, Adm M a x ∧ eval M b (x, ρ) w
  | _, _, .allE b, ρ => fun w => ∀ y, M.act y w → eval M b (y, ρ) w
  | _, _, .exE b, ρ => fun w => ∃ y, M.act y w ∧ eval M b (y, ρ) w
  | _, _, .eqE a b, ρ => fun _ => eval M a ρ = eval M b ρ
  | _, _, .eqP a b, ρ => fun _ => eval M a ρ = eval M b ρ
  | _, _, .pos, _ => M.P

/-- Closure under the fragment: every term with admitted parameters denotes an admitted object. -/
def LGeneral (M : Model W D) : Prop :=
  ∀ {Γ : List Ty} {t : Ty} (tm : Tm Γ t) (ρ : Env W D Γ), EnvAdm M Γ ρ → Adm M t (eval M tm ρ)

/-! ## The terms -/

open Tm

/-- `v0`, `v1`, `v2`: the innermost three variables. -/
abbrev v0 {Γ t} : Tm (t :: Γ) t := var .zero
abbrev v1 {Γ t u} : Tm (u :: t :: Γ) t := var (.succ .zero)
abbrev v2 {Γ t u u'} : Tm (u' :: u :: t :: Γ) t := var (.succ (.succ .zero))

/-- `G := λx. ∀φ. P φ → φ x`. -/
def tG {Γ} : Tm Γ .p := lamP (all .p (imp (appH pos v0) (appP v0 v1)))

/-- `E := λx. ∀φ. Ess φ x → □ ∃ᴱy. φ y`, with
`Ess φ x := φ x ∧ ∀ψ. ψ x → □ ∀ᴱy. φ y → ψ y` (variant 2). -/
def tE {Γ} : Tm Γ .p :=
  lamP (all .p (imp
    -- Ess φ x, with φ = v0, x = v1
    (and (appP v0 v1) (all .p (imp (appP v0 v2) (box (allE (imp (appP v2 v0) (appP v1 v0)))))))
    (box (exE (appP v1 v0)))))

/-- `E₃`, with `Ess₃ φ x := ∀ψ. ψ x → □ (φ ≠ ⊥ ∧ ∀ᴱy. φ y → ψ y)` (variant 3′). -/
def tE3 {Γ} : Tm Γ .p :=
  lamP (all .p (imp
    (all .p (imp (appP v0 v2)
      (box (and (neg (eqP v1 (lamP bot))) (allE (imp (appP v2 v0) (appP v1 v0)))))))
    (box (exE (appP v1 v0)))))

variable {M : Model W D} (hL : LGeneral M)

theorem eval_tG {Γ} (ρ : Env W D Γ) : eval M tG ρ = G M := rfl
theorem eval_tE {Γ} (ρ : Env W D Γ) : eval M tE ρ = E M := rfl
theorem eval_tE3 {Γ} (ρ : Env W D Γ) : eval M tE3 ρ = E3 M := rfl

include hL

/-- **Bridge.** Closure under the fragment of `𝓛` gives K1's `Closed` interface: each field is
the denotation of the displayed term (no world parameter, no world-type term). -/
theorem closed_of_lgeneral : Closed M where
  -- `λx.⊤`, `λx.⊥`
  top := hL (Γ := []) (lamP top) () trivial
  bot := hL (Γ := []) (lamP bot) () trivial
  -- `λx. ¬ φ x`
  neg := fun φ hφ => hL (Γ := [.p]) (lamP (neg (appP v1 v0))) (φ, ()) ⟨hφ, trivial⟩
  -- `λx. φ x ∧ ψ x`
  conj := fun φ ψ hφ hψ =>
    hL (Γ := [.p, .p]) (lamP (and (appP v1 v0) (appP v2 v0))) (φ, ψ, ()) ⟨hφ, hψ, trivial⟩
  -- `λx. q`
  lift := fun q hq => hL (Γ := [.s]) (lamP v1) (q, ()) ⟨hq, trivial⟩
  -- `¬ q`
  negS := fun q hq => hL (Γ := [.s]) (neg v0) (q, ()) ⟨hq, trivial⟩
  god := hL (Γ := []) tG () trivial
  -- `∃ᴱy. G y`
  exG := hL (Γ := []) (exE (appP tG v0)) () trivial
  pos := hL (Γ := []) pos () trivial
  -- `λψ'. ψ' = ψ`
  single := fun ψ hψ => hL (Γ := [.p]) (lamH (eqP v0 v1)) (ψ, ()) ⟨hψ, trivial⟩
  -- `λψ'. Φ ψ' ∨ Ψ ψ'`
  union := fun Φ Ψ hΦ hΨ =>
    hL (Γ := [.h, .h]) (lamH (or (appH v1 v0) (appH v2 v0))) (Φ, Ψ, ()) ⟨hΦ, hΨ, trivial⟩
  -- `λψ'. q ∧ Φ ψ'`
  guard := fun q Φ hq hΦ =>
    hL (Γ := [.s, .h]) (lamH (and v1 (appH v2 v0))) (q, Φ, ()) ⟨hq, hΦ, trivial⟩
  -- `∀ψ. Φ ψ → ψ = ψ₀`
  atMost := fun Φ ψ₀ hΦ hψ₀ =>
    hL (Γ := [.h, .p]) (all .p (imp (appH v1 v0) (eqP v0 v2))) (Φ, ψ₀, ()) ⟨hΦ, hψ₀, trivial⟩

/-- Necessary existence of variant 2 is admitted. -/
theorem E_adm : M.AT (E M) := hL (Γ := []) tE () trivial

/-- Necessary existence of variant 3′ (and 3) is admitted. -/
theorem E3_adm : M.AT (E3 M) := hL (Γ := []) tE3 () trivial

/-- Actuality `λz. ∃ᴱy. y = z` is admitted. -/
theorem act_adm : M.AT (fun z u => M.act z u) := by
  have h := hL (Γ := []) (lamP (exE (eqE v0 v1))) () trivial
  have he : (eval M (Γ := []) (lamP (exE (eqE v0 v1))) () : D → W → Prop) = fun z u => M.act z u := by
    funext z u
    show (∃ y, M.act y u ∧ y = z) = M.act z u
    exact propext ⟨fun ⟨_, hy, he⟩ => he ▸ hy, fun hz => ⟨z, hz, rfl⟩⟩
  exact he ▸ h

/-- K7's extra closures: `λz. z = y`, actuality, `φ y`. -/
theorem extra_of_lgeneral : Extra M where
  hid := fun y => hL (Γ := [.e]) (lamP (eqE v0 v1)) (y, ()) ⟨trivial, trivial⟩
  hact := act_adm hL
  happ := fun φ hφ y =>
    hL (Γ := [.e, .p]) (appP v1 v0) (y, φ, ()) ⟨trivial, hφ, trivial⟩

/-- K2's extra closure: possibilist `∃y. G y`. -/
theorem pexg_adm : M.AS (TwoClosedMixed.PExG M) := by
  have h := hL (Γ := []) (ex .e (appP tG v0)) () trivial
  have he : (eval M (Γ := []) (ex .e (appP tG v0)) () : W → Prop) = TwoClosedMixed.PExG M := by
    funext w
    exact propext ⟨fun ⟨y, _, hy⟩ => ⟨y, hy⟩, fun ⟨y, hy⟩ => ⟨y, trivial, hy⟩⟩
  exact he ▸ h

omit hL

/-! ## Transfer of K1 and K3 to `𝓛`-general models -/

/-- **K1, variant 2, over the fragment-closed models**: `Ax2a`, `Ax2b`, `Ax3`, `Ax4` give
`Ax1GenTwo ↔ Ax1Gen`, and `Ax1GenTwo` gives admitted modal collapse; no closure hypothesis
beyond `LGeneral`. -/
theorem k1_v2 [Nonempty D] (hL : LGeneral M) (h2a : Ax2a M) (h2b : Ax2b M) (h3 : Ax3 M)
    (h4 : Ax4 M) : (Ax1GenTwo M ↔ Ax1Gen M) ∧ (Ax1GenTwo M → MC M) :=
  ⟨equivalence (closed_of_lgeneral hL) (E_adm hL) h2a h2b h3 h4,
   mc_v2 (closed_of_lgeneral hL) (E_adm hL) h2a h2b h3 h4⟩

/-- **K1, variant 3′**, likewise. -/
theorem k1_v3 [Nonempty D] (hL : LGeneral M) (h2a : Ax2a M) (h2b : Ax2b M) (h3 : Ax3v3 M)
    (h4 : Ax4 M) : (Ax1GenTwo M ↔ Ax1Gen M) ∧ (Ax1GenTwo M → MC M) :=
  ⟨equivalence_v3 (closed_of_lgeneral hL) (E3_adm hL) h2a h2b h3 h4,
   mc_v3 (closed_of_lgeneral hL) (E3_adm hL) h2a h2b h3 h4⟩

/-- **K3 over the fragment-closed models**: variant 3 (clause in essence and `Ax4`), `Ax2a`,
`Ax3`, `Ax4c`, `Th4`, `Ax1GenTwo` give an actual God-like being at every world, with no side
condition (†) and without `Ax2b`; with `Ax2b`, admitted modal collapse. -/
theorem k3 [Nonempty W] [Nonempty D] (hL : LGeneral M) (h2a : Ax2a M) (h3 : Ax3v3 M)
    (h4 : Ax4c M) (h4' : Th4 M) (hT : Ax1GenTwo M) :
    (∀ w, ExG M w) ∧ (Ax2b M → MC M) :=
  ⟨gex (closed_of_lgeneral hL) (E3_adm hL) h2a h3 h4 h4' hT,
   fun h2b => DropDagger.mc (closed_of_lgeneral hL) (E3_adm hL) h2a h3 h4 h4' h2b hT⟩

/-! ## Full models are `𝓛`-general -/

theorem lgeneral_full (hS : ∀ q, M.AS q) (hT : ∀ φ, M.AT φ) (hH : ∀ Φ, M.AH Φ) :
    LGeneral M := by
  intro Γ t tm ρ _
  cases t
  · trivial
  · exact hS _
  · exact hT _
  · exact hH _

/-- Non-vacuity: K1's one-world full model is `𝓛`-general and satisfies every hypothesis of
`k1_v2` together with `Ax1GenTwo`. -/
theorem unitModel_lgeneral : LGeneral unitModel :=
  lgeneral_full (fun _ => trivial) (fun _ => trivial) (fun _ => trivial)

end Programme.«20261022-0733-ontological».Run2.LGeneral

#print axioms Programme.«20261022-0733-ontological».Run2.LGeneral.closed_of_lgeneral
#print axioms Programme.«20261022-0733-ontological».Run2.LGeneral.extra_of_lgeneral
#print axioms Programme.«20261022-0733-ontological».Run2.LGeneral.pexg_adm
#print axioms Programme.«20261022-0733-ontological».Run2.LGeneral.k1_v2
#print axioms Programme.«20261022-0733-ontological».Run2.LGeneral.k1_v3
#print axioms Programme.«20261022-0733-ontological».Run2.LGeneral.k3
#print axioms Programme.«20261022-0733-ontological».Run2.LGeneral.unitModel_lgeneral
