import Lean
import OpenQuestions.Ax1GenTwoVariant2

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


/-! Verbatim copy of the library's `Programme/20261022-1724-ontological/Run3/WitnessDeep.lean` (run 4: `DG`, `DW`,
`sound_v4_wt`), minus its `#print`s; the library's `Programme` modules are not prebuilt. -/

/-! # WitnessDeep.lean (th, run 3, round 10): target C (d) in deep form

Lines after this header: pr's `SepLS.lean` (K14 evidence; contains K8's `sep_not_valid_v4` and K12/K13's
`Canon`/`LS`) minus its final `#print`, then th's `WholeTerm.lean` section `Programme.ThWhole` (round 9:
`DG`, `DW`, `sound_v4_wt`, `of_DC`) minus `#print`s, both verbatim; then section `Programme.ThWit`:
the witness-only calculus `DG3` derives v4's separating sentence from every theory. -/

/-! # SepLS.lean (pr, run 3, round 9)

`DeepSep.lean` (K11, minus `#print`s) verbatim, then th's `LS.lean` from `namespace Programme.ThHenkin`
to its end (K12 completeness, LS, compactness; minus `#print`s) verbatim, then section `Programme.Run3.SepLS`:
the separating sentence has a countermodel of variant 2 with countably many worlds and countable carriers,
and no countermodel with finitely many worlds. -/

/-! # DeepSep.lean (run 3, round 7)

`DeepE.lean` (claims K8-K10) verbatim, followed by section `SepR`: v4's remarks in Example
`ex:separating` (finite models do not separate; the example's model is not a model of variant 2,
whatever `Pos` is) and the example itself as a v4 `VM`+`LGen` model. -/

/-! # Run 3, thread C: the deep calculus over v4's 𝓛-general models (one self-contained file)

Concatenation, in order, of:
1. `DeepLeib.lean` (claim K4), plus `Deriv.ren`/`Deriv.wkD` (renaming of whole derivations, with the
   new `leib` case) from the round-2 development of `DeepK.lean`;
2. the derivations of `DeepK.lean` (claim K2: run 2's K1 and K14), unchanged, now in K4's calculus;
3. th's bridge `agents/th/lean/Programme/Th/Bridge.lean` (M1 `toStr`, M2 `ofStr`, `valid_iff`),
   lines 205-606 verbatim, placed in `Programme.Run3.LX` (its copied preamble is K4's own);
4. `V4`: `sound_v4` (K4's calculus is sound over v4's def:lgeneral models), `k1_valid_v4`,
   `k14_valid_v4`;
5. round 6: `K3p` (the derivations of item 2 replayed for variant 3′, `Ax1GenTwoVariant3Plain`),
   `Conv.two_of_gen` (`Ax1Gen ⇒ Ax1GenTwo`), and in `V4`: `k3p_valid_v4`, `two_equivalent_v2`,
   `two_equivalent_v3p` (the modules' `Two_equivalent` over all v4 𝓛-general models);
6. `SepV2.lean` (claim K7), plus `sep_v4`/`sep_not_valid_v4`: the eqT-quotient of K7's structure is a
   v4 𝓛-general model of variant 2 where the separating sentence fails. -/

/-! # Deep derivations with Leibniz at every type of 𝓛; soundness over closed `eqT`-respecting structures

This file extends `DeepND.lean` (claim K1 of run 3; namespaces renamed `LX`/`HOLX`) by one rule,
`Deriv.leib`: Leibniz substitution at every type of `𝓛`, with an `𝓛`-motive and certified sides.
`soundness` now assumes `Resp S` (admitted functions respect `eqT` on admitted arguments, v4's
restriction semantics in the proof of `prop:lgeneral`); the new case uses the fundamental lemma
`fund`.  `leib_derivable`: Leibniz at `σ → σ` is derivable; `Flip.resp_needed`: over th's closed
flip structure (copied from `LeibnizGap.lean`) it fails, so `Resp` cannot be dropped;
`full_closed_resp`: the class is non-empty.  The original description of `DeepND.lean` follows.

## Deep derivations in the embedding, and soundness over 𝓛-general structures

v4 (arXiv 2609.36279v4) `prop:lgeneral` concerns a proof `π` in HOL of `⟦φ⟧` from `T`: the
embedding's world type is visible to `π`, so `π` may mention a nominal `λu. u = w`; the
proposition says that if the terms `π` uses as elements of an `𝓛`-domain are `𝓛`-terms with
`𝓛`-parameters, then `⟦φ⟧` holds in every `𝓛`-general model of `T`.

Here the HOL side is deep.  Types `HTy`: the types of `𝓛` (`L t`), the world type `w` and the
truth values `o`.  Terms `HTerm` contain the `𝓛`-level application/abstraction, `P`, world
abstraction `wabs` (so `λu. u = w` is `wabs (eq w (var 0) (var 1))`), application of a
proposition to a world (`holds`), `R`, actuality, the connectives at `o`, quantifiers and
equality at every type.  `emb` is the embedding `⟦-⟧` of `𝓛`-terms (`L.Tm`), connectives
unfolded.  Semantics: over an `L.Str` (worlds, entities, `R`, actuality, `P`, carriers `A t`
at every type of `𝓛`); quantifiers at `L t` range over `A t`, equality at `L t` is `L.eqT`
(agreement on admitted arguments), everything else standard.

`Deriv T ok` is natural deduction for this HOL with the theory `T` (a set of `𝓛`-sentences) as
axioms; its `∀`-elimination and `∃`-introduction at a type of `𝓛` require `ok t` of the instance.
`Cert t`: `t` is `emb r s` for an `𝓛`-term `s` whose parameters are mapped by `r` to variables of
`𝓛`-types.  **`soundness`**: every `Deriv T Cert` derivation is valid in every closed structure
(`L.Closed`) satisfying `T`.  `Deriv T Any` is the unrestricted calculus.

Equality substitution (`subst`) is restricted to *plain* types, where relativised equality is
identity (`e`, `σ`, `e → … → σ`, `w`, `o`); at other types of `𝓛` equality is used through
`funApp`/`funExt` only.  The β-rules, extensionality at `σ` and at arrow types of `𝓛`, and
classical logic are included. -/

/-! ## The language 𝓛 and its structures, copied from the library module
`Programme.«20261022-0733-ontological».Run2.LGeneralFull` (whose Programme modules are not built in the
mounted library); definitions unchanged, namespace changed. -/
namespace Programme.«20261022-1724-ontological».Run3.LX
inductive FTy
  | e
  | s
  | arr (a b : FTy)
  deriving DecidableEq

variable {W D : Type}

@[reducible] def Den (W D : Type) : FTy → Type
  | .e => D
  | .s => W → Prop
  | .arr a b => Den W D a → Den W D b

abbrev tp : FTy := .arr .e .s
abbrev th : FTy := .arr tp .s

/-- Pull-back along the world map `f` (with `g` used contravariantly at arrow domains). -/
def fl (f g : W → W) : (t : FTy) → Den W D t → Den W D t
  | .e, x => x
  | .s, q => fun w => q (f w)
  | .arr a b, F => fun z => fl f g b (F (fl g f a z))

theorem fl_comp : ∀ (t : FTy) (f g f' g' : W → W) (x : Den W D t),
    fl f' g' t (fl f g t x) = fl (fun w => f (f' w)) (fun w => g' (g w)) t x
  | .e, _, _, _, _, _ => rfl
  | .s, _, _, _, _, _ => rfl
  | .arr a b, f, g, f', g', F => by
      funext z
      show fl f' g' b (fl f g b (F (fl g f a (fl g' f' a z)))) = _
      rw [fl_comp a g' f' g f z, fl_comp b f g f' g']
      rfl

theorem fl_id : ∀ (t : FTy) (x : Den W D t), fl (fun w => w) (fun w => w) t x = x
  | .e, _ => rfl
  | .s, _ => rfl
  | .arr a b, F => by
      funext z
      show fl _ _ b (F (fl _ _ a z)) = F z
      rw [fl_id a z, fl_id b]

theorem fl_inv {f g : W → W} (h : ∀ w, f (g w) = w) (t : FTy) (x : Den W D t) :
    fl g f t (fl f g t x) = x := by
  rw [fl_comp]
  have e : (fun w => f (g w)) = fun w => w := funext h
  rw [e]; exact fl_id t x

/-! ## Terms -/

inductive Var : List FTy → FTy → Type
  | zero {Γ t} : Var (t :: Γ) t
  | succ {Γ t u} : Var Γ t → Var (u :: Γ) t

inductive Tm : List FTy → FTy → Type
  | var {Γ t} : Var Γ t → Tm Γ t
  | app {Γ a b} : Tm Γ (.arr a b) → Tm Γ a → Tm Γ b
  | lam {Γ a b} : Tm (a :: Γ) b → Tm Γ (.arr a b)
  | top {Γ} : Tm Γ .s
  | bot {Γ} : Tm Γ .s
  | neg {Γ} : Tm Γ .s → Tm Γ .s
  | and {Γ} : Tm Γ .s → Tm Γ .s → Tm Γ .s
  | or {Γ} : Tm Γ .s → Tm Γ .s → Tm Γ .s
  | imp {Γ} : Tm Γ .s → Tm Γ .s → Tm Γ .s
  | box {Γ} : Tm Γ .s → Tm Γ .s
  | all {Γ} (a : FTy) : Tm (a :: Γ) .s → Tm Γ .s
  | ex {Γ} (a : FTy) : Tm (a :: Γ) .s → Tm Γ .s
  | allE {Γ} : Tm (.e :: Γ) .s → Tm Γ .s
  | exE {Γ} : Tm (.e :: Γ) .s → Tm Γ .s
  | eq {Γ} (a : FTy) : Tm Γ a → Tm Γ a → Tm Γ .s
  | pos {Γ} : Tm Γ th

@[reducible] def Env (W D : Type) : List FTy → Type
  | [] => Unit
  | t :: Γ => Den W D t × Env W D Γ

def Var.get : {Γ : List FTy} → {t : FTy} → Var Γ t → Env W D Γ → Den W D t
  | _, _, .zero, ρ => ρ.1
  | _, _, .succ i, ρ => i.get ρ.2

/-- A structure for the full language: frame, actuality, positivity, carriers at every type. -/
structure Str (W D : Type) where
  R : W → W → Prop
  act : D → W → Prop
  P : Den W D th
  A : (t : FTy) → Den W D t → Prop

/-- Primitive equality: identity at `e` and `σ`, agreement on admitted arguments at arrows. -/
def eqT (S : Str W D) : (t : FTy) → Den W D t → Den W D t → Prop
  | .e, x, y => x = y
  | .s, x, y => x = y
  | .arr a b, F, G => ∀ z, S.A a z → eqT S b (F z) (G z)

def eval (S : Str W D) : {Γ : List FTy} → {t : FTy} → Tm Γ t → Env W D Γ → Den W D t
  | _, _, .var i, ρ => i.get ρ
  | _, _, .app F x, ρ => eval S F ρ (eval S x ρ)
  | _, _, .lam b, ρ => fun z => eval S b (z, ρ)
  | _, _, .top, _ => fun _ => True
  | _, _, .bot, _ => fun _ => False
  | _, _, .neg a, ρ => fun w => ¬ eval S a ρ w
  | _, _, .and a b, ρ => fun w => eval S a ρ w ∧ eval S b ρ w
  | _, _, .or a b, ρ => fun w => eval S a ρ w ∨ eval S b ρ w
  | _, _, .imp a b, ρ => fun w => eval S a ρ w → eval S b ρ w
  | _, _, .box a, ρ => fun w => ∀ v, S.R w v → eval S a ρ v
  | _, _, .all a b, ρ => fun w => ∀ x, S.A a x → eval S b (x, ρ) w
  | _, _, .ex a b, ρ => fun w => ∃ x, S.A a x ∧ eval S b (x, ρ) w
  | _, _, .allE b, ρ => fun w => ∀ y, S.act y w → eval S b (y, ρ) w
  | _, _, .exE b, ρ => fun w => ∃ y, S.act y w ∧ eval S b (y, ρ) w
  | _, _, .eq a x y, ρ => fun _ => eqT S a (eval S x ρ) (eval S y ρ)
  | _, _, .pos, _ => S.P

def EnvA (S : Str W D) : (Γ : List FTy) → Env W D Γ → Prop
  | [], _ => True
  | t :: Γ, ρ => S.A t ρ.1 ∧ EnvA S Γ ρ.2

/-- Closure of a structure under all terms. -/
def Closed (S : Str W D) : Prop :=
  ∀ {Γ : List FTy} {t : FTy} (tm : Tm Γ t) (ρ : Env W D Γ), EnvA S Γ ρ → S.A t (eval S tm ρ)

end Programme.«20261022-1724-ontological».Run3.LX

namespace Programme.«20261022-1724-ontological».Run3.HOLX

open Programme.«20261022-1724-ontological».Run3.LX

inductive HTy
  | L (t : FTy)
  | w
  | o
  deriving DecidableEq

variable {W D : Type}

@[reducible] def HDen (W D : Type) : HTy → Type
  | .L t => Den W D t
  | .w => W
  | .o => Prop

inductive HVar : List HTy → HTy → Type
  | zero {Γ a} : HVar (a :: Γ) a
  | succ {Γ a b} : HVar Γ a → HVar (b :: Γ) a

inductive HTerm : List HTy → HTy → Type
  | var {Γ a} : HVar Γ a → HTerm Γ a
  | appL {Γ a b} : HTerm Γ (.L (.arr a b)) → HTerm Γ (.L a) → HTerm Γ (.L b)
  | lamL {Γ a b} : HTerm (.L a :: Γ) (.L b) → HTerm Γ (.L (.arr a b))
  | pos {Γ} : HTerm Γ (.L th)
  | wabs {Γ} : HTerm (.w :: Γ) .o → HTerm Γ (.L .s)
  | holds {Γ} : HTerm Γ (.L .s) → HTerm Γ .w → HTerm Γ .o
  | rel {Γ} : HTerm Γ .w → HTerm Γ .w → HTerm Γ .o
  | act {Γ} : HTerm Γ (.L .e) → HTerm Γ .w → HTerm Γ .o
  | bot {Γ} : HTerm Γ .o
  | imp {Γ} : HTerm Γ .o → HTerm Γ .o → HTerm Γ .o
  | and {Γ} : HTerm Γ .o → HTerm Γ .o → HTerm Γ .o
  | or {Γ} : HTerm Γ .o → HTerm Γ .o → HTerm Γ .o
  | all {Γ} (a : HTy) : HTerm (a :: Γ) .o → HTerm Γ .o
  | ex {Γ} (a : HTy) : HTerm (a :: Γ) .o → HTerm Γ .o
  | eq {Γ} (a : HTy) : HTerm Γ a → HTerm Γ a → HTerm Γ .o

abbrev HEnv (W D : Type) (Γ : List HTy) := ∀ {a}, HVar Γ a → HDen W D a

def cons (x : HDen W D a) (ρ : HEnv W D Γ) : HEnv W D (a :: Γ)
  | _, .zero => x
  | _, .succ v => ρ v

/-- Range of a quantifier: the carrier at a type of `𝓛`, everything otherwise. -/
def Rng (S : Str W D) : (a : HTy) → HDen W D a → Prop
  | .L t, x => S.A t x
  | .w, _ => True
  | .o, _ => True

/-- Equality: relativised (`eqT`) at types of `𝓛`, identity at `w`, equivalence at `o`. -/
def EqH (S : Str W D) : (a : HTy) → HDen W D a → HDen W D a → Prop
  | .L t, x, y => eqT S t x y
  | .w, x, y => x = y
  | .o, x, y => (x ↔ y)

def heval (S : Str W D) : {Γ : List HTy} → {a : HTy} → HTerm Γ a → HEnv W D Γ → HDen W D a
  | _, _, .var v, ρ => ρ v
  | _, _, .appL f x, ρ => heval S f ρ (heval S x ρ)
  | _, _, .lamL b, ρ => fun z => heval S b (cons z ρ)
  | _, _, .pos, _ => S.P
  | _, _, .wabs φ, ρ => fun u => heval S φ (cons (a := .w) u ρ)
  | _, _, .holds p i, ρ => heval S p ρ (heval S i ρ)
  | _, _, .rel i j, ρ => S.R (heval S i ρ) (heval S j ρ)
  | _, _, .act x i, ρ => S.act (heval S x ρ) (heval S i ρ)
  | _, _, .bot, _ => False
  | _, _, .imp p q, ρ => heval S p ρ → heval S q ρ
  | _, _, .and p q, ρ => heval S p ρ ∧ heval S q ρ
  | _, _, .or p q, ρ => heval S p ρ ∨ heval S q ρ
  | _, _, .all a p, ρ => ∀ x, Rng S a x → heval S p (cons x ρ)
  | _, _, .ex a p, ρ => ∃ x, Rng S a x ∧ heval S p (cons x ρ)
  | _, _, .eq a s t, ρ => EqH S a (heval S s ρ) (heval S t ρ)

/-! ## Renaming and substitution -/

abbrev HRen (Γ Δ : List HTy) := ∀ {a}, HVar Γ a → HVar Δ a

def liftR (r : HRen Γ Δ) : HRen (a :: Γ) (a :: Δ)
  | _, .zero => .zero
  | _, .succ v => .succ (r v)

def rename : {Γ Δ : List HTy} → {a : HTy} → HRen Γ Δ → HTerm Γ a → HTerm Δ a
  | _, _, _, r, .var v => .var (r v)
  | _, _, _, r, .appL f x => .appL (rename r f) (rename r x)
  | _, _, _, r, .lamL b => .lamL (rename (liftR r) b)
  | _, _, _, _, .pos => .pos
  | _, _, _, r, .wabs φ => .wabs (rename (liftR r) φ)
  | _, _, _, r, .holds p i => .holds (rename r p) (rename r i)
  | _, _, _, r, .rel i j => .rel (rename r i) (rename r j)
  | _, _, _, r, .act x i => .act (rename r x) (rename r i)
  | _, _, _, _, .bot => .bot
  | _, _, _, r, .imp p q => .imp (rename r p) (rename r q)
  | _, _, _, r, .and p q => .and (rename r p) (rename r q)
  | _, _, _, r, .or p q => .or (rename r p) (rename r q)
  | _, _, _, r, .all a p => .all a (rename (liftR r) p)
  | _, _, _, r, .ex a p => .ex a (rename (liftR r) p)
  | _, _, _, r, .eq a s t => .eq a (rename r s) (rename r t)

theorem cons_liftR (r : HRen Γ Δ) (ρ : HEnv W D Δ) (x : HDen W D a) :
    (fun {b} (v : HVar (a :: Γ) b) => cons x ρ (liftR r v)) =
    (fun {b} (v : HVar (a :: Γ) b) => cons x (fun u => ρ (r u)) v) := by
  funext b v; cases v <;> rfl

theorem heval_rename (S : Str W D) : ∀ {Γ Δ a} (t : HTerm Γ a) (r : HRen Γ Δ) (ρ : HEnv W D Δ),
    heval S (rename r t) ρ = heval S t (fun v => ρ (r v))
  | _, _, _, .var _, _, _ => rfl
  | _, _, _, .appL f x, r, ρ => by
      simp only [rename, heval, heval_rename S f r ρ, heval_rename S x r ρ]
  | _, _, _, .lamL b, r, ρ => by
      funext z; simp only [rename, heval, heval_rename S b, cons_liftR]
  | _, _, _, .pos, _, _ => rfl
  | _, _, _, .wabs φ, r, ρ => by
      funext z; simp only [rename, heval, heval_rename S φ, cons_liftR]
  | _, _, _, .holds p i, r, ρ => by
      simp only [rename, heval, heval_rename S p r ρ, heval_rename S i r ρ]
  | _, _, _, .rel i j, r, ρ => by
      simp only [rename, heval, heval_rename S i r ρ, heval_rename S j r ρ]
  | _, _, _, .act x i, r, ρ => by
      simp only [rename, heval, heval_rename S x r ρ, heval_rename S i r ρ]
  | _, _, _, .bot, _, _ => rfl
  | _, _, _, .imp p q, r, ρ => by
      simp only [rename, heval, heval_rename S p r ρ, heval_rename S q r ρ]
  | _, _, _, .and p q, r, ρ => by
      simp only [rename, heval, heval_rename S p r ρ, heval_rename S q r ρ]
  | _, _, _, .or p q, r, ρ => by
      simp only [rename, heval, heval_rename S p r ρ, heval_rename S q r ρ]
  | _, _, _, .all a p, r, ρ => by
      simp only [rename, heval, heval_rename S p, cons_liftR]
  | _, _, _, .ex a p, r, ρ => by
      simp only [rename, heval, heval_rename S p, cons_liftR]
  | _, _, _, .eq a s t, r, ρ => by
      simp only [rename, heval, heval_rename S s r ρ, heval_rename S t r ρ]

abbrev HSub (Γ Δ : List HTy) := ∀ {a}, HVar Γ a → HTerm Δ a

def wk (t : HTerm Γ a) : HTerm (b :: Γ) a := rename (fun v => .succ v) t

def liftS (s : HSub Γ Δ) : HSub (a :: Γ) (a :: Δ)
  | _, .zero => .var .zero
  | _, .succ v => wk (s v)

def subst : {Γ Δ : List HTy} → {a : HTy} → HSub Γ Δ → HTerm Γ a → HTerm Δ a
  | _, _, _, s, .var v => s v
  | _, _, _, s, .appL f x => .appL (subst s f) (subst s x)
  | _, _, _, s, .lamL b => .lamL (subst (liftS s) b)
  | _, _, _, _, .pos => .pos
  | _, _, _, s, .wabs φ => .wabs (subst (liftS s) φ)
  | _, _, _, s, .holds p i => .holds (subst s p) (subst s i)
  | _, _, _, s, .rel i j => .rel (subst s i) (subst s j)
  | _, _, _, s, .act x i => .act (subst s x) (subst s i)
  | _, _, _, _, .bot => .bot
  | _, _, _, s, .imp p q => .imp (subst s p) (subst s q)
  | _, _, _, s, .and p q => .and (subst s p) (subst s q)
  | _, _, _, s, .or p q => .or (subst s p) (subst s q)
  | _, _, _, s, .all a p => .all a (subst (liftS s) p)
  | _, _, _, s, .ex a p => .ex a (subst (liftS s) p)
  | _, _, _, s, .eq a u v => .eq a (subst s u) (subst s v)

theorem cons_liftS (S : Str W D) (s : HSub Γ Δ) (ρ : HEnv W D Δ) (x : HDen W D a) :
    (fun {b} (v : HVar (a :: Γ) b) => heval S (liftS s v) (cons x ρ)) =
    (fun {b} (v : HVar (a :: Γ) b) => cons x (fun u => heval S (s u) ρ) v) := by
  funext b v
  cases v with
  | zero => rfl
  | succ v => simp only [liftS, wk, heval_rename]; rfl

theorem heval_subst (S : Str W D) : ∀ {Γ Δ a} (t : HTerm Γ a) (s : HSub Γ Δ) (ρ : HEnv W D Δ),
    heval S (subst s t) ρ = heval S t (fun v => heval S (s v) ρ)
  | _, _, _, .var _, _, _ => rfl
  | _, _, _, .appL f x, s, ρ => by
      simp only [subst, heval, heval_subst S f s ρ, heval_subst S x s ρ]
  | _, _, _, .lamL b, s, ρ => by
      funext z; simp only [subst, heval, heval_subst S b, cons_liftS]
  | _, _, _, .pos, _, _ => rfl
  | _, _, _, .wabs φ, s, ρ => by
      funext z; simp only [subst, heval, heval_subst S φ, cons_liftS]
  | _, _, _, .holds p i, s, ρ => by
      simp only [subst, heval, heval_subst S p s ρ, heval_subst S i s ρ]
  | _, _, _, .rel i j, s, ρ => by
      simp only [subst, heval, heval_subst S i s ρ, heval_subst S j s ρ]
  | _, _, _, .act x i, s, ρ => by
      simp only [subst, heval, heval_subst S x s ρ, heval_subst S i s ρ]
  | _, _, _, .bot, _, _ => rfl
  | _, _, _, .imp p q, s, ρ => by
      simp only [subst, heval, heval_subst S p s ρ, heval_subst S q s ρ]
  | _, _, _, .and p q, s, ρ => by
      simp only [subst, heval, heval_subst S p s ρ, heval_subst S q s ρ]
  | _, _, _, .or p q, s, ρ => by
      simp only [subst, heval, heval_subst S p s ρ, heval_subst S q s ρ]
  | _, _, _, .all a p, s, ρ => by
      simp only [subst, heval, heval_subst S p, cons_liftS]
  | _, _, _, .ex a p, s, ρ => by
      simp only [subst, heval, heval_subst S p, cons_liftS]
  | _, _, _, .eq a u v, s, ρ => by
      simp only [subst, heval, heval_subst S u s ρ, heval_subst S v s ρ]

/-- The substitution `[t/0]`. -/
def sub0 (t : HTerm Γ a) : HSub (a :: Γ) Γ
  | _, .zero => t
  | _, .succ v => .var v

def inst (p : HTerm (a :: Γ) b) (t : HTerm Γ a) : HTerm Γ b := subst (sub0 t) p

theorem heval_inst (S : Str W D) (p : HTerm (a :: Γ) b) (t : HTerm Γ a) (ρ : HEnv W D Γ) :
    heval S (inst p t) ρ = heval S p (cons (heval S t ρ) ρ) := by
  rw [inst, heval_subst]
  congr 1
  funext c v; cases v <;> rfl

theorem heval_wk (S : Str W D) (t : HTerm Γ a) (x : HDen W D b) (ρ : HEnv W D Γ) :
    heval S (wk t) (cons x ρ) = heval S t ρ := by
  rw [wk, heval_rename]; rfl

/-! ## The embedding of `𝓛` -/

abbrev LRen (Γ' : List FTy) (Γ : List HTy) := ∀ {t}, Var Γ' t → HVar Γ (.L t)

def liftL (r : LRen Γ' Γ) : LRen (a :: Γ') (.L a :: Γ)
  | _, .zero => .zero
  | _, .succ v => .succ (r v)

def shL (r : LRen Γ' Γ) : LRen Γ' (b :: Γ) := fun v => .succ (r v)

/-- `⟦-⟧`, the connectives unfolded at a fresh world variable. -/
def emb : {Γ' : List FTy} → {Γ : List HTy} → {t : FTy} → LRen Γ' Γ → Tm Γ' t → HTerm Γ (.L t)
  | _, _, _, r, .var i => .var (r i)
  | _, _, _, r, .app F x => .appL (emb r F) (emb r x)
  | _, _, _, r, .lam b => .lamL (emb (liftL r) b)
  | _, _, _, _, .top => .wabs (.imp .bot .bot)
  | _, _, _, _, .bot => .wabs .bot
  | _, _, _, r, .neg x => .wabs (.imp (.holds (emb (shL r) x) (.var .zero)) .bot)
  | _, _, _, r, .and x y => .wabs (.and (.holds (emb (shL r) x) (.var .zero))
      (.holds (emb (shL r) y) (.var .zero)))
  | _, _, _, r, .or x y => .wabs (.or (.holds (emb (shL r) x) (.var .zero))
      (.holds (emb (shL r) y) (.var .zero)))
  | _, _, _, r, .imp x y => .wabs (.imp (.holds (emb (shL r) x) (.var .zero))
      (.holds (emb (shL r) y) (.var .zero)))
  | _, _, _, r, .box x => .wabs (.all .w (.imp (.rel (.var (.succ .zero)) (.var .zero))
      (.holds (emb (shL (shL r)) x) (.var .zero))))
  | _, _, _, r, .all a b => .wabs (.all (.L a) (.holds (emb (liftL (shL r)) b) (.var (.succ .zero))))
  | _, _, _, r, .ex a b => .wabs (.ex (.L a) (.holds (emb (liftL (shL r)) b) (.var (.succ .zero))))
  | _, _, _, r, .allE b => .wabs (.all (.L .e) (.imp (.act (.var .zero) (.var (.succ .zero)))
      (.holds (emb (liftL (shL r)) b) (.var (.succ .zero)))))
  | _, _, _, r, .exE b => .wabs (.ex (.L .e) (.and (.act (.var .zero) (.var (.succ .zero)))
      (.holds (emb (liftL (shL r)) b) (.var (.succ .zero)))))
  | _, _, _, r, .eq a x y => .wabs (.eq (.L a) (emb (shL r) x) (emb (shL r) y))
  | _, _, _, _, .pos => .pos

/-- The `𝓛`-environment read off a HOL environment through `r`. -/
def pull : {Γ' : List FTy} → LRen Γ' Γ → HEnv W D Γ → Env W D Γ'
  | [], _, _ => ()
  | _ :: _, r, ρ => (ρ (r .zero), pull (fun v => r (.succ v)) ρ)

theorem get_pull : ∀ {Γ' t} (r : LRen Γ' Γ) (ρ : HEnv W D Γ) (i : Var Γ' t),
    i.get (pull r ρ) = ρ (r i)
  | _ :: _, _, _, _, .zero => rfl
  | _ :: _, _, r, ρ, .succ i => get_pull (fun v => r (.succ v)) ρ i

theorem pull_congr : ∀ {Γ' : List FTy} {Γ Δ : List HTy} (r : LRen Γ' Γ) (r' : LRen Γ' Δ)
    (ρ : HEnv W D Γ) (ρ' : HEnv W D Δ), (∀ {t} (i : Var Γ' t), ρ (r i) = ρ' (r' i)) →
    pull r ρ = pull r' ρ'
  | [], _, _, _, _, _, _, _ => rfl
  | _ :: _, _, _, r, r', ρ, ρ', h => by
      exact Prod.ext (h .zero) (pull_congr (fun v => r (.succ v)) (fun v => r' (.succ v)) ρ ρ'
        (fun i => h (.succ i)))

theorem pull_liftL (r : LRen Γ' Γ) (ρ : HEnv W D Γ) (z : Den W D a) :
    pull (liftL r) (cons (a := .L a) z ρ) = (z, pull r ρ) := by
  exact Prod.ext rfl (pull_congr _ r _ ρ (fun _ => rfl))

theorem pull_shL (r : LRen Γ' Γ) (ρ : HEnv W D Γ) (x : HDen W D b) :
    pull (shL r) (cons x ρ) = pull r ρ :=
  pull_congr _ r _ ρ (fun _ => rfl)

/-- **Agreement**: the embedding evaluates as the `𝓛`-term. -/
theorem heval_emb (S : Str W D) (hE : ∀ x, S.A .e x) : ∀ {Γ' Γ t} (r : LRen Γ' Γ) (tm : Tm Γ' t) (ρ : HEnv W D Γ),
    heval S (emb r tm) ρ = eval S tm (pull r ρ)
  | _, _, _, r, .var i, ρ => (get_pull r ρ i).symm
  | _, _, _, r, .app F x, ρ => by
      simp only [emb, heval, eval, heval_emb S hE r F ρ, heval_emb S hE r x ρ]
  | _, _, _, r, .lam b, ρ => by
      funext z; simp only [emb, heval, eval, heval_emb S hE _ b, pull_liftL]
  | _, _, _, _, .top, _ => by funext u; simp [emb, heval, eval]
  | _, _, _, _, .bot, _ => rfl
  | _, _, _, r, .neg x, ρ => by
      funext u; simp only [emb, heval, eval, heval_emb S hE _ x, pull_shL]; rfl
  | _, _, _, r, .and x y, ρ => by
      funext u; simp only [emb, heval, eval, heval_emb S hE _ x, heval_emb S hE _ y, pull_shL]; rfl
  | _, _, _, r, .or x y, ρ => by
      funext u; simp only [emb, heval, eval, heval_emb S hE _ x, heval_emb S hE _ y, pull_shL]; rfl
  | _, _, _, r, .imp x y, ρ => by
      funext u; simp only [emb, heval, eval, heval_emb S hE _ x, heval_emb S hE _ y, pull_shL]; rfl
  | _, _, _, r, .box x, ρ => by
      funext u; simp [emb, heval, eval, heval_emb S hE _ x, pull_shL, Rng, cons]
  | _, _, _, r, .all a b, ρ => by
      funext u; simp only [emb, heval, eval, heval_emb S hE _ b, pull_liftL, pull_shL, Rng]; rfl
  | _, _, _, r, .ex a b, ρ => by
      funext u; simp only [emb, heval, eval, heval_emb S hE _ b, pull_liftL, pull_shL, Rng]; rfl
  | _, _, _, r, .allE b, ρ => by
      funext u
      simp [emb, heval, eval, heval_emb S hE _ b, pull_liftL, pull_shL, Rng, cons, hE]
  | _, _, _, r, .exE b, ρ => by
      funext u
      simp [emb, heval, eval, heval_emb S hE _ b, pull_liftL, pull_shL, Rng, cons, hE]
  | _, _, _, r, .eq a x y, ρ => by
      funext u; simp only [emb, heval, eval, heval_emb S hE _ x, heval_emb S hE _ y, pull_shL]; rfl
  | _, _, _, _, .pos, _ => rfl


/-! ## Equality -/

theorem eqT_refl (S : Str W D) : ∀ (t : FTy) (x : Den W D t), eqT S t x x
  | .e, _ => rfl
  | .s, _ => rfl
  | .arr _ b, F => fun z _ => eqT_refl S b (F z)

theorem eqT_symm (S : Str W D) : ∀ (t : FTy) {x y : Den W D t}, eqT S t x y → eqT S t y x
  | .e, _, _, h => h.symm
  | .s, _, _, h => h.symm
  | .arr _ b, _, _, h => fun z hz => eqT_symm S b (h z hz)

theorem eqT_trans (S : Str W D) : ∀ (t : FTy) {x y z : Den W D t},
    eqT S t x y → eqT S t y z → eqT S t x z
  | .e, _, _, _, h, k => h.trans k
  | .s, _, _, _, h, k => h.trans k
  | .arr _ b, _, _, _, h, k => fun z hz => eqT_trans S b (h z hz) (k z hz)

theorem EqH_refl (S : Str W D) : ∀ (a : HTy) (x : HDen W D a), EqH S a x x
  | .L t, x => eqT_refl S t x
  | .w, _ => rfl
  | .o, _ => Iff.rfl

theorem EqH_symm (S : Str W D) : ∀ (a : HTy) {x y : HDen W D a}, EqH S a x y → EqH S a y x
  | .L t, _, _, h => eqT_symm S t h
  | .w, _, _, h => h.symm
  | .o, _, _, h => h.symm

theorem EqH_trans (S : Str W D) : ∀ (a : HTy) {x y z : HDen W D a},
    EqH S a x y → EqH S a y z → EqH S a x z
  | .L t, _, _, _, h, k => eqT_trans S t h k
  | .w, _, _, _, h, k => h.trans k
  | .o, _, _, _, h, k => h.trans k

/-- Types at which relativised equality is identity (when every entity is admitted). -/
def plainF : FTy → Bool
  | .e => true
  | .s => true
  | .arr .e b => plainF b
  | .arr _ _ => false

def plain : HTy → Bool
  | .L t => plainF t
  | .w => true
  | .o => true

theorem eqT_plain (S : Str W D) (hE : ∀ x, S.A .e x) :
    ∀ (t : FTy), plainF t = true → ∀ {x y : Den W D t}, eqT S t x y → x = y
  | .e, _, _, _, h => h
  | .s, _, _, _, h => h
  | .arr .e b, hp, _, _, h => funext fun z => eqT_plain S hE b hp (h z (hE z))
  | .arr .s _, hp, _, _, _ => by simp [plainF] at hp
  | .arr (.arr _ _) _, hp, _, _, _ => by simp [plainF] at hp

theorem EqH_plain (S : Str W D) (hE : ∀ x, S.A .e x) :
    ∀ (a : HTy), plain a = true → ∀ {x y : HDen W D a}, EqH S a x y → x = y
  | .L t, hp, _, _, h => eqT_plain S hE t hp h
  | .w, _, _, _, h => h
  | .o, _, _, _, h => propext h


/-! ## Substitution algebra (HOL side) -/

theorem rename_rename : ∀ {Γ Δ Θ a} (t : HTerm Γ a) (r : HRen Γ Δ) (r' : HRen Δ Θ) (r'' : HRen Γ Θ),
    (∀ {b} (v : HVar Γ b), r' (r v) = r'' v) → rename r' (rename r t) = rename r'' t := by
  intro Γ Δ Θ a t
  induction t generalizing Δ Θ with
  | var v => intro r r' r'' h; simp only [rename, h]
  | appL f x ihf ihx => intro r r' r'' h; simp only [rename, ihf r r' r'' h, ihx r r' r'' h]
  | lamL b ih =>
      intro r r' r'' h; simp only [rename]
      rw [ih (liftR r) (liftR r') (liftR r'') (fun v => by cases v <;> simp [liftR, h])]
  | pos => intro _ _ _ _; rfl
  | wabs φ ih =>
      intro r r' r'' h; simp only [rename]
      rw [ih (liftR r) (liftR r') (liftR r'') (fun v => by cases v <;> simp [liftR, h])]
  | holds p i ihp ihi => intro r r' r'' h; simp only [rename, ihp r r' r'' h, ihi r r' r'' h]
  | rel i j ihi ihj => intro r r' r'' h; simp only [rename, ihi r r' r'' h, ihj r r' r'' h]
  | act x i ihx ihi => intro r r' r'' h; simp only [rename, ihx r r' r'' h, ihi r r' r'' h]
  | bot => intro _ _ _ _; rfl
  | imp p q ihp ihq => intro r r' r'' h; simp only [rename, ihp r r' r'' h, ihq r r' r'' h]
  | and p q ihp ihq => intro r r' r'' h; simp only [rename, ihp r r' r'' h, ihq r r' r'' h]
  | or p q ihp ihq => intro r r' r'' h; simp only [rename, ihp r r' r'' h, ihq r r' r'' h]
  | all a φ ih =>
      intro r r' r'' h; simp only [rename]
      rw [ih (liftR r) (liftR r') (liftR r'') (fun v => by cases v <;> simp [liftR, h])]
  | ex a φ ih =>
      intro r r' r'' h; simp only [rename]
      rw [ih (liftR r) (liftR r') (liftR r'') (fun v => by cases v <;> simp [liftR, h])]
  | eq a x y ihx ihy => intro r r' r'' h; simp only [rename, ihx r r' r'' h, ihy r r' r'' h]

theorem subst_rename : ∀ {Γ Δ Θ a} (t : HTerm Γ a) (r : HRen Γ Δ) (s : HSub Δ Θ) (s' : HSub Γ Θ),
    (∀ {b} (v : HVar Γ b), s (r v) = s' v) → subst s (rename r t) = subst s' t := by
  intro Γ Δ Θ a t
  induction t generalizing Δ Θ with
  | var v => intro r s s' h; simp only [rename, subst, h]
  | appL f x ihf ihx => intro r s s' h; simp only [rename, subst, ihf r s s' h, ihx r s s' h]
  | lamL b ih =>
      intro r s s' h; simp only [rename, subst]
      rw [ih (liftR r) (liftS s) (liftS s') (fun v => by cases v <;> simp [liftR, liftS, h])]
  | pos => intro _ _ _ _; rfl
  | wabs φ ih =>
      intro r s s' h; simp only [rename, subst]
      rw [ih (liftR r) (liftS s) (liftS s') (fun v => by cases v <;> simp [liftR, liftS, h])]
  | holds p i ihp ihi => intro r s s' h; simp only [rename, subst, ihp r s s' h, ihi r s s' h]
  | rel i j ihi ihj => intro r s s' h; simp only [rename, subst, ihi r s s' h, ihj r s s' h]
  | act x i ihx ihi => intro r s s' h; simp only [rename, subst, ihx r s s' h, ihi r s s' h]
  | bot => intro _ _ _ _; rfl
  | imp p q ihp ihq => intro r s s' h; simp only [rename, subst, ihp r s s' h, ihq r s s' h]
  | and p q ihp ihq => intro r s s' h; simp only [rename, subst, ihp r s s' h, ihq r s s' h]
  | or p q ihp ihq => intro r s s' h; simp only [rename, subst, ihp r s s' h, ihq r s s' h]
  | all a φ ih =>
      intro r s s' h; simp only [rename, subst]
      rw [ih (liftR r) (liftS s) (liftS s') (fun v => by cases v <;> simp [liftR, liftS, h])]
  | ex a φ ih =>
      intro r s s' h; simp only [rename, subst]
      rw [ih (liftR r) (liftS s) (liftS s') (fun v => by cases v <;> simp [liftR, liftS, h])]
  | eq a x y ihx ihy => intro r s s' h; simp only [rename, subst, ihx r s s' h, ihy r s s' h]

theorem rename_subst : ∀ {Γ Δ Θ a} (t : HTerm Γ a) (s : HSub Γ Δ) (r : HRen Δ Θ) (s' : HSub Γ Θ),
    (∀ {b} (v : HVar Γ b), rename r (s v) = s' v) → rename r (subst s t) = subst s' t := by
  intro Γ Δ Θ a t
  induction t generalizing Δ Θ with
  | var v => intro s r s' h; simp only [subst, h]
  | appL f x ihf ihx => intro s r s' h; simp only [rename, subst, ihf s r s' h, ihx s r s' h]
  | lamL b ih =>
      intro s r s' h; simp only [rename, subst]
      rw [ih (liftS s) (liftR r) (liftS s') (fun v => by
        cases v with
        | zero => rfl
        | succ v =>
          simp only [liftS, wk]; rw [← h]
          rw [rename_rename _ _ _ (fun v => .succ (r v)) (fun _ => rfl)]
          exact rename_rename _ _ _ _ (fun _ => rfl))]
  | pos => intro _ _ _ _; rfl
  | wabs φ ih =>
      intro s r s' h; simp only [rename, subst]
      rw [ih (liftS s) (liftR r) (liftS s') (fun v => by
        cases v with
        | zero => rfl
        | succ v =>
          simp only [liftS, wk]; rw [← h]
          rw [rename_rename _ _ _ (fun v => .succ (r v)) (fun _ => rfl)]
          exact rename_rename _ _ _ _ (fun _ => rfl))]
  | holds p i ihp ihi => intro s r s' h; simp only [rename, subst, ihp s r s' h, ihi s r s' h]
  | rel i j ihi ihj => intro s r s' h; simp only [rename, subst, ihi s r s' h, ihj s r s' h]
  | act x i ihx ihi => intro s r s' h; simp only [rename, subst, ihx s r s' h, ihi s r s' h]
  | bot => intro _ _ _ _; rfl
  | imp p q ihp ihq => intro s r s' h; simp only [rename, subst, ihp s r s' h, ihq s r s' h]
  | and p q ihp ihq => intro s r s' h; simp only [rename, subst, ihp s r s' h, ihq s r s' h]
  | or p q ihp ihq => intro s r s' h; simp only [rename, subst, ihp s r s' h, ihq s r s' h]
  | all a φ ih =>
      intro s r s' h; simp only [rename, subst]
      rw [ih (liftS s) (liftR r) (liftS s') (fun v => by
        cases v with
        | zero => rfl
        | succ v =>
          simp only [liftS, wk]; rw [← h]
          rw [rename_rename _ _ _ (fun v => .succ (r v)) (fun _ => rfl)]
          exact rename_rename _ _ _ _ (fun _ => rfl))]
  | ex a φ ih =>
      intro s r s' h; simp only [rename, subst]
      rw [ih (liftS s) (liftR r) (liftS s') (fun v => by
        cases v with
        | zero => rfl
        | succ v =>
          simp only [liftS, wk]; rw [← h]
          rw [rename_rename _ _ _ (fun v => .succ (r v)) (fun _ => rfl)]
          exact rename_rename _ _ _ _ (fun _ => rfl))]
  | eq a x y ihx ihy => intro s r s' h; simp only [rename, subst, ihx s r s' h, ihy s r s' h]

theorem subst_subst : ∀ {Γ Δ Θ a} (t : HTerm Γ a) (s : HSub Γ Δ) (s' : HSub Δ Θ) (s'' : HSub Γ Θ),
    (∀ {b} (v : HVar Γ b), subst s' (s v) = s'' v) → subst s' (subst s t) = subst s'' t := by
  intro Γ Δ Θ a t
  induction t generalizing Δ Θ with
  | var v => intro s s' s'' h; simp only [subst, h]
  | appL f x ihf ihx => intro s s' s'' h; simp only [subst, ihf s s' s'' h, ihx s s' s'' h]
  | lamL b ih =>
      intro s s' s'' h; simp only [subst]
      rw [ih (liftS s) (liftS s') (liftS s'') (fun v => by
        cases v with
        | zero => rfl
        | succ v =>
          simp only [liftS, wk]; rw [← h]
          rw [subst_rename _ _ _ (fun v => wk (s' v)) (fun _ => rfl),
            rename_subst _ _ _ (fun v => wk (s' v)) (fun _ => rfl)])]
  | pos => intro _ _ _ _; rfl
  | wabs φ ih =>
      intro s s' s'' h; simp only [subst]
      rw [ih (liftS s) (liftS s') (liftS s'') (fun v => by
        cases v with
        | zero => rfl
        | succ v =>
          simp only [liftS, wk]; rw [← h]
          rw [subst_rename _ _ _ (fun v => wk (s' v)) (fun _ => rfl),
            rename_subst _ _ _ (fun v => wk (s' v)) (fun _ => rfl)])]
  | holds p i ihp ihi => intro s s' s'' h; simp only [subst, ihp s s' s'' h, ihi s s' s'' h]
  | rel i j ihi ihj => intro s s' s'' h; simp only [subst, ihi s s' s'' h, ihj s s' s'' h]
  | act x i ihx ihi => intro s s' s'' h; simp only [subst, ihx s s' s'' h, ihi s s' s'' h]
  | bot => intro _ _ _ _; rfl
  | imp p q ihp ihq => intro s s' s'' h; simp only [subst, ihp s s' s'' h, ihq s s' s'' h]
  | and p q ihp ihq => intro s s' s'' h; simp only [subst, ihp s s' s'' h, ihq s s' s'' h]
  | or p q ihp ihq => intro s s' s'' h; simp only [subst, ihp s s' s'' h, ihq s s' s'' h]
  | all a φ ih =>
      intro s s' s'' h; simp only [subst]
      rw [ih (liftS s) (liftS s') (liftS s'') (fun v => by
        cases v with
        | zero => rfl
        | succ v =>
          simp only [liftS, wk]; rw [← h]
          rw [subst_rename _ _ _ (fun v => wk (s' v)) (fun _ => rfl),
            rename_subst _ _ _ (fun v => wk (s' v)) (fun _ => rfl)])]
  | ex a φ ih =>
      intro s s' s'' h; simp only [subst]
      rw [ih (liftS s) (liftS s') (liftS s'') (fun v => by
        cases v with
        | zero => rfl
        | succ v =>
          simp only [liftS, wk]; rw [← h]
          rw [subst_rename _ _ _ (fun v => wk (s' v)) (fun _ => rfl),
            rename_subst _ _ _ (fun v => wk (s' v)) (fun _ => rfl)])]
  | eq a x y ihx ihy => intro s s' s'' h; simp only [subst, ihx s s' s'' h, ihy s s' s'' h]

theorem subst_id : ∀ {Γ a} (t : HTerm Γ a) (s : HSub Γ Γ),
    (∀ {b} (v : HVar Γ b), s v = .var v) → subst s t = t := by
  intro Γ a t
  induction t with
  | var v => intro s h; simp only [subst, h]
  | appL f x ihf ihx => intro s h; simp only [subst, ihf s h, ihx s h]
  | lamL b ih => intro s h; simp only [subst]; rw [ih (liftS s) (fun v => by cases v <;> simp [liftS, h, wk, rename])]
  | pos => intro _ _; rfl
  | wabs φ ih => intro s h; simp only [subst]; rw [ih (liftS s) (fun v => by cases v <;> simp [liftS, h, wk, rename])]
  | holds p i ihp ihi => intro s h; simp only [subst, ihp s h, ihi s h]
  | rel i j ihi ihj => intro s h; simp only [subst, ihi s h, ihj s h]
  | act x i ihx ihi => intro s h; simp only [subst, ihx s h, ihi s h]
  | bot => intro _ _; rfl
  | imp p q ihp ihq => intro s h; simp only [subst, ihp s h, ihq s h]
  | and p q ihp ihq => intro s h; simp only [subst, ihp s h, ihq s h]
  | or p q ihp ihq => intro s h; simp only [subst, ihp s h, ihq s h]
  | all a φ ih => intro s h; simp only [subst]; rw [ih (liftS s) (fun v => by cases v <;> simp [liftS, h, wk, rename])]
  | ex a φ ih => intro s h; simp only [subst]; rw [ih (liftS s) (fun v => by cases v <;> simp [liftS, h, wk, rename])]
  | eq a x y ihx ihy => intro s h; simp only [subst, ihx s h, ihy s h]

theorem inst_wk (t : HTerm Γ a) (x : HTerm Γ b) : inst (wk t) x = t := by
  rw [inst, wk, subst_rename _ _ (sub0 x) (fun v => .var v) (fun _ => rfl), subst_id _ _ (fun _ => rfl)]


/-! ## Substitution in `𝓛`, and the embedding commutes with renaming and substitution -/

abbrev RenL (Γ Δ : List FTy) := ∀ {t}, Var Γ t → Var Δ t

def liftRL (r : RenL Γ Δ) : RenL (a :: Γ) (a :: Δ)
  | _, .zero => .zero
  | _, .succ v => .succ (r v)

def renameL : {Γ Δ : List FTy} → {t : FTy} → RenL Γ Δ → Tm Γ t → Tm Δ t
  | _, _, _, r, .var i => .var (r i)
  | _, _, _, r, .app F x => .app (renameL r F) (renameL r x)
  | _, _, _, r, .lam b => .lam (renameL (liftRL r) b)
  | _, _, _, _, .top => .top
  | _, _, _, _, .bot => .bot
  | _, _, _, r, .neg x => .neg (renameL r x)
  | _, _, _, r, .and x y => .and (renameL r x) (renameL r y)
  | _, _, _, r, .or x y => .or (renameL r x) (renameL r y)
  | _, _, _, r, .imp x y => .imp (renameL r x) (renameL r y)
  | _, _, _, r, .box x => .box (renameL r x)
  | _, _, _, r, .all a b => .all a (renameL (liftRL r) b)
  | _, _, _, r, .ex a b => .ex a (renameL (liftRL r) b)
  | _, _, _, r, .allE b => .allE (renameL (liftRL r) b)
  | _, _, _, r, .exE b => .exE (renameL (liftRL r) b)
  | _, _, _, r, .eq a x y => .eq a (renameL r x) (renameL r y)
  | _, _, _, _, .pos => .pos

abbrev SubL (Γ Δ : List FTy) := ∀ {t}, Var Γ t → Tm Δ t

def wkL (t : Tm Γ a) : Tm (b :: Γ) a := renameL (fun v => .succ v) t

def liftSL (s : SubL Γ Δ) : SubL (a :: Γ) (a :: Δ)
  | _, .zero => .var .zero
  | _, .succ v => wkL (s v)

def substL : {Γ Δ : List FTy} → {t : FTy} → SubL Γ Δ → Tm Γ t → Tm Δ t
  | _, _, _, s, .var i => s i
  | _, _, _, s, .app F x => .app (substL s F) (substL s x)
  | _, _, _, s, .lam b => .lam (substL (liftSL s) b)
  | _, _, _, _, .top => .top
  | _, _, _, _, .bot => .bot
  | _, _, _, s, .neg x => .neg (substL s x)
  | _, _, _, s, .and x y => .and (substL s x) (substL s y)
  | _, _, _, s, .or x y => .or (substL s x) (substL s y)
  | _, _, _, s, .imp x y => .imp (substL s x) (substL s y)
  | _, _, _, s, .box x => .box (substL s x)
  | _, _, _, s, .all a b => .all a (substL (liftSL s) b)
  | _, _, _, s, .ex a b => .ex a (substL (liftSL s) b)
  | _, _, _, s, .allE b => .allE (substL (liftSL s) b)
  | _, _, _, s, .exE b => .exE (substL (liftSL s) b)
  | _, _, _, s, .eq a x y => .eq a (substL s x) (substL s y)
  | _, _, _, _, .pos => .pos

def sub0L (t : Tm Γ a) : SubL (a :: Γ) Γ
  | _, .zero => t
  | _, .succ v => .var v

def instL (b : Tm (a :: Γ) c) (t : Tm Γ a) : Tm Γ c := substL (sub0L t) b

theorem rename_emb : ∀ {Γ' Γ Δ t} (tm : Tm Γ' t) (ρ : HRen Γ Δ) (r : LRen Γ' Γ) (r' : LRen Γ' Δ),
    (∀ {u} (v : Var Γ' u), ρ (r v) = r' v) → rename ρ (emb r tm) = emb r' tm := by
  intro Γ' Γ Δ t tm
  induction tm generalizing Γ Δ with
  | var i =>
      intro ρ r r' h; simp only [emb, rename, h]
      all_goals rfl
  | app F x ihF ihx =>
      intro ρ r r' h; simp only [emb, rename, ihF ρ r r' h, ihx ρ r r' h]
      all_goals rfl
  | lam b ih =>
      intro ρ r r' h; simp only [emb, rename]
      rw [ih (liftR ρ) (liftL r) (liftL r') (fun v => by cases v <;> simp [liftR, liftL, h])]
      all_goals rfl
  | top =>
      intros; rfl
      all_goals rfl
  | bot =>
      intros; rfl
      all_goals rfl
  | neg x ih =>
      intro ρ r r' h; simp only [emb, rename]
      rw [ih (liftR ρ) (shL r) (shL r') (fun v => by simp [liftR, shL, h])]
      all_goals rfl
  | and x y ihx ihy =>
      intro ρ r r' h; simp only [emb, rename]
      rw [ihx (liftR ρ) (shL r) (shL r') (fun v => by simp [liftR, shL, h]),
        ihy (liftR ρ) (shL r) (shL r') (fun v => by simp [liftR, shL, h])]
      all_goals rfl
  | or x y ihx ihy =>
      intro ρ r r' h; simp only [emb, rename]
      rw [ihx (liftR ρ) (shL r) (shL r') (fun v => by simp [liftR, shL, h]),
        ihy (liftR ρ) (shL r) (shL r') (fun v => by simp [liftR, shL, h])]
      all_goals rfl
  | imp x y ihx ihy =>
      intro ρ r r' h; simp only [emb, rename]
      rw [ihx (liftR ρ) (shL r) (shL r') (fun v => by simp [liftR, shL, h]),
        ihy (liftR ρ) (shL r) (shL r') (fun v => by simp [liftR, shL, h])]
      all_goals rfl
  | box x ih =>
      intro ρ r r' h; simp only [emb, rename]
      rw [ih (liftR (liftR ρ)) (shL (shL r)) (shL (shL r')) (fun v => by simp [liftR, shL, h])]
      all_goals rfl
  | all a b ih =>
      intro ρ r r' h; simp only [emb, rename]
      rw [ih (liftR (liftR ρ)) (liftL (shL r)) (liftL (shL r'))
        (fun v => by cases v <;> simp [liftR, liftL, shL, h])]
      all_goals rfl
  | ex a b ih =>
      intro ρ r r' h; simp only [emb, rename]
      rw [ih (liftR (liftR ρ)) (liftL (shL r)) (liftL (shL r'))
        (fun v => by cases v <;> simp [liftR, liftL, shL, h])]
      all_goals rfl
  | allE b ih =>
      intro ρ r r' h; simp only [emb, rename]
      rw [ih (liftR (liftR ρ)) (liftL (shL r)) (liftL (shL r'))
        (fun v => by cases v <;> simp [liftR, liftL, shL, h])]
      all_goals rfl
  | exE b ih =>
      intro ρ r r' h; simp only [emb, rename]
      rw [ih (liftR (liftR ρ)) (liftL (shL r)) (liftL (shL r'))
        (fun v => by cases v <;> simp [liftR, liftL, shL, h])]
      all_goals rfl
  | eq a x y ihx ihy =>
      intro ρ r r' h; simp only [emb, rename]
      rw [ihx (liftR ρ) (shL r) (shL r') (fun v => by simp [liftR, shL, h]),
        ihy (liftR ρ) (shL r) (shL r') (fun v => by simp [liftR, shL, h])]
      all_goals rfl
  | pos => intros; rfl

theorem wk_emb (r : LRen Γ' Γ) (t : Tm Γ' u) : wk (b := b) (emb r t) = emb (shL r) t :=
  rename_emb _ _ _ _ (fun _ => rfl)

theorem emb_renameL : ∀ {Γ1 Γ2 Γ t} (tm : Tm Γ1 t) (q : RenL Γ1 Γ2) (r : LRen Γ2 Γ) (r' : LRen Γ1 Γ),
    (∀ {u} (v : Var Γ1 u), r (q v) = r' v) → emb r (renameL q tm) = emb r' tm := by
  intro Γ1 Γ2 Γ t tm
  induction tm generalizing Γ2 Γ with
  | var i =>
      intro q r r' h; simp only [emb, renameL, h]
      all_goals rfl
  | app F x ihF ihx =>
      intro q r r' h; simp only [emb, renameL, ihF q r r' h, ihx q r r' h]
      all_goals rfl
  | lam b ih =>
      intro q r r' h; simp only [emb, renameL]
      rw [ih (liftRL q) (liftL r) (liftL r') (fun v => by cases v <;> simp [liftRL, liftL, h])]
      all_goals rfl
  | top =>
      intros; rfl
      all_goals rfl
  | bot =>
      intros; rfl
      all_goals rfl
  | neg x ih =>
      intro q r r' h; simp only [emb, renameL]
      rw [ih q (shL r) (shL r') (fun v => by simp [shL, h])]
      all_goals rfl
  | and x y ihx ihy =>
      intro q r r' h; simp only [emb, renameL]
      rw [ihx q (shL r) (shL r') (fun v => by simp [shL, h]),
        ihy q (shL r) (shL r') (fun v => by simp [shL, h])]
      all_goals rfl
  | or x y ihx ihy =>
      intro q r r' h; simp only [emb, renameL]
      rw [ihx q (shL r) (shL r') (fun v => by simp [shL, h]),
        ihy q (shL r) (shL r') (fun v => by simp [shL, h])]
      all_goals rfl
  | imp x y ihx ihy =>
      intro q r r' h; simp only [emb, renameL]
      rw [ihx q (shL r) (shL r') (fun v => by simp [shL, h]),
        ihy q (shL r) (shL r') (fun v => by simp [shL, h])]
      all_goals rfl
  | box x ih =>
      intro q r r' h; simp only [emb, renameL]
      rw [ih q (shL (shL r)) (shL (shL r')) (fun v => by simp [shL, h])]
      all_goals rfl
  | all a b ih =>
      intro q r r' h; simp only [emb, renameL]
      rw [ih (liftRL q) (liftL (shL r)) (liftL (shL r'))
        (fun v => by cases v <;> simp [liftRL, liftL, shL, h])]
      all_goals rfl
  | ex a b ih =>
      intro q r r' h; simp only [emb, renameL]
      rw [ih (liftRL q) (liftL (shL r)) (liftL (shL r'))
        (fun v => by cases v <;> simp [liftRL, liftL, shL, h])]
      all_goals rfl
  | allE b ih =>
      intro q r r' h; simp only [emb, renameL]
      rw [ih (liftRL q) (liftL (shL r)) (liftL (shL r'))
        (fun v => by cases v <;> simp [liftRL, liftL, shL, h])]
      all_goals rfl
  | exE b ih =>
      intro q r r' h; simp only [emb, renameL]
      rw [ih (liftRL q) (liftL (shL r)) (liftL (shL r'))
        (fun v => by cases v <;> simp [liftRL, liftL, shL, h])]
      all_goals rfl
  | eq a x y ihx ihy =>
      intro q r r' h; simp only [emb, renameL]
      rw [ihx q (shL r) (shL r') (fun v => by simp [shL, h]),
        ihy q (shL r) (shL r') (fun v => by simp [shL, h])]
      all_goals rfl
  | pos => intros; rfl

theorem emb_wkL (r : LRen (a :: Γ') Γ) (t : Tm Γ' u) :
    emb r (wkL t) = emb (fun v => r (.succ v)) t :=
  emb_renameL _ _ _ _ (fun _ => rfl)

/-- Lifting the hypothesis of `subst_emb` under an `𝓛`-binder. -/
theorem subst_emb_liftL {σ : HSub Γ Δ} {r : LRen Γ' Γ} {r' : LRen Γ'' Δ} {τ : SubL Γ' Γ''}
    (h : ∀ {u} (v : Var Γ' u), σ (r v) = emb r' (τ v)) :
    ∀ {u} (v : Var (a :: Γ') u), liftS σ (liftL r v) = emb (liftL r') (liftSL τ v) := by
  intro u v
  cases v with
  | zero => rfl
  | succ v =>
      show wk (σ (r v)) = emb (liftL r') (wkL (τ v))
      rw [h, wk_emb, emb_wkL]; rfl

/-- Lifting the hypothesis of `subst_emb` under a world binder. -/
theorem subst_emb_shL {σ : HSub Γ Δ} {r : LRen Γ' Γ} {r' : LRen Γ'' Δ} {τ : SubL Γ' Γ''}
    (h : ∀ {u} (v : Var Γ' u), σ (r v) = emb r' (τ v)) :
    ∀ {u} (v : Var Γ' u), liftS (a := b) σ (shL r v) = emb (shL r') (τ v) := by
  intro u v
  show wk (σ (r v)) = _
  rw [h, wk_emb]

theorem subst_emb : ∀ {Γ' Γ'' Γ Δ t} (tm : Tm Γ' t) (σ : HSub Γ Δ) (r : LRen Γ' Γ) (r' : LRen Γ'' Δ)
    (τ : SubL Γ' Γ''), (∀ {u} (v : Var Γ' u), σ (r v) = emb r' (τ v)) →
    subst σ (emb r tm) = emb r' (substL τ tm) := by
  intro Γ' Γ'' Γ Δ t tm
  induction tm generalizing Γ'' Γ Δ with
  | var i =>
      intro σ r r' τ h; simp only [emb, subst, substL, h]
      all_goals rfl
  | app F x ihF ihx =>
      intro σ r r' τ h; simp only [emb, subst, substL, ihF σ r r' τ h, ihx σ r r' τ h]
      all_goals rfl
  | lam b ih =>
      intro σ r r' τ h; simp only [emb, subst, substL]
      rw [ih _ _ _ _ (subst_emb_liftL h)]
      all_goals rfl
  | top =>
      intros; rfl
      all_goals rfl
  | bot =>
      intros; rfl
      all_goals rfl
  | neg x ih =>
      intro σ r r' τ h; simp only [emb, subst, substL]
      rw [ih _ _ _ _ (subst_emb_shL h)]
      all_goals rfl
  | and x y ihx ihy =>
      intro σ r r' τ h; simp only [emb, subst, substL]
      rw [ihx _ _ _ _ (subst_emb_shL h), ihy _ _ _ _ (subst_emb_shL h)]
      all_goals rfl
  | or x y ihx ihy =>
      intro σ r r' τ h; simp only [emb, subst, substL]
      rw [ihx _ _ _ _ (subst_emb_shL h), ihy _ _ _ _ (subst_emb_shL h)]
      all_goals rfl
  | imp x y ihx ihy =>
      intro σ r r' τ h; simp only [emb, subst, substL]
      rw [ihx _ _ _ _ (subst_emb_shL h), ihy _ _ _ _ (subst_emb_shL h)]
      all_goals rfl
  | box x ih =>
      intro σ r r' τ h; simp only [emb, subst, substL]
      rw [ih _ _ _ _ (subst_emb_shL (subst_emb_shL h))]
      all_goals rfl
  | all a b ih =>
      intro σ r r' τ h; simp only [emb, subst, substL]
      rw [ih _ _ _ _ (subst_emb_liftL (subst_emb_shL h))]
      all_goals rfl
  | ex a b ih =>
      intro σ r r' τ h; simp only [emb, subst, substL]
      rw [ih _ _ _ _ (subst_emb_liftL (subst_emb_shL h))]
      all_goals rfl
  | allE b ih =>
      intro σ r r' τ h; simp only [emb, subst, substL]
      rw [ih _ _ _ _ (subst_emb_liftL (subst_emb_shL h))]
      all_goals rfl
  | exE b ih =>
      intro σ r r' τ h; simp only [emb, subst, substL]
      rw [ih _ _ _ _ (subst_emb_liftL (subst_emb_shL h))]
      all_goals rfl
  | eq a x y ihx ihy =>
      intro σ r r' τ h; simp only [emb, subst, substL]
      rw [ihx _ _ _ _ (subst_emb_shL h), ihy _ _ _ _ (subst_emb_shL h)]
      all_goals rfl
  | pos => intros; rfl

theorem substL_id : ∀ {Γ t} (tm : Tm Γ t) (s : SubL Γ Γ), (∀ {u} (v : Var Γ u), s v = .var v) →
    substL s tm = tm := by
  intro Γ t tm
  induction tm with
  | var i => intro s h; simp only [substL, h]
  | app F x ihF ihx => intro s h; simp only [substL, ihF s h, ihx s h]
  | lam b ih => intro s h; simp only [substL]; rw [ih _ (fun v => by cases v <;> simp [liftSL, h, wkL, renameL])]
  | top => intros; rfl
  | bot => intros; rfl
  | neg x ih => intro s h; simp only [substL, ih s h]
  | and x y ihx ihy => intro s h; simp only [substL, ihx s h, ihy s h]
  | or x y ihx ihy => intro s h; simp only [substL, ihx s h, ihy s h]
  | imp x y ihx ihy => intro s h; simp only [substL, ihx s h, ihy s h]
  | box x ih => intro s h; simp only [substL, ih s h]
  | all a b ih => intro s h; simp only [substL]; rw [ih _ (fun v => by cases v <;> simp [liftSL, h, wkL, renameL])]
  | ex a b ih => intro s h; simp only [substL]; rw [ih _ (fun v => by cases v <;> simp [liftSL, h, wkL, renameL])]
  | allE b ih => intro s h; simp only [substL]; rw [ih _ (fun v => by cases v <;> simp [liftSL, h, wkL, renameL])]
  | exE b ih => intro s h; simp only [substL]; rw [ih _ (fun v => by cases v <;> simp [liftSL, h, wkL, renameL])]
  | eq a x y ihx ihy => intro s h; simp only [substL, ihx s h, ihy s h]
  | pos => intros; rfl

/-- A substitution acting on the embedding as a renaming. -/
theorem subst_emb_ren (tm : Tm Γ' t) (σ : HSub Γ Δ) (r : LRen Γ' Γ) (r' : LRen Γ' Δ)
    (h : ∀ {u} (v : Var Γ' u), σ (r v) = .var (r' v)) : subst σ (emb r tm) = emb r' tm := by
  rw [subst_emb tm σ r r' (fun v => .var v) h, substL_id _ _ (fun _ => rfl)]

/-- `[t/0]` on the embedding is `[t/0]` in `𝓛`. -/
theorem inst_emb (b : Tm (a :: Γ') c) (r : LRen Γ' Γ) (t : Tm Γ' a) :
    inst (emb (liftL r) b) (emb r t) = emb r (instL b t) :=
  subst_emb b _ _ _ _ (fun v => by cases v <;> rfl)

/-! ## Deep derivations -/

/-- The whole-term condition on an instance: at a type of `𝓛`, the image under `⟦-⟧` of an
`𝓛`-term whose parameters are variables of `𝓛`-types; no condition at `w` and `o`. -/
def Cert : (a : HTy) → HTerm Γ a → Prop
  | .L t, x => ∃ (Γ' : List FTy) (s : Tm Γ' t) (r : LRen Γ' Γ), x = emb r s
  | .w, _ => True
  | .o, _ => True

/-- No condition: the unrestricted calculus. -/
def Any : (a : HTy) → HTerm Γ a → Prop := fun _ _ => True

def nilR : LRen [] Γ := fun v => by cases v

def emptyEnv : HEnv W D [] := fun v => by cases v

abbrev var0 : HTerm (a :: Γ) a := .var .zero

/-- Natural deduction for the HOL of the embedding, with the `𝓛`-sentences `T` as axioms (each
holds at every world).  `ok` constrains the instances of `∀`-elimination and `∃`-introduction. -/
inductive Deriv (T : Tm [] .s → Prop) (ok : ∀ {Γ : List HTy} (a : HTy), HTerm Γ a → Prop) :
    (Γ : List HTy) → List (HTerm Γ .o) → HTerm Γ .o → Prop
  | hyp {Γ hs φ} : φ ∈ hs → Deriv T ok Γ hs φ
  | ax {Γ hs} (φ : Tm [] .s) (i : HTerm Γ .w) : T φ → Deriv T ok Γ hs (.holds (emb nilR φ) i)
  | impI {Γ hs φ ψ} : Deriv T ok Γ (φ :: hs) ψ → Deriv T ok Γ hs (.imp φ ψ)
  | impE {Γ hs φ ψ} : Deriv T ok Γ hs (.imp φ ψ) → Deriv T ok Γ hs φ → Deriv T ok Γ hs ψ
  | byContra {Γ hs φ} : Deriv T ok Γ (.imp φ .bot :: hs) .bot → Deriv T ok Γ hs φ
  | andI {Γ hs φ ψ} : Deriv T ok Γ hs φ → Deriv T ok Γ hs ψ → Deriv T ok Γ hs (.and φ ψ)
  | andL {Γ hs φ ψ} : Deriv T ok Γ hs (.and φ ψ) → Deriv T ok Γ hs φ
  | andR {Γ hs φ ψ} : Deriv T ok Γ hs (.and φ ψ) → Deriv T ok Γ hs ψ
  | orL {Γ hs φ ψ} : Deriv T ok Γ hs φ → Deriv T ok Γ hs (.or φ ψ)
  | orR {Γ hs φ ψ} : Deriv T ok Γ hs ψ → Deriv T ok Γ hs (.or φ ψ)
  | orE {Γ hs φ ψ χ} : Deriv T ok Γ hs (.or φ ψ) → Deriv T ok Γ (φ :: hs) χ →
      Deriv T ok Γ (ψ :: hs) χ → Deriv T ok Γ hs χ
  | allI {Γ hs} (a : HTy) {φ : HTerm (a :: Γ) .o} :
      Deriv T ok (a :: Γ) (hs.map wk) φ → Deriv T ok Γ hs (.all a φ)
  | allE {Γ hs} (a : HTy) {φ : HTerm (a :: Γ) .o} (t : HTerm Γ a) :
      Deriv T ok Γ hs (.all a φ) → ok a t → Deriv T ok Γ hs (inst φ t)
  | exI {Γ hs} (a : HTy) {φ : HTerm (a :: Γ) .o} (t : HTerm Γ a) :
      ok a t → Deriv T ok Γ hs (inst φ t) → Deriv T ok Γ hs (.ex a φ)
  | exE {Γ hs} (a : HTy) {φ : HTerm (a :: Γ) .o} {χ : HTerm Γ .o} :
      Deriv T ok Γ hs (.ex a φ) → Deriv T ok (a :: Γ) (φ :: hs.map wk) (wk χ) →
      Deriv T ok Γ hs χ
  | refl {Γ hs} (a : HTy) (t : HTerm Γ a) : Deriv T ok Γ hs (.eq a t t)
  | symm {Γ hs} (a : HTy) {s t : HTerm Γ a} : Deriv T ok Γ hs (.eq a s t) → Deriv T ok Γ hs (.eq a t s)
  | trans {Γ hs} (a : HTy) {s t u : HTerm Γ a} : Deriv T ok Γ hs (.eq a s t) →
      Deriv T ok Γ hs (.eq a t u) → Deriv T ok Γ hs (.eq a s u)
  | subst {Γ hs} (a : HTy) {s t : HTerm Γ a} (φ : HTerm (a :: Γ) .o) : plain a = true →
      Deriv T ok Γ hs (.eq a s t) → Deriv T ok Γ hs (inst φ s) → Deriv T ok Γ hs (inst φ t)
  | funExt {Γ hs a b} {f g : HTerm Γ (.L (.arr a b))} :
      Deriv T ok Γ hs (.all (.L a) (.eq (.L b) (.appL (wk f) var0) (.appL (wk g) var0))) →
      Deriv T ok Γ hs (.eq (.L (.arr a b)) f g)
  | funApp {Γ hs a b} {f g : HTerm Γ (.L (.arr a b))} :
      Deriv T ok Γ hs (.eq (.L (.arr a b)) f g) →
      Deriv T ok Γ hs (.all (.L a) (.eq (.L b) (.appL (wk f) var0) (.appL (wk g) var0)))
  | wExt {Γ hs} {p q : HTerm Γ (.L .s)} :
      Deriv T ok Γ hs (.all .w (.eq .o (.holds (wk p) var0) (.holds (wk q) var0))) →
      Deriv T ok Γ hs (.eq (.L .s) p q)
  | wApp {Γ hs} {p q : HTerm Γ (.L .s)} :
      Deriv T ok Γ hs (.eq (.L .s) p q) →
      Deriv T ok Γ hs (.all .w (.eq .o (.holds (wk p) var0) (.holds (wk q) var0)))
  | propExt {Γ hs φ ψ} : Deriv T ok Γ (φ :: hs) ψ → Deriv T ok Γ (ψ :: hs) φ →
      Deriv T ok Γ hs (.eq .o φ ψ)
  | betaL {Γ hs a b} (body : HTerm (.L a :: Γ) (.L b)) (x : HTerm Γ (.L a)) :
      Deriv T ok Γ hs (.eq (.L b) (.appL (.lamL body) x) (inst body x))
  | betaWI {Γ hs} (φ : HTerm (.w :: Γ) .o) (i : HTerm Γ .w) :
      Deriv T ok Γ hs (inst φ i) → Deriv T ok Γ hs (.holds (.wabs φ) i)
  | betaWE {Γ hs} (φ : HTerm (.w :: Γ) .o) (i : HTerm Γ .w) :
      Deriv T ok Γ hs (.holds (.wabs φ) i) → Deriv T ok Γ hs (inst φ i)
  /-- Leibniz at every type of `𝓛`: the motive is an `𝓛`-formula `M` with the hole as its
  variable `0` (its other parameters read through `r`) at a world `i`; both sides certified. -/
  | leib {Γ hs} (a : FTy) {Γ' : List FTy} (r : LRen Γ' Γ) (M : Tm (a :: Γ') .s) (i : HTerm Γ .w)
      {s t : HTerm Γ (.L a)} : ok (.L a) s → ok (.L a) t → Deriv T ok Γ hs (.eq (.L a) s t) →
      Deriv T ok Γ hs (inst (.holds (emb (liftL r) M) (wk i)) s) →
      Deriv T ok Γ hs (inst (.holds (emb (liftL r) M) (wk i)) t)

/-! ## Respect for relativised equality, and the fundamental lemma

`Resp S`: admitted functions give `eqT`-equal values on `eqT`-equal admitted arguments.  This is
the semantics in v4's proof of `prop:lgeneral`, where a function of the model lives on the
carriers and is extended to the full domain by restriction. -/

def Resp (S : Str W D) : Prop :=
  ∀ (a b : FTy) (F : Den W D (.arr a b)), S.A (.arr a b) F →
    ∀ z z', S.A a z → S.A a z' → eqT S a z z' → eqT S b (F z) (F z')

/-- Pointwise `eqT` of `𝓛`-environments. -/
def EnvR (S : Str W D) : (Γ : List FTy) → Env W D Γ → Env W D Γ → Prop
  | [], _, _ => True
  | t :: Γ, ρ, ρ' => eqT S t ρ.1 ρ'.1 ∧ EnvR S Γ ρ.2 ρ'.2

theorem envR_refl (S : Str W D) : ∀ (Γ : List FTy) (ρ : Env W D Γ), EnvR S Γ ρ ρ
  | [], _ => trivial
  | t :: Γ, ρ => ⟨eqT_refl S t ρ.1, envR_refl S Γ ρ.2⟩

theorem get_rel (S : Str W D) : ∀ {Γ t} (i : Var Γ t) (ρ ρ' : Env W D Γ), EnvR S Γ ρ ρ' →
    eqT S t (i.get ρ) (i.get ρ')
  | _ :: _, _, .zero, _, _, h => h.1
  | _ :: _, _, .succ i, _, _, h => get_rel S i _ _ h.2

/-- **Fundamental lemma**: in a closed structure that respects `eqT`, every `𝓛`-term maps
pointwise `eqT`-equal admitted environments to `eqT`-equal values. -/
theorem fund (S : Str W D) (hE : ∀ x, S.A .e x) (hC : Closed S) (hR : Resp S) :
    ∀ {Γ t} (tm : Tm Γ t) (ρ ρ' : Env W D Γ), EnvA S Γ ρ → EnvA S Γ ρ' → EnvR S Γ ρ ρ' →
      eqT S t (eval S tm ρ) (eval S tm ρ')
  | _, _, .var i, ρ, ρ', _, _, h => get_rel S i ρ ρ' h
  | _, _, .app F x, ρ, ρ', hA, hA', h => by
      have hF := fund S hE hC hR F ρ ρ' hA hA' h
      have hx := fund S hE hC hR x ρ ρ' hA hA' h
      exact eqT_trans S _ (hR _ _ _ (hC F ρ hA) _ _ (hC x ρ hA) (hC x ρ' hA') hx)
        (hF _ (hC x ρ' hA'))
  | _, _, .lam b, ρ, ρ', hA, hA', h => fun z hz =>
      fund S hE hC hR b (z, ρ) (z, ρ') ⟨hz, hA⟩ ⟨hz, hA'⟩ ⟨eqT_refl S _ z, h⟩
  | _, _, .top, _, _, _, _, _ => rfl
  | _, _, .bot, _, _, _, _, _ => rfl
  | _, _, .neg x, ρ, ρ', hA, hA', h => by
      have e : eval S x ρ = eval S x ρ' := fund S hE hC hR x ρ ρ' hA hA' h
      show (fun w => ¬ eval S x ρ w) = (fun w => ¬ eval S x ρ' w); rw [e]
  | _, _, .and x y, ρ, ρ', hA, hA', h => by
      have e : eval S x ρ = eval S x ρ' := fund S hE hC hR x ρ ρ' hA hA' h
      have e' : eval S y ρ = eval S y ρ' := fund S hE hC hR y ρ ρ' hA hA' h
      show (fun w => eval S x ρ w ∧ eval S y ρ w) = (fun w => eval S x ρ' w ∧ eval S y ρ' w)
      rw [e, e']
  | _, _, .or x y, ρ, ρ', hA, hA', h => by
      have e : eval S x ρ = eval S x ρ' := fund S hE hC hR x ρ ρ' hA hA' h
      have e' : eval S y ρ = eval S y ρ' := fund S hE hC hR y ρ ρ' hA hA' h
      show (fun w => eval S x ρ w ∨ eval S y ρ w) = (fun w => eval S x ρ' w ∨ eval S y ρ' w)
      rw [e, e']
  | _, _, .imp x y, ρ, ρ', hA, hA', h => by
      have e : eval S x ρ = eval S x ρ' := fund S hE hC hR x ρ ρ' hA hA' h
      have e' : eval S y ρ = eval S y ρ' := fund S hE hC hR y ρ ρ' hA hA' h
      show (fun w => eval S x ρ w → eval S y ρ w) = (fun w => eval S x ρ' w → eval S y ρ' w)
      rw [e, e']
  | _, _, .box x, ρ, ρ', hA, hA', h => by
      have e : eval S x ρ = eval S x ρ' := fund S hE hC hR x ρ ρ' hA hA' h
      show (fun w => ∀ v, S.R w v → eval S x ρ v) = (fun w => ∀ v, S.R w v → eval S x ρ' v)
      rw [e]
  | _, _, .all a b, ρ, ρ', hA, hA', h => by
      have e : ∀ x, S.A a x → eval S b (x, ρ) = eval S b (x, ρ') := fun x hx =>
        fund S hE hC hR b (x, ρ) (x, ρ') ⟨hx, hA⟩ ⟨hx, hA'⟩ ⟨eqT_refl S _ x, h⟩
      show (fun w => ∀ x, S.A a x → eval S b (x, ρ) w) = (fun w => ∀ x, S.A a x → eval S b (x, ρ') w)
      funext w; apply propext
      exact ⟨fun H x hx => e x hx ▸ H x hx, fun H x hx => (e x hx).symm ▸ H x hx⟩
  | _, _, .ex a b, ρ, ρ', hA, hA', h => by
      have e : ∀ x, S.A a x → eval S b (x, ρ) = eval S b (x, ρ') := fun x hx =>
        fund S hE hC hR b (x, ρ) (x, ρ') ⟨hx, hA⟩ ⟨hx, hA'⟩ ⟨eqT_refl S _ x, h⟩
      show (fun w => ∃ x, S.A a x ∧ eval S b (x, ρ) w) = (fun w => ∃ x, S.A a x ∧ eval S b (x, ρ') w)
      funext w; apply propext
      exact ⟨fun ⟨x, hx, H⟩ => ⟨x, hx, e x hx ▸ H⟩, fun ⟨x, hx, H⟩ => ⟨x, hx, (e x hx).symm ▸ H⟩⟩
  | _, _, .allE b, ρ, ρ', hA, hA', h => by
      have e : ∀ x, eval S b (x, ρ) = eval S b (x, ρ') := fun x =>
        fund S hE hC hR b (x, ρ) (x, ρ') ⟨hE x, hA⟩ ⟨hE x, hA'⟩ ⟨eqT_refl S _ x, h⟩
      show (fun w => ∀ y, S.act y w → eval S b (y, ρ) w) = (fun w => ∀ y, S.act y w → eval S b (y, ρ') w)
      funext w; apply propext
      exact ⟨fun H x hx => e x ▸ H x hx, fun H x hx => (e x).symm ▸ H x hx⟩
  | _, _, .exE b, ρ, ρ', hA, hA', h => by
      have e : ∀ x, eval S b (x, ρ) = eval S b (x, ρ') := fun x =>
        fund S hE hC hR b (x, ρ) (x, ρ') ⟨hE x, hA⟩ ⟨hE x, hA'⟩ ⟨eqT_refl S _ x, h⟩
      show (fun w => ∃ y, S.act y w ∧ eval S b (y, ρ) w) = (fun w => ∃ y, S.act y w ∧ eval S b (y, ρ') w)
      funext w; apply propext
      exact ⟨fun ⟨x, hx, H⟩ => ⟨x, hx, e x ▸ H⟩, fun ⟨x, hx, H⟩ => ⟨x, hx, (e x).symm ▸ H⟩⟩
  | _, _, .eq a x y, ρ, ρ', hA, hA', h => by
      have hx := fund S hE hC hR x ρ ρ' hA hA' h
      have hy := fund S hE hC hR y ρ ρ' hA hA' h
      show (fun _ => eqT S a (eval S x ρ) (eval S y ρ)) = (fun _ => eqT S a (eval S x ρ') (eval S y ρ'))
      funext _; apply propext
      exact ⟨fun k => eqT_trans S a (eqT_symm S a hx) (eqT_trans S a k hy),
        fun k => eqT_trans S a hx (eqT_trans S a k (eqT_symm S a hy))⟩
  | _, _, .pos, _, _, _, _, _ => eqT_refl S _ _

/-! ## Soundness over 𝓛-general structures -/

/-- Variables of `𝓛`-types take admitted values. -/
def AdmEnv (S : Str W D) (ρ : HEnv W D Γ) : Prop := ∀ {a} (v : HVar Γ a), Rng S a (ρ v)

theorem admEnv_cons (S : Str W D) {ρ : HEnv W D Γ} (h : AdmEnv S ρ) {x : HDen W D a}
    (hx : Rng S a x) : AdmEnv S (cons x ρ) := by
  intro b v; cases v with
  | zero => exact hx
  | succ v => exact h v

theorem envA_pull (S : Str W D) {ρ : HEnv W D Γ} (h : AdmEnv S ρ) :
    ∀ {Γ' : List FTy} (r : LRen Γ' Γ), EnvA S Γ' (pull r ρ)
  | [], _ => trivial
  | _ :: _, r => ⟨h (r .zero), envA_pull S h (fun v => r (.succ v))⟩

/-- Certified instances denote admitted objects: this is where closure is used. -/
theorem cert_rng (S : Str W D) (hE : ∀ x, S.A .e x) (hC : Closed S) {ρ : HEnv W D Γ}
    (h : AdmEnv S ρ) : ∀ (a : HTy) (t : HTerm Γ a), Cert a t → Rng S a (heval S t ρ)
  | .L _, _, ⟨_, s, r, e⟩ => by
      subst e; show S.A _ _; rw [heval_emb S hE]; exact hC s _ (envA_pull S h r)
  | .w, _, _ => trivial
  | .o, _, _ => trivial

theorem mem_map_wk {hs : List (HTerm Γ .o)} {h : HTerm (a :: Γ) .o} (hm : h ∈ hs.map wk) :
    ∃ h', h' ∈ hs ∧ h = wk h' := by
  obtain ⟨h', m, e⟩ := List.mem_map.1 hm; exact ⟨h', m, e.symm⟩

/-- **Soundness** (`prop:lgeneral`, deep form): a derivation whose instances at types of `𝓛`
are certified holds, under every assignment of admitted values to the variables of
`𝓛`-types, in every structure that is closed under all terms of `𝓛`, admits every entity and
satisfies `T`. -/
theorem soundness (S : Str W D) (hE : ∀ x, S.A .e x) (hC : Closed S) (hR : Resp S)
    {T : Tm [] .s → Prop} (hT : ∀ φ, T φ → ∀ w, eval S φ () w) :
    ∀ {Γ hs φ}, Deriv T (fun a t => Cert a t) Γ hs φ →
      ∀ (ρ : HEnv W D Γ), AdmEnv S ρ → (∀ h ∈ hs, heval S h ρ) → heval S φ ρ := by
  intro Γ hs φ d
  induction d with
  | hyp m => exact fun ρ _ hh => hh _ m
  | ax φ i hφ =>
      intro ρ _ _
      show heval S (emb nilR φ) ρ (heval S i ρ)
      rw [heval_emb S hE]; exact hT φ hφ _
  | impI _ ih => exact fun ρ hρ hh hφ => ih ρ hρ (fun h m => by
      rcases List.mem_cons.1 m with rfl | m
      · exact hφ
      · exact hh h m)
  | impE _ _ ih1 ih2 => exact fun ρ hρ hh => ih1 ρ hρ hh (ih2 ρ hρ hh)
  | byContra _ ih =>
      intro ρ hρ hh
      apply Classical.byContradiction
      intro hn
      exact ih ρ hρ (fun h m => by
        rcases List.mem_cons.1 m with rfl | m
        · exact hn
        · exact hh h m)
  | andI _ _ ih1 ih2 => exact fun ρ hρ hh => ⟨ih1 ρ hρ hh, ih2 ρ hρ hh⟩
  | andL _ ih => exact fun ρ hρ hh => (ih ρ hρ hh).1
  | andR _ ih => exact fun ρ hρ hh => (ih ρ hρ hh).2
  | orL _ ih => exact fun ρ hρ hh => Or.inl (ih ρ hρ hh)
  | orR _ ih => exact fun ρ hρ hh => Or.inr (ih ρ hρ hh)
  | orE _ _ _ ih ih1 ih2 =>
      intro ρ hρ hh
      rcases ih ρ hρ hh with h | h
      · exact ih1 ρ hρ fun k m => by
          rcases List.mem_cons.1 m with rfl | m
          · exact h
          · exact hh k m
      · exact ih2 ρ hρ fun k m => by
          rcases List.mem_cons.1 m with rfl | m
          · exact h
          · exact hh k m
  | allI a _ ih =>
      intro ρ hρ hh x hx
      exact ih (cons x ρ) (admEnv_cons S hρ hx) fun k m => by
        obtain ⟨k', m', rfl⟩ := mem_map_wk m
        rw [heval_wk]; exact hh k' m'
  | allE a t _ hok ih =>
      intro ρ hρ hh
      rw [heval_inst]
      exact ih ρ hρ hh _ (cert_rng S hE hC hρ a t hok)
  | exI a t hok _ ih =>
      intro ρ hρ hh
      have := ih ρ hρ hh
      rw [heval_inst] at this
      exact ⟨_, cert_rng S hE hC hρ a t hok, this⟩
  | exE a _ _ ih1 ih2 =>
      intro ρ hρ hh
      obtain ⟨x, hx, hφ⟩ := ih1 ρ hρ hh
      have := ih2 (cons x ρ) (admEnv_cons S hρ hx) fun k m => by
        rcases List.mem_cons.1 m with rfl | m
        · exact hφ
        · obtain ⟨k', m', rfl⟩ := mem_map_wk m
          rw [heval_wk]; exact hh k' m'
      rwa [heval_wk] at this
  | refl a t => exact fun ρ _ _ => EqH_refl S a _
  | symm a _ ih => exact fun ρ hρ hh => EqH_symm S a (ih ρ hρ hh)
  | trans a _ _ ih1 ih2 => exact fun ρ hρ hh => EqH_trans S a (ih1 ρ hρ hh) (ih2 ρ hρ hh)
  | subst a φ hp _ _ ih1 ih2 =>
      intro ρ hρ hh
      have e := EqH_plain S hE a hp (ih1 ρ hρ hh)
      have := ih2 ρ hρ hh
      rw [heval_inst] at this ⊢
      rwa [← e]
  | funExt _ ih =>
      intro ρ hρ hh z hz
      have := ih ρ hρ hh z hz
      simpa only [heval, heval_wk, var0, cons, EqH] using this
  | funApp _ ih =>
      intro ρ hρ hh z hz
      have := ih ρ hρ hh z hz
      simpa only [heval, heval_wk, var0, cons, EqH] using this
  | wExt _ ih =>
      intro ρ hρ hh
      funext u
      have := ih ρ hρ hh u trivial
      simp only [heval, heval_wk, var0, cons, EqH] at this
      exact propext this
  | wApp _ ih =>
      intro ρ hρ hh u _
      have := ih ρ hρ hh
      simp only [heval, heval_wk, var0, cons, EqH]
      show _ ↔ _
      exact Iff.of_eq (congrFun this u)
  | propExt _ _ ih1 ih2 =>
      intro ρ hρ hh
      constructor
      · intro h; exact ih1 ρ hρ fun k m => by
          rcases List.mem_cons.1 m with rfl | m
          · exact h
          · exact hh k m
      · intro h; exact ih2 ρ hρ fun k m => by
          rcases List.mem_cons.1 m with rfl | m
          · exact h
          · exact hh k m
  | betaL body x =>
      intro ρ _ _
      show eqT S _ _ _
      simp only [heval, heval_inst]
      exact eqT_refl S _ _
  | betaWI φ i _ ih =>
      intro ρ hρ hh
      have := ih ρ hρ hh
      rw [heval_inst] at this
      exact this
  | betaWE φ i _ ih =>
      intro ρ hρ hh
      rw [heval_inst]
      exact ih ρ hρ hh
  | @leib Γ _ a Γ' r M i s t hs ht _ _ ih1 ih2 =>
      intro ρ hρ hh
      have e : eqT S a (heval S s ρ) (heval S t ρ) := ih1 ρ hρ hh
      have d := ih2 ρ hρ hh
      rw [heval_inst] at d ⊢
      simp only [heval, heval_wk, heval_emb S hE, pull_liftL] at d ⊢
      have := fund S hE hC hR M (heval S s ρ, pull r ρ) (heval S t ρ, pull r ρ)
        ⟨cert_rng S hE hC hρ _ _ hs, envA_pull S hρ r⟩ ⟨cert_rng S hE hC hρ _ _ ht, envA_pull S hρ r⟩
        ⟨e, envR_refl S _ _⟩
      have this' : eval S M _ = eval S M _ := this
      rw [← this']; exact d

/-- The form used for sentences: a certified derivation of `⟦φ⟧` at a world variable, from `T`
alone, gives `φ` at every world of every such structure. -/
theorem valid_of_deriv (S : Str W D) (hE : ∀ x, S.A .e x) (hC : Closed S) (hR : Resp S)
    {T : Tm [] .s → Prop} (hT : ∀ φ, T φ → ∀ w, eval S φ () w) {φ : Tm [] .s}
    (d : Deriv T (fun a t => Cert a t) [.w] [] (.holds (emb nilR φ) var0)) :
    ∀ w, eval S φ () w := by
  intro w
  have := soundness S hE hC hR hT d (cons (a := .w) w emptyEnv)
    (admEnv_cons (a := .w) S (fun v => by cases v) trivial) (fun _ m => by cases m)
  simp only [heval, heval_emb S hE] at this
  exact this

/-! ## Structural rules -/

theorem cons_sub {hs hs' : List (HTerm Γ .o)} (hsub : ∀ h, h ∈ hs → h ∈ hs') (x : HTerm Γ .o) :
    ∀ h, h ∈ x :: hs → h ∈ x :: hs' := fun h m => by
  rcases List.mem_cons.1 m with rfl | m
  · exact List.mem_cons_self ..
  · exact List.mem_cons_of_mem _ (hsub h m)

theorem map_sub {hs hs' : List (HTerm Γ .o)} (hsub : ∀ h, h ∈ hs → h ∈ hs') :
    ∀ h, h ∈ hs.map (wk (b := b)) → h ∈ hs'.map wk := fun h m => by
  obtain ⟨h', m', rfl⟩ := mem_map_wk m
  exact List.mem_map_of_mem (hsub h' m')

theorem Deriv.weaken {T : Tm [] .s → Prop} {ok : ∀ {Γ : List HTy} (a : HTy), HTerm Γ a → Prop} :
    ∀ {Γ hs φ}, Deriv T ok Γ hs φ → ∀ {hs'}, (∀ h, h ∈ hs → h ∈ hs') → Deriv T ok Γ hs' φ := by
  intro Γ hs φ d
  induction d with
  | hyp m => exact fun hsub => .hyp (hsub _ m)
  | ax φ i h => exact fun _ => .ax φ i h
  | impI _ ih => exact fun hsub => .impI (ih (cons_sub hsub _))
  | impE _ _ ih1 ih2 => exact fun hsub => .impE (ih1 hsub) (ih2 hsub)
  | byContra _ ih => exact fun hsub => .byContra (ih (cons_sub hsub _))
  | andI _ _ ih1 ih2 => exact fun hsub => .andI (ih1 hsub) (ih2 hsub)
  | andL _ ih => exact fun hsub => .andL (ih hsub)
  | andR _ ih => exact fun hsub => .andR (ih hsub)
  | orL _ ih => exact fun hsub => .orL (ih hsub)
  | orR _ ih => exact fun hsub => .orR (ih hsub)
  | orE _ _ _ ih ih1 ih2 => exact fun hsub => .orE (ih hsub) (ih1 (cons_sub hsub _)) (ih2 (cons_sub hsub _))
  | allI a _ ih => exact fun hsub => .allI a (ih (map_sub hsub))
  | allE a t _ hok ih => exact fun hsub => .allE a t (ih hsub) hok
  | exI a t hok _ ih => exact fun hsub => .exI a t hok (ih hsub)
  | exE a _ _ ih1 ih2 => exact fun hsub => .exE a (ih1 hsub) (ih2 (cons_sub (map_sub hsub) _))
  | refl a t => exact fun _ => .refl a t
  | symm a _ ih => exact fun hsub => .symm a (ih hsub)
  | trans a _ _ ih1 ih2 => exact fun hsub => .trans a (ih1 hsub) (ih2 hsub)
  | subst a φ hp _ _ ih1 ih2 => exact fun hsub => .subst a φ hp (ih1 hsub) (ih2 hsub)
  | funExt _ ih => exact fun hsub => .funExt (ih hsub)
  | funApp _ ih => exact fun hsub => .funApp (ih hsub)
  | wExt _ ih => exact fun hsub => .wExt (ih hsub)
  | wApp _ ih => exact fun hsub => .wApp (ih hsub)
  | propExt _ _ ih1 ih2 => exact fun hsub => .propExt (ih1 (cons_sub hsub _)) (ih2 (cons_sub hsub _))
  | betaL body x => exact fun _ => .betaL body x
  | betaWI φ i _ ih => exact fun hsub => .betaWI φ i (ih hsub)
  | betaWE φ i _ ih => exact fun hsub => .betaWE φ i (ih hsub)
  | leib a r M i h1 h2 _ _ ih1 ih2 => exact fun hsub => .leib a r M i h1 h2 (ih1 hsub) (ih2 hsub)

theorem Deriv.wk1 {T ok Γ hs φ} (d : Deriv T ok Γ hs φ) (ψ : HTerm Γ .o) : Deriv T ok Γ (ψ :: hs) φ :=
  d.weaken fun _ m => List.mem_cons_of_mem _ m

theorem Deriv.exFalso {T ok Γ hs φ} (d : Deriv T ok Γ hs .bot) : Deriv T ok Γ hs φ :=
  .byContra (d.wk1 _)

/-! ## Renaming whole derivations -/

def sub0R (ρ : HRen Γ Δ) (t : HTerm Γ a) : HSub (a :: Γ) Δ
  | _, .zero => rename ρ t
  | _, .succ v => .var (ρ v)

theorem rename_inst (ρ : HRen Γ Δ) (φ : HTerm (a :: Γ) b) (t : HTerm Γ a) :
    rename ρ (inst φ t) = inst (rename (liftR ρ) φ) (rename ρ t) := by
  unfold inst
  rw [rename_subst φ (sub0 t) ρ (sub0R ρ t) (fun v => by cases v <;> rfl),
    subst_rename φ (liftR ρ) (sub0 (rename ρ t)) (sub0R ρ t) (fun v => by cases v <;> rfl)]

theorem rename_liftR_wk (ρ : HRen Γ Δ) (h : HTerm Γ c) :
    rename (liftR (a := b) ρ) (wk h) = wk (rename ρ h) := by
  unfold wk
  rw [rename_rename h (fun v => .succ v) (liftR ρ) (fun v => .succ (ρ v)) (fun _ => rfl),
    rename_rename h ρ (fun v => .succ v) (fun v => .succ (ρ v)) (fun _ => rfl)]

theorem map_rename_wk (ρ : HRen Γ Δ) (hs : List (HTerm Γ .o)) :
    (hs.map (wk (b := b))).map (rename (liftR ρ)) = (hs.map (rename ρ)).map wk := by
  simp only [List.map_map]
  exact List.map_congr_left (fun h _ => rename_liftR_wk ρ h)

theorem cert_rename (ρ : HRen Γ Δ) : ∀ (a : HTy) (t : HTerm Γ a), Cert a t → Cert a (rename ρ t)
  | .L _, _, ⟨Γ', s, r, e⟩ => ⟨Γ', s, fun v => ρ (r v), by rw [e, rename_emb _ _ _ _ (fun _ => rfl)]⟩
  | .w, _, _ => trivial
  | .o, _, _ => trivial

/-- Certified derivations are closed under renaming of the context. -/
theorem Deriv.ren {T : Tm [] .s → Prop} :
    ∀ {Γ hs φ}, Deriv T (fun a t => Cert a t) Γ hs φ → ∀ {Δ} (ρ : HRen Γ Δ),
      Deriv T (fun a t => Cert a t) Δ (hs.map (rename ρ)) (rename ρ φ) := by
  intro Γ hs φ d
  induction d with
  | hyp m => exact fun ρ => .hyp (List.mem_map_of_mem m)
  | ax φ i h =>
      intro Δ ρ
      show Deriv _ _ _ _ (.holds (rename ρ (emb nilR φ)) (rename ρ i))
      rw [rename_emb _ _ _ nilR (fun v => by cases v)]
      exact .ax φ _ h
  | impI _ ih => exact fun ρ => .impI (ih ρ)
  | impE _ _ ih1 ih2 => exact fun ρ => .impE (ih1 ρ) (ih2 ρ)
  | byContra _ ih => exact fun ρ => .byContra (ih ρ)
  | andI _ _ ih1 ih2 => exact fun ρ => .andI (ih1 ρ) (ih2 ρ)
  | andL _ ih => exact fun ρ => .andL (ih ρ)
  | andR _ ih => exact fun ρ => .andR (ih ρ)
  | orL _ ih => exact fun ρ => .orL (ih ρ)
  | orR _ ih => exact fun ρ => .orR (ih ρ)
  | orE _ _ _ ih ih1 ih2 => exact fun ρ => .orE (ih ρ) (ih1 ρ) (ih2 ρ)
  | allI a _ ih =>
      intro Δ ρ
      have := ih (liftR ρ)
      rw [map_rename_wk] at this
      exact .allI a this
  | allE a t _ hok ih =>
      intro Δ ρ
      rw [rename_inst]
      exact .allE a _ (ih ρ) (cert_rename ρ a t hok)
  | exI a t hok _ ih =>
      intro Δ ρ
      have := ih ρ
      rw [rename_inst] at this
      exact .exI a _ (cert_rename ρ a t hok) this
  | exE a _ _ ih1 ih2 =>
      intro Δ ρ
      have := ih2 (liftR ρ)
      rw [List.map_cons, map_rename_wk, rename_liftR_wk] at this
      exact .exE a (ih1 ρ) this
  | refl a t => exact fun ρ => .refl a _
  | symm a _ ih => exact fun ρ => .symm a (ih ρ)
  | trans a _ _ ih1 ih2 => exact fun ρ => .trans a (ih1 ρ) (ih2 ρ)
  | subst a φ hp _ _ ih1 ih2 =>
      intro Δ ρ
      have h2 := ih2 ρ
      rw [rename_inst] at h2 ⊢
      exact .subst a _ hp (ih1 ρ) h2
  | funExt _ ih =>
      intro Δ ρ
      have := ih ρ
      simp only [rename, rename_liftR_wk] at this
      exact .funExt this
  | funApp _ ih =>
      intro Δ ρ
      have := Deriv.funApp (ih ρ)
      simp only [rename, rename_liftR_wk]
      exact this
  | wExt _ ih =>
      intro Δ ρ
      have := ih ρ
      simp only [rename, rename_liftR_wk] at this
      exact .wExt this
  | wApp _ ih =>
      intro Δ ρ
      have := Deriv.wApp (ih ρ)
      simp only [rename, rename_liftR_wk]
      exact this
  | propExt _ _ ih1 ih2 => exact fun ρ => .propExt (ih1 ρ) (ih2 ρ)
  | betaL body x =>
      intro Δ ρ
      show Deriv _ _ _ _ (.eq _ (.appL (.lamL (rename (liftR ρ) body)) (rename ρ x)) (rename ρ (inst body x)))
      rw [rename_inst]
      exact .betaL _ _
  | betaWI φ i _ ih =>
      intro Δ ρ
      have := ih ρ
      rw [rename_inst] at this
      exact .betaWI _ _ this
  | betaWE φ i _ ih =>
      intro Δ ρ
      have := Deriv.betaWE _ _ (ih ρ)
      rw [rename_inst]
      exact this
  | leib a r M i h1 h2 _ _ ih1 ih2 =>
      intro Δ ρ
      have e : ∀ s : HTerm _ (.L a), rename ρ (inst (.holds (emb (liftL r) M) (wk i)) s)
          = inst (.holds (emb (liftL (fun v => ρ (r v))) M) (wk (rename ρ i))) (rename ρ s) := by
        intro s
        rw [rename_inst]
        simp only [rename, rename_liftR_wk]
        rw [rename_emb M (liftR ρ) (liftL r) (liftL (fun v => ρ (r v))) (fun v => by cases v <;> rfl)]
      have h := ih2 ρ
      rw [e] at h ⊢
      exact .leib a _ M _ (cert_rename ρ _ _ h1) (cert_rename ρ _ _ h2) (ih1 ρ) h

/-- Weakening of a derivation by a fresh variable. -/
theorem Deriv.wkD {T : Tm [] .s → Prop} {Γ hs φ} (d : Deriv T (fun a t => Cert a t) Γ hs φ) (b : HTy) :
    Deriv T (fun a t => Cert a t) (b :: Γ) (hs.map wk) (wk φ) :=
  d.ren (fun v => .succ v)



/-! ## Labelled rules for `𝓛` as derived rules of the certified calculus

`Lf r φ i` is `⟦φ⟧ i`, the `𝓛`-formula `φ` (parameters read through `r`) at the world `i`.
Each rule below is a derived rule of `Deriv T Cert`; `∀`-elimination and `∃`-introduction at a
type of `𝓛` take an `𝓛`-term as instance, so the side condition `Cert` is discharged once here. -/

abbrev DC (T : Tm [] .s → Prop) := Deriv T (fun a t => Cert a t)

def Lf (r : LRen Γ' Γ) (φ : Tm Γ' .s) (i : HTerm Γ .w) : HTerm Γ .o := .holds (emb r φ) i

theorem cert_emb (r : LRen Γ' Γ) (t : Tm Γ' a) : Cert (.L a) (emb r t) := ⟨_, t, r, rfl⟩

theorem sub0_shL (r : LRen Γ' Γ) (x : Tm Γ' u) (i : HTerm Γ .w) :
    subst (sub0 i) (emb (shL r) x) = emb r x :=
  subst_emb_ren x _ _ _ (fun _ => rfl)

theorem sub0_shL2 (r : LRen Γ' Γ) (x : Tm Γ' u) (i : HTerm Γ .w) :
    subst (liftS (a := .w) (sub0 i)) (emb (shL (shL r)) x) = emb (shL r) x :=
  subst_emb_ren x _ _ _ (fun _ => rfl)

theorem sub0_liftL (r : LRen Γ' Γ) (x : Tm (a :: Γ') u) (i : HTerm Γ .w) :
    subst (liftS (a := .L a) (sub0 i)) (emb (liftL (shL r)) x) = emb (liftL r) x :=
  subst_emb_ren x _ _ _ (fun v => by cases v <;> rfl)

theorem wk_Lf (r : LRen Γ' Γ) (φ : Tm Γ' .s) (i : HTerm Γ .w) :
    wk (b := b) (Lf r φ i) = Lf (shL r) φ (wk i) := by
  show HTerm.holds (rename _ (emb r φ)) (rename _ i) = _
  rw [rename_emb _ _ _ (shL r) (fun _ => rfl)]; rfl

theorem emb_congr (t : Tm Γ' u) (r r' : LRen Γ' Γ) (h : ∀ {u} (v : Var Γ' u), r v = r' v) :
    emb r t = emb r' t := by
  have := subst_emb_ren t (fun v => .var v) r r' (fun v => by rw [h])
  rwa [subst_id _ _ (fun _ => rfl)] at this

section rules
variable {T : Tm [] .s → Prop} {Γ' : List FTy} {Γ : List HTy} {hs : List (HTerm Γ .o)}
  {r : LRen Γ' Γ} {i j : HTerm Γ .w}

theorem L_ax {φ : Tm [] .s} (h : T φ) (r : LRen [] Γ) (i : HTerm Γ .w) : DC T Γ hs (Lf r φ i) := by
  have := Deriv.ax (ok := fun a t => Cert a t) (hs := hs) φ i h
  rwa [emb_congr φ nilR r (fun v => by cases v)] at this

theorem L_topI : DC T Γ hs (Lf r .top i) :=
  Deriv.betaWI _ _ (Deriv.impI (Deriv.hyp (List.mem_cons_self ..)))

theorem L_botE {φ : HTerm Γ .o} (d : DC T Γ hs (Lf r .bot i)) : DC T Γ hs φ :=
  Deriv.exFalso (Deriv.betaWE _ _ d)

end rules

theorem inst_holds (p : HTerm (a :: Γ) (.L .s)) (k : HTerm (a :: Γ) .w) (t : HTerm Γ a) :
    inst (.holds p k) t = .holds (inst p t) (inst k t) := rfl

theorem inst_Lf_shL (r : LRen Γ' Γ) (x : Tm Γ' .s) (j : HTerm Γ .w) :
    inst (Lf (shL r) x var0) j = Lf r x j := by
  show HTerm.holds (subst (sub0 j) (emb (shL r) x)) j = _
  rw [sub0_shL]; rfl

theorem inst_Lf_liftL (r : LRen Γ' Γ) (b : Tm (a :: Γ') .s) (i : HTerm Γ .w) (t : Tm Γ' a) :
    inst (Lf (liftL r) b (wk i)) (emb r t) = Lf r (instL b t) i := by
  show HTerm.holds (inst (emb (liftL r) b) (emb r t)) (inst (wk i) (emb r t)) = _
  rw [inst_emb, inst_wk]; rfl

section rules2
variable {T : Tm [] .s → Prop} {Γ' : List FTy} {Γ : List HTy} {hs : List (HTerm Γ .o)}
  {r : LRen Γ' Γ} {i j : HTerm Γ .w}

theorem body_neg (x : Tm Γ' .s) :
    inst (.imp (.holds (emb (shL r) x) var0) .bot) i = .imp (Lf r x i) .bot := by
  show HTerm.imp (.holds (subst (sub0 i) (emb (shL r) x)) i) .bot = _
  rw [sub0_shL]; rfl

theorem body_bin (x y : Tm Γ' .s) (c : HTerm Γ .o → HTerm Γ .o → HTerm Γ .o)
    (c' : HTerm (.w :: Γ) .o → HTerm (.w :: Γ) .o → HTerm (.w :: Γ) .o)
    (hc : ∀ p q, inst (c' p q) i = c (inst p i) (inst q i)) :
    inst (c' (.holds (emb (shL r) x) var0) (.holds (emb (shL r) y) var0)) i =
      c (Lf r x i) (Lf r y i) := by
  rw [hc]
  show c (.holds (subst (sub0 i) (emb (shL r) x)) i) (.holds (subst (sub0 i) (emb (shL r) y)) i) = _
  rw [sub0_shL, sub0_shL]; rfl

theorem L_negI {x : Tm Γ' .s} (d : DC T Γ hs (.imp (Lf r x i) .bot)) : DC T Γ hs (Lf r (.neg x) i) :=
  Deriv.betaWI _ _ (by rw [body_neg]; exact d)

theorem L_negE {x : Tm Γ' .s} (d : DC T Γ hs (Lf r (.neg x) i)) : DC T Γ hs (.imp (Lf r x i) .bot) := by
  have := Deriv.betaWE _ _ d; rwa [body_neg] at this

theorem L_impI {x y : Tm Γ' .s} (d : DC T Γ hs (.imp (Lf r x i) (Lf r y i))) :
    DC T Γ hs (Lf r (.imp x y) i) :=
  Deriv.betaWI _ _ (by rw [body_bin x y .imp .imp (fun _ _ => rfl)]; exact d)

theorem L_impE {x y : Tm Γ' .s} (d : DC T Γ hs (Lf r (.imp x y) i)) :
    DC T Γ hs (.imp (Lf r x i) (Lf r y i)) := by
  have := Deriv.betaWE _ _ d; rwa [body_bin x y .imp .imp (fun _ _ => rfl)] at this

theorem L_andI {x y : Tm Γ' .s} (d : DC T Γ hs (.and (Lf r x i) (Lf r y i))) :
    DC T Γ hs (Lf r (.and x y) i) :=
  Deriv.betaWI _ _ (by rw [body_bin x y .and .and (fun _ _ => rfl)]; exact d)

theorem L_andE {x y : Tm Γ' .s} (d : DC T Γ hs (Lf r (.and x y) i)) :
    DC T Γ hs (.and (Lf r x i) (Lf r y i)) := by
  have := Deriv.betaWE _ _ d; rwa [body_bin x y .and .and (fun _ _ => rfl)] at this

theorem L_orI {x y : Tm Γ' .s} (d : DC T Γ hs (.or (Lf r x i) (Lf r y i))) :
    DC T Γ hs (Lf r (.or x y) i) :=
  Deriv.betaWI _ _ (by rw [body_bin x y .or .or (fun _ _ => rfl)]; exact d)

theorem L_orE {x y : Tm Γ' .s} (d : DC T Γ hs (Lf r (.or x y) i)) :
    DC T Γ hs (.or (Lf r x i) (Lf r y i)) := by
  have := Deriv.betaWE _ _ d; rwa [body_bin x y .or .or (fun _ _ => rfl)] at this

theorem body_eq (a : FTy) (x y : Tm Γ' a) :
    inst (.eq (.L a) (emb (shL r) x) (emb (shL r) y)) i = .eq (.L a) (emb r x) (emb r y) := by
  show HTerm.eq _ (subst (sub0 i) (emb (shL r) x)) (subst (sub0 i) (emb (shL r) y)) = _
  rw [sub0_shL, sub0_shL]

theorem L_eqI {a : FTy} {x y : Tm Γ' a} (d : DC T Γ hs (.eq (.L a) (emb r x) (emb r y))) :
    DC T Γ hs (Lf r (.eq a x y) i) :=
  Deriv.betaWI _ _ (by rw [body_eq]; exact d)

theorem L_eqE {a : FTy} {x y : Tm Γ' a} (d : DC T Γ hs (Lf r (.eq a x y) i)) :
    DC T Γ hs (.eq (.L a) (emb r x) (emb r y)) := by
  have := Deriv.betaWE _ _ d; rwa [body_eq] at this

theorem body_box (x : Tm Γ' .s) :
    inst (.all .w (.imp (.rel (.var (.succ .zero)) (.var .zero))
      (.holds (emb (shL (shL r)) x) (.var .zero)))) i =
    .all .w (.imp (.rel (wk i) var0) (Lf (shL r) x var0)) := by
  show HTerm.all .w (.imp (.rel (wk i) var0)
    (.holds (subst (liftS (sub0 i)) (emb (shL (shL r)) x)) var0)) = _
  rw [sub0_shL2]; rfl

theorem L_boxI {x : Tm Γ' .s}
    (d : DC T (.w :: Γ) (.rel (wk i) var0 :: hs.map wk) (Lf (shL r) x var0)) :
    DC T Γ hs (Lf r (.box x) i) :=
  Deriv.betaWI _ _ (by rw [body_box]; exact Deriv.allI .w (Deriv.impI d))

theorem L_boxE {x : Tm Γ' .s} (d : DC T Γ hs (Lf r (.box x) i)) (dj : DC T Γ hs (.rel i j)) :
    DC T Γ hs (Lf r x j) := by
  have h1 := Deriv.betaWE _ _ d
  rw [body_box] at h1
  have h2 := Deriv.allE .w j h1 trivial
  have e : inst (HTerm.imp (.rel (wk i) var0) (Lf (shL r) x var0)) j = .imp (.rel i j) (Lf r x j) := by
    show HTerm.imp (.rel (inst (wk i) j) j) (inst (Lf (shL r) x var0) j) = _
    rw [inst_wk, inst_Lf_shL]
  rw [e] at h2
  exact Deriv.impE h2 dj

theorem body_all (a : FTy) (b : Tm (a :: Γ') .s) :
    inst (.all (.L a) (.holds (emb (liftL (shL r)) b) (.var (.succ .zero)))) i =
    .all (.L a) (Lf (liftL r) b (wk i)) := by
  show HTerm.all (.L a) (.holds (subst (liftS (sub0 i)) (emb (liftL (shL r)) b)) (wk i)) = _
  rw [sub0_liftL]; rfl

theorem L_allI {a : FTy} {b : Tm (a :: Γ') .s}
    (d : DC T (.L a :: Γ) (hs.map wk) (Lf (liftL r) b (wk i))) : DC T Γ hs (Lf r (.all a b) i) :=
  Deriv.betaWI _ _ (by rw [body_all]; exact Deriv.allI _ d)

theorem L_allE {a : FTy} {b : Tm (a :: Γ') .s} (d : DC T Γ hs (Lf r (.all a b) i)) (t : Tm Γ' a) :
    DC T Γ hs (Lf r (instL b t) i) := by
  have h1 := Deriv.betaWE _ _ d
  rw [body_all] at h1
  have h2 := Deriv.allE (.L a) (emb r t) h1 (cert_emb r t)
  rwa [inst_Lf_liftL] at h2

theorem body_ex (a : FTy) (b : Tm (a :: Γ') .s) :
    inst (.ex (.L a) (.holds (emb (liftL (shL r)) b) (.var (.succ .zero)))) i =
    .ex (.L a) (Lf (liftL r) b (wk i)) := by
  show HTerm.ex (.L a) (.holds (subst (liftS (sub0 i)) (emb (liftL (shL r)) b)) (wk i)) = _
  rw [sub0_liftL]; rfl

theorem L_exI {a : FTy} {b : Tm (a :: Γ') .s} (t : Tm Γ' a) (d : DC T Γ hs (Lf r (instL b t) i)) :
    DC T Γ hs (Lf r (.ex a b) i) :=
  Deriv.betaWI _ _ (by
    rw [body_ex]
    exact Deriv.exI (.L a) (emb r t) (cert_emb r t) (by rw [inst_Lf_liftL]; exact d))

theorem L_exE {a : FTy} {b : Tm (a :: Γ') .s} {χ : HTerm Γ .o} (d : DC T Γ hs (Lf r (.ex a b) i))
    (k : DC T (.L a :: Γ) (Lf (liftL r) b (wk i) :: hs.map wk) (wk χ)) : DC T Γ hs χ := by
  have h1 := Deriv.betaWE _ _ d
  rw [body_ex] at h1
  exact Deriv.exE _ h1 k

theorem body_allE (b : Tm (.e :: Γ') .s) :
    inst (.all (.L .e) (.imp (.act (.var .zero) (.var (.succ .zero)))
      (.holds (emb (liftL (shL r)) b) (.var (.succ .zero))))) i =
    .all (.L .e) (.imp (.act var0 (wk i)) (Lf (liftL r) b (wk i))) := by
  show HTerm.all (.L .e) (.imp (.act var0 (wk i))
    (.holds (subst (liftS (sub0 i)) (emb (liftL (shL r)) b)) (wk i))) = _
  rw [sub0_liftL]; rfl

theorem L_allEI {b : Tm (.e :: Γ') .s}
    (d : DC T (.L .e :: Γ) (.act var0 (wk i) :: hs.map wk) (Lf (liftL r) b (wk i))) :
    DC T Γ hs (Lf r (.allE b) i) :=
  Deriv.betaWI _ _ (by rw [body_allE]; exact Deriv.allI _ (Deriv.impI d))

theorem L_allEE {b : Tm (.e :: Γ') .s} (d : DC T Γ hs (Lf r (.allE b) i)) (t : Tm Γ' .e)
    (da : DC T Γ hs (.act (emb r t) i)) : DC T Γ hs (Lf r (instL b t) i) := by
  have h1 := Deriv.betaWE _ _ d
  rw [body_allE] at h1
  have h2 := Deriv.allE (.L .e) (emb r t) h1 (cert_emb r t)
  have e : inst (HTerm.imp (.act var0 (wk i)) (Lf (liftL r) b (wk i))) (emb r t) =
      .imp (.act (emb r t) i) (Lf r (instL b t) i) := by
    show HTerm.imp (.act (emb r t) (inst (wk i) (emb r t))) (inst (Lf (liftL r) b (wk i)) (emb r t)) = _
    rw [inst_wk, inst_Lf_liftL]
  rw [e] at h2
  exact Deriv.impE h2 da

theorem body_exE (b : Tm (.e :: Γ') .s) :
    inst (.ex (.L .e) (.and (.act (.var .zero) (.var (.succ .zero)))
      (.holds (emb (liftL (shL r)) b) (.var (.succ .zero))))) i =
    .ex (.L .e) (.and (.act var0 (wk i)) (Lf (liftL r) b (wk i))) := by
  show HTerm.ex (.L .e) (.and (.act var0 (wk i))
    (.holds (subst (liftS (sub0 i)) (emb (liftL (shL r)) b)) (wk i))) = _
  rw [sub0_liftL]; rfl

theorem L_exEI {b : Tm (.e :: Γ') .s} (t : Tm Γ' .e) (da : DC T Γ hs (.act (emb r t) i))
    (d : DC T Γ hs (Lf r (instL b t) i)) : DC T Γ hs (Lf r (.exE b) i) :=
  Deriv.betaWI _ _ (by
    rw [body_exE]
    refine Deriv.exI (.L .e) (emb r t) (cert_emb r t) ?_
    show DC T Γ hs (.and (.act (emb r t) (inst (wk i) (emb r t))) (inst (Lf (liftL r) b (wk i)) (emb r t)))
    rw [inst_wk, inst_Lf_liftL]
    exact Deriv.andI da d)

theorem L_exEE {b : Tm (.e :: Γ') .s} {χ : HTerm Γ .o} (d : DC T Γ hs (Lf r (.exE b) i))
    (k : DC T (.L .e :: Γ) (.and (.act var0 (wk i)) (Lf (liftL r) b (wk i)) :: hs.map wk) (wk χ)) :
    DC T Γ hs χ := by
  have h1 := Deriv.betaWE _ _ d
  rw [body_exE] at h1
  exact Deriv.exE _ h1 k

/-- `β` at `σ`, both directions. -/
theorem L_betaE {a : FTy} {b : Tm (a :: Γ') .s} {x : Tm Γ' a}
    (d : DC T Γ hs (Lf r (.app (.lam b) x) i)) : DC T Γ hs (Lf r (instL b x) i) := by
  have e := Deriv.betaL (T := T) (ok := fun a t => Cert a t) (hs := hs) (emb (liftL r) b) (emb r x)
  have h := Deriv.subst (.L .s) (.holds var0 (wk i)) rfl e (by
    rw [inst_holds, inst_wk]; exact d)
  rw [inst_holds, inst_wk, inst_emb] at h
  exact h

theorem L_betaI {a : FTy} {b : Tm (a :: Γ') .s} {x : Tm Γ' a}
    (d : DC T Γ hs (Lf r (instL b x) i)) : DC T Γ hs (Lf r (.app (.lam b) x) i) := by
  have e := Deriv.symm _ (Deriv.betaL (T := T) (ok := fun a t => Cert a t) (hs := hs)
    (emb (liftL r) b) (emb r x))
  have h := Deriv.subst (.L .s) (.holds var0 (wk i)) rfl e (by
    rw [inst_holds, inst_wk, inst_emb]; exact d)
  rw [inst_holds, inst_wk] at h
  exact h

/-- Leibniz at a plain type of `𝓛`, with an `𝓛`-motive. -/
theorem L_rw {a : FTy} (hp : plainF a = true) {x y : Tm Γ' a} (M : Tm (a :: Γ') .s)
    (e : DC T Γ hs (.eq (.L a) (emb r x) (emb r y))) (d : DC T Γ hs (Lf r (instL M x) i)) :
    DC T Γ hs (Lf r (instL M y) i) := by
  have h := Deriv.subst (.L a) (Lf (liftL r) M (wk i)) hp e (by rw [inst_Lf_liftL]; exact d)
  rwa [inst_Lf_liftL] at h

/-- Leibniz at every type of `𝓛`, with an `𝓛`-motive. -/
theorem L_leib {a : FTy} {x y : Tm Γ' a} (M : Tm (a :: Γ') .s)
    (e : DC T Γ hs (.eq (.L a) (emb r x) (emb r y))) (d : DC T Γ hs (Lf r (instL M x) i)) :
    DC T Γ hs (Lf r (instL M y) i) := by
  have d' : DC T Γ hs (inst (.holds (emb (liftL r) M) (wk i)) (emb r x)) := by
    rw [show inst (.holds (emb (liftL r) M) (wk i)) (emb r x) = Lf r (instL M x) i from
      inst_Lf_liftL r M i x]; exact d
  have h := Deriv.leib a r M i (cert_emb r x) (cert_emb r y) e d'
  rwa [show inst (.holds (emb (liftL r) M) (wk i)) (emb r y) = Lf r (instL M y) i from
      inst_Lf_liftL r M i y] at h

end rules2

/-! ## The class is non-empty: full structures -/

/-- The full structure over any frame, actuality and positivity: every object admitted. -/
def fullStr (R : W → W → Prop) (act : D → W → Prop) (P : Den W D th) : Str W D :=
  ⟨R, act, P, fun _ _ => True⟩

theorem eqT_full (R : W → W → Prop) (act : D → W → Prop) (P : Den W D th) :
    ∀ (t : FTy) {x y : Den W D t}, eqT (fullStr R act P) t x y → x = y
  | .e, _, _, h => h
  | .s, _, _, h => h
  | .arr _ b, _, _, h => funext fun z => eqT_full R act P b (h z trivial)

theorem full_closed_resp (R : W → W → Prop) (act : D → W → Prop) (P : Den W D th) :
    Closed (fullStr R act P) ∧ Resp (fullStr R act P) ∧ ∀ x, (fullStr R act P).A .e x :=
  ⟨fun _ _ _ => trivial,
   fun _ _ F _ _ _ _ _ h => by rw [eqT_full R act P _ h]; exact eqT_refl _ _ _,
   fun _ => trivial⟩

/-! ## Leibniz's law at `σ → σ` is derivable -/

/-- `∀ f₁ f₂ : σ→σ. ∀ F : (σ→σ)→σ. f₁ = f₂ → F f₁ = F f₂` (the sentence of th's `LeibnizGap`). -/
def Leib : Tm [] .s :=
  .all (.arr .s .s) (.all (.arr .s .s) (.all (.arr (.arr .s .s) .s)
    (.imp (.eq (.arr .s .s) (.var (.succ (.succ .zero))) (.var (.succ .zero)))
          (.eq .s (.app (.var .zero) (.var (.succ (.succ .zero))))
                  (.app (.var .zero) (.var (.succ .zero)))))))

/-- The motive: `F f₁ = F □` in the context `□, F, f₂, f₁`. -/
def leibM : Tm (.arr .s .s :: [.arr (.arr .s .s) .s, .arr .s .s, .arr .s .s]) .s :=
  .eq .s (.app (.var (.succ .zero)) (.var (.succ (.succ (.succ .zero)))))
    (.app (.var (.succ .zero)) (.var .zero))

abbrev Γ4 : List HTy := [.L (.arr (.arr .s .s) .s), .L (.arr .s .s), .L (.arr .s .s), .w]
abbrev R3 : LRen [.arr (.arr .s .s) .s, .arr .s .s, .arr .s .s] Γ4 := liftL (liftL (liftL nilR))
abbrev I3 : HTerm Γ4 .w := wk (wk (wk var0))
abbrev leibH : HTerm Γ4 .o :=
  Lf R3 (.eq (.arr .s .s) (.var (.succ (.succ .zero))) (.var (.succ .zero))) I3

theorem leib_derivable {T : Tm [] .s → Prop} : DC T [.w] [] (Lf nilR Leib var0) := by
  refine L_allI (L_allI (L_allI (L_impI (Deriv.impI ?_))))
  -- context: F, f₂, f₁, w; hypothesis `f₁ = f₂` at `w`
  have e : DC T Γ4 [leibH] (.eq (.L (.arr .s .s)) (emb R3 (.var (.succ (.succ .zero))))
      (emb R3 (.var (.succ .zero)))) := L_eqE (Deriv.hyp (List.mem_cons_self ..))
  have d0 : DC T Γ4 [leibH] (Lf R3 (instL leibM (.var (.succ (.succ .zero)))) I3) :=
    L_eqI (Deriv.refl _ _)
  exact L_leib leibM e d0

end Programme.«20261022-1724-ontological».Run3.HOLX

namespace Programme.«20261022-1724-ontological».Run3.HOLX.Flip

open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.HOLX

variable {W D : Type}

/-! ## Symmetric structures -/

/-- A filtration of world bijections (pairs `(f, g)`, `g` the inverse of `f`). -/
structure Sym (R : W → W → Prop) (act : D → W → Prop) (P : Den W D th) where
  Fx : Nat → (W → W) → (W → W) → Prop
  mono : ∀ {n m f g}, n ≤ m → Fx m f g → Fx n f g
  inv : ∀ {n f g}, Fx n f g → Fx n g f
  fg : ∀ {f g}, Fx 0 f g → ∀ w, f (g w) = w
  hR : ∀ {f g}, Fx 0 f g → ∀ w v, R (f w) (f v) ↔ R w v
  hact : ∀ {f g}, Fx 0 f g → ∀ y w, act y (f w) ↔ act y w
  hP : ∀ {f g}, Fx 0 f g → fl f g th P = P
  conj : ∀ {f g}, Fx 0 f g → ∀ n, ∃ m, ∀ c d, Fx m c d →
    Fx n (fun w => f (c (g w))) (fun w => f (d (g w)))

variable {R : W → W → Prop} {act : D → W → Prop} {P : Den W D th}

def Sup (S : Sym R act P) (t : FTy) (x : Den W D t) : Prop :=
  ∃ n, ∀ f g, S.Fx n f g → fl f g t x = x

/-- Carriers: supported, and admitted-to-admitted at arrow types. -/
def AdmF (S : Sym R act P) : (t : FTy) → Den W D t → Prop
  | .e, _ => True
  | .s, q => Sup S .s q
  | .arr a b, F => Sup S (.arr a b) F ∧ ∀ z, AdmF S a z → AdmF S b (F z)

def str (S : Sym R act P) : Str W D := ⟨R, act, P, AdmF S⟩

variable (S : Sym R act P)

theorem sup_of_adm : ∀ (t : FTy) (x : Den W D t), AdmF S t x → Sup S t x
  | .e, _, _ => ⟨0, fun _ _ _ => rfl⟩
  | .s, _, h => h
  | .arr _ _, _, h => h.1

theorem sup_fl {f g : W → W} (h : S.Fx 0 f g) (t : FTy) (x : Den W D t) (hx : Sup S t x) :
    Sup S t (fl f g t x) := by
  obtain ⟨n, hn⟩ := hx
  obtain ⟨m, hm⟩ := S.conj h n
  refine ⟨m, fun c d hcd => ?_⟩
  have h1 : fl g f t (fl c d t (fl f g t x)) = x := by
    rw [fl_comp, fl_comp]; exact hn _ _ (hm c d hcd)
  have h2 := fl_inv (S.fg (S.inv h)) t (fl c d t (fl f g t x))
  rw [h1] at h2; exact h2.symm

theorem adm_fl : ∀ (t : FTy) {f g : W → W}, S.Fx 0 f g → ∀ x, AdmF S t x → AdmF S t (fl f g t x)
  | .e, _, _, _, _, _ => trivial
  | .s, _, _, h, x, hx => sup_fl S h .s x hx
  | .arr a b, f, g, h, F, hF =>
      ⟨sup_fl S h _ F hF.1, fun z hz =>
        adm_fl b h (F (fl g f a z)) (hF.2 _ (adm_fl a (S.inv h) z hz))⟩

theorem forall_fl {f g : W → W} (h : S.Fx 0 f g) (t : FTy) (Q : Den W D t → Prop) :
    (∀ x, AdmF S t x → Q (fl f g t x)) ↔ (∀ x, AdmF S t x → Q x) :=
  ⟨fun hq x hx => by
    have := hq _ (adm_fl S t (S.inv h) x hx)
    rwa [fl_inv (S.fg (S.inv h))] at this,
   fun hq x hx => hq _ (adm_fl S t h x hx)⟩

theorem exists_fl {f g : W → W} (h : S.Fx 0 f g) (t : FTy) (Q : Den W D t → Prop) :
    (∃ x, AdmF S t x ∧ Q (fl f g t x)) ↔ (∃ x, AdmF S t x ∧ Q x) :=
  ⟨fun ⟨x, hx, hq⟩ => ⟨_, adm_fl S t h x hx, hq⟩,
   fun ⟨x, hx, hq⟩ => ⟨fl g f t x, adm_fl S t (S.inv h) x hx, by
     rw [fl_inv (S.fg (S.inv h))]; exact hq⟩⟩

theorem eqT_fl : ∀ (t : FTy) {f g : W → W}, S.Fx 0 f g → ∀ x y,
    eqT (str S) t (fl f g t x) (fl f g t y) ↔ eqT (str S) t x y
  | .e, _, _, _, _, _ => Iff.rfl
  | .s, f, g, h, x, y =>
      ⟨fun e => by
        have := congrArg (fl g f .s) e
        rwa [fl_inv (S.fg h), fl_inv (S.fg h)] at this,
       fun e => e ▸ rfl⟩
  | .arr a b, f, g, h, F, G => by
      show (∀ z, AdmF S a z → eqT (str S) b (fl f g b (F (fl g f a z))) (fl f g b (G (fl g f a z))))
        ↔ ∀ z, AdmF S a z → eqT (str S) b (F z) (G z)
      rw [← forall_fl S h a]
      refine forall_congr' fun z => imp_congr_right fun _ => ?_
      rw [fl_inv (S.fg h), eqT_fl b h]

def flEnv (f g : W → W) : (Γ : List FTy) → Env W D Γ → Env W D Γ
  | [], _ => ()
  | t :: Γ, ρ => (fl f g t ρ.1, flEnv f g Γ ρ.2)

theorem get_fl (f g : W → W) : ∀ {Γ t} (i : Var Γ t) (ρ : Env W D Γ),
    i.get (flEnv f g Γ ρ) = fl f g t (i.get ρ)
  | _, _, .zero, _ => rfl
  | _, _, .succ i, ρ => get_fl f g i ρ.2

/-- **Equivariance** of evaluation under every symmetry. -/
theorem eval_act {f g : W → W} (h : S.Fx 0 f g) :
    ∀ {Γ t} (tm : Tm Γ t) (ρ : Env W D Γ),
      eval (str S) tm (flEnv f g Γ ρ) = fl f g t (eval (str S) tm ρ)
  | _, _, .var i, ρ => get_fl f g i ρ
  | _, _, .app (a := a) F x, ρ => by
      show eval _ F _ (eval _ x _) = _
      rw [eval_act h F ρ, eval_act h x ρ]
      show fl f g _ (eval _ F ρ (fl g f a (fl f g a (eval _ x ρ)))) = _
      rw [fl_inv (S.fg h)]; rfl
  | _, _, .lam (a := a) b, ρ => by
      funext z
      have e := eval_act h b (fl g f a z, ρ)
      have e2 : flEnv f g (a :: _) (fl g f a z, ρ) = (z, flEnv f g _ ρ) := by
        show (fl f g a (fl g f a z), _) = _
        rw [fl_inv (S.fg (S.inv h))]
      rw [e2] at e
      exact e
  | _, _, .top, _ => rfl
  | _, _, .bot, _ => rfl
  | _, _, .neg x, ρ => by
      funext w; show (¬ _) = _; rw [eval_act h x ρ]; rfl
  | _, _, .and x y, ρ => by
      funext w; show (_ ∧ _) = _; rw [eval_act h x ρ, eval_act h y ρ]; rfl
  | _, _, .or x y, ρ => by
      funext w; show (_ ∨ _) = _; rw [eval_act h x ρ, eval_act h y ρ]; rfl
  | _, _, .imp x y, ρ => by
      funext w; show (_ → _) = _; rw [eval_act h x ρ, eval_act h y ρ]; rfl
  | _, _, .box x, ρ => by
      funext w
      show (∀ v, R w v → eval (str S) x (flEnv f g _ ρ) v) = (∀ v, R (f w) v → eval (str S) x ρ v)
      rw [eval_act h x ρ]
      apply propext
      constructor
      · intro hv v hr
        have := hv (g v) (by rw [← S.hR h, S.fg h]; exact hr)
        simpa [fl, S.fg h] using this
      · intro hv v hr
        exact hv _ ((S.hR h w v).2 hr)
  | _, _, .all t b, ρ => by
      funext w
      show (∀ x, AdmF S t x → eval (str S) b (x, flEnv f g _ ρ) w) =
        (∀ x, AdmF S t x → eval (str S) b (x, ρ) (f w))
      apply propext
      rw [← forall_fl S h t]
      refine forall_congr' fun x => imp_congr_right fun _ => ?_
      exact Iff.of_eq (congrFun (eval_act h b (x, ρ)) w)
  | _, _, .ex t b, ρ => by
      funext w
      show (∃ x, AdmF S t x ∧ eval (str S) b (x, flEnv f g _ ρ) w) =
        (∃ x, AdmF S t x ∧ eval (str S) b (x, ρ) (f w))
      apply propext
      rw [← exists_fl S h t]
      refine exists_congr fun x => and_congr_right fun _ => ?_
      exact Iff.of_eq (congrFun (eval_act h b (x, ρ)) w)
  | _, _, .allE b, ρ => by
      funext w
      show (∀ y, act y w → eval (str S) b (y, flEnv f g _ ρ) w) =
        (∀ y, act y (f w) → eval (str S) b (y, ρ) (f w))
      apply propext
      refine forall_congr' fun y => ?_
      rw [S.hact h]
      exact imp_congr_right fun _ => Iff.of_eq (congrFun (eval_act h b (y, ρ)) w)
  | _, _, .exE b, ρ => by
      funext w
      show (∃ y, act y w ∧ eval (str S) b (y, flEnv f g _ ρ) w) =
        (∃ y, act y (f w) ∧ eval (str S) b (y, ρ) (f w))
      apply propext
      refine exists_congr fun y => ?_
      rw [S.hact h]
      exact and_congr_right fun _ => Iff.of_eq (congrFun (eval_act h b (y, ρ)) w)
  | _, _, .eq a x y, ρ => by
      funext w
      show eqT (str S) a (eval _ x _) (eval _ y _) = eqT (str S) a (eval _ x ρ) (eval _ y ρ)
      rw [eval_act h x ρ, eval_act h y ρ]
      exact propext (eqT_fl S a h _ _)
  | _, _, .pos, _ => (S.hP h).symm

theorem env_sup : ∀ (Γ : List FTy) (ρ : Env W D Γ), EnvA (str S) Γ ρ →
    ∃ N, ∀ f g, S.Fx N f g → flEnv f g Γ ρ = ρ
  | [], _, _ => ⟨0, fun _ _ _ => rfl⟩
  | t :: Γ, (x, r), ⟨h1, h2⟩ => by
      obtain ⟨n, hn⟩ := sup_of_adm S t x h1
      obtain ⟨m, hm⟩ := env_sup Γ r h2
      refine ⟨max n m, fun f g hfg => ?_⟩
      show (fl f g t x, flEnv f g Γ r) = (x, r)
      rw [hn f g (S.mono (Nat.le_max_left n m) hfg), hm f g (S.mono (Nat.le_max_right n m) hfg)]

theorem sup_eval {Γ t} (tm : Tm Γ t) (ρ : Env W D Γ) (hρ : EnvA (str S) Γ ρ) :
    Sup S t (eval (str S) tm ρ) := by
  obtain ⟨N, hN⟩ := env_sup S Γ ρ hρ
  refine ⟨N, fun f g hfg => ?_⟩
  rw [← eval_act S (S.mono (Nat.zero_le N) hfg) tm ρ, hN f g hfg]

theorem sup_app {a b : FTy} {F : Den W D (.arr a b)} {x : Den W D a}
    (hF : Sup S (.arr a b) F) (hx : Sup S a x) : Sup S b (F x) := by
  obtain ⟨n, hn⟩ := hF
  obtain ⟨m, hm⟩ := hx
  refine ⟨max n m, fun f g hfg => ?_⟩
  have e1 := hn f g (S.mono (Nat.le_max_left n m) hfg)
  have e2 := hm g f (S.inv (S.mono (Nat.le_max_right n m) hfg))
  have := congrFun e1 x
  show fl f g b (F x) = F x
  calc fl f g b (F x) = fl f g b (F (fl g f a x)) := by rw [e2]
    _ = F x := this

theorem get_adm : ∀ {Γ t} (i : Var Γ t) (ρ : Env W D Γ), EnvA (str S) Γ ρ →
    AdmF S t (i.get ρ)
  | _, _, .zero, _, h => h.1
  | _, _, .succ i, ρ, h => get_adm i ρ.2 h.2

/-- **Fact (a), full language.** -/
theorem closed : Closed (str S)
  | _, _, .var i, ρ, hρ => get_adm S i ρ hρ
  | _, _, .app F x, ρ, hρ => (closed F ρ hρ).2 _ (closed x ρ hρ)
  | _, _, .lam b, ρ, hρ => ⟨sup_eval S (.lam b) ρ hρ, fun z hz => closed b (z, ρ) ⟨hz, hρ⟩⟩
  | _, _, .pos, ρ, hρ => ⟨sup_eval S .pos ρ hρ, fun ψ hψ =>
      sup_app S (sup_eval S .pos ρ hρ) (sup_of_adm S _ ψ hψ)⟩
  | _, _, .top, ρ, hρ => sup_eval S .top ρ hρ
  | _, _, .bot, ρ, hρ => sup_eval S .bot ρ hρ
  | _, _, .neg x, ρ, hρ => sup_eval S (.neg x) ρ hρ
  | _, _, .and x y, ρ, hρ => sup_eval S (.and x y) ρ hρ
  | _, _, .or x y, ρ, hρ => sup_eval S (.or x y) ρ hρ
  | _, _, .imp x y, ρ, hρ => sup_eval S (.imp x y) ρ hρ
  | _, _, .box x, ρ, hρ => sup_eval S (.box x) ρ hρ
  | _, _, .all a b, ρ, hρ => sup_eval S (.all a b) ρ hρ
  | _, _, .ex a b, ρ, hρ => sup_eval S (.ex a b) ρ hρ
  | _, _, .allE b, ρ, hρ => sup_eval S (.allE b) ρ hρ
  | _, _, .exE b, ρ, hρ => sup_eval S (.exE b) ρ hρ
  | _, _, .eq a x y, ρ, hρ => sup_eval S (.eq a x y) ρ hρ


/-! ## The flip structure on `2^ℕ` -/

def Cw : Type := Nat → Bool

def xorw (w d : Cw) : Cw := fun n => xor (w n) (d n)

theorem xorw_xorw (w d : Cw) : xorw (xorw w d) d = w := by
  funext n; simp [xorw]

def Rf : Cw → Cw → Prop := fun w v => v = w
def actf : Unit → Cw → Prop := fun _ _ => True
def Pf : Den Cw Unit th := fun φ w => φ () w

/-- `Fx n f g`: `f = g` is the flip by some `d` vanishing below `n`. -/
def Fxf (n : Nat) (f g : Cw → Cw) : Prop :=
  ∃ d : Cw, (∀ k, k < n → d k = false) ∧ f = (fun w => xorw w d) ∧ g = (fun w => xorw w d)

def symf : Sym (W := Cw) (D := Unit) Rf actf Pf where
  Fx := Fxf
  mono := by
    intro n m f g hnm ⟨d, hd, hf, hg⟩
    exact ⟨d, fun k hk => hd k (Nat.lt_of_lt_of_le hk hnm), hf, hg⟩
  inv := by
    intro n f g ⟨d, hd, hf, hg⟩
    exact ⟨d, hd, hg, hf⟩
  fg := by
    intro f g ⟨d, _, hf, hg⟩ w
    subst hf; subst hg; exact xorw_xorw w d
  hR := by
    intro f g ⟨d, _, hf, _⟩ w v
    subst hf
    show xorw v d = xorw w d ↔ v = w
    constructor
    · intro h; have := congrArg (fun u => xorw u d) h; simpa [xorw_xorw] using this
    · intro h; rw [h]
  hact := by intro _ _ _ _ _; exact Iff.rfl
  hP := by
    intro f g ⟨d, _, hf, hg⟩
    subst hf; subst hg
    funext z w
    show z () (xorw (xorw w d) d) = z () w
    rw [xorw_xorw]
  conj := by
    intro f g ⟨d, _, hf, hg⟩ n
    refine ⟨n, fun c c' ⟨e, he, hc, hc'⟩ => ⟨e, he, ?_, ?_⟩⟩ <;>
    · subst hf; subst hg; subst hc; subst hc'
      funext w; funext k; simp only [xorw]; cases w k <;> cases d k <;> cases e k <;> rfl

abbrev SF : Str Cw Unit := str symf

theorem closed_SF : Closed SF := closed symf

theorem allE_SF : ∀ x, SF.A .e x := fun _ => trivial

/-! ## The witnesses -/

open Classical in
noncomputable def f₂ : Den Cw Unit (.arr .s .s) := fun p => if Sup symf .s p then p else fun _ => False

def f₁ : Den Cw Unit (.arr .s .s) := fun p => p

def Fw : Den Cw Unit (.arr (.arr .s .s) .s) := fun f x => f (fun y => y = x) x

theorem fx0 {f g : Cw → Cw} (h : Fxf 0 f g) : ∃ d : Cw, f = (fun w => xorw w d) ∧ g = (fun w => xorw w d) :=
  let ⟨d, _, hf, hg⟩ := h; ⟨d, hf, hg⟩

theorem sup_fl_iff {f g : Cw → Cw} (h : symf.Fx 0 f g) (q : Den Cw Unit .s) :
    Sup symf .s (fl f g .s q) ↔ Sup symf .s q := by
  constructor
  · intro hq
    have := sup_fl symf (symf.inv h) .s _ hq
    rwa [fl_inv (symf.fg h)] at this
  · exact sup_fl symf h .s q

theorem adm_f₁ : SF.A (.arr .s .s) f₁ :=
  ⟨⟨0, fun f g h => by
    funext z; show fl f g .s (fl g f .s z) = z; exact fl_inv (symf.fg (symf.inv h)) .s z⟩,
   fun _ hz => hz⟩

theorem adm_f₂ : SF.A (.arr .s .s) f₂ := by
  refine ⟨⟨0, fun f g h => ?_⟩, fun z hz => ?_⟩
  · funext z
    show fl f g .s (f₂ (fl g f .s z)) = f₂ z
    unfold f₂
    by_cases hz : Sup symf .s z
    · have hz' : Sup symf .s (fl g f .s z) := (sup_fl_iff (symf.inv h) z).2 hz
      rw [if_pos hz', if_pos hz]; exact fl_inv (symf.fg (symf.inv h)) .s z
    · have hz' : ¬ Sup symf .s (fl g f .s z) := fun h' => hz ((sup_fl_iff (symf.inv h) z).1 h')
      rw [if_neg hz', if_neg hz]; rfl
  · show AdmF symf .s (f₂ z)
    have hz' : Sup symf .s z := hz
    unfold f₂; rw [if_pos hz']; exact hz

theorem adm_Fw : SF.A (.arr (.arr .s .s) .s) Fw := by
  have hsup : Sup symf (.arr (.arr .s .s) .s) Fw := by
    refine ⟨0, fun f g h => ?_⟩
    obtain ⟨d, hf, hg⟩ := fx0 h
    subst hf; subst hg
    funext k x
    show k (fun w => (fun y => y = xorw x d) (xorw w d)) (xorw (xorw x d) d) = k (fun y => y = x) x
    rw [xorw_xorw]
    congr 1
    funext w; apply propext; constructor
    · intro e; have := congrArg (fun u => xorw u d) e; simpa [xorw_xorw] using this
    · intro e; rw [e]
  exact ⟨hsup, fun z hz => sup_app symf hsup (sup_of_adm symf _ z hz)⟩

theorem eq_f₁f₂ : eqT SF (.arr .s .s) f₁ f₂ := by
  intro z hz
  show z = f₂ z
  have hz' : Sup symf .s z := hz
  unfold f₂; rw [if_pos hz']

/-- Singletons are not supported. -/
theorem not_sup_singleton (x : Cw) : ¬ Sup symf .s (fun y => y = x) := by
  rintro ⟨n, hn⟩
  let d : Cw := fun k => decide (k = n)
  have hd : symf.Fx n (fun w => xorw w d) (fun w => xorw w d) :=
    ⟨d, fun k hk => by simp [d, Nat.ne_of_lt hk], rfl, rfl⟩
  have e := congrFun (hn _ _ hd) x
  have e' : xorw x d = x := by
    have : (xorw x d = x) = (x = x) := e
    rw [this]
  have := congrFun e' n
  simp [xorw, d] at this

theorem Fw_f₁ (w : Cw) : Fw f₁ w := rfl

theorem Fw_f₂ (w : Cw) : ¬ Fw f₂ w := by
  show ¬ f₂ (fun y => y = w) w
  unfold f₂; rw [if_neg (not_sup_singleton w)]; exact id


/-- Leibniz's law at `σ → σ` fails at every world of the closed flip structure. -/
theorem leib_fails (w : Cw) : ¬ eval SF Leib () w := by
  intro h
  have := h f₁ adm_f₁ f₂ adm_f₂ Fw adm_Fw eq_f₁f₂
  have e : Fw f₁ = Fw f₂ := this
  exact Fw_f₂ w (e ▸ Fw_f₁ w)

/-- **`Resp` cannot be dropped**: the extended calculus is unsound over the closed structure `SF`
(all entities admitted): it derives `Leib` from the empty theory, and `Leib` fails there. -/
theorem resp_needed :
    Closed SF ∧ (∀ x, SF.A .e x) ∧ DC (fun _ => False) [.w] [] (Lf nilR Leib var0) ∧
      ∀ w, ¬ eval SF Leib () w :=
  ⟨closed_SF, allE_SF, leib_derivable, leib_fails⟩

/-- Hence `SF` does not respect `eqT`. -/
theorem not_resp_SF : ¬ Resp SF := fun hR =>
  leib_fails (fun _ => false)
    (valid_of_deriv SF allE_SF closed_SF hR (T := fun _ => False) (fun _ h => h.elim) leib_derivable _)

end Programme.«20261022-1724-ontological».Run3.HOLX.Flip





namespace Programme.«20261022-1724-ontological».Run3.K1
open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.HOLX

/-! ## Variant 2 in `𝓛` (run 2's `TwoClosed`), polymorphic in the context -/

abbrev v0 : Tm (t :: Γ) t := .var .zero
abbrev v1 : Tm (u :: t :: Γ) t := .var (.succ .zero)
abbrev v2 : Tm (u :: u' :: t :: Γ) t := .var (.succ (.succ .zero))
abbrev v3 : Tm (u :: u' :: u'' :: t :: Γ) t := .var (.succ (.succ (.succ .zero)))
abbrev v4 : Tm (u :: u' :: u'' :: u''' :: t :: Γ) t := .var (.succ (.succ (.succ (.succ .zero))))
abbrev v5 : Tm (u :: u' :: u'' :: u''' :: u'''' :: t :: Γ) t :=
  .var (.succ (.succ (.succ (.succ (.succ .zero)))))

abbrev Pos (φ : Tm Γ tp) : Tm Γ .s := .app .pos φ
abbrev iff (x y : Tm Γ .s) : Tm Γ .s := .and (.imp x y) (.imp y x)
def God : Tm Γ tp := .lam (.all tp (.imp (Pos v0) (.app v0 v1)))
def topP : Tm Γ tp := .lam .top
def negP (φ : Tm Γ tp) : Tm Γ tp := .lam (.neg (.app (wkL φ) v0))

def Ax2a : Tm Γ .s :=
  .all tp (.and (.or (Pos v0) (Pos (negP v0))) (.neg (.and (Pos v0) (Pos (negP v0)))))
def PInc (φ ψ : Tm Γ tp) : Tm Γ .s := .box (.allE (.imp (.app (wkL φ) v0) (.app (wkL ψ) v0)))
def Ax4 : Tm Γ .s := .all tp (.all tp (.imp (Pos v1) (.imp (PInc v1 v0) (Pos v0))))
/-- Variant 2's essence: `Ess φ x := φ x ∧ ∀ψ. ψ x → □∀ᴱy. φ y → ψ y`. -/
def EsT (φ : Tm Γ tp) (x : Tm Γ .e) : Tm Γ .s :=
  .and (.app φ x) (.all tp (.imp (.app v0 (wkL x)) (PInc (wkL φ) v0)))
/-- Necessary existence: `E := λx. ∀φ. Ess φ x → □∃ᴱy. φ y`. -/
def ET : Tm Γ tp := .lam (.all tp (.imp (EsT v0 v1) (.box (.exE (.app v1 v0)))))
def TwoMembers (Φ : Tm Γ th) : Tm Γ .s :=
  .ex tp (.ex tp (.and (.app (wkL (wkL Φ)) v1) (.and (.app (wkL (wkL Φ)) v0) (.neg (.eq tp v1 v0)))))
def PosProps (Φ : Tm Γ th) : Tm Γ .s := .all tp (.imp (.app (wkL Φ) v0) (Pos v0))
def ConjOf (φ : Tm Γ tp) (Φ : Tm Γ th) : Tm Γ .s :=
  .box (.allE (iff (.app (wkL φ) v0) (.all tp (.imp (.app (wkL (wkL Φ)) v0) (.app v0 v1)))))
def Ax1GenTwo : Tm Γ .s :=
  .all th (.all tp (.imp (TwoMembers v1) (.imp (PosProps v1) (.imp (ConjOf v0 v1) (Pos v0)))))
def NonEmpty : Tm Γ .s := .ex .e .top
def Ax2b : Tm Γ .s := .all tp (.imp (Pos v0) (.box (Pos v0)))
/-- Modal collapse: `∀p. p → □p`. -/
def MC : Tm Γ .s := .all .s (.imp v0 (.box v0))
/-- Unrestricted `Ax1Gen`. -/
def Ax1Gen : Tm Γ .s := .all th (.all tp (.imp (PosProps v1) (.imp (ConjOf v0 v1) (Pos v0))))
def ExG : Tm Γ .s := .exE (.app God v0)

/-- The theory: variant 2's `Ax2a`, `Ax2b`, `Ax3`, `Ax4`, `Ax1GenTwo`, and a nonempty domain of
entities (run 2's `[Nonempty D]`). -/
inductive T2 : Tm [] .s → Prop
  | ax2a : T2 Ax2a
  | ax3 : T2 (Pos ET)
  | ax4 : T2 Ax4
  | two : T2 Ax1GenTwo
  | ne : T2 NonEmpty
  | ax2b : T2 Ax2b

/-! ## Structural helpers -/

section helpers
variable {T : Tm [] .s → Prop} {Γ : List HTy} {hs : List (HTerm Γ .o)}

theorem h0 {φ : HTerm Γ .o} {l : List (HTerm Γ .o)} : DC T Γ (φ :: l) φ :=
  .hyp (List.mem_cons_self ..)
theorem h1 {φ a : HTerm Γ .o} {l : List (HTerm Γ .o)} : DC T Γ (a :: φ :: l) φ :=
  .hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..))
theorem h2 {φ a b : HTerm Γ .o} {l : List (HTerm Γ .o)} : DC T Γ (a :: b :: φ :: l) φ :=
  .hyp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
theorem h3 {φ a b c : HTerm Γ .o} {l : List (HTerm Γ .o)} : DC T Γ (a :: b :: c :: φ :: l) φ :=
  .hyp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))

theorem h4 {φ a b c d : HTerm Γ .o} {l : List (HTerm Γ .o)} : DC T Γ (a :: b :: c :: d :: φ :: l) φ :=
  .hyp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_self ..)))))

/-- Cut: prove a lemma, then use it as a hypothesis. -/
theorem h5 {φ a b c d e : HTerm Γ .o} {l : List (HTerm Γ .o)} :
    DC T Γ (a :: b :: c :: d :: e :: φ :: l) φ :=
  (h4 (l := l)).wk1 _

theorem h6 {φ a b c d e f : HTerm Γ .o} {l : List (HTerm Γ .o)} :
    DC T Γ (a :: b :: c :: d :: e :: f :: φ :: l) φ :=
  (h5 (l := l)).wk1 _

theorem h7 {φ a b c d e f g : HTerm Γ .o} {l : List (HTerm Γ .o)} :
    DC T Γ (a :: b :: c :: d :: e :: f :: g :: φ :: l) φ :=
  (h6 (l := l)).wk1 _

theorem cut {φ χ : HTerm Γ .o} (d : DC T Γ hs φ) (k : DC T Γ (φ :: hs) χ) : DC T Γ hs χ :=
  .impE (.impI k) d

theorem sub_tail {x : HTerm Γ .o} {l : List (HTerm Γ .o)} : ∀ h, h ∈ l → h ∈ x :: l :=
  fun _ m => List.mem_cons_of_mem _ m

theorem byCases (φ : HTerm Γ .o) {χ : HTerm Γ .o} (d1 : DC T Γ (φ :: hs) χ)
    (d2 : DC T Γ (.imp φ .bot :: hs) χ) : DC T Γ hs χ :=
  .byContra (.impE h0 (.impE (.impI (d2.weaken (cons_sub sub_tail _)))
    (.impI (.impE h1 (d1.weaken (cons_sub sub_tail _))))))

/-- Modus ponens against a hypothesis negation. -/
theorem absurd' {φ χ : HTerm Γ .o} (d : DC T Γ hs φ) (n : DC T Γ hs (.imp φ .bot)) : DC T Γ hs χ :=
  Deriv.exFalso (.impE n d)

end helpers

/-! ## `𝓛`-level substitution facts -/

theorem substL_renameL : ∀ {Γ Δ Θ t} (tm : Tm Γ t) (q : RenL Γ Δ) (s : SubL Δ Θ) (s' : SubL Γ Θ),
    (∀ {u} (v : Var Γ u), s (q v) = s' v) → substL s (renameL q tm) = substL s' tm := by
  intro Γ Δ Θ t tm
  induction tm generalizing Δ Θ with
  | var i => intro q s s' h; simp only [renameL, substL, h]
  | app F x ihF ihx => intro q s s' h; simp only [renameL, substL, ihF q s s' h, ihx q s s' h]
  | lam b ih =>
      intro q s s' h; simp only [renameL, substL]
      rw [ih (liftRL q) (liftSL s) (liftSL s') (fun v => by cases v <;> simp [liftRL, liftSL, h])]
  | top => intros; rfl
  | bot => intros; rfl
  | neg x ih => intro q s s' h; simp only [renameL, substL, ih q s s' h]
  | and x y ihx ihy => intro q s s' h; simp only [renameL, substL, ihx q s s' h, ihy q s s' h]
  | or x y ihx ihy => intro q s s' h; simp only [renameL, substL, ihx q s s' h, ihy q s s' h]
  | imp x y ihx ihy => intro q s s' h; simp only [renameL, substL, ihx q s s' h, ihy q s s' h]
  | box x ih => intro q s s' h; simp only [renameL, substL, ih q s s' h]
  | all a b ih =>
      intro q s s' h; simp only [renameL, substL]
      rw [ih (liftRL q) (liftSL s) (liftSL s') (fun v => by cases v <;> simp [liftRL, liftSL, h])]
  | ex a b ih =>
      intro q s s' h; simp only [renameL, substL]
      rw [ih (liftRL q) (liftSL s) (liftSL s') (fun v => by cases v <;> simp [liftRL, liftSL, h])]
  | allE b ih =>
      intro q s s' h; simp only [renameL, substL]
      rw [ih (liftRL q) (liftSL s) (liftSL s') (fun v => by cases v <;> simp [liftRL, liftSL, h])]
  | exE b ih =>
      intro q s s' h; simp only [renameL, substL]
      rw [ih (liftRL q) (liftSL s) (liftSL s') (fun v => by cases v <;> simp [liftRL, liftSL, h])]
  | eq a x y ihx ihy => intro q s s' h; simp only [renameL, substL, ihx q s s' h, ihy q s s' h]
  | pos => intros; rfl

@[simp] theorem sub0L_wkL (t : Tm Γ a) (x : Tm Γ b) : substL (sub0L x) (wkL t) = t := by
  rw [wkL, substL_renameL _ _ (sub0L x) (fun v => .var v) (fun _ => rfl), substL_id _ _ (fun _ => rfl)]

@[simp] theorem liftSL_sub0L_wkL2 (t : Tm Γ a) (x : Tm Γ b) :
    substL (liftSL (a := c) (sub0L x)) (wkL (wkL t)) = wkL t := by
  have h1 := substL_renameL (renameL (fun v => .succ v) t) (fun v => .succ v) (liftSL (a := c) (sub0L x))
    (fun v => wkL (sub0L x v)) (fun _ => rfl)
  have h2 := substL_renameL t (fun v => .succ v) (fun v => wkL (sub0L x v))
    (fun v => (.var (.succ v) : Tm (c :: Γ) _)) (fun _ => rfl)
  have h3 := substL_renameL t (fun v => .succ v) (fun v => (.var v : Tm (c :: Γ) _))
    (fun v => .var (.succ v)) (fun _ => rfl)
  rw [substL_id _ _ (fun _ => rfl)] at h3
  unfold wkL
  rw [h1, h2, ← h3]

section deriv
variable {Γ' : List FTy} {Γ : List HTy} {hs : List (HTerm Γ .o)} {r : LRen Γ' Γ} {i : HTerm Γ .w}

def nilRL : RenL [] Γ' := fun v => by cases v

theorem ax_at {T : Tm [] .s → Prop} {φ0 : Tm [] .s} (h : T φ0) (φ : Tm Γ' .s)
    (e : renameL nilRL φ0 = φ) : DC T Γ hs (Lf r φ i) := by
  subst e
  have := L_ax (hs := hs) h (fun v => r (nilRL v)) i
  unfold Lf at this ⊢
  rwa [emb_renameL φ0 nilRL r (fun v => r (nilRL v)) (fun _ => rfl)]

theorem mem_wkL {φ : Tm Γ' .s} {l : List (HTerm Γ .o)} (m : Lf r φ i ∈ l) :
    Lf (liftL (a := a) r) (wkL φ) (wk i) ∈ l.map wk := by
  have := List.mem_map_of_mem (f := wk (b := .L a)) m
  rw [wk_Lf] at this
  unfold Lf at this ⊢; rw [emb_wkL]; exact this

theorem mem_wkL_neg {φ : Tm Γ' .s} {l : List (HTerm Γ .o)} (m : .imp (Lf r φ i) .bot ∈ l) :
    .imp (Lf (liftL (a := a) r) (wkL φ) (wk i)) .bot ∈ l.map wk := by
  have := List.mem_map_of_mem (f := wk (b := .L a)) m
  rw [show wk (HTerm.imp (Lf r φ i) .bot) = .imp (wk (Lf r φ i)) .bot from rfl, wk_Lf] at this
  unfold Lf at this ⊢; rw [emb_wkL]; exact this

theorem ax1GenTwo_at : DC T2 Γ hs (Lf r (.imp (TwoMembers .pos) (.imp (PosProps .pos)
    (.imp (ConjOf God .pos) (Pos God)))) i) := by
  have ax := ax_at (r := r) (i := i) (hs := hs) T2.two Ax1GenTwo rfl
  have a1 := L_allE (ax : DC T2 Γ hs (Lf r (.all th _) i)) .pos
  exact L_allE (a1 : DC T2 Γ hs (Lf r (.all tp _) i)) God

theorem posProps_pos : DC T2 Γ hs (Lf r (PosProps .pos) i) :=
  L_allI (L_impI (Deriv.impI h0))

theorem conjOf_god : DC T2 Γ hs (Lf r (ConjOf God .pos) i) :=
  L_boxI (L_allEI (L_andI (Deriv.andI (L_impI (Deriv.impI (L_betaE h0)))
    (L_impI (Deriv.impI (L_betaI h0))))))

/-- Positive `⊤`, from `Ax3` and `Ax4` (run 2's `pTop_v2`). -/
theorem ptop_at : DC T2 Γ hs (Lf r (Pos topP) i) :=
  .impE (L_impE (.impE (L_impE (L_allE (b := .imp (Pos (wkL ET)) (.imp (PInc (wkL ET) v0) (Pos v0)))
    (L_allE (b := .all tp (.imp (Pos v1) (.imp (PInc v1 v0) (Pos v0))))
      (ax_at (r := r) (i := i) T2.ax4 Ax4 rfl) ET) topP))
    (ax_at (r := r) (i := i) T2.ax3 (Pos ET) rfl)))
    (L_boxI (L_allEI (L_impI (.impI (L_betaI L_topI)))))

/-- With fewer than two positive properties, a positive property is `⊤`. -/
theorem onlyTop (φ : Tm Γ' tp) (ntm : .imp (Lf r (TwoMembers .pos) i) .bot ∈ hs)
    (pφ : DC T2 Γ hs (Lf r (Pos φ) i)) : DC T2 Γ hs (.eq (.L tp) (emb r φ) (emb r topP)) := by
  refine .byContra (absurd' ?_ (Deriv.hyp (List.mem_cons_of_mem _ ntm)))
  refine L_exI φ ?_
  refine L_exI topP ?_
  simp only [instL, substL, sub0L, liftSL, sub0L_wkL]
  exact L_andI (.andI (pφ.wk1 _) (L_andI (.andI ptop_at
    (L_negI (.impI (.impE h1 (L_eqE h0)))))))

/-- With fewer than two positive properties, every entity is God-like. -/
theorem godlike (x : Tm Γ' .e) (ntm : .imp (Lf r (TwoMembers .pos) i) .bot ∈ hs) :
    DC T2 Γ hs (Lf r (.app God x) i) := by
  refine L_betaI (L_allI (L_impI (.impI ?_)))
  have e := onlyTop (r := liftL r) (i := wk i) (hs := Lf (liftL r) (Pos v0) (wk i) :: hs.map wk) v0
    (List.mem_cons_of_mem _ (mem_wkL_neg (a := tp) ntm)) h0
  have := L_rw (i := wk i) (x := topP) (y := v0) rfl (Tm.app v0 (wkL (wkL x))) (.symm _ e)
    (L_betaI L_topI)
  simp only [instL, substL, sub0L, sub0L_wkL] at this
  exact this

theorem L_two : DC T2 Γ hs (Lf r (Pos God) i) := by
  refine byCases (Lf r (TwoMembers .pos) i) ?_ ?_
  · exact .impE (L_impE (.impE (L_impE (.impE (L_impE ax1GenTwo_at) h0)) posProps_pos)) conjOf_god
  · have a := L_allE (ax_at (r := r) (i := i) (hs := .imp (Lf r (TwoMembers .pos) i) .bot :: hs)
      T2.ax2a Ax2a rfl : DC T2 Γ _ (Lf r (.all tp _) i)) God
    refine .orE (L_orE (.andL (L_andE a))) h0 ?_
    -- `P (¬G)`: then `¬G = ⊤`, against a God-like entity
    have m_pn : Lf r (Pos (negP God)) i ∈ (Lf r (Pos (negP God)) i ::
        HTerm.imp (Lf r (TwoMembers .pos) i) .bot :: hs) := List.mem_cons_self ..
    have m_nt : HTerm.imp (Lf r (TwoMembers .pos) i) .bot ∈ (Lf r (Pos (negP God)) i ::
        HTerm.imp (Lf r (TwoMembers .pos) i) .bot :: hs) := List.mem_cons_of_mem _ (List.mem_cons_self ..)
    refine L_exE (ax_at (r := r) (i := i) T2.ne NonEmpty rfl) (.exFalso ?_)
    have e := onlyTop (r := liftL r) (i := wk i) (negP God)
      (hs := Lf (liftL r) .top (wk i) :: (Lf r (Pos (negP God)) i ::
        HTerm.imp (Lf r (TwoMembers .pos) i) .bot :: hs).map wk)
      (List.mem_cons_of_mem _ (mem_wkL_neg (a := .e) m_nt))
      (Deriv.hyp (List.mem_cons_of_mem _ (mem_wkL (a := .e) m_pn)))
    have g := godlike (r := liftL r) (i := wk i) v0
      (hs := Lf (liftL r) .top (wk i) :: (Lf r (Pos (negP God)) i ::
        HTerm.imp (Lf r (TwoMembers .pos) i) .bot :: hs).map wk)
      (List.mem_cons_of_mem _ (mem_wkL_neg (a := .e) m_nt))
    have := L_rw (i := wk i) (x := topP) (y := negP God) rfl (Tm.app v0 v1) (.symm _ e) (L_betaI L_topI)
    exact .impE (L_negE (L_betaE this)) g

def Dia {Δ : List FTy} (φ : Tm Δ .s) : Tm Δ .s := .neg (.box (.neg φ))

theorem mem_wkW {φ : Tm Γ' .s} {l : List (HTerm Γ .o)} (m : Lf r φ i ∈ l) :
    Lf (shL r) φ (wk (b := .w) i) ∈ l.map wk := by
  have := List.mem_map_of_mem (f := wk (b := .w)) m
  rwa [wk_Lf] at this

/-- `Th4_Two`: `◇∃ᴱ G`. -/
theorem th4_of {T : Tm [] .s → Prop} (h2a : T Ax2a) (h4 : T Ax4)
    (pgD : ∀ {Γ' : List FTy} {Γ : List HTy} {hs : List (HTerm Γ .o)} {r : LRen Γ' Γ}
      {i : HTerm Γ .w}, DC T Γ hs (Lf r (Pos God) i)) : DC T Γ hs (Lf r (Dia ExG) i) := by
  refine L_negI (.impI ?_)
  have a := L_allE (L_allE (ax_at (r := r) (i := i) (hs := Lf r (.box (.neg ExG)) i :: hs)
    h4 Ax4 rfl : DC T Γ _ (Lf r (.all tp _) i)) God : DC T Γ _ (Lf r (.all tp _) i)) (negP God)
  have pg : DC T Γ (Lf r (.box (.neg ExG)) i :: hs) (Lf r (Pos God) i) := pgD
  have inc : DC T Γ (Lf r (.box (.neg ExG)) i :: hs) (Lf r (PInc God (negP God)) i) := by
    refine L_boxI (L_allEI (L_impI (.impI ?_)))
    refine L_betaI (L_negI (.impI ?_))
    have m1 : Lf (shL r) (.box (.neg ExG)) (wk i) ∈
        (Lf r (.box (.neg ExG)) i :: hs).map (wk (b := .w)) := mem_wkW (List.mem_cons_self ..)
    have mb := mem_wkL (a := .e) (List.mem_cons_of_mem (HTerm.rel (wk i) var0) m1)
    have mr : wk (b := .L .e) (HTerm.rel (wk i) var0) ∈
        (HTerm.rel (wk i) var0 :: (Lf r (.box (.neg ExG)) i :: hs).map (wk (b := .w))).map wk :=
      List.mem_map_of_mem (List.mem_cons_self ..)
    exact .impE (L_negE (L_boxE (j := wk var0)
      (.hyp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ mb))))
      (.hyp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ mr))))))
      (L_exEI v0 h2 h0)
  have pn := L_impE (.impE (L_impE a) pg)
  have b := L_allE (ax_at (r := r) (i := i) (hs := Lf r (.box (.neg ExG)) i :: hs)
    h2a Ax2a rfl : DC T Γ _ (Lf r (.all tp _) i)) God
  exact .impE (L_negE (.andR (L_andE b))) (L_andI (.andI pg (.impE pn inc)))

theorem th4 : DC T2 Γ hs (Lf r (Dia ExG) i) := th4_of T2.ax2a T2.ax4 L_two

end deriv

theorem lift1 {T : Tm [] .s → Prop} {Γ hs φ} (d : DC T Γ hs φ) (b : HTy) (x : HTerm (b :: Γ) .o) :
    DC T (b :: Γ) (x :: hs.map wk) (wk φ) := (d.wkD b).wk1 x

/-! ## `G_ex_Two_at` -/

abbrev botP : Tm Δ tp := .lam .bot
/-- `χ := λx. ¬∃ᴱG ∧ ψ x`, with `ψ` the variable `v0`. -/
abbrev chiT : Tm (tp :: Δ) tp := .lam (.and (.neg ExG) (.app v1 v0))
/-- `Φ := λψ'. (¬∃ᴱG ∧ (ψ' = ⊤ ∨ ψ' = ψ)) ∨ (∃ᴱG ∧ ψ' = ⊥)`. -/
abbrev PhiT : Tm (tp :: Δ) th :=
  .lam (.or (.and (.neg ExG) (.or (.eq tp v0 topP) (.eq tp v0 v1))) (.and ExG (.eq tp v0 botP)))

section gex
variable {Γ' : List FTy} {Γ : List HTy} {hs : List (HTerm Γ .o)} {r : LRen (tp :: Γ') Γ}
  {i : HTerm Γ .w}

theorem gex_at (hp : DC T2 Γ hs (Lf r (Pos v0) i))
    (hn : DC T2 Γ hs (.imp (.eq (.L tp) (emb r v0) (emb r topP)) .bot)) :
    DC T2 Γ hs (Lf r ExG i) := by
  refine .byContra ?_
  have hp1 := hp.wk1 (.imp (Lf r ExG i) .bot)
  have hn1 := hn.wk1 (.imp (Lf r ExG i) .bot)
  have nE : DC T2 Γ (.imp (Lf r ExG i) .bot :: hs) (Lf r (.neg ExG) i) := L_negI h0
  have ax := L_allE (L_allE (ax_at (r := r) (i := i) T2.two Ax1GenTwo rfl :
    DC T2 Γ (.imp (Lf r ExG i) .bot :: hs) (Lf r (.all th _) i)) PhiT :
      DC T2 Γ _ (Lf r (.all tp _) i)) chiT
  have two : DC T2 Γ (.imp (Lf r ExG i) .bot :: hs) (Lf r (TwoMembers PhiT) i) := by
    refine L_exI topP (L_exI v0 ?_)
    refine L_andI (.andI (L_betaI ?_) (L_andI (.andI (L_betaI ?_) (L_negI (.impI ?_)))))
    · exact L_orI (.orL (L_andI (.andI nE (L_orI (.orL (L_eqI (.refl _ _)))))))
    · exact L_orI (.orL (L_andI (.andI nE (L_orI (.orR (L_eqI (.refl _ _)))))))
    · exact .impE (hn1.wk1 _) (.symm _ (L_eqE h0))
  have pos : DC T2 Γ (.imp (Lf r ExG i) .bot :: hs) (Lf r (PosProps PhiT) i) := by
    refine L_allI (L_impI (.impI ?_))
    refine .orE (L_orE (L_betaE h0)) ?_ ?_
    · refine .orE (L_orE (.andR (L_andE h0))) ?_ ?_
      · exact L_rw (M := Pos v0) (x := topP) (y := v0) rfl (.symm _ (L_eqE h0)) ptop_at
      · exact L_rw (M := Pos v0) (x := v1) (y := v0) rfl (.symm _ (L_eqE h0))
          (((lift1 hp1 (.L tp) _).wk1 _).wk1 _)
    · exact .exFalso (.impE (L_negE (((lift1 nE (.L tp) _).wk1 _))) (.andL (L_andE h0)))
  have cj : DC T2 Γ (.imp (Lf r ExG i) .bot :: hs) (Lf r (ConjOf chiT PhiT) i) := by
    refine L_boxI (L_allEI ?_)
    refine byCases (Lf (liftL (shL r)) ExG (wk var0)) ?_ ?_
    · refine L_andI (.andI (L_impI (.impI ?_)) (L_impI (.impI ?_)))
      · exact .exFalso (.impE (L_negE (.andL (L_andE (L_betaE h0)))) h1)
      · refine L_botE (r := liftL (shL r)) (i := wk var0) (L_betaE (x := v0) (b := .bot) ?_)
        refine .impE (φ := Lf (liftL (shL r)) (.app (wkL (PhiT (Δ := Γ'))) botP) (wk var0)) ?_ ?_
        · exact L_impE (L_allE (b := .imp (.app (wkL (wkL (PhiT (Δ := Γ')))) v0) (.app v0 v1)) h0 botP)
        · exact L_betaI (L_orI (.orR (L_andI (.andI h1 (L_eqI (.refl _ _))))))
    · refine L_andI (.andI (L_impI (.impI ?_)) (L_impI (.impI ?_)))
      · refine L_allI (L_impI (.impI ?_))
        refine .orE (L_orE (L_betaE h0)) ?_ ?_
        · refine .orE (L_orE (.andR (L_andE h0))) ?_ ?_
          · exact L_rw (M := (.app v0 v2 : Tm (tp :: tp :: .e :: tp :: Γ') .s)) (x := topP) (y := v0)
              rfl (.symm _ (L_eqE h0)) (L_betaI L_topI)
          · exact L_rw (M := (.app v0 v2 : Tm (tp :: tp :: .e :: tp :: Γ') .s)) (x := v2) (y := v0)
              rfl (.symm _ (L_eqE h0)) (.andR (L_andE (r := liftL (liftL (shL r))) (i := wk (wk var0))
                (L_betaE (b := .and (.neg ExG) (.app v3 v0)) (x := v1) h3)))
        · exact .exFalso (.impE h3 (.andL (L_andE (r := liftL (liftL (shL r))) (i := wk (wk var0))
            (x := ExG) (y := .eq tp v0 botP) h0)))
      · refine L_betaI (L_andI (.andI (L_negI h1) ?_))
        refine .impE (φ := Lf (liftL (shL r)) (.app (wkL (PhiT (Δ := Γ'))) v1) (wk var0)) ?_ ?_
        · exact L_impE (L_allE (b := .imp (.app (wkL (wkL (PhiT (Δ := Γ')))) v0) (.app v0 v1)) h0 v1)
        refine L_betaI (L_orI (.orL (L_andI (.andI (L_negI h1) ?_))))
        exact L_orI (.orR (L_eqI (.refl _ _)))
  have pchi : DC T2 Γ (.imp (Lf r ExG i) .bot :: hs) (Lf r (Pos chiT) i) := .impE (L_impE (.impE (L_impE (.impE (L_impE ax) two)) pos)) cj
  have inc : DC T2 Γ (.imp (Lf r ExG i) .bot :: hs) (Lf r (PInc chiT (negP God)) i) := by
    refine L_boxI (L_allEI (L_impI (.impI ?_)))
    refine L_betaI (L_negI (.impI ?_))
    exact .impE (L_negE (.andL (L_andE (L_betaE h1)))) (L_exEI v0 h2 h0)
  have a4 := L_allE (L_allE (ax_at (r := r) (i := i) T2.ax4 Ax4 rfl :
    DC T2 Γ (.imp (Lf r ExG i) .bot :: hs) (Lf r (.all tp _) i)) chiT :
      DC T2 Γ _ (Lf r (.all tp _) i)) (negP God)
  have pn : DC T2 Γ (.imp (Lf r ExG i) .bot :: hs) (Lf r (Pos (negP God)) i) :=
    .impE (L_impE (.impE (L_impE a4) pchi)) inc
  have b := L_allE (ax_at (r := r) (i := i) (hs := .imp (Lf r ExG i) .bot :: hs)
    T2.ax2a Ax2a rfl : DC T2 Γ _ (Lf r (.all tp _) i)) God
  exact .impE (L_negE (.andR (L_andE b))) (L_andI (.andI L_two pn))

end gex

/-! ## `G_ex_Two_unconditional` and modal collapse -/

/-- `∃ψ. Pψ ∧ ψ ≠ ⊤`. -/
abbrev Q2 : Tm Δ .s := .ex tp (.and (Pos v0) (.neg (.eq tp v0 topP)))
/-- `κ := λx. ∃ᴱG`. -/
abbrev kap : Tm Δ tp := .lam ExG

section gex2
variable {Γ' : List FTy} {Γ : List HTy} {hs : List (HTerm Γ .o)} {r : LRen Γ' Γ} {i : HTerm Γ .w}

theorem onlyTop2 (nq : DC T2 Γ hs (.imp (Lf r Q2 i) .bot)) (φ : Tm Γ' tp)
    (pφ : DC T2 Γ hs (Lf r (Pos φ) i)) : DC T2 Γ hs (.eq (.L tp) (emb r φ) (emb r topP)) :=
  .byContra (.impE (nq.wk1 _) (L_exI φ (L_andI (.andI (pφ.wk1 _) (L_negI (.impI (.impE h1 (L_eqE h0))))))))

theorem gex : DC T2 Γ hs (Lf r ExG i) := by
  refine byCases (Lf r Q2 i) ?_ ?_
  · refine L_exE h0 ?_
    refine gex_at (r := liftL r) (i := wk i) (.andL (L_andE h0)) (.impI ?_)
    exact .impE ((L_negE (.andR (L_andE h0))).wk1 _) (L_eqI h0)
  · refine L_exE (ax_at (r := r) (i := i) T2.ne NonEmpty rfl) ?_
    have ax := L_allE (ax_at (r := liftL r) (i := wk i)
      (hs := Lf (liftL r) .top (wk i) :: (HTerm.imp (Lf r Q2 i) .bot :: hs).map wk)
      T2.ax2a (Ax2a : Tm (.e :: Γ') .s) rfl : DC T2 _ _ (Lf (liftL r) (.all tp _) (wk i))) kap
    have nq : DC T2 _ (Lf (liftL r) .top (wk i) :: (HTerm.imp (Lf r Q2 i) .bot :: hs).map wk)
      (.imp (Lf (liftL r) Q2 (wk i)) .bot) := (lift1 h0 (.L .e) _)
    refine .orE (L_orE (.andL (L_andE ax))) ?_ ?_
    · have e := onlyTop2 (nq.wk1 _) kap h0
      exact L_betaE (L_rw (M := .app v0 v1) (x := topP) (y := kap) rfl (.symm _ e) (L_betaI L_topI))
    · have e := onlyTop2 (nq.wk1 _) (negP kap) h0
      refine .exFalso (.impE (L_negE (th4 (r := liftL r) (i := wk i))) (L_boxI (L_negI (.impI ?_))))
      have e' := (lift1 e .w (.rel (wk (wk i)) var0)).wk1 (Lf (shL (liftL r)) ExG var0)
      have k := L_betaE (L_rw (r := shL (liftL r)) (i := var0) (M := .app v0 v1) (x := topP) (y := negP kap)
        rfl (.symm _ e') (L_betaI L_topI))
      exact .impE (L_negE k) (L_betaI (b := ExG) (x := v0) h0)

/-- Modal collapse from `∃ᴱG` everywhere, `Ax2a` and `Ax2b` (run 2's `mc_of_gex`), on any frame. -/
theorem mc_of {T : Tm [] .s → Prop} (h2a : T Ax2a) (h2b : T Ax2b)
    (gexD : ∀ {Γ' : List FTy} {Γ : List HTy} {hs : List (HTerm Γ .o)} {r : LRen Γ' Γ}
      {i : HTerm Γ .w}, DC T Γ hs (Lf r ExG i)) : DC T Γ hs (Lf r MC i) := by
  refine L_allI (L_impI (.impI ?_))
  have ax := L_allE (ax_at (r := liftL r) (i := wk i) (hs := Lf (liftL r) v0 (wk i) :: hs.map wk)
    h2a (Ax2a : Tm (.s :: Γ') .s) rfl : DC T _ _ (Lf (liftL r) (.all tp _) (wk i)))
    (.lam v1 : Tm (.s :: Γ') tp)
  have pk : DC T _ (Lf (liftL r) v0 (wk i) :: hs.map wk) (Lf (liftL r) (Pos (.lam v1)) (wk i)) := by
    refine .orE (L_orE (.andL (L_andE ax))) h0 ?_
    refine L_exEE (gexD (r := liftL r) (i := wk i)) ?_
    refine .exFalso (.impE (L_negE (L_betaE (b := .neg (.app (wkL (.lam v2)) v0)) (x := v0) ?_))
      (L_betaI (r := liftL (liftL r)) (i := wk (wk i)) (b := v2) (x := v0) h2))
    refine .impE (L_impE (L_allE (b := .imp (Pos v0) (.app v0 v1)) (L_betaE (.andR h0)) _)) h1
  refine L_boxI ?_
  have b2 := L_allE (ax_at (r := shL (liftL r)) (i := wk (wk i))
    (hs := .rel (wk (wk i)) var0 :: (Lf (liftL r) v0 (wk i) :: hs.map wk).map wk)
    h2b (Ax2b : Tm (.s :: Γ') .s) rfl : DC T _ _ (Lf (shL (liftL r)) (.all tp _) (wk (wk i))))
    (.lam v1 : Tm (.s :: Γ') tp)
  have pj := L_boxE (.impE (L_impE b2) (lift1 pk .w _)) (j := var0) h0
  refine L_exEE (gexD (r := shL (liftL r)) (i := var0)) ?_
  exact L_betaE (r := liftL (shL (liftL r))) (i := wk var0) (b := v2) (x := v0)
    (.impE (φ := Lf (liftL (shL (liftL r))) (Pos (.lam v2)) (wk var0))
      (L_impE (L_allE (b := .imp (Pos v0) (.app v0 v1)) (L_betaE (.andR h0)) _)) (lift1 pj (.L .e) _))

/-- Modal collapse, on any frame. -/
theorem mc : DC T2 Γ hs (Lf r MC i) := mc_of T2.ax2a T2.ax2b gex

/-- `∀ψ'. Φ ψ' → ψ' = ψ₀`, in the context `ψ₀ :: φ :: Φ`. -/
abbrev AM : Tm (tp :: tp :: th :: Δ) .s := .all tp (.imp (.app v3 v0) (.eq tp v0 v1))

/-- **`Ax1GenTwo` gives `Ax1Gen`** as a certified deep derivation (run 2's `ax1Gen_of_two`). -/
theorem ax1Gen_of_two : DC T2 Γ hs (Lf r Ax1Gen i) := by
  refine L_allI (L_allI (L_impI (.impI (L_impI (.impI ?_)))))
  refine byCases (Lf (liftL (liftL r)) (TwoMembers v1) (wk (wk i))) ?_ ?_
  · refine .impE (L_impE (.impE (L_impE (.impE (L_impE ?_) h0)) h2)) h1
    exact L_allE (b := .imp (TwoMembers v2) (.imp (PosProps v2) (.imp (ConjOf v0 v2) (Pos v0))))
      (L_allE (b := .all tp (.imp (TwoMembers v1) (.imp (PosProps v1) (.imp (ConjOf v0 v1) (Pos v0)))))
        (ax_at (r := liftL (liftL r)) (i := wk (wk i)) T2.two Ax1GenTwo rfl) v1) v0
  · refine L_exE (r := liftL (liftL r)) (i := wk (wk i)) (b := .and (Pos v0) (AM (Δ := Γ'))) ?_ ?_
    · refine byCases (Lf (liftL (liftL r)) (.ex tp (.app v2 v0)) (wk (wk i))) ?_ ?_
      · refine L_exE h0 ?_
        show DC T2 _ _ (Lf (liftL (liftL (liftL r))) (.ex tp (.and (Pos v0)
          (.all tp (.imp (.app v4 v0) (.eq tp v0 v1))))) (wk (wk (wk i))))
        refine L_exI v0 ?_
        show DC T2 _ _ (Lf (liftL (liftL (liftL r))) (.and (Pos v0)
          (.all tp (.imp (.app v3 v0) (.eq tp v0 v1)))) (wk (wk (wk i))))
        refine L_andI (.andI ?_ ?_)
        · exact .impE (L_impE (L_allE (r := liftL (liftL (liftL r))) (i := wk (wk (wk i)))
            (b := .imp (.app v3 v0) (Pos v0)) h4 v0)) h0
        · refine L_allI (L_impI (.impI ?_))
          refine .byContra (.impE h4 ?_)
          show DC T2 _ _ (Lf (liftL (liftL (liftL (liftL r)))) (TwoMembers v3) (wk (wk (wk (wk i)))))
          refine L_exI v0 (L_exI v1 ?_)
          exact L_andI (.andI h1 (L_andI (.andI h2 (L_negI h0))))
      · refine L_exI topP ?_
        show DC T2 _ _ (Lf (liftL (liftL r)) (.and (Pos topP)
          (.all tp (.imp (.app v2 v0) (.eq tp v0 topP)))) (wk (wk i)))
        refine L_andI (.andI ptop_at ?_)
        refine L_allI (L_impI (.impI ?_))
        exact .exFalso (.impE (φ := Lf (liftL (liftL (liftL r))) (.ex tp (.app v3 v0)) (wk (wk (wk i))))
          h1 (L_exI v0 h0))
    · show DC T2 _ _ (Lf (liftL (liftL (liftL r))) (Pos v1) (wk (wk (wk i))))
      refine .impE (φ := Lf (liftL (liftL (liftL r))) (PInc v0 v1) (wk (wk (wk i)))) ?_ ?_
      · refine L_impE (.impE (φ := Lf (liftL (liftL (liftL r))) (Pos v0) (wk (wk (wk i)))) (L_impE ?_) ?_)
        · exact L_allE (b := .imp (Pos v1) (.imp (PInc v1 v0) (Pos v0)))
            (L_allE (b := .all tp (.imp (Pos v1) (.imp (PInc v1 v0) (Pos v0))))
              (ax_at (r := liftL (liftL (liftL r))) (i := wk (wk (wk i))) T2.ax4 Ax4 rfl) v0) v1
        · exact .andL (L_andE (r := liftL (liftL (liftL r))) (i := wk (wk (wk i)))
            (x := Pos v0) (y := AM) h0)
      · refine L_boxI ?_
        refine cut (φ := Lf (shL (liftL (liftL (liftL r)))) AM var0) ?_ ?_
        · refine L_boxE (j := var0) ?_ h0
          exact .impE (L_impE (L_allE (r := shL (liftL (liftL (liftL r)))) (i := wk (wk (wk (wk i))))
            (b := .imp v0 (.box v0)) mc AM))
            (.andR (L_andE (r := shL (liftL (liftL (liftL r)))) (i := wk (wk (wk (wk i))))
              (x := Pos v0) (y := AM) h1))
        refine cut (φ := Lf (shL (liftL (liftL (liftL r))))
          (.allE (iff (.app v2 v0) (.all tp (.imp (.app v4 v0) (.app v0 v1))))) var0) ?_ ?_
        · exact L_boxE (j := var0) h4 h1
        refine L_allEI (L_impI (.impI ?_))
        refine cut (φ := Lf (liftL (shL (liftL (liftL (liftL r))))) (.allE (iff (.app v3 v0)
          (.all tp (.imp (.app v5 v0) (.app v0 v1))))) (wk var0)) h2 ?_
        refine cut (φ := Lf (liftL (shL (liftL (liftL (liftL r)))))
          (.all tp (.imp (.app v4 v0) (.eq tp v0 v2))) (wk var0)) h4 ?_
        refine .impE (L_impE (.andR (L_andE (L_allEE h1 v0 h3)))) ?_
        refine L_allI (L_impI (.impI ?_))
        refine cut (φ := Lf (liftL (liftL (shL (liftL (liftL (liftL r)))))) (.eq tp v0 v2) (wk (wk var0)))
          ?_ ?_
        · exact .impE (L_impE (L_allE (r := liftL (liftL (shL (liftL (liftL (liftL r))))))
            (i := wk (wk var0)) (b := .imp (.app v5 v0) (.eq tp v0 v3)) h1 v0)) h0
        · exact L_rw (M := .app v0 v2) (x := v2) (y := v0) rfl (.symm _ (L_eqE h0)) h4

end gex2

end Programme.«20261022-1724-ontological».Run3.K1



namespace Programme.«20261022-1724-ontological».Run3.K14
open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.HOLX Programme.«20261022-1724-ontological».Run3.K1

/-! ## Variant 3′ in `𝓛` (run 2's `GexL`) -/

/-- Variant 3′'s essence: `Ess3 φ x := ∀ψ. ψ x → □(φ ≠ ⊥ ∧ ∀ᴱy. φ y → ψ y)`. -/
def Ess3 (φ : Tm Γ tp) (x : Tm Γ .e) : Tm Γ .s :=
  .all tp (.imp (.app v0 (wkL x)) (.box (.and (.neg (.eq tp (wkL φ) botP))
    (.allE (.imp (.app (wkL (wkL φ)) v0) (.app v1 v0))))))

/-- Necessary existence: `E₃ := λx. ∀φ. Ess3 φ x → □∃ᴱy. φ y`. -/
def E3T : Tm Γ tp := .lam (.all tp (.imp (Ess3 v0 v1) (.box (.exE (.app v1 v0)))))

/-- The theory: `Ax2a`, `Ax2b`, plain `Ax4`, variant 3′'s `Ax3` (`P E₃`) and `L` (`P G`). -/
inductive T3 : Tm [] .s → Prop
  | ax2a : T3 Ax2a
  | ax2b : T3 Ax2b
  | ax4 : T3 Ax4
  | ax3 : T3 (Pos E3T)
  | lax : T3 (Pos God)

section
variable {Γ' : List FTy} {Γ : List HTy} {hs : List (HTerm Γ .o)} {i : HTerm Γ .w}

/-- `PosOfGod`, with `ψ = v0` and `x = v1`. -/
theorem posOfGod {r : LRen (tp :: .e :: Γ') Γ} (hG : DC T3 Γ hs (Lf r (.app God v1) i))
    (hψ : DC T3 Γ hs (Lf r (.app v0 v1) i)) : DC T3 Γ hs (Lf r (Pos v0) i) := by
  refine .byContra ?_
  have ax := L_allE (b := .and (.or (Pos v0) (Pos (negP v0))) (.neg (.and (Pos v0) (Pos (negP v0)))))
    (ax_at (r := r) (i := i) (hs := .imp (Lf r (Pos v0) i) .bot :: hs) T3.ax2a Ax2a rfl) v0
  refine .orE (L_orE (.andL (L_andE ax))) (.impE h1 h0) ?_
  refine .impE (L_negE (L_betaE (b := .neg (.app (wkL v0) v0)) (x := v1) ?_)) ((hψ.wk1 _).wk1 _)
  exact .impE (L_impE (L_allE (b := .imp (Pos v0) (.app v0 v2)) (L_betaE ((hG.wk1 _).wk1 _)) _)) h0

/-- `Th1`: God-likeness is an essence of every God-like being. -/
theorem th1 {r : LRen (.e :: Γ') Γ} (hG : DC T3 Γ hs (Lf r (.app God v0) i)) :
    DC T3 Γ hs (Lf r (Ess3 God v0) i) := by
  refine cut hG ?_
  refine L_allI (L_impI (.impI ?_))
  refine cut (φ := Lf (liftL r) (Pos v0) (wk i)) (posOfGod h1 h0) ?_
  refine cut (φ := Lf (liftL r) (.box (Pos v0)) (wk i))
    (.impE (L_impE (L_allE (b := .imp (Pos v0) (.box (Pos v0)))
      (ax_at (r := liftL r) (i := wk i) T3.ax2b Ax2b rfl) v0)) h0) ?_
  refine L_boxI (L_andI (.andI ?_ ?_))
  · refine L_negI (.impI ?_)
    exact L_botE (r := shL (liftL r)) (i := wk (wk i)) (L_betaE (b := .bot) (x := v1)
      (L_rw (r := shL (liftL r)) (i := wk (wk i)) (M := .app v0 v2) (x := God) (y := botP) rfl
        (L_eqE h0) h5))
  · refine cut (φ := Lf (shL (liftL r)) (Pos v0) var0) (L_boxE (j := var0) h1 h0) ?_
    refine L_allEI (L_impI (.impI ?_))
    exact .impE (L_impE (L_allE (r := liftL (shL (liftL r))) (i := wk var0)
      (b := .imp (Pos v0) (.app v0 v1))
      (L_betaE (b := .all tp (.imp (Pos v0) (.app v0 v1))) (x := v0) h0) v1)) h2

/-- `Th2`: a God-like being makes an actual God-like being exist at every successor. -/
theorem th2 {r : LRen (.e :: Γ') Γ} (hG : DC T3 Γ hs (Lf r (.app God v0) i)) :
    DC T3 Γ hs (Lf r (.box ExG) i) := by
  have e3 := L_betaE (x := v0) (b := .all tp (.imp (Ess3 v0 v1) (.box (.exE (.app v1 v0)))))
    (.impE (L_impE (L_allE (b := .imp (Pos v0) (.app v0 v1))
      (L_betaE (b := .all tp (.imp (Pos v0) (.app v0 v1))) (x := v0) hG) E3T))
      (ax_at (r := r) (i := i) T3.ax3 (Pos E3T) rfl))
  exact .impE (L_impE (L_allE (b := .imp (Ess3 v0 v1) (.box (.exE (.app v1 v0)))) e3 God)) (th1 hG)

/-- Every world has a successor: `◇⊤`, from `Ax2a`, `Ax3`, plain `Ax4`. -/
theorem serial {r : LRen Γ' Γ} : DC T3 Γ hs (Lf r (Dia .top) i) := by
  refine L_negI (.impI ?_)
  have allPos : ∀ ψ : Tm Γ' tp, DC T3 Γ (Lf r (.box (.neg .top)) i :: hs) (Lf r (Pos ψ) i) := by
    intro ψ
    refine .impE (L_impE (.impE (L_impE (L_allE (b := .imp (Pos (wkL E3T)) (.imp (PInc (wkL E3T) v0) (Pos v0)))
      (L_allE (b := .all tp (.imp (Pos v1) (.imp (PInc v1 v0) (Pos v0))))
        (ax_at (r := r) (i := i) T3.ax4 Ax4 rfl) E3T) ψ))
      (ax_at (r := r) (i := i) T3.ax3 (Pos E3T) rfl))) ?_
    refine L_boxI (L_allEI (L_impI (.impI ?_)))
    exact .exFalso (.impE (L_negE (L_boxE (r := liftL (shL r)) (x := .neg .top) (i := wk (wk i))
      (j := wk var0) h3 h2)) L_topI)
  have ax := L_allE (b := .and (.or (Pos v0) (Pos (negP v0))) (.neg (.and (Pos v0) (Pos (negP v0)))))
    (ax_at (r := r) (i := i) (hs := Lf r (.box (.neg .top)) i :: hs) T3.ax2a Ax2a rfl) topP
  exact .impE (L_negE (.andR (L_andE ax))) (L_andI (.andI (allPos topP) (allPos (negP topP))))

/-- `Th4` from `L`. -/
theorem th4L {r : LRen Γ' Γ} : DC T3 Γ hs (Lf r (Dia ExG) i) :=
  th4_of T3.ax2a T3.ax4 (ax_at T3.lax (Pos God) rfl)

/-- `λx. ¬∃ᴱG`. -/
abbrev kn : Tm Δ tp := .lam (.neg ExG)

/-- **K14 (`gex_L`) as a certified deep derivation**: `L`, `Ax2a`, `Ax2b`, `Ax3`, plain `Ax4`
give an actual God-like being at every world. -/
theorem gex3 {r : LRen Γ' Γ} : DC T3 Γ hs (Lf r ExG i) := by
  refine .byContra ?_
  refine .impE (L_negE (th4L (r := r) (i := i))) ?_
  refine L_boxI (L_negI (.impI ?_))
  refine L_exEE (r := shL r) (i := var0) (b := .app God v0) h0 ?_
  -- context: `y`, the world `v`; `r₂ := liftL (shL r)`, `V := wk var0`, `I := wk (wk i)`
  refine cut (φ := Lf (liftL (shL r)) (.app God v0) (wk var0)) (.andR h0) ?_
  refine cut (φ := Lf (liftL (shL r)) (.box ExG) (wk var0)) (th2 h0) ?_
  refine cut (φ := Lf (liftL (shL r)) (.all tp (.imp (Ess3 v0 v1) (.box (.exE (.app v1 v0)))))
    (wk var0)) (L_betaE (x := v0) (b := .all tp (.imp (Ess3 v0 v1) (.box (.exE (.app v1 v0)))))
      (.impE (L_impE (L_allE (b := .imp (Pos v0) (.app v0 v1))
        (L_betaE (b := .all tp (.imp (Pos v0) (.app v0 v1))) (x := v0) h1) E3T))
        (ax_at (r := liftL (shL r)) (i := wk var0) T3.ax3 (Pos E3T) rfl))) ?_
  refine cut (φ := Lf (liftL (shL r)) (.app kn v0) (wk (wk i)))
    (L_betaI (b := .neg ExG) (x := v0) (L_negI h6)) ?_
  -- `λx. ¬∃ᴱG` is an essence of `y` at `v`
  refine cut (φ := Lf (liftL (shL r)) (Ess3 kn v0) (wk var0)) ?_ ?_
  · refine L_allI (L_impI (.impI ?_))
    refine L_boxI (L_andI (.andI ?_ ?_))
    · refine L_negI (.impI ?_)
      exact L_botE (r := shL (liftL (liftL (shL r)))) (i := wk (wk (wk (wk i))))
        (L_betaE (b := .bot) (x := v1)
          (L_rw (r := shL (liftL (liftL (shL r)))) (i := wk (wk (wk (wk i)))) (M := .app v0 v2)
            (x := kn) (y := botP) rfl (L_eqE h0) h3))
    · refine L_allEI (L_impI (.impI ?_))
      exact .exFalso (.impE (L_negE (L_betaE (r := liftL (shL (liftL (liftL (shL r)))))
        (i := wk var0) (b := .neg ExG) (x := v0) h0))
        (L_boxE (r := liftL (shL (liftL (liftL (shL r))))) (x := ExG) (i := wk (wk (wk (wk var0))))
          (j := wk var0) h6 h2))
  refine cut (φ := Lf (liftL (shL r)) (.box (.exE (.app kn v0))) (wk var0))
    (.impE (L_impE (L_allE (b := .imp (Ess3 v0 v1) (.box (.exE (.app v1 v0)))) h2 kn)) h0) ?_
  -- seriality at `v` exemplifies `λx. ¬∃ᴱG` at a successor, against `Th2`
  refine .impE (L_negE (serial (r := liftL (shL r)) (i := wk var0))) ?_
  refine L_boxI (L_negI (.impI ?_))
  refine cut (φ := Lf (shL (liftL (shL r))) ExG var0) (L_boxE (j := var0) h6 h1) ?_
  refine L_exEE (r := shL (liftL (shL r))) (i := var0) (b := .app kn v0) (L_boxE (j := var0) h3 h2) ?_
  exact .impE (L_negE (L_betaE (r := liftL (shL (liftL (shL r)))) (i := wk var0) (b := .neg ExG)
    (x := v0) (.andR h0))) h1

/-- Modal collapse from K14's theory. -/
theorem mc3 {r : LRen Γ' Γ} : DC T3 Γ hs (Lf r MC i) := mc_of T3.ax2a T3.ax2b gex3

end

end Programme.«20261022-1724-ontological».Run3.K14


/-! # Variant 3′ (`OpenQuestions.Ax1GenTwoVariant3Plain`) in `𝓛`

The module differs from variant 2 only in the essence: `Ess φ x := ∀ψ. ψ x → □(φ ≠ ⊥ ∧ ∀ᴱy. φ y → ψ y)`
(non-emptiness clause, no conjunct `φ x`), hence in what `Ax3 : P E` says.  The derivations of
`K1` use `Ax3` only through `P ⊤` (with `Ax4`), so they are replayed verbatim for the theory `T3p`. -/

namespace Programme.«20261022-1724-ontological».Run3.K3p
open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.HOLX Programme.«20261022-1724-ontological».Run3.K1

/-- Variant 3′'s essence: `Ess φ x := ∀ψ. ψ x → □(φ ≠ λ_.⊥ ∧ ∀ᴱy. φ y → ψ y)`. -/
def EsT3 (φ : Tm Γ tp) (x : Tm Γ .e) : Tm Γ .s :=
  .all tp (.imp (.app v0 (wkL x))
    (.box (.and (.neg (.eq tp (wkL φ) botP)) (.allE (.imp (.app (wkL (wkL φ)) v0) (.app v1 v0))))))
/-- Necessary existence with variant 3′'s essence: `E := λx. ∀φ. Ess φ x → □∃ᴱy. φ y`. -/
def ET3 : Tm Γ tp := .lam (.all tp (.imp (EsT3 v0 v1) (.box (.exE (.app v1 v0)))))

/-- Variant 3′: `Ax2a`, `Ax2b`, `Ax3 = P E` (variant 3′'s `E`), plain `Ax4`, `Ax1GenTwo`, `∃x.⊤`. -/
inductive T3p : Tm [] .s → Prop
  | ax2a : T3p Ax2a
  | ax3 : T3p (Pos ET3)
  | ax4 : T3p Ax4
  | two : T3p Ax1GenTwo
  | ne : T3p NonEmpty
  | ax2b : T3p Ax2b


section deriv
variable {Γ' : List FTy} {Γ : List HTy} {hs : List (HTerm Γ .o)} {r : LRen Γ' Γ} {i : HTerm Γ .w}

theorem ax1GenTwo_at : DC T3p Γ hs (Lf r (.imp (TwoMembers .pos) (.imp (PosProps .pos)
    (.imp (ConjOf God .pos) (Pos God)))) i) := by
  have ax := ax_at (r := r) (i := i) (hs := hs) T3p.two Ax1GenTwo rfl
  have a1 := L_allE (ax : DC T3p Γ hs (Lf r (.all th _) i)) .pos
  exact L_allE (a1 : DC T3p Γ hs (Lf r (.all tp _) i)) God

theorem posProps_pos : DC T3p Γ hs (Lf r (PosProps .pos) i) :=
  L_allI (L_impI (Deriv.impI h0))

theorem conjOf_god : DC T3p Γ hs (Lf r (ConjOf God .pos) i) :=
  L_boxI (L_allEI (L_andI (Deriv.andI (L_impI (Deriv.impI (L_betaE h0)))
    (L_impI (Deriv.impI (L_betaI h0))))))

/-- Positive `⊤`, from `Ax3` and `Ax4` (run 2's `pTop_v2`). -/
theorem ptop_at : DC T3p Γ hs (Lf r (Pos topP) i) :=
  .impE (L_impE (.impE (L_impE (L_allE (b := .imp (Pos (wkL ET3)) (.imp (PInc (wkL ET3) v0) (Pos v0)))
    (L_allE (b := .all tp (.imp (Pos v1) (.imp (PInc v1 v0) (Pos v0))))
      (ax_at (r := r) (i := i) T3p.ax4 Ax4 rfl) ET3) topP))
    (ax_at (r := r) (i := i) T3p.ax3 (Pos ET3) rfl)))
    (L_boxI (L_allEI (L_impI (.impI (L_betaI L_topI)))))

/-- With fewer than two positive properties, a positive property is `⊤`. -/
theorem onlyTop (φ : Tm Γ' tp) (ntm : .imp (Lf r (TwoMembers .pos) i) .bot ∈ hs)
    (pφ : DC T3p Γ hs (Lf r (Pos φ) i)) : DC T3p Γ hs (.eq (.L tp) (emb r φ) (emb r topP)) := by
  refine .byContra (absurd' ?_ (Deriv.hyp (List.mem_cons_of_mem _ ntm)))
  refine L_exI φ ?_
  refine L_exI topP ?_
  simp only [instL, substL, sub0L, liftSL, sub0L_wkL]
  exact L_andI (.andI (pφ.wk1 _) (L_andI (.andI ptop_at
    (L_negI (.impI (.impE h1 (L_eqE h0)))))))

/-- With fewer than two positive properties, every entity is God-like. -/
theorem godlike (x : Tm Γ' .e) (ntm : .imp (Lf r (TwoMembers .pos) i) .bot ∈ hs) :
    DC T3p Γ hs (Lf r (.app God x) i) := by
  refine L_betaI (L_allI (L_impI (.impI ?_)))
  have e := onlyTop (r := liftL r) (i := wk i) (hs := Lf (liftL r) (Pos v0) (wk i) :: hs.map wk) v0
    (List.mem_cons_of_mem _ (mem_wkL_neg (a := tp) ntm)) h0
  have := L_rw (i := wk i) (x := topP) (y := v0) rfl (Tm.app v0 (wkL (wkL x))) (.symm _ e)
    (L_betaI L_topI)
  simp only [instL, substL, sub0L, sub0L_wkL] at this
  exact this

theorem L_two : DC T3p Γ hs (Lf r (Pos God) i) := by
  refine byCases (Lf r (TwoMembers .pos) i) ?_ ?_
  · exact .impE (L_impE (.impE (L_impE (.impE (L_impE ax1GenTwo_at) h0)) posProps_pos)) conjOf_god
  · have a := L_allE (ax_at (r := r) (i := i) (hs := .imp (Lf r (TwoMembers .pos) i) .bot :: hs)
      T3p.ax2a Ax2a rfl : DC T3p Γ _ (Lf r (.all tp _) i)) God
    refine .orE (L_orE (.andL (L_andE a))) h0 ?_
    -- `P (¬G)`: then `¬G = ⊤`, against a God-like entity
    have m_pn : Lf r (Pos (negP God)) i ∈ (Lf r (Pos (negP God)) i ::
        HTerm.imp (Lf r (TwoMembers .pos) i) .bot :: hs) := List.mem_cons_self ..
    have m_nt : HTerm.imp (Lf r (TwoMembers .pos) i) .bot ∈ (Lf r (Pos (negP God)) i ::
        HTerm.imp (Lf r (TwoMembers .pos) i) .bot :: hs) := List.mem_cons_of_mem _ (List.mem_cons_self ..)
    refine L_exE (ax_at (r := r) (i := i) T3p.ne NonEmpty rfl) (.exFalso ?_)
    have e := onlyTop (r := liftL r) (i := wk i) (negP God)
      (hs := Lf (liftL r) .top (wk i) :: (Lf r (Pos (negP God)) i ::
        HTerm.imp (Lf r (TwoMembers .pos) i) .bot :: hs).map wk)
      (List.mem_cons_of_mem _ (mem_wkL_neg (a := .e) m_nt))
      (Deriv.hyp (List.mem_cons_of_mem _ (mem_wkL (a := .e) m_pn)))
    have g := godlike (r := liftL r) (i := wk i) v0
      (hs := Lf (liftL r) .top (wk i) :: (Lf r (Pos (negP God)) i ::
        HTerm.imp (Lf r (TwoMembers .pos) i) .bot :: hs).map wk)
      (List.mem_cons_of_mem _ (mem_wkL_neg (a := .e) m_nt))
    have := L_rw (i := wk i) (x := topP) (y := negP God) rfl (Tm.app v0 v1) (.symm _ e) (L_betaI L_topI)
    exact .impE (L_negE (L_betaE this)) g


theorem th4 : DC T3p Γ hs (Lf r (Dia ExG) i) := th4_of T3p.ax2a T3p.ax4 L_two

end deriv

/-! ## `G_ex_Two_at` -/


section gex
variable {Γ' : List FTy} {Γ : List HTy} {hs : List (HTerm Γ .o)} {r : LRen (tp :: Γ') Γ}
  {i : HTerm Γ .w}

theorem gex_at (hp : DC T3p Γ hs (Lf r (Pos v0) i))
    (hn : DC T3p Γ hs (.imp (.eq (.L tp) (emb r v0) (emb r topP)) .bot)) :
    DC T3p Γ hs (Lf r ExG i) := by
  refine .byContra ?_
  have hp1 := hp.wk1 (.imp (Lf r ExG i) .bot)
  have hn1 := hn.wk1 (.imp (Lf r ExG i) .bot)
  have nE : DC T3p Γ (.imp (Lf r ExG i) .bot :: hs) (Lf r (.neg ExG) i) := L_negI h0
  have ax := L_allE (L_allE (ax_at (r := r) (i := i) T3p.two Ax1GenTwo rfl :
    DC T3p Γ (.imp (Lf r ExG i) .bot :: hs) (Lf r (.all th _) i)) PhiT :
      DC T3p Γ _ (Lf r (.all tp _) i)) chiT
  have two : DC T3p Γ (.imp (Lf r ExG i) .bot :: hs) (Lf r (TwoMembers PhiT) i) := by
    refine L_exI topP (L_exI v0 ?_)
    refine L_andI (.andI (L_betaI ?_) (L_andI (.andI (L_betaI ?_) (L_negI (.impI ?_)))))
    · exact L_orI (.orL (L_andI (.andI nE (L_orI (.orL (L_eqI (.refl _ _)))))))
    · exact L_orI (.orL (L_andI (.andI nE (L_orI (.orR (L_eqI (.refl _ _)))))))
    · exact .impE (hn1.wk1 _) (.symm _ (L_eqE h0))
  have pos : DC T3p Γ (.imp (Lf r ExG i) .bot :: hs) (Lf r (PosProps PhiT) i) := by
    refine L_allI (L_impI (.impI ?_))
    refine .orE (L_orE (L_betaE h0)) ?_ ?_
    · refine .orE (L_orE (.andR (L_andE h0))) ?_ ?_
      · exact L_rw (M := Pos v0) (x := topP) (y := v0) rfl (.symm _ (L_eqE h0)) ptop_at
      · exact L_rw (M := Pos v0) (x := v1) (y := v0) rfl (.symm _ (L_eqE h0))
          (((lift1 hp1 (.L tp) _).wk1 _).wk1 _)
    · exact .exFalso (.impE (L_negE (((lift1 nE (.L tp) _).wk1 _))) (.andL (L_andE h0)))
  have cj : DC T3p Γ (.imp (Lf r ExG i) .bot :: hs) (Lf r (ConjOf chiT PhiT) i) := by
    refine L_boxI (L_allEI ?_)
    refine byCases (Lf (liftL (shL r)) ExG (wk var0)) ?_ ?_
    · refine L_andI (.andI (L_impI (.impI ?_)) (L_impI (.impI ?_)))
      · exact .exFalso (.impE (L_negE (.andL (L_andE (L_betaE h0)))) h1)
      · refine L_botE (r := liftL (shL r)) (i := wk var0) (L_betaE (x := v0) (b := .bot) ?_)
        refine .impE (φ := Lf (liftL (shL r)) (.app (wkL (PhiT (Δ := Γ'))) botP) (wk var0)) ?_ ?_
        · exact L_impE (L_allE (b := .imp (.app (wkL (wkL (PhiT (Δ := Γ')))) v0) (.app v0 v1)) h0 botP)
        · exact L_betaI (L_orI (.orR (L_andI (.andI h1 (L_eqI (.refl _ _))))))
    · refine L_andI (.andI (L_impI (.impI ?_)) (L_impI (.impI ?_)))
      · refine L_allI (L_impI (.impI ?_))
        refine .orE (L_orE (L_betaE h0)) ?_ ?_
        · refine .orE (L_orE (.andR (L_andE h0))) ?_ ?_
          · exact L_rw (M := (.app v0 v2 : Tm (tp :: tp :: .e :: tp :: Γ') .s)) (x := topP) (y := v0)
              rfl (.symm _ (L_eqE h0)) (L_betaI L_topI)
          · exact L_rw (M := (.app v0 v2 : Tm (tp :: tp :: .e :: tp :: Γ') .s)) (x := v2) (y := v0)
              rfl (.symm _ (L_eqE h0)) (.andR (L_andE (r := liftL (liftL (shL r))) (i := wk (wk var0))
                (L_betaE (b := .and (.neg ExG) (.app v3 v0)) (x := v1) h3)))
        · exact .exFalso (.impE h3 (.andL (L_andE (r := liftL (liftL (shL r))) (i := wk (wk var0))
            (x := ExG) (y := .eq tp v0 botP) h0)))
      · refine L_betaI (L_andI (.andI (L_negI h1) ?_))
        refine .impE (φ := Lf (liftL (shL r)) (.app (wkL (PhiT (Δ := Γ'))) v1) (wk var0)) ?_ ?_
        · exact L_impE (L_allE (b := .imp (.app (wkL (wkL (PhiT (Δ := Γ')))) v0) (.app v0 v1)) h0 v1)
        refine L_betaI (L_orI (.orL (L_andI (.andI (L_negI h1) ?_))))
        exact L_orI (.orR (L_eqI (.refl _ _)))
  have pchi : DC T3p Γ (.imp (Lf r ExG i) .bot :: hs) (Lf r (Pos chiT) i) := .impE (L_impE (.impE (L_impE (.impE (L_impE ax) two)) pos)) cj
  have inc : DC T3p Γ (.imp (Lf r ExG i) .bot :: hs) (Lf r (PInc chiT (negP God)) i) := by
    refine L_boxI (L_allEI (L_impI (.impI ?_)))
    refine L_betaI (L_negI (.impI ?_))
    exact .impE (L_negE (.andL (L_andE (L_betaE h1)))) (L_exEI v0 h2 h0)
  have a4 := L_allE (L_allE (ax_at (r := r) (i := i) T3p.ax4 Ax4 rfl :
    DC T3p Γ (.imp (Lf r ExG i) .bot :: hs) (Lf r (.all tp _) i)) chiT :
      DC T3p Γ _ (Lf r (.all tp _) i)) (negP God)
  have pn : DC T3p Γ (.imp (Lf r ExG i) .bot :: hs) (Lf r (Pos (negP God)) i) :=
    .impE (L_impE (.impE (L_impE a4) pchi)) inc
  have b := L_allE (ax_at (r := r) (i := i) (hs := .imp (Lf r ExG i) .bot :: hs)
    T3p.ax2a Ax2a rfl : DC T3p Γ _ (Lf r (.all tp _) i)) God
  exact .impE (L_negE (.andR (L_andE b))) (L_andI (.andI L_two pn))

end gex

/-! ## `G_ex_Two_unconditional` and modal collapse -/


section gex2
variable {Γ' : List FTy} {Γ : List HTy} {hs : List (HTerm Γ .o)} {r : LRen Γ' Γ} {i : HTerm Γ .w}

theorem onlyTop2 (nq : DC T3p Γ hs (.imp (Lf r Q2 i) .bot)) (φ : Tm Γ' tp)
    (pφ : DC T3p Γ hs (Lf r (Pos φ) i)) : DC T3p Γ hs (.eq (.L tp) (emb r φ) (emb r topP)) :=
  .byContra (.impE (nq.wk1 _) (L_exI φ (L_andI (.andI (pφ.wk1 _) (L_negI (.impI (.impE h1 (L_eqE h0))))))))

theorem gex : DC T3p Γ hs (Lf r ExG i) := by
  refine byCases (Lf r Q2 i) ?_ ?_
  · refine L_exE h0 ?_
    refine gex_at (r := liftL r) (i := wk i) (.andL (L_andE h0)) (.impI ?_)
    exact .impE ((L_negE (.andR (L_andE h0))).wk1 _) (L_eqI h0)
  · refine L_exE (ax_at (r := r) (i := i) T3p.ne NonEmpty rfl) ?_
    have ax := L_allE (ax_at (r := liftL r) (i := wk i)
      (hs := Lf (liftL r) .top (wk i) :: (HTerm.imp (Lf r Q2 i) .bot :: hs).map wk)
      T3p.ax2a (Ax2a : Tm (.e :: Γ') .s) rfl : DC T3p _ _ (Lf (liftL r) (.all tp _) (wk i))) kap
    have nq : DC T3p _ (Lf (liftL r) .top (wk i) :: (HTerm.imp (Lf r Q2 i) .bot :: hs).map wk)
      (.imp (Lf (liftL r) Q2 (wk i)) .bot) := (lift1 h0 (.L .e) _)
    refine .orE (L_orE (.andL (L_andE ax))) ?_ ?_
    · have e := onlyTop2 (nq.wk1 _) kap h0
      exact L_betaE (L_rw (M := .app v0 v1) (x := topP) (y := kap) rfl (.symm _ e) (L_betaI L_topI))
    · have e := onlyTop2 (nq.wk1 _) (negP kap) h0
      refine .exFalso (.impE (L_negE (th4 (r := liftL r) (i := wk i))) (L_boxI (L_negI (.impI ?_))))
      have e' := (lift1 e .w (.rel (wk (wk i)) var0)).wk1 (Lf (shL (liftL r)) ExG var0)
      have k := L_betaE (L_rw (r := shL (liftL r)) (i := var0) (M := .app v0 v1) (x := topP) (y := negP kap)
        rfl (.symm _ e') (L_betaI L_topI))
      exact .impE (L_negE k) (L_betaI (b := ExG) (x := v0) h0)

/-- Modal collapse, on any frame. -/
theorem mc : DC T3p Γ hs (Lf r MC i) := mc_of T3p.ax2a T3p.ax2b gex

/-- `∀ψ'. Φ ψ' → ψ' = ψ₀`, in the context `ψ₀ :: φ :: Φ`. -/
abbrev AM : Tm (tp :: tp :: th :: Δ) .s := .all tp (.imp (.app v3 v0) (.eq tp v0 v1))

/-- **`Ax1GenTwo` gives `Ax1Gen`** as a certified deep derivation (run 2's `ax1Gen_of_two`). -/
theorem ax1Gen_of_two : DC T3p Γ hs (Lf r Ax1Gen i) := by
  refine L_allI (L_allI (L_impI (.impI (L_impI (.impI ?_)))))
  refine byCases (Lf (liftL (liftL r)) (TwoMembers v1) (wk (wk i))) ?_ ?_
  · refine .impE (L_impE (.impE (L_impE (.impE (L_impE ?_) h0)) h2)) h1
    exact L_allE (b := .imp (TwoMembers v2) (.imp (PosProps v2) (.imp (ConjOf v0 v2) (Pos v0))))
      (L_allE (b := .all tp (.imp (TwoMembers v1) (.imp (PosProps v1) (.imp (ConjOf v0 v1) (Pos v0)))))
        (ax_at (r := liftL (liftL r)) (i := wk (wk i)) T3p.two Ax1GenTwo rfl) v1) v0
  · refine L_exE (r := liftL (liftL r)) (i := wk (wk i)) (b := .and (Pos v0) (AM (Δ := Γ'))) ?_ ?_
    · refine byCases (Lf (liftL (liftL r)) (.ex tp (.app v2 v0)) (wk (wk i))) ?_ ?_
      · refine L_exE h0 ?_
        show DC T3p _ _ (Lf (liftL (liftL (liftL r))) (.ex tp (.and (Pos v0)
          (.all tp (.imp (.app v4 v0) (.eq tp v0 v1))))) (wk (wk (wk i))))
        refine L_exI v0 ?_
        show DC T3p _ _ (Lf (liftL (liftL (liftL r))) (.and (Pos v0)
          (.all tp (.imp (.app v3 v0) (.eq tp v0 v1)))) (wk (wk (wk i))))
        refine L_andI (.andI ?_ ?_)
        · exact .impE (L_impE (L_allE (r := liftL (liftL (liftL r))) (i := wk (wk (wk i)))
            (b := .imp (.app v3 v0) (Pos v0)) h4 v0)) h0
        · refine L_allI (L_impI (.impI ?_))
          refine .byContra (.impE h4 ?_)
          show DC T3p _ _ (Lf (liftL (liftL (liftL (liftL r)))) (TwoMembers v3) (wk (wk (wk (wk i)))))
          refine L_exI v0 (L_exI v1 ?_)
          exact L_andI (.andI h1 (L_andI (.andI h2 (L_negI h0))))
      · refine L_exI topP ?_
        show DC T3p _ _ (Lf (liftL (liftL r)) (.and (Pos topP)
          (.all tp (.imp (.app v2 v0) (.eq tp v0 topP)))) (wk (wk i)))
        refine L_andI (.andI ptop_at ?_)
        refine L_allI (L_impI (.impI ?_))
        exact .exFalso (.impE (φ := Lf (liftL (liftL (liftL r))) (.ex tp (.app v3 v0)) (wk (wk (wk i))))
          h1 (L_exI v0 h0))
    · show DC T3p _ _ (Lf (liftL (liftL (liftL r))) (Pos v1) (wk (wk (wk i))))
      refine .impE (φ := Lf (liftL (liftL (liftL r))) (PInc v0 v1) (wk (wk (wk i)))) ?_ ?_
      · refine L_impE (.impE (φ := Lf (liftL (liftL (liftL r))) (Pos v0) (wk (wk (wk i)))) (L_impE ?_) ?_)
        · exact L_allE (b := .imp (Pos v1) (.imp (PInc v1 v0) (Pos v0)))
            (L_allE (b := .all tp (.imp (Pos v1) (.imp (PInc v1 v0) (Pos v0))))
              (ax_at (r := liftL (liftL (liftL r))) (i := wk (wk (wk i))) T3p.ax4 Ax4 rfl) v0) v1
        · exact .andL (L_andE (r := liftL (liftL (liftL r))) (i := wk (wk (wk i)))
            (x := Pos v0) (y := AM) h0)
      · refine L_boxI ?_
        refine cut (φ := Lf (shL (liftL (liftL (liftL r)))) AM var0) ?_ ?_
        · refine L_boxE (j := var0) ?_ h0
          exact .impE (L_impE (L_allE (r := shL (liftL (liftL (liftL r)))) (i := wk (wk (wk (wk i))))
            (b := .imp v0 (.box v0)) mc AM))
            (.andR (L_andE (r := shL (liftL (liftL (liftL r)))) (i := wk (wk (wk (wk i))))
              (x := Pos v0) (y := AM) h1))
        refine cut (φ := Lf (shL (liftL (liftL (liftL r))))
          (.allE (iff (.app v2 v0) (.all tp (.imp (.app v4 v0) (.app v0 v1))))) var0) ?_ ?_
        · exact L_boxE (j := var0) h4 h1
        refine L_allEI (L_impI (.impI ?_))
        refine cut (φ := Lf (liftL (shL (liftL (liftL (liftL r))))) (.allE (iff (.app v3 v0)
          (.all tp (.imp (.app v5 v0) (.app v0 v1))))) (wk var0)) h2 ?_
        refine cut (φ := Lf (liftL (shL (liftL (liftL (liftL r)))))
          (.all tp (.imp (.app v4 v0) (.eq tp v0 v2))) (wk var0)) h4 ?_
        refine .impE (L_impE (.andR (L_andE (L_allEE h1 v0 h3)))) ?_
        refine L_allI (L_impI (.impI ?_))
        refine cut (φ := Lf (liftL (liftL (shL (liftL (liftL (liftL r)))))) (.eq tp v0 v2) (wk (wk var0)))
          ?_ ?_
        · exact .impE (L_impE (L_allE (r := liftL (liftL (shL (liftL (liftL (liftL r))))))
            (i := wk (wk var0)) (b := .imp (.app v5 v0) (.eq tp v0 v3)) h1 v0)) h0
        · exact L_rw (M := .app v0 v2) (x := v2) (y := v0) rfl (.symm _ (L_eqE h0)) h4

end gex2


end Programme.«20261022-1724-ontological».Run3.K3p


/-! # The converse `Ax1Gen ⇒ Ax1GenTwo` as a deep derivation (the modules' `Two_weaker`) -/

namespace Programme.«20261022-1724-ontological».Run3.Conv
open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.HOLX Programme.«20261022-1724-ontological».Run3.K1

section
variable {Γ' : List FTy} {Γ : List HTy} {hs : List (HTerm Γ .o)} {r : LRen Γ' Γ} {i : HTerm Γ .w}

/-- From unrestricted `Ax1Gen` alone, `Ax1GenTwo`: drop the premiss `TwoMembers`. -/
theorem two_of_gen {T : Tm [] .s → Prop} (h : T Ax1Gen) : DC T Γ hs (Lf r Ax1GenTwo i) := by
  refine L_allI (L_allI (L_impI (.impI (L_impI (.impI (L_impI (.impI ?_)))))))
  refine .impE (L_impE (.impE (L_impE ?_) h1)) h0
  exact L_allE (b := .imp (PosProps v2) (.imp (ConjOf v0 v2) (Pos v0)))
    (L_allE (b := .all tp (.imp (PosProps v1) (.imp (ConjOf v0 v1) (Pos v0))))
      (ax_at (r := liftL (liftL r)) (i := wk (wk i)) h Ax1Gen rfl) v1) v0

end

/-- The one-axiom theory `{Ax1Gen}`. -/
inductive TGen : Tm [] .s → Prop
  | gen : TGen Ax1Gen

end Programme.«20261022-1724-ontological».Run3.Conv




namespace Programme.«20261022-1724-ontological».Run3.LX
open Programme.«20261022-1724-ontological».Run3.HOLX (Resp EnvR envR_refl get_rel fund eqT_refl eqT_symm eqT_trans)

/-! ## v4's 𝓛-general models, literally (def:lgeneral)

Carriers `C t` at every type of 𝓛; `C .s` is a set of propositions (`pr` injective) and
`C (a → b)` a set of functions *from `C a` to `C b`* (`ap` extensional), so `P_{a→b} ⊆ P_a → P_b`
as in v4.  `LGen M`: every term of 𝓛 with parameters from the carriers denotes in the carriers,
by the usual clauses; quantifiers at 𝓛-types range over the carriers, equality is identity. -/

structure VM (W : Type) where
  R : W → W → Prop
  C : FTy → Type
  act : C .e → W → Prop
  pr : C .s → W → Prop
  pr_inj : ∀ p q : C .s, pr p = pr q → p = q
  ap : {a b : FTy} → C (.arr a b) → C a → C b
  ap_ext : ∀ {a b : FTy} (f g : C (.arr a b)), (∀ x, ap f x = ap g x) → f = g
  P : C th

@[reducible] def VEnv (M : VM W) : List FTy → Type
  | [] => Unit
  | t :: Γ => M.C t × VEnv M Γ

def Var.vget (M : VM W) : {Γ : List FTy} → {t : FTy} → Var Γ t → VEnv M Γ → M.C t
  | _, _, .zero, ρ => ρ.1
  | _, _, .succ i, ρ => Var.vget M i ρ.2

structure LGen (M : VM W) where
  ev : {Γ : List FTy} → {t : FTy} → Tm Γ t → VEnv M Γ → M.C t
  var : ∀ {Γ t} (i : Var Γ t) (ρ : VEnv M Γ), ev (.var i) ρ = i.vget M ρ
  app : ∀ {Γ a b} (F : Tm Γ (.arr a b)) (x : Tm Γ a) (ρ : VEnv M Γ),
    ev (.app F x) ρ = M.ap (ev F ρ) (ev x ρ)
  lam : ∀ {Γ a b} (t : Tm (a :: Γ) b) (ρ : VEnv M Γ) (x : M.C a), M.ap (ev (.lam t) ρ) x = ev t (x, ρ)
  top : ∀ {Γ} (ρ : VEnv M Γ) w, M.pr (ev .top ρ) w ↔ True
  bot : ∀ {Γ} (ρ : VEnv M Γ) w, M.pr (ev .bot ρ) w ↔ False
  neg : ∀ {Γ} (x : Tm Γ .s) (ρ : VEnv M Γ) w, M.pr (ev (.neg x) ρ) w ↔ ¬ M.pr (ev x ρ) w
  and : ∀ {Γ} (x y : Tm Γ .s) (ρ : VEnv M Γ) w,
    M.pr (ev (.and x y) ρ) w ↔ (M.pr (ev x ρ) w ∧ M.pr (ev y ρ) w)
  or : ∀ {Γ} (x y : Tm Γ .s) (ρ : VEnv M Γ) w,
    M.pr (ev (.or x y) ρ) w ↔ (M.pr (ev x ρ) w ∨ M.pr (ev y ρ) w)
  imp : ∀ {Γ} (x y : Tm Γ .s) (ρ : VEnv M Γ) w,
    M.pr (ev (.imp x y) ρ) w ↔ (M.pr (ev x ρ) w → M.pr (ev y ρ) w)
  box : ∀ {Γ} (x : Tm Γ .s) (ρ : VEnv M Γ) w, M.pr (ev (.box x) ρ) w ↔ ∀ v, M.R w v → M.pr (ev x ρ) v
  all : ∀ {Γ} (a : FTy) (b : Tm (a :: Γ) .s) (ρ : VEnv M Γ) w,
    M.pr (ev (.all a b) ρ) w ↔ ∀ x : M.C a, M.pr (ev b (x, ρ)) w
  ex : ∀ {Γ} (a : FTy) (b : Tm (a :: Γ) .s) (ρ : VEnv M Γ) w,
    M.pr (ev (.ex a b) ρ) w ↔ ∃ x : M.C a, M.pr (ev b (x, ρ)) w
  allE : ∀ {Γ} (b : Tm (.e :: Γ) .s) (ρ : VEnv M Γ) w,
    M.pr (ev (.allE b) ρ) w ↔ ∀ y : M.C .e, M.act y w → M.pr (ev b (y, ρ)) w
  exE : ∀ {Γ} (b : Tm (.e :: Γ) .s) (ρ : VEnv M Γ) w,
    M.pr (ev (.exE b) ρ) w ↔ ∃ y : M.C .e, M.act y w ∧ M.pr (ev b (y, ρ)) w
  eq : ∀ {Γ} (a : FTy) (x y : Tm Γ a) (ρ : VEnv M Γ) w, M.pr (ev (.eq a x y) ρ) w ↔ ev x ρ = ev y ρ
  pos : ∀ {Γ} (ρ : VEnv M Γ), ev .pos ρ = M.P

/-! ## M1: from a v4 model to a closed `Resp` structure (extension by restriction) -/

section M1
variable (M : VM W)

/-- Logical relation between carrier elements and full-hierarchy objects. -/
def Rel : (t : FTy) → M.C t → Den W (M.C .e) t → Prop
  | .e, x, z => x = z
  | .s, x, q => M.pr x = q
  | .arr a b, f, F => ∀ x z, Rel a x z → Rel b (M.ap f x) (F z)

theorem den_ne {D : Type} (h : Nonempty D) : ∀ t, Nonempty (Den W D t)
  | .e => h
  | .s => ⟨fun _ => True⟩
  | .arr _ b => let ⟨y⟩ := den_ne h b; ⟨fun _ => y⟩

/-- A carrier element extended to the full hierarchy: at an argument related to a carrier
element, its value there; arbitrary elsewhere. -/
noncomputable def up (hne : Nonempty (M.C .e)) : (t : FTy) → M.C t → Den W (M.C .e) t
  | .e, x => x
  | .s, x => M.pr x
  | .arr a b, f => fun z =>
      @dite _ (∃ x, Rel M a x z) (Classical.propDecidable _)
        (fun h => up hne b (M.ap f (Classical.choose h))) (fun _ => Classical.choice (den_ne hne b))

theorem up_rel (hne : Nonempty (M.C .e)) : ∀ t : FTy,
    (∀ x, Rel M t x (up M hne t x)) ∧ (∀ x x' z, Rel M t x z → Rel M t x' z → x = x')
  | .e => ⟨fun _ => rfl, fun _ _ _ h h' => h.trans h'.symm⟩
  | .s => ⟨fun _ => rfl, fun _ _ _ h h' => M.pr_inj _ _ (h.trans h'.symm)⟩
  | .arr a b => by
      have iha := up_rel hne a
      have ihb := up_rel hne b
      refine ⟨fun f x z hxz => ?_, fun f g F hf hg => ?_⟩
      · have h : ∃ x, Rel M a x z := ⟨x, hxz⟩
        show Rel M b (M.ap f x) (@dite _ (∃ x, Rel M a x z) (Classical.propDecidable _) _ _)
        rw [dite_cond_eq_true (eq_true h), iha.2 _ _ _ (Classical.choose_spec h) hxz]
        exact ihb.1 _
      · exact M.ap_ext f g fun x =>
          ihb.2 _ _ _ (hf x _ (iha.1 x)) (hg x _ (iha.1 x))

/-- The structure: carriers = objects related to some carrier element. -/
noncomputable def toStr (hne : Nonempty (M.C .e)) : Str W (M.C .e) where
  R := M.R
  act := M.act
  P := up M hne th M.P
  A := fun t z => ∃ x, Rel M t x z

theorem eqT_rel (hne : Nonempty (M.C .e)) : ∀ (t : FTy) (x x' : M.C t) (z z' : Den W (M.C .e) t),
    Rel M t x z → Rel M t x' z' → (eqT (toStr M hne) t z z' ↔ x = x')
  | .e, _, _, _, _, h, h' => ⟨fun e => h.trans (e.trans h'.symm), fun e => h.symm.trans (e ▸ h')⟩
  | .s, _, _, _, _, h, h' =>
      ⟨fun e => M.pr_inj _ _ (h.trans (e.trans h'.symm)), fun e => h.symm.trans (e ▸ h')⟩
  | .arr a b, f, g, F, G, h, h' => by
      constructor
      · intro hFG
        exact M.ap_ext f g fun y =>
          (eqT_rel hne b _ _ _ _ (h y _ ((up_rel M hne a).1 y)) (h' y _ ((up_rel M hne a).1 y))).1
            (hFG _ (⟨y, (up_rel M hne a).1 y⟩ : ∃ x', Rel M a x' (up M hne a y)))
      · intro e u hu
        obtain ⟨y, hy⟩ : ∃ x, Rel M a x u := hu
        subst e
        exact (eqT_rel hne b _ _ _ _ (h y u hy) (h' y u hy)).2 rfl

def EnvRel : (Γ : List FTy) → VEnv M Γ → Env W (M.C .e) Γ → Prop
  | [], _, _ => True
  | t :: Γ, ρv, ρ => Rel M t ρv.1 ρ.1 ∧ EnvRel Γ ρv.2 ρ.2

theorem rel_get : ∀ {Γ t} (i : Var Γ t) (ρv : VEnv M Γ) (ρ : Env W (M.C .e) Γ), EnvRel M Γ ρv ρ →
    Rel M t (i.vget M ρv) (i.get ρ)
  | _ :: _, _, .zero, _, _, h => h.1
  | _ :: _, _, .succ i, _, _, h => rel_get i _ _ h.2

/-- Fundamental lemma of the bridge: every 𝓛-term's value in `M` is related to its value in
`toStr M`. -/
theorem rel_eval (hne : Nonempty (M.C .e)) (L : LGen M) : ∀ {Γ t} (tm : Tm Γ t) (ρv : VEnv M Γ)
    (ρ : Env W (M.C .e) Γ), EnvRel M Γ ρv ρ → Rel M t (L.ev tm ρv) (eval (toStr M hne) tm ρ)
  | _, _, .var i, ρv, ρ, h => by rw [L.var]; exact rel_get M i ρv ρ h
  | _, _, .app F x, ρv, ρ, h => by
      rw [L.app]; exact rel_eval hne L F ρv ρ h _ _ (rel_eval hne L x ρv ρ h)
  | _, _, .lam b, ρv, ρ, h => fun x z hxz => by
      rw [L.lam]; exact rel_eval hne L b (x, ρv) (z, ρ) ⟨hxz, h⟩
  | _, _, .top, ρv, ρ, _ => funext fun w => propext (L.top ρv w)
  | _, _, .bot, ρv, ρ, _ => funext fun w => propext (L.bot ρv w)
  | _, _, .neg x, ρv, ρ, h => by
      have ih : M.pr (L.ev x ρv) = _ := rel_eval hne L x ρv ρ h
      funext w; show _ = (¬ eval (toStr M hne) x ρ w); rw [← ih]; exact propext (L.neg x ρv w)
  | _, _, .and x y, ρv, ρ, h => by
      have ih : M.pr (L.ev x ρv) = _ := rel_eval hne L x ρv ρ h
      have ih' : M.pr (L.ev y ρv) = _ := rel_eval hne L y ρv ρ h
      funext w; show _ = ((eval (toStr M hne) x ρ w ∧ eval (toStr M hne) y ρ w)); rw [← ih, ← ih']; exact propext (L.and x y ρv w)
  | _, _, .or x y, ρv, ρ, h => by
      have ih : M.pr (L.ev x ρv) = _ := rel_eval hne L x ρv ρ h
      have ih' : M.pr (L.ev y ρv) = _ := rel_eval hne L y ρv ρ h
      funext w; show _ = ((eval (toStr M hne) x ρ w ∨ eval (toStr M hne) y ρ w)); rw [← ih, ← ih']; exact propext (L.or x y ρv w)
  | _, _, .imp x y, ρv, ρ, h => by
      have ih : M.pr (L.ev x ρv) = _ := rel_eval hne L x ρv ρ h
      have ih' : M.pr (L.ev y ρv) = _ := rel_eval hne L y ρv ρ h
      funext w; show _ = ((eval (toStr M hne) x ρ w → eval (toStr M hne) y ρ w)); rw [← ih, ← ih']; exact propext (L.imp x y ρv w)
  | _, _, .box x, ρv, ρ, h => by
      have ih : M.pr (L.ev x ρv) = _ := rel_eval hne L x ρv ρ h
      funext w; show _ = (∀ v, M.R w v → eval (toStr M hne) x ρ v); rw [← ih]; exact propext (L.box x ρv w)
  | _, _, .all a b, ρv, ρ, h => by
      funext w; apply propext; rw [L.all]
      constructor
      · intro H z hz
        obtain ⟨x, hx⟩ := hz
        have ih : M.pr (L.ev b (x, ρv)) = _ := rel_eval hne L b (x, ρv) (z, ρ) ⟨hx, h⟩
        exact ih ▸ H x
      · intro H x
        have hx := (up_rel M hne a).1 x
        have ih : M.pr (L.ev b (x, ρv)) = _ := rel_eval hne L b (x, ρv) (_, ρ) ⟨hx, h⟩
        exact ih ▸ H _ ⟨x, hx⟩
  | _, _, .ex a b, ρv, ρ, h => by
      funext w; apply propext; rw [L.ex]
      constructor
      · intro ⟨x, H⟩
        have hx := (up_rel M hne a).1 x
        have ih : M.pr (L.ev b (x, ρv)) = _ := rel_eval hne L b (x, ρv) (_, ρ) ⟨hx, h⟩
        exact ⟨_, ⟨x, hx⟩, ih ▸ H⟩
      · intro ⟨z, ⟨x, hx⟩, H⟩
        have ih : M.pr (L.ev b (x, ρv)) = _ := rel_eval hne L b (x, ρv) (z, ρ) ⟨hx, h⟩
        exact ⟨x, ih ▸ H⟩
  | _, _, .allE b, ρv, ρ, h => by
      funext w; apply propext; rw [L.allE]
      have ih : ∀ y, M.pr (L.ev b (y, ρv)) = eval (toStr M hne) b (y, ρ) := fun y =>
        rel_eval hne L b (y, ρv) (y, ρ) ⟨rfl, h⟩
      exact ⟨fun H y hy => ih y ▸ H y hy, fun H y hy => (ih y).symm ▸ H y hy⟩
  | _, _, .exE b, ρv, ρ, h => by
      funext w; apply propext; rw [L.exE]
      have ih : ∀ y, M.pr (L.ev b (y, ρv)) = eval (toStr M hne) b (y, ρ) := fun y =>
        rel_eval hne L b (y, ρv) (y, ρ) ⟨rfl, h⟩
      exact ⟨fun ⟨y, hy, H⟩ => ⟨y, hy, ih y ▸ H⟩, fun ⟨y, hy, H⟩ => ⟨y, hy, (ih y).symm ▸ H⟩⟩
  | _, _, .eq a x y, ρv, ρ, h => by
      funext w; apply propext; rw [L.eq]
      exact (eqT_rel M hne a _ _ _ _ (rel_eval hne L x ρv ρ h) (rel_eval hne L y ρv ρ h)).symm
  | _, _, .pos, ρv, ρ, _ => by rw [L.pos]; exact (up_rel M hne th).1 M.P

theorem toStr_entities (hne : Nonempty (M.C .e)) : ∀ x, (toStr M hne).A .e x := fun x => ⟨x, rfl⟩

theorem envRel_of_envA (hne : Nonempty (M.C .e)) : ∀ (Γ : List FTy) (ρ : Env W (M.C .e) Γ),
    EnvA (toStr M hne) Γ ρ → ∃ ρv, EnvRel M Γ ρv ρ
  | [], _, _ => ⟨(), trivial⟩
  | _ :: Γ, ρ, ⟨⟨x, hx⟩, h⟩ => let ⟨ρv, hv⟩ := envRel_of_envA hne Γ ρ.2 h; ⟨(x, ρv), hx, hv⟩

/-- **M1, closure.** -/
theorem toStr_closed (hne : Nonempty (M.C .e)) (L : LGen M) : Closed (toStr M hne) :=
  fun tm ρ hA => let ⟨ρv, hv⟩ := envRel_of_envA M hne _ ρ hA; ⟨_, rel_eval M hne L tm ρv ρ hv⟩

/-- **M1, respect.** -/
theorem toStr_resp (hne : Nonempty (M.C .e)) : Resp (toStr M hne) := by
  intro a b F ⟨f, hf⟩ z z' ⟨x, hx⟩ ⟨x', hx'⟩ hzz
  have e : x = x' := (eqT_rel M hne a _ _ _ _ hx hx').1 hzz
  subst e
  exact (eqT_rel M hne b _ _ _ _ (hf x z hx) (hf x z' hx')).2 rfl

/-- **M1, truth.** Every 𝓛-sentence has the same value in `M` and in `toStr M`. -/
theorem toStr_truth (hne : Nonempty (M.C .e)) (L : LGen M) (φ : Tm [] .s) (w : W) :
    eval (toStr M hne) φ () w ↔ M.pr (L.ev φ ()) w := by
  have h : M.pr (L.ev φ ()) = eval (toStr M hne) φ () := rel_eval M hne L φ () () trivial
  rw [h]

end M1

/-! ## M2: from a closed `Resp` structure to a v4 model (quotient by `eqT`) -/

section M2

/-- A chosen representative (core Lean has no `Quotient.out`). -/
noncomputable def qout {α : Type} {s : Setoid α} (q : Quotient s) : α :=
  Classical.choose (Quotient.exists_rep q)

theorem qout_eq {α : Type} {s : Setoid α} (q : Quotient s) : Quotient.mk s (qout q) = q :=
  Classical.choose_spec (Quotient.exists_rep q)

theorem mk_qout {α : Type} {s : Setoid α} (a : α) : s.r (qout (Quotient.mk s a)) a :=
  Quotient.exact (qout_eq (Quotient.mk s a))

variable {D : Type} (S : Str W D)

def setoidT (t : FTy) : Setoid {z // S.A t z} where
  r x y := eqT S t x.1 y.1
  iseqv := ⟨fun x => eqT_refl S t x.1, fun h => eqT_symm S t h, fun h k => eqT_trans S t h k⟩

/-- The carrier at `t`: admitted objects modulo `eqT`. -/
def Car (t : FTy) : Type := Quotient (setoidT S t)

theorem adm_app (hC : Closed S) {a b : FTy} (F : Den W D (.arr a b)) (z : Den W D a)
    (hF : S.A (.arr a b) F) (hz : S.A a z) : S.A b (F z) :=
  hC (Γ := [.arr a b, a]) (.app (.var .zero) (.var (.succ .zero))) (F, (z, ())) ⟨hF, hz, trivial⟩

def apQ (hC : Closed S) (hR : Resp S) {a b : FTy} : Car S (.arr a b) → Car S a → Car S b :=
  Quotient.lift₂ (s₁ := setoidT S (.arr a b)) (s₂ := setoidT S a) (fun F z =>
      Quotient.mk (setoidT S b) ⟨F.1 z.1, adm_app S hC F.1 z.1 F.2 z.2⟩)
    (fun F z _ z' hFG hzz => Quotient.sound
      (eqT_trans S b (hR a b F.1 F.2 z.1 z'.1 z.2 z'.2 hzz) (hFG z'.1 z'.2)))

/-- The quotient model. -/
def ofStr (hC : Closed S) (hR : Resp S) : VM W where
  R := S.R
  C := Car S
  act := Quotient.lift (s := setoidT S .e) (fun y w => S.act y.1 w) (fun y y' h => by
    show (fun w => S.act y.1 w) = (fun w => S.act y'.1 w)
    have h' : y.1 = y'.1 := h
    rw [h'])
  pr := Quotient.lift (s := setoidT S .s) (fun p => p.1) (fun _ _ h => h)
  pr_inj := fun p q => Quotient.inductionOn₂ (s₁ := setoidT S .s) (s₂ := setoidT S .s) p q
    fun _ _ h => Quotient.sound h
  ap := apQ S hC hR
  ap_ext := fun {a b} f g => Quotient.inductionOn₂ (s₁ := setoidT S (.arr a b))
    (s₂ := setoidT S (.arr a b)) f g fun F G h =>
      Quotient.sound fun z hz => Quotient.exact (h (Quotient.mk (setoidT S a) ⟨z, hz⟩))
  P := Quotient.mk (setoidT S th) ⟨S.P, hC (Γ := []) .pos () trivial⟩

variable (hC : Closed S) (hR : Resp S)

/-- Chosen representatives of an environment of classes. -/
noncomputable def outEnv : (Γ : List FTy) → VEnv (ofStr S hC hR) Γ → Env W D Γ
  | [], _ => ()
  | t :: Γ, ρv => ((qout (s := setoidT S t) ρv.1).1, outEnv Γ ρv.2)

theorem outEnv_A : ∀ (Γ : List FTy) (ρv : VEnv (ofStr S hC hR) Γ), EnvA S Γ (outEnv S hC hR Γ ρv)
  | [], _ => trivial
  | t :: Γ, ρv => ⟨(qout (s := setoidT S t) ρv.1).2, outEnv_A Γ ρv.2⟩

noncomputable def evQ {Γ : List FTy} {t : FTy} (tm : Tm Γ t) (ρv : VEnv (ofStr S hC hR) Γ) :
    Car S t :=
  Quotient.mk (setoidT S t) ⟨eval S tm (outEnv S hC hR Γ ρv), hC tm _ (outEnv_A S hC hR Γ ρv)⟩

theorem out_mk (t : FTy) (z : {z // S.A t z}) :
    eqT S t (qout (s := setoidT S t) (Quotient.mk (setoidT S t) z)).1 z.1 :=
  mk_qout (s := setoidT S t) z

theorem vget_out : ∀ {Γ t} (i : Var Γ t) (ρv : VEnv (ofStr S hC hR) Γ),
    Quotient.mk (setoidT S t) ⟨i.get (outEnv S hC hR Γ ρv), hC (.var i) _ (outEnv_A S hC hR Γ ρv)⟩
      = i.vget (ofStr S hC hR) ρv
  | _ :: _, _, .zero, ρv => qout_eq (s := setoidT S _) ρv.1
  | _ :: _, _, .succ i, ρv => vget_out i ρv.2

include hC hR in
/-- Changing the representative of one class does not change the value (fundamental lemma). -/
theorem eval_out (hE : ∀ x, S.A .e x) {Γ : List FTy} {a t : FTy} (b : Tm (a :: Γ) t)
    (z : {z // S.A a z}) (ρ : Env W D Γ) (hρ : EnvA S Γ ρ) :
    eqT S t (eval S b ((qout (s := setoidT S a) (Quotient.mk (setoidT S a) z)).1, ρ))
      (eval S b (z.1, ρ)) :=
  fund S hE hC hR b _ _ ⟨(qout (s := setoidT S a) _).2, hρ⟩ ⟨z.2, hρ⟩
    ⟨out_mk S a z, envR_refl S _ ρ⟩

/-- **M2.** The quotient is a v4 𝓛-general model. -/
noncomputable def ofStr_lgen (hE : ∀ x, S.A .e x) : LGen (ofStr S hC hR) where
  ev := evQ S hC hR
  var := fun i ρv => vget_out S hC hR i ρv
  app := fun _ _ _ => rfl
  lam := fun {Γ a b} t ρv x => by
    induction x using Quotient.inductionOn (s := setoidT S a) with
    | h z =>
      show Quotient.mk (setoidT S b) _ = Quotient.mk (setoidT S b) _
      exact Quotient.sound (eqT_symm S b (eval_out S hC hR hE t z _ (outEnv_A S hC hR Γ ρv)))
  top := fun _ _ => Iff.rfl
  bot := fun _ _ => Iff.rfl
  neg := fun _ _ _ => Iff.rfl
  and := fun _ _ _ _ => Iff.rfl
  or := fun _ _ _ _ => Iff.rfl
  imp := fun _ _ _ _ => Iff.rfl
  box := fun _ _ _ => Iff.rfl
  all := fun {Γ} a b ρv w => by
    show (∀ z, S.A a z → eval S b (z, outEnv S hC hR Γ ρv) w) ↔
      ∀ x : Car S a, eval S b ((qout (s := setoidT S a) x).1, outEnv S hC hR Γ ρv) w
    constructor
    · intro H x; exact H _ (qout (s := setoidT S a) x).2
    · intro H z hz
      have e : eval S b _ = eval S b (z, _) :=
        eval_out S hC hR hE b ⟨z, hz⟩ _ (outEnv_A S hC hR Γ ρv)
      exact e ▸ H (Quotient.mk (setoidT S a) ⟨z, hz⟩)
  ex := fun {Γ} a b ρv w => by
    show (∃ z, S.A a z ∧ eval S b (z, outEnv S hC hR Γ ρv) w) ↔
      ∃ x : Car S a, eval S b ((qout (s := setoidT S a) x).1, outEnv S hC hR Γ ρv) w
    constructor
    · intro ⟨z, hz, H⟩
      have e : eval S b _ = eval S b (z, _) :=
        eval_out S hC hR hE b ⟨z, hz⟩ _ (outEnv_A S hC hR Γ ρv)
      exact ⟨Quotient.mk (setoidT S a) ⟨z, hz⟩, e.symm ▸ H⟩
    · intro ⟨x, H⟩; exact ⟨_, (qout (s := setoidT S a) x).2, H⟩
  allE := fun {Γ} b ρv w => by
    show (∀ y, S.act y w → eval S b (y, outEnv S hC hR Γ ρv) w) ↔
      ∀ y : Car S .e, (ofStr S hC hR).act y w →
        eval S b ((qout (s := setoidT S .e) y).1, outEnv S hC hR Γ ρv) w
    constructor
    · intro H y
      induction y using Quotient.inductionOn (s := setoidT S .e) with
      | h y0 =>
        intro hy
        have e : (qout (s := setoidT S .e) (Quotient.mk (setoidT S .e) y0)).1 = y0.1 :=
          out_mk S .e y0
        rw [e]; exact H _ hy
    · intro H y hy
      have e : (qout (s := setoidT S .e) (Quotient.mk (setoidT S .e) ⟨y, hE y⟩)).1 = y :=
        out_mk S .e ⟨y, hE y⟩
      have := H (Quotient.mk (setoidT S .e) ⟨y, hE y⟩) hy
      rw [e] at this; exact this
  exE := fun {Γ} b ρv w => by
    show (∃ y, S.act y w ∧ eval S b (y, outEnv S hC hR Γ ρv) w) ↔
      ∃ y : Car S .e, (ofStr S hC hR).act y w ∧
        eval S b ((qout (s := setoidT S .e) y).1, outEnv S hC hR Γ ρv) w
    constructor
    · intro ⟨y, hy, H⟩
      have e : (qout (s := setoidT S .e) (Quotient.mk (setoidT S .e) ⟨y, hE y⟩)).1 = y :=
        out_mk S .e ⟨y, hE y⟩
      refine ⟨Quotient.mk (setoidT S .e) ⟨y, hE y⟩, hy, ?_⟩
      rw [e]; exact H
    · intro ⟨y, hy, H⟩
      revert hy H
      induction y using Quotient.inductionOn (s := setoidT S .e) with
      | h y0 =>
        intro hy H
        have e : (qout (s := setoidT S .e) (Quotient.mk (setoidT S .e) y0)).1 = y0.1 :=
          out_mk S .e y0
        rw [e] at H; exact ⟨_, hy, H⟩
  eq := fun a x y ρv w => ⟨fun h => Quotient.sound h, fun h => Quotient.exact h⟩
  pos := fun _ => rfl

/-- **M2, truth.** -/
theorem ofStr_truth (hE : ∀ x, S.A .e x) (φ : Tm [] .s) (w : W) :
    (ofStr S hC hR).pr ((ofStr_lgen S hC hR hE).ev φ ()) w ↔ eval S φ () w := Iff.rfl

end M2

/-! ## The two classes satisfy the same 𝓛-sentences -/

/-- `φ` holds in every v4 𝓛-general model (nonempty domain of individuals) of `T`. -/
def ValidV4 (T : Tm [] .s → Prop) (φ : Tm [] .s) : Prop :=
  ∀ (W : Type) (M : VM W) (L : LGen M), Nonempty (M.C .e) →
    (∀ ψ, T ψ → ∀ w, M.pr (L.ev ψ ()) w) → ∀ w, M.pr (L.ev φ ()) w

/-- `φ` holds in every closed `Resp` structure (nonempty, all entities admitted) of `T`. -/
def ValidStr (T : Tm [] .s → Prop) (φ : Tm [] .s) : Prop :=
  ∀ (W D : Type) (S : Str W D), Nonempty D → (∀ x, S.A .e x) → Closed S → Resp S →
    (∀ ψ, T ψ → ∀ w, eval S ψ () w) → ∀ w, eval S φ () w

theorem valid_iff (T : Tm [] .s → Prop) (φ : Tm [] .s) : ValidV4 T φ ↔ ValidStr T φ := by
  constructor
  · intro H W D S hne hE hC hR hT w
    have hne' : Nonempty ((ofStr S hC hR).C .e) :=
      let ⟨d⟩ := hne; ⟨Quotient.mk (setoidT S .e) ⟨d, hE d⟩⟩
    exact (ofStr_truth S hC hR hE φ w).1
      (H W _ (ofStr_lgen S hC hR hE) hne' (fun ψ hψ v => (ofStr_truth S hC hR hE ψ v).2 (hT ψ hψ v)) w)
  · intro H W M L hne hT w
    exact (toStr_truth M hne L φ w).1
      (H W _ (toStr M hne) hne (toStr_entities M hne) (toStr_closed M hne L) (toStr_resp M hne)
        (fun ψ hψ v => (toStr_truth M hne L ψ v).2 (hT ψ hψ v)) w)

end Programme.«20261022-1724-ontological».Run3.LX

/-! ## Soundness over v4's 𝓛-general models, and K1/K14 there

Composition of K4's `valid_of_deriv` (closed `Resp` structures) with th's bridge `valid_iff`. -/

namespace Programme.«20261022-1724-ontological».Run3.V4
open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.HOLX

/-- **Soundness over v4's def:lgeneral models.** A certified deep derivation (`∀E`/`∃I` instances
and Leibniz sides `𝓛`-terms, Leibniz motives `𝓛`-formulas) of the `𝓛`-sentence `φ` at a world
variable from the `𝓛`-theory `T` makes `φ` true at every world of every v4 `𝓛`-general model of
`T` with a nonempty domain of individuals. -/
theorem sound_v4 {T : Tm [] .s → Prop} {φ : Tm [] .s}
    (d : Deriv T (fun a t => Cert a t) [.w] [] (.holds (emb nilR φ) var0)) : ValidV4 T φ :=
  (valid_iff T φ).2 fun _ _ S _ hE hC hR hT => valid_of_deriv S hE hC hR hT d

/-- **K1 (run 2) over v4's models.** In every v4 `𝓛`-general model in which variant 2's `Ax2a`,
`Ax2b`, `Ax3`, `Ax4`, `Ax1GenTwo` and `∃x.⊤` hold at every world, unrestricted `Ax1Gen`, modal
collapse and `∃ᴱx. G x` hold at every world.  (`∃x.⊤` gives the nonempty domain.) -/
theorem k1_valid_v4 {W : Type} (M : VM W) (L : LGen M)
    (hT : ∀ ψ, K1.T2 ψ → ∀ w, M.pr (L.ev ψ ()) w) (w : W) :
    M.pr (L.ev (K1.Ax1Gen : Tm [] .s) ()) w ∧ M.pr (L.ev (K1.MC : Tm [] .s) ()) w ∧
      M.pr (L.ev (K1.ExG : Tm [] .s) ()) w := by
  have hne : Nonempty (M.C .e) := by
    obtain ⟨x, _⟩ := (L.ex (Γ := []) .e .top () w).1 (hT K1.NonEmpty .ne w)
    exact ⟨x⟩
  exact ⟨sound_v4 (K1.ax1Gen_of_two (r := nilR) (i := var0) (hs := [])) W M L hne hT w,
    sound_v4 (K1.mc (r := nilR) (i := var0) (hs := [])) W M L hne hT w,
    sound_v4 (K1.gex (r := nilR) (i := var0) (hs := [])) W M L hne hT w⟩

/-- **K14 (run 2) over v4's models.** In every v4 `𝓛`-general model with a nonempty domain of
individuals in which `Ax2a`, `Ax2b`, plain `Ax4`, `P E₃` and `P G` hold at every world,
`∃ᴱx. G x` and modal collapse hold at every world, on any frame. -/
theorem k14_valid_v4 {W : Type} (M : VM W) (L : LGen M) (hne : Nonempty (M.C .e))
    (hT : ∀ ψ, K14.T3 ψ → ∀ w, M.pr (L.ev ψ ()) w) (w : W) :
    M.pr (L.ev (K1.ExG : Tm [] .s) ()) w ∧ M.pr (L.ev (K1.MC : Tm [] .s) ()) w :=
  ⟨sound_v4 (K14.gex3 (r := nilR) (i := var0) (hs := [])) W M L hne hT w,
    sound_v4 (K14.mc3 (r := nilR) (i := var0) (hs := [])) W M L hne hT w⟩

end Programme.«20261022-1724-ontological».Run3.V4

/-! ## Target E over v4's models: `Two_equivalent` for variants 2 and 3′

`OpenQuestions.Ax1GenTwoVariant2.Two_equivalent` and `OpenQuestions.Ax1GenTwoVariant3Plain.Two_equivalent`
over **all** v4 𝓛-general models: given the module's `Ax2a`, `Ax2b`, `Ax3 = P E` (the module's own `E`),
plain `Ax4` and `∃x.⊤` at every world, `Ax1GenTwo` holds at every world iff unrestricted `Ax1Gen`
does.  `⇒` is `K1.ax1Gen_of_two` (variant 2) / `K3p.ax1Gen_of_two` (variant 3′); `⇐` is
`Conv.two_of_gen`, which uses `Ax1Gen` alone. -/

namespace Programme.«20261022-1724-ontological».Run3.V4
open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.HOLX

/-- **Variant 3′ (run 2's K1 for `Ax1GenTwoVariant3Plain`) over v4's models.**  In every v4
𝓛-general model in which `Ax2a`, `Ax2b`, `Ax3 = P E` (variant 3′'s `E`), plain `Ax4`,
`Ax1GenTwo` and `∃x.⊤` hold at every world, unrestricted `Ax1Gen`, modal collapse and `∃ᴱx. G x`
hold at every world. -/
theorem k3p_valid_v4 {W : Type} (M : VM W) (L : LGen M)
    (hT : ∀ ψ, K3p.T3p ψ → ∀ w, M.pr (L.ev ψ ()) w) (w : W) :
    M.pr (L.ev (K1.Ax1Gen : Tm [] .s) ()) w ∧ M.pr (L.ev (K1.MC : Tm [] .s) ()) w ∧
      M.pr (L.ev (K1.ExG : Tm [] .s) ()) w := by
  have hne : Nonempty (M.C .e) := by
    obtain ⟨x, _⟩ := (L.ex (Γ := []) .e .top () w).1 (hT K1.NonEmpty .ne w)
    exact ⟨x⟩
  exact ⟨sound_v4 (K3p.ax1Gen_of_two (r := nilR) (i := var0) (hs := [])) W M L hne hT w,
    sound_v4 (K3p.mc (r := nilR) (i := var0) (hs := [])) W M L hne hT w,
    sound_v4 (K3p.gex (r := nilR) (i := var0) (hs := [])) W M L hne hT w⟩

/-- `Ax1Gen ⇒ Ax1GenTwo` in every v4 𝓛-general model with nonempty individuals (`Two_weaker`). -/
theorem two_of_gen_v4 {W : Type} (M : VM W) (L : LGen M) (hne : Nonempty (M.C .e))
    (hG : ∀ w, M.pr (L.ev (K1.Ax1Gen : Tm [] .s) ()) w) (w : W) :
    M.pr (L.ev (K1.Ax1GenTwo : Tm [] .s) ()) w :=
  sound_v4 (Conv.two_of_gen (r := nilR) (i := var0) (hs := []) Conv.TGen.gen) W M L hne
    (fun ψ h => by cases h; exact hG) w

/-- **`Two_equivalent` of `Ax1GenTwoVariant2`, over all v4 𝓛-general models.** -/
theorem two_equivalent_v2 {W : Type} (M : VM W) (L : LGen M)
    (h2a : ∀ w, M.pr (L.ev (K1.Ax2a : Tm [] .s) ()) w) (h2b : ∀ w, M.pr (L.ev (K1.Ax2b : Tm [] .s) ()) w)
    (h3 : ∀ w, M.pr (L.ev (K1.Pos K1.ET : Tm [] .s) ()) w) (h4 : ∀ w, M.pr (L.ev (K1.Ax4 : Tm [] .s) ()) w)
    (hne : ∀ w, M.pr (L.ev (K1.NonEmpty : Tm [] .s) ()) w) :
    (∀ w, M.pr (L.ev (K1.Ax1GenTwo : Tm [] .s) ()) w) ↔ (∀ w, M.pr (L.ev (K1.Ax1Gen : Tm [] .s) ()) w) := by
  constructor
  · intro h2 w
    exact (k1_valid_v4 M L (fun ψ hψ => by cases hψ <;> assumption) w).1
  · intro hG w
    obtain ⟨x, _⟩ := (L.ex (Γ := []) .e .top () w).1 (hne w)
    exact two_of_gen_v4 M L ⟨x⟩ hG w

/-- **`Two_equivalent` of `Ax1GenTwoVariant3Plain` (variant 3′), over all v4 𝓛-general models.** -/
theorem two_equivalent_v3p {W : Type} (M : VM W) (L : LGen M)
    (h2a : ∀ w, M.pr (L.ev (K1.Ax2a : Tm [] .s) ()) w) (h2b : ∀ w, M.pr (L.ev (K1.Ax2b : Tm [] .s) ()) w)
    (h3 : ∀ w, M.pr (L.ev (K1.Pos K3p.ET3 : Tm [] .s) ()) w) (h4 : ∀ w, M.pr (L.ev (K1.Ax4 : Tm [] .s) ()) w)
    (hne : ∀ w, M.pr (L.ev (K1.NonEmpty : Tm [] .s) ()) w) :
    (∀ w, M.pr (L.ev (K1.Ax1GenTwo : Tm [] .s) ()) w) ↔ (∀ w, M.pr (L.ev (K1.Ax1Gen : Tm [] .s) ()) w) := by
  constructor
  · intro h2 w
    exact (k3p_valid_v4 M L (fun ψ hψ => by cases hψ <;> assumption) w).1
  · intro hG w
    obtain ⟨x, _⟩ := (L.ex (Γ := []) .e .top () w).1 (hne w)
    exact two_of_gen_v4 M L ⟨x⟩ hG w

end Programme.«20261022-1724-ontological».Run3.V4



/-! # Variant 2 over extensional carriers: v4's separating sentence fails, and is not derivable

Section `Ext` below is r1's `agents/r1/lean/Programme/Run3/Respect.lean` (claim K6 of run 3),
lines 138-652, copied unchanged: its preamble (the library's `LGeneralFull` definitions) is
identical to `Programme.Run3.LX` above, so it is opened instead of copied.

Section `V2` is new.  `symId`: worlds `2^ℕ`, **identity frame**, one always-actual entity,
`P φ w := φ () w`, the flip group.  Over the extensional carriers `strR symId`:
* `v2_holds`: variant 2's `Ax1Gen` (unrestricted), `Ax2a`, `Ax2b`, `Ax3`, `Ax4`, and also `MC`,
  `∃ᴱG` hold at every world (deep `𝓛`-sentences, evaluated);
* `resp_symId`: the structure is `Closed`, admits all entities and respects `eqT` (`Resp`);
* `sep_fails`: v4's `A ∃p. (Atom p ∧ p)` (r1's `phiSep`) fails at every world;
* `sep_not_derivable`: by K4's `HOLX.valid_of_deriv`, no certified derivation (with `leib`)
  derives `phiSep` from the variant-2 theory `T2`. -/

namespace Programme.«20261022-1724-ontological».Run3.SepV2
open Programme.«20261022-1724-ontological».Run3.LX

variable {W D : Type}

structure Model (W D : Type) where
  R : W → W → Prop
  act : D → W → Prop
  AS : (W → Prop) → Prop
  AT : (D → W → Prop) → Prop
  AH : ((D → W → Prop) → W → Prop) → Prop
  P : (D → W → Prop) → W → Prop

/-! ## Symmetric structures -/

/-- A filtration of world bijections (pairs `(f, g)`, `g` the inverse of `f`). -/
structure Sym (R : W → W → Prop) (act : D → W → Prop) (P : Den W D th) where
  Fx : Nat → (W → W) → (W → W) → Prop
  mono : ∀ {n m f g}, n ≤ m → Fx m f g → Fx n f g
  inv : ∀ {n f g}, Fx n f g → Fx n g f
  fg : ∀ {f g}, Fx 0 f g → ∀ w, f (g w) = w
  hR : ∀ {f g}, Fx 0 f g → ∀ w v, R (f w) (f v) ↔ R w v
  hact : ∀ {f g}, Fx 0 f g → ∀ y w, act y (f w) ↔ act y w
  hP : ∀ {f g}, Fx 0 f g → fl f g th P = P
  conj : ∀ {f g}, Fx 0 f g → ∀ n, ∃ m, ∀ c d, Fx m c d →
    Fx n (fun w => f (c (g w))) (fun w => f (d (g w)))

variable {R : W → W → Prop} {act : D → W → Prop} {P : Den W D th}

def Sup (S : Sym R act P) (t : FTy) (x : Den W D t) : Prop :=
  ∃ n, ∀ f g, S.Fx n f g → fl f g t x = x

variable (S : Sym R act P)

theorem sup_fl {f g : W → W} (h : S.Fx 0 f g) (t : FTy) (x : Den W D t) (hx : Sup S t x) :
    Sup S t (fl f g t x) := by
  obtain ⟨n, hn⟩ := hx
  obtain ⟨m, hm⟩ := S.conj h n
  refine ⟨m, fun c d hcd => ?_⟩
  have h1 : fl g f t (fl c d t (fl f g t x)) = x := by
    rw [fl_comp, fl_comp]; exact hn _ _ (hm c d hcd)
  have h2 := fl_inv (S.fg (S.inv h)) t (fl c d t (fl f g t x))
  rw [h1] at h2; exact h2.symm

def flEnv (f g : W → W) : (Γ : List FTy) → Env W D Γ → Env W D Γ
  | [], _ => ()
  | t :: Γ, ρ => (fl f g t ρ.1, flEnv f g Γ ρ.2)

theorem get_fl (f g : W → W) : ∀ {Γ t} (i : Var Γ t) (ρ : Env W D Γ),
    i.get (flEnv f g Γ ρ) = fl f g t (i.get ρ)
  | _, _, .zero, _ => rfl
  | _, _, .succ i, ρ => get_fl f g i ρ.2

theorem sup_app {a b : FTy} {F : Den W D (.arr a b)} {x : Den W D a}
    (hF : Sup S (.arr a b) F) (hx : Sup S a x) : Sup S b (F x) := by
  obtain ⟨n, hn⟩ := hF
  obtain ⟨m, hm⟩ := hx
  refine ⟨max n m, fun f g hfg => ?_⟩
  have e1 := hn f g (S.mono (Nat.le_max_left n m) hfg)
  have e2 := hm g f (S.inv (S.mono (Nat.le_max_right n m) hfg))
  have := congrFun e1 x
  show fl f g b (F x) = F x
  calc fl f g b (F x) = fl f g b (F (fl g f a x)) := by rw [e2]
    _ = F x := this

/-- Logical relation, guarded by support at arrow domains. -/
def rel : (t : FTy) → Den W D t → Den W D t → Prop
  | .e, x, y => x = y
  | .s, x, y => x = y
  | .arr a b, F, G => ∀ x y, Sup S a x → Sup S a y → rel a x y → rel b (F x) (G y)

def AdmR (t : FTy) (x : Den W D t) : Prop := Sup S t x ∧ rel S t x x

def strR : Str W D := ⟨R, act, P, AdmR S⟩

theorem sup_e (x : D) : Sup S .e x := ⟨0, fun _ _ _ => rfl⟩

theorem rel_symm : ∀ (t : FTy) (x y : Den W D t), rel S t x y → rel S t y x
  | .e, _, _, h => h.symm
  | .s, _, _, h => h.symm
  | .arr a b, _, _, h => fun x y hx hy hxy =>
      rel_symm b _ _ (h y x hy hx (rel_symm a _ _ hxy))

theorem rel_trans : ∀ (t : FTy) (x y z : Den W D t), rel S t x y → rel S t y z → rel S t x z
  | .e, _, _, _, h1, h2 => h1.trans h2
  | .s, _, _, _, h1, h2 => h1.trans h2
  | .arr a b, _, _, _, h1, h2 => fun x y hx hy hxy => by
      have hyy : rel S a y y := rel_trans a _ _ _ (rel_symm S a _ _ hxy) hxy
      exact rel_trans b _ _ _ (h1 x y hx hy hxy) (h2 y y hy hy hyy)

theorem rel_fl : ∀ (t : FTy) {f g : W → W}, S.Fx 0 f g → ∀ x y, rel S t x y →
    rel S t (fl f g t x) (fl f g t y)
  | .e, _, _, _, _, _, h => h
  | .s, f, _, _, x, y, h => by
      show (fun w => x (f w)) = fun w => y (f w)
      have h' : x = y := h
      rw [h']
  | .arr a b, f, g, hfg, F, G, hFG => fun x y hx hy hxy => by
      show rel S b (fl f g b (F (fl g f a x))) (fl f g b (G (fl g f a y)))
      exact rel_fl b hfg _ _ (hFG _ _ (sup_fl S (S.inv hfg) a x hx) (sup_fl S (S.inv hfg) a y hy)
        (rel_fl a (S.inv hfg) x y hxy))

theorem adm_flR (t : FTy) {f g : W → W} (h : S.Fx 0 f g) (x : Den W D t) (hx : AdmR S t x) :
    AdmR S t (fl f g t x) :=
  ⟨sup_fl S h t x hx.1, rel_fl S t h x x hx.2⟩

theorem forall_flR {f g : W → W} (h : S.Fx 0 f g) (t : FTy) (Q : Den W D t → Prop) :
    (∀ x, AdmR S t x → Q (fl f g t x)) ↔ (∀ x, AdmR S t x → Q x) :=
  ⟨fun hq x hx => by
    have := hq _ (adm_flR S t (S.inv h) x hx)
    rwa [fl_inv (S.fg (S.inv h))] at this,
   fun hq x hx => hq _ (adm_flR S t h x hx)⟩

theorem exists_flR {f g : W → W} (h : S.Fx 0 f g) (t : FTy) (Q : Den W D t → Prop) :
    (∃ x, AdmR S t x ∧ Q (fl f g t x)) ↔ (∃ x, AdmR S t x ∧ Q x) :=
  ⟨fun ⟨x, hx, hq⟩ => ⟨_, adm_flR S t h x hx, hq⟩,
   fun ⟨x, hx, hq⟩ => ⟨fl g f t x, adm_flR S t (S.inv h) x hx, by
     rw [fl_inv (S.fg (S.inv h))]; exact hq⟩⟩

theorem eqT_flR : ∀ (t : FTy) {f g : W → W}, S.Fx 0 f g → ∀ x y,
    eqT (strR S) t (fl f g t x) (fl f g t y) ↔ eqT (strR S) t x y
  | .e, _, _, _, _, _ => Iff.rfl
  | .s, f, g, h, x, y =>
      ⟨fun e => by
        have := congrArg (fl g f .s) e
        rwa [fl_inv (S.fg h), fl_inv (S.fg h)] at this,
       fun e => e ▸ rfl⟩
  | .arr a b, f, g, h, F, G => by
      show (∀ z, AdmR S a z → eqT (strR S) b (fl f g b (F (fl g f a z))) (fl f g b (G (fl g f a z))))
        ↔ ∀ z, AdmR S a z → eqT (strR S) b (F z) (G z)
      rw [← forall_flR S h a]
      refine forall_congr' fun z => imp_congr_right fun _ => ?_
      rw [fl_inv (S.fg h), eqT_flR b h]

theorem eval_actR {f g : W → W} (h : S.Fx 0 f g) :
    ∀ {Γ t} (tm : Tm Γ t) (ρ : Env W D Γ),
      eval (strR S) tm (flEnv f g Γ ρ) = fl f g t (eval (strR S) tm ρ)
  | _, _, .var i, ρ => get_fl f g i ρ
  | _, _, .app (a := a) F x, ρ => by
      show eval _ F _ (eval _ x _) = _
      rw [eval_actR h F ρ, eval_actR h x ρ]
      show fl f g _ (eval _ F ρ (fl g f a (fl f g a (eval _ x ρ)))) = _
      rw [fl_inv (S.fg h)]; rfl
  | _, _, .lam (a := a) b, ρ => by
      funext z
      have e := eval_actR h b (fl g f a z, ρ)
      have e2 : flEnv f g (a :: _) (fl g f a z, ρ) = (z, flEnv f g _ ρ) := by
        show (fl f g a (fl g f a z), _) = _
        rw [fl_inv (S.fg (S.inv h))]
      rw [e2] at e
      exact e
  | _, _, .top, _ => rfl
  | _, _, .bot, _ => rfl
  | _, _, .neg x, ρ => by
      funext w; show (¬ _) = _; rw [eval_actR h x ρ]; rfl
  | _, _, .and x y, ρ => by
      funext w; show (_ ∧ _) = _; rw [eval_actR h x ρ, eval_actR h y ρ]; rfl
  | _, _, .or x y, ρ => by
      funext w; show (_ ∨ _) = _; rw [eval_actR h x ρ, eval_actR h y ρ]; rfl
  | _, _, .imp x y, ρ => by
      funext w; show (_ → _) = _; rw [eval_actR h x ρ, eval_actR h y ρ]; rfl
  | _, _, .box x, ρ => by
      funext w
      show (∀ v, R w v → eval (strR S) x (flEnv f g _ ρ) v) = (∀ v, R (f w) v → eval (strR S) x ρ v)
      rw [eval_actR h x ρ]
      apply propext
      constructor
      · intro hv v hr
        have := hv (g v) (by rw [← S.hR h, S.fg h]; exact hr)
        simpa [fl, S.fg h] using this
      · intro hv v hr
        exact hv _ ((S.hR h w v).2 hr)
  | _, _, .all t b, ρ => by
      funext w
      show (∀ x, AdmR S t x → eval (strR S) b (x, flEnv f g _ ρ) w) =
        (∀ x, AdmR S t x → eval (strR S) b (x, ρ) (f w))
      apply propext
      rw [← forall_flR S h t]
      refine forall_congr' fun x => imp_congr_right fun _ => ?_
      exact Iff.of_eq (congrFun (eval_actR h b (x, ρ)) w)
  | _, _, .ex t b, ρ => by
      funext w
      show (∃ x, AdmR S t x ∧ eval (strR S) b (x, flEnv f g _ ρ) w) =
        (∃ x, AdmR S t x ∧ eval (strR S) b (x, ρ) (f w))
      apply propext
      rw [← exists_flR S h t]
      refine exists_congr fun x => and_congr_right fun _ => ?_
      exact Iff.of_eq (congrFun (eval_actR h b (x, ρ)) w)
  | _, _, .allE b, ρ => by
      funext w
      show (∀ y, act y w → eval (strR S) b (y, flEnv f g _ ρ) w) =
        (∀ y, act y (f w) → eval (strR S) b (y, ρ) (f w))
      apply propext
      refine forall_congr' fun y => ?_
      rw [S.hact h]
      exact imp_congr_right fun _ => Iff.of_eq (congrFun (eval_actR h b (y, ρ)) w)
  | _, _, .exE b, ρ => by
      funext w
      show (∃ y, act y w ∧ eval (strR S) b (y, flEnv f g _ ρ) w) =
        (∃ y, act y (f w) ∧ eval (strR S) b (y, ρ) (f w))
      apply propext
      refine exists_congr fun y => ?_
      rw [S.hact h]
      exact and_congr_right fun _ => Iff.of_eq (congrFun (eval_actR h b (y, ρ)) w)
  | _, _, .eq a x y, ρ => by
      funext w
      show eqT (strR S) a (eval _ x _) (eval _ y _) = eqT (strR S) a (eval _ x ρ) (eval _ y ρ)
      rw [eval_actR h x ρ, eval_actR h y ρ]
      exact propext (eqT_flR S a h _ _)
  | _, _, .pos, _ => (S.hP h).symm

/-! ## Environments -/

def EnvS : (Γ : List FTy) → Env W D Γ → Prop
  | [], _ => True
  | t :: Γ, ρ => Sup S t ρ.1 ∧ EnvS Γ ρ.2

def RelEnv : (Γ : List FTy) → Env W D Γ → Env W D Γ → Prop
  | [], _, _ => True
  | t :: Γ, ρ, ρ' => (Sup S t ρ.1 ∧ Sup S t ρ'.1 ∧ rel S t ρ.1 ρ'.1) ∧ RelEnv Γ ρ.2 ρ'.2

theorem envS_of_envA : ∀ (Γ : List FTy) (ρ : Env W D Γ), EnvA (strR S) Γ ρ → EnvS S Γ ρ
  | [], _, _ => trivial
  | _ :: Γ, ρ, h => ⟨h.1.1, envS_of_envA Γ ρ.2 h.2⟩

theorem relEnv_refl : ∀ (Γ : List FTy) (ρ : Env W D Γ), EnvA (strR S) Γ ρ → RelEnv S Γ ρ ρ
  | [], _, _ => trivial
  | _ :: Γ, ρ, h => ⟨⟨h.1.1, h.1.1, h.1.2⟩, relEnv_refl Γ ρ.2 h.2⟩

theorem envS_left : ∀ (Γ : List FTy) (ρ ρ' : Env W D Γ), RelEnv S Γ ρ ρ' → EnvS S Γ ρ
  | [], _, _, _ => trivial
  | _ :: Γ, ρ, ρ', h => ⟨h.1.1, envS_left Γ ρ.2 ρ'.2 h.2⟩

theorem envS_right : ∀ (Γ : List FTy) (ρ ρ' : Env W D Γ), RelEnv S Γ ρ ρ' → EnvS S Γ ρ'
  | [], _, _, _ => trivial
  | _ :: Γ, ρ, ρ', h => ⟨h.1.2.1, envS_right Γ ρ.2 ρ'.2 h.2⟩

theorem env_supR : ∀ (Γ : List FTy) (ρ : Env W D Γ), EnvS S Γ ρ →
    ∃ N, ∀ f g, S.Fx N f g → flEnv f g Γ ρ = ρ
  | [], _, _ => ⟨0, fun _ _ _ => rfl⟩
  | t :: Γ, (x, r), ⟨h1, h2⟩ => by
      obtain ⟨n, hn⟩ := h1
      obtain ⟨m, hm⟩ := env_supR Γ r h2
      refine ⟨max n m, fun f g hfg => ?_⟩
      show (fl f g t x, flEnv f g Γ r) = (x, r)
      rw [hn f g (S.mono (Nat.le_max_left n m) hfg), hm f g (S.mono (Nat.le_max_right n m) hfg)]

theorem sup_evalR {Γ t} (tm : Tm Γ t) (ρ : Env W D Γ) (hρ : EnvS S Γ ρ) :
    Sup S t (eval (strR S) tm ρ) := by
  obtain ⟨N, hN⟩ := env_supR S Γ ρ hρ
  refine ⟨N, fun f g hfg => ?_⟩
  rw [← eval_actR S (S.mono (Nat.zero_le N) hfg) tm ρ, hN f g hfg]

theorem rel_get : ∀ {Γ t} (i : Var Γ t) (ρ ρ' : Env W D Γ), RelEnv S Γ ρ ρ' →
    rel S t (i.get ρ) (i.get ρ')
  | _, _, .zero, _, _, h => h.1.2.2
  | _, _, .succ i, ρ, ρ', h => rel_get i ρ.2 ρ'.2 h.2

/-! ## Equality respects the relation, and is the relation on admitted objects -/

theorem eqT_congr : ∀ (t : FTy) (x x' y y' : Den W D t), rel S t x x' → rel S t y y' →
    (eqT (strR S) t x y ↔ eqT (strR S) t x' y')
  | .e, x, x', y, y', hx, hy => by
      have hx : x = x' := hx
      have hy : y = y' := hy
      subst hx; subst hy; exact Iff.rfl
  | .s, x, x', y, y', hx, hy => by
      have hx : x = x' := hx
      have hy : y = y' := hy
      subst hx; subst hy; exact Iff.rfl
  | .arr a b, F, F', G, G', hF, hG => by
      show (∀ z, AdmR S a z → eqT (strR S) b (F z) (G z)) ↔
        ∀ z, AdmR S a z → eqT (strR S) b (F' z) (G' z)
      refine forall_congr' fun z => imp_congr_right fun hz => ?_
      exact eqT_congr b _ _ _ _ (hF z z hz.1 hz.1 hz.2) (hG z z hz.1 hz.1 hz.2)

theorem eqT_rel : ∀ (t : FTy) (x y : Den W D t), AdmR S t x → AdmR S t y →
    eqT (strR S) t x y → rel S t x y
  | .e, _, _, _, _, h => h
  | .s, _, _, _, _, h => h
  | .arr a b, F, G, hF, hG, h => fun z1 z2 hz1 hz2 hz => by
      have hz22 : rel S a z2 z2 := rel_trans S a _ _ _ (rel_symm S a _ _ hz) hz
      have h1 : rel S b (F z1) (F z2) := hF.2 z1 z2 hz1 hz2 hz
      have h2 : eqT (strR S) b (F z2) (G z2) := h z2 ⟨hz2, hz22⟩
      have hAF : AdmR S b (F z2) := ⟨sup_app S hF.1 hz2, hF.2 z2 z2 hz2 hz2 hz22⟩
      have hAG : AdmR S b (G z2) := ⟨sup_app S hG.1 hz2, hG.2 z2 z2 hz2 hz2 hz22⟩
      exact rel_trans S b _ _ _ h1 (eqT_rel b _ _ hAF hAG h2)

theorem rel_eqT : ∀ (t : FTy) (x y : Den W D t), AdmR S t x → AdmR S t y →
    rel S t x y → eqT (strR S) t x y
  | .e, _, _, _, _, h => h
  | .s, _, _, _, _, h => h
  | .arr a b, F, G, hF, hG, h => fun z hz => by
      have hAF : AdmR S b (F z) := ⟨sup_app S hF.1 hz.1, hF.2 z z hz.1 hz.1 hz.2⟩
      have hAG : AdmR S b (G z) := ⟨sup_app S hG.1 hz.1, hG.2 z z hz.1 hz.1 hz.2⟩
      exact rel_eqT b _ _ hAF hAG (h z z hz.1 hz.1 hz.2)

/-! ## Fundamental lemma and closure -/

theorem fund : ∀ {Γ t} (tm : Tm Γ t) (ρ ρ' : Env W D Γ), RelEnv S Γ ρ ρ' →
    rel S t (eval (strR S) tm ρ) (eval (strR S) tm ρ')
  | _, _, .var i, ρ, ρ', h => rel_get S i ρ ρ' h
  | _, _, .app F x, ρ, ρ', h =>
      fund F ρ ρ' h _ _ (sup_evalR S x ρ (envS_left S _ ρ ρ' h))
        (sup_evalR S x ρ' (envS_right S _ ρ ρ' h)) (fund x ρ ρ' h)
  | _, _, .lam b, ρ, ρ', h => fun x y hx hy hxy => fund b (x, ρ) (y, ρ') ⟨⟨hx, hy, hxy⟩, h⟩
  | _, _, .top, _, _, _ => rfl
  | _, _, .bot, _, _, _ => rfl
  | _, _, .neg x, ρ, ρ', h => by
      have e : eval (strR S) x ρ = eval (strR S) x ρ' := fund x ρ ρ' h
      funext w; show (¬ _) = (¬ _); rw [e]
  | _, _, .and x y, ρ, ρ', h => by
      have e1 : eval (strR S) x ρ = eval (strR S) x ρ' := fund x ρ ρ' h
      have e2 : eval (strR S) y ρ = eval (strR S) y ρ' := fund y ρ ρ' h
      funext w; show (_ ∧ _) = (_ ∧ _); rw [e1, e2]
  | _, _, .or x y, ρ, ρ', h => by
      have e1 : eval (strR S) x ρ = eval (strR S) x ρ' := fund x ρ ρ' h
      have e2 : eval (strR S) y ρ = eval (strR S) y ρ' := fund y ρ ρ' h
      funext w; show (_ ∨ _) = (_ ∨ _); rw [e1, e2]
  | _, _, .imp x y, ρ, ρ', h => by
      have e1 : eval (strR S) x ρ = eval (strR S) x ρ' := fund x ρ ρ' h
      have e2 : eval (strR S) y ρ = eval (strR S) y ρ' := fund y ρ ρ' h
      funext w; show (_ → _) = (_ → _); rw [e1, e2]
  | _, _, .box x, ρ, ρ', h => by
      have e : eval (strR S) x ρ = eval (strR S) x ρ' := fund x ρ ρ' h
      funext w
      show (∀ v, R w v → eval (strR S) x ρ v) = (∀ v, R w v → eval (strR S) x ρ' v)
      rw [e]
  | _, _, .all t b, ρ, ρ', h => by
      funext w
      show (∀ x, AdmR S t x → eval (strR S) b (x, ρ) w) =
        (∀ x, AdmR S t x → eval (strR S) b (x, ρ') w)
      apply propext
      refine forall_congr' fun x => imp_congr_right fun hx => ?_
      have e : eval (strR S) b (x, ρ) = eval (strR S) b (x, ρ') :=
        fund b (x, ρ) (x, ρ') ⟨⟨hx.1, hx.1, hx.2⟩, h⟩
      rw [e]
  | _, _, .ex t b, ρ, ρ', h => by
      funext w
      show (∃ x, AdmR S t x ∧ eval (strR S) b (x, ρ) w) =
        (∃ x, AdmR S t x ∧ eval (strR S) b (x, ρ') w)
      apply propext
      refine exists_congr fun x => and_congr_right fun hx => ?_
      have e : eval (strR S) b (x, ρ) = eval (strR S) b (x, ρ') :=
        fund b (x, ρ) (x, ρ') ⟨⟨hx.1, hx.1, hx.2⟩, h⟩
      rw [e]
  | _, _, .allE b, ρ, ρ', h => by
      funext w
      show (∀ y, act y w → eval (strR S) b (y, ρ) w) = (∀ y, act y w → eval (strR S) b (y, ρ') w)
      apply propext
      refine forall_congr' fun y => imp_congr_right fun _ => ?_
      have e : eval (strR S) b (y, ρ) = eval (strR S) b (y, ρ') :=
        fund b (y, ρ) (y, ρ') ⟨⟨sup_e S y, sup_e S y, rfl⟩, h⟩
      rw [e]
  | _, _, .exE b, ρ, ρ', h => by
      funext w
      show (∃ y, act y w ∧ eval (strR S) b (y, ρ) w) = (∃ y, act y w ∧ eval (strR S) b (y, ρ') w)
      apply propext
      refine exists_congr fun y => and_congr_right fun _ => ?_
      have e : eval (strR S) b (y, ρ) = eval (strR S) b (y, ρ') :=
        fund b (y, ρ) (y, ρ') ⟨⟨sup_e S y, sup_e S y, rfl⟩, h⟩
      rw [e]
  | _, _, .eq a x y, ρ, ρ', h => by
      funext w
      show eqT (strR S) a (eval (strR S) x ρ) (eval (strR S) y ρ) =
        eqT (strR S) a (eval (strR S) x ρ') (eval (strR S) y ρ')
      exact propext (eqT_congr S a _ _ _ _ (fund x ρ ρ' h) (fund y ρ ρ' h))
  | _, _, .pos, _, _, _ => fun φ φ' _ _ hφ => by
      have e : φ = φ' := funext fun x => hφ x x (sup_e S x) (sup_e S x) rfl
      show P φ = P φ'
      rw [e]

/-- **Closure under all terms** of the full language, for the extensional carriers. -/
theorem closedR : Closed (strR S) := fun {Γ t} tm ρ hρ =>
  ⟨sup_evalR S tm ρ (envS_of_envA S Γ ρ hρ), fund S tm ρ ρ (relEnv_refl S Γ ρ hρ)⟩

/-- **Leibniz substitution** at every type, for every term motive. -/
theorem leibnizR {Γ : List FTy} {a : FTy} (φ : Tm (a :: Γ) .s) (ρ : Env W D Γ)
    (hρ : EnvA (strR S) Γ ρ) (x y : Den W D a) (hx : AdmR S a x) (hy : AdmR S a y)
    (h : eqT (strR S) a x y) : eval (strR S) φ (x, ρ) = eval (strR S) φ (y, ρ) :=
  fund S φ (x, ρ) (y, ρ) ⟨⟨hx.1, hy.1, eqT_rel S a x y hx hy h⟩, relEnv_refl S Γ ρ hρ⟩

/-- `Leib := ∀f₁ f₂ : σ→σ. ∀F : (σ→σ)→σ. f₁ = f₂ → F f₁ = F f₂` (th's P19 sentence). -/
def leib : Tm ([] : List FTy) .s :=
  .all (.arr .s .s) (.all (.arr .s .s) (.all (.arr (.arr .s .s) .s)
    (.imp (.eq (.arr .s .s) (.var (.succ (.succ .zero))) (.var (.succ .zero)))
      (.eq .s (.app (.var .zero) (.var (.succ (.succ .zero))))
        (.app (.var .zero) (.var (.succ .zero)))))))

theorem leib_true (w : W) : eval (strR S) leib () w := by
  intro f1 h1 f2 h2 F hF heq
  have hrel : rel S (.arr .s .s) f1 f2 := eqT_rel S _ f1 f2 h1 h2 heq
  exact hF.2 f1 f2 h1.1 h2.1 hrel

/-- Generic `LGenF`-style bridge: the extensional carriers agree with the support carriers at
`σ`, `τ`, `τ → σ`, are closed, and satisfy Leibniz. -/
theorem admR_s (q : Den W D .s) : AdmR S .s q ↔ Sup S .s q := ⟨fun h => h.1, fun h => ⟨h, rfl⟩⟩

theorem admR_tp (φ : Den W D tp) : AdmR S tp φ ↔ Sup S tp φ :=
  ⟨fun h => h.1, fun h => ⟨h, fun x y _ _ hxy => by
    have hxy : x = y := hxy
    subst hxy; rfl⟩⟩

theorem admR_th (Φ : Den W D th) : AdmR S th Φ ↔ Sup S th Φ :=
  ⟨fun h => h.1, fun h => ⟨h, fun φ φ' _ _ hφ => by
    have e : φ = φ' := funext fun x => hφ x x (sup_e S x) (sup_e S x) rfl
    show Φ φ = Φ φ'
    rw [e]⟩⟩

theorem lgenFR_of_sym (M : Model W D)
    (S : Sym M.R M.act M.P)
    (hS : ∀ q, Sup S .s q ↔ M.AS q) (hT : ∀ φ, Sup S tp φ ↔ M.AT φ)
    (hH : ∀ Φ, Sup S th Φ ↔ M.AH Φ) :
    ∃ A : (t : FTy) → Den W D t → Prop,
      (∀ x, A .e x) ∧ (∀ q, A .s q ↔ M.AS q) ∧ (∀ φ, A tp φ ↔ M.AT φ) ∧ (∀ Φ, A th Φ ↔ M.AH Φ) ∧
      Closed (strR S) ∧ A = AdmR S :=
  ⟨AdmR S, fun x => ⟨sup_e S x, rfl⟩, fun q => (admR_s S q).trans (hS q),
   fun φ => (admR_tp S φ).trans (hT φ), fun Φ => (admR_th S Φ).trans (hH Φ), closedR S, rfl⟩


/-! ## v4 Example `ex:separating` at all types of the language

`W` = infinite 0-1 sequences, every world sees every world, one always-actual individual,
`Pos` empty, group of flips `x ↦ x ⊕ d`, `G_n` = flips fixing the first `n` coordinates.  The
carriers are `AdmR`: hereditarily finitely supported, and extensional at every type. -/

namespace Sep

abbrev Cw := Nat → Bool

def xw (w d : Cw) : Cw := fun i => xor (w i) (d i)

def Fixes (n : Nat) (d : Cw) : Prop := ∀ i, i < n → d i = false

theorem xw_xw (w d : Cw) : xw (xw w d) d = w :=
  funext fun i => by simp only [xw]; cases w i <;> cases d i <;> rfl

theorem xw_conj (d e w : Cw) : xw (xw (xw w d) e) d = xw w e :=
  funext fun i => by simp only [xw]; cases w i <;> cases d i <;> cases e i <;> rfl

def PE : Den Cw Unit th := fun _ _ => False

def symE : Sym (D := Unit) (fun _ _ : Cw => True) (fun _ _ => True) PE where
  Fx n f g := ∃ d, Fixes n d ∧ f = (fun w => xw w d) ∧ g = (fun w => xw w d)
  mono := by
    rintro n m f g hnm ⟨d, hd, rfl, rfl⟩
    exact ⟨d, fun i hi => hd i (by omega), rfl, rfl⟩
  inv := by rintro n f g ⟨d, hd, rfl, rfl⟩; exact ⟨d, hd, rfl, rfl⟩
  fg := by rintro f g ⟨d, _, rfl, rfl⟩ w; exact xw_xw w d
  hR := fun _ _ _ => Iff.rfl
  hact := fun _ _ _ => Iff.rfl
  hP := by rintro f g ⟨d, _, rfl, rfl⟩; rfl
  conj := by
    rintro f g ⟨d, _, rfl, rfl⟩ n
    refine ⟨n, ?_⟩
    rintro c c' ⟨e, he, rfl, rfl⟩
    exact ⟨e, he, funext fun w => xw_conj d e w, funext fun w => xw_conj d e w⟩

theorem sup_s_of {q : Cw → Prop} {n : Nat}
    (h : ∀ d, Fixes n d → ∀ x, q (xw x d) ↔ q x) : Sup symE .s q :=
  ⟨n, by
    rintro f g ⟨d, hd, rfl, rfl⟩
    funext x
    exact propext (h d hd x)⟩

theorem of_sup_s {q : Cw → Prop} (h : Sup symE .s q) :
    ∃ n, ∀ d, Fixes n d → ∀ x, q (xw x d) ↔ q x := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, fun d hd x => Iff.of_eq (congrFun (hn _ _ ⟨d, hd, rfl, rfl⟩) x)⟩

/-- `D p := ∃ψ. ¬ψ ∧ ((ψ ∧ p) ≠ ⊥)` with `p` the variable of the context `[σ]`. -/
def dTm : Tm [.s] .s :=
  .ex .s (.and (.neg (.var .zero)) (.neg (.eq .s (.and (.var .zero) (.var (.succ .zero))) .bot)))

/-- `Atom p := (p ≠ ⊥) ∧ ¬((p ∧ D p) ≠ ⊥)`. -/
def atomTm : Tm [.s] .s :=
  .and (.neg (.eq .s (.var .zero) .bot)) (.neg (.neg (.eq .s (.and (.var .zero) dTm) .bot)))

/-- `A ∃p. (Atom p ∧ p)`, with `A χ := (χ = ⊤)`. -/
def phiSep : Tm ([] : List FTy) .s := .eq .s (.ex .s (.and atomTm (.var .zero))) .top

def dn (n : Nat) : Cw := fun i => decide (i = n)

theorem phi_false (w : Cw) : ¬ eval (strR symE) phiSep () w := by
  intro h
  have h1 : eval (strR symE) (Tm.ex .s (.and atomTm (.var .zero))) () = eval (strR symE) (Tm.top : Tm ([] : List FTy) .s) () := h
  have h2 := congrFun h1 (fun _ => false)
  have h3 : eval (strR symE) (Tm.ex .s (.and atomTm (.var .zero))) () (fun _ => false) :=
    (Iff.of_eq h2).2 trivial
  obtain ⟨p, hp, ⟨_, a2⟩, hpw⟩ := h3
  have a3 : eval (strR symE) (Tm.and (.var .zero) dTm : Tm [.s] .s) (p, ()) =
      eval (strR symE) (Tm.bot : Tm [.s] .s) (p, ()) :=
    Classical.not_not.1 (show ¬¬ (eval (strR symE) (Tm.and (.var .zero) dTm : Tm [.s] .s) (p, ()) =
      eval (strR symE) (Tm.bot : Tm [.s] .s) (p, ())) from a2)
  obtain ⟨n, hn⟩ := of_sup_s hp.1
  have key : eval (strR symE) dTm (p, ()) (fun _ => false) := by
    refine ⟨fun x => p x ∧ x n = true, ⟨sup_s_of (n := n + 1) ?_, rfl⟩, ?_, ?_⟩
    · intro d hd x
      have hdn : d n = false := hd n (Nat.lt_succ_self n)
      have e : xw x d n = x n := by simp [xw, hdn]
      rw [e]
      exact and_congr_left' (hn d (fun i hi => hd i (by omega)) x)
    · rintro ⟨_, h⟩
      exact absurd h (by simp)
    · intro he
      have hu := Iff.of_eq (congrFun he (xw (fun _ => false) (dn n)))
      have hpu : p (xw (fun _ => false) (dn n)) :=
        (hn (dn n) (fun i hi => by simp [dn]; omega) _).2 hpw
      have hb : xw (fun _ => false) (dn n) n = true := by simp [xw, dn]
      exact hu.1 ⟨⟨hpu, hb⟩, hpu⟩
  exact (Iff.of_eq (congrFun a3 (fun _ => false))).1 ⟨hpw, key⟩

/-- **Example `ex:separating` at all types of `𝓛`.**  The extensional hereditarily finitely
supported hierarchy over the flip group is closed under every term of the full simply typed
language, validates Leibniz `leib` at every world, and refutes `phiSep` at every world. -/
theorem separating_all_types :
    Closed (strR symE) ∧ (∀ w, eval (strR symE) leib () w) ∧ (∀ w, ¬ eval (strR symE) phiSep () w) :=
  ⟨closedR symE, leib_true symE, phi_false⟩

end Sep

namespace V2
open Programme.«20261022-1724-ontological».Run3.SepV2.Sep

def PId : Den Cw Unit th := fun φ w => φ () w

def symId : Sym (D := Unit) (fun w v : Cw => w = v) (fun _ _ => True) PId where
  Fx n f g := ∃ d, Fixes n d ∧ f = (fun w => xw w d) ∧ g = (fun w => xw w d)
  mono := by
    rintro n m f g hnm ⟨d, hd, rfl, rfl⟩
    exact ⟨d, fun i hi => hd i (by omega), rfl, rfl⟩
  inv := by rintro n f g ⟨d, hd, rfl, rfl⟩; exact ⟨d, hd, rfl, rfl⟩
  fg := by rintro f g ⟨d, _, rfl, rfl⟩ w; exact xw_xw w d
  hR := by
    rintro f g ⟨d, _, rfl, rfl⟩ w v
    show xw w d = xw v d ↔ w = v
    exact ⟨fun h => by simpa only [xw_xw] using congrArg (fun u => xw u d) h, fun h => h ▸ rfl⟩
  hact := fun _ _ _ => Iff.rfl
  hP := by
    rintro f g ⟨d, _, rfl, rfl⟩
    funext φ w
    show φ () (xw (xw w d) d) = φ () w
    rw [xw_xw]
  conj := by
    rintro f g ⟨d, _, rfl, rfl⟩ n
    refine ⟨n, ?_⟩
    rintro c c' ⟨e, he, rfl, rfl⟩
    exact ⟨e, he, funext fun w => xw_conj d e w, funext fun w => xw_conj d e w⟩

abbrev SI : Str Cw Unit := strR symId

theorem sup_s_of' {q : Cw → Prop} {n : Nat}
    (h : ∀ d, Fixes n d → ∀ x, q (xw x d) ↔ q x) : Sup symId .s q :=
  ⟨n, by
    rintro f g ⟨d, hd, rfl, rfl⟩
    funext x
    exact propext (h d hd x)⟩

theorem of_sup_s' {q : Cw → Prop} (h : Sup symId .s q) :
    ∃ n, ∀ d, Fixes n d → ∀ x, q (xw x d) ↔ q x := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, fun d hd x => Iff.of_eq (congrFun (hn _ _ ⟨d, hd, rfl, rfl⟩) x)⟩

/-- r1's `phi_false`, verbatim up to `symE ↦ symId` (the frame and `P` play no role). -/
theorem sep_fails (w : Cw) : ¬ eval SI phiSep () w := by
  intro h
  have h1 : eval SI (Tm.ex .s (.and atomTm (.var .zero))) () = eval SI (Tm.top : Tm ([] : List FTy) .s) () := h
  have h2 := congrFun h1 (fun _ => false)
  have h3 : eval SI (Tm.ex .s (.and atomTm (.var .zero))) () (fun _ => false) :=
    (Iff.of_eq h2).2 trivial
  obtain ⟨p, hp, ⟨_, a2⟩, hpw⟩ := h3
  have a3 : eval SI (Tm.and (.var .zero) dTm : Tm [.s] .s) (p, ()) =
      eval SI (Tm.bot : Tm [.s] .s) (p, ()) :=
    Classical.not_not.1 (show ¬¬ (eval SI (Tm.and (.var .zero) dTm : Tm [.s] .s) (p, ()) =
      eval SI (Tm.bot : Tm [.s] .s) (p, ())) from a2)
  obtain ⟨n, hn⟩ := of_sup_s' hp.1
  have key : eval SI dTm (p, ()) (fun _ => false) := by
    refine ⟨fun x => p x ∧ x n = true, ⟨sup_s_of' (n := n + 1) ?_, rfl⟩, ?_, ?_⟩
    · intro d hd x
      have hdn : d n = false := hd n (Nat.lt_succ_self n)
      have e : xw x d n = x n := by simp [xw, hdn]
      rw [e]
      exact and_congr_left' (hn d (fun i hi => hd i (by omega)) x)
    · rintro ⟨_, h⟩
      exact absurd h (by simp)
    · intro he
      have hu := Iff.of_eq (congrFun he (xw (fun _ => false) (dn n)))
      have hpu : p (xw (fun _ => false) (dn n)) :=
        (hn (dn n) (fun i hi => by simp [dn]; omega) _).2 hpw
      have hb : xw (fun _ => false) (dn n) n = true := by simp [xw, dn]
      exact hu.1 ⟨⟨hpu, hb⟩, hpu⟩
  exact (Iff.of_eq (congrFun a3 (fun _ => false))).1 ⟨hpw, key⟩

/-! ### Variant 2 as closed 𝓛-sentences (the encodings of `DeepK.lean`, parameters inlined) -/

abbrev x0 : Tm (t :: Γ) t := .var .zero
abbrev x1 : Tm (u :: t :: Γ) t := .var (.succ .zero)
abbrev x2 : Tm (u :: u' :: t :: Γ) t := .var (.succ (.succ .zero))
abbrev x3 : Tm (u :: u' :: u'' :: t :: Γ) t := .var (.succ (.succ (.succ .zero)))
abbrev Pos (φ : Tm Γ tp) : Tm Γ .s := .app .pos φ
abbrev iff (x y : Tm Γ .s) : Tm Γ .s := .and (.imp x y) (.imp y x)

/-- `Ax2a := ∀φ. (Pφ ∨ P(¬φ)) ∧ ¬(Pφ ∧ P(¬φ))`, `¬φ := λx. ¬ φ x`. -/
def ax2a : Tm [] .s :=
  .all tp (.and (.or (Pos x0) (Pos (.lam (.neg (.app x1 x0)))))
    (.neg (.and (Pos x0) (Pos (.lam (.neg (.app x1 x0)))))))
/-- `Ax2b := ∀φ. Pφ → □Pφ`. -/
def ax2b : Tm [] .s := .all tp (.imp (Pos x0) (.box (Pos x0)))
/-- `Ax4 := ∀φψ. Pφ → □∀ᴱx.(φx → ψx) → Pψ`. -/
def ax4 : Tm [] .s :=
  .all tp (.all tp (.imp (Pos x1) (.imp (.box (.allE (.imp (.app x2 x0) (.app x1 x0)))) (Pos x0))))
/-- Variant-2 essence of `φ` (var 1) at `x` (var 0), inside `λx.∀φ`:
`φ x ∧ ∀ψ. ψ x → □∀ᴱy. φ y → ψ y`. -/
def essT : Tm (tp :: .e :: Γ) .s :=
  .and (.app x0 x1) (.all tp (.imp (.app x0 x2) (.box (.allE (.imp (.app x2 x0) (.app x1 x0))))))
/-- `E := λx. ∀φ. Ess φ x → □∃ᴱy. φ y`; `Ax3 := P E`. -/
def eT : Tm Γ tp := .lam (.all tp (.imp essT (.box (.exE (.app x1 x0)))))
def ax3 : Tm [] .s := Pos eT
/-- Unrestricted `Ax1Gen := ∀Φ φ. (∀ψ. Φψ → Pψ) → □∀ᴱx.(φx ↔ ∀ψ. Φψ → ψx) → Pφ`. -/
def ax1Gen : Tm [] .s :=
  .all th (.all tp (.imp (.all tp (.imp (.app x2 x0) (Pos x0)))
    (.imp (.box (.allE (iff (.app x1 x0) (.all tp (.imp (.app x3 x0) (.app x0 x1))))))
      (Pos x0))))
/-- `MC := ∀p. p → □p`. -/
def mc : Tm [] .s := .all .s (.imp x0 (.box x0))
/-- `∃ᴱx. G x`, `G := λx. ∀φ. Pφ → φx`. -/
def exG : Tm [] .s := .exE (.all tp (.imp (Pos x0) (.app x0 x1)))

/-- The variant-2 theory. -/
def T2 : Tm [] .s → Prop := fun φ => φ = ax1Gen ∨ φ = ax2a ∨ φ = ax2b ∨ φ = ax3 ∨ φ = ax4

theorem v2_holds (w : Cw) :
    eval SI ax1Gen () w ∧ eval SI ax2a () w ∧ eval SI ax2b () w ∧ eval SI ax3 () w ∧
      eval SI ax4 () w ∧ eval SI mc () w ∧ eval SI exG () w := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Φ _ φ _ hpos hc
    exact (hc w rfl () trivial).2 fun ψ hA hψ => hpos ψ hA hψ
  · intro φ _
    exact ⟨Classical.em (φ () w), fun ⟨h1, h2⟩ => h2 h1⟩
  · intro φ _ h v hv
    exact hv ▸ h
  · intro φ _ hess v hv
    exact ⟨(), trivial, hv ▸ hess.1⟩
  · intro φ _ ψ _ h hinc
    exact hinc w rfl () trivial h
  · intro p _ h v hv
    exact hv ▸ h
  · exact ⟨(), trivial, fun φ _ h => h⟩

theorem v2_T (φ : Tm [] .s) (h : T2 φ) (w : Cw) : eval SI φ () w := by
  have := v2_holds w
  rcases h with rfl | rfl | rfl | rfl | rfl
  · exact this.1
  · exact this.2.1
  · exact this.2.2.1
  · exact this.2.2.2.1
  · exact this.2.2.2.2.1

theorem allE_S (x : Unit) : SI.A .e x := ⟨sup_e symId x, rfl⟩

/-- The structure lies in K4's soundness class: closed, all entities admitted, `eqT`-respecting. -/
theorem resp_symId : Closed SI ∧ (∀ x, SI.A .e x) ∧ HOLX.Resp SI := by
  refine ⟨closedR symId, allE_S, ?_⟩
  intro a b F hF z z' hz hz' he
  have hr : rel symId b (F z) (F z') := hF.2 z z' hz.1 hz'.1 (eqT_rel symId a z z' hz hz' he)
  have hA : ∀ y, AdmR symId a y → AdmR symId b (F y) := fun y hy =>
    closedR symId (Tm.app (.var .zero) (.var (.succ .zero)) : Tm [.arr a b, a] b) (F, y, ())
      ⟨hF, hy, trivial⟩
  exact rel_eqT symId b _ _ (hA z hz) (hA z' hz') hr

/-- **(d), semantic half.**  An extensional (Leibniz-respecting) model, closed under every term,
of variant 2 (unrestricted `Ax1Gen`, `Ax2a`, `Ax2b`, `Ax3`, `Ax4`; also `MC`, `∃ᴱG`, S5 frame)
in which v4's separating sentence `A ∃p.(Atom p ∧ p)` fails at every world. -/
theorem sep_v2 :
    Closed SI ∧ (∀ x, SI.A .e x) ∧ HOLX.Resp SI ∧ (∀ w, eval SI leib () w) ∧
      (∀ φ, T2 φ → ∀ w, eval SI φ () w) ∧ (∀ w, eval SI mc () w ∧ eval SI exG () w) ∧
      (∀ w, ¬ eval SI phiSep () w) :=
  ⟨resp_symId.1, resp_symId.2.1, resp_symId.2.2, leib_true symId, v2_T,
    fun w => ⟨(v2_holds w).2.2.2.2.2.1, (v2_holds w).2.2.2.2.2.2⟩, sep_fails⟩

/-- **(d), deep half.**  No derivation in K4's certified calculus (∀E/∃I instances `𝓛`-terms,
Leibniz with `𝓛`-motives at every type) derives v4's separating sentence from variant 2. -/
theorem sep_not_derivable :
    ¬ Nonempty (HOLX.Deriv T2 (fun a t => HOLX.Cert a t) [.w] []
      (.holds (HOLX.emb HOLX.nilR phiSep) HOLX.var0)) := fun ⟨d⟩ =>
  sep_fails (fun _ => false)
    (HOLX.valid_of_deriv SI allE_S (closedR symId) resp_symId.2.2 v2_T d _)

end V2
end Programme.«20261022-1724-ontological».Run3.SepV2


/-! ## (d) in v4's class: the quotient of `SI` is a v4 𝓛-general model of variant 2 -/

namespace Programme.«20261022-1724-ontological».Run3.SepV2.V2
open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.SepV2.Sep

/-- **(d), in v4's def:lgeneral class.**  There is a v4 `𝓛`-general model (carriers with
functions on carriers, closed under every term of `𝓛`; here the `eqT`-quotient of `SI`) with a
nonempty domain of individuals, in which variant 2's unrestricted `Ax1Gen`, `Ax2a`, `Ax2b`, `Ax3`,
`Ax4`, and `MC`, `∃ᴱG` hold at every world while `A ∃p.(Atom p ∧ p)` fails at every world. -/
theorem sep_v4 : ∃ (M : VM Cw) (L : LGen M), Nonempty (M.C .e) ∧
    (∀ φ, T2 φ → ∀ w, M.pr (L.ev φ ()) w) ∧
    (∀ w, M.pr (L.ev mc ()) w ∧ M.pr (L.ev exG ()) w) ∧ (∀ w, ¬ M.pr (L.ev phiSep ()) w) :=
  ⟨ofStr SI (closedR symId) resp_symId.2.2, ofStr_lgen SI (closedR symId) resp_symId.2.2 allE_S,
    ⟨Quotient.mk (setoidT SI .e) ⟨(), allE_S ()⟩⟩, v2_T,
    fun w => ⟨(v2_holds w).2.2.2.2.2.1, (v2_holds w).2.2.2.2.2.2⟩, sep_fails⟩

/-- Hence the separating sentence is not valid over v4's 𝓛-general models of variant 2. -/
theorem sep_not_valid_v4 : ¬ ValidV4 T2 phiSep := fun H =>
  sep_fails (fun _ => false)
    (H Cw _ (ofStr_lgen SI (closedR symId) resp_symId.2.2 allE_S)
      ⟨Quotient.mk (setoidT SI .e) ⟨(), allE_S ()⟩⟩ v2_T (fun _ => false))

end Programme.«20261022-1724-ontological».Run3.SepV2.V2



/-! ## v4 Example `ex:separating`: the two remarks, and the example as a v4 𝓛-general model

* `sep_example_v4`: the eqT-quotient of K6's structure (`strR symE`: total frame, one individual,
  `Pos` empty, extensional hereditarily finitely supported carriers over the flip group) is a v4
  `VM`+`LGen` model with universal `R` and empty `Pos`, a contingent proposition `{w | w₀ = 1}`, in
  which `A ∃p.(Atom p ∧ p)` fails at every world.
* `sep_of_minimal` / `sep_finite` / `sep_singletons`: in every v4 𝓛-general model in which every
  world `v` has a least proposition containing it (in particular, every model with finitely many
  worlds, and every model whose propositional domain contains the singletons, e.g. a standard
  one), `A ∃p.(Atom p ∧ p)` holds at every world: "no model with finitely many worlds separates".
* `v2_universal_trivial` / `sep_example_not_v2`: in a v4 𝓛-general model of variant 2 (K1's `T2`)
  on a universal frame every proposition is `∅` or `W`; hence no v4 𝓛-general model with a universal
  frame whose propositional domain contains `{w | w₀ = 1}` (v4's `M`, with *any* `Pos`) is a model of
  variant 2: "M is not a model of the axioms of variant 2, whatever Pos is taken to be". -/

namespace Programme.«20261022-1724-ontological».Run3.SepR
open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.SepV2 Programme.«20261022-1724-ontological».Run3.SepV2.Sep

attribute [local instance] Classical.propDecidable

section Sem
variable {W : Type} (M : VM W) (L : LGen M)

theorem ev_v0 {t : FTy} {Γ : List FTy} (x : M.C t) (ρ : VEnv M Γ) :
    L.ev (Tm.var .zero : Tm (t :: Γ) t) (x, ρ) = x := L.var _ _

theorem ev_v1 {t u : FTy} {Γ : List FTy} (y : M.C u) (x : M.C t) (ρ : VEnv M Γ) :
    L.ev (Tm.var (.succ .zero) : Tm (u :: t :: Γ) t) (y, x, ρ) = x := L.var _ _

/-- A proposition equals the bottom proposition iff it is false everywhere. -/
theorem eq_bot_iff {Γ : List FTy} (ρ : VEnv M Γ) (p : M.C .s) :
    p = L.ev (Tm.bot : Tm Γ .s) ρ ↔ ∀ u, ¬ M.pr p u := by
  constructor
  · rintro rfl u h; exact (L.bot ρ u).1 h
  · intro h
    exact M.pr_inj _ _ (funext fun u => propext ⟨fun hu => absurd hu (h u),
      fun hu => absurd hu ((L.bot ρ u).1)⟩)

/-- Semantics of `D p`: some proposition of the domain omits `u` and meets `p`. -/
theorem dTm_iff (x : M.C .s) (u : W) :
    M.pr (L.ev dTm (x, ())) u ↔ ∃ ψ : M.C .s, ¬ M.pr ψ u ∧ ∃ u', M.pr ψ u' ∧ M.pr x u' := by
  unfold dTm
  rw [L.ex]
  refine exists_congr fun ψ => ?_
  rw [L.and, L.neg, L.neg, L.eq, ev_v0, eq_bot_iff]
  simp only [L.and, L.var, Classical.not_forall, Classical.not_not]
  exact Iff.rfl

/-- Semantics of `Atom p` at `v`. -/
theorem atom_iff (x : M.C .s) (v : W) :
    M.pr (L.ev atomTm (x, ())) v ↔
      (∃ u, M.pr x u) ∧ ∀ u, ¬ (M.pr x u ∧ M.pr (L.ev dTm (x, ())) u) := by
  unfold atomTm
  rw [L.and, L.neg, L.neg, L.neg, L.eq, L.eq, ev_v0, eq_bot_iff, eq_bot_iff, Classical.not_not]
  simp only [L.and, L.var, Classical.not_forall, Classical.not_not]
  exact Iff.rfl

/-- Semantics of `A ∃p.(Atom p ∧ p)`: at any world, every world lies in an atom. -/
theorem phiSep_iff (w : W) :
    M.pr (L.ev phiSep ()) w ↔ ∀ v, ∃ x : M.C .s, M.pr (L.ev atomTm (x, ())) v ∧ M.pr x v := by
  unfold phiSep
  rw [L.eq]
  constructor
  · intro h v
    have hv : M.pr (L.ev (Tm.ex .s (.and atomTm (.var .zero))) ()) v := by
      rw [h]; exact (L.top (Γ := []) () v).2 trivial
    obtain ⟨x, hx⟩ := (L.ex _ _ _ _).1 hv
    rw [L.and, ev_v0] at hx
    exact ⟨x, hx⟩
  · intro h
    apply M.pr_inj
    funext v
    apply propext
    refine ⟨fun _ => (L.top (Γ := []) () v).2 trivial, fun _ => ?_⟩
    obtain ⟨x, hx⟩ := h v
    exact (L.ex _ _ _ _).2 ⟨x, by rw [L.and, ev_v0]; exact hx⟩

/-- **Sufficient condition for the separating sentence.** If every world `v` has a least proposition
of the domain containing it, then `A ∃p.(Atom p ∧ p)` holds at every world. -/
theorem sep_of_minimal
    (hmin : ∀ v, ∃ q : M.C .s, M.pr q v ∧ ∀ u, M.pr q u → ∀ p : M.C .s, M.pr p v → M.pr p u)
    (w : W) : M.pr (L.ev phiSep ()) w := by
  rw [phiSep_iff]
  intro v
  obtain ⟨q, hqv, hq⟩ := hmin v
  refine ⟨q, (atom_iff M L q v).2 ⟨⟨v, hqv⟩, ?_⟩, hqv⟩
  rintro u ⟨hqu, hd⟩
  obtain ⟨ψ, hψu, u', hψu', hqu'⟩ := (dTm_iff M L q u).1 hd
  by_cases hψv : M.pr ψ v
  · exact hψu (hq u hqu ψ hψv)
  · -- `¬ψ` is in the domain and contains `v`, hence `u'`
    have hn : M.pr (L.ev (Tm.neg (.var .zero) : Tm [.s] .s) (ψ, ())) v := by
      rw [L.neg, ev_v0]; exact hψv
    have hn' := hq u' hqu' _ hn
    rw [L.neg, ev_v0] at hn'
    exact hn' hψu'

/-- Conjunction in the propositional domain. -/
def conj (p q : M.C .s) : M.C .s :=
  L.ev (Tm.and (.var .zero) (.var (.succ .zero)) : Tm [.s, .s] .s) (p, q, ())

theorem pr_conj (p q : M.C .s) (u : W) : M.pr (conj M L p q) u ↔ M.pr p u ∧ M.pr q u := by
  unfold conj; rw [L.and, ev_v0, ev_v1]

/-- For a list of worlds, a proposition containing `v` and contained in every proposition of the
domain that contains `v` and omits a listed world. -/
noncomputable def cut (v : W) : List W → M.C .s
  | [] => L.ev (Tm.top : Tm [] .s) ()
  | u :: l =>
    conj M L (cut v l)
      (if h : ∃ p : M.C .s, M.pr p v ∧ ¬ M.pr p u then Classical.choose h
        else L.ev (Tm.top : Tm [] .s) ())

theorem cut_v (v : W) : ∀ l, M.pr (cut M L v l) v
  | [] => (L.top (Γ := []) () v).2 trivial
  | u :: l => by
    unfold cut
    rw [pr_conj]
    refine ⟨cut_v v l, ?_⟩
    split
    · next h => exact (Classical.choose_spec h).1
    · exact (L.top (Γ := []) () v).2 trivial

theorem cut_min (v : W) : ∀ l u, u ∈ l → M.pr (cut M L v l) u → ∀ p : M.C .s, M.pr p v → M.pr p u
  | [], _, hu, _, _, _ => nomatch hu
  | u' :: l, u, hu, hc, p, hp => by
    unfold cut at hc
    rw [pr_conj] at hc
    rcases List.mem_cons.1 hu with heq | hl
    · apply Classical.byContradiction
      intro hpu
      rw [heq] at hpu
      have h : ∃ p : M.C .s, M.pr p v ∧ ¬ M.pr p u' := ⟨p, hp, hpu⟩
      have hc2 := hc.2
      rw [dif_pos h] at hc2
      exact (Classical.choose_spec h).2 (heq ▸ hc2)
    · exact cut_min v l u hl hc.1 p hp

/-- **"No model with finitely many worlds separates"** (v4, remark in `ex:separating`). In every v4
𝓛-general model whose worlds are enumerated by a finite list, `A ∃p.(Atom p ∧ p)` holds at every
world. -/
theorem sep_finite (hfin : ∃ l : List W, ∀ w, w ∈ l) (w : W) : M.pr (L.ev phiSep ()) w := by
  obtain ⟨l, hl⟩ := hfin
  exact sep_of_minimal M L (fun v => ⟨cut M L v l, cut_v M L v l,
    fun u hu p hp => cut_min M L v l u (hl u) hu p hp⟩) w

/-- In every v4 𝓛-general model whose propositional domain contains every singleton (e.g. a
standard model), `A ∃p.(Atom p ∧ p)` holds at every world. -/
theorem sep_singletons (hs : ∀ v, ∃ q : M.C .s, ∀ u, M.pr q u ↔ u = v) (w : W) :
    M.pr (L.ev phiSep ()) w :=
  sep_of_minimal M L (fun v => by
    obtain ⟨q, hq⟩ := hs v
    exact ⟨q, (hq v).2 rfl, fun u hu p hp => by rw [(hq u).1 hu]; exact hp⟩) w

/-- **Variant 2 on a universal frame trivialises the propositional domain.** In every v4
𝓛-general model of K1's `T2` (variant 2: `Ax2a`, `Ax2b`, `Ax3`, `Ax4`, `Ax1GenTwo`, `∃x.⊤`) whose
accessibility is universal, every proposition of the domain is true everywhere or nowhere. -/
theorem v2_universal_trivial (hT : ∀ ψ, K1.T2 ψ → ∀ w, M.pr (L.ev ψ ()) w)
    (hU : ∀ w v, M.R w v) (p : M.C .s) : (∀ w, M.pr p w) ∨ (∀ w, ¬ M.pr p w) := by
  by_cases h : ∃ w, M.pr p w
  · obtain ⟨w, hw⟩ := h
    left
    intro v
    have hmc := (V4.k1_valid_v4 M L hT w).2.1
    unfold K1.MC at hmc
    rw [L.all] at hmc
    have := hmc p
    rw [L.imp, L.box, ev_v0] at this
    exact this hw v (hU w v)
  · exact Or.inr fun w hw => h ⟨w, hw⟩

/-- Hence a v4 𝓛-general model on infinite 0-1 sequences with universal accessibility whose
propositional domain contains `{w | w₀ = 1}` (as v4's `M` does, whatever `Pos` is) is not a model of
variant 2. -/
theorem not_v2_of_contingent {M : VM Cw} (L : LGen M) (hU : ∀ w v, M.R w v)
    (h0 : ∃ p : M.C .s, ∀ w, M.pr p w ↔ w 0 = true) :
    ¬ ∀ ψ, K1.T2 ψ → ∀ w, M.pr (L.ev ψ ()) w := by
  intro hT
  obtain ⟨p, hp⟩ := h0
  rcases v2_universal_trivial M L hT hU p with h | h
  · have := (hp (fun _ => false)).1 (h _); exact absurd this (by decide)
  · exact h (fun _ => true) ((hp _).2 rfl)

end Sem

/-! ### v4's model `M` of `ex:separating` as a v4 𝓛-general model -/

abbrev SE := strR symE

theorem allE_E (x : Unit) : SE.A .e x := ⟨sup_e symE x, rfl⟩

theorem resp_E : HOLX.Resp SE := by
  intro a b F hF z z' hz hz' he
  have hr : rel symE b (F z) (F z') := hF.2 z z' hz.1 hz'.1 (eqT_rel symE a z z' hz hz' he)
  have hA : ∀ y, AdmR symE a y → AdmR symE b (F y) := fun y hy =>
    closedR symE (Tm.app (.var .zero) (.var (.succ .zero)) : Tm [.arr a b, a] b) (F, y, ())
      ⟨hF, hy, trivial⟩
  exact rel_eqT symE b _ _ (hA z hz) (hA z' hz') hr

/-- The finitary proposition `{w | w₀ = 1}` is admitted. -/
theorem adm_x0 : SE.A .s (fun w => w 0 = true) :=
  (admR_s symE _).2 (sup_s_of (n := 1) fun d hd x => by
    have : d 0 = false := hd 0 (by decide)
    simp [xw, this])

/-- **Example `ex:separating` in v4's own model class.** The quotient of K6's structure is a v4
`VM` with an `LGen` (closed under every term of the full simply typed `𝓛`), one individual, universal
accessibility, `Pos` empty, and the contingent proposition `{w | w₀ = 1}`; `A ∃p.(Atom p ∧ p)`
fails at every world, and the model is not a model of variant 2. -/
theorem sep_example_v4 : ∃ (M : VM Cw) (L : LGen M), Nonempty (M.C .e) ∧ (∀ w v, M.R w v) ∧
    (∀ φ w, ¬ M.pr (M.ap M.P φ) w) ∧ (∃ p : M.C .s, ∀ w, M.pr p w ↔ w 0 = true) ∧
    (∀ w, ¬ M.pr (L.ev phiSep ()) w) ∧ ¬ (∀ ψ, K1.T2 ψ → ∀ w, M.pr (L.ev ψ ()) w) := by
  let M := ofStr SE (closedR symE) resp_E
  let L := ofStr_lgen SE (closedR symE) resp_E allE_E
  have hU : ∀ w v, M.R w v := fun _ _ => trivial
  have h0 : ∃ p : M.C .s, ∀ w, M.pr p w ↔ w 0 = true :=
    ⟨Quotient.mk (setoidT SE .s) ⟨_, adm_x0⟩, fun _ => Iff.rfl⟩
  refine ⟨M, L, ⟨Quotient.mk (setoidT SE .e) ⟨(), allE_E ()⟩⟩, hU, ?_, h0, ?_,
    not_v2_of_contingent L hU h0⟩
  · intro φ w
    refine Quotient.inductionOn (motive := fun φ => ¬ M.pr (M.ap M.P φ) w) φ ?_
    intro z h
    exact h
  · intro w h
    exact phi_false w ((ofStr_truth SE (closedR symE) resp_E allE_E phiSep w).1 h)

end Programme.«20261022-1724-ontological».Run3.SepR



namespace Programme.«20261022-1724-ontological».ThHenkin
open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.HOLX
def pair (a b : Nat) : Nat := 2 ^ a * (2 * b + 1)

theorem pow_succ' (c : Nat) (x : Nat) : 2 ^ (c + 1) * x = 2 * (2 ^ c * x) := by
  rw [Nat.pow_succ, Nat.mul_comm (2 ^ c) 2, Nat.mul_assoc]

theorem pair_inj : ∀ {a b c d : Nat}, pair a b = pair c d → a = c ∧ b = d
  | 0, b, 0, d, h => by simp [pair] at h; omega
  | 0, b, c + 1, d, h => by
      simp only [pair, pow_succ'] at h; generalize 2 ^ c * (2 * d + 1) = X at h; simp at h; omega
  | a + 1, b, 0, d, h => by
      simp only [pair, pow_succ'] at h; generalize 2 ^ a * (2 * b + 1) = X at h; simp at h; omega
  | a + 1, b, c + 1, d, h => by
      simp only [pair, pow_succ'] at h
      have h' : pair a b = pair c d := by unfold pair; omega
      have := pair_inj h'; omega

theorem pair_iff {a b c d : Nat} : pair a b = pair c d ↔ a = c ∧ b = d :=
  ⟨pair_inj, fun ⟨h1, h2⟩ => h1 ▸ h2 ▸ rfl⟩

theorem lt_pair (a b : Nat) : b < pair a b := by
  have : 1 ≤ 2 ^ a := Nat.one_le_two_pow
  unfold pair
  have : 1 * (2 * b + 1) ≤ 2 ^ a * (2 * b + 1) := Nat.mul_le_mul_right _ this
  omega

def codeF : FTy → Nat
  | .e => pair 0 0
  | .s => pair 1 0
  | .arr a b => pair 2 (pair (codeF a) (codeF b))

theorem codeF_inj : ∀ {a b : FTy}, codeF a = codeF b → a = b
  | .e, b, h => by cases b <;> simp_all [codeF, pair_iff]
  | .s, b, h => by cases b <;> simp_all [codeF, pair_iff]
  | .arr a b, c, h => by
      cases c with
      | arr c d =>
          simp only [codeF, pair_iff] at h
          rw [codeF_inj h.2.1, codeF_inj h.2.2]
      | _ => simp_all [codeF, pair_iff]

def codeH : HTy → Nat
  | .L t => pair 0 (codeF t)
  | .w => pair 1 0
  | .o => pair 2 0

theorem codeH_inj : ∀ {a b : HTy}, codeH a = codeH b → a = b
  | .L t, b, h => by
      cases b with
      | L u => simp only [codeH, pair_iff] at h; rw [codeF_inj h.2]
      | _ => simp_all [codeH, pair_iff]
  | .w, b, h => by cases b <;> simp_all [codeH, pair_iff]
  | .o, b, h => by cases b <;> simp_all [codeH, pair_iff]

def codeV : {Γ : List HTy} → {a : HTy} → HVar Γ a → Nat
  | _, _, .zero => 0
  | _, _, .succ v => codeV v + 1

theorem codeV_inj : ∀ {Γ a} (v v' : HVar Γ a), codeV v = codeV v' → v = v'
  | _, _, .zero, .zero, _ => rfl
  | _, _, .zero, .succ _, h => by simp [codeV] at h
  | _, _, .succ _, .zero, h => by simp [codeV] at h
  | _, _, .succ v, .succ v', h => by
      simp only [codeV, Nat.add_right_cancel_iff] at h; rw [codeV_inj v v' h]

def codeT : {Γ : List HTy} → {a : HTy} → HTerm Γ a → Nat
  | _, _, .var v => pair 0 (codeV v)
  | _, _, @HTerm.appL _ a _ f x => pair 1 (pair (codeF a) (pair (codeT f) (codeT x)))
  | _, _, .lamL b => pair 2 (codeT b)
  | _, _, .pos => pair 3 0
  | _, _, .wabs φ => pair 4 (codeT φ)
  | _, _, .holds p i => pair 5 (pair (codeT p) (codeT i))
  | _, _, .rel i j => pair 6 (pair (codeT i) (codeT j))
  | _, _, .act x i => pair 7 (pair (codeT x) (codeT i))
  | _, _, .bot => pair 8 0
  | _, _, .imp p q => pair 9 (pair (codeT p) (codeT q))
  | _, _, .and p q => pair 10 (pair (codeT p) (codeT q))
  | _, _, .or p q => pair 11 (pair (codeT p) (codeT q))
  | _, _, .all a p => pair 12 (pair (codeH a) (codeT p))
  | _, _, .ex a p => pair 13 (pair (codeH a) (codeT p))
  | _, _, .eq a s t => pair 14 (pair (codeH a) (pair (codeT s) (codeT t)))

theorem codeT_inj : ∀ {Γ a} (t t' : HTerm Γ a), codeT t = codeT t' → t = t'
  | _, _, .var v, t', h => by
      cases t' <;> simp only [codeT, pair_iff] at h <;> first | omega | rw [codeV_inj _ _ h.2]
  | _, _, @HTerm.appL _ a _ f x, t', h => by
      cases t' with
      | @appL _ a' _ f' x' =>
          simp only [codeT, pair_iff] at h
          obtain ⟨_, ha, hf, hx⟩ := h
          cases codeF_inj ha
          rw [codeT_inj f f' hf, codeT_inj x x' hx]
      | _ => simp only [codeT, pair_iff] at h; omega
  | _, _, .lamL b, t', h => by
      cases t' with
      | lamL b' => simp only [codeT, pair_iff] at h; rw [codeT_inj b b' h.2]
      | _ => simp only [codeT, pair_iff] at h; omega
  | _, _, .pos, t', h => by cases t' <;> simp only [codeT, pair_iff] at h <;> first | omega | rfl
  | _, _, .wabs φ, t', h => by
      cases t' with
      | wabs φ' => simp only [codeT, pair_iff] at h; rw [codeT_inj φ φ' h.2]
      | _ => simp only [codeT, pair_iff] at h; omega
  | _, _, .holds p i, t', h => by
      cases t' with
      | holds p' i' =>
          simp only [codeT, pair_iff] at h; rw [codeT_inj p p' h.2.1, codeT_inj i i' h.2.2]
      | _ => simp only [codeT, pair_iff] at h; omega
  | _, _, .rel p i, t', h => by
      cases t' with
      | rel p' i' =>
          simp only [codeT, pair_iff] at h; rw [codeT_inj p p' h.2.1, codeT_inj i i' h.2.2]
      | _ => simp only [codeT, pair_iff] at h; omega
  | _, _, .act p i, t', h => by
      cases t' with
      | act p' i' =>
          simp only [codeT, pair_iff] at h; rw [codeT_inj p p' h.2.1, codeT_inj i i' h.2.2]
      | _ => simp only [codeT, pair_iff] at h; omega
  | _, _, .bot, t', h => by cases t' <;> simp only [codeT, pair_iff] at h <;> first | omega | rfl
  | _, _, .imp p i, t', h => by
      cases t' with
      | imp p' i' =>
          simp only [codeT, pair_iff] at h; rw [codeT_inj p p' h.2.1, codeT_inj i i' h.2.2]
      | _ => simp only [codeT, pair_iff] at h; omega
  | _, _, .and p i, t', h => by
      cases t' with
      | and p' i' =>
          simp only [codeT, pair_iff] at h; rw [codeT_inj p p' h.2.1, codeT_inj i i' h.2.2]
      | _ => simp only [codeT, pair_iff] at h; omega
  | _, _, .or p i, t', h => by
      cases t' with
      | or p' i' =>
          simp only [codeT, pair_iff] at h; rw [codeT_inj p p' h.2.1, codeT_inj i i' h.2.2]
      | _ => simp only [codeT, pair_iff] at h; omega
  | _, _, .all a p, t', h => by
      cases t' with
      | all a' p' =>
          simp only [codeT, pair_iff] at h
          obtain ⟨_, ha, hp⟩ := h
          cases codeH_inj ha
          rw [codeT_inj p p' hp]
      | _ => simp only [codeT, pair_iff] at h; omega
  | _, _, .ex a p, t', h => by
      cases t' with
      | ex a' p' =>
          simp only [codeT, pair_iff] at h
          obtain ⟨_, ha, hp⟩ := h
          cases codeH_inj ha
          rw [codeT_inj p p' hp]
      | _ => simp only [codeT, pair_iff] at h; omega
  | _, _, .eq a s t, t', h => by
      cases t' with
      | eq a' s' t'' =>
          simp only [codeT, pair_iff] at h
          obtain ⟨_, ha, hs, ht⟩ := h
          cases codeH_inj ha
          rw [codeT_inj s s' hs, codeT_inj t t'' ht]
      | _ => simp only [codeT, pair_iff] at h; omega


/-! ## A locally nameless code: bound variables by index, free variables by level.
It is invariant under weakening of the context, so the Lindenbaum enumeration at stage `k` can
work over the current context only. -/

theorem codeV_lt : ∀ {Γ a} (v : HVar Γ a), codeV v < Γ.length
  | _, _, .zero => by simp [codeV]
  | _, _, .succ v => by have := codeV_lt v; simp [codeV]; omega

def vcode (d : Nat) (v : HVar Γ a) : Nat :=
  if codeV v < d then pair 0 (codeV v) else pair 1 (Γ.length - 1 - codeV v)

theorem vcode_inj (d : Nat) (v v' : HVar Γ a) (h : vcode d v = vcode d v') : v = v' := by
  have l := codeV_lt v; have l' := codeV_lt v'
  apply codeV_inj
  unfold vcode at h
  split at h <;> split at h <;> simp only [pair_iff] at h <;> omega

def codeL : {Γ : List HTy} → {a : HTy} → Nat → HTerm Γ a → Nat
  | _, _, d, .var v => pair 0 (vcode d v)
  | _, _, d, @HTerm.appL _ a _ f x => pair 1 (pair (codeF a) (pair (codeL d f) (codeL d x)))
  | _, _, d, .lamL b => pair 2 (codeL (d + 1) b)
  | _, _, d, .pos => pair 3 0
  | _, _, d, .wabs φ => pair 4 (codeL (d + 1) φ)
  | _, _, d, .holds p i => pair 5 (pair (codeL d p) (codeL d i))
  | _, _, d, .rel i j => pair 6 (pair (codeL d i) (codeL d j))
  | _, _, d, .act x i => pair 7 (pair (codeL d x) (codeL d i))
  | _, _, d, .bot => pair 8 0
  | _, _, d, .imp p q => pair 9 (pair (codeL d p) (codeL d q))
  | _, _, d, .and p q => pair 10 (pair (codeL d p) (codeL d q))
  | _, _, d, .or p q => pair 11 (pair (codeL d p) (codeL d q))
  | _, _, d, .all a p => pair 12 (pair (codeH a) (codeL (d + 1) p))
  | _, _, d, .ex a p => pair 13 (pair (codeH a) (codeL (d + 1) p))
  | _, _, d, .eq a s t => pair 14 (pair (codeH a) (pair (codeL d s) (codeL d t)))

theorem codeL_inj : ∀ {Γ a} (d : Nat) (t t' : HTerm Γ a), codeL d t = codeL d t' → t = t'
  | _, _, d, .var v, t', h => by
      cases t' with
      | var v' => simp only [codeL, pair_iff] at h; rw [vcode_inj d v v' h.2]
      | _ => simp only [codeL, pair_iff] at h; omega
  | _, _, d, @HTerm.appL _ a _ f x, t', h => by
      cases t' with
      | @appL _ a' _ f' x' =>
          simp only [codeL, pair_iff] at h
          obtain ⟨_, ha, hf, hx⟩ := h
          cases codeF_inj ha
          rw [codeL_inj d f f' hf, codeL_inj d x x' hx]
      | _ => simp only [codeL, pair_iff] at h; omega
  | _, _, d, .lamL b, t', h => by
      cases t' with
      | lamL b' => simp only [codeL, pair_iff] at h; rw [codeL_inj (d + 1) b b' h.2]
      | _ => simp only [codeL, pair_iff] at h; omega
  | _, _, d, .pos, t', h => by cases t' <;> first | rfl | (simp only [codeL, pair_iff] at h; omega)
  | _, _, d, .wabs φ, t', h => by
      cases t' with
      | wabs φ' => simp only [codeL, pair_iff] at h; rw [codeL_inj (d + 1) φ φ' h.2]
      | _ => simp only [codeL, pair_iff] at h; omega
  | _, _, d, .holds p i, t', h => by
      cases t' with
      | holds p' i' =>
          simp only [codeL, pair_iff] at h; rw [codeL_inj d p p' h.2.1, codeL_inj d i i' h.2.2]
      | _ => simp only [codeL, pair_iff] at h; omega
  | _, _, d, .rel p i, t', h => by
      cases t' with
      | rel p' i' =>
          simp only [codeL, pair_iff] at h; rw [codeL_inj d p p' h.2.1, codeL_inj d i i' h.2.2]
      | _ => simp only [codeL, pair_iff] at h; omega
  | _, _, d, .act p i, t', h => by
      cases t' with
      | act p' i' =>
          simp only [codeL, pair_iff] at h; rw [codeL_inj d p p' h.2.1, codeL_inj d i i' h.2.2]
      | _ => simp only [codeL, pair_iff] at h; omega
  | _, _, d, .bot, t', h => by cases t' <;> first | rfl | (simp only [codeL, pair_iff] at h; omega)
  | _, _, d, .imp p i, t', h => by
      cases t' with
      | imp p' i' =>
          simp only [codeL, pair_iff] at h; rw [codeL_inj d p p' h.2.1, codeL_inj d i i' h.2.2]
      | _ => simp only [codeL, pair_iff] at h; omega
  | _, _, d, .and p i, t', h => by
      cases t' with
      | and p' i' =>
          simp only [codeL, pair_iff] at h; rw [codeL_inj d p p' h.2.1, codeL_inj d i i' h.2.2]
      | _ => simp only [codeL, pair_iff] at h; omega
  | _, _, d, .or p i, t', h => by
      cases t' with
      | or p' i' =>
          simp only [codeL, pair_iff] at h; rw [codeL_inj d p p' h.2.1, codeL_inj d i i' h.2.2]
      | _ => simp only [codeL, pair_iff] at h; omega
  | _, _, d, .all a p, t', h => by
      cases t' with
      | all a' p' =>
          simp only [codeL, pair_iff] at h
          obtain ⟨_, ha, hp⟩ := h
          cases codeH_inj ha
          rw [codeL_inj (d + 1) p p' hp]
      | _ => simp only [codeL, pair_iff] at h; omega
  | _, _, d, .ex a p, t', h => by
      cases t' with
      | ex a' p' =>
          simp only [codeL, pair_iff] at h
          obtain ⟨_, ha, hp⟩ := h
          cases codeH_inj ha
          rw [codeL_inj (d + 1) p p' hp]
      | _ => simp only [codeL, pair_iff] at h; omega
  | _, _, d, .eq a s t, t', h => by
      cases t' with
      | eq a' s' t'' =>
          simp only [codeL, pair_iff] at h
          obtain ⟨_, ha, hs, ht⟩ := h
          cases codeH_inj ha
          rw [codeL_inj d s s' hs, codeL_inj d t t'' ht]
      | _ => simp only [codeL, pair_iff] at h; omega


/-- A renaming preserving the code of variables at depth `d`. -/
def Good (d : Nat) (r : HRen Γ Δ) : Prop := ∀ {b} (v : HVar Γ b), vcode d (r v) = vcode d v

theorem good_lift {d : Nat} {r : HRen Γ Δ} (h : Good d r) : Good (d + 1) (liftR (a := c) r) := by
  intro b v
  cases v with
  | zero => simp [vcode, liftR, codeV]
  | succ v =>
      have hv := h v
      have l := codeV_lt v; have l' := codeV_lt (r v)
      simp only [vcode, liftR, codeV, List.length_cons] at hv ⊢
      by_cases h1 : codeV v < d <;> by_cases h2 : codeV (r v) < d <;>
        simp only [h1, h2, ite_true, ite_false, Nat.add_lt_add_iff_right, pair_iff] at hv ⊢ <;>
        (obtain ⟨hv1, hv2⟩ := hv; exact ⟨by first | trivial | omega, by omega⟩)

theorem good_succ : Good 0 (fun v => (HVar.succ v : HVar (c :: Γ) _)) := by
  intro b v
  have l := codeV_lt v
  simp only [vcode, codeV, List.length_cons, Nat.not_lt_zero, ite_false, pair_iff]
  exact ⟨trivial, by omega⟩

theorem codeL_rename : ∀ {Γ Δ a} (t : HTerm Γ a) (d : Nat) (r : HRen Γ Δ), Good d r →
    codeL d (rename r t) = codeL d t := by
  intro Γ Δ a t
  induction t generalizing Δ with
  | var v => intro d r h; simp only [rename, codeL, h v]
  | appL f x ihf ihx => intro d r h; simp only [rename, codeL, ihf d r h, ihx d r h]
  | lamL b ih => intro d r h; simp only [rename, codeL, ih (d + 1) _ (good_lift h)]
  | pos => intro _ _ _; rfl
  | wabs φ ih => intro d r h; simp only [rename, codeL, ih (d + 1) _ (good_lift h)]
  | holds p i ihp ihi => intro d r h; simp only [rename, codeL, ihp d r h, ihi d r h]
  | rel p i ihp ihi => intro d r h; simp only [rename, codeL, ihp d r h, ihi d r h]
  | act p i ihp ihi => intro d r h; simp only [rename, codeL, ihp d r h, ihi d r h]
  | bot => intro _ _ _; rfl
  | imp p i ihp ihi => intro d r h; simp only [rename, codeL, ihp d r h, ihi d r h]
  | and p i ihp ihi => intro d r h; simp only [rename, codeL, ihp d r h, ihi d r h]
  | or p i ihp ihi => intro d r h; simp only [rename, codeL, ihp d r h, ihi d r h]
  | all a p ih => intro d r h; simp only [rename, codeL, ih (d + 1) _ (good_lift h)]
  | ex a p ih => intro d r h; simp only [rename, codeL, ih (d + 1) _ (good_lift h)]
  | eq a s t ihs iht => intro d r h; simp only [rename, codeL, ihs d r h, iht d r h]

/-- Weakening does not change the code. -/
theorem codeL_wk (t : HTerm Γ a) : codeL 0 (wk (b := c) t) = codeL 0 t :=
  codeL_rename t 0 _ good_succ

/-- The formula over `Γ` with code `n`, if any (classical). -/
noncomputable def decL (Γ : List HTy) (a : HTy) (n : Nat) : Option (HTerm Γ a) :=
  open Classical in if h : ∃ t : HTerm Γ a, codeL 0 t = n then some (Classical.choose h) else none

theorem decL_codeL (t : HTerm Γ a) : decL Γ a (codeL 0 t) = some t := by
  have h : ∃ t' : HTerm Γ a, codeL 0 t' = codeL 0 t := ⟨t, rfl⟩
  unfold decL; rw [dif_pos h]; exact congrArg some (codeL_inj 0 _ _ (Classical.choose_spec h))

/-! ## Lindenbaum's construction with Henkin witnesses

Stage `k + 1` adds one variable to the context of stage `k`: for the formula processed at
stage `k` that is an `∃ a. χ` the variable is its witness, otherwise a dummy variable of type `o`.
Contexts never get variables that are not witnesses, which matters: a variable of type `L e` in
the context makes `∃ x : e. ⊤` derivable. -/

noncomputable def unpair (k : Nat) : Nat × Nat :=
  open Classical in
  if h : ∃ a b, pair a b = k then (Classical.choose h, Classical.choose (Classical.choose_spec h))
  else (0, 0)

theorem unpair_pair (a b : Nat) : unpair (pair a b) = (a, b) := by
  have h : ∃ a' b', pair a' b' = pair a b := ⟨a, b, rfl⟩
  unfold unpair; rw [dif_pos h]
  have e := pair_inj (Classical.choose_spec (Classical.choose_spec h))
  simp only [Prod.mk.injEq]; exact e

theorem le_pair (a b : Nat) : a ≤ pair a b := by
  have h1 : a < 2 ^ a := Nat.lt_two_pow_self
  have : 2 ^ a * 1 ≤ 2 ^ a * (2 * b + 1) := Nat.mul_le_mul_left _ (by omega)
  unfold pair; omega

section lind
variable (T : Tm [] .s → Prop)

def Cons (Γ : List HTy) (hs : List (HTerm Γ .o)) : Prop := ¬ DC T Γ hs .bot

def topH : HTerm Γ .o := .imp .bot .bot
def negH (φ : HTerm Γ .o) : HTerm Γ .o := .imp φ .bot

structure St where
  Γ : List HTy
  hs : List (HTerm Γ .o)

/-- Witness data: for `∃ a. χ` the type `a` and `χ`; otherwise a dummy `o`-variable. -/
def wit : HTerm Γ .o → (Σ b : HTy, HTerm (b :: Γ) .o)
  | .ex a χ => ⟨a, χ⟩
  | φ => ⟨.o, wk φ⟩

theorem wit_cases (ψ : HTerm Γ .o) :
    (∃ a χ, ψ = .ex a χ ∧ wit ψ = ⟨a, χ⟩) ∨ wit ψ = ⟨.o, wk ψ⟩ := by
  cases ψ <;> simp [wit]

/-- The formula decided at stage `k`: the formula over the current context with code
`(unpair k).2`, or its negation if it is inconsistent with the stage; `⊤` if there is none. -/
noncomputable def pick (k : Nat) (Γ : List HTy) (hs : List (HTerm Γ .o)) : HTerm Γ .o :=
  open Classical in
  match decL Γ .o (unpair k).2 with
  | some φ => if Cons T Γ (φ :: hs) then φ else negH φ
  | none => topH

noncomputable def step (k : Nat) (s : St) : St :=
  ⟨(wit (pick T k s.Γ s.hs)).1 :: s.Γ,
    (wit (pick T k s.Γ s.hs)).2 :: (pick T k s.Γ s.hs :: s.hs).map wk⟩

theorem pick_cons (k : Nat) {Γ : List HTy} {hs : List (HTerm Γ .o)} (h : Cons T Γ hs) :
    Cons T Γ (pick T k Γ hs :: hs) := by
  unfold pick
  split
  · rename_i φ _
    split
    · assumption
    · rename_i hn
      intro d
      apply h
      have d1 : DC T Γ hs (negH φ) := .impI (Classical.byContradiction hn)
      exact .impE (.impI d) d1
  · intro d
    exact h (.impE (.impI d) (.impI (.hyp (List.mem_cons_self ..))))

theorem wit_cons {Γ : List HTy} {ψ : HTerm Γ .o} {hs : List (HTerm Γ .o)} (h : Cons T Γ (ψ :: hs)) :
    Cons T ((wit ψ).1 :: Γ) ((wit ψ).2 :: (ψ :: hs).map wk) := by
  rcases wit_cases ψ with ⟨a, χ, rfl, e⟩ | e
  · rw [e]; intro d
    exact h (.exE a (.hyp (List.mem_cons_self ..)) d)
  · rw [e]; intro d
    apply h
    have e1 : DC T Γ (ψ :: hs) (.ex .o topH) := .exI .o .bot trivial (.impI (.hyp (List.mem_cons_self ..)))
    refine .exE .o e1 (d.weaken ?_)
    intro x m
    rcases List.mem_cons.1 m with rfl | m
    · exact List.mem_cons_of_mem _ (List.mem_map_of_mem (List.mem_cons_self ..))
    · exact List.mem_cons_of_mem _ m

theorem step_cons (k : Nat) (s : St) (h : Cons T s.Γ s.hs) : Cons T (step T k s).Γ (step T k s).hs :=
  wit_cons T (pick_cons T k h)

variable (Γ0 : List HTy) (hs0 : List (HTerm Γ0 .o))

noncomputable def stage : Nat → St
  | 0 => ⟨Γ0, hs0⟩
  | k + 1 => step T k (stage k)

noncomputable abbrev Cx (n : Nat) : List HTy := (stage T Γ0 hs0 n).Γ
noncomputable abbrev Hs (n : Nat) : List (HTerm (Cx T Γ0 hs0 n) .o) := (stage T Γ0 hs0 n).hs

theorem stage_cons (h : Cons T Γ0 hs0) : ∀ n, Cons T (Cx T Γ0 hs0 n) (Hs T Γ0 hs0 n)
  | 0 => h
  | n + 1 => step_cons T n _ (stage_cons h n)

theorem mem_succ {n : Nat} {x : HTerm (Cx T Γ0 hs0 n) .o} (m : x ∈ Hs T Γ0 hs0 n) :
    wk x ∈ Hs T Γ0 hs0 (n + 1) :=
  List.mem_cons_of_mem _ (List.mem_map_of_mem (List.mem_cons_of_mem _ m))

noncomputable def liftTo (m : Nat) : (N : Nat) → m ≤ N → HRen (Cx T Γ0 hs0 m) (Cx T Γ0 hs0 N)
  | 0, h => fun v => by have e : m = 0 := by omega
                        subst e; exact v
  | N + 1, h => fun v => if h' : m ≤ N then .succ (liftTo m N h' v) else
      by have e : m = N + 1 := by omega
         subst e; exact v

theorem liftTo_succ {m N : Nat} (h : m ≤ N) {a} (v : HVar (Cx T Γ0 hs0 m) a) :
    liftTo T Γ0 hs0 m (N + 1) (Nat.le_succ_of_le h) v = .succ (liftTo T Γ0 hs0 m N h v) := by
  rw [liftTo.eq_2]; exact dif_pos h

theorem liftTo_refl : ∀ (m : Nat) (h : m ≤ m) {a} (v : HVar (Cx T Γ0 hs0 m) a), liftTo T Γ0 hs0 m m h v = v
  | 0, _, _, _ => rfl
  | m + 1, _, _, v => by
      rw [liftTo.eq_2]; exact (dif_neg (Nat.not_succ_le_self m)).trans rfl

theorem liftTo_trans {m n : Nat} (h1 : m ≤ n) : ∀ (N : Nat) (h2 : n ≤ N) (h3 : m ≤ N) {a}
    (v : HVar (Cx T Γ0 hs0 m) a),
    liftTo T Γ0 hs0 n N h2 (liftTo T Γ0 hs0 m n h1 v) = liftTo T Γ0 hs0 m N h3 v
  | 0, h2, h3, a, v => by
      obtain rfl : n = 0 := by omega
      obtain rfl : m = 0 := by omega
      rw [liftTo_refl]
  | N + 1, h2, h3, a, v => by
      by_cases hn : n ≤ N
      · rw [liftTo_succ T Γ0 hs0 hn, liftTo_succ T Γ0 hs0 (Nat.le_trans h1 hn),
          liftTo_trans h1 N hn (Nat.le_trans h1 hn)]
      · obtain rfl : n = N + 1 := by omega
        rw [liftTo_refl]

theorem good_liftTo (m : Nat) : ∀ (N : Nat) (h : m ≤ N), Good 0 (liftTo T Γ0 hs0 m N h)
  | 0, h => by
      obtain rfl : m = 0 := by omega
      intro v; show vcode 0 (liftTo T Γ0 hs0 0 0 h v) = _; rw [liftTo_refl]
  | N + 1, h => by
      by_cases hm : m ≤ N
      · intro v
        show vcode 0 (liftTo T Γ0 hs0 m (N + 1) h v) = _
        rw [liftTo_succ T Γ0 hs0 hm]
        exact (good_succ (liftTo T Γ0 hs0 m N hm v)).trans (good_liftTo m N hm v)
      · obtain rfl : m = N + 1 := by omega
        intro v; show vcode 0 (liftTo T Γ0 hs0 _ _ h v) = _; rw [liftTo_refl]

theorem rename_id' (t : HTerm Γ a) (r : HRen Γ Γ) (h : ∀ {b} (v : HVar Γ b), r v = v) : rename r t = t := by
  have e := subst_rename t r (fun v => .var v) (fun v => .var v) (fun v => by rw [h])
  rw [subst_id _ _ (fun _ => rfl), subst_id _ _ (fun _ => rfl)] at e; exact e

theorem inst_lift_var0 (χ : HTerm (a :: Γ) b) :
    inst (rename (liftR (fun v => (HVar.succ v : HVar (a :: Γ) _))) χ) (.var .zero) = χ := by
  unfold inst
  rw [subst_rename χ _ (sub0 (.var .zero)) (fun v => .var v) (fun v => by cases v <;> rfl)]
  exact subst_id χ _ (fun _ => rfl)

theorem rename_liftTo_succ {m n : Nat} (h : m ≤ n) (φ : HTerm (Cx T Γ0 hs0 m) a) :
    rename (liftTo T Γ0 hs0 m (n + 1) (Nat.le_succ_of_le h)) φ = wk (rename (liftTo T Γ0 hs0 m n h) φ) := by
  unfold wk
  exact (rename_rename φ _ _ _ (fun v => (liftTo_succ T Γ0 hs0 h v).symm)).symm

theorem rename_liftTo_trans {m n N : Nat} (h1 : m ≤ n) (h2 : n ≤ N) (φ : HTerm (Cx T Γ0 hs0 m) a) :
    rename (liftTo T Γ0 hs0 n N h2) (rename (liftTo T Γ0 hs0 m n h1) φ) =
      rename (liftTo T Γ0 hs0 m N (Nat.le_trans h1 h2)) φ :=
  rename_rename φ _ _ _ (fun v => liftTo_trans T Γ0 hs0 h1 N h2 _ v)

/-- Membership in the limit of the stages. -/
def Mem (m : Nat) (φ : HTerm (Cx T Γ0 hs0 m) .o) : Prop :=
  ∃ N, ∃ h : m ≤ N, rename (liftTo T Γ0 hs0 m N h) φ ∈ Hs T Γ0 hs0 N

theorem mem_mono {m N : Nat} (h : m ≤ N) (φ : HTerm (Cx T Γ0 hs0 m) .o)
    (hm : rename (liftTo T Γ0 hs0 m N h) φ ∈ Hs T Γ0 hs0 N) :
    ∀ d, rename (liftTo T Γ0 hs0 m (N + d) (Nat.le_trans h (Nat.le_add_right N d))) φ ∈ Hs T Γ0 hs0 (N + d)
  | 0 => hm
  | d + 1 => by
      show rename (liftTo T Γ0 hs0 m (N + d + 1) _) φ ∈ Hs T Γ0 hs0 (N + d + 1)
      rw [rename_liftTo_succ T Γ0 hs0 (Nat.le_trans h (Nat.le_add_right N d))]
      exact mem_succ T Γ0 hs0 (mem_mono h φ hm d)

theorem mem_at {m N : Nat} (φ : HTerm (Cx T Γ0 hs0 m) .o) (hφ : Mem T Γ0 hs0 m φ) (hN : m ≤ N) :
    ∃ N', ∃ h : N ≤ N', rename (liftTo T Γ0 hs0 m N' (Nat.le_trans hN h)) φ ∈ Hs T Γ0 hs0 N' := by
  obtain ⟨N0, h0, hm⟩ := hφ
  refine ⟨N0 + N, Nat.le_add_left N N0, ?_⟩
  exact mem_mono T Γ0 hs0 h0 φ hm N

theorem mem_all {m : Nat} : ∀ (hs : List (HTerm (Cx T Γ0 hs0 m) .o)), (∀ x, x ∈ hs → Mem T Γ0 hs0 m x) →
    ∃ N, ∃ h : m ≤ N, ∀ x, x ∈ hs → rename (liftTo T Γ0 hs0 m N h) x ∈ Hs T Γ0 hs0 N
  | [], _ => ⟨m, Nat.le_refl m, fun _ m => nomatch m⟩
  | x :: hs, hm => by
      obtain ⟨N1, h1, k1⟩ := mem_all hs (fun y my => hm y (List.mem_cons_of_mem _ my))
      obtain ⟨N2, h2, k2⟩ := mem_at T Γ0 hs0 x (hm x (List.mem_cons_self ..)) h1
      refine ⟨N2, Nat.le_trans h1 h2, fun y my => ?_⟩
      rcases List.mem_cons.1 my with rfl | my
      · exact k2
      · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h2
        exact mem_mono T Γ0 hs0 h1 y (k1 y my) d

/-- The limit is consistent. -/
theorem mem_consistent (hc : Cons T Γ0 hs0) {m : Nat} (hs : List (HTerm (Cx T Γ0 hs0 m) .o))
    (hm : ∀ x, x ∈ hs → Mem T Γ0 hs0 m x) : ¬ DC T (Cx T Γ0 hs0 m) hs .bot := by
  intro d
  obtain ⟨N, h, k⟩ := mem_all T Γ0 hs0 hs hm
  apply stage_cons T Γ0 hs0 hc N
  refine (d.ren (liftTo T Γ0 hs0 m N h)).weaken ?_
  intro y my
  obtain ⟨x, mx, rfl⟩ := List.mem_map.1 my
  exact k x mx

theorem mem_lift {m k : Nat} (h : m ≤ k) {φ : HTerm (Cx T Γ0 hs0 m) .o} (hφ : Mem T Γ0 hs0 m φ) :
    Mem T Γ0 hs0 k (rename (liftTo T Γ0 hs0 m k h) φ) := by
  obtain ⟨N', h', hm⟩ := mem_at T Γ0 hs0 φ hφ h
  exact ⟨N', h', by rw [rename_liftTo_trans]; exact hm⟩

theorem mem_self {N : Nat} {φ : HTerm (Cx T Γ0 hs0 N) .o} (h : φ ∈ Hs T Γ0 hs0 N) : Mem T Γ0 hs0 N φ :=
  ⟨N, Nat.le_refl N, by rw [rename_id' φ _ (fun v => liftTo_refl T Γ0 hs0 N _ v)]; exact h⟩

/-- The stage at which `φ` is decided. -/
noncomputable def dstage (m : Nat) (φ : HTerm (Cx T Γ0 hs0 m) .o) : Nat := pair m (codeL 0 φ)

theorem pick_at (m : Nat) (φ : HTerm (Cx T Γ0 hs0 m) .o) :
    pick T (dstage T Γ0 hs0 m φ) (Cx T Γ0 hs0 (dstage T Γ0 hs0 m φ)) (Hs T Γ0 hs0 (dstage T Γ0 hs0 m φ)) =
      (open Classical in
      if Cons T _ (rename (liftTo T Γ0 hs0 m _ (le_pair _ _)) φ :: Hs T Γ0 hs0 (dstage T Γ0 hs0 m φ))
      then rename (liftTo T Γ0 hs0 m _ (le_pair _ _)) φ
      else negH (rename (liftTo T Γ0 hs0 m _ (le_pair _ _)) φ)) := by
  have hc : codeL 0 (rename (liftTo T Γ0 hs0 m _ (le_pair m (codeL 0 φ))) φ) = codeL 0 φ :=
    codeL_rename φ 0 _ (good_liftTo T Γ0 hs0 m _ _)
  have hd : decL (Cx T Γ0 hs0 (dstage T Γ0 hs0 m φ)) .o (unpair (dstage T Γ0 hs0 m φ)).2 =
      some (rename (liftTo T Γ0 hs0 m _ (le_pair _ _)) φ) := by
    unfold dstage; rw [unpair_pair]
    have := decL_codeL (rename (liftTo T Γ0 hs0 m _ (le_pair m (codeL 0 φ))) φ)
    rw [hc] at this; exact this
  unfold pick; rw [hd]; rfl

theorem pick_mem (k : Nat) (x : HTerm (Cx T Γ0 hs0 k) .o)
    (hx : x = pick T k (Cx T Γ0 hs0 k) (Hs T Γ0 hs0 k)) : wk x ∈ Hs T Γ0 hs0 (k + 1) := by
  subst hx
  exact List.mem_cons_of_mem _ (List.mem_map_of_mem (List.mem_cons_self ..))

/-- The limit is maximal. -/
theorem mem_max (m : Nat) (φ : HTerm (Cx T Γ0 hs0 m) .o) :
    Mem T Γ0 hs0 m φ ∨ Mem T Γ0 hs0 m (negH φ) := by
  have hp := pick_at T Γ0 hs0 m φ
  have hk := le_pair m (codeL 0 φ)
  split at hp
  · left
    refine ⟨_, Nat.le_succ_of_le hk, ?_⟩
    rw [rename_liftTo_succ T Γ0 hs0 hk]
    exact pick_mem T Γ0 hs0 _ _ hp.symm
  · right
    refine ⟨_, Nat.le_succ_of_le hk, ?_⟩
    rw [rename_liftTo_succ T Γ0 hs0 hk]
    exact pick_mem T Γ0 hs0 _ _ hp.symm

theorem mem_not_both (hc : Cons T Γ0 hs0) {m : Nat} {φ : HTerm (Cx T Γ0 hs0 m) .o}
    (h1 : Mem T Γ0 hs0 m φ) (h2 : Mem T Γ0 hs0 m (negH φ)) : False := by
  refine mem_consistent T Γ0 hs0 hc [φ, negH φ] ?_ ?_
  · intro x mx; simp only [List.mem_cons, List.not_mem_nil, or_false] at mx
    rcases mx with rfl | rfl <;> assumption
  · exact .impE (.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..))) (.hyp (List.mem_cons_self ..))

theorem step_wit (k : Nat) (s : St) {a : HTy} (χ : HTerm (a :: s.Γ) .o)
    (hp : pick T k s.Γ s.hs = .ex a χ) :
    ∃ x : HVar (step T k s).Γ a, inst (rename (liftR (fun v => (HVar.succ v : HVar (step T k s).Γ _))) χ) (.var x) ∈
      (step T k s).hs := by
  unfold step
  generalize pick T k s.Γ s.hs = p at hp ⊢
  subst hp
  refine ⟨.zero, ?_⟩
  show inst (rename (liftR (fun v => (HVar.succ v : HVar (a :: s.Γ) _))) χ) (.var .zero) ∈
    (χ :: ((HTerm.ex a χ :: s.hs).map wk : List (HTerm (a :: s.Γ) .o)))
  rw [inst_lift_var0]; exact List.mem_cons_self ..

/-- The limit has Henkin witnesses. -/
theorem mem_henkin (hc : Cons T Γ0 hs0) {m : Nat} {a : HTy} {χ : HTerm (a :: Cx T Γ0 hs0 m) .o}
    (h : Mem T Γ0 hs0 m (.ex a χ)) :
    ∃ N, ∃ hN : m ≤ N, ∃ x : HVar (Cx T Γ0 hs0 N) a,
      Mem T Γ0 hs0 N (inst (rename (liftR (liftTo T Γ0 hs0 m N hN)) χ) (.var x)) := by
  have hk := le_pair m (codeL 0 (HTerm.ex a χ))
  have hp := pick_at T Γ0 hs0 m (.ex a χ)
  split at hp
  · obtain ⟨x, hx⟩ := step_wit T _ _ _ hp
    refine ⟨_ + 1, Nat.le_succ_of_le hk, x, mem_self T Γ0 hs0 ?_⟩
    have e : rename (liftR (fun v => (HVar.succ v : HVar (Cx T Γ0 hs0 (dstage T Γ0 hs0 m (.ex a χ) + 1)) _)))
        (rename (liftR (liftTo T Γ0 hs0 m _ hk)) χ) =
        rename (liftR (liftTo T Γ0 hs0 m _ (Nat.le_succ_of_le hk))) χ :=
      rename_rename χ _ _ _ (fun v => by
        cases v with
        | zero => rfl
        | succ v => exact congrArg HVar.succ (liftTo_succ T Γ0 hs0 hk v).symm)
    rw [← e]; exact hx
  · exfalso
    rename_i hn
    have m1 : Mem T Γ0 hs0 (dstage T Γ0 hs0 m (.ex a χ) + 1) (wk (negH (rename (liftTo T Γ0 hs0 m _ hk) (.ex a χ)))) :=
      mem_self T Γ0 hs0 (pick_mem T Γ0 hs0 _ _ hp.symm)
    have m2 := mem_lift T Γ0 hs0 (Nat.le_succ_of_le hk) h
    rw [rename_liftTo_succ T Γ0 hs0 hk] at m2
    exact mem_not_both T Γ0 hs0 hc m2 m1

/-- The limit is deductively closed. -/
theorem mem_deriv (hc : Cons T Γ0 hs0) {m : Nat} {hs : List (HTerm (Cx T Γ0 hs0 m) .o)}
    {φ : HTerm (Cx T Γ0 hs0 m) .o} (hm : ∀ x, x ∈ hs → Mem T Γ0 hs0 m x) (d : DC T (Cx T Γ0 hs0 m) hs φ) :
    Mem T Γ0 hs0 m φ := by
  rcases mem_max T Γ0 hs0 m φ with h | h
  · exact h
  · exfalso
    refine mem_consistent T Γ0 hs0 hc (negH φ :: hs) ?_ (.impE (.hyp (List.mem_cons_self ..)) (d.wk1 _))
    intro x mx
    rcases List.mem_cons.1 mx with rfl | mx
    · exact h
    · exact hm x mx

/-- The starting point of completeness: a non-derivable `⟦φ⟧` at a world variable. -/
theorem start_cons {φ : Tm [] .s} (h : ¬ DC T [.w] [] (.holds (emb nilR φ) var0)) :
    Cons T [.w] [negH (.holds (emb nilR φ) var0)] :=
  fun d => h (.byContra d)

end lind
end Programme.«20261022-1724-ontological».ThHenkin

/-! ## M3d: the canonical model -/

namespace Programme.«20261022-1724-ontological».ThCanon
open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.HOLX Programme.«20261022-1724-ontological».ThHenkin
noncomputable section

/-! ### Normal form of certified terms -/

def Lpart : List HTy → List FTy
  | [] => []
  | .L t :: Γ => t :: Lpart Γ
  | .w :: Γ => Lpart Γ
  | .o :: Γ => Lpart Γ

def canonR : {Γ : List HTy} → {t : FTy} → Var (Lpart Γ) t → HVar Γ (.L t)
  | .L _ :: _, _, .zero => .zero
  | .L _ :: Γ, _, .succ v => .succ (canonR (Γ := Γ) v)
  | .w :: Γ, _, v => .succ (canonR (Γ := Γ) v)
  | .o :: Γ, _, v => .succ (canonR (Γ := Γ) v)

def lposG : {Γ : List HTy} → {a : HTy} → HVar Γ a → (t : FTy) → a = .L t → Var (Lpart Γ) t
  | _, _, @HVar.zero Γ a, t, h =>
      match a, h with
      | .L _, rfl => (Var.zero : Var (Lpart (.L t :: Γ)) t)
  | _, _, @HVar.succ Γ _ b v, t, h =>
      match b with
      | .L _ => .succ (lposG v t h)
      | .w => lposG v t h
      | .o => lposG v t h

def lpos {Γ : List HTy} {t : FTy} (v : HVar Γ (.L t)) : Var (Lpart Γ) t := lposG v t rfl

theorem canonR_lposG : ∀ {Γ : List HTy} {a : HTy} (v : HVar Γ a) (t : FTy) (h : a = .L t),
    canonR (lposG v t h) = h ▸ v
  | _, _, @HVar.zero Γ a, t, h => by cases h; rfl
  | _, _, @HVar.succ Γ _ b v, t, h => by
      cases h
      cases b <;> simp only [lposG, canonR, canonR_lposG v _ rfl]

theorem canonR_lpos {Γ : List HTy} {t : FTy} (v : HVar Γ (.L t)) : canonR (lpos v) = v :=
  canonR_lposG v t rfl

theorem lpos_canonR : ∀ {Γ : List HTy} {t : FTy} (v : Var (Lpart Γ) t), lpos (canonR v) = v
  | .L _ :: _, _, .zero => rfl
  | .L _ :: Γ, _, .succ v => congrArg Var.succ (lpos_canonR (Γ := Γ) v)
  | .w :: Γ, _, v => lpos_canonR (Γ := Γ) v
  | .o :: Γ, _, v => lpos_canonR (Γ := Γ) v

/-- Every embedded term is an embedding through the canonical renaming. -/
theorem emb_nf (r : LRen Γ' Γ) (s : Tm Γ' t) :
    emb r s = emb canonR (renameL (fun v => lpos (r v)) s) :=
  (emb_renameL s _ canonR r (fun v => canonR_lpos (r v))).symm

theorem cert_nf {x : HTerm Γ (.L t)} (h : Cert (.L t) x) : ∃ s : Tm (Lpart Γ) t, x = emb canonR s := by
  obtain ⟨_, s, r, rfl⟩ := h
  exact ⟨_, emb_nf r s⟩


/-! ### 𝓛-level substitution algebra -/

theorem substL_renameL : ∀ {Γ Δ Θ t} (tm : Tm Γ t) (q : RenL Γ Δ) (s : SubL Δ Θ) (s' : SubL Γ Θ),
    (∀ {u} (v : Var Γ u), s (q v) = s' v) → substL s (renameL q tm) = substL s' tm := by
  intro Γ Δ Θ t tm
  induction tm generalizing Δ Θ with
  | var i => intro q s s' h; simp only [renameL, substL, h]
  | app F x ihF ihx => intro q s s' h; simp only [renameL, substL, ihF q s s' h, ihx q s s' h]
  | lam b ih =>
      intro q s s' h; simp only [renameL, substL]
      rw [ih (liftRL q) (liftSL s) (liftSL s') (fun v => by cases v <;> simp [liftRL, liftSL, h])]
  | top => intros; rfl
  | bot => intros; rfl
  | neg x ih => intro q s s' h; simp only [renameL, substL, ih q s s' h]
  | and x y ihx ihy => intro q s s' h; simp only [renameL, substL, ihx q s s' h, ihy q s s' h]
  | or x y ihx ihy => intro q s s' h; simp only [renameL, substL, ihx q s s' h, ihy q s s' h]
  | imp x y ihx ihy => intro q s s' h; simp only [renameL, substL, ihx q s s' h, ihy q s s' h]
  | box x ih => intro q s s' h; simp only [renameL, substL, ih q s s' h]
  | all a b ih =>
      intro q s s' h; simp only [renameL, substL]
      rw [ih (liftRL q) (liftSL s) (liftSL s') (fun v => by cases v <;> simp [liftRL, liftSL, h])]
  | ex a b ih =>
      intro q s s' h; simp only [renameL, substL]
      rw [ih (liftRL q) (liftSL s) (liftSL s') (fun v => by cases v <;> simp [liftRL, liftSL, h])]
  | allE b ih =>
      intro q s s' h; simp only [renameL, substL]
      rw [ih (liftRL q) (liftSL s) (liftSL s') (fun v => by cases v <;> simp [liftRL, liftSL, h])]
  | exE b ih =>
      intro q s s' h; simp only [renameL, substL]
      rw [ih (liftRL q) (liftSL s) (liftSL s') (fun v => by cases v <;> simp [liftRL, liftSL, h])]
  | eq a x y ihx ihy => intro q s s' h; simp only [renameL, substL, ihx q s s' h, ihy q s s' h]
  | pos => intros; rfl

theorem renameL_renameL : ∀ {Γ Δ Θ t} (tm : Tm Γ t) (q : RenL Γ Δ) (q' : RenL Δ Θ) (q'' : RenL Γ Θ),
    (∀ {u} (v : Var Γ u), q' (q v) = q'' v) → renameL q' (renameL q tm) = renameL q'' tm := by
  intro Γ Δ Θ t tm
  induction tm generalizing Δ Θ with
  | var i => intro q s s' h; simp only [renameL, h]
  | app F x ihF ihx => intro q s s' h; simp only [renameL, ihF q s s' h, ihx q s s' h]
  | lam b ih =>
      intro q s s' h; simp only [renameL]
      rw [ih (liftRL q) (liftRL s) (liftRL s') (fun v => by cases v <;> simp [liftRL, h])]
  | top => intros; rfl
  | bot => intros; rfl
  | neg x ih => intro q s s' h; simp only [renameL, ih q s s' h]
  | and x y ihx ihy => intro q s s' h; simp only [renameL, ihx q s s' h, ihy q s s' h]
  | or x y ihx ihy => intro q s s' h; simp only [renameL, ihx q s s' h, ihy q s s' h]
  | imp x y ihx ihy => intro q s s' h; simp only [renameL, ihx q s s' h, ihy q s s' h]
  | box x ih => intro q s s' h; simp only [renameL, ih q s s' h]
  | all a b ih =>
      intro q s s' h; simp only [renameL]
      rw [ih (liftRL q) (liftRL s) (liftRL s') (fun v => by cases v <;> simp [liftRL, h])]
  | ex a b ih =>
      intro q s s' h; simp only [renameL]
      rw [ih (liftRL q) (liftRL s) (liftRL s') (fun v => by cases v <;> simp [liftRL, h])]
  | allE b ih =>
      intro q s s' h; simp only [renameL]
      rw [ih (liftRL q) (liftRL s) (liftRL s') (fun v => by cases v <;> simp [liftRL, h])]
  | exE b ih =>
      intro q s s' h; simp only [renameL]
      rw [ih (liftRL q) (liftRL s) (liftRL s') (fun v => by cases v <;> simp [liftRL, h])]
  | eq a x y ihx ihy => intro q s s' h; simp only [renameL, ihx q s s' h, ihy q s s' h]
  | pos => intros; rfl

theorem renameL_wkL (q : RenL Γ Δ) (t : Tm Γ u) :
    renameL (liftRL (a := a) q) (wkL t) = wkL (renameL q t) := by
  unfold wkL
  exact (renameL_renameL t (fun v => .succ v) (liftRL q) (fun v => .succ (q v)) (fun _ => rfl)).trans
    (renameL_renameL t q (fun v => .succ v) (fun v => .succ (q v)) (fun _ => rfl)).symm

theorem renameL_substL : ∀ {Γ Δ Θ t} (tm : Tm Γ t) (s : SubL Γ Δ) (q : RenL Δ Θ) (s' : SubL Γ Θ),
    (∀ {u} (v : Var Γ u), renameL q (s v) = s' v) → renameL q (substL s tm) = substL s' tm := by
  intro Γ Δ Θ t tm
  induction tm generalizing Δ Θ with
  | var i => intro s q s' h; simp only [substL, h]
  | app F x ihF ihx => intro s q s' h; simp only [renameL, substL, ihF s q s' h, ihx s q s' h]
  | lam b ih =>
      intro s q s' h; simp only [renameL, substL]
      rw [ih (liftSL s) (liftRL q) (liftSL s') (fun v => by
        cases v with
        | zero => rfl
        | succ v => simp only [liftSL]; rw [renameL_wkL, h])]
  | top => intros; rfl
  | bot => intros; rfl
  | neg x ih => intro s q s' h; simp only [renameL, substL, ih s q s' h]
  | and x y ihx ihy => intro s q s' h; simp only [renameL, substL, ihx s q s' h, ihy s q s' h]
  | or x y ihx ihy => intro s q s' h; simp only [renameL, substL, ihx s q s' h, ihy s q s' h]
  | imp x y ihx ihy => intro s q s' h; simp only [renameL, substL, ihx s q s' h, ihy s q s' h]
  | box x ih => intro s q s' h; simp only [renameL, substL, ih s q s' h]
  | all a b ih =>
      intro s q s' h; simp only [renameL, substL]
      rw [ih (liftSL s) (liftRL q) (liftSL s') (fun v => by
        cases v with
        | zero => rfl
        | succ v => simp only [liftSL]; rw [renameL_wkL, h])]
  | ex a b ih =>
      intro s q s' h; simp only [renameL, substL]
      rw [ih (liftSL s) (liftRL q) (liftSL s') (fun v => by
        cases v with
        | zero => rfl
        | succ v => simp only [liftSL]; rw [renameL_wkL, h])]
  | allE b ih =>
      intro s q s' h; simp only [renameL, substL]
      rw [ih (liftSL s) (liftRL q) (liftSL s') (fun v => by
        cases v with
        | zero => rfl
        | succ v => simp only [liftSL]; rw [renameL_wkL, h])]
  | exE b ih =>
      intro s q s' h; simp only [renameL, substL]
      rw [ih (liftSL s) (liftRL q) (liftSL s') (fun v => by
        cases v with
        | zero => rfl
        | succ v => simp only [liftSL]; rw [renameL_wkL, h])]
  | eq a x y ihx ihy => intro s q s' h; simp only [renameL, substL, ihx s q s' h, ihy s q s' h]
  | pos => intros; rfl

theorem substL_wkL (s : SubL Γ Δ) (t : Tm Γ u) :
    substL (liftSL (a := a) s) (wkL t) = wkL (substL s t) := by
  unfold wkL
  exact (substL_renameL t (fun v => .succ v) (liftSL s) (fun v => wkL (s v)) (fun _ => rfl)).trans
    (renameL_substL t s (fun v => .succ v) (fun v => wkL (s v)) (fun _ => rfl)).symm

theorem substL_substL : ∀ {Γ Δ Θ t} (tm : Tm Γ t) (s : SubL Γ Δ) (s' : SubL Δ Θ) (s'' : SubL Γ Θ),
    (∀ {u} (v : Var Γ u), substL s' (s v) = s'' v) → substL s' (substL s tm) = substL s'' tm := by
  intro Γ Δ Θ t tm
  induction tm generalizing Δ Θ with
  | var i => intro s q s' h; simp only [substL, h]
  | app F x ihF ihx => intro s q s' h; simp only [substL, ihF s q s' h, ihx s q s' h]
  | lam b ih =>
      intro s q s' h; simp only [substL]
      rw [ih (liftSL s) (liftSL q) (liftSL s') (fun v => by
        cases v with
        | zero => rfl
        | succ v => simp only [liftSL]; rw [substL_wkL, h])]
  | top => intros; rfl
  | bot => intros; rfl
  | neg x ih => intro s q s' h; simp only [substL, ih s q s' h]
  | and x y ihx ihy => intro s q s' h; simp only [substL, ihx s q s' h, ihy s q s' h]
  | or x y ihx ihy => intro s q s' h; simp only [substL, ihx s q s' h, ihy s q s' h]
  | imp x y ihx ihy => intro s q s' h; simp only [substL, ihx s q s' h, ihy s q s' h]
  | box x ih => intro s q s' h; simp only [substL, ih s q s' h]
  | all a b ih =>
      intro s q s' h; simp only [substL]
      rw [ih (liftSL s) (liftSL q) (liftSL s') (fun v => by
        cases v with
        | zero => rfl
        | succ v => simp only [liftSL]; rw [substL_wkL, h])]
  | ex a b ih =>
      intro s q s' h; simp only [substL]
      rw [ih (liftSL s) (liftSL q) (liftSL s') (fun v => by
        cases v with
        | zero => rfl
        | succ v => simp only [liftSL]; rw [substL_wkL, h])]
  | allE b ih =>
      intro s q s' h; simp only [substL]
      rw [ih (liftSL s) (liftSL q) (liftSL s') (fun v => by
        cases v with
        | zero => rfl
        | succ v => simp only [liftSL]; rw [substL_wkL, h])]
  | exE b ih =>
      intro s q s' h; simp only [substL]
      rw [ih (liftSL s) (liftSL q) (liftSL s') (fun v => by
        cases v with
        | zero => rfl
        | succ v => simp only [liftSL]; rw [substL_wkL, h])]
  | eq a x y ihx ihy => intro s q s' h; simp only [substL, ihx s q s' h, ihy s q s' h]
  | pos => intros; rfl

theorem sub0L_wkL (t : Tm Γ a) (x : Tm Γ b) : substL (sub0L x) (wkL t) = t := by
  rw [wkL, substL_renameL _ _ (sub0L x) (fun v => .var v) (fun _ => rfl), substL_id _ _ (fun _ => rfl)]

/-- Instantiating a lifted substitution: `(s↑ b)[x] = (x · s) b`. -/
def consL (x : Tm Δ a) (s : SubL Γ Δ) : SubL (a :: Γ) Δ
  | _, .zero => x
  | _, .succ v => s v

theorem instL_liftSL (b : Tm (a :: Γ) u) (s : SubL Γ Δ) (x : Tm Δ a) :
    instL (substL (liftSL s) b) x = substL (consL x s) b :=
  substL_substL b _ _ _ (fun v => by
    cases v with
    | zero => rfl
    | succ v => exact sub0L_wkL _ _)

theorem renameL_id' (tm : Tm Γ t) (q : RenL Γ Γ) (h : ∀ {u} (v : Var Γ u), q v = v) : renameL q tm = tm := by
  have := substL_renameL tm q (fun v => .var v) (fun v => .var v) (fun v => by simp only [h])
  rwa [substL_id _ _ (fun _ => rfl), substL_id _ _ (fun _ => rfl)] at this

/-! ### The seed and stage bookkeeping -/

/-- Data of the canonical construction: a consistent start with a world term. -/
structure Seed where
  T : Tm [] .s → Prop
  Γ0 : List HTy
  hs0 : List (HTerm Γ0 .o)
  hc : Cons T Γ0 hs0
  i0 : HTerm Γ0 .w

namespace Seed
variable (Z : Seed)

noncomputable abbrev X (n : Nat) : List HTy := Cx Z.T Z.Γ0 Z.hs0 n
noncomputable abbrev lt (m N : Nat) (h : m ≤ N) : HRen (Z.X m) (Z.X N) := liftTo Z.T Z.Γ0 Z.hs0 m N h
abbrev M (n : Nat) (φ : HTerm (Z.X n) .o) : Prop := Mem Z.T Z.Γ0 Z.hs0 n φ
abbrev D (n : Nat) (hs : List (HTerm (Z.X n) .o)) (φ : HTerm (Z.X n) .o) : Prop := DC Z.T (Z.X n) hs φ
noncomputable abbrev Lp (n : Nat) : List FTy := Lpart (Z.X n)

theorem lt_trans {m n N : Nat} (h1 : m ≤ n) (h2 : n ≤ N) (h3 : m ≤ N) {a} (v : HVar (Z.X m) a) :
    Z.lt n N h2 (Z.lt m n h1 v) = Z.lt m N h3 v := liftTo_trans Z.T Z.Γ0 Z.hs0 h1 N h2 h3 v

theorem lt_refl (m : Nat) (h : m ≤ m) {a} (v : HVar (Z.X m) a) : Z.lt m m h v = v :=
  liftTo_refl Z.T Z.Γ0 Z.hs0 m h v

theorem ren_trans {m n N : Nat} (h1 : m ≤ n) (h2 : n ≤ N) (h3 : m ≤ N) (φ : HTerm (Z.X m) a) :
    rename (Z.lt n N h2) (rename (Z.lt m n h1) φ) = rename (Z.lt m N h3) φ :=
  rename_rename φ _ _ _ (fun v => Z.lt_trans h1 h2 h3 v)

theorem ren_refl (m : Nat) (h : m ≤ m) (φ : HTerm (Z.X m) a) : rename (Z.lt m m h) φ = φ :=
  rename_id' φ _ (fun v => Z.lt_refl m h v)

theorem M_deriv {n : Nat} {hs : List (HTerm (Z.X n) .o)} {φ : HTerm (Z.X n) .o}
    (hm : ∀ x, x ∈ hs → Z.M n x) (d : Z.D n hs φ) : Z.M n φ :=
  mem_deriv Z.T Z.Γ0 Z.hs0 Z.hc hm d

theorem M_of {n : Nat} {φ : HTerm (Z.X n) .o} (d : Z.D n [] φ) : Z.M n φ :=
  Z.M_deriv (fun _ m => by simp at m) d

theorem M_mp {n : Nat} {φ ψ : HTerm (Z.X n) .o} (h : Z.M n φ) (d : Z.D n [φ] ψ) : Z.M n ψ :=
  Z.M_deriv (fun x m => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at m; subst m; exact h) d

theorem M_mp2 {n : Nat} {φ φ' ψ : HTerm (Z.X n) .o} (h : Z.M n φ) (h' : Z.M n φ') (d : Z.D n [φ, φ'] ψ) :
    Z.M n ψ :=
  Z.M_deriv (fun x m => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at m
    rcases m with rfl | rfl <;> assumption) d

theorem M_max (n : Nat) (φ : HTerm (Z.X n) .o) : Z.M n φ ∨ Z.M n (negH φ) := mem_max Z.T Z.Γ0 Z.hs0 n φ

theorem M_not_both {n : Nat} {φ : HTerm (Z.X n) .o} (h1 : Z.M n φ) (h2 : Z.M n (negH φ)) : False :=
  mem_not_both Z.T Z.Γ0 Z.hs0 Z.hc h1 h2

theorem M_neg {n : Nat} {φ : HTerm (Z.X n) .o} : Z.M n (negH φ) ↔ ¬ Z.M n φ :=
  ⟨fun h h' => Z.M_not_both h' h, fun h => (Z.M_max n φ).resolve_left h⟩

theorem M_bot {n : Nat} : ¬ Z.M n .bot := fun h =>
  mem_consistent Z.T Z.Γ0 Z.hs0 Z.hc [.bot] (fun x m => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at m; subst m; exact h)
    (.hyp (List.mem_cons_self ..))

theorem M_lift {n K : Nat} (h : n ≤ K) (φ : HTerm (Z.X n) .o) :
    Z.M n φ ↔ Z.M K (rename (Z.lt n K h) φ) := by
  constructor
  · exact fun m => mem_lift Z.T Z.Γ0 Z.hs0 h m
  · intro m
    rcases Z.M_max n φ with h1 | h1
    · exact h1
    · exact (Z.M_not_both m (mem_lift Z.T Z.Γ0 Z.hs0 h h1)).elim

/-- Stage independence for natural families of formulas. -/
theorem transfer {m : Nat} (Φ : (K : Nat) → m ≤ K → HTerm (Z.X K) .o)
    (nat : ∀ K K' (hK : m ≤ K) (h : K ≤ K'), rename (Z.lt K K' h) (Φ K hK) = Φ K' (Nat.le_trans hK h))
    {K1 K2 : Nat} (h1 : m ≤ K1) (h2 : m ≤ K2) (m1 : Z.M K1 (Φ K1 h1)) : Z.M K2 (Φ K2 h2) := by
  have a := (Z.M_lift (Nat.le_max_left K1 K2) _).1 m1
  rw [nat] at a
  rw [Z.M_lift (Nat.le_max_right K1 K2), nat]
  exact a

/-! ### Global terms: an 𝓛-term over the 𝓛-part of some stage -/

abbrev G (t : FTy) : Type := Σ n, Tm (Z.Lp n) t

/-- Stage lifting on the 𝓛-part. -/
noncomputable def qL (m N : Nat) (h : m ≤ N) : RenL (Z.Lp m) (Z.Lp N) := fun v => lpos (Z.lt m N h (canonR v))

theorem emb_qL {m N : Nat} (h : m ≤ N) (s : Tm (Z.Lp m) t) :
    emb canonR (renameL (Z.qL m N h) s) = rename (Z.lt m N h) (emb canonR s) := by
  exact (emb_renameL s _ canonR (fun v => Z.lt m N h (canonR v)) (fun v => canonR_lpos _)).trans
    (rename_emb s _ canonR _ (fun _ => rfl)).symm

theorem qL_trans {m n N : Nat} (h1 : m ≤ n) (h2 : n ≤ N) (h3 : m ≤ N) {u} (v : Var (Z.Lp m) u) :
    Z.qL n N h2 (Z.qL m n h1 v) = Z.qL m N h3 v := by
  simp only [qL, canonR_lpos, Z.lt_trans h1 h2 h3]

theorem qL_refl (m : Nat) (h : m ≤ m) {u} (v : Var (Z.Lp m) u) : Z.qL m m h v = v := by
  simp only [qL, Z.lt_refl, lpos_canonR]

variable {Z}

noncomputable def liftG (x : Z.G t) (N : Nat) (h : x.1 ≤ N) : Tm (Z.Lp N) t := renameL (Z.qL x.1 N h) x.2

/-- The embedded image of a global term at a stage. -/
noncomputable def E (x : Z.G t) (N : Nat) (h : x.1 ≤ N) : HTerm (Z.X N) (.L t) := emb canonR (liftG x N h)

theorem E_ren (x : Z.G t) (N : Nat) (h : x.1 ≤ N) : E x N h = rename (Z.lt x.1 N h) (emb canonR x.2) :=
  Z.emb_qL h x.2

theorem liftG_trans (x : Z.G t) {N N' : Nat} (h : x.1 ≤ N) (h' : N ≤ N') :
    renameL (Z.qL N N' h') (liftG x N h) = liftG x N' (Nat.le_trans h h') :=
  renameL_renameL _ _ _ _ (fun v => Z.qL_trans _ _ _ v)

theorem E_nat (x : Z.G t) {N N' : Nat} (h : x.1 ≤ N) (h' : N ≤ N') :
    rename (Z.lt N N' h') (E x N h) = E x N' (Nat.le_trans h h') := by
  rw [E_ren, E_ren, Z.ren_trans]

theorem liftG_self (x : Z.G t) (h : x.1 ≤ x.1) : liftG x x.1 h = x.2 :=
  renameL_id' _ _ (fun v => Z.qL_refl x.1 h v)

/-- Worlds: a world term at some stage. -/
abbrev Wd (Z : Seed) : Type := Σ n, HTerm (Z.X n) .w

noncomputable def wl (w : Z.Wd) (N : Nat) (h : w.1 ≤ N) : HTerm (Z.X N) .w := rename (Z.lt w.1 N h) w.2

theorem wl_nat (w : Z.Wd) {N N' : Nat} (h : w.1 ≤ N) (h' : N ≤ N') :
    rename (Z.lt N N' h') (wl w N h) = wl w N' (Nat.le_trans h h') := Z.ren_trans _ _ _ _

end Seed

/-! ### Derivation helpers -/

section dh
variable {T : Tm [] .s → Prop} {Γ' : List FTy} {Γ : List HTy} {hs : List (HTerm Γ .o)} {r : LRen Γ' Γ}

def oneR (v : HVar Γ (.L t)) : LRen [t] Γ
  | _, .zero => v

theorem cert_var (v : HVar Γ (.L t)) : Cert (.L t) (.var v) := ⟨[t], .var .zero, oneR v, rfl⟩

theorem cert_var0 : ∀ (a : HTy), Cert a (var0 : HTerm (a :: Γ) a)
  | .L _ => cert_var _
  | .w => trivial
  | .o => trivial

theorem inst_ren_wk (ρ : HRen Γ Δ) (P : HTerm Γ c) (t : HTerm Δ a) :
    inst (rename (liftR ρ) (wk P)) t = rename ρ P := by rw [rename_liftR_wk, inst_wk]

/-- `¬∀ ⊢ ∃¬`. -/
theorem d_ex_not {φ : HTerm (a :: Γ) .o} : DC T Γ (negH (.all a φ) :: hs) (.ex a (negH φ)) := by
  refine .byContra (.impE (.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..))) (.allI a (.byContra ?_)))
  refine .impE (φ := .ex a (rename (liftR (fun v => (HVar.succ v : HVar (a :: Γ) _))) (negH φ))) (.hyp ?_) ?_
  · exact List.mem_cons_of_mem _ (List.mem_map_of_mem (List.mem_cons_self ..))
  · refine .exI a var0 (cert_var0 a) ?_
    rw [inst_lift_var0]; exact .hyp (List.mem_cons_self ..)

theorem d_holds_rw {p q : HTerm Γ (.L .s)} {i : HTerm Γ .w} (e : DC T Γ hs (.eq (.L .s) p q))
    (d : DC T Γ hs (.holds p i)) : DC T Γ hs (.holds q i) := by
  have h := Deriv.subst (.L .s) (.holds var0 (wk i)) rfl e (by
    show DC T Γ hs (.holds p (inst (wk i) p)); rw [inst_wk]; exact d)
  show DC T Γ hs (.holds q i)
  have e2 : inst (HTerm.holds var0 (wk i)) q = .holds q i := by
    show HTerm.holds q (inst (wk i) q) = _; rw [inst_wk]
  rw [e2] at h; exact h

theorem d_act_rw {x y : HTerm Γ (.L .e)} {i : HTerm Γ .w} (e : DC T Γ hs (.eq (.L .e) x y))
    (d : DC T Γ hs (.act x i)) : DC T Γ hs (.act y i) := by
  have h := Deriv.subst (.L .e) (.act var0 (wk i)) rfl e (by
    show DC T Γ hs (.act x (inst (wk i) x)); rw [inst_wk]; exact d)
  have e2 : inst (HTerm.act var0 (wk i)) y = .act y i := by
    show HTerm.act y (inst (wk i) y) = _; rw [inst_wk]
  rw [e2] at h; exact h

/-- Congruence: an `𝓛`-context respects provable equality of `𝓛`-terms. -/
theorem d_cong (i : HTerm Γ .w) {x y : Tm Γ' a} (B : Tm (a :: Γ') b)
    (e : DC T Γ hs (.eq (.L a) (emb r x) (emb r y))) :
    DC T Γ hs (.eq (.L b) (emb r (instL B x)) (emb r (instL B y))) := by
  have hx : instL (Tm.eq b (wkL (instL B x)) B) x = .eq b (instL B x) (instL B x) := by
    show Tm.eq b (substL (sub0L x) (wkL (instL B x))) (instL B x) = _; rw [sub0L_wkL]
  have hy : instL (Tm.eq b (wkL (instL B x)) B) y = .eq b (instL B x) (instL B y) := by
    show Tm.eq b (substL (sub0L y) (wkL (instL B x))) (instL B y) = _; rw [sub0L_wkL]
  have d0 : DC T Γ hs (Lf r (instL (Tm.eq b (wkL (instL B x)) B) x) i) := by
    rw [hx]; exact L_eqI (Deriv.refl _ _)
  have d1 := L_leib _ e d0
  rw [hy] at d1
  exact L_eqE d1

theorem d_app (i : HTerm Γ .w) {f f' : Tm Γ' (.arr a b)} {x x' : Tm Γ' a}
    (ef : DC T Γ hs (.eq (.L (.arr a b)) (emb r f) (emb r f')))
    (ex : DC T Γ hs (.eq (.L a) (emb r x) (emb r x'))) :
    DC T Γ hs (.eq (.L b) (emb r (.app f x)) (emb r (.app f' x'))) := by
  have h1 := Deriv.allE (.L a) (emb r x) (Deriv.funApp ef) (cert_emb r x)
  have e1 : inst (HTerm.eq (.L b) (.appL (wk (emb r f)) var0) (.appL (wk (emb r f')) var0)) (emb r x) =
      .eq (.L b) (.appL (emb r f) (emb r x)) (.appL (emb r f') (emb r x)) := by
    show HTerm.eq _ (.appL (inst (wk (emb r f)) (emb r x)) (emb r x))
      (.appL (inst (wk (emb r f')) (emb r x)) (emb r x)) = _
    rw [inst_wk, inst_wk]
  rw [e1] at h1
  have h2 := d_cong i (Tm.app (wkL f') (.var .zero)) ex
  have e2 : ∀ z : Tm Γ' a, instL (Tm.app (wkL f') (.var .zero)) z = .app f' z := fun z => by
    show Tm.app (substL (sub0L z) (wkL f')) z = _; rw [sub0L_wkL]
  rw [e2, e2] at h2
  exact Deriv.trans _ h1 h2

end dh

/-! ### The canonical model -/

namespace Seed
variable {Z : Seed}

/-- A world term at every stage. -/
noncomputable def wK (Z : Seed) (K : Nat) : HTerm (Z.X K) .w := rename (Z.lt 0 K (Nat.zero_le K)) Z.i0

theorem E_mk (n : Nat) (s : Tm (Z.Lp n) t) (K : Nat) (h : n ≤ K) :
    E (⟨n, s⟩ : Z.G t) K h = rename (Z.lt n K h) (emb canonR s) := E_ren _ _ _

def Eqv (x y : Z.G t) : Prop :=
  ∀ K (hx : x.1 ≤ K) (hy : y.1 ≤ K), Z.M K (.eq (.L t) (E x K hx) (E y K hy))

theorem eqv_at {x y : Z.G t} {K : Nat} (hx : x.1 ≤ K) (hy : y.1 ≤ K)
    (m : Z.M K (.eq (.L t) (E x K hx) (E y K hy))) : Eqv x y := fun K' hx' hy' =>
  Z.transfer (m := max x.1 y.1)
    (fun K hK => .eq (.L t) (E x K (Nat.le_trans (Nat.le_max_left _ _) hK))
      (E y K (Nat.le_trans (Nat.le_max_right _ _) hK)))
    (fun K K' hK h => by
      show HTerm.eq _ (rename _ (E x K _)) (rename _ (E y K _)) = _
      rw [E_nat, E_nat])
    (Nat.max_le.2 ⟨hx, hy⟩) (Nat.max_le.2 ⟨hx', hy'⟩) m

theorem eqv_refl (x : Z.G t) : Eqv x x :=
  eqv_at (Nat.le_refl _) (Nat.le_refl _) (Z.M_of (.refl _ _))

theorem eqv_symm {x y : Z.G t} (h : Eqv x y) : Eqv y x :=
  eqv_at (K := max y.1 x.1) (Nat.le_max_left _ _) (Nat.le_max_right _ _)
    (Z.M_mp (h _ (Nat.le_max_right _ _) (Nat.le_max_left _ _)) (.symm _ (.hyp (List.mem_cons_self ..))))

theorem eqv_trans {x y z : Z.G t} (h1 : Eqv x y) (h2 : Eqv y z) : Eqv x z := by
  have hx : x.1 ≤ max (max x.1 y.1) z.1 := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have hy : y.1 ≤ max (max x.1 y.1) z.1 := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  have hz : z.1 ≤ max (max x.1 y.1) z.1 := Nat.le_max_right _ _
  exact eqv_at hx hz (Z.M_mp2 (h1 _ hx hy) (h2 _ hy hz)
    (.trans _ (.hyp (List.mem_cons_self ..)) (.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))

instance setoidG (Z : Seed) (t : FTy) : Setoid (Z.G t) where
  r := Eqv
  iseqv := ⟨eqv_refl, eqv_symm, eqv_trans⟩

abbrev Car (Z : Seed) (t : FTy) : Type := Quotient (setoidG Z t)

abbrev cls (x : Z.G t) : Z.Car t := Quotient.mk (setoidG Z t) x

theorem cls_eq {x y : Z.G t} : cls x = cls y ↔ Eqv x y := ⟨Quotient.exact, fun h => Quotient.sound h⟩

/-- A global term and its lift to a later stage are equal. -/
theorem cls_lift (x : Z.G t) (N : Nat) (h : x.1 ≤ N) : cls (⟨N, liftG x N h⟩ : Z.G t) = cls x := by
  apply cls_eq.2
  refine eqv_at (K := N) (Nat.le_refl N) h ?_
  rw [E_mk, Z.ren_refl]
  exact Z.M_of (.refl _ _)

/-! #### Truth of propositions, actuality, accessibility -/

def prF (p : Z.G .s) (w : Z.Wd) : Prop :=
  Z.M (max p.1 w.1) (.holds (E p _ (Nat.le_max_left _ _)) (wl w _ (Nat.le_max_right _ _)))

theorem prF_iff (p : Z.G .s) (w : Z.Wd) (K : Nat) (hp : p.1 ≤ K) (hw : w.1 ≤ K) :
    prF p w ↔ Z.M K (.holds (E p K hp) (wl w K hw)) := by
  have nat : ∀ K K' (hK : max p.1 w.1 ≤ K) (h : K ≤ K'),
      rename (Z.lt K K' h) (HTerm.holds (E p K (Nat.le_trans (Nat.le_max_left _ _) hK))
        (wl w K (Nat.le_trans (Nat.le_max_right _ _) hK))) =
      .holds (E p K' (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_trans hK h)))
        (wl w K' (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans hK h))) := fun K K' hK h => by
    show HTerm.holds (rename _ (E p K _)) (rename _ (wl w K _)) = _
    rw [E_nat, wl_nat]
  exact ⟨Z.transfer _ nat (Nat.le_refl _) (Nat.max_le.2 ⟨hp, hw⟩),
    Z.transfer _ nat (Nat.max_le.2 ⟨hp, hw⟩) (Nat.le_refl _)⟩

theorem prF_resp {p q : Z.G .s} (h : Eqv p q) (w : Z.Wd) (hp : prF p w) : prF q w := by
  let K := max (max p.1 q.1) w.1
  have h1 : p.1 ≤ K := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have h2 : q.1 ≤ K := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  have h3 : w.1 ≤ K := Nat.le_max_right _ _
  rw [prF_iff p w K h1 h3] at hp
  rw [prF_iff q w K h2 h3]
  exact Z.M_mp2 (h K h1 h2) hp (d_holds_rw (.hyp (List.mem_cons_self ..))
    (.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..))))

def actF (x : Z.G .e) (w : Z.Wd) : Prop :=
  Z.M (max x.1 w.1) (.act (E x _ (Nat.le_max_left _ _)) (wl w _ (Nat.le_max_right _ _)))

theorem actF_iff (x : Z.G .e) (w : Z.Wd) (K : Nat) (hx : x.1 ≤ K) (hw : w.1 ≤ K) :
    actF x w ↔ Z.M K (.act (E x K hx) (wl w K hw)) := by
  have nat : ∀ K K' (hK : max x.1 w.1 ≤ K) (h : K ≤ K'),
      rename (Z.lt K K' h) (HTerm.act (E x K (Nat.le_trans (Nat.le_max_left _ _) hK))
        (wl w K (Nat.le_trans (Nat.le_max_right _ _) hK))) =
      .act (E x K' (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_trans hK h)))
        (wl w K' (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans hK h))) := fun K K' hK h => by
    show HTerm.act (rename _ (E x K _)) (rename _ (wl w K _)) = _
    rw [E_nat, wl_nat]
  exact ⟨Z.transfer _ nat (Nat.le_refl _) (Nat.max_le.2 ⟨hx, hw⟩),
    Z.transfer _ nat (Nat.max_le.2 ⟨hx, hw⟩) (Nat.le_refl _)⟩

theorem actF_resp {x y : Z.G .e} (h : Eqv x y) (w : Z.Wd) (hp : actF x w) : actF y w := by
  let K := max (max x.1 y.1) w.1
  have h1 : x.1 ≤ K := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have h2 : y.1 ≤ K := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  have h3 : w.1 ≤ K := Nat.le_max_right _ _
  rw [actF_iff x w K h1 h3] at hp
  rw [actF_iff y w K h2 h3]
  exact Z.M_mp2 (h K h1 h2) hp (d_act_rw (.hyp (List.mem_cons_self ..))
    (.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..))))

def RF (w v : Z.Wd) : Prop :=
  Z.M (max w.1 v.1) (.rel (wl w _ (Nat.le_max_left _ _)) (wl v _ (Nat.le_max_right _ _)))

theorem RF_iff (w v : Z.Wd) (K : Nat) (hw : w.1 ≤ K) (hv : v.1 ≤ K) :
    RF w v ↔ Z.M K (.rel (wl w K hw) (wl v K hv)) := by
  have nat : ∀ K K' (hK : max w.1 v.1 ≤ K) (h : K ≤ K'),
      rename (Z.lt K K' h) (HTerm.rel (wl w K (Nat.le_trans (Nat.le_max_left _ _) hK))
        (wl v K (Nat.le_trans (Nat.le_max_right _ _) hK))) =
      .rel (wl w K' (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_trans hK h)))
        (wl v K' (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans hK h))) := fun K K' hK h => by
    show HTerm.rel (rename _ (wl w K _)) (rename _ (wl v K _)) = _
    rw [wl_nat, wl_nat]
  exact ⟨Z.transfer _ nat (Nat.le_refl _) (Nat.max_le.2 ⟨hw, hv⟩),
    Z.transfer _ nat (Nat.max_le.2 ⟨hw, hv⟩) (Nat.le_refl _)⟩

/-! #### Application, extensionality, injectivity of truth -/

abbrev apF (f : Z.G (.arr a b)) (x : Z.G a) : Z.G b :=
  ⟨max f.1 x.1, .app (liftG f _ (Nat.le_max_left _ _)) (liftG x _ (Nat.le_max_right _ _))⟩

theorem E_apF (f : Z.G (.arr a b)) (x : Z.G a) (K : Nat) (h : max f.1 x.1 ≤ K) :
    E (apF f x) K h = emb canonR (.app (liftG f K (Nat.le_trans (Nat.le_max_left _ _) h))
      (liftG x K (Nat.le_trans (Nat.le_max_right _ _) h))) := by
  show emb canonR (Tm.app (renameL (Z.qL (max f.1 x.1) K h) (liftG f _ (Nat.le_max_left _ _)))
    (renameL (Z.qL (max f.1 x.1) K h) (liftG x _ (Nat.le_max_right _ _)))) = _
  rw [liftG_trans f (Nat.le_max_left f.1 x.1) h, liftG_trans x (Nat.le_max_right f.1 x.1) h]

theorem apF_resp {f f' : Z.G (.arr a b)} {x x' : Z.G a} (hf : Eqv f f') (hx : Eqv x x') :
    Eqv (apF f x) (apF f' x') := by
  let K := max (max f.1 x.1) (max f'.1 x'.1)
  have k1 : max f.1 x.1 ≤ K := Nat.le_max_left _ _
  have k2 : max f'.1 x'.1 ≤ K := Nat.le_max_right _ _
  have h1 : f.1 ≤ K := Nat.le_trans (Nat.le_max_left _ _) k1
  have h2 : f'.1 ≤ K := Nat.le_trans (Nat.le_max_left _ _) k2
  have h3 : x.1 ≤ K := Nat.le_trans (Nat.le_max_right _ _) k1
  have h4 : x'.1 ≤ K := Nat.le_trans (Nat.le_max_right _ _) k2
  refine eqv_at k1 k2 ?_
  rw [E_apF, E_apF]
  have d : Z.D K [.eq (.L (.arr a b)) (E f K h1) (E f' K h2), .eq (.L a) (E x K h3) (E x' K h4)]
      (.eq (.L b) (emb canonR (.app (liftG f K h1) (liftG x K h3)))
        (emb canonR (.app (liftG f' K h2) (liftG x' K h4)))) :=
    d_app (Z.wK K) (.hyp (List.mem_cons_self ..)) (.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  exact Z.M_mp2 (hf K h1 h2) (hx K h3 h4) d

theorem M_eqo {N : Nat} {A B : HTerm (Z.X N) .o} (h : Z.M N A ↔ Z.M N B) : Z.M N (.eq .o A B) := by
  by_cases ha : Z.M N A
  · exact Z.M_mp2 ha (h.1 ha) (.propExt (.hyp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self ..)))) (.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
  · have hb : ¬ Z.M N B := fun hb => ha (h.2 hb)
    exact Z.M_mp2 (Z.M_neg.2 ha) (Z.M_neg.2 hb)
      (.propExt (.exFalso (.impE (.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
        (.hyp (List.mem_cons_self ..))))
        (.exFalso (.impE (.hyp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
        (.hyp (List.mem_cons_self ..)))))

theorem prInj (p q : Z.G .s) (h : ∀ w, prF p w ↔ prF q w) : Eqv p q := by
  let K := max p.1 q.1
  have hp : p.1 ≤ K := Nat.le_max_left _ _
  have hq : q.1 ≤ K := Nat.le_max_right _ _
  refine eqv_at hp hq ?_
  rcases Z.M_max K (.eq (.L .s) (E p K hp) (E q K hq)) with m | m
  · exact m
  exfalso
  have m1 : Z.M K (negH (.all .w (.eq .o (.holds (wk (E p K hp)) var0) (.holds (wk (E q K hq)) var0)))) :=
    Z.M_mp m (.impI (.impE (.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      (.wExt (.hyp (List.mem_cons_self ..)))))
  have m2 := Z.M_mp m1 d_ex_not
  obtain ⟨N, hN, x, mx⟩ := mem_henkin Z.T Z.Γ0 Z.hs0 Z.hc m2
  have e : inst (rename (liftR (Z.lt K N hN))
      (negH (.eq .o (.holds (wk (E p K hp)) var0) (.holds (wk (E q K hq)) var0)))) (.var x) =
      negH (.eq .o (.holds (E p N (Nat.le_trans hp hN)) (.var x)) (.holds (E q N (Nat.le_trans hq hN)) (.var x))) := by
    show HTerm.imp (.eq .o (.holds (inst (rename (liftR _) (wk (E p K hp))) (.var x)) (.var x))
      (.holds (inst (rename (liftR _) (wk (E q K hq))) (.var x)) (.var x))) .bot = _
    rw [inst_ren_wk, inst_ren_wk, E_nat, E_nat]; rfl
  have mx' : Z.M N _ := mx
  rw [e] at mx'
  let w : Z.Wd := ⟨N, .var x⟩
  have hw : wl w N (Nat.le_refl N) = .var x := Z.ren_refl _ _ _
  have h1 := prF_iff p w N (Nat.le_trans hp hN) (Nat.le_refl N)
  have h2 := prF_iff q w N (Nat.le_trans hq hN) (Nat.le_refl N)
  rw [hw] at h1 h2
  exact Z.M_not_both (M_eqo (h1.symm.trans ((h w).trans h2))) mx'

theorem apExt (f g : Z.G (.arr a b)) (h : ∀ x : Z.G a, Eqv (apF f x) (apF g x)) : Eqv f g := by
  let K := max f.1 g.1
  have hf : f.1 ≤ K := Nat.le_max_left _ _
  have hg : g.1 ≤ K := Nat.le_max_right _ _
  refine eqv_at hf hg ?_
  rcases Z.M_max K (.eq (.L (.arr a b)) (E f K hf) (E g K hg)) with m | m
  · exact m
  exfalso
  have m1 : Z.M K (negH (.all (.L a) (.eq (.L b) (.appL (wk (E f K hf)) var0) (.appL (wk (E g K hg)) var0)))) :=
    Z.M_mp m (.impI (.impE (.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      (.funExt (.hyp (List.mem_cons_self ..)))))
  have m2 := Z.M_mp m1 d_ex_not
  obtain ⟨N, hN, y, my⟩ := mem_henkin Z.T Z.Γ0 Z.hs0 Z.hc m2
  have e : inst (rename (liftR (Z.lt K N hN))
      (negH (.eq (.L b) (.appL (wk (E f K hf)) var0) (.appL (wk (E g K hg)) var0)))) (.var y) =
      negH (.eq (.L b) (.appL (E f N (Nat.le_trans hf hN)) (.var y)) (.appL (E g N (Nat.le_trans hg hN)) (.var y))) := by
    show HTerm.imp (.eq (.L b) (.appL (inst (rename (liftR _) (wk (E f K hf))) (.var y)) (.var y))
      (.appL (inst (rename (liftR _) (wk (E g K hg))) (.var y)) (.var y))) .bot = _
    rw [inst_ren_wk, inst_ren_wk, E_nat, E_nat]; rfl
  have my' : Z.M N _ := my
  rw [e] at my'
  let yv : Z.G a := ⟨N, .var (lpos y)⟩
  have ey : E yv N (Nat.le_refl N) = .var y := by
    rw [E_mk, Z.ren_refl]; show HTerm.var (canonR (lpos y)) = _; rw [canonR_lpos]
  have k := h yv N (Nat.max_le.2 ⟨Nat.le_trans hf hN, Nat.le_refl N⟩) (Nat.max_le.2 ⟨Nat.le_trans hg hN, Nat.le_refl N⟩)
  rw [E_apF, E_apF] at k
  have e2 : ∀ (u : Z.G (.arr a b)) (hu : u.1 ≤ N) (hu' : max u.1 yv.1 ≤ N),
      emb canonR (Tm.app (liftG u N (Nat.le_trans (Nat.le_max_left _ _) hu'))
        (liftG yv N (Nat.le_trans (Nat.le_max_right _ _) hu'))) = .appL (E u N hu) (.var y) := by
    intro u hu hu'
    show HTerm.appL (E u N _) (E yv N _) = _
    rw [ey]
  rw [e2 f (Nat.le_trans hf hN) (Nat.max_le.2 ⟨Nat.le_trans hf hN, Nat.le_refl N⟩),
    e2 g (Nat.le_trans hg hN) (Nat.max_le.2 ⟨Nat.le_trans hg hN, Nat.le_refl N⟩)] at k
  exact Z.M_not_both k my'

end Seed

/-- **The canonical v4 model.** -/
noncomputable def VMc (Z : Seed) : VM Z.Wd where
  R := Seed.RF
  C := Z.Car
  act := Quotient.lift (s := Seed.setoidG Z .e) (fun x w => Seed.actF x w)
    (fun _ _ h => funext fun w => propext ⟨Seed.actF_resp h w, Seed.actF_resp (Seed.eqv_symm h) w⟩)
  pr := Quotient.lift (s := Seed.setoidG Z .s) (fun p w => Seed.prF p w)
    (fun _ _ h => funext fun w => propext ⟨Seed.prF_resp h w, Seed.prF_resp (Seed.eqv_symm h) w⟩)
  pr_inj := fun p q => Quotient.inductionOn₂ (s₁ := Seed.setoidG Z .s) (s₂ := Seed.setoidG Z .s) p q
    fun p q h => Seed.cls_eq.2 (Seed.prInj p q (fun w => Iff.of_eq (congrFun h w)))
  ap := fun {a b} => Quotient.lift₂ (s₁ := Seed.setoidG Z (.arr a b)) (s₂ := Seed.setoidG Z a)
    (fun f x => Seed.cls (Seed.apF f x)) (fun _ _ _ _ hf hx => Seed.cls_eq.2 (Seed.apF_resp hf hx))
  ap_ext := fun {a b} f g => Quotient.inductionOn₂ (s₁ := Seed.setoidG Z (.arr a b))
    (s₂ := Seed.setoidG Z (.arr a b)) f g fun f g h => Seed.cls_eq.2 (Seed.apExt f g
      (fun x => Seed.cls_eq.1 (h (Seed.cls x))))
  P := Seed.cls (⟨0, .pos⟩ : Z.G th)

/-! ### The 𝓛-general structure of the canonical model -/

namespace Seed
variable {Z : Seed}

abbrev Tr (K : Nat) (φ : Tm (Z.Lp K) .s) (i : HTerm (Z.X K) .w) : Prop := Z.M K (Lf canonR φ i)

theorem tr_top {K : Nat} {i : HTerm (Z.X K) .w} : Tr K .top i := Z.M_of L_topI

theorem tr_bot {K : Nat} {i : HTerm (Z.X K) .w} : ¬ Tr K .bot i := fun h =>
  Z.M_bot (Z.M_mp h (L_botE (.hyp (List.mem_cons_self ..))))

theorem tr_neg {K : Nat} {x : Tm (Z.Lp K) .s} {i : HTerm (Z.X K) .w} : Tr K (.neg x) i ↔ ¬ Tr K x i :=
  ⟨fun h hx => Z.M_bot (Z.M_mp2 h hx (.impE (L_negE (.hyp (List.mem_cons_self ..)))
      (.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..))))),
   fun h => Z.M_mp (Z.M_neg.2 h) (L_negI (.hyp (List.mem_cons_self ..)))⟩

theorem tr_and {K : Nat} {x y : Tm (Z.Lp K) .s} {i : HTerm (Z.X K) .w} :
    Tr K (.and x y) i ↔ Tr K x i ∧ Tr K y i :=
  ⟨fun h => ⟨Z.M_mp h (.andL (L_andE (.hyp (List.mem_cons_self ..)))),
      Z.M_mp h (.andR (L_andE (.hyp (List.mem_cons_self ..))))⟩,
   fun h => Z.M_mp2 h.1 h.2 (L_andI (.andI (.hyp (List.mem_cons_self ..))
      (.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))⟩

theorem tr_or {K : Nat} {x y : Tm (Z.Lp K) .s} {i : HTerm (Z.X K) .w} :
    Tr K (.or x y) i ↔ Tr K x i ∨ Tr K y i := by
  constructor
  · intro h
    by_cases hx : Tr K x i
    · exact .inl hx
    by_cases hy : Tr K y i
    · exact .inr hy
    exfalso
    refine Z.M_bot (Z.M_deriv (hs := [Lf canonR (.or x y) i, negH (Lf canonR x i), negH (Lf canonR y i)])
      (fun z m => ?_) (.orE (L_orE (.hyp (List.mem_cons_self ..)))
        (.impE (.hyp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
          (.hyp (List.mem_cons_self ..)))
        (.impE (.hyp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_self ..))))) (.hyp (List.mem_cons_self ..)))))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at m
    rcases m with rfl | rfl | rfl
    · exact h
    · exact Z.M_neg.2 hx
    · exact Z.M_neg.2 hy
  · rintro (h | h)
    · exact Z.M_mp h (L_orI (.orL (.hyp (List.mem_cons_self ..))))
    · exact Z.M_mp h (L_orI (.orR (.hyp (List.mem_cons_self ..))))

theorem tr_imp {K : Nat} {x y : Tm (Z.Lp K) .s} {i : HTerm (Z.X K) .w} :
    Tr K (.imp x y) i ↔ (Tr K x i → Tr K y i) := by
  constructor
  · intro h hx
    exact Z.M_mp2 h hx (.impE (L_impE (.hyp (List.mem_cons_self ..)))
      (.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
  · intro h
    by_cases hx : Tr K x i
    · exact Z.M_mp (h hx) (L_impI (.impI (.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))
    · exact Z.M_mp (Z.M_neg.2 hx) (L_impI (.impI (.exFalso (.impE
        (.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..))) (.hyp (List.mem_cons_self ..))))))

/-! #### Environments -/

def stg : {Γ' : List FTy} → VEnv (VMc Z) Γ' → Nat
  | [], _ => 0
  | t :: _, ρ => max (qout (s := setoidG Z t) ρ.1).1 (stg ρ.2)

def subE : {Γ' : List FTy} → (ρ : VEnv (VMc Z) Γ') → (K : Nat) → stg ρ ≤ K → {t : FTy} →
    Var Γ' t → Tm (Z.Lp K) t
  | u :: _, ρ, K, h, _, .zero => liftG (qout (s := setoidG Z u) ρ.1) K (Nat.le_trans (Nat.le_max_left _ _) h)
  | _ :: _, ρ, K, h, _, .succ i => subE ρ.2 K (Nat.le_trans (Nat.le_max_right _ _) h) i

theorem sub_nat : ∀ {Γ' : List FTy} (ρ : VEnv (VMc Z) Γ') {K N : Nat} (hK : stg ρ ≤ K) (h : K ≤ N) {t : FTy}
    (i : Var Γ' t), renameL (Z.qL K N h) (subE ρ K hK i) = subE ρ N (Nat.le_trans hK h) i
  | _ :: _, _, _, _, _, _, _, .zero => liftG_trans _ _ _
  | _ :: _, ρ, _, _, _, h, _, .succ i => sub_nat ρ.2 _ h i

theorem ev_nat (ρ : VEnv (VMc Z) Γ') {K N : Nat} (hK : stg ρ ≤ K) (h : K ≤ N) (tm : Tm Γ' t) :
    renameL (Z.qL K N h) (substL (subE ρ K hK) tm) = substL (subE ρ N (Nat.le_trans hK h)) tm :=
  renameL_substL _ _ _ _ (fun v => sub_nat ρ hK h v)

abbrev evc (tm : Tm Γ' t) (ρ : VEnv (VMc Z) Γ') : Z.G t := ⟨stg ρ, substL (subE ρ (stg ρ) (Nat.le_refl _)) tm⟩

theorem E_ev (tm : Tm Γ' t) (ρ : VEnv (VMc Z) Γ') (K : Nat) (h : stg ρ ≤ K) :
    E (evc tm ρ) K h = emb canonR (substL (subE ρ K h) tm) :=
  congrArg (emb canonR) (ev_nat ρ (Nat.le_refl _) h tm)

theorem pr_ev (φ : Tm Γ' .s) (ρ : VEnv (VMc Z) Γ') (w : Z.Wd) (K : Nat) (hK : stg ρ ≤ K) (hw : w.1 ≤ K) :
    (VMc Z).pr (cls (evc φ ρ)) w ↔ Tr K (substL (subE ρ K hK) φ) (wl w K hw) := by
  have := prF_iff (evc φ ρ) w K hK hw
  rw [E_ev] at this
  exact this

theorem lift_tr {K N : Nat} (h : K ≤ N) (φ : Tm (Z.Lp K) .s) (i : HTerm (Z.X K) .w) :
    rename (Z.lt K N h) (Lf canonR φ i) = Lf canonR (renameL (Z.qL K N h) φ) (rename (Z.lt K N h) i) := by
  show HTerm.holds (rename _ (emb canonR φ)) (rename _ i) = _
  rw [← Z.emb_qL]; rfl

end Seed

theorem substL_congr (tm : Tm Γ t) {s s' : SubL Γ Δ} (h : ∀ {u} (v : Var Γ u), s v = s' v) :
    substL s tm = substL s' tm := by
  have := substL_renameL tm (fun v => v) s s' (fun v => h v)
  rwa [renameL_id' _ _ (fun _ => rfl)] at this

theorem substL_var (q : RenL Γ Δ) (tm : Tm Γ t) : substL (fun v => .var (q v)) tm = renameL q tm := by
  have := substL_renameL tm q (fun v => .var v) (fun v => .var (q v)) (fun _ => rfl)
  rw [substL_id _ _ (fun _ => rfl)] at this
  exact this.symm

namespace Seed
variable {Z : Seed}

theorem subE_cons (x : Z.Car u) (ρ : VEnv (VMc Z) Γ') (K : Nat) (h : stg (Γ' := u :: Γ') (x, ρ) ≤ K) (b : Tm (u :: Γ') t) :
    substL (subE (Γ' := u :: Γ') (x, ρ) K h) b =
      substL (consL (liftG (qout (s := setoidG Z u) x) K (Nat.le_trans (Nat.le_max_left _ _) h))
        (subE ρ K (Nat.le_trans (Nat.le_max_right _ _) h))) b :=
  substL_congr b (fun v => by cases v <;> rfl)

theorem cls_subE : ∀ {Γ' : List FTy} (ρ : VEnv (VMc Z) Γ') (K : Nat) (h : stg ρ ≤ K) {t : FTy} (i : Var Γ' t),
    cls (⟨K, subE ρ K h i⟩ : Z.G t) = i.vget (VMc Z) ρ
  | u :: _, ρ, K, h, _, .zero => (cls_lift _ _ _).trans (qout_eq (s := setoidG Z u) ρ.1)
  | _ :: _, ρ, K, h, _, .succ i => cls_subE ρ.2 K _ i

theorem ev_var (i : Var Γ' t) (ρ : VEnv (VMc Z) Γ') : cls (evc (.var i) ρ) = i.vget (VMc Z) ρ :=
  cls_subE ρ _ _ i

theorem ev_app (F : Tm Γ' (.arr a b)) (x : Tm Γ' a) (ρ : VEnv (VMc Z) Γ') :
    cls (evc (.app F x) ρ) = (VMc Z).ap (cls (evc F ρ)) (cls (evc x ρ)) := by
  show cls (evc (.app F x) ρ) = cls (apF (evc F ρ) (evc x ρ))
  apply cls_eq.2
  refine eqv_at (K := max (stg ρ) (stg ρ)) (Nat.le_max_left _ _) (Nat.le_refl _) ?_
  rw [E_ev, E_apF]
  show Z.M _ (.eq _ (emb canonR (Tm.app (substL _ F) (substL _ x))) (emb canonR (Tm.app
    (renameL (Z.qL (stg ρ) _ _) (substL _ F)) (renameL (Z.qL (stg ρ) _ _) (substL _ x)))))
  rw [ev_nat, ev_nat]
  exact Z.M_of (.refl _ _)

theorem ev_lam (t : Tm (a :: Γ') b) (ρ : VEnv (VMc Z) Γ') (x : Z.Car a) :
    (VMc Z).ap (cls (evc (.lam t) ρ)) x = cls (evc (Γ' := a :: Γ') t (x, ρ)) := by
  induction x using Quotient.inductionOn (s := setoidG Z a) with
  | h u =>
  show cls (apF (evc (.lam t) ρ) u) = _
  apply cls_eq.2
  let K := max (max (stg ρ) u.1) (stg (Γ' := a :: Γ') (cls u, ρ))
  have k1 : max (stg ρ) u.1 ≤ K := Nat.le_max_left _ _
  have k2 : stg (Γ' := a :: Γ') (cls u, ρ) ≤ K := Nat.le_max_right _ _
  have hS : stg ρ ≤ K := Nat.le_trans (Nat.le_max_left _ _) k1
  have hu : u.1 ≤ K := Nat.le_trans (Nat.le_max_right _ _) k1
  refine eqv_at k1 k2 ?_
  rw [E_apF, E_ev, subE_cons]
  show Z.M K (.eq _ (emb canonR (Tm.app (renameL (Z.qL (stg ρ) K _) (substL _ (Tm.lam t))) (liftG u K hu))) _)
  rw [ev_nat]
  -- β, then replace the representative
  have e1 := Deriv.betaL (T := Z.T) (ok := fun a t => Cert a t) (hs := [])
    (emb (liftL canonR) (substL (liftSL (subE ρ K hS)) t)) (emb canonR (liftG u K hu))
  rw [inst_emb, instL_liftSL] at e1
  have q := mk_qout (s := setoidG Z a) u
  have e2 : Z.M K (.eq (.L a) (E u K hu) (E (qout (s := setoidG Z a) (cls u)) K
      (Nat.le_trans (Nat.le_max_left _ _) k2))) := eqv_symm q K _ _
  have e3 := Z.M_mp e2 (d_cong (r := canonR) (Z.wK K) (substL (liftSL (subE ρ K hS)) t) (.hyp (List.mem_cons_self ..)))
  rw [instL_liftSL, instL_liftSL] at e3
  exact Z.M_mp e3 (.trans _ (e1.weaken (fun _ m => nomatch m)) (.hyp (List.mem_cons_self ..)))

theorem ev_pos (ρ : VEnv (VMc Z) Γ') : cls (evc .pos ρ) = (VMc Z).P :=
  cls_eq.2 (eqv_at (K := stg ρ) (Nat.le_refl _) (Nat.zero_le _) (Z.M_of (.refl _ _)))

theorem ev_eq (a : FTy) (x y : Tm Γ' a) (ρ : VEnv (VMc Z) Γ') (w : Z.Wd) :
    (VMc Z).pr (cls (evc (.eq a x y) ρ)) w ↔ cls (evc x ρ) = cls (evc y ρ) := by
  let K := max (stg ρ) w.1
  have hS : stg ρ ≤ K := Nat.le_max_left _ _
  rw [pr_ev _ ρ w K hS (Nat.le_max_right _ _), cls_eq]
  constructor
  · intro h
    refine eqv_at hS hS ?_
    rw [E_ev, E_ev]
    exact Z.M_mp h (L_eqE (.hyp (List.mem_cons_self ..)))
  · intro h
    have := h K hS hS
    rw [E_ev, E_ev] at this
    exact Z.M_mp this (L_eqI (.hyp (List.mem_cons_self ..)))

end Seed

/-! #### Quantifier and box clauses -/

section qh
variable {T : Tm [] .s → Prop} {Γ'' : List FTy} {Γ : List HTy} {hs : List (HTerm Γ .o)}
  {r : LRen Γ'' Γ} {i : HTerm Γ .w}

theorem L_all_hyp {b : Tm (a :: Γ'') .s} :
    DC T Γ (.all (.L a) (Lf (liftL r) b (wk i)) :: hs) (Lf r (.all a b) i) :=
  Deriv.betaWI _ _ (by rw [body_all]; exact .hyp (List.mem_cons_self ..))

theorem L_allE_hyp {b : Tm (.e :: Γ'') .s} :
    DC T Γ (.all (.L .e) (.imp (.act var0 (wk i)) (Lf (liftL r) b (wk i))) :: hs) (Lf r (.allE b) i) :=
  Deriv.betaWI _ _ (by rw [body_allE]; exact .hyp (List.mem_cons_self ..))

theorem L_box_hyp {x : Tm Γ'' .s} :
    DC T Γ (.all .w (.imp (.rel (wk i) var0) (Lf (shL r) x var0)) :: hs) (Lf r (.box x) i) :=
  Deriv.betaWI _ _ (by rw [body_box]; exact .hyp (List.mem_cons_self ..))

theorem L_ex_hyp {b : Tm (a :: Γ'') .s} :
    DC T Γ (Lf r (.ex a b) i :: hs) (.ex (.L a) (Lf (liftL r) b (wk i))) := by
  have h0 : DC T Γ (Lf r (.ex a b) i :: hs) (Lf r (.ex a b) i) := .hyp (List.mem_cons_self ..)
  have := Deriv.betaWE _ _ h0
  rwa [body_ex] at this

theorem L_exE_hyp {b : Tm (.e :: Γ'') .s} :
    DC T Γ (Lf r (.exE b) i :: hs) (.ex (.L .e) (.and (.act var0 (wk i)) (Lf (liftL r) b (wk i)))) := by
  have h0 : DC T Γ (Lf r (.exE b) i :: hs) (Lf r (.exE b) i) := .hyp (List.mem_cons_self ..)
  have := Deriv.betaWE _ _ h0
  rwa [body_exE] at this

/-- From `¬φ'`, where `φ'` implies `φ`, get `¬φ`... in the form used below. -/
theorem d_neg_of {φ ψ : HTerm Γ .o} (d : DC T Γ (ψ :: hs) φ) : DC T Γ (negH φ :: hs) (negH ψ) :=
  .impI (.impE (.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    ((d.weaken (fun x m => by
      rcases List.mem_cons.1 m with rfl | m
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ m)))))

end qh

theorem inst_act (ρ : HRen Γ Δ) (j : HTerm Γ .w) (t : HTerm Δ (.L .e)) :
    inst (rename (liftR ρ) (HTerm.act var0 (wk j))) t = .act t (rename ρ j) := by
  show HTerm.act t (inst (rename (liftR ρ) (wk j)) t) = _; rw [inst_ren_wk]

theorem inst_rel (ρ : HRen Γ Δ) (j : HTerm Γ .w) (t : HTerm Δ .w) :
    inst (rename (liftR ρ) (HTerm.rel (wk j) var0)) t = .rel (rename ρ j) t := by
  show HTerm.rel (inst (rename (liftR ρ) (wk j)) t) t = _; rw [inst_ren_wk]

namespace Seed
variable {Z : Seed}

theorem M_negimp {N : Nat} {A B : HTerm (Z.X N) .o} (h : Z.M N (negH (.imp A B))) : Z.M N A ∧ ¬ Z.M N B := by
  refine ⟨Z.M_mp h (.byContra (.impE (.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    (.impI (.exFalso (.impE (.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..))) (.hyp (List.mem_cons_self ..))))))),
    fun hb => Z.M_not_both (Z.M_mp hb (.impI (.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..))))) h⟩

theorem M_and {N : Nat} {A B : HTerm (Z.X N) .o} (h : Z.M N (.and A B)) : Z.M N A ∧ Z.M N B :=
  ⟨Z.M_mp h (.andL (.hyp (List.mem_cons_self ..))), Z.M_mp h (.andR (.hyp (List.mem_cons_self ..)))⟩

theorem tr_lift {K N : Nat} (h : K ≤ N) (φ : Tm (Z.Lp K) .s) (i : HTerm (Z.X K) .w) :
    Tr K φ i ↔ Tr N (renameL (Z.qL K N h) φ) (rename (Z.lt K N h) i) := by
  show Z.M K _ ↔ Z.M N _
  rw [Z.M_lift h, lift_tr]

theorem tr_cons {K : Nat} (B : Tm (a :: Γ') .s) (σ : SubL Γ' (Z.Lp K)) {U U' : Tm (Z.Lp K) a}
    (e : Z.M K (.eq (.L a) (emb canonR U) (emb canonR U'))) {i : HTerm (Z.X K) .w}
    (h : Tr K (substL (consL U σ) B) i) : Tr K (substL (consL U' σ) B) i := by
  have h' : Z.M K (Lf canonR (instL (substL (liftSL σ) B) U) i) := by rw [instL_liftSL]; exact h
  have := Z.M_mp2 e h' (L_leib _ (.hyp (List.mem_cons_self ..)) (.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
  rwa [instL_liftSL] at this

theorem henkin_inst {K N : Nat} (hN : K ≤ N) (B : Tm (a :: Z.Lp K) .s) (j : HTerm (Z.X K) .w)
    (y : HVar (Z.X N) (.L a)) :
    inst (rename (liftR (Z.lt K N hN)) (Lf (liftL canonR) B (wk j))) (.var y) =
      Lf canonR (substL (consL (.var (lpos y)) (fun v => .var (Z.qL K N hN v))) B) (rename (Z.lt K N hN) j) := by
  show HTerm.holds (inst (rename (liftR _) (emb (liftL canonR) B)) (.var y))
    (inst (rename (liftR _) (wk j)) (.var y)) = _
  rw [inst_ren_wk, rename_emb B _ (liftL canonR) (liftL (fun v => Z.lt K N hN (canonR v)))
    (fun v => by cases v <;> rfl)]
  unfold inst
  rw [subst_emb B _ (liftL _) canonR (consL (.var (lpos y)) (fun v => .var (Z.qL K N hN v))) (fun v => by
    cases v with
    | zero => show HTerm.var y = HTerm.var (canonR (lpos y)); rw [canonR_lpos]
    | succ v => show HTerm.var _ = HTerm.var (canonR (lpos _)); rw [canonR_lpos])]
  rfl

theorem cons_comp {Γ' : List FTy} (ρ : VEnv (VMc Z) Γ') {K N : Nat} (hK : stg ρ ≤ K) (hN : K ≤ N)
    (Y : Tm (Z.Lp N) a) (b : Tm (a :: Γ') .s) :
    substL (consL Y (fun v => .var (Z.qL K N hN v))) (substL (liftSL (subE ρ K hK)) b) =
      substL (consL Y (subE ρ N (Nat.le_trans hK hN))) b :=
  substL_substL _ _ _ _ (fun v => by
    cases v with
    | zero => rfl
    | succ v =>
        show substL _ (renameL _ (subE ρ K hK v)) = subE ρ N _ v
        rw [substL_renameL (subE ρ K hK v) (fun v => .succ v) _ (fun v => .var (Z.qL K N hN v)) (fun _ => rfl),
          substL_var, sub_nat])

theorem cons_lift {Γ' : List FTy} (ρ : VEnv (VMc Z) Γ') {K N : Nat} (hK : stg ρ ≤ K) (hN : K ≤ N)
    (Y : Tm (Z.Lp K) a) (b : Tm (a :: Γ') .s) :
    renameL (Z.qL K N hN) (substL (consL Y (subE ρ K hK)) b) =
      substL (consL (renameL (Z.qL K N hN) Y) (subE ρ N (Nat.le_trans hK hN))) b :=
  renameL_substL _ _ _ _ (fun v => by
    cases v with
    | zero => rfl
    | succ v => exact sub_nat ρ hK hN v)

theorem E_var (N : Nat) (y : HVar (Z.X N) (.L a)) (h : N ≤ N) :
    E (⟨N, .var (lpos y)⟩ : Z.G a) N h = .var y := by
  rw [E_mk, Z.ren_refl]; show HTerm.var (canonR (lpos y)) = _; rw [canonR_lpos]

/-- The Henkin step for an `𝓛`-quantifier: a witness variable, as a global term. -/
theorem ev_all (a : FTy) (b : Tm (a :: Γ') .s) (ρ : VEnv (VMc Z) Γ') (w : Z.Wd) :
    (VMc Z).pr (cls (evc (.all a b) ρ)) w ↔
      ∀ x : Z.Car a, (VMc Z).pr (cls (evc (Γ' := a :: Γ') b (x, ρ))) w := by
  constructor
  · intro h x
    induction x using Quotient.inductionOn (s := setoidG Z a) with
    | h u =>
    let K := max (max (stg ρ) w.1) (stg (Γ' := a :: Γ') (cls u, ρ))
    have hS : stg ρ ≤ K := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
    have hw : w.1 ≤ K := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
    have k2 : stg (Γ' := a :: Γ') (cls u, ρ) ≤ K := Nat.le_max_right _ _
    rw [pr_ev _ ρ w K hS hw] at h
    rw [pr_ev _ _ w K k2 hw, subE_cons]
    have := Z.M_mp h (L_allE (.hyp (List.mem_cons_self ..))
      (liftG (qout (s := setoidG Z a) (cls u)) K (Nat.le_trans (Nat.le_max_left _ _) k2)))
    rwa [instL_liftSL] at this
  · intro H
    let K := max (stg ρ) w.1
    have hS : stg ρ ≤ K := Nat.le_max_left _ _
    have hw : w.1 ≤ K := Nat.le_max_right _ _
    rw [pr_ev _ ρ w K hS hw]
    rcases Z.M_max K (Lf canonR (substL (subE ρ K hS) (.all a b)) (wl w K hw)) with m | m
    · exact m
    exfalso
    have m2 := Z.M_mp (Z.M_mp m (d_neg_of L_all_hyp)) d_ex_not
    obtain ⟨N, hN, y, my⟩ := mem_henkin Z.T Z.Γ0 Z.hs0 Z.hc m2
    have e := henkin_inst hN (substL (liftSL (subE ρ K hS)) b) (wl w K hw) y
    rw [cons_comp, wl_nat] at e
    have my' : Z.M N (negH (Lf canonR (substL (consL (.var (lpos y)) (subE ρ N (Nat.le_trans hS hN))) b)
        (wl w N (Nat.le_trans hw hN)))) := by
      have : Z.M N (negH (inst (rename (liftR (Z.lt K N hN)) (Lf (liftL canonR) (substL (liftSL (subE ρ K hS)) b)
        (wk (wl w K hw)))) (.var y))) := my
      rwa [e] at this
    let yv : Z.G a := ⟨N, .var (lpos y)⟩
    have Hx := H (cls yv)
    let K' := max N (stg (Γ' := a :: Γ') (cls yv, ρ))
    have hNK : N ≤ K' := Nat.le_max_left _ _
    have k2 : stg (Γ' := a :: Γ') (cls yv, ρ) ≤ K' := Nat.le_max_right _ _
    have hw' : w.1 ≤ K' := Nat.le_trans (Nat.le_trans hw hN) hNK
    rw [pr_ev _ _ w K' k2 hw', subE_cons] at Hx
    have my2 := (Z.M_lift hNK _).1 my'
    have e2 : rename (Z.lt N K' hNK) (negH (Lf canonR (substL (consL (.var (lpos y))
        (subE ρ N (Nat.le_trans hS hN))) b) (wl w N (Nat.le_trans hw hN)))) =
        negH (Lf canonR (substL (consL (liftG yv K' hNK) (subE ρ K' (Nat.le_trans (Nat.le_trans hS hN) hNK))) b)
          (wl w K' hw')) := by
      show HTerm.imp (rename _ (Lf canonR _ _)) .bot = _
      rw [lift_tr, cons_lift, wl_nat]; rfl
    rw [e2] at my2
    have q := mk_qout (s := setoidG Z a) yv
    exact Z.M_not_both (tr_cons b _ (q K' _ hNK) Hx) my2

end Seed

namespace Seed
variable {Z : Seed}

theorem act_cls (u : Z.G .e) (w : Z.Wd) : (VMc Z).act (cls u) w ↔ actF u w := Iff.rfl

theorem ev_ex (a : FTy) (b : Tm (a :: Γ') .s) (ρ : VEnv (VMc Z) Γ') (w : Z.Wd) :
    (VMc Z).pr (cls (evc (.ex a b) ρ)) w ↔
      ∃ x : Z.Car a, (VMc Z).pr (cls (evc (Γ' := a :: Γ') b (x, ρ))) w := by
  constructor
  · intro h
    let K := max (stg ρ) w.1
    have hS : stg ρ ≤ K := Nat.le_max_left _ _
    have hw : w.1 ≤ K := Nat.le_max_right _ _
    rw [pr_ev _ ρ w K hS hw] at h
    have m2 := Z.M_mp h L_ex_hyp
    obtain ⟨N, hN, y, my⟩ := mem_henkin Z.T Z.Γ0 Z.hs0 Z.hc m2
    have e := henkin_inst hN (substL (liftSL (subE ρ K hS)) b) (wl w K hw) y
    rw [cons_comp, wl_nat] at e
    have my' : Tr N (substL (consL (.var (lpos y)) (subE ρ N (Nat.le_trans hS hN))) b)
        (wl w N (Nat.le_trans hw hN)) := by
      have : Z.M N (inst (rename (liftR (Z.lt K N hN)) (Lf (liftL canonR) (substL (liftSL (subE ρ K hS)) b)
        (wk (wl w K hw)))) (.var y)) := my
      rwa [e] at this
    let yv : Z.G a := ⟨N, .var (lpos y)⟩
    refine ⟨cls yv, ?_⟩
    let K' := max N (stg (Γ' := a :: Γ') (cls yv, ρ))
    have hNK : N ≤ K' := Nat.le_max_left _ _
    have k2 : stg (Γ' := a :: Γ') (cls yv, ρ) ≤ K' := Nat.le_max_right _ _
    have hw' : w.1 ≤ K' := Nat.le_trans (Nat.le_trans hw hN) hNK
    rw [pr_ev _ _ w K' k2 hw', subE_cons]
    have my2 := (tr_lift hNK _ _).1 my'
    rw [cons_lift, wl_nat] at my2
    have q := mk_qout (s := setoidG Z a) yv
    exact tr_cons b _ (eqv_symm q K' hNK _) my2
  · rintro ⟨x, hx⟩
    induction x using Quotient.inductionOn (s := setoidG Z a) with
    | h u =>
    let K := max (max (stg ρ) w.1) (stg (Γ' := a :: Γ') (cls u, ρ))
    have hS : stg ρ ≤ K := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
    have hw : w.1 ≤ K := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
    have k2 : stg (Γ' := a :: Γ') (cls u, ρ) ≤ K := Nat.le_max_right _ _
    rw [pr_ev _ _ w K k2 hw, subE_cons] at hx
    rw [pr_ev _ ρ w K hS hw]
    have hx' : Tr K (instL (substL (liftSL (subE ρ K hS)) b)
        (liftG (qout (s := setoidG Z a) (cls u)) K (Nat.le_trans (Nat.le_max_left _ _) k2))) (wl w K hw) := by
      rw [instL_liftSL]; exact hx
    exact Z.M_mp hx' (L_exI _ (.hyp (List.mem_cons_self ..)))

theorem ev_allE (b : Tm (.e :: Γ') .s) (ρ : VEnv (VMc Z) Γ') (w : Z.Wd) :
    (VMc Z).pr (cls (evc (.allE b) ρ)) w ↔
      ∀ x : Z.Car .e, (VMc Z).act x w → (VMc Z).pr (cls (evc (Γ' := .e :: Γ') b (x, ρ))) w := by
  constructor
  · intro h x hxw
    induction x using Quotient.inductionOn (s := setoidG Z .e) with
    | h u =>
    let K := max (max (stg ρ) w.1) (stg (Γ' := .e :: Γ') (cls u, ρ))
    have hS : stg ρ ≤ K := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
    have hw : w.1 ≤ K := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
    have k2 : stg (Γ' := .e :: Γ') (cls u, ρ) ≤ K := Nat.le_max_right _ _
    rw [pr_ev _ ρ w K hS hw] at h
    rw [pr_ev _ _ w K k2 hw, subE_cons]
    have hq : actF (qout (s := setoidG Z .e) (cls u)) w :=
      actF_resp (eqv_symm (mk_qout (s := setoidG Z .e) u)) w hxw
    rw [actF_iff _ w K (Nat.le_trans (Nat.le_max_left _ _) k2) hw] at hq
    have := Z.M_mp2 h hq (L_allEE (.hyp (List.mem_cons_self ..))
      (liftG (qout (s := setoidG Z .e) (cls u)) K (Nat.le_trans (Nat.le_max_left _ _) k2))
      (.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
    rwa [instL_liftSL] at this
  · intro H
    let K := max (stg ρ) w.1
    have hS : stg ρ ≤ K := Nat.le_max_left _ _
    have hw : w.1 ≤ K := Nat.le_max_right _ _
    rw [pr_ev _ ρ w K hS hw]
    rcases Z.M_max K (Lf canonR (substL (subE ρ K hS) (.allE b)) (wl w K hw)) with m | m
    · exact m
    exfalso
    have m2 := Z.M_mp (Z.M_mp m (d_neg_of L_allE_hyp)) d_ex_not
    obtain ⟨N, hN, y, my⟩ := mem_henkin Z.T Z.Γ0 Z.hs0 Z.hc m2
    have e := henkin_inst hN (substL (liftSL (subE ρ K hS)) b) (wl w K hw) y
    rw [cons_comp, wl_nat] at e
    have ea := inst_act (Z.lt K N hN) (wl w K hw) (.var y)
    rw [wl_nat] at ea
    have my' : Z.M N (negH (.imp (.act (.var y) (wl w N (Nat.le_trans hw hN)))
        (Lf canonR (substL (consL (.var (lpos y)) (subE ρ N (Nat.le_trans hS hN))) b)
        (wl w N (Nat.le_trans hw hN))))) := by
      have : Z.M N (negH (.imp (inst (rename (liftR (Z.lt K N hN)) (HTerm.act var0 (wk (wl w K hw)))) (.var y))
        (inst (rename (liftR (Z.lt K N hN)) (Lf (liftL canonR) (substL (liftSL (subE ρ K hS)) b)
        (wk (wl w K hw)))) (.var y)))) := my
      rwa [e, ea] at this
    obtain ⟨ma, mb⟩ := M_negimp my'
    let yv : Z.G .e := ⟨N, .var (lpos y)⟩
    have hact : (VMc Z).act (cls yv) w := by
      show actF yv w
      rw [actF_iff yv w N (Nat.le_refl N) (Nat.le_trans hw hN), E_var]
      exact ma
    have Hx := H (cls yv) hact
    let K' := max N (stg (Γ' := .e :: Γ') (cls yv, ρ))
    have hNK : N ≤ K' := Nat.le_max_left _ _
    have k2 : stg (Γ' := .e :: Γ') (cls yv, ρ) ≤ K' := Nat.le_max_right _ _
    have hw' : w.1 ≤ K' := Nat.le_trans (Nat.le_trans hw hN) hNK
    rw [pr_ev _ _ w K' k2 hw', subE_cons] at Hx
    have q := mk_qout (s := setoidG Z .e) yv
    have h3 := tr_cons b _ (q K' _ hNK) Hx
    apply mb
    refine (tr_lift hNK _ _).2 ?_
    rw [cons_lift, wl_nat]
    exact h3

theorem ev_exE (b : Tm (.e :: Γ') .s) (ρ : VEnv (VMc Z) Γ') (w : Z.Wd) :
    (VMc Z).pr (cls (evc (.exE b) ρ)) w ↔
      ∃ x : Z.Car .e, (VMc Z).act x w ∧ (VMc Z).pr (cls (evc (Γ' := .e :: Γ') b (x, ρ))) w := by
  constructor
  · intro h
    let K := max (stg ρ) w.1
    have hS : stg ρ ≤ K := Nat.le_max_left _ _
    have hw : w.1 ≤ K := Nat.le_max_right _ _
    rw [pr_ev _ ρ w K hS hw] at h
    have m2 := Z.M_mp h L_exE_hyp
    obtain ⟨N, hN, y, my⟩ := mem_henkin Z.T Z.Γ0 Z.hs0 Z.hc m2
    have e := henkin_inst hN (substL (liftSL (subE ρ K hS)) b) (wl w K hw) y
    rw [cons_comp, wl_nat] at e
    have ea := inst_act (Z.lt K N hN) (wl w K hw) (.var y)
    rw [wl_nat] at ea
    have my' : Z.M N (.and (.act (.var y) (wl w N (Nat.le_trans hw hN)))
        (Lf canonR (substL (consL (.var (lpos y)) (subE ρ N (Nat.le_trans hS hN))) b)
        (wl w N (Nat.le_trans hw hN)))) := by
      have : Z.M N (.and (inst (rename (liftR (Z.lt K N hN)) (HTerm.act var0 (wk (wl w K hw)))) (.var y))
        (inst (rename (liftR (Z.lt K N hN)) (Lf (liftL canonR) (substL (liftSL (subE ρ K hS)) b)
        (wk (wl w K hw)))) (.var y))) := my
      rwa [e, ea] at this
    obtain ⟨ma, mb⟩ := M_and my'
    let yv : Z.G .e := ⟨N, .var (lpos y)⟩
    refine ⟨cls yv, ?_, ?_⟩
    · show actF yv w
      rw [actF_iff yv w N (Nat.le_refl N) (Nat.le_trans hw hN), E_var]
      exact ma
    let K' := max N (stg (Γ' := .e :: Γ') (cls yv, ρ))
    have hNK : N ≤ K' := Nat.le_max_left _ _
    have k2 : stg (Γ' := .e :: Γ') (cls yv, ρ) ≤ K' := Nat.le_max_right _ _
    have hw' : w.1 ≤ K' := Nat.le_trans (Nat.le_trans hw hN) hNK
    rw [pr_ev _ _ w K' k2 hw', subE_cons]
    have my2 := (tr_lift hNK _ _).1 mb
    rw [cons_lift, wl_nat] at my2
    have q := mk_qout (s := setoidG Z .e) yv
    exact tr_cons b _ (eqv_symm q K' hNK _) my2
  · rintro ⟨x, hxw, hx⟩
    induction x using Quotient.inductionOn (s := setoidG Z .e) with
    | h u =>
    let K := max (max (stg ρ) w.1) (stg (Γ' := .e :: Γ') (cls u, ρ))
    have hS : stg ρ ≤ K := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
    have hw : w.1 ≤ K := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
    have k2 : stg (Γ' := .e :: Γ') (cls u, ρ) ≤ K := Nat.le_max_right _ _
    rw [pr_ev _ _ w K k2 hw, subE_cons] at hx
    rw [pr_ev _ ρ w K hS hw]
    have hq : actF (qout (s := setoidG Z .e) (cls u)) w :=
      actF_resp (eqv_symm (mk_qout (s := setoidG Z .e) u)) w hxw
    rw [actF_iff _ w K (Nat.le_trans (Nat.le_max_left _ _) k2) hw] at hq
    have hx' : Tr K (instL (substL (liftSL (subE ρ K hS)) b)
        (liftG (qout (s := setoidG Z .e) (cls u)) K (Nat.le_trans (Nat.le_max_left _ _) k2))) (wl w K hw) := by
      rw [instL_liftSL]; exact hx
    exact Z.M_mp2 hq hx' (L_exEI _ (.hyp (List.mem_cons_self ..)) (.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..))))

theorem ev_box (x : Tm Γ' .s) (ρ : VEnv (VMc Z) Γ') (w : Z.Wd) :
    (VMc Z).pr (cls (evc (.box x) ρ)) w ↔ ∀ v, (VMc Z).R w v → (VMc Z).pr (cls (evc x ρ)) v := by
  constructor
  · intro h v hv
    let K := max (max (stg ρ) w.1) v.1
    have hS : stg ρ ≤ K := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
    have hw : w.1 ≤ K := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
    have hv' : v.1 ≤ K := Nat.le_max_right _ _
    rw [pr_ev _ ρ w K hS hw] at h
    rw [pr_ev _ ρ v K hS hv']
    have hr : Z.M K (.rel (wl w K hw) (wl v K hv')) := (RF_iff w v K hw hv').1 hv
    exact Z.M_mp2 h hr (L_boxE (.hyp (List.mem_cons_self ..)) (.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
  · intro H
    let K := max (stg ρ) w.1
    have hS : stg ρ ≤ K := Nat.le_max_left _ _
    have hw : w.1 ≤ K := Nat.le_max_right _ _
    rw [pr_ev _ ρ w K hS hw]
    rcases Z.M_max K (Lf canonR (substL (subE ρ K hS) (.box x)) (wl w K hw)) with m | m
    · exact m
    exfalso
    have m2 := Z.M_mp (Z.M_mp m (d_neg_of L_box_hyp)) d_ex_not
    obtain ⟨N, hN, y, my⟩ := mem_henkin Z.T Z.Γ0 Z.hs0 Z.hc m2
    have er := inst_rel (Z.lt K N hN) (wl w K hw) (.var y)
    rw [wl_nat] at er
    have el : inst (rename (liftR (Z.lt K N hN)) (Lf (shL canonR) (substL (subE ρ K hS) x) var0)) (.var y) =
        Lf canonR (substL (subE ρ N (Nat.le_trans hS hN)) x) (.var y) := by
      show HTerm.holds (inst (rename (liftR _) (emb (shL canonR) (substL (subE ρ K hS) x))) (.var y)) (.var y) = _
      rw [rename_emb _ _ (shL canonR) (shL (fun v => Z.lt K N hN (canonR v))) (fun _ => rfl)]
      unfold inst
      rw [sub0_shL, ← ev_nat ρ hS hN x]
      show HTerm.holds (emb (fun v => Z.lt K N hN (canonR v)) _) _ =
        HTerm.holds (emb canonR (renameL (Z.qL K N hN) _)) _
      rw [Z.emb_qL, rename_emb _ _ canonR _ (fun _ => rfl)]
    have my' : Z.M N (negH (.imp (.rel (wl w N (Nat.le_trans hw hN)) (.var y))
        (Lf canonR (substL (subE ρ N (Nat.le_trans hS hN)) x) (.var y)))) := by
      have : Z.M N (negH (.imp (inst (rename (liftR (Z.lt K N hN)) (HTerm.rel (wk (wl w K hw)) var0)) (.var y))
        (inst (rename (liftR (Z.lt K N hN)) (Lf (shL canonR) (substL (subE ρ K hS) x) var0)) (.var y)))) := my
      rwa [er, el] at this
    obtain ⟨ma, mb⟩ := M_negimp my'
    let v : Z.Wd := ⟨N, .var y⟩
    have hwv : wl v N (Nat.le_refl N) = .var y := Z.ren_refl _ _ _
    have hR : (VMc Z).R w v := by
      show RF w v
      rw [RF_iff w v N (Nat.le_trans hw hN) (Nat.le_refl N), hwv]
      exact ma
    have Hv := H v hR
    rw [pr_ev _ ρ v N (Nat.le_trans hS hN) (Nat.le_refl N), hwv] at Hv
    exact mb Hv

end Seed

namespace Seed
variable {Z : Seed}

theorem pr_evK (φ : Tm Γ' .s) (ρ : VEnv (VMc Z) Γ') (w : Z.Wd) :
    (VMc Z).pr (cls (evc φ ρ)) w ↔
      Tr (max (stg ρ) w.1) (substL (subE ρ _ (Nat.le_max_left _ _)) φ) (wl w _ (Nat.le_max_right _ _)) :=
  pr_ev φ ρ w _ _ _

end Seed

/-- **The canonical model is 𝓛-general** (v4 def:lgeneral, as `LGen`). -/
noncomputable def LGc (Z : Seed) : LGen (VMc Z) where
  ev := fun tm ρ => Seed.cls (Seed.evc tm ρ)
  var := Seed.ev_var
  app := Seed.ev_app
  lam := Seed.ev_lam
  top := fun ρ w => ⟨fun _ => trivial, fun _ => (Seed.pr_evK _ ρ w).2 Seed.tr_top⟩
  bot := fun ρ w => ⟨fun h => Seed.tr_bot ((Seed.pr_evK _ ρ w).1 h), False.elim⟩
  neg := fun x ρ w => (Seed.pr_evK _ ρ w).trans (Seed.tr_neg.trans (not_congr (Seed.pr_evK x ρ w).symm))
  and := fun x y ρ w => (Seed.pr_evK _ ρ w).trans (Seed.tr_and.trans
    (and_congr (Seed.pr_evK x ρ w).symm (Seed.pr_evK y ρ w).symm))
  or := fun x y ρ w => (Seed.pr_evK _ ρ w).trans (Seed.tr_or.trans
    (or_congr (Seed.pr_evK x ρ w).symm (Seed.pr_evK y ρ w).symm))
  imp := fun x y ρ w => (Seed.pr_evK _ ρ w).trans (Seed.tr_imp.trans
    (imp_congr (Seed.pr_evK x ρ w).symm (Seed.pr_evK y ρ w).symm))
  box := Seed.ev_box
  all := Seed.ev_all
  ex := Seed.ev_ex
  allE := Seed.ev_allE
  exE := Seed.ev_exE
  eq := Seed.ev_eq
  pos := Seed.ev_pos

/-! ### Completeness -/

def nilRL : RenL [] Δ := fun v => nomatch v

theorem closed_tr {Z : Seed} {K : Nat} (ψ : Tm [] .s) (σ : SubL [] (Z.Lp K)) (i : HTerm (Z.X K) .w) :
    Lf canonR (substL σ ψ) i = Lf nilR ψ i := by
  rw [substL_congr ψ (s' := fun v => .var (nilRL v)) (fun v => nomatch v), substL_var]
  show HTerm.holds (emb canonR (renameL nilRL ψ)) i = HTerm.holds (emb nilR ψ) i
  rw [emb_renameL ψ nilRL canonR nilR (fun v => nomatch v)]

/-- **Completeness (M3).** If `∃x.⊤ ∈ T` and the `𝓛`-sentence `φ` holds in every v4 `𝓛`-general
model of `T` with nonempty individuals, then `⟦φ⟧` has a certified deep derivation from `T` at a
world variable. -/
theorem completeness {T : Tm [] .s → Prop} {φ : Tm [] .s} (hNE : T (.ex .e .top)) (H : ValidV4 T φ) :
    DC T [.w] [] (.holds (emb nilR φ) var0) := by
  refine Classical.byContradiction fun hd => ?_
  let Z : Seed := ⟨T, [.w], [negH (.holds (emb nilR φ) var0)], start_cons T hd, var0⟩
  have hT : ∀ ψ, T ψ → ∀ w, (VMc Z).pr ((LGc Z).ev ψ ()) w := fun ψ hψ w => by
    show (VMc Z).pr (Seed.cls (Seed.evc ψ ())) w
    rw [Seed.pr_evK]
    show Z.M _ _
    rw [closed_tr]
    exact Z.M_of (L_ax hψ nilR _)
  let w0 : Z.Wd := ⟨0, var0⟩
  have hne : Nonempty ((VMc Z).C .e) := by
    obtain ⟨x, _⟩ := ((LGc Z).ex (Γ := []) .e .top () w0).1 (hT _ hNE w0)
    exact ⟨x⟩
  have h0 := H Z.Wd (VMc Z) (LGc Z) hne hT w0
  have h1 : (VMc Z).pr (Seed.cls (Seed.evc φ ())) w0 := h0
  rw [Seed.pr_ev φ () w0 0 (Nat.le_refl 0) (Nat.le_refl 0)] at h1
  have h2 : Z.M 0 (Lf canonR (substL (Seed.subE (Z := Z) (Γ' := []) () 0 (Nat.le_refl 0)) φ)
      (Seed.wl w0 0 (Nat.le_refl 0))) := h1
  rw [closed_tr, Seed.wl, Z.ren_refl] at h2
  exact Z.M_not_both h2 (mem_self T [.w] _ (List.mem_cons_self ..))

/-- **Soundness and completeness over v4's 𝓛-general models**, for theories with `∃x.⊤`. -/
theorem sound_complete {T : Tm [] .s → Prop} {φ : Tm [] .s} (hNE : T (.ex .e .top)) :
    DC T [.w] [] (.holds (emb nilR φ) var0) ↔ ValidV4 T φ :=
  ⟨Programme.«20261022-1724-ontological».Run3.V4.sound_v4, completeness hNE⟩

/-- The same over closed `eqT`-respecting structures (K4's class), via the bridge. -/
theorem sound_complete_str {T : Tm [] .s → Prop} {φ : Tm [] .s} (hNE : T (.ex .e .top)) :
    DC T [.w] [] (.holds (emb nilR φ) var0) ↔ ValidStr T φ :=
  (sound_complete hNE).trans (valid_iff T φ)

/-- `T` with the sentence `∃x.⊤` (nonempty individuals) added. -/
def withNE (T : Tm [] .s → Prop) : Tm [] .s → Prop := fun ψ => T ψ ∨ ψ = .ex .e .top

theorem validV4_withNE {T : Tm [] .s → Prop} {φ : Tm [] .s} : ValidV4 (withNE T) φ ↔ ValidV4 T φ := by
  constructor
  · intro H W M L hne hT w
    refine H W M L hne (fun ψ hψ v => ?_) w
    rcases hψ with hψ | rfl
    · exact hT ψ hψ v
    · obtain ⟨x⟩ := hne
      exact (L.ex (Γ := []) .e .top () v).2 ⟨x, (L.top (Γ := [.e]) (x, ()) v).2 trivial⟩
  · intro H W M L hne hT w
    exact H W M L hne (fun ψ hψ v => hT ψ (.inl hψ) v) w

/-- **Soundness and completeness for every 𝓛-theory**: `φ` holds in every v4 𝓛-general model of `T`
with nonempty individuals iff `⟦φ⟧` has a certified deep derivation from `T ∪ {∃x.⊤}`. -/
theorem sound_complete_all {T : Tm [] .s → Prop} {φ : Tm [] .s} :
    DC (withNE T) [.w] [] (.holds (emb nilR φ) var0) ↔ ValidV4 T φ :=
  (sound_complete (.inr rfl)).trans validV4_withNE


/-! ## Downward Löwenheim–Skolem (th, round 8)
The canonical model `VMc Z` has countably many worlds and countable carriers at every type: worlds are
`Σ n, HTerm (Z.X n) .w` (coded by `pair n (codeT _)`), carriers are quotients of `Σ n, Tm (Z.Lp n) t`
(coded by an injective code of 𝓛-terms through a chosen representative). Hence every 𝓛-sentence that
fails in some v4 𝓛-general model of `T` (nonempty individuals) fails in a countable one. -/

/-- `α` injects into `Nat`. -/
def Ctbl (α : Type) : Prop := ∃ f : α → Nat, ∀ a b, f a = f b → a = b

def codeVar : {Γ : List FTy} → {t : FTy} → Var Γ t → Nat
  | _, _, .zero => 0
  | _, _, .succ v => codeVar v + 1

theorem codeVar_inj : ∀ {Γ t} (v v' : Var Γ t), codeVar v = codeVar v' → v = v'
  | _, _, .zero, .zero, _ => rfl
  | _, _, .zero, .succ _, h => by simp [codeVar] at h
  | _, _, .succ _, .zero, h => by simp [codeVar] at h
  | _, _, .succ v, .succ v', h => by
      simp only [codeVar, Nat.add_right_cancel_iff] at h; rw [codeVar_inj v v' h]

def codeTm : {Γ : List FTy} → {t : FTy} → Tm Γ t → Nat
  | _, _, .var v => pair 0 (codeVar v)
  | _, _, @Tm.app _ a _ f x => pair 1 (pair (codeF a) (pair (codeTm f) (codeTm x)))
  | _, _, .lam b => pair 2 (codeTm b)
  | _, _, .top => pair 3 0
  | _, _, .bot => pair 4 0
  | _, _, .neg p => pair 5 (codeTm p)
  | _, _, .and p q => pair 6 (pair (codeTm p) (codeTm q))
  | _, _, .or p q => pair 7 (pair (codeTm p) (codeTm q))
  | _, _, .imp p q => pair 8 (pair (codeTm p) (codeTm q))
  | _, _, .box p => pair 9 (codeTm p)
  | _, _, .all a p => pair 10 (pair (codeF a) (codeTm p))
  | _, _, .ex a p => pair 11 (pair (codeF a) (codeTm p))
  | _, _, .allE p => pair 12 (codeTm p)
  | _, _, .exE p => pair 13 (codeTm p)
  | _, _, .eq a s t => pair 14 (pair (codeF a) (pair (codeTm s) (codeTm t)))
  | _, _, .pos => pair 15 0

theorem codeTm_inj : ∀ {Γ t} (x y : Tm Γ t), codeTm x = codeTm y → x = y
  | _, _, .var v, y, h => by
      cases y <;> simp only [codeTm, pair_iff] at h <;> first | omega | rw [codeVar_inj _ _ h.2]
  | _, _, @Tm.app _ a _ f x, y, h => by
      cases y with
      | @app _ a' _ f' x' =>
          simp only [codeTm, pair_iff] at h
          obtain ⟨_, ha, hf, hx⟩ := h
          cases codeF_inj ha
          rw [codeTm_inj f f' hf, codeTm_inj x x' hx]
      | _ => simp only [codeTm, pair_iff] at h; omega
  | _, _, .lam b, y, h => by
      cases y with
      | lam b' => simp only [codeTm, pair_iff] at h; rw [codeTm_inj b b' h.2]
      | _ => simp only [codeTm, pair_iff] at h; omega
  | _, _, .top, y, h => by cases y <;> simp only [codeTm, pair_iff] at h <;> first | omega | rfl
  | _, _, .bot, y, h => by cases y <;> simp only [codeTm, pair_iff] at h <;> first | omega | rfl
  | _, _, .pos, y, h => by cases y <;> simp only [codeTm, pair_iff] at h <;> first | omega | rfl
  | _, _, .neg p, y, h => by
      cases y with
      | neg p' => simp only [codeTm, pair_iff] at h; rw [codeTm_inj p p' h.2]
      | _ => simp only [codeTm, pair_iff] at h; omega
  | _, _, .box p, y, h => by
      cases y with
      | box p' => simp only [codeTm, pair_iff] at h; rw [codeTm_inj p p' h.2]
      | _ => simp only [codeTm, pair_iff] at h; omega
  | _, _, .allE p, y, h => by
      cases y with
      | allE p' => simp only [codeTm, pair_iff] at h; rw [codeTm_inj p p' h.2]
      | _ => simp only [codeTm, pair_iff] at h; omega
  | _, _, .exE p, y, h => by
      cases y with
      | exE p' => simp only [codeTm, pair_iff] at h; rw [codeTm_inj p p' h.2]
      | _ => simp only [codeTm, pair_iff] at h; omega
  | _, _, .and p q, y, h => by
      cases y with
      | and p' q' => simp only [codeTm, pair_iff] at h; rw [codeTm_inj p p' h.2.1, codeTm_inj q q' h.2.2]
      | _ => simp only [codeTm, pair_iff] at h; omega
  | _, _, .or p q, y, h => by
      cases y with
      | or p' q' => simp only [codeTm, pair_iff] at h; rw [codeTm_inj p p' h.2.1, codeTm_inj q q' h.2.2]
      | _ => simp only [codeTm, pair_iff] at h; omega
  | _, _, .imp p q, y, h => by
      cases y with
      | imp p' q' => simp only [codeTm, pair_iff] at h; rw [codeTm_inj p p' h.2.1, codeTm_inj q q' h.2.2]
      | _ => simp only [codeTm, pair_iff] at h; omega
  | _, _, .all a p, y, h => by
      cases y with
      | all a' p' =>
          simp only [codeTm, pair_iff] at h
          obtain ⟨_, ha, hp⟩ := h
          cases codeF_inj ha
          rw [codeTm_inj p p' hp]
      | _ => simp only [codeTm, pair_iff] at h; omega
  | _, _, .ex a p, y, h => by
      cases y with
      | ex a' p' =>
          simp only [codeTm, pair_iff] at h
          obtain ⟨_, ha, hp⟩ := h
          cases codeF_inj ha
          rw [codeTm_inj p p' hp]
      | _ => simp only [codeTm, pair_iff] at h; omega
  | _, _, .eq a s t, y, h => by
      cases y with
      | eq a' s' t' =>
          simp only [codeTm, pair_iff] at h
          obtain ⟨_, ha, hs, ht⟩ := h
          cases codeF_inj ha
          rw [codeTm_inj s s' hs, codeTm_inj t t' ht]
      | _ => simp only [codeTm, pair_iff] at h; omega

theorem ctbl_sigma {F : Nat → Type} (c : ∀ n, F n → Nat) (hc : ∀ n (x y : F n), c n x = c n y → x = y) :
    Ctbl (Σ n, F n) := by
  refine ⟨fun x => pair x.1 (c x.1 x.2), ?_⟩
  rintro ⟨n, x⟩ ⟨m, y⟩ h
  obtain ⟨h1, h2⟩ := pair_inj h
  cases h1
  rw [hc n x y h2]

theorem ctbl_quot {α : Type} {s : Setoid α} (h : Ctbl α) : Ctbl (Quotient s) := by
  obtain ⟨f, hf⟩ := h
  refine ⟨fun q => f (qout q), fun a b hab => ?_⟩
  rw [← qout_eq a, ← qout_eq b, hf _ _ hab]

theorem ctbl_worlds (Z : Seed) : Ctbl Z.Wd :=
  ctbl_sigma (fun _ t => codeT t) (fun _ x y h => codeT_inj x y h)

theorem ctbl_carriers (Z : Seed) (t : FTy) : Ctbl ((VMc Z).C t) :=
  ctbl_quot (ctbl_sigma (F := fun n => Tm (Z.Lp n) t) (fun _ x => codeTm x) (fun _ x y h => codeTm_inj x y h))

/-- **Downward Löwenheim–Skolem for v4's 𝓛-general models.** If `T ∋ ∃x.⊤` and an 𝓛-sentence `φ` fails
in some 𝓛-general model of `T` with nonempty individuals, it fails in one whose set of worlds and every
carrier `C t` inject into `Nat`. -/
theorem lowenheim_skolem {T : Tm [] .s → Prop} {φ : Tm [] .s} (hNE : T (.ex .e .top))
    (H : ¬ ValidV4 T φ) :
    ∃ (W : Type) (M : VM W) (L : LGen M), Ctbl W ∧ (∀ t, Ctbl (M.C t)) ∧ Nonempty (M.C .e) ∧
      (∀ ψ, T ψ → ∀ w, M.pr (L.ev ψ ()) w) ∧ ∃ w, ¬ M.pr (L.ev φ ()) w := by
  have hd : ¬ DC T [.w] [] (.holds (emb nilR φ) var0) := fun d => H (Programme.«20261022-1724-ontological».Run3.V4.sound_v4 d)
  let Z : Seed := ⟨T, [.w], [negH (.holds (emb nilR φ) var0)], start_cons T hd, var0⟩
  have hT : ∀ ψ, T ψ → ∀ w, (VMc Z).pr ((LGc Z).ev ψ ()) w := fun ψ hψ w => by
    show (VMc Z).pr (Seed.cls (Seed.evc ψ ())) w
    rw [Seed.pr_evK]
    show Z.M _ _
    rw [closed_tr]
    exact Z.M_of (L_ax hψ nilR _)
  let w0 : Z.Wd := ⟨0, var0⟩
  have hne : Nonempty ((VMc Z).C .e) := by
    obtain ⟨x, _⟩ := ((LGc Z).ex (Γ := []) .e .top () w0).1 (hT _ hNE w0)
    exact ⟨x⟩
  refine ⟨Z.Wd, VMc Z, LGc Z, ctbl_worlds Z, ctbl_carriers Z, hne, hT, w0, fun h0 => ?_⟩
  have h1 : (VMc Z).pr (Seed.cls (Seed.evc φ ())) w0 := h0
  rw [Seed.pr_ev φ () w0 0 (Nat.le_refl 0) (Nat.le_refl 0)] at h1
  have h2 : Z.M 0 (Lf canonR (substL (Seed.subE (Z := Z) (Γ' := []) () 0 (Nat.le_refl 0)) φ)
      (Seed.wl w0 0 (Nat.le_refl 0))) := h1
  rw [closed_tr, Seed.wl, Z.ren_refl] at h2
  exact Z.M_not_both h2 (mem_self T [.w] _ (List.mem_cons_self ..))

/-- Validity over countable 𝓛-general models. -/
def ValidCtbl (T : Tm [] .s → Prop) (φ : Tm [] .s) : Prop :=
  ∀ (W : Type) (M : VM W) (L : LGen M), Ctbl W → (∀ t, Ctbl (M.C t)) → Nonempty (M.C .e) →
    (∀ ψ, T ψ → ∀ w, M.pr (L.ev ψ ()) w) → ∀ w, M.pr (L.ev φ ()) w

/-- For theories with `∃x.⊤`, validity over all v4 𝓛-general models equals validity over countable ones. -/
theorem valid_iff_ctbl {T : Tm [] .s → Prop} {φ : Tm [] .s} (hNE : T (.ex .e .top)) :
    ValidV4 T φ ↔ ValidCtbl T φ := by
  constructor
  · intro H W M L _ _ hne hT w
    exact H W M L hne hT w
  · intro H
    refine Classical.byContradiction fun hn => ?_
    obtain ⟨W, M, L, hW, hC, hne, hT, w, hw⟩ := lowenheim_skolem hNE hn
    exact hw (H W M L hW hC hne hT w)

/-- Every 𝓛-theory: `⟦φ⟧` derivable from `T ∪ {∃x.⊤}` iff `φ` holds in all countable 𝓛-general models of `T`. -/
theorem sound_complete_ctbl {T : Tm [] .s → Prop} {φ : Tm [] .s} :
    DC (withNE T) [.w] [] (.holds (emb nilR φ) var0) ↔ ValidCtbl T φ := by
  rw [sound_complete (.inr rfl), valid_iff_ctbl (.inr rfl)]
  constructor
  · intro H W M L hW hC hne hT w
    exact H W M L hW hC hne (fun ψ hψ v => by
      rcases hψ with hψ | rfl
      · exact hT ψ hψ v
      · obtain ⟨x⟩ := hne
        exact (L.ex (Γ := []) .e .top () v).2 ⟨x, (L.top (Γ := [.e]) (x, ()) v).2 trivial⟩) w
  · intro H W M L hW hC hne hT w
    exact H W M L hW hC hne (fun ψ hψ v => hT ψ (.inl hψ) v) w

/-! ## Compactness (th, round 8): a derivation uses finitely many axioms of `T`. -/

theorem mem_app3 {α : Type} {x : α} {l1 l2 l3 : List α} (h : x ∈ l1 ++ l2 ++ l3) :
    x ∈ l1 ∨ x ∈ l2 ∨ x ∈ l3 := by
  simp only [List.mem_append] at h; rcases h with (h | h) | h <;> simp [h]

macro "fin_close" : tactic => `(tactic| first
  | assumption
  | (apply ‹∀ T' : Tm [] .s → Prop, (∀ ψ, ψ ∈ _ → T' ψ) → _›; intro ψ hψ; apply ‹∀ ψ, ψ ∈ _ → _›; simp [hψ]))

theorem Deriv.finite {T : Tm [] .s → Prop} {ok : ∀ {Γ : List HTy} (a : HTy), HTerm Γ a → Prop}
    {Γ : List HTy} {hs : List (HTerm Γ .o)} {φ : HTerm Γ .o} (d : Deriv T ok Γ hs φ) :
    ∃ l : List (Tm [] .s), (∀ ψ, ψ ∈ l → T ψ) ∧
      ∀ T' : Tm [] .s → Prop, (∀ ψ, ψ ∈ l → T' ψ) → Deriv T' ok Γ hs φ := by
  induction d with
  | ax φ i h => exact ⟨[φ], fun ψ hψ => by simp at hψ; subst hψ; exact h, fun T' h' => .ax φ i (h' φ (by simp))⟩
  | hyp _ =>
    refine ⟨[], fun ψ hψ => ?_, fun T' h => ?_⟩
    · simp at hψ
    · skip
      apply Deriv.hyp <;> first | assumption
  | impI _ ih1 =>
    obtain ⟨l1, a1, k1⟩ := ih1
    refine ⟨l1, fun ψ hψ => ?_, fun T' h => ?_⟩
    · exact a1 ψ hψ
    · skip
      have e1 := k1 T' (fun ψ hψ => h ψ (by simp [hψ]))
      clear k1
      apply Deriv.impI <;> first | assumption
  | impE _ _ ih1 ih2 =>
    obtain ⟨l1, a1, k1⟩ := ih1
    obtain ⟨l2, a2, k2⟩ := ih2
    refine ⟨l1 ++ l2, fun ψ hψ => ?_, fun T' h => ?_⟩
    · simp only [List.mem_append] at hψ
      rcases hψ with h | h
      · exact a1 ψ h
      · exact a2 ψ h
    · skip
      have e1 := k1 T' (fun ψ hψ => h ψ (by simp [hψ]))
      have e2 := k2 T' (fun ψ hψ => h ψ (by simp [hψ]))
      clear k1 k2
      apply Deriv.impE <;> first | assumption
  | byContra _ ih1 =>
    obtain ⟨l1, a1, k1⟩ := ih1
    refine ⟨l1, fun ψ hψ => ?_, fun T' h => ?_⟩
    · exact a1 ψ hψ
    · skip
      have e1 := k1 T' (fun ψ hψ => h ψ (by simp [hψ]))
      clear k1
      apply Deriv.byContra <;> first | assumption
  | andI _ _ ih1 ih2 =>
    obtain ⟨l1, a1, k1⟩ := ih1
    obtain ⟨l2, a2, k2⟩ := ih2
    refine ⟨l1 ++ l2, fun ψ hψ => ?_, fun T' h => ?_⟩
    · simp only [List.mem_append] at hψ
      rcases hψ with h | h
      · exact a1 ψ h
      · exact a2 ψ h
    · skip
      have e1 := k1 T' (fun ψ hψ => h ψ (by simp [hψ]))
      have e2 := k2 T' (fun ψ hψ => h ψ (by simp [hψ]))
      clear k1 k2
      apply Deriv.andI <;> first | assumption
  | andL _ ih1 =>
    obtain ⟨l1, a1, k1⟩ := ih1
    refine ⟨l1, fun ψ hψ => ?_, fun T' h => ?_⟩
    · exact a1 ψ hψ
    · skip
      have e1 := k1 T' (fun ψ hψ => h ψ (by simp [hψ]))
      clear k1
      apply Deriv.andL <;> first | assumption
  | andR _ ih1 =>
    obtain ⟨l1, a1, k1⟩ := ih1
    refine ⟨l1, fun ψ hψ => ?_, fun T' h => ?_⟩
    · exact a1 ψ hψ
    · skip
      have e1 := k1 T' (fun ψ hψ => h ψ (by simp [hψ]))
      clear k1
      apply Deriv.andR <;> first | assumption
  | orL _ ih1 =>
    obtain ⟨l1, a1, k1⟩ := ih1
    refine ⟨l1, fun ψ hψ => ?_, fun T' h => ?_⟩
    · exact a1 ψ hψ
    · skip
      have e1 := k1 T' (fun ψ hψ => h ψ (by simp [hψ]))
      clear k1
      apply Deriv.orL <;> first | assumption
  | orR _ ih1 =>
    obtain ⟨l1, a1, k1⟩ := ih1
    refine ⟨l1, fun ψ hψ => ?_, fun T' h => ?_⟩
    · exact a1 ψ hψ
    · skip
      have e1 := k1 T' (fun ψ hψ => h ψ (by simp [hψ]))
      clear k1
      apply Deriv.orR <;> first | assumption
  | orE _ _ _ ih1 ih2 ih3 =>
    obtain ⟨l1, a1, k1⟩ := ih1
    obtain ⟨l2, a2, k2⟩ := ih2
    obtain ⟨l3, a3, k3⟩ := ih3
    refine ⟨l1 ++ l2 ++ l3, fun ψ hψ => ?_, fun T' h => ?_⟩
    · simp only [List.mem_append] at hψ
      rcases hψ with (h | h) | h
      · exact a1 ψ h
      · exact a2 ψ h
      · exact a3 ψ h
    · skip
      have e1 := k1 T' (fun ψ hψ => h ψ (by simp [hψ]))
      have e2 := k2 T' (fun ψ hψ => h ψ (by simp [hψ]))
      have e3 := k3 T' (fun ψ hψ => h ψ (by simp [hψ]))
      clear k1 k2 k3
      apply Deriv.orE <;> first | assumption
  | allI _ _ ih1 =>
    obtain ⟨l1, a1, k1⟩ := ih1
    refine ⟨l1, fun ψ hψ => ?_, fun T' h => ?_⟩
    · exact a1 ψ hψ
    · skip
      have e1 := k1 T' (fun ψ hψ => h ψ (by simp [hψ]))
      clear k1
      apply Deriv.allI <;> first | assumption
  | allE _ _ _ _ ih1 =>
    obtain ⟨l1, a1, k1⟩ := ih1
    refine ⟨l1, fun ψ hψ => ?_, fun T' h => ?_⟩
    · exact a1 ψ hψ
    · skip
      have e1 := k1 T' (fun ψ hψ => h ψ (by simp [hψ]))
      clear k1
      apply Deriv.allE <;> first | assumption
  | exI _ _ _ _ ih1 =>
    obtain ⟨l1, a1, k1⟩ := ih1
    refine ⟨l1, fun ψ hψ => ?_, fun T' h => ?_⟩
    · exact a1 ψ hψ
    · skip
      have e1 := k1 T' (fun ψ hψ => h ψ (by simp [hψ]))
      clear k1
      apply Deriv.exI <;> first | assumption
  | exE _ _ _ ih1 ih2 =>
    obtain ⟨l1, a1, k1⟩ := ih1
    obtain ⟨l2, a2, k2⟩ := ih2
    refine ⟨l1 ++ l2, fun ψ hψ => ?_, fun T' h => ?_⟩
    · simp only [List.mem_append] at hψ
      rcases hψ with h | h
      · exact a1 ψ h
      · exact a2 ψ h
    · skip
      have e1 := k1 T' (fun ψ hψ => h ψ (by simp [hψ]))
      have e2 := k2 T' (fun ψ hψ => h ψ (by simp [hψ]))
      clear k1 k2
      apply Deriv.exE <;> first | assumption
  | refl _ _ =>
    refine ⟨[], fun ψ hψ => ?_, fun T' h => ?_⟩
    · simp at hψ
    · skip
      apply Deriv.refl <;> first | assumption
  | symm _ _ ih1 =>
    obtain ⟨l1, a1, k1⟩ := ih1
    refine ⟨l1, fun ψ hψ => ?_, fun T' h => ?_⟩
    · exact a1 ψ hψ
    · skip
      have e1 := k1 T' (fun ψ hψ => h ψ (by simp [hψ]))
      clear k1
      apply Deriv.symm <;> first | assumption
  | trans _ _ _ ih1 ih2 =>
    obtain ⟨l1, a1, k1⟩ := ih1
    obtain ⟨l2, a2, k2⟩ := ih2
    refine ⟨l1 ++ l2, fun ψ hψ => ?_, fun T' h => ?_⟩
    · simp only [List.mem_append] at hψ
      rcases hψ with h | h
      · exact a1 ψ h
      · exact a2 ψ h
    · skip
      have e1 := k1 T' (fun ψ hψ => h ψ (by simp [hψ]))
      have e2 := k2 T' (fun ψ hψ => h ψ (by simp [hψ]))
      clear k1 k2
      apply Deriv.trans <;> first | assumption
  | subst _ _ _ _ _ ih1 ih2 =>
    obtain ⟨l1, a1, k1⟩ := ih1
    obtain ⟨l2, a2, k2⟩ := ih2
    refine ⟨l1 ++ l2, fun ψ hψ => ?_, fun T' h => ?_⟩
    · simp only [List.mem_append] at hψ
      rcases hψ with h | h
      · exact a1 ψ h
      · exact a2 ψ h
    · skip
      have e1 := k1 T' (fun ψ hψ => h ψ (by simp [hψ]))
      have e2 := k2 T' (fun ψ hψ => h ψ (by simp [hψ]))
      clear k1 k2
      apply Deriv.subst <;> first | assumption
  | funExt _ ih1 =>
    obtain ⟨l1, a1, k1⟩ := ih1
    refine ⟨l1, fun ψ hψ => ?_, fun T' h => ?_⟩
    · exact a1 ψ hψ
    · skip
      have e1 := k1 T' (fun ψ hψ => h ψ (by simp [hψ]))
      clear k1
      apply Deriv.funExt <;> first | assumption
  | funApp _ ih1 =>
    obtain ⟨l1, a1, k1⟩ := ih1
    refine ⟨l1, fun ψ hψ => ?_, fun T' h => ?_⟩
    · exact a1 ψ hψ
    · skip
      have e1 := k1 T' (fun ψ hψ => h ψ (by simp [hψ]))
      clear k1
      apply Deriv.funApp <;> first | assumption
  | wExt _ ih1 =>
    obtain ⟨l1, a1, k1⟩ := ih1
    refine ⟨l1, fun ψ hψ => ?_, fun T' h => ?_⟩
    · exact a1 ψ hψ
    · skip
      have e1 := k1 T' (fun ψ hψ => h ψ (by simp [hψ]))
      clear k1
      apply Deriv.wExt <;> first | assumption
  | wApp _ ih1 =>
    obtain ⟨l1, a1, k1⟩ := ih1
    refine ⟨l1, fun ψ hψ => ?_, fun T' h => ?_⟩
    · exact a1 ψ hψ
    · skip
      have e1 := k1 T' (fun ψ hψ => h ψ (by simp [hψ]))
      clear k1
      apply Deriv.wApp <;> first | assumption
  | propExt _ _ ih1 ih2 =>
    obtain ⟨l1, a1, k1⟩ := ih1
    obtain ⟨l2, a2, k2⟩ := ih2
    refine ⟨l1 ++ l2, fun ψ hψ => ?_, fun T' h => ?_⟩
    · simp only [List.mem_append] at hψ
      rcases hψ with h | h
      · exact a1 ψ h
      · exact a2 ψ h
    · skip
      have e1 := k1 T' (fun ψ hψ => h ψ (by simp [hψ]))
      have e2 := k2 T' (fun ψ hψ => h ψ (by simp [hψ]))
      clear k1 k2
      apply Deriv.propExt <;> first | assumption
  | betaL _ _ =>
    refine ⟨[], fun ψ hψ => ?_, fun T' h => ?_⟩
    · simp at hψ
    · skip
      apply Deriv.betaL <;> first | assumption
  | betaWI _ _ _ ih1 =>
    obtain ⟨l1, a1, k1⟩ := ih1
    refine ⟨l1, fun ψ hψ => ?_, fun T' h => ?_⟩
    · exact a1 ψ hψ
    · skip
      have e1 := k1 T' (fun ψ hψ => h ψ (by simp [hψ]))
      clear k1
      apply Deriv.betaWI <;> first | assumption
  | betaWE _ _ _ ih1 =>
    obtain ⟨l1, a1, k1⟩ := ih1
    refine ⟨l1, fun ψ hψ => ?_, fun T' h => ?_⟩
    · exact a1 ψ hψ
    · skip
      have e1 := k1 T' (fun ψ hψ => h ψ (by simp [hψ]))
      clear k1
      apply Deriv.betaWE <;> first | assumption
  | leib a r M i h1 h2 _ _ ih1 ih2 =>
    obtain ⟨l1, a1, k1⟩ := ih1
    obtain ⟨l2, a2, k2⟩ := ih2
    refine ⟨l1 ++ l2, fun ψ hψ => ?_, fun T' h => ?_⟩
    · simp only [List.mem_append] at hψ
      rcases hψ with h | h
      · exact a1 ψ h
      · exact a2 ψ h
    · skip
      have e1 := k1 T' (fun ψ hψ => h ψ (by simp [hψ]))
      have e2 := k2 T' (fun ψ hψ => h ψ (by simp [hψ]))
      clear k1 k2
      exact Deriv.leib a r M i h1 h2 e1 e2

open Classical in
/-- **Compactness of K4's certified calculus**, hence (by completeness) of validity over v4's 𝓛-general
models: if `φ` holds in every 𝓛-general model of `T` with nonempty individuals, it holds in every such
model of some finite list of members of `T`. -/
theorem compactness {T : Tm [] .s → Prop} {φ : Tm [] .s} (H : ValidV4 T φ) :
    ∃ l : List (Tm [] .s), (∀ ψ, ψ ∈ l → T ψ) ∧ ValidV4 (fun ψ => ψ ∈ l) φ := by
  obtain ⟨l, hl, k⟩ := Deriv.finite (sound_complete_all.2 H)
  refine ⟨l.filter (fun ψ => decide (T ψ)), ?_, ?_⟩
  · intro ψ hψ
    simpa using (List.mem_filter.1 hψ).2
  · apply sound_complete_all.1
    apply k
    intro ψ hψ
    by_cases hT : T ψ
    · exact .inl (List.mem_filter.2 ⟨hψ, by simpa using hT⟩)
    · rcases hl ψ hψ with h | h
      · exact absurd h hT
      · exact .inr h

end
end Programme.«20261022-1724-ontological».ThCanon



/-! ## The separating sentence: countable but no finite countermodel (pr, round 9)
Composition of K8 (`sep_not_valid_v4`), K11 (`sep_finite`) and th's `lowenheim_skolem`. -/

namespace Programme.«20261022-1724-ontological».Run3.SepLS
open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.SepV2.Sep Programme.«20261022-1724-ontological».ThCanon

/-- **Countably infinite is the threshold for `A ∃p.(Atom p ∧ p)` over variant 2.** There is a v4
𝓛-general model with nonempty individuals in which variant 2 (`Ax1Gen`, `Ax2a`, `Ax2b`, `Ax3`, `Ax4`)
holds at every world and `A ∃p.(Atom p ∧ p)` fails at some world, whose worlds and carriers at every
type inject into `Nat` and whose worlds are not a finite list; and every v4 𝓛-general model with
finitely many worlds satisfies the sentence at every world. -/
theorem sep_threshold :
    (∃ (W : Type) (M : VM W) (L : LGen M), Ctbl W ∧ (∀ t, Ctbl (M.C t)) ∧ Nonempty (M.C .e) ∧
      (∀ ψ, Programme.«20261022-1724-ontological».Run3.SepV2.V2.T2 ψ → ∀ w, M.pr (L.ev ψ ()) w) ∧
      (∃ w, ¬ M.pr (L.ev phiSep ()) w) ∧ ¬ ∃ l : List W, ∀ w, w ∈ l) ∧
    (∀ (W : Type) (M : VM W) (L : LGen M), (∃ l : List W, ∀ w, w ∈ l) →
      ∀ w, M.pr (L.ev phiSep ()) w) := by
  refine ⟨?_, fun W M L hfin w => Programme.«20261022-1724-ontological».Run3.SepR.sep_finite M L hfin w⟩
  have hn : ¬ ValidV4 (withNE Programme.«20261022-1724-ontological».Run3.SepV2.V2.T2) phiSep := fun H =>
    Programme.«20261022-1724-ontological».Run3.SepV2.V2.sep_not_valid_v4 (validV4_withNE.1 H)
  obtain ⟨W, M, L, hW, hC, hne, hT, w, hw⟩ := lowenheim_skolem (.inr rfl) hn
  exact ⟨W, M, L, hW, hC, hne, fun ψ hψ => hT ψ (.inl hψ), ⟨w, hw⟩,
    fun hfin => hw (Programme.«20261022-1724-ontological».Run3.SepR.sep_finite M L hfin w)⟩

end Programme.«20261022-1724-ontological».Run3.SepLS



/-! # Target C (b): v4's `prop:lgeneral` for a calculus with unrestricted Leibniz (th, round 9)

`DG T ok okL`: K4's natural deduction, except that the two equality-substitution rules (`subst` at
plain types, `leib` with an `𝓛`-motive) are replaced by one **Leibniz rule at every type with an
arbitrary motive** `φ : HTerm (a :: Γ) o`, as Lean's `Eq.mpr`/`congrArg` allow.  `ok` constrains
the instances of `∀E`/`∃I`, `okL a φ s t` the Leibniz steps.

`WT u` (whole-term): every argument of an application at a type of `𝓛` anywhere in `u` is a term
of `𝓛` (`Cert`).  This is v4's position clause: an argument of a constant of the signature (`pos`)
or of a variable of a type of `𝓛`, or of any other head (stricter than v4, which reads terms
modulo β, where every application is headed by a constant or a variable).

`LeibOK a φ s t`: `a` is a type at which relativised equality is identity, or the motive is `WT`
and both sides are terms of `𝓛`.  Soundness (`sound_wt`, `sound_v4_wt`) needs `WT` only for
Leibniz motives; v4's hypothesis asks it of every line. -/

namespace Programme.«20261022-1724-ontological».ThWhole
open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.HOLX Programme.«20261022-1724-ontological».Run3.V4 Programme.«20261022-1724-ontological».ThCanon

variable {W D : Type}

def WT : {Γ : List HTy} → {a : HTy} → HTerm Γ a → Prop
  | _, _, .var _ => True
  | _, _, .appL f x => WT f ∧ Cert _ x
  | _, _, .lamL b => WT b
  | _, _, .pos => True
  | _, _, .wabs φ => WT φ
  | _, _, .holds p i => WT p ∧ WT i
  | _, _, .rel i j => WT i ∧ WT j
  | _, _, .act x i => WT x ∧ WT i
  | _, _, .bot => True
  | _, _, .imp p q => WT p ∧ WT q
  | _, _, .and p q => WT p ∧ WT q
  | _, _, .or p q => WT p ∧ WT q
  | _, _, .all _ p => WT p
  | _, _, .ex _ p => WT p
  | _, _, .eq _ s t => WT s ∧ WT t

def LeibOK {Γ : List HTy} (a : HTy) (φ : HTerm (a :: Γ) .o) (s t : HTerm Γ a) : Prop :=
  plain a = true ∨ (WT φ ∧ Cert a s ∧ Cert a t)

/-- K4's calculus with Leibniz at every type and every motive (side condition `okL`). -/
inductive DG (T : Tm [] .s → Prop) (ok : ∀ {Γ : List HTy} (a : HTy), HTerm Γ a → Prop)
    (okL : ∀ {Γ : List HTy} (a : HTy), HTerm (a :: Γ) .o → HTerm Γ a → HTerm Γ a → Prop) :
    (Γ : List HTy) → List (HTerm Γ .o) → HTerm Γ .o → Prop
  | hyp {Γ hs φ} : φ ∈ hs → DG T ok okL Γ hs φ
  | ax {Γ hs} (φ : Tm [] .s) (i : HTerm Γ .w) : T φ → DG T ok okL Γ hs (.holds (emb nilR φ) i)
  | impI {Γ hs φ ψ} : DG T ok okL Γ (φ :: hs) ψ → DG T ok okL Γ hs (.imp φ ψ)
  | impE {Γ hs φ ψ} : DG T ok okL Γ hs (.imp φ ψ) → DG T ok okL Γ hs φ → DG T ok okL Γ hs ψ
  | byContra {Γ hs φ} : DG T ok okL Γ (.imp φ .bot :: hs) .bot → DG T ok okL Γ hs φ
  | andI {Γ hs φ ψ} : DG T ok okL Γ hs φ → DG T ok okL Γ hs ψ → DG T ok okL Γ hs (.and φ ψ)
  | andL {Γ hs φ ψ} : DG T ok okL Γ hs (.and φ ψ) → DG T ok okL Γ hs φ
  | andR {Γ hs φ ψ} : DG T ok okL Γ hs (.and φ ψ) → DG T ok okL Γ hs ψ
  | orL {Γ hs φ ψ} : DG T ok okL Γ hs φ → DG T ok okL Γ hs (.or φ ψ)
  | orR {Γ hs φ ψ} : DG T ok okL Γ hs ψ → DG T ok okL Γ hs (.or φ ψ)
  | orE {Γ hs φ ψ χ} : DG T ok okL Γ hs (.or φ ψ) → DG T ok okL Γ (φ :: hs) χ →
      DG T ok okL Γ (ψ :: hs) χ → DG T ok okL Γ hs χ
  | allI {Γ hs} (a : HTy) {φ : HTerm (a :: Γ) .o} :
      DG T ok okL (a :: Γ) (hs.map wk) φ → DG T ok okL Γ hs (.all a φ)
  | allE {Γ hs} (a : HTy) {φ : HTerm (a :: Γ) .o} (t : HTerm Γ a) :
      DG T ok okL Γ hs (.all a φ) → ok a t → DG T ok okL Γ hs (inst φ t)
  | exI {Γ hs} (a : HTy) {φ : HTerm (a :: Γ) .o} (t : HTerm Γ a) :
      ok a t → DG T ok okL Γ hs (inst φ t) → DG T ok okL Γ hs (.ex a φ)
  | exE {Γ hs} (a : HTy) {φ : HTerm (a :: Γ) .o} {χ : HTerm Γ .o} :
      DG T ok okL Γ hs (.ex a φ) → DG T ok okL (a :: Γ) (φ :: hs.map wk) (wk χ) →
      DG T ok okL Γ hs χ
  | refl {Γ hs} (a : HTy) (t : HTerm Γ a) : DG T ok okL Γ hs (.eq a t t)
  | symm {Γ hs} (a : HTy) {s t : HTerm Γ a} : DG T ok okL Γ hs (.eq a s t) → DG T ok okL Γ hs (.eq a t s)
  | trans {Γ hs} (a : HTy) {s t u : HTerm Γ a} : DG T ok okL Γ hs (.eq a s t) →
      DG T ok okL Γ hs (.eq a t u) → DG T ok okL Γ hs (.eq a s u)
  | leibG {Γ hs} (a : HTy) {s t : HTerm Γ a} (φ : HTerm (a :: Γ) .o) : okL a φ s t →
      DG T ok okL Γ hs (.eq a s t) → DG T ok okL Γ hs (inst φ s) → DG T ok okL Γ hs (inst φ t)
  | funExt {Γ hs a b} {f g : HTerm Γ (.L (.arr a b))} :
      DG T ok okL Γ hs (.all (.L a) (.eq (.L b) (.appL (wk f) var0) (.appL (wk g) var0))) →
      DG T ok okL Γ hs (.eq (.L (.arr a b)) f g)
  | funApp {Γ hs a b} {f g : HTerm Γ (.L (.arr a b))} :
      DG T ok okL Γ hs (.eq (.L (.arr a b)) f g) →
      DG T ok okL Γ hs (.all (.L a) (.eq (.L b) (.appL (wk f) var0) (.appL (wk g) var0)))
  | wExt {Γ hs} {p q : HTerm Γ (.L .s)} :
      DG T ok okL Γ hs (.all .w (.eq .o (.holds (wk p) var0) (.holds (wk q) var0))) →
      DG T ok okL Γ hs (.eq (.L .s) p q)
  | wApp {Γ hs} {p q : HTerm Γ (.L .s)} :
      DG T ok okL Γ hs (.eq (.L .s) p q) →
      DG T ok okL Γ hs (.all .w (.eq .o (.holds (wk p) var0) (.holds (wk q) var0)))
  | propExt {Γ hs φ ψ} : DG T ok okL Γ (φ :: hs) ψ → DG T ok okL Γ (ψ :: hs) φ →
      DG T ok okL Γ hs (.eq .o φ ψ)
  | betaL {Γ hs a b} (body : HTerm (.L a :: Γ) (.L b)) (x : HTerm Γ (.L a)) :
      DG T ok okL Γ hs (.eq (.L b) (.appL (.lamL body) x) (inst body x))
  | betaWI {Γ hs} (φ : HTerm (.w :: Γ) .o) (i : HTerm Γ .w) :
      DG T ok okL Γ hs (inst φ i) → DG T ok okL Γ hs (.holds (.wabs φ) i)
  | betaWE {Γ hs} (φ : HTerm (.w :: Γ) .o) (i : HTerm Γ .w) :
      DG T ok okL Γ hs (.holds (.wabs φ) i) → DG T ok okL Γ hs (inst φ i)

/-- The whole-term calculus: `∀E`/`∃I` instances and Leibniz steps as in v4's hypothesis. -/
abbrev DW (T : Tm [] .s → Prop) := DG T (fun a t => Cert a t) (fun a φ s t => LeibOK a φ s t)

/-! ## A logical relation for relativised equality -/

/-- `LR t x y`: `x`, `y` send admitted `eqT`-equal arguments to related values. -/
def LR (S : Str W D) : (t : FTy) → Den W D t → Den W D t → Prop
  | .e, x, y => x = y
  | .s, x, y => x = y
  | .arr a b, F, G => ∀ z z', S.A a z → S.A a z' → eqT S a z z' → LR S b (F z) (G z')

def RH (S : Str W D) : (a : HTy) → HDen W D a → HDen W D a → Prop
  | .L t, x, y => LR S t x y
  | .w, x, y => x = y
  | .o, x, y => (x ↔ y)

theorem LR_eqT_iff (S : Str W D) : ∀ (t : FTy) {x x' y y' : Den W D t},
    LR S t x x' → LR S t y y' → (eqT S t x y ↔ eqT S t x' y')
  | .e, _, _, _, _, hx, hy => by
      show _ = _ ↔ _ = _
      have hx' : _ = _ := hx; have hy' : _ = _ := hy; rw [hx', hy']
  | .s, _, _, _, _, hx, hy => by
      show _ = _ ↔ _ = _
      have hx' : _ = _ := hx; have hy' : _ = _ := hy; rw [hx', hy']
  | .arr a b, x, x', y, y', hx, hy => by
      show (∀ z, S.A a z → eqT S b (x z) (y z)) ↔ (∀ z, S.A a z → eqT S b (x' z) (y' z))
      exact ⟨fun H z hz => (LR_eqT_iff S b (hx z z hz hz (eqT_refl S a z))
          (hy z z hz hz (eqT_refl S a z))).1 (H z hz),
        fun H z hz => (LR_eqT_iff S b (hx z z hz hz (eqT_refl S a z))
          (hy z z hz hz (eqT_refl S a z))).2 (H z hz)⟩

theorem adm_LR (S : Str W D) (hC : Closed S) (hR : Resp S) : ∀ (t : FTy) {x y : Den W D t},
    S.A t x → S.A t y → eqT S t x y → LR S t x y
  | .e, _, _, _, _, h => h
  | .s, _, _, _, _, h => h
  | .arr a b, F, G, hF, hG, h => fun z z' hz hz' hzz =>
      adm_LR S hC hR b (adm_app S hC F z hF hz) (adm_app S hC G z' hG hz')
        (eqT_trans S b (hR a b F hF z z' hz hz' hzz) (h z' hz'))

theorem envR_pull (S : Str W D) {ρ ρ' : HEnv W D Γ}
    (h : ∀ {b} (v : HVar Γ b), EqH S b (ρ v) (ρ' v)) :
    ∀ {Γ' : List FTy} (r : LRen Γ' Γ), EnvR S Γ' (pull r ρ) (pull r ρ')
  | [], _ => trivial
  | _ :: _, r => ⟨h (r .zero), envR_pull S h (fun v => r (.succ v))⟩

theorem rel_cons (S : Str W D) {ρ ρ' : HEnv W D Γ}
    (h : ∀ {b} (v : HVar Γ b), EqH S b (ρ v) (ρ' v)) {x x' : HDen W D a} (hx : EqH S a x x') :
    ∀ {b} (v : HVar (a :: Γ) b), EqH S b (cons x ρ v) (cons x' ρ' v) := by
  intro b v; cases v with
  | zero => exact hx
  | succ v => exact h v

/-- **Congruence for whole-term formulas**: a `WT` term sends pointwise `EqH`-related admitted
environments to `RH`-related values. -/
theorem cong (S : Str W D) (hE : ∀ x, S.A .e x) (hC : Closed S) (hR : Resp S) :
    ∀ {Γ a} (u : HTerm Γ a), WT u → ∀ (ρ ρ' : HEnv W D Γ), AdmEnv S ρ → AdmEnv S ρ' →
      (∀ {b} (v : HVar Γ b), EqH S b (ρ v) (ρ' v)) → RH S a (heval S u ρ) (heval S u ρ')
  | _, .L t, .var v, _, ρ, ρ', hA, hA', h => adm_LR S hC hR t (hA v) (hA' v) (h v)
  | _, .w, .var v, _, ρ, ρ', _, _, h => h v
  | _, .o, .var v, _, ρ, ρ', _, _, h => h v
  | _, _, .appL f x, hw, ρ, ρ', hA, hA', h => by
      obtain ⟨hf, hx⟩ : WT f ∧ Cert _ x := hw
      have hF := cong S hE hC hR f hf ρ ρ' hA hA' h
      have ha := cert_rng S hE hC hA _ x hx
      have ha' := cert_rng S hE hC hA' _ x hx
      obtain ⟨_, s, r, rfl⟩ := hx
      have e : eqT S _ (heval S (emb r s) ρ) (heval S (emb r s) ρ') := by
        rw [heval_emb S hE, heval_emb S hE]
        exact fund S hE hC hR s _ _ (envA_pull S hA r) (envA_pull S hA' r) (envR_pull S h r)
      exact hF _ _ ha ha' e
  | _, _, .lamL b, hb, ρ, ρ', hA, hA', h => fun z z' hz hz' hzz => by
      show RH S (.L _) (heval S b (cons (a := .L _) z ρ)) (heval S b (cons (a := .L _) z' ρ'))
      exact cong S hE hC hR b hb (cons z ρ) (cons z' ρ') (admEnv_cons S hA (a := .L _) hz) (admEnv_cons S hA' (a := .L _) hz')
        (rel_cons S h (a := .L _) hzz)
  | _, _, .pos, _, _, _, _, _, _ => adm_LR S hC hR th (hC (Γ := []) .pos () trivial)
      (hC (Γ := []) .pos () trivial) (eqT_refl S th _)
  | _, _, .wabs φ, hφ, ρ, ρ', hA, hA', h => by
      show (fun u => heval S φ (cons (a := .w) u ρ)) = (fun u => heval S φ (cons (a := .w) u ρ'))
      funext u; apply propext
      exact cong S hE hC hR φ hφ (cons u ρ) (cons u ρ') (admEnv_cons S hA (a := .w) trivial)
        (admEnv_cons S hA' (a := .w) trivial) (rel_cons S h (a := .w) rfl)
  | _, _, .holds p i, hw, ρ, ρ', hA, hA', h => by
      simp only [WT] at hw; obtain ⟨hp, hi⟩ := hw
      have e1 : heval S p ρ = heval S p ρ' := cong S hE hC hR p hp ρ ρ' hA hA' h
      have e2 : heval S i ρ = heval S i ρ' := cong S hE hC hR i hi ρ ρ' hA hA' h
      show heval S p ρ (heval S i ρ) ↔ heval S p ρ' (heval S i ρ')
      rw [e1, e2]
  | _, _, .rel i j, hw, ρ, ρ', hA, hA', h => by
      simp only [WT] at hw; obtain ⟨hi, hj⟩ := hw
      have e1 : heval S i ρ = heval S i ρ' := cong S hE hC hR i hi ρ ρ' hA hA' h
      have e2 : heval S j ρ = heval S j ρ' := cong S hE hC hR j hj ρ ρ' hA hA' h
      show S.R (heval S i ρ) (heval S j ρ) ↔ S.R (heval S i ρ') (heval S j ρ')
      rw [e1, e2]
  | _, _, .act x i, hw, ρ, ρ', hA, hA', h => by
      simp only [WT] at hw; obtain ⟨hx, hi⟩ := hw
      have e1 : heval S x ρ = heval S x ρ' := cong S hE hC hR x hx ρ ρ' hA hA' h
      have e2 : heval S i ρ = heval S i ρ' := cong S hE hC hR i hi ρ ρ' hA hA' h
      show S.act (heval S x ρ) (heval S i ρ) ↔ S.act (heval S x ρ') (heval S i ρ')
      rw [e1, e2]
  | _, _, .bot, _, _, _, _, _, _ => Iff.rfl
  | _, _, .imp p q, hw, ρ, ρ', hA, hA', h => by
      simp only [WT] at hw; obtain ⟨hp, hq⟩ := hw
      exact imp_congr (cong S hE hC hR p hp ρ ρ' hA hA' h) (cong S hE hC hR q hq ρ ρ' hA hA' h)
  | _, _, .and p q, hw, ρ, ρ', hA, hA', h => by
      simp only [WT] at hw; obtain ⟨hp, hq⟩ := hw
      exact and_congr (cong S hE hC hR p hp ρ ρ' hA hA' h) (cong S hE hC hR q hq ρ ρ' hA hA' h)
  | _, _, .or p q, hw, ρ, ρ', hA, hA', h => by
      simp only [WT] at hw; obtain ⟨hp, hq⟩ := hw
      exact or_congr (cong S hE hC hR p hp ρ ρ' hA hA' h) (cong S hE hC hR q hq ρ ρ' hA hA' h)
  | _, _, .all a p, hp, ρ, ρ', hA, hA', h => by
      have e : ∀ x, Rng S a x → (heval S p (cons x ρ) ↔ heval S p (cons x ρ')) := fun x hx =>
        cong S hE hC hR p hp (cons x ρ) (cons x ρ') (admEnv_cons S hA hx) (admEnv_cons S hA' hx)
          (rel_cons S h (EqH_refl S a x))
      exact ⟨fun H x hx => (e x hx).1 (H x hx), fun H x hx => (e x hx).2 (H x hx)⟩
  | _, _, .ex a p, hp, ρ, ρ', hA, hA', h => by
      have e : ∀ x, Rng S a x → (heval S p (cons x ρ) ↔ heval S p (cons x ρ')) := fun x hx =>
        cong S hE hC hR p hp (cons x ρ) (cons x ρ') (admEnv_cons S hA hx) (admEnv_cons S hA' hx)
          (rel_cons S h (EqH_refl S a x))
      exact ⟨fun ⟨x, hx, H⟩ => ⟨x, hx, (e x hx).1 H⟩, fun ⟨x, hx, H⟩ => ⟨x, hx, (e x hx).2 H⟩⟩
  | _, _, .eq (.L t) s u, hw, ρ, ρ', hA, hA', h => by
      simp only [WT] at hw; obtain ⟨hs, hu⟩ := hw
      exact LR_eqT_iff S t (cong S hE hC hR s hs ρ ρ' hA hA' h) (cong S hE hC hR u hu ρ ρ' hA hA' h)
  | _, _, .eq .w s u, hw, ρ, ρ', hA, hA', h => by
      simp only [WT] at hw; obtain ⟨hs, hu⟩ := hw
      have e1 : heval S s ρ = heval S s ρ' := cong S hE hC hR s hs ρ ρ' hA hA' h
      have e2 : heval S u ρ = heval S u ρ' := cong S hE hC hR u hu ρ ρ' hA hA' h
      show heval S s ρ = heval S u ρ ↔ heval S s ρ' = heval S u ρ'
      rw [e1, e2]
  | _, _, .eq .o s u, hw, ρ, ρ', hA, hA', h => by
      simp only [WT] at hw; obtain ⟨hs, hu⟩ := hw
      have e1 := cong S hE hC hR s hs ρ ρ' hA hA' h
      have e2 := cong S hE hC hR u hu ρ ρ' hA hA' h
      show (heval S s ρ ↔ heval S u ρ) ↔ (heval S s ρ' ↔ heval S u ρ')
      exact iff_congr e1 e2

/-! ## Soundness of the whole-term calculus -/

theorem sound_wt (S : Str W D) (hE : ∀ x, S.A .e x) (hC : Closed S) (hR : Resp S)
    {T : Tm [] .s → Prop} (hT : ∀ φ, T φ → ∀ w, eval S φ () w) :
    ∀ {Γ hs φ}, DW T Γ hs φ →
      ∀ (ρ : HEnv W D Γ), AdmEnv S ρ → (∀ h ∈ hs, heval S h ρ) → heval S φ ρ := by
  intro Γ hs φ d
  induction d with
  | hyp m => exact fun ρ _ hh => hh _ m
  | ax φ i hφ =>
      intro ρ _ _
      show heval S (emb nilR φ) ρ (heval S i ρ)
      rw [heval_emb S hE]; exact hT φ hφ _
  | impI _ ih => exact fun ρ hρ hh hφ => ih ρ hρ (fun h m => by
      rcases List.mem_cons.1 m with rfl | m
      · exact hφ
      · exact hh h m)
  | impE _ _ ih1 ih2 => exact fun ρ hρ hh => ih1 ρ hρ hh (ih2 ρ hρ hh)
  | byContra _ ih =>
      intro ρ hρ hh
      apply Classical.byContradiction
      intro hn
      exact ih ρ hρ (fun h m => by
        rcases List.mem_cons.1 m with rfl | m
        · exact hn
        · exact hh h m)
  | andI _ _ ih1 ih2 => exact fun ρ hρ hh => ⟨ih1 ρ hρ hh, ih2 ρ hρ hh⟩
  | andL _ ih => exact fun ρ hρ hh => (ih ρ hρ hh).1
  | andR _ ih => exact fun ρ hρ hh => (ih ρ hρ hh).2
  | orL _ ih => exact fun ρ hρ hh => Or.inl (ih ρ hρ hh)
  | orR _ ih => exact fun ρ hρ hh => Or.inr (ih ρ hρ hh)
  | orE _ _ _ ih ih1 ih2 =>
      intro ρ hρ hh
      rcases ih ρ hρ hh with h | h
      · exact ih1 ρ hρ fun k m => by
          rcases List.mem_cons.1 m with rfl | m
          · exact h
          · exact hh k m
      · exact ih2 ρ hρ fun k m => by
          rcases List.mem_cons.1 m with rfl | m
          · exact h
          · exact hh k m
  | allI a _ ih =>
      intro ρ hρ hh x hx
      exact ih (cons x ρ) (admEnv_cons S hρ hx) fun k m => by
        obtain ⟨k', m', rfl⟩ := mem_map_wk m
        rw [heval_wk]; exact hh k' m'
  | allE a t _ hok ih =>
      intro ρ hρ hh
      rw [heval_inst]
      exact ih ρ hρ hh _ (cert_rng S hE hC hρ a t hok)
  | exI a t hok _ ih =>
      intro ρ hρ hh
      have := ih ρ hρ hh
      rw [heval_inst] at this
      exact ⟨_, cert_rng S hE hC hρ a t hok, this⟩
  | exE a _ _ ih1 ih2 =>
      intro ρ hρ hh
      obtain ⟨x, hx, hφ⟩ := ih1 ρ hρ hh
      have := ih2 (cons x ρ) (admEnv_cons S hρ hx) fun k m => by
        rcases List.mem_cons.1 m with rfl | m
        · exact hφ
        · obtain ⟨k', m', rfl⟩ := mem_map_wk m
          rw [heval_wk]; exact hh k' m'
      rwa [heval_wk] at this
  | refl a t => exact fun ρ _ _ => EqH_refl S a _
  | symm a _ ih => exact fun ρ hρ hh => EqH_symm S a (ih ρ hρ hh)
  | trans a _ _ ih1 ih2 => exact fun ρ hρ hh => EqH_trans S a (ih1 ρ hρ hh) (ih2 ρ hρ hh)
  | @leibG Γ _ a s t φ hok _ _ ih1 ih2 =>
      intro ρ hρ hh
      have e : EqH S a (heval S s ρ) (heval S t ρ) := ih1 ρ hρ hh
      have d := ih2 ρ hρ hh
      rw [heval_inst] at d ⊢
      rcases hok with hp | ⟨hφ, hs, ht⟩
      · rwa [← EqH_plain S hE a hp e]
      · exact (cong S hE hC hR φ hφ (cons (heval S s ρ) ρ) (cons (heval S t ρ) ρ)
          (admEnv_cons S hρ (cert_rng S hE hC hρ a s hs))
          (admEnv_cons S hρ (cert_rng S hE hC hρ a t ht))
          (rel_cons S (fun v => EqH_refl S _ (ρ v)) e)).1 d
  | funExt _ ih =>
      intro ρ hρ hh z hz
      have := ih ρ hρ hh z hz
      simpa only [heval, heval_wk, var0, cons, EqH] using this
  | funApp _ ih =>
      intro ρ hρ hh z hz
      have := ih ρ hρ hh z hz
      simpa only [heval, heval_wk, var0, cons, EqH] using this
  | wExt _ ih =>
      intro ρ hρ hh
      funext u
      have := ih ρ hρ hh u trivial
      simp only [heval, heval_wk, cons, EqH] at this
      exact propext this
  | wApp _ ih =>
      intro ρ hρ hh u _
      have := ih ρ hρ hh
      simp only [heval, heval_wk, cons, EqH]
      show _ ↔ _
      exact Iff.of_eq (congrFun this u)
  | propExt _ _ ih1 ih2 =>
      intro ρ hρ hh
      constructor
      · intro h; exact ih1 ρ hρ fun k m => by
          rcases List.mem_cons.1 m with rfl | m
          · exact h
          · exact hh k m
      · intro h; exact ih2 ρ hρ fun k m => by
          rcases List.mem_cons.1 m with rfl | m
          · exact h
          · exact hh k m
  | betaL body x =>
      intro ρ _ _
      show eqT S _ _ _
      simp only [heval, heval_inst]
      exact eqT_refl S _ _
  | betaWI φ i _ ih =>
      intro ρ hρ hh
      have := ih ρ hρ hh
      rw [heval_inst] at this
      exact this
  | betaWE φ i _ ih =>
      intro ρ hρ hh
      rw [heval_inst]
      exact ih ρ hρ hh

/-- **v4 `prop:lgeneral`, deep form.**  A derivation of `⟦φ⟧` at a world variable from the
`𝓛`-theory `T`, with Leibniz at every type and every motive, whose `∀E`/`∃I` instances at types
of `𝓛` are terms of `𝓛` and whose Leibniz steps at non-plain types have whole-term motives and
`𝓛`-term sides, makes `φ` true at every world of every v4 `𝓛`-general model of `T` with
nonempty individuals. -/
theorem sound_v4_wt {T : Tm [] .s → Prop} {φ : Tm [] .s}
    (d : DW T [.w] [] (.holds (emb nilR φ) var0)) : ValidV4 T φ := by
  refine (valid_iff T φ).2 fun _ _ S _ hE hC hR hT w => ?_
  have := sound_wt S hE hC hR hT d (cons (a := .w) w emptyEnv)
    (admEnv_cons (a := .w) S (fun v => by cases v) trivial) (fun _ m => by cases m)
  simp only [heval, heval_emb S hE] at this
  exact this

/-! ## K4's calculus is a fragment; by completeness, the two derive the same 𝓛-sentences -/

theorem wt_w : ∀ {Γ} (i : HTerm Γ .w), WT i
  | _, .var _ => trivial

theorem wt_emb : ∀ {Γ' Γ t} (r : LRen Γ' Γ) (tm : Tm Γ' t), WT (emb r tm)
  | _, _, _, _, .var _ => trivial
  | _, _, _, r, .app F x => ⟨wt_emb r F, ⟨_, x, r, rfl⟩⟩
  | _, _, _, r, .lam b => wt_emb (liftL r) b
  | _, _, _, _, .top => ⟨trivial, trivial⟩
  | _, _, _, _, .bot => trivial
  | _, _, _, r, .neg x => ⟨⟨wt_emb _ x, trivial⟩, trivial⟩
  | _, _, _, r, .and x y => ⟨⟨wt_emb _ x, trivial⟩, ⟨wt_emb _ y, trivial⟩⟩
  | _, _, _, r, .or x y => ⟨⟨wt_emb _ x, trivial⟩, ⟨wt_emb _ y, trivial⟩⟩
  | _, _, _, r, .imp x y => ⟨⟨wt_emb _ x, trivial⟩, ⟨wt_emb _ y, trivial⟩⟩
  | _, _, _, r, .box x => ⟨⟨trivial, trivial⟩, ⟨wt_emb _ x, trivial⟩⟩
  | _, _, _, r, .all a b => ⟨wt_emb _ b, trivial⟩
  | _, _, _, r, .ex a b => ⟨wt_emb _ b, trivial⟩
  | _, _, _, r, .allE b => ⟨⟨trivial, trivial⟩, ⟨wt_emb _ b, trivial⟩⟩
  | _, _, _, r, .exE b => ⟨⟨trivial, trivial⟩, ⟨wt_emb _ b, trivial⟩⟩
  | _, _, _, r, .eq a x y => ⟨wt_emb _ x, wt_emb _ y⟩
  | _, _, _, _, .pos => trivial

theorem of_DC {T : Tm [] .s → Prop} : ∀ {Γ hs φ}, DC T Γ hs φ → DW T Γ hs φ := by
  intro Γ hs φ d
  induction d with
  | hyp m => exact .hyp m
  | ax φ i h => exact .ax φ i h
  | impI _ ih => exact .impI ih
  | impE _ _ ih1 ih2 => exact .impE ih1 ih2
  | byContra _ ih => exact .byContra ih
  | andI _ _ ih1 ih2 => exact .andI ih1 ih2
  | andL _ ih => exact .andL ih
  | andR _ ih => exact .andR ih
  | orL _ ih => exact .orL ih
  | orR _ ih => exact .orR ih
  | orE _ _ _ ih ih1 ih2 => exact .orE ih ih1 ih2
  | allI a _ ih => exact .allI a ih
  | allE a t _ hok ih => exact .allE a t ih hok
  | exI a t hok _ ih => exact .exI a t hok ih
  | exE a _ _ ih1 ih2 => exact .exE a ih1 ih2
  | refl a t => exact .refl a t
  | symm a _ ih => exact .symm a ih
  | trans a _ _ ih1 ih2 => exact .trans a ih1 ih2
  | subst a φ hp _ _ ih1 ih2 => exact .leibG a φ (.inl hp) ih1 ih2
  | funExt _ ih => exact .funExt ih
  | funApp _ ih => exact .funApp ih
  | wExt _ ih => exact .wExt ih
  | wApp _ ih => exact .wApp ih
  | propExt _ _ ih1 ih2 => exact .propExt ih1 ih2
  | betaL body x => exact .betaL body x
  | betaWI φ i _ ih => exact .betaWI φ i ih
  | betaWE φ i _ ih => exact .betaWE φ i ih
  | leib a r M i hs ht _ _ ih1 ih2 =>
      exact .leibG (.L a) _ (.inr ⟨⟨wt_emb _ M, wt_w _⟩, hs, ht⟩) ih1 ih2

/-- **Sound and complete, and conservative over K4's calculus**: for every `𝓛`-theory `T`, the
whole-term calculus derives `⟦φ⟧` from `T ∪ {∃x.⊤}` iff K4's certified calculus does iff `φ`
holds in every v4 `𝓛`-general model of `T` with nonempty individuals. -/
theorem wt_sound_complete {T : Tm [] .s → Prop} {φ : Tm [] .s} :
    (DW (withNE T) [.w] [] (.holds (emb nilR φ) var0) ↔ ValidV4 T φ) ∧
    (DW (withNE T) [.w] [] (.holds (emb nilR φ) var0) ↔ DC (withNE T) [.w] [] (.holds (emb nilR φ) var0)) :=
  have h1 : DW (withNE T) [.w] [] (.holds (emb nilR φ) var0) ↔ ValidV4 T φ :=
    ⟨fun d => validV4_withNE.1 (sound_v4_wt d), fun H => of_DC (sound_complete_all.2 H)⟩
  ⟨h1, h1.trans sound_complete_all.symm⟩

end Programme.«20261022-1724-ontological».ThWhole


namespace Programme.«20261022-1724-ontological».ThWit
open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.HOLX Programme.«20261022-1724-ontological».Run3.V4 Programme.«20261022-1724-ontological».ThCanon Programme.«20261022-1724-ontological».ThWhole

/-- `D p := ∃q. ¬q ∧ ((q ∧ p) ≠ ⊥)`, `p` the variable `0`. -/
def dT : Tm (.s :: Γ') .s :=
  .ex .s (.and (.neg (.var .zero)) (.neg (.eq .s (.and (.var .zero) (.var (.succ .zero))) .bot)))
/-- `Atom p := (p ≠ ⊥) ∧ ¬((p ∧ D p) ≠ ⊥)`. -/
def atT : Tm (.s :: Γ') .s :=
  .and (.neg (.eq .s (.var .zero) .bot)) (.neg (.neg (.eq .s (.and (.var .zero) dT) .bot)))
def bodyT : Tm (.s :: Γ') .s := .and atT (.var .zero)
/-- `∃p. Atom p ∧ p`. -/
def XT : Tm Γ' .s := .ex .s bodyT
/-- `A ∃p. (Atom p ∧ p)`. -/
def phiT : Tm Γ' .s := .eq .s XT .top

theorem phiT_eq : (phiT : Tm [] .s) = Programme.«20261022-1724-ontological».Run3.SepV2.Sep.phiSep := rfl

/-- `F := λp. (Atom p ∧ p) ∧ ¬X` and `G := λp. ⊥`, closed terms of `𝓛` of type `σ → σ`. -/
def FT : Tm Γ' (.arr .s .s) := .lam (.and bodyT (.neg XT))
def GT : Tm Γ' (.arr .s .s) := .lam .bot

variable {T : Tm [] .s → Prop}

theorem wk_emb {Γ' : List FTy} {Γ : List HTy} (r : LRen Γ' Γ) (x : Tm Γ' t) :
    wk (b := b) (emb r x) = emb (shL r) x :=
  rename_emb x _ r (shL r) (fun _ => rfl)

/-- Extensionality at `σ` for embedded terms. -/
theorem L_ext {Γ' : List FTy} {Γ : List HTy} {hs : List (HTerm Γ .o)} {r : LRen Γ' Γ} {x y : Tm Γ' .s}
    (d1 : DC T (.w :: Γ) (Lf (shL r) x var0 :: hs.map wk) (Lf (shL r) y var0))
    (d2 : DC T (.w :: Γ) (Lf (shL r) y var0 :: hs.map wk) (Lf (shL r) x var0)) :
    DC T Γ hs (.eq (.L .s) (emb r x) (emb r y)) := by
  refine Deriv.wExt (Deriv.allI _ (Deriv.propExt ?_ ?_))
  · rw [wk_emb, wk_emb]; exact d1
  · rw [wk_emb, wk_emb]; exact d2

theorem hyp0 {Γ : List HTy} {hs : List (HTerm Γ .o)} {φ : HTerm Γ .o} : DC T Γ (φ :: hs) φ :=
  Deriv.hyp (List.mem_cons_self ..)

/-- `F = G` in K4's certified calculus (every quantifier instance a term of `𝓛`). -/
theorem FG {Γ' : List FTy} {Γ : List HTy} {hs : List (HTerm Γ .o)} (r : LRen Γ' Γ) :
    DC T Γ hs (.eq (.L (.arr .s .s)) (emb r FT) (emb r GT)) := by
  refine Deriv.funExt (Deriv.allI _ ?_)
  show DC T _ _ (.eq (.L .s) (emb (liftL r) (.app FT (.var .zero))) (emb (liftL r) (.app GT (.var .zero))))
  refine L_ext ?_ ?_
  · have h0 : DC T _ (Lf (shL (liftL r)) (.app FT (.var .zero)) var0 :: (hs.map wk).map wk) (Lf (shL (liftL r)) (instL (Γ := .s :: Γ') (.and bodyT (.neg XT)) (.var .zero)) var0) :=
      L_betaE hyp0
    have h := L_andE (x := bodyT) (y := .neg XT) h0
    have hb := Deriv.andL h
    have hn := L_negE (Deriv.andR h)
    exact Deriv.exFalso (Deriv.impE hn (L_exI (b := bodyT) (.var .zero) hb))
  · exact L_botE (L_betaE (b := .bot) hyp0)

/-- Witness criterion alone: `∀E`/`∃I` instances at types of `𝓛` are terms of `𝓛`, Leibniz unrestricted. -/
abbrev DG3 (T : Tm [] .s → Prop) := DG T (fun a t => Cert a t) (fun _ _ _ _ => True)

theorem DG.mono {T : Tm [] .s → Prop} {ok : ∀ {Γ : List HTy} (a : HTy), HTerm Γ a → Prop}
    {okL okL' : ∀ {Γ : List HTy} (a : HTy), HTerm (a :: Γ) .o → HTerm Γ a → HTerm Γ a → Prop}
    (hL : ∀ {Γ : List HTy} (a : HTy) (φ : HTerm (a :: Γ) .o) s t, okL a φ s t → okL' a φ s t) :
    ∀ {Γ hs φ}, DG T ok okL Γ hs φ → DG T ok okL' Γ hs φ := by
  intro Γ hs φ d
  induction d with
  | hyp m => exact .hyp m
  | ax φ i h => exact .ax φ i h
  | impI _ ih => exact .impI ih
  | impE _ _ ih1 ih2 => exact .impE ih1 ih2
  | byContra _ ih => exact .byContra ih
  | andI _ _ ih1 ih2 => exact .andI ih1 ih2
  | andL _ ih => exact .andL ih
  | andR _ ih => exact .andR ih
  | orL _ ih => exact .orL ih
  | orR _ ih => exact .orR ih
  | orE _ _ _ ih ih1 ih2 => exact .orE ih ih1 ih2
  | allI a _ ih => exact .allI a ih
  | allE a t _ hok ih => exact .allE a t ih hok
  | exI a t hok _ ih => exact .exI a t hok ih
  | exE a _ _ ih1 ih2 => exact .exE a ih1 ih2
  | refl a t => exact .refl a t
  | symm a _ ih => exact .symm a ih
  | trans a _ _ ih1 ih2 => exact .trans a ih1 ih2
  | leibG a φ h _ _ ih1 ih2 => exact .leibG a φ (hL a φ _ _ h) ih1 ih2
  | funExt _ ih => exact .funExt ih
  | funApp _ ih => exact .funApp ih
  | wExt _ ih => exact .wExt ih
  | wApp _ ih => exact .wApp ih
  | propExt _ _ ih1 ih2 => exact .propExt ih1 ih2
  | betaL body x => exact .betaL body x
  | betaWI φ i _ ih => exact .betaWI φ i ih
  | betaWE φ i _ ih => exact .betaWE φ i ih

/-- K4's certified calculus is a fragment of the witness-only calculus. -/
theorem lift {Γ hs φ} (d : DC T Γ hs φ) : DG3 T Γ hs φ :=
  DG.mono (fun _ _ _ _ _ => trivial) (of_DC d)

/-- The nominal `λv. v = u` of the world variable `u` (not a term of `𝓛`). -/
def Nom : HTerm (.w :: Γ0) (.L .s) := .wabs (.eq .w var0 (.var (.succ .zero)))

/-- Normalise substitutions and embeddings in the goal. -/
macro "nrm" : tactic => `(tactic| simp only [inst, subst, sub0, liftS, wk, rename, liftR, emb, shL, liftL,
  XT, bodyT, atT, dT, Nom, Lf, FT, GT, List.map_cons])
macro "nrm" "at" h:ident : tactic => `(tactic| simp only [inst, subst, sub0, liftS, wk, rename, liftR, emb,
  shL, liftL, XT, bodyT, atT, dT, Nom, Lf, FT, GT, List.map_cons] at $h:ident)

theorem withHyp {Γ : List HTy} {hs : List (HTerm Γ .o)} {φ ψ : HTerm Γ .o}
    (k : DG3 T Γ (φ :: hs) φ → DG3 T Γ (φ :: hs) ψ) : DG3 T Γ (φ :: hs) ψ :=
  k (DG.hyp (List.mem_cons_self ..))

theorem withHyp12 {Γ : List HTy} {hs : List (HTerm Γ .o)} {φ φ' ψ : HTerm Γ .o}
    (k : DG3 T Γ (φ :: φ' :: hs) φ → DG3 T Γ (φ :: φ' :: hs) φ' → DG3 T Γ (φ :: φ' :: hs) ψ) :
    DG3 T Γ (φ :: φ' :: hs) ψ :=
  k (DG.hyp (List.mem_cons_self ..)) (DG.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..)))

theorem withHyp123 {Γ : List HTy} {hs : List (HTerm Γ .o)} {φ φ' φ'' ψ : HTerm Γ .o}
    (k : DG3 T Γ (φ :: φ' :: φ'' :: hs) φ → DG3 T Γ (φ :: φ' :: φ'' :: hs) φ' →
      DG3 T Γ (φ :: φ' :: φ'' :: hs) φ'' → DG3 T Γ (φ :: φ' :: φ'' :: hs) ψ) :
    DG3 T Γ (φ :: φ' :: φ'' :: hs) ψ :=
  k (DG.hyp (List.mem_cons_self ..)) (DG.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    (DG.hyp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))

/-- Ex falso from the second hypothesis `⊥` at a world (`⟦⊥⟧ i`). -/
theorem botHyp {Γ : List HTy} {hs : List (HTerm Γ .o)} {i : HTerm Γ .w} {ψ : HTerm Γ .o} :
    DG3 T Γ (.holds (.wabs .bot) i :: hs) ψ :=
  DG.byContra (DG.betaWE _ _ (DG.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..))))

/-- The cut rule. -/
theorem cutG {Γ : List HTy} {hs : List (HTerm Γ .o)} {φ ψ : HTerm Γ .o}
    (d : DG3 T Γ hs φ) (k : DG3 T Γ (φ :: hs) ψ) : DG3 T Γ hs ψ := DG.impE (DG.impI k) d

theorem cut2 {Γ : List HTy} {hs : List (HTerm Γ .o)} {φ φ' ψ : HTerm Γ .o}
    (d : DG3 T Γ hs φ) (d' : DG3 T Γ hs φ') (k : DG3 T Γ (φ' :: φ :: hs) ψ) : DG3 T Γ hs ψ :=
  DG.impE (DG.impE (DG.impI (DG.impI k)) d) d'

/-- `(F N)(u)` for the nominal `N` of `u`, given `¬X(u)`: `N` is an atom true at `u`. -/
theorem FN {Γ0 : List HTy} {hs : List (HTerm (.w :: Γ0) .o)} :
    DG3 T (.w :: Γ0) (.imp (Lf nilR XT var0) .bot :: hs) (.holds (.appL (emb nilR FT) Nom) var0) := by
  have e := DG.betaL (T := T) (ok := fun a t => Cert a t) (okL := fun _ _ _ _ => True)
    (hs := .imp (Lf nilR XT var0) .bot :: hs) (emb (liftL nilR) (.and bodyT (.neg XT))) Nom
  refine DG.leibG (.L .s) (.holds var0 (.var (.succ .zero))) trivial (DG.symm _ e) ?_
  refine DG.betaWI _ _ ?_
  refine DG.andI ?_ ?_
  · refine DG.betaWI _ _ (DG.andI ?_ (DG.betaWI _ _ (DG.refl .w var0)))
    refine DG.betaWI _ _ (DG.andI ?_ ?_)
    · -- `N ≠ ⊥` at `u`
      refine DG.betaWI _ _ (DG.impI ?_)
      nrm
      refine withHyp fun h => ?_
      have h1 := DG.betaWE _ _ h
      nrm at h1
      have h3 := DG.allE .w var0 (DG.wApp h1) trivial
      nrm at h3
      exact DG.betaWE _ _ (DG.leibG .o var0 trivial h3 (DG.betaWI _ _ (DG.refl .w var0)))
    · -- `¬((N ∧ D N) ≠ ⊥)` at `u`
      refine DG.betaWI _ _ (DG.impI ?_)
      nrm
      refine withHyp fun h => ?_
      have h1 := DG.betaWE _ _ h
      nrm at h1
      refine DG.impE h1 (DG.betaWI _ _ ?_)
      nrm
      refine DG.wExt (DG.allI _ (DG.propExt ?_ botHyp))
      nrm
      refine withHyp fun h => ?_
      have h2 := DG.betaWE _ _ h
      nrm at h2
      have hvu := DG.betaWE _ _ (DG.andL h2)
      nrm at hvu
      have hD := DG.betaWE _ _ (DG.andR h2)
      nrm at hD
      refine DG.exE _ hD ?_
      nrm
      refine withHyp12 fun hq0 hh => ?_
      have hq := DG.betaWE _ _ hq0
      nrm at hq
      have h2' := DG.betaWE _ _ hh
      nrm at h2'
      have hvu := DG.betaWE _ _ (DG.andL h2')
      nrm at hvu
      have hnq := DG.betaWE _ _ (DG.andL hq)
      nrm at hnq
      have hne := DG.betaWE _ _ (DG.andR hq)
      nrm at hne
      refine DG.betaWI _ _ (DG.impE hne ?_)
      refine cut2 hvu hnq ?_
      refine DG.betaWI _ _ ?_
      nrm
      refine DG.wExt (DG.allI _ (DG.propExt ?_ botHyp))
      nrm
      refine withHyp123 fun ht hnq' hvu' => ?_
      have h5 := DG.betaWE _ _ ht
      nrm at h5
      have htu := DG.betaWE _ _ (DG.andR h5)
      nrm at htu
      have hqv := DG.leibG .w (.holds (.var (.succ (.succ .zero))) var0) trivial
        (DG.trans .w htu (DG.symm .w hvu')) (DG.andL h5)
      exact DG.betaWI _ _ (DG.impE hnq' hqv)
  · refine DG.betaWI _ _ ?_
    nrm
    exact DG.hyp (List.mem_cons_self ..)

/-- **The separating body `X = ∃p. Atom p ∧ p` at any world variable**, in the witness-only
calculus, from any theory.  The single step outside v4's whole-term hypothesis is a Leibniz
step at `σ → σ` from `F = G` (both sides closed terms of `𝓛`) whose motive `f(N)(u)` applies the
hole to the nominal `N = λv. v = u`. -/
theorem sepX {Γ0 : List HTy} {hs : List (HTerm (.w :: Γ0) .o)} :
    DG3 T (.w :: Γ0) hs (Lf nilR XT var0) := by
  refine DG.byContra ?_
  have h := DG.leibG (.L (.arr .s .s)) (.holds (.appL var0 (wk Nom)) (.var (.succ .zero))) trivial
    (lift (FG (T := T) (hs := .imp (Lf nilR XT var0) .bot :: hs) nilR)) FN
  nrm at h
  have eb := DG.betaL (T := T) (ok := fun a t => Cert a t) (okL := fun _ _ _ _ => True)
    (hs := .imp (Lf nilR XT var0) .bot :: hs) (.wabs .bot) (Nom (Γ0 := Γ0))
  nrm at eb
  exact DG.betaWE _ _ (DG.leibG (.L .s) (.holds var0 (.var (.succ .zero))) trivial eb h)

/-- **v4's separating sentence `A ∃p.(Atom p ∧ p)` is derivable from every theory in the
witness-only calculus.** -/
theorem sep_deep : DG3 T [.w] [] (.holds (emb nilR phiT) var0) := by
  refine DG.betaWI _ _ ?_
  nrm
  refine DG.wExt (DG.allI _ (DG.propExt ?_ ?_))
  · nrm
    exact DG.betaWI _ _ (DG.impI (DG.hyp (List.mem_cons_self ..)))
  · have := sepX (T := T) (Γ0 := [.w]) (hs := [.holds (emb (nilR (Γ := [.w, .w])) .top) var0])
    nrm at this
    nrm
    exact this

/-- The nominal is not a term of `𝓛`. -/
theorem nom_not_cert {Γ : List HTy} {k : HTerm (.w :: Γ) .w} : ¬ Cert (.L .s) (HTerm.wabs (.eq .w var0 k)) := by
  rintro ⟨Γ', t, r, h⟩
  cases t <;> simp [emb] at h

/-- The one Leibniz step of `sepX` outside the plain types: its sides are terms of `𝓛`, its type is
not plain, and its motive is not whole-term, so it violates exactly v4's motive clause. -/
theorem step_profile {Γ0 : List HTy} :
    Cert (.L (.arr .s .s)) (emb (nilR (Γ := .w :: Γ0)) FT) ∧ Cert (.L (.arr .s .s)) (emb (nilR (Γ := .w :: Γ0)) GT) ∧
    plain (.L (.arr .s .s)) = false ∧
    ¬ LeibOK (.L (.arr .s .s)) (.holds (.appL var0 (wk (Nom (Γ0 := Γ0)))) (.var (.succ .zero)))
      (emb nilR FT) (emb nilR GT) := by
  refine ⟨cert_emb _ _, cert_emb _ _, rfl, ?_⟩
  rintro (h | ⟨⟨⟨_, hc⟩, _⟩, _⟩)
  · exact Bool.false_ne_true h
  · exact nom_not_cert (k := .var (.succ (.succ .zero))) hc

/-- **Target C (d), deep form: the witness criterion alone does not suffice for variant 2.**
The calculus whose `∀E`/`∃I` instances at types of `𝓛` are terms of `𝓛` but whose Leibniz steps are
unrestricted derives `A ∃p.(Atom p ∧ p)` from variant 2 (indeed from every theory), while the
sentence fails in a v4 `𝓛`-general model of variant 2 (K8); with v4's motive clause added
(`DW`) every derivation is sound (`sound_v4_wt`). -/
theorem witness_alone_unsound :
    DG3 Programme.«20261022-1724-ontological».Run3.SepV2.V2.T2 [.w] [] (.holds (emb nilR Programme.«20261022-1724-ontological».Run3.SepV2.Sep.phiSep) var0) ∧
    ¬ ValidV4 Programme.«20261022-1724-ontological».Run3.SepV2.V2.T2 Programme.«20261022-1724-ontological».Run3.SepV2.Sep.phiSep ∧
    ¬ (∀ φ : Tm [] .s, DG3 Programme.«20261022-1724-ontological».Run3.SepV2.V2.T2 [.w] [] (.holds (emb nilR φ) var0) →
        ValidV4 Programme.«20261022-1724-ontological».Run3.SepV2.V2.T2 φ) ∧
    (∀ φ : Tm [] .s, DW Programme.«20261022-1724-ontological».Run3.SepV2.V2.T2 [.w] [] (.holds (emb nilR φ) var0) →
        ValidV4 Programme.«20261022-1724-ontological».Run3.SepV2.V2.T2 φ) :=
  ⟨sep_deep, Programme.«20261022-1724-ontological».Run3.SepV2.V2.sep_not_valid_v4,
    fun H => Programme.«20261022-1724-ontological».Run3.SepV2.V2.sep_not_valid_v4 (H _ sep_deep), fun _ d => sound_v4_wt d⟩

end Programme.«20261022-1724-ontological».ThWit



/-! ## Tool part `Core` -/
section

/-! # Thread H (run 6, pr): object-level helpers and the meta-level mirror of run 4's deep syntax

`Lctx`/`Lproj` read the `𝓛`-part of a HOL context; `cert_L` certifies `emb (Lproj Γ) s`.  The
`wt_*` lemmas build whole-term proofs constructor by constructor.  Meta side: `FT`/`HT`/`DT`/`LT`
mirror `FTy`/`HTy`/`HTerm`/`Tm` (de Bruijn indices), with substitution, `βη`-normalisation, the
meta `emb`, and two read-backs from `HTerm`s to `𝓛`-terms (exact, and modulo `βη`). -/

open Lean Meta
open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.HOLX
  Programme.«20261022-1724-ontological».ThWhole

namespace Programme.H

/-! ## Object level -/

/-- The `𝓛`-types of a HOL context, innermost first. -/
def Lctx : List HTy → List FTy
  | [] => []
  | .L t :: Γ => t :: Lctx Γ
  | .w :: Γ => Lctx Γ
  | .o :: Γ => Lctx Γ

/-- The renaming that reads the `𝓛`-variables of `Lctx Γ` as variables of `Γ`. -/
def Lproj : (Γ : List HTy) → LRen (Lctx Γ) Γ
  | [] => nilR
  | .L _ :: Γ => liftL (Lproj Γ)
  | .w :: Γ => shL (Lproj Γ)
  | .o :: Γ => shL (Lproj Γ)

theorem cert_L (Γ : List HTy) (t : FTy) (s : Tm (Lctx Γ) t) : Cert (.L t) (emb (Lproj Γ) s) :=
  ⟨_, s, Lproj Γ, rfl⟩
theorem cert_w (Γ : List HTy) (x : HTerm Γ .w) : Cert .w x := trivial
theorem cert_o (Γ : List HTy) (x : HTerm Γ .o) : Cert .o x := trivial

theorem leibOK_plain (Γ : List HTy) (a : HTy) (h : plain a = true) (φ : HTerm (a :: Γ) .o)
    (s t : HTerm Γ a) : LeibOK a φ s t := Or.inl h
theorem leibOK_wt (Γ : List HTy) (a : HTy) (φ : HTerm (a :: Γ) .o) (s t : HTerm Γ a)
    (h : WT φ) (hs : Cert a s) (ht : Cert a t) : LeibOK a φ s t := Or.inr ⟨h, hs, ht⟩

theorem wt_var (Γ : List HTy) (a : HTy) (v : HVar Γ a) : WT (HTerm.var v) := trivial
theorem wt_appL (Γ : List HTy) (a b : FTy) (f : HTerm Γ (.L (.arr a b))) (x : HTerm Γ (.L a))
    (hf : WT f) (hx : Cert _ x) : WT (HTerm.appL f x) := ⟨hf, hx⟩
theorem wt_lamL (Γ : List HTy) (a b : FTy) (body : HTerm (.L a :: Γ) (.L b)) (h : WT body) :
    WT (HTerm.lamL body) := h
theorem wt_pos (Γ : List HTy) : WT (HTerm.pos (Γ := Γ)) := trivial
theorem wt_wabs (Γ : List HTy) (φ : HTerm (.w :: Γ) .o) (h : WT φ) : WT (HTerm.wabs φ) := h
theorem wt_holds (Γ : List HTy) (p : HTerm Γ (.L .s)) (i : HTerm Γ .w) (hp : WT p) (hi : WT i) :
    WT (HTerm.holds p i) := ⟨hp, hi⟩
theorem wt_rel (Γ : List HTy) (i j : HTerm Γ .w) (hi : WT i) (hj : WT j) : WT (HTerm.rel i j) :=
  ⟨hi, hj⟩
theorem wt_act (Γ : List HTy) (x : HTerm Γ (.L .e)) (i : HTerm Γ .w) (hx : WT x) (hi : WT i) :
    WT (HTerm.act x i) := ⟨hx, hi⟩
theorem wt_bot (Γ : List HTy) : WT (HTerm.bot (Γ := Γ)) := trivial
theorem wt_imp (Γ : List HTy) (p q : HTerm Γ .o) (hp : WT p) (hq : WT q) : WT (HTerm.imp p q) :=
  ⟨hp, hq⟩
theorem wt_and (Γ : List HTy) (p q : HTerm Γ .o) (hp : WT p) (hq : WT q) : WT (HTerm.and p q) :=
  ⟨hp, hq⟩
theorem wt_or (Γ : List HTy) (p q : HTerm Γ .o) (hp : WT p) (hq : WT q) : WT (HTerm.or p q) :=
  ⟨hp, hq⟩
theorem wt_all (Γ : List HTy) (a : HTy) (p : HTerm (a :: Γ) .o) (h : WT p) : WT (HTerm.all a p) := h
theorem wt_ex (Γ : List HTy) (a : HTy) (p : HTerm (a :: Γ) .o) (h : WT p) : WT (HTerm.ex a p) := h
theorem wt_eq (Γ : List HTy) (a : HTy) (s t : HTerm Γ a) (hs : WT s) (ht : WT t) :
    WT (HTerm.eq a s t) := ⟨hs, ht⟩

/-! ## Meta level: types, HOL terms, `𝓛`-terms -/

inductive FT | e | s | arr (a b : FT)
  deriving BEq, Inhabited, Repr, Hashable

inductive HT | L (t : FT) | w | o
  deriving BEq, Inhabited, Repr, Hashable

def FT.plain : FT → Bool
  | .e => true
  | .s => true
  | .arr .e b => b.plain
  | .arr _ _ => false

def HT.plain : HT → Bool
  | .L t => t.plain
  | _ => true

def FT.tp : FT := .arr .e .s
def FT.th : FT := .arr FT.tp .s

def FT.toString : FT → String
  | .e => "e" | .s => "σ" | .arr a b => s!"({a.toString} → {b.toString})"
def HT.toString : HT → String
  | .L t => t.toString | .w => "w" | .o => "o"
instance : ToString FT := ⟨FT.toString⟩
instance : ToString HT := ⟨HT.toString⟩

/-- Meta mirror of `HTerm` (de Bruijn; `lamL` records its domain). -/
inductive DT where
  | var (n : Nat)
  | appL (f x : DT)
  | lamL (a : FT) (b : DT)
  | pos
  | wabs (b : DT)
  | holds (p i : DT)
  | rel (i j : DT)
  | act (x i : DT)
  | bot
  | imp (p q : DT)
  | and (p q : DT)
  | or (p q : DT)
  | all (a : HT) (b : DT)
  | ex (a : HT) (b : DT)
  | eq (a : HT) (s t : DT)
  deriving BEq, Inhabited, Repr, Hashable

/-- Meta mirror of `Tm`. -/
inductive LT where
  | var (n : Nat)
  | app (f x : LT)
  | lam (a : FT) (b : LT)
  | top | bot
  | neg (x : LT)
  | and (x y : LT) | or (x y : LT) | imp (x y : LT)
  | box (x : LT)
  | all (a : FT) (b : LT) | ex (a : FT) (b : LT)
  | allE (b : LT) | exE (b : LT)
  | eq (a : FT) (x y : LT)
  | pos
  deriving BEq, Inhabited, Repr

namespace DT

def shift (d : Nat) (c : Nat := 0) : DT → DT
  | var n => if n ≥ c then var (n + d) else var n
  | appL f x => appL (f.shift d c) (x.shift d c)
  | lamL a b => lamL a (b.shift d (c + 1))
  | pos => pos
  | wabs b => wabs (b.shift d (c + 1))
  | holds p i => holds (p.shift d c) (i.shift d c)
  | rel i j => rel (i.shift d c) (j.shift d c)
  | act x i => act (x.shift d c) (i.shift d c)
  | bot => bot
  | imp p q => imp (p.shift d c) (q.shift d c)
  | and p q => and (p.shift d c) (q.shift d c)
  | or p q => or (p.shift d c) (q.shift d c)
  | all a b => all a (b.shift d (c + 1))
  | ex a b => ex a (b.shift d (c + 1))
  | eq a s t => eq a (s.shift d c) (t.shift d c)

/-- Substitute `s` for variable `j` (and lower the variables above `j`), as `HOLX.subst`. -/
def subst (j : Nat) (s : DT) : DT → DT
  | var n => if n == j then s.shift j 0 else if n > j then var (n - 1) else var n
  | appL f x => appL (subst j s f) (subst j s x)
  | lamL a b => lamL a (subst (j + 1) s b)
  | pos => pos
  | wabs b => wabs (subst (j + 1) s b)
  | holds p i => holds (subst j s p) (subst j s i)
  | rel i k => rel (subst j s i) (subst j s k)
  | act x i => act (subst j s x) (subst j s i)
  | bot => bot
  | imp p q => imp (subst j s p) (subst j s q)
  | and p q => and (subst j s p) (subst j s q)
  | or p q => or (subst j s p) (subst j s q)
  | all a b => all a (subst (j + 1) s b)
  | ex a b => ex a (subst (j + 1) s b)
  | eq a x y => eq a (subst j s x) (subst j s y)

/-- `HOLX.inst`. -/
def inst (b t : DT) : DT := subst 0 t b

def hasVar (j : Nat) : DT → Bool
  | var n => n == j
  | appL f x => f.hasVar j || x.hasVar j
  | lamL _ b => b.hasVar (j + 1)
  | pos => false
  | wabs b => b.hasVar (j + 1)
  | holds p i => p.hasVar j || i.hasVar j
  | rel i k => i.hasVar j || k.hasVar j
  | act x i => x.hasVar j || i.hasVar j
  | bot => false
  | imp p q | and p q | or p q => p.hasVar j || q.hasVar j
  | all _ b | ex _ b => b.hasVar (j + 1)
  | eq _ x y => x.hasVar j || y.hasVar j

/-- Lower all variables by one (variable `0` must not occur). -/
def down (x : DT) : DT := x.inst (var 0)

/-- `βη`-normal form (β at `𝓛`-application and at world application, η at both). -/
partial def nf : DT → DT
  | var n => var n
  | appL f x =>
      match nf f with
      | lamL _ b => nf (b.inst (nf x))
      | f' => appL f' (nf x)
  | lamL a b =>
      let b' := nf b
      match b' with
      | appL f (var 0) => if f.hasVar 0 then lamL a b' else f.down
      | _ => lamL a b'
  | pos => pos
  | wabs b =>
      let b' := nf b
      match b' with
      | holds p (var 0) => if p.hasVar 0 then wabs b' else p.down
      | _ => wabs b'
  | holds p i =>
      match nf p with
      | wabs b => nf (b.inst (nf i))
      | p' => holds p' (nf i)
  | rel i j => rel (nf i) (nf j)
  | act x i => act (nf x) (nf i)
  | bot => bot
  | imp p q => imp (nf p) (nf q)
  | and p q => and (nf p) (nf q)
  | or p q => or (nf p) (nf q)
  | all a b => all a (nf b)
  | ex a b =>
      -- `◇`: `∃v. R i v ∧ B` is read as `¬∀v. R i v → ¬B` (`Translate.eqNF0` derives the equation)
      match a, nf b with
      | .w, and (rel i (var 0)) B => imp (all .w (imp (rel i (var 0)) (imp B bot))) bot
      -- `∃x. x @ w` is read as `∃ᴱx. ⊤`
      | .L .e, act (var 0) i => ex (.L .e) (and (act (var 0) i) (imp bot bot))
      | _, b' => ex a b'
  | eq a s t => eq a (nf s) (nf t)

/-- Head `β`-reduction only (world and `𝓛` application). -/
partial def hnf : DT → DT
  | holds p i => match hnf p with
    | wabs b => hnf (b.inst i)
    | p' => holds p' i
  | appL f x => match hnf f with
    | lamL _ b => hnf (b.inst x)
    | f' => appL f' x
  | x => x

partial def toStr : DT → String
  | var n => s!"#{n}"
  | appL f x => s!"({f.toStr} {x.toStr})"
  | lamL a b => s!"(λ:{a}. {b.toStr})"
  | pos => "P"
  | wabs b => s!"(λw. {b.toStr})"
  | holds p i => s!"{p.toStr}@{i.toStr}"
  | rel i j => s!"R {i.toStr} {j.toStr}"
  | act x i => s!"act {x.toStr} {i.toStr}"
  | bot => "⊥"
  | imp p q => s!"({p.toStr} → {q.toStr})"
  | and p q => s!"({p.toStr} ∧ {q.toStr})"
  | or p q => s!"({p.toStr} ∨ {q.toStr})"
  | all a b => s!"(∀:{a}. {b.toStr})"
  | ex a b => s!"(∃:{a}. {b.toStr})"
  | eq a s t => s!"({s.toStr} =[{a}] {t.toStr})"

instance : ToString DT := ⟨toStr⟩

end DT

/-- Type of a meta HOL term in a context (head = variable `0`). -/
partial def DT.ty (ctx : List HT) : DT → Except String HT
  | .var n => match ctx[n]? with
      | some a => pure a
      | none => throw s!"unbound variable #{n}"
  | .appL f _ => do
      match ← DT.ty ctx f with
      | .L (.arr _ b) => pure (.L b)
      | a => throw s!"appL head of type {a}"
  | .lamL a b => do
      match ← DT.ty (.L a :: ctx) b with
      | .L t => pure (.L (.arr a t))
      | t => throw s!"lamL body of type {t}"
  | .pos => pure (.L FT.th)
  | .wabs _ => pure (.L .s)
  | _ => pure .o

/-- Index among the `𝓛`-variables of the context of HOL variable `n` (if it is one). -/
def lidx (ctx : List HT) (n : Nat) : Option Nat := Id.run do
  let mut k := 0
  for j in [0:n] do
    if let some (.L _) := ctx[j]? then k := k + 1
  match ctx[n]? with
  | some (.L _) => return some k
  | _ => return none

/-- `Lproj ctx` as a list: `𝓛`-index ↦ HOL index. -/
def lprojL (ctx : List HT) : List Nat := Id.run do
  let mut out := #[]
  for j in [0:ctx.length] do
    if let some (.L _) := ctx[j]? then out := out.push j
  return out.toList

def lctxL (ctx : List HT) : List FT :=
  ctx.filterMap fun | .L t => some t | _ => none

/-- Meta `emb`. -/
def embD (r : List Nat) : LT → DT
  | .var j => .var (r.getD j 0)
  | .app F x => .appL (embD r F) (embD r x)
  | .lam a b => .lamL a (embD (0 :: r.map (· + 1)) b)
  | .top => .wabs (.imp .bot .bot)
  | .bot => .wabs .bot
  | .neg x => .wabs (.imp (.holds (embD (r.map (· + 1)) x) (.var 0)) .bot)
  | .and x y => .wabs (.and (.holds (embD (r.map (· + 1)) x) (.var 0)) (.holds (embD (r.map (· + 1)) y) (.var 0)))
  | .or x y => .wabs (.or (.holds (embD (r.map (· + 1)) x) (.var 0)) (.holds (embD (r.map (· + 1)) y) (.var 0)))
  | .imp x y => .wabs (.imp (.holds (embD (r.map (· + 1)) x) (.var 0)) (.holds (embD (r.map (· + 1)) y) (.var 0)))
  | .box x => .wabs (.all .w (.imp (.rel (.var 1) (.var 0)) (.holds (embD (r.map (· + 2)) x) (.var 0))))
  | .all a b => .wabs (.all (.L a) (.holds (embD (0 :: r.map (· + 2)) b) (.var 1)))
  | .ex a b => .wabs (.ex (.L a) (.holds (embD (0 :: r.map (· + 2)) b) (.var 1)))
  | .allE b => .wabs (.all (.L .e) (.imp (.act (.var 0) (.var 1)) (.holds (embD (0 :: r.map (· + 2)) b) (.var 1))))
  | .exE b => .wabs (.ex (.L .e) (.and (.act (.var 0) (.var 1)) (.holds (embD (0 :: r.map (· + 2)) b) (.var 1))))
  | .eq a x y => .wabs (.eq (.L a) (embD (r.map (· + 1)) x) (embD (r.map (· + 1)) y))
  | .pos => .pos

/-- Exact inverse of `emb (Lproj ctx)`: `rbE ctx x = some s` iff `x = emb (Lproj ctx) s`. -/
partial def rbE (ctx : List HT) : DT → Option LT
  | .var n => (lidx ctx n).map LT.var
  | .appL f x => LT.app <$> rbE ctx f <*> rbE ctx x
  | .lamL a b => LT.lam a <$> rbE (.L a :: ctx) b
  | .pos => some .pos
  | .wabs b =>
      let c1 := HT.w :: ctx
      match b with
      | .imp .bot .bot => some .top
      | .bot => some .bot
      | .imp (.holds x (.var 0)) .bot => LT.neg <$> rbE c1 x
      | .and (.holds x (.var 0)) (.holds y (.var 0)) => LT.and <$> rbE c1 x <*> rbE c1 y
      | .or (.holds x (.var 0)) (.holds y (.var 0)) => LT.or <$> rbE c1 x <*> rbE c1 y
      | .imp (.holds x (.var 0)) (.holds y (.var 0)) => LT.imp <$> rbE c1 x <*> rbE c1 y
      | .all .w (.imp (.rel (.var 1) (.var 0)) (.holds x (.var 0))) => LT.box <$> rbE (.w :: c1) x
      | .all (.L .e) (.imp (.act (.var 0) (.var 1)) (.holds x (.var 1))) =>
          LT.allE <$> rbE (.L .e :: c1) x
      | .ex (.L .e) (.and (.act (.var 0) (.var 1)) (.holds x (.var 1))) =>
          LT.exE <$> rbE (.L .e :: c1) x
      | .all (.L a) (.holds x (.var 1)) => LT.all a <$> rbE (.L a :: c1) x
      | .ex (.L a) (.holds x (.var 1)) => LT.ex a <$> rbE (.L a :: c1) x
      | .eq (.L a) x y => LT.eq a <$> rbE c1 x <*> rbE c1 y
      | _ => none
  | _ => none

mutual
/-- Read-back of a `βη`-normal term at a type of `𝓛`. -/
partial def rbT (ctx : List HT) : DT → Option LT
  | .var n => (lidx ctx n).map LT.var
  | .appL f x => LT.app <$> rbT ctx f <*> rbT ctx x
  | .lamL a b => LT.lam a <$> rbT (.L a :: ctx) b
  | .pos => some .pos
  | .wabs b => rbF (.w :: ctx) 0 b
  | _ => none
/-- Read-back of a `βη`-normal formula as an `𝓛`-sentence at the world variable `wi`. -/
partial def rbF (ctx : List HT) (wi : Nat) : DT → Option LT
  | .bot => some .bot
  | .imp .bot .bot => some .top
  | .imp a .bot => LT.neg <$> rbF ctx wi a
  | .imp a b => LT.imp <$> rbF ctx wi a <*> rbF ctx wi b
  | .and a b => LT.and <$> rbF ctx wi a <*> rbF ctx wi b
  | .or a b => LT.or <$> rbF ctx wi a <*> rbF ctx wi b
  | .all (.L .e) (.imp (.act (.var 0) (.var k)) b) =>
      if k == wi + 1 then LT.allE <$> rbF (.L .e :: ctx) (wi + 1) b
      else LT.all .e <$> rbF (.L .e :: ctx) (wi + 1) (.imp (.act (.var 0) (.var k)) b)
  | .ex (.L .e) (.and (.act (.var 0) (.var k)) b) =>
      if k == wi + 1 then LT.exE <$> rbF (.L .e :: ctx) (wi + 1) b
      else none
  | .all (.L a) b => LT.all a <$> rbF (.L a :: ctx) (wi + 1) b
  | .ex (.L a) b => LT.ex a <$> rbF (.L a :: ctx) (wi + 1) b
  | .all .w (.imp (.rel (.var k) (.var 0)) b) =>
      if k == wi + 1 then LT.box <$> rbF (.w :: ctx) 0 b else none
  | .eq (.L a) x y => LT.eq a <$> rbT ctx x <*> rbT ctx y
  | .holds x (.var k) => if k == wi then rbT ctx x else none
  | _ => none
end

/-- Canonical certified form of a term at a type of `𝓛`: `emb (Lproj ctx)` of the read-back of its
`βη`-normal form. -/
def canonL (ctx : List HT) (x : DT) : Option (LT × DT) := do
  let tm ← rbT ctx x.nf
  let x' := embD (lprojL ctx) tm
  if x'.nf == x.nf then some (tm, x') else none

/-- Read-back of a closed formula at the world variable `wi` as an `𝓛`-sentence (modulo `βη`). -/
def sentenceOf (ctx : List HT) (wi : Nat) (φ : DT) : Option LT := rbF ctx wi φ.nf

partial def LT.toStr : LT → String
  | .var n => s!"v{n}"
  | .app f x => s!"({f.toStr} {x.toStr})"
  | .lam a b => s!"(λ:{a}. {b.toStr})"
  | .top => "⊤" | .bot => "⊥"
  | .neg x => s!"¬{x.toStr}"
  | .and x y => s!"({x.toStr} ∧ {y.toStr})"
  | .or x y => s!"({x.toStr} ∨ {y.toStr})"
  | .imp x y => s!"({x.toStr} → {y.toStr})"
  | .box x => s!"□{x.toStr}"
  | .all a b => s!"(∀:{a}. {b.toStr})"
  | .ex a b => s!"(∃:{a}. {b.toStr})"
  | .allE b => s!"(∀ᴱ. {b.toStr})"
  | .exE b => s!"(∃ᴱ. {b.toStr})"
  | .eq a x y => s!"({x.toStr} =[{a}] {y.toStr})"
  | .pos => "P"

/-! ## Emission of object-level terms -/

def mkFTy : FT → Expr
  | .e => mkConst ``FTy.e
  | .s => mkConst ``FTy.s
  | .arr a b => mkApp2 (mkConst ``FTy.arr) (mkFTy a) (mkFTy b)

def mkHTy : HT → Expr
  | .L t => mkApp (mkConst ``HTy.L) (mkFTy t)
  | .w => mkConst ``HTy.w
  | .o => mkConst ``HTy.o

def mkListE (ty : Expr) (xs : List Expr) : Expr :=
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [Level.zero]) ty x acc)
    (mkApp (mkConst ``List.nil [Level.zero]) ty)

def mkCtx (ctx : List HT) : Expr := mkListE (mkConst ``HTy) (ctx.map mkHTy)
def mkLCtx (ctx : List FT) : Expr := mkListE (mkConst ``FTy) (ctx.map mkFTy)

def mkHVar : List HT → Nat → Except String Expr
  | a :: Γ, 0 => pure (mkApp2 (mkConst ``HVar.zero) (mkCtx Γ) (mkHTy a))
  | b :: Γ, n + 1 => do
      let some a := Γ[n]? | throw "mkHVar: out of range"
      pure (mkApp4 (mkConst ``HVar.succ) (mkCtx Γ) (mkHTy a) (mkHTy b) (← mkHVar Γ n))
  | [], _ => throw "mkHVar: empty context"

partial def mkHTerm (ctx : List HT) (x : DT) : Except String Expr := do
  let Γ := mkCtx ctx
  match x with
  | .var n =>
      let some a := ctx[n]? | throw s!"mkHTerm: unbound #{n}"
      pure (mkApp3 (mkConst ``HTerm.var) Γ (mkHTy a) (← mkHVar ctx n))
  | .appL f y =>
      match ← DT.ty ctx f with
      | .L (.arr a b) =>
          pure (mkApp5 (mkConst ``HTerm.appL) Γ (mkFTy a) (mkFTy b) (← mkHTerm ctx f) (← mkHTerm ctx y))
      | _ => throw "mkHTerm: appL"
  | .lamL a b =>
      match ← DT.ty (.L a :: ctx) b with
      | .L t => pure (mkApp4 (mkConst ``HTerm.lamL) Γ (mkFTy a) (mkFTy t) (← mkHTerm (.L a :: ctx) b))
      | _ => throw "mkHTerm: lamL"
  | .pos => pure (mkApp (mkConst ``HTerm.pos) Γ)
  | .wabs b => pure (mkApp2 (mkConst ``HTerm.wabs) Γ (← mkHTerm (.w :: ctx) b))
  | .holds p i => pure (mkApp3 (mkConst ``HTerm.holds) Γ (← mkHTerm ctx p) (← mkHTerm ctx i))
  | .rel i j => pure (mkApp3 (mkConst ``HTerm.rel) Γ (← mkHTerm ctx i) (← mkHTerm ctx j))
  | .act y i => pure (mkApp3 (mkConst ``HTerm.act) Γ (← mkHTerm ctx y) (← mkHTerm ctx i))
  | .bot => pure (mkApp (mkConst ``HTerm.bot) Γ)
  | .imp p q => pure (mkApp3 (mkConst ``HTerm.imp) Γ (← mkHTerm ctx p) (← mkHTerm ctx q))
  | .and p q => pure (mkApp3 (mkConst ``HTerm.and) Γ (← mkHTerm ctx p) (← mkHTerm ctx q))
  | .or p q => pure (mkApp3 (mkConst ``HTerm.or) Γ (← mkHTerm ctx p) (← mkHTerm ctx q))
  | .all a b => pure (mkApp3 (mkConst ``HTerm.all) Γ (mkHTy a) (← mkHTerm (a :: ctx) b))
  | .ex a b => pure (mkApp3 (mkConst ``HTerm.ex) Γ (mkHTy a) (← mkHTerm (a :: ctx) b))
  | .eq a s t => pure (mkApp4 (mkConst ``HTerm.eq) Γ (mkHTy a) (← mkHTerm ctx s) (← mkHTerm ctx t))

def mkLVar : List FT → Nat → Except String Expr
  | t :: Γ, 0 => pure (mkApp2 (mkConst ``Var.zero) (mkLCtx Γ) (mkFTy t))
  | u :: Γ, n + 1 => do
      let some t := Γ[n]? | throw "mkLVar: out of range"
      pure (mkApp4 (mkConst ``Var.succ) (mkLCtx Γ) (mkFTy t) (mkFTy u) (← mkLVar Γ n))
  | [], _ => throw "mkLVar: empty context"

partial def LT.ty (ctx : List FT) : LT → Except String FT
  | .var n => match ctx[n]? with | some t => pure t | none => throw "LT.ty: unbound"
  | .app f _ => do match ← LT.ty ctx f with | .arr _ b => pure b | _ => throw "LT.ty: app"
  | .lam a b => do pure (.arr a (← LT.ty (a :: ctx) b))
  | .pos => pure FT.th
  | _ => pure .s

partial def mkTm (ctx : List FT) (x : LT) : Except String Expr := do
  let Γ := mkLCtx ctx
  match x with
  | .var n =>
      let some t := ctx[n]? | throw "mkTm: unbound"
      pure (mkApp3 (mkConst ``Tm.var) Γ (mkFTy t) (← mkLVar ctx n))
  | .app f y =>
      match ← LT.ty ctx f with
      | .arr a b => pure (mkApp5 (mkConst ``Tm.app) Γ (mkFTy a) (mkFTy b) (← mkTm ctx f) (← mkTm ctx y))
      | _ => throw "mkTm: app"
  | .lam a b => do
      let t ← LT.ty (a :: ctx) b
      pure (mkApp4 (mkConst ``Tm.lam) Γ (mkFTy a) (mkFTy t) (← mkTm (a :: ctx) b))
  | .top => pure (mkApp (mkConst ``Tm.top) Γ)
  | .bot => pure (mkApp (mkConst ``Tm.bot) Γ)
  | .neg y => pure (mkApp2 (mkConst ``Tm.neg) Γ (← mkTm ctx y))
  | .and y z => pure (mkApp3 (mkConst ``Tm.and) Γ (← mkTm ctx y) (← mkTm ctx z))
  | .or y z => pure (mkApp3 (mkConst ``Tm.or) Γ (← mkTm ctx y) (← mkTm ctx z))
  | .imp y z => pure (mkApp3 (mkConst ``Tm.imp) Γ (← mkTm ctx y) (← mkTm ctx z))
  | .box y => pure (mkApp2 (mkConst ``Tm.box) Γ (← mkTm ctx y))
  | .all a b => pure (mkApp3 (mkConst ``Tm.all) Γ (mkFTy a) (← mkTm (a :: ctx) b))
  | .ex a b => pure (mkApp3 (mkConst ``Tm.ex) Γ (mkFTy a) (← mkTm (a :: ctx) b))
  | .allE b => pure (mkApp2 (mkConst ``Tm.allE) Γ (← mkTm (.e :: ctx) b))
  | .exE b => pure (mkApp2 (mkConst ``Tm.exE) Γ (← mkTm (.e :: ctx) b))
  | .eq a y z => pure (mkApp4 (mkConst ``Tm.eq) Γ (mkFTy a) (← mkTm ctx y) (← mkTm ctx z))
  | .pos => pure (mkApp (mkConst ``Tm.pos) Γ)

end Programme.H

namespace Programme.H
open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.HOLX
  Programme.«20261022-1724-ontological».ThWhole

/-- Weakening of the hypotheses of a `DG` derivation (as `Deriv.weaken`). -/
theorem DG.weakenH {T : Tm [] .s → Prop} {ok : ∀ {Γ : List HTy} (a : HTy), HTerm Γ a → Prop}
    {okL : ∀ {Γ : List HTy} (a : HTy), HTerm (a :: Γ) .o → HTerm Γ a → HTerm Γ a → Prop} :
    ∀ {Γ hs φ}, DG T ok okL Γ hs φ → ∀ {hs'}, (∀ h, h ∈ hs → h ∈ hs') → DG T ok okL Γ hs' φ := by
  intro Γ hs φ d
  induction d with
  | hyp m => exact fun hsub => .hyp (hsub _ m)
  | ax φ i h => exact fun _ => .ax φ i h
  | impI _ ih => exact fun hsub => .impI (ih (cons_sub hsub _))
  | impE _ _ ih1 ih2 => exact fun hsub => .impE (ih1 hsub) (ih2 hsub)
  | byContra _ ih => exact fun hsub => .byContra (ih (cons_sub hsub _))
  | andI _ _ ih1 ih2 => exact fun hsub => .andI (ih1 hsub) (ih2 hsub)
  | andL _ ih => exact fun hsub => .andL (ih hsub)
  | andR _ ih => exact fun hsub => .andR (ih hsub)
  | orL _ ih => exact fun hsub => .orL (ih hsub)
  | orR _ ih => exact fun hsub => .orR (ih hsub)
  | orE _ _ _ ih ih1 ih2 => exact fun hsub => .orE (ih hsub) (ih1 (cons_sub hsub _)) (ih2 (cons_sub hsub _))
  | allI a _ ih => exact fun hsub => .allI a (ih (map_sub hsub))
  | allE a t _ hok ih => exact fun hsub => .allE a t (ih hsub) hok
  | exI a t hok _ ih => exact fun hsub => .exI a t hok (ih hsub)
  | exE a _ _ ih1 ih2 => exact fun hsub => .exE a (ih1 hsub) (ih2 (cons_sub (map_sub hsub) _))
  | refl a t => exact fun _ => .refl a t
  | symm a _ ih => exact fun hsub => .symm a (ih hsub)
  | trans a _ _ ih1 ih2 => exact fun hsub => .trans a (ih1 hsub) (ih2 hsub)
  | leibG a φ hok _ _ ih1 ih2 => exact fun hsub => .leibG a φ hok (ih1 hsub) (ih2 hsub)
  | funExt _ ih => exact fun hsub => .funExt (ih hsub)
  | funApp _ ih => exact fun hsub => .funApp (ih hsub)
  | wExt _ ih => exact fun hsub => .wExt (ih hsub)
  | wApp _ ih => exact fun hsub => .wApp (ih hsub)
  | propExt _ _ ih1 ih2 => exact fun hsub => .propExt (ih1 (cons_sub hsub _)) (ih2 (cons_sub hsub _))
  | betaL body x => exact fun _ => .betaL body x
  | betaWI φ i _ ih => exact fun hsub => .betaWI φ i (ih hsub)
  | betaWE φ i _ ih => exact fun hsub => .betaWE φ i (ih hsub)

/-- A derivation from no hypotheses holds under any. -/
theorem DG.ofNil {T : Tm [] .s → Prop} {ok : ∀ {Γ : List HTy} (a : HTy), HTerm Γ a → Prop}
    {okL : ∀ {Γ : List HTy} (a : HTy), HTerm (a :: Γ) .o → HTerm Γ a → HTerm Γ a → Prop}
    {Γ : List HTy} (hs : List (HTerm Γ .o)) {φ : HTerm Γ .o} (d : DG T ok okL Γ [] φ) :
    DG T ok okL Γ hs φ :=
  Programme.H.DG.weakenH d fun _ m => absurd m (List.not_mem_nil)

/-! ## Lemmas: derivations that use earlier lemmas as sentences of the theory (a semantic cut) -/

/-- A list of sentences, newest first, each an axiom (`A`) or valid over the sentences before it. -/
inductive Good (A : Tm [] .s → Prop) : List (Tm [] .s) → Prop
  | nil : Good A []
  | axm {s : Tm [] .s} {L : List (Tm [] .s)} : A s → Good A L → Good A (s :: L)
  | lem {s : Tm [] .s} {L : List (Tm [] .s)} : ValidV4 (fun φ => φ ∈ L) s → Good A L →
      Good A (s :: L)

/-- Cut: what is valid over a good list of lemmas is valid over the axioms alone. -/
theorem Good.valid {A : Tm [] .s → Prop} {L : List (Tm [] .s)} {χ : Tm [] .s} (g : Good A L)
    (h : ValidV4 (fun φ => φ ∈ L) χ) : ValidV4 A χ := by
  intro W M Lg hne hA
  apply h W M Lg hne
  clear h
  induction g with
  | nil => intro ψ hψ; cases hψ
  | axm hs _ ih =>
      intro ψ hψ
      rcases List.mem_cons.mp hψ with rfl | hψ
      · exact hA _ hs
      · exact ih ψ hψ
  | lem hv _ ih =>
      intro ψ hψ
      rcases List.mem_cons.mp hψ with rfl | hψ
      · exact hv W M Lg hne ih
      · exact ih ψ hψ

end Programme.H

end


/-! ## Tool part `Emit` -/
section

/-! # Thread H: meta derivations (`Der`) and their emission as `DW` proof terms

`Der` mirrors the rules of run 4's `DG` with every formula the rule needs recorded explicitly;
`emit` turns a `Der` into a term of type `DG T ok okL Γ hs φ` (with `ok`, `okL` the whole-term side
conditions of `DW`), recomputing each conclusion on the meta level and checking it against the
premises.  Side conditions are discharged by `cert_L`/`cert_w`/`cert_o` and `leibOK_plain`/
`leibOK_wt`; a failing side condition is an error naming the rule. -/

open Lean Meta
open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.HOLX
  Programme.«20261022-1724-ontological».ThWhole

namespace Programme.H

inductive Der where
  | hyp (k : Nat)
  | ax (idx : Nat) (i : DT)
  | impI (A : DT) (d : Der)
  | impE (d1 d2 : Der)
  | byContra (A : DT) (d : Der)
  | andI (d1 d2 : Der)
  | andL (d : Der)
  | andR (d : Der)
  | orL (B : DT) (d : Der)
  | orR (A : DT) (d : Der)
  | orE (d d1 d2 : Der)
  | allI (a : HT) (d : Der)
  | allE (t : DT) (d : Der)
  | exI (a : HT) (φ t : DT) (d : Der)
  | exE (d d2 : Der) (χ : DT)
  | refl (a : HT) (t : DT)
  | symm (d : Der)
  | trans (d1 d2 : Der)
  | leib (a : HT) (φ s t : DT) (deq d : Der)
  | funExt (d : Der)
  | funApp (d : Der)
  | wExt (d : Der)
  | wApp (d : Der)
  | propExt (φ ψ : DT) (d1 d2 : Der)
  | betaL (body x : DT)
  | betaWI (φ i : DT) (d : Der)
  | betaWE (d : Der)
  deriving Inhabited

/-- What the emitter needs: the theory (as an expression and as a list of sentences), `ok`, `okL`. -/
structure EmitEnv where
  T : Expr
  sentences : Array LT
  sentenceExprs : Array Expr
  ok : Expr
  okL : Expr

structure EmitCache where
  ctxs : Std.HashMap (List HT) Expr := {}
  terms : Std.HashMap (List HT × DT) Expr := {}
  lists : Std.HashMap (List HT × List DT) Expr := {}

abbrev EmitM := ReaderT EmitEnv (StateRefT EmitCache MetaM)

def ctxC (ctx : List HT) : EmitM Expr := do
  if let some e := (← get).ctxs[ctx]? then return e
  let e ← match ctx with
    | [] => pure (mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``HTy))
    | a :: rest => do pure (mkApp3 (mkConst ``List.cons [Level.zero]) (mkConst ``HTy) (mkHTy a) (← ctxC rest))
  modify fun c => { c with ctxs := c.ctxs.insert ctx e }
  pure e

def hvarC : List HT → Nat → EmitM Expr
  | a :: Γ, 0 => do pure (mkApp2 (mkConst ``HVar.zero) (← ctxC Γ) (mkHTy a))
  | b :: Γ, n + 1 => do
      let some a := Γ[n]? | throwError "hvarC: out of range"
      pure (mkApp4 (mkConst ``HVar.succ) (← ctxC Γ) (mkHTy a) (mkHTy b) (← hvarC Γ n))
  | [], _ => throwError "hvarC: empty context"

partial def tmC (ctx : List HT) (x : DT) : EmitM Expr := do
  if let some e := (← get).terms[(ctx, x)]? then return e
  let Γ ← ctxC ctx
  let ty (y : DT) (c : List HT) : EmitM HT := match DT.ty c y with
    | .ok t => pure t
    | .error m => throwError m
  let e ← match x with
    | .var n =>
        let some a := ctx[n]? | throwError s!"tmC: unbound #{n}"
        pure (mkApp3 (mkConst ``HTerm.var) Γ (mkHTy a) (← hvarC ctx n))
    | .appL f y =>
        match ← ty f ctx with
        | .L (.arr a b) => pure (mkApp5 (mkConst ``HTerm.appL) Γ (mkFTy a) (mkFTy b) (← tmC ctx f) (← tmC ctx y))
        | _ => throwError "tmC: appL"
    | .lamL a b =>
        match ← ty b (.L a :: ctx) with
        | .L t => pure (mkApp4 (mkConst ``HTerm.lamL) Γ (mkFTy a) (mkFTy t) (← tmC (.L a :: ctx) b))
        | _ => throwError "tmC: lamL"
    | .pos => pure (mkApp (mkConst ``HTerm.pos) Γ)
    | .wabs b => do pure (mkApp2 (mkConst ``HTerm.wabs) Γ (← tmC (.w :: ctx) b))
    | .holds p i => do pure (mkApp3 (mkConst ``HTerm.holds) Γ (← tmC ctx p) (← tmC ctx i))
    | .rel i j => do pure (mkApp3 (mkConst ``HTerm.rel) Γ (← tmC ctx i) (← tmC ctx j))
    | .act y i => do pure (mkApp3 (mkConst ``HTerm.act) Γ (← tmC ctx y) (← tmC ctx i))
    | .bot => pure (mkApp (mkConst ``HTerm.bot) Γ)
    | .imp p q => do pure (mkApp3 (mkConst ``HTerm.imp) Γ (← tmC ctx p) (← tmC ctx q))
    | .and p q => do pure (mkApp3 (mkConst ``HTerm.and) Γ (← tmC ctx p) (← tmC ctx q))
    | .or p q => do pure (mkApp3 (mkConst ``HTerm.or) Γ (← tmC ctx p) (← tmC ctx q))
    | .all a b => do pure (mkApp3 (mkConst ``HTerm.all) Γ (mkHTy a) (← tmC (a :: ctx) b))
    | .ex a b => do pure (mkApp3 (mkConst ``HTerm.ex) Γ (mkHTy a) (← tmC (a :: ctx) b))
    | .eq a s t => do pure (mkApp4 (mkConst ``HTerm.eq) Γ (mkHTy a) (← tmC ctx s) (← tmC ctx t))
  modify fun c => { c with terms := c.terms.insert (ctx, x) e }
  pure e

/-- The hypothesis list as an expression (shared tails). -/
partial def listC (ctx : List HT) (hs : List DT) : EmitM Expr := do
  if let some e := (← get).lists[(ctx, hs)]? then return e
  let Γ ← ctxC ctx
  let ety := mkApp2 (mkConst ``HTerm) Γ (mkHTy .o)
  let e ← match hs with
    | [] => pure (mkApp (mkConst ``List.nil [Level.zero]) ety)
    | h :: rest => do pure (mkApp3 (mkConst ``List.cons [Level.zero]) ety (← tmC ctx h) (← listC ctx rest))
  modify fun c => { c with lists := c.lists.insert (ctx, hs) e }
  pure e

/-- Proof of `hs[k] ∈ hs` (shared). -/
def memC (ctx : List HT) (hs : List DT) (k : Nat) : EmitM Expr := do
  let Γ ← ctxC ctx
  let ety := mkApp2 (mkConst ``HTerm) Γ (mkHTy .o)
  match hs, k with
  | x :: rest, 0 => pure (mkApp3 (mkConst ``List.Mem.head [Level.zero]) ety (← tmC ctx x) (← listC ctx rest))
  | y :: rest, n + 1 => do
      let some a := rest[n]? | throwError "memC: out of range"
      let h ← memC ctx rest n
      pure (mkApp5 (mkConst ``List.Mem.tail [Level.zero]) ety (← tmC ctx a) (← tmC ctx y) (← listC ctx rest) h)
  | [], _ => throwError "memC: empty"

def liftE {α} (x : Except String α) : EmitM α := do
  match x with
  | .ok a => pure a
  | .error e => throwError e

def hTermTy (Γ : Expr) : Expr := mkApp2 (mkConst ``HTerm) Γ (mkHTy .o)

/-- Proof of `hs[k] ∈ hs`. -/
def memProof (elemTy : Expr) (xs : List Expr) (k : Nat) : Except String Expr := do
  match xs, k with
  | x :: rest, 0 => pure (mkApp3 (mkConst ``List.Mem.head [Level.zero]) elemTy x (mkListE elemTy rest))
  | y :: rest, n + 1 => do
      let some a := rest[n]? | throw "memProof: out of range"
      let h ← memProof elemTy rest n
      pure (mkApp5 (mkConst ``List.Mem.tail [Level.zero]) elemTy a y (mkListE elemTy rest) h)
  | [], _ => throw "memProof: empty"

/-- Proof of `Cert a x`. -/
def certProof (ctx : List HT) (a : HT) (x : DT) : Except String Expr := do
  let Γ := mkCtx ctx
  match a with
  | .w => pure (mkApp2 (mkConst ``cert_w) Γ (← mkHTerm ctx x))
  | .o => pure (mkApp2 (mkConst ``cert_o) Γ (← mkHTerm ctx x))
  | .L t =>
      match rbE ctx x with
      | some tm =>
          if embD (lprojL ctx) tm == x then
            pure (mkApp3 (mkConst ``cert_L) Γ (mkFTy t) (← mkTm (lctxL ctx) tm))
          else throw s!"not a term of 𝓛 (whole-term condition): {x}"
      | none => throw s!"not a term of 𝓛 (whole-term condition): {x}"

/-- Proof of `WT x`. -/
partial def wtProof (ctx : List HT) (x : DT) : Except String Expr := do
  let Γ := mkCtx ctx
  match x with
  | .var n =>
      let some a := ctx[n]? | throw "wtProof: unbound"
      pure (mkApp3 (mkConst ``wt_var) Γ (mkHTy a) (← mkHVar ctx n))
  | .appL f y =>
      match ← DT.ty ctx f with
      | .L (.arr a b) =>
          pure (mkAppN (mkConst ``wt_appL) #[Γ, mkFTy a, mkFTy b, ← mkHTerm ctx f, ← mkHTerm ctx y,
            ← wtProof ctx f, ← certProof ctx (.L a) y])
      | _ => throw "wtProof: appL"
  | .lamL a b =>
      match ← DT.ty (.L a :: ctx) b with
      | .L t => pure (mkAppN (mkConst ``wt_lamL) #[Γ, mkFTy a, mkFTy t, ← mkHTerm (.L a :: ctx) b,
          ← wtProof (.L a :: ctx) b])
      | _ => throw "wtProof: lamL"
  | .pos => pure (mkApp (mkConst ``wt_pos) Γ)
  | .wabs b => pure (mkApp3 (mkConst ``wt_wabs) Γ (← mkHTerm (.w :: ctx) b) (← wtProof (.w :: ctx) b))
  | .holds p i => pure (mkAppN (mkConst ``wt_holds) #[Γ, ← mkHTerm ctx p, ← mkHTerm ctx i,
      ← wtProof ctx p, ← wtProof ctx i])
  | .rel i j => pure (mkAppN (mkConst ``wt_rel) #[Γ, ← mkHTerm ctx i, ← mkHTerm ctx j,
      ← wtProof ctx i, ← wtProof ctx j])
  | .act y i => pure (mkAppN (mkConst ``wt_act) #[Γ, ← mkHTerm ctx y, ← mkHTerm ctx i,
      ← wtProof ctx y, ← wtProof ctx i])
  | .bot => pure (mkApp (mkConst ``wt_bot) Γ)
  | .imp p q => pure (mkAppN (mkConst ``wt_imp) #[Γ, ← mkHTerm ctx p, ← mkHTerm ctx q,
      ← wtProof ctx p, ← wtProof ctx q])
  | .and p q => pure (mkAppN (mkConst ``wt_and) #[Γ, ← mkHTerm ctx p, ← mkHTerm ctx q,
      ← wtProof ctx p, ← wtProof ctx q])
  | .or p q => pure (mkAppN (mkConst ``wt_or) #[Γ, ← mkHTerm ctx p, ← mkHTerm ctx q,
      ← wtProof ctx p, ← wtProof ctx q])
  | .all a b => pure (mkAppN (mkConst ``wt_all) #[Γ, mkHTy a, ← mkHTerm (a :: ctx) b,
      ← wtProof (a :: ctx) b])
  | .ex a b => pure (mkAppN (mkConst ``wt_ex) #[Γ, mkHTy a, ← mkHTerm (a :: ctx) b,
      ← wtProof (a :: ctx) b])
  | .eq a s t => pure (mkAppN (mkConst ``wt_eq) #[Γ, mkHTy a, ← mkHTerm ctx s, ← mkHTerm ctx t,
      ← wtProof ctx s, ← wtProof ctx t])

/-- Proof of `LeibOK a φ s t`. -/
def leibOKProof (ctx : List HT) (a : HT) (φ s t : DT) : Except String Expr := do
  let Γ := mkCtx ctx
  if a.plain then
    pure (mkAppN (mkConst ``leibOK_plain) #[Γ, mkHTy a, mkApp2 (mkConst ``Eq.refl [Level.one])
      (mkConst ``Bool) (mkConst ``Bool.true), ← mkHTerm (a :: ctx) φ, ← mkHTerm ctx s, ← mkHTerm ctx t])
  else
    let wt ← match wtProof (a :: ctx) φ with
      | .ok p => pure p
      | .error e => throw s!"Leibniz at {a}: motive not whole-term ({e}); motive {φ}"
    pure (mkAppN (mkConst ``leibOK_wt) #[Γ, mkHTy a, ← mkHTerm (a :: ctx) φ, ← mkHTerm ctx s,
      ← mkHTerm ctx t, wt, ← certProof ctx a s, ← certProof ctx a t])

def chkEq (what : String) (x y : DT) : EmitM Unit :=
  unless x == y do throwError s!"emit ({what}): expected {y}, got {x}"

/-- Emit a derivation in context `ctx` under hypotheses `hs`; returns the proof and its conclusion. -/
partial def emit (ctx : List HT) (hs : List DT) (d : Der) : EmitM (Expr × DT) := do
  let env ← read
  let Γ ← ctxC ctx
  let HS ← listC ctx hs
  let pre (c : Name) : Expr := mkAppN (mkConst c) #[env.T, env.ok, env.okL, Γ, HS]
  let tm (x : DT) : EmitM Expr := tmC ctx x
  match d with
  | .hyp k =>
      let some φ := hs[k]? | throwError s!"emit: hyp {k} out of range"
      let mp ← memC ctx hs k
      pure (mkAppN (pre ``DG.hyp) #[← tm φ, mp], φ)
  | .ax idx i =>
      let some s := env.sentences[idx]? | throwError "emit: axiom index"
      let some sE := env.sentenceExprs[idx]? | throwError "emit: axiom index"
      let sentTy := mkApp2 (mkConst ``Tm) (mkLCtx []) (mkFTy .s)
      -- the theory lists its sentences newest first
      let mp ← liftE (memProof sentTy env.sentenceExprs.toList.reverse (env.sentenceExprs.size - 1 - idx))
      pure (mkAppN (pre ``DG.ax) #[sE, ← tm i, mp], .holds (embD [] s) i)
  | .impI A d =>
      let (D, B) ← emit ctx (A :: hs) d
      pure (mkAppN (pre ``DG.impI) #[← tm A, ← tm B, D], .imp A B)
  | .impE d1 d2 =>
      let (D1, X) ← emit ctx hs d1
      let .imp A B := X | throwError s!"emit impE: not an implication: {X}"
      let (D2, A') ← emit ctx hs d2
      chkEq "impE" A' A
      pure (mkAppN (pre ``DG.impE) #[← tm A, ← tm B, D1, D2], B)
  | .byContra A d =>
      let (D, X) ← emit ctx (.imp A .bot :: hs) d
      chkEq "byContra" X .bot
      pure (mkAppN (pre ``DG.byContra) #[← tm A, D], A)
  | .andI d1 d2 =>
      let (D1, A) ← emit ctx hs d1
      let (D2, B) ← emit ctx hs d2
      pure (mkAppN (pre ``DG.andI) #[← tm A, ← tm B, D1, D2], .and A B)
  | .andL d =>
      let (D, X) ← emit ctx hs d
      let .and A B := X | throwError s!"emit andL: {X}"
      pure (mkAppN (pre ``DG.andL) #[← tm A, ← tm B, D], A)
  | .andR d =>
      let (D, X) ← emit ctx hs d
      let .and A B := X | throwError s!"emit andR: {X}"
      pure (mkAppN (pre ``DG.andR) #[← tm A, ← tm B, D], B)
  | .orL B d =>
      let (D, A) ← emit ctx hs d
      pure (mkAppN (pre ``DG.orL) #[← tm A, ← tm B, D], .or A B)
  | .orR A d =>
      let (D, B) ← emit ctx hs d
      pure (mkAppN (pre ``DG.orR) #[← tm A, ← tm B, D], .or A B)
  | .orE d d1 d2 =>
      let (D, X) ← emit ctx hs d
      let .or A B := X | throwError s!"emit orE: {X}"
      let (D1, C) ← emit ctx (A :: hs) d1
      let (D2, C') ← emit ctx (B :: hs) d2
      chkEq "orE" C' C
      pure (mkAppN (pre ``DG.orE) #[← tm A, ← tm B, ← tm C, D, D1, D2], C)
  | .allI a d =>
      let (D, B) ← emit (a :: ctx) (hs.map (·.shift 1)) d
      pure (mkAppN (pre ``DG.allI) #[mkHTy a, ← tmC (a :: ctx) B, D], .all a B)
  | .allE t d =>
      let (D, X) ← emit ctx hs d
      let .all a B := X | throwError s!"emit allE: {X}"
      let okP ← match a with
        | .w => pure (mkApp2 (mkConst ``cert_w) Γ (← tm t))
        | .o => pure (mkApp2 (mkConst ``cert_o) Γ (← tm t))
        | _ => match certProof ctx a t with
          | .ok p => pure p
          | .error e => throwError s!"∀E instance at {a}: {e}"
      pure (mkAppN (pre ``DG.allE) #[mkHTy a, ← tmC (a :: ctx) B, ← tm t, D, okP],
        B.inst t)
  | .exI a φ t d =>
      let (D, X) ← emit ctx hs d
      chkEq "exI" X (φ.inst t)
      let okP ← match certProof ctx a t with
        | .ok p => pure p
        | .error e => throwError s!"∃I witness at {a}: {e}"
      pure (mkAppN (pre ``DG.exI) #[mkHTy a, ← tmC (a :: ctx) φ, ← tm t, okP, D],
        .ex a φ)
  | .exE d d2 χ =>
      let (D, X) ← emit ctx hs d
      let .ex a φ := X | throwError s!"emit exE: {X}"
      let (D2, Y) ← emit (a :: ctx) (φ :: hs.map (·.shift 1)) d2
      chkEq "exE" Y (χ.shift 1)
      pure (mkAppN (pre ``DG.exE) #[mkHTy a, ← tmC (a :: ctx) φ, ← tm χ, D, D2], χ)
  | .refl a t => pure (mkAppN (pre ``DG.refl) #[mkHTy a, ← tm t], .eq a t t)
  | .symm d =>
      let (D, X) ← emit ctx hs d
      let .eq a s t := X | throwError s!"emit symm: {X}"
      pure (mkAppN (pre ``DG.symm) #[mkHTy a, ← tm s, ← tm t, D], .eq a t s)
  | .trans d1 d2 =>
      let (D1, X) ← emit ctx hs d1
      let .eq a s t := X | throwError s!"emit trans: {X}"
      let (D2, Y) ← emit ctx hs d2
      let .eq a' t' u := Y | throwError s!"emit trans: {Y}"
      unless a == a' do throwError "emit trans: types differ"
      chkEq "trans middle" t' t
      pure (mkAppN (pre ``DG.trans) #[mkHTy a, ← tm s, ← tm t, ← tm u, D1, D2], .eq a s u)
  | .leib a φ s t deq d =>
      let (Deq, X) ← emit ctx hs deq
      chkEq "leib equation" X (.eq a s t)
      let (Dd, Y) ← emit ctx hs d
      chkEq "leib premise" Y (φ.inst s)
      let okP ← if a.plain then
          pure (mkAppN (mkConst ``leibOK_plain) #[Γ, mkHTy a, mkApp2 (mkConst ``Eq.refl [Level.one])
            (mkConst ``Bool) (mkConst ``Bool.true), ← tmC (a :: ctx) φ, ← tm s, ← tm t])
        else liftE (leibOKProof ctx a φ s t)
      pure (mkAppN (pre ``DG.leibG) #[mkHTy a, ← tm s, ← tm t, ← tmC (a :: ctx) φ, okP,
        Deq, Dd], φ.inst t)
  | .funExt d =>
      let (D, X) ← emit ctx hs d
      let .all (.L a) (.eq (.L b) (.appL f' (.var 0)) (.appL g' (.var 0))) := X
        | throwError s!"emit funExt: {X}"
      let f := f'.down
      let g := g'.down
      chkEq "funExt f" (f.shift 1) f'
      chkEq "funExt g" (g.shift 1) g'
      pure (mkAppN (pre ``DG.funExt) #[mkFTy a, mkFTy b, ← tm f, ← tm g, D], .eq (.L (.arr a b)) f g)
  | .funApp d =>
      let (D, X) ← emit ctx hs d
      let .eq (.L (.arr a b)) f g := X | throwError s!"emit funApp: {X}"
      pure (mkAppN (pre ``DG.funApp) #[mkFTy a, mkFTy b, ← tm f, ← tm g, D],
        .all (.L a) (.eq (.L b) (.appL (f.shift 1) (.var 0)) (.appL (g.shift 1) (.var 0))))
  | .wExt d =>
      let (D, X) ← emit ctx hs d
      let .all .w (.eq .o (.holds p' (.var 0)) (.holds q' (.var 0))) := X | throwError s!"emit wExt: {X}"
      let p := p'.down
      let q := q'.down
      chkEq "wExt p" (p.shift 1) p'
      chkEq "wExt q" (q.shift 1) q'
      pure (mkAppN (pre ``DG.wExt) #[← tm p, ← tm q, D], .eq (.L .s) p q)
  | .wApp d =>
      let (D, X) ← emit ctx hs d
      let .eq (.L .s) p q := X | throwError s!"emit wApp: {X}"
      pure (mkAppN (pre ``DG.wApp) #[← tm p, ← tm q, D],
        .all .w (.eq .o (.holds (p.shift 1) (.var 0)) (.holds (q.shift 1) (.var 0))))
  | .propExt φ ψ d1 d2 =>
      let (D1, X) ← emit ctx (φ :: hs) d1
      chkEq "propExt 1" X ψ
      let (D2, Y) ← emit ctx (ψ :: hs) d2
      chkEq "propExt 2" Y φ
      pure (mkAppN (pre ``DG.propExt) #[← tm φ, ← tm ψ, D1, D2], .eq .o φ ψ)
  | .betaL body x =>
      let .L a ← liftE (DT.ty ctx x) | throwError "emit betaL: argument type"
      let .L b ← liftE (DT.ty (.L a :: ctx) body) | throwError "emit betaL: body type"
      pure (mkAppN (pre ``DG.betaL) #[mkFTy a, mkFTy b, ← tmC (.L a :: ctx) body, ← tm x],
        .eq (.L b) (.appL (.lamL a body) x) (body.inst x))
  | .betaWI φ i d =>
      let (D, X) ← emit ctx hs d
      chkEq "betaWI" X (φ.inst i)
      pure (mkAppN (pre ``DG.betaWI) #[← tmC (.w :: ctx) φ, ← tm i, D], .holds (.wabs φ) i)
  | .betaWE d =>
      let (D, X) ← emit ctx hs d
      let .holds (.wabs φ) i := X | throwError s!"emit betaWE: {X}"
      pure (mkAppN (pre ``DG.betaWE) #[← tmC (.w :: ctx) φ, ← tm i, D], φ.inst i)

end Programme.H

end


/-! ## Tool part `Translate` -/
section

/-! # Thread H: from shallow Lean proofs to run 4's deep derivations

`#deep_translate thm as Name` reads the statement and the proof term of `thm` (a theorem of a
shallow `OpenQuestions` module, or a proof of one of its statements), and

* computes the deep image: an `𝓛`-sentence `φ` (read back from the statement), and a theory `T`
  (the module's axioms the proof uses, the statement's hypotheses, and instances of hypothesis
  schemas, each read back as an `𝓛`-sentence);
* translates the proof term, step by step, into a derivation of run 4's calculus `DG` with the
  whole-term side conditions of `DW`;
* adds `Name.T`, `Name.φ`, `Name.deep : DW Name.T [.w] [] (.holds (emb nilR Name.φ) var0)` and
  `Name.valid : ValidV4 Name.T Name.φ` (by `sound_v4_wt`), all kernel-checked.

A step outside the fragment, or an `∀E`/`∃I` instance or a Leibniz step that violates the
whole-term condition, stops the translation with an error naming it.  The fragment:
`fun`/application (→I/→E, ∀I/∀E at the types of `𝓛`, worlds and `Prop`), `And`/`Or`/`Iff`/
`Exists`/`True`/`False`/`Not`/`Ne` introduction and elimination (including `casesOn`/`rec` and the
matchers built from them), `Classical.byContradiction`/`byCases`/`em`, `dite`/`Decidable.byCases`
on `Classical.propDecidable`, `Eq.refl`/`symm`/`trans`/`mp`/`mpr`/`ndrec`/`rec`/`subst`, `congrArg`,
`congrFun`, `funext`, `propext`, `of_eq_true`/`eq_true`/`eq_self`, `β`/`η` (as derivations), and
unfolding of definitions and of the proofs of theorems (the module's and Lean's own), which are then
translated in turn. -/

open Lean Meta Elab Command Term
open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.HOLX
  Programme.«20261022-1724-ontological».ThWhole

namespace Programme.H

/-! ## Translation state -/

/-- A hypothesis of the statement that is read as a sentence (or a schema of sentences) of `T`. -/
structure FactVar where
  fvar : FVarId
  name : String

structure TState where
  sentences : Array LT := #[]
  sentenceNames : Array String := #[]
  /-- Which constant/hypothesis each sentence comes from (for reporting). -/
  usedConsts : Array Name := #[]
  depth : Nat := 0
  steps : Nat := 0
  /-- The deep variable standing for `Classical.ofNonempty : e`, if enabled. -/
  nonemptyVar : Option FVarId := none
  nonemptyUsed : Bool := false
  /-- The proof term being translated (for error messages). -/
  current : Expr := .bvar 0
  /-- The theorems whose proofs are being unfolded, innermost first. -/
  stack : List Name := []
  /-- Replacement proofs: constant ↦ theorem with the identical statement. -/
  replace : List (Name × Name) := []
  /-- Memo for the conversion engine (derivations there use no outer hypotheses). -/
  eqCache : Std.HashMap (List HT × HT × DT) (DT × Der) := {}
  /-- Theorems translated once and used as lemmas: name ↦ index of their sentence. -/
  lemmaIdx : Std.HashMap Name Nat := {}
  /-- Theorems whose statement is not a validity of an `𝓛`-sentence (unfolded at each use). -/
  noLemma : Std.HashSet Name := {}
  /-- The lemma derivations: sentence index, theorem, derivation (in `[.w]`), its target. -/
  lemmas : Array (Nat × Name × Der × DT) := #[]
  /-- Translate theorems as lemmas (otherwise unfold their proofs at each use). -/
  useLemmas : Bool := true
  /-- For sentences read off an instance of a statement hypothesis: the instance's Lean type and
  `fun h => h args` (closed), for the structural check. -/
  factTys : Std.HashMap Nat (Expr × Expr) := {}
  /-- Statement hypotheses read as closed frame formulas (C7): fact index and image, in the order
  of the derivation's hypothesis list (newest first). -/
  frames : List (Nat × DT) := []

/-- The translation context: deep variables (outermost first), hypotheses (most recent first). -/
structure TCtx where
  vars : Array (FVarId × HT) := #[]
  hyps : List (Option FVarId × DT) := []
  facts : Array FactVar := #[]

abbrev TM := StateRefT TState MetaM

def TCtx.deep (c : TCtx) : List HT := c.vars.toList.reverse.map (·.2)

def TCtx.idx? (c : TCtx) (id : FVarId) : Option Nat := do
  let pos ← c.vars.findIdx? (·.1 == id)
  pure (c.vars.size - 1 - pos)

def TCtx.pushVar (c : TCtx) (id : FVarId) (a : HT) : TCtx :=
  { c with vars := c.vars.push (id, a), hyps := c.hyps.map fun (h, A) => (h, A.shift 1) }

def TCtx.pushHyp (c : TCtx) (h : Option FVarId) (A : DT) : TCtx :=
  { c with hyps := (h, A) :: c.hyps }

def TCtx.hypIdx? (c : TCtx) (id : FVarId) : Option (Nat × DT) := Id.run do
  let mut k := 0
  for (h, A) in c.hyps do
    if h == some id then return some (k, A)
    k := k + 1
  return none

def TCtx.isFact (c : TCtx) (id : FVarId) : Bool := c.facts.any (·.fvar == id)

/-- Progress log, only if the environment variable `DEEP_LOG` names a file. -/
def dbg (s : String) : TM Unit := do
  if let some f ← IO.getEnv "DEEP_LOG" then
    let h ← IO.FS.Handle.mk f .append
    h.putStrLn s
    h.flush

def outside {α} (what : MessageData) : TM α := do
  let cur := (← get).current
  let stk := (← get).stack
  throwError m!"[deep_translate] outside the fragment: {what}\n  in the step: {cur}\n  inside the proof of: {stk}"

def wtFail {α} (what : MessageData) : TM α := do
  let cur := (← get).current
  let stk := (← get).stack
  throwError m!"[deep_translate] whole-term condition violated: {what}\n  in the step: {cur}\n  inside the proof of: {stk}"

/-! ## Types -/

/-- Module names of the shallow embedding (all modules share them). -/
def isWorldTy (e : Expr) : Bool := e.isConstOf `i
def isEntTy (e : Expr) : Bool := e.isConstOf `e

partial def ftOf (ty : Expr) : MetaM (Option FT) := do
  let ty ← whnfR ty
  if isEntTy ty then return some .e
  match ty with
  | .forallE _ dom cod _ =>
      if cod.hasLooseBVars then return none
      let dom' ← whnfR dom
      if isWorldTy dom' then
        let cod' ← whnfR cod
        if cod'.isProp then return some .s else return none
      let some a ← ftOf dom | return none
      let some b ← ftOf cod | return none
      return some (.arr a b)
  | _ => return none

def htOf? (ty : Expr) : MetaM (Option HT) := do
  let ty' ← whnfR ty
  if isWorldTy ty' then return some .w
  if ty'.isProp then return some .o
  return (← ftOf ty).map HT.L

def htOf (ty : Expr) : TM HT := do
  match ← htOf? ty with
  | some a => pure a
  | none => outside m!"type {← ppExpr ty} is not a type of 𝓛, the world type or Prop"

/-! ## Unfolding -/

/-- Constants never unfolded: the signature of the embedding and the logical constants. -/
def primitiveConsts : List Name :=
  [`i, `e, `R, `existsAt, `P, ``True, ``False, ``Not, ``And, ``Or, ``Iff, ``Exists, ``Eq, ``Ne,
   ``Classical.ofNonempty, ``Classical.choice]

/-- Unfold a constant application `c args` (definition or theorem value), `β`-reducing. -/
def unfoldApp? (e : Expr) : MetaM (Option Expr) := do
  let .const c lvls := e.getAppFn | return none
  if primitiveConsts.contains c then return none
  let info ← getConstInfo c
  let v ← match info with
    | .defnInfo d => pure d.value
    | .thmInfo t => pure t.value
    | _ => return none
  if info.levelParams.length != lvls.length then return none
  let v := v.instantiateLevelParams info.levelParams lvls
  return some (v.beta e.getAppArgs)

/-! ## Terms and formulas: the image `img` -/

mutual
/-- Image of a Lean term (of a type of `𝓛`, the world type or `Prop`) in the current context;
definitions unfolded, `β`-reduced, `η`-reduced. -/
partial def img (c : TCtx) (e : Expr) : TM DT := do
  let x ← img0 c e
  pure x.nf

partial def img0 (c : TCtx) (e : Expr) : TM DT := do
  match e with
  | .mdata _ b => img0 c b
  | .letE _ _ v b _ => img0 c (b.instantiate1 v)
  | .fvar id =>
      match c.idx? id with
      | some k => pure (.var k)
      | none =>
          if (← get).nonemptyVar == some id then
            match c.idx? id with
            | some k => pure (.var k)
            | none => outside "nonempty witness out of scope"
          else outside s!"free variable {(← id.getDecl).userName} is not a deep variable"
  | .lam n ty b bi =>
      let some a ← htOf? ty | outside s!"λ over a type outside 𝓛: {← ppExpr ty}"
      if (← htOf? (← inferType e)).isNone then
        outside m!"the term {← ppExpr e} has type {← ppExpr (← inferType e)}, not a type of 𝓛 or the world type"
      withLocalDecl n bi ty fun x => do
        let c' := c.pushVar x.fvarId! a
        let body ← img0 c' (b.instantiate1 x)
        match a with
        | .L t => pure (.lamL t body)
        | .w => pure (.wabs body)
        | .o => outside "λ over Prop"
  | .forallE n ty b bi =>
      if (← isProp ty) && !b.hasLooseBVars then
        pure (.imp (← img0 c ty) (← img0 c b))
      else if (← isProp ty) then
        -- a motive applied to the proof: β-reduce, then it must not depend on it
        withLocalDecl n bi ty fun h => do
          let body ← Core.betaReduce (b.instantiate1 h)
          if body.containsFVar h.fvarId! then outside m!"dependent implication {← ppExpr e}"
          pure (.imp (← img0 c ty) (← img0 c body))
      else
        let some a ← htOf? ty | outside s!"∀ over a type outside 𝓛: {← ppExpr ty}"
        withLocalDecl n bi ty fun x => do
          pure (.all a (← img0 (c.pushVar x.fvarId! a) (b.instantiate1 x)))
  | .app .. | .const .. => imgApp c e
  | .proj .. => outside s!"projection in a term: {← ppExpr e}"
  | _ => outside s!"term {← ppExpr e}"

partial def imgApp (c : TCtx) (e : Expr) : TM DT := do
  let f := e.getAppFn
  let args := e.getAppArgs
  if f.isLambda then return ← img0 c e.headBeta
  if let .mdata _ f' := f then return ← img0 c (mkAppN f' args)
  if let .letE _ _ v b _ := f then return ← img0 c (mkAppN (b.instantiate1 v) args)
  if let .const n _ := f then
    let arity : Option Nat := match n with
      | ``Not => some 1 | ``And => some 2 | ``Or => some 2 | ``Iff => some 2 | ``Exists => some 2
      | ``Eq => some 3 | ``Ne => some 3 | `R => some 2 | `existsAt => some 2 | _ => none
    if let some k := arity then
      if args.size < k then
        -- an under-applied connective (e.g. the nominal `Eq w`): η-expand first
        return ← img0 c (← etaExpand e)
  match f with
  | .const n _ =>
      match n, args.size with
      | ``False, 0 => pure .bot
      | ``True, 0 => pure (.imp .bot .bot)
      | ``Not, 1 => pure (.imp (← img0 c args[0]!) .bot)
      | ``And, 2 => pure (.and (← img0 c args[0]!) (← img0 c args[1]!))
      | ``Or, 2 => pure (.or (← img0 c args[0]!) (← img0 c args[1]!))
      | ``Iff, 2 =>
          let a ← img0 c args[0]!
          let b ← img0 c args[1]!
          pure (.and (.imp a b) (.imp b a))
      | ``Exists, 2 =>
          let some a ← htOf? args[0]! | outside s!"∃ over {← ppExpr args[0]!}"
          let p := args[1]!
          withLocalDecl `x .default args[0]! fun x => do
            pure (.ex a (← img0 (c.pushVar x.fvarId! a) (mkApp p x).headBeta))
      | ``Eq, 3 =>
          let some a ← htOf? args[0]! | outside s!"= at {← ppExpr args[0]!}"
          pure (.eq a (← img0 c args[1]!) (← img0 c args[2]!))
      | ``Ne, 3 =>
          let some a ← htOf? args[0]! | outside s!"≠ at {← ppExpr args[0]!}"
          pure (.imp (.eq a (← img0 c args[1]!) (← img0 c args[2]!)) .bot)
      | `R, 2 => pure (.rel (← img0 c args[0]!) (← img0 c args[1]!))
      | `existsAt, 2 => pure (.act (← img0 c args[0]!) (← img0 c args[1]!))
      | `P, _ => imgSpine c .pos (.L FT.th) args
      | ``Classical.ofNonempty, 2 | ``Classical.choice, 2 =>
          -- `ofNonempty` is `choice inferInstance`; both are the one entity `c₀` (proof irrelevance)
          unless isEntTy (← whnfR args[0]!) do outside "Classical.ofNonempty at a type other than e"
          match (← get).nonemptyVar with
          | some id =>
              modify fun s => { s with nonemptyUsed := true }
              match c.idx? id with
              | some k => imgSpine c (.var k) (.L .e) args[2:].toArray
              | none => outside "nonempty witness out of scope"
          | none => throwError "[deep_translate] needs-nonempty"
      | _, _ =>
          match ← unfoldApp? e with
          | some e' => img0 c e'
          | none => outside s!"constant {n} (no definition to unfold)"
  | .fvar id =>
      match c.idx? id with
      | some k =>
          let some a := c.deep[k]? | outside "variable"
          imgSpine c (.var k) a args
      | none => outside s!"application of {(← id.getDecl).userName}, not a deep variable"
  | _ => outside s!"application head {← ppExpr f}"

partial def imgSpine (c : TCtx) (hd : DT) (a : HT) (args : Array Expr) : TM DT := do
  let mut x := hd
  let mut ty := a
  for arg in args do
    match ty with
    | .L (.arr _ b) =>
        x := .appL x (← img0 c arg)
        ty := .L b
    | .L .s =>
        x := .holds x (← img0 c arg)
        ty := .o
    | _ => outside "over-applied term"
  pure x
end

/-! ## Conversion: `βη` as derivations -/

def liftEx {α} (x : Except String α) : TM α := do
  match x with
  | .ok a => pure a
  | .error e => throwError e

/-- `eq o (holds (wabs φ) i) (φ[i])`. -/
def betaWEq (φ i : DT) : Der :=
  .propExt (.holds (.wabs φ) i) (φ.inst i) (.betaWE (.hyp 0)) (.betaWI φ i (.hyp 0))

/-- Can Leibniz at `a` with this motive and sides be emitted? -/
def leibOk (ctx : List HT) (a : HT) (φ s t : DT) : Bool :=
  a.plain || ((wtProof (a :: ctx) φ).toOption.isSome && (certProof ctx a s).toOption.isSome &&
    (certProof ctx a t).toOption.isSome)

/-- From `d : eq a X Y` and a context `C[·]` (a formula/term with hole `var 0` of type `a` in
`a :: ctx`, of type `b`), derive `eq b C[X] C[Y]` (Leibniz on the motive `C[X] = C[·]`). -/
def congrD (ctx : List HT) (a b : HT) (C : DT) (X Y : DT) (d : Der) : TM Der := do
  let CX := C.inst X
  let motive := DT.eq b (CX.shift 1) C
  unless leibOk ctx a motive X Y do
    wtFail s!"congruence at {a} needs Leibniz with motive {motive}, sides {X}, {Y}"
  pure (.leib a motive X Y d (.refl b CX))

mutual
/-- `eqNF ctx a X = (N, d)`: `N = X.nf` and `d` derives `eq a X N`. -/
partial def eqNF (ctx : List HT) (a : HT) (X : DT) : TM (DT × Der) := do
  if let some r := (← get).eqCache[(ctx, a, X)]? then return r
  let r ← eqNF0 ctx a X
  modify fun s => { s with eqCache := s.eqCache.insert (ctx, a, X) r }
  pure r

partial def eqNF0 (ctx : List HT) (a : HT) (X : DT) : TM (DT × Der) := do
  let N := X.nf
  if N == X then return (X, .refl a X)
  match X with
  | .appL f x =>
      let .L (.arr ta tb) ← liftEx (DT.ty ctx f) | throwError "eqNF appL"
      match f with
      | .lamL _ body =>
          let r := body.inst x
          let (N', dr) ← eqNF ctx (.L tb) r
          let db : Der := .betaL body x
          pure (N', if N' == r then db else .trans db dr)
      | _ =>
        let (f', df) ← eqNF ctx (.L (.arr ta tb)) f
        if f' == f then
          let (x', dx) ← eqNF ctx (.L ta) x
          if x' == x then return (X, .refl a X)
          let C := DT.appL (f.shift 1) (.var 0)
          pure (.appL f x', ← congrD ctx (.L ta) (.L tb) C x x' dx)
        else
          -- the function changes: `funApp` at a certified argument
          let some (_, xs) := canonL ctx x
            | do
              -- no certified form: Leibniz on the function
              let C := DT.appL (.var 0) (x.shift 1)
              let d1 ← congrD ctx (.L (.arr ta tb)) (.L tb) C f f' df
              let Y := DT.appL f' x
              let (N', dY) ← eqNF ctx (.L tb) Y
              return (N', if N' == Y then d1 else .trans d1 dY)
          let mut d : Der := .refl (.L tb) X
          let mut first := true
          if xs != x then
            let (xn, dxn) ← eqNF ctx (.L ta) x
            let (_, dxs) ← eqNF ctx (.L ta) xs
            -- x = xs  via their common normal form
            let dxx : Der := .trans dxn (.symm dxs)
            let _ := xn
            d ← congrD ctx (.L ta) (.L tb) (.appL (f.shift 1) (.var 0)) x xs dxx
            first := false
          let step : Der := .allE xs (.funApp df)
          d := if first then step else .trans d step
          let Y := DT.appL f' xs
          let (N', dY) ← eqNF ctx (.L tb) Y
          pure (N', if N' == Y then d else .trans d dY)
  | .lamL ta body =>
      let .L tb ← liftEx (DT.ty (.L ta :: ctx) body) | throwError "eqNF lamL"
      let (body', db) ← eqNF (.L ta :: ctx) (.L tb) body
      let X' := DT.lamL ta body'
      let d ← if body' == body then pure (Der.refl a X) else do
        -- funExt: ∀z. (λ body) z = (λ body') z
        let b1 := body.shift 1 1
        let b2 := body'.shift 1 1
        let inner : Der := .trans (.trans (.betaL b1 (.var 0)) db) (.symm (.betaL b2 (.var 0)))
        pure (.funExt (.allI (.L ta) inner))
      -- η
      match body' with
      | .appL g (.var 0) =>
          if !g.hasVar 0 then
            let g0 := g.down
            let de : Der := .funExt (.allI (.L ta) (.betaL (body'.shift 1 1) (.var 0)))
            let d' := if body' == body then de else .trans d de
            let (N', dn) ← eqNF ctx a g0
            pure (N', if N' == g0 then d' else .trans d' dn)
          else pure (X', d)
      | _ => pure (X', d)
  | .wabs body =>
      let (body', db) ← eqNF (.w :: ctx) .o body
      let X' := DT.wabs body'
      let d ← if body' == body then pure (Der.refl a X) else do
        let b1 := body.shift 1 1
        let b2 := body'.shift 1 1
        let inner : Der := .trans (.trans (betaWEq b1 (.var 0)) db) (.symm (betaWEq b2 (.var 0)))
        pure (.wExt (.allI .w inner))
      match body' with
      | .holds p (.var 0) =>
          if !p.hasVar 0 then
            let p0 := p.down
            let de : Der := .wExt (.allI .w (betaWEq (body'.shift 1 1) (.var 0)))
            let d' := if body' == body then de else .trans d de
            let (N', dn) ← eqNF ctx a p0
            pure (N', if N' == p0 then d' else .trans d' dn)
          else pure (X', d)
      | _ => pure (X', d)
  | .holds p i =>
      let (p', dp) ← eqNF ctx (.L .s) p
      let d0 ← if p' == p then pure (Der.refl .o X) else
        congrD ctx (.L .s) .o (.holds (.var 0) (i.shift 1)) p p' dp
      match p' with
      | .wabs body =>
          let r := body.inst i
          let (N', dr) ← eqNF ctx .o r
          let d1 : Der := if p' == p then betaWEq body i else .trans d0 (betaWEq body i)
          pure (N', if N' == r then d1 else .trans d1 dr)
      | _ => pure (.holds p' i, d0)
  | .act x i =>
      let (x', dx) ← eqNF ctx (.L .e) x
      pure (.act x' i, ← congrD ctx (.L .e) .o (.act (.var 0) (i.shift 1)) x x' dx)
  | .imp p q => binO ctx X .imp p q
  | .and p q => binO ctx X .and p q
  | .or p q => binO ctx X .or p q
  | .all b body =>
      let (body', db) ← eqNF (b :: ctx) .o body
      let X' := DT.all b body'
      -- all b body ⊢ all b body' and back
      let fwd : Der := .allI b (.leib .o (.var 0) body body' db (.allE (.var 0) (.hyp 0)))
      let bwd : Der := .allI b (.leib .o (.var 0) body' body (.symm db) (.allE (.var 0) (.hyp 0)))
      pure (X', .propExt X X' fwd bwd)
  | .ex .w (.and (.rel I (.var 0)) B) =>
      -- `◇`, classically: `(∃v. R I v ∧ B) = ¬∀v. R I v → ¬B'`
      let (B', dB) ← eqNF (.w :: ctx) .o B
      let A := DT.all .w (.imp (.rel I (.var 0)) (.imp B' .bot))
      let X' := DT.imp A .bot
      let fwd : Der := .impI A (.exE (.hyp 1)
        (.impE (.impE (.allE (.var 0) (.hyp 1)) (.andL (.hyp 0)))
          (.leib .o (.var 0) B B' dB (.andR (.hyp 0)))) .bot)
      let body := DT.and (.rel I (.var 0)) B
      let fwd := if B' == B then .impI A (.exE (.hyp 1)
        (.impE (.impE (.allE (.var 0) (.hyp 1)) (.andL (.hyp 0))) (.andR (.hyp 0))) .bot) else fwd
      let toB : Der := if B' == B then .hyp 0 else .leib .o (.var 0) B' B (.symm dB) (.hyp 0)
      let bwd : Der := .byContra X (.impE (.hyp 1) (.allI .w (.impI (.rel I (.var 0)) (.impI B'
        (.impE (.hyp 2) (.exI .w (body.shift 1 1) (.var 0) (.andI (.hyp 1) toB)))))))
      pure (X', .propExt X X' fwd bwd)
  | .ex (.L .e) (.act (.var 0) I) =>
      -- `(∃x. x @ I) = (∃x. x @ I ∧ ⊤)`
      let body' := DT.and (.act (.var 0) I) (.imp .bot .bot)
      let X' := DT.ex (.L .e) body'
      let fwd : Der := .exE (.hyp 0) (.exI (.L .e) (body'.shift 1 1) (.var 0)
        (.andI (.hyp 0) (.impI .bot (.hyp 0)))) X'
      let bwd : Der := .exE (.hyp 0) (.exI (.L .e) ((DT.act (.var 0) I).shift 1 1) (.var 0)
        (.andL (.hyp 0))) X
      pure (X', .propExt X X' fwd bwd)
  | .ex b body =>
      let (body', db) ← eqNF (b :: ctx) .o body
      let X' := DT.ex b body'
      let fwd : Der := .exE (.hyp 0) (.exI b (body'.shift 1 1) (.var 0)
        (.leib .o (.var 0) body body' db (.hyp 0))) X'
      let bwd : Der := .exE (.hyp 0) (.exI b (body.shift 1 1) (.var 0)
        (.leib .o (.var 0) body' body (.symm db) (.hyp 0))) X
      pure (X', .propExt X X' fwd bwd)
  | .eq b s t =>
      let (s', ds) ← eqNF ctx b s
      let (t', dt) ← eqNF ctx b t
      let X' := DT.eq b s' t'
      -- s = t ⊢ s' = t' : trans (symm ds) (trans h dt); and back
      let fwd : Der := .trans (.trans (.symm ds) (.hyp 0)) dt
      let bwd : Der := .trans (.trans ds (.hyp 0)) (.symm dt)
      let fwd := if s' == s then (if t' == t then Der.hyp 0 else .trans (.hyp 0) dt) else fwd
      let bwd := if s' == s then (if t' == t then Der.hyp 0 else .trans (.hyp 0) (.symm dt)) else bwd
      pure (X', .propExt X X' fwd bwd)
  | _ => throwError s!"eqNF: unexpected {X}"

partial def binO (ctx : List HT) (X : DT) (mk : DT → DT → DT) (p q : DT) : TM (DT × Der) := do
  let (p', dp) ← eqNF ctx .o p
  let (q', dq) ← eqNF ctx .o q
  let mut d : Der := .refl .o X
  let mut first := true
  if p' != p then
    d ← congrD ctx .o .o (mk (.var 0) (q.shift 1)) p p' dp
    first := false
  if q' != q then
    let s ← congrD ctx .o .o (mk (p'.shift 1) (.var 0)) q q' dq
    d := if first then s else .trans d s
  pure (mk p' q', d)
end

/-- Turn a derivation of `X` into one of `Y`, for `βη`-equal `X`, `Y` (formulas). -/
def conv (ctx : List HT) (d : Der) (X Y : DT) : TM Der := do
  if X == Y then return d
  -- cheap cases: world β at the top
  if let .holds (.wabs φ) i := X then
    if φ.inst i == Y then return .betaWE d
  if let .holds (.wabs φ) i := Y then
    if φ.inst i == X then return .betaWI φ i d
  let (nX, dX) ← eqNF ctx .o X
  let (nY, dY) ← eqNF ctx .o Y
  unless nX == nY do
    throwError m!"[deep_translate] not convertible:\n  {X}\n  {Y}\n(normal forms\n  {nX}\n  {nY})"
  let deq : Der := if nY == Y then dX else .trans dX (.symm dY)
  pure (.leib .o (.var 0) X Y deq d)

/-- Expose an implication/quantifier/conjunction/... at the head of a conclusion. -/
def expose (ctx : List HT) (d : Der) (X : DT) : TM (Der × DT) := do
  match X with
  | .imp .. | .all .. | .and .. | .or .. | .ex .. | .eq .. | .bot => pure (d, X)
  | _ =>
      -- a `◇` at the head stays an `∃` over worlds (its `nf` is `¬□¬`)
      if let h@(.ex .w (.and (.rel _ (.var 0)) _)) := X.hnf then
        return (← conv ctx d X h, h)
      let N := X.nf
      pure (← conv ctx d X N, N)

end Programme.H

end


/-! ## Tool part `Prf` -/
section

/-! # Thread H: the proof-term walker -/

open Lean Meta Elab Command Term
open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.HOLX
  Programme.«20261022-1724-ontological».ThWhole

namespace Programme.H

/-- The canonical certified form of an `∀E`/`∃I` instance (`emb` of an `𝓛`-term). -/
def canonInst (c : TCtx) (a : HT) (arg : Expr) : TM DT := do
  let x ← img c arg
  match a with
  | .L _ =>
      match canonL c.deep x with
      | some (_, x') => pure x'
      | none => wtFail m!"instance {← ppExpr arg} is not a term of 𝓛 (image {x})"
  | _ => pure x

/-- Replace every argument of an `𝓛`-application by its canonical certified form (if it has one). -/
partial def certify (ctx : List HT) : DT → DT
  | .appL f y =>
      let y' := match canonL ctx y with | some (_, z) => z | none => certify ctx y
      .appL (certify ctx f) y'
  | .lamL a b => .lamL a (certify (.L a :: ctx) b)
  | .wabs b => .wabs (certify (.w :: ctx) b)
  | .holds p i => .holds (certify ctx p) i
  | .act x i => .act (certify ctx x) i
  | .imp p q => .imp (certify ctx p) (certify ctx q)
  | .and p q => .and (certify ctx p) (certify ctx q)
  | .or p q => .or (certify ctx p) (certify ctx q)
  | .all a b => .all a (certify (a :: ctx) b)
  | .ex a b => .ex a (certify (a :: ctx) b)
  | .eq a s t => .eq a (certify ctx s) (certify ctx t)
  | x => x

def addSentence (S : LT) (src : String) : TM Nat := do
  let st ← get
  match st.sentences.findIdx? (· == S) with
  | some k => pure k
  | none =>
      set { st with sentences := st.sentences.push S, sentenceNames := st.sentenceNames.push src }
      pure st.sentences.size

/-- Peel exactly `n` quantifiers (fewer if there are not so many). -/
def peelN : Nat → DT → List HT × DT
  | n + 1, .all a b => let (bs, body) := peelN n b; (a :: bs, body)
  | _, x => ([], x)

/-- Peel a prefix of quantifiers. -/
def peelAll : DT → List HT × DT
  | .all a b => let (bs, body) := peelAll b; (a :: bs, body)
  | x => ([], x)

/-- A validity fact `∀ x₁ … w … xₙ, body` (one world binder, the others at types of `𝓛`): its
`𝓛`-sentence `∀x₁…xₙ. body` joins `T` (its index is supplied by `getIdx`), and the derivation of
its image is returned. -/
def factDerWith (c : TCtx) (src : String) (ty : Expr) (getIdx : LT → TM Nat) : TM (Der × DT) := do
  let F ← img c ty
  let (bs, body) := peelAll F
  let wposs := (List.range bs.length).filter fun j => bs[j]? == some HT.w
  let [wpos] := wposs | outside m!"{src}: not a validity statement with one world quantifier: {F}"
  let n := bs.length
  let ctx' := bs.reverse ++ c.deep
  let wi := n - 1 - wpos
  let some S := sentenceOf ctx' wi body
    | outside m!"{src}: the statement is not an 𝓛-sentence: {body}"
  -- the `𝓛`-binders, outermost first, with their indices in `ctx'`
  let lbs := (List.range n).filterMap fun j =>
    match bs[j]? with | some (HT.L t) => some (t, n - 1 - j) | _ => none
  let nl := lbs.length
  -- closedness: no `𝓛`-variable beyond the binders
  let rec maxVar : LT → Nat → Bool
    | .var k, d => k < d
    | .app f x, d => maxVar f d && maxVar x d
    | .lam _ b, d => maxVar b (d + 1)
    | .neg x, d | .box x, d => maxVar x d
    | .and x y, d | .or x y, d | .imp x y, d | .eq _ x y, d => maxVar x d && maxVar y d
    | .all _ b, d | .ex _ b, d | .allE b, d | .exE b, d => maxVar b (d + 1)
    | _, _ => true
  unless maxVar S nl do outside m!"{src}: the statement has free parameters"
  let S' := lbs.reverse.foldl (fun acc (t, _) => LT.all t acc) S
  let idx ← getIdx S'
  let mut d : Der := .ax idx (.var wi)
  let mut X : DT := .holds (embD [] S') (.var wi)
  for (_, k) in lbs do
    let (d', X') ← expose ctx' d X
    let .all _ B := X' | throwError m!"factDer: expected ∀, got {X'}"
    d := .allE (.var k) d'
    X := B.inst (.var k)
  d ← conv ctx' d X body
  for b in bs.reverse do
    d := .allI b d
  pure (d, F)

def factDer (c : TCtx) (src : String) (ty : Expr) : TM (Der × DT) :=
  factDerWith c src ty fun S => addSentence S src

def isFactAxiom (n : Name) : MetaM Bool := do
  let info ← getConstInfo n
  let .axiomInfo _ := info | return false
  if [``propext, ``Classical.choice, ``Quot.sound, `iNonempty, `eNonempty].contains n then return false
  isProp info.type

def specialNames : List Name :=
  [``And.casesOn, ``And.intro, ``And.left, ``And.rec, ``And.right, ``Classical.byCases,
   ``Classical.byContradiction, ``Classical.em, ``Decidable.byCases, ``Eq.mp, ``Eq.mpr, ``Eq.ndrec,
   ``Eq.rec, ``Eq.refl, ``Eq.subst, ``Eq.symm, ``Eq.trans, ``Exists.casesOn, ``Exists.elim,
   ``Exists.intro, ``Exists.rec, ``False.casesOn, ``False.elim, ``False.rec, ``Iff.intro, ``Iff.mp,
   ``Iff.mpr, ``Iff.refl, ``Iff.rfl, ``Or.casesOn, ``Or.elim, ``Or.inl, ``Or.inr, ``Or.rec,
   ``absurd, ``cast, ``congrArg, ``congrFun, ``congrFun', ``forall_congr, `congr, ``eq_self, ``eq_true, ``funext, ``id,
   ``letFun, ``of_eq_true, ``propext, ``rfl]

def trivD : Der := .impI .bot (.hyp 0)
def topD : DT := .imp .bot .bot

/-- Peel the `𝓛`/world binders of a goal (unfolding `Mvalid`). -/
partial def peelVars {α} (ty : Expr) (xs : Array Expr) (k : Array Expr → Expr → TM α) : TM α := do
  let ty' ← whnf ty
  match ty' with
  | .forallE n dom body bi =>
      let seenW ← xs.anyM fun x => return isWorldTy (← whnfR (← inferType x))
      if seenW && isWorldTy (← whnfR dom) then k xs ty  -- a second world binder: the body's `□`
      else if (← htOf? dom).isSome && !(← isProp dom) then
        withLocalDecl n bi dom fun x => peelVars (body.instantiate1 x) (xs.push x) k
      else k xs ty
  | _ => k xs ty

def needsNonempty (ex : Exception) : TM Bool := do
  return (← ex.toMessageData.toString).startsWith "[deep_translate] needs-nonempty"

/-- A closed frame formula (C7): `rel` between bound world variables, `⊥`, connectives, world
quantifiers, equality of bound world variables. -/
def DT.frameOK : DT → Nat → Bool
  | .rel (.var i) (.var j), d => i < d && j < d
  | .eq .w (.var i) (.var j), d => i < d && j < d
  | .bot, _ => true
  | .imp p q, d | .and p q, d | .or p q, d => DT.frameOK p d && DT.frameOK q d
  | .all .w b, d | .ex .w b, d => DT.frameOK b (d + 1)
  | _, _ => false

mutual

partial def chk (c : TCtx) (e : Expr) (A : DT) : TM Der := do
  let (d, X) ← prf c e
  conv c.deep d X A

partial def prf (c : TCtx) (e : Expr) : TM (Der × DT) := do
  modify fun s => { s with steps := s.steps + 1, current := e }
  if (← get).steps > 400000 then outside m!"step limit at {← ppExpr e}"
  if (← get).steps % 500 == 0 then dbg (s!"[deep] step {(← get).steps}, depth {(← get).depth} {(← get).stack.take 3}")
  match e with
  | .mdata _ b => prf c b
  | .letE n ty v b _ =>
      if ← isProp ty then
        let (dv, A) ← prf c v
        withLocalDecl n .default ty fun h => do
          let (db, B) ← prf (c.pushHyp h.fvarId! A) (b.instantiate1 h)
          pure (.impE (.impI A db) dv, B)
      else prf c (b.instantiate1 v)
  | .fvar id =>
      if let some (k, A) := c.hypIdx? id then return (.hyp k, A)
      if c.isFact id then
        return ← factDer c s!"{(← id.getDecl).userName}" (← id.getType)
      outside m!"proof variable {(← id.getDecl).userName} is not a hypothesis"
  | .lam n ty b bi =>
      if ← isProp ty then
        let A ← img c ty
        withLocalDecl n bi ty fun h => do
          let (d, B) ← prf (c.pushHyp h.fvarId! A) (b.instantiate1 h)
          pure (.impI A d, .imp A B)
      else
        let a ← htOf ty
        withLocalDecl n bi ty fun x => do
          let (d, B) ← prf (c.pushVar x.fvarId! a) (b.instantiate1 x)
          pure (.allI a d, .all a B)
  | .app .. | .const .. => prfApp c e
  | .proj s i h =>
      let (d, X) ← prf c h
      let (d, X) ← expose c.deep d X
      match s, i, X with
      | ``And, 0, .and A _ => pure (.andL d, A)
      | ``And, 1, .and _ B => pure (.andR d, B)
      | ``Iff, 0, .and A _ => pure (.andL d, A)
      | ``Iff, 1, .and _ B => pure (.andR d, B)
      | _, _, _ => outside m!"projection {s}.{i} of {X}"
  | _ => outside m!"proof term {← ppExpr e}"

partial def applyArgs (c : TCtx) (d0 : Der) (X0 : DT) (args : Array Expr) : TM (Der × DT) := do
  let mut d := d0
  let mut X := X0
  for arg in args do
    let (d', X') ← expose c.deep d X
    match X' with
    | .imp A B =>
        let da ← chk c arg A
        d := .impE d' da
        X := B
    | .all a B =>
        let t ← canonInst c a arg
        d := .allE t d'
        X := B.inst t
    | _ => outside m!"argument {← ppExpr arg} applied to a proof of {X'}"
  pure (d, X)

/-- A goal `∀ x… w …, body` (statement hypotheses `facts` already in scope) with proof `pf`: its
`𝓛`-sentence `φ`, a derivation of `holds (emb φ) w` in `[.w]` and that target.  With `withNE`,
`Classical.ofNonempty : e` is a variable taken from the sentence `∃x.⊤` of `T`. -/
partial def goalCore (facts : Array FactVar) (goalTy pf : Expr) (withNE : Bool) :
    TM (LT × Der × DT) := do
  let savedNE := (← get).nonemptyVar
  modify fun s => { s with nonemptyVar := none }
  let r ← peelVars goalTy #[] fun xs body => do
    let ws ← xs.filterM fun x => do return isWorldTy (← whnfR (← inferType x))
    let #[w0] := ws | outside m!"statement {← ppExpr goalTy} is not a validity (one world binder)"
    let ls := xs.filter (· != w0)
    let q ← mkLambdaFVars ls (mkAppN pf xs)
    let mut c0 : TCtx := { vars := #[(w0.fvarId!, .w)], facts := facts }
    -- C7: hypotheses whose image is a closed frame formula go into the hypothesis list
    if facts.size > 0 then
      let mut frames : List (Nat × DT) := []
      let mut rest : Array FactVar := #[]
      let mut k := 0
      for f in facts do
        let F? ← try some <$> img c0 (← instantiateMVars (← f.fvar.getType)) catch _ => pure none
        match F? with
        | some F =>
            if DT.frameOK F 0 then
              frames := (k, F) :: frames
              c0 := c0.pushHyp (some f.fvar) F
            else rest := rest.push f
        | none => rest := rest.push f
        k := k + 1
      c0 := { c0 with facts := rest }
      modify fun s => { s with frames := frames }
    let Fimg ← img c0 (← mkForallFVars ls body)
    let (bs, fbody) := peelN ls.size Fimg
    let ctx' := bs.reverse ++ c0.deep
    let some S := sentenceOf ctx' bs.length fbody
      | outside m!"the statement is not an 𝓛-sentence: {fbody}"
    let φ := bs.reverse.foldl (fun acc b => match b with | .L t => LT.all t acc | _ => acc) S
    let target := DT.holds (embD [] φ) (.var 0)
    if withNE then
      withLocalDecl `c₀ .default (mkConst `e) fun cv => do
        modify fun s => { s with nonemptyVar := some cv.fvarId! }
        let neIdx ← addSentence (.ex .e .top) "NonEmpty"
        let c1 : TCtx := (c0.pushVar cv.fvarId! (.L .e)).pushHyp none (.imp .bot .bot)
        let (d, X) ← prf c1 q
        let d ← conv c1.deep d X (target.shift 1)
        let dNE0 : Der := .ax neIdx (.var 0)
        let XNE := DT.holds (embD [] (.ex .e .top)) (.var 0)
        let (dNE, XNE') ← expose c0.deep dNE0 XNE
        unless XNE' == DT.ex (.L .e) (.imp .bot .bot) do throwError m!"NonEmpty: {XNE'}"
        pure (φ, Der.exE dNE d target, target)
    else
      let (d, X) ← prf c0 q
      let d ← conv c0.deep d X target
      pure (φ, d, target)
  modify fun s => { s with nonemptyVar := savedNE }
  pure r

/-- A theorem whose statement is a validity of a closed `𝓛`-sentence is translated once (from the
theory so far) and then used as a sentence of the theory: a lemma.  Otherwise `none` (unfold). -/
partial def lemmaApp (c : TCtx) (n : Name) (args : Array Expr) : TM (Option (Der × DT)) := do
  unless (← get).useLemmas do return none
  if (← get).noLemma.contains n then return none
  let info ← getConstInfo n
  let .thmInfo tv := info | return none
  unless info.levelParams.isEmpty do return none
  let idx ← match (← get).lemmaIdx[n]? with
    | some k => pure k
    | none =>
      let st ← get
      let ref ← IO.mkRef (none : Option LT)
      let ok ← try
          let _ ← factDerWith c (toString n) info.type fun S => do ref.set (some S); pure 0
          pure true
        catch _ => pure false
      set st
      let some S ← ref.get | do
        modify fun s => { s with noLemma := s.noLemma.insert n }
        return none
      unless ok do
        modify fun s => { s with noLemma := s.noLemma.insert n }
        return none
      let enter : TM Unit := modify fun s => { s with stack := n :: s.stack, depth := s.depth + 1 }
      enter
      let (φ, d, target) ← try goalCore #[] info.type tv.value false catch ex => do
        unless ← needsNonempty ex do throw ex
        set st
        enter
        goalCore #[] info.type tv.value true
      unless φ == S do outside m!"lemma {n}: sentence mismatch {φ.toStr} vs {S.toStr}"
      let k ← match (← get).sentences.findIdx? (· == S) with
        | some k => pure k
        | none => do
            let k := (← get).sentences.size
            modify fun s => { s with sentences := s.sentences.push S,
                                     sentenceNames := s.sentenceNames.push s!"lemma {n}",
                                     lemmas := s.lemmas.push (k, n, d, target) }
            pure k
      modify fun s => { s with lemmaIdx := s.lemmaIdx.insert n k, stack := s.stack.tail,
                               depth := s.depth - 1 }
      pure k
  let (d, X) ← factDerWith c (toString n) info.type fun _ => pure idx
  return some (← applyArgs c d X args)

partial def prfApp (c : TCtx) (e : Expr) : TM (Der × DT) := do
  let f := e.getAppFn
  let args := e.getAppArgs
  if f.isLambda then return ← prf c e.headBeta
  if let .mdata _ f' := f then return ← prf c (mkAppN f' args)
  if let .letE _ _ v b _ := f then return ← prf c (mkAppN (b.instantiate1 v) args)
  match f with
  | .const n _ =>
      if let some r ← special c n args then return r
      if specialNames.contains n then
        -- partially applied logical constant: η-expand
        let e' ← etaExpand e
        if e'.isLambda then return ← prf c e'
        outside m!"{n} applied to too few arguments"
      if ← isFactAxiom n then
        let (d, X) ← factDer c s!"{n}" (← inferType f)
        return ← applyArgs c d X args
      let e ← match (← get).replace.lookup n with
        | some n' => pure (mkAppN (mkConst n' (f.constLevels!)) args)
        | none => pure e
      if let some r ← lemmaApp c e.getAppFn.constName! args then return r
      match ← unfoldApp? e with
      | some e' =>
          let st ← get
          if st.depth > 400 then outside m!"unfolding depth exceeded at {n}"
          modify fun s => { s with depth := s.depth + 1, stack := n :: s.stack }
          let r ← prf c e'
          modify fun s => { s with depth := s.depth - 1, stack := s.stack.tail }
          pure r
      | none => outside m!"constant {n}"
  | .fvar id =>
      if let some (k, A) := c.hypIdx? id then return ← applyArgs c (.hyp k) A args
      if c.isFact id then return ← factApp c id args
      outside m!"application of {(← id.getDecl).userName}, which is not a hypothesis"
  | .proj .. =>
      let (d, X) ← prf c f
      applyArgs c d X args
  | _ => outside m!"application head {← ppExpr f}"

/-- A hypothesis of the statement applied to arguments.  Leading arguments at types outside `𝓛`
(a schema, as `Ax1GenR`'s set of properties) are substituted into the statement first; the instance
must again be an `𝓛`-sentence. -/
partial def factApp (c : TCtx) (id : FVarId) (args : Array Expr) : TM (Der × DT) := do
  let name := s!"{(← id.getDecl).userName}"
  let mut ty ← instantiateMVars (← id.getType)
  let mut k := 0
  -- schema arguments
  repeat
    let ty' ← whnf ty
    let .forallE _ dom _ _ := ty' | break
    if (← htOf? dom).isSome || (← isProp dom) then break
    let some arg := args[k]? | outside m!"{name}: schema used without an instance"
    ty := ty'.bindingBody!.instantiate1 arg
    k := k + 1
  let src := if k == 0 then name else s!"{name} (instance)"
  let instFn ← mkLambdaFVars #[mkFVar id] (mkAppN (mkFVar id) (args.extract 0 k))
  let (d, X) ← factDerWith c src ty fun S => do
    let i ← addSentence S src
    if !ty.hasFVar && !instFn.hasFVar && !(← get).factTys.contains i then
      modify fun st => { st with factTys := st.factTys.insert i (ty, instFn) }
    pure i
  applyArgs c d X args[k:].toArray

/-- Leibniz substitution along `h : a = b` of type `α`, with Lean motive `mot x` (a `Prop`). -/
partial def leibCase (c : TCtx) (α aE bE : Expr) (mot : Expr → Expr) (m h : Expr) :
    TM (Der × DT) := do
  let ta ← htOf α
  let φ ← withLocalDecl `x .default α fun x => do img (c.pushVar x.fvarId! ta) (mot x)
  if ta.plain then
    let s ← img c aE
    let t ← img c bE
    let dh ← chk c h (.eq ta s t)
    let dm ← chk c m (φ.inst s)
    pure (.leib ta φ s t dh dm, φ.inst t)
  else
    let s ← canonInst c ta aE
    let t ← canonInst c ta bE
    let φ' := certify (ta :: c.deep) φ
    unless leibOk c.deep ta φ' s t do
      wtFail m!"Leibniz step at {ta} with motive {φ'} (sides {s}, {t})"
    let dh ← chk c h (.eq ta s t)
    let dm ← chk c m (φ'.inst s)
    pure (.leib ta φ' s t dh dm, φ'.inst t)

/-- Classical case split on `p` for the goal `q`. -/
partial def caseSplit (c : TCtx) (p q : Expr) (f1 f2 : Expr → Expr) : TM (Der × DT) := do
  let P ← img c p
  let Q ← img c q
  let c1 := c.pushHyp none (.imp Q .bot)
  let d1 ← withLocalDecl `h .default p fun h => chk (c1.pushHyp h.fvarId! P) (f1 h).headBeta Q
  let d2 ← withLocalDecl `h .default (mkNot p) fun h =>
    chk (c1.pushHyp h.fvarId! (.imp P .bot)) (f2 h).headBeta Q
  let dNotP : Der := .impI P (.impE (.hyp 1) d1)
  let dQ : Der := .impE (.impI (.imp P .bot) d2) dNotP
  pure (.byContra Q (.impE (.hyp 0) dQ), Q)

partial def orCase (c : TCtx) (a b : Expr) (h f g : Expr) (C : DT) : TM (Der × DT) := do
  let (dh, X) ← prf c h
  let (dh, X) ← expose c.deep dh X
  let .or A B := X | outside m!"∨-elimination of {X}"
  let d1 ← withLocalDecl `h .default a fun x => chk (c.pushHyp x.fvarId! A) (mkApp f x).headBeta C
  let d2 ← withLocalDecl `h .default b fun x => chk (c.pushHyp x.fvarId! B) (mkApp g x).headBeta C
  pure (.orE dh d1 d2, C)

partial def exCase (c : TCtx) (α p h f : Expr) (C : DT) : TM (Der × DT) := do
  let (dh, X) ← prf c h
  let (dh, X) ← expose c.deep dh X
  -- a `◇` already read as `¬□¬`: back to `∃v. R I v ∧ B` (`conv`: equal normal forms)
  let (dh, X) ← match X with
    | .imp (.all .w (.imp (.rel I (.var 0)) (.imp B .bot))) .bot =>
        let Y := DT.ex .w (.and (.rel I (.var 0)) B)
        pure (← conv c.deep dh X Y, Y)
    | _ => pure (dh, X)
  let .ex a φ := X | outside m!"∃-elimination of {X}"
  let d2 ← withLocalDecl `x .default α fun x => do
    let c1 := c.pushVar x.fvarId! a
    withLocalDecl `hx .default (mkApp p x).headBeta fun hx => do
      -- `∃x. x @ w` read as `∃ᴱx. ⊤`: the body is `x @ w ∧ ⊤`, the Lean hypothesis is `x @ w`
      if let .and B0 (.imp .bot .bot) := φ then
        let B ← img c1 (mkApp p x).headBeta
        if B.nf != φ.nf then
          let d ← chk ((c1.pushHyp none φ).pushHyp hx.fvarId! B) (mkApp2 f x hx).headBeta (C.shift 1)
          return .impE (.impI B d) (← conv c1.deep (.andL (.hyp 0)) B0 B)
      chk (c1.pushHyp hx.fvarId! φ) (mkApp2 f x hx).headBeta (C.shift 1)
  pure (.exE dh d2 C, C)

partial def andCase (c : TCtx) (a b h f : Expr) (C : DT) : TM (Der × DT) := do
  let (dh, X) ← prf c h
  let (dh, X) ← expose c.deep dh X
  let .and A B := X | outside m!"∧-elimination of {X}"
  let d ← withLocalDecl `ha .default a fun ha => withLocalDecl `hb .default b fun hb =>
    chk ((c.pushHyp ha.fvarId! A).pushHyp hb.fvarId! B) (mkApp2 f ha hb).headBeta C
  pure (.impE (.impE (.impI A (.impI B d)) (.andL dh)) (.andR dh), C)

/-- The motive of a non-dependent eliminator, applied to the major premise. -/
partial def motiveAt (c : TCtx) (motive major : Expr) : TM DT := do
  img c (mkApp motive major).headBeta

/-- Handlers for the logical constants; `none` if `n` is not one of them. -/
partial def special (c : TCtx) (n : Name) (args : Array Expr) : TM (Option (Der × DT)) := do
  let k := args.size
  let rest (m : Nat) : Array Expr := args[m:].toArray
  let fin (m : Nat) (r : Der × DT) : TM (Option (Der × DT)) := do
    if k == m then pure (some r) else some <$> applyArgs c r.1 r.2 (rest m)
  match n with
  | ``And.intro => do
      if k < 4 then return none
      let A ← img c args[0]!
      let B ← img c args[1]!
      let da ← chk c args[2]! A
      let db ← chk c args[3]! B
      fin 4 (.andI da db, .and A B)
  | ``And.left | ``And.right => do
      if k < 3 then return none
      let (d, X) ← prf c args[2]!
      let (d, X) ← expose c.deep d X
      let .and A B := X | outside m!"{n} of {X}"
      fin 3 (if n == ``And.left then (.andL d, A) else (.andR d, B))
  | ``And.casesOn => do
      if k < 5 then return none
      fin 5 (← andCase c args[0]! args[1]! args[3]! args[4]! (← motiveAt c args[2]! args[3]!))
  | ``And.rec => do
      if k < 5 then return none
      fin 5 (← andCase c args[0]! args[1]! args[4]! args[3]! (← motiveAt c args[2]! args[4]!))
  | ``Or.inl => do
      if k < 3 then return none
      let (d, A) ← prf c args[2]!
      let B ← img c args[1]!
      fin 3 (.orL B d, .or A B)
  | ``Or.inr => do
      if k < 3 then return none
      let (d, B) ← prf c args[2]!
      let A ← img c args[0]!
      fin 3 (.orR A d, .or A B)
  | ``Or.elim => do
      if k < 6 then return none
      fin 6 (← orCase c args[0]! args[1]! args[3]! args[4]! args[5]! (← img c args[2]!))
  | ``Or.casesOn => do
      if k < 6 then return none
      fin 6 (← orCase c args[0]! args[1]! args[3]! args[4]! args[5]! (← motiveAt c args[2]! args[3]!))
  | ``Or.rec => do
      if k < 6 then return none
      fin 6 (← orCase c args[0]! args[1]! args[5]! args[3]! args[4]! (← motiveAt c args[2]! args[5]!))
  | ``Exists.intro => do
      if k < 4 then return none
      let a ← htOf args[0]!
      let φ ← withLocalDecl `x .default args[0]! fun x => do
        img (c.pushVar x.fvarId! a) (mkApp args[1]! x).headBeta
      let t ← canonInst c a args[2]!
      let dh ← chk c args[3]! (φ.inst t)
      fin 4 (.exI a φ t dh, .ex a φ)
  | ``Exists.elim => do
      if k < 5 then return none
      fin 5 (← exCase c args[0]! args[1]! args[3]! args[4]! (← img c args[2]!))
  | ``Exists.casesOn => do
      if k < 5 then return none
      fin 5 (← exCase c args[0]! args[1]! args[3]! args[4]! (← motiveAt c args[2]! args[3]!))
  | ``Exists.rec => do
      if k < 5 then return none
      fin 5 (← exCase c args[0]! args[1]! args[4]! args[3]! (← motiveAt c args[2]! args[4]!))
  | ``False.elim => do
      if k < 2 then return none
      let C ← img c args[0]!
      let d ← chk (c.pushHyp none (.imp C .bot)) args[1]! .bot
      fin 2 (.byContra C d, C)
  | ``False.rec | ``False.casesOn => do
      if k < 2 then return none
      let C ← motiveAt c args[0]! args[1]!
      let d ← chk (c.pushHyp none (.imp C .bot)) args[1]! .bot
      fin 2 (.byContra C d, C)
  | ``absurd => do
      if k < 4 then return none
      let A ← img c args[0]!
      let B ← img c args[1]!
      let c' := c.pushHyp none (.imp B .bot)
      let d1 ← chk c' args[2]! A
      let d2 ← chk c' args[3]! (.imp A .bot)
      fin 4 (.byContra B (.impE d2 d1), B)
  | ``Classical.byContradiction => do
      if k < 2 then return none
      let P ← img c args[0]!
      let d ← withLocalDecl `hn .default (mkNot args[0]!) fun hn =>
        chk (c.pushHyp hn.fvarId! (.imp P .bot)) (mkApp args[1]! hn).headBeta .bot
      fin 2 (.byContra P d, P)
  | ``Classical.byCases => do
      if k < 4 then return none
      fin 4 (← caseSplit c args[0]! args[1]! (mkApp args[2]!) (mkApp args[3]!))
  | ``Decidable.byCases => do
      if k < 5 then return none
      fin 5 (← caseSplit c args[0]! args[1]! (mkApp args[3]!) (mkApp args[4]!))
  | ``dite => do
      if k < 5 then return none
      unless ← isProp args[0]! do return none
      fin 5 (← caseSplit c args[1]! args[0]! (mkApp args[3]!) (mkApp args[4]!))
  | ``ite => do
      if k < 5 then return none
      unless ← isProp args[0]! do return none
      fin 5 (← caseSplit c args[1]! args[0]! (fun _ => args[3]!) (fun _ => args[4]!))
  | ``Classical.em => do
      if k < 1 then return none
      let P ← img c args[0]!
      let X := DT.or P (.imp P .bot)
      let inner : Der := .impI P (.impE (.hyp 1) (.orL (.imp P .bot) (.hyp 0)))
      fin 1 (.byContra X (.impE (.hyp 0) (.orR P inner)), X)
  | ``Iff.intro => do
      if k < 4 then return none
      let A ← img c args[0]!
      let B ← img c args[1]!
      let d1 ← chk c args[2]! (.imp A B)
      let d2 ← chk c args[3]! (.imp B A)
      fin 4 (.andI d1 d2, .and (.imp A B) (.imp B A))
  | ``Iff.mp | ``Iff.mpr => do
      if k < 3 then return none
      let (d, X) ← prf c args[2]!
      let (d, X) ← expose c.deep d X
      let .and L R := X | outside m!"{n} of {X}"
      fin 3 (if n == ``Iff.mp then (.andL d, L) else (.andR d, R))
  | ``Iff.rfl | ``Iff.refl => do
      if k < 1 then return none
      let A ← img c args[0]!
      let d : Der := .impI A (.hyp 0)
      fin 1 (.andI d d, .and (.imp A A) (.imp A A))
  | ``id => do
      if k < 2 then return none
      let (d, X) ← prf c args[1]!
      fin 2 (d, X)
  | ``True.intro | ``trivial => fin 0 (trivD, topD)
  | ``Eq.refl | ``rfl => do
      if k < 2 then return none
      let a ← htOf args[0]!
      let t ← img c args[1]!
      fin 2 (.refl a t, .eq a t t)
  | ``Eq.symm => do
      if k < 4 then return none
      let (d, X) ← prf c args[3]!
      let (d, X) ← expose c.deep d X
      let .eq a s t := X | outside m!"Eq.symm of {X}"
      fin 4 (.symm d, .eq a t s)
  | ``Eq.trans => do
      if k < 6 then return none
      let (d1, X) ← prf c args[4]!
      let (d1, X) ← expose c.deep d1 X
      let .eq a s t := X | outside m!"Eq.trans of {X}"
      let u ← img c args[3]!
      let d2 ← chk c args[5]! (.eq a t u)
      fin 6 (.trans d1 d2, .eq a s u)
  | ``Eq.mpr => do
      if k < 4 then return none
      let A ← img c args[0]!
      let B ← img c args[1]!
      let dh ← chk c args[2]! (.eq .o A B)
      let db ← chk c args[3]! B
      fin 4 (.leib .o (.var 0) B A (.symm dh) db, A)
  | ``Eq.mp | ``cast => do
      if k < 4 then return none
      let A ← img c args[0]!
      let B ← img c args[1]!
      let dh ← chk c args[2]! (.eq .o A B)
      let da ← chk c args[3]! A
      fin 4 (.leib .o (.var 0) A B dh da, B)
  | ``Eq.ndrec => do
      if k < 6 then return none
      fin 6 (← leibCase c args[0]! args[1]! args[4]! (fun x => (mkApp args[2]! x).headBeta)
        args[3]! args[5]!)
  | ``Eq.rec => do
      if k < 6 then return none
      let mot := args[2]!
      let .lam _ _ (.lam _ _ body _) _ := mot | outside "Eq.rec with a motive that is not λ x h"
      if body.hasLooseBVar 0 then outside "Eq.rec with a motive depending on the proof"
      fin 6 (← leibCase c args[0]! args[1]! args[4]! (fun x => (body.lowerLooseBVars 1 1).instantiate1 x)
        args[3]! args[5]!)
  | ``Eq.subst => do
      if k < 6 then return none
      fin 6 (← leibCase c args[0]! args[2]! args[3]! (fun x => (mkApp args[1]! x).headBeta)
        args[5]! args[4]!)
  | ``congrArg => do
      if k < 6 then return none
      let α := args[0]!
      let a1 := args[2]!
      let a2 := args[3]!
      let f := args[4]!
      let fa1 := (mkApp f a1).headBeta
      let lv ← getLevel' args[1]!
      let mot (x : Expr) : Expr := mkApp3 (mkConst ``Eq [lv]) args[1]! fa1 (mkApp f x).headBeta
      let m := mkApp2 (mkConst ``Eq.refl [lv]) args[1]! fa1
      let _ := α
      fin 6 (← leibCase c α a1 a2 mot m args[5]!)
  | `congr => do
      -- `congr h₁ h₂ : f₁ a₁ = f₂ a₂` as `(congrFun h₁ a₁).trans (congrArg f₂ h₂)`
      if k < 8 then return none
      let e' ← mkEqTrans (← mkCongrFun args[6]! args[4]!) (← mkCongrArg args[3]! args[7]!)
      fin 8 (← prf c e')
  | ``forall_congr => do
      -- `forall_congr h : (∀a, p a) = (∀a, q a)` as `propext ⟨λ hp a. (h a) ▸ hp a, λ hq a. (h a) ▸ hq a⟩`
      -- (core's own proof is `funext h ▸ rfl`, `funext` at `α → Prop`)
      if k < 4 then return none
      let α := args[0]!
      let p := args[1]!
      let q := args[2]!
      let h := args[3]!
      let allP ← withLocalDecl `a .default α fun a => mkForallFVars #[a] (mkApp p a).headBeta
      let allQ ← withLocalDecl `a .default α fun a => mkForallFVars #[a] (mkApp q a).headBeta
      let fwd ← withLocalDecl `hp .default allP fun hp => withLocalDecl `a .default α fun a => do
        mkLambdaFVars #[hp, a] (← mkEqMP (mkApp h a) (mkApp hp a))
      let bwd ← withLocalDecl `hq .default allQ fun hq => withLocalDecl `a .default α fun a => do
        mkLambdaFVars #[hq, a] (← mkEqMPR (mkApp h a) (mkApp hq a))
      let e' := mkApp3 (mkConst ``propext) allP allQ (mkApp4 (mkConst ``Iff.intro) allP allQ fwd bwd)
      fin 4 (← prf c e')
  | ``congrFun | ``congrFun' => do
      if k < 6 then return none
      -- `congrFun (congrArg f h) x` is `congrArg (λy. f y x) h` (no equation between functions)
      let h4 := args[4]!
      if h4.isAppOfArity ``congrArg 6 then
        let x := args[5]!
        let f := h4.appFn!.appArg!
        let fnew ← withLocalDecl `y .default h4.getAppArgs[0]! fun y =>
          mkLambdaFVars #[y] (mkApp (mkApp f y).headBeta x).headBeta
        return ← fin 6 (← prf c (← mkCongrArg fnew h4.appArg!))
      let ta ← htOf args[0]!
      let F ← img c args[2]!
      let G ← img c args[3]!
      match ta with
      | .L t =>
          let .L (.arr _ tb) ← liftEx (DT.ty c.deep F) | outside "congrFun type"
          let x ← canonInst c ta args[5]!
          let dh ← chk c args[4]! (.eq (.L (.arr t tb)) F G)
          fin 6 (.allE x (.funApp dh), .eq (.L tb) (.appL F x) (.appL G x))
      | .w =>
          let dh ← chk c args[4]! (.eq (.L .s) F G)
          let i ← img c args[5]!
          fin 6 (.allE i (.wApp dh), .eq .o (.holds F i) (.holds G i))
      | _ => outside "congrFun over Prop"
  | ``funext => do
      if k < 5 then return none
      let ta ← htOf args[0]!
      let F ← img c args[2]!
      let G ← img c args[3]!
      match ta with
      | .L t =>
          let .L (.arr _ tb) ← liftEx (DT.ty c.deep F) | outside "funext type"
          let dh ← chk c args[4]! (.all (.L t) (.eq (.L tb) (.appL (F.shift 1) (.var 0))
            (.appL (G.shift 1) (.var 0))))
          fin 5 (.funExt dh, .eq (.L (.arr t tb)) F G)
      | .w =>
          let dh ← chk c args[4]! (.all .w (.eq .o (.holds (F.shift 1) (.var 0))
            (.holds (G.shift 1) (.var 0))))
          fin 5 (.wExt dh, .eq (.L .s) F G)
      | _ => outside "funext over Prop"
  | ``propext => do
      if k < 3 then return none
      let A ← img c args[0]!
      let B ← img c args[1]!
      let I := DT.and (.imp A B) (.imp B A)
      let dh1 ← chk (c.pushHyp none A) args[2]! I
      let dh2 ← chk (c.pushHyp none B) args[2]! I
      fin 3 (.propExt A B (.impE (.andL dh1) (.hyp 0)) (.impE (.andR dh2) (.hyp 0)), .eq .o A B)
  | ``of_eq_true => do
      if k < 2 then return none
      let P ← img c args[0]!
      let dh ← chk c args[1]! (.eq .o P topD)
      fin 2 (.leib .o (.var 0) topD P (.symm dh) trivD, P)
  | ``eq_true => do
      if k < 2 then return none
      let P ← img c args[0]!
      let d2 ← chk (c.pushHyp none topD) args[1]! P
      fin 2 (.propExt P topD trivD d2, .eq .o P topD)
  | ``eq_self => do
      if k < 2 then return none
      let a ← htOf args[0]!
      let t ← img c args[1]!
      let E := DT.eq a t t
      fin 2 (.propExt E topD trivD (.refl a t), .eq .o E topD)
  | ``letFun => do
      if k < 4 then return none
      if ← isProp args[0]! then
        let (dv, A) ← prf c args[2]!
        let (d, X) ← withLocalDecl `h .default args[0]! fun h => do
          let (db, B) ← prf (c.pushHyp h.fvarId! A) (mkApp args[3]! h).headBeta
          pure (Der.impE (.impI A db) dv, B)
        fin 4 (d, X)
      else
        let (d, X) ← prf c (mkApp args[3]! args[2]!).headBeta
        fin 4 (d, X)
  | _ => return none
where
  getLevel' (ty : Expr) : TM Level := do
    let l ← getLevel ty
    pure l

end

end Programme.H

end


/-! ## Tool part `Bridge` -/
section

/-! # Thread H: the bridge from the deep image back to the module's statement

After `#deep_translate X as N`, when every sentence of `N.T` comes from a module axiom (or is
`∃x.⊤`, from the module's `Nonempty e`) and `X` has no hypotheses read as facts, the command adds

* `N.bridge<k> : ∀ w, eval S N.ax<k> () w` for each axiom sentence, proved from the module axiom,
  where `S := fullStr R existsAt P` is the full structure on the module's own frame, actuality and
  positivity;
* `N.of_deep : type_of% @X`, the module's statement re-proved from `N.valid` (run 4's
  `valid_iff`, `full_closed_resp`) and the bridges.

Both are elaborated from source text and kernel-checked.  `N.of_deep` is the image check: had the
read-back misread a definition of the module, `N.φ` evaluated in the full structure would not give
back the module's statement, and `N.of_deep` would not build.  The proofs only unfold definitions
(`bridge_unfold`: the module's definitions and `N`'s sentences), normalise the full structure
(`bridge_simp`: `eval`, carriers `True`, primitive equality is identity, `↔` as two implications) and
then apply the module axiom (resp. `N.valid`'s instance) to hypotheses. -/

open Lean Meta Elab Tactic
open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.HOLX

namespace Programme.H

theorem eqT_full_iff {W D : Type} (R : W → W → Prop) (act : D → W → Prop) (P : Den W D th) :
    ∀ (t : FTy) {x y : Den W D t}, eqT (fullStr R act P) t x y ↔ x = y
  | .e, _, _ => Iff.rfl
  | .s, _, _ => Iff.rfl
  | .arr _ b, _, _ => ⟨fun h => funext fun z => (eqT_full_iff R act P b).1 (h z trivial),
      fun h z _ => (eqT_full_iff R act P b).2 (congrFun h z)⟩

theorem fullStr_A {W D : Type} (R : W → W → Prop) (act : D → W → Prop) (P : Den W D th) (t x) :
    (fullStr R act P).A t x = True := rfl
theorem fullStr_R {W D : Type} (R : W → W → Prop) (act : D → W → Prop) (P : Den W D th) :
    (fullStr R act P).R = R := rfl
theorem fullStr_act {W D : Type} (R : W → W → Prop) (act : D → W → Prop) (P : Den W D th) :
    (fullStr R act P).act = act := rfl
theorem fullStr_P {W D : Type} (R : W → W → Prop) (act : D → W → Prop) (P : Den W D th) :
    (fullStr R act P).P = P := rfl

/-- Is `n` a definition to unfold for the bridge: a non-type definition of an `OpenQuestions` or
`Notes` module, or a declaration in the namespace `base` (the translation's sentences). -/
def bridgeUnfoldable (base : Name) (n : Name) : MetaM Bool := do
  if primitiveConsts.contains n then return false
  let env ← getEnv
  let some (.defnInfo d) := env.find? n | return false
  let inScope ← if base.isPrefixOf n then pure true else
    match env.getModuleIdxFor? n with
    | some idx =>
        let m := env.header.moduleNames[idx.toNat]!
        pure (m.getRoot == `OpenQuestions || m.getRoot == `Notes)
    | none => pure false
  if !inScope then return false
  return !(← forallTelescope d.type fun _ b => pure (b.isSort && !b.isProp))

/-- `bridge_unfold N`: δ-expand (and β-reduce) the module's definitions and `N`'s sentences in the
goal and in every hypothesis. -/
elab "bridge_unfold " base:ident : tactic => do
  let base := base.getId
  let names := (← getEnv).constants.fold (init := (#[] : Array Name)) fun acc n _ => acc.push n
  let mut ok : NameSet := {}
  for n in names do
    if ← bridgeUnfoldable base n then ok := ok.insert n
  let expand (e : Expr) : MetaM Expr := do
    let e ← deltaExpand e ok.contains
    Core.betaReduce e
  liftMetaTactic fun g => do
    let g ← g.change (← expand (← g.getType))
    let mut g := g
    for d in (← g.getDecl).lctx do
      if d.isImplementationDetail then continue
      g ← g.changeLocalDecl d.fvarId (← expand d.type)
    pure [g]

macro "bridge_simp" : tactic => `(tactic| simp only [eval, Var.get, fullStr_A, fullStr_R, fullStr_act,
  fullStr_P, eqT_full_iff, true_implies, forall_const, true_and, and_true, ne_eq,
  iff_iff_implies_and_implies, Classical.not_forall, Classical.not_imp, Classical.not_not, exists_prop] at *)

end Programme.H

end


/-! ## Tool part `Struct` -/
section

/-! # Thread H: the structural image check (th's C8, run 6 `Programme.Run6.ThH5`)

`of_deep` reads `N.T` and `N.φ` in the full structure, so it fixes them only up to full-structure
equivalence (th's `full_check_blind`: a reifier conjoining v4's `phiSep` would pass).  The
structural check is stronger: `shR` is the unguarded reading of an `𝓛`-term (one Lean connective
per constructor), and the tool emits, for each axiom sentence `N.ax<k>` read off module axiom `X`
with `n` outer binders, `N.struct<k> : type_of% @X = shV R existsAt P n N.ax<k> ()`, and the same
`N.struct_φ` for the statement.  These are proved by `rfl` after δ-unfolding the module side and at
most two rewrites, each an identity of Lean propositions: `(a ↔ b) = ((a → b) ∧ (b → a))` (the
module's `Mequiv`) and `(∃ v, R w v ∧ B v) = ¬∀ v, R w v → ¬B v` (the module's `Mdia`, C5).
No guard erasure, no `eqT`.  An extra conjunct, a dropped guard or a swapped quantifier fails.
`N.of_struct : type_of% @X` then re-proves the module statement from `N.valid` through th's
`of_valid_full` and `shV_iff` only.  `shR`, `eval_full_eq`, `shV`, `shV_iff`, `of_valid_full`
are th's (copied, renamed into `Programme.H`). -/

open Lean Meta Elab Tactic
open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.HOLX

namespace Programme.H

variable {W D : Type}

/-- The structural, unguarded reading of an `𝓛`-term (th, C8). -/
def shR (R : W → W → Prop) (act : D → W → Prop) (P : Den W D th) :
    {Γ : List FTy} → {t : FTy} → Tm Γ t → Env W D Γ → Den W D t
  | _, _, .var i, ρ => i.get ρ
  | _, _, .app F x, ρ => shR R act P F ρ (shR R act P x ρ)
  | _, _, .lam b, ρ => fun z => shR R act P b (z, ρ)
  | _, _, .top, _ => fun _ => True
  | _, _, .bot, _ => fun _ => False
  | _, _, .neg a, ρ => fun w => ¬ shR R act P a ρ w
  | _, _, .and a b, ρ => fun w => shR R act P a ρ w ∧ shR R act P b ρ w
  | _, _, .or a b, ρ => fun w => shR R act P a ρ w ∨ shR R act P b ρ w
  | _, _, .imp a b, ρ => fun w => shR R act P a ρ w → shR R act P b ρ w
  | _, _, .box a, ρ => fun w => ∀ v, R w v → shR R act P a ρ v
  | _, _, .all _ b, ρ => fun w => ∀ x, shR R act P b (x, ρ) w
  | _, _, .ex _ b, ρ => fun w => ∃ x, shR R act P b (x, ρ) w
  | _, _, .allE b, ρ => fun w => ∀ y, act y w → shR R act P b (y, ρ) w
  | _, _, .exE b, ρ => fun w => ∃ y, act y w ∧ shR R act P b (y, ρ) w
  | _, _, .eq _ x y, ρ => fun _ => shR R act P x ρ = shR R act P y ρ
  | _, _, .pos, _ => P

theorem eqT_full_iff' (R : W → W → Prop) (act : D → W → Prop) (P : Den W D th)
    (t : FTy) (x y : Den W D t) : eqT (fullStr R act P) t x y ↔ x = y :=
  ⟨eqT_full R act P t, fun h => h ▸ eqT_refl _ t x⟩

/-- In the full structure, evaluation is the structural reading (th, C8). -/
theorem eval_full_eq (R : W → W → Prop) (act : D → W → Prop) (P : Den W D th) :
    ∀ {Γ : List FTy} {t : FTy} (φ : Tm Γ t) (ρ : Env W D Γ),
      eval (fullStr R act P) φ ρ = shR R act P φ ρ := by
  intro Γ t φ
  induction φ with
  | var i => intro ρ; rfl
  | app F x ihF ihx => intro ρ; simp only [eval, shR, ihF, ihx]
  | lam b ih => intro ρ; funext z; simp only [eval, shR, ih]
  | top => intro ρ; rfl
  | bot => intro ρ; rfl
  | neg a ih => intro ρ; funext w; simp only [eval, shR, ih]
  | and a b iha ihb => intro ρ; funext w; simp only [eval, shR, iha, ihb]
  | or a b iha ihb => intro ρ; funext w; simp only [eval, shR, iha, ihb]
  | imp a b iha ihb => intro ρ; funext w; simp only [eval, shR, iha, ihb]
  | box a ih => intro ρ; funext w; simp only [eval, shR, ih]; rfl
  | all a b ih =>
      intro ρ; funext w
      exact propext ⟨fun h x => (ih (x, ρ)) ▸ h x trivial, fun h x _ => (ih (x, ρ)) ▸ h x⟩
  | ex a b ih =>
      intro ρ; funext w
      exact propext ⟨fun ⟨x, _, hx⟩ => ⟨x, (ih (x, ρ)) ▸ hx⟩,
        fun ⟨x, hx⟩ => ⟨x, trivial, (ih (x, ρ)).symm ▸ hx⟩⟩
  | allE b ih => intro ρ; funext w; simp only [eval, shR, ih]; rfl
  | exE b ih => intro ρ; funext w; simp only [eval, shR, ih]; rfl
  | eq a x y ihx ihy =>
      intro ρ; funext w
      simp only [eval, shR, ← ihx, ← ihy]
      exact propext (eqT_full_iff' R act P a _ _)
  | pos => intro ρ; rfl

/-- Validity reading with `n` leading object quantifiers pulled out (th, C8). -/
def shV (R : W → W → Prop) (act : D → W → Prop) (P : Den W D th) :
    Nat → {Γ : List FTy} → Tm Γ .s → Env W D Γ → Prop
  | 0, _, φ, ρ => ∀ w, shR R act P φ ρ w
  | n + 1, _, .all _ b, ρ => ∀ x, shV R act P n b (x, ρ)
  | _ + 1, _, φ, ρ => ∀ w, shR R act P φ ρ w

theorem shV_iff (R : W → W → Prop) (act : D → W → Prop) (P : Den W D th) :
    ∀ (n : Nat) {Γ : List FTy} (φ : Tm Γ .s) (ρ : Env W D Γ),
      shV R act P n φ ρ ↔ ∀ w, shR R act P φ ρ w
  | 0, _, _, _ => Iff.rfl
  | n + 1, _, φ, ρ => by
      cases φ with
      | all a b =>
          simp only [shV, shR]
          exact ⟨fun h w x => (shV_iff R act P n b (x, ρ)).1 (h x) w,
                 fun h x => (shV_iff R act P n b (x, ρ)).2 fun w => h w x⟩
      | _ => simp only [shV]

/-- A `ValidV4` certificate read in the full structure, structurally (th, C8). -/
theorem of_valid_full {T : Tm [] .s → Prop} {φ : Tm [] .s} (h : ValidV4 T φ)
    (R : W → W → Prop) (act : D → W → Prop) (P : Den W D th) [Nonempty D]
    (hT : ∀ ψ, T ψ → ∀ w, shR R act P ψ () w) : ∀ w, shR R act P φ () w := by
  intro w
  have hS := (valid_iff T φ).1 h W D (fullStr R act P) inferInstance (fun _ => trivial)
    (full_closed_resp R act P).1 (full_closed_resp R act P).2.1
    (fun ψ hψ w => by rw [eval_full_eq]; exact hT ψ hψ w) w
  rwa [eval_full_eq] at hS

/-- The two rewrites allowed on the module side: identities of Lean propositions. -/
theorem iff_nf (a b : Prop) : (a ↔ b) = ((a → b) ∧ (b → a)) :=
  propext ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩
theorem dia_nf (r : W → W → Prop) (w : W) (b : W → Prop) :
    (∃ v, r w v ∧ b v) = ¬ ∀ v, r w v → ¬ b v :=
  propext ⟨fun ⟨v, hv, hb⟩ h => h v hv hb,
    fun h => Classical.byContradiction fun hn => h fun v hv hb => hn ⟨v, hv, hb⟩⟩

/-- `struct_unfold`: δ-expand (and β-reduce) the module's definitions (and `N`'s statement types) on the left-hand side of an
equation goal only. -/
elab "struct_unfold " base:ident : tactic => do
  let base := base.getId
  let names := (← getEnv).constants.fold (init := (#[] : Array Name)) fun acc n _ => acc.push n
  let mut ok : NameSet := {}
  for n in names do
    if ← bridgeUnfoldable base n then ok := ok.insert n
  let ok' := ok
  liftMetaTactic fun g => do
    let ty ← instantiateMVars (← g.getType)
    let some (_, l, r) := ty.eq? | throwError "struct_unfold: not an equation"
    let l ← Core.betaReduce (← deltaExpand l ok'.contains)
    let g ← g.change (← mkEq l r)
    pure [g]

end Programme.H

end


/-! ## Tool part `Frame` -/
section

/-! # Thread H: frame hypotheses (th's C7, run 6 `Programme.Run6.ThH6`)

A statement hypothesis such as `symm : ∀ x y, x 𝗿 y → y 𝗿 x` is not an `𝓛`-sentence, but its image
is a closed HOL formula built from `rel`, world variables, connectives and world quantifiers only
(`RelOnly`).  The tool keeps such hypotheses in the hypothesis list of the derivation (weakened into
the world context) and concludes `ValidV4Fs Fs T φ`: `φ` holds in every v4 `𝓛`-general model of
`T` whose frame satisfies every `F ∈ Fs`.  `RelW`, `RelOnly`, `relOnly_o`, `frameStr`,
`FrameHolds` and the proofs of `sound_v4_wt_frames` and `of_validFs_full` are th's (`ThH6`:
`sound_v4_wt_frame`, `of_validF_full`), generalised here from one formula to a list. -/

open Lean Meta Elab Tactic
open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.HOLX
  Programme.«20261022-1724-ontological».ThWhole

namespace Programme.H

variable {W D D' : Type}

inductive RelW : {Γ : List HTy} → HTerm Γ .w → Prop
  | var {Γ} (v : HVar Γ .w) : RelW (.var v)

/-- Frame formulas: only world variables, `rel`, equality at `w`, connectives, world quantifiers. -/
inductive RelOnly : {Γ : List HTy} → HTerm Γ .o → Prop
  | rel {Γ} {i j : HTerm Γ .w} : RelW i → RelW j → RelOnly (.rel i j)
  | bot {Γ} : RelOnly (Γ := Γ) .bot
  | imp {Γ} {p q : HTerm Γ .o} : RelOnly p → RelOnly q → RelOnly (.imp p q)
  | and {Γ} {p q : HTerm Γ .o} : RelOnly p → RelOnly q → RelOnly (.and p q)
  | or {Γ} {p q : HTerm Γ .o} : RelOnly p → RelOnly q → RelOnly (.or p q)
  | all {Γ} {p : HTerm (.w :: Γ) .o} : RelOnly p → RelOnly (.all .w p)
  | ex {Γ} {p : HTerm (.w :: Γ) .o} : RelOnly p → RelOnly (.ex .w p)
  | eq {Γ} {s u : HTerm Γ .w} : RelW s → RelW u → RelOnly (.eq .w s u)

theorem relOnly_w {Γ} (S : Str W D) (S' : Str W D')
    (ρ : HEnv W D Γ) (ρ' : HEnv W D' Γ) (hρ : ∀ v : HVar Γ .w, ρ v = ρ' v)
    {i : HTerm Γ .w} (h : RelW i) : heval S i ρ = heval S' i ρ' := by
  cases h with
  | var v => exact hρ v

theorem cons_w {Γ} {ρ : HEnv W D Γ} {ρ' : HEnv W D' Γ} (hρ : ∀ v : HVar Γ .w, ρ v = ρ' v) (u : W) :
    ∀ v : HVar (.w :: Γ) .w, cons (a := .w) u ρ v = cons (a := .w) u ρ' v
  | .zero => rfl
  | .succ v => hρ v

/-- Frame invariance (th): a frame formula has the same truth value in two structures on one frame. -/
theorem relOnly_o (S : Str W D) (S' : Str W D') (hS : S.R = S'.R) {Γ} {φ : HTerm Γ .o}
    (h : RelOnly φ) : ∀ (ρ : HEnv W D Γ) (ρ' : HEnv W D' Γ), (∀ v : HVar Γ .w, ρ v = ρ' v) →
      (heval S φ ρ ↔ heval S' φ ρ') := by
  induction h with
  | rel hi hj =>
      intro ρ ρ' hρ
      show S.R _ _ ↔ S'.R _ _
      rw [relOnly_w S S' ρ ρ' hρ hi, relOnly_w S S' ρ ρ' hρ hj, hS]
  | bot => intro _ _ _; exact Iff.rfl
  | imp _ _ ihp ihq => intro ρ ρ' hρ; exact imp_congr (ihp ρ ρ' hρ) (ihq ρ ρ' hρ)
  | and _ _ ihp ihq => intro ρ ρ' hρ; exact and_congr (ihp ρ ρ' hρ) (ihq ρ ρ' hρ)
  | or _ _ ihp ihq => intro ρ ρ' hρ; exact or_congr (ihp ρ ρ' hρ) (ihq ρ ρ' hρ)
  | all _ ih =>
      intro ρ ρ' hρ
      show (∀ u, True → _) ↔ (∀ u, True → _)
      exact forall_congr' fun u => imp_congr Iff.rfl (ih _ _ (cons_w hρ u))
  | ex _ ih =>
      intro ρ ρ' hρ
      show (∃ u, True ∧ _) ↔ (∃ u, True ∧ _)
      exact exists_congr fun u => and_congr Iff.rfl (ih _ _ (cons_w hρ u))
  | eq hs hu =>
      intro ρ ρ' hρ
      show _ = _ ↔ _ = _
      rw [relOnly_w S S' ρ ρ' hρ hs, relOnly_w S S' ρ ρ' hρ hu]

/-- The unit structure over a frame. -/
def frameStr (R : W → W → Prop) : Str W Unit := ⟨R, fun _ _ => True, fun _ _ => True, fun _ _ => True⟩

/-- The frame semantics of a closed frame formula. -/
def FrameHolds (R : W → W → Prop) (F : HTerm [] .o) : Prop :=
  heval (frameStr R) F emptyEnv

def AllRel : List (HTerm [] .o) → Prop
  | [] => True
  | F :: Fs => RelOnly F ∧ AllRel Fs

def FramesHold (R : W → W → Prop) : List (HTerm [] .o) → Prop
  | [] => True
  | F :: Fs => FrameHolds R F ∧ FramesHold R Fs

theorem AllRel.mem : ∀ {Fs : List (HTerm [] .o)}, AllRel Fs → ∀ F ∈ Fs, RelOnly F
  | _ :: _, ⟨h, _⟩, _, .head _ => h
  | _ :: _, ⟨_, hs⟩, F, .tail _ m => AllRel.mem hs F m

theorem FramesHold.mem {R : W → W → Prop} : ∀ {Fs : List (HTerm [] .o)}, FramesHold R Fs →
    ∀ F ∈ Fs, FrameHolds R F
  | _ :: _, ⟨h, _⟩, _, .head _ => h
  | _ :: _, ⟨_, hs⟩, F, .tail _ m => FramesHold.mem hs F m

/-- `ValidV4` over the v4 `𝓛`-general models whose frame satisfies every formula of `Fs`. -/
def ValidV4Fs (Fs : List (HTerm [] .o)) (T : Tm [] .s → Prop) (φ : Tm [] .s) : Prop :=
  ∀ (W : Type) (M : VM W) (L : LGen M), Nonempty (M.C .e) → FramesHold M.R Fs →
    (∀ ψ, T ψ → ∀ w, M.pr (L.ev ψ ()) w) → ∀ w, M.pr (L.ev φ ()) w

/-- **Soundness with frame hypotheses** (th's `sound_v4_wt_frame`, for a list). -/
theorem sound_v4_wt_frames {Fs : List (HTerm [] .o)} (hF : AllRel Fs) {T : Tm [] .s → Prop}
    {φ : Tm [] .s} (d : DW T [.w] (Fs.map (wk (b := .w))) (.holds (emb nilR φ) var0)) :
    ValidV4Fs Fs T φ := by
  intro W M L hne hFr hT w
  have hS := toStr_entities M hne
  have := sound_wt (toStr M hne) hS (toStr_closed M hne L) (toStr_resp M hne)
    (fun ψ hψ v => (toStr_truth M hne L ψ v).2 (hT ψ hψ v)) d (cons (a := .w) w emptyEnv)
    (admEnv_cons (a := .w) _ (fun v => by cases v) trivial) (fun h m => by
      obtain ⟨F, hFm, rfl⟩ := List.mem_map.1 m
      rw [heval_wk]
      exact (relOnly_o (frameStr M.R) (toStr M hne) rfl (hF.mem F hFm) emptyEnv emptyEnv
        (fun v => by cases v)).1 (hFr.mem F hFm))
  simp only [heval, heval_emb _ hS] at this
  exact (toStr_truth M hne L φ w).1 this

/-- Cut for `ValidV4Fs` (the lemmas are valid on all frames). -/
theorem Good.validFs {A : Tm [] .s → Prop} {L : List (Tm [] .s)} {χ : Tm [] .s} {Fs} (g : Good A L)
    (h : ValidV4Fs Fs (fun φ => φ ∈ L) χ) : ValidV4Fs Fs A χ := by
  intro W M Lg hne hF hA
  apply h W M Lg hne hF
  clear h
  induction g with
  | nil => intro ψ hψ; cases hψ
  | axm hs _ ih =>
      intro ψ hψ
      rcases List.mem_cons.mp hψ with rfl | hψ
      · exact hA _ hs
      · exact ih ψ hψ
  | lem hv _ ih =>
      intro ψ hψ
      rcases List.mem_cons.mp hψ with rfl | hψ
      · exact hv W M Lg hne ih
      · exact ih ψ hψ

/-- **Image bridge with frame formulas** (th's `of_validF_full`, for a list). -/
theorem of_validFs_full {Fs : List (HTerm [] .o)} {T : Tm [] .s → Prop} {φ : Tm [] .s}
    (h : ValidV4Fs Fs T φ)
    (R : W → W → Prop) (act : D → W → Prop) (P : Den W D th) [Nonempty D] (hF : FramesHold R Fs)
    (hT : ∀ ψ, T ψ → ∀ w, shR R act P ψ () w) : ∀ w, shR R act P φ () w := by
  intro w
  have hC : Closed (fullStr R act P) := (full_closed_resp R act P).1
  have hR : Resp (fullStr R act P) := (full_closed_resp R act P).2.1
  have hE : ∀ x, (fullStr R act P).A .e x := fun _ => trivial
  have hne : Nonempty ((ofStr (fullStr R act P) hC hR).C .e) :=
    let ⟨d⟩ := (inferInstance : Nonempty D); ⟨Quotient.mk (setoidT _ .e) ⟨d, hE d⟩⟩
  have := h W _ (ofStr_lgen _ hC hR hE) hne hF
    (fun ψ hψ v => (ofStr_truth _ hC hR hE ψ v).2 (by rw [eval_full_eq]; exact hT ψ hψ v)) w
  have := (ofStr_truth _ hC hR hE φ w).1 this
  rwa [eval_full_eq] at this

/-- Prove `RelOnly F` / `RelW i` for a concrete term by its constructors. -/
partial def solveRelOnly (g : MVarId) : MetaM Unit := do
  let ctors := [``RelOnly.rel, ``RelOnly.bot, ``RelOnly.imp, ``RelOnly.and, ``RelOnly.or,
    ``RelOnly.all, ``RelOnly.ex, ``RelOnly.eq, ``RelW.var]
  for c in ctors do
    let s ← saveState
    try
      let gs ← g.apply (← mkConstWithFreshMVarLevels c)
      for g' in gs do
        unless ← g'.isAssigned do solveRelOnly g'
      return
    catch _ => s.restore
  throwError m!"not a frame formula: {← g.getType}"

/-- `frame_hold h`: prove `FrameHolds R F` from the module's hypothesis `h`: introduce the world
binders and hypotheses of `F` (by `whnf`), then `apply h` and close its premises by assumption. -/
elab "frame_hold " h:term : tactic => do
  for _ in [0:64] do
    let g ← getMainGoal
    let t ← whnf (← g.getType)
    unless t.isForall do break
    let g ← g.change t
    let (_, g) ← g.intro1
    replaceMainGoal [g]
  evalTactic (← `(tactic| first | exact $h | (apply $h <;> assumption)))

end Programme.H

end


/-! ## Tool part `Cmd` -/
section

/-! # Thread H: the command `#deep_translate thm as Name` -/

open Lean Meta Elab Command Term
open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.HOLX
  Programme.«20261022-1724-ontological».ThWhole

namespace Programme.H

partial def Der.size : Der → Nat
  | .hyp _ | .ax .. | .refl .. | .betaL .. => 1
  | .impI _ d | .byContra _ d | .andL d | .andR d | .orL _ d | .orR _ d | .allI _ d | .allE _ d
  | .exI _ _ _ d | .symm d | .funExt d | .funApp d | .wExt d | .wApp d | .betaWI _ _ d
  | .betaWE d => 1 + d.size
  | .impE d1 d2 | .andI d1 d2 | .trans d1 d2 | .leib _ _ _ _ d1 d2 | .propExt _ _ d1 d2
  | .exE d1 d2 _ => 1 + d1.size + d2.size
  | .orE d d1 d2 => 1 + d.size + d1.size + d2.size

/-- One goal of a statement: hypotheses read as facts, `𝓛`/world binders, the proof. -/
structure Goal where
  suffix : String
  ty : Expr
  proof : Expr

/-- Split `↔`/`∧` statements into goals. -/
partial def splitGoals (suffix : String) (ty prf : Expr) : MetaM (Array Goal) := do
  let ty' ← whnfR ty
  match ty'.getAppFn, ty'.getAppArgs with
  | .const ``Iff _, #[a, b] =>
      -- a proof `Iff.intro p q` is split into `p` and `q` (each direction from its own axioms)
      let (p1, p2) := if prf.isAppOfArity ``Iff.intro 4 then (prf.appFn!.appArg!, prf.appArg!)
        else (mkApp3 (mkConst ``Iff.mp) a b prf, mkApp3 (mkConst ``Iff.mpr) a b prf)
      let g1 ← splitGoals (suffix ++ "mp") (← mkArrow a b) p1
      let g2 ← splitGoals (suffix ++ "mpr") (← mkArrow b a) p2
      pure (g1 ++ g2)
  | .const ``And _, #[a, b] =>
      let (p1, p2) := if prf.isAppOfArity ``And.intro 4 then (prf.appFn!.appArg!, prf.appArg!)
        else (mkApp3 (mkConst ``And.left) a b prf, mkApp3 (mkConst ``And.right) a b prf)
      let g1 ← splitGoals (suffix ++ "left") a p1
      let g2 ← splitGoals (suffix ++ "right") b p2
      pure (g1 ++ g2)
  | _, _ => pure #[{ suffix, ty, proof := prf }]

structure Result where
  sentences : Array LT
  names : Array String
  phi : LT
  der : Der
  target : DT
  lemmas : Array (Nat × Name × Der × DT)
  facts : Array String := #[]
  factTys : Std.HashMap Nat (Expr × Expr) := {}
  frames : List (Nat × DT) := []

/-- Translate one goal: the sentences of `T` (axioms and lemmas), `φ`, the derivation. -/
partial def translateGoal (g : Goal) (withNE : Bool) : TM Result := do
  -- hypotheses: leading binders whose type is a `Prop` (facts / schemas)
  let rec peelFacts (ty prf : Expr) (facts : Array FactVar) (k : Array FactVar → Expr → TM Result) :
      TM Result := do
    let ty' ← whnfR ty
    match ty' with
    | .forallE n dom body bi =>
        if (← isProp dom) then
          withLocalDecl n bi dom fun h => do
            peelFacts (body.instantiate1 h) (mkApp prf h)
              (facts.push { fvar := h.fvarId!, name := n.toString }) k
        else k facts ty
    | _ => k facts ty
  peelFacts g.ty g.proof #[] fun facts goalTy => do
    let pf := mkAppN g.proof (facts.map (fun (f : FactVar) => mkFVar f.fvar))
    let (φ, d, target) ← goalCore facts goalTy pf withNE
    let st ← get
    pure { sentences := st.sentences, names := st.sentenceNames, phi := φ, der := d, target,
           lemmas := st.lemmas, facts := facts.map (·.name), factTys := st.factTys,
           frames := st.frames }

def logF (s : String) : IO Unit := do
  if let some f ← IO.getEnv "DEEP_LOG" then
    let h ← IO.FS.Handle.mk f .append
    h.putStrLn s
    h.flush

def addDef (n : Name) (ty v : Expr) : CoreM Unit := do
  let dv : DefinitionVal := { name := n, levelParams := [], type := ty, value := v,
                              hints := ReducibilityHints.abbrev, safety := DefinitionSafety.safe }
  addDecl (Declaration.defnDecl dv)

def addThm (n : Name) (ty v : Expr) : CoreM Unit := do
  let tv : TheoremVal := { name := n, levelParams := [], type := ty, value := v }
  addDecl (Declaration.thmDecl tv)

/-- The tactic script for `of_deep`: split `↔`/`∧` as `splitGoals` does, leaves from `leaves`. -/
partial def bridgeScript (leaves : Std.HashMap String String) (suffix : String) (ty : Expr) :
    MetaM (Option String) := do
  let ty' ← whnfR ty
  let indent (s : String) : String := "\n".intercalate ((s.splitOn "\n").map ("  " ++ ·))
  let two (a b : String) (ta tb : Expr) : MetaM (Option String) := do
    let some s1 ← bridgeScript leaves (suffix ++ a) ta | return none
    let some s2 ← bridgeScript leaves (suffix ++ b) tb | return none
    return some s!"constructor\n· {(indent s1).drop 2}\n· {(indent s2).drop 2}"
  match ty'.getAppFn, ty'.getAppArgs with
  | .const ``Iff _, #[a, b] => two "mp" "mpr" (← mkArrow a b) (← mkArrow b a)
  | .const ``And _, #[a, b] => two "left" "right" a b
  | _, _ => return leaves[suffix]?

/-! Term-mode proofs, inside the fragment, of core simp lemmas whose core proofs leave it
(`decide`, `funext` at `Prop → Prop`); the tool uses them in place of the core lemma. -/
namespace Rw
theorem not_true_eq_false : (¬True) = False := propext ⟨fun h => h trivial, False.elim⟩
theorem not_false_eq_true : (¬False) = True := propext ⟨fun _ => trivial, fun _ h => h⟩
example : type_of% @not_true_eq_false = type_of% @_root_.not_true_eq_false := rfl
example : type_of% @not_false_eq_true = type_of% @_root_.not_false_eq_true := rfl
end Rw

def builtinRepl : List (Name × Name) :=
  [(``_root_.not_true_eq_false, ``Rw.not_true_eq_false),
   (``_root_.not_false_eq_true, ``Rw.not_false_eq_true)]

/-- Give every node of a generated command the position of the `#deep_translate` command, so
that a failing bridge is reported there. -/
partial def relocate (info : SourceInfo) : Syntax → Syntax
  | .node _ k args => .node info k (args.map (relocate info))
  | .atom _ v => .atom info v
  | .ident _ raw v pre => .ident info raw v pre
  | .missing => .missing

syntax (name := deepTranslate) "#deep_translate " ident " as " ident (" replacing " ident " by " ident)* : command

@[command_elab deepTranslate] def elabDeepTranslate : CommandElab := fun stx => do
  let src := stx[1]
  let dst := stx[3].getId
  let replStx : Array Syntax := stx[4].getArgs
  let bridges ← liftTermElabM do
    let mut bridges : Array String := #[]
    let mut repl : List (Name × Name) := builtinRepl
    for r in replStx do
      let a ← realizeGlobalConstNoOverloadWithInfo r[1]
      let b ← realizeGlobalConstNoOverloadWithInfo r[3]
      unless ← isDefEq (← getConstInfo a).type (← getConstInfo b).type do
        throwError m!"replacement {b} does not have the statement of {a}"
      repl := (a, b) :: repl
    let srcName ← realizeGlobalConstNoOverloadWithInfo src
    let info ← getConstInfo srcName
    let val ← match info with
      | .thmInfo t => pure t.value
      | .defnInfo d => pure d.value
      | _ => throwError "{srcName} has no proof term"
    let goals ← splitGoals "" info.type val
    let mut leaves : Std.HashMap String String := {}
    for g in goals do
      let base := if g.suffix == "" then dst else dst ++ Name.mkSimple g.suffix
      let r ← try (translateGoal g false).run' { replace := repl } catch ex =>
        if (← ex.toMessageData.toString).startsWith "[deep_translate] needs-nonempty" then
          (translateGoal g true).run' { replace := repl }
        else throw ex
      logF (s!"[deep] {← IO.monoMsNow} translated: {r.der.size} rules, {r.sentences.size} sentences")
      -- declarations: the sentences
      let sentTy := mkApp2 (mkConst ``Tm) (mkLCtx []) (mkFTy .s)
      let sentListTy := mkApp (mkConst ``List [Level.zero]) sentTy
      let mut sentConsts : Array Expr := #[]
      for k in [0:r.sentences.size] do
        let nm := base ++ Name.mkSimple s!"ax{k}"
        let some s := r.sentences[k]? | unreachable!
        let e ← match mkTm [] s with | .ok e => pure e | .error m => throwError m
        addDef nm sentTy e
        sentConsts := sentConsts.push (mkConst nm)
      let phiE ← match mkTm [] r.phi with | .ok e => pure e | .error m => throwError m
      addDef (base ++ `φ) sentTy phiE
      let memPred (lst : Expr) : MetaM Expr := withLocalDecl `φ .default sentTy fun x => do
        mkLambdaFVars #[x] (mkApp5 (mkConst ``Membership.mem [Level.zero, Level.zero]) sentTy
          sentListTy (mkApp (mkConst ``List.instMembership [Level.zero]) sentTy) lst x)
      -- the prefix theories: `Tpre j` = sentences `j-1, …, 0` (newest first)
      let preList (j : Nat) : Expr := mkListE sentTy (sentConsts.extract 0 j).toList.reverse
      let dwVal ← instantiateValueLevelParams (← getConstInfo ``DW) []
      let wCtx := mkCtx [.w]
      let dwTy (TE : Expr) (sE : Expr) : Expr := mkAppN (mkConst ``DW) #[TE, wCtx,
        mkListE (hTermTy wCtx) [],
        mkApp3 (mkConst ``HTerm.holds) wCtx
          (mkApp5 (mkConst ``emb) (mkLCtx []) wCtx (mkFTy .s) (mkApp (mkConst ``nilR) wCtx) sE)
          (mkApp2 (mkConst ``var0) (mkHTy .w) (mkListE (mkConst ``HTy) []))]
      let mut cache : EmitCache := {}
      let emitAt (TName : Name) (j : Nat) (d : Der) (tgt : DT) (cache : EmitCache) (hs : List DT := []) :
          TermElabM (Expr × EmitCache) := do
        let dwApp := (mkApp dwVal (mkConst TName)).headBeta
        let env : EmitEnv := { T := mkConst TName, sentences := r.sentences.extract 0 j,
                               sentenceExprs := sentConsts.extract 0 j,
                               ok := dwApp.getAppArgs[1]!, okL := dwApp.getAppArgs[2]! }
        let ((pf, concl), cache') ← ((emit [.w] hs d).run env).run cache
        unless concl == tgt do throwError m!"conclusion mismatch: {concl} vs {tgt}"
        pure (pf, cache')
      -- lemmas, each from the sentences before it
      let mut lemValid : Std.HashMap Nat Expr := {}
      for (j, ln, d, tgt) in r.lemmas do
        let TName := base ++ Name.mkSimple s!"T{j}"
        addDef TName (← mkArrow sentTy (mkSort Level.zero)) (← memPred (preList j))
        let (pf, cache') ← emitAt TName j d tgt cache
        cache := cache'
        let lname := base ++ Name.mkSimple s!"lem{j}"
        addThm lname (dwTy (mkConst TName) sentConsts[j]!) pf
        let vname := base ++ Name.mkSimple s!"lem{j}_valid"
        addThm vname (mkApp2 (mkConst ``ValidV4) (mkConst TName) sentConsts[j]!)
          (mkApp3 (mkConst ``sound_v4_wt) (mkConst TName) sentConsts[j]! (mkConst lname))
        lemValid := lemValid.insert j (mkConst vname)
        logF s!"[deep] {← IO.monoMsNow} lemma {j} ({ln}) emitted"
      -- the main derivation, from all sentences
      let n := r.sentences.size
      let TfullName := base ++ `Tfull
      addDef TfullName (← mkArrow sentTy (mkSort Level.zero)) (← memPred (preList n))
      let frameHs := r.frames.map (·.2)
      let (pf, _) ← emitAt TfullName n r.der r.target cache frameHs
      let hasFrames := !r.frames.isEmpty
      if hasFrames then
        -- C7: the frame formulas, closed, and `RelOnly` for each
        let hT0 := mkApp2 (mkConst ``HTerm) (mkCtx []) (mkHTy .o)
        let envF : EmitEnv := { T := mkConst TfullName, sentences := #[], sentenceExprs := #[],
                                ok := .bvar 0, okL := .bvar 0 }
        let (FsL, _) ← ((frameHs.mapM fun F => tmC [] F).run envF).run {}
        let FsE := mkListE hT0 FsL
        addDef (base ++ `Fs) (mkApp (mkConst ``List [Level.zero]) hT0) FsE
        let mut okE : Expr := mkConst ``True.intro
        let mut okTy : Expr := mkConst ``True
        for F in FsL.reverse do
          let goalTy := mkApp2 (mkConst ``RelOnly) (mkCtx []) F
          let g ← mkFreshExprMVar goalTy
          solveRelOnly g.mvarId!
          let p ← instantiateMVars g
          okE := mkApp4 (mkConst ``And.intro) goalTy okTy p okE
          okTy := mkApp2 (mkConst ``And) goalTy okTy
        addThm (base ++ `Fs_ok) (mkApp (mkConst ``AllRel) (mkConst (base ++ `Fs))) okE
        let wkFn ← withLocalDecl `t .default hT0 fun t => do
          mkLambdaFVars #[t] (mkApp4 (mkConst ``wk) (mkCtx []) (mkHTy .o) (mkHTy .w) t)
        let hsE := mkApp4 (mkConst ``List.map [Level.zero, Level.zero]) hT0
          (mkApp2 (mkConst ``HTerm) (mkCtx [.w]) (mkHTy .o)) wkFn (mkConst (base ++ `Fs))
        let ty := mkAppN (mkConst ``DW) #[mkConst TfullName, wCtx, hsE,
          mkApp3 (mkConst ``HTerm.holds) wCtx
            (mkApp5 (mkConst ``emb) (mkLCtx []) wCtx (mkFTy .s) (mkApp (mkConst ``nilR) wCtx) (mkConst (base ++ `φ)))
            (mkApp2 (mkConst ``var0) (mkHTy .w) (mkListE (mkConst ``HTy) []))]
        addThm (base ++ `deep) ty pf
      else
        addThm (base ++ `deep) (dwTy (mkConst TfullName) (mkConst (base ++ `φ))) pf
      logF (s!"[deep] {← IO.monoMsNow} main kernel-checked")
      -- `T`: the axioms (non-lemma sentences); the lemmas are cut by `Good.valid`
      let axIdx := (List.range n).filter fun j => !lemValid.contains j
      let axList := mkListE sentTy (axIdx.map fun j => sentConsts[j]!)
      let TName := base ++ `T
      addDef TName (← mkArrow sentTy (mkSort Level.zero)) (← memPred axList)
      let mut good : Expr := mkApp (mkConst ``Good.nil) (mkConst TName)
      for j in [0:n] do
        let L := preList j
        let sE := sentConsts[j]!
        match lemValid[j]? with
        | some v => good := mkAppN (mkConst ``Good.lem) #[mkConst TName, sE, L, v, good]
        | none =>
            let some pos := axIdx.idxOf? j | unreachable!
            let mp ← liftM (m := TermElabM) <| match memProof sentTy (axIdx.map fun j => sentConsts[j]!) pos with
              | .ok e => pure e | .error m => throwError m
            good := mkAppN (mkConst ``Good.axm) #[mkConst TName, sE, L, mp, good]
      addThm (base ++ `good) (mkApp2 (mkConst ``Good) (mkConst TName) (preList n)) good
      if hasFrames then
        let FsC : Expr := Lean.mkConst (base ++ `Fs)
        addThm (base ++ `validF) (mkApp3 (mkConst ``ValidV4Fs) FsC (mkConst TName) (mkConst (base ++ `φ)))
          (mkAppN (mkConst ``Good.validFs) #[mkConst TName, preList n, mkConst (base ++ `φ), FsC,
            mkConst (base ++ `good),
            mkAppN (mkConst ``sound_v4_wt_frames) #[FsC, mkConst (base ++ `Fs_ok), mkConst TfullName,
              mkConst (base ++ `φ), mkConst (base ++ `deep)]])
      else
        addThm (base ++ `valid) (mkApp2 (mkConst ``ValidV4) (mkConst TName) (mkConst (base ++ `φ)))
          (mkAppN (mkConst ``Good.valid) #[mkConst TName, preList n, mkConst (base ++ `φ),
            mkConst (base ++ `good),
            mkApp3 (mkConst ``sound_v4_wt) (mkConst TfullName) (mkConst (base ++ `φ)) (mkConst (base ++ `deep))])
      let total := r.lemmas.foldl (fun acc (_, _, d, _) => acc + d.size) r.der.size
      let mut msg := m!"{base}: φ = {r.phi.toStr}\n  derivation: {r.der.size} rule applications, {r.lemmas.size} lemmas, {total} in all"
      for k in [0:r.sentences.size] do
        msg := msg ++ m!"\n  [{k}] ({r.names[k]!}) = {r.sentences[k]!.toStr}"
      logInfo msg
      -- the bridge back to the module's statement (see `Bridge`): every axiom sentence comes
      -- from a module axiom, from `NonEmpty`, or from a hypothesis of the statement (a fact)
      let env ← getEnv
      let factIdx (nm : String) : Option Nat :=
        let nm' := if nm.endsWith " (instance)" then String.ofList (nm.toList.take (nm.length - 11)) else nm
        r.facts.findIdx? (· == nm')
      let axSrc : List (Nat × Option Name × Option Nat) ← axIdx.mapM fun j => do
        let nm := r.names[j]!
        if nm == "NonEmpty" then return (j, none, none)
        if let some k := factIdx nm then return (j, none, some k)
        let c := nm.toName
        match env.find? c with
        | some (.axiomInfo _) => return (j, some c, none)
        | _ => return (j, some Name.anonymous, none)
      if axSrc.all (fun (_, c, _) => c != some Name.anonymous) then
        let S := "(fullStr _root_.R _root_.existsAt _root_.P)"
        let opn := "open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.HOLX Programme.H in\n"
        let mut cases := ""
        for (j, c, f) in axSrc do
          let ax := s!"{base ++ Name.mkSimple s!"ax{j}"}"
          let stmt := s!"∀ w, eval {S} {ax} () w"
          match c, f with
          | some c, _ =>
              let body := s!"  suffices H : type_of% @_root_.{c} → {stmt} from H @_root_.{c}\n  bridge_unfold {base}\n  try bridge_simp\n  first | done | (intro h; intros; apply h <;> assumption)"
              bridges := bridges.push (opn ++ s!"theorem {base ++ Name.mkSimple s!"bridge{j}"} : {stmt} := by\n{body}")
              cases := cases ++ s!"\n      · exact {base ++ Name.mkSimple s!"bridge{j}"}"
          | none, some k =>
              cases := cases ++ s!"\n      · bridge_unfold {base}\n        try bridge_simp\n        first | done | (intros; apply hf{k} <;> assumption)"
          | none, none =>
              let body := s!"  bridge_unfold {base}\n  try bridge_simp\n  first | done | exact ⟨Classical.ofNonempty, trivial⟩ | exact fun _ => ⟨Classical.ofNonempty, trivial⟩"
              bridges := bridges.push (opn ++ s!"theorem {base ++ Name.mkSimple s!"bridge{j}"} : {stmt} := by\n{body}")
              cases := cases ++ s!"\n      · exact {base ++ Name.mkSimple s!"bridge{j}"}"
        -- the structural image check (th's C8): `type_of% @X = shV .. n N.ax<k> ()` by `rfl`
        let shVs := "shV _root_.R _root_.existsAt _root_.P"
        let structTac := s!"  struct_unfold {base}\n  first\n  | rfl\n  | (simp only [Programme.H.iff_nf, Programme.H.dia_nf _root_.R]; rfl)"
        let nBinders (e : Expr) : Nat := Id.run do
          let mut e := e
          let mut n := 0
          while e.isForall do
            n := n + 1
            e := e.bindingBody!
          return n
        let mut scases := ""
        let mut structOk := g.suffix == ""
        for (j, c, f) in axSrc do
          let ax := s!"{base ++ Name.mkSimple s!"ax{j}"}"
          let sn := base ++ Name.mkSimple s!"struct{j}"
          match c, f with
          | some c, _ =>
              let nb := nBinders (← getConstInfo c).type
              bridges := bridges.push (opn ++ s!"theorem {sn} : type_of% @_root_.{c} = {shVs} {nb} {ax} () := by\n{structTac}")
              scases := scases ++ s!"\n  · exact (shV_iff _root_.R _root_.existsAt _root_.P {nb} _ _).1 (cast {sn} @_root_.{c})"
          | none, none =>
              bridges := bridges.push (opn ++ s!"theorem {sn} : (∀ _ : _root_.i, ∃ _ : _root_.e, True) = {shVs} 0 {ax} () := rfl")
              scases := scases ++ s!"\n  · exact (shV_iff _root_.R _root_.existsAt _root_.P 0 _ _).1 (cast {sn} (fun _ => ⟨Classical.ofNonempty, trivial⟩))"
          | none, some k =>
              match r.factTys[j]? with
              | some (ty, fn) =>
                  let tn := base ++ Name.mkSimple s!"factTy{j}"
                  addDef tn (mkSort Level.zero) ty
                  let fnTy ← inferType fn
                  addDef (base ++ Name.mkSimple s!"factInst{j}") (.forallE `h fnTy.bindingDomain! (mkConst tn) .default) fn
                  let nb := nBinders ty
                  bridges := bridges.push (opn ++ s!"theorem {sn} : {tn} = {shVs} {nb} {ax} () := by\n{structTac}")
                  scases := scases ++ s!"\n  · exact (shV_iff _root_.R _root_.existsAt _root_.P {nb} _ _).1 (cast {sn} ({base ++ Name.mkSimple s!"factInst{j}"} hf{k}))"
              | none => structOk := false
        -- the statement after its hypotheses (non-dependent arrows only)
        let mut stmtBody := info.type
        for _ in [0:r.facts.size] do
          if stmtBody.isForall then stmtBody := stmtBody.bindingBody! else structOk := false
        if stmtBody.hasLooseBVars then structOk := false
        if structOk then
          let nb := nBinders stmtBody
          let intros := if r.facts.size == 0 then "" else
            "intro " ++ " ".intercalate ((List.range r.facts.size).map fun k => s!"hf{k}") ++ "\n  "
          let sφ := base ++ `struct_φ
          let lhs ← if r.facts.size == 0 then pure s!"type_of% @_root_.{srcName}" else do
            addDef (base ++ `goalTy) (mkSort Level.zero) stmtBody
            pure s!"{base ++ `goalTy}"
          bridges := bridges.push (opn ++ s!"theorem {sφ} : {lhs} = {shVs} {nb} {base ++ `φ} () := by\n{structTac}")
          let memS := if axSrc.length == 0 then "  cases hψ"
            else s!"  simp only [List.mem_cons, List.not_mem_nil, or_false] at hψ\n  rcases hψ with {" | ".intercalate (axSrc.map fun _ => "rfl")}{scases}"
          let certify := if r.frames.isEmpty then s!"of_valid_full {base ++ `valid} _root_.R _root_.existsAt _root_.P ?_"
            else
              let hold := r.frames.foldr (fun (k, _) acc => s!"(And.intro (by frame_hold hf{k}) {acc})") "trivial"
              s!"of_validFs_full {base ++ `validF} _root_.R _root_.existsAt _root_.P {hold} ?_"
          bridges := bridges.push (opn ++ s!"/-- The module's statement from the deep certificate through the structural checks only (no `bridge_simp`). -/\ntheorem {dst ++ `of_struct} : type_of% @_root_.{srcName} := by\n  {intros}refine cast {sφ}.symm ((shV_iff _root_.R _root_.existsAt _root_.P {nb} _ _).2 ({certify}))\n  intro ψ hψ\n  delta {base ++ `T} at hψ\n{memS}")
        let pat := " | ".intercalate (axSrc.map fun _ => "rfl")
        let memT := if axSrc.length == 0 then "      cases hψ"
          else s!"      simp only [List.mem_cons, List.not_mem_nil, or_false] at hψ\n      rcases hψ with {pat}{cases}"
        let intros := if r.facts.size == 0 then "" else
          "intro " ++ " ".intercalate ((List.range r.facts.size).map fun k => s!"hf{k}") ++ "\n"
        if r.frames.isEmpty then
         leaves := leaves.insert g.suffix (intros ++ s!"have hfc := full_closed_resp _root_.R _root_.existsAt _root_.P
have hd := (valid_iff {base ++ `T} {base ++ `φ}).1 {base ++ `valid} _root_.i _root_.e {S} inferInstance hfc.2.2 hfc.1 hfc.2.1
  (fun ψ hψ => by
      delta {base ++ `T} at hψ
{memT})
clear hfc
revert hd
bridge_unfold {base}
try bridge_simp
first | done | trivial | (intro hd; intros; first | trivial | (apply hd <;> assumption) | exact hd _)")
      else
        logInfo m!"{base}: no bridge (a sentence not from a module axiom or hypothesis)"
    -- `dst.of_deep : type_of% @X`, split as the goals were
    if let some sc ← bridgeScript leaves "" info.type then
      let opn := "open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.HOLX Programme.H in\n"
      let ind := "\n".intercalate ((sc.splitOn "\n").map ("  " ++ ·))
      bridges := bridges.push (opn ++ s!"/-- The module's statement, re-proved from the deep certificates read in the full structure on the module's postulates: the image check. -/\ntheorem {dst ++ `of_deep} : type_of% @_root_.{srcName} := by\n{ind}")
    pure bridges
  for b in bridges do
    match Parser.runParserCategory (← getEnv) `command b with
    | .ok bstx => withRef stx <| elabCommand (relocate (SourceInfo.fromRef stx) bstx)
    | .error err => throwError m!"[deep_translate] bridge does not parse: {err}\n{b}"

end Programme.H

end


open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.HOLX
  Programme.«20261022-1724-ontological».ThWhole

/-! ## Translations of the module's own proofs (symmetric frames) -/

set_option maxHeartbeats 0 in
#deep_translate Th3 as Programme.Run6.H.Th3K
set_option maxHeartbeats 0 in
#deep_translate Th5_KB as Programme.Run6.H.Th5K
set_option maxHeartbeats 0 in
#deep_translate MC_KB as Programme.Run6.H.MCK

/-- The frame formula read off `symm` is `∀u v. R u v → R v u`. -/
example : Programme.Run6.H.Th3K.Fs = [.all .w (.all .w (.imp (.rel (.var (.succ .zero)) (.var .zero))
    (.rel (.var .zero) (.var (.succ .zero)))))] := rfl

/-! ## Probes: a hypothesis mentioning `P` is not a frame formula (sk's C7 probe) -/

namespace Programme.Run6.H.Probe
theorem relP (h : ∀ w v : i, w 𝗿 v → P G v) : ⌊□(P G)⌋ := fun w v r => h w v r
end Programme.Run6.H.Probe

/--
error: [deep_translate] outside the fragment: h: not a validity statement with one world quantifier: (∀:w. (∀:w. (R #1 #0 → (P (λ:e. (λw. (∀:(e → σ). ((P #0)@#1 → (#0 #2)@#1)))))@#0)))
  in the step: h w v r
  inside the proof of: []
-/
#guard_msgs in
#deep_translate Programme.Run6.H.Probe.relP as Programme.Run6.H.PRP

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
