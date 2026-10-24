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
namespace Programme.Run3.LX
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

end Programme.Run3.LX

namespace Programme.Run3.HOLX

open Programme.Run3.LX

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

end Programme.Run3.HOLX

namespace Programme.Run3.HOLX.Flip

open Programme.Run3.LX Programme.Run3.HOLX

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

end Programme.Run3.HOLX.Flip





namespace Programme.Run3.K1
open Programme.Run3.LX Programme.Run3.HOLX

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

end Programme.Run3.K1



namespace Programme.Run3.K14
open Programme.Run3.LX Programme.Run3.HOLX Programme.Run3.K1

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

end Programme.Run3.K14


/-! # Variant 3′ (`OpenQuestions.Ax1GenTwoVariant3Plain`) in `𝓛`

The module differs from variant 2 only in the essence: `Ess φ x := ∀ψ. ψ x → □(φ ≠ ⊥ ∧ ∀ᴱy. φ y → ψ y)`
(non-emptiness clause, no conjunct `φ x`), hence in what `Ax3 : P E` says.  The derivations of
`K1` use `Ax3` only through `P ⊤` (with `Ax4`), so they are replayed verbatim for the theory `T3p`. -/

namespace Programme.Run3.K3p
open Programme.Run3.LX Programme.Run3.HOLX Programme.Run3.K1

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


end Programme.Run3.K3p


/-! # The converse `Ax1Gen ⇒ Ax1GenTwo` as a deep derivation (the modules' `Two_weaker`) -/

namespace Programme.Run3.Conv
open Programme.Run3.LX Programme.Run3.HOLX Programme.Run3.K1

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

end Programme.Run3.Conv




namespace Programme.Run3.LX
open Programme.Run3.HOLX (Resp EnvR envR_refl get_rel fund eqT_refl eqT_symm eqT_trans)

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

end Programme.Run3.LX

/-! ## Soundness over v4's 𝓛-general models, and K1/K14 there

Composition of K4's `valid_of_deriv` (closed `Resp` structures) with th's bridge `valid_iff`. -/

namespace Programme.Run3.V4
open Programme.Run3.LX Programme.Run3.HOLX

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

end Programme.Run3.V4

/-! ## Target E over v4's models: `Two_equivalent` for variants 2 and 3′

`OpenQuestions.Ax1GenTwoVariant2.Two_equivalent` and `OpenQuestions.Ax1GenTwoVariant3Plain.Two_equivalent`
over **all** v4 𝓛-general models: given the module's `Ax2a`, `Ax2b`, `Ax3 = P E` (the module's own `E`),
plain `Ax4` and `∃x.⊤` at every world, `Ax1GenTwo` holds at every world iff unrestricted `Ax1Gen`
does.  `⇒` is `K1.ax1Gen_of_two` (variant 2) / `K3p.ax1Gen_of_two` (variant 3′); `⇐` is
`Conv.two_of_gen`, which uses `Ax1Gen` alone. -/

namespace Programme.Run3.V4
open Programme.Run3.LX Programme.Run3.HOLX

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

end Programme.Run3.V4



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

namespace Programme.Run3.SepV2
open Programme.Run3.LX

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
open Programme.Run3.SepV2.Sep

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
end Programme.Run3.SepV2


/-! ## (d) in v4's class: the quotient of `SI` is a v4 𝓛-general model of variant 2 -/

namespace Programme.Run3.SepV2.V2
open Programme.Run3.LX Programme.Run3.SepV2.Sep

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

end Programme.Run3.SepV2.V2



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

namespace Programme.Run3.SepR
open Programme.Run3.LX Programme.Run3.SepV2 Programme.Run3.SepV2.Sep

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

end Programme.Run3.SepR

#print axioms Programme.Run3.SepR.phiSep_iff
#print axioms Programme.Run3.SepR.sep_of_minimal
#print axioms Programme.Run3.SepR.sep_finite
#print axioms Programme.Run3.SepR.sep_singletons
#print axioms Programme.Run3.SepR.v2_universal_trivial
#print axioms Programme.Run3.SepR.not_v2_of_contingent
#print axioms Programme.Run3.SepR.sep_example_v4
