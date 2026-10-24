/-! # Certified deep derivations of run 2's K1 and K14 proofs (thread C (b))

This file is self-contained: it repeats `DeepND.lean` (the deep calculus `Deriv`, `Cert`, and
`soundness` over closed structures, claim K1 of this run) with one addition, `Deriv.ren`
(certified derivations are closed under renaming of the context), and then translates two
shallow proofs of the programme into `Deriv T Cert` derivations, i.e. derivations whose every
`∀`-elimination and `∃`-introduction at a type of `𝓛` has an `𝓛`-term (the image of `⟦-⟧`) as
instance, with no nominal anywhere:

* `K1`: run 2's `TwoClosed` (variant 2, `Ax1GenTwo`): `L_two`, `th4`, `gex_at`, `gex`, `mc`,
  `ax1Gen_of_two`.  Theory `T2`: `Ax2a`, `Ax2b`, `Ax3`, `Ax4`, `Ax1GenTwo`, `∃x.⊤`.
* `K14`: run 2's `GexL.gex_L` (variant 3′, `L`, no conjunction axiom): `posOfGod`, `th1`, `th2`,
  `serial`, `th4L`, `gex3`, `mc3`.  Theory `T3`: `Ax2a`, `Ax2b`, plain `Ax4`, `P E₃`, `P G`.

The `𝓛`-level rules (`L_*`) are derived rules of `Deriv T Cert`; each derivation below is
built from them and from the primitive rules only.  `Sem`: by `valid_of_deriv`, the conclusions
hold at every world of every closed structure admitting all entities that satisfies the theory.
Namespaces are `Programme.Run3.Deep.*` (the definitions of `DeepND.lean` under a new prefix). -/

/-! # Deep derivations in the embedding, and soundness over 𝓛-general structures

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
namespace Programme.Run3.Deep.L
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

end Programme.Run3.Deep.L

namespace Programme.Run3.Deep.HOL

open Programme.Run3.Deep.L

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
theorem soundness (S : Str W D) (hE : ∀ x, S.A .e x) (hC : Closed S)
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

/-- The form used for sentences: a certified derivation of `⟦φ⟧` at a world variable, from `T`
alone, gives `φ` at every world of every such structure. -/
theorem valid_of_deriv (S : Str W D) (hE : ∀ x, S.A .e x) (hC : Closed S)
    {T : Tm [] .s → Prop} (hT : ∀ φ, T φ → ∀ w, eval S φ () w) {φ : Tm [] .s}
    (d : Deriv T (fun a t => Cert a t) [.w] [] (.holds (emb nilR φ) var0)) :
    ∀ w, eval S φ () w := by
  intro w
  have := soundness S hE hC hT d (cons (a := .w) w emptyEnv)
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

end rules2

end Programme.Run3.Deep.HOL



namespace Programme.Run3.Deep.K1
open Programme.Run3.Deep.L Programme.Run3.Deep.HOL

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

end Programme.Run3.Deep.K1


namespace Programme.Run3.Deep.K14
open Programme.Run3.Deep.L Programme.Run3.Deep.HOL Programme.Run3.Deep.K1

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

end Programme.Run3.Deep.K14

namespace Programme.Run3.Deep.Sem
open Programme.Run3.Deep.L Programme.Run3.Deep.HOL

variable {W D : Type}

/-- **K1, semantically.** In every closed structure admitting all entities in which variant 2's
`Ax2a`, `Ax2b`, `Ax3`, `Ax4`, `Ax1GenTwo` and `∃x.⊤` hold at every world, unrestricted `Ax1Gen`,
modal collapse `∀p. p → □p` and `∃ᴱx. G x` hold at every world.  Proved by `valid_of_deriv` from
the certified derivations `K1.ax1Gen_of_two`, `K1.mc`, `K1.gex`. -/
theorem k1_valid (S : Str W D) (hE : ∀ x, S.A .e x) (hC : Closed S)
    (hT : ∀ φ, K1.T2 φ → ∀ w, eval S φ () w) (w : W) :
    eval S (K1.Ax1Gen : Tm [] .s) () w ∧ eval S (K1.MC : Tm [] .s) () w ∧ eval S (K1.ExG : Tm [] .s) () w :=
  ⟨valid_of_deriv S hE hC hT (K1.ax1Gen_of_two (r := nilR) (i := var0) (hs := [])) w,
    valid_of_deriv S hE hC hT (K1.mc (r := nilR) (i := var0) (hs := [])) w,
    valid_of_deriv S hE hC hT (K1.gex (r := nilR) (i := var0) (hs := [])) w⟩

/-- **K14, semantically.** In every closed structure admitting all entities in which `Ax2a`,
`Ax2b`, plain `Ax4`, `P E₃` and `P G` hold at every world, `∃ᴱx. G x` and modal collapse hold at
every world, on any frame. -/
theorem k14_valid (S : Str W D) (hE : ∀ x, S.A .e x) (hC : Closed S)
    (hT : ∀ φ, K14.T3 φ → ∀ w, eval S φ () w) (w : W) :
    eval S (K1.ExG : Tm [] .s) () w ∧ eval S (K1.MC : Tm [] .s) () w :=
  ⟨valid_of_deriv S hE hC hT (K14.gex3 (r := nilR) (i := var0) (hs := [])) w,
    valid_of_deriv S hE hC hT (K14.mc3 (r := nilR) (i := var0) (hs := [])) w⟩

/-- The certified derivations themselves, as sentences at a world variable from the theory alone. -/
theorem k1_derivations :
    DC K1.T2 [.w] [] (Lf nilR K1.Ax1Gen var0) ∧ DC K1.T2 [.w] [] (Lf nilR K1.MC var0) ∧
      DC K1.T2 [.w] [] (Lf nilR K1.ExG var0) :=
  ⟨K1.ax1Gen_of_two, K1.mc, K1.gex⟩

theorem k14_derivations :
    DC K14.T3 [.w] [] (Lf nilR K1.ExG var0) ∧ DC K14.T3 [.w] [] (Lf nilR K1.MC var0) :=
  ⟨K14.gex3, K14.mc3⟩

end Programme.Run3.Deep.Sem

#print axioms Programme.Run3.Deep.HOL.soundness
#print axioms Programme.Run3.Deep.HOL.Deriv.ren
#print axioms Programme.Run3.Deep.Sem.k1_derivations
#print axioms Programme.Run3.Deep.Sem.k14_derivations
#print axioms Programme.Run3.Deep.Sem.k1_valid
#print axioms Programme.Run3.Deep.Sem.k14_valid
