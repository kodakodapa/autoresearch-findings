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

#print axioms Programme.Run3.HOLX.soundness
#print axioms Programme.Run3.HOLX.valid_of_deriv
#print axioms Programme.Run3.HOLX.heval_emb
#print axioms Programme.Run3.HOLX.leib_derivable
#print axioms Programme.Run3.HOLX.Flip.resp_needed
#print axioms Programme.Run3.HOLX.Flip.not_resp_SF
#print axioms Programme.Run3.HOLX.fund
#print axioms Programme.Run3.HOLX.full_closed_resp
