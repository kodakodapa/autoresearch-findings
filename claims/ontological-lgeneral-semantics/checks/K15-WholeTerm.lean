/-! WholeTerm.lean (th, round 9): Canon.lean (checks/completeness.py) lines 1-4339 verbatim, plus target C (b):
v4 prop:lgeneral for a deep calculus with Leibniz at every type and motive (namespace Programme.ThWhole). -/
/-! # M3: Henkin completeness of K4's certified calculus over v4's 𝓛-general models (th, thread C)

Assembly, in order:
1. pr's `agents/pr/lean/Programme/Run3/DeepV4.lean` lines 1-1891 verbatim: K4's calculus `Deriv T Cert`
   (`DC T`), its soundness over closed `Resp` structures, `Deriv.ren`;
2. the same file's lines 2904-3309 verbatim: th's bridge (v4's models `VM`/`LGen`, `ValidV4`, `ValidStr`,
   `valid_iff`), and lines 3315-3325 (`sound_v4`);
3. th's `Henkin.lean` (namespace `Programme.ThHenkin`): coding, Lindenbaum chain with Henkin witnesses;
4. new, namespace `Programme.ThCanon`: the canonical model.
   * `cert_nf`: every certified term is `emb canonR s` for an 𝓛-term `s` over the 𝓛-part of the context.
   * `Seed`: a consistent start `(Γ0, hs0)` with a world term; `Seed.G t`: 𝓛-terms over the 𝓛-part of
     some stage; `Seed.Eqv`: provable equality in the limit (stage independent, `transfer`).
   * `VMc`: worlds = world terms of the stages; carriers `C t` = `G t` modulo `Eqv`; `R`, actuality and
     truth read off membership; `pr_inj` (from `wExt` and a world witness) and `ap_ext` (from `funExt` and
     an 𝓛-witness) by Henkin witnesses; `ap` well defined by `funApp` and K4's Leibniz rule.
   * `LGc : LGen (VMc Z)`: the truth lemma, one clause per field of `LGen` (`ev_all`, `ev_box`, ...).
   * `completeness`: if `∃x.⊤ ∈ T` and `ValidV4 T φ`, then `DC T [w] [] ⟦φ⟧(w)`;
     `sound_complete` (with `sound_v4`), `sound_complete_str` (closed `Resp` structures), and
     `sound_complete_all`: for every theory `T`, `DC (T ∪ {∃x.⊤}) ⟦φ⟧ ↔ ValidV4 T φ`. -/

/-! # Run 3, thread C: the deep calculus over v4's 𝓛-general models (one self-contained file)

Concatenation, in order, of:
1. `DeepLeib.lean` (claim K4), plus `Deriv.ren`/`Deriv.wkD` (renaming of whole derivations, with the
   new `leib` case) from the round-2 development of `DeepK.lean`;
2. the derivations of `DeepK.lean` (claim K2: run 2's K1 and K14), unchanged, now in K4's calculus;
3. th's bridge `agents/th/lean/Programme/Th/Bridge.lean` (M1 `toStr`, M2 `ofStr`, `valid_iff`),
   lines 205-606 verbatim, placed in `Programme.Run3.LX` (its copied preamble is K4's own);
4. `V4`: `sound_v4` (K4's calculus is sound over v4's def:lgeneral models), `k1_valid_v4`,
   `k14_valid_v4`;
5. `SepV2.lean` (claim K7), plus `sep_v4`/`sep_not_valid_v4`: the eqT-quotient of K7's structure is a
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

namespace Programme.Run3.V4
open Programme.Run3.LX Programme.Run3.HOLX

/-- **Soundness over v4's def:lgeneral models.** A certified deep derivation (`∀E`/`∃I` instances
and Leibniz sides `𝓛`-terms, Leibniz motives `𝓛`-formulas) of the `𝓛`-sentence `φ` at a world
variable from the `𝓛`-theory `T` makes `φ` true at every world of every v4 `𝓛`-general model of
`T` with a nonempty domain of individuals. -/
theorem sound_v4 {T : Tm [] .s → Prop} {φ : Tm [] .s}
    (d : Deriv T (fun a t => Cert a t) [.w] [] (.holds (emb nilR φ) var0)) : ValidV4 T φ :=
  (valid_iff T φ).2 fun _ _ S _ hE hC hR hT => valid_of_deriv S hE hC hR hT d

end Programme.Run3.V4


namespace Programme.ThHenkin
open Programme.Run3.LX Programme.Run3.HOLX
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
end Programme.ThHenkin

/-! ## M3d: the canonical model -/

namespace Programme.ThCanon
open Programme.Run3.LX Programme.Run3.HOLX Programme.ThHenkin
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
  ⟨Programme.Run3.V4.sound_v4, completeness hNE⟩

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

end
end Programme.ThCanon


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

namespace Programme.ThWhole
open Programme.Run3.LX Programme.Run3.HOLX Programme.Run3.V4 Programme.ThCanon

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

end Programme.ThWhole

#print axioms Programme.ThWhole.cong
#print axioms Programme.ThWhole.sound_wt
#print axioms Programme.ThWhole.sound_v4_wt
#print axioms Programme.ThWhole.of_DC
#print axioms Programme.ThWhole.wt_sound_complete
