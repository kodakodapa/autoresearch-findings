/-! # Thread F: `NoNecExist` fails in an `𝓛`-general model (th's conjecture P9)

`NoNecExist` (in `Ax1GenTwoVariant3Plain`, `Ax1GenTwoVariant3Th4`, `Ax1GenOneVariant3`,
`Ax1GenBoxVariant3`, `GoedelVariantHOML3inS4oneFile`) says: with two distinct worlds (and
reflexivity, where the module asks for it) nothing has necessary existence, `¬ E x w`.
Its hypotheses are frame facts.  The model below is `𝓛`-general in the sense of
arXiv 2609.36279v4, `def:lgeneral`, satisfies the axioms of all five modules, and has two
distinct worlds, a universal (so reflexive, transitive, symmetric) relation and `E x w`.
By `prop:lgeneral`, no proof of `NoNecExist` meets the hypothesis of the soundness theorem:
the item has no hybrid-free proof.

**The model.**  Worlds `Bool`, one individual (`Unit`), actual everywhere, `R` universal,
`P φ w := φ () w`.  The domain `P_τ` at each type of `𝓛` (types built from `e`, `o`, `σ` by `→`)
is the hereditarily swap-invariant objects (`Adm`), the swap `w ↦ !w` acting on the full
type hierarchy by conjugation (`act`).

**`𝓛`-generality** (`lgeneral`).  `Tm` is `𝓛` as a datatype: variables of every type, `λ`,
application, the signature (`P`, `existsAt`), the lifted connectives `⊥ ⊤ ¬ ∧ ∨ → ↔`, `□`, `◇`,
possibilist quantifiers at every type, actualist ones at `e`, the primitive equality at every
type (lifted: `fun _ => x = y`), and at the `o` level validity `⌊·⌋`, the propositional
connectives, quantifiers at every type and equality.  There is no term of the world type.
Every term with admitted parameters denotes an admitted object: evaluation commutes with the
swap (`eval_act`), because the swap fixes `R`, `existsAt` and `P` and permutes each domain.

**The axioms** are stated as in the modules, with every quantifier at a type of `𝓛` ranging over
the domain (`def:lgeneral`).  Admitted propositions and properties are constant in the world,
so the model is a one-world model as far as `𝓛` sees: `E` holds of the individual. -/

namespace Programme.F.NoNecModel

/-! ## Types, domains, the swap -/

inductive Ty
  | e | o | s
  | arr : Ty → Ty → Ty

/-- Full type hierarchy over worlds `Bool` and individuals `Unit`; `s` is `σ = i → o`. -/
@[reducible] def Den : Ty → Type
  | .e => Unit
  | .o => Prop
  | .s => Bool → Prop
  | .arr a b => Den a → Den b

/-- The swap of the two worlds, acting by conjugation. -/
def act : (t : Ty) → Den t → Den t
  | .e, x => x
  | .o, p => p
  | .s, q => fun w => q (!w)
  | .arr a b, f => fun x => act b (f (act a x))

theorem act_act : (t : Ty) → (x : Den t) → act t (act t x) = x
  | .e, _ => rfl
  | .o, _ => rfl
  | .s, q => funext fun w => by simp [act]
  | .arr a b, f => funext fun x => by
      show act b (act b (f (act a (act a x)))) = f x
      rw [act_act a, act_act b]

theorem act_inj (t : Ty) {x y : Den t} (h : act t x = act t y) : x = y := by
  rw [← act_act t x, h, act_act]

/-- The domains: hereditarily swap-invariant objects. -/
def Adm : (t : Ty) → Den t → Prop
  | .e, _ => True
  | .o, _ => True
  | .s, q => act .s q = q
  | .arr a b, f => act (.arr a b) f = f ∧ ∀ x, Adm a x → Adm b (f x)

theorem Adm.inv : {t : Ty} → {x : Den t} → Adm t x → act t x = x
  | .e, _, _ => rfl
  | .o, _, _ => rfl
  | .s, _, h => h
  | .arr _ _, _, h => h.1

/-! ## The model's signature -/

def R : Bool → Bool → Prop := fun _ _ => True
def existsAt : Unit → Bool → Prop := fun _ _ => True
def P : (Unit → Bool → Prop) → Bool → Prop := fun φ w => φ () w

/-! ## `𝓛` as a datatype -/

inductive Var : List Ty → Ty → Type
  | zero {Γ t} : Var (t :: Γ) t
  | succ {Γ t u} : Var Γ t → Var (u :: Γ) t

inductive Tm : List Ty → Ty → Type
  | var {Γ t} : Var Γ t → Tm Γ t
  | lam {Γ a b} : Tm (a :: Γ) b → Tm Γ (.arr a b)
  | app {Γ a b} : Tm Γ (.arr a b) → Tm Γ a → Tm Γ b
  | pos {Γ} : Tm Γ (.arr (.arr .e .s) .s)
  | ex {Γ} : Tm Γ (.arr .e .s)
  -- lifted connectives
  | top {Γ} : Tm Γ .s
  | bot {Γ} : Tm Γ .s
  | neg {Γ} : Tm Γ .s → Tm Γ .s
  | and {Γ} : Tm Γ .s → Tm Γ .s → Tm Γ .s
  | or {Γ} : Tm Γ .s → Tm Γ .s → Tm Γ .s
  | imp {Γ} : Tm Γ .s → Tm Γ .s → Tm Γ .s
  | iff {Γ} : Tm Γ .s → Tm Γ .s → Tm Γ .s
  | box {Γ} : Tm Γ .s → Tm Γ .s
  | dia {Γ} : Tm Γ .s → Tm Γ .s
  | all {Γ} (a : Ty) : Tm (a :: Γ) .s → Tm Γ .s
  | exi {Γ} (a : Ty) : Tm (a :: Γ) .s → Tm Γ .s
  | allE {Γ} : Tm (.e :: Γ) .s → Tm Γ .s
  | exiE {Γ} : Tm (.e :: Γ) .s → Tm Γ .s
  | eq {Γ} (a : Ty) : Tm Γ a → Tm Γ a → Tm Γ .s
  -- conditions at `o`
  | valid {Γ} : Tm Γ .s → Tm Γ .o
  | truO {Γ} : Tm Γ .o
  | falO {Γ} : Tm Γ .o
  | negO {Γ} : Tm Γ .o → Tm Γ .o
  | andO {Γ} : Tm Γ .o → Tm Γ .o → Tm Γ .o
  | orO {Γ} : Tm Γ .o → Tm Γ .o → Tm Γ .o
  | impO {Γ} : Tm Γ .o → Tm Γ .o → Tm Γ .o
  | allO {Γ} (a : Ty) : Tm (a :: Γ) .o → Tm Γ .o
  | exiO {Γ} (a : Ty) : Tm (a :: Γ) .o → Tm Γ .o
  | eqO {Γ} (a : Ty) : Tm Γ a → Tm Γ a → Tm Γ .o

@[reducible] def Env : List Ty → Type
  | [] => Unit
  | t :: Γ => Den t × Env Γ

def Var.get : {Γ : List Ty} → {t : Ty} → Var Γ t → Env Γ → Den t
  | _, _, .zero, ρ => ρ.1
  | _, _, .succ i, ρ => i.get ρ.2

def actEnv : (Γ : List Ty) → Env Γ → Env Γ
  | [], ρ => ρ
  | t :: Γ, ρ => (act t ρ.1, actEnv Γ ρ.2)

def EnvAdm : (Γ : List Ty) → Env Γ → Prop
  | [], _ => True
  | t :: Γ, ρ => Adm t ρ.1 ∧ EnvAdm Γ ρ.2

/-- Henkin evaluation: quantifiers at a type range over its domain `Adm`. -/
def eval : {Γ : List Ty} → {t : Ty} → Tm Γ t → Env Γ → Den t
  | _, _, .var i, ρ => i.get ρ
  | _, _, .lam b, ρ => fun x => eval b (x, ρ)
  | _, _, .app f x, ρ => eval f ρ (eval x ρ)
  | _, _, .pos, _ => P
  | _, _, .ex, _ => existsAt
  | _, _, .top, _ => fun _ => True
  | _, _, .bot, _ => fun _ => False
  | _, _, .neg a, ρ => fun w => ¬ eval a ρ w
  | _, _, .and a b, ρ => fun w => eval a ρ w ∧ eval b ρ w
  | _, _, .or a b, ρ => fun w => eval a ρ w ∨ eval b ρ w
  | _, _, .imp a b, ρ => fun w => eval a ρ w → eval b ρ w
  | _, _, .iff a b, ρ => fun w => (eval a ρ w ↔ eval b ρ w)
  | _, _, .box a, ρ => fun w => ∀ v, R w v → eval a ρ v
  | _, _, .dia a, ρ => fun w => ∃ v, R w v ∧ eval a ρ v
  | _, _, .all a b, ρ => fun w => ∀ x, Adm a x → eval b (x, ρ) w
  | _, _, .exi a b, ρ => fun w => ∃ x, Adm a x ∧ eval b (x, ρ) w
  | _, _, .allE b, ρ => fun w => ∀ y, existsAt y w → eval b (y, ρ) w
  | _, _, .exiE b, ρ => fun w => ∃ y, existsAt y w ∧ eval b (y, ρ) w
  | _, _, .eq _ a b, ρ => fun _ => eval a ρ = eval b ρ
  | _, _, .valid a, ρ => ∀ w, eval a ρ w
  | _, _, .truO, _ => True
  | _, _, .falO, _ => False
  | _, _, .negO a, ρ => ¬ eval a ρ
  | _, _, .andO a b, ρ => eval a ρ ∧ eval b ρ
  | _, _, .orO a b, ρ => eval a ρ ∨ eval b ρ
  | _, _, .impO a b, ρ => eval a ρ → eval b ρ
  | _, _, .allO a b, ρ => ∀ x, Adm a x → eval b (x, ρ)
  | _, _, .exiO a b, ρ => ∃ x, Adm a x ∧ eval b (x, ρ)
  | _, _, .eqO _ a b, ρ => eval a ρ = eval b ρ

/-- `𝓛`-generality: every term with admitted parameters denotes in the domain of its type. -/
def LGeneral : Prop :=
  ∀ {Γ : List Ty} {t : Ty} (tm : Tm Γ t) (ρ : Env Γ), EnvAdm Γ ρ → Adm t (eval tm ρ)

/-! ## Evaluation commutes with the swap -/

theorem get_act : {Γ : List Ty} → {t : Ty} → (i : Var Γ t) → (ρ : Env Γ) →
    i.get (actEnv Γ ρ) = act t (i.get ρ)
  | _, _, .zero, _ => rfl
  | _, _, .succ i, ρ => get_act i ρ.2

theorem actEnv_cons {Γ : List Ty} {a : Ty} (x : Den a) (ρ : Env Γ) :
    actEnv (a :: Γ) ((act a x, ρ) : Env (a :: Γ)) = ((x, actEnv Γ ρ) : Env (a :: Γ)) := by
  show (act a (act a x), actEnv Γ ρ) = (x, actEnv Γ ρ)
  rw [act_act]

theorem forall_bool (q : Bool → Prop) : (∀ v, q (!v)) ↔ ∀ v, q v :=
  ⟨fun h v => by simpa using h (!v), fun h v => h _⟩

theorem exists_bool (q : Bool → Prop) : (∃ v, q (!v)) ↔ ∃ v, q v :=
  ⟨fun ⟨v, h⟩ => ⟨_, h⟩, fun ⟨v, h⟩ => ⟨!v, by simpa using h⟩⟩

theorem eval_act : {Γ : List Ty} → {t : Ty} → (tm : Tm Γ t) → (ρ : Env Γ) →
    eval tm (actEnv Γ ρ) = act t (eval tm ρ)
  | _, _, .var i, ρ => get_act i ρ
  | _, .arr a _, .lam b, ρ => funext fun x => by
      show eval b (x, actEnv _ ρ) = act _ (eval b (act a x, ρ))
      have h := eval_act b ((act a x, ρ) : Env (a :: _))
      rwa [actEnv_cons] at h
  | _, _, .app (a := a) f x, ρ => by
      show eval f (actEnv _ ρ) (eval x (actEnv _ ρ)) = _
      rw [eval_act f, eval_act x]
      show act _ (eval f ρ (act a (act a (eval x ρ)))) = _
      rw [act_act]; rfl
  | _, _, .pos, _ => funext fun ψ => funext fun w => by
      show P ψ w = P (act (.arr .e .s) ψ) (!w)
      simp [P, act]
  | _, _, .ex, _ => rfl
  | _, _, .top, _ => rfl
  | _, _, .bot, _ => rfl
  | _, _, .neg a, ρ => funext fun w => by
      show (¬ eval a (actEnv _ ρ) w) = ¬ eval a ρ (!w); rw [eval_act a]; rfl
  | _, _, .and a b, ρ => funext fun w => by
      show (eval a (actEnv _ ρ) w ∧ eval b (actEnv _ ρ) w) = (eval a ρ (!w) ∧ eval b ρ (!w))
      rw [eval_act a, eval_act b]; rfl
  | _, _, .or a b, ρ => funext fun w => by
      show (eval a (actEnv _ ρ) w ∨ eval b (actEnv _ ρ) w) = (eval a ρ (!w) ∨ eval b ρ (!w))
      rw [eval_act a, eval_act b]; rfl
  | _, _, .imp a b, ρ => funext fun w => by
      show (eval a (actEnv _ ρ) w → eval b (actEnv _ ρ) w) = (eval a ρ (!w) → eval b ρ (!w))
      rw [eval_act a, eval_act b]; rfl
  | _, _, .iff a b, ρ => funext fun w => by
      show (eval a (actEnv _ ρ) w ↔ eval b (actEnv _ ρ) w) = (eval a ρ (!w) ↔ eval b ρ (!w))
      rw [eval_act a, eval_act b]; rfl
  | _, _, .box a, ρ => funext fun w => by
      show (∀ v, R w v → eval a (actEnv _ ρ) v) = ∀ v, R (!w) v → eval a ρ v
      rw [eval_act a]
      exact propext ⟨fun h v _ => by simpa [act] using h (!v) trivial,
        fun h v _ => h _ trivial⟩
  | _, _, .dia a, ρ => funext fun w => by
      show (∃ v, R w v ∧ eval a (actEnv _ ρ) v) = ∃ v, R (!w) v ∧ eval a ρ v
      rw [eval_act a]
      exact propext ⟨fun ⟨v, _, h⟩ => ⟨_, trivial, h⟩,
        fun ⟨v, _, h⟩ => ⟨!v, trivial, by simpa [act] using h⟩⟩
  | _, _, .all a b, ρ => funext fun w => by
      show (∀ x, Adm a x → eval b (x, actEnv _ ρ) w) = ∀ x, Adm a x → eval b (x, ρ) (!w)
      refine propext (forall_congr' fun x => imp_congr_right fun hx => ?_)
      have h := eval_act b ((x, ρ) : Env (_ :: _))
      rw [show actEnv (_ :: _) ((x, ρ) : Env (_ :: _)) = ((x, actEnv _ ρ) : Env (_ :: _)) from
        Prod.ext hx.inv rfl] at h
      rw [h]; rfl
  | _, _, .exi a b, ρ => funext fun w => by
      show (∃ x, Adm a x ∧ eval b (x, actEnv _ ρ) w) = ∃ x, Adm a x ∧ eval b (x, ρ) (!w)
      refine propext (exists_congr fun x => and_congr_right fun hx => ?_)
      have h := eval_act b ((x, ρ) : Env (_ :: _))
      rw [show actEnv (_ :: _) ((x, ρ) : Env (_ :: _)) = ((x, actEnv _ ρ) : Env (_ :: _)) from
        Prod.ext hx.inv rfl] at h
      rw [h]; rfl
  | _, _, .allE b, ρ => funext fun w => by
      show (∀ y, existsAt y w → eval b (y, actEnv _ ρ) w) = ∀ y, existsAt y (!w) → eval b (y, ρ) (!w)
      refine propext (forall_congr' fun y => imp_congr Iff.rfl ?_)
      have h := eval_act b ((y, ρ) : Env (.e :: _))
      exact Eq.to_iff (congrFun h w)
  | _, _, .exiE b, ρ => funext fun w => by
      show (∃ y, existsAt y w ∧ eval b (y, actEnv _ ρ) w) = ∃ y, existsAt y (!w) ∧ eval b (y, ρ) (!w)
      refine propext (exists_congr fun y => and_congr Iff.rfl ?_)
      have h := eval_act b ((y, ρ) : Env (.e :: _))
      exact Eq.to_iff (congrFun h w)
  | _, _, .eq a x y, ρ => funext fun w => by
      show (eval x (actEnv _ ρ) = eval y (actEnv _ ρ)) = (eval x ρ = eval y ρ)
      rw [eval_act x, eval_act y]
      exact propext ⟨act_inj a, fun h => h ▸ rfl⟩
  | _, _, .valid a, ρ => by
      show (∀ w, eval a (actEnv _ ρ) w) = ∀ w, eval a ρ w
      rw [eval_act a]; exact propext (forall_bool _)
  | _, _, .truO, _ => rfl
  | _, _, .falO, _ => rfl
  | _, _, .negO a, ρ => by
      show (¬ eval a (actEnv _ ρ)) = ¬ eval a ρ; rw [eval_act a]; rfl
  | _, _, .andO a b, ρ => by
      show (eval a (actEnv _ ρ) ∧ eval b (actEnv _ ρ)) = (eval a ρ ∧ eval b ρ)
      rw [eval_act a, eval_act b]; rfl
  | _, _, .orO a b, ρ => by
      show (eval a (actEnv _ ρ) ∨ eval b (actEnv _ ρ)) = (eval a ρ ∨ eval b ρ)
      rw [eval_act a, eval_act b]; rfl
  | _, _, .impO a b, ρ => by
      show (eval a (actEnv _ ρ) → eval b (actEnv _ ρ)) = (eval a ρ → eval b ρ)
      rw [eval_act a, eval_act b]; rfl
  | _, _, .allO a b, ρ => by
      show (∀ x, Adm a x → eval b (x, actEnv _ ρ)) = ∀ x, Adm a x → eval b (x, ρ)
      refine propext (forall_congr' fun x => imp_congr_right fun hx => ?_)
      have h := eval_act b ((x, ρ) : Env (_ :: _))
      rw [show actEnv (_ :: _) ((x, ρ) : Env (_ :: _)) = ((x, actEnv _ ρ) : Env (_ :: _)) from
        Prod.ext hx.inv rfl] at h
      rw [h]; rfl
  | _, _, .exiO a b, ρ => by
      show (∃ x, Adm a x ∧ eval b (x, actEnv _ ρ)) = ∃ x, Adm a x ∧ eval b (x, ρ)
      refine propext (exists_congr fun x => and_congr_right fun hx => ?_)
      have h := eval_act b ((x, ρ) : Env (_ :: _))
      rw [show actEnv (_ :: _) ((x, ρ) : Env (_ :: _)) = ((x, actEnv _ ρ) : Env (_ :: _)) from
        Prod.ext hx.inv rfl] at h
      rw [h]; rfl
  | _, _, .eqO a x y, ρ => by
      show (eval x (actEnv _ ρ) = eval y (actEnv _ ρ)) = (eval x ρ = eval y ρ)
      rw [eval_act x, eval_act y]
      exact propext ⟨act_inj a, fun h => h ▸ rfl⟩

/-! ## The domains are closed under `𝓛` -/

theorem EnvAdm.inv : {Γ : List Ty} → {ρ : Env Γ} → EnvAdm Γ ρ → actEnv Γ ρ = ρ
  | [], _, _ => rfl
  | _ :: _, _, ⟨h1, h2⟩ => Prod.ext h1.inv h2.inv

theorem EnvAdm.get : {Γ : List Ty} → {t : Ty} → (i : Var Γ t) → {ρ : Env Γ} → EnvAdm Γ ρ →
    Adm t (i.get ρ)
  | _, _, .zero, _, h => h.1
  | _, _, .succ i, _, h => EnvAdm.get i h.2

theorem inv_eval {Γ : List Ty} {t : Ty} (tm : Tm Γ t) {ρ : Env Γ} (h : EnvAdm Γ ρ) :
    act t (eval tm ρ) = eval tm ρ := by
  rw [← eval_act, h.inv]

theorem lgeneral : LGeneral := by
  intro Γ t tm
  induction tm with
  | var i => exact fun _ h => h.get i
  | lam b ih => exact fun _ h => ⟨inv_eval (.lam b) h, fun x hx => ih (x, _) ⟨hx, h⟩⟩
  | app f x ihf ihx => exact fun _ h => (ihf _ h).2 _ (ihx _ h)
  | pos => exact fun _ h => ⟨inv_eval .pos h, fun ψ hψ =>
      funext fun w => by
        show ψ () (!w) = ψ () w
        exact (congrFun (congrFun hψ.1 ()) w)⟩
  | ex => exact fun _ _ => ⟨rfl, fun _ _ => rfl⟩
  | top => exact fun _ h => inv_eval .top h
  | bot => exact fun _ h => inv_eval .bot h
  | neg a _ => exact fun _ h => inv_eval (.neg a) h
  | and a b _ _ => exact fun _ h => inv_eval (.and a b) h
  | or a b _ _ => exact fun _ h => inv_eval (.or a b) h
  | imp a b _ _ => exact fun _ h => inv_eval (.imp a b) h
  | iff a b _ _ => exact fun _ h => inv_eval (.iff a b) h
  | box a _ => exact fun _ h => inv_eval (.box a) h
  | dia a _ => exact fun _ h => inv_eval (.dia a) h
  | all a b _ => exact fun _ h => inv_eval (.all a b) h
  | exi a b _ => exact fun _ h => inv_eval (.exi a b) h
  | allE b _ => exact fun _ h => inv_eval (.allE b) h
  | exiE b _ => exact fun _ h => inv_eval (.exiE b) h
  | eq a x y _ _ => exact fun _ h => inv_eval (.eq a x y) h
  | valid _ _ => exact fun _ _ => trivial
  | truO => exact fun _ _ => trivial
  | falO => exact fun _ _ => trivial
  | negO _ _ => exact fun _ _ => trivial
  | andO _ _ _ _ => exact fun _ _ => trivial
  | orO _ _ _ _ => exact fun _ _ => trivial
  | impO _ _ _ _ => exact fun _ _ => trivial
  | allO _ _ _ => exact fun _ _ => trivial
  | exiO _ _ _ => exact fun _ _ => trivial
  | eqO _ _ _ _ _ => exact fun _ _ => trivial

/-! ## The theories of the five modules, read in the model

Each definition follows the module text, with every quantifier at a type of `𝓛` ranging over
the domain.  `PIncN` is the inclusion with the non-emptiness clause of Fig. 8 (`⊃ᴺ` in the
variant-3 modules, `⊃ᴱ` in `Ax1GenTwoVariant3Plain`), used by `Ess` in all five; `PInc` is the
plain inclusion of `Ax4` in `Ax1GenTwoVariant3Plain`. -/

abbrev τ := Unit → Bool → Prop
/-- The domain of properties `e → σ`. -/
abbrev AP (φ : τ) : Prop := Adm (.arr .e .s) φ
/-- The domain of world-dependent sets of properties `(e → σ) → σ`. -/
abbrev AH (Φ : τ → Bool → Prop) : Prop := Adm (.arr (.arr .e .s) .s) Φ

def conj (φ ψ : τ) : τ := fun x w => φ x w ∧ ψ x w
def negp (φ : τ) : τ := fun x w => ¬ φ x w
def G (x : Unit) (w : Bool) : Prop := ∀ φ, AP φ → P φ w → φ x w
def PIncN (φ ψ : τ) (w : Bool) : Prop :=
  ∀ v, R w v → (φ ≠ fun _ _ => False) ∧ ∀ y, existsAt y v → φ y v → ψ y v
def PInc (φ ψ : τ) (w : Bool) : Prop := ∀ v, R w v → ∀ y, existsAt y v → φ y v → ψ y v
def Ess (φ : τ) (x : Unit) (w : Bool) : Prop := ∀ ψ, AP ψ → ψ x w → PIncN φ ψ w
def E (x : Unit) (w : Bool) : Prop :=
  ∀ φ, AP φ → Ess φ x w → ∀ v, R w v → ∃ y, existsAt y v ∧ φ y v
def PosProps (Φ : τ → Bool → Prop) (w : Bool) : Prop := ∀ φ, AP φ → Φ φ w → P φ w
def ConjOf (φ : τ) (Φ : τ → Bool → Prop) (w : Bool) : Prop :=
  ∀ v, R w v → ∀ z, existsAt z v → (φ z v ↔ ∀ ψ, AP ψ → Φ ψ v → ψ z v)
def TwoMembers (Φ : τ → Bool → Prop) (w : Bool) : Prop :=
  ∃ ψ₁ ψ₂, AP ψ₁ ∧ AP ψ₂ ∧ Φ ψ₁ w ∧ Φ ψ₂ w ∧ ψ₁ ≠ ψ₂
def NonEmptyS (Φ : τ → Bool → Prop) (w : Bool) : Prop := ∃ ψ, AP ψ ∧ Φ ψ w

def Ax1 : Prop := ∀ φ ψ, AP φ → AP ψ → ∀ w, P φ w ∧ P ψ w → P (conj φ ψ) w
def Ax2a : Prop := ∀ φ, AP φ → ∀ w, (P φ w ∨ P (negp φ) w) ∧ ¬ (P φ w ∧ P (negp φ) w)
def Ax2b : Prop := ∀ φ, AP φ → ∀ w, P φ w → ∀ v, R w v → P φ v
def Ax3 : Prop := ∀ w, P E w
/-- `Ax4` with the inclusion of Fig. 8 (the four variant-3 modules). -/
def Ax4N : Prop := ∀ φ ψ, AP φ → AP ψ → ∀ w, P φ w ∧ PIncN φ ψ w → P ψ w
/-- `Ax4` with the plain inclusion (`Ax1GenTwoVariant3Plain`). -/
def Ax4 : Prop := ∀ φ ψ, AP φ → AP ψ → ∀ w, P φ w ∧ PInc φ ψ w → P ψ w
def Ax1Gen : Prop :=
  ∀ Φ φ, AH Φ → AP φ → ∀ w, PosProps Φ w ∧ ConjOf φ Φ w → P φ w
def Ax1GenTwo : Prop :=
  ∀ Φ φ, AH Φ → AP φ → ∀ w, (TwoMembers Φ w ∧ PosProps Φ w) ∧ ConjOf φ Φ w → P φ w
def Ax1GenOne : Prop :=
  ∀ Φ φ, AH Φ → AP φ → ∀ w, (NonEmptyS Φ w ∧ PosProps Φ w) ∧ ConjOf φ Φ w → P φ w
def Ax1GenBox : Prop :=
  ∀ Φ φ, AH Φ → AP φ → ∀ w,
    (PosProps Φ w ∧ ∀ v, R w v → PosProps Φ v) ∧ ConjOf φ Φ w → P φ w
def Th4 : Prop := ∀ w, ∃ v, R w v ∧ ∃ x, existsAt x v ∧ G x v

/-! ### `E` and `G` are the denotations of their `𝓛`-terms -/

open Tm in
/-- `E := λx. ∀φ. (∀ψ. ψ x → □((φ ≠ λ_.⊥) ∧ ∀ᴱy. φ y → ψ y)) → □ ∃ᴱy. φ y`. -/
def tE : Tm [] (.arr .e .s) :=
  lam (all (.arr .e .s) (imp
    (all (.arr .e .s) (imp (app (var .zero) (var (.succ (.succ .zero))))
      (box (and (neg (eq (.arr .e .s) (var (.succ .zero)) (lam bot)))
        (allE (imp (app (var (.succ (.succ .zero))) (var .zero))
                   (app (var (.succ .zero)) (var .zero))))))))
    (box (exiE (app (var (.succ .zero)) (var .zero))))))

open Tm in
/-- `G := λx. ∀φ. P φ → φ x`. -/
def tG : Tm [] (.arr .e .s) :=
  lam (all (.arr .e .s) (imp (app pos (var .zero)) (app (var .zero) (var (.succ .zero)))))

theorem eval_tE : eval tE () = E := rfl
theorem eval_tG : eval tG () = G := rfl

theorem adm_E : AP E := eval_tE ▸ lgeneral tE () trivial
theorem adm_G : AP G := eval_tG ▸ lgeneral tG () trivial

/-! ### Admitted properties are constant -/

theorem AP.const {φ : τ} (h : AP φ) (x : Unit) (w : Bool) : φ x w ↔ φ () true := by
  have hc : ∀ w, φ () (!w) = φ () w := fun w => congrFun (congrFun h.1 ()) w
  cases x; cases w
  · exact Eq.to_iff (hc true)
  · exact Iff.rfl

theorem adm_top : AP (fun _ _ => True) := lgeneral (Tm.lam (Γ := []) Tm.top) () trivial

theorem ess_iff {φ : τ} (h : AP φ) (w : Bool) : Ess φ () w ↔ φ () true := by
  constructor
  · intro hE
    refine Classical.byContradiction fun hn => ?_
    refine (hE _ adm_top trivial w trivial).1 (funext fun x => funext fun v => ?_)
    exact propext ⟨fun hx => hn ((h.const x v).1 hx), False.elim⟩
  · intro ht ψ hψ hψx v _
    refine ⟨fun heq => ?_, fun y _ _ => (hψ.const y v).2 ((hψ.const () w).1 hψx)⟩
    have := (h.const () true).2 ht
    rw [heq] at this; exact this

theorem E_all (x : Unit) (w : Bool) : E x w := by
  cases x
  intro φ hφ hess v _
  exact ⟨(), trivial, (hφ.const () v).2 ((ess_iff hφ w).1 hess)⟩

theorem ax1 : Ax1 := fun _ _ _ _ _ h => h
theorem ax2a : Ax2a := fun φ _ w =>
  ⟨Classical.em (φ () w), fun ⟨h1, h2⟩ => h2 h1⟩
theorem ax2b : Ax2b := fun _ h w hp v _ => (h.const () v).2 ((h.const () w).1 hp)
theorem ax3 : Ax3 := fun w => E_all () w
theorem ax4N : Ax4N := fun _ _ _ _ w ⟨hp, hi⟩ => (hi w trivial).2 () trivial hp
theorem ax4 : Ax4 := fun _ _ _ _ w ⟨hp, hi⟩ => hi w trivial () trivial hp
theorem ax1Gen : Ax1Gen := fun _ _ _ _ w ⟨hpos, hc⟩ =>
  (hc w trivial () trivial).2 fun ψ hψ hΦ => hpos ψ hψ hΦ
theorem ax1GenTwo : Ax1GenTwo := fun Φ φ hΦ hφ w ⟨⟨_, hp⟩, hc⟩ => ax1Gen Φ φ hΦ hφ w ⟨hp, hc⟩
theorem ax1GenOne : Ax1GenOne := fun Φ φ hΦ hφ w ⟨⟨_, hp⟩, hc⟩ => ax1Gen Φ φ hΦ hφ w ⟨hp, hc⟩
theorem ax1GenBox : Ax1GenBox := fun Φ φ hΦ hφ w ⟨⟨hp, _⟩, hc⟩ => ax1Gen Φ φ hΦ hφ w ⟨hp, hc⟩
theorem th4 : Th4 := fun w => ⟨w, trivial, (), trivial, fun _ _ hp => hp⟩

/-- **The model.**  `𝓛`-general for the whole of `𝓛`; two distinct worlds; `R` reflexive and
transitive (universal); the axioms of `Ax1GenTwoVariant3Plain` (`Ax1`, `Ax2a`, `Ax2b`, `Ax3`,
plain `Ax4`, `Ax1GenTwo`), of the four variant-3 modules (`Ax4` of Fig. 8, `Ax1GenTwo`,
`Ax1GenOne`, `Ax1GenBox`, unrestricted `Ax1Gen`, postulated `Th4`); and `NoNecExist` fails in
each of its two forms. -/
theorem nonec_model :
    LGeneral ∧ (true ≠ false) ∧ (∀ u, R u u) ∧ (∀ x y z, R x y ∧ R y z → R x z) ∧
    Ax1 ∧ Ax2a ∧ Ax2b ∧ Ax3 ∧ Ax4 ∧ Ax4N ∧
    Ax1Gen ∧ Ax1GenTwo ∧ Ax1GenOne ∧ Ax1GenBox ∧ Th4 ∧
    AP E ∧ AP G ∧ (∀ x w, E x w) ∧
    ¬ (∀ v w : Bool, v ≠ w → ∀ x, ¬ E x w) ∧
    ¬ (∀ v w : Bool, v ≠ w → (∀ u, R u u) → ∀ x, ¬ E x w) :=
  ⟨lgeneral, Bool.noConfusion, fun _ => trivial, fun _ _ _ _ => trivial,
   ax1, ax2a, ax2b, ax3, ax4, ax4N, ax1Gen, ax1GenTwo, ax1GenOne, ax1GenBox, th4,
   adm_E, adm_G, E_all,
   fun h => h true false Bool.noConfusion () (E_all () false),
   fun h => h true false Bool.noConfusion (fun _ => trivial) () (E_all () false)⟩

end Programme.F.NoNecModel

#print axioms Programme.F.NoNecModel.nonec_model
