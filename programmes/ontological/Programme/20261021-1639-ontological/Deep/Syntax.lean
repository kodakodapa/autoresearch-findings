/- Typed modal higher-order syntax. This module uses full function-space models,
not general Henkin models, and makes no validity-transfer claim. -/
namespace Programme.«20261021-1639-ontological».Deep

inductive Ty where
  | entity | prop | arr : Ty → Ty → Ty
  deriving DecidableEq

abbrev Property := Ty.arr Ty.entity Ty.prop

inductive Var : List Ty → Ty → Type where
  | here : Var (a :: Γ) a
  | there : Var Γ a → Var (b :: Γ) a

/-- Constants are an arbitrary typed signature. No world-sort constructor occurs. -/
inductive Term (Const : Ty → Type) : List Ty → Ty → Type where
  | var : Var Γ a → Term Const Γ a
  | const : Const a → Term Const Γ a
  | app : Term Const Γ (.arr a b) → Term Const Γ a → Term Const Γ b
  | lam : Term Const (a :: Γ) b → Term Const Γ (.arr a b)
  | falsum : Term Const Γ .prop
  | imp : Term Const Γ .prop → Term Const Γ .prop → Term Const Γ .prop
  | box : Term Const Γ .prop → Term Const Γ .prop
  | all : Term Const (a :: Γ) .prop → Term Const Γ .prop
  | equal : Term Const Γ a → Term Const Γ a → Term Const Γ .prop

/-- The ontological signature exposes actuality and positivity at their Notes types. -/
inductive OntConst : Ty → Type where
  | actual : OntConst Property
  | positive : OntConst (.arr Property .prop)

def Carrier (W E : Type) : Ty → Type
  | .entity => E
  | .prop => W → Prop
  | .arr a b => Carrier W E a → Carrier W E b

abbrev Env (W E : Type) (Γ : List Ty) := ∀ {a}, Var Γ a → Carrier W E a

def extend (ρ : Env W E Γ) (x : Carrier W E a) : Env W E (a :: Γ)
  | _, .here => x
  | _, .there v => ρ v

structure Model (Const : Ty → Type) (W E : Type) where
  rel : W → W → Prop
  interp : ∀ {a}, Const a → Carrier W E a

def eval (m : Model C W E) (ρ : Env W E Γ) : Term C Γ a → Carrier W E a
  | .var v => ρ v
  | .const c => m.interp c
  | .app f x => eval m ρ f (eval m ρ x)
  | .lam t => fun x => eval m (extend ρ x) t
  | .falsum => fun _ => False
  | .imp p q => fun w => eval m ρ p w → eval m ρ q w
  | .box p => fun w => ∀ v, m.rel w v → eval m ρ p v
  | .all p => fun w => ∀ x, eval m (extend ρ x) p w
  | .equal s t => fun _ => eval m ρ s = eval m ρ t

abbrev Ren (Γ Δ : List Ty) := ∀ {a}, Var Γ a → Var Δ a

def liftRen (r : Ren Γ Δ) : Ren (a :: Γ) (a :: Δ)
  | _, .here => .here
  | _, .there v => .there (r v)

def rename (r : Ren Γ Δ) : Term C Γ a → Term C Δ a
  | .var v => .var (r v)
  | .const c => .const c
  | .app f x => .app (rename r f) (rename r x)
  | .lam t => .lam (rename (liftRen r) t)
  | .falsum => .falsum
  | .imp p q => .imp (rename r p) (rename r q)
  | .box p => .box (rename r p)
  | .all p => .all (rename (liftRen r) p)
  | .equal s t => .equal (rename r s) (rename r t)

theorem extend_liftRen (r : Ren Γ Δ) (ρ : Env W E Δ) (x : Carrier W E a) :
    (fun {b} (v : Var (a :: Γ) b) => extend ρ x (liftRen r v)) =
    (fun {b} (v : Var (a :: Γ) b) => extend (fun v => ρ (r v)) x v) := by
  funext b v
  cases v <;> rfl

theorem eval_rename (m : Model C W E) (t : Term C Γ a)
    (r : Ren Γ Δ) (ρ : Env W E Δ) :
    eval m ρ (rename r t) = eval m (fun v => ρ (r v)) t := by
  induction t generalizing Δ with
  | var v => rfl
  | const c => rfl
  | app f x hf hx => simp only [rename, eval, hf, hx]
  | lam t ih =>
    funext x
    simp only [rename, eval, ih]
    congr 1
    funext b v
    cases v <;> rfl
  | falsum => rfl
  | imp p q hp hq => simp only [rename, eval, hp, hq]; rfl
  | box p hp => simp only [rename, eval, hp]; rfl
  | all p hp =>
    simp only [rename, eval, hp, extend_liftRen]
    rfl
  | equal s t hs ht => simp only [rename, eval, hs, ht]; rfl

abbrev Sub (C : Ty → Type) (Γ Δ : List Ty) := ∀ {a}, Var Γ a → Term C Δ a

def liftSub (s : Sub C Γ Δ) : Sub C (a :: Γ) (a :: Δ)
  | _, .here => .var .here
  | _, .there v => rename (fun u => .there u) (s v)

def subst (s : Sub C Γ Δ) : Term C Γ a → Term C Δ a
  | .var v => s v
  | .const c => .const c
  | .app f x => .app (subst s f) (subst s x)
  | .lam t => .lam (subst (liftSub s) t)
  | .falsum => .falsum
  | .imp p q => .imp (subst s p) (subst s q)
  | .box p => .box (subst s p)
  | .all p => .all (subst (liftSub s) p)
  | .equal u v => .equal (subst s u) (subst s v)

theorem eval_liftSub (m : Model C W E) (s : Sub C Γ Δ)
    (ρ : Env W E Δ) (x : Carrier W E a) :
    (fun {b} (v : Var (a :: Γ) b) => eval m (extend ρ x) (liftSub s v)) =
    (fun {b} (v : Var (a :: Γ) b) => extend (fun u => eval m ρ (s u)) x v) := by
  funext b v
  cases v with
  | here => rfl
  | there v => simp only [liftSub, eval_rename]; rfl

/-- Semantic substitution, including both higher-order binders and modal box. -/
theorem eval_subst (m : Model C W E) (t : Term C Γ a)
    (s : Sub C Γ Δ) (ρ : Env W E Δ) :
    eval m ρ (subst s t) = eval m (fun v => eval m ρ (s v)) t := by
  induction t generalizing Δ with
  | var v => rfl
  | const c => rfl
  | app f x hf hx => simp only [subst, eval, hf, hx]
  | lam t ih =>
    funext x
    simp only [subst, eval, ih, eval_liftSub]
  | falsum => rfl
  | imp p q hp hq => simp only [subst, eval, hp, hq]; rfl
  | box p hp => simp only [subst, eval, hp]; rfl
  | all p hp => simp only [subst, eval, hp, eval_liftSub]; rfl
  | equal u v hu hv => simp only [subst, eval, hu, hv]; rfl

#print axioms eval_rename
#print axioms eval_subst
end Programme.«20261021-1639-ontological».Deep
