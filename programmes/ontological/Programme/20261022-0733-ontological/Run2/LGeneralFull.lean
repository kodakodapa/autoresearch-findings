import Programme.«20261022-0733-ontological».Run2.LGeneral
/-! # Fact (a) for the full simply typed language over `e` and `σ`

pr's `LGeneral` (`Run2.LGeneral`) closes models under a fragment of v4's `𝓛` (types `e, σ, τ, τ→σ`;
equality at `e` and `τ` only).  Here the language has **every** simple type built from `e` and
`σ` (`FTy`), application and abstraction at every arrow type, the connectives and `□` at `σ`,
possibilist quantifiers at every type (over the admitted carrier), actualist quantifiers at `e`,
primitive equality at every type, and the constant `P`.  Following the proof of v4
`prop:lgeneral`, an object of type `a → b` matters only through its values on admitted
arguments, so equality at an arrow type is agreement on admitted arguments (`eqT`).

`LGenF M` says: there are carriers `A t` at every type, equal to `M.AS`, `M.AT`, `M.AH` at `σ`,
`τ`, `τ → σ` and everything at `e`, such that every term with admitted parameters denotes an
admitted object.  `LGenF M → LGeneral M` (`lgeneral_of_lgenF`): the full notion is stronger.

Fact (a) generically (`lgenF_of_sym`): if a filtration `Fx n` of world bijections preserves
`R`, actuality and `P`, is closed under inverses and conjugation-bounded, then the carriers
"supported by some `Fx n`, and (at arrow types) admitted-to-admitted" are closed.
Instances: every flip model `FMGeneral.mk R ac P` with a flip symmetry (so `fm`, `gfm`, `fmId`)
(`lgenF_mk`, `lgenF_fm`, ...). -/

namespace Programme.«20261022-0733-ontological».Run2.LGeneralFull

open Programme.«20261022-0733-ontological».Run2.TwoClosed

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

/-- **`𝓛`-general in the full sense**: carriers at every type extending `M`'s, closed under
all terms of the full language. -/
def LGenF (M : Model W D) : Prop :=
  ∃ A : (t : FTy) → Den W D t → Prop,
    (∀ x, A .e x) ∧ (∀ q, A .s q ↔ M.AS q) ∧ (∀ φ, A tp φ ↔ M.AT φ) ∧ (∀ Φ, A th Φ ↔ M.AH Φ) ∧
    Closed ⟨M.R, M.act, M.P, A⟩

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

/-- At `τ → σ`, support already gives the admitted-to-admitted clause. -/
theorem admF_th (Φ : Den W D th) : AdmF S th Φ ↔ Sup S th Φ :=
  ⟨fun h => h.1, fun h => ⟨h, fun ψ hψ => sup_app S h (sup_of_adm S _ ψ hψ)⟩⟩

theorem admF_tp (φ : Den W D tp) : AdmF S tp φ ↔ Sup S tp φ :=
  ⟨fun h => h.1, fun h => ⟨h, fun z _ => sup_app S h (sup_of_adm S .e z trivial)⟩⟩

/-- **Generic fact (a)**: a symmetric model whose carriers at `σ`, `τ`, `τ → σ` are the supported
objects is `𝓛`-general in the full sense. -/
theorem lgenF_of_sym (M : Model W D) (S : Sym M.R M.act M.P)
    (hS : ∀ q, Sup S .s q ↔ M.AS q) (hT : ∀ φ, Sup S tp φ ↔ M.AT φ)
    (hH : ∀ Φ, Sup S th Φ ↔ M.AH Φ) : LGenF M :=
  ⟨AdmF S, fun _ => trivial, hS, fun φ => (admF_tp S φ).trans (hT φ),
   fun Φ => (admF_th S Φ).trans (hH Φ), closed S⟩

end Programme.«20261022-0733-ontological».Run2.LGeneralFull
