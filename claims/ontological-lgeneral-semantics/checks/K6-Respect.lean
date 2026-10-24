/-! # Extensional carriers: the FM models respect Leibniz at every type

Run 2's `LGenF` carriers (`LGeneralFull.AdmF`) are closed under all terms, but equality at an arrow
type is agreement on admitted arguments (`eqT`), and an admitted `F : (σ→σ) → σ` need not respect
it.  So `Leib := ∀f₁f₂:σ→σ. ∀F:(σ→σ)→σ. f₁ = f₂ → F f₁ = F f₂` can fail in `str S`
(th's P9/P19), whereas in v4's `def:lgeneral` (`P_{a→b} ⊆ P_a → P_b`) it cannot.

Here the carriers are cut down by a logical relation guarded by support:
`rel (a→b) F G := ∀ x y supported, rel x y → rel (F x) (G y)`, `AdmR t x := Sup t x ∧ rel t x x`.
Results, for every symmetric structure `S : LGeneralFull.Sym`:
* `closedR`: `strR S` is closed under all terms of the full language;
* `eqT_rel`: on admitted objects `eqT = rel`; `leibnizR`: Leibniz substitution for every term
  motive at every type; `leib_true`: the sentence `Leib` holds at every world;
* at `σ`, `τ`, `τ → σ` the carriers are those of `AdmF` (`lgenFR_of_sym`), so every earlier claim
  about `fm`, `gfm`, `fmId`, `rx` (K102, K104, K108 ...) is about the same models.
-/
namespace Programme.Run3.Respect

-- Verbatim copy of the definitions of the library's Run2.LGeneralFull (lines 26-141, 150-167,
-- 184-192, 229-236, 332-342), so that this file builds on its own.
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

end Programme.Run3.Respect

#print axioms Programme.Run3.Respect.closedR
#print axioms Programme.Run3.Respect.leibnizR
#print axioms Programme.Run3.Respect.leib_true
#print axioms Programme.Run3.Respect.lgenFR_of_sym
#print axioms Programme.Run3.Respect.Sep.separating_all_types
#print axioms Programme.Run3.Respect.Sep.phi_false
