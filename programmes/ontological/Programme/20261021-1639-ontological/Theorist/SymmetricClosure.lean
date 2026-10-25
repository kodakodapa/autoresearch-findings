import Programme.«20261021-1639-ontological».Deep.Henkin

/-! Generic Fraenkel–Mostowski symmetry closure for the deep HOML language
(plan P242). `Programme.Deep.{Syntax,FullAgreement,Henkin}` are verbatim copies of
r1's K25/K29/K36 files.

Data: a group acting on worlds and entities, accessibility invariant under it, and a
decreasing chain of subgroups `K n` closed under conjugation (a normal filter base).
Carriers: entities; at `prop` and arrow types, the functions that are equivariant
under some `K n` (hereditarily symmetric objects). Result: with invariant constants,
deep evaluation commutes with the group (`equivariant`) and every term denotes
(`denotes`), so the hereditarily symmetric carriers form a K36 `Henkin.Model` with
`closed` proved. Its admitted propositions are exactly the `K n`-invariant ones
(`admitted_iff`). -/

namespace Programme.«20261021-1639-ontological».Theorist.SymmetricClosure
open Programme.«20261021-1639-ontological».Deep Programme.«20261021-1639-ontological».Deep.Henkin

structure Sym (W E : Type) where
  G : Type
  mul : G → G → G
  inv : G → G
  aw : G → W → W
  ae : G → E → E
  aw_mul : ∀ g h w, aw (mul g h) w = aw g (aw h w)
  ae_mul : ∀ g h x, ae (mul g h) x = ae g (ae h x)
  aw_inv : ∀ g w, aw (inv g) (aw g w) = w
  aw_inv' : ∀ g w, aw g (aw (inv g) w) = w
  ae_inv : ∀ g x, ae (inv g) (ae g x) = x
  ae_inv' : ∀ g x, ae g (ae (inv g) x) = x
  K : Nat → G → Prop
  anti : ∀ {n m g}, n ≤ m → K m g → K n g
  normal : ∀ g n, ∃ m, ∀ h, K m h → K n (mul (inv g) (mul h g))
  ent_supp : ∀ x, ∃ n, ∀ g, K n g → ae g x = x

variable {W E : Type} (S : Sym W E)

/-- A carrier with a group action. -/
structure Car where
  T : Type
  act : S.G → T → T
  act_mul : ∀ g h x, act (S.mul g h) x = act g (act h x)
  act_inv : ∀ g x, act (S.inv g) (act g x) = x
  act_inv' : ∀ g x, act g (act (S.inv g) x) = x

variable {S}


theorem Car.conj (A : Car S) (g h : S.G) (y : A.T) :
    A.act (S.mul (S.inv g) (S.mul h g)) y = A.act (S.inv g) (A.act h (A.act g y)) := by
  rw [A.act_mul, A.act_mul]

theorem Car.inv_mul (A : Car S) (g h : S.G) (x : A.T) :
    A.act (S.inv (S.mul g h)) x = A.act (S.inv h) (A.act (S.inv g) x) := by
  have e : A.act g (A.act h (A.act (S.inv (S.mul g h)) x)) = x := by
    rw [← A.act_mul]; exact A.act_inv' _ _
  conv => rhs; rw [← e]
  rw [A.act_inv, A.act_inv]

theorem Car.act_inj (A : Car S) (g : S.G) {x y : A.T} (h : A.act g x = A.act g y) : x = y := by
  rw [← A.act_inv g x, h, A.act_inv]

/-- `f` commutes with every element of `K n`. -/
def Equi (A B : Car S) (n : Nat) (f : A.T → B.T) : Prop :=
  ∀ g, S.K n g → ∀ x, f (A.act g x) = B.act g (f x)

/-- `x` is fixed by every element of `K n`. -/
def Fix (A : Car S) (n : Nat) (x : A.T) : Prop := ∀ g, S.K n g → A.act g x = x

theorem Fix.mono {A : Car S} {n m : Nat} {x : A.T} (h : Fix A n x) (hnm : n ≤ m) :
    Fix A m x := fun g hg => h g (S.anti hnm hg)

theorem conj_equi (A B : Car S) (g : S.G) {n : Nat} {f : A.T → B.T} (hf : Equi A B n f) :
    ∃ m, Equi A B m (fun x => B.act g (f (A.act (S.inv g) x))) := by
  obtain ⟨m, hm⟩ := S.normal g n
  refine ⟨m, fun h hh x => ?_⟩
  have hk := hm h hh
  have e1 : A.act (S.inv g) (A.act h x) =
      A.act (S.mul (S.inv g) (S.mul h g)) (A.act (S.inv g) x) := by
    rw [A.conj, A.act_inv']
  show B.act g (f (A.act (S.inv g) (A.act h x))) = B.act h (B.act g (f (A.act (S.inv g) x)))
  rw [e1, hf _ hk, B.conj, B.act_inv']

@[reducible] def arrCar (A B : Car S) : Car S where
  T := {f : A.T → B.T // ∃ n, Equi A B n f}
  act g f := ⟨fun x => B.act g (f.1 (A.act (S.inv g) x)), by
    obtain ⟨n, hn⟩ := f.2
    exact conj_equi A B g hn⟩
  act_mul g h f := by
    apply Subtype.ext; funext x
    show B.act (S.mul g h) (f.1 (A.act (S.inv (S.mul g h)) x)) =
      B.act g (B.act h (f.1 (A.act (S.inv h) (A.act (S.inv g) x))))
    rw [B.act_mul, A.inv_mul]
  act_inv g f := by
    apply Subtype.ext; funext x
    show B.act (S.inv g) (B.act g (f.1 (A.act (S.inv g) (A.act (S.inv (S.inv g)) x)))) = f.1 x
    rw [B.act_inv, A.act_inv']
  act_inv' g f := by
    apply Subtype.ext; funext x
    show B.act g (B.act (S.inv g) (f.1 (A.act (S.inv (S.inv g)) (A.act (S.inv g) x)))) = f.1 x
    rw [B.act_inv', A.act_inv]

theorem fix_of_equi (A B : Car S) {n : Nat} (f : (arrCar A B).T) (hn : Equi A B n f.1) :
    Fix (arrCar A B) n f := by
  refine fun g hg => Subtype.ext (funext fun x => ?_)
  show B.act g (f.1 (A.act (S.inv g) x)) = f.1 x
  rw [← hn g hg, A.act_inv']

theorem arr_fix (A B : Car S) (f : (arrCar A B).T) : ∃ n, Fix (arrCar A B) n f := by
  obtain ⟨n, hn⟩ := f.2
  exact ⟨n, fix_of_equi A B f hn⟩

variable (S)

@[reducible] def worldCar : Car S where
  T := W
  act := S.aw
  act_mul := S.aw_mul
  act_inv := S.aw_inv
  act_inv' := S.aw_inv'

@[reducible] def propCar : Car S where
  T := Prop
  act _ p := p
  act_mul _ _ _ := rfl
  act_inv _ _ := rfl
  act_inv' _ _ := rfl

@[reducible] def entCar : Car S where
  T := E
  act := S.ae
  act_mul := S.ae_mul
  act_inv := S.ae_inv
  act_inv' := S.ae_inv'

/-- Hereditarily symmetric carriers: propositions are symmetric functions `W → Prop`. -/
@[reducible] def car : Ty → Car S
  | .entity => entCar S
  | .prop => arrCar (worldCar S) (propCar S)
  | .arr a b => arrCar (car a) (car b)

variable {S}

theorem typed_fix : ∀ (a : Ty) (x : (car S a).T), ∃ n, Fix (car S a) n x
  | .entity, x => S.ent_supp x
  | .prop, x => arr_fix _ _ x
  | .arr _ _, x => arr_fix _ _ x

/-- Symmetric propositions: invariant under some `K n`. -/
def SymProp (S : Sym W E) (p : W → Prop) : Prop :=
  ∃ n, ∀ g, S.K n g → ∀ w, p (S.aw g w) = p w

theorem symProp_iff (p : W → Prop) : SymProp S p ↔ ∃ n, Equi (worldCar S) (propCar S) n p :=
  Iff.rfl

theorem typed_nonempty [Nonempty E] : ∀ a : Ty, Nonempty (car S a).T
  | .entity => (inferInstance : Nonempty E)
  | .prop => ⟨⟨fun _ => False, 0, fun _ _ _ => rfl⟩⟩
  | .arr a b => by
    obtain ⟨y⟩ := (typed_nonempty b : Nonempty (car S b).T)
    obtain ⟨n, hn⟩ := typed_fix b y
    exact ⟨⟨fun _ => y, n, fun g hg _ => (hn g hg).symm⟩⟩

@[reducible] def arrVal {A B : Car S} (f : (arrCar A B).T) : A.T → B.T := f.1

open Classical in
noncomputable def absF (A B : Car S) [ne : Nonempty (arrCar A B).T] (F : A.T → B.T) :
    (arrCar A B).T :=
  if h : ∃ n, Equi A B n F then ⟨F, h⟩ else Classical.choice ne

theorem absF_val (A B : Car S) [Nonempty (arrCar A B).T] {F : A.T → B.T}
    (h : ∃ n, Equi A B n F) : arrVal (absF A B F) = F := by
  have e : absF A B F = (⟨F, h⟩ : (arrCar A B).T) := dif_pos h
  rw [e]

variable (S)

open Classical in
@[reducible] noncomputable def frame [Nonempty E] (R : W → W → Prop) : Frame W where
  D a := (car S a).T
  nonempty := typed_nonempty
  app {a b} f x := arrVal (A := car S a) (B := car S b) f x
  ext {a b} f g h := Subtype.ext (funext h)
  truth p := arrVal (A := worldCar S) (B := propCar S) p
  truth_inj p q h := Subtype.ext h
  abstract {a b} F := @absF _ _ _ (car S a) (car S b) (typed_nonempty (.arr a b)) F
  abstract_spec {a b} F := by
    rintro ⟨g, hg⟩ x
    have e : F = g.1 := funext fun y => (hg y).symm
    have h : ∃ n, Equi (car S a) (car S b) n F := e ▸ g.2
    exact congrFun (@absF_val _ _ _ (car S a) (car S b) (typed_nonempty (.arr a b)) F h) x
  reify p := @absF _ _ _ (worldCar S) (propCar S) (typed_nonempty .prop) p
  reify_spec p := by
    rintro ⟨q, hq⟩
    have h : SymProp S p := hq ▸ q.2
    exact @absF_val _ _ _ (worldCar S) (propCar S) (typed_nonempty .prop) p h
  rel := R

variable {S} [Nonempty E] {R : W → W → Prop}

theorem reify_val {p : W → Prop} (h : SymProp S p) : (frame S R).truth ((frame S R).reify p) = p :=
  (frame S R).reify_spec p ⟨⟨p, h⟩, rfl⟩

theorem abstract_val {a b : Ty} {F : (car S a).T → (car S b).T}
    (h : ∃ n, Equi (car S a) (car S b) n F) (x : (car S a).T) :
    (frame S R).app ((frame S R).abstract F) x = F x :=
  (frame S R).abstract_spec F ⟨⟨F, h⟩, fun _ => rfl⟩ x

/-- The action on assignments. -/
def actA (g : S.G) (ρ : Assignment (frame S R) Γ) : Assignment (frame S R) Γ :=
  fun {a} v => (car S a).act g (ρ v)

theorem push_act (g : S.G) (ρ : Assignment (frame S R) Γ) (x : (car S a).T) :
    @Eq (Assignment (frame S R) (a :: Γ)) (push (actA g ρ) ((car S a).act g x))
      (actA g (push ρ x)) := by
  funext b v
  cases v <;> rfl

/-- Every assignment of a finite context has a common symmetry support. -/
theorem assign_fix : ∀ {Γ : List Ty} (ρ : Assignment (frame S R) Γ),
    ∃ n, ∀ g, S.K n g → @Eq (Assignment (frame S R) Γ) (actA g ρ) ρ
  | [], ρ => ⟨0, fun g _ => by funext b v; nomatch v⟩
  | a :: Γ, ρ => by
    obtain ⟨n1, h1⟩ := assign_fix (Γ := Γ) (fun v => ρ (.there v))
    obtain ⟨n2, h2⟩ := typed_fix a (ρ .here)
    refine ⟨max n1 n2, fun g hg => ?_⟩
    funext b v
    cases v with
    | here => exact h2 g (S.anti (Nat.le_max_right _ _) hg)
    | there v =>
      have := congrArg (fun r : Assignment (frame S R) Γ => r v)
        (h1 g (S.anti (Nat.le_max_left _ _) hg))
      exact this

/-- A proposition-valued family covariant in the assignment is symmetric. -/
theorem family_sym (Q : Assignment (frame S R) Γ → W → Prop)
    (hQ : ∀ g (ρ : Assignment (frame S R) Γ), Q (actA g ρ) = fun w => Q ρ (S.aw (S.inv g) w)) (ρ) : SymProp S (Q ρ) := by
  obtain ⟨n, hn⟩ := assign_fix ρ
  refine ⟨n, fun g hg w => ?_⟩
  have e := congrFun (hQ g ρ) (S.aw g w)
  rw [hn g hg, S.aw_inv] at e
  exact e

theorem reify_equi (Q : Assignment (frame S R) Γ → W → Prop)
    (hQ : ∀ g (ρ : Assignment (frame S R) Γ), Q (actA g ρ) = fun w => Q ρ (S.aw (S.inv g) w)) (g : S.G) (ρ) :
    (frame S R).reify (Q (actA g ρ)) = (car S .prop).act g ((frame S R).reify (Q ρ)) := by
  apply (frame S R).truth_inj
  rw [reify_val (family_sym Q hQ _)]
  show Q (actA g ρ) = fun w => (frame S R).truth ((frame S R).reify (Q ρ)) (S.aw (S.inv g) w)
  rw [reify_val (family_sym Q hQ _)]
  exact hQ g ρ

variable {C : Ty → Type} (I : ∀ {a}, C a → (car S a).T)

abbrev Equivariant (R : W → W → Prop) (t : Term C Γ a) : Prop :=
  ∀ g (ρ : Assignment (frame S R) Γ), translate (frame S R) I t (actA g ρ) = (car S a).act g (translate (frame S R) I t ρ)

abbrev QImp (R : W → W → Prop) (p q : Term C Γ .prop) (ρ : Assignment (frame S R) Γ) : W → Prop :=
  Shallow.imp ((frame S R).truth (translate (frame S R) I p ρ)) ((frame S R).truth (translate (frame S R) I q ρ))
abbrev QBox (R : W → W → Prop) (p : Term C Γ .prop) (ρ : Assignment (frame S R) Γ) : W → Prop :=
  Shallow.box R ((frame S R).truth (translate (frame S R) I p ρ))
abbrev QAll (R : W → W → Prop) (p : Term C (a :: Γ) .prop) (ρ : Assignment (frame S R) Γ) : W → Prop :=
  Shallow.all (fun x => (frame S R).truth (translate (frame S R) I p (push ρ x)))
abbrev QEq (R : W → W → Prop) (s t : Term C Γ a) (ρ : Assignment (frame S R) Γ) : W → Prop :=
  Shallow.equal (translate (frame S R) I s ρ) (translate (frame S R) I t ρ)

theorem truth_act (g : S.G) (q : (car S .prop).T) (w : W) :
    (frame S R).truth ((car S .prop).act g q) w = (frame S R).truth q (S.aw (S.inv g) w) := rfl

theorem tr_truth {p : Term C Γ .prop} (hp : Equivariant I R p) (g : S.G)
    (ρ : Assignment (frame S R) Γ) (v : W) :
    arrVal (A := worldCar S) (B := propCar S) (translate (frame S R) I p (actA g ρ)) v =
      arrVal (A := worldCar S) (B := propCar S) (translate (frame S R) I p ρ) (S.aw (S.inv g) v) := by
  rw [hp g ρ]

theorem qimp_cov {p q : Term C Γ .prop} (hp : Equivariant I R p) (hq : Equivariant I R q) :
    ∀ g (ρ : Assignment (frame S R) Γ),
      QImp I R p q (actA g ρ) = fun w => QImp I R p q ρ (S.aw (S.inv g) w) := by
  intro g ρ; funext w
  simp only [QImp, Shallow.imp, tr_truth I hp, tr_truth I hq]

theorem qbox_cov (hR : ∀ g w v, R (S.aw g w) (S.aw g v) ↔ R w v)
    {p : Term C Γ .prop} (hp : Equivariant I R p) :
    ∀ g (ρ : Assignment (frame S R) Γ),
      QBox I R p (actA g ρ) = fun w => QBox I R p ρ (S.aw (S.inv g) w) := by
  intro g ρ; funext w
  simp only [QBox, Shallow.box, tr_truth I hp]
  apply propext; constructor
  · intro H v hv
    have := H (S.aw g v) ((hR (S.inv g) w (S.aw g v)).mp (by rw [S.aw_inv]; exact hv))
    rwa [S.aw_inv] at this
  · intro H v hv
    exact H _ ((hR (S.inv g) w v).mpr hv)

theorem qall_cov {p : Term C (a :: Γ) .prop} (hp : Equivariant I R p) :
    ∀ g (ρ : Assignment (frame S R) Γ),
      QAll I R p (actA g ρ) = fun w => QAll I R p ρ (S.aw (S.inv g) w) := by
  intro g ρ; funext w
  have e : ∀ x v, arrVal (A := worldCar S) (B := propCar S) (translate (frame S R) I p
      (push (actA g ρ) ((car S a).act g x))) v =
      arrVal (A := worldCar S) (B := propCar S) (translate (frame S R) I p (push ρ x))
        (S.aw (S.inv g) v) := by
    intro x v; rw [push_act, hp]
  simp only [QAll, Shallow.all]
  apply propext; constructor
  · intro H x
    rw [← e]; exact H _
  · intro H x
    have := e ((car S a).act (S.inv g) x) w
    rw [(car S a).act_inv'] at this
    rw [this]; exact H _

theorem qeq_cov {s t : Term C Γ a} (hs : Equivariant I R s) (ht : Equivariant I R t) :
    ∀ g (ρ : Assignment (frame S R) Γ),
      QEq I R s t (actA g ρ) = fun w => QEq I R s t ρ (S.aw (S.inv g) w) := by
  intro g ρ; funext w
  simp only [QEq, Shallow.equal, hs g ρ, ht g ρ]
  exact propext ⟨(car S a).act_inj g, fun h => h ▸ rfl⟩

theorem lam_equi {t : Term C (a :: Γ) b} (ht : Equivariant I R t) (ρ : Assignment (frame S R) Γ) :
    ∃ n, Equi (car S a) (car S b) n (fun x => translate (frame S R) I t (push ρ x)) := by
  obtain ⟨n, hn⟩ := assign_fix ρ
  refine ⟨n, fun g hg x => ?_⟩
  show translate (frame S R) I t (push ρ ((car S a).act g x)) = (car S b).act g (translate (frame S R) I t (push ρ x))
  conv => lhs; rw [← hn g hg]
  rw [push_act, ht]

/-- Evaluation commutes with the group action. -/
theorem equivariant (hR : ∀ g w v, R (S.aw g w) (S.aw g v) ↔ R w v)
    (hI : ∀ {a} (c : C a) g, (car S a).act g (I c) = I c) (t : Term C Γ a) :
    Equivariant I R t := by
  induction t with
  | var v => intro g ρ; rfl
  | const c => intro g ρ; exact (hI c g).symm
  | app f x hf hx =>
    intro g ρ
    show (frame S R).app (translate (frame S R) I f (actA g ρ)) (translate (frame S R) I x (actA g ρ)) = _
    rw [hf, hx]
    show (car S _).act g ((frame S R).app (translate (frame S R) I f ρ)
      ((car S _).act (S.inv g) ((car S _).act g (translate (frame S R) I x ρ)))) = _
    rw [(car S _).act_inv]; rfl
  | @lam a Γ b t ih =>
    intro g ρ
    apply (frame S R).ext; intro x
    show (frame S R).app ((frame S R).abstract fun y => translate (frame S R) I t (push (actA g ρ) y)) x =
      (car S b).act g ((frame S R).app ((frame S R).abstract fun y => translate (frame S R) I t (push ρ y))
        ((car S a).act (S.inv g) x))
    rw [abstract_val (lam_equi I ih _), abstract_val (lam_equi I ih _)]
    conv => lhs; rw [← (car S a).act_inv' g x]
    rw [push_act, ih]
  | falsum =>
    intro g ρ
    apply (frame S R).truth_inj
    show (frame S R).truth ((frame S R).reify Shallow.bot) =
      fun w => (frame S R).truth ((frame S R).reify Shallow.bot) (S.aw (S.inv g) w)
    rw [reify_val ⟨0, fun _ _ _ => rfl⟩]; rfl
  | imp p q hp hq => exact reify_equi _ (qimp_cov I hp hq)
  | box p hp => exact reify_equi _ (qbox_cov I hR hp)
  | all p hp => exact reify_equi _ (qall_cov I hp)
  | equal s t hs ht => exact reify_equi _ (qeq_cov I hs ht)

/-- Every term denotes: the hereditarily symmetric carriers are closed under terms. -/
theorem denotes (hR : ∀ g w v, R (S.aw g w) (S.aw g v) ↔ R w v)
    (hI : ∀ {a} (c : C a) g, (car S a).act g (I c) = I c) (t : Term C Γ a) (ρ : Assignment (frame S R) Γ) :
    Denotes (frame S R) I ρ t (translate (frame S R) I t ρ) := by
  induction t with
  | var v => exact .var
  | const c => exact .const
  | app f x hf hx => exact .app (hf ρ) (hx ρ)
  | lam t ih =>
    refine .lam fun x => ?_
    show Denotes _ _ _ _ ((frame S R).app ((frame S R).abstract fun y => translate (frame S R) I t (push ρ y)) x)
    rw [abstract_val (lam_equi I (equivariant I hR hI t) ρ)]
    exact ih _
  | falsum => exact .falsum (reify_val ⟨0, fun _ _ _ => rfl⟩)
  | imp p q hp hq =>
    exact .imp (hp ρ) (hq ρ)
      (reify_val (family_sym _ (qimp_cov I (equivariant I hR hI p) (equivariant I hR hI q)) ρ))
  | box p hp =>
    exact .box (hp ρ) (reify_val (family_sym _ (qbox_cov I hR (equivariant I hR hI p)) ρ))
  | all p hp =>
    exact .all (fun x => hp (push ρ x))
      (reify_val (family_sym _ (qall_cov I (equivariant I hR hI p)) ρ))
  | equal s t hs ht =>
    exact .equal (hs ρ) (ht ρ)
      (reify_val (family_sym _ (qeq_cov I (equivariant I hR hI s) (equivariant I hR hI t)) ρ))

/-- The symmetric Henkin model (K36 `Model`, with `closed` proved). -/
noncomputable def model (hR : ∀ g w v, R (S.aw g w) (S.aw g v) ↔ R w v)
    (hI : ∀ {a} (c : C a) g, (car S a).act g (I c) = I c) : Henkin.Model C W where
  frame := frame S R
  interp := I
  closed := fun ρ t => ⟨_, denotes I hR hI t ρ⟩

/-- Admitted propositions of the symmetric model are exactly the symmetric ones. -/
theorem admitted_iff (p : W → Prop) :
    (∃ q : (frame S R).D .prop, (frame S R).truth q = p) ↔ SymProp S p := by
  constructor
  · rintro ⟨q, rfl⟩; exact q.2
  · intro h; exact ⟨_, reify_val h⟩

#print axioms equivariant
#print axioms denotes
#print axioms model
#print axioms admitted_iff
end Programme.«20261021-1639-ontological».Theorist.SymmetricClosure
