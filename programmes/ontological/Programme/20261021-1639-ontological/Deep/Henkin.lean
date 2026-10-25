import Programme.«20261021-1639-ontological».Deep.FullAgreement

namespace Programme.«20261021-1639-ontological».Deep.Henkin

/-- Extensional Henkin preframe. Neither propositions nor arrow carriers need be full.
The total selectors have laws only on representable functions/intensions. -/
structure Frame (W : Type) where
  D : Ty → Type
  nonempty : ∀ a, Nonempty (D a)
  app : D (.arr a b) → D a → D b
  ext : ∀ {a b} (f g : D (.arr a b)), (∀ x, app f x = app g x) → f = g
  truth : D .prop → W → Prop
  truth_inj : ∀ p q, truth p = truth q → p = q
  abstract : (D a → D b) → D (.arr a b)
  abstract_spec : ∀ {a b} (f : D a → D b),
    (∃ g, ∀ x, app g x = f x) → ∀ x, app (abstract f) x = f x
  reify : (W → Prop) → D .prop
  reify_spec : ∀ p, (∃ q, truth q = p) → truth (reify p) = p
  rel : W → W → Prop

abbrev Assignment (h : Frame W) (Γ : List Ty) := ∀ {a}, Var Γ a → h.D a

def push (ρ : Assignment h Γ) (x : h.D a) : Assignment h (a :: Γ)
  | _, .here => x
  | _, .there v => ρ v

/-- Deep semantics is a relation, so lambda closure is not smuggled in by using
full function carriers. Quantifiers range over exactly D a. -/
inductive Denotes (h : Frame W) (I : ∀ {a}, C a → h.D a) :
    {Γ : List Ty} → {a : Ty} → Assignment h Γ → Term C Γ a → h.D a → Prop where
  | var : Denotes h I ρ (.var v) (ρ v)
  | const : Denotes h I ρ (.const c) (I c)
  | app : Denotes h I ρ f fv → Denotes h I ρ x xv →
      Denotes h I ρ (.app f x) (h.app fv xv)
  | lam : (∀ x, Denotes h I (push ρ x) t (h.app f x)) → Denotes h I ρ (.lam t) f
  | falsum : h.truth p = (fun _ => False) → Denotes h I ρ .falsum p
  | imp : Denotes h I ρ s p → Denotes h I ρ t q →
      h.truth r = (fun w => h.truth p w → h.truth q w) → Denotes h I ρ (.imp s t) r
  | box : Denotes h I ρ t p →
      h.truth q = (fun w => ∀ v, h.rel w v → h.truth p v) → Denotes h I ρ (.box t) q
  | all {f : h.D a → h.D .prop} : (∀ x, Denotes h I (push ρ x) t (f x)) →
      h.truth p = (fun w => ∀ x, h.truth (f x) w) → Denotes h I ρ (.all t) p
  | equal : Denotes h I ρ s x → Denotes h I ρ t y →
      h.truth p = (fun _ => x = y) → Denotes h I ρ (.equal s t) p

/-- Definable-term closure is the explicit general-model condition. It is a
hypothesis about a carrier family, not an assertion that arbitrary families close. -/
structure Model (C : Ty → Type) (W : Type) where
  frame : Frame W
  interp : ∀ {a}, C a → frame.D a
  closed : ∀ {Γ a} (ρ : Assignment frame Γ) (t : Term C Γ a),
    ∃ v, Denotes frame interp ρ t v

/-- Independent compositional shallow interpretation using Henkin operators. -/
def translate (h : Frame W) (I : ∀ {a}, C a → h.D a) :
    Term C Γ a → Assignment h Γ → h.D a
  | .var v => fun ρ => ρ v
  | .const c => fun _ => I c
  | .app f x => fun ρ => h.app (translate h I f ρ) (translate h I x ρ)
  | .lam t => fun ρ => h.abstract (fun x => translate h I t (push ρ x))
  | .falsum => fun _ => h.reify Shallow.bot
  | .imp p q => fun ρ => h.reify (Shallow.imp (h.truth (translate h I p ρ))
      (h.truth (translate h I q ρ)))
  | .box p => fun ρ => h.reify (Shallow.box h.rel (h.truth (translate h I p ρ)))
  | .all p => fun ρ => h.reify (Shallow.all (fun x => h.truth (translate h I p (push ρ x))))
  | .equal s t => fun ρ => h.reify (Shallow.equal (translate h I s ρ) (translate h I t ρ))

theorem reify_of (h : Frame W) (p : W → Prop) (q : h.D .prop)
    (hq : h.truth q = p) : h.reify p = q :=
  h.truth_inj _ _ ((h.reify_spec p ⟨q, hq⟩).trans hq.symm)

theorem agreement (d : Denotes h I ρ t v) : translate h I t ρ = v := by
  induction d with
  | var => rfl
  | const => rfl
  | app df dx hf hx => simp only [translate, hf, hx]
  | @lam a b Γ ρ t f d ih =>
    apply h.ext
    intro x
    exact (h.abstract_spec _ ⟨f, fun y => (ih y).symm⟩ x).trans (ih x)
  | falsum hp => exact reify_of h _ _ hp
  | imp ds dt hr hs ht =>
    simp only [translate, hs, ht]
    exact reify_of h _ _ hr
  | box dt hq ht =>
    simp only [translate, ht]
    exact reify_of h _ _ hq
  | all dt hp ht =>
    simp only [translate, ht]
    exact reify_of h _ _ hp
  | equal ds dt hp hs ht =>
    simp only [translate, hs, ht]
    exact reify_of h _ _ hp

theorem unique (d : Denotes h I ρ t v) (e : Denotes h I ρ t u) : v = u :=
  (agreement d).symm.trans (agreement e)

theorem translate_denotes (m : Model C W) (ρ : Assignment m.frame Γ) (t : Term C Γ a) :
    Denotes m.frame m.interp ρ t (translate m.frame m.interp t ρ) := by
  obtain ⟨v, hv⟩ := m.closed ρ t
  rw [agreement hv]
  exact hv

def DeepValid (m : Model C W) (ρ : Assignment m.frame Γ) (p : Term C Γ .prop) : Prop :=
  ∃ v, Denotes m.frame m.interp ρ p v ∧ ∀ w, m.frame.truth v w

theorem valid_iff (m : Model C W) (ρ : Assignment m.frame Γ) (p : Term C Γ .prop) :
    Shallow.valid (m.frame.truth (translate m.frame m.interp p ρ)) ↔ DeepValid m ρ p := by
  constructor
  · intro hp
    exact ⟨_, translate_denotes m ρ p, hp⟩
  · rintro ⟨v, hv, hp⟩
    rw [agreement hv]
    exact hp

theorem consequence_iff (m : Model C W) (ρ : Assignment m.frame Γ)
    (premises : Term C Γ .prop → Prop) (q : Term C Γ .prop) :
    ((∀ p, premises p → Shallow.valid (m.frame.truth (translate m.frame m.interp p ρ))) →
      Shallow.valid (m.frame.truth (translate m.frame m.interp q ρ))) ↔
    ((∀ p, premises p → DeepValid m ρ p) → DeepValid m ρ q) := by
  simp only [valid_iff]

/-- Full carriers instantiate the general-model interface. -/
def carrierNonempty [Nonempty E] (W : Type) : ∀ a, Nonempty (Carrier W E a)
  | .entity => (inferInstance : Nonempty E)
  | .prop => ⟨fun _ => False⟩
  | .arr _ b => by
    obtain ⟨y⟩ := carrierNonempty (E := E) W b
    exact ⟨fun _ => y⟩

def fullFrame [Nonempty E] (m : Programme.«20261021-1639-ontological».Deep.Model C W E) : Frame W where
  D := Carrier W E
  nonempty := carrierNonempty W
  app := fun f x => f x
  ext := fun _ _ h => funext h
  truth := id
  truth_inj := fun _ _ h => h
  abstract := id
  abstract_spec := fun _ _ _ => rfl
  reify := id
  reify_spec := fun _ _ => rfl
  rel := m.rel

theorem full_denotes [Nonempty E] (m : Programme.«20261021-1639-ontological».Deep.Model C W E)
    (t : Term C Γ a) (ρ : Env W E Γ) :
    Denotes (fullFrame m) m.interp ρ t (eval m ρ t) := by
  induction t with
  | var v => exact .var
  | const c => exact .const
  | app f x hf hx => exact .app (hf ρ) (hx ρ)
  | lam t ih => exact .lam (fun x => ih (extend ρ x))
  | falsum => exact .falsum rfl
  | imp p q hp hq => exact .imp (hp ρ) (hq ρ) rfl
  | box p hp => exact .box (hp ρ) rfl
  | all p hp => exact .all (fun x => hp (extend ρ x)) rfl
  | equal s t hs ht => exact .equal (hs ρ) (ht ρ) rfl

def ofFull [Nonempty E] (m : Programme.«20261021-1639-ontological».Deep.Model C W E) : Model C W where
  frame := fullFrame m
  interp := m.interp
  closed := fun ρ t => ⟨eval m ρ t, full_denotes m t ρ⟩

theorem full_specialization [Nonempty E] (m : Programme.«20261021-1639-ontological».Deep.Model C W E)
    (t : Term C Γ a) (ρ : Env W E Γ) :
    translate (fullFrame m) m.interp t ρ = eval m ρ t :=
  agreement (full_denotes m t ρ)

#print axioms full_denotes
#print axioms full_specialization
#print axioms agreement
#print axioms unique
#print axioms translate_denotes
#print axioms valid_iff
#print axioms consequence_iff
end Programme.«20261021-1639-ontological».Deep.Henkin
