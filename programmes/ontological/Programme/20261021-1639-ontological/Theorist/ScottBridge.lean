import Programme.«20261021-1639-ontological».Theorist.SymmetricModels

namespace Programme.«20261021-1639-ontological».Theorist.ScottBridge
open Programme.«20261021-1639-ontological».Deep Programme.«20261021-1639-ontological».Deep.Henkin Programme.«20261021-1639-ontological».Theorist.HenkinScott
open Programme.«20261021-1639-ontological».Theorist.SymmetricModels

variable {W : Type} (m : Henkin.Model OntConst W)

/-- Truth set of a term in a closed model (shallow translation = deep denotation, K36). -/
def sem (ρ : Assignment m.frame Γ) (t : Term OntConst Γ .prop) : W → Prop :=
  m.frame.truth (translate m.frame m.interp t ρ)

theorem deepValid_iff (ρ : Assignment m.frame Γ) (t : Term OntConst Γ .prop) :
    DeepValid m ρ t ↔ ∀ w, sem m ρ t w := (valid_iff m ρ t).symm

variable {m}

/-- What a denotation of a term records, read off the outermost constructor. -/
def Inv (m : Henkin.Model OntConst W) {Γ} (ρ : Assignment m.frame Γ) :
    {a : Ty} → Term OntConst Γ a → m.frame.D a → Prop
  | _, .falsum, r => m.frame.truth r = fun _ => False
  | _, .imp p q, r => m.frame.truth r = fun w =>
      m.frame.truth (translate m.frame m.interp p ρ) w → m.frame.truth (translate m.frame m.interp q ρ) w
  | _, .box p, r => m.frame.truth r = fun w =>
      ∀ v, m.frame.rel w v → m.frame.truth (translate m.frame m.interp p ρ) v
  | _, .all p, r => m.frame.truth r = fun w =>
      ∀ x, m.frame.truth (translate m.frame m.interp p (push ρ x)) w
  | _, .lam t, r => ∀ x, m.frame.app r x = translate m.frame m.interp t (push ρ x)
  | _, _, _ => True

theorem inv {ρ : Assignment m.frame Γ} {t : Term OntConst Γ a} {r}
    (d : Denotes m.frame m.interp @ρ t r) : Inv m ρ t r := by
  induction d with
  | var => trivial
  | const => trivial
  | app => trivial
  | lam ds _ => intro x; exact (agreement (ds x)).symm
  | falsum hp => exact hp
  | imp ds dt hr => simp only [Inv, agreement ds, agreement dt]; exact hr
  | box ds hr => simp only [Inv, agreement ds]; exact hr
  | all ds hr => simp only [Inv, fun x => agreement (ds x)]; exact hr
  | equal => trivial

theorem sem_falsum (ρ : Assignment m.frame Γ) (w : W) : sem m ρ .falsum w ↔ False :=
  Iff.of_eq (congrFun (inv (translate_denotes m ρ .falsum)) w)

theorem sem_imp (ρ : Assignment m.frame Γ) (p q : Term OntConst Γ .prop) (w : W) :
    sem m ρ (.imp p q) w ↔ (sem m ρ p w → sem m ρ q w) :=
  Iff.of_eq (congrFun (inv (translate_denotes m ρ (.imp p q))) w)

theorem sem_box (ρ : Assignment m.frame Γ) (p : Term OntConst Γ .prop) (w : W) :
    sem m ρ (.box p) w ↔ ∀ v, m.frame.rel w v → sem m ρ p v :=
  Iff.of_eq (congrFun (inv (translate_denotes m ρ (.box p))) w)

theorem sem_all (ρ : Assignment m.frame Γ) (p : Term OntConst (a :: Γ) .prop) (w : W) :
    sem m ρ (.all p) w ↔ ∀ x, sem m (push ρ x) p w :=
  Iff.of_eq (congrFun (inv (translate_denotes m ρ (.all p))) w)

theorem tr_lam (ρ : Assignment m.frame Γ) (t : Term OntConst (a :: Γ) b) (x : m.frame.D a) :
    m.frame.app (translate m.frame m.interp (.lam t) ρ) x =
      translate m.frame m.interp t (push ρ x) :=
  inv (translate_denotes m ρ (.lam t)) x


theorem sem_app (ρ : Assignment m.frame Γ) (f : Term OntConst Γ (.arr a .prop))
    (x : Term OntConst Γ a) (w : W) : sem m ρ (.app f x) w =
    m.frame.truth (m.frame.app (translate m.frame m.interp f ρ) (translate m.frame m.interp x ρ)) w := rfl

/-! ### Scott's axioms as deep terms (de Bruijn indices). -/
abbrev T := Term OntConst
def v0 : T (a :: Γ) a := .var .here
def v1 : T (b :: a :: Γ) a := .var (.there .here)
def v2 : T (c :: b :: a :: Γ) a := .var (.there (.there .here))
def neg (t : T Γ .prop) : T Γ .prop := .imp t .falsum
def conj (s t : T Γ .prop) : T Γ .prop := neg (.imp s (neg t))
def pos (t : T Γ Property) : T Γ .prop := .app (.const .positive) t
/-- Guarded implication: actualist (`a = true`) adds the actuality antecedent. -/
def gimp (a : Bool) (x : T Γ .entity) (φ : T Γ .prop) : T Γ .prop :=
  if a then .imp (.app (.const .actual) x) φ else φ

def tA1a : T [] .prop := .all (.imp (pos (.lam (neg (.app v1 v0)))) (neg (pos v0)))
def tA1b : T [] .prop := .all (.imp (neg (pos v0)) (pos (.lam (neg (.app v1 v0)))))
def tA2 (a : Bool) : T [] .prop :=
  .all (.all (.imp (pos v1) (.imp (.box (.all (gimp a v0 (.imp (.app v2 v0) (.app v1 v0))))) (pos v0))))
def tG : T [] Property := .lam (.all (.imp (pos v0) (.app v0 v1)))
def tA3 : T [] .prop := pos tG
def tA4 : T [] .prop := .all (.imp (pos v0) (.box (pos v0)))
/-- Ess P x, in context [P, x]. -/
def tEss (a : Bool) : T [Property, .entity] .prop :=
  conj (.app v0 v1) (.all (.imp (.app v0 v2) (.box (.all (gimp a v0 (.imp (.app v2 v0) (.app v1 v0)))))))
def tExA (a : Bool) : T [Property, .entity] .prop := neg (.all (gimp a v0 (neg (.app v1 v0))))
def tNE (a : Bool) : T [] Property := .lam (.all (.imp (tEss a) (.box (tExA a))))
def tA5 (a : Bool) : T [] .prop := pos (tNE a)
def tMC : T [] .prop := .all (.imp (v0 : T [.prop] .prop) (.box v0))

@[simp] theorem tr_v0 (ρ : Assignment m.frame Γ) (x : m.frame.D a) :
    translate m.frame m.interp (v0 : T (a :: Γ) a) (push ρ x) = x := rfl
@[simp] theorem tr_v1 (ρ : Assignment m.frame Γ) (x : m.frame.D a) (y : m.frame.D b) :
    translate m.frame m.interp (v1 : T (b :: a :: Γ) a) (push (push ρ x) y) = x := rfl
@[simp] theorem tr_v2 (ρ : Assignment m.frame Γ) (x : m.frame.D a) (y : m.frame.D b)
    (z : m.frame.D c) :
    translate m.frame m.interp (v2 : T (c :: b :: a :: Γ) a) (push (push (push ρ x) y) z) = x := rfl
@[simp] theorem tr_const (ρ : Assignment m.frame Γ) (k : OntConst a) :
    translate m.frame m.interp (.const k : T Γ a) ρ = m.interp k := rfl

theorem sem_neg (ρ : Assignment m.frame Γ) (t : T Γ .prop) (w : W) :
    sem m ρ (neg t) w ↔ ¬ sem m ρ t w := by
  simp only [neg, sem_imp, sem_falsum]

theorem sem_conj (ρ : Assignment m.frame Γ) (s t : T Γ .prop) (w : W) :
    sem m ρ (conj s t) w ↔ sem m ρ s w ∧ sem m ρ t w := by
  simp only [conj, sem_neg, sem_imp]; exact ⟨fun h => Classical.byContradiction fun hn =>
    h fun hs ht => hn ⟨hs, ht⟩, fun ⟨hs, ht⟩ h => h hs ht⟩

variable {gm : GModel W (m.frame.D .entity)}

theorem sem_gimp (hp : Presents m gm) (a : Bool) (ρ : Assignment m.frame Γ) (x : T Γ .entity)
    (φ : T Γ .prop) (w : W) :
    sem m ρ (gimp a x φ) w ↔ (guard gm a (translate m.frame m.interp x ρ) w → sem m ρ φ w) := by
  cases a with
  | false => simp [gimp, HenkinScott.guard]
  | true =>
    rw [show gimp true x φ = .imp (.app (.const .actual) x) φ from rfl, sem_imp, sem_app]
    simp only [HenkinScott.guard, forall_const]
    exact imp_congr_left (hp.2.2.2.1 _ w)

theorem sem_pos (hp : Presents m gm) (ρ : Assignment m.frame Γ) (t : T Γ Property) (w : W) :
    sem m ρ (pos t) w ↔
      gm.positive (fun x => m.frame.truth (m.frame.app (translate m.frame m.interp t ρ) x)) w :=
  hp.2.2.2.2 _ w

theorem img_lam (ρ : Assignment m.frame Γ) (b : T (.entity :: Γ) .prop) :
    (fun x => m.frame.truth (m.frame.app (translate m.frame m.interp (.lam b) ρ) x)) =
      fun x w => sem m (push ρ x) b w := by
  funext x; rw [tr_lam]; rfl

theorem bridge_A4 (hp : Presents m gm) (ρ : Assignment m.frame []) :
    DeepValid m ρ tA4 ↔ A4 gm := by
  rw [deepValid_iff]
  simp only [tA4, sem_all, sem_imp, sem_box, sem_pos hp]
  constructor
  · intro h p w ha hpw v hv
    obtain ⟨P, rfl⟩ := (hp.2.1 p).2 ha
    exact h w P hpw v ((hp.2.2.1 w v).2 hv)
  · intro h w P hpw v hv
    exact h _ w ((hp.2.1 _).1 ⟨P, rfl⟩) hpw v ((hp.2.2.1 w v).1 hv)

theorem bridge_MC (hp : Presents m gm) (ρ : Assignment m.frame []) :
    DeepValid m ρ tMC ↔ MCadm gm := by
  rw [deepValid_iff]
  simp only [tMC, sem_all, sem_imp, sem_box]
  constructor
  · intro h p ha w hw v hv
    obtain ⟨q, rfl⟩ := (hp.1 p).2 ha
    exact h w q hw v ((hp.2.2.1 w v).2 hv)
  · intro h w q hw v hv
    exact h _ ((hp.1 _).1 ⟨q, rfl⟩) w hw v ((hp.2.2.1 w v).1 hv)

theorem bridge_A1a (hp : Presents m gm) (ρ : Assignment m.frame []) :
    DeepValid m ρ tA1a ↔ A1a gm := by
  rw [deepValid_iff]
  simp only [tA1a, sem_all, sem_imp, sem_neg, sem_pos hp, img_lam, sem_app, tr_v0, tr_v1]
  constructor
  · intro h p w ha
    obtain ⟨P, rfl⟩ := (hp.2.1 p).2 ha
    exact h w P
  · intro h w P
    exact h _ w ((hp.2.1 _).1 ⟨P, rfl⟩)


theorem bridge_A1b (hp : Presents m gm) (ρ : Assignment m.frame []) :
    DeepValid m ρ tA1b ↔ A1b gm := by
  rw [deepValid_iff]
  simp only [tA1b, sem_all, sem_imp, sem_neg, sem_pos hp, img_lam, tr_v0, tr_v1]
  constructor
  · intro h p w ha
    obtain ⟨P, rfl⟩ := (hp.2.1 p).2 ha
    exact h w P
  · intro h w P
    exact h _ w ((hp.2.1 _).1 ⟨P, rfl⟩)

theorem bridge_A2 (hp : Presents m gm) (a : Bool) (ρ : Assignment m.frame []) :
    DeepValid m ρ (tA2 a) ↔ A2 gm a := by
  rw [deepValid_iff]
  simp only [tA2, sem_all, sem_imp, sem_box, sem_pos hp, sem_gimp hp, sem_app, tr_v0, tr_v1, tr_v2]
  constructor
  · intro h p q w hpa hqa hpw hsub
    obtain ⟨P, rfl⟩ := (hp.2.1 p).2 hpa
    obtain ⟨Q, rfl⟩ := (hp.2.1 q).2 hqa
    exact h w P Q hpw fun v hv y => hsub v ((hp.2.2.1 w v).1 hv) y
  · intro h w P Q hpw hsub
    exact h _ _ w ((hp.2.1 _).1 ⟨P, rfl⟩) ((hp.2.1 _).1 ⟨Q, rfl⟩) hpw
      fun v hv y => hsub v ((hp.2.2.1 w v).2 hv) y

/-- The deep God-like predicate has truth image `GH`. -/
theorem img_G (hp : Presents m gm) (ρ : Assignment m.frame []) :
    (fun x => m.frame.truth (m.frame.app (translate m.frame m.interp tG ρ) x)) = GH gm := by
  rw [tG, img_lam]
  funext x w
  simp only [sem_all, sem_imp, sem_pos hp, sem_app, tr_v0, tr_v1]
  apply propext
  constructor
  · intro h p ha hpw
    obtain ⟨P, rfl⟩ := (hp.2.1 p).2 ha
    exact h P hpw
  · intro h P hpw
    exact h _ ((hp.2.1 _).1 ⟨P, rfl⟩) hpw

theorem bridge_A3 (hp : Presents m gm) (ρ : Assignment m.frame []) :
    DeepValid m ρ tA3 ↔ A3 gm := by
  rw [deepValid_iff]
  simp only [tA3, sem_pos hp, img_G hp]
  rfl

theorem sem_Ess (hp : Presents m gm) (a : Bool) (ρ : Assignment m.frame [])
    (x : m.frame.D .entity) (P : m.frame.D Property) (w : W) :
    sem m (push (push ρ x) P) (tEss a) w ↔
      EssH gm a (fun y => m.frame.truth (m.frame.app P y)) x w := by
  simp only [tEss, sem_conj, sem_all, sem_imp, sem_box, sem_gimp hp, sem_app, tr_v0, tr_v1, tr_v2]
  refine and_congr Iff.rfl ⟨fun h q ha hqx v hv y => ?_, fun h Q hqx v hv y => ?_⟩
  · obtain ⟨Q, rfl⟩ := (hp.2.1 q).2 ha
    exact h Q hqx v ((hp.2.2.1 w v).2 hv) y
  · exact h _ ((hp.2.1 _).1 ⟨Q, rfl⟩) hqx v ((hp.2.2.1 w v).1 hv) y

theorem sem_ExA (hp : Presents m gm) (a : Bool) (ρ : Assignment m.frame [])
    (x : m.frame.D .entity) (P : m.frame.D Property) (v : W) :
    sem m (push (push ρ x) P) (tExA a) v ↔
      ∃ y, guard gm a y v ∧ m.frame.truth (m.frame.app P y) v := by
  simp only [tExA, sem_neg, sem_all, sem_gimp hp, sem_app, tr_v0, tr_v1]
  exact ⟨fun h => Classical.byContradiction fun hn => h fun y hy hpy => hn ⟨y, hy, hpy⟩,
    fun ⟨y, hy, hpy⟩ h => h y hy hpy⟩

/-- The deep necessary-existence predicate has truth image `NEH`. -/
theorem img_NE (hp : Presents m gm) (a : Bool) (ρ : Assignment m.frame []) :
    (fun x => m.frame.truth (m.frame.app (translate m.frame m.interp (tNE a) ρ) x)) =
      NEH gm a := by
  rw [tNE, img_lam]
  funext x w
  simp only [sem_all, sem_imp, sem_box, sem_Ess hp, sem_ExA hp]
  apply propext
  constructor
  · intro h p ha hess v hv
    obtain ⟨P, rfl⟩ := (hp.2.1 p).2 ha
    exact h P hess v ((hp.2.2.1 w v).2 hv)
  · intro h P hess v hv
    exact h _ ((hp.2.1 _).1 ⟨P, rfl⟩) hess v ((hp.2.2.1 w v).1 hv)

theorem bridge_A5 (hp : Presents m gm) (a : Bool) (ρ : Assignment m.frame []) :
    DeepValid m ρ (tA5 a) ↔ A5 gm a := by
  rw [deepValid_iff]
  simp only [tA5, sem_pos hp, img_NE hp]
  rfl

#print axioms bridge_A1a
#print axioms bridge_A1b
#print axioms bridge_A2
#print axioms bridge_A3
#print axioms bridge_A4
#print axioms bridge_A5
#print axioms bridge_MC
end Programme.«20261021-1639-ontological».Theorist.ScottBridge
