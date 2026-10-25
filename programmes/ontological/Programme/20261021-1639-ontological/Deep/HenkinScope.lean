import Programme.«20261021-1639-ontological».Deep.Henkin

namespace Programme.«20261021-1639-ontological».Deep.Henkin

def Clause (h : Frame W) (I : ∀ {a}, C a → h.D a) (ρ : Assignment h Γ) :
    (t : Term C Γ a) → h.D a → Prop
  | .falsum, v => h.truth v = fun _ => False
  | .box t, v => h.truth v = fun w => ∀ u, h.rel w u → h.truth (translate h I t ρ) u
  | .imp s t, v => h.truth v = fun w =>
      h.truth (translate h I s ρ) w → h.truth (translate h I t ρ) w
  | .all t, v => h.truth v = fun w => ∀ x, h.truth (translate h I t (push ρ x)) w
  | .equal s t, v => h.truth v = fun _ => translate h I s ρ = translate h I t ρ
  | .lam t, v => ∀ x, h.app v x = translate h I t (push ρ x)
  | _, _ => True

theorem denotes_clause (d : Denotes h I ρ t v) : Clause h I ρ t v := by
  induction d with
  | var => trivial
  | const => trivial
  | app _ _ _ _ => trivial
  | lam ds _ => exact fun x => (agreement (ds x)).symm
  | falsum hp => exact hp
  | imp ds dt hr _ _ => simpa only [Clause, agreement ds, agreement dt] using hr
  | box dt hq _ => simpa only [Clause, agreement dt] using hq
  | all ds hr _ => simpa only [Clause, agreement (ds _)] using hr
  | equal ds dt hr _ _ => simpa only [Clause, agreement ds, agreement dt] using hr

theorem truth_imp (m : Model C W) (ρ : Assignment m.frame Γ)
    (s t : Term C Γ .prop) :
    m.frame.truth (translate m.frame m.interp (.imp s t) ρ) =
      fun w => m.frame.truth (translate m.frame m.interp s ρ) w →
        m.frame.truth (translate m.frame m.interp t ρ) w :=
  denotes_clause (translate_denotes m ρ (.imp s t))

theorem truth_all (m : Model C W) (ρ : Assignment m.frame Γ)
    (t : Term C (a :: Γ) .prop) :
    m.frame.truth (translate m.frame m.interp (.all t) ρ) =
      fun w => ∀ x, m.frame.truth (translate m.frame m.interp t (push ρ x)) w :=
  denotes_clause (translate_denotes m ρ (.all t))

theorem truth_equal (m : Model C W) (ρ : Assignment m.frame Γ)
    (s t : Term C Γ a) :
    m.frame.truth (translate m.frame m.interp (.equal s t) ρ) =
      fun _ => translate m.frame m.interp s ρ = translate m.frame m.interp t ρ :=
  denotes_clause (translate_denotes m ρ (.equal s t))

/-- Actuality is an admitted property, and its guard is evaluated at the current world. -/
theorem actualist_agreement (m : Model OntConst W) (ρ : Assignment m.frame Γ)
    (p : Term OntConst (.entity :: Γ) .prop) (w : W) :
    m.frame.truth (translate m.frame m.interp (allActual p) ρ) w ↔
      ∀ x, m.frame.truth (m.frame.app (m.interp OntConst.actual) x) w →
        m.frame.truth (translate m.frame m.interp p (push ρ x)) w := by
  change m.frame.truth (translate m.frame m.interp (.all _) ρ) w ↔ _
  rw [truth_all]
  simp only [truth_imp]
  rfl

/-- Closure for lambda and primitive equality forces admitted predicates to separate
any two elements, even though the predicate carrier need not be the full function space. -/
theorem separating_predicate (m : Model C W) (x : m.frame.D a) :
    ∃ p : m.frame.D (.arr a .prop),
      ∀ y w, m.frame.truth (m.frame.app p y) w ↔ y = x := by
  let ρ : Assignment m.frame [a] := fun {b} v => by
    cases v with
    | here => exact x
    | there v => cases v
  let t : Term C [a] (.arr a .prop) :=
    .lam (.equal (.var .here) (.var (.there .here)))
  obtain ⟨p, hp⟩ := m.closed ρ t
  refine ⟨p, ?_⟩
  intro y w
  have eqn := denotes_clause hp y
  rw [eqn, truth_equal]
  rfl

/-- Leibniz equality quantifies only over admitted predicates. Primitive equality
and lambda closure suffice for equivalence; no full predicate domain is assumed. -/
theorem leibniz_iff (m : Model C W) (x y : m.frame.D a) (w : W) :
    (∀ p : m.frame.D (.arr a .prop),
      m.frame.truth (m.frame.app p x) w → m.frame.truth (m.frame.app p y) w) ↔ x = y := by
  constructor
  · intro h
    obtain ⟨p, hp⟩ := separating_predicate m x
    exact ((hp y w).mp (h p ((hp x w).mpr rfl))).symm
  · intro h
    subst y
    exact fun _ hx => hx

#print axioms actualist_agreement
#print axioms separating_predicate
#print axioms leibniz_iff
end Programme.«20261021-1639-ontological».Deep.Henkin
