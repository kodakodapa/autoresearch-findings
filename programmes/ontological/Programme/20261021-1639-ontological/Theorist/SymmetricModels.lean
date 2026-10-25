import Programme.«20261021-1639-ontological».Theorist.SymmetricClosure
import Programme.«20261021-1639-ontological».Skeptic.TernSymmetry

/-! The three infinite D14 witnesses (`cantor`, `cantorCW`, `tern` from HenkinScott /
HenkinMinimal, K49) are truth-image presentations of definably closed K36 Henkin models.

Generic part: for a symmetry datum on `W` with entity type `Unit`, universal accessibility,
actuality ⊤ and an equivariant positivity constant, `SymmetricClosure.model` is a K36
`Henkin.Model OntConst W` (closure under every term proved). Its admitted propositions and
properties are exactly the symmetric ones. Specific part: binary xor masks (Cantor) and ternary
coordinate shifts (sk's `TernSymmetry`, copied) with the tail stabilisers `K n`; symmetric sets are
exactly `Based n` / `Based3 n`, so the admitted carriers, accessibility and actuality coincide
with those of `cantor`, `cantorCW`, `tern`, and positivity coincides on every admitted property.
Since the GModel axioms only apply `positive` to admitted properties, the K49 deletion witnesses
for A1b, A4 and A3 are presentations of closed Henkin models. -/

namespace Programme.«20261021-1639-ontological».Theorist.SymmetricModels
open Programme.«20261021-1639-ontological».Deep Programme.«20261021-1639-ontological».Deep.Henkin Programme.«20261021-1639-ontological».Theorist.SymmetricClosure
open Programme.«20261021-1639-ontological».Theorist.HenkinScott Programme.«20261021-1639-ontological».Theorist.HenkinMinimal

variable {W : Type} (S : Sym W Unit)

/-- Actuality ⊤ as a symmetric property. -/
def topProperty : (car S Property).T :=
  ⟨fun _ => ⟨fun _ => True, 0, fun _ _ _ => rfl⟩, 0, fun _ _ _ => rfl⟩

/-- Truth image of a property element. -/
def propT (f : (car S Property).T) : Unit → W → Prop := fun x w => (f.1 x).1 w

/-- A rigid positivity constant from a predicate on truth images invariant under the group. -/
def rigidPos (pos : (Unit → W → Prop) → Prop)
    (hpos : ∀ g f, pos (propT S ((car S Property).act g f)) = pos (propT S f)) :
    (car S (.arr Property .prop)).T :=
  ⟨fun f => ⟨fun _ => pos (propT S f), 0, fun _ _ _ => rfl⟩, 0, fun g _ f =>
    Subtype.ext (funext fun _ => hpos g f)⟩

/-- Current-world positivity: a property is positive at `w` iff it holds of `()` at `w`. -/
def cwPos : (car S (.arr Property .prop)).T :=
  ⟨fun f => f.1 (), 0, fun _ _ _ => rfl⟩

def interp (pos : (car S (.arr Property .prop)).T) : ∀ {a}, OntConst a → (car S a).T
  | _, .actual => topProperty S
  | _, .positive => pos

variable {S}

theorem interp_inv (hK0 : ∀ g, S.K 0 g) (pos : (car S (.arr Property .prop)).T)
    (hp : Equi (car S Property) (car S .prop) 0 pos.1) :
    ∀ {a} (c : OntConst a) g, (car S a).act g (interp S pos c) = interp S pos c := by
  intro a c g
  cases c with
  | actual => exact fix_of_equi (entCar S) (car S .prop) (topProperty S) (fun _ _ _ => rfl) g (hK0 g)
  | positive => exact fix_of_equi (car S Property) (car S .prop) pos hp g (hK0 g)

variable (S)

/-- The closed symmetric Henkin model with universal accessibility. -/
noncomputable def unitModel (hK0 : ∀ g, S.K 0 g) (pos : (car S (.arr Property .prop)).T)
    (hp : Equi (car S Property) (car S .prop) 0 pos.1) : Henkin.Model OntConst W :=
  model (R := fun _ _ => True) (interp S pos) (fun _ _ _ => Iff.rfl) (interp_inv hK0 pos hp)

variable {S}

theorem unit_property_iff (f : Unit → W → Prop) :
    (∃ P : (car S Property).T, propT S P = f) ↔ SymProp S (f ()) := by
  constructor
  · rintro ⟨P, rfl⟩; exact (P.1 ()).2
  · intro h
    let q : (car S .prop).T := ⟨f (), h⟩
    obtain ⟨n, hn⟩ := typed_fix (S := S) .prop q
    refine ⟨⟨fun _ => q, n, fun g hg _ => (hn g hg).symm⟩, ?_⟩
    funext x w; cases x; rfl

/-- Presentation of `unitModel`: carriers, accessibility, actuality and positivity. -/
theorem presentation (hK0 : ∀ g, S.K 0 g) (pos : (car S (.arr Property .prop)).T)
    (hp : Equi (car S Property) (car S .prop) 0 pos.1) :
    let m := unitModel S hK0 pos hp
    (∀ p : W → Prop, (∃ q : m.frame.D .prop, m.frame.truth q = p) ↔ SymProp S p) ∧
    (∀ f : Unit → W → Prop,
      (∃ P : m.frame.D Property, (fun x => m.frame.truth (m.frame.app P x)) = f) ↔
        SymProp S (f ())) ∧
    (∀ w v, m.frame.rel w v) ∧
    (fun x => m.frame.truth (m.frame.app (m.interp OntConst.actual) x)) = (fun _ _ => True) ∧
    (∀ P : m.frame.D Property,
      m.frame.truth (m.frame.app (m.interp OntConst.positive) P) = (pos.1 P).1) :=
  ⟨fun p => admitted_iff p, fun f => unit_property_iff f, fun _ _ => trivial, rfl,
    fun _ => rfl⟩

/-- `gm` is the truth-image presentation of the Henkin model `m` (as r1's K45 `toGModel`):
same admitted propositions and properties, accessibility and actuality, and positivity agreeing
on every admitted property. -/
def Presents (m : Henkin.Model OntConst W) (gm : GModel W (m.frame.D .entity)) : Prop :=
  (∀ p, (∃ q : m.frame.D .prop, m.frame.truth q = p) ↔ gm.admP p) ∧
  (∀ f, (∃ P : m.frame.D Property, (fun x => m.frame.truth (m.frame.app P x)) = f) ↔ gm.adm f) ∧
  (∀ w v, m.frame.rel w v ↔ gm.rel w v) ∧
  (∀ x w, m.frame.truth (m.frame.app (m.interp OntConst.actual) x) w ↔ gm.actual x w) ∧
  (∀ P : m.frame.D Property, ∀ w, m.frame.truth (m.frame.app (m.interp OntConst.positive) P) w ↔
    gm.positive (fun x => m.frame.truth (m.frame.app P x)) w)

/-! ### Binary xor masks. -/

def mask (g v : Wc) : Wc := fun k => xor (v k) (g k)

def bsym : Sym Wc Unit where
  G := Wc
  mul g h := fun k => xor (g k) (h k)
  inv g := g
  aw := mask
  ae _ x := x
  aw_mul g h w := by
    funext k; simp only [mask]
    generalize w k = a; generalize g k = b; generalize h k = c; revert a b c; decide
  ae_mul _ _ _ := rfl
  aw_inv g w := by
    funext k; simp only [mask]; generalize w k = a; generalize g k = b; revert a b; decide
  aw_inv' g w := by
    funext k; simp only [mask]; generalize w k = a; generalize g k = b; revert a b; decide
  ae_inv _ _ := rfl
  ae_inv' _ _ := rfl
  K n g := ∀ k, k < n → g k = false
  anti hnm h k hk := h k (Nat.lt_of_lt_of_le hk hnm)
  normal g n := ⟨n, fun h hh k hk => by
    show xor (g k) (xor (h k) (g k)) = false
    rw [hh k hk]; generalize g k = a; revert a; decide⟩
  ent_supp _ := ⟨0, fun _ _ => rfl⟩

theorem bsym_K0 : ∀ g, bsym.K 0 g := fun _ _ hk => absurd hk (Nat.not_lt_zero _)

theorem symProp_bsym (p : Wc → Prop) : SymProp bsym p ↔ ∃ n, Based n p := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, fun v v' hag => ?_⟩
    let g : Wc := fun k => xor (v k) (v' k)
    have hg : bsym.K n g := fun k hk => by
      show xor (v k) (v' k) = false
      rw [hag k hk]; generalize v' k = a; revert a; decide
    have e : mask g v = v' := by
      funext k; simp only [mask, g]
      generalize v k = a; generalize v' k = b; revert a b; decide
    rw [← e]; exact Iff.of_eq (hn g hg v).symm
  · rintro ⟨n, hb⟩
    refine ⟨n, fun g hg w => propext (hb _ _ fun k hk => ?_)⟩
    show xor (w k) (g k) = w k
    rw [hg k hk]; generalize w k = a; revert a; decide

/-- Necessity positivity (`cantor`) is invariant: masks are bijections of worlds. -/
theorem nec_inv : ∀ (g : bsym.G) (f : (car bsym Property).T),
    (∀ v, propT bsym ((car bsym Property).act g f) () v) = (∀ v, propT bsym f () v) := by
  intro g f
  apply propext; constructor
  · intro h v
    have := h (bsym.aw g v)
    show (f.1 ()).1 v
    have e : bsym.aw (bsym.inv g) (bsym.aw g v) = v := bsym.aw_inv g v
    simpa only [propT, e] using this
  · intro h v; exact h _

noncomputable def cantorModel : Henkin.Model OntConst Wc :=
  unitModel bsym bsym_K0 (rigidPos bsym (fun f => ∀ v, f () v) nec_inv) (fun g _ f =>
    Subtype.ext (funext fun _ => nec_inv g f))

noncomputable def cantorCWModel : Henkin.Model OntConst Wc :=
  unitModel bsym bsym_K0 (cwPos bsym) (fun _ _ _ => rfl)

/-- `cantor` presents a closed Henkin model: same admitted carriers, accessibility, actuality,
and positivity on every admitted property. -/
theorem cantor_presentation : Presents cantorModel cantor := by
  obtain ⟨h1, h2, _, _, _⟩ := presentation bsym_K0
    (rigidPos bsym (fun f => ∀ v, f () v) nec_inv) (fun g _ f =>
    Subtype.ext (funext fun _ => nec_inv g f))
  exact ⟨fun p => (h1 p).trans (symProp_bsym p), fun f => (h2 f).trans (symProp_bsym _),
    fun _ _ => iff_of_true trivial trivial, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩

theorem cantorCW_presentation : Presents cantorCWModel cantorCW := by
  obtain ⟨h1, h2, _, _, _⟩ := presentation bsym_K0 (cwPos bsym) (fun _ _ _ => rfl)
  exact ⟨fun p => (h1 p).trans (symProp_bsym p), fun f => (h2 f).trans (symProp_bsym _),
    fun _ _ => iff_of_true trivial trivial, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩

/-! ### Ternary coordinate shifts. -/
open Programme.«20261021-1639-ontological».Skeptic.TernSymmetry

def tsym : Sym W3 Unit where
  G := W3
  mul g h := fun k => g k + h k
  inv g := fun k => 0 - g k
  aw := shift
  ae _ x := x
  aw_mul g h w := by
    funext k; simp only [shift]
    generalize w k = a; generalize g k = b; generalize h k = c; revert a b c; decide
  ae_mul _ _ _ := rfl
  aw_inv g w := by
    funext k; simp only [shift]; generalize w k = a; generalize g k = b; revert a b; decide
  aw_inv' g w := by
    funext k; simp only [shift]; generalize w k = a; generalize g k = b; revert a b; decide
  ae_inv _ _ := rfl
  ae_inv' _ _ := rfl
  K n g := ∀ k, k < n → g k = 0
  anti hnm h k hk := h k (Nat.lt_of_lt_of_le hk hnm)
  normal g n := ⟨n, fun h hh k hk => by
    show (0 - g k) + (h k + g k) = 0
    rw [hh k hk]; generalize g k = a; revert a; decide⟩
  ent_supp _ := ⟨0, fun _ _ => rfl⟩

theorem tsym_K0 : ∀ g, tsym.K 0 g := fun _ _ hk => absurd hk (Nat.not_lt_zero _)

theorem symProp_tsym (p : W3 → Prop) : SymProp tsym p ↔ ∃ n, Based3 n p := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, (based3_iff_shifts n p).2 fun m hm v => Iff.of_eq (hn m hm v)⟩
  · rintro ⟨n, hb⟩
    exact ⟨n, fun g hg w => propext ((based3_iff_shifts n p).1 hb g hg w)⟩

/-- Recursive ternary majority is invariant under every shift (sk's `pos3_shift`). -/
theorem pos3_inv : ∀ (g : tsym.G) (f : (car tsym Property).T),
    pos3 (propT tsym ((car tsym Property).act g f) ()) = pos3 (propT tsym f ()) := by
  intro g f
  obtain ⟨n, hb⟩ := (symProp_tsym _).1 (f.1 ()).2
  exact propext (pos3_shift (tsym.inv g) _ n hb)

noncomputable def ternModel : Henkin.Model OntConst W3 :=
  unitModel tsym tsym_K0 (rigidPos tsym (fun f => pos3 (f ())) pos3_inv) (fun g _ f =>
    Subtype.ext (funext fun _ => pos3_inv g f))

theorem tern_presentation : Presents ternModel tern := by
  obtain ⟨h1, h2, _, _, _⟩ := presentation tsym_K0
    (rigidPos tsym (fun f => pos3 (f ())) pos3_inv) (fun g _ f =>
    Subtype.ext (funext fun _ => pos3_inv g f))
  exact ⟨fun p => (h1 p).trans (symProp_tsym p), fun f => (h2 f).trans (symProp_tsym _),
    fun _ _ => iff_of_true trivial trivial, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩

/-- K49's three infinite deletion witnesses, each paired with its closed Henkin model. -/
theorem closed_drop_A1b (a : Bool) : Presents cantorModel cantor ∧
    Clo3 cantor a ∧ Symm cantor ∧ A1a cantor ∧ ¬ A1b cantor ∧ A2 cantor a ∧ A3 cantor ∧
    A4 cantor ∧ A5 cantor a ∧ ¬ MCadm cantor := And.intro cantor_presentation (henkin_drop_A1b a)
theorem closed_drop_A4 (a : Bool) : Presents cantorCWModel cantorCW ∧
    Clo3 cantorCW a ∧ Symm cantorCW ∧ A1a cantorCW ∧ A1b cantorCW ∧ A2 cantorCW a ∧
    A3 cantorCW ∧ ¬ A4 cantorCW ∧ A5 cantorCW a ∧ ¬ MCadm cantorCW := And.intro cantorCW_presentation (henkin_drop_A4 a)
theorem closed_drop_A3 (a : Bool) : Presents ternModel tern ∧
    Clo3 tern a ∧ Symm tern ∧ A1a tern ∧ A1b tern ∧ A2 tern a ∧ ¬ A3 tern ∧ A4 tern ∧
    A5 tern a ∧ ¬ MCadm tern := And.intro tern_presentation (henkin_drop_A3 a)

#print axioms closed_drop_A1b
#print axioms closed_drop_A4
#print axioms closed_drop_A3
#print axioms cantor_presentation
#print axioms cantorCW_presentation
#print axioms tern_presentation
end Programme.«20261021-1639-ontological».Theorist.SymmetricModels
