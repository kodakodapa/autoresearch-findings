-- Rebased from th P252/P267; TernSymmetry proof by sk.
import Programme.«20261021-1639-ontological».Atlas.SymmetricModels
import Programme.«20261021-1639-ontological».Atlas.HenkinVariant2

/-! The remaining finite witnesses as presentations of closed K36 Henkin models, via the
generic symmetric closure (`SymmetricClosure.model`) with an arbitrary invariant accessibility
relation and arbitrary invariant actuality/positivity constants.

* Trivial group (`trivSym`): every carrier is the full function space, so every proposition
  and property is admitted. Any `ScottTable.Model` with nonempty entities is the presentation of
  a closed Henkin model (`full_presentation`); in particular the three D7 deletion witnesses
  behind K49's `henkin_drop_A1a/A2/A5` (`closed_drop_A1a/A2/A5`).
* Swap group on `Bool` (`swapSym`, `K n` = whole group), `R = ≠`, current-world positivity:
  D15's `swap` GModel is the presentation (`swap_presentation`), and every higher predicate of
  the closed model has a truth image in `swapS` (`swap_higher`), so the Ax1Gen quantifier of
  `swap_props` ranges over a superset of the deep higher-predicate carrier. -/

namespace Programme.«20261021-1639-ontological».Atlas.SymmetricFinite
open Programme.«20261021-1639-ontological».Deep Programme.«20261021-1639-ontological».Deep.Henkin Programme.«20261021-1639-ontological».Atlas.SymmetricClosure
open Programme.«20261021-1639-ontological».Atlas.HenkinScott Programme.«20261021-1639-ontological».Atlas.HenkinMinimal
open Programme.«20261021-1639-ontological».Atlas.SymmetricModels

variable {W E : Type}

/-- Interpretation from an actuality and a positivity element. -/
def interp2 (S : Sym W E) (act : (car S Property).T) (pos : (car S (.arr Property .prop)).T) :
    ∀ {a}, OntConst a → (car S a).T
  | _, .actual => act
  | _, .positive => pos

/-- Truth image of a property element, for any entity type. -/
def propE (S : Sym W E) (f : (car S Property).T) : E → W → Prop := fun x w => (f.1 x).1 w

/-! ### Trivial group: full carriers. -/

def trivSym (W E : Type) : Sym W E where
  G := Unit
  mul _ _ := ()
  inv _ := ()
  aw _ w := w
  ae _ x := x
  aw_mul _ _ _ := rfl
  ae_mul _ _ _ := rfl
  aw_inv _ _ := rfl
  aw_inv' _ _ := rfl
  ae_inv _ _ := rfl
  ae_inv' _ _ := rfl
  K _ _ := True
  anti _ _ := trivial
  normal _ _ := ⟨0, fun _ _ => trivial⟩
  ent_supp _ := ⟨0, fun _ _ => rfl⟩

theorem triv_act : ∀ (a : Ty) (g : (trivSym W E).G) (x : (car (trivSym W E) a).T),
    (car (trivSym W E) a).act g x = x
  | .entity, _, _ => rfl
  | .prop, _, _ => rfl
  | .arr a b, g, f => Subtype.ext (funext fun x => by
      show (car (trivSym W E) b).act g (f.1 ((car (trivSym W E) a).act ((trivSym W E).inv g) x)) = f.1 x
      rw [triv_act a, triv_act b])

theorem triv_equi (a b : Ty) (n : Nat) (f : (car (trivSym W E) a).T → (car (trivSym W E) b).T) :
    Equi (car (trivSym W E) a) (car (trivSym W E) b) n f := fun g _ x => by
  rw [triv_act a, triv_act b]

def triv_mk {a b : Ty} (f : (car (trivSym W E) a).T → (car (trivSym W E) b).T) :
    (car (trivSym W E) (.arr a b)).T := ⟨f, 0, triv_equi a b 0 f⟩

def trivProp (p : W → Prop) : (car (trivSym W E) .prop).T :=
  ⟨p, 0, fun _ _ _ => rfl⟩

theorem triv_symProp (p : W → Prop) : SymProp (trivSym W E) p := ⟨0, fun _ _ _ => rfl⟩

/-- Full model data as interpretation constants. -/
def fullAct (m : Programme.«20261021-1639-ontological».Countermodels.Tests.Model W E) : (car (trivSym W E) Property).T :=
  triv_mk (a := .entity) (b := .prop) fun x => trivProp (m.actual x)
def fullPos (m : Programme.«20261021-1639-ontological».Countermodels.Tests.Model W E) : (car (trivSym W E) (.arr Property .prop)).T :=
  triv_mk (a := Property) (b := .prop) fun f => trivProp (m.positive (propE _ f))

noncomputable def fullModel [Nonempty E] (m : Programme.«20261021-1639-ontological».Countermodels.Tests.Model W E) : Henkin.Model OntConst W :=
  model (S := trivSym W E) (R := m.rel) (interp2 _ (fullAct m) (fullPos m))
    (fun _ _ _ => Iff.rfl) (fun {a} _ g => triv_act a g _)

theorem full_presentation [Nonempty E] (m : Programme.«20261021-1639-ontological».Countermodels.Tests.Model W E) :
    Presents (fullModel m) (full m) := by
  refine ⟨fun p => iff_of_true ((admitted_iff p).2 (triv_symProp p)) trivial,
    fun f => iff_of_true ⟨triv_mk (a := .entity) (b := .prop) fun x => trivProp (f x), rfl⟩ trivial,
    fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩

/-- K49's three finite deletion witnesses, each paired with its closed Henkin model. -/
theorem closed_drop_A1a (a : Bool) :
    Presents (fullModel ScottTable.allPos) (full ScottTable.allPos) ∧
    Clo3 (full ScottTable.allPos) a ∧ Symm (full ScottTable.allPos) ∧
    ¬ A1a (full ScottTable.allPos) ∧ A1b (full ScottTable.allPos) ∧
    A2 (full ScottTable.allPos) a ∧ A3 (full ScottTable.allPos) ∧ A4 (full ScottTable.allPos) ∧
    A5 (full ScottTable.allPos) a ∧ ¬ MCadm (full ScottTable.allPos) :=
  ⟨full_presentation _, henkin_drop_A1a a⟩
theorem closed_drop_A2 (a : Bool) :
    Presents (fullModel ScottTable.twoPos) (full ScottTable.twoPos) ∧
    Clo3 (full ScottTable.twoPos) a ∧ Symm (full ScottTable.twoPos) ∧
    A1a (full ScottTable.twoPos) ∧ A1b (full ScottTable.twoPos) ∧
    ¬ A2 (full ScottTable.twoPos) a ∧ A3 (full ScottTable.twoPos) ∧ A4 (full ScottTable.twoPos) ∧
    A5 (full ScottTable.twoPos) a ∧ ¬ MCadm (full ScottTable.twoPos) :=
  ⟨full_presentation _, henkin_drop_A2 a⟩
theorem closed_drop_A5 (a : Bool) :
    Presents (fullModel ScottTable.princ) (full ScottTable.princ) ∧
    Clo3 (full ScottTable.princ) a ∧ Symm (full ScottTable.princ) ∧
    A1a (full ScottTable.princ) ∧ A1b (full ScottTable.princ) ∧
    A2 (full ScottTable.princ) a ∧ A3 (full ScottTable.princ) ∧ A4 (full ScottTable.princ) ∧
    ¬ A5 (full ScottTable.princ) a ∧ ¬ MCadm (full ScottTable.princ) :=
  ⟨full_presentation _, henkin_drop_A5 a⟩

/-! ### Swap group on two worlds. -/

def swapSym : Sym Bool Unit where
  G := Bool
  mul g h := xor g h
  inv g := g
  aw g w := xor w g
  ae _ x := x
  aw_mul g h w := by revert g h w; decide
  ae_mul _ _ _ := rfl
  aw_inv g w := by revert g w; decide
  aw_inv' g w := by revert g w; decide
  ae_inv _ _ := rfl
  ae_inv' _ _ := rfl
  K _ _ := True
  anti _ _ := trivial
  normal _ _ := ⟨0, fun _ _ => trivial⟩
  ent_supp _ := ⟨0, fun _ _ => rfl⟩

theorem swapSym_K0 : ∀ g, swapSym.K 0 g := fun _ => trivial

theorem symProp_swap (p : Bool → Prop) : SymProp swapSym p ↔ (p true ↔ p false) := by
  constructor
  · rintro ⟨n, hn⟩
    exact Iff.of_eq (hn true trivial false)
  · intro h
    refine ⟨0, fun g _ w => propext ?_⟩
    cases g <;> cases w <;> simp [swapSym, h]

theorem swapRel_inv : ∀ g w v, (swapSym.aw g v ≠ swapSym.aw g w) ↔ (v ≠ w) := by
  intro g w v
  show (xor v g ≠ xor w g) ↔ (v ≠ w)
  cases g <;> cases w <;> cases v <;> decide

noncomputable def swapModel : Henkin.Model OntConst Bool :=
  model (S := swapSym) (R := fun w v => v ≠ w) (SymmetricModels.interp swapSym (cwPos swapSym))
    swapRel_inv (interp_inv swapSym_K0 (cwPos swapSym) (fun _ _ _ => rfl))

open Programme.«20261021-1639-ontological».Atlas.HenkinVariant2 in
theorem swap_presentation : Presents swapModel swap := by
  refine ⟨fun p => (admitted_iff p).trans (symProp_swap p), fun f => ?_,
    fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩
  exact (unit_property_iff (S := swapSym) f).trans (symProp_swap _)

open Programme.«20261021-1639-ontological».Atlas.HenkinVariant2 in
/-- Every closed-model higher predicate is swap-invariant on admitted properties: its truth
image lies in `swapS`, the higher-predicate range used by `swap_props`. -/
theorem swap_higher (s : (car swapSym (.arr Property .prop)).T) :
    swapS (fun q w => ∃ Q : (car swapSym Property).T, propT swapSym Q = q ∧ (s.1 Q).1 w) := by
  intro q _
  have key : ∀ Q : (car swapSym Property).T, (s.1 Q).1 true ↔ (s.1 Q).1 false := by
    intro Q
    obtain ⟨n, hn⟩ := (s.1 Q).2
    exact Iff.of_eq (hn true trivial false)
  exact ⟨fun ⟨Q, hQ, h⟩ => ⟨Q, hQ, (key Q).1 h⟩, fun ⟨Q, hQ, h⟩ => ⟨Q, hQ, (key Q).2 h⟩⟩

open Programme.«20261021-1639-ontological».Atlas.HenkinVariant2 in
/-- D15's irreflexive witness paired with its closed Henkin model. -/
theorem closed_swap (a : Bool) : Presents swapModel swap ∧
    (∀ s : (car swapSym (.arr Property .prop)).T,
      swapS (fun q w => ∃ Q : (car swapSym Property).T, propT swapSym Q = q ∧ (s.1 Q).1 w)) ∧
    CloV2 swap a swapS ∧ Ax1Gen swap a swapS ∧ Ax2a swap ∧ Ax2b swap ∧ Ax3 swap a ∧
    Ax1 swap ∧ Ax4 swap a ∧ (∀ w v, swap.rel w v → swap.rel v w) ∧
    (∀ w, ¬ swap.rel w w) ∧ MCadm swap :=
  ⟨swap_presentation, swap_higher, swap_props a⟩

#print axioms full_presentation
#print axioms closed_drop_A1a
#print axioms closed_drop_A2
#print axioms closed_drop_A5
#print axioms swap_presentation
#print axioms swap_higher
#print axioms closed_swap
end Programme.«20261021-1639-ontological».Atlas.SymmetricFinite
