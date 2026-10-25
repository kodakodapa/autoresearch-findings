import Programme.«20261021-1639-ontological».Atlas.HenkinVariant2
import Programme.«20261021-1639-ontological».Atlas.Variant2Table
import Programme.«20261021-1639-ontological».Atlas.SymmetricFinite

/- Full-carrier witnesses for the CloV2 interface; not a deep Ax1Gen bridge. -/
namespace Programme.«20261021-1639-ontological».Atlas.HenkinVariant2Table
open HenkinScott HenkinVariant2

def allS {W E : Type} : ((E → W → Prop) → W → Prop) → Prop := fun _ => True

def allPos : GModel Bool Unit :=
  ⟨fun _ _ => True, fun _ _ => True, fun _ => True, fun _ => True, fun _ _ => True⟩
def free : GModel Unit Nat :=
  ⟨fun _ _ => True, fun _ _ => True, fun _ => True, fun _ => True, Variant2Table.freeP⟩

theorem allPos_clo (a : Bool) : CloV2 allPos a allS :=
  ⟨trivial, fun _ _ => trivial, trivial, fun _ _ => trivial, trivial,
    fun _ _ => trivial, trivial, fun _ _ => trivial⟩
theorem free_clo (a : Bool) : CloV2 free a allS :=
  ⟨trivial, fun _ _ => trivial, trivial, fun _ _ => trivial, trivial,
    fun _ _ => trivial, trivial, fun _ _ => trivial⟩

theorem drop_ax2a (a : Bool) :
    CloV2 allPos a allS ∧ Ax1Gen allPos a allS ∧ Ax1 allPos ∧
    Ax2b allPos ∧ Ax3 allPos a ∧ Ax4 allPos a ∧ ¬ Ax2a allPos ∧
    (∀ x w, ¬ GH allPos x w) ∧
    ¬ (∀ w v, allPos.rel w v → ∃ x, guard allPos a x v ∧ GH allPos x v) ∧
    ¬ MCadm allPos := by
  refine ⟨allPos_clo a, fun _ _ _ _ _ _ _ => trivial,
    fun _ _ _ _ _ _ _ => trivial, fun _ _ _ _ _ _ => trivial,
    fun _ => trivial, fun _ _ _ _ _ _ _ => trivial, ?_, ?_, ?_, ?_⟩
  · intro h; exact (h botP false trivial).2 ⟨trivial, trivial⟩
  · intro x w h; exact h botP trivial trivial
  · intro h; obtain ⟨x, _, hg⟩ := h false false trivial
    exact hg botP trivial trivial
  · intro h; exact Bool.noConfusion (h (fun w => w = false) trivial false rfl true trivial)

theorem free_no_god (x : Nat) (w : Unit) : ¬ GH free x w := by
  intro h
  exact Variant2Table.free_no_god x w (fun p hp => h p trivial hp)

theorem drop_ax1gen (a : Bool) :
    CloV2 free a allS ∧ Ax1 free ∧ Ax2a free ∧ Ax2b free ∧
    Ax3 free a ∧ Ax4 free a ∧ ¬ Ax1Gen free a allS ∧
    (∀ x w, ¬ GH free x w) ∧
    ¬ (∀ w v, free.rel w v → ∃ x, guard free a x v ∧ GH free x v) := by
  obtain ⟨h1, h2, h2b, _, h4, _, _, _⟩ := Variant2Table.drop_ax1gen
  have ha : Ax2a free := fun p w _ => h2 p w
  refine ⟨free_clo a, fun p q w _ _ hp hq => h1 p q w hp hq, ha,
    fun p w _ hp v hv => h2b p w hp v hv, ?_, ?_, ?_, free_no_god, ?_⟩
  · intro w
    apply FreeUltra.U_good.2.2.1 _ _ FreeUltra.U_good.1
    intro n _ p _ hp v _
    cases w; cases v
    exact ⟨n, fun _ => trivial, hp.1⟩
  · intro p q w _ _ hp hi
    exact h4 p q w hp (fun v hv y _ hy => hi v hv y (fun _ => trivial) hy)
  · intro hg
    obtain ⟨x, _, hx⟩ := god_everywhere_H (free_clo a) hg ha ()
    exact free_no_god x () hx
  · intro h
    obtain ⟨x, _, hx⟩ := h () () trivial
    exact free_no_god x () hx

theorem deletion_frames : Variant2Table.S5Frame allPos.rel ∧ Variant2Table.S5Frame free.rel :=
  ⟨⟨fun _ => trivial, fun _ _ _ => trivial, fun _ _ _ _ _ => trivial⟩,
   ⟨fun _ => trivial, fun _ _ _ => trivial, fun _ _ _ _ _ => trivial⟩⟩
def allPosFull : Programme.«20261021-1639-ontological».Countermodels.Tests.Model Bool Unit :=
  ⟨allPos.rel, allPos.actual, allPos.positive⟩
def freeFull : Programme.«20261021-1639-ontological».Countermodels.Tests.Model Unit Nat :=
  ⟨free.rel, free.actual, free.positive⟩

theorem allPos_presentation : SymmetricModels.Presents
    (SymmetricFinite.fullModel allPosFull) allPos :=
  SymmetricFinite.full_presentation allPosFull

theorem free_presentation : SymmetricModels.Presents
    (SymmetricFinite.fullModel freeFull) free :=
  SymmetricFinite.full_presentation freeFull

#print axioms allPos_presentation
#print axioms free_presentation
#print axioms drop_ax2a
#print axioms drop_ax1gen
#print axioms deletion_frames
end Programme.«20261021-1639-ontological».Atlas.HenkinVariant2Table
