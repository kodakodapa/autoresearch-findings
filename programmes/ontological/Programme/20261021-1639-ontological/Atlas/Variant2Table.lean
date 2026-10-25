import Programme.«20261021-1639-ontological».Atlas.Variant2Split
import Programme.«20261021-1639-ontological».Atlas.FreeUltra

/- Full-intension deletion witnesses. Uses the free ultrafilter constructed by th,
rebased in FreeUltra; no finite-model claim is made for the Ax1Gen deletion. -/
namespace Programme.«20261021-1639-ontological».Atlas.Variant2Table
open Programme.«20261021-1639-ontological».Atlas.Variant2 Programme.«20261021-1639-ontological».Atlas.Variant2Split
open Programme.«20261021-1639-ontological».Atlas.FreeUltra Programme.«20261021-1639-ontological».Atlas.PrincipalAxis

def totalR : Bool → Bool → Prop := fun _ _ => True
def allGuard {E W : Type} : E → W → Prop := fun _ _ => True
def allPositive : (Unit → Bool → Prop) → Bool → Prop := fun _ _ => True

theorem drop_ax2a :
    Ax1 allPositive ∧ Ax1Gen totalR allGuard allPositive ∧
    Ax2b totalR allPositive ∧ Ax3 totalR allGuard allGuard allPositive ∧
    Ax4 totalR allGuard allPositive ∧ ¬ Ax2a allPositive ∧
    (∀ x w, ¬ God allPositive x w) ∧ ¬ Th5 totalR allGuard allPositive ∧ ¬ MC totalR := by
  refine ⟨fun _ _ _ _ _ => trivial, fun _ _ _ _ => trivial,
    fun _ _ _ _ _ => trivial, fun _ => trivial, fun _ _ _ _ _ => trivial,
    fun h => (h bot false).2 ⟨trivial, trivial⟩,
    fun _ _ h => h bot trivial, ?_, ?_⟩
  · intro h
    obtain ⟨x, _, hg⟩ := h false false trivial
    exact hg bot trivial
  · intro h
    exact Bool.noConfusion (h (fun w => w = false) false rfl true trivial)

-- A singleton S5 frame; the infinite domain is essential to this free-ultrafilter witness.
def oneR : Unit → Unit → Prop := fun _ _ => True
def freeP : (Nat → Unit → Prop) → Unit → Prop := fun p w => U (fun n => p n w)

theorem free_no_god (x : Nat) (w : Unit) : ¬ God freeP x w := by
  intro h
  exact h (fun n _ => n ≠ x) (U_frechet _ (cof_ne x)) rfl

theorem drop_ax1gen :
    Ax1 freeP ∧ Ax2a freeP ∧ Ax2b oneR freeP ∧
    Ax3 oneR allGuard allGuard freeP ∧ Ax4 oneR allGuard freeP ∧
    ¬ Ax1Gen oneR allGuard freeP ∧
    (∀ x w, ¬ God freeP x w) ∧ ¬ Th5 oneR allGuard freeP := by
  have h1 : Ax1 freeP := fun p q w hp hq => U_good.2.2.2 _ _ hp hq
  have h2 : Ax2a freeP := by
    intro p w
    refine ⟨U_ultra _, ?_⟩
    intro ⟨hp, hn⟩
    exact U_good.2.1 (U_good.2.2.1 _ _ (U_good.2.2.2 _ _ hp hn)
      (fun _ h => h.2 h.1))
  refine ⟨h1, h2, ?_, ?_, ?_, ?_, free_no_god, ?_⟩
  · intro p w hp v _
    cases w; cases v; exact hp
  · intro w
    apply U_good.2.2.1 _ _ U_good.1
    intro n _ p hp v _
    cases w; cases v
    exact ⟨n, trivial, hp.1⟩
  · intro p q w hp hi
    exact U_good.2.2.1 _ _ hp (fun n hn => hi w trivial n trivial hn)
  · intro hg
    obtain ⟨x, _, hx⟩ := god hg h2 ()
    exact free_no_god x () hx
  · intro h
    obtain ⟨x, _, hx⟩ := h () () trivial
    exact free_no_god x () hx

def S5Frame {W : Type} (R : W → W → Prop) : Prop :=
  (∀ w, R w w) ∧ (∀ w v, R w v → R v w) ∧
  (∀ w v u, R w v → R v u → R w u)

theorem deletion_frames : S5Frame totalR ∧ S5Frame oneR :=
  ⟨⟨fun _ => trivial, fun _ _ _ => trivial, fun _ _ _ _ _ => trivial⟩,
   ⟨fun _ => trivial, fun _ _ _ => trivial, fun _ _ _ _ _ => trivial⟩⟩

#print axioms deletion_frames
#print axioms drop_ax2a
#print axioms drop_ax1gen
end Programme.«20261021-1639-ontological».Atlas.Variant2Table
