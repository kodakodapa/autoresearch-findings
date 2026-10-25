import Programme.«20261021-1639-ontological».Atlas.ScottTable
/- Adapted from th, P111. D9: filter inclusion axis. `UpCW` is upward closure under current-world guarded inclusion,
as in library Notes.ModalFilter `Filter` (⊆ᴱ actualist, ⊆ᵐ possibilist); Scott's A2 is the
boxed version. -/
namespace Programme.«20261021-1639-ontological».Atlas.FilterAxis
open Programme.«20261021-1639-ontological».Atlas.ScottTable Programme.«20261021-1639-ontological».Countermodels.Tests Programme.«20261021-1639-ontological».Countermodels.Scott Programme.«20261021-1639-ontological».Atlas.Scott
variable {W E : Type} (m : Model W E) (a : Bool)

def HasU : Prop := ∀ w, m.positive (fun _ _ => True) w
def NoEmpty : Prop := ∀ w, ¬ m.positive (fun _ _ => False) w
def UpCW : Prop := ∀ p q w, m.positive p w →
  (∀ y, guard m a y w → p y w → q y w) → m.positive q w
def Inter : Prop := ∀ p q w, m.positive p w → m.positive q w →
  m.positive (fun x v => p x v ∧ q x v) w
/-- The library's `Filter P` at every world (current-world inclusion). -/
def FilterCW : Prop := HasU m ∧ NoEmpty m ∧ UpCW m a ∧ Inter m

theorem id_of_cw_A4 (hU : HasU m) (h0 : NoEmpty m) (hup : UpCW m a) (h4 : A4 m) :
    ∀ w v, m.rel w v → w = v := by
  intro w v hwv
  apply Classical.byContradiction
  intro hne
  have hw : m.positive (fun _ u => u ≠ v) w :=
    hup _ _ w (hU w) (fun _ _ _ => hne)
  exact h0 v (hup _ _ v (h4 _ w hw v hwv) (fun _ _ h => h rfl))

theorem mc_of_id (h : ∀ w v, m.rel w v → w = v) : MC m :=
  fun _ w hp v hv => h w v hv ▸ hp

theorem id_of_mc (h : MC m) : ∀ w v, m.rel w v → w = v :=
  fun w v hv => h (fun u => w = u) w rfl v hv

/-- Converse, Scott A1a, A2, A3 (no A4, no A5): on a frame with `R ⊆ id`, P is a current-world filter. -/
theorem filter_of_id (h1 : A1a m) (h2 : A2 m a) (h3 : A3 m)
    (hid : ∀ w v, m.rel w v → w = v) : FilterCW m a := by
  have up : UpCW m a := by
    intro p q w hp hpq
    exact h2 p q w hp (fun v hv y hy hpy => by
      have := hid w v hv; subst this; exact hpq y hy hpy)
  refine ⟨fun w => up _ _ w (h3 w) (fun _ _ _ => trivial), ?_, up, ?_⟩
  · intro w h0
    exact h1 (fun _ _ => False) w (up _ _ w h0 (fun _ _ h => h.elim)) h0
  · intro p q w hp hq
    exact up _ _ w (h3 w) (fun y _ hg => ⟨hg p hp, hg q hq⟩)

/-- Scott A1a–A4: the library's current-world filter property is equivalent to modal collapse. -/
theorem filter_iff_mc (h1 : A1a m) (h2 : A2 m a) (h3 : A3 m) (h4 : A4 m) :
    FilterCW m a ↔ MC m :=
  ⟨fun ⟨hU, h0, hup, _⟩ => mc_of_id m (id_of_cw_A4 m a hU h0 hup h4),
   fun h => filter_of_id m a h1 h2 h3 (id_of_mc m h)⟩

/-! Countermodels on the universal two-world frame (S5), one always-actual entity. -/
def localP : Model Bool Unit := univ2 (fun _ _ => True) (fun p w => p () w)
def rigidP : Model Bool Unit := univ2 (fun _ _ => True) (fun p _ => p () false)
def noneP : Model Bool Unit := univ2 (fun _ _ => True) (fun _ _ => False)
def allP : Model Bool Unit := univ2 (fun _ _ => True) (fun _ _ => True)

theorem drop_A4 : FilterCW localP a ∧ ¬ A4 localP ∧ ¬ MC localP :=
  ⟨⟨fun _ => trivial, fun _ h => h, fun _ _ _ hp h => h () (fun _ => trivial) hp,
    fun _ _ _ hp hq => ⟨hp, hq⟩⟩,
   fun h => h (fun _ w => w = false) false rfl true trivial |> Bool.noConfusion,
   univ2_not_mc _ _⟩

/-- Rigid principal ultrafilter: boxed upward closure (Scott A2), A4, but not `UpCW`. -/
theorem drop_UpCW : HasU rigidP ∧ NoEmpty rigidP ∧ ¬ UpCW rigidP a ∧ Inter rigidP ∧
    A2 rigidP a ∧ A4 rigidP ∧ ¬ MC rigidP :=
  ⟨fun _ => trivial, fun _ h => h,
   fun h => Bool.noConfusion (h (fun _ _ => True) (fun _ v => v = true) true trivial
     (fun _ _ _ => rfl)),
   fun _ _ _ hp hq => ⟨hp, hq⟩,
   fun _ _ _ hp h => h false trivial () (fun _ => trivial) hp,
   fun _ _ h _ _ => h, univ2_not_mc _ _⟩

theorem drop_HasU : NoEmpty noneP ∧ UpCW noneP a ∧ Inter noneP ∧ A4 noneP ∧ ¬ MC noneP :=
  ⟨fun _ h => h, fun _ _ _ h _ => h, fun _ _ _ h _ => h, fun _ _ h _ _ => h,
   univ2_not_mc _ _⟩

theorem drop_NoEmpty : HasU allP ∧ UpCW allP a ∧ Inter allP ∧ A4 allP ∧ ¬ MC allP :=
  ⟨fun _ => trivial, fun _ _ _ _ _ => trivial, fun _ _ _ _ _ => trivial,
   fun _ _ _ _ _ => trivial, univ2_not_mc _ _⟩

#print axioms id_of_cw_A4
#print axioms filter_iff_mc
#print axioms drop_A4
#print axioms drop_UpCW
#print axioms drop_HasU
#print axioms drop_NoEmpty
end Programme.«20261021-1639-ontological».Atlas.FilterAxis
