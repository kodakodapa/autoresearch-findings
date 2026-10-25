import Programme.«20261022-0733-ontological».Run2.LGeneral
import Programme.«20261022-0733-ontological».Run2.GodlessL

/-! # Minimality of the `L` route and the `Th4` route to `G_ex` (th's E9, P87)

K6 (`GexL.gex_L`) derives `∃ᴱ G` at every world in variant 3′ from `Closed`, `E₃` admitted,
`Ax2a`, `Ax2b`, `Ax3`, `Ax4` and `L`; `GexL.gex_noConj` derives it in variant 3 from `Ax2a`, `Ax2b`,
`Ax3`, `Ax4c` and `Th4`.  th's models (`agents/th/lean/Programme/Th/LMinimal.lean`), restated over
the definitions of `TwoClosed`, `DropDagger`, `BoxIdle` (imported, none copied):

* `noAx3`, `noAx4`, `noAx2a`: *full* two-world models (worlds `Bool`, one entity, universal `R`,
  everything actual, every proposition, property and set of properties admitted), so they are
  `𝓛`-general (`LGeneral.lgeneral_full`), not only models of the interface.  Positivity is
  `φ () true` (rigid principal ultrafilter), `¬ φ () false` (contains `⊥`), and `True`.
* `Ax2b`: the godless model of E8 (`GodlessL`), a model of the `Closed` interface only.

Over the `𝓛`-general models, therefore: `Ax2a`, `Ax3`, `Ax4` are each needed for `G_ex` from `L`
(variant 3′), and `Ax3` for `G_ex` from `Th4` (variant 3). -/

namespace Programme.«20261022-0733-ontological».Run2.Minimal

open Programme.«20261022-0733-ontological».Run2.TwoClosed Programme.«20261022-0733-ontological».Run2.DropDagger Programme.«20261022-0733-ontological».Run2.BoxIdle
  Programme.«20261022-0733-ontological».Run2.LGeneral

/-- Full model on `Bool × Unit`, universal `R`, all actual, with positivity `P`. -/
def full (P : (Unit → Bool → Prop) → Bool → Prop) : Model Bool Unit where
  R := fun _ _ => True
  act := fun _ _ => True
  AS := fun _ => True
  AT := fun _ => True
  AH := fun _ => True
  P := P

theorem full_lgeneral (P : (Unit → Bool → Prop) → Bool → Prop) : LGeneral (full P) :=
  lgeneral_full (fun _ => trivial) (fun _ => trivial) (fun _ => trivial)

/-- The property "the world is `b`". -/
def at_ (b : Bool) : Unit → Bool → Prop := fun _ v => v = b

theorem ess3_at (P : (Unit → Bool → Prop) → Bool → Prop) (b : Bool) :
    Ess3 (full P) (at_ b) () b := fun ψ _ hψ v _ =>
  ⟨fun h => by
    have h' : at_ b () b = bot () b := congrFun (congrFun h ()) b
    exact h'.mp rfl,
    fun y _ hv => by cases y; subst hv; exact hψ⟩

theorem ess_at (P : (Unit → Bool → Prop) → Bool → Prop) (b : Bool) :
    Ess (full P) (at_ b) () b :=
  ⟨rfl, fun ψ _ hψ v _ y _ hv => by cases y; subst hv; exact hψ⟩

theorem not_E3 (P : (Unit → Bool → Prop) → Bool → Prop) (b : Bool) : ¬ E3 (full P) () b :=
  fun h => by
    obtain ⟨_, _, hv⟩ := h (at_ b) trivial (ess3_at P b) (!b) trivial
    cases b <;> exact Bool.noConfusion hv

theorem not_E (P : (Unit → Bool → Prop) → Bool → Prop) (b : Bool) : ¬ E (full P) () b :=
  fun h => by
    obtain ⟨_, _, hv⟩ := h (at_ b) trivial (ess_at P b) (!b) trivial
    cases b <;> exact Bool.noConfusion hv

theorem full_not_mc (P : (Unit → Bool → Prop) → Bool → Prop) : ¬ MC (full P) := fun h =>
  Bool.noConfusion (h (fun v => v = true) trivial true rfl false trivial)

theorem ax4c_of_ax4 {W D : Type} {M : Model W D} (h : Ax4 M) : Ax4c M :=
  fun φ ψ hφ hψ w hp hi => h φ ψ hφ hψ w hp fun v hv y hy hy' => (hi v hv).2 y hy hy'

/-! ### Without `Ax3`: rigid principal ultrafilter at `true` -/

def noAx3 : Model Bool Unit := full fun φ _ => φ () true

theorem noAx3_god (w : Bool) : G noAx3 () w ↔ w = true :=
  ⟨fun h => h (at_ true) trivial rfl, fun h φ _ hφ => by subst h; exact hφ⟩

theorem noAx3_props :
    Ax2a noAx3 ∧ Ax2b noAx3 ∧ Ax4 noAx3 ∧ Ax4c noAx3 ∧ L noAx3 ∧ Th4 noAx3 ∧
      ¬ ExG noAx3 false ∧ ¬ Ax3 noAx3 ∧ ¬ Ax3v3 noAx3 ∧ ¬ MC noAx3 := by
  have h4 : Ax4 noAx3 := fun _ _ _ _ _ hφ hi => hi true trivial () trivial hφ
  refine ⟨fun φ _ _ => ⟨Classical.em _, fun ⟨a, b⟩ => b a⟩,
    fun _ _ _ h _ _ => h, h4, ax4c_of_ax4 h4, fun _ => (noAx3_god true).2 rfl,
    fun _ => ⟨true, trivial, (), trivial, (noAx3_god true).2 rfl⟩, ?_,
    fun h => not_E _ true (h true), fun h => not_E3 _ true (h true), full_not_mc _⟩
  rintro ⟨y, _, hg⟩
  cases y
  exact Bool.noConfusion ((noAx3_god false).1 hg)

/-! ### Without `Ax4`: positivity "false at `false`", which contains `⊥` -/

def noAx4 : Model Bool Unit := full fun φ _ => ¬ φ () false

theorem noAx4_no_god (x : Unit) (w : Bool) : ¬ G noAx4 x w := fun h =>
  h bot trivial (fun h => h)

theorem noAx4_props :
    Ax2a noAx4 ∧ Ax2b noAx4 ∧ Ax3 noAx4 ∧ Ax3v3 noAx4 ∧ L noAx4 ∧
      (∀ w, ¬ ExG noAx4 w) ∧ ¬ Ax4 noAx4 ∧ ¬ MC noAx4 :=
  ⟨fun φ _ _ => ⟨(Classical.em (φ () false)).symm.imp id fun h hn => hn h,
      fun ⟨a, b⟩ => b a⟩,
    fun _ _ _ h _ _ => h, fun _ => not_E _ false, fun _ => not_E3 _ false,
    fun _ => noAx4_no_god () false, fun _ ⟨y, _, hg⟩ => noAx4_no_god y _ hg,
    fun h => h bot top trivial trivial false (fun h => h) (fun _ _ _ _ _ => trivial) trivial,
    full_not_mc _⟩

/-! ### Without `Ax2a`: everything positive -/

def noAx2a : Model Bool Unit := full fun _ _ => True

theorem noAx2a_no_god (x : Unit) (w : Bool) : ¬ G noAx2a x w := fun h => h bot trivial trivial

theorem noAx2a_props :
    Ax2b noAx2a ∧ Ax3 noAx2a ∧ Ax3v3 noAx2a ∧ Ax4 noAx2a ∧ Ax4c noAx2a ∧
      L noAx2a ∧ (∀ w, ¬ ExG noAx2a w) ∧ ¬ Ax2a noAx2a ∧ ¬ MC noAx2a :=
  ⟨fun _ _ _ _ _ _ => trivial, fun _ => trivial, fun _ => trivial,
    fun _ _ _ _ _ _ _ => trivial, fun _ _ _ _ _ _ _ => trivial, fun _ => trivial,
    fun _ ⟨y, _, hg⟩ => noAx2a_no_god y _ hg,
    fun h => (h top trivial true).2 ⟨trivial, trivial⟩, full_not_mc _⟩

/-- **Minimality over `𝓛`-general models.**  None of `Ax2a`, `Ax3`, `Ax4` can be dropped from
K6's `G_ex` from `L` (variant 3′; `Closed` and `E₃` admitted follow from `LGeneral`), and `Ax3`
cannot be dropped from `G_ex` from `Th4` (variant 3, `Ax4c`). -/
theorem minimal_lgeneral :
    ¬ (∀ M : Model Bool Unit, LGeneral M → Ax2b M → Ax3v3 M → Ax4 M → L M → ∀ w, ExG M w) ∧
    ¬ (∀ M : Model Bool Unit, LGeneral M → Ax2a M → Ax2b M → Ax4 M → L M → ∀ w, ExG M w) ∧
    ¬ (∀ M : Model Bool Unit, LGeneral M → Ax2a M → Ax2b M → Ax3v3 M → L M → ∀ w, ExG M w) ∧
    ¬ (∀ M : Model Bool Unit, LGeneral M → Ax2a M → Ax2b M → Ax4c M → Th4 M →
        ∀ w, ExG M w) := by
  obtain ⟨a2, b2, b4, b4c, bl, bth, bng, _⟩ := noAx3_props
  obtain ⟨c2a, c2b, _, c3', cl, cng, _⟩ := noAx4_props
  obtain ⟨d2b, _, d3', d4, _, dl, dng, _⟩ := noAx2a_props
  exact ⟨fun h => dng true (h noAx2a (full_lgeneral _) d2b d3' d4 dl true),
    fun h => bng (h noAx3 (full_lgeneral _) a2 b2 b4 bl false),
    fun h => cng true (h noAx4 (full_lgeneral _) c2a c2b c3' cl true),
    fun h => bng (h noAx3 (full_lgeneral _) a2 b2 b4c bth false)⟩

/-- The same for variant 2's `Ax3` where it applies: the full models also refute `Ax3` (`noAx3`)
or satisfy it (`noAx4`, `noAx2a`). -/
theorem v2_ax3 : ¬ Ax3 noAx3 ∧ Ax3 noAx4 ∧ Ax3 noAx2a :=
  ⟨noAx3_props.2.2.2.2.2.2.2.1, noAx4_props.2.2.1, noAx2a_props.2.1⟩

/-- **Ax2b, interface level** (E8): over the `Closed` interface (not shown `𝓛`-general),
`Ax2b` cannot be dropped from either route. -/
theorem ax2b_interface :
    ¬ (∀ (M : Model RigidFree.Cw Unit), Closed M → M.AT (E3 M) → Ax2a M → Ax3v3 M → Ax4 M →
        L M → ∀ w, ExG M w) ∧
    ¬ (∀ (M : Model RigidFree.Cw Unit), Closed M → M.AT (E3 M) → Ax2a M → Ax3v3 M → Ax4c M →
        Th4 M → ∀ w, ExG M w) :=
  ⟨GodlessL.gex_needs_ax2b.1, GodlessL.gex_needs_ax2b.2.2⟩

end Programme.«20261022-0733-ontological».Run2.Minimal

#print axioms Programme.«20261022-0733-ontological».Run2.Minimal.minimal_lgeneral
#print axioms Programme.«20261022-0733-ontological».Run2.Minimal.ax2b_interface
