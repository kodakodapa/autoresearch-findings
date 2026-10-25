import Programme.«20261022-0733-ontological».Run2.LGeneralFullBridge
import Programme.«20261022-0733-ontological».Run2.LGeneralFullInst

/-! # Monotheism column of the atlas (closed and `𝓛`-general models)

* `mono`: if admitted properties are closed under negation and contain every identity predicate
  `λz. z = y`, then `Ax2a` alone gives monotheism (`G x w → G y w → x = y`), at every world, on
  every frame, for any actuality.  No other axiom.  (K50 of the earlier run, re-established over
  `TwoClosed.Model`.)
* `mono_lgenF`: in every model `𝓛`-general for v4's full `𝓛` (`LGenF`), `Ax2a` gives monotheism.
* `ax2a_needed`: `Ax2a` cannot be dropped.  A full one-world model with two actual entities and
  only `⊤` positive is `LGenF` and `Closed`, satisfies `Ax2b`, `Ax3`, `Ax3v3`, `Ax4`, `Ax1Gen`,
  `Ax1GenTwo` and `MC`, has `∃ᴱ G`, and both entities are God-like: monotheism fails. -/

namespace Programme.«20261022-0733-ontological».Run2.Monotheism

open Programme.«20261022-0733-ontological».Run2.TwoClosed
open Programme.«20261022-0733-ontological».Run2.LGeneralFull (LGenF)

variable {W D : Type} {M : Model W D}

def Mono (M : Model W D) : Prop := ∀ x y w, G M x w → G M y w → x = y

/-- **`Ax2a` gives monotheism** once identity predicates are admitted. -/
theorem mono (hneg : ∀ φ, M.AT φ → M.AT (neg φ)) (hid : ∀ y : D, M.AT (fun z _ => z = y))
    (h2a : Ax2a M) : Mono M := by
  intro x y w hx hy
  rcases (h2a _ (hid x) w).1 with hp | hn
  · exact (hy _ (hid x) hp).symm
  · exact absurd rfl (hx _ (hneg _ (hid x)) hn)

/-- **Every `𝓛`-general model (v4's full `𝓛`) with `Ax2a` is monotheistic.** -/
theorem mono_lgenF (hL : LGenF M) (h2a : Ax2a M) : Mono M :=
  mono (LGeneral.closed_of_lgeneral (LGeneralFull.lgeneral_of_lgenF hL)).neg
    (LGeneral.extra_of_lgeneral (LGeneralFull.lgeneral_of_lgenF hL)).hid h2a

/-! ## `Ax2a` is needed: two God-like entities -/

/-- Full carriers, one reflexive world, two always-actual entities, only `⊤` positive. -/
def tg : Model Unit Bool where
  R := fun _ _ => True
  act := fun _ _ => True
  AS := fun _ => True
  AT := fun _ => True
  AH := fun _ => True
  P := fun φ _ => φ = top

theorem lgenF_tg : LGenF tg :=
  LGeneralFullInst.lgenF_full tg (fun _ => trivial) (fun _ => trivial) (fun _ => trivial)

theorem closed_tg : Closed tg :=
  LGeneral.closed_of_lgeneral (LGeneralFull.lgeneral_of_lgenF lgenF_tg)

theorem god_tg (x : Bool) (w : Unit) : G tg x w := fun φ _ h => by
  show φ x w; rw [show φ = top from h]; trivial

theorem ax2b_tg : Ax2b tg := fun _ _ _ h _ _ => h

theorem ax4_tg : Ax4 tg := fun φ ψ _ _ w (h : φ = top) hinc => by
  show ψ = top
  subst h
  funext z u
  cases u; cases w
  exact propext ⟨fun _ => trivial, fun _ => hinc () trivial z trivial trivial⟩

theorem ax3_tg : Ax3 tg := fun _ => by
  show E tg = top
  funext x w
  cases w
  refine propext ⟨fun _ => trivial, fun _ φ _ hess v _ => ?_⟩
  cases v
  exact ⟨x, trivial, hess.1⟩

theorem ax3v3_tg : Ax3v3 tg := fun _ => by
  show E3 tg = top
  funext x w
  cases w
  refine propext ⟨fun _ => trivial, fun _ φ _ hess v _ => ?_⟩
  cases v
  obtain ⟨hne, hsub⟩ := hess (fun z _ => z = x) trivial rfl () trivial
  have : ∃ y u, φ y u := Classical.byContradiction fun hn =>
    hne (by funext y u; exact propext ⟨fun h => hn ⟨y, u, h⟩, False.elim⟩)
  obtain ⟨y, u, hy⟩ := this
  cases u
  have : y = x := hsub y trivial hy
  subst this
  exact ⟨y, trivial, hy⟩

theorem ax1Gen_tg : Ax1Gen tg := fun Φ φ _ _ w pos cj => by
  show φ = top
  funext z u
  cases u; cases w
  refine propext ⟨fun _ => trivial, fun _ => (cj () trivial z trivial).2 fun ψ hA hm => ?_⟩
  rw [show ψ = top from pos ψ hA hm]; trivial

theorem ax1GenTwo_tg : Ax1GenTwo tg := fun Φ φ hΦ hφ w _ pos cj => ax1Gen_tg Φ φ hΦ hφ w pos cj

theorem mc_tg : MC tg := fun _ _ w h v _ => by cases w; cases v; exact h

theorem not_ax2a_tg : ¬ Ax2a tg := fun h => by
  rcases (h (fun z _ => z = true) trivial ()).1 with hp | hn
  · have := congrFun (congrFun hp false) (); simp [top] at this
  · have := congrFun (congrFun hn true) (); simp [neg, top] at this

theorem not_mono_tg : ¬ Mono tg := fun h => Bool.noConfusion (h true false () (god_tg _ _) (god_tg _ _))

/-- **`Ax2a` is needed for monotheism**, even with all other axioms of variant 2 and 3′, both
conjunction axioms, `MC` and `∃ᴱ G`. -/
theorem ax2a_needed :
    LGenF tg ∧ Closed tg ∧ Ax2b tg ∧ Ax3 tg ∧ Ax3v3 tg ∧ Ax4 tg ∧ Ax1Gen tg ∧ Ax1GenTwo tg ∧
      MC tg ∧ (∀ w, ExG tg w) ∧ ¬ Ax2a tg ∧ ¬ Mono tg :=
  ⟨lgenF_tg, closed_tg, ax2b_tg, ax3_tg, ax3v3_tg, ax4_tg, ax1Gen_tg, ax1GenTwo_tg, mc_tg,
    fun w => ⟨true, trivial, god_tg _ w⟩, not_ax2a_tg, not_mono_tg⟩

end Programme.«20261022-0733-ontological».Run2.Monotheism

#print axioms Programme.«20261022-0733-ontological».Run2.Monotheism.mono
#print axioms Programme.«20261022-0733-ontological».Run2.Monotheism.mono_lgenF
#print axioms Programme.«20261022-0733-ontological».Run2.Monotheism.ax2a_needed
