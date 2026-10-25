import Programme.«20261022-0733-ontological».Run2.TwoNoRigidity
import Programme.«20261022-0733-ontological».Run2.LGeneralFullInst
import Programme.«20261022-0733-ontological».Run2.Minimal

/-! # The hypotheses of `Ax1GenTwo → Ax1Gen` (E13 / K22), sharpened and shown minimal

* `ax1Gen_of_two_2a4`: in closed models, `Ax2a` and `Ax4` alone give `Ax1GenTwo → Ax1Gen`;
  `⊤` positive follows from them (`pTop_of_2a4`), so neither `Ax3` nor `Ax3v3` is needed.
* `tm` ("only `⊤` is positive"): v4 `ex:separating`'s FM carriers, one entity, S5, `P φ w :↔ φ = ⊤`.
  `LGenF`, `Closed`, `Ax2b`, `Ax3`, `Ax3v3`, `Ax4`, `L`, God at every world, `Ax1GenTwo`
  (vacuously: two distinct positive properties never exist), but not `Ax1Gen`, `Ax2a`, `MC`.
  So `Ax2a` cannot be dropped, neither from the equivalence nor from K1's MC half.
  The failing instance is `Φ := λψ u. u₀ = 1 ∧ ψ = ⊥`, empty at worlds with bit 0 false, and
  `φ := λ_ u. u₀ ≠ 1`: the collection is world-dependent, which `Ax2a` (via the lifted
  `atMost` proposition of E13's second case) is what rules out.
* `anti`: full two-world S5 model, `P φ w :↔ ¬ φ w`.  `Ax2a`, `Ax3`, `Ax3v3`, `Ax1GenTwo`,
  not `Ax1Gen`, not `Ax4`.  So `Ax4` cannot be dropped. -/

namespace Programme.«20261022-0733-ontological».Run2.TwoNeedsAx2a

open Programme.«20261022-0733-ontological».Run2.TwoClosed Programme.«20261022-0733-ontological».Run2.FM Programme.«20261022-0733-ontological».Run2.RigidFree
  Programme.«20261022-0733-ontological».Run2.BoxIdle
open Programme.«20261022-0733-ontological».Run2.LGeneralFullInst (lgenF_full lgenF_mk)
open Programme.«20261022-0733-ontological».Run2.LGeneralFull (LGenF)
open Programme.«20261022-0733-ontological».Run2.FMGeneral (mk sym_total)

variable {W D : Type} {M : Model W D}

/-! ## Sharpened theorem -/

theorem neg_bot_eq : (neg (bot : D → W → Prop)) = top := by
  funext x w; simp [neg, bot, top]

theorem pTop_of_2a4 (C : Closed M) (h2a : Ax2a M) (h4 : Ax4 M) (w : W) : M.P top w := by
  rcases (h2a top C.top w).1 with h | h
  · exact h
  · -- `¬⊤ = ⊥` positive gives every admitted property positive, in particular `¬⊥ = ⊤`
    have hb : M.P bot w := by
      have : (neg (top : D → W → Prop)) = bot := by funext x w; simp [neg, bot, top]
      rw [this] at h; exact h
    exact h4 bot top C.bot C.top w hb fun _ _ _ _ h => h.elim

/-- `Ax1GenTwo → Ax1Gen` in closed models from `Ax2a` and `Ax4` only. -/
theorem ax1Gen_of_two_2a4 [Nonempty D] (C : Closed M) (h2a : Ax2a M) (h4 : Ax4 M)
    (hT : Ax1GenTwo M) : Ax1Gen M :=
  TwoNoRigidity.ax1Gen_of_two_noRigid C h2a (pTop_of_2a4 C h2a h4) h4 hT

theorem equivalence_2a4 [Nonempty D] (C : Closed M) (h2a : Ax2a M) (h4 : Ax4 M) :
    Ax1GenTwo M ↔ Ax1Gen M :=
  ⟨ax1Gen_of_two_2a4 C h2a h4, two_of_ax1Gen⟩

/-! ## `Ax2a` is needed: only `⊤` positive, on FM carriers -/

def tm : Model Cw Unit := mk (fun _ _ => True) (fun _ _ => True) (fun φ _ => φ = top)

theorem G_tm (x : Unit) (w : Cw) : G tm x w := fun φ _ h => by subst h; trivial

theorem closed_tm : Closed tm where
  top := Programme.«20261022-0733-ontological».Run2.RigidFree.closed.top
  bot := Programme.«20261022-0733-ontological».Run2.RigidFree.closed.bot
  neg := Programme.«20261022-0733-ontological».Run2.RigidFree.closed.neg
  conj := Programme.«20261022-0733-ontological».Run2.RigidFree.closed.conj
  lift := Programme.«20261022-0733-ontological».Run2.RigidFree.closed.lift
  negS := Programme.«20261022-0733-ontological».Run2.RigidFree.closed.negS
  god := based_const _ fun w v => iff_of_true (G_tm () w) (G_tm () v)
  exG := based_const _ fun w v => iff_of_true ⟨(), trivial, G_tm () w⟩ ⟨(), trivial, G_tm () v⟩
  pos := single_fmh top Programme.«20261022-0733-ontological».Run2.RigidFree.closed.top
  single := single_fmh
  union := fun _ _ => union_fmh
  guard := fun _ _ => guard_fmh
  atMost := fun _ _ hΦ h0 => atMost_based hΦ h0

theorem lgenF_tm : LGenF tm :=
  lgenF_mk (R := fun _ _ => True) (ac := fun _ _ => True) (P := fun φ _ => φ = top)
    0 (fun d _ => sym_total (funext fun ψ => funext fun w => by
      show (act d ψ = top) = (ψ = top)
      apply propext; constructor
      · intro h; rw [← act_act d ψ, h]; rfl
      · intro h; rw [h]; rfl))

theorem E_tm (x : Unit) (w : Cw) : E tm x w := Programme.«20261022-0733-ontological».Run2.RigidFree.E_all x w
theorem E3_tm (x : Unit) (w : Cw) : E3 tm x w := Programme.«20261022-0733-ontological».Run2.RigidFree.E3_all x w

theorem E_adm_tm : tm.AT (E tm) := based_const _ fun w v => iff_of_true (E_tm () w) (E_tm () v)
theorem E3_adm_tm : tm.AT (E3 tm) :=
  based_const _ fun w v => iff_of_true (E3_tm () w) (E3_tm () v)

theorem ax3_tm : Ax3 tm := fun _ => funext fun x => funext fun w => propext (iff_true_intro (E_tm x w))
theorem ax3v3_tm : Ax3v3 tm := fun _ =>
  funext fun x => funext fun w => propext (iff_true_intro (E3_tm x w))

theorem ax4_tm : Ax4 tm := fun φ ψ _ _ w hφ hinc =>
  funext fun x => funext fun v => propext (iff_true_intro (hinc v trivial x trivial (by
    show φ x v; rw [show φ = top from hφ]; trivial)))

theorem ax2b_tm : Ax2b tm := fun _ _ _ h _ _ => h

theorem l_tm : L tm := fun _ => funext fun x => funext fun w => propext (iff_true_intro (G_tm x w))

theorem exG_tm (w : Cw) : ExG tm w := ⟨(), trivial, G_tm () w⟩

theorem ax1GenTwo_tm : Ax1GenTwo tm := fun _ _ _ _ _ ⟨ψ₁, ψ₂, h1, h2, m1, m2, hne⟩ pos _ =>
  absurd ((show ψ₁ = top from pos ψ₁ h1 m1).trans (show ψ₂ = top from pos ψ₂ h2 m2).symm) hne

def bitTrue : Cw → Prop := fun v => v 0 = true

theorem bitTrue_based : Based bitTrue := (bit_based 0 true : Based (bit 0 true ()))

theorem not_ax1Gen_tm : ¬ Ax1Gen tm := by
  intro h
  let Φ : (Unit → Cw → Prop) → Cw → Prop := fun ψ u => bitTrue u ∧ ψ = bot
  let φ : Unit → Cw → Prop := fun _ u => ¬ bitTrue u
  have hΦ : tm.AH Φ := guard_fmh bitTrue_based (single_fmh bot Programme.«20261022-0733-ontological».Run2.RigidFree.closed.bot)
  have hφ : tm.AT φ := Programme.«20261022-0733-ontological».Run2.RigidFree.closed.negS _ bitTrue_based
  have hP := h Φ φ hΦ hφ (fun _ => false)
    (fun ψ _ hm => absurd hm.1 (by simp [bitTrue]))
    (fun v _ z _ => ⟨fun hn ψ _ hm => absurd hm.1 hn,
      fun hall hb => by have := hall bot Programme.«20261022-0733-ontological».Run2.RigidFree.closed.bot ⟨hb, rfl⟩; exact this⟩)
  have : φ () (fun _ => true) := by rw [show φ = top from hP]; trivial
  exact this rfl

theorem not_ax2a_tm : ¬ Ax2a tm := by
  intro h
  rcases (h (bit 0 true) (bit_based 0 true) (fun _ => false)).1 with hp | hp
  · have : bit 0 true () (fun _ => false) := by rw [show bit 0 true = top from hp]; trivial
    exact Bool.false_ne_true this
  · have : neg (bit 0 true) () (fun _ => true) := by
      rw [show neg (bit 0 true) = top from hp]; trivial
    exact this rfl

theorem not_mc_tm : ¬ MC tm := Programme.«20261022-0733-ontological».Run2.RigidFree.not_mc

/-- **`Ax2a` is needed.**  An `𝓛`-general (v4's full `𝓛`) S5 model satisfying `Ax2b`, `Ax3`,
`Ax3v3`, `Ax4`, `L`, `Ax1GenTwo`, God everywhere, in which `Ax1Gen`, `Ax2a`, admitted MC fail. -/
theorem ax2a_needed :
    LGenF tm ∧ Closed tm ∧ tm.AT (E tm) ∧ tm.AT (E3 tm) ∧ Ax2b tm ∧ Ax3 tm ∧ Ax3v3 tm ∧
      Ax4 tm ∧ L tm ∧ (∀ w, ExG tm w) ∧ (∀ w v, tm.R w v) ∧ (∀ y w, tm.act y w) ∧
      Ax1GenTwo tm ∧ ¬ Ax1Gen tm ∧ ¬ Ax2a tm ∧ ¬ MC tm :=
  ⟨lgenF_tm, closed_tm, E_adm_tm, E3_adm_tm, ax2b_tm, ax3_tm, ax3v3_tm, ax4_tm, l_tm, exG_tm,
    fun _ _ => trivial, fun _ _ => trivial, ax1GenTwo_tm, not_ax1Gen_tm, not_ax2a_tm, not_mc_tm⟩

/-! ## `Ax4` is needed: full two-world model, positivity = falsity at the current world -/

def anti : Model Bool Unit := Programme.«20261022-0733-ontological».Run2.Minimal.full fun φ w => ¬ φ () w

theorem closed_anti : Closed anti where
  top := trivial
  bot := trivial
  neg := fun _ _ => trivial
  conj := fun _ _ _ _ => trivial
  lift := fun _ _ => trivial
  negS := fun _ _ => trivial
  god := trivial
  exG := trivial
  pos := trivial
  single := fun _ _ => trivial
  union := fun _ _ _ _ => trivial
  guard := fun _ _ _ _ => trivial
  atMost := fun _ _ _ _ => trivial

theorem ax2a_anti : Ax2a anti := fun φ _ w =>
  ⟨(Classical.em (φ () w)).symm.imp id fun h hn => hn h, fun ⟨a, b⟩ => b a⟩

theorem ax3_anti : Ax3 anti := fun w => Programme.«20261022-0733-ontological».Run2.Minimal.not_E _ w
theorem ax3v3_anti : Ax3v3 anti := fun w => Programme.«20261022-0733-ontological».Run2.Minimal.not_E3 _ w

theorem ax1GenTwo_anti : Ax1GenTwo anti := fun _ _ _ _ w ⟨ψ₁, _, h1, _, m1, _, _⟩ pos cj hφ =>
  pos ψ₁ h1 m1 ((cj w trivial () trivial).1 hφ ψ₁ h1 m1)

theorem not_ax1Gen_anti : ¬ Ax1Gen anti := fun h =>
  h (fun _ _ => False) top trivial trivial true (fun _ _ hm => hm.elim)
    (fun _ _ _ _ => ⟨fun _ _ _ hm => hm.elim, fun _ => trivial⟩) trivial

theorem not_ax4_anti : ¬ Ax4 anti := fun h =>
  h bot top trivial trivial true (fun h => h) (fun _ _ _ _ _ => trivial) trivial

/-- **`Ax4` is needed.**  A full (so `𝓛`-general) two-world S5 model of `Ax2a`, `Ax3`, `Ax3v3`
and `Ax1GenTwo` in which `Ax1Gen` and `Ax4` fail. -/
theorem ax4_needed :
    LGenF anti ∧ Closed anti ∧ Ax2a anti ∧ Ax3 anti ∧ Ax3v3 anti ∧ Ax1GenTwo anti ∧
      ¬ Ax1Gen anti ∧ ¬ Ax4 anti :=
  ⟨lgenF_full anti (fun _ => trivial) (fun _ => trivial) (fun _ => trivial), closed_anti,
    ax2a_anti, ax3_anti, ax3v3_anti, ax1GenTwo_anti, not_ax1Gen_anti, not_ax4_anti⟩

end Programme.«20261022-0733-ontological».Run2.TwoNeedsAx2a

#print axioms Programme.«20261022-0733-ontological».Run2.TwoNeedsAx2a.equivalence_2a4
#print axioms Programme.«20261022-0733-ontological».Run2.TwoNeedsAx2a.ax2a_needed
#print axioms Programme.«20261022-0733-ontological».Run2.TwoNeedsAx2a.ax4_needed
