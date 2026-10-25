import Programme.«20261022-0733-ontological».Run2.TwoNoRigidityFull
import Programme.«20261022-0733-ontological».Run2.LGeneralFullInst
/-! # `Ax2a` cannot be dropped from K22 (E13)

K22: `Closed`, `E`/`E3` admitted, `Ax2a`, `Ax3` (or `Ax3v3`), `Ax4` give `Ax1GenTwo ↔ Ax1Gen`.
Here: on the FM carriers of v4 `ex:separating` (S5, one entity, all actual), take positivity
to be *necessary truth*, `P φ w := ∀ v, φ () v`.  Then only `⊤` is positive, so `Ax1GenTwo` is
vacuous (no two distinct positive properties), while `Ax1Gen` fails for the guarded singleton
collection `Φ ψ v := v 0 = true ∧ ψ = ⊥`, whose conjunction `λ_ v. v 0 = false` is not positive.
No essences exist on these carriers (`RigidFree.no_ess`), so `E = E3 = ⊤` and `Ax3`, `Ax3v3` hold.
`Ax4` and `Ax2b` hold; `Ax2a` fails.  The model is `𝓛`-general for v4's full `𝓛`. -/
namespace Programme.«20261022-0733-ontological».Run2.NeedAx2a

open Programme.«20261022-0733-ontological».Run2.TwoClosed Programme.«20261022-0733-ontological».Run2.RigidFree Programme.«20261022-0733-ontological».Run2.FM
open Programme.«20261022-0733-ontological».Run2.LGeneralFull

/-- Necessary-truth positivity on the FM carriers. -/
def nt : Model Cw Unit :=
  Programme.«20261022-0733-ontological».Run2.FMGeneral.mk (fun _ _ => True) (fun _ _ => True) (fun φ _ => ∀ v, φ () v)

theorem xorw_surj (d v : Cw) : ∃ u, xorw u d = v := ⟨xorw v d, xorw_xorw v d⟩

theorem actH_nt (d : Cw) : Programme.«20261022-0733-ontological».Run2.FMGeneral.actH d nt.P = nt.P := by
  funext ψ w
  show (∀ v, act d ψ () v) = ∀ v, ψ () v
  apply propext
  constructor
  · intro h v
    obtain ⟨u, hu⟩ := xorw_surj d v
    have := h u
    simp only [act] at this
    rw [hu] at this; exact this
  · intro h v; exact h _

theorem lgenF_nt : LGenF nt :=
  LGeneralFullInst.lgenF_mk 0 fun d _ => Programme.«20261022-0733-ontological».Run2.FMGeneral.sym_total (actH_nt d)

theorem top_of_pos {φ : Unit → Cw → Prop} {w : Cw} (h : nt.P φ w) : φ = top :=
  funext fun x => funext fun v => by cases x; exact propext (iff_of_true (h v) trivial)

theorem god_all (x : Unit) (w : Cw) : G nt x w := fun _ _ h => by cases x; exact h w

theorem exG_all (w : Cw) : ExG nt w := ⟨(), trivial, god_all () w⟩

theorem pos_fmh : FMH nt.P :=
  ⟨0, fun d _ ψ w => by
    have := congrFun (congrFun (actH_nt d) ψ) w
    exact (Eq.to_iff this).symm⟩

theorem closed_nt : Closed nt where
  top := RigidFree.closed.top
  bot := RigidFree.closed.bot
  neg := RigidFree.closed.neg
  conj := RigidFree.closed.conj
  lift := RigidFree.closed.lift
  negS := RigidFree.closed.negS
  god := based_const _ fun w v => iff_of_true (god_all () w) (god_all () v)
  exG := based_const _ fun w v => iff_of_true (exG_all w) (exG_all v)
  pos := pos_fmh
  single := single_fmh
  union := fun _ _ => union_fmh
  guard := fun _ _ => guard_fmh
  atMost := fun _ _ hΦ h0 => atMost_based hΦ h0

theorem E_adm_nt : nt.AT (E nt) := RigidFree.E_adm
theorem E3_adm_nt : nt.AT (E3 nt) := RigidFree.E3_adm

theorem ax3_nt : Ax3 nt := fun _ v => E_all () v
theorem ax3v3_nt : Ax3v3 nt := fun _ v => E3_all () v

theorem ax4_nt : Ax4 nt := fun _ _ _ _ _ hφ hinc v => hinc v trivial () trivial (hφ v)

theorem ax2b_nt : Ax2b nt := fun _ _ _ hφ _ _ => hφ

theorem ax1GenTwo_nt : Ax1GenTwo nt := by
  rintro Φ φ _ _ w ⟨ψ₁, ψ₂, h₁, h₂, m₁, m₂, hne⟩ hpos _
  exact absurd ((top_of_pos (hpos ψ₁ h₁ m₁)).trans (top_of_pos (hpos ψ₂ h₂ m₂)).symm) hne

/-- The all-false world. -/
def w0 : Cw := fun _ => false

theorem not_ax1Gen_nt : ¬ Ax1Gen nt := by
  intro h
  have hΦ : nt.AH (fun ψ v => v 0 = true ∧ ψ = bot) :=
    guard_fmh (bit_based 0 true) (single_fmh bot RigidFree.closed.bot)
  have hφ : nt.AT (fun _ v => v 0 = false) := bit_based 0 false
  have hp := h _ _ hΦ hφ w0 (fun ψ _ hm => absurd hm.1 (by simp [w0]))
    (fun v _ z _ => by
      constructor
      · intro hv ψ _ hm
        have hv' : v 0 = false := hv
        rw [hm.1] at hv'; exact absurd hv' (by simp)
      · intro hall
        show v 0 = false
        cases hv : v 0
        · rfl
        · exact absurd (hall bot RigidFree.closed.bot ⟨hv, rfl⟩) id)
  have := hp (fun _ => true)
  exact Bool.noConfusion this

theorem not_ax2a_nt : ¬ Ax2a nt := by
  intro h
  rcases (h (fun _ v => v 0 = true) (bit_based 0 true) w0).1 with hp | hp
  · exact absurd (hp w0) (by simp [w0])
  · exact absurd (hp (fun _ => true)) (by simp [neg])

/-- Only the completeness half of `Ax2a` fails; consistency holds. -/
theorem ax2a_cons_nt : ∀ φ w, ¬ (nt.P φ w ∧ nt.P (neg φ) w) :=
  fun _ w ⟨h1, h2⟩ => h2 w (h1 w)

theorem not_mc_nt : ¬ MC nt := by
  intro h
  have := h (fun v => v 0 = true) (bit_based 0 true) (fun _ => true) rfl w0 trivial
  exact Bool.noConfusion this

/-- **`Ax2a` is needed in K22.**  An S5 model on v4's FM carriers, `𝓛`-general for v4's full
`𝓛`, closed as in K1, `E` and `E3` admitted, satisfying `Ax3`, `Ax3v3`, `Ax4`, `Ax2b` and
`Ax1GenTwo`, with God at every world, in which `Ax1Gen`, `Ax2a` and admitted MC fail. -/
theorem need_ax2a :
    LGenF nt ∧ Closed nt ∧ nt.AT (E nt) ∧ nt.AT (E3 nt) ∧ (∀ w v, nt.R w v) ∧
      (∀ y w, nt.act y w) ∧ Ax3 nt ∧ Ax3v3 nt ∧ Ax4 nt ∧ Ax2b nt ∧ Ax1GenTwo nt ∧
      (∀ w, ExG nt w) ∧ (∀ φ w, ¬ (nt.P φ w ∧ nt.P (neg φ) w)) ∧ ¬ Ax1Gen nt ∧ ¬ Ax2a nt ∧
      ¬ MC nt :=
  ⟨lgenF_nt, closed_nt, E_adm_nt, E3_adm_nt, fun _ _ => trivial, fun _ _ => trivial, ax3_nt,
    ax3v3_nt, ax4_nt, ax2b_nt, ax1GenTwo_nt, exG_all, ax2a_cons_nt, not_ax1Gen_nt, not_ax2a_nt, not_mc_nt⟩

end Programme.«20261022-0733-ontological».Run2.NeedAx2a

#print axioms Programme.«20261022-0733-ontological».Run2.NeedAx2a.need_ax2a
