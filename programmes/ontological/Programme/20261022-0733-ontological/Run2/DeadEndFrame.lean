import Programme.«20261022-0733-ontological».Run2.KBMinimal
/-! # What replaces symmetry in `kb_collapse`: the exact frame condition

With full property carriers, Ax2a, Ax3 (variant 2 or 3′) and Ax4 force every world to see a
*reflexive dead end*: a world `v` with `R v v` whose only successor is `v` (`sees_rdeadEnd`,
from `StandardKB.sees_deadEnd` and `KBMinimal.serial`).  Hence:
* `frame_collapse_iff`: `R ⊆ id` holds iff the frame satisfies `C`: a world that sees a dead end
  is that dead end.  Symmetry implies `C`, so this sharpens `kb_collapse`; `C` is strictly
  weaker (it holds vacuously on frames with no dead end).
* `no_model`: on a frame with no reflexive dead end (any irreflexive frame, a 3-cycle) there is
  no full-carrier model of Ax2a, Ax3 (or Ax3v3) and Ax4 at all: the consistency row of the
  atlas over such frames is empty. -/

namespace Programme.«20261022-0733-ontological».Run2.DeadEndFrame

open Programme.«20261022-0733-ontological».Run2.TwoClosed Programme.«20261022-0733-ontological».Run2.StandardKB Programme.«20261022-0733-ontological».Run2.KBMinimal

variable {W D : Type} {M : Model W D}

/-- Dead end: the only successor is itself. -/
def Dead (M : Model W D) (v : W) : Prop := ∀ u, M.R v u → u = v

/-- The frame condition replacing symmetry. -/
def CondC (M : Model W D) : Prop := ∀ w v, M.R w v → Dead M v → w = v

theorem sees_rdeadEnd (hF : FullT M) (h2a : Ax2a M) (h4 : Ax4 M) (h3 : Ax3 M ∨ Ax3v3 M)
    (w : W) : ∃ v, M.R w v ∧ M.R v v ∧ Dead M v := by
  obtain ⟨v, hv, hd⟩ := sees_deadEnd hF h2a h4 h3 w
  obtain ⟨u, hu⟩ := serial (hF _) (hF _) h2a h4 v
  exact ⟨v, hv, hd u hu ▸ hu, hd⟩

theorem frame_collapse_iff (hF : FullT M) (h2a : Ax2a M) (h4 : Ax4 M) (h3 : Ax3 M ∨ Ax3v3 M) :
    (∀ w v, M.R w v → v = w) ↔ CondC M := by
  constructor
  · intro h w v hwv _
    exact (h w v hwv).symm
  · intro hC w u hwu
    obtain ⟨v, hv, _, hd⟩ := sees_rdeadEnd hF h2a h4 h3 w
    have hw : w = v := hC w v hv hd
    subst hw
    exact hd u hwu

theorem symm_condC (hS : ∀ w v, M.R w v → M.R v w) : CondC M :=
  fun w v hwv hd => hd w (hS w v hwv)

/-- Collapse on `C`-frames: `R ⊆ id`, MC, Ax2b. -/
theorem condC_collapse (hF : FullT M) (hC : CondC M) (h2a : Ax2a M) (h4 : Ax4 M)
    (h3 : Ax3 M ∨ Ax3v3 M) : (∀ w v, M.R w v → v = w) ∧ MC M ∧ Ax2b M := by
  have h := (frame_collapse_iff hF h2a h4 h3).2 hC
  exact ⟨h, fun _ _ _ hp _ hwv => (h _ _ hwv) ▸ hp, fun _ _ _ hp _ hwv => (h _ _ hwv) ▸ hp⟩

/-- No full-carrier model on a frame without a reflexive dead end. -/
theorem no_model [Nonempty W] (hF : FullT M) (hno : ∀ v, M.R v v → ¬ Dead M v) :
    ¬ (Ax2a M ∧ Ax4 M ∧ (Ax3 M ∨ Ax3v3 M)) := by
  rintro ⟨h2a, h4, h3⟩
  obtain ⟨w⟩ := ‹Nonempty W›
  obtain ⟨v, _, hvv, hd⟩ := sees_rdeadEnd hF h2a h4 h3 w
  exact hno v hvv hd

/-- Example: the 3-cycle `0 → 1 → 2 → 0` satisfies `C` vacuously, is not symmetric, and carries
no full model of Ax2a, Ax3, Ax4. -/
theorem cycle3 (M : Model (Fin 3) D) (hR : ∀ w v, M.R w v ↔ v.val = (w.val + 1) % 3)
    (hF : FullT M) :
    CondC M ∧ ¬ (∀ w v, M.R w v → M.R v w) ∧ ¬ (Ax2a M ∧ Ax4 M ∧ (Ax3 M ∨ Ax3v3 M)) := by
  have hno : ∀ v, ¬ M.R v v := by
    intro v h; have := (hR v v).1 h; have := v.isLt; omega
  refine ⟨fun w v hwv hd => ?_, fun hS => ?_, no_model hF fun v h _ => hno v h⟩
  · -- `v` sees its successor, which must be `v`: impossible
    have h1 : M.R v ⟨(v.val + 1) % 3, Nat.mod_lt _ (by omega)⟩ := (hR _ _).2 rfl
    have e := hd _ h1
    rw [e] at h1
    exact absurd h1 (hno v)
  · have h1 : M.R 0 1 := (hR _ _).2 rfl
    have := (hR 1 0).1 (hS _ _ h1)
    simp at this

end Programme.«20261022-0733-ontological».Run2.DeadEndFrame

#print axioms Programme.«20261022-0733-ontological».Run2.DeadEndFrame.frame_collapse_iff
#print axioms Programme.«20261022-0733-ontological».Run2.DeadEndFrame.condC_collapse
#print axioms Programme.«20261022-0733-ontological».Run2.DeadEndFrame.no_model
#print axioms Programme.«20261022-0733-ontological».Run2.DeadEndFrame.cycle3
