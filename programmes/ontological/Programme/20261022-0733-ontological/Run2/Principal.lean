import Programme.«20261022-0733-ontological».Run2.Ultrafilter

/-! Copied from th's `Programme/Th/Principal.lean` (author th); namespace and import changed.

# The principality column (F1) and the two exits from collapse

`Princ M w`: admitted positivity at `w` is the principal filter of an entity actual at `w`
(Henkin, current-world reading of F1 with the generator a single actual entity).

* `uf_of_princ`: principality gives the ultrafilter property `UF` (needs `Closed` only).
* `princ_of_gex`: `Ax2a` and an actual God-like being at `w` give `Princ M w`.
* `princ_of_2a4two`: `Closed`, `D ≠ ∅`, `Ax2a`, `Ax4`, `Ax1GenTwo` give `Princ` at every world
  (no `Ax2b`, `Ax3`, `MC`); `princ_minimal`: each needed (K34's witnesses; via `uf_of_princ`).
* `mc_of_princ_2b`: `Closed`, principality at every world and `Ax2b` give admitted `MC`, any frame.
* `exits`: `fm` is principal everywhere, not rigid, no `MC`; `rx` is rigid, principal nowhere,
  no `MC`. So {principality, rigidity} is a minimal collapse base and the two exits are distinct. -/

namespace Programme.«20261022-0733-ontological».Run2.Principal

open Programme.«20261022-0733-ontological».Run2 Programme.«20261022-0733-ontological».Run2.TwoClosed Programme.«20261022-0733-ontological».Run2.Ultrafilter
open Programme.«20261022-0733-ontological».Run2.LGeneralFull (LGenF)

variable {W D : Type} {M : Model W D}

/-- F1 (current world, Henkin): positivity at `w` is principal at an entity actual at `w`. -/
def Princ (M : Model W D) (w : W) : Prop :=
  ∃ g, M.act g w ∧ ∀ φ, M.AT φ → (M.P φ w ↔ φ g w)

theorem uf_of_princ (C : Closed M) {w : W} (h : Princ M w) : UF M w := by
  obtain ⟨g, hg, hp⟩ := h
  refine ⟨(hp _ C.top).2 trivial, fun hb => (hp _ C.bot).1 hb, ?_, ?_, ?_⟩
  · intro φ ψ hφ hψ pφ hinc; exact (hp ψ hψ).2 (hinc g hg ((hp φ hφ).1 pφ))
  · intro φ ψ hφ hψ pφ pψ
    exact (hp _ (C.conj _ _ hφ hψ)).2 ⟨(hp φ hφ).1 pφ, (hp ψ hψ).1 pψ⟩
  · intro φ hφ
    by_cases e : φ g w
    · exact Or.inl ((hp φ hφ).2 e)
    · exact Or.inr ((hp _ (C.neg _ hφ)).2 e)

theorem princ_of_gex (C : Closed M) (h2a : Ax2a M) {w : W} (h : ExG M w) : Princ M w := by
  obtain ⟨y, hy, hG⟩ := h
  refine ⟨y, hy, fun φ hφ => ⟨hG φ hφ, fun hφy => ?_⟩⟩
  exact ((h2a φ hφ w).1).resolve_right fun pn => hG _ (C.neg _ hφ) pn hφy

theorem princ_of_2a4two [Nonempty D] (C : Closed M) (h2a : Ax2a M) (h4 : Ax4 M)
    (hT : Ax1GenTwo M) (w : W) : Princ M w :=
  princ_of_gex C h2a (GexTwo.gex_2a4 C h2a h4 hT w)

/-- **Principality and rigidity give collapse**, any frame and actuality. -/
theorem mc_of_princ_2b (C : Closed M) (hp : ∀ w, Princ M w) (h2b : Ax2b M) : MC M := by
  intro p hp' w hw v hv
  obtain ⟨g, -, hg⟩ := hp w
  obtain ⟨g', -, hg'⟩ := hp v
  have pl : M.P (fun _ => p) w := (hg _ (C.lift p hp')).2 hw
  exact (hg' _ (C.lift p hp')).1 (h2b _ (C.lift p hp') w pl v hv)

/-- **Each of `Ax2a`, `Ax4`, `Ax1GenTwo` is needed for `princ_of_2a4two`**; the witnesses are
principal at no world. -/
theorem princ_minimal :
    (LGenF Minimal.noAx2a ∧ Closed Minimal.noAx2a ∧ Ax4 Minimal.noAx2a ∧
      Ax1GenTwo Minimal.noAx2a ∧ ¬ Ax2a Minimal.noAx2a ∧ ∀ w, ¬ Princ Minimal.noAx2a w) ∧
    (LGenF TwoNeedsAx2a.anti ∧ Closed TwoNeedsAx2a.anti ∧ Ax2a TwoNeedsAx2a.anti ∧
      Ax1GenTwo TwoNeedsAx2a.anti ∧ ¬ Ax4 TwoNeedsAx2a.anti ∧ ∀ w, ¬ Princ TwoNeedsAx2a.anti w) ∧
    (LGenF RigidExit.rx ∧ Closed RigidExit.rx ∧ Ax2a RigidExit.rx ∧ Ax4 RigidExit.rx ∧
      ¬ Ax1GenTwo RigidExit.rx ∧ ∀ w, ¬ Princ RigidExit.rx w) := by
  obtain ⟨⟨a1, a2, a3, a4, a5, a6⟩, ⟨b1, b2, b3, b4, b5, b6⟩, ⟨c1, c2, c3, c4, c5, c6⟩⟩ :=
    uf_minimal
  exact ⟨⟨a1, a2, a3, a4, a5, fun w h => a6 w (uf_of_princ a2 h)⟩,
    ⟨b1, b2, b3, b4, b5, fun w h => b6 w (uf_of_princ b2 h)⟩,
    ⟨c1, c2, c3, c4, c5, fun w h => c6 w (uf_of_princ c2 h)⟩⟩

/-- **The two exits are distinct.** `fm`: principal everywhere, `Ax2b` fails, `MC` fails.
`rx`: `Ax2b` holds, principal nowhere, `MC` fails. Both `LGenF` and `Closed`. -/
theorem exits :
    (LGenF FM.fm ∧ Closed FM.fm ∧ (∀ w, Princ FM.fm w) ∧ ¬ Ax2b FM.fm ∧ ¬ MC FM.fm) ∧
    (LGenF RigidExit.rx ∧ Closed RigidExit.rx ∧ Ax2b RigidExit.rx ∧
      (∀ w, ¬ Princ RigidExit.rx w) ∧ ¬ MC RigidExit.rx) := by
  obtain ⟨l8, h2a, -, -, -, -, -, -, -, -, -, -, hg, n2b, nmc⟩ := AtlasFull.k8_full
  obtain ⟨-, -, ⟨c1, c2, -, -, -, c6⟩⟩ := princ_minimal
  exact ⟨⟨l8, FM.closed_fm, fun w => princ_of_gex FM.closed_fm h2a (hg w), n2b, nmc⟩,
    ⟨c1, c2, RigidExit.ax2b, c6, RigidExit.not_mc⟩⟩

end Programme.«20261022-0733-ontological».Run2.Principal

#print axioms Programme.«20261022-0733-ontological».Run2.Principal.uf_of_princ
#print axioms Programme.«20261022-0733-ontological».Run2.Principal.princ_of_2a4two
#print axioms Programme.«20261022-0733-ontological».Run2.Principal.mc_of_princ_2b
#print axioms Programme.«20261022-0733-ontological».Run2.Principal.princ_minimal
#print axioms Programme.«20261022-0733-ontological».Run2.Principal.exits
