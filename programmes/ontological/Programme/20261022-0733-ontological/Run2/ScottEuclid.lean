import Programme.«20261022-0733-ontological».Run2.ScottColumn
-- Copied from agents/th/lean/Programme/Th/ScottEuclid.lean (author th); namespaces changed, gap model is my Run2.FiniteBinary.fb (= th sep).

/-! # Scott's variant on Euclidean frames (K42 row extended to K5/KD45)

* `scott_gex_eucl`: closed models (K1's `Closed`, `E` admitted), Euclidean `R`, any actuality:
  Scott's A1–A5 give an actual God-like entity at every world that has an `R`-predecessor.
* `scott_mc_eucl`: and admitted MC holds at each such world (`p w → p v` for `R w v`).
* `scott_kd45_gap`: the finite full model `FiniteBinary.fb` (th: `sep`) (`R w v ↔ v = 0`: serial, transitive,
  Euclidean, i.e. KD45) satisfies A1–A5 and binary A1; world 1 has no predecessor and has no
  `∃ᴱ G`, `UF`, `Princ`; MC fails.  So the predecessor condition cannot be dropped, and KD45
  (like S4, `scott_s4_gap`) does not give Scott's conclusions; S5 = reflexive Euclidean does. -/

namespace Programme.«20261022-0733-ontological».Run2.ScottEuclid

open Programme.«20261022-0733-ontological».Run2 Programme.«20261022-0733-ontological».Run2.TwoClosed Programme.«20261022-0733-ontological».Run2.Ultrafilter Programme.«20261022-0733-ontological».Run2.Principal
  Programme.«20261022-0733-ontological».Run2.Binary Programme.«20261022-0733-ontological».Run2.ScottColumn
open Programme.«20261022-0733-ontological».Run2.LGeneralFull (LGenF)

variable {W D : Type} {M : Model W D}

theorem scott_gex_eucl (C : Closed M) (hE : M.AT (E M)) (h2a : Ax2a M) (h2b : Ax2b M)
    (h3 : Ax3 M) (h4 : Ax4 M) (hL : L M)
    (heu : ∀ u v w, M.R u v → M.R u w → M.R v w) {u w : W} (hu : M.R u w) : ExG M w := by
  obtain ⟨v, hv, hg⟩ := god_succ C h2a h4 hL u
  exact spread C hE h2a h2b h3 hg (heu u v w hv hu)

theorem scott_mc_eucl (C : Closed M) (hE : M.AT (E M)) (h2a : Ax2a M) (h2b : Ax2b M)
    (h3 : Ax3 M) (h4 : Ax4 M) (hL : L M)
    (heu : ∀ u v w, M.R u v → M.R u w → M.R v w) {u w : W} (hu : M.R u w)
    (p : W → Prop) (hp : M.AS p) (hw : p w) (v : W) (hv : M.R w v) : p v := by
  have gw := scott_gex_eucl C hE h2a h2b h3 h4 hL heu hu
  have gv := spread C hE h2a h2b h3 gw hv
  obtain ⟨g, -, hg⟩ := princ_of_gex C h2a gw
  obtain ⟨g', -, hg'⟩ := princ_of_gex C h2a gv
  have pl : M.P (fun _ => p) w := (hg _ (C.lift p hp)).2 hw
  exact (hg' _ (C.lift p hp)).1 (h2b _ (C.lift p hp) w pl v hv)

open Programme.«20261022-0733-ontological».Run2.FiniteBinary

theorem scott_kd45_gap :
    LGenF fb ∧ Closed fb ∧ (∀ w, ∃ v, fb.R w v) ∧
      (∀ a b c, fb.R a b → fb.R b c → fb.R a c) ∧
      (∀ u v w, fb.R u v → fb.R u w → fb.R v w) ∧
      Ax2a fb ∧ Ax4 fb ∧ L fb ∧ Ax2b fb ∧ Ax3 fb ∧ Ax1Bin fb ∧
      (∀ u, ¬ fb.R u true) ∧ ¬ MC fb ∧ ¬ ExG fb true ∧ ¬ UF fb true ∧ ¬ Princ fb true :=
  ⟨fb_sep.1, closed_fb, fun _ => ⟨false, rfl⟩, fun _ _ _ _ h => h, fun _ _ _ _ h => h,
    ax2a_fb, ax4_fb, fun _ _ _ h => h, ax2b_fb, ax3_fb, bin_fb,
    fun _ h => Bool.noConfusion h, not_mc_fb, not_exG1, not_uf1, not_princ1⟩

end Programme.«20261022-0733-ontological».Run2.ScottEuclid

#print axioms Programme.«20261022-0733-ontological».Run2.ScottEuclid.scott_gex_eucl
#print axioms Programme.«20261022-0733-ontological».Run2.ScottEuclid.scott_mc_eucl
#print axioms Programme.«20261022-0733-ontological».Run2.ScottEuclid.scott_kd45_gap
