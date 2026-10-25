import Programme.«20261022-0733-ontological».Run2.KBMinimal

/-! sk audit of K18: in the 3' branch (`Ax3v3`), symmetry is not needed.
Full carriers, `Ax2a`, `Ax4`, `Ax3v3` force a single world on ANY frame. -/
namespace Programme.«20261022-0733-ontological».Run2.V3NoSym

open Programme.«20261022-0733-ontological».Run2.TwoClosed Programme.«20261022-0733-ontological».Run2.StandardKB

variable {W D : Type} {M : Model W D}

theorem v3_singleton (hF : FullT M) (h2a : Ax2a M) (h4 : Ax4 M) (h3 : Ax3v3 M) :
    ∀ a b : W, a = b := by
  intro a b
  obtain ⟨v, y, _, _, hE⟩ := somewhere (hF _) (hF _) h2a h4 (hF _) (h3 a)
  obtain ⟨s, hs⟩ := Programme.«20261022-0733-ontological».Run2.KBMinimal.serial (hF _) (hF _) h2a h4 v
  -- every world is a successor of v
  have all_succ : ∀ c, M.R v c := by
    intro c
    refine Classical.byContradiction fun hc => ?_
    have ess : Ess3 M (fun _ u => u = c) y v := by
      intro ψ _ _ t ht
      refine ⟨fun e => ?_, fun z _ hz => absurd (hz ▸ ht) hc⟩
      have : (fun (_ : D) (u : W) => u = c) y c := rfl
      rw [e] at this; exact this
    obtain ⟨_, _, hz⟩ := hE _ (hF _) ess s hs
    exact hc (hz ▸ hs)
  -- every successor of v is v
  have only_v : ∀ t, M.R v t → t = v := by
    intro t ht
    have ess : Ess3 M (fun z u => z = y ∧ u = v) y v := by
      intro ψ _ hψ r _
      refine ⟨fun e => ?_, fun z _ hz => ?_⟩
      · have : (fun (z : D) (u : W) => z = y ∧ u = v) y v := ⟨rfl, rfl⟩
        rw [e] at this; exact this
      · obtain ⟨rfl, rfl⟩ := hz; exact hψ
    obtain ⟨_, _, _, hz⟩ := hE _ (hF _) ess t ht
    exact hz
  rw [only_v a (all_succ a), only_v b (all_succ b)]

theorem v3_collapse (hF : FullT M) (h2a : Ax2a M) (h4 : Ax4 M) (h3 : Ax3v3 M) :
    ∀ w v, M.R w v → v = w := fun w v _ => v3_singleton hF h2a h4 h3 v w

end Programme.«20261022-0733-ontological».Run2.V3NoSym

#print axioms Programme.«20261022-0733-ontological».Run2.V3NoSym.v3_singleton
#print axioms Programme.«20261022-0733-ontological».Run2.V3NoSym.v3_collapse
