import Programme.«20261022-0733-ontological».Run2.KRow
/-! # God exists only at dead ends (full property carriers)

sk's bounded check (P234 (d)) found every world with a successor other than itself godless.
This holds in every model with all properties admitted, from `Ax3` (or `Ax3v3`) alone:
a God-like `x` at `w` has the positive property `E` (resp. `E₃`), and the nominal essence
`λz u. z = x ∧ u = w` (`StandardKB.deadEnd_of_E`) forces `w` to be a dead end.
No `Ax2a`, `Ax4`, frame condition or actuality hypothesis is used.

* `god_dead`: `G x w → ∀ v, R w v → v = w`.
* `god_everywhere_collapse`: God at every world gives `R ⊆ id`, hence MC and `Ax2b`.
* `escape_godless`: a model refuting MC (or `Ax2b`) has a world without any God-like entity,
  actual or not.  So with full properties, escaping collapse always costs existence somewhere. -/

namespace Programme.«20261022-0733-ontological».Run2.GodDead

open Programme.«20261022-0733-ontological».Run2.TwoClosed Programme.«20261022-0733-ontological».Run2.StandardKB Programme.«20261022-0733-ontological».Run2.DeadEndFrame

variable {W D : Type} {M : Model W D}

theorem god_dead (hF : FullT M) (h3 : Ax3 M ∨ Ax3v3 M) {x : D} {w : W} (hG : G M x w) :
    ∀ v, M.R w v → v = w := by
  rcases h3 with h3 | h3
  · exact deadEnd_of_E hF (hG _ (hF _) (h3 w))
  · exact deadEnd_of_E3 hF (hG _ (hF _) (h3 w))

theorem god_everywhere_collapse (hF : FullT M) (h3 : Ax3 M ∨ Ax3v3 M)
    (hG : ∀ w, ∃ x, G M x w) :
    (∀ w v, M.R w v → v = w) ∧ MC M ∧ Ax2b M := by
  have hR : ∀ w v, M.R w v → v = w := fun w v h =>
    let ⟨_, hx⟩ := hG w; god_dead hF h3 hx v h
  refine ⟨hR, fun _ _ w hp v hv => hR w v hv ▸ hp, fun _ _ w hp v hv => hR w v hv ▸ hp⟩

theorem escape_godless (hF : FullT M) (h3 : Ax3 M ∨ Ax3v3 M) (h : ¬ MC M ∨ ¬ Ax2b M) :
    ∃ w, ∀ x, ¬ G M x w := by
  apply Classical.byContradiction
  intro hn
  have hG : ∀ w, ∃ x, G M x w := fun w =>
    Classical.byContradiction fun hw => hn ⟨w, fun x hx => hw ⟨x, hx⟩⟩
  have := god_everywhere_collapse hF h3 hG
  rcases h with h | h
  · exact h this.2.1
  · exact h this.2.2

end Programme.«20261022-0733-ontological».Run2.GodDead

#print axioms Programme.«20261022-0733-ontological».Run2.GodDead.god_dead
#print axioms Programme.«20261022-0733-ontological».Run2.GodDead.god_everywhere_collapse
#print axioms Programme.«20261022-0733-ontological».Run2.GodDead.escape_godless
