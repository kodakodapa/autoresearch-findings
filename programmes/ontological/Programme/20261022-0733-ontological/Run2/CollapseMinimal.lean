import Programme.«20261022-0733-ontological».Run2.KBMinimal
import Programme.«20261022-0733-ontological».Run2.FMGeneral

/-! # Minimality of `standard_collapse` (thread D)

`Separating.standard_collapse` (K13): full property and collection carriers (`FullTH`),
`Ax1Gen`, `Ax2a` and `Ax3` (or `Ax3v3`) give `∀ w v, R w v → v = w`, MC and `Ax2b`, on every
frame.  Each hypothesis is needed; every countermodel below is closed under our fragment of `𝓛`
(`LGeneral`), is S5 (total `R`) with an edge `R w v`, `v ≠ w`, and refutes admitted MC:

* `FullTH`: `FM.fm` (K13, `FMGeneral.k13_lgeneral`);
* `Ax1Gen`: `KBMinimal.noAx4` (positivity is falsity at `false`; `⊤` is not positive);
* `Ax2a`: `KBMinimal.noAx2a` (everything positive);
* `Ax3` and `Ax3v3`: `truth`, positivity is truth at the current world (the K31 exit). -/
namespace Programme.«20261022-0733-ontological».Run2.CollapseMinimal

open Programme.«20261022-0733-ontological».Run2.TwoClosed Programme.«20261022-0733-ontological».Run2.LGeneral Programme.«20261022-0733-ontological».Run2.StandardKB
  Programme.«20261022-0733-ontological».Run2.KBMinimal

theorem fullTH_two (P) : Separating.FullTH (two P) := ⟨fun _ => trivial, fun _ => trivial⟩

theorem noAx4_not_ax1Gen : ¬ Ax1Gen noAx4 := by
  intro h
  have := h (fun _ _ => False) top trivial trivial false (fun _ _ h => h.elim)
    (fun _ _ _ _ => ⟨fun _ _ _ h => h.elim, fun _ => trivial⟩)
  exact this trivial

theorem noAx2a_ax1Gen : Ax1Gen noAx2a := fun _ _ _ _ _ _ _ => trivial

/-- Positivity is truth at the current world. -/
def truth : Model Bool Unit := two fun φ w => φ () w

theorem truth_props :
    Ax1Gen truth ∧ Ax2a truth ∧ Ax4 truth ∧ ¬ Ax3 truth ∧ ¬ Ax3v3 truth ∧ ¬ Ax2b truth := by
  refine ⟨?_, ?_, ?_, fun h => not_E _ (h false), fun h => not_E3 _ (h false), ?_⟩
  · intro Φ φ _ _ w hpos hconj
    exact ((hconj w trivial () trivial).2 fun ψ _ hψ => hpos ψ trivial hψ)
  · intro φ _ w
    show (φ () w ∨ ¬ φ () w) ∧ ¬ (φ () w ∧ ¬ φ () w)
    exact ⟨Classical.em _, fun ⟨a, b⟩ => b a⟩
  · intro φ ψ _ _ w hφ hinc
    exact hinc w trivial () trivial hφ
  · intro h
    exact Bool.noConfusion (h (fun _ w => w = false) trivial false rfl true trivial : true = false)

/-- **Minimality of `standard_collapse`.** Each of `FullTH`, `Ax1Gen`, `Ax2a`, `Ax3`/`Ax3v3` is
needed: dropping one leaves an S5 model, closed under our fragment of `𝓛`, of the others with an
edge `R w v`, `v ≠ w`, and admitted MC failing. -/
theorem standard_minimal :
    -- no `FullTH`
    (LGeneral FM.fm ∧ (∀ w v, FM.fm.R w v) ∧ Ax1Gen FM.fm ∧ Ax2a FM.fm ∧ Ax3 FM.fm ∧
      Ax3v3 FM.fm ∧ ¬ MC FM.fm) ∧
    -- no `Ax1Gen`
    (LGeneral noAx4 ∧ Separating.FullTH noAx4 ∧ (∀ w v, noAx4.R w v) ∧ Ax2a noAx4 ∧
      Ax3 noAx4 ∧ Ax3v3 noAx4 ∧ ¬ Ax1Gen noAx4 ∧ ¬ (∀ w v, noAx4.R w v → v = w) ∧
      ¬ MC noAx4) ∧
    -- no `Ax2a`
    (LGeneral noAx2a ∧ Separating.FullTH noAx2a ∧ (∀ w v, noAx2a.R w v) ∧ Ax1Gen noAx2a ∧
      Ax3 noAx2a ∧ Ax3v3 noAx2a ∧ ¬ Ax2a noAx2a ∧ ¬ (∀ w v, noAx2a.R w v → v = w) ∧
      ¬ MC noAx2a) ∧
    -- no `Ax3`, no `Ax3v3`
    (LGeneral truth ∧ Separating.FullTH truth ∧ (∀ w v, truth.R w v) ∧ Ax1Gen truth ∧
      Ax2a truth ∧ ¬ Ax3 truth ∧ ¬ Ax3v3 truth ∧ ¬ (∀ w v, truth.R w v → v = w) ∧
      ¬ MC truth) := by
  obtain ⟨hLf, h1f, h2af, h3f, h3vf, _, _, hmf, _⟩ := FMGeneral.k13_lgeneral.2
  obtain ⟨a1, a2, a3, _⟩ := noAx4_props
  obtain ⟨c1, c2, _, c4⟩ := noAx2a_props
  obtain ⟨t1, t2, _, t4, t5, _⟩ := truth_props
  exact ⟨⟨hLf, fun _ _ => trivial, h1f, h2af, h3f, h3vf, hmf⟩,
    ⟨two_lgeneral _, fullTH_two _, fun _ _ => trivial, a1, a2, a3, noAx4_not_ax1Gen,
      two_not_id _, two_not_mc _⟩,
    ⟨two_lgeneral _, fullTH_two _, fun _ _ => trivial, noAx2a_ax1Gen, c1, c2, c4,
      two_not_id _, two_not_mc _⟩,
    ⟨two_lgeneral _, fullTH_two _, fun _ _ => trivial, t1, t2, t4, t5, two_not_id _,
      two_not_mc _⟩⟩

end Programme.«20261022-0733-ontological».Run2.CollapseMinimal

#print axioms Programme.«20261022-0733-ontological».Run2.CollapseMinimal.standard_minimal
