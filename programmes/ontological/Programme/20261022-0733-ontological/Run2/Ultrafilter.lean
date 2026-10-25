import Programme.«20261022-0733-ontological».Run2.GexTwo
import Programme.«20261022-0733-ontological».Run2.AtlasFull

/-! # The ultrafilter column (copied from th's `Programme.Th.Ultrafilter`, author th; namespace and import changed): `Ax2a`, `Ax4`, `Ax1GenTwo` make positivity an ultrafilter

`UF M w` is the paper's `UFilter P` at `w` (library `OpenQuestions/Ax1GenTwoVariant2.lean`,
`Filter`/`UFilter`), read over admitted properties: `⊤` positive, `⊥` not positive, upward closed
under the *local* actualist inclusion `⊆ᴱ` at `w` (no box), closed under binary meets, and prime.

* `uf_of_2a4two`: over `Closed`, `D ≠ ∅`, any frame and actuality, `Ax2a`, `Ax4`, `Ax1GenTwo` give
  `UF M w` at every world.  No `Ax2b`, no `MC`, no essence, no `Ax3`.  The paper's `PisFilter`
  boxes the local inclusion with `MC_Two`; here the local step uses instead the actual God-like
  being at `w` (K34, `gex_2a4`): if `φ` is positive and `ψ` is not, `φ ∧ ¬ψ` is positive by
  `Ax2a` and the meet, so the actual God-like being at `w` has `φ` but not `ψ`.
* `uf_minimal`: each hypothesis is needed; every witness is `LGenF` and `Closed` and fails `UF`
  at **every** world (`noAx2a`: `⊥` positive; `anti`: `⊤` not positive; `rx`: not upward closed).
* `uf_without_collapse`: K8's `fm` has `UF` at every world but refutes admitted `MC` and `Ax2b`.
  The ultrafilter property does not drive collapse (cf. arXiv 2608.07578's thesis). -/

namespace Programme.«20261022-0733-ontological».Run2.Ultrafilter

open Programme.«20261022-0733-ontological».Run2 Programme.«20261022-0733-ontological».Run2.TwoClosed
open Programme.«20261022-0733-ontological».Run2.LGeneralFull (LGenF)

variable {W D : Type} {M : Model W D}

/-- The paper's `UFilter P` at `w`, over admitted properties, local inclusion `⊆ᴱ`. -/
def UF (M : Model W D) (w : W) : Prop :=
  M.P top w ∧ ¬ M.P bot w ∧
  (∀ φ ψ, M.AT φ → M.AT ψ → M.P φ w → (∀ x, M.act x w → φ x w → ψ x w) → M.P ψ w) ∧
  (∀ φ ψ, M.AT φ → M.AT ψ → M.P φ w → M.P ψ w → M.P (conj φ ψ) w) ∧
  (∀ φ, M.AT φ → M.P φ w ∨ M.P (neg φ) w)

/-- Binary meets from `Ax1GenTwo` (`Φ = {φ, ψ}`). -/
theorem meet (C : Closed M) (hT : Ax1GenTwo M) {φ ψ : D → W → Prop} (hφ : M.AT φ) (hψ : M.AT ψ)
    {w : W} (pφ : M.P φ w) (pψ : M.P ψ w) : M.P (conj φ ψ) w := by
  by_cases e : φ = ψ
  · subst e
    have : conj φ φ = φ := funext fun x => funext fun v => propext and_self_iff
    rw [this]; exact pφ
  · exact hT (fun χ _ => χ = φ ∨ χ = ψ) (conj φ ψ)
      (C.union _ _ (C.single _ hφ) (C.single _ hψ)) (C.conj _ _ hφ hψ) w
      ⟨φ, ψ, hφ, hψ, Or.inl rfl, Or.inr rfl, e⟩
      (fun χ _ h => h.elim (fun h => h ▸ pφ) (fun h => h ▸ pψ))
      (fun v _ z _ => ⟨fun ⟨a, b⟩ χ _ h => h.elim (fun h => h ▸ a) (fun h => h ▸ b),
        fun h => ⟨h φ hφ (Or.inl rfl), h ψ hψ (Or.inr rfl)⟩⟩)

/-- **Ultrafilter at every world** from `Closed`, `Ax2a`, `Ax4`, `Ax1GenTwo`; any frame. -/
theorem uf_of_2a4two [Nonempty D] (C : Closed M) (h2a : Ax2a M) (h4 : Ax4 M) (hT : Ax1GenTwo M)
    (w : W) : UF M w := by
  have pt := TwoNeedsAx2a.pTop_of_2a4 C h2a h4 w
  refine ⟨pt, fun pb => ?_, ?_, fun φ ψ hφ hψ => meet C hT hφ hψ, fun φ hφ => (h2a φ hφ w).1⟩
  · have e : neg (bot : D → W → Prop) = top := TwoNeedsAx2a.neg_bot_eq
    exact (h2a bot C.bot w).2 ⟨pb, e ▸ pt⟩
  · intro φ ψ hφ hψ pφ hinc
    refine Classical.byContradiction fun nψ => ?_
    have pn : M.P (neg ψ) w := ((h2a ψ hψ w).1).resolve_left nψ
    have pc := meet C hT hφ (C.neg _ hψ) pφ pn
    obtain ⟨y, hy, hG⟩ := GexTwo.gex_2a4 C h2a h4 hT w
    obtain ⟨a, b⟩ := hG _ (C.conj _ _ hφ (C.neg _ hψ)) pc
    exact b (hinc y hy a)

/-! ## Each hypothesis is needed -/

theorem noAx2a_not_uf (w : Bool) : ¬ UF Minimal.noAx2a w := fun h => h.2.1 trivial

theorem anti_not_uf (w : Bool) : ¬ UF TwoNeedsAx2a.anti w := fun h => h.1 trivial

theorem rx_not_uf (w : RigidExit.Wd) : ¬ UF RigidExit.rx w := by
  intro ⟨pt, _, up, _, _⟩
  obtain ⟨i, -, hi⟩ := w.2.1 0
  let ψ : Unit → RigidExit.Wd → Prop := fun _ v => v.1 i = true
  have hψ : RigidExit.rx.AT ψ := RigidExit.bit_adm i true
  have pψ : RigidExit.rx.P ψ w := up top ψ RigidExit.top_adm hψ pt (fun _ _ _ => hi)
  have pn : RigidExit.rx.P (neg ψ) w :=
    ⟨i + 1, fun v hv (h : v.1 i = true) => by rw [hv i (Nat.lt_succ_self i)] at h; exact Bool.noConfusion h⟩
  exact (RigidExit.ax2a ψ hψ w).2 ⟨pψ, pn⟩

/-- **Each of `Ax2a`, `Ax4`, `Ax1GenTwo` is needed for `uf_of_2a4two`.** -/
theorem uf_minimal :
    -- without `Ax2a`
    (LGenF Minimal.noAx2a ∧ Closed Minimal.noAx2a ∧ Ax4 Minimal.noAx2a ∧
      Ax1GenTwo Minimal.noAx2a ∧ ¬ Ax2a Minimal.noAx2a ∧ ∀ w, ¬ UF Minimal.noAx2a w) ∧
    -- without `Ax4`
    (LGenF TwoNeedsAx2a.anti ∧ Closed TwoNeedsAx2a.anti ∧ Ax2a TwoNeedsAx2a.anti ∧
      Ax1GenTwo TwoNeedsAx2a.anti ∧ ¬ Ax4 TwoNeedsAx2a.anti ∧ ∀ w, ¬ UF TwoNeedsAx2a.anti w) ∧
    -- without `Ax1GenTwo`
    (LGenF RigidExit.rx ∧ Closed RigidExit.rx ∧ Ax2a RigidExit.rx ∧ Ax4 RigidExit.rx ∧
      ¬ Ax1GenTwo RigidExit.rx ∧ ∀ w, ¬ UF RigidExit.rx w) := by
  obtain ⟨⟨a1, a2, a3, a4, a5, -⟩, ⟨b1, b2, b3, b4, b5, -⟩, ⟨c1, c2, c3, c4, c5, -⟩⟩ :=
    GexTwo.gex_minimal
  exact ⟨⟨a1, a2, a3, a4, a5, noAx2a_not_uf⟩, ⟨b1, b2, b3, b4, b5, anti_not_uf⟩,
    ⟨c1, c2, c3, c4, c5, rx_not_uf⟩⟩

/-- **Ultrafilter without collapse**: K8's `fm` (`LGenF`) has `UF` at every world, `MC` and
`Ax2b` fail. -/
theorem uf_without_collapse :
    LGenF FM.fm ∧ Closed FM.fm ∧ (∀ w, UF FM.fm w) ∧ ¬ MC FM.fm ∧ ¬ Ax2b FM.fm := by
  obtain ⟨l8, h2a, -, -, h4, -, -, -, -, h2, -, -, -, n2b, nmc⟩ := AtlasFull.k8_full
  exact ⟨l8, FM.closed_fm, uf_of_2a4two FM.closed_fm h2a h4 h2, nmc, n2b⟩

end Programme.«20261022-0733-ontological».Run2.Ultrafilter

#print axioms Programme.«20261022-0733-ontological».Run2.Ultrafilter.uf_of_2a4two
#print axioms Programme.«20261022-0733-ontological».Run2.Ultrafilter.uf_minimal
#print axioms Programme.«20261022-0733-ontological».Run2.Ultrafilter.uf_without_collapse
