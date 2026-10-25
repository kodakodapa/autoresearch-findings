/- Rebased with attribution to th P386. -/
import Programme.«20261021-1639-ontological».Atlas.V2DeepFull

/-! D17 (open in P348/P354): on symmetric frames, do deep variant-2 Ax1, Ax2a, Ax2b, Ax3, Ax4
(no Ax1Gen) force modal collapse in closed Henkin semantics? **No**, already on S5 frames.

Worlds `ℕ × (ℕ → Bool)` ("slot `k`, stream `s`"), universal accessibility, one always-actual
entity. Group: families of xor masks `g : ℕ → ℕ → Bool` acting slotwise,
`(k, s) ↦ (k, s ⊕ g k)`; `K n` = masks vanishing on `k < n, j < n`. So a symmetric proposition
of level `n` is, on each slot `k ≥ n`, either everywhere true or everywhere false, and on every
slot it is invariant under flipping any stream coordinate `j ≥ n`.

Positivity (rigid): `𝒫 φ :⇔ U {k | ∀ s, φ () (k, s)}` for the Zorn-free free ultrafilter `U`
(K44). It is invariant under the group, so `SymmetricModels.unitModel` gives a closed K36 model.
* Ax2a: on slots `k ≥ n` each admitted `φ` is constant, and `U` contains the cofinite sets.
* Ax1, Ax4: `U` is a filter. Ax2b: positivity does not depend on the world.
* Ax3: no admitted property is an essence (flip a stream coordinate `j ≥ n`), so NE is `⊤`.
* MC fails: `w.1 = 0` is admitted. NecEx fails: `k < w.1` is positive. Hence Ax1Gen fails. -/

namespace Programme.«20261021-1639-ontological».Atlas.D17
open Programme.«20261021-1639-ontological».Deep Programme.«20261021-1639-ontological».Deep.Henkin Programme.«20261021-1639-ontological».Atlas.SymmetricClosure
open Programme.«20261021-1639-ontological».Atlas.HenkinScott Programme.«20261021-1639-ontological».Atlas.SymmetricModels
open Programme.«20261021-1639-ontological».Atlas.ScottBridge Programme.«20261021-1639-ontological».Atlas.ScottDeep Programme.«20261021-1639-ontological».Atlas.V2Deep
open Programme.«20261021-1639-ontological».Atlas.V2DeepFull

abbrev Wd := Nat × Wc

def dmask (g : Nat → Wc) (w : Wd) : Wd := (w.1, mask (g w.1) w.2)

def dsym : Sym Wd Unit where
  G := Nat → Wc
  mul g h := fun k j => xor (g k j) (h k j)
  inv g := g
  aw := dmask
  ae _ x := x
  aw_mul g h w := by
    obtain ⟨k, s⟩ := w
    simp only [dmask]
    congr 1; funext j; unfold mask; show xor (s j) (xor (g k j) (h k j)) = xor (xor (s j) (h k j)) (g k j)
    cases s j <;> cases g k j <;> cases h k j <;> rfl
  ae_mul _ _ _ := rfl
  aw_inv g w := by
    obtain ⟨k, s⟩ := w
    simp only [dmask]
    congr 1; funext j; unfold mask
    cases s j <;> cases g k j <;> rfl
  aw_inv' g w := by
    obtain ⟨k, s⟩ := w
    simp only [dmask]
    congr 1; funext j; unfold mask
    cases s j <;> cases g k j <;> rfl
  ae_inv _ _ := rfl
  ae_inv' _ _ := rfl
  K n g := ∀ k j, k < n → j < n → g k j = false
  anti hnm h k j hk hj := h k j (Nat.lt_of_lt_of_le hk hnm) (Nat.lt_of_lt_of_le hj hnm)
  normal g n := ⟨n, fun h hh k j hk hj => by
    show xor (g k j) (xor (h k j) (g k j)) = false
    rw [hh k j hk hj]; generalize g k j = a; revert a; decide⟩
  ent_supp _ := ⟨0, fun _ _ => rfl⟩

theorem dsym_K0 : ∀ g, dsym.K 0 g := fun _ _ _ hk => absurd hk (Nat.not_lt_zero _)

/-- Rigid free-ultrafilter positivity on necessity slots. -/
def posD (f : Unit → Wd → Prop) : Prop := FreeUltra.U (fun k => ∀ s, f () (k, s))

theorem posD_inv : ∀ (g : dsym.G) (f : (car dsym Property).T),
    posD (propT dsym ((car dsym Property).act g f)) = posD (propT dsym f) := by
  intro g f
  unfold posD
  congr 1
  funext k
  apply propext; constructor
  · intro h s
    have := h (mask (g k) s)
    have e : dsym.aw (dsym.inv g) (k, mask (g k) s) = (k, s) := dsym.aw_inv g (k, s)
    simpa only [propT, e] using this
  · intro h s; exact h _

noncomputable def dModel : Henkin.Model OntConst Wd :=
  unitModel dsym dsym_K0 (rigidPos dsym posD posD_inv) (fun g _ f =>
    Subtype.ext (funext fun _ => posD_inv g f))

def dgm : GModel Wd Unit where
  rel _ _ := True
  actual _ _ := True
  adm p := SymProp dsym (p ())
  admP p := SymProp dsym p
  positive p _ := posD p

theorem d_presentation : Presents dModel dgm := by
  obtain ⟨h1, h2, _, _, _⟩ := presentation dsym_K0 (rigidPos dsym posD posD_inv) (fun g _ f =>
    Subtype.ext (funext fun _ => posD_inv g f))
  exact ⟨h1, h2, fun _ _ => iff_of_true trivial trivial, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩

/-! ### Symmetric propositions. -/

/-- On a slot `k ≥ n` a level-`n` proposition is constant. -/
theorem tail_const {p : Wd → Prop} {n : Nat} (hn : ∀ g, dsym.K n g → ∀ w, p (dsym.aw g w) = p w)
    {k : Nat} (hk : n ≤ k) (s s' : Wc) : p (k, s) ↔ p (k, s') := by
  let g : dsym.G := fun k' i => if k' = k then xor (s i) (s' i) else false
  have hg : dsym.K n g := fun k' _ hk' _ => by
    have : k' ≠ k := by omega
    simp [g, this]
  have e : dsym.aw g (k, s) = (k, s') := by
    show (k, mask (g k) s) = (k, s')
    congr 1; funext i; simp only [mask, g, if_pos rfl]
    generalize s i = a; generalize s' i = b; revert a b; decide
  rw [← e, hn g hg]

/-- Flipping a stream coordinate `j ≥ n` preserves a level-`n` proposition. -/
theorem flip_inv {p : Wd → Prop} {n : Nat} (hn : ∀ g, dsym.K n g → ∀ w, p (dsym.aw g w) = p w)
    (k : Nat) (s : Wc) {j : Nat} (hj : n ≤ j) : p (k, HenkinScott.flip s j) ↔ p (k, s) := by
  let g : dsym.G := fun _ i => decide (i = j)
  have hg : dsym.K n g := fun _ i _ hi => by
    have : i ≠ j := by omega
    simp [g, this]
  have e : dsym.aw g (k, s) = (k, HenkinScott.flip s j) := by
    show (k, mask (g k) s) = (k, HenkinScott.flip s j)
    congr 1; funext i
    by_cases h : i = j
    · subst h; simp [mask, HenkinScott.flip, g]
    · simp [mask, HenkinScott.flip, g, h]
  rw [← e, hn g hg]

theorem slot_sym (c : Nat → Prop) : SymProp dsym (fun w => c w.1) := ⟨0, fun _ _ _ => rfl⟩

/-- No admitted property is an essence of the entity at any world. -/
theorem no_essence (a : Bool) (p : Unit → Wd → Prop) (hp : dgm.adm p) (w : Wd) :
    ¬ EssH dgm a p () w := by
  obtain ⟨k, s⟩ := w
  intro ⟨hpt, hq⟩
  obtain ⟨n, hn⟩ := hp
  let j := n + k
  have hflip : p () (k, HenkinScott.flip s j) := (flip_inv hn k s (Nat.le_add_right n k)).2 hpt
  have hadm : dgm.adm (fun _ w => w.1 = k ∧ w.2 j = s j) := by
    refine ⟨n + k + 1, fun g hg w => propext ?_⟩
    obtain ⟨k', s'⟩ := w
    show (k' = k ∧ xor (s' j) (g k' j) = s j) ↔ (k' = k ∧ s' j = s j)
    constructor
    · rintro ⟨rfl, h⟩
      rw [hg k' j (by omega) (by omega)] at h
      exact ⟨rfl, by simpa using h⟩
    · rintro ⟨rfl, h⟩
      rw [hg k' j (by omega) (by omega)]
      exact ⟨rfl, by simpa using h⟩
  have := (hq _ hadm ⟨rfl, rfl⟩ (k, HenkinScott.flip s j) trivial () (fun _ => trivial) hflip).2
  simp [HenkinScott.flip] at this

/-! ### The GModel axioms. -/

theorem d_ax1 : HenkinVariant2.Ax1 dgm := by
  intro p q w _ _ hp hq
  exact FreeUltra.U_good.2.2.1 _ _ (FreeUltra.U_good.2.2.2 _ _ hp hq)
    fun _ h s => ⟨h.1 s, h.2 s⟩

theorem d_ax2a : HenkinVariant2.Ax2a dgm := by
  intro p w hp
  obtain ⟨n, hn⟩ := hp
  refine ⟨?_, fun ⟨h1, h2⟩ => ?_⟩
  · rcases FreeUltra.U_ultra (fun k => ∀ s, p () (k, s)) with h | h
    · exact Or.inl h
    · refine Or.inr (FreeUltra.U_good.2.2.1 _ _ (FreeUltra.U_good.2.2.2 _ _ h
        (FreeUltra.U_frechet _ ⟨n, fun k hk => hk⟩)) fun k ⟨hk, hnk⟩ s hs => hk fun s' => ?_)
      exact (tail_const hn hnk s s').1 hs
  · exact FreeUltra.U_good.2.1 (FreeUltra.U_good.2.2.1 _ _ (FreeUltra.U_good.2.2.2 _ _ h1 h2)
      fun _ h => h.2 (fun _ => false) (h.1 _))

theorem d_ax4 (a : Bool) : HenkinVariant2.Ax4 dgm a := by
  intro p q w _ _ hp hsub
  exact FreeUltra.U_good.2.2.1 _ _ hp fun k hk s =>
    hsub (k, s) trivial () (fun _ => trivial) (hk s)

theorem d_ax3 (a : Bool) : A5 dgm a := by
  intro w
  apply FreeUltra.U_good.2.2.1 _ _ FreeUltra.U_good.1
  intro k _ s p hp he
  exact (no_essence a p hp (k, s) he).elim

/-- D17 answered negatively: an S5 closed Henkin model validating deep Ax1, Ax2a, Ax2b, Ax3 and
Ax4 but not MC, not `□∃ᵍ G` and not Ax1Gen, in both uniform guard regimes. -/
theorem d17 (a : Bool) (ρ : Assignment dModel.frame []) :
    (∀ w v, dModel.frame.rel w v) ∧
    DeepValid dModel ρ tAx1 ∧ DeepValid dModel ρ tAx2a ∧ DeepValid dModel ρ tA4 ∧
    DeepValid dModel ρ (tA5 a) ∧ DeepValid dModel ρ (tAx4 a) ∧
    ¬ DeepValid dModel ρ tMC ∧ ¬ DeepValid dModel ρ (tNecEx a) ∧
    ¬ DeepValid dModel ρ (tAx1Gen a) := by
  have hp := d_presentation
  have d2 := (bridge_Ax2a hp ρ).2 d_ax2a
  have nne : ¬ DeepValid dModel ρ (tNecEx a) := fun h => by
    obtain ⟨x, _, hg⟩ := (bridge_NecEx hp a ρ).1 h (0, fun _ => false) (0, fun _ => false) trivial
    have := hg (fun _ w => 0 < w.1) (slot_sym _)
      (FreeUltra.U_frechet _ ⟨1, fun k hk _ => hk⟩)
    exact Nat.lt_irrefl 0 this
  refine ⟨fun w v => (hp.2.2.1 w v).2 trivial, (bridge_Ax1 hp ρ).2 d_ax1, d2,
    (bridge_A4 hp ρ).2 fun _ _ _ h _ _ => h, (bridge_A5 hp a ρ).2 (d_ax3 a),
    (bridge_Ax4 hp a ρ).2 (d_ax4 a), fun h => ?_, nne, fun h => nne (deep_v2 a ρ h d2).2⟩
  have := (bridge_MC hp ρ).1 h (fun w => w.1 = 0) (slot_sym (fun k => k = 0)) (0, fun _ => false) rfl
    (1, fun _ => false) trivial
  exact Nat.one_ne_zero this

#print axioms d_presentation
#print axioms no_essence
#print axioms d17
end Programme.«20261021-1639-ontological».Atlas.D17
