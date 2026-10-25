import Programme.«20261021-1639-ontological».Atlas.D17

/-! Symmetric-frame T row, Ax1Gen deletion (open after P386, pr P375).

D17's model plus one extra world `none` fixed by the group, with accessibility
`R w v :⇔ ¬ (w = none ∧ v = none)`: symmetric, every slot world reflexive, `none` irreflexive.
Positivity is D17's rigid free-ultrafilter positivity read on the slot worlds only.
* Ax1, Ax2a, Ax2b, Ax4: as in D17 (every slot world is a successor of every world).
* Ax3: no admitted property is an essence at a slot world, so NE holds on every slot world.
  (`none` may carry essences; positivity never looks at `none`.)
* T fails at `none`: the admitted `isSome` holds at every successor of `none`, not at `none`.
  Hence Ax1Gen fails (`deep_v2`).
So on symmetric frames `{Ax1Gen, Ax2a}` stays the unique minimal deep T set over the six-menu
(with pr's symmetric dead-end Ax2a deletion, K78). -/

namespace Programme.«20261021-1639-ontological».Atlas.D17T
open Programme.«20261021-1639-ontological».Deep Programme.«20261021-1639-ontological».Deep.Henkin Programme.«20261021-1639-ontological».Atlas.SymmetricClosure
open Programme.«20261021-1639-ontological».Atlas.HenkinScott Programme.«20261021-1639-ontological».Atlas.SymmetricModels
open Programme.«20261021-1639-ontological».Atlas.ScottBridge Programme.«20261021-1639-ontological».Atlas.ScottDeep Programme.«20261021-1639-ontological».Atlas.V2Deep
open Programme.«20261021-1639-ontological».Atlas.V2DeepFull Programme.«20261021-1639-ontological».Atlas.D17

abbrev We := Option Wd

def emask (g : Nat → Wc) : We → We
  | none => none
  | some w => some (dmask g w)

def esym : Sym We Unit where
  G := Nat → Wc
  mul g h := fun k j => xor (g k j) (h k j)
  inv g := g
  aw := emask
  ae _ x := x
  aw_mul g h w := by
    cases w with
    | none => rfl
    | some w => exact congrArg some (dsym.aw_mul g h w)
  ae_mul _ _ _ := rfl
  aw_inv g w := by
    cases w with
    | none => rfl
    | some w => exact congrArg some (dsym.aw_inv g w)
  aw_inv' g w := by
    cases w with
    | none => rfl
    | some w => exact congrArg some (dsym.aw_inv' g w)
  ae_inv _ _ := rfl
  ae_inv' _ _ := rfl
  K := dsym.K
  anti := dsym.anti
  normal := dsym.normal
  ent_supp _ := ⟨0, fun _ _ => rfl⟩

theorem esym_K0 : ∀ g, esym.K 0 g := dsym_K0

def eRel (w v : We) : Prop := ¬ (w = none ∧ v = none)

theorem eRel_inv : ∀ g w v, eRel (esym.aw g w) (esym.aw g v) ↔ eRel w v := by
  intro g w v
  cases w <;> cases v <;> simp [eRel, esym, emask]

/-- D17 positivity on the slot worlds. -/
def posE (f : Unit → We → Prop) : Prop := FreeUltra.U (fun k => ∀ s, f () (some (k, s)))

theorem posE_inv : ∀ (g : esym.G) (f : (car esym Property).T),
    posE (propT esym ((car esym Property).act g f)) = posE (propT esym f) := by
  intro g f
  unfold posE
  congr 1
  funext k
  apply propext; constructor
  · intro h s
    have := h (mask (g k) s)
    have e : esym.aw (esym.inv g) (some (k, mask (g k) s)) = some (k, s) :=
      esym.aw_inv g (some (k, s))
    simpa only [propT, e] using this
  · intro h s; exact h _

noncomputable def eModel : Henkin.Model OntConst We :=
  model (S := esym) (R := eRel) (SymmetricModels.interp esym (rigidPos esym posE posE_inv))
    eRel_inv (interp_inv esym_K0 (rigidPos esym posE posE_inv) (fun g _ f =>
      Subtype.ext (funext fun _ => posE_inv g f)))

def egm : GModel We Unit where
  rel := eRel
  actual _ _ := True
  adm p := SymProp esym (p ())
  admP p := SymProp esym p
  positive p _ := posE p

theorem e_presentation : Presents eModel egm :=
  ⟨fun p => admitted_iff p, fun f => unit_property_iff (S := esym) f,
    fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩

/-- Slot invariance of an `esym`-symmetric proposition, restricted to slot worlds. -/
theorem slot_hyp {p : We → Prop} {n : Nat} (hn : ∀ g, esym.K n g → ∀ w, p (esym.aw g w) = p w) :
    ∀ g, dsym.K n g → ∀ w, p (some (dsym.aw g w)) = p (some w) :=
  fun g hg w => hn g hg (some w)

theorem no_essence (a : Bool) (p : Unit → We → Prop) (hp : egm.adm p) (k : Nat) (s : Wc) :
    ¬ EssH egm a p () (some (k, s)) := by
  intro ⟨hpt, hq⟩
  obtain ⟨n, hn⟩ := hp
  let j := n + k
  have hflip : p () (some (k, HenkinScott.flip s j)) :=
    (flip_inv (p := fun w => p () (some w)) (slot_hyp hn) k s (Nat.le_add_right n k)).2 hpt
  have hadm : egm.adm (fun _ w => ∃ s', w = some (k, s') ∧ s' j = s j) := by
    refine ⟨n + k + 1, fun g hg w => propext ?_⟩
    cases w with
    | none => simp [esym, emask]
    | some w =>
      obtain ⟨k', s'⟩ := w
      show (∃ t, some (k', mask (g k') s') = some (k, t) ∧ t j = s j) ↔
        (∃ t, some (k', s') = some (k, t) ∧ t j = s j)
      constructor
      · rintro ⟨t, ht, htj⟩
        cases ht
        refine ⟨s', rfl, ?_⟩
        have := hg k j (by omega) (by omega)
        simpa [mask, this] using htj
      · rintro ⟨t, ht, htj⟩
        cases ht
        refine ⟨mask (g k) s', rfl, ?_⟩
        have := hg k j (by omega) (by omega)
        simpa [mask, this] using htj
  have := (hq _ hadm ⟨s, rfl, rfl⟩ (some (k, HenkinScott.flip s j)) (by simp [egm, eRel]) ()
    (fun _ => trivial) hflip)
  obtain ⟨t, ht, htj⟩ := this
  cases ht
  simp [HenkinScott.flip] at htj

theorem e_ax1 : HenkinVariant2.Ax1 egm := by
  intro p q w _ _ hp hq
  exact FreeUltra.U_good.2.2.1 _ _ (FreeUltra.U_good.2.2.2 _ _ hp hq)
    fun _ h s => ⟨h.1 s, h.2 s⟩

theorem e_ax2a : HenkinVariant2.Ax2a egm := by
  intro p w hp
  obtain ⟨n, hn⟩ := hp
  have hn' := slot_hyp (p := p ()) hn
  refine ⟨?_, fun ⟨h1, h2⟩ => ?_⟩
  · rcases FreeUltra.U_ultra (fun k => ∀ s, p () (some (k, s))) with h | h
    · exact Or.inl h
    · refine Or.inr (FreeUltra.U_good.2.2.1 _ _ (FreeUltra.U_good.2.2.2 _ _ h
        (FreeUltra.U_frechet _ ⟨n, fun k hk => hk⟩)) fun k ⟨hk, hnk⟩ s hs => hk fun s' => ?_)
      exact (tail_const (p := fun w => p () (some w)) hn' hnk s s').1 hs
  · exact FreeUltra.U_good.2.1 (FreeUltra.U_good.2.2.1 _ _ (FreeUltra.U_good.2.2.2 _ _ h1 h2)
      fun _ h => h.2 (fun _ => false) (h.1 _))

theorem e_ax4 (a : Bool) : HenkinVariant2.Ax4 egm a := by
  intro p q w _ _ hp hsub
  exact FreeUltra.U_good.2.2.1 _ _ hp fun k hk s =>
    hsub (some (k, s)) (by cases w <;> simp [egm, eRel]) () (fun _ => trivial) (hk s)

theorem e_ax3 (a : Bool) : A5 egm a := by
  intro w
  apply FreeUltra.U_good.2.2.1 _ _ FreeUltra.U_good.1
  intro k _ s p hp he
  exact (no_essence a p hp k s he).elim

/-- Symmetric-frame Ax1Gen deletion for T: a closed Henkin model on a symmetric frame with an
irreflexive world validating deep Ax1, Ax2a, Ax2b, Ax3 and Ax4 but not T, MC or Ax1Gen, in both
uniform guard regimes. -/
theorem d17T (a : Bool) (ρ : Assignment eModel.frame []) :
    (∀ w v, eModel.frame.rel w v → eModel.frame.rel v w) ∧ ¬ eModel.frame.rel none none ∧
    DeepValid eModel ρ tAx1 ∧ DeepValid eModel ρ tAx2a ∧ DeepValid eModel ρ tA4 ∧
    DeepValid eModel ρ (tA5 a) ∧ DeepValid eModel ρ (tAx4 a) ∧
    ¬ DeepValid eModel ρ tT ∧ ¬ DeepValid eModel ρ tMC ∧
    ¬ DeepValid eModel ρ (tAx1Gen a) := by
  have hp := e_presentation
  have d2 := (bridge_Ax2a hp ρ).2 e_ax2a
  have isSome_adm : egm.admP (fun w => w.isSome) := ⟨0, fun g _ w => by cases w <;> rfl⟩
  have nT : ¬ DeepValid eModel ρ tT := fun h => by
    have := (bridge_T hp ρ).1 h (fun w => w.isSome) isSome_adm none (fun v hv => by
      cases v with
      | none => exact (hv ⟨rfl, rfl⟩).elim
      | some _ => rfl)
    exact Bool.noConfusion this
  refine ⟨fun w v h h' => h ⟨h'.2, h'.1⟩, fun h => h ⟨rfl, rfl⟩,
    (bridge_Ax1 hp ρ).2 e_ax1, d2,
    (bridge_A4 hp ρ).2 fun _ _ _ h _ _ => h, (bridge_A5 hp a ρ).2 (e_ax3 a),
    (bridge_Ax4 hp a ρ).2 (e_ax4 a), nT, fun h => ?_, fun h => nT (deep_v2 a ρ h d2).1⟩
  have := (bridge_MC hp ρ).1 h (fun w => w.isNone) ⟨0, fun g _ w => by cases w <;> rfl⟩
    none rfl (some (0, fun _ => false)) (fun h => by cases h.2)
  exact Bool.noConfusion this

#print axioms e_presentation
#print axioms no_essence
#print axioms d17T
end Programme.«20261021-1639-ontological».Atlas.D17T
