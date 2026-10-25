import Programme.«20261022-0733-ontological».Run2.LGeneralFull
import Programme.«20261022-0733-ontological».Run2.FMGeneral
import Programme.«20261022-0733-ontological».Run2.RigidExit
/-! # The separators are `𝓛`-general for the full simply typed language

Instances of `LGeneralFull.lgenF_of_sym`:
* every flip model `FMGeneral.mk R ac P` whose `R`, actuality and `P` are fixed by some `G_m`
  (`lgenF_mk`), hence `fm` (K8, K10, K13, K16), `gfm` (K9) and `fmId` (K17);
* the rigid free-ultrafilter model `RigidExit.rx` (E12), group `Sym(ℕ)`;
* every model with full carriers (`lgenF_full`), e.g. the finite controls of K11, K14, K18.
The carriers at every type of `FTy` are the supported, admitted-to-admitted objects; at `σ`,
`τ`, `τ → σ` they are exactly the model's `AS`, `AT`, `AH`. -/

namespace Programme.«20261022-0733-ontological».Run2.LGeneralFullInst

open Programme.«20261022-0733-ontological».Run2.LGeneralFull Programme.«20261022-0733-ontological».Run2.TwoClosed Programme.«20261022-0733-ontological».Run2.FM Programme.«20261022-0733-ontological».Run2.RigidFree
open Programme.«20261022-0733-ontological».Run2.FMGeneral (xorw_comm actTy adm_iff_fix mk sym_total fmId)
open Programme.«20261022-0733-ontological».Run2.LGeneral (Adm)

/-! ## Full carriers -/

theorem lgenF_full {W D : Type} (M : Model W D) (hS : ∀ q, M.AS q) (hT : ∀ φ, M.AT φ)
    (hH : ∀ Φ, M.AH Φ) : LGenF M :=
  ⟨fun _ _ => True, fun _ => trivial, fun q => iff_of_true trivial (hS q),
   fun φ => iff_of_true trivial (hT φ), fun Φ => iff_of_true trivial (hH Φ),
   fun _ _ _ => trivial⟩

/-! ## Flip models -/

def fx (m n : Nat) (f g : Cw → Cw) : Prop :=
  ∃ d, Fixes (max n m) d ∧ f = (fun w => xorw w d) ∧ g = (fun w => xorw w d)

theorem xorw_conj (d e w : Cw) : xorw (xorw (xorw w d) e) d = xorw w e := by
  rw [xorw_comm, xorw_xorw]

def symMk {R : Cw → Cw → Prop} {ac : Unit → Cw → Prop} {P : (Unit → Cw → Prop) → Cw → Prop}
    (m : Nat) (hm : ∀ d, Fixes m d → Programme.«20261022-0733-ontological».Run2.FMGeneral.Sym R ac P d) :
    LGeneralFull.Sym (D := Unit) R ac P where
  Fx := fx m
  mono := by
    rintro n n' f g hn ⟨d, hd, rfl, rfl⟩
    exact ⟨d, fixes_mono (Nat.max_le.2 ⟨Nat.le_trans hn (Nat.le_max_left _ _),
      Nat.le_max_right _ _⟩) hd, rfl, rfl⟩
  inv := by rintro n f g ⟨d, hd, rfl, rfl⟩; exact ⟨d, hd, rfl, rfl⟩
  fg := by rintro f g ⟨d, _, rfl, rfl⟩ w; exact xorw_xorw w d
  hR := by
    rintro f g ⟨d, hd, rfl, rfl⟩
    exact (hm d (fixes_mono (Nat.le_max_right 0 m) hd)).R
  hact := by
    rintro f g ⟨d, hd, rfl, rfl⟩
    exact (hm d (fixes_mono (Nat.le_max_right 0 m) hd)).ac
  hP := by
    rintro f g ⟨d, hd, rfl, rfl⟩
    exact (hm d (fixes_mono (Nat.le_max_right 0 m) hd)).P
  conj := by
    rintro f g ⟨d, _, rfl, rfl⟩ n
    refine ⟨n, ?_⟩
    rintro c c' ⟨e, he, rfl, rfl⟩
    exact ⟨e, he, funext fun w => xorw_conj d e w, funext fun w => xorw_conj d e w⟩

section
variable {R : Cw → Cw → Prop} {ac : Unit → Cw → Prop} {P : (Unit → Cw → Prop) → Cw → Prop}
  (m : Nat) (hm : ∀ d, Fixes m d → Programme.«20261022-0733-ontological».Run2.FMGeneral.Sym R ac P d)

open Programme.«20261022-0733-ontological».Run2.FMGeneral in
theorem sup_iff (t : Programme.«20261022-0733-ontological».Run2.LGeneral.Ty) (t' : FTy)
    (x : Programme.«20261022-0733-ontological».Run2.LGeneral.Den Cw Unit t) (x' : LGeneralFull.Den Cw Unit t')
    (hx : ∀ d, fl (fun w => xorw w d) (fun w => xorw w d) t' x' = x' ↔ actTy d t x = x) :
    Sup (symMk m hm) t' x' ↔ Adm (mk R ac P) t x := by
  rw [adm_iff_fix]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨max n m, fun d hd => (hx d).1 (hn _ _ ⟨d, hd, rfl, rfl⟩)⟩
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rintro f g ⟨d, hd, rfl, rfl⟩
    exact (hx d).2 (hn d (fixes_mono (Nat.le_max_left n m) hd))

open Programme.«20261022-0733-ontological».Run2.FMGeneral in
/-- **Fact (a), full language, flip models.** -/
theorem lgenF_mk (m : Nat) (hm : ∀ d, Fixes m d → Programme.«20261022-0733-ontological».Run2.FMGeneral.Sym R ac P d) :
    LGenF (mk R ac P) :=
  lgenF_of_sym (mk R ac P) (symMk m hm)
    (fun q => sup_iff m hm .s .s q q fun _ => Iff.rfl)
    (fun φ => sup_iff m hm .p tp φ φ fun _ => Iff.rfl)
    (fun Φ => sup_iff m hm .h th Φ Φ fun _ => Iff.rfl)
end

open Programme.«20261022-0733-ontological».Run2.FMGeneral in
theorem lgenF_fm : LGenF fm :=
  lgenF_mk (R := fun _ _ => True) (ac := fun _ _ => True) (P := fm.P)
    0 (fun d _ => sym_total (funext fun ψ => funext fun w => by
      show act d ψ () (xorw w d) = ψ () w
      simp [act, xorw_xorw]))

open Programme.«20261022-0733-ontological».Run2.FMGeneral in
theorem lgenF_gfm : LGenF gfm :=
  lgenF_mk (R := fun _ _ => True) (ac := fun _ _ => True) (P := gfm.P)
    1 (fun d hd => sym_total (funext fun ψ => funext fun w => by
      show act d ψ () (Programme.«20261022-0733-ontological».Run2.GodlessL.f (xorw w d)) = ψ () (Programme.«20261022-0733-ontological».Run2.GodlessL.f w)
      simp [act, f_xorw hd, xorw_xorw]))

open Programme.«20261022-0733-ontological».Run2.FMGeneral in
theorem lgenF_fmId : LGenF fmId :=
  lgenF_mk 0 (fun d _ => ⟨fun w v => ⟨fun h => by
      have := congrArg (fun u => xorw u d) h; simpa [xorw_xorw] using this,
      fun h => by rw [h]⟩, fun _ _ => Iff.rfl,
    funext fun ψ => funext fun w => by
      show act d ψ () (xorw w d) = ψ () w
      simp [act, xorw_xorw]⟩)

/-! ## The rigid exit `rx` (group `Sym(ℕ)`) -/

namespace Rx
open Programme.«20261022-0733-ontological».Run2.RigidExit

def fxr (n : Nat) (f g : Wd → Wd) : Prop :=
  ∃ π, Programme.«20261022-0733-ontological».Run2.RigidExit.Fixes n π ∧ f = wact π ∧ g = wact π.inv

theorem cj_fixes {π σ : Pm} {n : Nat} (hσ : Programme.«20261022-0733-ontological».Run2.RigidExit.Fixes (bnd π.p n) σ) :
    Programme.«20261022-0733-ontological».Run2.RigidExit.Fixes n (cj π σ) := by
  intro i hi
  show π.q (σ.p (π.p i)) = i
  rw [hσ (π.p i) (lt_bnd π.p hi), π.qp]

def symRxF : LGeneralFull.Sym (D := Unit) rx.R rx.act rx.P where
  Fx := fxr
  mono := by
    rintro n n' f g hn ⟨π, hπ, rfl, rfl⟩
    exact ⟨π, fun i hi => hπ i (by omega), rfl, rfl⟩
  inv := by
    rintro n f g ⟨π, hπ, rfl, rfl⟩
    exact ⟨π.inv, pm_fix_q hπ, rfl, rfl⟩
  fg := by rintro f g ⟨π, _, rfl, rfl⟩ w; exact wact_inv π w
  hR := fun _ _ _ => Iff.rfl
  hact := fun _ _ _ => Iff.rfl
  hP := by
    rintro f g ⟨π, _, rfl, rfl⟩
    funext ψ w
    exact propext ((auto_rx π).hP ψ w)
  conj := by
    rintro f g ⟨π, _, rfl, rfl⟩ n
    refine ⟨bnd π.p n, ?_⟩
    rintro c c' ⟨σ, hσ, rfl, rfl⟩
    exact ⟨cj π σ, cj_fixes hσ, funext fun w => Subtype.ext rfl, funext fun w => Subtype.ext rfl⟩

theorem sup_iff (t : Programme.«20261022-0733-ontological».Run2.LGeneral.Ty) (t' : FTy)
    (x : Programme.«20261022-0733-ontological».Run2.LGeneral.Den Wd Unit t) (x' : LGeneralFull.Den Wd Unit t')
    (hx : ∀ π, fl (wact π) (wact π.inv) t' x' = x' ↔ Programme.«20261022-0733-ontological».Run2.RigidExit.fl (toAut π) t x = x) :
    Sup symRxF t' x' ↔ Programme.«20261022-0733-ontological».Run2.RigidExit.AdmF t x := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rintro _ ⟨π, hπ, rfl⟩
    exact (hx π).1 (hn _ _ ⟨π, hπ, rfl, rfl⟩)
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rintro f g ⟨π, hπ, rfl, rfl⟩
    exact (hx π).2 (hn _ ⟨π, hπ, rfl⟩)

/-- **Fact (a), full language, for `rx`.** -/
theorem lgenF_rx : LGenF rx :=
  lgenF_of_sym rx symRxF
    (fun q => sup_iff .s .s q q fun _ => Iff.rfl)
    (fun φ => sup_iff .p tp φ φ fun _ => Iff.rfl)
    (fun Φ => sup_iff .h th Φ Φ fun _ => Iff.rfl)

end Rx

end Programme.«20261022-0733-ontological».Run2.LGeneralFullInst

#print axioms Programme.«20261022-0733-ontological».Run2.LGeneralFull.lgenF_of_sym
#print axioms Programme.«20261022-0733-ontological».Run2.LGeneralFullInst.lgenF_full
#print axioms Programme.«20261022-0733-ontological».Run2.LGeneralFullInst.lgenF_fm
#print axioms Programme.«20261022-0733-ontological».Run2.LGeneralFullInst.lgenF_gfm
#print axioms Programme.«20261022-0733-ontological».Run2.LGeneralFullInst.lgenF_fmId
#print axioms Programme.«20261022-0733-ontological».Run2.LGeneralFullInst.Rx.lgenF_rx

namespace Programme.«20261022-0733-ontological».Run2.LGeneralFullInst
open Programme.«20261022-0733-ontological».Run2.LGeneralFull Programme.«20261022-0733-ontological».Run2.TwoClosed Programme.«20261022-0733-ontological».Run2.FM

/-- The four infinite separators are `𝓛`-general in the full sense, hence also fragment-closed. -/
theorem lgenF_all : LGenF fm ∧ LGenF gfm ∧ LGenF Programme.«20261022-0733-ontological».Run2.FMGeneral.fmId ∧
    LGenF Programme.«20261022-0733-ontological».Run2.RigidExit.rx :=
  ⟨lgenF_fm, lgenF_gfm, lgenF_fmId, Rx.lgenF_rx⟩

open Programme.«20261022-0733-ontological».Run2.RigidExit in
/-- E12 with full `𝓛`-generality. -/
theorem rigid_exit_full :
    LGenF rx ∧ (∀ w v, rx.R w v) ∧ (∀ y w, rx.act y w) ∧
    Ax2a rx ∧ Ax2b rx ∧ Ax3 rx ∧ Ax3v3 rx ∧ Ax4 rx ∧
    ¬ MC rx ∧ (∀ w, ¬ ExG rx w) ∧ ¬ Ax1Gen rx ∧ ¬ Ax1GenTwo rx :=
  ⟨Rx.lgenF_rx, rigid_exit.2⟩

end Programme.«20261022-0733-ontological».Run2.LGeneralFullInst

#print axioms Programme.«20261022-0733-ontological».Run2.LGeneralFullInst.lgenF_all
#print axioms Programme.«20261022-0733-ontological».Run2.LGeneralFullInst.rigid_exit_full
