import Programme.«20261022-0733-ontological».Run2.LGeneralFullAll
import Programme.«20261022-0733-ontological».Run2.CollapseMinimal
import Programme.«20261022-0733-ontological».Run2.DeadEndFrame
import Programme.«20261022-0733-ontological».Run2.V3NoSym
import Programme.«20261022-0733-ontological».Run2.Separating
import Programme.«20261022-0733-ontological».Run2.Minimal

/-! Transfer of the separators to v4's full language `𝓛` (`LGenF`, th's `LGeneralFull`).

Every witness model used in K8-K11, K13, K14, K16-K20 is `LGenF`: the flip models `fm`, `gfm`,
`fmId` and `rx` by `lgenF_of_sym`, all full-carrier models by `lgenF_full`.  Each theorem below
is the old statement with `LGenF` of its witnesses added in front (old `LGeneral` conjuncts are
implied by `lgeneral_of_lgenF` and kept). -/
namespace Programme.«20261022-0733-ontological».Run2.AtlasFull

open Programme.«20261022-0733-ontological».Run2.TwoClosed Programme.«20261022-0733-ontological».Run2.LGeneralFull Programme.«20261022-0733-ontological».Run2.LGeneralFullInst
open Programme.«20261022-0733-ontological».Run2.StandardKB Programme.«20261022-0733-ontological».Run2.DropDagger Programme.«20261022-0733-ontological».Run2.BoxIdle Programme.«20261022-0733-ontological».Run2.OneHF

/-- Any full-carrier model is `LGenF`. -/
theorem lgenF_allFull {W D : Type} (M : Model W D) (hS : ∀ q, M.AS q) (hT : ∀ φ, M.AT φ)
    (hH : ∀ Φ, M.AH Φ) : LGenF M := lgenF_full M hS hT hH

theorem lgenF_two (P) : LGenF (KBMinimal.two P) :=
  lgenF_full _ (fun _ => trivial) (fun _ => trivial) (fun _ => trivial)

theorem lgenF_mfull (P) : LGenF (Minimal.full P) :=
  lgenF_full _ (fun _ => trivial) (fun _ => trivial) (fun _ => trivial)

theorem lgenF_s4 : LGenF s4model :=
  lgenF_full _ (fun _ => trivial) (fun _ => trivial) (fun _ => trivial)

theorem lgenF_maj : LGenF Separating.maj :=
  lgenF_full _ (fun _ => trivial) (fun _ => trivial) (fun _ => trivial)

/-- K8 in full `𝓛`. -/
theorem k8_full : LGenF FM.fm ∧ Ax2a FM.fm ∧ Ax3 FM.fm ∧ Ax3v3 FM.fm ∧ Ax4 FM.fm ∧
    Ax4c FM.fm ∧ Th4 FM.fm ∧ L FM.fm ∧ Ax1Gen FM.fm ∧ Ax1GenTwo FM.fm ∧ Ax1GenOne FM.fm ∧
    Ax1GenBoxTwo FM.fm ∧ (∀ w, ExG FM.fm w) ∧ ¬ Ax2b FM.fm ∧ ¬ MC FM.fm :=
  ⟨lgenF_fm, FMGeneral.k8_lgeneral.2⟩

/-- K9 in full `𝓛`. -/
theorem k9_full : LGenF FM.gfm ∧ Ax2a FM.gfm ∧ Ax3 FM.gfm ∧ Ax3v3 FM.gfm ∧ Ax4 FM.gfm ∧
    Ax4c FM.gfm ∧ Th4 FM.gfm ∧ L FM.gfm ∧ Ax1GenBoxTwo FM.gfm ∧
    ¬ ExG FM.gfm (fun _ => false) ∧ ¬ Ax2b FM.gfm ∧ ¬ MC FM.gfm ∧
    ¬ Ax1Gen FM.gfm ∧ ¬ Ax1GenTwo FM.gfm ∧ ¬ Ax1GenOne FM.gfm :=
  ⟨lgenF_gfm, FMGeneral.k9_lgeneral.2⟩

/-- K10 in full `𝓛`. -/
theorem k10_full : LGenF FM.fm ∧ (∀ φ w, FM.fm.P φ w ↔ ∀ x, G FM.fm x w → φ x w) ∧
    Ax2a FM.fm ∧ Ax3 FM.fm ∧ Ax3v3 FM.fm ∧ Ax4 FM.fm ∧ L FM.fm ∧ Ax1Gen FM.fm ∧
    (∀ w, ExG FM.fm w) ∧ (∀ w v, FM.fm.R w v) ∧ ¬ Ax2b FM.fm ∧ ¬ MC FM.fm :=
  ⟨lgenF_fm, FMGeneral.k10_lgeneral.2⟩

/-- K11 in full `𝓛`: the three-plus-one non-derivabilities of `∃ᴱG` everywhere. -/
theorem k11_full :
    ¬ (∀ M : Model Bool Unit, LGenF M → Ax2b M → Ax3v3 M → Ax4 M → L M → ∀ w, ExG M w) ∧
    ¬ (∀ M : Model Bool Unit, LGenF M → Ax2a M → Ax2b M → Ax4 M → L M → ∀ w, ExG M w) ∧
    ¬ (∀ M : Model Bool Unit, LGenF M → Ax2a M → Ax2b M → Ax3v3 M → L M → ∀ w, ExG M w) ∧
    ¬ (∀ M : Model Bool Unit, LGenF M → Ax2a M → Ax2b M → Ax4c M → Th4 M →
        ∀ w, ExG M w) := by
  obtain ⟨a2, b2, b4, b4c, bl, bth, bng, _⟩ := Minimal.noAx3_props
  obtain ⟨c2a, c2b, _, c3', cl, cng, _⟩ := Minimal.noAx4_props
  obtain ⟨d2b, _, d3', d4, _, dl, dng, _⟩ := Minimal.noAx2a_props
  exact ⟨fun h => dng true (h Minimal.noAx2a (lgenF_mfull _) d2b d3' d4 dl true),
    fun h => bng (h Minimal.noAx3 (lgenF_mfull _) a2 b2 b4 bl false),
    fun h => cng true (h Minimal.noAx4 (lgenF_mfull _) c2a c2b c3' cl true),
    fun h => bng (h Minimal.noAx3 (lgenF_mfull _) a2 b2 b4c bth false)⟩

/-- K13 in full `𝓛`. -/
theorem k13_full :
    (∀ (W D : Type) (M : Model W D), Separating.FullTH M → Ax1Gen M → Ax2a M →
      (Ax3 M ∨ Ax3v3 M) → (∀ w v, M.R w v → v = w) ∧ MC M ∧ Ax2b M) ∧
    (LGenF FM.fm ∧ Ax1Gen FM.fm ∧ Ax2a FM.fm ∧ Ax3 FM.fm ∧ Ax3v3 FM.fm ∧ Ax4 FM.fm ∧
      L FM.fm ∧ ¬ MC FM.fm ∧ ¬ Ax2b FM.fm) :=
  ⟨FMGeneral.k13_lgeneral.1, lgenF_fm, FMGeneral.k13_lgeneral.2.2⟩

/-- K14 in full `𝓛`: `L` cannot be dropped from `gex_L`. -/
theorem k14_full :
    (LGenF Separating.maj ∧ Ax2a Separating.maj ∧ Ax2b Separating.maj ∧ Ax3 Separating.maj ∧
      Ax3v3 Separating.maj ∧ Ax4 Separating.maj ∧ Ax4c Separating.maj ∧
      (∀ w v, Separating.maj.R w v) ∧ ¬ L Separating.maj ∧ ¬ ExG Separating.maj ()) ∧
    ¬ (∀ M : Model Unit (Fin 3), LGenF M → Ax2a M → Ax2b M → Ax3 M → Ax3v3 M → Ax4 M →
      ∀ w, ExG M w) := by
  obtain ⟨_, h⟩ := Separating.majority
  refine ⟨⟨lgenF_maj, h⟩, fun hall => ?_⟩
  obtain ⟨a, b, c, d, e, _, _, _, g⟩ := h
  exact g (hall _ lgenF_maj a b c d e ())

/-- K16 in full `𝓛`. -/
theorem k16_full :
    (∀ (W D : Type) (M : Model W D), FullT M → (∀ w v, M.R w v → M.R v w) → Ax2a M →
      Ax4 M → (Ax3 M ∨ Ax3v3 M) → (∀ w v, M.R w v → v = w) ∧ MC M ∧ Ax2b M) ∧
    (LGenF FM.fm ∧ (∀ w v, FM.fm.R w v) ∧ Ax2a FM.fm ∧ Ax3 FM.fm ∧ Ax3v3 FM.fm ∧ Ax4 FM.fm ∧
      Ax1Gen FM.fm ∧ L FM.fm ∧ ¬ MC FM.fm ∧ ¬ Ax2b FM.fm) :=
  ⟨separating_kb.1, lgenF_fm, separating_kb.2.2⟩

/-- K17 in full `𝓛` (identity frame, variant 2 without Ax3v3). -/
theorem k17_full : LGenF FMGeneral.fmId ∧ Ax1Gen FMGeneral.fmId ∧ Ax2a FMGeneral.fmId ∧
    Ax2b FMGeneral.fmId ∧ Ax3 FMGeneral.fmId ∧ Ax4 FMGeneral.fmId ∧ MC FMGeneral.fmId ∧
    (∀ w, ExG FMGeneral.fmId w) ∧ ¬ Ax3v3 FMGeneral.fmId ∧
    (∀ w, ¬ AtomAt FMGeneral.fmId.AS w) := by
  obtain ⟨_, a, b, c, d, e, f, g, _, h, i, _⟩ := separating_v2
  exact ⟨lgenF_fmId, a, b, c, d, e, f, g, h, i⟩

/-- K18, narrowed per sk P178.  Variant 2 (`Ax3`): each hypothesis of `kb_collapse` is needed,
with `LGenF` witnesses.  Variant 3' (`Ax3v3`): symmetry is not needed, since full properties,
Ax2a, Ax4, Ax3v3 force a single world on any frame (sk's `v3_singleton`).  Plus seriality. -/
theorem k18_full :
    -- variant 2, no `FullT`
    (LGenF FM.fm ∧ (∀ w v, FM.fm.R w v) ∧ Ax2a FM.fm ∧ Ax3 FM.fm ∧ Ax4 FM.fm ∧ ¬ MC FM.fm) ∧
    -- variant 2, no symmetry
    (LGenF s4model ∧ FullT s4model ∧ Ax2a s4model ∧ Ax3 s4model ∧ Ax4 s4model ∧
      s4model.R false true ∧ ¬ MC s4model) ∧
    -- no `Ax4`
    (LGenF KBMinimal.noAx4 ∧ FullT KBMinimal.noAx4 ∧ (∀ w v, KBMinimal.noAx4.R w v) ∧
      Ax2a KBMinimal.noAx4 ∧ Ax3 KBMinimal.noAx4 ∧ ¬ Ax4 KBMinimal.noAx4 ∧
      ¬ (∀ w v, KBMinimal.noAx4.R w v → v = w) ∧ ¬ MC KBMinimal.noAx4) ∧
    -- no `Ax3`
    (LGenF KBMinimal.noAx3 ∧ FullT KBMinimal.noAx3 ∧ (∀ w v, KBMinimal.noAx3.R w v) ∧
      Ax2a KBMinimal.noAx3 ∧ Ax4 KBMinimal.noAx3 ∧ ¬ Ax3 KBMinimal.noAx3 ∧
      ¬ (∀ w v, KBMinimal.noAx3.R w v → v = w) ∧ ¬ MC KBMinimal.noAx3) ∧
    -- no `Ax2a`
    (LGenF KBMinimal.noAx2a ∧ FullT KBMinimal.noAx2a ∧ (∀ w v, KBMinimal.noAx2a.R w v) ∧
      Ax3 KBMinimal.noAx2a ∧ Ax4 KBMinimal.noAx2a ∧ ¬ Ax2a KBMinimal.noAx2a ∧
      ¬ (∀ w v, KBMinimal.noAx2a.R w v → v = w) ∧ ¬ MC KBMinimal.noAx2a) ∧
    -- variant 3': one world on any frame
    (∀ (W D : Type) (M : Model W D), FullT M → Ax2a M → Ax4 M → Ax3v3 M → ∀ a b : W, a = b) ∧
    -- seriality
    (∀ (W D : Type) (M : Model W D), FullT M → Ax2a M → Ax4 M → ∀ w, ∃ v, M.R w v) := by
  obtain ⟨⟨_, f1, f2, f3, _, f4, f5⟩, ⟨_, s1, s2, s3, s4, s5, s6⟩,
    ⟨_, a1, a2, a3, a4, _, a5, a6, a7⟩, ⟨_, b1, b2, b3, b4, b5, _, b6, b7⟩,
    ⟨_, c1, c2, c3, _, c4, c5, c6, c7⟩⟩ := KBMinimal.kb_minimal
  exact ⟨⟨lgenF_fm, f1, f2, f3, f4, f5⟩, ⟨lgenF_s4, s1, s2, s3, s4, s5, s6⟩,
    ⟨lgenF_two _, a1, a2, a3, a4, a5, a6, a7⟩, ⟨lgenF_two _, b1, b2, b3, b4, b5, b6, b7⟩,
    ⟨lgenF_two _, c1, c2, c3, c4, c5, c6, c7⟩,
    fun _ _ _ hF h2a h4 h3 => V3NoSym.v3_singleton hF h2a h4 h3,
    fun _ _ _ hF h2a h4 => KBMinimal.serial (hF _) (hF _) h2a h4⟩

/-- K20 in full `𝓛`. -/
theorem k20_full :
    (LGenF FM.fm ∧ (∀ w v, FM.fm.R w v) ∧ Ax1Gen FM.fm ∧ Ax2a FM.fm ∧ Ax3 FM.fm ∧
      Ax3v3 FM.fm ∧ ¬ MC FM.fm) ∧
    (LGenF KBMinimal.noAx4 ∧ Separating.FullTH KBMinimal.noAx4 ∧
      (∀ w v, KBMinimal.noAx4.R w v) ∧ Ax2a KBMinimal.noAx4 ∧ Ax3 KBMinimal.noAx4 ∧
      Ax3v3 KBMinimal.noAx4 ∧ ¬ Ax1Gen KBMinimal.noAx4 ∧
      ¬ (∀ w v, KBMinimal.noAx4.R w v → v = w) ∧ ¬ MC KBMinimal.noAx4) ∧
    (LGenF KBMinimal.noAx2a ∧ Separating.FullTH KBMinimal.noAx2a ∧
      (∀ w v, KBMinimal.noAx2a.R w v) ∧ Ax1Gen KBMinimal.noAx2a ∧ Ax3 KBMinimal.noAx2a ∧
      Ax3v3 KBMinimal.noAx2a ∧ ¬ Ax2a KBMinimal.noAx2a ∧
      ¬ (∀ w v, KBMinimal.noAx2a.R w v → v = w) ∧ ¬ MC KBMinimal.noAx2a) ∧
    (LGenF CollapseMinimal.truth ∧ Separating.FullTH CollapseMinimal.truth ∧
      (∀ w v, CollapseMinimal.truth.R w v) ∧ Ax1Gen CollapseMinimal.truth ∧
      Ax2a CollapseMinimal.truth ∧ ¬ Ax3 CollapseMinimal.truth ∧
      ¬ Ax3v3 CollapseMinimal.truth ∧ ¬ (∀ w v, CollapseMinimal.truth.R w v → v = w) ∧
      ¬ MC CollapseMinimal.truth) := by
  obtain ⟨⟨_, f⟩, ⟨_, a⟩, ⟨_, c⟩, ⟨_, t⟩⟩ := CollapseMinimal.standard_minimal
  exact ⟨⟨lgenF_fm, f⟩, ⟨lgenF_two _, a⟩, ⟨lgenF_two _, c⟩, ⟨lgenF_two _, t⟩⟩

end Programme.«20261022-0733-ontological».Run2.AtlasFull

#print axioms Programme.«20261022-0733-ontological».Run2.AtlasFull.k8_full
#print axioms Programme.«20261022-0733-ontological».Run2.AtlasFull.k9_full
#print axioms Programme.«20261022-0733-ontological».Run2.AtlasFull.k10_full
#print axioms Programme.«20261022-0733-ontological».Run2.AtlasFull.k11_full
#print axioms Programme.«20261022-0733-ontological».Run2.AtlasFull.k13_full
#print axioms Programme.«20261022-0733-ontological».Run2.AtlasFull.k14_full
#print axioms Programme.«20261022-0733-ontological».Run2.AtlasFull.k16_full
#print axioms Programme.«20261022-0733-ontological».Run2.AtlasFull.k17_full
#print axioms Programme.«20261022-0733-ontological».Run2.AtlasFull.k18_full
#print axioms Programme.«20261022-0733-ontological».Run2.AtlasFull.k20_full
