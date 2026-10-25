import Programme.«20261022-0733-ontological».Run2.GexL
import Programme.«20261022-0733-ontological».Run2.Minimal
import Programme.«20261022-0733-ontological».Run2.Separating
import Programme.«20261022-0733-ontological».Run2.LGeneralFullInst

/-! # The `Th4` route to `G_ex` (K6, variant 3) is exactly `Ax2a`, `Ax2b`, `Ax3v3`, `Th4`

K6's `gex_noConj` assumes `Ax2a`, `Ax2b`, `Ax3v3`, `Ax4c` and `Th4`; `Ax4c` there only serves to
give seriality (`serial_c`).  But `Th4` (`◇ ∃ᴱ x. G x` at every world) already gives a successor
at every world, so:

* `gex_th4`: in closed models with `E3` admitted, `Ax2a`, `Ax2b`, `Ax3v3` and `Th4` give an actual
  God-like being at every world, and (`mc_th4`) admitted modal collapse.  No `Ax4` of any kind.
* `th4_minimal`: each of the four is needed, by `𝓛`-general (v4's full `𝓛`) models:
  - `Ax2a`: `pb`, v4's FM carriers, one entity, S5, `P φ w :↔ ∀ v, v₀ = 1 → φ v` (the principal
    filter of the finitely based set "bit 0 is 1").  God-like exactly where bit 0 is 1, so
    `Th4` holds and worlds with bit 0 equal to 0 are godless.  It also satisfies `Ax3`, `Ax4`,
    `Ax4c` and `L`.
  - `Ax2b`: K9's `gfm`.
  - `Ax3v3`: `Minimal.noAx3` (full two-world S5, `P φ w :↔ φ true`).
  - `Th4`: K14's `maj` (one world, three entities, majority positivity). -/

namespace Programme.«20261022-0733-ontological».Run2.Th4Route

open Programme.«20261022-0733-ontological».Run2.TwoClosed Programme.«20261022-0733-ontological».Run2.DropDagger Programme.«20261022-0733-ontological».Run2.BoxIdle
  Programme.«20261022-0733-ontological».Run2.RigidFree Programme.«20261022-0733-ontological».Run2.FM
open Programme.«20261022-0733-ontological».Run2.LGeneralFull (LGenF)
open Programme.«20261022-0733-ontological».Run2.LGeneralFullInst (lgenF_full lgenF_mk lgenF_gfm)
open Programme.«20261022-0733-ontological».Run2.FMGeneral (mk sym_total)

variable {W D : Type} {M : Model W D}

/-! ## The sharpened route -/

theorem gex_th4 (C : Closed M) (hE : M.AT (E3 M)) (h2a : Ax2a M) (h2b : Ax2b M) (h3 : Ax3v3 M)
    (hth4 : Th4 M) (w : W) : ExG M w :=
  GexL.gex_core C hE h2a h2b h3 (fun u => (hth4 u).imp fun _ h => h.1) hth4 w

theorem mc_th4 (C : Closed M) (hE : M.AT (E3 M)) (h2a : Ax2a M) (h2b : Ax2b M) (h3 : Ax3v3 M)
    (hth4 : Th4 M) : MC M :=
  GexL.mc_of_gex C h2a h2b (gex_th4 C hE h2a h2b h3 hth4)

/-! ## Full models are closed -/

theorem closed_full (M : Model W D) (hS : ∀ q, M.AS q) (hT : ∀ φ, M.AT φ) (hH : ∀ Φ, M.AH Φ) :
    Closed M where
  top := hT _
  bot := hT _
  neg := fun _ _ => hT _
  conj := fun _ _ _ _ => hT _
  lift := fun _ _ => hT _
  negS := fun _ _ => hS _
  god := hT _
  exG := hS _
  pos := hH _
  single := fun _ _ => hH _
  union := fun _ _ _ _ => hH _
  guard := fun _ _ _ _ => hH _
  atMost := fun _ _ _ _ => hS _

/-! ## `Ax2a` is needed: the principal filter of "bit 0 is 1" on FM carriers -/

def B (v : Cw) : Prop := v 0 = true

def pbP : (Unit → Cw → Prop) → Cw → Prop := fun φ _ => ∀ v, B v → φ () v

def pb : Model Cw Unit := mk (fun _ _ => True) (fun _ _ => True) pbP

theorem B_xorw {d : Cw} (hd : Fixes 1 d) (v : Cw) : B (xorw v d) ↔ B v := by
  simp [B, xorw, hd 0 Nat.zero_lt_one]

theorem pbP_act {d : Cw} (hd : Fixes 1 d) (ψ : Unit → Cw → Prop) (w : Cw) :
    pbP (act d ψ) (xorw w d) ↔ pbP ψ w :=
  ⟨fun h v hv => by
      have := h (xorw v d) ((B_xorw hd v).2 hv)
      simpa [act, xorw_xorw] using this,
    fun h v hv => h (xorw v d) ((B_xorw hd v).2 hv)⟩

theorem G_pb (x : Unit) (w : Cw) : G pb x w ↔ B w :=
  ⟨fun h => h (bit 0 true) (bit_based 0 true) fun _ hv => hv,
   fun hw _ _ hφ => by cases x; exact hφ w hw⟩

theorem G_pb_eq : G pb = bit 0 true := by
  funext x w; exact propext (G_pb x w)

theorem exG_pb (w : Cw) : ExG pb w ↔ B w :=
  ⟨fun ⟨y, _, h⟩ => (G_pb y w).1 h, fun h => ⟨(), trivial, (G_pb () w).2 h⟩⟩

theorem closed_pb : Closed pb where
  top := RigidFree.closed.top
  bot := RigidFree.closed.bot
  neg := RigidFree.closed.neg
  conj := RigidFree.closed.conj
  lift := RigidFree.closed.lift
  negS := RigidFree.closed.negS
  god := by
    show Based (G pb ())
    rw [G_pb_eq]; exact bit_based 0 true
  exG := by
    have : ExG pb = fun w => B w := funext fun w => propext (exG_pb w)
    show Based (ExG pb)
    rw [this]; exact bit_based 0 true
  pos := ⟨1, fun d hd ψ w => (pbP_act hd ψ w).symm⟩
  single := single_fmh
  union := fun _ _ => union_fmh
  guard := fun _ _ => guard_fmh
  atMost := fun _ _ hΦ h0 => atMost_based hΦ h0

theorem lgenF_pb : LGenF pb :=
  lgenF_mk (R := fun _ _ => True) (ac := fun _ _ => True) (P := pbP)
    1 (fun d hd => sym_total (funext fun ψ => funext fun w => propext (pbP_act hd ψ w)))

theorem E3_pb (x : Unit) (w : Cw) : E3 pb x w := RigidFree.E3_all x w
theorem E_pb (x : Unit) (w : Cw) : E pb x w := RigidFree.E_all x w

theorem E3_adm_pb : pb.AT (E3 pb) :=
  based_const _ fun w v => iff_of_true (E3_pb () w) (E3_pb () v)

theorem ax2b_pb : Ax2b pb := fun _ _ _ h _ _ => h
theorem ax3_pb : Ax3 pb := fun _ v _ => E_pb () v
theorem ax3v3_pb : Ax3v3 pb := fun _ v _ => E3_pb () v
theorem ax4_pb : Ax4 pb := fun _ _ _ _ w hφ hi v hv => hi v trivial () trivial (hφ v hv)
theorem ax4c_pb : Ax4c pb := fun _ _ _ _ w hφ hi v hv => (hi v trivial).2 () trivial (hφ v hv)
theorem l_pb : L pb := fun _ v hv => (G_pb () v).2 hv
theorem th4_pb : Th4 pb := fun _ => ⟨fun _ => true, trivial, (exG_pb _).2 rfl⟩
theorem godless_pb : ¬ ExG pb (fun _ => false) := fun h => Bool.false_ne_true ((exG_pb _).1 h)

theorem not_ax2a_pb : ¬ Ax2a pb := by
  intro h
  rcases (h (bit 1 true) (bit_based 1 true) (fun _ => true)).1 with hp | hp
  · have := hp (fun i => decide (i = 0)) rfl
    simp [bit] at this
  · exact hp (fun _ => true) rfl rfl

/-- `B` is admitted, true at `1^ω`, false at `0^ω`, and `R` is total. -/
theorem not_mc_pb : ¬ MC pb := fun h =>
  absurd (h B (bit_based 0 true) (fun _ => true) rfl (fun _ => false) trivial) (by simp [B])

/-- **`Ax2a` cannot be dropped from the `Th4` route** (nor from K6's `L` route). -/
theorem ax2a_needed :
    LGenF pb ∧ Closed pb ∧ pb.AT (E3 pb) ∧ Ax2b pb ∧ Ax3 pb ∧ Ax3v3 pb ∧ Ax4 pb ∧ Ax4c pb ∧
      L pb ∧ Th4 pb ∧ (∀ w v, pb.R w v) ∧ (∀ y w, pb.act y w) ∧
      ¬ ExG pb (fun _ => false) ∧ ¬ Ax2a pb ∧ ¬ MC pb :=
  ⟨lgenF_pb, closed_pb, E3_adm_pb, ax2b_pb, ax3_pb, ax3v3_pb, ax4_pb, ax4c_pb, l_pb, th4_pb,
    fun _ _ => trivial, fun _ _ => trivial, godless_pb, not_ax2a_pb, not_mc_pb⟩

/-! ## Minimality -/

/-- **Each hypothesis of `gex_th4` is needed**, by `𝓛`-general models (closed, `E3` admitted)
satisfying the other three, with a world lacking an actual God-like being. -/
theorem th4_minimal :
    -- no `Ax2a`
    (LGenF pb ∧ Closed pb ∧ pb.AT (E3 pb) ∧ Ax2b pb ∧ Ax3v3 pb ∧ Th4 pb ∧
      ¬ Ax2a pb ∧ ∃ w, ¬ ExG pb w) ∧
    -- no `Ax2b`
    (LGenF gfm ∧ Closed gfm ∧ gfm.AT (E3 gfm) ∧ Ax2a gfm ∧ Ax3v3 gfm ∧ Th4 gfm ∧
      ¬ Ax2b gfm ∧ ∃ w, ¬ ExG gfm w) ∧
    -- no `Ax3v3`
    (LGenF Minimal.noAx3 ∧ Closed Minimal.noAx3 ∧ Minimal.noAx3.AT (E3 Minimal.noAx3) ∧
      Ax2a Minimal.noAx3 ∧ Ax2b Minimal.noAx3 ∧ Th4 Minimal.noAx3 ∧
      ¬ Ax3v3 Minimal.noAx3 ∧ ∃ w, ¬ ExG Minimal.noAx3 w) ∧
    -- no `Th4`
    (LGenF Separating.maj ∧ Closed Separating.maj ∧ Separating.maj.AT (E3 Separating.maj) ∧
      Ax2a Separating.maj ∧ Ax2b Separating.maj ∧ Ax3v3 Separating.maj ∧
      ¬ Th4 Separating.maj ∧ ∃ w, ¬ ExG Separating.maj w) := by
  obtain ⟨gC, -, -, gE3, g2a, -, g3v, -, -, gth4, -, -, -, -, gnex, gn2b, -⟩ := godless_fm
  obtain ⟨a2, b2, -, -, -, bth, bng, -, bn3v, -⟩ := Minimal.noAx3_props
  obtain ⟨-, m2a, m2b, -, m3v, -, -, -, -, mng⟩ := Separating.majority
  refine ⟨⟨lgenF_pb, closed_pb, E3_adm_pb, ax2b_pb, ax3v3_pb, th4_pb, not_ax2a_pb, _, godless_pb⟩,
    ⟨lgenF_gfm, gC, gE3, g2a, g3v, gth4, gn2b, _, gnex⟩,
    ⟨lgenF_full _ (fun _ => trivial) (fun _ => trivial) (fun _ => trivial),
      closed_full _ (fun _ => trivial) (fun _ => trivial) (fun _ => trivial), trivial,
      a2, b2, bth, bn3v, _, bng⟩,
    ⟨lgenF_full _ (fun _ => trivial) (fun _ => trivial) (fun _ => trivial),
      closed_full _ (fun _ => trivial) (fun _ => trivial) (fun _ => trivial), trivial,
      m2a, m2b, m3v, fun h => mng ?_, _, mng⟩⟩
  obtain ⟨v, -, hv⟩ := h ()
  cases v; exact hv

end Programme.«20261022-0733-ontological».Run2.Th4Route

#print axioms Programme.«20261022-0733-ontological».Run2.Th4Route.gex_th4
#print axioms Programme.«20261022-0733-ontological».Run2.Th4Route.mc_th4
#print axioms Programme.«20261022-0733-ontological».Run2.Th4Route.ax2a_needed
#print axioms Programme.«20261022-0733-ontological».Run2.Th4Route.th4_minimal
