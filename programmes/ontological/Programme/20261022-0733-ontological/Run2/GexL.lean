import Programme.«20261022-0733-ontological».Run2.DropDagger
import Programme.«20261022-0733-ontological».Run2.BoxIdle
import Programme.«20261022-0733-ontological».Run2.TwoWorld

/-! # Necessary existence from `L` and `Ax2b`, no conjunction axiom, in closed models

Target E, open item A4 of arXiv 2609.36279v4 (`sec:boxtwo`, `sec:open`): does variant 3′ under
`Ax1GenBoxTwo` prove `G_ex` without nominals?  K4 (`BoxIdle`) reduces `Ax1GenBoxTwo` to `L`.
th's conjecture E5 (`agents/th/lean/Programme/Th/GexBoxTwoV3Plain.lean`, `G_ex_L`) proves `G_ex`
from `L` with `Ax2a`, `Ax2b`, `Ax3`, `Ax4`: at a God-world `v` the God-like `y` has necessary
existence, and the constant property "no actual God-like being exists", non-empty because it
holds at a godless world, holds at no successor of `v` (Th2), so it is vacuously an essence of
`y` (variant 3′'s essence has no conjunct `φ x`); necessary existence then exemplifies it at a
successor (seriality), against Th2.

Here that argument is carried out over K1's Henkin-style `Model` with the `Closed` interface.
The witness is `lift (negS exG)`; nothing else from the closure is used besides `G`, `E3`
admitted and `neg`/`top` for seriality.  The core (`gex_core`) takes seriality and `Th4` as
hypotheses and so serves both variant 3′ (plain `Ax4`, `Th4` from `L`) and variant 3 (clause in
`Ax4`, `Th4` as in the library module, no conjunction axiom at all). -/

namespace Programme.«20261022-0733-ontological».Run2.GexL

open Programme.«20261022-0733-ontological».Run2.TwoClosed Programme.«20261022-0733-ontological».Run2.DropDagger Programme.«20261022-0733-ontological».Run2.BoxIdle

variable {W D : Type} {M : Model W D}

section core
variable (C : Closed M) (hE : M.AT (E3 M)) (h2a : Ax2a M) (h2b : Ax2b M) (h3 : Ax3v3 M)

include C h2a in
/-- `PosOfGod`. -/
theorem posOfGod {x : D} {ψ : D → W → Prop} {w : W} (hA : M.AT ψ) (hG : G M x w)
    (h : ψ x w) : M.P ψ w :=
  Classical.byContradiction fun hn =>
    hG _ (C.neg _ hA) ((h2a ψ hA w).1.resolve_left hn) h

include C h2a h2b in
/-- `Th1`: God-likeness is an essence of every God-like being (variant 3's essence). -/
theorem th1 {x : D} {w : W} (hG : G M x w) : Ess3 M (G M) x w := by
  intro ψ hA hψ v hv
  refine ⟨fun heq => ?_, fun y _ hGy => hGy ψ hA (h2b ψ hA w (posOfGod C h2a hA hG hψ) v hv)⟩
  have := hG
  rw [heq] at this
  exact this

include C hE h2a h2b h3 in
/-- `Th2`: a God-like being makes an actual God-like being exist at every successor. -/
theorem th2 {x : D} {w : W} (hG : G M x w) : ∀ v, M.R w v → ExG M v :=
  hG _ hE (h3 w) (G M) C.god (th1 C h2a h2b hG)

include C hE h2a h2b h3 in
/-- **Global spread** (th's lemma): with seriality and `Th4`, an actual God-like being exists at
every world, reachable or not.  No conjunction axiom, no frame condition beyond seriality. -/
theorem gex_core (hser : ∀ w, ∃ v, M.R w v) (hth4 : DropDagger.Th4 M) (w0 : W) : ExG M w0 :=
  Classical.byContradiction fun hn => by
    obtain ⟨v, _, y, _, hGy⟩ := hth4 w0
    have Ey : E3 M y v := hGy _ hE (h3 v)
    let φ : D → W → Prop := fun _ u => ¬ ExG M u
    have hφ : M.AT φ := C.lift _ (C.negS _ C.exG)
    have hne : φ ≠ bot := fun h => by
      have := congrFun (congrFun h y) w0
      exact (this ▸ hn : bot y w0)
    have ess : Ess3 M φ y v := fun _ _ _ u hu =>
      ⟨hne, fun _ _ hz => (hz (th2 C hE h2a h2b h3 hGy u hu)).elim⟩
    obtain ⟨u, hu⟩ := hser v
    obtain ⟨_, _, hz⟩ := Ey φ hφ ess u hu
    exact hz (th2 C hE h2a h2b h3 hGy u hu)

include C h2a h2b in
/-- Modal collapse for admitted propositions from `G_ex` everywhere, on any frame. -/
theorem mc_of_gex (hg : ∀ w, ExG M w) : MC M := by
  intro p hp w hpw v hv
  obtain ⟨g, _, hgw⟩ := hg w
  obtain ⟨k, _, hGk⟩ := hg v
  have hl : M.AT (fun _ => p) := C.lift _ hp
  exact hGk _ hl (h2b _ hl w (posOfGod C h2a hl hgw hpw) v hv)

end core

/-! ## Variant 3′: plain `Ax4`, `L` -/

section v3plain
variable (C : Closed M) (hE : M.AT (E3 M)) (h2a : Ax2a M) (h2b : Ax2b M) (h3 : Ax3v3 M)
  (h4 : Ax4 M)

include C hE h2a h3 h4 in
/-- Seriality from `Ax2a`, `Ax3`, plain `Ax4`. -/
theorem serial (w : W) : ∃ v, M.R w v :=
  Classical.byContradiction fun dead => by
    have all : ∀ ψ, M.AT ψ → M.P ψ w := fun ψ hA =>
      h4 _ ψ hE hA w (h3 w) fun v hv => absurd ⟨v, hv⟩ dead
    exact (h2a top C.top w).2 ⟨all _ C.top, all _ (C.neg _ C.top)⟩

include C h2a h4 in
/-- `Th4` from `L`. -/
theorem th4_L (hL : L M) : DropDagger.Th4 M := fun w =>
  Classical.byContradiction fun hn =>
    (h2a (G M) C.god w).2 ⟨hL w,
      h4 (G M) (neg (G M)) C.god (C.neg _ C.god) w (hL w)
        fun v hv y hy hg _ => hn ⟨v, hv, y, hy, hg⟩⟩

include C hE h2a h2b h3 h4 in
/-- **Variant 3′**: `L`, `Ax2a`, `Ax2b`, `Ax3`, plain `Ax4` give an actual God-like being at every
world, on any frame, with no conjunction axiom. -/
theorem gex_L (hL : L M) (w : W) : ExG M w :=
  gex_core C hE h2a h2b h3 (serial C hE h2a h3 h4) (th4_L C h2a h4 hL) w

include C hE h2a h2b h3 h4 in
theorem mc_L (hL : L M) : MC M :=
  mc_of_gex C h2a h2b (gex_L C hE h2a h2b h3 h4 hL)

include C hE h2a h2b h3 h4 in
/-- **Open item A4, closed models**: in variant 3′, `Ax1GenBoxTwo` gives `G_ex` at every world
and admitted modal collapse on any frame (through K4's `L_of_boxTwo`). -/
theorem gex_boxTwo [Nonempty D] (hB : Ax1GenBoxTwo M) (w : W) : ExG M w :=
  gex_L C hE h2a h2b h3 h4 (L_of_boxTwo C h2a (pTop_v3 hE C h3 h4) hB) w

include C hE h2a h2b h3 h4 in
theorem mc_boxTwo [Nonempty D] (hB : Ax1GenBoxTwo M) : MC M :=
  mc_L C hE h2a h2b h3 h4 (L_of_boxTwo C h2a (pTop_v3 hE C h3 h4) hB)

end v3plain

/-! ## Variant 3: clause in `Ax4`, `Th4` postulated, no conjunction axiom -/

section v3
variable (C : Closed M) (hE : M.AT (E3 M)) (h2a : Ax2a M) (h2b : Ax2b M) (h3 : Ax3v3 M)
  (h4 : Ax4c M) (hth4 : DropDagger.Th4 M)

include C hE h2a h3 h4 in
theorem serial_c (w : W) : ∃ v, M.R w v :=
  Classical.byContradiction fun dead => by
    have all : ∀ ψ, M.AT ψ → M.P ψ w := fun ψ hA =>
      h4 _ ψ hE hA w (h3 w) fun v hv => absurd ⟨v, hv⟩ dead
    exact (h2a top C.top w).2 ⟨all _ C.top, all _ (C.neg _ C.top)⟩

include C hE h2a h2b h3 h4 hth4 in
/-- **Variant 3** with `Th4`: `Ax2a`, `Ax2b`, `Ax3`, `Ax4` (clause) give `G_ex` at every world,
on any frame, with no conjunction axiom. -/
theorem gex_noConj (w : W) : ExG M w :=
  gex_core C hE h2a h2b h3 (serial_c C hE h2a h3 h4) hth4 w

include C hE h2a h2b h3 h4 hth4 in
theorem mc_noConj : MC M :=
  mc_of_gex C h2a h2b (gex_noConj C hE h2a h2b h3 h4 hth4)

end v3

/-! ## Non-vacuity: K1's one-world model satisfies the hypotheses of both -/

theorem unitModel_sat :
    Closed unitModel ∧ unitModel.AT (E3 unitModel) ∧ Ax2a unitModel ∧ Ax2b unitModel ∧
      Ax3v3 unitModel ∧ Ax4 unitModel ∧ Ax4c unitModel ∧ L unitModel ∧
      DropDagger.Th4 unitModel := by
  obtain ⟨C, _, h2a, h2b, _, h4, _⟩ := TwoClosed.unitModel_sat
  obtain ⟨hE, h3⟩ := unitModel_v3
  obtain ⟨-, -, -, -, -, h4c, hth4, -⟩ := DropDagger.unitModel_sat
  refine ⟨C, hE, h2a, h2b, h3, h4, h4c, ?_, hth4⟩
  intro w
  show (G unitModel) () w
  intro φ _ hφ
  exact hφ

/-- K3's two-world model (admitted = rigid, `P φ w := Rig φ ∧ φ () w`) satisfies `L` too, so with
`TwoWorld.sat` all hypotheses hold together on a two-world frame. -/
theorem twoWorld_L : L TwoWorld.twoModel := fun w =>
  ⟨TwoWorld.closed.god, TwoWorld.G_all () w⟩

end Programme.«20261022-0733-ontological».Run2.GexL

#print axioms Programme.«20261022-0733-ontological».Run2.GexL.gex_core
#print axioms Programme.«20261022-0733-ontological».Run2.GexL.gex_L
#print axioms Programme.«20261022-0733-ontological».Run2.GexL.mc_L
#print axioms Programme.«20261022-0733-ontological».Run2.GexL.gex_boxTwo
#print axioms Programme.«20261022-0733-ontological».Run2.GexL.mc_boxTwo
#print axioms Programme.«20261022-0733-ontological».Run2.GexL.gex_noConj
#print axioms Programme.«20261022-0733-ontological».Run2.GexL.mc_noConj
#print axioms Programme.«20261022-0733-ontological».Run2.GexL.unitModel_sat
#print axioms Programme.«20261022-0733-ontological».Run2.GexL.twoWorld_L
