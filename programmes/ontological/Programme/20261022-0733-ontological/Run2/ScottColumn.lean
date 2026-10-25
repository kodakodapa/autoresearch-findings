import Programme.«20261022-0733-ontological».Run2.FiniteBinary
-- Copied from agents/th/lean/Programme/Th/ScottColumn.lean (author th); namespace and imports changed.

/-! # Scott's variant in closed models: the KB row and a finite S4 separator

Scott's variant (`Notes/ScottVariantHOML.lean`) is variant 2's essence and necessary existence
with `A1 = Ax2a`, `A2 = Ax4`, `A3 = L` (`P G`), `A4 = Ax2b`, `A5 = Ax3`; no conjunction axiom.

* `scott_gex_sym`: closed models (K1's `Closed`, plus `E` admitted), symmetric `R`, any actuality:
  Scott's five axioms give an actual God-like entity at every world.
* `scott_mc_sym`: and therefore admitted MC (via K38's `princ_of_gex`, `mc_of_princ_2b`).
* `scott_s4_gap`: a finite full (`LGenF`) model on a reflexive transitive two-world frame
  satisfies all five, binary A1, but not `Ax1GenTwo`, MC, `∃ᴱ G` at world 1, `UF`, `Princ`.
  It is P355's model with reflexive `R`. -/

namespace Programme.«20261022-0733-ontological».Run2.ScottColumn

open Programme.«20261022-0733-ontological».Run2 Programme.«20261022-0733-ontological».Run2.TwoClosed Programme.«20261022-0733-ontological».Run2.Ultrafilter Programme.«20261022-0733-ontological».Run2.Principal
  Programme.«20261022-0733-ontological».Run2.Binary
open Programme.«20261022-0733-ontological».Run2.LGeneralFull (LGenF)

variable {W D : Type} {M : Model W D}

/-- Scott's `A3`. -/
def L (M : Model W D) : Prop := ∀ w, M.P (G M) w

theorem not_pBot (C : Closed M) (h2a : Ax2a M) (h4 : Ax4 M) (w : W) : ¬ M.P bot w := fun hb =>
  (h2a top C.top w).2 ⟨h4 bot top C.bot C.top w hb fun _ _ _ _ h => h.elim,
    h4 bot (neg top) C.bot (C.neg _ C.top) w hb fun _ _ _ _ h => h.elim⟩

/-- `T1` for `G`: some successor has an actual God-like entity. -/
theorem god_succ (C : Closed M) (h2a : Ax2a M) (h4 : Ax4 M) (hL : L M) (w : W) :
    ∃ v, M.R w v ∧ ExG M v := by
  refine Classical.byContradiction fun hn => not_pBot C h2a h4 w ?_
  exact h4 (G M) bot C.god C.bot w (hL w) fun v hv y hy hg => hn ⟨v, hv, y, hy, hg⟩

/-- `PosOfGod`. -/
theorem pos_of_god (C : Closed M) (h2a : Ax2a M) {x : D} {v : W} (hg : G M x v) {ψ}
    (hψ : M.AT ψ) (h : ψ x v) : M.P ψ v :=
  ((h2a ψ hψ v).1).resolve_right fun pn => hg _ (C.neg _ hψ) pn h

/-- `T2`: God's essence. -/
theorem ess_god (C : Closed M) (h2a : Ax2a M) (h2b : Ax2b M) {x : D} {v : W} (hg : G M x v) :
    Ess M (G M) x v :=
  ⟨hg, fun ψ hψ h u hu _y _ hy => hy ψ hψ (h2b ψ hψ v (pos_of_god C h2a hg hψ h) u hu)⟩

/-- Successors of a godful world are godful. -/
theorem spread (C : Closed M) (hE : M.AT (E M)) (h2a : Ax2a M) (h2b : Ax2b M) (h3 : Ax3 M)
    {v : W} (hv : ExG M v) {u : W} (hu : M.R v u) : ExG M u := by
  obtain ⟨x, -, hg⟩ := hv
  exact hg (E M) hE (h3 v) (G M) C.god (ess_god C h2a h2b hg) u hu

theorem scott_gex_sym (C : Closed M) (hE : M.AT (E M)) (h2a : Ax2a M) (h2b : Ax2b M)
    (h3 : Ax3 M) (h4 : Ax4 M) (hL : L M) (hsym : ∀ w v, M.R w v → M.R v w) (w : W) :
    ExG M w := by
  obtain ⟨v, hv, hg⟩ := god_succ C h2a h4 hL w
  exact spread C hE h2a h2b h3 hg (hsym w v hv)

theorem scott_mc_sym (C : Closed M) (hE : M.AT (E M)) (h2a : Ax2a M) (h2b : Ax2b M)
    (h3 : Ax3 M) (h4 : Ax4 M) (hL : L M) (hsym : ∀ w v, M.R w v → M.R v w) : MC M :=
  mc_of_princ_2b C (fun w => princ_of_gex C h2a (scott_gex_sym C hE h2a h2b h3 h4 hL hsym w)) h2b

/-! ## Finite S4 separator -/

open Programme.«20261022-0733-ontological».Run2.FiniteBinary (at0 Φ₀ top_ne_at0)

def s4 : Model Bool Unit where
  R := fun w v => v = false ∨ v = w
  act := fun _ _ => True
  AS := fun _ => True
  AT := fun _ => True
  AH := fun _ => True
  P := fun φ _ => φ () false

theorem closed_s4 : Closed s4 where
  top := trivial
  bot := trivial
  neg := fun _ _ => trivial
  conj := fun _ _ _ _ => trivial
  lift := fun _ _ => trivial
  negS := fun _ _ => trivial
  god := trivial
  exG := trivial
  pos := trivial
  single := fun _ _ => trivial
  union := fun _ _ _ _ => trivial
  guard := fun _ _ _ _ => trivial
  atMost := fun _ _ _ _ => trivial

theorem refl_s4 (w : Bool) : s4.R w w := Or.inr rfl
theorem trans_s4 (a b c : Bool) (h1 : s4.R a b) (h2 : s4.R b c) : s4.R a c := by
  rcases h2 with h | h
  · exact Or.inl h
  · subst h; exact h1

theorem l_s4 : L s4 := fun _ _ _ h => h

theorem ax3_s4 : Ax3 s4 := fun _ φ _ hess v hv => by
  rcases hv with rfl | rfl
  · exact ⟨(), trivial, hess.1⟩
  · exact ⟨(), trivial, hess.1⟩

theorem ax4_s4 : Ax4 s4 := fun _ _ _ _ _ hφ hinc => hinc false (Or.inl rfl) () trivial hφ

theorem not_two_s4 : ¬ Ax1GenTwo s4 := fun h =>
  h Φ₀ bot trivial trivial true
    ⟨top, at0, trivial, trivial, Or.inl ⟨rfl, Or.inl rfl⟩, Or.inl ⟨rfl, Or.inr rfl⟩, top_ne_at0⟩
    (fun ψ _ hψ => by
      rcases hψ with ⟨-, rfl | rfl⟩ | ⟨h, -⟩
      · exact trivial
      · exact rfl
      · exact Bool.noConfusion h)
    (fun v hv z _ => by
      rcases hv with rfl | rfl
      · exact ⟨fun h => h.elim, fun h => h bot trivial (Or.inr ⟨rfl, rfl⟩)⟩
      · exact ⟨fun h => h.elim, fun h => Bool.noConfusion (h at0 trivial (Or.inl ⟨rfl, Or.inr rfl⟩))⟩)

/-- **Scott's variant on S4: finite separator.** -/
theorem scott_s4_gap :
    LGenF s4 ∧ Closed s4 ∧ (∀ w, s4.R w w) ∧
      (∀ a b c, s4.R a b → s4.R b c → s4.R a c) ∧
      Ax2a s4 ∧ Ax4 s4 ∧ L s4 ∧ Ax2b s4 ∧ Ax3 s4 ∧ Ax1Bin s4 ∧
      ¬ Ax1GenTwo s4 ∧ ¬ MC s4 ∧ ¬ ExG s4 true ∧ ¬ UF s4 true ∧ ¬ Princ s4 true :=
  ⟨LGeneralFullInst.lgenF_full s4 (fun _ => trivial) (fun _ => trivial) (fun _ => trivial),
    closed_s4, refl_s4, trans_s4,
    fun φ _ _ => ⟨(Classical.em (φ () false)).imp id id, fun ⟨a, b⟩ => b a⟩,
    ax4_s4, l_s4, fun _ _ _ h _ _ => h, ax3_s4, fun _ _ _ _ _ h1 h2 => ⟨h1, h2⟩,
    not_two_s4,
    fun h => Bool.noConfusion (h (fun v => v = true) trivial true rfl false (Or.inl rfl)),
    fun ⟨_, _, hg⟩ => Bool.noConfusion (hg at0 trivial (show at0 () false from rfl)),
    fun ⟨_, nb, up, _, _⟩ => nb (up at0 bot trivial trivial (show at0 () false from rfl)
      (fun _ _ h => Bool.noConfusion h)),
    fun ⟨_, _, h⟩ => Bool.noConfusion ((h at0 trivial).mp rfl)⟩

end Programme.«20261022-0733-ontological».Run2.ScottColumn

#print axioms Programme.«20261022-0733-ontological».Run2.ScottColumn.scott_gex_sym
#print axioms Programme.«20261022-0733-ontological».Run2.ScottColumn.scott_mc_sym
#print axioms Programme.«20261022-0733-ontological».Run2.ScottColumn.scott_s4_gap
