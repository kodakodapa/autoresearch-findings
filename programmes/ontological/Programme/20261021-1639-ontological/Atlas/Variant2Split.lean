import Programme.«20261021-1639-ontological».Atlas.Variant2
/- D8: adapted from sk P107, on pr's existing parameterized semantics.
Full intensions; no finiteness or nonempty-type hypotheses. -/
namespace Programme.«20261021-1639-ontological».Atlas.Variant2Split
open Programme.«20261021-1639-ontological».Atlas.Variant2
universe u v
variable {W : Type u} {E : Type v} (R : W → W → Prop) (g k : E → W → Prop)
  (P : (E → W → Prop) → W → Prop)
def Ax2a : Prop := ∀ p w, (P p w ∨ P (neg p) w) ∧ ¬ (P p w ∧ P (neg p) w)
def Ax1Gen : Prop := ∀ (s : (E → W → Prop) → W → Prop) p w,
  ((∀ q, s q w → P q w) ∧
   (∀ v, R w v → ∀ y, g y v → (p y v ↔ ∀ q, s q v → q y v))) → P p w
def Ax2b : Prop := ∀ p w, P p w → ∀ v, R w v → P p v
def Ax3 : Prop := ∀ w, P (NE R g k) w
variable {R g k P}
theorem toCore (h1 : Ax1Gen R g P) (h2 : Ax2a P) : Core R g P :=
  ⟨h2, fun s p w hp hc => h1 s p w ⟨hp, hc⟩⟩
theorem refl (h1 : Ax1Gen R g P) (h2 : Ax2a P) (w : W) : R w w :=
  frame_reflexive R g P (toCore h1 h2) w
theorem god (h1 : Ax1Gen R g P) (h2 : Ax2a P) (w : W) : ∃ x, g x w ∧ God P x w :=
  god_everywhere R g P (toCore h1 h2) w
def Ax1 (P : (E → W → Prop) → W → Prop) : Prop :=
  ∀ φ ψ w, P φ w → P ψ w → P (fun x v => φ x v ∧ ψ x v) w
/-- Ax4: `⌊P φ ∧ᵐ (φ ⊃ᴺ ψ) →ᵐ P ψ⌋`, PInc guarded by g. -/
def Ax4 (R : W → W → Prop) (g : E → W → Prop) (P : (E → W → Prop) → W → Prop) : Prop :=
  ∀ φ ψ w, P φ w → (∀ v, R w v → ∀ y, g y v → φ y v → ψ y v) → P ψ w
def MC (R : W → W → Prop) : Prop := ∀ (p : W → Prop) w, p w → ∀ v, R w v → p v
def Th5 (R : W → W → Prop) (k : E → W → Prop) (P : (E → W → Prop) → W → Prop) : Prop :=
  ∀ w v, R w v → ∃ x, k x v ∧ God P x v
def Mono (P : (E → W → Prop) → W → Prop) : Prop := ∀ (x y : E) w, God P x w → God P y w → x = y

/-- D8 L1, first half: Ax1Gen alone, at an irreflexive world every property is positive. -/
theorem L1_irrefl (h1 : Ax1Gen R g P) (w : W) (hw : ¬ R w w) (φ : E → W → Prop) : P φ w :=
  h1 (fun ψ u => u ≠ w ∧ ψ = φ) φ w
    ⟨fun _ h => (h.1 rfl).elim, fun _ hv _ _ =>
      ⟨fun h _ hψ => hψ.2 ▸ h, fun h => h φ ⟨fun e => hw (e ▸ hv), rfl⟩⟩⟩

/-- D8 L1, second half: membership in P(w) depends only on the g-guarded slice at w. -/
theorem L1_slice (h1 : Ax1Gen R g P) (w : W) (φ φ' : E → W → Prop) (hφ : P φ w)
    (hs : ∀ z, g z w → (φ' z w ↔ φ z w)) : P φ' w := by
  classical
  refine h1 (fun ψ u => (u = w ∧ ψ = φ) ∨ (u ≠ w ∧ ψ = φ')) φ' w
    ⟨fun ψ h => ?_, fun v _ z hz => ?_⟩
  · rcases h with ⟨_, rfl⟩ | ⟨h, _⟩
    · exact hφ
    · exact (h rfl).elim
  · by_cases e : v = w
    · subst e
      refine ⟨fun h ψ hψ => ?_, fun h => (hs z hz).2 (h φ (Or.inl ⟨rfl, rfl⟩))⟩
      rcases hψ with ⟨_, rfl⟩ | ⟨hne, _⟩
      · exact (hs z hz).1 h
      · exact (hne rfl).elim
    · refine ⟨fun h ψ hψ => ?_, fun h => h φ' (Or.inr ⟨e, rfl⟩)⟩
      rcases hψ with ⟨he, _⟩ | ⟨_, rfl⟩
      · exact (e he).elim
      · exact h

/-- D8 L2: Ax2b and Ax1Gen (no Ax2a) make every property positive at a proper successor. -/
theorem L2 (hb : Ax2b R P) (h1 : Ax1Gen R g P) (w v : W) (hv : R w v) (hne : v ≠ w)
    (χ : E → W → Prop) : P χ v := by
  classical
  let φ : E → W → Prop := fun z u => u ≠ w → χ z u
  have hφ : P φ w := h1 (fun ψ u => u ≠ w ∧ ψ = φ) φ w
    ⟨fun _ h => (h.1 rfl).elim, fun u _ z _ => by
      by_cases e : u = w
      · subst e
        exact ⟨fun _ ψ hψ => (hψ.1 rfl).elim, fun _ h => (h rfl).elim⟩
      · exact ⟨fun h ψ hψ => hψ.2 ▸ h, fun h => h φ ⟨e, rfl⟩⟩⟩
  have hφv : P φ v := hb φ w hφ v hv
  by_cases hvv : R v v
  · exact L1_slice h1 v φ χ hφv (fun z _ => ⟨fun h _ => h, fun h => h hne⟩)
  · exact L1_irrefl h1 v hvv χ

/-- Structure theorem: Ax2a + Ax1Gen give reflexivity and a principal P(w) at a g-guarded a_w. -/
theorem principal (h1 : Ax1Gen R g P) (h2 : Ax2a P) (w : W) :
    R w w ∧ ∃ a, g a w ∧ ∀ φ, P φ w ↔ φ a w := by
  refine ⟨refl h1 h2 w, ?_⟩
  obtain ⟨a, ha, hG⟩ := god h1 h2 w
  refine ⟨a, ha, fun φ => ⟨hG φ, fun h => Classical.byContradiction fun hn => ?_⟩⟩
  exact hG _ ((h2 φ w).1.resolve_left hn) h

/-- Converse of the structure theorem: such models satisfy Ax2a and Ax1Gen. -/
theorem principal_converse (hr : ∀ w, R w w)
    (hp : ∀ w, ∃ a, g a w ∧ ∀ φ, P φ w ↔ φ a w) : Ax2a P ∧ Ax1Gen R g P := by
  refine ⟨fun φ w => ?_, fun Φ φ w ⟨hpos, hconj⟩ => ?_⟩
  · obtain ⟨a, _, h⟩ := hp w
    rw [h, h]
    by_cases hφ : φ a w
    · exact ⟨Or.inl hφ, fun hh => hh.2 hh.1⟩
    · exact ⟨Or.inr hφ, fun hh => hh.2 hh.1⟩
  · obtain ⟨a, ha, h⟩ := hp w
    exact (h φ).2 ((hconj w (hr w) a ha).2 fun ψ hψ => (h ψ).1 (hpos ψ hψ))

/-- Ax1 is redundant given Ax2a + Ax1Gen. -/
theorem ax1_of (h1 : Ax1Gen R g P) (h2 : Ax2a P) : Ax1 P := by
  intro φ ψ w hφ hψ
  obtain ⟨_, a, _, h⟩ := principal h1 h2 w
  exact (h _).2 ⟨(h φ).1 hφ, (h ψ).1 hψ⟩

/-- Ax4 is redundant given Ax2a + Ax1Gen (PInc guard = conjunction guard, as in variant 2). -/
theorem ax4_of (h1 : Ax1Gen R g P) (h2 : Ax2a P) : Ax4 R g P := by
  intro φ ψ w hφ hinc
  obtain ⟨hr, a, ha, h⟩ := principal h1 h2 w
  exact (h ψ).2 (hinc w hr a ha ((h φ).1 hφ))

/-- Monotheism from Ax2a alone (identity; Leibniz equality coincides under full properties). -/
theorem mono_of_ax2a (h2 : Ax2a P) : Mono P := by
  intro x y w hx hy
  rcases (h2 (fun z _ => z = x) w).1 with h | h
  · exact (hy _ h).symm
  · exact (hx _ h rfl).elim

/-- Exit model: S5 on two worlds, one always-actual entity, P(w) = {φ | φ () w}. -/
def exitP : (Unit → Bool → Prop) → Bool → Prop := fun φ w => φ () w

theorem exit_model :
    let R : Bool → Bool → Prop := fun _ _ => True
    let g : Unit → Bool → Prop := fun _ _ => True
    Ax2a exitP ∧ Ax1Gen R g exitP ∧ Ax1 exitP ∧ Ax4 R g exitP ∧ Th5 R g exitP ∧
      ¬ MC R ∧ ¬ Ax2b R exitP ∧ ¬ Ax3 R g g exitP := by
  intro R g
  have hp : ∀ w, ∃ a, g a w ∧ ∀ φ, exitP φ w ↔ φ a w := fun w => ⟨(), trivial, fun _ => Iff.rfl⟩
  obtain ⟨h2, h1⟩ := principal_converse (R := R) (g := g) (fun _ => trivial) hp
  refine ⟨h2, h1, ax1_of h1 h2, ax4_of h1 h2, fun _ v _ => god h1 h2 v, ?_, ?_, ?_⟩
  · intro h; exact absurd (h (fun w => w = false) false rfl true trivial) (by decide)
  · intro h
    have h' : exitP (fun _ u => u = false) true := h (fun _ u => u = false) false rfl true trivial
    exact absurd (show true = false from h') (by decide)
  · intro h
    have hne := h false
    have hess : Ess R g (fun y u => y = () ∧ u = false) () false :=
      ⟨⟨rfl, rfl⟩, fun ψ hψ u _ y _ hy => by obtain ⟨rfl, rfl⟩ := hy; exact hψ⟩
    obtain ⟨_, _, _, e⟩ := hne _ hess true trivial
    exact absurd e (by decide)

def Symmetric (R : W → W → Prop) : Prop := ∀ w v, R w v → R v w
def Th3 (R : W → W → Prop) (k : E → W → Prop)
    (P : (E → W → Prop) → W → Prop) : Prop :=
  ∀ w, (∃ v, R w v ∧ ∃ x, k x v ∧ God P x v) →
    ∀ v, R w v → ∃ x, k x v ∧ God P x v

theorem god_ax3_final (h3 : Ax3 R g k P) (x : E) (w : W) (hg : God P x w) :
    ∀ v, R w v → v = w := by
  intro v hv
  obtain ⟨_, _, he⟩ := hg _ (h3 w) _ (singleton_essence R g x w) v hv
  exact he.2

theorem god_predecessor (h1 : Ax1Gen R g P) (hb : Ax2b R P)
    (w v : W) (hv : R w v) (x : E) (hg : God P x v) : v = w := by
  apply Classical.byContradiction
  intro hn
  exact hg bot (L2 hb h1 w v hv hn bot)

theorem th3_of_ax2b_ax3 (h1 : Ax1Gen R g P) (hb : Ax2b R P)
    (h3 : Ax3 R g k P) : Th3 R k P := by
  intro w ⟨u, hu, x, hx, hg⟩ v hv
  have he := god_predecessor h1 hb w u hu x hg
  subst u
  have he := god_ax3_final h3 x w hg v hv
  subst v
  exact ⟨x, hx, hg⟩

theorem th3_KB_of_ax3 (hs : Symmetric R) (h3 : Ax3 R g k P) : Th3 R k P := by
  intro w ⟨u, hu, x, hx, hg⟩ v hv
  have he := god_ax3_final h3 x u hg w (hs w u hu)
  subst w
  have he := god_ax3_final h3 x u hg v hv
  subst v
  exact ⟨x, hx, hg⟩

theorem th3_KB_of_ax2b (hs : Symmetric R) (h1 : Ax1Gen R g P)
    (hb : Ax2b R P) : Th3 R k P := by
  intro w ⟨u, hu, x, hx, hg⟩ v hv
  have he := god_predecessor h1 hb w u hu x hg
  subst u
  have he := god_predecessor h1 hb v w (hs w v hv) x hg
  subst v
  exact ⟨x, hx, hg⟩

theorem id_KB_of_ax2a_ax3_ax4 (hs : Symmetric R) (h2 : Ax2a P)
    (h3 : Ax3 R g k P) (h4 : Ax4 R g P) : ∀ w v, R w v → w = v := by
  intro w v hv
  have hex : ∃ t, R w t ∧ ∃ x, g x t ∧ NE R g k x t := by
    apply Classical.byContradiction
    intro hn
    have hp : P (neg (NE R g k)) w := h4 _ _ w (h3 w)
      (fun t ht x hx hne => (hn ⟨t, ht, x, hx, hne⟩).elim)
    exact (h2 _ w).2 ⟨h3 w, hp⟩
  obtain ⟨t, ht, x, _, hne⟩ := hex
  obtain ⟨_, _, he⟩ := hne _ (singleton_essence R g x t) w (hs w t ht)
  have e := he.2
  subst t
  obtain ⟨_, _, he⟩ := hne _ (singleton_essence R g x w) v hv
  exact he.2.symm

theorem mc_KB_of_ax2a_ax3_ax4 (hs : Symmetric R) (h2 : Ax2a P)
    (h3 : Ax3 R g k P) (h4 : Ax4 R g P) : MC R := by
  intro p w hp v hv
  exact id_KB_of_ax2a_ax3_ax4 hs h2 h3 h4 w v hv ▸ hp

#print axioms god_ax3_final
#print axioms th3_of_ax2b_ax3
#print axioms th3_KB_of_ax3
#print axioms th3_KB_of_ax2b
#print axioms mc_KB_of_ax2a_ax3_ax4
#print axioms L1_irrefl
#print axioms L1_slice
#print axioms L2
#print axioms principal
#print axioms principal_converse
#print axioms ax1_of
#print axioms ax4_of
#print axioms mono_of_ax2a
#print axioms exit_model
end Programme.«20261021-1639-ontological».Atlas.Variant2Split
