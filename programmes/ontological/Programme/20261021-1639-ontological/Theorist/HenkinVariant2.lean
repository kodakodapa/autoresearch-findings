import Programme.«20261021-1639-ontological».Theorist.HenkinMinimal
/- D15: Goedel variant 2 (unrestricted world-dependent Ax1Gen) under Henkin semantics.
Properties range over `m.adm`, higher predicates (the `s` of Ax1Gen) over `admS`.
Variant-2 Ess/NE coincide with Scott's (`EssH`, `NEH`: `p x w` conjunct, PInc guard).
Positive results (no world naming; every admitted term used is listed in `CloV2`):
  `god_everywhere_H`  Ax1Gen + Ax2a ⇒ ∀w ∃ guarded x, G x w            (object part of K19)
  `principal_H`       ... and P(·,w) is principal at that God on admitted properties (K34)
  `T_adm`             Ax1Gen + Ax2a ⇒ □c → c for admitted propositions c
  `mc_of_ax2b_H`      Ax1Gen + Ax2a + Ax2b ⇒ MCadm, on every frame        (K20, Ax2b route)
Countermodels:
  `swap_*`   2 worlds, R = ≠ (irreflexive, symmetric), admitted = swap-invariant: all variant-2
             axioms hold, R is not reflexive (frame part of K19/K20 fails).
  `cw_*`     binary Cantor worlds, S5, P = current-world truth: Ax1, Ax2a, Ax3, Ax4, Ax1Gen (for
             every higher predicate), God everywhere, but ¬MCadm and ¬Ax2b (K20/K31 Ax3 route fails). -/
namespace Programme.«20261021-1639-ontological».Theorist.HenkinVariant2
open Programme.«20261021-1639-ontological».Theorist.HenkinScott Programme.«20261021-1639-ontological».Theorist.HenkinMinimal

variable {W E : Type} (m : GModel W E) (a : Bool)
  (admS : ((E → W → Prop) → W → Prop) → Prop)

def botP : E → W → Prop := fun _ _ => False
def negP (p : E → W → Prop) : E → W → Prop := fun x v => ¬ p x v

def Ax2a : Prop := ∀ p w, m.adm p →
  (m.positive p w ∨ m.positive (negP p) w) ∧ ¬ (m.positive p w ∧ m.positive (negP p) w)
def Ax1Gen : Prop := ∀ s p w, admS s → m.adm p →
  (∀ q, m.adm q → s q w → m.positive q w) →
  (∀ v, m.rel w v → ∀ y, guard m a y v → (p y v ↔ ∀ q, m.adm q → s q v → q y v)) →
  m.positive p w
def Ax2b : Prop := ∀ p w, m.adm p → m.positive p w → ∀ v, m.rel w v → m.positive p v
def Ax3 : Prop := ∀ w, m.positive (NEH m a) w
def Ax1 : Prop := ∀ p q w, m.adm p → m.adm q → m.positive p w → m.positive q w →
  m.positive (fun x v => p x v ∧ q x v) w
def Ax4 : Prop := ∀ p q w, m.adm p → m.adm q → m.positive p w →
  (∀ v, m.rel w v → ∀ y, guard m a y v → p y v → q y v) → m.positive q w

/-- Definable terms admitted; none names a world. -/
structure CloV2 : Prop where
  bot : m.adm botP
  neg : ∀ p, m.adm p → m.adm (negP p)
  god : m.adm (GH m)
  lift : ∀ c, m.admP c → m.adm (fun _ v => c v)
  empty : admS (fun _ _ => False)
  eq : ∀ φ, m.adm φ → admS (fun q _ => q = φ)
  pos : admS m.positive
  wit : ∀ φ, m.adm φ → admS (fun q v => q = φ ∨ ((∃ y, guard m a y v ∧ φ y v) ∧ q = botP))

variable {m a admS}
variable (hc : CloV2 m a admS) (h1 : Ax1Gen m a admS) (h2 : Ax2a m)
include hc h1 h2

theorem not_pos_bot (w : W) : ¬ m.positive botP w := by
  have ht : m.positive (negP botP) w :=
    h1 _ _ w hc.empty (hc.neg _ hc.bot) (fun _ _ h => h.elim)
      (fun _ _ _ _ => ⟨fun _ _ _ hf => hf.elim, fun _ h => h⟩)
  exact fun hb => (h2 botP w hc.bot).2 ⟨hb, ht⟩

/-- Slice dependence via the admitted higher predicate `q = φ`. -/
theorem slice (φ ψ : E → W → Prop) (hφ : m.adm φ) (hψ : m.adm ψ) (w : W)
    (hpos : m.positive φ w)
    (hs : ∀ v, m.rel w v → ∀ y, guard m a y v → (ψ y v ↔ φ y v)) : m.positive ψ w :=
  h1 (fun q _ => q = φ) ψ w (hc.eq φ hφ) hψ (fun q _ hq => hq ▸ hpos)
    (fun v hv y hy => ⟨fun h q _ hq => hq ▸ (hs v hv y hy).1 h,
      fun h => (hs v hv y hy).2 (h φ hφ rfl)⟩)

/-- A positive admitted property is instantiated by a guarded entity at the current world. -/
theorem witness (φ : E → W → Prop) (hφ : m.adm φ) (w : W) (hpos : m.positive φ w) :
    ∃ y, guard m a y w ∧ φ y w := by
  apply Classical.byContradiction
  intro hn
  apply not_pos_bot hc h1 h2 w
  apply h1 _ botP w (hc.wit φ hφ) hc.bot
  · intro q _ hs
    rcases hs with rfl | ⟨hN, _⟩
    · exact hpos
    · exact (hn hN).elim
  · intro v _ y hy
    refine ⟨fun h => h.elim, fun h => ?_⟩
    by_cases hN : ∃ y, guard m a y v ∧ φ y v
    · exact h botP hc.bot (Or.inr ⟨hN, rfl⟩)
    · exact hN ⟨y, hy, h φ hφ (Or.inl rfl)⟩

theorem god_positive_H (w : W) : m.positive (GH m) w :=
  h1 m.positive (GH m) w hc.pos hc.god (fun _ _ h => h) (fun _ _ _ _ => Iff.rfl)

/-- Object part of K19: a guarded God at every world. -/
theorem god_everywhere_H (w : W) : ∃ x, guard m a x w ∧ GH m x w :=
  witness hc h1 h2 _ hc.god w (god_positive_H hc h1 h2 w)

/-- K34, Henkin: P(·,w) is principal at a guarded God on admitted properties. -/
theorem principal_H (w : W) :
    ∃ x, guard m a x w ∧ ∀ φ, m.adm φ → (m.positive φ w ↔ φ x w) := by
  obtain ⟨x, hx, hg⟩ := god_everywhere_H hc h1 h2 w
  refine ⟨x, hx, fun φ hφ => ⟨hg φ hφ, fun h => Classical.byContradiction fun hn => ?_⟩⟩
  exact hg _ (hc.neg φ hφ) ((h2 φ w hφ).1.resolve_left hn) h

/-- T-schema for admitted propositions (replaces K19's reflexivity). -/
theorem T_adm (c : W → Prop) (hcA : m.admP c) (w : W) (hbox : ∀ v, m.rel w v → c v) : c w := by
  apply Classical.byContradiction
  intro hnc
  have hφ := hc.lift c hcA
  obtain ⟨x, _, hpr⟩ := principal_H hc h1 h2 w
  have hneg : m.positive (negP (fun _ v => c v)) w :=
    (h2 _ w hφ).1.resolve_left (fun hp => hnc ((hpr _ hφ).1 hp))
  exact not_pos_bot hc h1 h2 w
    (slice hc h1 h2 _ botP (hc.neg _ hφ) hc.bot w hneg
      (fun v hv _ _ => ⟨fun h => h.elim, fun h => h (hbox v hv)⟩))

/-- K20 (Ax2b route), Henkin: object-level collapse on every frame. -/
theorem mc_of_ax2b_H (hb : Ax2b m) : MCadm m := by
  intro c hcA w hw v hwv
  have hφ := hc.lift c hcA
  obtain ⟨x, _, hpr⟩ := principal_H hc h1 h2 w
  have hv := hb _ w hφ ((hpr _ hφ).2 hw) v hwv
  obtain ⟨y, _, hpr'⟩ := principal_H hc h1 h2 v
  exact (hpr' _ hφ).1 hv

omit hc h1 h2
variable (a)

/-! ### Swap model: irreflexive two-world frame, swap-invariant intensions. -/

def swap : GModel Bool Unit where
  rel w v := v ≠ w
  actual _ _ := True
  adm p := p () true ↔ p () false
  admP c := c true ↔ c false
  positive p w := p () w

def swapS (s : (Unit → Bool → Prop) → Bool → Prop) : Prop :=
  ∀ q, swap.adm q → (s q true ↔ s q false)

theorem swap_inv {p : Unit → Bool → Prop} (hp : swap.adm p) (x : Unit) (w v : Bool) :
    p x w ↔ p x v := by
  cases x; cases w <;> cases v <;> simp_all [swap]

theorem swapS_inv {s : (Unit → Bool → Prop) → Bool → Prop} (hs : swapS s)
    {q : Unit → Bool → Prop} (hq : swap.adm q) (w v : Bool) : s q w ↔ s q v := by
  cases w <;> cases v <;> simp_all [swapS]

theorem swap_G (x : Unit) (w : Bool) : GH swap x w := by
  intro p _ hp; cases x; exact hp

theorem swap_NE (x : Unit) (w : Bool) : NEH swap a x w := by
  intro p hp he v _
  exact ⟨(), fun _ => trivial, (swap_inv hp x w v).1 he.1⟩

theorem swap_clo : CloV2 swap a swapS := by
  refine ⟨Iff.rfl, fun p hp => not_congr hp, iff_of_true (swap_G () true) (swap_G () false), fun c hc => hc, fun _ _ => Iff.rfl,
    fun φ _ q _ => Iff.rfl, fun q hq => hq, fun φ hφ q hq => ?_⟩
  have h1 : (∃ y, guard swap a y true ∧ φ y true) ↔ (∃ y, guard swap a y false ∧ φ y false) :=
    ⟨fun ⟨y, _, h⟩ => ⟨y, fun _ => trivial, (swap_inv hφ y true false).1 h⟩,
     fun ⟨y, _, h⟩ => ⟨y, fun _ => trivial, (swap_inv hφ y true false).2 h⟩⟩
  exact or_congr Iff.rfl (and_congr h1 Iff.rfl)

theorem swap_props :
    CloV2 swap a swapS ∧ Ax1Gen swap a swapS ∧ Ax2a swap ∧ Ax2b swap ∧ Ax3 swap a ∧
    Ax1 swap ∧ Ax4 swap a ∧ (∀ w v, swap.rel w v → swap.rel v w) ∧
    (∀ w, ¬ swap.rel w w) ∧ MCadm swap := by
  refine ⟨swap_clo a, ?_, ?_, ?_, fun w => swap_NE a () w, fun _ _ _ _ _ hp hq => ⟨hp, hq⟩,
    ?_, fun _ _ h => Ne.symm h, fun _ h => h rfl, ?_⟩
  · intro s p w hs hp hpos hconj
    have := (hconj (!w) (show (!w) ≠ w by cases w <;> decide) () (fun _ => trivial)).2
      (fun q hq hsq => (swap_inv hq () w (!w)).1 (hpos q hq ((swapS_inv hs hq w (!w)).2 hsq)))
    exact (swap_inv hp () w (!w)).2 this
  · intro p w _
    show (p () w ∨ ¬ p () w) ∧ ¬ (p () w ∧ ¬ p () w)
    exact ⟨Classical.em _, fun h => h.2 h.1⟩
  · intro p w hp h v _
    exact (swap_inv hp () w v).1 h
  · intro p q w hp hq h hpq
    have := hpq (!w) (show (!w) ≠ w by cases w <;> decide) () (fun _ => trivial) ((swap_inv hp () w (!w)).1 h)
    exact (swap_inv hq () w (!w)).2 this
  · intro c hcA w hw v _
    cases w <;> cases v <;> simp_all [swap]

/-! ### Current-world Cantor model: Ax3 does not force object-level collapse. -/

theorem cw_props :
    CloV2 cantorCW a (fun _ => True) ∧ Ax1Gen cantorCW a (fun _ => True) ∧ Ax2a cantorCW ∧
    Ax3 cantorCW a ∧ Ax1 cantorCW ∧ Ax4 cantorCW a ∧
    (∀ w v, cantorCW.rel w v) ∧ (∀ w, ∃ x, GH cantorCW x w) ∧
    ¬ Ax2b cantorCW ∧ ¬ MCadm cantorCW := by
  obtain ⟨hn, _, _, _, _, hbot, hl⟩ := cantor_clo_partial a
  have hcw := (henkin_drop_A4 a).1
  refine ⟨⟨hbot, hn, hcw.g, hl, trivial, fun _ _ => trivial, trivial, fun _ _ => trivial⟩,
    ?_, ?_, fun w => cantorCW_NE a () w, fun _ _ _ _ _ hp hq => ⟨hp, hq⟩, ?_,
    fun _ _ => trivial, fun w => ⟨(), cantorCW_G () w⟩, ?_, (henkin_drop_A4 a).2.2.2.2.2.2.2.2⟩
  · intro s p w _ _ hpos hconj
    exact (hconj w trivial () (fun _ => trivial)).2 (fun q hq hsq => hpos q hq hsq)
  · intro p w _
    show (p () w ∨ ¬ p () w) ∧ ¬ (p () w ∧ ¬ p () w)
    exact ⟨Classical.em _, fun h => h.2 h.1⟩
  · intro p q w _ _ hp hpq
    exact hpq w trivial () (fun _ => trivial) hp
  · intro h
    have hadm : cantorCW.adm (fun _ v => v 0 = true) :=
      ⟨1, fun v v' hvv => by show v 0 = true ↔ v' 0 = true; rw [hvv 0 Nat.zero_lt_one]⟩
    have := h _ (fun _ => true) hadm rfl (fun _ => false) trivial
    exact Bool.false_ne_true this

#print axioms god_everywhere_H
#print axioms principal_H
#print axioms T_adm
#print axioms mc_of_ax2b_H
#print axioms swap_props
#print axioms cw_props
end Programme.«20261021-1639-ontological».Theorist.HenkinVariant2
