import Programme.«20261022-0733-ontological».Run2.FMGeneral

/-! # Standard symmetric models of Ax2a, Ax3, Ax4 collapse; the FM carriers separate (thread D)

th's E11 (P140, `agents/th/lean/Programme/Th/StandardKB.lean`), restated over the definitions of
`TwoClosed` (not copied from th's `RigidityFree` copy).

**Standard side** (`kb_collapse`).  With every property admitted, variant 2 (or 3') `Ax2a`, `Ax3`
and `Ax4` make every world see a *dead end* (`sees_deadEnd`): the nominal essence
`λz u. z = y ∧ u = v` of an entity necessarily existing at `v` forces every successor of `v` to
be `v`.  On a symmetric frame `R ⊆ id`, so admitted MC and `Ax2b`.  No `Ax1Gen`, no rigidity, no
principality is used.

**Fragment side** (`separating_kb`).  `FM.fm` is S5, closed under the fragment of `𝓛`
(`FMGeneral.lgeneral_fm`), and satisfies `Ax2a`, `Ax3`, `Ax3v3`, `Ax4`, `Ax1Gen`, `L`, not MC
or `Ax2b`.

**S4 does not suffice** (`s4_props`); **principality is God-existence** (`principal_iff_god`).

**Variant 2 separator** (`separating_v2`, sk P120): `FMGeneral.fmId` (identity frame) is a
fragment-closed model of variant 2 where v4's sentence `A ∃p. (Atom p ∧ p)` fails at every
world; it holds wherever singletons are admitted. -/
namespace Programme.«20261022-0733-ontological».Run2.StandardKB

open Programme.«20261022-0733-ontological».Run2.TwoClosed Programme.«20261022-0733-ontological».Run2.BoxIdle Programme.«20261022-0733-ontological».Run2.RigidFree Programme.«20261022-0733-ontological».Run2.FM
open Programme.«20261022-0733-ontological».Run2.LGeneral Programme.«20261022-0733-ontological».Run2.FMGeneral

variable {W D : Type} {M : Model W D}

theorem neg_top : neg (top : D → W → Prop) = bot := by
  funext x v; exact propext ⟨fun h => h trivial, False.elim⟩

/-- `Ax2a` and `Ax4` exclude a positive `⊥`. -/
theorem not_pBot (hT : M.AT top) (hB : M.AT bot) (h2a : Ax2a M) (h4 : Ax4 M) (w : W) :
    ¬ M.P bot w := by
  intro hb
  have ht : M.P top w := h4 bot top hB hT w hb (fun _ _ _ _ h => h.elim)
  exact (h2a top hT w).2 ⟨ht, neg_top ▸ hb⟩

/-- A positive property is exemplified by an actual entity at some successor. -/
theorem somewhere (hT : M.AT top) (hB : M.AT bot) (h2a : Ax2a M) (h4 : Ax4 M)
    {φ : D → W → Prop} (hA : M.AT φ) {w : W} (hφ : M.P φ w) :
    ∃ v y, M.R w v ∧ M.act y v ∧ φ y v :=
  Classical.byContradiction fun hn =>
    not_pBot hT hB h2a h4 w (h4 φ bot hA hB w hφ fun v hv y hy h => hn ⟨v, y, hv, hy, h⟩)

/-- Full property carrier. -/
def FullT (M : Model W D) : Prop := ∀ φ, M.AT φ

theorem deadEnd_of_E (hF : FullT M) {y : D} {v : W} (hE : E M y v) :
    ∀ u, M.R v u → u = v := by
  intro u hvu
  have ess : Ess M (fun z u => z = y ∧ u = v) y v :=
    ⟨⟨rfl, rfl⟩, fun ψ _ hψ u _ z _ ⟨hz, hu⟩ => hz ▸ hu ▸ hψ⟩
  obtain ⟨_, _, _, hu⟩ := hE _ (hF _) ess u hvu
  exact hu

theorem deadEnd_of_E3 (hF : FullT M) {y : D} {v : W} (hE : E3 M y v) :
    ∀ u, M.R v u → u = v := by
  intro u hvu
  have ess : Ess3 M (fun z u => z = y ∧ u = v) y v := by
    intro ψ _ hψ u _
    refine ⟨fun e => ?_, fun z _ ⟨hz, hu⟩ => hz ▸ hu ▸ hψ⟩
    have : (fun z u => z = y ∧ u = v) y v := ⟨rfl, rfl⟩
    rw [e] at this; exact this
  obtain ⟨_, _, _, hu⟩ := hE _ (hF _) ess u hvu
  exact hu

/-- Every world sees a dead end (variant 2 or 3'), any frame. -/
theorem sees_deadEnd (hF : FullT M) (h2a : Ax2a M) (h4 : Ax4 M) (h3 : Ax3 M ∨ Ax3v3 M)
    (w : W) : ∃ v, M.R w v ∧ ∀ u, M.R v u → u = v := by
  rcases h3 with h3 | h3
  · obtain ⟨v, y, hv, _, hE⟩ := somewhere (hF _) (hF _) h2a h4 (hF _) (h3 w)
    exact ⟨v, hv, deadEnd_of_E hF hE⟩
  · obtain ⟨v, y, hv, _, hE⟩ := somewhere (hF _) (hF _) h2a h4 (hF _) (h3 w)
    exact ⟨v, hv, deadEnd_of_E3 hF hE⟩

/-- **KB collapse.** -/
theorem kb_collapse (hF : FullT M) (hS : ∀ w v, M.R w v → M.R v w) (h2a : Ax2a M) (h4 : Ax4 M)
    (h3 : Ax3 M ∨ Ax3v3 M) : (∀ w v, M.R w v → v = w) ∧ MC M ∧ Ax2b M := by
  have h : ∀ w v, M.R w v → v = w := by
    intro w u hwu
    obtain ⟨v, hv, hd⟩ := sees_deadEnd hF h2a h4 h3 w
    have hw : w = v := hd w (hS w v hv)
    subst hw
    exact hd u hwu
  exact ⟨h, fun _ _ _ hp _ hwv => (h _ _ hwv) ▸ hp, fun _ _ _ hp _ hwv => (h _ _ hwv) ▸ hp⟩

/-- **Separation (KB).** -/
theorem separating_kb :
    (∀ (W D : Type) (M : Model W D), FullT M → (∀ w v, M.R w v → M.R v w) → Ax2a M →
      Ax4 M → (Ax3 M ∨ Ax3v3 M) → (∀ w v, M.R w v → v = w) ∧ MC M ∧ Ax2b M) ∧
    (LGeneral fm ∧ (∀ w v, fm.R w v) ∧ Ax2a fm ∧ Ax3 fm ∧ Ax3v3 fm ∧ Ax4 fm ∧ Ax1Gen fm ∧
      L fm ∧ ¬ MC fm ∧ ¬ Ax2b fm) := by
  obtain ⟨_, _, _, _, h2a, h3, h3', h4, _, _, hL, h1, _, _, _, _, hR, _, hb, hm⟩ :=
    rigidity_independent_fm
  exact ⟨fun _ _ _ hF hS h2a h4 h3 => kb_collapse hF hS h2a h4 h3,
    lgeneral_fm, hR, h2a, h3, h3', h4, h1, hL, hm, hb⟩

/-! ## S4 does not suffice -/

/-- Worlds `false → true`, both reflexive; positivity is truth at the dead end `true`. -/
def s4model : Model Bool Unit where
  R := fun a b => a = b ∨ b = true
  act := fun _ _ => True
  AS := fun _ => True
  AT := fun _ => True
  AH := fun _ => True
  P := fun φ _ => φ () true

theorem s4_props :
    LGeneral s4model ∧ (∀ a, s4model.R a a) ∧
      (∀ a b c, s4model.R a b → s4model.R b c → s4model.R a c) ∧
      Ax2a s4model ∧ Ax2b s4model ∧ Ax3 s4model ∧ Ax4 s4model ∧
      ¬ MC s4model ∧ ¬ ExG s4model false ∧ ExG s4model true := by
  refine ⟨lgeneral_full (fun _ => trivial) (fun _ => trivial) (fun _ => trivial),
    fun _ => Or.inl rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b c h1 h2
    rcases h2 with rfl | rfl
    · exact h1
    · exact Or.inr rfl
  · intro φ _ _
    show (φ () true ∨ ¬ φ () true) ∧ ¬ (φ () true ∧ ¬ φ () true)
    exact ⟨Classical.em _, fun ⟨a, b⟩ => b a⟩
  · intro _ _ _ hp _ _; exact hp
  · intro w
    show E s4model () true
    intro φ _ hess v hv
    have hv' : v = true := by rcases hv with h | h <;> simp_all
    exact ⟨(), trivial, hv' ▸ hess.1⟩
  · intro φ ψ _ _ w hφ hinc
    exact hinc true (Or.inr rfl) () trivial hφ
  · intro h
    have := h (fun w => w = false) trivial false rfl true (Or.inr rfl)
    exact Bool.noConfusion this
  · rintro ⟨y, _, hy⟩
    exact Bool.noConfusion (hy (fun _ u => u = true) trivial rfl)
  · exact ⟨(), trivial, fun φ _ hφ => hφ⟩

/-! ## Principality is God-existence under `Ax2a` -/

def Principal (M : Model W D) (w : W) : Prop :=
  ∀ φ, M.AT φ → (M.P φ w ↔ ∀ x, G M x w → φ x w)

theorem principal_iff_god (hT : M.AT top) (hN : ∀ φ, M.AT φ → M.AT (neg φ)) (h2a : Ax2a M)
    (w : W) : Principal M w ↔ ∃ x, G M x w := by
  constructor
  · intro hP
    refine Classical.byContradiction fun hn => ?_
    have none : ∀ x, ¬ G M x w := fun x hx => hn ⟨x, hx⟩
    have a := (hP top hT).2 fun x hx => (none x hx).elim
    have b := (hP (neg top) (hN _ hT)).2 fun x hx => (none x hx).elim
    exact (h2a top hT w).2 ⟨a, b⟩
  · rintro ⟨x, hx⟩ φ hA
    refine ⟨fun hφ y hy => hy φ hA hφ, fun h => ?_⟩
    rcases (h2a φ hA w).1 with hp | hn
    · exact hp
    · exact absurd (h x hx) (hx _ (hN φ hA) hn)

/-! ## sk's variant-2 separator on the identity frame (P120) -/

theorem fmId_god (x : Unit) (w : Cw) : G fmId x w := fun φ _ h => by cases x; exact h

theorem fmId_E (x : Unit) (w : Cw) : E fmId x w := fun _ _ hess v hv => by
  subst hv; cases x; exact ⟨(), trivial, hess.1⟩

theorem fmId_not_ax3v3 : ¬ Ax3v3 fmId := by
  intro h
  let w : Cw := fun _ => false
  let φ : Unit → Cw → Prop := fun _ u => u 0 = true
  have hφ : Based (φ ()) := ⟨1, fun a b hab => by simp only [φ]; rw [hab 0 Nat.zero_lt_one]⟩
  have hess : Ess3 fmId φ () w := fun ψ _ _ v hv => by
    subst hv
    refine ⟨fun e => ?_, fun y _ hy => absurd hy (by simp [φ, w])⟩
    have : φ () (fun _ => true) := rfl
    rw [e] at this; exact this
  obtain ⟨_, _, hy⟩ := h w φ hφ hess w rfl
  simp [φ, w] at hy

/-- `𝖣 p` at `u`: some admitted `ψ` fails at `u` and meets `p`. -/
def Dif {W : Type} (AS : (W → Prop) → Prop) (p : W → Prop) (u : W) : Prop :=
  ∃ ψ, AS ψ ∧ ¬ ψ u ∧ ∃ x, ψ x ∧ p x

def Atom {W : Type} (AS : (W → Prop) → Prop) (p : W → Prop) : Prop :=
  (∃ x, p x) ∧ ¬ ∃ x, p x ∧ Dif AS p x

/-- v4's sentence `∃p. Atom p ∧ p` at `w`, `p` ranging over `AS`. -/
def AtomAt {W : Type} (AS : (W → Prop) → Prop) (w : W) : Prop := ∃ p, AS p ∧ Atom AS p ∧ p w

theorem atomAt_of_singleton {W : Type} (AS : (W → Prop) → Prop) (w : W)
    (h : AS (fun u => u = w)) : AtomAt AS w :=
  ⟨_, h, ⟨⟨w, rfl⟩, fun ⟨x, hx, ψ, _, hn, y, hy, hyx⟩ => hn (hx ▸ hyx ▸ hy)⟩, rfl⟩

theorem not_atomAt (w : Cw) : ¬ AtomAt Based w := by
  rintro ⟨p, ⟨n, hn⟩, ⟨_, hno⟩, hw⟩
  let w' : Cw := fun i => if i = n then !(w n) else w i
  have hw' : p w' := (hn w w' fun i hi => by simp [w', Nat.ne_of_lt hi]).1 hw
  refine hno ⟨w, hw, fun u => u n = !(w n), ⟨n + 1, fun a b hab => by
    show a n = !(w n) ↔ b n = !(w n)
    rw [hab n (Nat.lt_succ_self n)]⟩, by simp, w', by simp [w'], hw'⟩

/-- **Variant-2 separator.** `fmId` is closed under the fragment, S5 (identity frame), satisfies
variant 2 (`Ax1Gen`, `Ax2a`, `Ax2b`, `Ax3`, `Ax4`) with MC and God everywhere, fails `Ax3v3`, and
refutes `A ∃p.(Atom p ∧ p)` at every world; the sentence holds wherever singletons are admitted. -/
theorem separating_v2 :
    LGeneral fmId ∧ Ax1Gen fmId ∧ Ax2a fmId ∧ Ax2b fmId ∧ Ax3 fmId ∧ Ax4 fmId ∧ MC fmId ∧
      (∀ w, ExG fmId w) ∧
      (∀ w v u, fmId.R w w ∧ (fmId.R w v → fmId.R v w) ∧ (fmId.R w v → fmId.R v u → fmId.R w u)) ∧
      ¬ Ax3v3 fmId ∧ (∀ w, ¬ AtomAt fmId.AS w) ∧
      (∀ {W : Type} (AS : (W → Prop) → Prop), (∀ w, AS (fun u => u = w)) → ∀ w, AtomAt AS w) :=
  ⟨lgeneral_fmId,
    fun _ _ _ _ w hpos hc => (hc w rfl () trivial).2 fun ψ hA hm => hpos ψ hA hm,
    fun φ _ w => ⟨Classical.em (φ () w), fun ⟨h1, h2⟩ => h2 h1⟩,
    fun _ _ _ h _ hv => hv ▸ h,
    fun w => fmId_E () w,
    fun _ _ _ _ w hφ hinc => hinc w rfl () trivial hφ,
    fun _ _ _ h _ hv => hv ▸ h,
    fun w => ⟨(), trivial, fmId_god () w⟩,
    fun _ _ _ => ⟨rfl, fun h => h ▸ rfl, fun h1 h2 => h2 ▸ h1⟩,
    fmId_not_ax3v3, not_atomAt,
    fun AS h w => atomAt_of_singleton AS w (h w)⟩

end Programme.«20261022-0733-ontological».Run2.StandardKB

#print axioms Programme.«20261022-0733-ontological».Run2.StandardKB.kb_collapse
#print axioms Programme.«20261022-0733-ontological».Run2.StandardKB.separating_kb
#print axioms Programme.«20261022-0733-ontological».Run2.StandardKB.s4_props
#print axioms Programme.«20261022-0733-ontological».Run2.StandardKB.principal_iff_god
#print axioms Programme.«20261022-0733-ontological».Run2.StandardKB.separating_v2
