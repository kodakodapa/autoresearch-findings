import Programme.«20261022-0733-ontological».Run2.GodlessL

/-! # K8 and K9 over the finitely supported carriers of arXiv 2609.36279 v4 Example `ex:separating`

th's construction (P103, `agents/th/lean/Programme/Th/FMSupported.lean`, `FMGodless.lean`),
restated over the definitions of `TwoClosed`, `DropDagger`, `OneHF`, `BoxIdle`, `UniqueEss` and
the models of `RigidFree`/`GodlessL` (imported, not copied).

v4 `ex:separating` takes, on `W = 2^ℕ` with the total relation and one individual, the hereditarily
finitely supported objects for the flip group `x ↦ x ⊕ d`, `G_n` = flips with `d i = false` for
`i < n`.  Its fact (b): at proposition type these are the finitary (finitely based) sets.  Here the
property and proposition carriers stay those of `cantor`; the collection carrier becomes
`FMH`, the collections fixed by some `G_n`.  `fm` (positivity = truth at `w`) and `gfm` (positivity
= truth at `f w`, `f` sets bit `0`, fixed by `G_1`) keep every conjunct of K8 and K9.  The step
"these carriers are closed under all `𝓛`-terms" is v4's fact (a), proved on paper, not here. -/
namespace Programme.«20261022-0733-ontological».Run2.FM

open Programme.«20261022-0733-ontological».Run2.TwoClosed Programme.«20261022-0733-ontological».Run2.DropDagger Programme.«20261022-0733-ontological».Run2.OneHF
  Programme.«20261022-0733-ontological».Run2.BoxIdle Programme.«20261022-0733-ontological».Run2.UniqueEss Programme.«20261022-0733-ontological».Run2.RigidFree

/-! ## Flips -/

/-- The flip `w ⊕ d`. -/
def xorw (w d : Cw) : Cw := fun i => xor (w i) (d i)

theorem xorw_xorw (w d : Cw) : xorw (xorw w d) d = w := by
  funext i; simp [xorw]

theorem xorw_cancel (w v : Cw) : xorw w (xorw w v) = v := by
  funext i; simp [xorw]

/-- `d ∈ G_n`. -/
def Fixes (n : Nat) (d : Cw) : Prop := ∀ i, i < n → d i = false

theorem fixes_mono {n m : Nat} (h : n ≤ m) {d : Cw} (hd : Fixes m d) : Fixes n d :=
  fun i hi => hd i (Nat.lt_of_lt_of_le hi h)

/-- Action of a flip on a property. -/
def act (d : Cw) (ψ : Unit → Cw → Prop) : Unit → Cw → Prop := fun x v => ψ x (xorw v d)

theorem act_act (d : Cw) (ψ : Unit → Cw → Prop) : act d (act d ψ) = ψ := by
  funext x v; simp [act, xorw_xorw]

/-- Finitely based = fixed by some `G_n` (fact (b) of the example). -/
theorem based_iff (p : Cw → Prop) :
    Based p ↔ ∃ n, ∀ d, Fixes n d → ∀ w, (p w ↔ p (xorw w d)) := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, fun d hd w => hn w _ fun i hi => by simp [xorw, hd i hi]⟩
  · rintro ⟨n, hn⟩
    refine ⟨n, fun w v hwv => ?_⟩
    have hd : Fixes n (xorw w v) := fun i hi => by simp [xorw, hwv i hi]
    have := hn _ hd w
    rwa [xorw_cancel] at this

theorem act_based {ψ : Unit → Cw → Prop} (h : Based (ψ ())) (d : Cw) : Based (act d ψ ()) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, fun w v hwv => hn _ _ fun i hi => by simp [xorw, hwv i hi]⟩

theorem act_fix {ψ : Unit → Cw → Prop} {n : Nat}
    (hn : ∀ d, Fixes n d → ∀ w, (ψ () w ↔ ψ () (xorw w d))) {d : Cw} (hd : Fixes n d) :
    act d ψ = ψ := by
  funext x v; cases x; exact propext (hn d hd v).symm

/-- Finitely supported collections of properties. -/
def FMH (Φ : (Unit → Cw → Prop) → Cw → Prop) : Prop :=
  ∃ n, ∀ d, Fixes n d → ∀ ψ w, (Φ ψ w ↔ Φ (act d ψ) (xorw w d))

/-- Values of a supported collection at finitary properties are finitary. -/
theorem fmH_values {Φ} (hΦ : FMH Φ) {ψ : Unit → Cw → Prop} (hψ : Based (ψ ())) : Based (Φ ψ) := by
  obtain ⟨n, hn⟩ := hΦ
  obtain ⟨m, hm⟩ := (based_iff _).1 hψ
  refine (based_iff _).2 ⟨max n m, fun d hd w => ?_⟩
  have e := act_fix hm (fixes_mono (Nat.le_max_right n m) hd)
  have := hn d (fixes_mono (Nat.le_max_left n m) hd) ψ w
  rwa [e] at this

theorem atMost_based {Φ} (hΦ : FMH Φ) {ψ₀ : Unit → Cw → Prop} (h0 : Based (ψ₀ ())) :
    Based (atMostS (fun φ => Based (φ ())) Φ ψ₀) := by
  obtain ⟨n, hn⟩ := hΦ
  obtain ⟨m, hm⟩ := (based_iff _).1 h0
  have one : ∀ d, Fixes (max n m) d → ∀ u, atMostS (fun φ => Based (φ ())) Φ ψ₀ u →
      atMostS (fun φ => Based (φ ())) Φ ψ₀ (xorw u d) := by
    intro d hd u h ψ hA hm'
    have h1 : Φ (act d ψ) u := by
      have := (hn d (fixes_mono (Nat.le_max_left n m) hd) ψ (xorw u d)).1 hm'
      rwa [xorw_xorw] at this
    have h2 := h (act d ψ) (act_based hA d) h1
    have e := act_fix hm (fixes_mono (Nat.le_max_right n m) hd)
    rw [← act_act d ψ, h2, e]
  refine (based_iff _).2 ⟨max n m, fun d hd u => ⟨one d hd u, fun h => ?_⟩⟩
  have := one d hd _ h
  rwa [xorw_xorw] at this

theorem fmH_sub {Φ} (hΦ : FMH Φ) : cantor.AH Φ := fun _ h0 => atMost_based hΦ h0

theorem single_fmh (ψ : Unit → Cw → Prop) (hψ : Based (ψ ())) : FMH (fun ψ' (_ : Cw) => ψ' = ψ) := by
  obtain ⟨n, hn⟩ := (based_iff _).1 hψ
  refine ⟨n, fun d hd ψ' _ => ?_⟩
  have e := act_fix hn hd
  constructor
  · intro h; rw [h, e]
  · intro h; rw [← act_act d ψ', h, e]

theorem union_fmh {Φ Ψ} (hΦ : FMH Φ) (hΨ : FMH Ψ) : FMH (fun ψ w => Φ ψ w ∨ Ψ ψ w) := by
  obtain ⟨n, hn⟩ := hΦ; obtain ⟨m, hm⟩ := hΨ
  exact ⟨max n m, fun d hd ψ w =>
    or_congr (hn d (fixes_mono (Nat.le_max_left n m) hd) ψ w)
      (hm d (fixes_mono (Nat.le_max_right n m) hd) ψ w)⟩

theorem guard_fmh {p : Cw → Prop} {Φ} (hp : Based p) (hΦ : FMH Φ) :
    FMH (fun ψ w => p w ∧ Φ ψ w) := by
  obtain ⟨n, hn⟩ := hΦ
  obtain ⟨m, hm⟩ := (based_iff _).1 hp
  exact ⟨max n m, fun d hd ψ w =>
    and_congr (hm d (fixes_mono (Nat.le_max_right n m) hd) w)
      (hn d (fixes_mono (Nat.le_max_left n m) hd) ψ w)⟩

/-! ## K8 over FM carriers -/

def fm : Model Cw Unit where
  R := fun _ _ => True
  act := fun _ _ => True
  AS := Based
  AT := fun φ => Based (φ ())
  AH := FMH
  P := fun φ w => φ () w

theorem pos_fm : FMH fm.P := ⟨0, fun d _ ψ w => by simp [fm, act, xorw_xorw]⟩

theorem closed_fm : Closed fm where
  top := RigidFree.closed.top
  bot := RigidFree.closed.bot
  neg := RigidFree.closed.neg
  conj := RigidFree.closed.conj
  lift := RigidFree.closed.lift
  negS := RigidFree.closed.negS
  god := RigidFree.closed.god
  exG := RigidFree.closed.exG
  pos := pos_fm
  single := single_fmh
  union := fun _ _ => union_fmh
  guard := fun _ _ => guard_fmh
  atMost := fun _ _ hΦ h0 => atMost_based hΦ h0

theorem ax1Gen_fm : Ax1Gen fm := fun _ _ _ _ w hpos hc =>
  (hc w trivial () trivial).2 fun ψ hA hm => hpos ψ hA hm

theorem ax1GenTwo_fm : Ax1GenTwo fm := fun Φ φ hΦ hφ w _ => ax1Gen_fm Φ φ hΦ hφ w
theorem ax1GenOne_fm : Ax1GenOne fm := fun Φ φ hΦ hφ w _ => ax1Gen_fm Φ φ hΦ hφ w

/-- **K8 over the carriers of v4 `ex:separating`.** Every conjunct of `RigidFree.rigidity_independent`,
with `AH` the finitely supported collections. -/
theorem rigidity_independent_fm :
    Closed fm ∧ Extra fm ∧ fm.AT (E fm) ∧ fm.AT (E3 fm) ∧
      Ax2a fm ∧ Ax3 fm ∧ Ax3v3 fm ∧ Ax4 fm ∧ Ax4c fm ∧ Th4 fm ∧
      L fm ∧ Ax1Gen fm ∧ Ax1GenTwo fm ∧ Ax1GenOne fm ∧ Ax1GenBoxTwo fm ∧
      (∀ w, ExG fm w) ∧ (∀ w v, fm.R w v) ∧ (∀ y w, fm.act y w) ∧
      ¬ Ax2b fm ∧ ¬ MC fm :=
  ⟨closed_fm, ⟨RigidFree.extra.hid, RigidFree.extra.hact, RigidFree.extra.happ⟩, RigidFree.E_adm, RigidFree.E3_adm, RigidFree.ax2a,
    RigidFree.ax3, RigidFree.ax3v3, RigidFree.ax4, RigidFree.ax4c, RigidFree.th4, RigidFree.l,
    ax1Gen_fm, ax1GenTwo_fm, ax1GenOne_fm, boxTwo_of_L closed_fm.god RigidFree.ax4 RigidFree.l,
    RigidFree.exG_all, fun _ _ => trivial, fun _ _ => trivial, RigidFree.not_ax2b,
    RigidFree.not_mc⟩

/-- The collection carrier: every admitted collection is admitted in `cantor`, and takes
finitary values on finitary properties (so it represents the example's `P_{(e→σ)→σ}`). -/
theorem carriers : ∀ Φ, fm.AH Φ → cantor.AH Φ ∧ ∀ ψ, fm.AT ψ → fm.AS (Φ ψ) :=
  fun _ hΦ => ⟨fmH_sub hΦ, fun _ hψ => fmH_values hΦ hψ⟩

/-- Thread D (K10 over FM carriers): positivity of `fm` is the principal filter generated by
God-likeness; principality kept, rigidity dropped, no collapse. -/
theorem rigidity_exit_fm :
    Closed fm ∧ (∀ φ w, fm.P φ w ↔ ∀ x, G fm x w → φ x w) ∧
      Ax2a fm ∧ Ax3 fm ∧ Ax3v3 fm ∧ Ax4 fm ∧ L fm ∧ Ax1Gen fm ∧
      (∀ w, ExG fm w) ∧ (∀ w v, fm.R w v) ∧ ¬ Ax2b fm ∧ ¬ MC fm :=
  ⟨closed_fm, fun _ w => ⟨fun h x _ => by cases x; exact h, fun h => h () (RigidFree.god_all () w)⟩,
    RigidFree.ax2a, RigidFree.ax3, RigidFree.ax3v3, RigidFree.ax4, RigidFree.l, ax1Gen_fm,
    RigidFree.exG_all, fun _ _ => trivial, RigidFree.not_ax2b, RigidFree.not_mc⟩

/-! ## K9 over FM carriers -/

open Programme.«20261022-0733-ontological».Run2.GodlessL in
def gfm : Model Cw Unit where
  R := fun _ _ => True
  act := fun _ _ => True
  AS := Based
  AT := fun φ => Based (φ ())
  AH := FMH
  P := fun φ w => φ () (GodlessL.f w)

theorem f_xorw {d : Cw} (hd : Fixes 1 d) (w : Cw) :
    GodlessL.f (xorw w d) = xorw (GodlessL.f w) d := by
  funext i; by_cases hi : i = 0
  · subst hi; simp [GodlessL.f, xorw, hd 0 Nat.zero_lt_one]
  · simp [GodlessL.f, xorw, hi]

/-- Positivity of `gfm` is fixed by `G_1`. -/
theorem pos_gfm : FMH gfm.P := ⟨1, fun d hd ψ w => by
  show ψ () (GodlessL.f w) ↔ ψ () (xorw (GodlessL.f (xorw w d)) d)
  rw [f_xorw hd, xorw_xorw]⟩

theorem closed_gfm : Closed gfm where
  top := GodlessL.closed.top
  bot := GodlessL.closed.bot
  neg := GodlessL.closed.neg
  conj := GodlessL.closed.conj
  lift := GodlessL.closed.lift
  negS := GodlessL.closed.negS
  god := GodlessL.closed.god
  exG := GodlessL.closed.exG
  pos := pos_gfm
  single := single_fmh
  union := fun _ _ => union_fmh
  guard := fun _ _ => guard_fmh
  atMost := fun _ _ hΦ h0 => atMost_based hΦ h0

theorem not_gex_g : ¬ ExG gfm (fun _ => false) := GodlessL.not_gex

theorem not_ax1GenTwo_g : ¬ Ax1GenTwo gfm := fun hT =>
  not_gex_g (TwoClosed.gex closed_gfm GodlessL.ax2a
    (pTop_v2 GodlessL.E_adm closed_gfm GodlessL.ax3 GodlessL.ax4) GodlessL.ax4 hT _)

theorem not_ax1Gen_g : ¬ Ax1Gen gfm := fun h =>
  not_ax1GenTwo_g fun Φ φ hΦ hφ w _ => h Φ φ hΦ hφ w

theorem not_ax1GenOne_g : ¬ Ax1GenOne gfm := fun h1 =>
  not_gex_g (OneHF.gex closed_gfm GodlessL.extra.hact GodlessL.E3_adm GodlessL.ax2a
    GodlessL.ax3v3 GodlessL.ax4c h1 _)

/-- **K9 over the carriers of v4 `ex:separating`.** Every conjunct of `GodlessL.godless_L`, with
`AH` the finitely supported collections. -/
theorem godless_fm :
    Closed gfm ∧ Extra gfm ∧ gfm.AT (E gfm) ∧ gfm.AT (E3 gfm) ∧
      Ax2a gfm ∧ Ax3 gfm ∧ Ax3v3 gfm ∧ Ax4 gfm ∧ Ax4c gfm ∧
      Th4 gfm ∧ L gfm ∧ Ax1GenBoxTwo gfm ∧
      (∀ w v, gfm.R w v) ∧ (∀ y w, gfm.act y w) ∧
      ¬ ExG gfm (fun _ => false) ∧ ¬ Ax2b gfm ∧ ¬ MC gfm ∧
      ¬ Ax1Gen gfm ∧ ¬ Ax1GenTwo gfm ∧ ¬ Ax1GenOne gfm :=
  ⟨closed_gfm, ⟨GodlessL.extra.hid, GodlessL.extra.hact, GodlessL.extra.happ⟩, GodlessL.E_adm, GodlessL.E3_adm, GodlessL.ax2a, GodlessL.ax3,
    GodlessL.ax3v3, GodlessL.ax4, GodlessL.ax4c, GodlessL.th4, GodlessL.l,
    boxTwo_of_L closed_gfm.god GodlessL.ax4 GodlessL.l, fun _ _ => trivial, fun _ _ => trivial,
    not_gex_g, GodlessL.not_ax2b, GodlessL.not_mc, not_ax1Gen_g, not_ax1GenTwo_g,
    not_ax1GenOne_g⟩

end Programme.«20261022-0733-ontological».Run2.FM

#print axioms Programme.«20261022-0733-ontological».Run2.FM.rigidity_independent_fm
#print axioms Programme.«20261022-0733-ontological».Run2.FM.godless_fm
#print axioms Programme.«20261022-0733-ontological».Run2.FM.carriers
#print axioms Programme.«20261022-0733-ontological».Run2.FM.rigidity_exit_fm
