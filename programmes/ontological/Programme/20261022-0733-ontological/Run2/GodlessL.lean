import Programme.«20261022-0733-ontological».Run2.RigidFree

/-! # `G_ex` from `L` (and from `Th4` in variant 3) needs `Ax2b` (th's E8, P76)

The model is th's (`agents/th/lean/Programme/Th/GodlessL.lean`), restated over the definitions of
`TwoClosed`, `DropDagger`, `OneHF`, `BoxIdle`, `UniqueEss` and the carriers of `RigidFree`
(imported, not copied).  Same carriers as `RigidFree.cantor`; positivity at `w` is truth at `f w`,
where `f` sets bit `0` to `true`.  God-likeness is "bit `0` is true", so worlds with bit `0` false
are godless.  Besides th's list we check variant 3's `Ax4c`, `Th4` and the `Extra` closures, so
`GexL.gex_noConj` cannot drop `Ax2b` either; and `Ax1GenTwo`, `Ax1GenOne` fail, as K1/K3/K5 force. -/
namespace Programme.«20261022-0733-ontological».Run2.GodlessL

open Programme.«20261022-0733-ontological».Run2.TwoClosed Programme.«20261022-0733-ontological».Run2.DropDagger Programme.«20261022-0733-ontological».Run2.OneHF
  Programme.«20261022-0733-ontological».Run2.BoxIdle Programme.«20261022-0733-ontological».Run2.UniqueEss Programme.«20261022-0733-ontological».Run2.RigidFree

/-- Set bit `0` to `true`. -/
def f (w : Cw) : Cw := fun i => if i = 0 then true else w i

theorem f_zero (w : Cw) : f w 0 = true := by simp [f]

theorem f_fix {w : Cw} (h : w 0 = true) : f w = w := by
  funext i; by_cases hi : i = 0 <;> simp [f, hi, h]

def godless : Model Cw Unit where
  R := fun _ _ => True
  act := fun _ _ => True
  AS := Based
  AT := fun φ => Based (φ ())
  AH := fun Φ => ∀ ψ₀, Based (ψ₀ ()) → Based (atMostS (fun φ => Based (φ ())) Φ ψ₀)
  P := fun φ w => φ () (f w)

theorem god_iff (x : Unit) (w : Cw) : G godless x w ↔ w 0 = true := by
  constructor
  · intro h; exact h (bit 0 true) (bit_based 0 true) (f_zero w)
  · intro h φ _ hφ; cases x; change φ () (f w) at hφ; rw [f_fix h] at hφ; exact hφ

theorem exG_iff (w : Cw) : ExG godless w ↔ w 0 = true :=
  ⟨fun ⟨x, _, h⟩ => (god_iff x w).1 h, fun h => ⟨(), trivial, (god_iff () w).2 h⟩⟩

theorem bit0_based : Based (fun w : Cw => w 0 = true) := bit_based 0 true

theorem pos_atMost_false (ψ₀ : Unit → Cw → Prop) (u : Cw) :
    ¬ atMostS godless.AT godless.P ψ₀ u := by
  intro h
  have h1 := h top ⟨0, fun _ _ _ => Iff.rfl⟩ trivial
  have h2 := h (bit 0 true) (bit_based 0 true) (f_zero u)
  have : top = bit 0 true := h1.trans h2.symm
  have h3 : bit 0 true () (fun _ => false) := by rw [← this]; trivial
  exact Bool.false_ne_true h3

/-- Essences do not mention positivity, so `cantor`'s no-essence lemmas apply verbatim. -/
theorem E3_all (x : Unit) (w : Cw) : E3 godless x w := by
  intro φ hφ he; cases x; exact absurd he (no_ess3 φ hφ w)

theorem E_all (x : Unit) (w : Cw) : E godless x w := by
  intro φ hφ he; cases x; exact absurd he (no_ess φ hφ w)

theorem closed : Closed godless where
  top := ⟨0, fun _ _ _ => Iff.rfl⟩
  bot := ⟨0, fun _ _ _ => Iff.rfl⟩
  neg := fun φ ⟨n, hn⟩ => ⟨n, fun w v h => not_congr (hn w v h)⟩
  conj := fun φ ψ hφ hψ => based_bin hφ hψ fun _ _ h1 h2 => and_congr h1 h2
  lift := fun p hp => hp
  negS := fun p ⟨n, hn⟩ => ⟨n, fun w v h => not_congr (hn w v h)⟩
  god := based_bin bit0_based bit0_based fun w v h _ =>
    (god_iff () w).trans (h.trans (god_iff () v).symm)
  exG := based_bin bit0_based bit0_based fun w v h _ =>
    (exG_iff w).trans (h.trans (exG_iff v).symm)
  pos := fun ψ₀ _ => based_const _ fun w v =>
    iff_of_false (pos_atMost_false ψ₀ w) (pos_atMost_false ψ₀ v)
  single := fun ψ _ ψ₀ _ => based_const _ fun _ _ => Iff.rfl
  union := fun Φ Ψ hΦ hΨ ψ₀ h0 => based_bin (hΦ ψ₀ h0) (hΨ ψ₀ h0) fun w v h1 h2 => by
    unfold atMostS at *
    constructor
    · intro h ψ hA hm
      rcases hm with hm | hm
      · exact (h1.1 fun ψ' hA' hm' => h ψ' hA' (Or.inl hm')) ψ hA hm
      · exact (h2.1 fun ψ' hA' hm' => h ψ' hA' (Or.inr hm')) ψ hA hm
    · intro h ψ hA hm
      rcases hm with hm | hm
      · exact (h1.2 fun ψ' hA' hm' => h ψ' hA' (Or.inl hm')) ψ hA hm
      · exact (h2.2 fun ψ' hA' hm' => h ψ' hA' (Or.inr hm')) ψ hA hm
  guard := fun p Φ hp hΦ ψ₀ h0 => based_bin hp (hΦ ψ₀ h0) fun w v h1 h2 => by
    unfold atMostS at *
    constructor
    · intro h ψ hA ⟨hpv, hm⟩
      exact (h2.1 fun ψ' hA' hm' => h ψ' hA' ⟨h1.2 hpv, hm'⟩) ψ hA hm
    · intro h ψ hA ⟨hpw, hm⟩
      exact (h2.2 fun ψ' hA' hm' => h ψ' hA' ⟨h1.1 hpw, hm'⟩) ψ hA hm
  atMost := fun Φ ψ₀ hΦ h0 => hΦ ψ₀ h0

theorem extra : Extra godless where
  hid := fun y => based_const _ fun w v => by cases y; exact iff_of_true rfl rfl
  hact := based_const _ fun w v => iff_of_true trivial trivial
  happ := fun φ hφ y => by cases y; exact hφ

theorem ax2a : Ax2a godless := fun φ _ w =>
  ⟨Classical.em (φ () (f w)), fun ⟨h1, h2⟩ => h2 h1⟩

theorem ax4 : Ax4 godless := fun _ _ _ _ w hφ hinc => hinc (f w) trivial () trivial hφ

theorem ax4c : Ax4c godless := fun _ _ _ _ w hφ hinc => (hinc (f w) trivial).2 () trivial hφ

theorem ax3 : Ax3 godless := fun w => E_all () (f w)
theorem ax3v3 : Ax3v3 godless := fun w => E3_all () (f w)
theorem E_adm : godless.AT (E godless) :=
  based_const _ fun w v => iff_of_true (E_all () w) (E_all () v)
theorem E3_adm : godless.AT (E3 godless) :=
  based_const _ fun w v => iff_of_true (E3_all () w) (E3_all () v)

theorem l : L godless := fun w => (god_iff () (f w)).2 (f_zero w)

theorem ax1GenBoxTwo : Ax1GenBoxTwo godless := boxTwo_of_L closed.god ax4 l

theorem th4 : Th4 godless := fun _ => ⟨fun _ => true, trivial, (exG_iff _).2 rfl⟩

/-- The all-false world is godless. -/
theorem not_gex : ¬ ExG godless (fun _ => false) := fun h =>
  Bool.false_ne_true ((exG_iff _).1 h)

theorem not_ax2b : ¬ Ax2b godless := by
  intro h
  have := h (bit 1 true) (bit_based 1 true) (fun _ => true) (by simp [godless, bit, f])
    (fun _ => false) trivial
  simp [godless, bit, f] at this

theorem not_mc : ¬ MC godless := by
  intro h
  have := h (fun v => v 0 = true) bit0_based (fun _ => true) rfl (fun _ => false) trivial
  exact Bool.false_ne_true this

/-- `Ax1GenTwo` fails, as it must: K1's `TwoClosed.gex` would give a God at the godless world. -/
theorem not_ax1GenTwo : ¬ Ax1GenTwo godless := fun hT =>
  not_gex (TwoClosed.gex closed ax2a (pTop_v2 E_adm closed ax3 ax4) ax4 hT _)

theorem not_ax1Gen : ¬ Ax1Gen godless := fun h =>
  not_ax1GenTwo fun Φ φ hΦ hφ w _ => h Φ φ hΦ hφ w

/-- `Ax1GenOne` fails, as it must: K5's `OneHF.gex` would give a God at the godless world. -/
theorem not_ax1GenOne : ¬ Ax1GenOne godless := fun h1 =>
  not_gex (OneHF.gex closed extra.hact E3_adm ax2a ax3v3 ax4c h1 _)

/-- **Main** (th's `godless_L`, extended).  A model of the `Closed` interface with `Extra`, on an
S5 frame, everything actual, `E` and `E3` admitted, satisfying `Ax2a`, `Ax3` (variants 2 and 3'),
`Ax4`, `Ax4c`, `Th4`, `L` and `Ax1GenBoxTwo`, with a godless world; `Ax2b`, admitted MC,
`Ax1Gen`, `Ax1GenTwo` and `Ax1GenOne` fail. -/
theorem godless_L :
    Closed godless ∧ Extra godless ∧ godless.AT (E godless) ∧ godless.AT (E3 godless) ∧
      Ax2a godless ∧ Ax3 godless ∧ Ax3v3 godless ∧ Ax4 godless ∧ Ax4c godless ∧
      Th4 godless ∧ L godless ∧ Ax1GenBoxTwo godless ∧
      (∀ w v, godless.R w v) ∧ (∀ y w, godless.act y w) ∧
      ¬ ExG godless (fun _ => false) ∧ ¬ Ax2b godless ∧ ¬ MC godless ∧
      ¬ Ax1Gen godless ∧ ¬ Ax1GenTwo godless ∧ ¬ Ax1GenOne godless :=
  ⟨closed, extra, E_adm, E3_adm, ax2a, ax3, ax3v3, ax4, ax4c, th4, l, ax1GenBoxTwo,
    fun _ _ => trivial, fun _ _ => trivial, not_gex, not_ax2b, not_mc, not_ax1Gen,
    not_ax1GenTwo, not_ax1GenOne⟩

/-- Hence `Ax2b` cannot be dropped from the `G_ex` halves of K6: from `L` in 3' (`gex_L`), from
`Ax1GenBoxTwo` in 3' (`gex_boxTwo`), and from `Th4` in variant 3 (`gex_noConj`). -/
theorem gex_needs_ax2b :
    ¬ (∀ (M : Model Cw Unit), Closed M → M.AT (E3 M) → Ax2a M → Ax3v3 M → Ax4 M →
        L M → ∀ w, ExG M w) ∧
    ¬ (∀ (M : Model Cw Unit), Closed M → M.AT (E3 M) → Ax2a M → Ax3v3 M → Ax4 M →
        Ax1GenBoxTwo M → ∀ w, ExG M w) ∧
    ¬ (∀ (M : Model Cw Unit), Closed M → M.AT (E3 M) → Ax2a M → Ax3v3 M → Ax4c M →
        Th4 M → ∀ w, ExG M w) :=
  ⟨fun h => not_gex (h _ closed E3_adm ax2a ax3v3 ax4 l _),
   fun h => not_gex (h _ closed E3_adm ax2a ax3v3 ax4 ax1GenBoxTwo _),
   fun h => not_gex (h _ closed E3_adm ax2a ax3v3 ax4c th4 _)⟩

end Programme.«20261022-0733-ontological».Run2.GodlessL

#print axioms Programme.«20261022-0733-ontological».Run2.GodlessL.godless_L
#print axioms Programme.«20261022-0733-ontological».Run2.GodlessL.gex_needs_ax2b
