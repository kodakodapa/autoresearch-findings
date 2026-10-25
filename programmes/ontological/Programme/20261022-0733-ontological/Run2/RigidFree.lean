import Programme.«20261022-0733-ontological».Run2.UniqueEss

/-! # Ax2b is independent: a closed model without rigidity (th's E7, P65)

The model and its proofs are th's (`agents/th/lean/Programme/Th/RigidityFree.lean`), restated over
the definitions of `TwoClosed`, `DropDagger`, `OneHF`, `BoxIdle` and `UniqueEss` themselves (imported,
not copied).  Worlds are Boolean streams, one entity, universal accessibility, everything actual;
admitted propositions and properties are the finitely based ones; positivity is truth at the
current world.  No admitted property is an essence, so `E` and `E3` hold everywhere.

Every hypothesis of the MC halves of K1 (variants 2 and 3'), K3 (variant 3, Ax1GenTwo, Th4), K5
(Ax1GenOne, actuality admitted), K6 (`L`, `Ax1GenBoxTwo`, variant 3 with Th4) and the extra
closures of K7 holds here, except `Ax2b`; admitted modal collapse fails.  So `Ax2b` cannot be
dropped from any of those MC results. -/
namespace Programme.«20261022-0733-ontological».Run2.RigidFree

open Programme.«20261022-0733-ontological».Run2.TwoClosed Programme.«20261022-0733-ontological».Run2.DropDagger Programme.«20261022-0733-ontological».Run2.OneHF
  Programme.«20261022-0733-ontological».Run2.BoxIdle Programme.«20261022-0733-ontological».Run2.UniqueEss

/-! ## The model -/

abbrev Cw := Nat → Bool

/-- `p` depends only on the first `n` bits. -/
def Based (p : Cw → Prop) : Prop :=
  ∃ n, ∀ w v : Cw, (∀ i, i < n → w i = v i) → (p w ↔ p v)

theorem based_const (p : Cw → Prop) (h : ∀ w v, p w ↔ p v) : Based p := ⟨0, fun w v _ => h w v⟩

theorem based_mono {p : Cw → Prop} {n m : Nat} (hnm : n ≤ m)
    (h : ∀ w v : Cw, (∀ i, i < n → w i = v i) → (p w ↔ p v)) :
    ∀ w v : Cw, (∀ i, i < m → w i = v i) → (p w ↔ p v) :=
  fun w v hwv => h w v fun i hi => hwv i (Nat.lt_of_lt_of_le hi hnm)

theorem based_bin {p q r : Cw → Prop} (hp : Based p) (hq : Based q)
    (hr : ∀ w v, (p w ↔ p v) → (q w ↔ q v) → (r w ↔ r v)) : Based r := by
  obtain ⟨n, hn⟩ := hp; obtain ⟨m, hm⟩ := hq
  exact ⟨max n m, fun w v hwv =>
    hr w v (based_mono (Nat.le_max_left n m) hn w v hwv)
      (based_mono (Nat.le_max_right n m) hm w v hwv)⟩

def atMostS (AT : (Unit → Cw → Prop) → Prop) (Φ : (Unit → Cw → Prop) → Cw → Prop)
    (ψ₀ : Unit → Cw → Prop) (u : Cw) : Prop := ∀ ψ, AT ψ → Φ ψ u → ψ = ψ₀

def cantor : Model Cw Unit where
  R := fun _ _ => True
  act := fun _ _ => True
  AS := Based
  AT := fun φ => Based (φ ())
  AH := fun Φ => ∀ ψ₀, Based (ψ₀ ()) → Based (atMostS (fun φ => Based (φ ())) Φ ψ₀)
  P := fun φ w => φ () w

/-- Flip bit `n`. -/
def flip (w : Cw) (n : Nat) : Cw := fun i => if i = n then !w i else w i

theorem flip_agree (w : Cw) (n i : Nat) (hi : i < n) : w i = flip w n i := by
  simp [flip, Nat.ne_of_lt hi]

theorem flip_at (w : Cw) (n : Nat) : flip w n n = !w n := by simp [flip]

theorem god_all (x : Unit) (w : Cw) : G cantor x w := by
  intro φ _ h; cases x; exact h

theorem exG_all (w : Cw) : ExG cantor w := ⟨(), trivial, god_all () w⟩

/-- The basic clopen "bit `n` equals `b`". -/
def bit (n : Nat) (b : Bool) : Unit → Cw → Prop := fun _ v => v n = b

theorem bit_based (n : Nat) (b : Bool) : cantor.AT (bit n b) :=
  ⟨n + 1, fun w v h => by
    show w n = b ↔ v n = b
    rw [h n (Nat.lt_succ_self n)]⟩

/-- At every world, positivity has two different admitted members. -/
theorem pos_atMost_false (ψ₀ : Unit → Cw → Prop) (u : Cw) : ¬ atMostS cantor.AT cantor.P ψ₀ u := by
  intro h
  have h1 := h top ⟨0, fun _ _ _ => Iff.rfl⟩ trivial
  have h2 := h (bit 0 (u 0)) (bit_based 0 (u 0)) rfl
  have : top = bit 0 (u 0) := h1.trans h2.symm
  have h3 : bit 0 (u 0) () (flip u 0) := by rw [← this]; trivial
  have h4 : flip u 0 0 = u 0 := h3
  rw [flip_at] at h4; cases hu : u 0 <;> simp [hu] at h4

/-- No admitted property is an essence (variant 3'): the support bit can always be flipped. -/
theorem no_ess3 (φ : Unit → Cw → Prop) (hφ : cantor.AT φ) (w : Cw) : ¬ Ess3 cantor φ () w := by
  intro he
  obtain ⟨n, hn⟩ := hφ
  have ne : φ ≠ bot := (he top ⟨0, fun _ _ _ => Iff.rfl⟩ trivial w trivial).1
  have : ∃ v0, φ () v0 := Classical.byContradiction fun hno =>
    ne (funext fun x => funext fun v => by cases x; exact propext ⟨fun h => hno ⟨v, h⟩, False.elim⟩)
  obtain ⟨v0, hv0⟩ := this
  have hv1 : φ () (flip v0 n) := (hn v0 (flip v0 n) (flip_agree v0 n)).1 hv0
  have hb := fun v (hv : φ () v) =>
    (he (bit n (w n)) (bit_based n (w n)) rfl v trivial).2 () trivial hv
  have e0 : v0 n = w n := hb v0 hv0
  have e1 : flip v0 n n = w n := hb _ hv1
  rw [flip_at, e0] at e1; cases hw : w n <;> simp [hw] at e1

/-- No admitted property is an essence (variant 2, with the conjunct `φ x`). -/
theorem no_ess (φ : Unit → Cw → Prop) (hφ : cantor.AT φ) (w : Cw) : ¬ Ess cantor φ () w := by
  intro ⟨hw, he⟩
  obtain ⟨n, hn⟩ := hφ
  have hv1 : φ () (flip w n) := (hn w (flip w n) (flip_agree w n)).1 hw
  have e1 : flip w n n = w n := he (bit n (w n)) (bit_based n (w n)) rfl _ trivial () trivial hv1
  rw [flip_at] at e1; cases hw' : w n <;> simp [hw'] at e1

theorem E3_all (x : Unit) (w : Cw) : E3 cantor x w := by
  intro φ hφ he; cases x; exact absurd he (no_ess3 φ hφ w)

theorem E_all (x : Unit) (w : Cw) : E cantor x w := by
  intro φ hφ he; cases x; exact absurd he (no_ess φ hφ w)

theorem closed : Closed cantor where
  top := ⟨0, fun _ _ _ => Iff.rfl⟩
  bot := ⟨0, fun _ _ _ => Iff.rfl⟩
  neg := fun φ ⟨n, hn⟩ => ⟨n, fun w v h => not_congr (hn w v h)⟩
  conj := fun φ ψ hφ hψ => based_bin hφ hψ fun _ _ h1 h2 => and_congr h1 h2
  lift := fun p hp => hp
  negS := fun p ⟨n, hn⟩ => ⟨n, fun w v h => not_congr (hn w v h)⟩
  god := based_const _ fun w v => iff_of_true (god_all () w) (god_all () v)
  exG := based_const _ fun w v => iff_of_true (exG_all w) (exG_all v)
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

theorem ax2a : Ax2a cantor := fun φ _ w =>
  ⟨Classical.em (φ () w), fun ⟨h1, h2⟩ => h2 h1⟩

theorem ax4 : Ax4 cantor := fun _ _ _ _ w hφ hinc => hinc w trivial () trivial hφ

theorem ax4c : Ax4c cantor := fun _ _ _ _ w hφ hinc => (hinc w trivial).2 () trivial hφ

theorem ax3 : Ax3 cantor := fun w => E_all () w
theorem ax3v3 : Ax3v3 cantor := fun w => E3_all () w
theorem E_adm : cantor.AT (E cantor) := based_const _ fun w v => iff_of_true (E_all () w) (E_all () v)
theorem E3_adm : cantor.AT (E3 cantor) :=
  based_const _ fun w v => iff_of_true (E3_all () w) (E3_all () v)

theorem l : L cantor := fun w => god_all () w

theorem ax1Gen : Ax1Gen cantor := fun _ _ _ _ w hpos hc =>
  (hc w trivial () trivial).2 fun ψ hA hm => hpos ψ hA hm

theorem ax1GenTwo : Ax1GenTwo cantor := fun Φ φ hΦ hφ w _ => ax1Gen Φ φ hΦ hφ w

theorem ax1GenOne : Ax1GenOne cantor := fun Φ φ hΦ hφ w _ => ax1Gen Φ φ hΦ hφ w

theorem ax1GenBoxTwo : Ax1GenBoxTwo cantor := boxTwo_of_L closed.god ax4 l

theorem th4 : Th4 cantor := fun w => ⟨w, trivial, exG_all w⟩

theorem extra : Extra cantor where
  hid := fun y => based_const _ fun w v => by cases y; exact iff_of_true rfl rfl
  hact := based_const _ fun w v => iff_of_true trivial trivial
  happ := fun φ hφ y => by cases y; exact hφ

theorem not_ax2b : ¬ Ax2b cantor := by
  intro h
  have := h (bit 0 true) (bit_based 0 true) (fun _ => true) rfl (fun _ => false) trivial
  exact Bool.false_ne_true this

theorem not_mc : ¬ MC cantor := by
  intro h
  have := h (fun v => v 0 = true) (bit_based 0 true) (fun _ => true) rfl (fun _ => false) trivial
  exact Bool.false_ne_true this

/-- **Main** (th's `rigidity_independent`, over our own definitions).  A closed model on an S5
frame with `Extra`, `E`, `E3` admitted, satisfying `Ax2a`, `Ax3` (variants 2 and 3'), `Ax4`,
variant 3's `Ax4c`, `Th4`, `L`, unrestricted `Ax1Gen`, `Ax1GenTwo`, `Ax1GenOne`, `Ax1GenBoxTwo`,
with God existing at every world, in which `Ax2b` and admitted modal collapse fail. -/
theorem rigidity_independent :
    Closed cantor ∧ Extra cantor ∧ cantor.AT (E cantor) ∧ cantor.AT (E3 cantor) ∧
      Ax2a cantor ∧ Ax3 cantor ∧ Ax3v3 cantor ∧ Ax4 cantor ∧ Ax4c cantor ∧ Th4 cantor ∧
      L cantor ∧ Ax1Gen cantor ∧ Ax1GenTwo cantor ∧ Ax1GenOne cantor ∧ Ax1GenBoxTwo cantor ∧
      (∀ w, ExG cantor w) ∧ (∀ w v, cantor.R w v) ∧ (∀ y w, cantor.act y w) ∧
      ¬ Ax2b cantor ∧ ¬ MC cantor :=
  ⟨closed, extra, E_adm, E3_adm, ax2a, ax3, ax3v3, ax4, ax4c, th4, l, ax1Gen, ax1GenTwo,
    ax1GenOne, ax1GenBoxTwo, exG_all, fun _ _ => trivial, fun _ _ => trivial, not_ax2b, not_mc⟩

/-- Hence `Ax2b` cannot be dropped from the MC halves of K1 (variants 2 and 3'), K3, K5, K6. -/
theorem ax2b_needed :
    ¬ (∀ (M : Model Cw Unit), Closed M → M.AT (E M) → Ax2a M → Ax3 M → Ax4 M →
        Ax1GenTwo M → MC M) ∧
    ¬ (∀ (M : Model Cw Unit), Closed M → M.AT (E3 M) → Ax2a M → Ax3v3 M → Ax4 M →
        L M → MC M) ∧
    ¬ (∀ (M : Model Cw Unit), Closed M → M.AT (E3 M) → Ax2a M → Ax3v3 M → Ax4c M →
        Th4 M → Ax1GenTwo M → MC M) ∧
    ¬ (∀ (M : Model Cw Unit), Closed M → M.AT (fun z u => M.act z u) → M.AT (E3 M) → Ax2a M →
        Ax3v3 M → Ax4c M → Ax1GenOne M → MC M) :=
  ⟨fun h => not_mc (h _ closed E_adm ax2a ax3 ax4 ax1GenTwo),
   fun h => not_mc (h _ closed E3_adm ax2a ax3v3 ax4 l),
   fun h => not_mc (h _ closed E3_adm ax2a ax3v3 ax4c th4 ax1GenTwo),
   fun h => not_mc (h _ closed extra.hact E3_adm ax2a ax3v3 ax4c ax1GenOne)⟩

end Programme.«20261022-0733-ontological».Run2.RigidFree

#print axioms Programme.«20261022-0733-ontological».Run2.RigidFree.rigidity_independent
#print axioms Programme.«20261022-0733-ontological».Run2.RigidFree.ax2b_needed
