import Programme.«20261022-0733-ontological».Run2.FittingColumn

/-! # Fitting's extensional positivity over closed (Henkin) carriers

Closed version of `Run2.FittingColumn` (K44/K45, full carriers).  Positivity applies to *admitted*
extensions `AE : (D → Prop) → Prop`; every quantifier over extensions (in `G`, `Ess`, `NE`, the
axioms) ranges over `AE`, and modal collapse ranges over admitted propositions `AS`.

The only closure used (`Clo`) is: `⊤`, `⊥`, negation and the singletons `λz. z = y`; every one is
the denotation of a nominal-free term with primitive equality at type `e`.  No conjunction, no
union, no lift.  The axioms `A3`, `A5` include that `↓G`, `↓NE` are admitted (the term denotes in
the carrier), as in a Henkin model.

Results, any frame, any actuality (`act := True` is the possibilist reading):
* `principal`: `A1, A2, A3` give a God-like `g` at `w` with `P Y w ↔ Y g` on admitted `Y`;
* `mono`: `A1` gives monotheism;  `serial`: `A1, A2` give seriality;
* `gex_of_pred`, `gex_refl`, `gex_sym`: as in the full column;
* `frame_iff`: for every frame `R`: (some closed model of `A1–A5` lives on `R`) ∧ (every closed
  model of `A1–A5` on `R`, any `D`, actuality, carriers, has `∃ᴱ G` at every world) iff `R` is
  serial and every world has an `R`-predecessor (K45 over closed carriers);
* `ofFull`: a full `FModel` is a closed model and each axiom transfers (`ofFull_iff`), so the
  full-carrier countermodels of K44 (s5, kd45, the five drop models) are closed countermodels;
  in particular `s5_no_collapse`: rigid principal positivity with God everywhere and no
  admitted MC. -/

namespace Programme.«20261022-0733-ontological».Run2.FittingClosed

structure CModel (W D : Type) where
  R : W → W → Prop
  act : D → W → Prop
  AS : (W → Prop) → Prop
  AE : (D → Prop) → Prop
  P : (D → Prop) → W → Prop

variable {W D : Type} (M : CModel W D)

def G (x : D) (w : W) : Prop := ∀ Y, M.AE Y → M.P Y w → Y x
def Ess (Y : D → Prop) (x : D) (w : W) : Prop :=
  Y x ∧ ∀ Z, M.AE Z → Z x → ∀ v, M.R w v → ∀ z, M.act z v → Y z → Z z
def NE (x : D) (w : W) : Prop :=
  ∀ Y, M.AE Y → Ess M Y x w → ∀ v, M.R w v → ∃ z, M.act z v ∧ Y z
def down (φ : D → W → Prop) (w : W) : D → Prop := fun x => φ x w

/-- Closure under the nominal-free operations used. -/
structure Clo : Prop where
  top : M.AE fun _ => True
  bot : M.AE fun _ => False
  neg : ∀ Y, M.AE Y → M.AE fun x => ¬ Y x
  single : ∀ y : D, M.AE fun z => z = y

def A1 : Prop := ∀ Y, M.AE Y → ∀ w, M.P (fun x => ¬ Y x) w ↔ ¬ M.P Y w
def A2 : Prop := ∀ Y Z, M.AE Y → M.AE Z → ∀ w, M.P Y w →
  (∀ v, M.R w v → ∀ z, M.act z v → Y z → Z z) → M.P Z w
def A3 : Prop := ∀ w, M.AE (down (G M) w) ∧ M.P (down (G M) w) w
def A4 : Prop := ∀ Y, M.AE Y → ∀ w, M.P Y w → ∀ v, M.R w v → M.P Y v
def A5 : Prop := ∀ w, M.AE (down (NE M) w) ∧ M.P (down (NE M) w) w

def ExG (w : W) : Prop := ∃ x, M.act x w ∧ G M x w
def MC : Prop := ∀ p, M.AS p → ∀ w, p w → ∀ v, M.R w v → p v
def Princ (w : W) : Prop := ∃ g, ∀ Y, M.AE Y → (M.P Y w ↔ Y g)

variable {M}

theorem not_pBot (C : Clo M) (h1 : A1 M) (h2 : A2 M) (w : W) : ¬ M.P (fun _ => False) w :=
  fun hb => (h1 _ C.top w).1 (h2 _ _ C.bot (C.neg _ C.top) w hb fun _ _ _ _ h => h.elim)
    (h2 _ _ C.bot C.top w hb fun _ _ _ _ h => h.elim)

theorem mono (C : Clo M) (h1 : A1 M) {x y : D} {w : W} (hx : G M x w) (hy : G M y w) :
    x = y := by
  by_cases h : M.P (fun z => z = x) w
  · exact (hy _ (C.single x) h).symm
  · exact absurd rfl (hx _ (C.neg _ (C.single x)) ((h1 _ (C.single x) w).2 h))

theorem god_exists (C : Clo M) (h1 : A1 M) (h2 : A2 M) (h3 : A3 M) (w : W) : ∃ g, G M g w :=
  Classical.byContradiction fun hn =>
    not_pBot C h1 h2 w (h2 _ _ (h3 w).1 C.bot w (h3 w).2 fun _ _ z _ hz => hn ⟨z, hz⟩)

theorem principal (C : Clo M) (h1 : A1 M) (h2 : A2 M) (h3 : A3 M) (w : W) :
    ∃ g, G M g w ∧ ∀ Y, M.AE Y → (M.P Y w ↔ Y g) := by
  obtain ⟨g, hg⟩ := god_exists C h1 h2 h3 w
  refine ⟨g, hg, fun Y hY => ⟨hg Y hY, fun hYg => Classical.byContradiction fun hn => ?_⟩⟩
  exact hg _ (C.neg _ hY) ((h1 Y hY w).2 hn) hYg

theorem princ (C : Clo M) (h1 : A1 M) (h2 : A2 M) (h3 : A3 M) (w : W) : Princ M w :=
  let ⟨g, _, h⟩ := principal C h1 h2 h3 w; ⟨g, h⟩

theorem god_rigid (C : Clo M) (h1 : A1 M) (h4 : A4 M) {g : D} {u w : W} (hg : G M g u)
    (huw : M.R u w) : G M g w := fun Y hY hP => Classical.byContradiction fun hn => by
  by_cases hu : M.P Y u
  · exact hn (hg Y hY hu)
  · exact (h1 Y hY w).1 (h4 _ (C.neg _ hY) u ((h1 Y hY u).2 hu) w huw) hP

theorem ess_single (g : D) (w : W) : Ess M (fun x => x = g) g w :=
  ⟨rfl, fun _ _ hz _ _ _ _ he => he ▸ hz⟩

theorem act_succ (C : Clo M) (h5 : A5 M) {g : D} {u w : W} (hg : G M g u) (huw : M.R u w) :
    M.act g w := by
  obtain ⟨z, hz, rfl⟩ := hg _ (h5 u).1 (h5 u).2 _ (C.single g) (ess_single g u) w huw
  exact hz

theorem gex_of_pred (C : Clo M) (h1 : A1 M) (h2 : A2 M) (h3 : A3 M) (h4 : A4 M) (h5 : A5 M)
    {u w : W} (huw : M.R u w) : ExG M w :=
  let ⟨g, hg⟩ := god_exists C h1 h2 h3 u
  ⟨g, act_succ C h5 hg huw, god_rigid C h1 h4 hg huw⟩

theorem gex_refl (C : Clo M) (h1 : A1 M) (h2 : A2 M) (h3 : A3 M) (h5 : A5 M) {w : W}
    (hw : M.R w w) : ExG M w :=
  let ⟨g, hg⟩ := god_exists C h1 h2 h3 w
  ⟨g, act_succ C h5 hg hw, hg⟩

theorem serial (C : Clo M) (h1 : A1 M) (h2 : A2 M) (w : W) : ∃ v, M.R w v := by
  refine Classical.byContradiction fun hn => ?_
  have vac : ∀ Y : D → Prop, ∀ v, M.R w v → ∀ z, M.act z v → Y z → False :=
    fun _ v hv _ _ _ => hn ⟨v, hv⟩
  by_cases h : M.P (fun _ => True) w
  · exact not_pBot C h1 h2 w (h2 _ _ C.top C.bot w h (vac _))
  · exact not_pBot C h1 h2 w (h2 _ _ (C.neg _ C.top) C.bot w ((h1 _ C.top w).2 h) (vac _))

theorem gex_sym (C : Clo M) (h1 : A1 M) (h2 : A2 M) (h3 : A3 M) (h4 : A4 M) (h5 : A5 M)
    (hsym : ∀ w v, M.R w v → M.R v w) (w : W) : ExG M w :=
  let ⟨v, hv⟩ := serial C h1 h2 w
  gex_of_pred C h1 h2 h3 h4 h5 (hsym w v hv)

/-! ## Full models are closed models -/

open Programme.«20261022-0733-ontological».Run2.FittingColumn in
/-- A full `FModel` read as a closed model with every extension and proposition admitted. -/
def ofFull (m : FModel W D) : CModel W D where
  R := m.R
  act := m.act
  AS := fun _ => True
  AE := fun _ => True
  P := m.P

open Programme.«20261022-0733-ontological».Run2.FittingColumn in
theorem clo_ofFull (m : FModel W D) : Clo (ofFull m) :=
  ⟨trivial, trivial, fun _ _ => trivial, fun _ => trivial⟩

open Programme.«20261022-0733-ontological».Run2.FittingColumn in
theorem G_ofFull (m : FModel W D) (x : D) (w : W) :
    G (ofFull m) x w ↔ FittingColumn.G m x w :=
  ⟨fun h Y hY => h Y trivial hY, fun h Y _ hY => h Y hY⟩

open Programme.«20261022-0733-ontological».Run2.FittingColumn in
theorem NE_ofFull (m : FModel W D) (x : D) (w : W) :
    NE (ofFull m) x w ↔ FittingColumn.NE m x w :=
  ⟨fun h Y hE => h Y trivial ⟨hE.1, fun Z _ => hE.2 Z⟩,
   fun h Y _ hE => h Y ⟨hE.1, fun Z => hE.2 Z trivial⟩⟩

open Programme.«20261022-0733-ontological».Run2.FittingColumn in
/-- **Each axiom, existence, principality and MC transfer from full to closed reading.** -/
theorem ofFull_iff (m : FModel W D) :
    (A1 (ofFull m) ↔ FittingColumn.A1 m) ∧ (A2 (ofFull m) ↔ FittingColumn.A2 m) ∧
    (A3 (ofFull m) ↔ FittingColumn.A3 m) ∧ (A4 (ofFull m) ↔ FittingColumn.A4 m) ∧
    (A5 (ofFull m) ↔ FittingColumn.A5 m) ∧ (∀ w, ExG (ofFull m) w ↔ FittingColumn.ExG m w) ∧
    (∀ w, Princ (ofFull m) w ↔ FittingColumn.Princ m w) ∧ (MC (ofFull m) ↔ FittingColumn.MC m) := by
  have hG : G (ofFull m) = FittingColumn.G m :=
    funext fun x => funext fun w => propext (G_ofFull m x w)
  have hN : NE (ofFull m) = FittingColumn.NE m :=
    funext fun x => funext fun w => propext (NE_ofFull m x w)
  refine ⟨⟨fun h Y w => h Y trivial w, fun h Y _ w => h Y w⟩,
    ⟨fun h Y Z w => h Y Z trivial trivial w, fun h Y Z _ _ w => h Y Z w⟩, ?_,
    ⟨fun h Y w => h Y trivial w, fun h Y _ w => h Y w⟩, ?_, fun w => ?_,
    fun w => ⟨fun ⟨g, h⟩ => ⟨g, fun Y => h Y trivial⟩, fun ⟨g, h⟩ => ⟨g, fun Y _ => h Y⟩⟩,
    ⟨fun h p w => h p trivial w, fun h p _ w => h p w⟩⟩
  · show (∀ w, True ∧ m.P (down (G (ofFull m)) w) w) ↔ _
    rw [hG]; exact ⟨fun h w => (h w).2, fun h w => ⟨trivial, h w⟩⟩
  · show (∀ w, True ∧ m.P (down (NE (ofFull m)) w) w) ↔ _
    rw [hN]; exact ⟨fun h w => (h w).2, fun h w => ⟨trivial, h w⟩⟩
  · show (∃ x, m.act x w ∧ G (ofFull m) x w) ↔ _
    rw [hG]; rfl

open Programme.«20261022-0733-ontological».Run2.FittingColumn in
/-- **Closed S5 model**: `A1–A5`, God and principality everywhere, rigid `P`, admitted MC
fails. -/
theorem s5_no_collapse : Clo (ofFull s5) ∧ A1 (ofFull s5) ∧ A2 (ofFull s5) ∧ A3 (ofFull s5) ∧
    A4 (ofFull s5) ∧ A5 (ofFull s5) ∧ (∀ w, ExG (ofFull s5) w) ∧
    (∀ w, Princ (ofFull s5) w) ∧ ¬ MC (ofFull s5) := by
  obtain ⟨i1, i2, i3, i4, i5, ig, ip, im⟩ := ofFull_iff s5
  obtain ⟨a1, a2, a3, a4, a5, ag, ap, am⟩ := FittingColumn.s5_no_collapse
  exact ⟨clo_ofFull _, i1.2 a1, i2.2 a2, i3.2 a3, i4.2 a4, i5.2 a5, fun w => (ig w).2 (ag w),
    fun w => (ip w).2 (ap w), fun h => am (im.1 h)⟩

/-! ## The frame row over closed carriers -/

/-- One entity, actual exactly at worlds with a predecessor, `P Y w ↔ Y ()`, full carriers. -/
def predModel (R : W → W → Prop) : CModel W Unit where
  R := R
  act := fun _ w => ∃ u, R u w
  AS := fun _ => True
  AE := fun _ => True
  P := fun Y _ => Y ()

theorem predModel_axioms (R : W → W → Prop) (hser : ∀ w, ∃ v, R w v) :
    Clo (predModel R) ∧ A1 (predModel R) ∧ A2 (predModel R) ∧ A3 (predModel R) ∧
      A4 (predModel R) ∧ A5 (predModel R) := by
  refine ⟨⟨trivial, trivial, fun _ _ => trivial, fun _ => trivial⟩, fun _ _ _ => Iff.rfl,
    fun Y Z _ _ w h hi => ?_, fun w => ⟨trivial, fun _ _ h => h⟩, fun _ _ _ h _ _ => h,
    fun w => ⟨trivial, fun _ _ hE v hv => ⟨(), ⟨w, hv⟩, hE.1⟩⟩⟩
  · obtain ⟨v, hv⟩ := hser w
    exact hi v hv () ⟨w, hv⟩ h

theorem predModel_exG (R : W → W → Prop) (w : W) : ExG (predModel R) w ↔ ∃ u, R u w :=
  ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨(), h, fun _ _ hY => hY⟩⟩

/-- **Fitting frame row, closed carriers.** -/
theorem frame_iff (R : W → W → Prop) :
    ((∃ (D : Type) (M : CModel W D), M.R = R ∧ Clo M ∧ A1 M ∧ A2 M ∧ A3 M ∧ A4 M ∧ A5 M) ∧
      ∀ (D : Type) (M : CModel W D), M.R = R → Clo M → A1 M → A2 M → A3 M → A4 M → A5 M →
        ∀ w, ExG M w) ↔
    (∀ w, ∃ v, R w v) ∧ ∀ w, ∃ u, R u w := by
  constructor
  · rintro ⟨⟨D, M, rfl, C, h1, h2, -, -, -⟩, hall⟩
    have hser := serial C h1 h2
    refine ⟨hser, fun w => ?_⟩
    obtain ⟨c, a1, a2, a3, a4, a5⟩ := predModel_axioms M.R hser
    exact (predModel_exG M.R w).1 (hall Unit (predModel M.R) rfl c a1 a2 a3 a4 a5 w)
  · rintro ⟨hser, hpred⟩
    obtain ⟨c, a1, a2, a3, a4, a5⟩ := predModel_axioms R hser
    refine ⟨⟨Unit, predModel R, rfl, c, a1, a2, a3, a4, a5⟩, ?_⟩
    rintro D M rfl C h1 h2 h3 h4 h5 w
    obtain ⟨u, hu⟩ := hpred w
    exact gex_of_pred C h1 h2 h3 h4 h5 hu

end Programme.«20261022-0733-ontological».Run2.FittingClosed

#print axioms Programme.«20261022-0733-ontological».Run2.FittingClosed.principal
#print axioms Programme.«20261022-0733-ontological».Run2.FittingClosed.mono
#print axioms Programme.«20261022-0733-ontological».Run2.FittingClosed.gex_of_pred
#print axioms Programme.«20261022-0733-ontological».Run2.FittingClosed.gex_refl
#print axioms Programme.«20261022-0733-ontological».Run2.FittingClosed.gex_sym
#print axioms Programme.«20261022-0733-ontological».Run2.FittingClosed.ofFull_iff
#print axioms Programme.«20261022-0733-ontological».Run2.FittingClosed.s5_no_collapse
#print axioms Programme.«20261022-0733-ontological».Run2.FittingClosed.frame_iff
