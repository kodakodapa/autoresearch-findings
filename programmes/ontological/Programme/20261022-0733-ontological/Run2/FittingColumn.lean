/-! # Fitting's extensional positivity: the frame row and minimality

Fitting's reconstruction (Fitting 2002, *Types, Tableaus, and Gödel's God*; AFP
`Types_Tableaus_and_Goedels_God`): positivity applies to *extensions* `D → Prop` (rigid sets of
entities), not to intensions `D → W → Prop`. Full carriers (every extension), actualist `∀ᴱ`.

* `G x w := ∀ Y, P Y w → Y x`
* `Ess Y x w := Y x ∧ ∀ Z, Z x → □ ∀ᴱ z, Y z → Z z`,  `NE x w := ∀ Y, Ess Y x w → □ ∃ᴱ Y`
* `A1 : P (¬Y) ↔ ¬ P Y`, `A2 : P Y ∧ □ ∀ᴱ (Y → Z) → P Z`, `A3 : P (↓G)`, `A4 : P Y → □ P Y`,
  `A5 : P (↓NE)`, where `↓φ` is the extension of `φ` at the current world.

Results (full carriers, any frame, any actuality):
* `principal`: `A1, A2, A3` make positivity at `w` principal at the unique God-like entity.
* `gex_of_pred`: `A1–A5`: every world with an `R`-predecessor has an actual God-like entity.
* `gex_refl`: on a reflexive world `A1, A2, A3, A5` suffice (no `A4`).
* `gex_sym`: symmetric frames: `∃ᴱ G` everywhere (seriality follows from `A1, A2`).
* `mono`: `A1` alone gives monotheism.
* `s5_no_collapse`: an S5 model satisfies `A1–A5`, God and principality everywhere, rigid `P`,
  but not MC: principal + rigid extensional positivity does not collapse.
* `kd45_gap`: a KD45 model (`R w v ↔ v = 0`) satisfies `A1–A5`, refutes MC and `∃ᴱ G` at world 1.
* Minimality: `noA1`, `noA2`, `noA3` (one reflexive world), `noA5` (S5) satisfy the other four
  axioms and lack `∃ᴱ G` somewhere; `noA4` (symmetric, irreflexive) satisfies
  `A1, A2, A3, A5` and has `∃ᴱ G` nowhere. -/

namespace Programme.«20261022-0733-ontological».Run2.FittingColumn

structure FModel (W D : Type) where
  R : W → W → Prop
  act : D → W → Prop
  P : (D → Prop) → W → Prop

variable {W D : Type} (M : FModel W D)

def G (x : D) (w : W) : Prop := ∀ Y, M.P Y w → Y x
def Ess (Y : D → Prop) (x : D) (w : W) : Prop :=
  Y x ∧ ∀ Z : D → Prop, Z x → ∀ v, M.R w v → ∀ z, M.act z v → Y z → Z z
def NE (x : D) (w : W) : Prop := ∀ Y, Ess M Y x w → ∀ v, M.R w v → ∃ z, M.act z v ∧ Y z
def down (φ : D → W → Prop) (w : W) : D → Prop := fun x => φ x w

def A1 : Prop := ∀ Y w, M.P (fun x => ¬ Y x) w ↔ ¬ M.P Y w
def A2 : Prop := ∀ Y Z w, M.P Y w → (∀ v, M.R w v → ∀ z, M.act z v → Y z → Z z) → M.P Z w
def A3 : Prop := ∀ w, M.P (down (G M) w) w
def A4 : Prop := ∀ Y w, M.P Y w → ∀ v, M.R w v → M.P Y v
def A5 : Prop := ∀ w, M.P (down (NE M) w) w

def ExG (w : W) : Prop := ∃ x, M.act x w ∧ G M x w
def MC : Prop := ∀ p : W → Prop, ∀ w, p w → ∀ v, M.R w v → p v
def Princ (w : W) : Prop := ∃ g, ∀ Y, M.P Y w ↔ Y g

variable {M}

theorem not_pBot (h1 : A1 M) (h2 : A2 M) (w : W) : ¬ M.P (fun _ => False) w := fun hb =>
  (h1 (fun _ => True) w).1 (h2 _ _ w hb fun _ _ _ _ h => h.elim)
    (h2 _ _ w hb fun _ _ _ _ h => h.elim)

theorem mono (h1 : A1 M) {x y : D} {w : W} (hx : G M x w) (hy : G M y w) : x = y := by
  by_cases h : M.P (fun z => z = x) w
  · exact (hy _ h).symm
  · exact absurd rfl (hx _ ((h1 _ w).2 h))

theorem god_exists (h1 : A1 M) (h2 : A2 M) (h3 : A3 M) (w : W) : ∃ g, G M g w :=
  Classical.byContradiction fun hn =>
    not_pBot h1 h2 w (h2 _ _ w (h3 w) fun _ _ z _ hz => hn ⟨z, hz⟩)

theorem principal (h1 : A1 M) (h2 : A2 M) (h3 : A3 M) (w : W) :
    ∃ g, G M g w ∧ ∀ Y, M.P Y w ↔ Y g := by
  obtain ⟨g, hg⟩ := god_exists h1 h2 h3 w
  refine ⟨g, hg, fun Y => ⟨hg Y, fun hY => Classical.byContradiction fun hn => ?_⟩⟩
  exact hg _ ((h1 Y w).2 hn) hY

theorem princ (h1 : A1 M) (h2 : A2 M) (h3 : A3 M) (w : W) : Princ M w :=
  let ⟨g, _, h⟩ := principal h1 h2 h3 w; ⟨g, h⟩

/-- Rigidity transports a God-like entity along `R`. -/
theorem god_rigid (h1 : A1 M) (h4 : A4 M) {g : D} {u w : W} (hg : G M g u) (huw : M.R u w) :
    G M g w := fun Y hY => Classical.byContradiction fun hn => by
  by_cases hu : M.P Y u
  · exact hn (hg Y hu)
  · exact (h1 Y w).1 (h4 _ u ((h1 Y u).2 hu) w huw) hY

theorem ess_single (g : D) (w : W) : Ess M (fun x => x = g) g w :=
  ⟨rfl, fun _ hz _ _ _ _ he => he ▸ hz⟩

/-- `A5` at `u`: a God-like entity at `u` is actual at every successor of `u`. -/
theorem act_succ (h5 : A5 M) {g : D} {u w : W} (hg : G M g u) (huw : M.R u w) : M.act g w := by
  obtain ⟨z, hz, rfl⟩ := hg _ (h5 u) _ (ess_single g u) w huw
  exact hz

theorem gex_of_pred (h1 : A1 M) (h2 : A2 M) (h3 : A3 M) (h4 : A4 M) (h5 : A5 M)
    {u w : W} (huw : M.R u w) : ExG M w :=
  let ⟨g, hg⟩ := god_exists h1 h2 h3 u
  ⟨g, act_succ h5 hg huw, god_rigid h1 h4 hg huw⟩

theorem gex_refl (h1 : A1 M) (h2 : A2 M) (h3 : A3 M) (h5 : A5 M) {w : W} (hw : M.R w w) :
    ExG M w :=
  let ⟨g, hg⟩ := god_exists h1 h2 h3 w
  ⟨g, act_succ h5 hg hw, hg⟩

theorem serial (h1 : A1 M) (h2 : A2 M) (w : W) : ∃ v, M.R w v := by
  refine Classical.byContradiction fun hn => ?_
  have vac : ∀ Y : D → Prop, ∀ v, M.R w v → ∀ z, M.act z v → Y z → False := fun _ v hv _ _ _ => hn ⟨v, hv⟩
  by_cases h : M.P (fun _ => True) w
  · exact not_pBot h1 h2 w (h2 _ _ w h (vac _))
  · exact not_pBot h1 h2 w (h2 _ _ w ((h1 _ w).2 h) (vac _))

theorem gex_sym (h1 : A1 M) (h2 : A2 M) (h3 : A3 M) (h4 : A4 M) (h5 : A5 M)
    (hsym : ∀ w v, M.R w v → M.R v w) (w : W) : ExG M w :=
  let ⟨v, hv⟩ := serial h1 h2 w
  gex_of_pred h1 h2 h3 h4 h5 (hsym w v hv)

/-! ## Models -/

/-- S5, two worlds, one always-actual entity, `P Y := Y ()`. -/
def s5 : FModel Bool Unit where
  R := fun _ _ => True
  act := fun _ _ => True
  P := fun Y _ => Y ()

theorem s5_no_collapse :
    A1 s5 ∧ A2 s5 ∧ A3 s5 ∧ A4 s5 ∧ A5 s5 ∧ (∀ w, ExG s5 w) ∧ (∀ w, Princ s5 w) ∧ ¬ MC s5 :=
  ⟨fun _ _ => Iff.rfl, fun _ _ w h hi => hi w trivial () trivial h, fun _ _ h => h,
   fun _ _ h _ _ => h, fun _ _ hE _ _ => ⟨(), trivial, hE.1⟩,
   fun _ => ⟨(), trivial, fun _ h => h⟩, fun _ => ⟨(), fun _ => Iff.rfl⟩,
   fun h => Bool.noConfusion (h (fun w => w = true) true rfl false trivial)⟩

/-- KD45 (`R w v ↔ v = false`), the entity actual only at `false`. -/
def kd45 : FModel Bool Unit where
  R := fun _ v => v = false
  act := fun _ v => v = false
  P := fun Y _ => Y ()

theorem kd45_gap :
    (∀ w v u, kd45.R w v → kd45.R v u → kd45.R w u) ∧
    (∀ w v u, kd45.R w v → kd45.R w u → kd45.R v u) ∧ (∀ w, ∃ v, kd45.R w v) ∧
    A1 kd45 ∧ A2 kd45 ∧ A3 kd45 ∧ A4 kd45 ∧ A5 kd45 ∧ (∀ w, Princ kd45 w) ∧
    ExG kd45 false ∧ ¬ ExG kd45 true ∧ ¬ MC kd45 :=
  ⟨fun _ _ _ _ h => h, fun _ _ _ _ h => h, fun _ => ⟨false, rfl⟩,
   fun _ _ => Iff.rfl, fun _ _ _ h hi => hi false rfl () rfl h, fun _ _ h => h,
   fun _ _ h _ _ => h, fun _ _ hE _ hv => ⟨(), hv, hE.1⟩, fun _ => ⟨(), fun _ => Iff.rfl⟩,
   ⟨(), rfl, fun _ h => h⟩, fun ⟨_, hx, _⟩ => Bool.noConfusion hx,
   fun h => Bool.noConfusion (h (fun w => w = true) true rfl false rfl)⟩

/-- Drop `A1`: everything positive. -/
def mNoA1 : FModel Unit Unit where
  R := fun _ _ => True
  act := fun _ _ => True
  P := fun _ _ => True

theorem noA1 : ¬ A1 mNoA1 ∧ A2 mNoA1 ∧ A3 mNoA1 ∧ A4 mNoA1 ∧ A5 mNoA1 ∧ ¬ ExG mNoA1 () :=
  ⟨fun h => (h (fun _ => True) ()).1 trivial trivial, fun _ _ _ _ _ => trivial,
   fun _ => trivial, fun _ _ _ _ _ => trivial, fun _ => trivial,
   fun ⟨_, _, hg⟩ => hg (fun _ => False) trivial⟩

/-- Drop `A2`: only the empty extension positive, nothing actual. -/
def mNoA2 : FModel Unit Unit where
  R := fun _ _ => True
  act := fun _ _ => False
  P := fun Y _ => ¬ Y ()

theorem noA2 : A1 mNoA2 ∧ ¬ A2 mNoA2 ∧ A3 mNoA2 ∧ A4 mNoA2 ∧ A5 mNoA2 ∧ ¬ ExG mNoA2 () :=
  ⟨fun _ _ => Iff.rfl,
   fun h => h (fun _ => False) (fun _ => True) () id (fun _ _ _ _ h => h.elim) trivial,
   fun _ h => h (fun _ => False) id, fun _ _ h _ _ => h,
   fun _ h => h (fun _ => True) ⟨trivial, fun _ _ _ _ _ ha => ha.elim⟩ () trivial |>.elim
     fun _ ⟨ha, _⟩ => ha,
   fun ⟨_, ha, _⟩ => ha⟩

/-- Three entities. -/
inductive Three | a | b | c deriving DecidableEq

/-- Drop `A3`: one world, three actual entities, majority positivity. -/
def mNoA3 : FModel Unit Three where
  R := fun _ _ => True
  act := fun _ _ => True
  P := fun Y _ => (Y .a ∧ Y .b) ∨ (Y .a ∧ Y .c) ∨ (Y .b ∧ Y .c)

theorem noA3_notG (x : Three) : ¬ G mNoA3 x () := fun h => by
  have hp : mNoA3.P (fun z => z ≠ x) () := by cases x <;> simp [mNoA3]
  exact h _ hp rfl

theorem noA3 : A1 mNoA3 ∧ A2 mNoA3 ∧ ¬ A3 mNoA3 ∧ A4 mNoA3 ∧ A5 mNoA3 ∧ ¬ ExG mNoA3 () := by
  refine ⟨fun Y _ => ?_, fun Y Z _ h hi => ?_, fun h => ?_, fun _ _ h _ _ => h,
    fun _ => Or.inl ⟨fun _ hE _ _ => ⟨_, trivial, hE.1⟩, fun _ hE _ _ => ⟨_, trivial, hE.1⟩⟩,
    fun ⟨x, _, hg⟩ => noA3_notG x hg⟩
  · show (¬Y .a ∧ ¬Y .b ∨ ¬Y .a ∧ ¬Y .c ∨ ¬Y .b ∧ ¬Y .c) ↔
      ¬((Y .a ∧ Y .b) ∨ (Y .a ∧ Y .c) ∨ (Y .b ∧ Y .c))
    by_cases a : Y .a <;> by_cases b : Y .b <;> by_cases c : Y .c <;> simp [a, b, c]
  · have hz := fun z => hi () trivial z trivial
    rcases h with ⟨p, q⟩ | ⟨p, q⟩ | ⟨p, q⟩
    · exact Or.inl ⟨hz _ p, hz _ q⟩
    · exact Or.inr (Or.inl ⟨hz _ p, hz _ q⟩)
    · exact Or.inr (Or.inr ⟨hz _ p, hz _ q⟩)
  · rcases h () with ⟨p, _⟩ | ⟨p, _⟩ | ⟨p, _⟩
    · exact noA3_notG _ p
    · exact noA3_notG _ p
    · exact noA3_notG _ p

/-- Drop `A5`: S5, the entity actual only at `false`. -/
def mNoA5 : FModel Bool Unit where
  R := fun _ _ => True
  act := fun _ v => v = false
  P := fun Y _ => Y ()

theorem noA5 : A1 mNoA5 ∧ A2 mNoA5 ∧ A3 mNoA5 ∧ A4 mNoA5 ∧ ¬ A5 mNoA5 ∧ ¬ ExG mNoA5 true :=
  ⟨fun _ _ => Iff.rfl, fun _ _ _ h hi => hi false trivial () rfl h, fun _ _ h => h,
   fun _ _ h _ _ => h,
   fun h => match h true (fun _ => True) ⟨trivial, fun Z hz _ _ z _ _ => by cases z; exact hz⟩
      true trivial with
     | ⟨_, hv, _⟩ => Bool.noConfusion hv,
   fun ⟨_, hx, _⟩ => Bool.noConfusion hx⟩

/-- Drop `A4`: two worlds that see only each other; God at `w` is entity `w`, actual only
at the other world. -/
def mNoA4 : FModel Bool Bool where
  R := fun w v => v ≠ w
  act := fun x v => x ≠ v
  P := fun Y w => Y w

theorem noA4 : (∀ w v, mNoA4.R w v → mNoA4.R v w) ∧ A1 mNoA4 ∧ A2 mNoA4 ∧ A3 mNoA4 ∧
    ¬ A4 mNoA4 ∧ A5 mNoA4 ∧ ∀ w, ¬ ExG mNoA4 w :=
  ⟨fun _ _ h => Ne.symm h, fun _ _ => Iff.rfl,
   fun _ _ w h hi => hi (!w) (by cases w <;> simp [mNoA4]) w (by cases w <;> simp [mNoA4]) h,
   fun _ _ h => h,
   fun h => Bool.noConfusion (h (fun z => z = false) false rfl true (by simp [mNoA4])),
   fun _ _ hE v hv => ⟨_, Ne.symm hv, hE.1⟩,
   fun w ⟨_, hx, hg⟩ => hx (hg (fun z => z = w) rfl)⟩

end Programme.«20261022-0733-ontological».Run2.FittingColumn

#print axioms Programme.«20261022-0733-ontological».Run2.FittingColumn.principal
#print axioms Programme.«20261022-0733-ontological».Run2.FittingColumn.mono
#print axioms Programme.«20261022-0733-ontological».Run2.FittingColumn.gex_of_pred
#print axioms Programme.«20261022-0733-ontological».Run2.FittingColumn.gex_refl
#print axioms Programme.«20261022-0733-ontological».Run2.FittingColumn.gex_sym
#print axioms Programme.«20261022-0733-ontological».Run2.FittingColumn.s5_no_collapse
#print axioms Programme.«20261022-0733-ontological».Run2.FittingColumn.kd45_gap
#print axioms Programme.«20261022-0733-ontological».Run2.FittingColumn.noA1
#print axioms Programme.«20261022-0733-ontological».Run2.FittingColumn.noA2
#print axioms Programme.«20261022-0733-ontological».Run2.FittingColumn.noA3
#print axioms Programme.«20261022-0733-ontological».Run2.FittingColumn.noA4
#print axioms Programme.«20261022-0733-ontological».Run2.FittingColumn.noA5
