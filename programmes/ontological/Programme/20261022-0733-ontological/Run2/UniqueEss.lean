import Programme.«20261022-0733-ontological».Run2.GexL
import Programme.«20261022-0733-ontological».Run2.OneHF

/-! # AllExist, UniqueEss1, UniqueEss2 in closed models of variant 3 and 3′, no nominal

Target E, arXiv 2609.36279v4 `sec:open`: the library module `Ax1GenTwoVariant3Th4.lean` derives
`AllExist_Two`, `Reach_Two`, `EssMemI_Two`, `UniqueEss1_Two`, `UniqueEss2_Two` from
`G_ex_Two someNonGod`, so they inherit the side condition (†).  th's conjecture E6
(`agents/th/lean/Programme/Th/UniqueEss*.lean`) abstracts the chain over a `G_ex` hypothesis.

Here the chain is carried out over K1's Henkin-style `Model` with the `Closed` interface, taking
seriality and `G_ex` (an actual God-like being at every world) as hypotheses, and then
instantiated with each hybrid-free `G_ex` proved over the interface:
K3 (`DropDagger.gex`: variant 3, `Ax1GenTwo`, `Th4`, no (†)), K5 (`OneHF.gex`: `Ax1GenOne`),
K6 (`GexL.gex_noConj`: variant 3, `Th4`, `Ax2b`, no conjunction axiom; `GexL.gex_L`: variant 3′, `L`).

Three closures beyond `Closed` (each the denotation of a nominal-free term with an entity
parameter, not a world parameter):
* `hid`: `λz. z = y` for each entity `y` (primitive identity);
* `hact`: `λz. z@` (actuality, a constant of the signature, as in K5);
* `happ`: `φ y` for admitted `φ` and entity `y` (application), so `λ_. φ y` is admitted by `lift`.
The identity predicate replaces the shallow Leibniz `z ≡ x`; `UniqueEss2` concludes primitive
equality of the two essences. -/

namespace Programme.«20261022-0733-ontological».Run2.UniqueEss

open Programme.«20261022-0733-ontological».Run2.TwoClosed Programme.«20261022-0733-ontological».Run2.DropDagger

variable {W D : Type} {M : Model W D}

/-- The extra closures. -/
structure Extra (M : Model W D) : Prop where
  hid : ∀ y : D, M.AT (fun z _ => z = y)
  hact : M.AT (fun z u => M.act z u)
  happ : ∀ φ, M.AT φ → ∀ y : D, M.AS (φ y)

section chain
variable (C : Closed M) (X : Extra M) (hE : M.AT (E3 M)) (h2a : Ax2a M) (h3 : Ax3v3 M)
  (hser : ∀ w, ∃ v, M.R w v) (gex : ∀ w, ExG M w)

include C X hE h3 hser gex in
/-- `AllExist`: every entity is actual at every world.  No `Ax2b`. -/
theorem allExist (w : W) (y : D) : M.act y w :=
  Classical.byContradiction fun ny => by
    obtain ⟨g, _, hG⟩ := gex w
    have Eg : E3 M g w := hG _ hE (h3 w)
    let φ : D → W → Prop := conj (fun z _ => z = y) (neg (fun z u => M.act z u))
    have hφ : M.AT φ := C.conj _ _ (X.hid y) (C.neg _ X.hact)
    have ess : Ess3 M φ g w := fun _ _ _ _ _ =>
      ⟨fun h => (congrFun (congrFun h y) w ▸ (⟨rfl, ny⟩ : φ y w) : bot y w),
       fun _ hz hφz => (hφz.2 hz).elim⟩
    obtain ⟨v, hv⟩ := hser w
    obtain ⟨_, hz, _, hnz⟩ := Eg φ hφ ess v hv
    exact hnz hz

include C X hE h3 hser gex in
/-- `Reach`: every admitted non-empty property is exemplified at a successor of every world. -/
theorem reach {φ : D → W → Prop} (hA : M.AT φ) (w : W) (hne : φ ≠ bot) :
    ∃ v, M.R w v ∧ ∃ y, φ y v :=
  Classical.byContradiction fun hn => by
    have ⟨z, t, hzt⟩ : ∃ z t, φ z t := Classical.byContradiction fun h =>
      hne (funext fun z => funext fun t => propext ⟨fun hφ => h ⟨z, t, hφ⟩, False.elim⟩)
    let χ : D → W → Prop := fun _ => φ z
    have hχ : M.AT χ := C.lift _ (X.happ φ hA z)
    obtain ⟨g, _, hG⟩ := gex w
    have ess : Ess3 M χ g w := fun _ _ _ v hv =>
      ⟨fun h => (congrFun (congrFun h z) t ▸ (hzt : χ z t) : bot z t),
       fun _ _ hc => (hn ⟨v, hv, z, hc⟩).elim⟩
    obtain ⟨v, hv⟩ := hser w
    obtain ⟨_, _, hc⟩ := hG _ hE (h3 w) χ hχ ess v hv
    exact hn ⟨v, hv, z, hc⟩

include C X hE h3 hser gex in
/-- `EssMemI`: an essence of `x` holds of `x`. -/
theorem essMem {φ : D → W → Prop} {x : D} {w : W} (hA : M.AT φ) (h : Ess3 M φ x w) : φ x w :=
  Classical.byContradiction fun hn => by
    obtain ⟨u, hu⟩ := hser w
    have hne := (h (neg φ) (C.neg _ hA) hn u hu).1
    obtain ⟨v, hv, y, hy⟩ := reach C X hE h3 hser gex hA w hne
    exact (h (neg φ) (C.neg _ hA) hn v hv).2 y (allExist C X hE h3 hser gex v y) hy hy

variable (h2b : Ax2b M)

include C X hE h2a h2b h3 hser gex in
/-- `UniqueEss1`: two essences of `x` are necessarily coextensive on actual entities. -/
theorem uniqueEss1 {φ ψ : D → W → Prop} (hφA : M.AT φ) (hψA : M.AT ψ) {x : D} {w : W}
    (hφ : Ess3 M φ x w) (hψ : Ess3 M ψ x w) :
    ∀ v, M.R w v → ∀ y, M.act y v → (φ y v ↔ ψ y v) := fun v hv y hy => by
  have mc := GexL.mc_of_gex C h2a h2b gex
  have tr : ∀ φ' ψ', M.AT φ' → M.AT ψ' → Ess3 M φ' x w → Ess3 M ψ' x w → φ' y v → ψ' y v :=
    fun φ' ψ' _ hψ'A hφ' hψ' hφy => by
      have hyx : y = x := (hφ' _ (X.hid x) rfl v hv).2 y hy hφy
      have hψx : ψ' x v :=
        mc _ (X.happ ψ' hψ'A x) w (essMem C X hE h3 hser gex hψ'A hψ') v hv
      exact hyx ▸ hψx
  exact ⟨tr φ ψ hφA hψA hφ hψ, tr ψ φ hψA hφA hψ hφ⟩

include C X hE h2a h2b h3 hser gex in
/-- `UniqueEss2`: two essences of `x` are identical properties. -/
theorem uniqueEss2 {φ ψ : D → W → Prop} (hφA : M.AT φ) (hψA : M.AT ψ) {x : D} {w : W}
    (hφ : Ess3 M φ x w) (hψ : Ess3 M ψ x w) : φ = ψ := by
  have half : ∀ φ' ψ', M.AT φ' → M.AT ψ' → Ess3 M φ' x w → Ess3 M ψ' x w →
      ∀ z t, φ' z t → ψ' z t := fun φ' ψ' hφ'A hψ'A hφ' hψ' z t hzt =>
    Classical.byContradiction fun hn => by
      let χ : D → W → Prop := conj φ' (neg ψ')
      have hχ : M.AT χ := C.conj _ _ hφ'A (C.neg _ hψ'A)
      have hne : χ ≠ bot := fun h =>
        (congrFun (congrFun h z) t ▸ (⟨hzt, hn⟩ : χ z t) : bot z t)
      obtain ⟨u, hu, y, hφy, hnψy⟩ := reach C X hE h3 hser gex hχ w hne
      exact hnψy ((uniqueEss1 C X hE h2a h3 hser gex h2b hφ'A hψ'A hφ' hψ' u hu y
        (allExist C X hE h3 hser gex u y)).1 hφy)
  exact funext fun z => funext fun t =>
    propext ⟨half φ ψ hφA hψA hφ hψ z t, half ψ φ hψA hφA hψ hφ z t⟩

end chain

/-! ## The four settings -/

/-- The three conclusions bundled. -/
def Results (M : Model W D) : Prop :=
  (∀ w y, M.act y w) ∧
  (Ax2b M → ∀ φ ψ, M.AT φ → M.AT ψ → ∀ x w, Ess3 M φ x w → Ess3 M ψ x w →
    (∀ v, M.R w v → ∀ y, M.act y v → (φ y v ↔ ψ y v)) ∧ φ = ψ)

theorem results (C : Closed M) (X : Extra M) (hE : M.AT (E3 M)) (h2a : Ax2a M) (h3 : Ax3v3 M)
    (hser : ∀ w, ∃ v, M.R w v) (gex : ∀ w, ExG M w) : Results M :=
  ⟨fun w y => allExist C X hE h3 hser gex w y, fun h2b _ _ hφA hψA _ _ hφ hψ =>
    ⟨uniqueEss1 C X hE h2a h3 hser gex h2b hφA hψA hφ hψ,
     uniqueEss2 C X hE h2a h3 hser gex h2b hφA hψA hφ hψ⟩⟩

/-- **Variant 3, `Ax1GenTwo`, `Th4`, no side condition (†)** (with K3). -/
theorem results_two [Nonempty W] [Nonempty D] (C : Closed M) (X : Extra M) (hE : M.AT (E3 M))
    (h2a : Ax2a M) (h3 : Ax3v3 M) (h4 : Ax4c M) (hth4 : Th4 M) (hT : Ax1GenTwo M) :
    Results M :=
  results C X hE h2a h3 (GexL.serial_c C hE h2a h3 h4)
    (DropDagger.gex C hE h2a h3 h4 hth4 hT)

/-- **Variant 3, `Ax1GenOne`** (with K5). -/
theorem results_one [Nonempty D] (C : Closed M) (X : Extra M) (hE : M.AT (E3 M))
    (h2a : Ax2a M) (h3 : Ax3v3 M) (h4 : Ax4c M) (h1 : OneHF.Ax1GenOne M) : Results M :=
  results C X hE h2a h3 (GexL.serial_c C hE h2a h3 h4)
    (OneHF.gex C X.hact hE h2a h3 h4 h1)

/-- **Variant 3, `Th4`, `Ax2b`, no conjunction axiom** (with K6). -/
theorem results_noConj (C : Closed M) (X : Extra M) (hE : M.AT (E3 M)) (h2a : Ax2a M)
    (h2b : Ax2b M) (h3 : Ax3v3 M) (h4 : Ax4c M) (hth4 : Th4 M) : Results M :=
  results C X hE h2a h3 (GexL.serial_c C hE h2a h3 h4)
    (GexL.gex_noConj C hE h2a h2b h3 h4 hth4)

/-- **Variant 3′, plain `Ax4`, `L`** (with K6). -/
theorem results_L (C : Closed M) (X : Extra M) (hE : M.AT (E3 M)) (h2a : Ax2a M)
    (h2b : Ax2b M) (h3 : Ax3v3 M) (h4 : Ax4 M) (hL : BoxIdle.L M) : Results M :=
  results C X hE h2a h3 (GexL.serial C hE h2a h3 h4) (GexL.gex_L C hE h2a h2b h3 h4 hL)

/-- **Variant 3′, `Ax1GenBoxTwo`** (with K4, K6). -/
theorem results_boxTwo [Nonempty D] (C : Closed M) (X : Extra M) (hE : M.AT (E3 M))
    (h2a : Ax2a M) (h2b : Ax2b M) (h3 : Ax3v3 M) (h4 : Ax4 M) (hB : BoxIdle.Ax1GenBoxTwo M) :
    Results M :=
  results C X hE h2a h3 (GexL.serial C hE h2a h3 h4) (GexL.gex_boxTwo C hE h2a h2b h3 h4 hB)

/-! ## Non-vacuity: K1's one-world model satisfies the extra closures -/

theorem unitModel_extra : Extra unitModel :=
  ⟨fun _ => trivial, trivial, fun _ _ _ => trivial⟩

end Programme.«20261022-0733-ontological».Run2.UniqueEss

#print axioms Programme.«20261022-0733-ontological».Run2.UniqueEss.allExist
#print axioms Programme.«20261022-0733-ontological».Run2.UniqueEss.uniqueEss1
#print axioms Programme.«20261022-0733-ontological».Run2.UniqueEss.uniqueEss2
#print axioms Programme.«20261022-0733-ontological».Run2.UniqueEss.results_two
#print axioms Programme.«20261022-0733-ontological».Run2.UniqueEss.results_one
#print axioms Programme.«20261022-0733-ontological».Run2.UniqueEss.results_noConj
#print axioms Programme.«20261022-0733-ontological».Run2.UniqueEss.results_L
#print axioms Programme.«20261022-0733-ontological».Run2.UniqueEss.results_boxTwo
#print axioms Programme.«20261022-0733-ontological».Run2.UniqueEss.unitModel_extra
