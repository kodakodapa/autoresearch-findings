import OpenQuestions.Ax1GenTwoVariant3Th4
/-! # Thread F: hybrid-free `G_ex_Two_hybrid` and `AllExist_Two` in `Ax1GenTwoVariant3Th4`

`const` (every lifted proposition is constant) is proved exactly as in `Programme.F.TwoV3`, from
`Ax1GenTwo`, `Ax2a`, `Ax2b`, `Ax3`, `Ax4` and no frame condition; with the postulated `Th4` it moves
the God-like being of a successor back to the world of evaluation.  `AllExist_Two` takes th's
witness `z = y ∧ ¬(∃ᴱ u, u = z)` (P8) in place of a bare `existsAt`. -/

namespace Programme.«20261022-1314-ontological».F.TwoV3Th4

private theorem topEq : (~ᵐ(fun _ : e => ⊥ᵐ)) = (fun _ : e => ⊤ᵐ) := by funext x v; simp

private theorem neBot {φ : e → σ} {x : e} {w : i} (h : φ x w) : φ ≠ (fun _ : e => ⊥ᵐ) :=
  fun h' => (congrFun (congrFun h' x) w ▸ h : ⊥ᵐ w)

/-- A positive non-empty property makes `⊤` positive. -/
private theorem top_of {φ : e → σ} {w : i} (hφ : P φ w) (ne : φ ≠ (fun _ : e => ⊥ᵐ)) :
    P (fun _ : e => ⊤ᵐ) w :=
  Ax4 φ _ w ⟨hφ, fun _ _ => ⟨ne, fun _ _ _ => trivial⟩⟩

/-- With `P G` and `¬ P ⊥` at `w`, a God-like being is actual at some successor of `w`. -/
private theorem dia_G {w : i} (PG : P G w) (nb : ¬ P (fun _ : e => ⊥ᵐ) w) : (◇(∃ᴱ x, G x)) w :=
  Classical.byContradiction fun hn =>
    have Gne : G ≠ (fun _ : e => ⊥ᵐ) := fun h => nb (h ▸ PG)
    nb (Ax4 G _ w ⟨PG, fun v hv => ⟨Gne, fun z hz hG => hn ⟨v, hv, z, hz, hG⟩⟩⟩)

/-- At a world with an actual God-like `g`, every non-empty property is exemplified at some
successor (else it is a vacuous essence of `g`, against `E g u`). -/
private theorem reach {g : e} {u : i} (hG : G g u) (χ : e → σ) (ne : χ ≠ (fun _ : e => ⊥ᵐ)) :
    ∃ u1, u 𝗿 u1 ∧ ∃ y, χ y u1 :=
  Classical.byContradiction fun hn =>
    have Eg : E g u := hG E (Ax3 u)
    have ess : Ess χ g u := fun _ _ v hv =>
      ⟨ne, fun y _ hχ => (hn ⟨v, hv, y, hχ⟩).elim⟩
    let ⟨v, hv⟩ := Serial u
    let ⟨y, _, hχ⟩ := Eg χ ess v hv
    hn ⟨v, hv, y, hχ⟩

/-- **Every lifted proposition is constant**, hybrid-free and with no frame condition. -/
theorem const (q : σ) (w v : i) (hw : q w) : q v :=
  Classical.byContradiction fun hv =>
    let a : e := Classical.ofNonempty
    let χ : e → σ := fun _ => q
    let χn : e → σ := fun _ => ¬ᵐ q
    have ne1 : χ ≠ (fun _ => ⊥ᵐ) := @neBot χ a w hw
    have ne2 : χn ≠ (fun _ => ⊥ᵐ) := @neBot χn a v hv
    -- at every world `⊤` is positive, `⊥` is not, and `P` has two members
    have top : ∀ t, P (fun _ : e => ⊤ᵐ) t := fun t =>
      ((Ax2a χ t).1).elim (fun h => top_of h ne1) (fun h => top_of h ne2)
    have nb : ∀ t, ¬ P (fun _ : e => ⊥ᵐ) t := fun t hb => (Ax2a _ t).2 ⟨hb, topEq ▸ top t⟩
    have two : ∀ t, TwoMembers P t := fun t =>
      ((Ax2a χ t).1).elim
        (fun h => ⟨_, χ, top t, h, fun h' => hv (Eq.mp (congrFun (congrFun h' a) v) trivial)⟩)
        (fun h => ⟨_, ~ᵐχ, top t, h, fun h' => Eq.mp (congrFun (congrFun h' a) w) trivial hw⟩)
    have PG : P G w := Ax1GenTwo P G w ⟨⟨two w, fun _ h => h⟩, fun _ _ _ _ => Iff.rfl⟩
    let ⟨u, _, g, _, hG⟩ := dia_G PG (nb w)
    let ⟨u1, r1, _, hq1⟩ := reach hG χn ne2
    let ⟨u2, r2, _, hq2⟩ := reach hG χ ne1
    let ⟨z1, _, hz1⟩ := Th2 g u hG u1 r1
    let ⟨z2, _, hz2⟩ := Th2 g u hG u2 r2
    (Classical.em (q u)).elim
      (fun hu => hq1 (hz1 χ (Ax2b χ u (PosOfGod hG hu) u1 r1)))
      (fun hu => hz2 χn (Ax2b χn u (PosOfGod hG hu) u2 r2) hq2)

theorem G_ex_Two_hybrid_hf : type_of% @G_ex_Two_hybrid := fun w =>
  let ⟨v, _, hex⟩ := Th4 w
  const _ v w hex

theorem AllExist_Two_pt (someNonGod : ∃ u z, (∃ᴱ y, G y) u ∧ ¬ G z u) (w : i) (y : e) :
    y @ᵐ w :=
  Classical.byContradiction fun ny =>
    let ⟨g, _, hG⟩ := G_ex_Two someNonGod w
    have Eg : E g w := hG E (Ax3 w)
    let φ : e → σ := fun z => (z =ᵐ y) ∧ᵐ ¬ᵐ(∃ᴱ u, u =ᵐ z)
    have ess : Ess φ g w := fun _ _ _ _ =>
      ⟨fun h => (congrFun (congrFun h y) w ▸
          (⟨rfl, fun ⟨_, hu, he⟩ => ny (he ▸ hu)⟩ : φ y w) : ⊥ᵐ w),
       fun z hz ⟨_, hnz⟩ => (hnz ⟨z, hz, rfl⟩).elim⟩
    let ⟨v, hv⟩ := Serial w
    let ⟨z, hz, _, hnz⟩ := Eg φ ess v hv
    hnz ⟨z, hz, rfl⟩

theorem AllExist_Two_hf : type_of% @AllExist_Two := AllExist_Two_pt

example : type_of% @G_ex_Two_hybrid_hf = type_of% @G_ex_Two_hybrid := rfl
example : type_of% @AllExist_Two_hf = type_of% @AllExist_Two := rfl

end Programme.«20261022-1314-ontological».F.TwoV3Th4

#print axioms Programme.«20261022-1314-ontological».F.TwoV3Th4.G_ex_Two_hybrid_hf
#print axioms Programme.«20261022-1314-ontological».F.TwoV3Th4.AllExist_Two_hf
