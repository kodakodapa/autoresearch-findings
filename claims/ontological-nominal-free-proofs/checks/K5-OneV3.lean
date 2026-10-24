import OpenQuestions.Ax1GenOneVariant3
/-! # Thread F: hybrid-free proofs for `Ax1GenOneVariant3`

v4 derives the second layer (`PTop_One_deriv`, `G_ex_One_deriv`, `One_gives_S`, ...) from
`OneWorld`, whose proof uses the point properties `Pt x w` (nominals).  Its object-language shadow
is `const`: every lifted proposition is constant, proved as in `Programme.F.TwoV3` with `L_One`
(`Φ := P`) in place of `Ax1GenTwo`.  `AllActual_of_PBot` and `AllExist_One` replace the bare
`existsAt` and `Pt` witnesses by `¬(∃ᴱ u, u = z)` and `z = y ∧ ¬(∃ᴱ u, u = z)`. -/

namespace Programme.F.OneV3

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
    have top : P (fun _ : e => ⊤ᵐ) w :=
      ((Ax2a χ w).1).elim (fun h => top_of h ne1) (fun h => top_of h ne2)
    have nb : ¬ P (fun _ : e => ⊥ᵐ) w := fun hb => (Ax2a _ w).2 ⟨hb, topEq ▸ top⟩
    let ⟨u, _, g, _, hG⟩ := dia_G (L_One w) nb
    let ⟨u1, r1, _, hq1⟩ := reach hG χn ne2
    let ⟨u2, r2, _, hq2⟩ := reach hG χ ne1
    let ⟨_, _, hz1⟩ := Th2 g u hG u1 r1
    let ⟨_, _, hz2⟩ := Th2 g u hG u2 r2
    (Classical.em (q u)).elim
      (fun hu => hq1 (hz1 χ (Ax2b χ u (PosOfGod hG hu) u1 r1)))
      (fun hu => hz2 χn (Ax2b χn u (PosOfGod hG hu) u2 r2) hq2)

theorem MC_unconditional_hf : type_of% @MC_unconditional := fun φ w hφ v _ => const φ w v hφ
theorem MC_One_hf : type_of% @MC_One := fun φ w hφ v _ => const φ w v hφ

/-- `AllActual_of_PBot` with "being non-actual" written `¬(∃ᴱ u, u = z)`. -/
theorem AllActual_of_PBot_hf : type_of% @AllActual_of_PBot := by
  intro w pb
  refine Classical.byContradiction fun h => ?_
  let ν : e → σ := fun z => ¬ᵐ(∃ᴱ u, u =ᵐ z)
  have Pν : P ν w := Ax1GenOne (fun ψ' _ => ψ' = (fun _ : e => ⊥ᵐ)) ν w
    ⟨⟨⟨_, rfl⟩, fun _ hψ => hψ ▸ pb⟩,
     fun _ _ z hz => ⟨fun hν => (hν ⟨z, hz, rfl⟩).elim, fun all _ => all (fun _ => ⊥ᵐ) rfl⟩⟩
  have ne : ν ≠ (fun _ => ⊥ᵐ) := fun e => h fun z u =>
    Classical.byContradiction fun hn =>
      (congrFun (congrFun e z) u ▸ (fun ⟨_, hu, he⟩ => hn (he ▸ hu) : ν z u) : ⊥ᵐ u)
  have all : ∀ ψ : e → σ, P ψ w := fun ψ =>
    Ax4 ν ψ w ⟨Pν, fun _ _ => ⟨ne, fun y hy hν => (hν ⟨y, hy, rfl⟩).elim⟩⟩
  exact (Ax2a (fun _ => ⊤ᵐ) w).2 ⟨all _, all _⟩

/-- `¬ P ⊥`: else every positive property is empty, so every property is `⊤` or `⊥` and `E`
(positive, `Ax3`) is `⊥`; but with everything actual (`AllActual_of_PBot_hf`) any individual
has `E`, each of its essences being non-empty, hence `⊤`. -/
theorem NotPBot_One_deriv_hf : type_of% @NotPBot_One_deriv := fun w pb =>
  have act := AllActual_of_PBot_hf pb
  have allbot : ∀ φ : e → σ, P φ w → φ = (fun _ : e => ⊥ᵐ) := fun φ hφ =>
    Classical.byContradiction fun hne => (Ax2a _ w).2 ⟨pb, topEq ▸ top_of hφ hne⟩
  let a : e := Classical.ofNonempty
  have Ea : E a w := fun φ hess v hv =>
    have hne : φ ≠ (fun _ => ⊥ᵐ) := (hess (fun _ => ⊤ᵐ) trivial v hv).1
    have htop : φ = (fun _ => ⊤ᵐ) := ((Ax2a φ w).1).elim
      (fun h => (hne (allbot φ h)).elim)
      (fun h => funext fun z => funext fun t => propext ⟨fun _ => trivial, fun _ =>
        Classical.byContradiction fun hn => (Eq.mp (congrFun (congrFun (allbot _ h) z) t) hn : ⊥ᵐ t)⟩)
    ⟨a, act a v, htop ▸ trivial⟩
  (Eq.mp (congrFun (congrFun (allbot E (Ax3 w)) a) w) Ea : ⊥ᵐ w)

theorem PTop_One_deriv_hf : type_of% @PTop_One_deriv := fun w =>
  topEq ▸ (Ax2a (fun _ : e => ⊥ᵐ) w).1.resolve_left (NotPBot_One_deriv_hf w)

theorem E_top_of_PBot_hf : type_of% @E_top_of_PBot := fun pb =>
  (NotPBot_One_deriv_hf _ pb).elim

theorem G_ex_One_deriv_hf : type_of% @G_ex_One_deriv := fun w =>
  let ⟨v, _, hv⟩ := dia_G (L_One w) (NotPBot_One_deriv_hf w)
  const _ v w hv

theorem Th4_One_deriv_hf : type_of% @Th4_One_deriv := fun w =>
  let ⟨v, hv⟩ := Serial w
  ⟨v, hv, G_ex_One_deriv_hf v⟩

/-- `AllExist_One`: "being `y` and not actual" would be a vacuous essence of the God-like being
at `w` (witness `z = y ∧ ¬(∃ᴱ u, u = z)`, no `Pt`). -/
theorem AllExist_One_hf : type_of% @AllExist_One := fun y w =>
  Classical.byContradiction fun ny =>
    let ⟨g, _, hG⟩ := G_ex_One_deriv_hf w
    have Eg : E g w := hG E (Ax3 w)
    let φ : e → σ := fun z => (z =ᵐ y) ∧ᵐ ¬ᵐ(∃ᴱ u, u =ᵐ z)
    have ess : Ess φ g w := fun _ _ _ _ =>
      ⟨fun h => (congrFun (congrFun h y) w ▸
          (⟨rfl, fun ⟨_, hu, he⟩ => ny (he ▸ hu)⟩ : φ y w) : ⊥ᵐ w),
       fun z hz ⟨_, hnz⟩ => (hnz ⟨z, hz, rfl⟩).elim⟩
    let ⟨v, hv⟩ := Serial w
    let ⟨z, hz, _, hnz⟩ := Eg φ ess v hv
    hnz ⟨z, hz, rfl⟩

/-- `One_gives_S`: an empty `Φ` stays empty at successors (`const` on `Φ ψ`), so the conjunction
holds of every actual being there, and `Ax4` from `P ⊤` gives `P φ`. -/
theorem One_gives_S_hf : type_of% @One_gives_S := fun Φ φ w ⟨pos, cj⟩ =>
  if hex : ∃ ψ, Φ ψ w then Ax1GenOne Φ φ w ⟨⟨hex, pos⟩, cj⟩
  else
    Ax4 (fun _ : e => ⊤ᵐ) φ w ⟨PTop_One_deriv_hf w, fun v hv =>
      ⟨@neBot (fun _ : e => ⊤ᵐ) Classical.ofNonempty w trivial, fun y hy _ =>
        (cj v hv y hy).2 fun ψ hψ => (hex ⟨ψ, const (Φ ψ) v w hψ⟩).elim⟩⟩

theorem One_gives_Box_hf : type_of% @One_gives_Box := fun Φ φ w ⟨⟨pos, _⟩, cj⟩ =>
  One_gives_S_hf Φ φ w ⟨pos, cj⟩

/-- `Box_gives_One`: `PosProps Φ` is boxed, as membership moves back by `const` and positivity
forward by `Ax2b`. -/
theorem Box_gives_One_hf : type_of% @Box_gives_One := fun hBox Φ φ w ⟨⟨_, pos⟩, cj⟩ =>
  hBox Φ φ w ⟨⟨pos, fun v hv ψ hψ => Ax2b ψ w (pos ψ (const (Φ ψ) v w hψ)) v hv⟩, cj⟩

example : type_of% @MC_unconditional_hf = type_of% @MC_unconditional := rfl
example : type_of% @MC_One_hf = type_of% @MC_One := rfl
example : type_of% @AllActual_of_PBot_hf = type_of% @AllActual_of_PBot := rfl
example : type_of% @NotPBot_One_deriv_hf = type_of% @NotPBot_One_deriv := rfl
example : type_of% @PTop_One_deriv_hf = type_of% @PTop_One_deriv := rfl
example : type_of% @E_top_of_PBot_hf = type_of% @E_top_of_PBot := rfl
example : type_of% @G_ex_One_deriv_hf = type_of% @G_ex_One_deriv := rfl
example : type_of% @Th4_One_deriv_hf = type_of% @Th4_One_deriv := rfl
example : type_of% @AllExist_One_hf = type_of% @AllExist_One := rfl
example : type_of% @One_gives_S_hf = type_of% @One_gives_S := rfl
example : type_of% @One_gives_Box_hf = type_of% @One_gives_Box := rfl
example : type_of% @Box_gives_One_hf = type_of% @Box_gives_One := rfl

end Programme.F.OneV3

#print axioms Programme.F.OneV3.MC_unconditional_hf
#print axioms Programme.F.OneV3.MC_One_hf
#print axioms Programme.F.OneV3.AllActual_of_PBot_hf
#print axioms Programme.F.OneV3.NotPBot_One_deriv_hf
#print axioms Programme.F.OneV3.PTop_One_deriv_hf
#print axioms Programme.F.OneV3.E_top_of_PBot_hf
#print axioms Programme.F.OneV3.G_ex_One_deriv_hf
#print axioms Programme.F.OneV3.Th4_One_deriv_hf
#print axioms Programme.F.OneV3.AllExist_One_hf
#print axioms Programme.F.OneV3.One_gives_S_hf
#print axioms Programme.F.OneV3.One_gives_Box_hf
#print axioms Programme.F.OneV3.Box_gives_One_hf
