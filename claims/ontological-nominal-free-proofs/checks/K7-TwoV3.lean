import OpenQuestions.Ax1GenTwoVariant3
/-! # Thread F: hybrid-free `MC`, `L` and `G_ex` in `Ax1GenTwoVariant3`

v4 derives everything here from `OneWorld`, whose proof uses the point properties `Pt x w`
(nominals).  Its object-language shadow is `const`: **every lifted proposition is constant**.
Were `q w` and `¬ q v`, the constant properties `λ_. q` and `λ_. ¬q` are both non-empty, so
`Ax2a`/`Ax4` make `⊤` positive and `P` has two members, `Ax1GenTwo` gives `P G`, and `Ax4`
(`G ⊃ᴺ ⊥` otherwise) puts an actual God-like `g` at a successor `u` of `w`.  As `E g u`, the
non-empty `λ_. q` and `λ_. ¬q` are each exemplified at a successor of `u` (else they would be
vacuous essences of `g`), where God-like beings exist (`Th2`); but `g`'s positive `λ_. q` or
`λ_. ¬q` (`PosOfGod`) is rigid (`Ax2b`), so they cannot differ.  No frame condition. -/

namespace Programme.F.TwoV3

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

theorem MC_unconditional_hf : type_of% @MC_unconditional := fun φ w hφ v _ => const φ w v hφ
theorem MC_Two_hf : type_of% @MC_Two := fun φ w hφ v _ => const φ w v hφ

/-- Every property is `⊤` or `⊥` when `P` has at most one member and `⊤` or `⊥` is it. -/
private theorem onlyOne {w : i} (two : ¬ TwoMembers P w) {c : e → σ} (hc : P c w) :
    ∀ ψ, P ψ w → ψ = c := fun ψ hψ =>
  Classical.byContradiction fun hne => two ⟨ψ, c, hψ, hc, hne⟩

/-- `L` (`P G`) hybrid-free.  If `P` has two members, `Ax1GenTwo` with `Φ := P`.  Otherwise
its single member `c` is `⊤` or `⊥` (`Ax2a` at `⊥`), and `Ax2a` at `G` either gives `P G` or
makes `~G = c`, which contradicts `G`'s value at `w`. -/
theorem L_Two_hybrid_hf : type_of% @L_Two_hybrid := fun w =>
  if two : TwoMembers P w then
    Ax1GenTwo P G w ⟨⟨two, fun _ h => h⟩, fun _ _ _ _ => Iff.rfl⟩
  else
    let a : e := Classical.ofNonempty
    ((Ax2a G w).1).elim id fun hnG => by
      exfalso
      rcases (Ax2a (fun _ : e => ⊥ᵐ) w).1 with hb | ht
      · -- only member `⊥`: `~G = ⊥`, so `G a w`, but `G a w` needs `⊥ a w`
        have hG : (~ᵐG) = (fun _ => ⊥ᵐ) := onlyOne two hb _ hnG
        have hGa : G a w := Classical.byContradiction fun h =>
          (Eq.mp (congrFun (congrFun hG a) w) h : ⊥ᵐ w)
        exact hGa _ hb
      · -- only member `⊤`: `~G = ⊤`, so `¬ G a w`, but every positive property is `⊤`
        have ht' : P (fun _ : e => ⊤ᵐ) w := topEq ▸ ht
        have hG : (~ᵐG) = (fun _ => ⊤ᵐ) := onlyOne two ht' _ hnG
        exact (Eq.mp (congrFun (congrFun hG a) w).symm trivial)
          (fun φ hφ => (onlyOne two ht' φ hφ).symm ▸ trivial)

/-- `G_ex` under "every world has an actual individual", hybrid-free.  `⊥` is not positive: else
every positive property is empty (`Ax4`), so every property is `⊤` or `⊥` (`Ax2a`), and `E` is `⊥`
(`Ax3`); but an actual `a` has `E` then, each of its essences being non-empty, hence `⊤`, hence
actually exemplified everywhere.  So `L` and `Ax4` put a God-like being at a successor
(`dia_G`), and `const` carries its existence back to `w`. -/
theorem G_ex_Two_actual_hybrid_hf : type_of% @G_ex_Two_actual_hybrid := fun ae w =>
  have nb : ¬ P (fun _ : e => ⊥ᵐ) w := fun hb =>
    have allbot : ∀ φ : e → σ, P φ w → φ = (fun _ : e => ⊥ᵐ) := fun φ hφ =>
      Classical.byContradiction fun hne => (Ax2a _ w).2 ⟨hb, topEq ▸ top_of hφ hne⟩
    let ⟨a, _⟩ := ae w
    have Ea : E a w := fun φ hess v hv =>
      have hne : φ ≠ (fun _ => ⊥ᵐ) := (hess (fun _ => ⊤ᵐ) trivial v hv).1
      have htop : φ = (fun _ => ⊤ᵐ) := ((Ax2a φ w).1).elim
        (fun h => (hne (allbot φ h)).elim)
        (fun h => funext fun z => funext fun t => propext ⟨fun _ => trivial, fun _ =>
          Classical.byContradiction fun hn => (Eq.mp (congrFun (congrFun (allbot _ h) z) t) hn : ⊥ᵐ t)⟩)
      let ⟨b, hb⟩ := ae v
      ⟨b, hb, htop ▸ trivial⟩
    (Eq.mp (congrFun (congrFun (allbot E (Ax3 w)) a) w) Ea : ⊥ᵐ w)
  let ⟨v, _, hv⟩ := dia_G (L_Two_hybrid_hf w) nb
  const _ v w hv

theorem Th4_Two_actual_hybrid_hf : type_of% @Th4_Two_actual_hybrid := fun ae w =>
  let ⟨v, hv⟩ := Serial w
  ⟨v, hv, G_ex_Two_actual_hybrid_hf ae v⟩

example : type_of% @MC_unconditional_hf = type_of% @MC_unconditional := rfl
example : type_of% @MC_Two_hf = type_of% @MC_Two := rfl
example : type_of% @L_Two_hybrid_hf = type_of% @L_Two_hybrid := rfl
example : type_of% @G_ex_Two_actual_hybrid_hf = type_of% @G_ex_Two_actual_hybrid := rfl
example : type_of% @Th4_Two_actual_hybrid_hf = type_of% @Th4_Two_actual_hybrid := rfl

end Programme.F.TwoV3

#print axioms Programme.F.TwoV3.MC_unconditional_hf
#print axioms Programme.F.TwoV3.MC_Two_hf
#print axioms Programme.F.TwoV3.L_Two_hybrid_hf
#print axioms Programme.F.TwoV3.G_ex_Two_actual_hybrid_hf
#print axioms Programme.F.TwoV3.Th4_Two_actual_hybrid_hf
