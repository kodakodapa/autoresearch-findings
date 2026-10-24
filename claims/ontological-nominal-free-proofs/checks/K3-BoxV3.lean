import OpenQuestions.Ax1GenBoxVariant3
/-! # Thread F: hybrid-free `MC_S4`, `Th5_S4`, `Ax1Gen_of_refl` in `Ax1GenBoxVariant3`

v4 (this module's section on S4) derives these via `OneWorld`, i.e. with nominals, and notes
that hybrid-free derivations under `Ax1GenBox` are not known.  Here: `const` (every lifted
proposition is constant), as in `Programme.F.TwoV3`, with the module's hybrid-free `L` and
`PTop`.  Then collapse is `const`, `□PosProps Φ` follows from `PosProps Φ` by `const` on `Φ ψ`
and `Ax2b`, and the God-like being of `Th4` is moved by `const`.  Reflexivity is unused. -/

namespace Programme.F.BoxV3

private theorem topEq : (~ᵐ(fun _ : e => ⊥ᵐ)) = (fun _ : e => ⊤ᵐ) := by funext x v; simp

private theorem neBot {φ : e → σ} {x : e} {w : i} (h : φ x w) : φ ≠ (fun _ : e => ⊥ᵐ) :=
  fun h' => (congrFun (congrFun h' x) w ▸ h : ⊥ᵐ w)

/-- A positive non-empty property makes `⊤` positive. -/
private theorem _top_of {φ : e → σ} {w : i} (hφ : P φ w) (ne : φ ≠ (fun _ : e => ⊥ᵐ)) :
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
    have nb : ¬ P (fun _ : e => ⊥ᵐ) w := fun hb => (Ax2a _ w).2 ⟨hb, topEq ▸ PTop w⟩
    let ⟨u, _, g, _, hG⟩ := dia_G (L w) nb
    let ⟨u1, r1, _, hq1⟩ := reach hG χn ne2
    let ⟨u2, r2, _, hq2⟩ := reach hG χ ne1
    let ⟨_, _, hz1⟩ := Th2 g u hG u1 r1
    let ⟨_, _, hz2⟩ := Th2 g u hG u2 r2
    (Classical.em (q u)).elim
      (fun hu => hq1 (hz1 χ (Ax2b χ u (PosOfGod hG hu) u1 r1)))
      (fun hu => hz2 χn (Ax2b χn u (PosOfGod hG hu) u2 r2) hq2)

theorem MC_S4_hf : type_of% @MC_S4 := fun _ φ w hφ v _ => const φ w v hφ

theorem Ax1Gen_of_refl_hf : type_of% @Ax1Gen_of_refl := fun _ Φ φ w ⟨pos, cj⟩ =>
  Ax1GenBox Φ φ w ⟨⟨pos, fun v hv ψ hψ => Ax2b ψ w (pos ψ (const (Φ ψ) v w hψ)) v hv⟩, cj⟩

theorem Th5_S4_hf : type_of% @Th5_S4 := fun _ w v _ =>
  let ⟨u, _, hex⟩ := Th4 w
  const _ u v hex

example : type_of% @MC_S4_hf = type_of% @MC_S4 := rfl
example : type_of% @Ax1Gen_of_refl_hf = type_of% @Ax1Gen_of_refl := rfl
example : type_of% @Th5_S4_hf = type_of% @Th5_S4 := rfl

end Programme.F.BoxV3

#print axioms Programme.F.BoxV3.MC_S4_hf
#print axioms Programme.F.BoxV3.Ax1Gen_of_refl_hf
#print axioms Programme.F.BoxV3.Th5_S4_hf
