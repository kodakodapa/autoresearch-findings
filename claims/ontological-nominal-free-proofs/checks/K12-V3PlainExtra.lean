import OpenQuestions.Ax1GenTwoVariant3Plain
/-! # Thread F: `AllExist` and `MC_OneWorld` in `Ax1GenTwoVariant3Plain`

Proofs by th (P8, `agents/th/lean/Programme/F/V3Plain.lean`), filed here.  `AllExist` with the
witness `fun z => z = y ∧ ¬(∃ᴱ u, u = z)` instead of a bare `existsAt`; `MC_OneWorld` is the
module's hybrid-free `MC_Two_unconditional` with the reflexivity hypothesis unused. -/

namespace Programme.F.V3PlainExtra

theorem AllExist_pt (nonempty : ∀ w : i, ∃ x : e, x @ᵐ w) (w : i) (y : e) : y @ᵐ w :=
  Classical.byContradiction fun ny =>
    let ⟨g, _, hG⟩ := G_ex_Two nonempty w
    have Eg : E g w := hG E (Ax3 w)
    let φ : e → σ := fun z => (z =ᵐ y) ∧ᵐ ¬ᵐ(∃ᴱ u, u =ᵐ z)
    have ess : Ess φ g w := fun _ _ _ _ =>
      ⟨fun h => (congrFun (congrFun h y) w ▸
          (⟨rfl, fun ⟨_, hu, he⟩ => ny (he ▸ hu)⟩ : φ y w) : ⊥ᵐ w),
       fun z hz ⟨_, hnz⟩ => (hnz ⟨z, hz, rfl⟩).elim⟩
    let ⟨v, hv⟩ := Serial w
    let ⟨z, hz, _, hnz⟩ := Eg φ ess v hv
    hnz ⟨z, hz, rfl⟩

theorem AllExist_hf : type_of% @AllExist := AllExist_pt

theorem MC_OneWorld_hf : type_of% @MC_OneWorld := fun _ φ => MC_Two_unconditional φ

example : type_of% @AllExist_hf = type_of% @AllExist := rfl
example : type_of% @MC_OneWorld_hf = type_of% @MC_OneWorld := rfl

end Programme.F.V3PlainExtra

#print axioms Programme.F.V3PlainExtra.AllExist_hf
#print axioms Programme.F.V3PlainExtra.MC_OneWorld_hf
