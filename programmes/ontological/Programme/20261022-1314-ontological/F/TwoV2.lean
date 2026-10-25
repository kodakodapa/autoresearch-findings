import OpenQuestions.Ax1GenTwoVariant2
/-! # Thread F: hybrid-free `Ax1Gen_of_Two` and `Two_equivalent` in `Ax1GenTwoVariant2`

v4's proof of `Ax1Gen_of_Two` goes through `R_Id` (modal collapse at the nominal
`fun u => u = w`).  Here the singleton and empty instances are carried to every successor by
modal collapse at object-language sentences built from `Φ` and the single member `ψ₀`:
`Φ ψ₀` and `∀ᵐ ψ, Φ ψ →ᵐ ψ =ᵐ ψ₀` (singleton), `∀ᵐ ψ, ¬ᵐ Φ ψ` (empty).  Collapse itself is the
module's `MC_Two_unconditional`, which the detector certifies.  No frame condition, no nominal. -/

namespace Programme.«20261022-1314-ontological».F.TwoV2

/-- Hybrid-free proof of the module's `Ax1Gen_of_Two` (same statement, via `type_of%`). -/
theorem Ax1Gen_of_Two_hf : type_of% @Ax1Gen_of_Two := by
  intro Φ φ w ⟨pos, conj⟩
  by_cases two : TwoMembers Φ w
  · exact Ax1GenTwo Φ φ w ⟨⟨two, pos⟩, conj⟩
  by_cases hex : (∃ᵐ ψ, Φ ψ) w
  · obtain ⟨ψ₀, m0⟩ := hex
    have uniq : (∀ᵐ ψ, Φ ψ →ᵐ (ψ =ᵐ ψ₀)) w := fun ψ hψ =>
      Classical.byContradiction fun hne => two ⟨ψ, ψ₀, hψ, m0, hne⟩
    have incl : (ψ₀ ⊃ᴺ φ) w := fun v rv y ay h =>
      have uv := MC_Two_unconditional (∀ᵐ ψ, Φ ψ →ᵐ (ψ =ᵐ ψ₀)) w uniq v rv
      (conj v rv y ay).2 (fun ψ hψ => by
        have hψ0 : ψ = ψ₀ := uv ψ hψ
        rw [hψ0]; exact h)
    exact Ax4 ψ₀ φ w ⟨pos ψ₀ m0, incl⟩
  · have none : (∀ᵐ ψ, ¬ᵐ (Φ ψ)) w := fun ψ hψ => hex ⟨ψ, hψ⟩
    have incl : ((fun _ : e => ⊤ᵐ) ⊃ᴺ φ) w := fun v rv y ay _ =>
      have nv := MC_Two_unconditional (∀ᵐ ψ, ¬ᵐ (Φ ψ)) w none v rv
      (conj v rv y ay).2 (fun ψ hψ => (nv ψ hψ).elim)
    exact Ax4 _ φ w ⟨PTop w, incl⟩

/-- Hybrid-free proof of the module's `Two_equivalent` (same statement, via `type_of%`). -/
theorem Two_equivalent_hf : type_of% @Two_equivalent :=
  ⟨fun _ => Ax1Gen_of_Two_hf, Two_weaker⟩

example : type_of% @Ax1Gen_of_Two_hf = type_of% @Ax1Gen_of_Two := rfl
example : type_of% @Two_equivalent_hf = type_of% @Two_equivalent := rfl

/-- Hybrid-free `loc_of_conj`: no reflexivity.  Seriality gives a successor `v`; modal collapse
carries `z`'s actuality to `v` and the negation of the local equivalence (an `L`-sentence with
the individual `z` free) from `w` to `v`, where `conj` refutes it. -/
theorem loc_of_conj_hf : type_of% @loc_of_conj := by
  intro φ Φ w z conj a
  obtain ⟨v, rv⟩ := Serial w
  have av : (∃ᴱ y, y =ᵐ z) v :=
    MC_Two_unconditional (∃ᴱ y, y =ᵐ z) w ⟨z, a, rfl⟩ v rv
  obtain ⟨y, ay, hyz⟩ := av
  have hyz' : y = z := hyz
  subst hyz'
  refine Classical.byContradiction fun hn => ?_
  exact MC_Two_unconditional (¬ᵐ(φ y ↔ᵐ (∀ᵐ ψ, Φ ψ →ᵐ ψ y))) w hn v rv (conj v rv y ay)

/-- Hybrid-free `P_of_conj`. -/
theorem P_of_conj_hf : type_of% @P_of_conj := by
  intro Φ φ w pos conj
  exact Ax1Gen_of_Two_hf Φ φ w ⟨pos, conj⟩

/-- Hybrid-free `ae_Two_nominal`: the module's own `ae_Two`. -/
theorem ae_Two_nominal_hf : type_of% @ae_Two_nominal := ae_Two

/-- Hybrid-free `G_ex_Two_unconditional_nominal`. -/
theorem G_ex_Two_unconditional_nominal_hf : type_of% @G_ex_Two_unconditional_nominal :=
  G_ex_Two ae_Two

/-- Hybrid-free `only_top_and_empty_domain_False`: `ae_Two` refutes the empty domain. -/
theorem only_top_and_empty_domain_False_hf : type_of% @only_top_and_empty_domain_False := by
  intro w _ empty
  exact empty (ae_Two w)

/-- Hybrid-free `only_top_and_empty_domain`. -/
theorem only_top_and_empty_domain_hf : type_of% @only_top_and_empty_domain := by
  intro w _ empty
  exact empty (ae_Two w)

example : type_of% @loc_of_conj_hf = type_of% @loc_of_conj := rfl
example : type_of% @P_of_conj_hf = type_of% @P_of_conj := rfl
example : type_of% @ae_Two_nominal_hf = type_of% @ae_Two_nominal := rfl
example : type_of% @G_ex_Two_unconditional_nominal_hf = type_of% @G_ex_Two_unconditional_nominal := rfl
example : type_of% @only_top_and_empty_domain_False_hf = type_of% @only_top_and_empty_domain_False := rfl
example : type_of% @only_top_and_empty_domain_hf = type_of% @only_top_and_empty_domain := rfl

end Programme.«20261022-1314-ontological».F.TwoV2

#print axioms Programme.«20261022-1314-ontological».F.TwoV2.Ax1Gen_of_Two_hf
#print axioms Programme.«20261022-1314-ontological».F.TwoV2.Two_equivalent_hf
#print axioms Programme.«20261022-1314-ontological».F.TwoV2.loc_of_conj_hf
#print axioms Programme.«20261022-1314-ontological».F.TwoV2.P_of_conj_hf
#print axioms Programme.«20261022-1314-ontological».F.TwoV2.ae_Two_nominal_hf
#print axioms Programme.«20261022-1314-ontological».F.TwoV2.G_ex_Two_unconditional_nominal_hf
#print axioms Programme.«20261022-1314-ontological».F.TwoV2.only_top_and_empty_domain_False_hf
#print axioms Programme.«20261022-1314-ontological».F.TwoV2.only_top_and_empty_domain_hf
