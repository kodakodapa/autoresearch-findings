import OpenQuestions.Ax1GenRigidVariant2
/-! # Thread F: hybrid-free `L_R` in `Ax1GenRigidVariant2`, no condition on positivity

Proof idea due to th (board P68, `agents/th/lean/Programme/F/Rigid.lean`); re-stated here in a
separate namespace for the strict full-name check.  v4's object-language witness `PosGlobal`
(`A(P ψ)`) was only known to work under `RigidPos`.  For every `ψ` the guarded property
`λx. P ψ →ᵐ ψ x` is globally positive (`Ax2a`, `Ax2b`, `Ax4`) and agrees with `ψ` wherever `ψ` is
positive, which gives the missing half of `ConjR G PosGlobal`.  Logic **K**, no frame condition. -/

namespace Programme.«20261022-1314-ontological».F.RigidHF

/-- `λx. P ψ →ᵐ ψ x` is positive at every world. -/
theorem guard_pos_hf (ψ : e → σ) : PosGlobal (fun x => P ψ →ᵐ ψ x) :=
  posGlobal_of fun u =>
    Classical.byCases
      (fun hP : P ψ u => Ax4 ψ _ u ⟨hP, fun _ _ _ _ hy _ => hy⟩)
      (fun hP : ¬ P ψ u => Ax4 (~ᵐψ) _ u ⟨(Ax2a' ψ u).1 hP, fun v hv _ _ _ hPv =>
        absurd ⟨hPv, Ax2b _ u ((Ax2a' ψ u).1 hP) v hv⟩ (Ax2a ψ v).2⟩)

/-- Hybrid-free proof of the module's `L_R` (same statement, via `type_of%`). -/
theorem L_R_hf : type_of% @L_R := fun h w =>
  h PosGlobal G w
    ⟨fun _ hψ => posGlobal_at hψ w,
     fun v _hv _z _hz =>
       ⟨fun hG ψ hψ => hG ψ (posGlobal_at hψ v),
        fun hall ψ hPv => hall _ (guard_pos_hf ψ) hPv⟩⟩

example : type_of% @L_R_hf = type_of% @L_R := rfl

end Programme.«20261022-1314-ontological».F.RigidHF

#print axioms Programme.«20261022-1314-ontological».F.RigidHF.L_R_hf
#print axioms Programme.«20261022-1314-ontological».F.RigidHF.guard_pos_hf
