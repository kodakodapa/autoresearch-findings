import OpenQuestions.Ax1GenTwoVariant3PlainPoss
/-! # Thread F: hybrid-free `MC_unconditional` in `Ax1GenTwoVariant3PlainPoss`

v4 proves `MC_unconditional` from `OneWorld` (point properties, nominals).  The module's own
`MC_Two` has the identical statement and a hybrid-free proof (through `G_ex_Two`, which v4's
detector certifies), so it is reused here. -/

namespace Programme.«20261022-1314-ontological».F.TwoV3PlainPoss

theorem MC_unconditional_hf : type_of% @MC_unconditional := MC_Two

example : type_of% @MC_unconditional_hf = type_of% @MC_unconditional := rfl

end Programme.«20261022-1314-ontological».F.TwoV3PlainPoss

#print axioms Programme.«20261022-1314-ontological».F.TwoV3PlainPoss.MC_unconditional_hf
