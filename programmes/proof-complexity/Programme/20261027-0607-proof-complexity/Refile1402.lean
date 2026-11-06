import Programme.«20261026-1402-proof-complexity».ClassExt
import Programme.«20261026-1402-proof-complexity».GraphSubst
import Programme.«20261026-1402-proof-complexity».ExtLemma
import Programme.«20261026-1402-proof-complexity».ExtLin
import Programme.«20261026-1402-proof-complexity».SymDesign
import Programme.«20261026-1402-proof-complexity».Ext1Exact

/-! Refiles of run-1402 theorems (owner P1, job 1): each theorem restates the library theorem by its
own type and proves it by the library name. -/

namespace Programme.«20261027-0607-proof-complexity».Refile1402

open Programme.«20261026-1402-proof-complexity»

theorem class_sound : type_of% @ClassExt.class_sound := @ClassExt.class_sound
theorem lower_of_graph : type_of% @GraphSubst.lower_of_graph := @GraphSubst.lower_of_graph
theorem no_refutation_of_ext : type_of% @ExtLemma.no_refutation_of_ext := @ExtLemma.no_refutation_of_ext
theorem no_refutation_of_ext_ge : type_of% @ExtLemma.no_refutation_of_ext_ge :=
  @ExtLemma.no_refutation_of_ext_ge
theorem EXT_of_span : type_of% @ExtLin.EXT_of_span := @ExtLin.EXT_of_span
theorem sym_design : type_of% @SymDesign.sym_design := @SymDesign.sym_design
theorem f3_exact : type_of% @Ext1Exact.f3_exact := @Ext1Exact.f3_exact

example : type_of% @class_sound = type_of% @ClassExt.class_sound := rfl
example : type_of% @lower_of_graph = type_of% @GraphSubst.lower_of_graph := rfl
example : type_of% @no_refutation_of_ext = type_of% @ExtLemma.no_refutation_of_ext := rfl
example : type_of% @no_refutation_of_ext_ge = type_of% @ExtLemma.no_refutation_of_ext_ge := rfl
example : type_of% @EXT_of_span = type_of% @ExtLin.EXT_of_span := rfl
example : type_of% @sym_design = type_of% @SymDesign.sym_design := rfl
example : type_of% @f3_exact = type_of% @Ext1Exact.f3_exact := rfl

end Programme.«20261027-0607-proof-complexity».Refile1402

#print axioms Programme.«20261027-0607-proof-complexity».Refile1402.class_sound
#print axioms Programme.«20261027-0607-proof-complexity».Refile1402.lower_of_graph
#print axioms Programme.«20261027-0607-proof-complexity».Refile1402.no_refutation_of_ext
#print axioms Programme.«20261027-0607-proof-complexity».Refile1402.no_refutation_of_ext_ge
#print axioms Programme.«20261027-0607-proof-complexity».Refile1402.EXT_of_span
#print axioms Programme.«20261027-0607-proof-complexity».Refile1402.sym_design
#print axioms Programme.«20261027-0607-proof-complexity».Refile1402.f3_exact
