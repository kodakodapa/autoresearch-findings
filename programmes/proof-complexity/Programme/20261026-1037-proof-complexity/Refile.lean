import Programme.«20261025-1627-proof-complexity».OntoF2K4
import Programme.«20261025-1627-proof-complexity».OntoF3K9
import Programme.«20261025-1627-proof-complexity».OntoNS
import Programme.«20261025-1627-proof-complexity».OntoQ7
import Programme.«20261025-1627-proof-complexity».NoDrop
import Programme.«20261025-1627-proof-complexity».DesignExt
import Programme.«20261025-1627-proof-complexity».OntoExt2
import Programme.«20261025-1627-proof-complexity».OntoExt3
import Programme.«20261025-1627-proof-complexity».OntoExt4
import Programme.«20261025-1627-proof-complexity».Hard234ND
import Programme.«20261025-1627-proof-complexity».K5Design

/-! Refiles of the programme's proved C3 claims (owner P25): each theorem restates a library
theorem by its own type and proves it by the library name. -/

namespace Programme.«20261026-1037-proof-complexity».Refile

open Programme.«20261025-1627-proof-complexity»

theorem k101 : type_of% @OntoF2K4.f2_k4_exact := @OntoF2K4.f2_k4_exact
theorem k102 : type_of% @OntoF3K9.f3_plateau := @OntoF3K9.f3_plateau
theorem k103 : type_of% @OntoNS.ns_f3_k9 := @OntoNS.ns_f3_k9
theorem k104 : type_of% @OntoQ7.q7_facts := @OntoQ7.q7_facts
theorem k106 : type_of% @NoDrop.pc_ns := @NoDrop.pc_ns
theorem k110 : type_of% @DesignExt.ext_sound := @DesignExt.ext_sound
theorem k111 : type_of% @OntoExt2.ontoFPHP_no_deg2_all := @OntoExt2.ontoFPHP_no_deg2_all
theorem k113 : type_of% @OntoExt3.ontoFPHP_no_deg3_all := @OntoExt3.ontoFPHP_no_deg3_all
theorem k119 : type_of% @OntoExt4.ontoFPHP_no_deg4_all := @OntoExt4.ontoFPHP_no_deg4_all
theorem k121 : type_of% @OntoF2K4.f2_deg4 := @OntoF2K4.f2_deg4
theorem k122 : type_of% @OntoF2K4.f2_plateau := @OntoF2K4.f2_plateau
theorem k123 : type_of% @OntoF3K9.f3_deg4 := @OntoF3K9.f3_deg4
theorem k124 : (type_of% @OntoNS.ns_pc) ∧ (type_of% @OntoNS.ns_f2_k4) :=
  ⟨@OntoNS.ns_pc, @OntoNS.ns_f2_k4⟩
theorem k124a : type_of% @OntoNS.ns_pc := @OntoNS.ns_pc
theorem k124b : type_of% @OntoNS.ns_f2_k4 := @OntoNS.ns_f2_k4
theorem k125 : type_of% @Hard234ND.hard234_nd := @Hard234ND.hard234_nd
theorem k126 : type_of% @K5Design.no_ns4 := @K5Design.no_ns4

end Programme.«20261026-1037-proof-complexity».Refile

#print axioms Programme.«20261026-1037-proof-complexity».Refile.k101
#print axioms Programme.«20261026-1037-proof-complexity».Refile.k102
#print axioms Programme.«20261026-1037-proof-complexity».Refile.k103
#print axioms Programme.«20261026-1037-proof-complexity».Refile.k104
#print axioms Programme.«20261026-1037-proof-complexity».Refile.k106
#print axioms Programme.«20261026-1037-proof-complexity».Refile.k110
#print axioms Programme.«20261026-1037-proof-complexity».Refile.k111
#print axioms Programme.«20261026-1037-proof-complexity».Refile.k113
#print axioms Programme.«20261026-1037-proof-complexity».Refile.k119
#print axioms Programme.«20261026-1037-proof-complexity».Refile.k121
#print axioms Programme.«20261026-1037-proof-complexity».Refile.k122
#print axioms Programme.«20261026-1037-proof-complexity».Refile.k123
#print axioms Programme.«20261026-1037-proof-complexity».Refile.k124
#print axioms Programme.«20261026-1037-proof-complexity».Refile.k124a
#print axioms Programme.«20261026-1037-proof-complexity».Refile.k124b
#print axioms Programme.«20261026-1037-proof-complexity».Refile.k125
#print axioms Programme.«20261026-1037-proof-complexity».Refile.k126
