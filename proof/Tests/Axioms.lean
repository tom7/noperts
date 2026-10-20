import Septopert
import DeltoidalHexecontahedron
import PentagonalHexecontahedron
import SnubDodecahedron
import SnubCube
import Nopert231
import Minimality
import ProofOfMainTheorem

/-!
# The headline theorems use only the standard axioms

This file fails to build unless each headline theorem depends on exactly
`propext`, `Classical.choice` and `Quot.sound` (no `sorryAx`, no
`Lean.ofReduceBool` from `native_decide`, no added axioms).
-/

open Lean Elab Command in
elab "#assert_standard_axioms " id:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let axioms ← liftCoreM <| collectAxioms name
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  unless axioms.qsort Name.lt == expected.qsort Name.lt do
    throwError "{name} depends on {axioms}"

#assert_standard_axioms Septopert.isNopert_of_certificatesValid
#assert_standard_axioms DeltoidalHexecontahedron.isNopert_of_certificatesValid
#assert_standard_axioms PentagonalHexecontahedron.isNopert_of_certificatesValid
#assert_standard_axioms SnubDodecahedron.isNopert_of_certificatesValid
#assert_standard_axioms SnubCube.isNopert_of_certificatesValid
#assert_standard_axioms Nopert231.isNopert_of_certificatesValid
#assert_standard_axioms seven_le_card_of_isNopert
#assert_standard_axioms facet_card_le_four_of_isNopert
#assert_standard_axioms not_four_quad_facets_of_isNopert
#assert_standard_axioms not_two_quad_facets_vertex_of_isNopert
#assert_standard_axioms not_facets_vertex_triShadow_of_isNopert
#assert_standard_axioms not_facets_edge_triShadow_of_isNopert
#assert_standard_axioms not_facets_edge_tri_triShadow_of_isNopert
#assert_standard_axioms Minimality.isRupert_of_pos_combinations
#assert_standard_axioms Minimality.sum_cross2_shear
#assert_standard_axioms Minimality.three_level_resultants
#assert_standard_axioms Minimality.three_level_torque
#assert_standard_axioms Minimality.screenVel_axis
#assert_standard_axioms Minimality.isRupert_of_axis
#assert_standard_axioms Minimality.isRupert_of_axis_image
#assert_standard_axioms Minimality.convex_setOf_isInwardAt
#assert_standard_axioms Minimality.isRupert_of_axis_helly
#assert_standard_axioms Minimality.odd_card_sign_changes
#assert_standard_axioms Minimality.tie_core_right
#assert_standard_axioms Minimality.isRupert_of_tie_right
#assert_standard_axioms Minimality.isRupert_of_tie_right_neg
#assert_standard_axioms Minimality.sum_cross2_collapse
#assert_standard_axioms not_type10_of_isNopert
#assert_standard_axioms not_type19_of_isNopert
#assert_standard_axioms not_type13_of_isNopert
#assert_standard_axioms not_type17_of_isNopert
#assert_standard_axioms not_type27_of_isNopert
#assert_standard_axioms not_type23_of_isNopert
#assert_standard_axioms not_type25_of_isNopert
#assert_standard_axioms not_type26_of_isNopert
#assert_standard_axioms not_type12_of_isNopert
#assert_standard_axioms not_type22_of_isNopert
#assert_standard_axioms not_type28_of_isNopert
#assert_standard_axioms not_type05_of_isNopert
#assert_standard_axioms minimalNopert_of_certificatesValid
