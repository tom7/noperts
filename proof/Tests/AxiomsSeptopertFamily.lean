import SeptopertFamily

/-!
# The Septopert family theorem uses only the standard axioms

In its own file so that it does not depend on the Septopert modules; see
`Tests/Axioms.lean` for the others.
-/

open Lean Elab Command in
elab "#assert_standard_axioms " id:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let axioms ← liftCoreM <| collectAxioms name
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  unless axioms.qsort Name.lt == expected.qsort Name.lt do
    throwError "{name} depends on {axioms}"

#assert_standard_axioms SeptopertFamily.not_isNopert_of_familyHeight_lt_seven
#assert_standard_axioms SeptopertFamily.not_isNopert_of_sub_le_twelve
