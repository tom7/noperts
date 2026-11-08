import ChippedM18

/-!
# ChippedM18 uses only the standard axioms

ChippedM18 cannot be imported together with the Septopert (both define
`MatrixPose.mirrorTie`), so its check is in its own file; see `Tests/Axioms.lean`
for the others.
-/

open Lean Elab Command in
elab "#assert_standard_axioms " id:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let axioms ← liftCoreM <| collectAxioms name
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  unless axioms.qsort Name.lt == expected.qsort Name.lt do
    throwError "{name} depends on {axioms}"

#assert_standard_axioms ChippedM18.isNopert_of_certificatesValid
