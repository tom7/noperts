import SeptopertShell

/-!
# The Septopert island is enclosed (`native_decide`)

`SeptopertShell.islandEnclosed : IslandEnclosed` as a theorem in the environment, from the inlined certificate
`SeptopertShell.shellText` (`SeptopertShell/data/shell.txt`), checked by `native_decide` while this file builds
(about 75 s wall and 7 GB on 2026-11-09; the slab checks run as parallel tasks, `ClosureData.checkPar`).

This trusts the Lean compiler and runtime, like the native executable `checkSeptopertShell`, which checks the same
certificate and instantiates the same statement at run time. Unlike the executable it gives a theorem that other
files can import. The headline theorems of the repository use only the standard axioms (`Tests/Axioms.lean`) and do
not import this file; here the assertion at the end allows exactly the standard axioms plus the auxiliary axioms
`native_decide` creates.
-/

namespace SeptopertShell

/-- The inlined certificate, parsed (`none` if it does not parse). -/
def shellData? : Option ClosureData :=
  match parseShell shellText with
  | .ok C => some C
  | .error _ => none

theorem shellData?_isSome : shellData?.isSome = true := by native_decide

/-- The inlined certificate. -/
def shellData : ClosureData := shellData?.get shellData?_isSome

theorem shellData_classicOk : shellData.classicOk = true := by native_decide

theorem shellData_checkPar : shellData.checkPar 32 = true := by native_decide

/-- **The Septopert island is enclosed by Rupert shapes** (`native_decide` on the inlined certificate). -/
theorem islandEnclosed : IslandEnclosed :=
  islandEnclosed_of_closureData shellData (shellData.check_of_checkPar shellData_checkPar) shellData_classicOk

end SeptopertShell

open Lean Elab Command in
/-- Fails unless the theorem depends only on the standard axioms and `native_decide`'s auxiliary axioms. -/
elab "#assert_native_axioms " id:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let axioms ← liftCoreM <| collectAxioms name
  let standard := #[``propext, ``Classical.choice, ``Quot.sound]
  for a in axioms do
    unless standard.contains a || (a.toString.splitOn "._native.native_decide.").length > 1 do
      throwError "{name} depends on {a}"

#assert_native_axioms SeptopertShell.islandEnclosed
