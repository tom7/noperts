import Septopert
import DeltoidalHexecontahedron
import PentagonalHexecontahedron
import SnubDodecahedron
import SnubDodecahedron.NativeExecutable
import PentagonalHexecontahedron.NativeExecutable
import DeltoidalHexecontahedron.NativeExecutable
import Nopert231
import ProofOfMainTheorem

/-!
# No solid model is in scope by importing a solid

Every solid provides its `Noperts.Pipeline.SolidModel` as a `scoped instance`
in its own namespace. A file that imports several solids (like this one, or
`ProofOfMainTheorem`) must not see any of them unless it opens a solid's
namespace, so that no statement silently depends on which instance happens
to be found. This file fails to build if an instance is found here.
-/

open Lean Meta in
#eval show MetaM Unit from do
  if (← synthInstance? (mkConst ``Noperts.Pipeline.SolidModel)).isSome then
    throwError "a SolidModel instance is in scope without opening a solid's namespace"

/-! The native local-table checker's certificate-row check
(`SparseLocalViewTree.CertificateViewCheck`) is the snub dodecahedron's
tangent-cone check inside its namespace, and the default (every vertex) for
the other solids. -/

section
open SnubDodecahedron
example : (inferInstance : Noperts.Pipeline.SparseLocalViewTree.CertificateViewCheck) =
    SnubDodecahedron.certificateViewCheck := rfl
end

section
open PentagonalHexecontahedron
example : (inferInstance : Noperts.Pipeline.SparseLocalViewTree.CertificateViewCheck) =
    Noperts.Pipeline.SparseLocalViewTree.CertificateViewCheck.allVertices := rfl
end

section
open DeltoidalHexecontahedron
example : (inferInstance : Noperts.Pipeline.SparseLocalViewTree.CertificateViewCheck) =
    Noperts.Pipeline.SparseLocalViewTree.CertificateViewCheck.allVertices := rfl
end
