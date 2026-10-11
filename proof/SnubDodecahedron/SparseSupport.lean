module

public import Pipeline.SparseSupport
public import SnubDodecahedron.SolidModel
public import SnubDodecahedron.GeneratedTangentCones
public import SnubDodecahedron.TangentCones

@[expose] public section

/-!
# Sparse support checks for the snub dodecahedron

The rational model of the snub dodecahedron has at most seven tangent-cone
generators at each vertex (`TangentCones`), and the kernel-checked table
`GeneratedTangentCones.table_valid_kernel` shows that every other vertex lies
in the cone they span. So its native checker checks the support condition of
the identity-tube certificate rows against seven vertices instead of sixty
(`Pipeline/SparseSupport.lean`). Both instances below are scoped: in effect
inside `namespace SnubDodecahedron` only.
-/

namespace SnubDodecahedron

open Noperts Noperts.Pipeline

theorem supportError_pos : 0 < AtlasProjectiveLocalCertificate.supportError := by
  decide +kernel

/-- The snub dodecahedron's tangent-cone generators, for the sparse support
check. -/
@[reducible] scoped instance tangentCones : Noperts.Pipeline.SparseSupport.TangentCones where
  supportGenerator := SnubDodecahedron.SparseSupport.supportGenerator
  tangent base target h :=
    ⟨(GeneratedTangentCones.table base target).generator,
      (GeneratedTangentCones.table base target).coefficient,
      GeneratedTangentCones.table_valid_kernel base target h⟩
  supportError_pos := supportError_pos

/-- The snub dodecahedron's native checker validates certificate rows by
`Box.SparseViewValid` (tangent-cone generators; sound by the kernel-checked
tangent-cone table) instead of the default check against every vertex. -/
@[reducible] scoped instance certificateViewCheck :
    SparseLocalViewTree.CertificateViewCheck :=
  Noperts.Pipeline.SparseSupport.TangentCones.certificateViewCheck

end SnubDodecahedron

end
