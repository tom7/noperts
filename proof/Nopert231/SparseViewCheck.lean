module

public import Pipeline.SparseSupport
public import Nopert231.SolidModel
public import Nopert231.GeneratedTangentCones

@[expose] public section

/-!
# Sparse support checks for candidate #231

The rational model of candidate #231 has at most seven tangent-cone
generators at each vertex (`SparseSupport.supportGenerator`), and the
kernel-checked table `GeneratedTangentCones.table_valid_kernel` shows that
every other vertex lies in the cone they span. So its native checker checks
the support condition of the identity-tube certificate rows against seven
vertices instead of twenty (`Pipeline/SparseSupport.lean`). Both instances
below are scoped: in effect inside `namespace Nopert231` only.
-/

namespace Nopert231

open Noperts Noperts.Pipeline

theorem supportError_pos : 0 < AtlasProjectiveLocalCertificate.supportError := by
  decide +kernel

/-- Candidate #231's tangent-cone generators, for the sparse support check. -/
@[reducible] scoped instance tangentCones : Noperts.Pipeline.SparseSupport.TangentCones where
  supportGenerator := Nopert231.SparseSupport.supportGenerator
  tangent base target h :=
    ⟨(GeneratedTangentCones.table base target).generator,
      (GeneratedTangentCones.table base target).coefficient,
      GeneratedTangentCones.table_valid_kernel base target h⟩
  supportError_pos := supportError_pos

/-- Candidate #231's native checker validates certificate rows by
`Box.SparseViewValid` (tangent-cone generators; sound by the kernel-checked
tangent-cone table) instead of the default check against every vertex. -/
@[reducible] scoped instance certificateViewCheck :
    SparseLocalViewTree.CertificateViewCheck :=
  Noperts.Pipeline.SparseSupport.TangentCones.certificateViewCheck

end Nopert231

end
