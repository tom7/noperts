module

public import Nopert231.WedgeCoverData
public import Pipeline.AtlasProjectiveView

@[expose] public section

/-!
# Candidate #231's view cover

`WedgeCoverData` (written by `search/common/emit-wedge-cover.py`, as for the
other solids) lists the code triangles, the triangle they cover
(`baseTriangle`, codebdd.json's fundamental domain) and the tree whose
natively checked `coverValid` proves the cover. The base triangle is the
upper view wedge of the fivefold pipeline (checked by the kernel).
-/

namespace Nopert231.WedgeCover

open Noperts.Pipeline Noperts.Pipeline.WedgeCover Noperts.Atlas.ProjectiveView

/-- The base triangle is the upper view wedge. -/
theorem baseTriangle_eq :
    toReal AtlasProjectiveView.upperWedgeTriangle = toReal baseTriangle := by
  congr 1

end Nopert231.WedgeCover

end
