module

public import Pipeline.WedgeCover

@[expose] public section

/-!
# Covering the upper view wedge by triangles (names for the generated data)

The decision-tree certificate that a list of triangles covers
`upperWedgeTriangle` is `Pipeline/WedgeCover.lean`. Candidate #231's
generated tree (`WedgeCoverData`, written by
`search/nopert231/scripts/emit-wedge-cover.py`) imports this module and is
written in `namespace Nopert231.WedgeCover`, naming `Node`, `Tri`,
`wedgeConstraints`, `wedge_covered` and `AtlasProjectiveView.upperWedgeTriangle`
unqualified. This module makes those names refer to the pipeline's, so that
the generated file stays as the generator writes it.
-/

namespace Nopert231.WedgeCover

export Noperts.Pipeline.WedgeCover (V Tri Node wedgeConstraints wedge_covered)

end Nopert231.WedgeCover

namespace Nopert231.AtlasProjectiveView

export Noperts.Pipeline.AtlasProjectiveView (upperWedgeTriangle)

end Nopert231.AtlasProjectiveView

end
