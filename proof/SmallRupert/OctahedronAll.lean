module

public import SmallRupert.Oct9Quad

@[expose] public section

/-!
# Theorem 9.9: every convex octahedron is Rupert (LEMMAS.md L9)

The proof follows L9: an edge view with the antipodal vertex hidden (a *quad
edge*) whose tilted silhouette is robustly unimodal (Lemma 9.3, Cor. 8.0′),
or two touching edges (Lemma 9.4, an axis view), or a planar equator; the
right pair of edges is found in the Gale diagram (Lemmas 9.6–9.8, §9.5), with
the case of two parallel opposite faces treated separately (§9.6).
Everything is reduced to the frame-free Lemma 8.0 / Corollary 8.0′ of
`Tilt.lean`.
-/

namespace SmallRupert

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- **Theorem 9.9.**  Every convex octahedron is Rupert. -/
theorem isRupert_octahedron {a a' b b' c c' : ℝ³} (h : IsOctahedron a a' b b' c c') :
    IsRupert {a, a', b, b', c, c'} := by
  sorry

end SmallRupert

end
