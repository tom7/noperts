module

public import SmallRupert.Oct9Gale

@[expose] public section

/-!
# Theorem 9.9, the parallel case `f = 0` (LEMMAS.md §9.6)

With normalized labels (`κ_A, κ_B, κ_C > 0`), `f = g_a + g_b + g_c = 0`
means that the opposite faces `abc` and `a'b'c'` are parallel.  Each pair `W`
gives a weak crossed pair whose edges are not bad (same argument as §9.5);
Lemma 9.11 shows each such edge gives a passage unless it is touching or its
lateral edge is parallel to the common normal, and at most one edge of the
octahedron is parallel to it.
-/

namespace SmallRupert

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- **Theorem 9.9, case `f = 0`** (§9.6). -/
theorem isRupert_octahedron_parallel {a a' b b' c c' : ℝ³} (h : IsOctahedron a a' b b' c c')
    (G : GaleData a a' b b' c c') (hκa : 0 < galeD G.l G.m a a')
    (hκb : 0 < galeD G.l G.m b b') (hκc : 0 < galeD G.l G.m c c')
    (hf : G.l a + G.l b + G.l c = 0 ∧ G.m a + G.m b + G.m c = 0) :
    IsRupert {a, a', b, b', c, c'} := by
  sorry

end SmallRupert

end
