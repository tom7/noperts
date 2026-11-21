module

public import Minimality.LinkDSP24

@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace

namespace Minimality
open HDNApex

/-- **Theorem 8.10 on a rim at a generic view (no vertex behind a rim vertex).**  The rim `p`
passes all triple tests at `u`, every other point of `V` is strictly inside, the rim has a
depth-separated parallel pair (`DepthSepAt`) and no horizontal double normal of the rim cycle
(`NoHDNRim`): `V` is Rupert, whether or not the rim depths are unimodal.  The case `M = ∅`
of `isRupert_of_chords_depthSeparated`, as `isRupert_of_edgeView_depthSeparated_rim` is the
edge-view case. -/
theorem isRupert_of_rimView_depthSeparated_rim (V : Finset ℝ³) (u : ℝ³) (hu : u ≠ 0)
    {k : ℕ} [NeZero k] (hk : 3 ≤ k) (p : ZMod k → ℝ³) (hpV : ∀ i, p i ∈ V)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < det3 (p (i + 1) - p i) (p j - p i) u)
    (hrest : ∀ v ∈ V, (∀ j, v ≠ p j) → ∀ i, 0 < det3 (p (i + 1) - p i) (v - p i) u)
    {a c : ZMod k} (hds : DepthSepAt p u a c) (hnd : NoHDNRim p u) : IsRupert V := by
  classical
  obtain ⟨R, hR, ρ, hρ, hRu⟩ := exists_rotation_to_ez_pos u hu
  have hp : IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (p i))) := by
    refine ⟨hk, fun i j hi hj => ?_⟩
    simp only [proj_rot_sub]
    exact cross2_proj_rot_pos hR hρ hRu (hcyc i j hi hj)
  refine isRupert_of_chords_depthSeparated V ∅ R hR hρ hRu p hpV (fun i => Finset.notMem_empty _)
    hp ?_ (isDepthSeparatedPair_of_depthSepAt hR hρ hRu p hk hcyc hds)
    (hnd R hR ρ hρ.ne' hRu hp) (fun m hm => absurd hm (Finset.notMem_empty _))
  intro v hv _ hvp
  refine hp.mem_interior_of_left fun i => ?_
  simp only [proj_rot_sub]
  exact cross2_proj_rot_pos hR hρ hRu (hrest v hv hvp i)

namespace LeafB24

/-- The rim `0 4 6 2 5`. -/
def rimB : ZMod 5 → Fin 7 := ![0, 4, 6, 2, 5]



theorem foot_above {L s zc zi zj : ℝ} (h0 : 0 < s) (h1 : s < L) (hi : zi < zc) (hj : zj < zc) :
    L * zc ≠ (L - s) * zi + s * zj := by
  intro h
  nlinarith [mul_pos (sub_pos.mpr h1) (sub_pos.mpr hi), mul_pos h0 (sub_pos.mpr hj)]

theorem foot_below {L s zc zi zj : ℝ} (h0 : 0 < s) (h1 : s < L) (hi : zc < zi) (hj : zc < zj) :
    L * zc ≠ (L - s) * zi + s * zj := by
  intro h
  nlinarith [mul_pos (sub_pos.mpr h1) (sub_pos.mpr hi), mul_pos h0 (sub_pos.mpr hj)]


end LeafB24
end Minimality
