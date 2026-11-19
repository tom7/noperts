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

theorem exists_rimB (m : Fin 7) (h1 : m ≠ 1) (h3 : m ≠ 3) : ∃ j, m = rimB j := by
  revert m; decide

theorem foot_above {L s zc zi zj : ℝ} (h0 : 0 < s) (h1 : s < L) (hi : zi < zc) (hj : zj < zc) :
    L * zc ≠ (L - s) * zi + s * zj := by
  intro h
  nlinarith [mul_pos (sub_pos.mpr h1) (sub_pos.mpr hi), mul_pos h0 (sub_pos.mpr hj)]

theorem foot_below {L s zc zi zj : ℝ} (h0 : 0 < s) (h1 : s < L) (hi : zc < zi) (hj : zc < zj) :
    L * zc ≠ (L - s) * zi + s * zj := by
  intro h
  nlinarith [mul_pos (sub_pos.mpr h1) (sub_pos.mpr hi), mul_pos h0 (sub_pos.mpr hj)]

theorem ds_B {z : ZMod 5 → ℝ} (r1 : z 3 < z 4) (r2 : z 3 < z 0) (r3 : z 3 < z 1) (r4 : z 2 < z 3) :
    DepthSepZ z 1 3 := by
  have hv : ((1 : ZMod 5) - 3).val = 3 := by decide
  unfold DepthSepZ; left; rw [hv]
  refine ⟨fun s hs1 hs2 => ?_, fun s hs1 hs2 => ?_⟩ <;> interval_cases s <;>
    first | exact r1 | exact r2 | exact r3 | exact r4

/-- **Leaf B, rim `0 4 6 2 5`, wedge `z6 < z2 < z0`.**  Pair (edge `4 → 6`, far corner `2`). -/
theorem isRupert_leafB_04625 {x : Fin 7 → ℝ³} {u : ℝ³} (hu : u ≠ 0)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 →
      0 < det3 (x (rimB (i + 1)) - x (rimB i)) (x (rimB j) - x (rimB i)) u)
    (hrest : ∀ v ∈ ({1, 3} : Finset (Fin 7)), ∀ i,
      0 < det3 (x (rimB (i + 1)) - x (rimB i)) (x v - x (rimB i)) u)
    (r1 : ⟪x 6, u⟫ < ⟪x 2, u⟫) (r2 : ⟪x 2, u⟫ < ⟪x 0, u⟫) (r3 : ⟪x 0, u⟫ < ⟪x 4, u⟫)
    (r4 : ⟪x 0, u⟫ < ⟪x 5, u⟫) (r5 : ⟪x 4, u⟫ ≠ ⟪x 5, u⟫)
    (hpp : ParPairAt (fun i => x (rimB i)) u 1 3)
    (c : ZMod 5 → ZMod 5) (hc1 : c 1 = 3) (hc3 : c 3 = 2) (hc0 : c 0 = 2 ∨ c 0 = 3)
    (hc4 : c 4 = 2 ∨ c 4 = 3)
    (hanti : ∀ i l, l ≠ c i → det3 (x (rimB (i + 1)) - x (rimB i)) (x (rimB l) - x (rimB i)) u
        < det3 (x (rimB (i + 1)) - x (rimB i)) (x (rimB (c i)) - x (rimB i)) u)
    (hfoot46 : 0 < scr u (x 2 - x 4) (x 6 - x 4) → scr u (x 2 - x 4) (x 6 - x 4) < scr u (x 6 - x 4) (x 6 - x 4) →
      scr u (x 6 - x 4) (x 6 - x 4) * ⟪x 2, u⟫ <
        (scr u (x 6 - x 4) (x 6 - x 4) - scr u (x 2 - x 4) (x 6 - x 4)) * ⟪x 4, u⟫
          + scr u (x 2 - x 4) (x 6 - x 4) * ⟪x 6, u⟫) :
    IsRupert (Finset.univ.image x) := by
  classical
  have hk : 3 ≤ 5 := by norm_num
  have hz : DepthSepZ (fun i => ⟪x (rimB i), u⟫) 1 3 :=
    ds_B (z := fun i => ⟪x (rimB i), u⟫) (by simpa [rimB] using (r2.trans r4))
      (by simpa [rimB] using r2) (by simpa [rimB] using r2.trans r3) (by simpa [rimB] using r1)
  have hi5 : ∀ i : ZMod 5, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by decide
  have hinj : Function.Injective fun i => ⟪x (rimB i), u⟫ := by
    intro i j h
    have e0 : ⟪x (rimB 0), u⟫ = ⟪x 0, u⟫ := rfl
    have e1 : ⟪x (rimB 1), u⟫ = ⟪x 4, u⟫ := rfl
    have e2 : ⟪x (rimB 2), u⟫ = ⟪x 6, u⟫ := rfl
    have e3 : ⟪x (rimB 3), u⟫ = ⟪x 2, u⟫ := rfl
    have e4 : ⟪x (rimB 4), u⟫ = ⟪x 5, u⟫ := rfl
    simp only at h
    rcases hi5 i with rfl | rfl | rfl | rfl | rfl <;> rcases hi5 j with rfl | rfl | rfl | rfl | rfl <;>
      simp only [e0, e1, e2, e3, e4] at h <;>
      first | rfl | (exfalso; linarith) | (exact absurd h r5) | (exact absurd h.symm r5)
  have hd0 : ∀ a : ℝ³, det3 a 0 u = 0 := fun a => by simp only [det3_expand]; simp
  have hdd : ∀ a : ℝ³, det3 a a u = 0 := fun a => by simp only [det3_expand]; ring
  have hc2 : c 2 = 0 ∨ c 2 = 1 ∨ c 2 = 4 := by
    have e : (2 : ZMod 5) + 1 = 3 := by decide
    have h2 : c 2 ≠ 2 := by
      intro h
      have := hanti 2 3 (by rw [h]; decide)
      rw [h, e, sub_self, hdd, hd0] at this
      exact lt_irrefl _ this
    have h3 : c 2 ≠ 3 := by
      intro h
      have := hanti 2 2 (by rw [h]; decide)
      rw [h, e, sub_self, hd0, hdd] at this
      exact lt_irrefl _ this
    rcases hi5 (c 2) with h | h | h | h | h <;> simp_all
  have hnd : NoHDNRim (fun i => x (rimB i)) u := by
    refine HDNRim.noHDNRim_of_anti hk hcyc hinj c hanti ?_
    intro i h0 h1
    rcases hi5 i with rfl | rfl | rfl | rfl | rfl
    · rcases hc0 with h | h <;> rw [h] at h0 h1 ⊢
      · exact foot_below h0 h1 (by show ⟪x 6, u⟫ < ⟪x 0, u⟫; linarith)
          (by show ⟪x 6, u⟫ < ⟪x 4, u⟫; linarith)
      · exact foot_below h0 h1 (by show ⟪x 2, u⟫ < ⟪x 0, u⟫; linarith)
          (by show ⟪x 2, u⟫ < ⟪x 4, u⟫; linarith)
    · rw [hc1] at h0 h1 ⊢
      exact ne_of_lt (hfoot46 h0 h1)
    · rcases hc2 with h | h | h <;> rw [h] at h0 h1 ⊢
      · exact foot_above h0 h1 (by show ⟪x 6, u⟫ < ⟪x 0, u⟫; linarith)
          (by show ⟪x 2, u⟫ < ⟪x 0, u⟫; linarith)
      · exact foot_above h0 h1 (by show ⟪x 6, u⟫ < ⟪x 4, u⟫; linarith)
          (by show ⟪x 2, u⟫ < ⟪x 4, u⟫; linarith)
      · exact foot_above h0 h1 (by show ⟪x 6, u⟫ < ⟪x 5, u⟫; linarith)
          (by show ⟪x 2, u⟫ < ⟪x 5, u⟫; linarith)
    · rw [hc3] at h0 h1 ⊢
      exact foot_below h0 h1 (by show ⟪x 6, u⟫ < ⟪x 2, u⟫; linarith)
        (by show ⟪x 6, u⟫ < ⟪x 5, u⟫; linarith)
    · rcases hc4 with h | h <;> rw [h] at h0 h1 ⊢
      · exact foot_below h0 h1 (by show ⟪x 6, u⟫ < ⟪x 5, u⟫; linarith)
          (by show ⟪x 6, u⟫ < ⟪x 0, u⟫; linarith)
      · exact foot_below h0 h1 (by show ⟪x 2, u⟫ < ⟪x 5, u⟫; linarith)
          (by show ⟪x 2, u⟫ < ⟪x 0, u⟫; linarith)
  refine isRupert_of_rimView_depthSeparated_rim _ u hu hk (fun i => x (rimB i)) ?_ hcyc ?_
    (depthSepAt_of hpp hz) hnd
  · intro i; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  · intro v hv hvp i
    obtain ⟨m, -, rfl⟩ := Finset.mem_image.mp hv
    have hm : m = 1 ∨ m = 3 := by
      by_contra hne
      push Not at hne
      obtain ⟨hn1, hn3⟩ := hne
      have : ∃ j, m = rimB j := by
        exact exists_rimB m hn1 hn3
      obtain ⟨j, hj⟩ := this
      exact hvp j (by rw [hj])
    exact hrest m (by rcases hm with rfl | rfl <;> simp) i

end LeafB24
end Minimality
