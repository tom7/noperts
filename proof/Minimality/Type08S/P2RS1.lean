module

public import Minimality.Type08S.P2RS0

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# G-RS: Theorem D (22.3) with a robustly unimodal rim (ties allowed)

`isRupert_of_slide_robust` = `isRupert_of_slideP` with `hinj0 ∧ UniOrSep` replaced by robust unimodality at `u₀`;
robustness passes to `u₀ + t e` for small `t > 0` (`IsRobustUnimodal.refine`), the rim has no horizontal double
normal there (`eventually_noHDNRim_slide`), and the end is 18.3 (`isRupert_of_uniform_doubles_robustUnimodal`, `D = ∅`).
Statement identical to `P2Pkg.isRupert_of_slide_robust`.
-/

set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

theorem isRupert_of_slide_robust (V M : Finset ℝ³) (u₀ e : ℝ³) (hu₀ : u₀ ≠ 0) {k : ℕ} [NeZero k]
    (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V) (hxM : ∀ i, x i ∉ M)
    (hk : 3 ≤ k) (ρ : ℝ) (hρ : ρ ≠ 0)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → SlideTest ρ (x (i + 1) - x i) (x j - x i) u₀ e)
    (hrest : ∀ y ∈ V, y ∉ M → (∀ j, y ≠ x j) → ∀ i,
      SlideTest ρ (x (i + 1) - x i) (y - x i) u₀ e)
    (hM : ∀ m ∈ M, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∃ i : ZMod k, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      m = x i + s • (x (i + 1) - x i) + δ • (u₀ + t • e))
    (hz : IsRobustUnimodal (fun i => ⟪x i, u₀⟫)) (hbad : NoPersistHDN x u₀ e) : IsRupert V := by
  classical
  have hne : ∀ᶠ t in 𝓝[>] (0 : ℝ), u₀ + t • e ≠ 0 := by
    have hc : Continuous fun t : ℝ => u₀ + t • e := by fun_prop
    exact (hc.continuousAt.eventually (isOpen_ne.mem_nhds
      (show u₀ + (0 : ℝ) • e ≠ 0 by simpa using hu₀))).filter_mono nhdsWithin_le_nhds
  have h1 := eventually_forall_cycle fun i j hi hj => eventually_det3_slide (hcyc i j hi hj)
  have h2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ y ∈ V, ∀ i : ZMod k, y ∉ M → (∀ j, y ≠ x j) →
      0 < ρ * det3 (x (i + 1) - x i) (y - x i) (u₀ + t • e) := by
    refine (eventually_all_finset V).mpr fun y hy => eventually_all.mpr fun i => ?_
    by_cases hyM : y ∉ M
    · by_cases hyx : ∀ j, y ≠ x j
      · filter_upwards [eventually_det3_slide (hrest y hy hyM hyx i)] with t ht _ _ using ht
      · filter_upwards with t _ h using absurd h hyx
    · filter_upwards with t h using absurd h hyM
  have h3 := (eventually_all_finset M).mpr hM
  have h4 : ∀ᶠ t in 𝓝[>] (0 : ℝ), IsRobustUnimodal (fun i => ⟪x i, u₀ + t • e⟫) := by
    have hlim : ∀ i, Tendsto (fun t : ℝ => ⟪x i, u₀ + t • e⟫) (𝓝[>] (0 : ℝ)) (𝓝 ⟪x i, u₀⟫) := by
      intro i
      have hc : Continuous fun t : ℝ => ⟪x i, u₀ + t • e⟫ := by fun_prop
      have := (hc.continuousAt (x := 0)).tendsto
      simpa using this.mono_left nhdsWithin_le_nhds
    filter_upwards [eventually_strict_order hlim] with t ht using hz.refine ht
  have h5 := eventually_noHDNRim_slide x u₀ e hbad
  obtain ⟨t, ⟨⟨⟨⟨hcyc', hrest'⟩, hM'⟩, hz'⟩, hu⟩, hnd⟩ :=
    ((((h1.and h2).and h3).and h4).and hne).and h5 |>.exists
  set u := u₀ + t • e with hu_def
  have key : ∀ (σ : ℝ), (σ = 1 ∨ σ = -1) → 0 < σ * ρ → IsRupert V := by
    intro σ hσ hσρ
    have hσ0 : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
    have hsu : σ • u ≠ 0 := smul_ne_zero hσ0 hu
    obtain ⟨R, hR, r, hr, hRu⟩ := exists_rotation_to_ez_pos (σ • u) hsu
    have hds : ∀ X Y : ℝ³, det3 X Y (σ • u) = σ * det3 X Y u := by
      intro X Y; simp only [det3_expand, PiLp.smul_apply, smul_eq_mul]; ring
    have hpos : ∀ X Y : ℝ³, 0 < ρ * det3 X Y u → 0 < det3 X Y (σ • u) := by
      intro X Y hXY
      rw [hds]
      have : 0 < (σ * ρ) * (ρ * det3 X Y u) := mul_pos hσρ hXY
      have hρρ : 0 < ρ * ρ := mul_self_pos.mpr hρ
      nlinarith
    have hp : IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (x i))) := by
      refine ⟨hk, fun i j hi hj => ?_⟩
      simp only [proj_rot_sub]
      exact cross2_proj_rot_pos hR hr hRu (hpos _ _ (hcyc' i j hi hj))
    have hdepth := depth_rot hR hr.ne' hRu
    have hin : ∀ v ∈ V, v ∉ M → v ∉ (∅ : Finset ℝ³) → (∀ i, v ≠ x i) →
        proj_xy (R.toEuclideanLin v) ∈
          interior (convexHull ℝ (Set.range fun i => proj_xy (R.toEuclideanLin (x i)))) := by
      intro y hy hyM _ hyx
      refine hp.mem_interior_of_left fun i => ?_
      simp only [proj_rot_sub]
      exact cross2_proj_rot_pos hR hr hRu (hpos _ _ (hrest' y hy i hyM hyx))
    have hM'' : ∀ m ∈ M, ∃ i : ZMod k, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
        m = x i + s • (x (i + 1) - x i) + δ • (σ • u) := by
      intro m hm
      obtain ⟨i, s, δ, hs0, hs1, hδ, hmeq⟩ := hM' m hm
      refine ⟨i, s, δ * σ, hs0, hs1, mul_ne_zero hδ hσ0, ?_⟩
      rw [hmeq, smul_smul, mul_assoc]
      rcases hσ with rfl | rfl <;> norm_num
    have hz2 : IsRobustUnimodal (fun i => (R.toEuclideanLin (x i)) 2) := by
      simp only [hdepth, real_inner_smul_right]
      rcases hσ with rfl | rfl
      · simp only [one_mul]; exact hz'.smul (inv_pos.mpr hr)
      · have := hz'.neg.smul (inv_pos.mpr hr)
        simpa only [neg_one_mul, mul_neg] using this
    have hnd2 : ¬ HasHorizontalDoubleNormal (fun i => proj_xy (R.toEuclideanLin (x i)))
        (fun i => (R.toEuclideanLin (x i)) 2) := by
      refine hnd R hR (σ * r) (mul_ne_zero hσ0 hr.ne') ?_ hp
      have h' : R.toEuclideanLin (σ • u) = r • ez := hRu
      rw [map_smul] at h'
      have : R.toEuclideanLin u = (σ * r) • ez := by
        rw [mul_smul, ← h', smul_smul]
        rcases hσ with rfl | rfl <;> simp
      exact this
    exact isRupert_of_uniform_doubles_robustUnimodal V M ∅ R hR hr hRu x hxV hxM hp hin hz2 hnd2
      hM'' (fun y hy => absurd hy (Finset.notMem_empty _))
  rcases lt_or_gt_of_ne hρ with hn | hp
  · exact key (-1) (Or.inr rfl) (by nlinarith)
  · exact key 1 (Or.inl rfl) (by linarith)

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.isRupert_of_slide_robust
