module

public import Minimality.Type08S.P2I1

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# P3a core, part 8: `close_core` — from the rim hypotheses (any `ZMod k'` rim of the screen quadrilateral)
to `IsRupert`, at the frame level.
-/

set_option autoImplicit true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

set_option maxHeartbeats 4000000 in
theorem close_core_g (hF : Fr e1 e2 e3) (O w : ℝ³)
    {κ κv L zf Xr Yr zr Xg Yg zg Xp zp : ℝ} (hκ : κ ≠ 0) (hκv : κv ≠ 0)
    (hL : 0 < L) (hYr : 0 < Yr) (hYg : 0 < Yg)
    (hcr : 0 < (Xg - Xr) * (-Yr) - (Yg - Yr) * (L - Xr)) (hcg : 0 < Yg * Xr - Xg * Yr)
    (hpx : fpt e1 e2 e3 O Xp 0 zp ≠ fpt e1 e2 e3 O 0 0 κ) (hpf : fpt e1 e2 e3 O Xp 0 zp ≠ fpt e1 e2 e3 O L 0 zf)
    (hpm : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      fpt e1 e2 e3 O Xp 0 zp = fpt e1 e2 e3 O 0 0 κ +
        s • (fpt e1 e2 e3 O L 0 zf - fpt e1 e2 e3 O 0 0 κ) + δ • (κv • e3 + t • ((κ * κv) • e1)))
    (hw : ∀ i : ZMod 4, SlideTest κv
      (Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (i + 1) - Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg i)
      (w - Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg i) (κv • e3) ((κ * κv) • e1))
    {k' : ℕ} [NeZero k'] (hk3 : 3 ≤ k') (τ : ZMod k' → ZMod 4)
    (hcyc : ∀ i j : ZMod k', j ≠ i → j ≠ i + 1 → 0 < det3
      (Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (τ (i + 1)) - Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (τ i))
      (Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (τ j) - Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (τ i)) (κv • e3))
    (hleft : ∀ (i : ZMod k') (a : ZMod 4), 0 ≤ det3
      (Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (τ (i + 1)) - Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (τ i))
      (Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg a - Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (τ i)) (κv • e3))
    (hzR : IsRobustUnimodal (fun i => ⟪Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (τ i), κv • e3⟫))
    (hbadR : NoPersistHDN (fun i => Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (τ i)) (κv • e3) (L • e1)) :
    IsRupert ({O, fpt e1 e2 e3 O 0 0 κ, fpt e1 e2 e3 O L 0 zf, fpt e1 e2 e3 O Xr Yr zr,
      fpt e1 e2 e3 O Xg Yg zg, fpt e1 e2 e3 O Xp 0 zp, w} : Finset ℝ³) := by
  have hk4 := rim_k_eq_4 hF hκv hL hYr hYg hcr hcg hk3 τ hcyc hleft (O := O) (κ := κ) (zf := zf)
    (zr := zr) (zg := zg)
  subst hk4
  obtain ⟨hpos, hneg⟩ := rim_orient4 hF hκv hL hYr hYg hcr hcg τ hcyc hleft (O := O) (κ := κ)
    (zf := zf) (zr := zr) (zg := zg)
  have hlam : (κ * κv / L) ≠ 0 := div_ne_zero (mul_ne_zero hκ hκv) hL.ne'
  have hsm : (κ * κv / L) • (L • e1) = (κ * κv) • e1 := by
    rw [smul_smul]; congr 1; field_simp
  refine slide_core_g hF O w hκ hκv hL hYr hYg hcr hcg hpx hpf hpm hw ?_ ?_
  · rcases lt_or_gt_of_ne hκv with hn | hp
    · obtain ⟨c, hc⟩ := hneg hn
      have := robust_of_reflect (z := fun j : ZMod 4 => ⟪Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg j, κv • e3⟫) c
        (by convert hzR using 2 with i; rw [hc i]; try rfl)
      exact this
    · obtain ⟨c, hc⟩ := hpos hp
      have := robust_of_shift (z := fun j : ZMod 4 => ⟪Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg j, κv • e3⟫) c
        (by convert hzR using 2 with i; rw [hc i]; try rfl)
      exact this
  · have h' := noPersist_smul' hbadR hlam
    rw [hsm] at h'
    rcases lt_or_gt_of_ne hκv with hn | hp
    · obtain ⟨c, hc⟩ := hneg hn
      exact noPersist_of_reflect c (by convert h' using 2 with i; rw [hc i]; try rfl)
    · obtain ⟨c, hc⟩ := hpos hp
      exact noPersist_of_shift c (by convert h' using 2 with i; rw [hc i]; try rfl)

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.close_core_g
