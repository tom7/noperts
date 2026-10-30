module

public import Minimality.Type08S.P2SC2core

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# SC2-V, top vertex `t = r` over `f̄` (package G): parameter form

`r = (L, Yr, zf)` (so `r̄ = f̄`), `Yg < Yr`, `Xg < L`.  Motion `M0` (η = 0, `V(r) = 0`): `θ = -1`,
`VY = L - X + β(z - zf)`, `VX = -Yr + Mκ(z - zf) - θ Y`, `β = σ b`; `M1 = (0,0,0,aX,aY)` (screen velocity correction of `r̄`),
`S = {F-row of f, both rows of r}`, one dependency; the gap `G = Yr(σ²bL + σ(zf-zp))/L` is the sign condition
`σ(zf - zp) ≥ 0` (`h_{x'} ≤ h_f`).  Scales: `M` large first, then `s` (tilt) large.
-/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

theorem ev_lin3 {α β : ℝ} (hα : 0 < α) : ∀ᶠ s : ℝ in atTop, 0 < α * s + β := by
  filter_upwards [eventually_gt_atTop (|β| / α)] with M hM
  have := (div_lt_iff₀ hα).1 hM
  nlinarith [neg_abs_le β]

theorem sc2V_core_r (hF : Fr e1 e2 e3) (o : ℝ³) (E : Finset ℝ³)
    {σ L zp zx zf Xg Yr Yg zg b κ : ℝ}
    (hL : 0 < L) (hzx : 0 < σ * (zx - zp)) (hYg : 0 < Yg) (hYgr : Yg < Yr) (hXg : Xg < L)
    (hcg : 0 < Yg * L - Xg * Yr)
    (hb : 0 < b) (hb1 : 0 < L + σ * b * (zp - zf)) (hb2 : 0 < L + σ * b * (zx - zf))
    (hzf : 0 ≤ σ * (zf - zp))
    (hκg : 0 < κ * (zg - zf)) (hκx : 0 < κ * (zx - zf))
    (hE : ∀ᶠ s : ℝ in atTop, ∀ y ∈ E, TriCert
      (rim5 e1 e2 e3 o L zp zx zf L Yr zf Xg Yg zg E)
      (pc e1 e2 e3 0 0 1) (pc e1 e2 e3 (σ * s) (-σ) 0) y) :
    IsRupert (rim5 e1 e2 e3 o L zp zx zf L Yr zf Xg Yg zg E) := by
  have hσ : σ ≠ 0 := by rintro rfl; simp at hzx
  have hYr : 0 < Yr := hYg.trans hYgr
  have hG : 0 < Yr * (σ ^ 2 * b * L + σ * (zf - zp)) / L := by
    have : 0 < σ ^ 2 := by positivity
    have : 0 < σ ^ 2 * b * L := by positivity
    positivity
  -- step 1: M
  have e4 := ev_lin3 (β := -Xg * (L + σ * b * (zx - zf)) - Yg * Yr) (α := Yg * (κ * (zx - zf)))
    (mul_pos hYg hκx)
  have e9 := ev_lin3 (β := -Xg * (L - Xg + σ * b * (zg - zf)) + Yg * (-Yr + Yg)) (α := Yg * (κ * (zg - zf)))
    (mul_pos hYg hκg)
  have e10 := ev_lin3 (β := (Xg - L) * (L - Xg + σ * b * (zg - zf)) + (Yr - Yg) * (-Yr + Yg))
    (α := (Yr - Yg) * (κ * (zg - zf))) (mul_pos (sub_pos.2 hYgr) hκg)
  obtain ⟨M, h4, h9, h10⟩ := (e4.and (e9.and e10)).exists
  -- step 2: s
  have f2 := ev_lin3 (β := σ * (zx - zp) * (-Yr + M * κ * (zp - zf)))
    (α := σ * (zx - zp) * (L + σ * b * (zp - zf))) (mul_pos hzx hb1)
  have f3 := ev_lin3 (β := σ * (zx - zp) * (-Yr + M * κ * (zx - zf)))
    (α := σ * (zx - zp) * (L + σ * b * (zx - zf))) (mul_pos hzx hb2)
  have fs := ev_lin3 (β := Xg) (α := Yg) hYg
  obtain ⟨s, h2, h3, hs, hEs⟩ := (f2.and (f3.and (fs.and hE))).exists
  obtain ⟨G, hGd⟩ : ∃ G, G = Yr * (σ ^ 2 * b * L + σ * (zf - zp)) / L := ⟨_, rfl⟩
  have hG0 : 0 < G := by rw [hGd]; exact hG
  have hGL : G * L = Yr * (σ ^ 2 * b * L + σ * (zf - zp)) := by rw [hGd]; field_simp
  obtain ⟨d8, hd8d⟩ : ∃ d8, d8 = (L - Xg) * G / (4 * (Yr - Yg)) := ⟨_, rfl⟩
  have hLX : 0 < L - Xg := sub_pos.2 hXg
  have hYY : 0 < Yr - Yg := sub_pos.2 hYgr
  have hd80 : 0 < d8 := by rw [hd8d]; positivity
  have hd8 : d8 * (4 * (Yr - Yg)) = (L - Xg) * G := by rw [hd8d]; field_simp
  refine sc5_core2 hF o E (S := s) (⟨-(σ * b), M * κ, -1, -Yr - M * κ * zf, L - σ * b * zf⟩ : Mo)
    (⟨0, 0, 0, -σ * s * (σ * b * Yr + M * κ * L) - d8, σ * (σ * b * Yr + M * κ * L) - G / 2⟩ : Mo)
    hL hzx (by nlinarith [mul_pos hLX hYr]) hYr hcg (by linarith)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hEs
  all_goals simp only [Rw, L2, VX, VY]
  · left; linarith [mul_pos hL hb1]
  · right; refine ⟨by ring, ?_⟩
    linarith [h2]
  · right; refine ⟨by ring, ?_⟩
    linarith [h3]
  · left; linarith [h4]
  · left; nlinarith [mul_pos hYr hYr]
  · right; refine ⟨by ring, ?_⟩
    linarith [mul_pos hL hG0, hGL]
  · right; refine ⟨by ring, ?_⟩
    linarith [mul_pos hLX hG0, hd8]
  · right; refine ⟨by ring, ?_⟩
    linarith [mul_pos hYr hd80]
  · left; linarith [h9]
  · left; linarith [h10]

end Type08Sp
end Minimality
