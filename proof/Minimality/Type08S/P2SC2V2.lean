module

public import Minimality.Type08S.P2SC2V1

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# SC2-V, top vertex `t = g` over `f̄` (package G): parameter form

`g = (L, Yg, zf)` (`ḡ = f̄`), `Yr < Yg`, `L < Xr`; `x` and `r` strictly on opposite sides of `z_f`.
Same motion as for `t = r` (`V(g) = 0`); `S = {F-row of f, both rows of g}`.
-/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

theorem sc2V_core_g (hF : Fr e1 e2 e3) (o : ℝ³) (E : Finset ℝ³)
    {σ L zp zx zf Xr Yr zr Yg b κ : ℝ}
    (hL : 0 < L) (hzx : 0 < σ * (zx - zp)) (hYr : 0 < Yr) (hYrg : Yr < Yg) (hXr : L < Xr)
    (hcg : 0 < Yg * Xr - L * Yr)
    (hb : 0 < b) (hb1 : 0 < L + σ * b * (zp - zf)) (hb2 : 0 < L + σ * b * (zx - zf))
    (hzf : 0 ≤ σ * (zf - zp))
    (hκr : κ * (zr - zf) < 0) (hκx : 0 < κ * (zx - zf))
    (hE : ∀ᶠ s : ℝ in atTop, ∀ y ∈ E, TriCert
      (rim5 e1 e2 e3 o L zp zx zf Xr Yr zr L Yg zf E)
      (pc e1 e2 e3 0 0 1) (pc e1 e2 e3 (σ * s) (-σ) 0) y) :
    IsRupert (rim5 e1 e2 e3 o L zp zx zf Xr Yr zr L Yg zf E) := by
  have hσ : σ ≠ 0 := by rintro rfl; simp at hzx
  have hYg : 0 < Yg := hYr.trans hYrg
  have hG : 0 < Yg * (σ ^ 2 * b * L + σ * (zf - zp)) / L := by
    have : 0 < σ ^ 2 := by positivity
    have : 0 < σ ^ 2 * b * L := by positivity
    positivity
  have e4 := ev_lin3 (β := -L * (L + σ * b * (zx - zf)) - Yg * Yg) (α := Yg * (κ * (zx - zf)))
    (mul_pos hYg hκx)
  have e7 := ev_lin3 (β := (L - Xr) * (L - Xr + σ * b * (zr - zf)) + (Yg - Yr) * (Yg - Yr))
    (α := -((Yg - Yr) * (κ * (zr - zf)))) (by nlinarith [sub_pos.2 hYrg])
  have e8 := ev_lin3 (β := (Xr - L) * (L - Xr + σ * b * (zr - zf)) - Yr * (Yr - Yg))
    (α := -(Yr * (κ * (zr - zf)))) (by nlinarith)
  obtain ⟨M, h4, h7, h8⟩ := (e4.and (e7.and e8)).exists
  have f2 := ev_lin3 (β := σ * (zx - zp) * (-Yg + M * κ * (zp - zf)))
    (α := σ * (zx - zp) * (L + σ * b * (zp - zf))) (mul_pos hzx hb1)
  have f3 := ev_lin3 (β := σ * (zx - zp) * (-Yg + M * κ * (zx - zf)))
    (α := σ * (zx - zp) * (L + σ * b * (zx - zf))) (mul_pos hzx hb2)
  have fs := ev_lin3 (β := L) (α := Yg) hYg
  obtain ⟨s, h2, h3, hs, hEs⟩ := (f2.and (f3.and (fs.and hE))).exists
  obtain ⟨G, hGd⟩ : ∃ G, G = Yg * (σ ^ 2 * b * L + σ * (zf - zp)) / L := ⟨_, rfl⟩
  have hG0 : 0 < G := by rw [hGd]; exact hG
  have hGL : G * L = Yg * (σ ^ 2 * b * L + σ * (zf - zp)) := by rw [hGd]; field_simp
  have hYY : 0 < Yg - Yr := sub_pos.2 hYrg
  obtain ⟨d9, hd9d⟩ : ∃ d9, d9 = G * (Yg * Xr - L * Yr) / (4 * Yg * (Yg - Yr)) := ⟨_, rfl⟩
  have hd90 : 0 < d9 := by rw [hd9d]; positivity
  have hd9 : d9 * (4 * Yg * (Yg - Yr)) = G * (Yg * Xr - L * Yr) := by rw [hd9d]; field_simp
  obtain ⟨q, hqd⟩ : ∃ q, q = L * G / (2 * Yg) := ⟨_, rfl⟩
  have hq : q * (2 * Yg) = L * G := by rw [hqd]; field_simp
  have hXL : 0 < Xr - L := sub_pos.2 hXr
  refine sc5_core2 hF o E (S := s) (⟨-(σ * b), M * κ, -1, -Yg - M * κ * zf, L - σ * b * zf⟩ : Mo)
    (⟨0, 0, 0, d9 - q - σ * s * (σ * b * Yg + M * κ * L), σ * (σ * b * Yg + M * κ * L) - G / 2⟩ : Mo)
    hL hzx (by nlinarith [mul_pos hXL hYg]) hYr hcg (by linarith)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hEs
  all_goals simp only [Rw, L2, VX, VY]
  · left; linarith [mul_pos hL hb1]
  · right; refine ⟨by ring, ?_⟩
    linarith [h2]
  · right; refine ⟨by ring, ?_⟩
    linarith [h3]
  · left; linarith [h4]
  · left; nlinarith [mul_pos hYr hYg]
  · right; refine ⟨by ring, ?_⟩
    linarith [mul_pos hL hG0, hGL]
  · left; linarith [h7]
  · left; linarith [h8]
  · right; refine ⟨by ring, ?_⟩
    linarith [mul_pos hYg hd90, hq, hGL]
  · right; refine ⟨by ring, ?_⟩
    have hq2 : q * (2 * Yg) * (Yg - Yr) = L * G * (Yg - Yr) := by rw [hq]
    have h4g : 0 < 4 * Yg := by positivity
    refine lt_of_mul_lt_mul_right ?_ h4g.le
    linarith [mul_pos hG0 hcg, hd9, hq2]

end Type08Sp
end Minimality
