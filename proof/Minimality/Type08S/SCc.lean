module

public import Minimality.Type08S.SCg

@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

/-- The affine data `(χ, Φ)` of Corollary SC-c: `Φ > 0` at the two `F`-pair points `(0, zp)`,
`(L, zf)`, `Φ < 0` at the top projection `(Xt, zt)` on the open chord `x̄ f̄`, and (R3) for the
scaled depth function `M (zx - zt)(z - zt)`. -/
theorem sc_data {L zp zx zf Xt zt : ℝ} (hL : 0 < L) (hzx : zp ≠ zx) (hX0 : 0 < Xt) (hXL : Xt < L)
    (hch : (zt - zx) * L = (zf - zx) * Xt) (hk : zx ≠ zt) :
    ∃ φ0 φ1 θ M : ℝ, 0 < M ∧ 0 < φ0 + φ1 * zp + θ * 0 ∧ 0 < φ0 + φ1 * zf + θ * L ∧
      φ0 + φ1 * zt + θ * Xt < 0 ∧
      0 ≤ M * (zx - zt) * (zx - zt) + (φ0 + φ1 * zx + θ * 0) ∧
      0 ≤ M * (zx - zt) * (zp - zt) + (φ0 + φ1 * zp + θ * 0) := by
  have hd : zx - zp ≠ 0 := sub_ne_zero.2 hzx.symm
  have hk2 : 0 < (zx - zt) * (zx - zt) := mul_self_pos.2 (sub_ne_zero.2 hk)
  set X0 := (Xt + L) / 2 with hX0d
  set M := (X0 + 1) / ((zx - zt) * (zx - zt)) with hM
  have hMpos : 0 < M := div_pos (by rw [hX0d]; linarith) hk2
  have hMk : M * ((zx - zt) * (zx - zt)) = X0 + 1 := by rw [hM]; field_simp
  set a := (X0 + 1 + |M * (zx - zt) * (zp - zt)|) / (zx - zp) with ha
  have haz : a * (zx - zp) = X0 + 1 + |M * (zx - zt) * (zp - zt)| := by rw [ha]; field_simp
  refine ⟨a * zx - X0, -a, a * (zf - zx) / L + 1, M, hMpos, ?_, ?_, ?_, ?_, ?_⟩
  · have := abs_nonneg (M * (zx - zt) * (zp - zt))
    nlinarith
  · field_simp; rw [hX0d]; nlinarith
  · have e : a * (zf - zx) / L * Xt = a * (zt - zx) := by field_simp; linear_combination (-a) * hch
    have : a * zx - X0 + -a * zt + (a * (zf - zx) / L + 1) * Xt = Xt - X0 := by
      rw [add_mul, e]; ring
    rw [this, hX0d]; linarith
  · have : a * zx - X0 + -a * zx + (a * (zf - zx) / L + 1) * 0 = - X0 := by ring
    rw [this]; nlinarith [hMk, hX0d]
  · have := abs_nonneg (M * (zx - zt) * (zp - zt))
    have := neg_abs_le (M * (zx - zt) * (zp - zt))
    nlinarith


/-- **Corollary SC-c, top vertex `g`** (`Yr < Yg`): `ḡ` lies on the open chord `x̄ f̄` of the
`F`-plane, and the depths of `f`, `r` lie on the other side of `z_g` from `z_x`. -/
theorem lemmaSCc_g (hF : Fr e1 e2 e3) (o : ℝ³) (E : Finset ℝ³)
    {σ L zp zx zf Xr Yr zr Xg Yg zg : ℝ}
    (hL : 0 < L) (hzx : 0 < σ * (zx - zp))
    (hcr : 0 < (Xg - Xr) * (-Yr) - (Yg - Yr) * (L - Xr)) (hYr : 0 < Yr) (hYrg : Yr < Yg)
    (hcg : 0 < Yg * Xr - Xg * Yr)
    (hX0 : 0 < Xg) (hXL : Xg < L) (hch : (zg - zx) * L = (zf - zx) * Xg)
    (hdf : (zx - zg) * (zf - zg) < 0) (hdr : (zx - zg) * (zr - zg) < 0)
    (hE : ∀ᶠ s : ℝ in atTop, ∀ y ∈ E, TriCert (rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yg zg E)
      (pc e1 e2 e3 0 0 1) (pc e1 e2 e3 (σ * s) (-σ) 0) y) :
    IsRupert (rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yg zg E) := by
  have hk : zx ≠ zg := by
    intro h; rw [h] at hdf; simp at hdf
  obtain ⟨φ0, φ1, θ, M, hM, hp, hf, ht, hRx, hRp⟩ := sc_data hL (fun h : zp = zx => by rw [h] at hzx; simp at hzx) hX0 hXL hch hk
  refine lemmaSC_g hF o E (σ := σ) (φ0 := φ0) (φ1 := φ1) (θ := θ) (χ0 := -(M * (zx - zg)) * zg)
    (χ1 := M * (zx - zg)) hL hzx hcr hYr hYrg hcg ?_ ?_ ?_ ?_ hp hf ht ?_ ?_ hE
  · nlinarith [mul_neg_of_pos_of_neg hM hdf]
  · nlinarith [mul_neg_of_pos_of_neg hM hdr]
  · ring
  · nlinarith [mul_pos hM (mul_self_pos.2 (sub_ne_zero.2 hk))]
  · nlinarith
  · nlinarith

/-- **Corollary SC-c, top vertex `r`** (`Yg < Yr`): `r̄` on the open chord, `f` on the other side
of `z_r` from `z_x`, `g` on the same side as `z_x`. -/
theorem lemmaSCc_r (hF : Fr e1 e2 e3) (o : ℝ³) (E : Finset ℝ³)
    {σ L zp zx zf Xr Yr zr Xg Yg zg : ℝ}
    (hL : 0 < L) (hzx : 0 < σ * (zx - zp))
    (hcr : 0 < (Xg - Xr) * (-Yr) - (Yg - Yr) * (L - Xr)) (hYr : 0 < Yr) (hYg : 0 < Yg)
    (hYrg : Yg < Yr) (hcg : 0 < Yg * Xr - Xg * Yr)
    (hX0 : 0 < Xr) (hXL : Xr < L) (hch : (zr - zx) * L = (zf - zx) * Xr)
    (hdf : (zx - zr) * (zf - zr) < 0) (hdg : 0 < (zx - zr) * (zg - zr))
    (hE : ∀ᶠ s : ℝ in atTop, ∀ y ∈ E, TriCert (rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yg zg E)
      (pc e1 e2 e3 0 0 1) (pc e1 e2 e3 (σ * s) (-σ) 0) y) :
    IsRupert (rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yg zg E) := by
  have hk : zx ≠ zr := by
    intro h; rw [h] at hdf; simp at hdf
  obtain ⟨φ0, φ1, θ, M, hM, hp, hf, ht, hRx, hRp⟩ := sc_data hL (fun h : zp = zx => by rw [h] at hzx; simp at hzx) hX0 hXL hch hk
  refine lemmaSC_r hF o E (σ := σ) (φ0 := φ0) (φ1 := φ1) (θ := θ) (χ0 := -(M * (zx - zr)) * zr)
    (χ1 := M * (zx - zr)) hL hzx hcr hYr hYg hYrg hcg ?_ ?_ ?_ ?_ hp hf ht ?_ ?_ hE
  · nlinarith [mul_neg_of_pos_of_neg hM hdf]
  · ring
  · nlinarith [mul_pos hM hdg]
  · nlinarith [mul_pos hM (mul_self_pos.2 (sub_ne_zero.2 hk))]
  · nlinarith
  · nlinarith

end Type08Sp
end Minimality
