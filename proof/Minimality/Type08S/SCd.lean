module

public import Minimality.Type08S.SCs

@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

theorem exists_small (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ∃ η : ℝ, 0 < η ∧ η < a ∧ η < b ∧ η < c := by
  refine ⟨min a (min b c) / 2, by positivity, ?_, ?_, ?_⟩
  · have := min_le_left a (min b c); linarith [lt_min ha (lt_min hb hc)]
  · have := (min_le_right a (min b c)).trans (min_le_left b c)
    linarith [lt_min ha (lt_min hb hc)]
  · have := (min_le_right a (min b c)).trans (min_le_right b c)
    linarith [lt_min ha (lt_min hb hc)]

/-- The line `σ(X) = σ0 + m X` of the far edge's projection crosses the chord from `(0, zx)` to
`(L, zf)` at `Xx ∈ (0, L)`, and `σ0 < zx`: then `σ(L) > zf`. -/
theorem sigmaL_gt {L zx zf Xx σ0 m : ℝ} (hX0 : 0 < Xx) (hXL : Xx < L) (hσ : σ0 < zx)
    (hch : zx * L + (zf - zx) * Xx = (σ0 + m * Xx) * L) : zf < σ0 + m * L := by
  have hL : 0 < L := by linarith
  have key : (σ0 + m * L - zf) * (Xx * L) = (zx - σ0) * (L - Xx) * L := by
    linear_combination (-L) * hch
  have : 0 < (σ0 + m * L - zf) * (Xx * L) := by
    rw [key]; exact mul_pos (mul_pos (by linarith) (by linarith)) hL
  have h2 : 0 < Xx * L := mul_pos hX0 hL
  by_contra hc
  push Not at hc
  nlinarith

/-- **Corollary SC-d, case (I)** (`x` above the crossing level): five-corner closing with a
top side `rg` (`Yr = Yg`, `Xg < Xr`) whose projection line `z = σ0 + m X` crosses the open chord
(condition (D): `zp < σ0 < zx`), and a level `z0` with `f, r` below, `g, x` above and below
`σ0`. -/
theorem lemmaSCd_I (hF : Fr e1 e2 e3) (o : ℝ³) (E : Finset ℝ³)
    {L zp zx zf Xr Yr zr Xg zg σ0 m Xx z0 : ℝ}
    (hL : 0 < L) (hzx : zp < zx) (hYr : 0 < Yr) (hXrg : Xg < Xr)
    (hσ0 : σ0 = zg - m * Xg) (hm : zr - zg = m * (Xr - Xg))
    (hD1 : zp < σ0) (hD2 : σ0 < zx) (hX0 : 0 < Xx) (hXL : Xx < L)
    (hch : zx * L + (zf - zx) * Xx = (σ0 + m * Xx) * L)
    (hz1 : zf < z0) (hz2 : zr < z0) (hz3 : z0 < zg) (hz4 : z0 < zx) (hz5 : z0 < σ0)
    (hE : ∀ᶠ s : ℝ in atTop, ∀ y ∈ E, TriCert (rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yr zg E)
      (pc e1 e2 e3 0 0 1) (pc e1 e2 e3 (1 * s) (-1) 0) y) :
    IsRupert (rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yr zg E) := by
  have hσL := sigmaL_gt hX0 hXL hD2 hch
  obtain ⟨η, hη, h1, h2, h3⟩ := exists_small (σ0 - z0) (σ0 - zp) (σ0 + m * L - zf)
    (by linarith) (by linarith) (by linarith)
  refine lemmaSC_s (σ := 1) hF o E (φ0 := σ0 - η) (φ1 := -1) (θ := m) (χ0 := -z0) (χ1 := 1)
    hL (by linarith : (0:ℝ) < 1 * (zx - zp)) hYr rfl hXrg ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hE
  all_goals nlinarith

/-- **Corollary SC-d, case (II)** (`x` below the crossing level): `g, x` below `z0`, `f, r` above. -/
theorem lemmaSCd_II (hF : Fr e1 e2 e3) (o : ℝ³) (E : Finset ℝ³)
    {L zp zx zf Xr Yr zr Xg zg σ0 m Xx z0 : ℝ}
    (hL : 0 < L) (hzx : zp < zx) (hYr : 0 < Yr) (hXrg : Xg < Xr)
    (hσ0 : σ0 = zg - m * Xg) (hm : zr - zg = m * (Xr - Xg))
    (hD1 : zp < σ0) (hD2 : σ0 < zx) (hX0 : 0 < Xx) (hXL : Xx < L)
    (hch : zx * L + (zf - zx) * Xx = (σ0 + m * Xx) * L)
    (hz1 : z0 < zf) (hz2 : z0 < zr) (hz3 : zg < z0) (hz4 : zx < z0)
    (hE : ∀ᶠ s : ℝ in atTop, ∀ y ∈ E, TriCert (rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yr zg E)
      (pc e1 e2 e3 0 0 1) (pc e1 e2 e3 (1 * s) (-1) 0) y) :
    IsRupert (rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yr zg E) := by
  have hσL := sigmaL_gt hX0 hXL hD2 hch
  obtain ⟨η, hη, h1, h2, h3⟩ := exists_small (zx - σ0) (σ0 - zp) (σ0 + m * L - zf)
    (by linarith) (by linarith) (by linarith)
  set K := (|σ0 - η - zx| + |σ0 - η - zp|) / (z0 - zx) + 1 with hK
  have hd : 0 < z0 - zx := by linarith
  have hKd : K * (z0 - zx) = |σ0 - η - zx| + |σ0 - η - zp| + (z0 - zx) := by
    rw [hK]; field_simp
  have hKp : 0 < K := by
    rw [hK]; have := abs_nonneg (σ0 - η - zx); have := abs_nonneg (σ0 - η - zp)
    positivity
  have a1 := neg_abs_le (σ0 - η - zx)
  have a2 := neg_abs_le (σ0 - η - zp)
  have a3 := abs_nonneg (σ0 - η - zx)
  have a4 := abs_nonneg (σ0 - η - zp)
  refine lemmaSC_s (σ := 1) hF o E (φ0 := σ0 - η) (φ1 := -1) (θ := m) (χ0 := K * z0) (χ1 := -K)
    hL (by linarith : (0:ℝ) < 1 * (zx - zp)) hYr rfl hXrg ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hE
  all_goals nlinarith

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.lemmaSCd_I
#print axioms Minimality.Type08Sp.lemmaSCd_II
