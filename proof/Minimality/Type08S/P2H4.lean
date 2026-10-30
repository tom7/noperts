module

public import Minimality.Type08S.P2H3
public import Minimality.Type08S.P2SCX

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# pkH H4: Lemma D (sp08d §3) in frame numbers: class (d) and the top-side chord-end-at-`x` cases

`LemEF`: Lemma E (iii), weak form, for the top side `Yr = Yg`: with `D(z) := (Xr - Xg)(z - zf) + L (zr - zg)`
(`= (Xr - Xg)(z - ζ)`, `ζ` the depth where `Π' = aff(f, r, g)` meets the line `x x'`; in 3-D,
`det3 (r - f) (g - f) (p - f) = Y (Xr - Xg) (z_p - ζ)` for `p` on the axis), `D(zx) · D(zp) ≤ 0`.

* `classD5_of`: class (d) (`DCross`, not collinear) + robustness + `LemEF`, `zp < zx` ⇒ `ClassD5` (incl. (D) and the
  level `z0` of SC-d case I / II); `classD5_neg`: the mirror `zx < zp` (σ = −1) gives `ClassD5` of the reflected
  depths.
* `classX5_of`: `XEnd` + `LemEF` (top-side cases) ⇒ pkD's `ClassX5 σ` (its `x ∉ Π'` sign `hPi`).
-/

set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- Lemma E (iii), weak, at the closing's top side, frame form. -/
def LemEF (zp L zx zf Xr zr Xg zg : ℝ) : Prop :=
  ((Xr - Xg) * (zx - zf) + L * (zr - zg)) * ((Xr - Xg) * (zp - zf) + L * (zr - zg)) ≤ 0

/-- The sign of `D(zx)` from Lemma E: `x` strictly on its side of `Π'` (`σ (zx - zp) > 0`). -/
theorem lemE_sign {σ zp L zx zf Xr zr Xg zg : ℝ} (hσ : 0 < σ * (zx - zp)) (hXrg : Xg < Xr)
    (hE : LemEF zp L zx zf Xr zr Xg zg) (hD : (Xr - Xg) * (zx - zf) + L * (zr - zg) ≠ 0) :
    0 < σ * ((Xr - Xg) * (zx - zf) + L * (zr - zg)) := by
  unfold LemEF at hE
  set Dx := (Xr - Xg) * (zx - zf) + L * (zr - zg) with hDx
  have hDp : (Xr - Xg) * (zp - zf) + L * (zr - zg) = Dx - (Xr - Xg) * (zx - zp) := by rw [hDx]; ring
  rw [hDp] at hE
  rcases lt_trichotomy (σ * Dx) 0 with h | h | h
  · exfalso
    have h1 : σ * (Dx - (Xr - Xg) * (zx - zp)) < 0 := by nlinarith [mul_pos (sub_pos.2 hXrg) hσ]
    have k1 := mul_pos (neg_pos.2 h) (neg_pos.2 h1)
    have k2 : (-(σ * Dx)) * (-(σ * (Dx - (Xr - Xg) * (zx - zp)))) =
        σ ^ 2 * (Dx * (Dx - (Xr - Xg) * (zx - zp))) := by ring
    rw [k2] at k1
    nlinarith [mul_nonneg (sq_nonneg σ) (neg_nonneg.2 hE)]
  · exfalso
    have hσ0 : σ ≠ 0 := by rintro rfl; simp at hσ
    exact hD ((mul_eq_zero.mp h).resolve_left hσ0)
  · exact h

/-- **Lemma D + SC-d's levels: class (d) ⇒ `ClassD5`** (`x` above `x'`). -/
theorem classD5_of {zp L zx zf Xr Yr zr Xg Yg zg : ℝ} (hL : 0 < L) (hzp : zp < zx) (hXrg : Xg < Xr)
    (hd : DCross L zx zf Xr Yr zr Xg Yg zg) (hnc : ¬ Coll5 L zx zf Xr zr Xg zg)
    (hrob : Rob4 zx zf zr zg) (hE : LemEF zp L zx zf Xr zr Xg zg) :
    ClassD5 zp L zx zf Xr Yr zr Xg Yg zg := by
  obtain ⟨hY, s, s', hs0, hs1, ht0, ht1, hX, hz⟩ := hd
  have hcase := rob4_d hrob hs0 hs1 ht0 ht1 hz
  have hΔ : 0 < Xr - Xg := sub_pos.2 hXrg
  set m := (zr - zg) / (Xr - Xg) with hmdef
  have hm : zr - zg = m * (Xr - Xg) := by rw [hmdef]; field_simp
  -- x ∉ Π' (not collinear)
  have hD : (Xr - Xg) * (zx - zf) + L * (zr - zg) ≠ 0 := by
    intro h0
    apply hnc
    constructor
    · linear_combination (-L) * hz + (zf - zx) * hX + s' * h0
    · linear_combination (-L) * hz + (zf - zx) * hX + (s' - 1) * h0
  have hDx := lemE_sign (σ := 1) (by linarith) hXrg hE hD
  rw [one_mul] at hDx
  have hDp : (Xr - Xg) * (zp - zf) + L * (zr - zg) ≤ 0 := by
    unfold LemEF at hE
    by_contra hc; push_neg at hc; nlinarith [mul_pos hDx hc]
  set K := zx - zf + m * L with hK
  have hKpos : 0 < K := by
    have : (Xr - Xg) * (zx - zf) + L * (zr - zg) = (Xr - Xg) * K := by rw [hK, hm]; ring
    rw [this] at hDx; exact pos_of_mul_pos_right hDx hΔ.le
  have hKp : zp ≤ zx - K := by
    have : (Xr - Xg) * (zp - zf) + L * (zr - zg) = (Xr - Xg) * (zp - (zx - K)) := by rw [hK, hm]; ring
    rw [this] at hDp
    have : zp - (zx - K) ≤ 0 := by
      by_contra hc; push_neg at hc; nlinarith [mul_pos hΔ hc]
    linarith
  set σ0 := zg - m * Xg with hσ0
  have hσK : σ0 = zx - s * K := by
    rw [hσ0, hK]
    linear_combination (-1) * hz + m * hX - (1 - s') * hm
  set zc := zx + s * (zf - zx) with hzc
  have hσc : σ0 = zc - m * (s * L) := by rw [hσK, hzc, hK]; ring
  have hD1 : zp < σ0 := by rw [hσK]; nlinarith [mul_pos (sub_pos.2 hs1) hKpos]
  have hD2 : σ0 < zx := by rw [hσK]; nlinarith [mul_pos hs0 hKpos]
  have hch : zx * L + (zf - zx) * (s * L) = (σ0 + m * (s * L)) * L := by rw [hσc, hzc]; ring
  have hX0 : 0 < s * L := by positivity
  have hXL : s * L < L := by nlinarith [mul_pos (sub_pos.2 hs1) hL]
  clear_value σ0 zc K m
  rcases hcase with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · have hmneg : m < 0 := by
      by_contra hc; push_neg at hc; linarith [mul_nonneg hc hΔ.le]
    have a1 : zf < zc := by rw [hzc]; linarith [mul_pos (sub_pos.2 hs1) (sub_pos.2 h1)]
    have a2 : zc < zx := by rw [hzc]; linarith [mul_pos hs0 (sub_pos.2 h1)]
    have a3 : zc < σ0 := by rw [hσc]; linarith [mul_pos (neg_pos.2 hmneg) (mul_pos hs0 hL)]
    have hAB : max zf zr < min (min zg zx) σ0 :=
      max_lt (lt_min (lt_min (by linarith) (by linarith)) (by linarith))
        (lt_min (lt_min h4 (by linarith)) (by linarith))
    refine ⟨σ0, m, s * L, (max zf zr + min (min zg zx) σ0) / 2, hY.symm, hXrg, hzp, hσ0, hm, hD1, hD2,
      hX0, hXL, hch, Or.inl ⟨?_, ?_, ?_, ?_, ?_⟩⟩
    · linarith [le_max_left zf zr]
    · linarith [le_max_right zf zr]
    · linarith [min_le_left (min zg zx) σ0, min_le_left zg zx]
    · linarith [min_le_left (min zg zx) σ0, min_le_right zg zx]
    · linarith [min_le_right (min zg zx) σ0]
  · have a1 : zx < zc := by rw [hzc]; linarith [mul_pos hs0 (sub_pos.2 h1)]
    have a2 : zc < zf := by rw [hzc]; linarith [mul_pos (sub_pos.2 hs1) (sub_pos.2 h1)]
    have hAB : max zg zx < min zf zr :=
      max_lt (lt_min (by linarith) h4) (lt_min (by linarith) (by linarith))
    refine ⟨σ0, m, s * L, (max zg zx + min zf zr) / 2, hY.symm, hXrg, hzp, hσ0, hm, hD1, hD2,
      hX0, hXL, hch, Or.inr ⟨?_, ?_, ?_, ?_⟩⟩
    · linarith [min_le_left zf zr]
    · linarith [min_le_right zf zr]
    · linarith [le_max_left zg zx]
    · linarith [le_max_right zg zx]

/-- The mirror (`x` below `x'`, σ = −1): `ClassD5` of the reflected depths. -/
theorem classD5_neg {zp L zx zf Xr Yr zr Xg Yg zg : ℝ} (hL : 0 < L) (hzp : zx < zp) (hXrg : Xg < Xr)
    (hd : DCross L zx zf Xr Yr zr Xg Yg zg) (hnc : ¬ Coll5 L zx zf Xr zr Xg zg)
    (hrob : Rob4 zx zf zr zg) (hE : LemEF zp L zx zf Xr zr Xg zg) :
    ClassD5 (-zp) L (-zx) (-zf) Xr Yr (-zr) Xg Yg (-zg) := by
  obtain ⟨hY, s, s', hs0, hs1, ht0, ht1, hX, hz⟩ := hd
  refine classD5_of hL (by linarith) hXrg ⟨hY, s, s', hs0, hs1, ht0, ht1, hX, by linarith⟩ ?_ hrob.neg ?_
  · rintro ⟨h1, h2⟩; exact hnc ⟨by linarith, by linarith⟩
  · unfold LemEF at hE ⊢; nlinarith

/-- `x ∉ Π'` sign of SC-X (`hPi`) from Lemma E, for `x̄` on the line of the top side. -/
theorem hPi_of {σ zp L zx zf Xr zr Xg zg : ℝ} (hσ : 0 < σ * (zx - zp)) (hXr : 0 < Xr) (hXrg : Xg < Xr)
    (hcol : (zg - zx) * Xr = (zr - zx) * Xg) (hnc : ¬ Coll5 L zx zf Xr zr Xg zg)
    (hE : LemEF zp L zx zf Xr zr Xg zg) :
    0 < σ * ((zr - zx) * L - (zf - zx) * Xr) := by
  have hΔ : 0 < Xr - Xg := sub_pos.2 hXrg
  have key : ((zr - zx) * L - (zf - zx) * Xr) * (Xr - Xg) =
      Xr * ((Xr - Xg) * (zx - zf) + L * (zr - zg)) := by linear_combination L * hcol
  have hD : (Xr - Xg) * (zx - zf) + L * (zr - zg) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at key
    have hP : (zr - zx) * L - (zf - zx) * Xr = 0 := (mul_eq_zero.mp key).resolve_right hΔ.ne'
    apply hnc
    refine ⟨by linarith, ?_⟩
    have : ((zg - zx) * L - (zf - zx) * Xg) * Xr = 0 := by linear_combination L * hcol + Xg * hP
    have := (mul_eq_zero.mp this).resolve_right hXr.ne'
    linarith
  have hs := lemE_sign hσ hXrg hE hD
  have : 0 < σ * ((zr - zx) * L - (zf - zx) * Xr) * (Xr - Xg) := by
    rw [mul_assoc, key]; nlinarith [mul_pos hXr hs]
  exact pos_of_mul_pos_left this hΔ.le

/-- **Chord end at `x`: `XEnd` + Lemma E ⇒ `ClassX5`.** -/
theorem classX5_of {σ zp L zx zf Xr Yr zr Xg Yg zg : ℝ} (hσ : 0 < σ * (zx - zp)) (hYr : 0 < Yr)
    (hcg : 0 < Yg * Xr - Xg * Yr) (hx : XEnd L zx zf Xr Yr zr Xg Yg zg)
    (hnc : Yr = Yg → ¬ Coll5 L zx zf Xr zr Xg zg) (hE : Yr = Yg → LemEF zp L zx zf Xr zr Xg zg) :
    ClassX5 σ L zx zf Xr Yr zr Xg Yg zg := by
  rcases hx with ⟨h1, h2, h3, h4, h5⟩ | h | h | ⟨h1, h2, h3, h4⟩ | h
  · refine Or.inl ⟨h1, h2, h3, h4, h5, hPi_of hσ h3 (by linarith) h4 (hnc h1.symm) (hE h1.symm)⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · have hXr : 0 < Xr := by rw [h1, h2] at hcg; nlinarith
    refine Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2, h3, h4,
      hPi_of hσ hXr (by linarith) (by rw [h2, h3]; ring) (hnc h1.symm) (hE h1.symm)⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

end Type08Sp
end Minimality
