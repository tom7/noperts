module

public import Minimality.Type08S.P2H4

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# pkH H5: P-H, SC-d for both orientations (σ = ±1, the `K_2` mirror), and the combined top lemma

* `SCcert`: the decoupled criterion (R) of Lemma SC for a top side, as numbers (`χ`, `Φ`).
* `certD_of`: `ClassD5` ⇒ `SCcert` (the motions of `lemmaSCd_I` / `lemmaSCd_II`, extracted).
* `cert_neg`: (R) is invariant under the depth reflection, so `ClassD5` of the reflected depths gives (R) too.
* `lemmaSCd_any`: (R) ⇒ Rupert, for **any** orientation `σ` (`lemmaSC_s`).
* `lemmaSC8`: class (c) (SC-c), class (d) in either orientation (SC-d), chord end at `x` (SC-X) ⇒ Rupert.
-/

set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

/-- Criterion (R) of Lemma SC for the five-corner rim with a top side (frame numbers). -/
def SCcert (zp L zx zf Xr zr Xg zg : ℝ) : Prop :=
  ∃ φ0 φ1 θ χ0 χ1 : ℝ, χ0 + χ1 * zf < 0 ∧ χ0 + χ1 * zr < 0 ∧ 0 < χ0 + χ1 * zg ∧ 0 < χ0 + χ1 * zx ∧
    0 < φ0 + φ1 * zp + θ * 0 ∧ 0 < φ0 + φ1 * zf + θ * L ∧ φ0 + φ1 * zr + θ * Xr < 0 ∧
    φ0 + φ1 * zg + θ * Xg < 0 ∧
    0 ≤ (χ0 + χ1 * zx) + (φ0 + φ1 * zx + θ * 0) ∧ 0 ≤ (χ0 + χ1 * zp) + (φ0 + φ1 * zp + θ * 0)

/-- **SC-d's motions** (cases I and II of `lemmaSCd_I/II`) as a certificate. -/
theorem certD_of {zp L zx zf Xr Yr zr Xg Yg zg : ℝ} (hL : 0 < L)
    (h : ClassD5 zp L zx zf Xr Yr zr Xg Yg zg) : SCcert zp L zx zf Xr zr Xg zg := by
  obtain ⟨σ0, m, Xx, z0, hYY, hXrg, hzz, hσ0, hm, hD1, hD2, hX0, hXL, hch, hz⟩ := h
  have hσL := sigmaL_gt hX0 hXL hD2 hch
  rcases hz with ⟨hz1, hz2, hz3, hz4, hz5⟩ | ⟨hz1, hz2, hz3, hz4⟩
  · obtain ⟨η, hη, h1, h2, h3⟩ := exists_small (σ0 - z0) (σ0 - zp) (σ0 + m * L - zf)
      (by linarith) (by linarith) (by linarith)
    refine ⟨σ0 - η, -1, m, -z0, 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith
  · obtain ⟨η, hη, h1, h2, h3⟩ := exists_small (zx - σ0) (σ0 - zp) (σ0 + m * L - zf)
      (by linarith) (by linarith) (by linarith)
    set K := (|σ0 - η - zx| + |σ0 - η - zp|) / (z0 - zx) + 1 with hK
    have hd : 0 < z0 - zx := by linarith
    have hKd : K * (z0 - zx) = |σ0 - η - zx| + |σ0 - η - zp| + (z0 - zx) := by
      rw [hK]; field_simp
    have hKp : 0 < K := by
      rw [hK]; have := abs_nonneg (σ0 - η - zx); have := abs_nonneg (σ0 - η - zp)
      positivity
    clear_value K
    have a1 := neg_abs_le (σ0 - η - zx)
    have a2 := neg_abs_le (σ0 - η - zp)
    have a3 := abs_nonneg (σ0 - η - zx)
    have a4 := abs_nonneg (σ0 - η - zp)
    have b1 := mul_pos hKp (sub_pos.2 hz1)
    have b2 := mul_pos hKp (sub_pos.2 hz2)
    have b3 := mul_pos hKp (sub_pos.2 hz3)
    have b5 := mul_pos hKp (sub_pos.2 hzz)
    refine ⟨σ0 - η, -1, m, K * z0, -K, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith

/-- (R) is invariant under `z ↦ -z` (`χ1`, `φ1` change sign). -/
theorem cert_neg {zp L zx zf Xr zr Xg zg : ℝ} (h : SCcert (-zp) L (-zx) (-zf) Xr (-zr) Xg (-zg)) :
    SCcert zp L zx zf Xr zr Xg zg := by
  obtain ⟨φ0, φ1, θ, χ0, χ1, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  refine ⟨φ0, -φ1, θ, χ0, -χ1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- **SC-d in either orientation**: (R) ⇒ Rupert, any `σ` with `σ (zx - zp) > 0`. -/
theorem lemmaSCd_any (hF : Fr e1 e2 e3) (o : ℝ³) (E : Finset ℝ³)
    {σ L zp zx zf Xr Yr zr Xg Yg zg : ℝ}
    (hL : 0 < L) (hzx : 0 < σ * (zx - zp)) (hYr : 0 < Yr) (hYrg : Yg = Yr) (hXrg : Xg < Xr)
    (hc : SCcert zp L zx zf Xr zr Xg zg)
    (hE : ∀ᶠ s : ℝ in atTop, ∀ y ∈ E, TriCert (rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yg zg E)
      (pc e1 e2 e3 0 0 1) (pc e1 e2 e3 (σ * s) (-σ) 0) y) :
    IsRupert (rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yg zg E) := by
  obtain ⟨φ0, φ1, θ, χ0, χ1, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hc
  exact lemmaSC_s hF o E hL hzx hYr hYrg hXrg h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 hE

/-- The persistent classes closed at first order: SC-c, SC-d (both orientations), SC-X. -/
def Top8 (σ zp L zx zf Xr Yr zr Xg Yg zg : ℝ) : Prop :=
  ClassC5 L zx zf Xr Yr zr Xg Yg zg ∨ (Yg = Yr ∧ Xg < Xr ∧ SCcert zp L zx zf Xr zr Xg zg) ∨
    ClassX5 σ L zx zf Xr Yr zr Xg Yg zg

theorem lemmaSC8 (hF : Fr e1 e2 e3) (o : ℝ³) (E : Finset ℝ³)
    {σ zp L zx zf Xr Yr zr Xg Yg zg : ℝ}
    (hL : 0 < L) (hzx : 0 < σ * (zx - zp))
    (hcr : 0 < (Xg - Xr) * (-Yr) - (Yg - Yr) * (L - Xr)) (hYr : 0 < Yr) (hYg : 0 < Yg)
    (hcg : 0 < Yg * Xr - Xg * Yr) (hc : Top8 σ zp L zx zf Xr Yr zr Xg Yg zg)
    (hE : ∀ᶠ s : ℝ in atTop, ∀ y ∈ E, TriCert (rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yg zg E)
      (pc e1 e2 e3 0 0 1) (pc e1 e2 e3 (σ * s) (-σ) 0) y) :
    IsRupert (rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yg zg E) := by
  rcases hc with hc | ⟨h1, h2, h3⟩ | hc
  · exact lemmaSCc hF o E hL hzx hcr hYr hYg hcg hc hE
  · exact lemmaSCd_any hF o E hL hzx hYr h1 h2 h3 hE
  · exact lemmaSCX hF o E hL hzx hcr hYr hYg hcg hc hE

end Type08Sp
end Minimality
