module

public import Minimality.Type08S.P2SCXm

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# Lemma SC-X, end case: top vertex `g` over the apex (`Xg = 0`, `zg = zx`, `Yr < Yg`)  (sp08f §3, table row 1)
-/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

/-- **SC-X, top vertex `g` at `λ = 0`, `z_g = z_x`.**  Robustness: `f`, `r` strictly on one side of `z_x`.
Motion: `θ = (1 - η/s)/Y_g` (so `1 - θ Y_g = η/s`), `N = -M (z_f - z_x)`, `k ≈ M`. -/
theorem lemmaSCX_gvert (hF : Fr e1 e2 e3) (o : ℝ³) (E : Finset ℝ³)
    {σ L zp zx zf Xr Yr zr Xg Yg zg : ℝ}
    (hL : 0 < L) (hzx : 0 < σ * (zx - zp))
    (hcr : 0 < (Xg - Xr) * (-Yr) - (Yg - Yr) * (L - Xr)) (hYr : 0 < Yr) (hYrg : Yr < Yg)
    (hcg : 0 < Yg * Xr - Xg * Yr)
    (hXg : Xg = 0) (hzg : zg = zx) (hrob : 0 < (zf - zx) * (zr - zx))
    (hE : ∀ᶠ s : ℝ in atTop, ∀ y ∈ E, TriCert (rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yg zg E)
      (pc e1 e2 e3 0 0 1) (pc e1 e2 e3 (σ * s) (-σ) 0) y) :
    IsRupert (rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yg zg E) := by
  subst hXg
  subst zg
  have hYg : 0 < Yg := by linarith
  have hXr : 0 < Xr := by
    by_contra h; have h' := not_lt.1 h; nlinarith
  have huf : zf - zx ≠ 0 := fun h => by rw [h] at hrob; simp at hrob
  have huf2 : 0 < (zf - zx) ^ 2 := by positivity
  have hYY : 0 < Yg - Yr := by linarith
  set θ0 : ℝ := 1 / Yg with hθ0
  have hθ : θ0 * Yg = 1 := by rw [hθ0]; field_simp
  have hθpos : 0 < θ0 := by rw [hθ0]; positivity
  set η0 : ℝ := Xr / (4 * (Yg - Yr) * Yg) with hη0
  have hηpos : 0 < η0 := by rw [hη0]; positivity
  have hη2 : (Yg - Yr) * η0 * Yg = Xr / 4 := by rw [hη0]; field_simp
  have eM5 := ev_lin (α := Yr * (zf - zx) ^ 2) (β := (Xr - L) * θ0 * L - Yr) (mul_pos hYr huf2)
  have eM7 := ev_lin (α := (Yg - Yr) * ((zf - zx) * (zr - zx)))
    (β := -Xr * θ0 * Xr - (Yg - Yr) * (1 - θ0 * Yr)) (mul_pos hYY hrob)
  have eM8 := ev_lin (α := Yr * ((zf - zx) * (zr - zx)))
    (β := (Xr - L) * θ0 * Xr - Yr * (1 - θ0 * Yr)) (mul_pos hYr hrob)
  obtain ⟨M, ⟨h5, h7⟩, h8⟩ := ((eM5.and eM7).and eM8).exists
  set N : ℝ := -M * (zf - zx) with hN
  have ek1 := ev_lin (α := σ * (zx - zp)) (β := -1) hzx
  have ek2 := ev_lin (α := σ * (zx - zp)) (β := -(N * (zx - zp) + 1)) hzx
  obtain ⟨k, hk1, hk2⟩ := (ek1.and ek2).exists
  refine scx_wrap hF o E (θ0 := θ0) (η0 := η0) (N := N) (k := k) hL hzx hcr hYr hYg hcg
    (by nlinarith) (by nlinarith) ?_ ?_ ?_ ?_ ?_ ?_ hE
  · left; simp only [rA, hN]; nlinarith
  · left; simp only [rA]; nlinarith [mul_pos hθpos hL]
  · left; simp only [rA, hN]; nlinarith
  · left; simp only [rA, hN]; nlinarith
  · right; constructor
    · simp only [rA]; linear_combination (-Yg) * hθ
    · simp only [rC]; nlinarith [mul_pos (mul_pos hYg hηpos) hYg]
  · right; constructor
    · simp only [rA]; linear_combination (Yg - Yr) * hθ
    · simp only [rC]; nlinarith

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.lemmaSCX_gvert
