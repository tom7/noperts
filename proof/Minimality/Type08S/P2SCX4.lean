module

public import Minimality.Type08S.P2SCXm

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# Lemma SC-X, end case: far end `r` of a top side over the apex (`Xr = 0`, `zr = zx`, `Yg = Yr`)
(sp08f §3, table row 4).
-/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

/-- **SC-X, far end `r` of the top side `[g, r]`** (`Yg = Yr`, `Xg < 0 = Xr`, `z_r = z_x`).
Robustness: `f`, `g` strictly on opposite sides of `z_x`.  Motion: `θ = 1/Y_r`. -/
theorem lemmaSCX_rend (hF : Fr e1 e2 e3) (o : ℝ³) (E : Finset ℝ³)
    {σ L zp zx zf Xr Yr zr Xg Yg zg : ℝ}
    (hL : 0 < L) (hzx : 0 < σ * (zx - zp))
    (hcr : 0 < (Xg - Xr) * (-Yr) - (Yg - Yr) * (L - Xr)) (hYr : 0 < Yr) (hYg : 0 < Yg)
    (hYrg : Yg = Yr) (hcg : 0 < Yg * Xr - Xg * Yr)
    (hXr : Xr = 0) (hzr : zr = zx) (hrob : (zf - zx) * (zg - zx) < 0)
    (hE : ∀ᶠ s : ℝ in atTop, ∀ y ∈ E, TriCert (rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yg zg E)
      (pc e1 e2 e3 0 0 1) (pc e1 e2 e3 (σ * s) (-σ) 0) y) :
    IsRupert (rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yg zg E) := by
  subst hXr
  subst zr
  subst Yg
  have hXg : Xg < 0 := by
    by_contra h; have h' := not_lt.1 h; nlinarith
  have huf : zf - zx ≠ 0 := fun h => by rw [h] at hrob; simp at hrob
  have huf2 : 0 < (zf - zx) ^ 2 := by positivity
  set θ0 : ℝ := 1 / Yr with hθ0
  have hθ : θ0 * Yr = 1 := by rw [hθ0]; field_simp
  have hθpos : 0 < θ0 := by rw [hθ0]; positivity
  have hneg : 0 < -((zf - zx) * (zg - zx)) := by linarith
  have eM5 := ev_lin (α := Yr * (zf - zx) ^ 2) (β := (0 - L) * θ0 * L - Yr) (mul_pos hYr huf2)
  have eM9 := ev_lin (α := Yr * (-((zf - zx) * (zg - zx)))) (β := -Xg * θ0 * Xg)
    (mul_pos hYr hneg)
  obtain ⟨M, h5, h9⟩ := (eM5.and eM9).exists
  set N : ℝ := -M * (zf - zx) with hN
  have ek1 := ev_lin (α := σ * (zx - zp)) (β := -1) hzx
  have ek2 := ev_lin (α := σ * (zx - zp)) (β := -(N * (zx - zp) + 1)) hzx
  obtain ⟨k, hk1, hk2⟩ := (ek1.and ek2).exists
  refine scx_wrap hF o E (θ0 := θ0) (η0 := 0) (N := N) (k := k) hL hzx hcr hYr hYr hcg
    (by nlinarith) (by nlinarith) ?_ ?_ ?_ ?_ ?_ ?_ hE
  · left; simp only [rA, hN]; nlinarith
  · left; simp only [rA]; nlinarith [mul_pos hθpos hL]
  · right; constructor
    · simp only [rA]; ring
    · simp only [rC]; nlinarith
  · right; constructor
    · simp only [rA]; linear_combination Yr * hθ
    · simp only [rC]; nlinarith
  · left; simp only [rA, hN]; nlinarith
  · left; simp only [rA]; nlinarith [mul_pos hθpos (mul_self_pos.2 hXg.ne)]

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.lemmaSCX_rend
