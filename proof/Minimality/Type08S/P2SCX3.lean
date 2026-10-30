module

public import Minimality.Type08S.P2SCXm

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# Lemma SC-X, end case: near end `g` of a top side over the apex (`Xg = 0`, `zg = zx`, `Yg = Yr`)
(sp08f §3, table row 3).  Uses `x ∉ Π'`.
-/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

/-- **SC-X, near end `g` of the top side `[g, r]`** (`Yg = Yr`, `Xg = 0 < Xr`, `z_g = z_x`).
Robustness: `f`, `r` strictly on one side of `z_x`.  `x ∉ Π'` is `hPi`: the line of the top side, evaluated
at `λ = L`, is on the `σ`-positive side of `z_f` (times `Xr > 0`).
Motion: `θ = -β s_σ = η/s·(-1)` (so `V_Y ≡ B` along the top side), `θ0 = 0`. -/
theorem lemmaSCX_gend (hF : Fr e1 e2 e3) (o : ℝ³) (E : Finset ℝ³)
    {σ L zp zx zf Xr Yr zr Xg Yg zg : ℝ}
    (hL : 0 < L) (hzx : 0 < σ * (zx - zp))
    (hcr : 0 < (Xg - Xr) * (-Yr) - (Yg - Yr) * (L - Xr)) (hYr : 0 < Yr) (hYg : 0 < Yg)
    (hYrg : Yg = Yr) (hcg : 0 < Yg * Xr - Xg * Yr)
    (hXg : Xg = 0) (hzg : zg = zx) (hrob : 0 < (zf - zx) * (zr - zx))
    (hPi : 0 < σ * ((zr - zx) * L - (zf - zx) * Xr))
    (hE : ∀ᶠ s : ℝ in atTop, ∀ y ∈ E, TriCert (rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yg zg E)
      (pc e1 e2 e3 0 0 1) (pc e1 e2 e3 (σ * s) (-σ) 0) y) :
    IsRupert (rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yg zg E) := by
  subst hXg
  subst zg
  subst Yg
  have hXr : 0 < Xr := by
    by_contra h; have h' := not_lt.1 h; nlinarith
  have huf : zf - zx ≠ 0 := fun h => by rw [h] at hrob; simp at hrob
  have huf2 : 0 < (zf - zx) ^ 2 := by positivity
  have eM5 := ev_lin (α := Yr * (zf - zx) ^ 2) (β := -Yr) (mul_pos hYr huf2)
  have eM8 := ev_lin (α := Yr * ((zf - zx) * (zr - zx))) (β := -Yr) (mul_pos hYr hrob)
  obtain ⟨M, h5, h8⟩ := (eM5.and eM8).exists
  set N : ℝ := -M * (zf - zx) with hN
  have ek1 := ev_lin (α := σ * (zx - zp)) (β := -1) hzx
  have ek2 := ev_lin (α := σ * (zx - zp)) (β := -(N * (zx - zp) + 1)) hzx
  have hαk : 0 < σ * ((zr - zx) * L - (zf - zx) * Xr) / Xr := div_pos hPi hXr
  have ek3 := ev_lin (α := σ * ((zr - zx) * L - (zf - zx) * Xr) / Xr) (β := -1 / 2) hαk
  obtain ⟨k, hk1, hk2, hk3⟩ := (ek1.and (ek2.and ek3)).exists
  set η0 : ℝ := -(σ * k) * (zr - zx) / Xr with hη0
  have hη : η0 * Xr = -(σ * k) * (zr - zx) := by rw [hη0]; field_simp
  refine scx_wrap hF o E (θ0 := 0) (η0 := η0) (N := N) (k := k) hL hzx hcr hYr hYr hcg
    (by nlinarith) (by nlinarith) ?_ ?_ ?_ ?_ ?_ ?_ hE
  · left; simp only [rA, hN]; nlinarith
  · right; constructor
    · simp only [rA]; ring
    · simp only [rC]
      have : (η0 * L + σ * k * (zf - zx) + 1 / 2) = - (σ * ((zr - zx) * L - (zf - zx) * Xr) / Xr * k) + 1 / 2 := by
        rw [hη0]; field_simp; ring
      nlinarith
  · right; constructor
    · simp only [rA]; ring
    · simp only [rC]; nlinarith
  · left; simp only [rA, hN]; nlinarith
  · left; simp only [rA]; nlinarith
  · right; constructor
    · simp only [rA]; ring
    · simp only [rC]; nlinarith

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.lemmaSCX_gend
