module

public import Minimality.Type16UE
public import Minimality.Type16UC

@[expose] public section


/-!
# U1: the frame at the edge view `s06` with corner `e = 6` (type 16, normal form)

`p = x3 - x6`, `q = x4 - x6`, `r = x6 - x0`, `d = x6`.  A point `nfP (α, β, γ)` has screen coordinates
`(1 - α - γ + sβ, β/q, pβ/q - α)`, `s = (p+r-1)/q` (normal-form parameters).
-/

set_option autoImplicit true
set_option linter.unusedVariables false
open scoped RealInnerProductSpace
open Finset Filter

namespace Minimality
namespace H16U
open TwoRay Type08Sp Type08Sp.C2 V2

variable {x : Fin 7 → ℝ³}

theorem frame6_det (N : NF16 x) : det3 (x 3 - x 6) (x 4 - x 6) (x 6 - x 0) ≠ 0 := by
  have h1 : x 3 - x 6 = nfV N.E₁ N.E₂ N.E₃ 0 0 (-1) := by
    rw [N.x3, N.x6, nfP_sub]; norm_num
  have h2 : x 4 - x 6 = nfV N.E₁ N.E₂ N.E₃ N.p N.q (N.r - 1) := by
    rw [N.x4, N.x6, nfP_sub]; norm_num
  have h3 : x 6 - x 0 = nfV N.E₁ N.E₂ N.E₃ (-1) 0 1 := by
    rw [N.x6, N.x0, nfP_sub]; norm_num
  rw [h1, h2, h3, det3_nfV]
  have : det3c 0 0 (-1) N.p N.q (N.r - 1) (-1) 0 1 = -N.q := by unfold det3c; ring
  rw [this]
  exact mul_ne_zero (neg_ne_zero.2 N.hq.ne') N.hD

theorem nfP_eq_fpoint (N : NF16 x) (α β γ : ℝ) :
    nfP N.o N.E₁ N.E₂ N.E₃ α β γ =
      fpoint (x 3 - x 6) (x 4 - x 6) (x 6 - x 0) (x 6)
        (1 - α - γ + (N.p + N.r - 1) / N.q * β, β / N.q, N.p * β / N.q - α) := by
  have hq := N.hq.ne'
  have h3 := N.x3; have h4 := N.x4; have h6 := N.x6; have h0 := N.x0
  simp only [fpoint, fcomb, h3, h4, h6, h0, nfP]
  match_scalars <;> field_simp <;> ring


/-- Depths along `u = x6 - x0` in the normal form. -/
theorem depth_nf (N : NF16 x) (α β γ : ℝ) :
    ⟪nfP N.o N.E₁ N.E₂ N.E₃ α β γ, x 6 - x 0⟫ =
      ⟪N.o, x 6 - x 0⟫ + α * ⟪N.E₁, x 6 - x 0⟫ + β * ⟪N.E₂, x 6 - x 0⟫ + γ * ⟪N.E₃, x 6 - x 0⟫ :=
  inner_nfP _ _ _ _ _ _ _ _

theorem m13_pos (N : NF16 x) : ⟪N.E₁, x 6 - x 0⟫ < ⟪N.E₃, x 6 - x 0⟫ := by
  have : N.E₃ - N.E₁ = x 6 - x 0 := by
    have h6 := N.x6; have h0 := N.x0
    simp only [nfP] at h6 h0
    rw [h6, h0]; module
  have h : 0 < ⟪x 6 - x 0, x 6 - x 0⟫ := real_inner_self_pos.2 (sub_ne_zero.2 (fun e => by
    have := N.inj e; revert this; decide))
  have e : ⟪x 6 - x 0, x 6 - x 0⟫ = ⟪N.E₃, x 6 - x 0⟫ - ⟪N.E₁, x 6 - x 0⟫ := by
    rw [← inner_sub_left, this]
  linarith

theorem m2_eq (N : NF16 x) : ⟪N.E₂, x 6 - x 0⟫ = ⟪x 5 - x 3, x 6 - x 0⟫ := by
  have h5 := N.x5; have h3 := N.x3
  simp only [nfP] at h5 h3
  have : N.E₂ = x 5 - x 3 := by rw [h5, h3]; module
  rw [this]

theorem R1_neg (T : Type16 x) (P : Par T) (hF : 0 < T.ff 5 (x 6) - T.ff 5 (x 0)) :
    (P.N.g - 1) * (P.N.p + P.N.r) - P.N.d * (P.N.q - 1) < 0 := by
  have h := P.eF
  have hpd : 0 < P.N.p * P.N.d := mul_pos P.N.hp P.N.hd
  have h1 : 0 < (T.ff 5 (x 6) - T.ff 5 (x 0)) * (P.N.p * P.N.d) := mul_pos hF hpd
  rw [h] at h1
  by_contra hc; push Not at hc
  nlinarith [mul_nonpos_of_nonpos_of_nonneg P.ht3.le hc]

theorem R2_neg (T : Type16 x) (P : Par T) (hH : T.ff 7 (x 6) - T.ff 7 (x 0) < 0) :
    (P.N.b - 1) * (P.N.p + P.N.r) - P.N.a * (P.N.q - 1) < 0 := by
  have h := P.eH
  have hpd : 0 < P.N.a * P.N.r := mul_pos P.N.ha P.N.hr
  have h1 : (T.ff 7 (x 6) - T.ff 7 (x 0)) * (P.N.a * P.N.r) < 0 := mul_neg_of_neg_of_pos hH hpd
  rw [h] at h1
  by_contra hc; push Not at hc
  nlinarith [mul_nonneg (neg_nonneg.2 P.hh3.le) hc]

theorem R2_pos (T : Type16 x) (P : Par T) (hH : 0 < T.ff 7 (x 6) - T.ff 7 (x 0)) :
    0 < (P.N.b - 1) * (P.N.p + P.N.r) - P.N.a * (P.N.q - 1) := by
  have h := P.eH
  have hpd : 0 < P.N.a * P.N.r := mul_pos P.N.ha P.N.hr
  have h1 : 0 < (T.ff 7 (x 6) - T.ff 7 (x 0)) * (P.N.a * P.N.r) := mul_pos hH hpd
  rw [h] at h1
  by_contra hc; push Not at hc
  nlinarith [mul_nonneg (neg_nonneg.2 P.hh3.le) (neg_nonneg.2 hc)]

end H16U
end Minimality
