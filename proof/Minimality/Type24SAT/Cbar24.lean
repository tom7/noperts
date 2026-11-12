module

public import Minimality.Type24SAT.Facets24
public import Minimality.Type24

@[expose] public section

/-!
# Type 24, the C-bar reading: `omega3, omega4, omega5 > 0, Delta >= 0` as the encoder's facing literals

The tree's type 24 residual hypothesis (`not_type24_outside_Cbar_of_isNopert`, `Minimality.omega3/4/5`, `Minimality.Delta24`,
oblique coordinates at `y 1` in the frame `y 0 - y 1, y 2 - y 1, y 6 - y 1`) against the literals of the encoder
(`Sem24`: `H:01 = fc 7 0 1`, `E:12 = fc 4 1 2`, `C:16 = fc 2 1 6`, `NCEH = nv 2 4 7`):
  `omega3 > 0` gives `H:01-`, `omega4 > 0` gives `E:12+`, `omega5 > 0` gives `C:16+`,
  all three and `Delta > 0` give `NCEH+` (and `Delta >= 0` gives `NCEH >= 0`).
Orientation is the hypothesis `Convex24 (ext y)` (the orientation of the labelled reference shape), as in `Facets24`.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
open scoped RealInnerProductSpace

namespace Minimality.T24.SAT
open Minimality

section
variable (y : Fin 7 → ℝ³)

private theorem e0 : ext y 0 = y 0 := rfl
private theorem e1 : ext y 1 = y 1 := rfl
private theorem e2 : ext y 2 = y 2 := rfl
private theorem e3 : ext y 3 = y 3 := rfl
private theorem e4 : ext y 4 = y 4 := rfl
private theorem e5 : ext y 5 = y 5 := rfl
private theorem e6 : ext y 6 = y 6 := rfl

/-- The H identity: `(n7 . (x0 - x1)) * X0num = (X2num + X6num - D) * (n7 . (x1 - x2))`. -/
theorem H_id : ⟪nrm (ext y) 7, ext y 0 - ext y 1⟫ * vol3 (y 3 - y 1) (y 2 - y 1) (y 6 - y 1) =
    (vol3 (y 0 - y 1) (y 3 - y 1) (y 6 - y 1) + vol3 (y 0 - y 1) (y 2 - y 1) (y 3 - y 1)
      - vol3 (y 0 - y 1) (y 2 - y 1) (y 6 - y 1)) * ⟪nrm (ext y) 7, ext y 1 - ext y 2⟫ := by
  rw [inner_eq_dot, inner_eq_dot, toV3_nrm]
  simp only [pt, nrm3, toV3, fa_7, fb_7, fc_7, sg_7, V3.smul, V3.cr, V3.dot, V3.sub, e0, e1, e2, e3, e6, vol3,
    PiLp.sub_apply]
  push_cast
  ring

/-- The E identity: `(n4 . (x1 - x2)) * X2num(4) = (X0num(4) + X6num(4) - D) * (-(n4 . (x1 - x0)))`. -/
theorem E_id : ⟪nrm (ext y) 4, ext y 1 - ext y 2⟫ * vol3 (y 0 - y 1) (y 4 - y 1) (y 6 - y 1) =
    (vol3 (y 4 - y 1) (y 2 - y 1) (y 6 - y 1) + vol3 (y 0 - y 1) (y 2 - y 1) (y 4 - y 1)
      - vol3 (y 0 - y 1) (y 2 - y 1) (y 6 - y 1)) * (-⟪nrm (ext y) 4, ext y 1 - ext y 0⟫) := by
  rw [inner_eq_dot, inner_eq_dot, toV3_nrm]
  simp only [pt, nrm3, toV3, fa_4, fb_4, fc_4, sg_4, V3.smul, V3.cr, V3.dot, V3.sub, e0, e1, e2, e4, e6, vol3,
    PiLp.sub_apply]
  push_cast
  ring

/-- The C identity: `(n2 . (x1 - x6)) * X6num(5) = (X0num(5) + X2num(5) - D) * (-(n2 . (x1 - x0)))`. -/
theorem C_id : ⟪nrm (ext y) 2, ext y 1 - ext y 6⟫ * vol3 (y 0 - y 1) (y 2 - y 1) (y 5 - y 1) =
    (vol3 (y 5 - y 1) (y 2 - y 1) (y 6 - y 1) + vol3 (y 0 - y 1) (y 5 - y 1) (y 6 - y 1)
      - vol3 (y 0 - y 1) (y 2 - y 1) (y 6 - y 1)) * (-⟪nrm (ext y) 2, ext y 1 - ext y 0⟫) := by
  rw [inner_eq_dot, inner_eq_dot, toV3_nrm]
  simp only [pt, nrm3, toV3, fa_2, fb_2, fc_2, sg_2, V3.smul, V3.cr, V3.dot, V3.sub, e0, e1, e2, e5, e6, vol3,
    PiLp.sub_apply]
  push_cast
  ring

/-- `omega3 > 0` as a quotient of brackets, with both denominators nonzero. -/
theorem omega3_eq (h : 0 < omega3 y) : det24 y ≠ 0 ∧ vol3 (y 3 - y 1) (y 2 - y 1) (y 6 - y 1) ≠ 0 ∧
    omega3 y = (vol3 (y 0 - y 1) (y 3 - y 1) (y 6 - y 1) + vol3 (y 0 - y 1) (y 2 - y 1) (y 3 - y 1)
      - vol3 (y 0 - y 1) (y 2 - y 1) (y 6 - y 1)) / vol3 (y 3 - y 1) (y 2 - y 1) (y 6 - y 1) := by
  have hD : det24 y ≠ 0 := by
    intro hD; simp [omega3, oblX0, oblX2, oblX6, hD] at h
  have hX : vol3 (y 3 - y 1) (y 2 - y 1) (y 6 - y 1) ≠ 0 := by
    intro hX; simp [omega3, oblX0, hX] at h
  refine ⟨hD, hX, ?_⟩
  have hD' : vol3 (y 0 - y 1) (y 2 - y 1) (y 6 - y 1) ≠ 0 := hD
  simp only [omega3, oblX0, oblX2, oblX6, det24]
  field_simp

theorem omega4_eq (h : 0 < omega4 y) : det24 y ≠ 0 ∧ vol3 (y 0 - y 1) (y 4 - y 1) (y 6 - y 1) ≠ 0 ∧
    omega4 y = (vol3 (y 4 - y 1) (y 2 - y 1) (y 6 - y 1) + vol3 (y 0 - y 1) (y 2 - y 1) (y 4 - y 1)
      - vol3 (y 0 - y 1) (y 2 - y 1) (y 6 - y 1)) / vol3 (y 0 - y 1) (y 4 - y 1) (y 6 - y 1) := by
  have hD : det24 y ≠ 0 := by
    intro hD; simp [omega4, oblX0, oblX2, oblX6, hD] at h
  have hX : vol3 (y 0 - y 1) (y 4 - y 1) (y 6 - y 1) ≠ 0 := by
    intro hX; simp [omega4, oblX2, hX] at h
  refine ⟨hD, hX, ?_⟩
  have hD' : vol3 (y 0 - y 1) (y 2 - y 1) (y 6 - y 1) ≠ 0 := hD
  simp only [omega4, oblX0, oblX2, oblX6, det24]
  field_simp

theorem omega5_eq (h : 0 < omega5 y) : det24 y ≠ 0 ∧ vol3 (y 0 - y 1) (y 2 - y 1) (y 5 - y 1) ≠ 0 ∧
    omega5 y = (vol3 (y 5 - y 1) (y 2 - y 1) (y 6 - y 1) + vol3 (y 0 - y 1) (y 5 - y 1) (y 6 - y 1)
      - vol3 (y 0 - y 1) (y 2 - y 1) (y 6 - y 1)) / vol3 (y 0 - y 1) (y 2 - y 1) (y 5 - y 1) := by
  have hD : det24 y ≠ 0 := by
    intro hD; simp [omega5, oblX0, oblX2, oblX6, hD] at h
  have hX : vol3 (y 0 - y 1) (y 2 - y 1) (y 5 - y 1) ≠ 0 := by
    intro hX; simp [omega5, oblX6, hX] at h
  refine ⟨hD, hX, ?_⟩
  have hD' : vol3 (y 0 - y 1) (y 2 - y 1) (y 6 - y 1) ≠ 0 := hD
  simp only [omega5, oblX0, oblX2, oblX6, det24]
  field_simp

/-- Multiplicative form: `A * X = N * B`, `X ≠ 0` gives `A = N / X * B`. -/
theorem mul_form {A B N X : ℝ} (hX : X ≠ 0) (h : A * X = N * B) : A = N / X * B := by
  field_simp; linarith

/-- `n7 . (x0 - x1) = omega3 * (n7 . (x1 - x2))`. -/
theorem H_val (h : 0 < omega3 y) : ⟪nrm (ext y) 7, ext y 0 - ext y 1⟫ = omega3 y * ⟪nrm (ext y) 7, ext y 1 - ext y 2⟫ := by
  obtain ⟨_, hX, he⟩ := omega3_eq y h
  rw [he]; exact mul_form hX (H_id y)

/-- `n4 . (x1 - x2) = omega4 * cv(4,1)`. -/
theorem E_val (h : 0 < omega4 y) : ⟪nrm (ext y) 4, ext y 1 - ext y 2⟫ = omega4 y * (-⟪nrm (ext y) 4, ext y 1 - ext y 0⟫) := by
  obtain ⟨_, hX, he⟩ := omega4_eq y h
  rw [he]; exact mul_form hX (E_id y)

/-- `n2 . (x1 - x6) = omega5 * cv(2,1)`. -/
theorem C_val (h : 0 < omega5 y) : ⟪nrm (ext y) 2, ext y 1 - ext y 6⟫ = omega5 y * (-⟪nrm (ext y) 2, ext y 1 - ext y 0⟫) := by
  obtain ⟨_, hX, he⟩ := omega5_eq y h
  rw [he]; exact mul_form hX (C_id y)

theorem cv71 (hC : Convex24 (ext y)) : 0 < -⟪nrm (ext y) 7, ext y 1 - ext y 2⟫ := by
  have h := hC (7, 1) (by decide)
  simpa [cv, fa_7, e2] using h

theorem cv41 (hC : Convex24 (ext y)) : 0 < -⟪nrm (ext y) 4, ext y 1 - ext y 0⟫ := by
  have h := hC (4, 1) (by decide)
  simpa [cv, fa_4, e0] using h

theorem cv21 (hC : Convex24 (ext y)) : 0 < -⟪nrm (ext y) 2, ext y 1 - ext y 0⟫ := by
  have h := hC (2, 1) (by decide)
  simpa [cv, fa_2, e0] using h

/-- **`omega3 > 0` is `H:01-`.** -/
theorem cbar_H (hC : Convex24 (ext y)) (h : 0 < omega3 y) : LitHolds (ext y) (.fc 7 0 1) (-1) := by
  simp only [LitHolds, val]
  rw [H_val y h]
  have := cv71 y hC
  push_cast
  nlinarith

/-- **`omega4 > 0` is `E:12+`.** -/
theorem cbar_E (hC : Convex24 (ext y)) (h : 0 < omega4 y) : LitHolds (ext y) (.fc 4 1 2) 1 := by
  simp only [LitHolds, val]
  rw [E_val y h]
  have := cv41 y hC
  push_cast
  nlinarith

/-- **`omega5 > 0` is `C:16+`.** -/
theorem cbar_C (hC : Convex24 (ext y)) (h : 0 < omega5 y) : LitHolds (ext y) (.fc 2 1 6) 1 := by
  simp only [LitHolds, val]
  rw [C_val y h]
  have := cv21 y hC
  push_cast
  nlinarith

/-- Binet-Cauchy: `det (n1,n2,n3) * det (a,b,c) = det [n_i . e_j]`. -/
theorem binet_cauchy (n1 n2 n3 a b c : ℝ³) :
    det3 n1 n2 n3 * vol3 a b c =
      ⟪n1, a⟫ * (⟪n2, b⟫ * ⟪n3, c⟫ - ⟪n2, c⟫ * ⟪n3, b⟫) - ⟪n1, b⟫ * (⟪n2, a⟫ * ⟪n3, c⟫ - ⟪n2, c⟫ * ⟪n3, a⟫)
      + ⟪n1, c⟫ * (⟪n2, a⟫ * ⟪n3, b⟫ - ⟪n2, b⟫ * ⟪n3, a⟫) := by
  simp only [det3_expand, vol3, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]
  ring

/-- The frame determinant is `cv(0,6)`. -/
theorem det24_eq : det24 y = -⟪nrm (ext y) 0, ext y 6 - ext y 0⟫ := by
  unfold det24
  rw [inner_eq_dot, toV3_nrm]
  simp only [pt, nrm3, toV3, fa_0, fb_0, fc_0, sg_0, V3.smul, V3.cr, V3.dot, V3.sub, e0, e1, e2, e6, vol3,
    PiLp.sub_apply]
  push_cast
  ring

theorem det24_pos (hC : Convex24 (ext y)) : 0 < det24 y := by
  have h := hC (0, 6) (by decide)
  rw [det24_eq]
  simpa [cv, fa_0, e0] using h

/-- **The product formula**: `NCEH * D = cv(2,1) cv(4,1) cv(7,2) * Delta` (when all three omegas are positive). -/
theorem nceh_formula (h3 : 0 < omega3 y) (h4 : 0 < omega4 y) (h5 : 0 < omega5 y) :
    det3 (nrm (ext y) 2) (nrm (ext y) 4) (nrm (ext y) 7) * det24 y =
      (-⟪nrm (ext y) 2, ext y 1 - ext y 0⟫) * (-⟪nrm (ext y) 4, ext y 1 - ext y 0⟫) *
        (-⟪nrm (ext y) 7, ext y 1 - ext y 2⟫) * Delta24 y := by
  have key := binet_cauchy (nrm (ext y) 2) (nrm (ext y) 4) (nrm (ext y) 7) (y 0 - y 1) (y 2 - y 1) (y 6 - y 1)
  have a2 : ⟪nrm (ext y) 2, y 0 - y 1⟫ = -⟪nrm (ext y) 2, ext y 1 - ext y 0⟫ := by
    simp only [inner_eq_dot, toV3_nrm]
    simp only [pt, nrm3, toV3, fa_2, fb_2, fc_2, sg_2, V3.smul, V3.cr, V3.dot, V3.sub, e0, e1, e2, e5, PiLp.sub_apply]
    push_cast
    ring
  have b2 : ⟪nrm (ext y) 2, y 2 - y 1⟫ = -⟪nrm (ext y) 2, ext y 1 - ext y 0⟫ := by
    simp only [inner_eq_dot, toV3_nrm]
    simp only [pt, nrm3, toV3, fa_2, fb_2, fc_2, sg_2, V3.smul, V3.cr, V3.dot, V3.sub, e0, e1, e2, e5, PiLp.sub_apply]
    push_cast
    ring
  have c2 : ⟪nrm (ext y) 2, y 6 - y 1⟫ = -(omega5 y * (-⟪nrm (ext y) 2, ext y 1 - ext y 0⟫)) := by
    rw [← C_val y h5]
    simp only [inner_eq_dot, toV3_nrm]
    simp only [pt, nrm3, toV3, fa_2, fb_2, fc_2, sg_2, V3.smul, V3.cr, V3.dot, V3.sub, e0, e1, e2, e5, e6, PiLp.sub_apply]
    push_cast
    ring
  have a4 : ⟪nrm (ext y) 4, y 0 - y 1⟫ = -⟪nrm (ext y) 4, ext y 1 - ext y 0⟫ := by
    simp only [inner_eq_dot, toV3_nrm]
    simp only [pt, nrm3, toV3, fa_4, fb_4, fc_4, sg_4, V3.smul, V3.cr, V3.dot, V3.sub, e0, e1, e4, e6, PiLp.sub_apply]
    push_cast
    ring
  have b4 : ⟪nrm (ext y) 4, y 2 - y 1⟫ = -(omega4 y * (-⟪nrm (ext y) 4, ext y 1 - ext y 0⟫)) := by
    rw [← E_val y h4]
    simp only [inner_eq_dot, toV3_nrm]
    simp only [pt, nrm3, toV3, fa_4, fb_4, fc_4, sg_4, V3.smul, V3.cr, V3.dot, V3.sub, e0, e1, e2, e4, e6, PiLp.sub_apply]
    push_cast
    ring
  have c4 : ⟪nrm (ext y) 4, y 6 - y 1⟫ = -⟪nrm (ext y) 4, ext y 1 - ext y 0⟫ := by
    simp only [inner_eq_dot, toV3_nrm]
    simp only [pt, nrm3, toV3, fa_4, fb_4, fc_4, sg_4, V3.smul, V3.cr, V3.dot, V3.sub, e0, e1, e4, e6, PiLp.sub_apply]
    push_cast
    ring
  have a7 : ⟪nrm (ext y) 7, y 0 - y 1⟫ = -(omega3 y * (-⟪nrm (ext y) 7, ext y 1 - ext y 2⟫)) := by
    have := H_val y h3
    rw [show y 0 - y 1 = ext y 0 - ext y 1 from rfl, this]; ring
  have b7 : ⟪nrm (ext y) 7, y 2 - y 1⟫ = -⟪nrm (ext y) 7, ext y 1 - ext y 2⟫ := by
    simp only [inner_eq_dot, toV3_nrm]
    simp only [pt, nrm3, toV3, fa_7, fb_7, fc_7, sg_7, V3.smul, V3.cr, V3.dot, V3.sub, e1, e2, e3, e6, PiLp.sub_apply]
    push_cast
    ring
  have c7 : ⟪nrm (ext y) 7, y 6 - y 1⟫ = -⟪nrm (ext y) 7, ext y 1 - ext y 2⟫ := by
    simp only [inner_eq_dot, toV3_nrm]
    simp only [pt, nrm3, toV3, fa_7, fb_7, fc_7, sg_7, V3.smul, V3.cr, V3.dot, V3.sub, e1, e2, e3, e6, PiLp.sub_apply]
    push_cast
    ring
  rw [a2, b2, c2, a4, b4, c4, a7, b7, c7] at key
  unfold Delta24
  have hd : det24 y = vol3 (y 0 - y 1) (y 2 - y 1) (y 6 - y 1) := rfl
  rw [hd]
  linear_combination key

/-- **`Delta > 0` (with the omegas) is `NCEH+`.** -/
theorem cbar_NCEH (hC : Convex24 (ext y)) (h3 : 0 < omega3 y) (h4 : 0 < omega4 y) (h5 : 0 < omega5 y)
    (hΔ : 0 < Delta24 y) : LitHolds (ext y) (.nv 2 4 7) 1 := by
  simp only [LitHolds, val]
  have f := nceh_formula y h3 h4 h5
  have p := det24_pos y hC
  have m := mul_pos (mul_pos (cv21 y hC) (cv41 y hC)) (cv71 y hC)
  have : 0 < det3 (nrm (ext y) 2) (nrm (ext y) 4) (nrm (ext y) 7) * det24 y := by rw [f]; exact mul_pos m hΔ
  have := pos_of_mul_pos_left this p.le
  simpa using this

/-- With `Delta >= 0` only: `NCEH >= 0` (the boundary `Delta = 0` is exactly `NCEH = 0`). -/
theorem cbar_NCEH_nonneg (hC : Convex24 (ext y)) (h3 : 0 < omega3 y) (h4 : 0 < omega4 y) (h5 : 0 < omega5 y)
    (hΔ : 0 ≤ Delta24 y) : 0 ≤ val (ext y) (.nv 2 4 7) := by
  simp only [val]
  have f := nceh_formula y h3 h4 h5
  have p := det24_pos y hC
  have m := mul_pos (mul_pos (cv21 y hC) (cv41 y hC)) (cv71 y hC)
  have : 0 ≤ det3 (nrm (ext y) 2) (nrm (ext y) 4) (nrm (ext y) 7) * det24 y := by rw [f]; exact mul_nonneg m.le hΔ
  exact nonneg_of_mul_nonneg_left this p

/-- The zero boundary: `NCEH = 0` exactly when `Delta = 0`. -/
theorem cbar_NCEH_zero_iff (hC : Convex24 (ext y)) (h3 : 0 < omega3 y) (h4 : 0 < omega4 y) (h5 : 0 < omega5 y) :
    val (ext y) (.nv 2 4 7) = 0 ↔ Delta24 y = 0 := by
  simp only [val]
  have f := nceh_formula y h3 h4 h5
  have p := det24_pos y hC
  have m := mul_pos (mul_pos (cv21 y hC) (cv41 y hC)) (cv71 y hC)
  constructor
  · intro h0; rw [h0, zero_mul] at f; exact (mul_eq_zero.mp f.symm).resolve_left m.ne'
  · intro h0; rw [h0, mul_zero] at f; exact (mul_eq_zero.mp f).resolve_right p.ne'

/-- **The C-bar reading** (Delta > 0 part strict): `H:01-`, `E:12+`, `C:16+`, `NCEH+`. -/
theorem cbar_literals (hC : Convex24 (ext y)) (h3 : 0 < omega3 y) (h4 : 0 < omega4 y) (h5 : 0 < omega5 y)
    (hΔ : 0 < Delta24 y) :
    LitHolds (ext y) (.fc 7 0 1) (-1) ∧ LitHolds (ext y) (.fc 4 1 2) 1 ∧ LitHolds (ext y) (.fc 2 1 6) 1 ∧
      LitHolds (ext y) (.nv 2 4 7) 1 :=
  ⟨cbar_H y hC h3, cbar_E y hC h4, cbar_C y hC h5, cbar_NCEH y hC h3 h4 h5 hΔ⟩
end

end Minimality.T24.SAT
