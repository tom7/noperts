module

public import Minimality.RCell24
public import Minimality.RDispatch24

@[expose] public section

set_option autoImplicit false

open scoped RealInnerProductSpace
open Finset Matrix
open Minimality Minimality.H21 Minimality.H24.SAT Minimality.T24.SAT Minimality.LexCell

namespace Minimality.T24.QN

/-- The two-ear condition at the quad normal `b = F.N 3` (s0x_S24 indices 2:025 4:046 6:235 7:236 8:346). -/
def TwoEar {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  ⟪F.N 7, F.N 3⟫ ≤ 0 ∧ (0 ≤ ⟪F.N 2, F.N 3⟫ ∨ 0 ≤ ⟪F.N 6, F.N 3⟫) ∧
    (0 ≤ ⟪F.N 4, F.N 3⟫ ∨ 0 ≤ ⟪F.N 8, F.N 3⟫)

section Foundations

private theorem inner_pos_self {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (t : Fin 9) :
    0 < ⟪F.N t, F.N t⟫ := by
  obtain ⟨j, i, hj, hi⟩ := s24_off t
  have hlt : ⟪F.N t, x i - x j⟫ < 0 := by
    rw [F.inner_sub, F.zero t j hj, sub_zero]
    exact F.neg t i hi
  have hne : F.N t ≠ 0 := fun h => by simp [h] at hlt
  exact real_inner_self_pos.2 hne

/-- If `⟪Nᵢ, uⱼ⟫` has nonzero determinant, then any `D` orthogonal to `u₁, u₂, u₃` is `0`. -/
private theorem eq_zero_of_inner_basis {u₁ u₂ u₃ N₁ N₂ N₃ D : ℝ³}
    (hdet : (Matrix.of ![![⟪N₁, u₁⟫, ⟪N₁, u₂⟫, ⟪N₁, u₃⟫],
        ![⟪N₂, u₁⟫, ⟪N₂, u₂⟫, ⟪N₂, u₃⟫],
        ![⟪N₃, u₁⟫, ⟪N₃, u₂⟫, ⟪N₃, u₃⟫]]).det ≠ 0)
    (h1 : ⟪D, u₁⟫ = 0) (h2 : ⟪D, u₂⟫ = 0) (h3 : ⟪D, u₃⟫ = 0) : D = 0 := by
  let A : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of ![N₁, N₂, N₃]
  let B : Matrix (Fin 3) (Fin 3) ℝ := Matrix.transpose (Matrix.of ![u₁, u₂, u₃])
  have hAB : A * B = Matrix.of ![![⟪N₁, u₁⟫, ⟪N₁, u₂⟫, ⟪N₁, u₃⟫],
      ![⟪N₂, u₁⟫, ⟪N₂, u₂⟫, ⟪N₂, u₃⟫],
      ![⟪N₃, u₁⟫, ⟪N₃, u₂⟫, ⟪N₃, u₃⟫]] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [A, B, Matrix.mul_apply, Fin.sum_univ_three, PiLp.inner_apply, mul_comm]
  have hBdet : B.det ≠ 0 := by
    intro h0
    apply hdet
    rw [← hAB, Matrix.det_mul, h0, mul_zero]
  have hD : (fun i => D i) ᵥ* B = 0 := by
    ext j
    fin_cases j
    · simpa [B, Matrix.vecMul, dotProduct, Fin.sum_univ_three, PiLp.inner_apply, mul_comm] using h1
    · simpa [B, Matrix.vecMul, dotProduct, Fin.sum_univ_three, PiLp.inner_apply, mul_comm] using h2
    · simpa [B, Matrix.vecMul, dotProduct, Fin.sum_univ_three, PiLp.inner_apply, mul_comm] using h3
  have hD0 := Matrix.eq_zero_of_vecMul_eq_zero hBdet hD
  ext i
  exact congrFun hD0 i

private theorem det_upper_tri_ne_zero {M : Matrix (Fin 3) (Fin 3) ℝ}
    (h10 : M 1 0 = 0) (h20 : M 2 0 = 0) (h21 : M 2 1 = 0)
    (h00 : M 0 0 ≠ 0) (h11 : M 1 1 ≠ 0) (h22 : M 2 2 ≠ 0) : M.det ≠ 0 := by
  rw [Matrix.det_fin_three, h10, h20, h21]
  simp only [mul_zero, zero_mul, add_zero, sub_zero]
  exact mul_ne_zero (mul_ne_zero h00 h11) h22

private theorem det_lower_tri_ne_zero {M : Matrix (Fin 3) (Fin 3) ℝ}
    (h01 : M 0 1 = 0) (h02 : M 0 2 = 0) (h12 : M 1 2 = 0)
    (h00 : M 0 0 ≠ 0) (h11 : M 1 1 ≠ 0) (h22 : M 2 2 ≠ 0) : M.det ≠ 0 := by
  rw [Matrix.det_fin_three, h01, h02, h12]
  simp only [mul_zero, zero_mul, add_zero, sub_zero]
  exact mul_ne_zero (mul_ne_zero h00 h11) h22

private noncomputable def type24OfFac {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    Minimality.Type24 x where
  t012 := ⟨F.f 0, F.N 0, F.hN 0, fun i hi => F.zero 0 i (by simpa [s0x_S24] using hi),
    fun i hi => F.neg 0 i (by simpa [s0x_S24] using hi)⟩
  t016 := ⟨F.f 1, F.N 1, F.hN 1, fun i hi => F.zero 1 i (by simpa [s0x_S24] using hi),
    fun i hi => F.neg 1 i (by simpa [s0x_S24] using hi)⟩
  t126 := ⟨F.f 5, F.N 5, F.hN 5, fun i hi => F.zero 5 i (by simpa [s0x_S24] using hi),
    fun i hi => F.neg 5 i (by simpa [s0x_S24] using hi)⟩
  t236 := ⟨F.f 7, F.N 7, F.hN 7, fun i hi => F.zero 7 i (by simpa [s0x_S24] using hi),
    fun i hi => F.neg 7 i (by simpa [s0x_S24] using hi)⟩
  t046 := ⟨F.f 4, F.N 4, F.hN 4, fun i hi => F.zero 4 i (by simpa [s0x_S24] using hi),
    fun i hi => F.neg 4 i (by simpa [s0x_S24] using hi)⟩
  t025 := ⟨F.f 2, F.N 2, F.hN 2, fun i hi => F.zero 2 i (by simpa [s0x_S24] using hi),
    fun i hi => F.neg 2 i (by simpa [s0x_S24] using hi)⟩

end Foundations

section OB1Cap

private theorem ob1_normal_inner_nonneg {u v w N₀ N₁ : ℝ³}
    (h0u : ⟪N₀, u⟫ = 0) (h0v : ⟪N₀, v⟫ = 0) (h0w : ⟪N₀, w⟫ < 0)
    (h1u : ⟪N₁, u⟫ = 0) (h1w : ⟪N₁, w⟫ = 0) (h1v : ⟪N₁, v⟫ < 0)
    (huv : ⟪u, v⟫ ≤ 0) (huw : ⟪u, w⟫ ≤ 0) (hvw : ⟪v, w⟫ ≤ 0)
    (hdet : det3 u v w ≠ 0) : 0 ≤ ⟪N₀, N₁⟫ := by
  have e : ∀ a b : ℝ³, ⟪a, b⟫ = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := fun a b => by
    simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]; ring
  have hN0 : det3 u v w • N₀ = ⟪N₀, w⟫ • cross u v := by
    simp only [e] at h0u h0v
    ext i
    fin_cases i <;> simp [cross, det3_expand, e]
    · linear_combination (v 1 * w 2 - v 2 * w 1) * h0u - (u 1 * w 2 - u 2 * w 1) * h0v
    · linear_combination (v 2 * w 0 - v 0 * w 2) * h0u - (u 2 * w 0 - u 0 * w 2) * h0v
    · linear_combination (v 0 * w 1 - v 1 * w 0) * h0u - (u 0 * w 1 - u 1 * w 0) * h0v
  have hN1 : det3 u v w • N₁ = (-⟪N₁, v⟫) • cross u w := by
    simp only [e] at h1u h1w
    ext i
    fin_cases i <;> simp [cross, det3_expand, e]
    · linear_combination (-(w 1 * v 2 - w 2 * v 1)) * h1u + (u 1 * v 2 - u 2 * v 1) * h1w
    · linear_combination (-(w 2 * v 0 - w 0 * v 2)) * h1u + (u 2 * v 0 - u 0 * v 2) * h1w
    · linear_combination (-(w 0 * v 1 - w 1 * v 0)) * h1u + (u 0 * v 1 - u 1 * v 0) * h1w
  have hid : (det3 u v w) ^ 2 * ⟪N₀, N₁⟫ =
      (⟪N₀, w⟫ * (-⟪N₁, v⟫)) * (⟪u, u⟫ * ⟪v, w⟫ - ⟪u, w⟫ * ⟪u, v⟫) := by
    have hinn : ⟪det3 u v w • N₀, det3 u v w • N₁⟫ =
        ⟪⟪N₀, w⟫ • cross u v, (-⟪N₁, v⟫) • cross u w⟫ := by rw [hN0, hN1]
    simp only [real_inner_smul_left, real_inner_smul_right] at hinn
    have hlag : ⟪cross u v, cross u w⟫ = ⟪u, u⟫ * ⟪v, w⟫ - ⟪u, w⟫ * ⟪u, v⟫ := by
      simp only [e, cross]; simp; ring
    rw [hlag] at hinn
    linear_combination hinn
  have hdet2 : 0 < (det3 u v w) ^ 2 := sq_pos_of_ne_zero hdet
  have hcoef : ⟪N₀, w⟫ * (-⟪N₁, v⟫) < 0 := mul_neg_of_neg_of_pos h0w (neg_pos.2 h1v)
  have hlag_le : ⟪u, u⟫ * ⟪v, w⟫ - ⟪u, w⟫ * ⟪u, v⟫ ≤ 0 := by
    have huu : 0 ≤ ⟪u, u⟫ := real_inner_self_nonneg
    nlinarith [mul_nonpos_of_nonneg_of_nonpos huu hvw, mul_nonneg (neg_nonneg.2 huw) (neg_nonneg.2 huv)]
  have hrhs : 0 ≤ (det3 u v w) ^ 2 * ⟪N₀, N₁⟫ := by
    rw [hid]
    exact mul_nonneg_of_nonpos_of_nonpos hcoef.le hlag_le
  exact nonneg_of_mul_nonneg_right hrhs hdet2

private theorem det3_e026_ne {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) ≠ 0 := by
  have hne := (type24OfFac F).det_ne
  have heq : det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) = det24 x := by
    simp only [det24, vol3, det3_expand]; ring
  rwa [heq]

private theorem ob1_cap_inner {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hob : ⟪x 0 - x 1, x 2 - x 1⟫ ≤ 0 ∧ ⟪x 0 - x 1, x 6 - x 1⟫ ≤ 0 ∧ ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0) :
    0 ≤ ⟪F.N 0, F.N 1⟫ ∧ 0 ≤ ⟪F.N 0, F.N 5⟫ ∧ 0 ≤ ⟪F.N 1, F.N 5⟫ := by
  have hdet := det3_e026_ne F
  have hdet026 : det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) ≠ 0 := hdet
  have hdet062 : det3 (x 0 - x 1) (x 6 - x 1) (x 2 - x 1) ≠ 0 := by
    have : det3 (x 0 - x 1) (x 6 - x 1) (x 2 - x 1) = -det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) := by
      simp only [det3_expand]; ring
    rw [this]; exact neg_ne_zero.2 hdet
  have hdet206 : det3 (x 2 - x 1) (x 0 - x 1) (x 6 - x 1) ≠ 0 := by
    have : det3 (x 2 - x 1) (x 0 - x 1) (x 6 - x 1) = -det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) := by
      simp only [det3_expand]; ring
    rw [this]; exact neg_ne_zero.2 hdet
  have hdet602 : det3 (x 6 - x 1) (x 0 - x 1) (x 2 - x 1) ≠ 0 := by
    have : det3 (x 6 - x 1) (x 0 - x 1) (x 2 - x 1) = det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) := by
      simp only [det3_expand]; ring
    rw [this]; exact hdet
  have h00 : ⟪F.N 0, x 0 - x 1⟫ = 0 := by rw [F.inner_sub, F.zero 0 0 (by decide), F.zero 0 1 (by decide), sub_self]
  have h02 : ⟪F.N 0, x 2 - x 1⟫ = 0 := by rw [F.inner_sub, F.zero 0 2 (by decide), F.zero 0 1 (by decide), sub_self]
  have h06 : ⟪F.N 0, x 6 - x 1⟫ < 0 := by rw [F.inner_sub, F.zero 0 1 (by decide), sub_zero]; exact F.neg 0 6 (by decide)
  have h10 : ⟪F.N 1, x 0 - x 1⟫ = 0 := by rw [F.inner_sub, F.zero 1 0 (by decide), F.zero 1 1 (by decide), sub_self]
  have h16 : ⟪F.N 1, x 6 - x 1⟫ = 0 := by rw [F.inner_sub, F.zero 1 6 (by decide), F.zero 1 1 (by decide), sub_self]
  have h12 : ⟪F.N 1, x 2 - x 1⟫ < 0 := by rw [F.inner_sub, F.zero 1 1 (by decide), sub_zero]; exact F.neg 1 2 (by decide)
  have h52 : ⟪F.N 5, x 2 - x 1⟫ = 0 := by rw [F.inner_sub, F.zero 5 2 (by decide), F.zero 5 1 (by decide), sub_self]
  have h56 : ⟪F.N 5, x 6 - x 1⟫ = 0 := by rw [F.inner_sub, F.zero 5 6 (by decide), F.zero 5 1 (by decide), sub_self]
  have h50 : ⟪F.N 5, x 0 - x 1⟫ < 0 := by rw [F.inner_sub, F.zero 5 1 (by decide), sub_zero]; exact F.neg 5 0 (by decide)
  refine ⟨?_, ?_, ?_⟩
  · exact ob1_normal_inner_nonneg h00 h02 h06 h10 h16 h12 hob.1 hob.2.1 hob.2.2 hdet026
  · exact ob1_normal_inner_nonneg h02 h00 h06 h52 h56 h50
      (by rw [real_inner_comm]; exact hob.1) hob.2.2 hob.2.1 hdet206
  · exact ob1_normal_inner_nonneg h16 h10 h12 h56 h52 h50
      (by rw [real_inner_comm]; exact hob.2.1) (by rw [real_inner_comm]; exact hob.2.2) hob.1 hdet602

private theorem expand_cap_dual {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (w : ℝ³) :
    w = (⟪w, x 0 - x 1⟫ / (-F.f 5 (x 0))) • (-F.N 5) +
        (⟪w, x 2 - x 1⟫ / (-F.f 1 (x 2))) • (-F.N 1) +
        (⟪w, x 6 - x 1⟫ / (-F.f 0 (x 6))) • (-F.N 0) := by
  have α0 : 0 < -F.f 5 (x 0) := neg_pos.2 (F.neg 5 0 (by decide))
  have α2 : 0 < -F.f 1 (x 2) := neg_pos.2 (F.neg 1 2 (by decide))
  have α6 : 0 < -F.f 0 (x 6) := neg_pos.2 (F.neg 0 6 (by decide))
  have h00 : ⟪F.N 0, x 0 - x 1⟫ = 0 := by rw [F.inner_sub, F.zero 0 0 (by decide), F.zero 0 1 (by decide), sub_self]
  have h02 : ⟪F.N 0, x 2 - x 1⟫ = 0 := by rw [F.inner_sub, F.zero 0 2 (by decide), F.zero 0 1 (by decide), sub_self]
  have h06 : ⟪F.N 0, x 6 - x 1⟫ = F.f 0 (x 6) := by rw [F.inner_sub, F.zero 0 1 (by decide), sub_zero]
  have h10 : ⟪F.N 1, x 0 - x 1⟫ = 0 := by rw [F.inner_sub, F.zero 1 0 (by decide), F.zero 1 1 (by decide), sub_self]
  have h16 : ⟪F.N 1, x 6 - x 1⟫ = 0 := by rw [F.inner_sub, F.zero 1 6 (by decide), F.zero 1 1 (by decide), sub_self]
  have h12 : ⟪F.N 1, x 2 - x 1⟫ = F.f 1 (x 2) := by rw [F.inner_sub, F.zero 1 1 (by decide), sub_zero]
  have h52 : ⟪F.N 5, x 2 - x 1⟫ = 0 := by rw [F.inner_sub, F.zero 5 2 (by decide), F.zero 5 1 (by decide), sub_self]
  have h56 : ⟪F.N 5, x 6 - x 1⟫ = 0 := by rw [F.inner_sub, F.zero 5 6 (by decide), F.zero 5 1 (by decide), sub_self]
  have h50 : ⟪F.N 5, x 0 - x 1⟫ = F.f 5 (x 0) := by rw [F.inner_sub, F.zero 5 1 (by decide), sub_zero]
  have hdet : (Matrix.of ![![⟪F.N 5, x 0 - x 1⟫, ⟪F.N 5, x 2 - x 1⟫, ⟪F.N 5, x 6 - x 1⟫],
      ![⟪F.N 1, x 0 - x 1⟫, ⟪F.N 1, x 2 - x 1⟫, ⟪F.N 1, x 6 - x 1⟫],
      ![⟪F.N 0, x 0 - x 1⟫, ⟪F.N 0, x 2 - x 1⟫, ⟪F.N 0, x 6 - x 1⟫]]).det ≠ 0 :=
    det_upper_tri_ne_zero (by simp [h10]) (by simp [h00]) (by simp [h02])
      (by simp [h50]; exact (F.neg 5 0 (by decide)).ne)
      (by simp [h12]; exact (F.neg 1 2 (by decide)).ne)
      (by simp [h06]; exact (F.neg 0 6 (by decide)).ne)
  let D := w - ((⟪w, x 0 - x 1⟫ / (-F.f 5 (x 0))) • (-F.N 5) +
      (⟪w, x 2 - x 1⟫ / (-F.f 1 (x 2))) • (-F.N 1) +
      (⟪w, x 6 - x 1⟫ / (-F.f 0 (x 6))) • (-F.N 0))
  have h5n : F.f 5 (x 0) ≠ 0 := (F.neg 5 0 (by decide)).ne
  have h1n : F.f 1 (x 2) ≠ 0 := (F.neg 1 2 (by decide)).ne
  have h0n : F.f 0 (x 6) ≠ 0 := (F.neg 0 6 (by decide)).ne
  have hD0 : D = 0 := by
    refine eq_zero_of_inner_basis hdet ?_ ?_ ?_
    · simp only [D, inner_sub_left, inner_add_left, real_inner_smul_left, inner_neg_left,
        h50, h10, h00, sub_eq_zero]
      field_simp; ring
    · simp only [D, inner_sub_left, inner_add_left, real_inner_smul_left, inner_neg_left,
        h52, h12, h02, sub_eq_zero]
      field_simp; ring
    · simp only [D, inner_sub_left, inner_add_left, real_inner_smul_left, inner_neg_left,
        h56, h16, h06, sub_eq_zero]
      field_simp; ring
  exact sub_eq_zero.1 hD0

private theorem quad_dot_cap_nonpos {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hob : ⟪x 0 - x 1, x 2 - x 1⟫ ≤ 0 ∧ ⟪x 0 - x 1, x 6 - x 1⟫ ≤ 0 ∧ ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0)
    (hnB : F.f 3 (x 1) ≤ F.f 3 (x 2)) (hnC : F.f 3 (x 1) ≤ F.f 3 (x 6)) :
    ⟪F.N 5, F.N 3⟫ < 0 ∧ ⟪F.N 1, F.N 3⟫ ≤ 0 ∧ ⟪F.N 0, F.N 3⟫ ≤ 0 ∧
      (⟪F.N 2, F.N 3⟫ ≤ 0 → ⟪F.N 0, F.N 3⟫ < 0) ∧
      (⟪F.N 4, F.N 3⟫ ≤ 0 → ⟪F.N 1, F.N 3⟫ < 0) := by
  obtain ⟨h01, h05, h15⟩ := ob1_cap_inner F hob
  have h55 : 0 < ⟪F.N 5, F.N 5⟫ := inner_pos_self F 5
  have h11 : 0 < ⟪F.N 1, F.N 1⟫ := inner_pos_self F 1
  have h00 : 0 < ⟪F.N 0, F.N 0⟫ := inner_pos_self F 0
  have α0 : 0 < -F.f 5 (x 0) := neg_pos.2 (F.neg 5 0 (by decide))
  have α2 : 0 < -F.f 1 (x 2) := neg_pos.2 (F.neg 1 2 (by decide))
  have α6 : 0 < -F.f 0 (x 6) := neg_pos.2 (F.neg 0 6 (by decide))
  have hb0 : 0 < ⟪F.N 3, x 0 - x 1⟫ := by
    rw [F.inner_sub, F.zero 3 0 (by decide), zero_sub]; exact neg_pos.2 (F.neg 3 1 (by decide))
  have hb2 : 0 ≤ ⟪F.N 3, x 2 - x 1⟫ := by rw [F.inner_sub]; linarith
  have hb6 : 0 ≤ ⟪F.N 3, x 6 - x 1⟫ := by rw [F.inner_sub]; linarith
  have hexp := expand_cap_dual F (F.N 3)
  have h53 : ⟪F.N 5, F.N 3⟫ < 0 := by
    conv_lhs => rw [hexp]
    simp only [inner_add_right, real_inner_smul_right, inner_neg_right]
    have hA : 0 < (⟪F.N 3, x 0 - x 1⟫ / (-F.f 5 (x 0))) * ⟪F.N 5, F.N 5⟫ :=
      mul_pos (div_pos hb0 α0) h55
    have hB : 0 ≤ (⟪F.N 3, x 2 - x 1⟫ / (-F.f 1 (x 2))) * ⟪F.N 5, F.N 1⟫ :=
      mul_nonneg (div_nonneg hb2 α2.le) (by rw [real_inner_comm]; exact h15)
    have hC : 0 ≤ (⟪F.N 3, x 6 - x 1⟫ / (-F.f 0 (x 6))) * ⟪F.N 5, F.N 0⟫ :=
      mul_nonneg (div_nonneg hb6 α6.le) (by rw [real_inner_comm]; exact h05)
    linarith
  have h13 : ⟪F.N 1, F.N 3⟫ ≤ 0 := by
    conv_lhs => rw [hexp]
    simp only [inner_add_right, real_inner_smul_right, inner_neg_right]
    have hA : 0 ≤ (⟪F.N 3, x 0 - x 1⟫ / (-F.f 5 (x 0))) * ⟪F.N 1, F.N 5⟫ :=
      mul_nonneg (div_pos hb0 α0).le h15
    have hB : 0 ≤ (⟪F.N 3, x 2 - x 1⟫ / (-F.f 1 (x 2))) * ⟪F.N 1, F.N 1⟫ :=
      mul_nonneg (div_nonneg hb2 α2.le) h11.le
    have hC : 0 ≤ (⟪F.N 3, x 6 - x 1⟫ / (-F.f 0 (x 6))) * ⟪F.N 1, F.N 0⟫ :=
      mul_nonneg (div_nonneg hb6 α6.le) (by rw [real_inner_comm]; exact h01)
    linarith
  have h03 : ⟪F.N 0, F.N 3⟫ ≤ 0 := by
    conv_lhs => rw [hexp]
    simp only [inner_add_right, real_inner_smul_right, inner_neg_right]
    have hA : 0 ≤ (⟪F.N 3, x 0 - x 1⟫ / (-F.f 5 (x 0))) * ⟪F.N 0, F.N 5⟫ :=
      mul_nonneg (div_pos hb0 α0).le h05
    have hB : 0 ≤ (⟪F.N 3, x 2 - x 1⟫ / (-F.f 1 (x 2))) * ⟪F.N 0, F.N 1⟫ :=
      mul_nonneg (div_nonneg hb2 α2.le) h01
    have hC : 0 ≤ (⟪F.N 3, x 6 - x 1⟫ / (-F.f 0 (x 6))) * ⟪F.N 0, F.N 0⟫ :=
      mul_nonneg (div_nonneg hb6 α6.le) h00.le
    linarith
  refine ⟨h53, h13, h03, ?_, ?_⟩
  · intro h23
    refine lt_of_le_of_ne h03 fun h03eq => ?_
    have hexp2 := expand_cap_dual F (F.N 2)
    have h20 : 0 < ⟪F.N 2, x 0 - x 1⟫ := by
      rw [F.inner_sub, F.zero 2 0 (by decide), zero_sub]; exact neg_pos.2 (F.neg 2 1 (by decide))
    have h22 : 0 < ⟪F.N 2, x 2 - x 1⟫ := by
      rw [F.inner_sub, F.zero 2 2 (by decide), zero_sub]; exact neg_pos.2 (F.neg 2 1 (by decide))
    have h35 : ⟪F.N 3, F.N 5⟫ = ⟪F.N 5, F.N 3⟫ := real_inner_comm _ _
    have h31 : ⟪F.N 3, F.N 1⟫ = ⟪F.N 1, F.N 3⟫ := real_inner_comm _ _
    have h30 : ⟪F.N 3, F.N 0⟫ = ⟪F.N 0, F.N 3⟫ := real_inner_comm _ _
    have h23pos : 0 < ⟪F.N 2, F.N 3⟫ := by
      rw [real_inner_comm]
      conv_rhs => rw [hexp2]
      simp only [inner_add_right, real_inner_smul_right, inner_neg_right, h35, h31, h30]
      have hA : 0 < (⟪F.N 2, x 0 - x 1⟫ / (-F.f 5 (x 0))) * (-⟪F.N 5, F.N 3⟫) :=
        mul_pos (div_pos h20 α0) (neg_pos.2 h53)
      have hB : 0 ≤ (⟪F.N 2, x 2 - x 1⟫ / (-F.f 1 (x 2))) * (-⟪F.N 1, F.N 3⟫) :=
        mul_nonneg (div_pos h22 α2).le (neg_nonneg.2 h13)
      have hC : (⟪F.N 2, x 6 - x 1⟫ / (-F.f 0 (x 6))) * (-⟪F.N 0, F.N 3⟫) = 0 := by
        rw [h03eq]; ring
      linarith
    linarith
  · intro h43
    refine lt_of_le_of_ne h13 fun h13eq => ?_
    have hexp4 := expand_cap_dual F (F.N 4)
    have h40 : 0 < ⟪F.N 4, x 0 - x 1⟫ := by
      rw [F.inner_sub, F.zero 4 0 (by decide), zero_sub]; exact neg_pos.2 (F.neg 4 1 (by decide))
    have h46 : 0 < ⟪F.N 4, x 6 - x 1⟫ := by
      rw [F.inner_sub, F.zero 4 6 (by decide), zero_sub]; exact neg_pos.2 (F.neg 4 1 (by decide))
    have h35 : ⟪F.N 3, F.N 5⟫ = ⟪F.N 5, F.N 3⟫ := real_inner_comm _ _
    have h31 : ⟪F.N 3, F.N 1⟫ = ⟪F.N 1, F.N 3⟫ := real_inner_comm _ _
    have h30 : ⟪F.N 3, F.N 0⟫ = ⟪F.N 0, F.N 3⟫ := real_inner_comm _ _
    have h43pos : 0 < ⟪F.N 4, F.N 3⟫ := by
      rw [real_inner_comm]
      conv_rhs => rw [hexp4]
      simp only [inner_add_right, real_inner_smul_right, inner_neg_right, h35, h31, h30]
      have hA : 0 < (⟪F.N 4, x 0 - x 1⟫ / (-F.f 5 (x 0))) * (-⟪F.N 5, F.N 3⟫) :=
        mul_pos (div_pos h40 α0) (neg_pos.2 h53)
      have hB : (⟪F.N 4, x 2 - x 1⟫ / (-F.f 1 (x 2))) * (-⟪F.N 1, F.N 3⟫) = 0 := by
        rw [h13eq]; ring
      have hC : 0 ≤ (⟪F.N 4, x 6 - x 1⟫ / (-F.f 0 (x 6))) * (-⟪F.N 0, F.N 3⟫) :=
        mul_nonneg (div_pos h46 α6).le (neg_nonneg.2 h03)
      linarith
    linarith

end OB1Cap

section Syzygies

private theorem syzygy_v3 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    ∃ a b c d : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧
      a • F.N 3 + b • F.N 7 = c • F.N 6 + d • F.N 8 := by
  let p2 := -F.f 3 (x 2)
  let p6 := -F.f 3 (x 6)
  let q4 := -F.f 7 (x 4)
  let r6 := -F.f 6 (x 6)
  let r4 := -F.f 6 (x 4)
  let s2 := -F.f 8 (x 2)
  have hp2 : 0 < p2 := neg_pos.2 (F.neg 3 2 (by decide))
  have hp6 : 0 < p6 := neg_pos.2 (F.neg 3 6 (by decide))
  have hq4 : 0 < q4 := neg_pos.2 (F.neg 7 4 (by decide))
  have hr6 : 0 < r6 := neg_pos.2 (F.neg 6 6 (by decide))
  have hr4 : 0 < r4 := neg_pos.2 (F.neg 6 4 (by decide))
  have hs2 : 0 < s2 := neg_pos.2 (F.neg 8 2 (by decide))
  refine ⟨s2 * r6 * q4, p6 * s2 * r4, p6 * s2 * q4, p2 * r6 * q4,
    by positivity, by positivity, by positivity, by positivity, ?_⟩
  let D := (s2 * r6 * q4) • F.N 3 + (p6 * s2 * r4) • F.N 7 -
      ((p6 * s2 * q4) • F.N 6 + (p2 * r6 * q4) • F.N 8)
  have hdet : (Matrix.of ![![⟪F.N 8, x 2 - x 3⟫, ⟪F.N 8, x 6 - x 3⟫, ⟪F.N 8, x 4 - x 3⟫],
      ![⟪F.N 6, x 2 - x 3⟫, ⟪F.N 6, x 6 - x 3⟫, ⟪F.N 6, x 4 - x 3⟫],
      ![⟪F.N 7, x 2 - x 3⟫, ⟪F.N 7, x 6 - x 3⟫, ⟪F.N 7, x 4 - x 3⟫]]).det ≠ 0 := by
    have h82 : ⟪F.N 8, x 2 - x 3⟫ = -s2 := by rw [F.inner_sub, F.zero 8 3 (by decide), sub_zero]; dsimp only [s2]; ring
    have h86 : ⟪F.N 8, x 6 - x 3⟫ = 0 := by rw [F.inner_sub, F.zero 8 6 (by decide), F.zero 8 3 (by decide), sub_self]
    have h84 : ⟪F.N 8, x 4 - x 3⟫ = 0 := by rw [F.inner_sub, F.zero 8 4 (by decide), F.zero 8 3 (by decide), sub_self]
    have h62 : ⟪F.N 6, x 2 - x 3⟫ = 0 := by rw [F.inner_sub, F.zero 6 2 (by decide), F.zero 6 3 (by decide), sub_self]
    have h66 : ⟪F.N 6, x 6 - x 3⟫ = -r6 := by rw [F.inner_sub, F.zero 6 3 (by decide), sub_zero]; dsimp only [r6]; ring
    have h72 : ⟪F.N 7, x 2 - x 3⟫ = 0 := by rw [F.inner_sub, F.zero 7 2 (by decide), F.zero 7 3 (by decide), sub_self]
    have h76 : ⟪F.N 7, x 6 - x 3⟫ = 0 := by rw [F.inner_sub, F.zero 7 6 (by decide), F.zero 7 3 (by decide), sub_self]
    have h74 : ⟪F.N 7, x 4 - x 3⟫ = -q4 := by rw [F.inner_sub, F.zero 7 3 (by decide), sub_zero]; dsimp only [q4]; ring
    exact det_upper_tri_ne_zero (by simp [h62]) (by simp [h72]) (by simp [h76])
      (by simp [h82]; exact hs2.ne')
      (by simp [h66]; exact hr6.ne')
      (by simp [h74]; exact hq4.ne')
  have hD0 : D = 0 := by
    refine eq_zero_of_inner_basis hdet ?_ ?_ ?_
    · simp only [D, inner_sub_left, inner_add_left, real_inner_smul_left, F.inner_sub,
        F.zero 3 3 (by decide), F.zero 7 3 (by decide), F.zero 6 3 (by decide), F.zero 8 3 (by decide),
        F.zero 7 2 (by decide), F.zero 6 2 (by decide), sub_zero, mul_zero, add_zero, zero_add]
      dsimp only [p2, s2]; ring
    · simp only [D, inner_sub_left, inner_add_left, real_inner_smul_left, F.inner_sub,
        F.zero 3 3 (by decide), F.zero 7 3 (by decide), F.zero 6 3 (by decide), F.zero 8 3 (by decide),
        F.zero 7 6 (by decide), F.zero 8 6 (by decide), sub_zero, mul_zero, add_zero]
      dsimp only [p6, r6]; ring
    · simp only [D, inner_sub_left, inner_add_left, real_inner_smul_left, F.inner_sub,
        F.zero 3 3 (by decide), F.zero 7 3 (by decide), F.zero 6 3 (by decide), F.zero 8 3 (by decide),
        F.zero 3 4 (by decide), F.zero 8 4 (by decide), sub_zero, mul_zero, zero_add, add_zero]
      dsimp only [q4, r4]; ring
  exact sub_eq_zero.1 hD0

private theorem det_v2_ne_zero {M : Matrix (Fin 3) (Fin 3) ℝ}
    (h01 : M 0 1 = 0) (h10 : M 1 0 = 0) (h20 : M 2 0 = 0) (h22 : M 2 2 = 0)
    (h00 : M 0 0 ≠ 0) (h12 : M 1 2 ≠ 0) (h21 : M 2 1 ≠ 0) : M.det ≠ 0 := by
  rw [Matrix.det_fin_three, h01, h10, h20, h22]
  simp only [mul_zero, zero_mul, add_zero, zero_sub, sub_zero, neg_ne_zero]
  exact mul_ne_zero (mul_ne_zero h00 h12) h21

private theorem syzygy_v2 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    ∃ a b c d : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧
      a • (-F.N 5) + b • F.N 7 + c • F.N 2 = d • F.N 6 := by
  let b0 := -F.f 5 (x 0)
  let b3 := -F.f 5 (x 3)
  let r0 := -F.f 7 (x 0)
  let t6 := -F.f 2 (x 6)
  let t3 := -F.f 2 (x 3)
  let s6 := -F.f 6 (x 6)
  let s0 := -F.f 6 (x 0)
  have hb0 : 0 < b0 := neg_pos.2 (F.neg 5 0 (by decide))
  have hb3 : 0 < b3 := neg_pos.2 (F.neg 5 3 (by decide))
  have hr0 : 0 < r0 := neg_pos.2 (F.neg 7 0 (by decide))
  have ht6 : 0 < t6 := neg_pos.2 (F.neg 2 6 (by decide))
  have ht3 : 0 < t3 := neg_pos.2 (F.neg 2 3 (by decide))
  have hs6 : 0 < s6 := neg_pos.2 (F.neg 6 6 (by decide))
  have hs0 : 0 < s0 := neg_pos.2 (F.neg 6 0 (by decide))
  refine ⟨s6 * t3 * r0, b3 * t6 * s0 + s6 * t3 * b0, b3 * r0 * s6, b3 * r0 * t6,
    by positivity, by positivity, by positivity, by positivity, ?_⟩
  let D := (s6 * t3 * r0) • (-F.N 5) + (b3 * t6 * s0 + s6 * t3 * b0) • F.N 7 +
      (b3 * r0 * s6) • F.N 2 - (b3 * r0 * t6) • F.N 6
  have hdet : (Matrix.of ![![⟪F.N 2, x 6 - x 2⟫, ⟪F.N 2, x 0 - x 2⟫, ⟪F.N 2, x 3 - x 2⟫],
      ![⟪F.N 5, x 6 - x 2⟫, ⟪F.N 5, x 0 - x 2⟫, ⟪F.N 5, x 3 - x 2⟫],
      ![⟪F.N 7, x 6 - x 2⟫, ⟪F.N 7, x 0 - x 2⟫, ⟪F.N 7, x 3 - x 2⟫]]).det ≠ 0 := by
    have h26 : ⟪F.N 2, x 6 - x 2⟫ = -t6 := by rw [F.inner_sub, F.zero 2 2 (by decide), sub_zero]; dsimp only [t6]; ring
    have h20 : ⟪F.N 2, x 0 - x 2⟫ = 0 := by rw [F.inner_sub, F.zero 2 0 (by decide), F.zero 2 2 (by decide), sub_self]
    have h56 : ⟪F.N 5, x 6 - x 2⟫ = 0 := by rw [F.inner_sub, F.zero 5 6 (by decide), F.zero 5 2 (by decide), sub_self]
    have h53 : ⟪F.N 5, x 3 - x 2⟫ = -b3 := by rw [F.inner_sub, F.zero 5 2 (by decide), sub_zero]; dsimp only [b3]; ring
    have h76 : ⟪F.N 7, x 6 - x 2⟫ = 0 := by rw [F.inner_sub, F.zero 7 6 (by decide), F.zero 7 2 (by decide), sub_self]
    have h70 : ⟪F.N 7, x 0 - x 2⟫ = -r0 := by rw [F.inner_sub, F.zero 7 2 (by decide), sub_zero]; dsimp only [r0]; ring
    have h73 : ⟪F.N 7, x 3 - x 2⟫ = 0 := by rw [F.inner_sub, F.zero 7 3 (by decide), F.zero 7 2 (by decide), sub_self]
    exact det_v2_ne_zero (by simp [h20]) (by simp [h56]) (by simp [h76]) (by simp [h73])
      (by simp [h26]; exact ht6.ne')
      (by simp [h53]; exact hb3.ne')
      (by simp [h70]; exact hr0.ne')
  have hD0 : D = 0 := by
    refine eq_zero_of_inner_basis hdet ?_ ?_ ?_
    · simp only [D, inner_sub_left, inner_add_left, real_inner_smul_left, inner_neg_left,
        F.inner_sub, F.zero 5 2 (by decide), F.zero 7 2 (by decide), F.zero 2 2 (by decide),
        F.zero 6 2 (by decide), F.zero 5 6 (by decide), F.zero 7 6 (by decide), sub_zero,
        mul_zero, neg_zero, zero_add, add_zero]
      dsimp only [t6, s6]; ring
    · simp only [D, inner_sub_left, inner_add_left, real_inner_smul_left, inner_neg_left,
        F.inner_sub, F.zero 5 2 (by decide), F.zero 7 2 (by decide), F.zero 2 2 (by decide),
        F.zero 6 2 (by decide), F.zero 2 0 (by decide), sub_zero, mul_zero, add_zero]
      dsimp only [b0, r0, s0]; ring
    · simp only [D, inner_sub_left, inner_add_left, real_inner_smul_left, inner_neg_left,
        F.inner_sub, F.zero 5 2 (by decide), F.zero 7 2 (by decide), F.zero 2 2 (by decide),
        F.zero 6 2 (by decide), F.zero 7 3 (by decide), F.zero 6 3 (by decide), sub_zero,
        mul_zero, add_zero]
      dsimp only [b3, t3]; ring
  exact sub_eq_zero.1 hD0

private theorem syzygy_v6 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    ∃ a b c d : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧
      a • (-F.N 5) + b • F.N 7 + c • F.N 4 = d • F.N 8 := by
  let b0 := -F.f 5 (x 0)
  let b3 := -F.f 5 (x 3)
  let r0 := -F.f 7 (x 0)
  let t2 := -F.f 4 (x 2)
  let t3 := -F.f 4 (x 3)
  let s2 := -F.f 8 (x 2)
  let s0 := -F.f 8 (x 0)
  have hb0 : 0 < b0 := neg_pos.2 (F.neg 5 0 (by decide))
  have hb3 : 0 < b3 := neg_pos.2 (F.neg 5 3 (by decide))
  have hr0 : 0 < r0 := neg_pos.2 (F.neg 7 0 (by decide))
  have ht2 : 0 < t2 := neg_pos.2 (F.neg 4 2 (by decide))
  have ht3 : 0 < t3 := neg_pos.2 (F.neg 4 3 (by decide))
  have hs2 : 0 < s2 := neg_pos.2 (F.neg 8 2 (by decide))
  have hs0 : 0 < s0 := neg_pos.2 (F.neg 8 0 (by decide))
  refine ⟨s2 * t3 * r0, b3 * t2 * s0 + s2 * t3 * b0, b3 * r0 * s2, b3 * r0 * t2,
    by positivity, by positivity, by positivity, by positivity, ?_⟩
  let D := (s2 * t3 * r0) • (-F.N 5) + (b3 * t2 * s0 + s2 * t3 * b0) • F.N 7 +
      (b3 * r0 * s2) • F.N 4 - (b3 * r0 * t2) • F.N 8
  have hdet : (Matrix.of ![![⟪F.N 4, x 2 - x 6⟫, ⟪F.N 4, x 0 - x 6⟫, ⟪F.N 4, x 3 - x 6⟫],
      ![⟪F.N 5, x 2 - x 6⟫, ⟪F.N 5, x 0 - x 6⟫, ⟪F.N 5, x 3 - x 6⟫],
      ![⟪F.N 7, x 2 - x 6⟫, ⟪F.N 7, x 0 - x 6⟫, ⟪F.N 7, x 3 - x 6⟫]]).det ≠ 0 := by
    have h42 : ⟪F.N 4, x 2 - x 6⟫ = -t2 := by rw [F.inner_sub, F.zero 4 6 (by decide), sub_zero]; dsimp only [t2]; ring
    have h40 : ⟪F.N 4, x 0 - x 6⟫ = 0 := by rw [F.inner_sub, F.zero 4 0 (by decide), F.zero 4 6 (by decide), sub_self]
    have h52 : ⟪F.N 5, x 2 - x 6⟫ = 0 := by rw [F.inner_sub, F.zero 5 2 (by decide), F.zero 5 6 (by decide), sub_self]
    have h53 : ⟪F.N 5, x 3 - x 6⟫ = -b3 := by rw [F.inner_sub, F.zero 5 6 (by decide), sub_zero]; dsimp only [b3]; ring
    have h72 : ⟪F.N 7, x 2 - x 6⟫ = 0 := by rw [F.inner_sub, F.zero 7 2 (by decide), F.zero 7 6 (by decide), sub_self]
    have h70 : ⟪F.N 7, x 0 - x 6⟫ = -r0 := by rw [F.inner_sub, F.zero 7 6 (by decide), sub_zero]; dsimp only [r0]; ring
    have h73 : ⟪F.N 7, x 3 - x 6⟫ = 0 := by rw [F.inner_sub, F.zero 7 3 (by decide), F.zero 7 6 (by decide), sub_self]
    exact det_v2_ne_zero (by simp [h40]) (by simp [h52]) (by simp [h72]) (by simp [h73])
      (by simp [h42]; exact ht2.ne')
      (by simp [h53]; exact hb3.ne')
      (by simp [h70]; exact hr0.ne')
  have hD0 : D = 0 := by
    refine eq_zero_of_inner_basis hdet ?_ ?_ ?_
    · simp only [D, inner_sub_left, inner_add_left, real_inner_smul_left, inner_neg_left,
        F.inner_sub, F.zero 5 6 (by decide), F.zero 7 6 (by decide), F.zero 4 6 (by decide),
        F.zero 8 6 (by decide), F.zero 5 2 (by decide), F.zero 7 2 (by decide), sub_zero,
        mul_zero, neg_zero, zero_add, add_zero]
      dsimp only [t2, s2]; ring
    · simp only [D, inner_sub_left, inner_add_left, real_inner_smul_left, inner_neg_left,
        F.inner_sub, F.zero 5 6 (by decide), F.zero 7 6 (by decide), F.zero 4 6 (by decide),
        F.zero 8 6 (by decide), F.zero 4 0 (by decide), sub_zero, mul_zero, add_zero]
      dsimp only [b0, r0, s0]; ring
    · simp only [D, inner_sub_left, inner_add_left, real_inner_smul_left, inner_neg_left,
        F.inner_sub, F.zero 5 6 (by decide), F.zero 7 6 (by decide), F.zero 4 6 (by decide),
        F.zero 8 6 (by decide), F.zero 7 3 (by decide), F.zero 8 3 (by decide), sub_zero,
        mul_zero, add_zero]
      dsimp only [b3, t3]; ring
  exact sub_eq_zero.1 hD0

private theorem syzygy_cbar {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hcb : Minimality.T24.CbarIn x) :
    ∃ a b c d : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 ≤ d ∧
      a • F.N 2 + b • F.N 4 + c • F.N 7 = d • F.N 5 := by
  let T := type24OfFac F
  have hω3 : 0 < omega3 x := hcb.1
  have hω4 : 0 < omega4 x := hcb.2.1
  have hω5 : 0 < omega5 x := hcb.2.2.1
  have hΔ : 0 ≤ Delta24 x := hcb.2.2.2
  have h45 : 1 < omega4 x * omega5 x := omega_prod_gt_one hω4 hω5 hω3 (by
    have := hΔ; simp only [Delta24] at this ⊢; linarith)
  have hf2 : 0 < -F.f 2 (x 1) := neg_pos.2 (F.neg 2 1 (by decide))
  have hf4 : 0 < -F.f 4 (x 1) := neg_pos.2 (F.neg 4 1 (by decide))
  have hf7 : 0 < -F.f 7 (x 1) := neg_pos.2 (F.neg 7 1 (by decide))
  have hf5 : 0 < -F.f 5 (x 0) := neg_pos.2 (F.neg 5 0 (by decide))
  have h2_0 : ⟪F.N 2, x 0 - x 1⟫ = -F.f 2 (x 1) := by rw [F.inner_sub, F.zero 2 0 (by decide), zero_sub]
  have h2_2 : ⟪F.N 2, x 2 - x 1⟫ = -F.f 2 (x 1) := by rw [F.inner_sub, F.zero 2 2 (by decide), zero_sub]
  have h2_6 : ⟪F.N 2, x 6 - x 1⟫ = omega5 x * F.f 2 (x 1) := by
    have h5 := T.rep 5
    have h5f : ⟪F.N 2, x 5 - x 1⟫ = -F.f 2 (x 1) := by rw [F.inner_sub, F.zero 2 5 (by decide), zero_sub]
    have he5 : oblX0 x 5 + oblX2 x 5 - omega5 x * oblX6 x 5 = 1 := T.eq5
    have hX6 : 0 < oblX6 x 5 := T.X6_pos (by decide)
    have hsum : ⟪F.N 2, x 5 - x 1⟫ = oblX0 x 5 * ⟪F.N 2, x 0 - x 1⟫ +
        oblX2 x 5 * ⟪F.N 2, x 2 - x 1⟫ + oblX6 x 5 * ⟪F.N 2, x 6 - x 1⟫ := by
      have h5' : x 5 - x 1 = oblX0 x 5 • (x 0 - x 1) + oblX2 x 5 • (x 2 - x 1) +
          oblX6 x 5 • (x 6 - x 1) := by rw [h5]; abel
      rw [h5']; simp only [inner_add_right, real_inner_smul_right]
    rw [h5f, h2_0, h2_2] at hsum
    have hmul : oblX6 x 5 * ⟪F.N 2, x 6 - x 1⟫ = oblX6 x 5 * (omega5 x * F.f 2 (x 1)) := by
      linear_combination -hsum + F.f 2 (x 1) * he5
    exact mul_left_cancel₀ hX6.ne' hmul
  have h4_0 : ⟪F.N 4, x 0 - x 1⟫ = -F.f 4 (x 1) := by rw [F.inner_sub, F.zero 4 0 (by decide), zero_sub]
  have h4_6 : ⟪F.N 4, x 6 - x 1⟫ = -F.f 4 (x 1) := by rw [F.inner_sub, F.zero 4 6 (by decide), zero_sub]
  have h4_2 : ⟪F.N 4, x 2 - x 1⟫ = omega4 x * F.f 4 (x 1) := by
    have h4 := T.rep 4
    have h4f : ⟪F.N 4, x 4 - x 1⟫ = -F.f 4 (x 1) := by rw [F.inner_sub, F.zero 4 4 (by decide), zero_sub]
    have he4 : oblX0 x 4 + oblX6 x 4 - omega4 x * oblX2 x 4 = 1 := T.eq4
    have hX2 : 0 < oblX2 x 4 := T.X2_pos (by decide)
    have hsum : ⟪F.N 4, x 4 - x 1⟫ = oblX0 x 4 * ⟪F.N 4, x 0 - x 1⟫ +
        oblX2 x 4 * ⟪F.N 4, x 2 - x 1⟫ + oblX6 x 4 * ⟪F.N 4, x 6 - x 1⟫ := by
      have h4' : x 4 - x 1 = oblX0 x 4 • (x 0 - x 1) + oblX2 x 4 • (x 2 - x 1) +
          oblX6 x 4 • (x 6 - x 1) := by rw [h4]; abel
      rw [h4']; simp only [inner_add_right, real_inner_smul_right]
    rw [h4f, h4_0, h4_6] at hsum
    have hmul : oblX2 x 4 * ⟪F.N 4, x 2 - x 1⟫ = oblX2 x 4 * (omega4 x * F.f 4 (x 1)) := by
      linear_combination -hsum + F.f 4 (x 1) * he4
    exact mul_left_cancel₀ hX2.ne' hmul
  have h7_2 : ⟪F.N 7, x 2 - x 1⟫ = -F.f 7 (x 1) := by rw [F.inner_sub, F.zero 7 2 (by decide), zero_sub]
  have h7_6 : ⟪F.N 7, x 6 - x 1⟫ = -F.f 7 (x 1) := by rw [F.inner_sub, F.zero 7 6 (by decide), zero_sub]
  have h7_0 : ⟪F.N 7, x 0 - x 1⟫ = omega3 x * F.f 7 (x 1) := by
    have h3 := T.rep 3
    have h3f : ⟪F.N 7, x 3 - x 1⟫ = -F.f 7 (x 1) := by rw [F.inner_sub, F.zero 7 3 (by decide), zero_sub]
    have he3 : oblX2 x 3 + oblX6 x 3 - omega3 x * oblX0 x 3 = 1 := T.eq3
    have hX0 : 0 < oblX0 x 3 := T.X0_pos (by decide)
    have hsum : ⟪F.N 7, x 3 - x 1⟫ = oblX0 x 3 * ⟪F.N 7, x 0 - x 1⟫ +
        oblX2 x 3 * ⟪F.N 7, x 2 - x 1⟫ + oblX6 x 3 * ⟪F.N 7, x 6 - x 1⟫ := by
      have h3' : x 3 - x 1 = oblX0 x 3 • (x 0 - x 1) + oblX2 x 3 • (x 2 - x 1) +
          oblX6 x 3 • (x 6 - x 1) := by rw [h3]; abel
      rw [h3']; simp only [inner_add_right, real_inner_smul_right]
    rw [h3f, h7_2, h7_6] at hsum
    have hmul : oblX0 x 3 * ⟪F.N 7, x 0 - x 1⟫ = oblX0 x 3 * (omega3 x * F.f 7 (x 1)) := by
      linear_combination -hsum + F.f 7 (x 1) * he3
    exact mul_left_cancel₀ hX0.ne' hmul
  refine ⟨(omega4 x + 1) / (-F.f 2 (x 1)), (omega5 x + 1) / (-F.f 4 (x 1)),
    (omega4 x * omega5 x - 1) / (-F.f 7 (x 1)), Delta24 x / (-F.f 5 (x 0)),
    div_pos (by linarith) hf2, div_pos (by linarith) hf4, div_pos (by linarith) hf7,
    div_nonneg hΔ hf5.le, ?_⟩
  let D := ((omega4 x + 1) / (-F.f 2 (x 1))) • F.N 2 +
      ((omega5 x + 1) / (-F.f 4 (x 1))) • F.N 4 +
      ((omega4 x * omega5 x - 1) / (-F.f 7 (x 1))) • F.N 7 -
      (Delta24 x / (-F.f 5 (x 0))) • F.N 5
  have h00 : ⟪F.N 0, x 0 - x 1⟫ = 0 := by rw [F.inner_sub, F.zero 0 0 (by decide), F.zero 0 1 (by decide), sub_self]
  have h02 : ⟪F.N 0, x 2 - x 1⟫ = 0 := by rw [F.inner_sub, F.zero 0 2 (by decide), F.zero 0 1 (by decide), sub_self]
  have h06 : ⟪F.N 0, x 6 - x 1⟫ = F.f 0 (x 6) := by rw [F.inner_sub, F.zero 0 1 (by decide), sub_zero]
  have h10 : ⟪F.N 1, x 0 - x 1⟫ = 0 := by rw [F.inner_sub, F.zero 1 0 (by decide), F.zero 1 1 (by decide), sub_self]
  have h16 : ⟪F.N 1, x 6 - x 1⟫ = 0 := by rw [F.inner_sub, F.zero 1 6 (by decide), F.zero 1 1 (by decide), sub_self]
  have h12 : ⟪F.N 1, x 2 - x 1⟫ = F.f 1 (x 2) := by rw [F.inner_sub, F.zero 1 1 (by decide), sub_zero]
  have h52 : ⟪F.N 5, x 2 - x 1⟫ = 0 := by rw [F.inner_sub, F.zero 5 2 (by decide), F.zero 5 1 (by decide), sub_self]
  have h56 : ⟪F.N 5, x 6 - x 1⟫ = 0 := by rw [F.inner_sub, F.zero 5 6 (by decide), F.zero 5 1 (by decide), sub_self]
  have h50 : ⟪F.N 5, x 0 - x 1⟫ = F.f 5 (x 0) := by rw [F.inner_sub, F.zero 5 1 (by decide), sub_zero]
  have hdet : (Matrix.of ![![⟪F.N 5, x 0 - x 1⟫, ⟪F.N 5, x 2 - x 1⟫, ⟪F.N 5, x 6 - x 1⟫],
      ![⟪F.N 1, x 0 - x 1⟫, ⟪F.N 1, x 2 - x 1⟫, ⟪F.N 1, x 6 - x 1⟫],
      ![⟪F.N 0, x 0 - x 1⟫, ⟪F.N 0, x 2 - x 1⟫, ⟪F.N 0, x 6 - x 1⟫]]).det ≠ 0 :=
    det_upper_tri_ne_zero (by simp [h10]) (by simp [h00]) (by simp [h02])
      (by simp [h50]; exact (F.neg 5 0 (by decide)).ne)
      (by simp [h12]; exact (F.neg 1 2 (by decide)).ne)
      (by simp [h06]; exact (F.neg 0 6 (by decide)).ne)
  have hD0 : D = 0 := by
    refine eq_zero_of_inner_basis hdet ?_ ?_ ?_
    · simp only [D, inner_sub_left, inner_add_left, real_inner_smul_left,
        h2_0, h4_0, h7_0, h50]
      have hf2' : F.f 2 (x 1) ≠ 0 := (F.neg 2 1 (by decide)).ne
      have hf4' : F.f 4 (x 1) ≠ 0 := (F.neg 4 1 (by decide)).ne
      have hf7' : F.f 7 (x 1) ≠ 0 := (F.neg 7 1 (by decide)).ne
      have hf5' : F.f 5 (x 0) ≠ 0 := (F.neg 5 0 (by decide)).ne
      field_simp; simp only [Delta24]; ring
    · simp only [D, inner_sub_left, inner_add_left, real_inner_smul_left,
        h2_2, h4_2, h7_2, h52, mul_zero, sub_zero]
      have hf2' : F.f 2 (x 1) ≠ 0 := (F.neg 2 1 (by decide)).ne
      have hf4' : F.f 4 (x 1) ≠ 0 := (F.neg 4 1 (by decide)).ne
      have hf7' : F.f 7 (x 1) ≠ 0 := (F.neg 7 1 (by decide)).ne
      field_simp; ring
    · simp only [D, inner_sub_left, inner_add_left, real_inner_smul_left,
        h2_6, h4_6, h7_6, h56, mul_zero, sub_zero]
      have hf2' : F.f 2 (x 1) ≠ 0 := (F.neg 2 1 (by decide)).ne
      have hf4' : F.f 4 (x 1) ≠ 0 := (F.neg 4 1 (by decide)).ne
      have hf7' : F.f 7 (x 1) ≠ 0 := (F.neg 7 1 (by decide)).ne
      field_simp; ring
  exact sub_eq_zero.1 hD0

end Syzygies

section Regimes

private theorem lexPos3_pos_or_neg {a b c : ℝ} (h : ¬ (a = 0 ∧ b = 0 ∧ c = 0)) :
    LexPos3 a b c ∨ LexPos3 (-a) (-b) (-c) := by
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · right; exact Or.inl (neg_pos.2 ha)
  · rcases lt_trichotomy b 0 with hb | rfl | hb
    · right; exact Or.inr ⟨neg_zero, Or.inl (neg_pos.2 hb)⟩
    · rcases lt_trichotomy c 0 with hc | rfl | hc
      · right; exact Or.inr ⟨neg_zero, Or.inr ⟨neg_zero, neg_pos.2 hc⟩⟩
      · exact (h ⟨rfl, rfl, rfl⟩).elim
      · left; exact Or.inr ⟨rfl, Or.inr ⟨rfl, hc⟩⟩
    · left; exact Or.inr ⟨rfl, Or.inl hb⟩
  · left; exact Or.inl ha

private theorem lexPos3_neg_not_pos {a b c : ℝ} (h : LexPos3 (-a) (-b) (-c)) : ¬ LexPos3 a b c := by
  rintro (ha | ⟨rfl, hb | ⟨rfl, hc⟩⟩)
  · rcases h with h' | ⟨h', _⟩ <;> linarith
  · rcases h with h' | ⟨_, h' | ⟨h', _⟩⟩ <;> linarith
  · rcases h with h' | ⟨_, h' | ⟨_, h'⟩⟩ <;> linarith

private theorem lexPos3_add {a₁ b₁ c₁ a₂ b₂ c₂ : ℝ} (h₁ : LexPos3 a₁ b₁ c₁) (h₂ : LexPos3 a₂ b₂ c₂) :
    LexPos3 (a₁ + a₂) (b₁ + b₂) (c₁ + c₂) := by
  rcases h₁ with ha₁ | ⟨rfl, hb₁ | ⟨rfl, hc₁⟩⟩ <;> rcases h₂ with ha₂ | ⟨rfl, hb₂ | ⟨rfl, hc₂⟩⟩
  · exact Or.inl (by linarith)
  · exact Or.inl (by linarith)
  · exact Or.inl (by linarith)
  · exact Or.inl (by linarith)
  · exact Or.inr ⟨by ring, Or.inl (by linarith)⟩
  · exact Or.inr ⟨by ring, Or.inl (by linarith)⟩
  · exact Or.inl (by linarith)
  · exact Or.inr ⟨by ring, Or.inl (by linarith)⟩
  · exact Or.inr ⟨by ring, Or.inr ⟨by ring, by linarith⟩⟩

private theorem lexPos3_smul {k a b c : ℝ} (hk : 0 < k) (h : LexPos3 a b c) :
    LexPos3 (k * a) (k * b) (k * c) := by
  rcases h with ha | ⟨rfl, hb | ⟨rfl, hc⟩⟩
  · exact Or.inl (mul_pos hk ha)
  · exact Or.inr ⟨by ring, Or.inl (mul_pos hk hb)⟩
  · exact Or.inr ⟨by ring, Or.inr ⟨by ring, mul_pos hk hc⟩⟩

private theorem lexPos3_smul_iff {k a b c : ℝ} (hk : 0 < k) :
    LexPos3 (k * a) (k * b) (k * c) ↔ LexPos3 a b c := by
  constructor
  · intro h
    simpa [inv_mul_cancel_left₀ hk.ne'] using lexPos3_smul (inv_pos.2 hk) h
  · exact lexPos3_smul hk

private theorem v3_syzygy_dot {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (h6 : ⟪F.N 6, F.N 3⟫ ≤ 0) (h8 : ⟪F.N 8, F.N 3⟫ ≤ 0) : ⟪F.N 7, F.N 3⟫ < 0 := by
  obtain ⟨a, b, c, d, ha, hb, hc, hd, heq⟩ := syzygy_v3 F
  have h33 : 0 < ⟪F.N 3, F.N 3⟫ := inner_pos_self F 3
  have hinn : ⟪a • F.N 3 + b • F.N 7, F.N 3⟫ = ⟪c • F.N 6 + d • F.N 8, F.N 3⟫ := by rw [heq]
  simp only [inner_add_left, real_inner_smul_left] at hinn
  nlinarith [mul_pos ha h33, mul_nonpos_of_nonneg_of_nonpos hc.le h6,
    mul_nonpos_of_nonneg_of_nonpos hd.le h8]

private def Regime1 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  0 < ⟪F.N 2, F.N 3⟫ ∨ 0 < ⟪F.N 4, F.N 3⟫

private def Regime2 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  ⟪F.N 2, F.N 3⟫ ≤ 0 ∧ ⟪F.N 4, F.N 3⟫ ≤ 0 ∧
    (0 < ⟪F.N 6, F.N 3⟫ ∨ (⟪F.N 6, F.N 3⟫ ≤ 0 ∧ ⟪F.N 4, F.N 3⟫ < 0 ∧ ⟪F.N 8, F.N 3⟫ < 0))

private def Regime3 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  ⟪F.N 2, F.N 3⟫ ≤ 0 ∧ ⟪F.N 4, F.N 3⟫ ≤ 0 ∧ ⟪F.N 6, F.N 3⟫ ≤ 0 ∧
    (0 < ⟪F.N 8, F.N 3⟫ ∨ (⟪F.N 8, F.N 3⟫ ≤ 0 ∧ ⟪F.N 2, F.N 3⟫ < 0 ∧ ⟪F.N 6, F.N 3⟫ < 0))

private theorem regime_cover {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hTE : ¬ TwoEar F) :
    Regime1 F ∨ Regime2 F ∨ Regime3 F := by
  by_cases h1 : 0 < ⟪F.N 2, F.N 3⟫ ∨ 0 < ⟪F.N 4, F.N 3⟫
  · exact Or.inl h1
  push Not at h1
  by_cases h6 : 0 < ⟪F.N 6, F.N 3⟫
  · exact Or.inr (Or.inl ⟨h1.1, h1.2, Or.inl h6⟩)
  push Not at h6
  by_cases h8 : 0 < ⟪F.N 8, F.N 3⟫
  · exact Or.inr (Or.inr ⟨h1.1, h1.2, h6, Or.inl h8⟩)
  push Not at h8
  have h7 : ⟪F.N 7, F.N 3⟫ < 0 := v3_syzygy_dot F h6 h8
  have hnot : ¬ ((0 ≤ ⟪F.N 2, F.N 3⟫ ∨ 0 ≤ ⟪F.N 6, F.N 3⟫) ∧
      (0 ≤ ⟪F.N 4, F.N 3⟫ ∨ 0 ≤ ⟪F.N 8, F.N 3⟫)) := fun h => hTE ⟨h7.le, h⟩
  rw [not_and_or] at hnot
  rcases hnot with h26 | h48
  · push Not at h26
    exact Or.inr (Or.inr ⟨h1.1, h1.2, h6, Or.inr ⟨h8, h26.1, h26.2⟩⟩)
  · push Not at h48
    exact Or.inr (Or.inl ⟨h1.1, h1.2, Or.inr ⟨h6, h48.1, h48.2⟩⟩)

private theorem r1_indep {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (t : Fin 9) :
    ¬ (⟪F.N t, F.N 3⟫ = 0 ∧ ⟪F.N t, -F.N 1⟫ = 0 ∧ ⟪F.N t, -F.N 0⟫ = 0) := by
  rintro ⟨h3, h1, h0⟩
  have hdet : (Matrix.of ![![⟪x 0 - x 1, F.N 3⟫, ⟪x 0 - x 1, -F.N 1⟫, ⟪x 0 - x 1, -F.N 0⟫],
      ![⟪x 2 - x 1, F.N 3⟫, ⟪x 2 - x 1, -F.N 1⟫, ⟪x 2 - x 1, -F.N 0⟫],
      ![⟪x 6 - x 1, F.N 3⟫, ⟪x 6 - x 1, -F.N 1⟫, ⟪x 6 - x 1, -F.N 0⟫]]).det ≠ 0 := by
    have h30 : ⟪x 0 - x 1, F.N 3⟫ = -F.f 3 (x 1) := by
      rw [real_inner_comm, F.inner_sub, F.zero 3 0 (by decide), zero_sub]
    have h10 : ⟪x 0 - x 1, -F.N 1⟫ = 0 := by
      rw [real_inner_comm, inner_neg_left, F.inner_sub, F.zero 1 0 (by decide), F.zero 1 1 (by decide), sub_self, neg_zero]
    have h12 : ⟪x 2 - x 1, -F.N 1⟫ = -F.f 1 (x 2) := by
      rw [real_inner_comm, inner_neg_left, F.inner_sub, F.zero 1 1 (by decide), sub_zero]
    have h16 : ⟪x 6 - x 1, -F.N 1⟫ = 0 := by
      rw [real_inner_comm, inner_neg_left, F.inner_sub, F.zero 1 6 (by decide), F.zero 1 1 (by decide), sub_self, neg_zero]
    have h00 : ⟪x 0 - x 1, -F.N 0⟫ = 0 := by
      rw [real_inner_comm, inner_neg_left, F.inner_sub, F.zero 0 0 (by decide), F.zero 0 1 (by decide), sub_self, neg_zero]
    have h02 : ⟪x 2 - x 1, -F.N 0⟫ = 0 := by
      rw [real_inner_comm, inner_neg_left, F.inner_sub, F.zero 0 2 (by decide), F.zero 0 1 (by decide), sub_self, neg_zero]
    have h06 : ⟪x 6 - x 1, -F.N 0⟫ = -F.f 0 (x 6) := by
      rw [real_inner_comm, inner_neg_left, F.inner_sub, F.zero 0 1 (by decide), sub_zero]
    exact det_lower_tri_ne_zero (by simp [h10]) (by simp [h00]) (by simp [h02])
      (by simp [h30]; exact (F.neg 3 1 (by decide)).ne)
      (by simp [h12]; exact (F.neg 1 2 (by decide)).ne)
      (by simp [h06]; exact (F.neg 0 6 (by decide)).ne)
  have ht0 : F.N t = 0 := eq_zero_of_inner_basis hdet h3 h1 h0
  have hpos := inner_pos_self F t
  simp [ht0] at hpos

private theorem r2_indep {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (t : Fin 9) :
    ¬ (⟪F.N t, F.N 3⟫ = 0 ∧ ⟪F.N t, -F.N 6⟫ = 0 ∧ ⟪F.N t, -F.N 2⟫ = 0) := by
  rintro ⟨h3, h6, h2⟩
  have hdet : (Matrix.of ![![⟪x 1 - x 5, F.N 3⟫, ⟪x 1 - x 5, -F.N 6⟫, ⟪x 1 - x 5, -F.N 2⟫],
      ![⟪x 4 - x 5, F.N 3⟫, ⟪x 4 - x 5, -F.N 6⟫, ⟪x 4 - x 5, -F.N 2⟫],
      ![⟪x 3 - x 5, F.N 3⟫, ⟪x 3 - x 5, -F.N 6⟫, ⟪x 3 - x 5, -F.N 2⟫]]).det ≠ 0 := by
    have h31 : ⟪x 1 - x 5, F.N 3⟫ = F.f 3 (x 1) := by
      rw [real_inner_comm, F.inner_sub, F.zero 3 5 (by decide), sub_zero]
    have h34 : ⟪x 4 - x 5, F.N 3⟫ = 0 := by
      rw [real_inner_comm, F.inner_sub, F.zero 3 4 (by decide), F.zero 3 5 (by decide), sub_self]
    have h33 : ⟪x 3 - x 5, F.N 3⟫ = 0 := by
      rw [real_inner_comm, F.inner_sub, F.zero 3 3 (by decide), F.zero 3 5 (by decide), sub_self]
    have h64 : ⟪x 4 - x 5, -F.N 6⟫ = -F.f 6 (x 4) := by
      rw [real_inner_comm, inner_neg_left, F.inner_sub, F.zero 6 5 (by decide), sub_zero]
    have h63 : ⟪x 3 - x 5, -F.N 6⟫ = 0 := by
      rw [real_inner_comm, inner_neg_left, F.inner_sub, F.zero 6 3 (by decide), F.zero 6 5 (by decide), sub_self, neg_zero]
    have h23 : ⟪x 3 - x 5, -F.N 2⟫ = -F.f 2 (x 3) := by
      rw [real_inner_comm, inner_neg_left, F.inner_sub, F.zero 2 5 (by decide), sub_zero]
    exact det_upper_tri_ne_zero (by simp [h34]) (by simp [h33]) (by simp [h63])
      (by simp [h31]; exact (F.neg 3 1 (by decide)).ne)
      (by simp [h64]; exact (F.neg 6 4 (by decide)).ne)
      (by simp [h23]; exact (F.neg 2 3 (by decide)).ne)
  have ht0 : F.N t = 0 := eq_zero_of_inner_basis hdet h3 h6 h2
  have hpos := inner_pos_self F t
  simp [ht0] at hpos

private theorem r3_indep {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (t : Fin 9) :
    ¬ (⟪F.N t, F.N 3⟫ = 0 ∧ ⟪F.N t, -F.N 8⟫ = 0 ∧ ⟪F.N t, -F.N 4⟫ = 0) := by
  rintro ⟨h3, h8, h4⟩
  have hdet : (Matrix.of ![![⟪x 1 - x 4, F.N 3⟫, ⟪x 1 - x 4, -F.N 8⟫, ⟪x 1 - x 4, -F.N 4⟫],
      ![⟪x 5 - x 4, F.N 3⟫, ⟪x 5 - x 4, -F.N 8⟫, ⟪x 5 - x 4, -F.N 4⟫],
      ![⟪x 3 - x 4, F.N 3⟫, ⟪x 3 - x 4, -F.N 8⟫, ⟪x 3 - x 4, -F.N 4⟫]]).det ≠ 0 := by
    have h31 : ⟪x 1 - x 4, F.N 3⟫ = F.f 3 (x 1) := by
      rw [real_inner_comm, F.inner_sub, F.zero 3 4 (by decide), sub_zero]
    have h35 : ⟪x 5 - x 4, F.N 3⟫ = 0 := by
      rw [real_inner_comm, F.inner_sub, F.zero 3 5 (by decide), F.zero 3 4 (by decide), sub_self]
    have h33 : ⟪x 3 - x 4, F.N 3⟫ = 0 := by
      rw [real_inner_comm, F.inner_sub, F.zero 3 3 (by decide), F.zero 3 4 (by decide), sub_self]
    have h85 : ⟪x 5 - x 4, -F.N 8⟫ = -F.f 8 (x 5) := by
      rw [real_inner_comm, inner_neg_left, F.inner_sub, F.zero 8 4 (by decide), sub_zero]
    have h83 : ⟪x 3 - x 4, -F.N 8⟫ = 0 := by
      rw [real_inner_comm, inner_neg_left, F.inner_sub, F.zero 8 3 (by decide), F.zero 8 4 (by decide), sub_self, neg_zero]
    have h43 : ⟪x 3 - x 4, -F.N 4⟫ = -F.f 4 (x 3) := by
      rw [real_inner_comm, inner_neg_left, F.inner_sub, F.zero 4 4 (by decide), sub_zero]
    exact det_upper_tri_ne_zero (by simp [h35]) (by simp [h33]) (by simp [h83])
      (by simp [h31]; exact (F.neg 3 1 (by decide)).ne)
      (by simp [h85]; exact (F.neg 8 5 (by decide)).ne)
      (by simp [h43]; exact (F.neg 4 3 (by decide)).ne)
  have ht0 : F.N t = 0 := eq_zero_of_inner_basis hdet h3 h8 h4
  have hpos := inner_pos_self F t
  simp [ht0] at hpos

end Regimes

section RimClosure

private theorem lemmaM_quad {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    ⟪x 0, -F.N 1⟫ < ⟪x 3, -F.N 1⟫ ∧ ⟪x 0, -F.N 1⟫ < ⟪x 4, -F.N 1⟫ ∧
      ⟪x 0, -F.N 1⟫ < ⟪x 5, -F.N 1⟫ ∧
      (⟪x 4, -F.N 1⟫ < ⟪x 3, -F.N 1⟫ ∨ ⟪x 5, -F.N 1⟫ < ⟪x 3, -F.N 1⟫) := by
  have h0lt : ∀ v : Fin 7, v ∉ ({0, 1, 6} : Finset (Fin 7)) → ⟪x 0, -F.N 1⟫ < ⟪x v, -F.N 1⟫ := by
    intro v hv
    rw [← sub_pos, ← inner_sub_left, real_inner_comm, inner_neg_left, F.inner_sub,
      F.zero 1 0 (by decide), sub_zero]
    exact neg_pos.2 (F.neg 1 v (by simpa [s0x_S24] using hv))
  refine ⟨h0lt 3 (by decide), h0lt 4 (by decide), h0lt 5 (by decide), ?_⟩
  let σ : ℝ := F.f 2 (x 3) / F.f 2 (x 4)
  let τ : ℝ := F.f 4 (x 3) / F.f 4 (x 5)
  have hf24 : F.f 2 (x 4) < 0 := F.neg 2 4 (by decide)
  have hf23 : F.f 2 (x 3) < 0 := F.neg 2 3 (by decide)
  have hf45 : F.f 4 (x 5) < 0 := F.neg 4 5 (by decide)
  have hf43 : F.f 4 (x 3) < 0 := F.neg 4 3 (by decide)
  have hσ : 0 < σ := div_pos_of_neg_of_neg hf23 hf24
  have hτ : 0 < τ := div_pos_of_neg_of_neg hf43 hf45
  let D := (x 3 - x 0) - (σ • (x 4 - x 0) + τ • (x 5 - x 0))
  have hdet : (Matrix.of ![![⟪x 1 - x 0, F.N 3⟫, ⟪x 1 - x 0, F.N 4⟫, ⟪x 1 - x 0, F.N 2⟫],
      ![⟪x 5 - x 0, F.N 3⟫, ⟪x 5 - x 0, F.N 4⟫, ⟪x 5 - x 0, F.N 2⟫],
      ![⟪x 4 - x 0, F.N 3⟫, ⟪x 4 - x 0, F.N 4⟫, ⟪x 4 - x 0, F.N 2⟫]]).det ≠ 0 := by
    have h31 : ⟪x 1 - x 0, F.N 3⟫ = F.f 3 (x 1) := by rw [real_inner_comm, F.inner_sub, F.zero 3 0 (by decide), sub_zero]
    have h35 : ⟪x 5 - x 0, F.N 3⟫ = 0 := by rw [real_inner_comm, F.inner_sub, F.zero 3 5 (by decide), F.zero 3 0 (by decide), sub_self]
    have h34 : ⟪x 4 - x 0, F.N 3⟫ = 0 := by rw [real_inner_comm, F.inner_sub, F.zero 3 4 (by decide), F.zero 3 0 (by decide), sub_self]
    have h45 : ⟪x 5 - x 0, F.N 4⟫ = F.f 4 (x 5) := by rw [real_inner_comm, F.inner_sub, F.zero 4 0 (by decide), sub_zero]
    have h44 : ⟪x 4 - x 0, F.N 4⟫ = 0 := by rw [real_inner_comm, F.inner_sub, F.zero 4 4 (by decide), F.zero 4 0 (by decide), sub_self]
    have h24 : ⟪x 4 - x 0, F.N 2⟫ = F.f 2 (x 4) := by rw [real_inner_comm, F.inner_sub, F.zero 2 0 (by decide), sub_zero]
    exact det_upper_tri_ne_zero (by simp [h35]) (by simp [h34]) (by simp [h44])
      (by simp [h31]; exact (F.neg 3 1 (by decide)).ne)
      (by simp [h45]; exact hf45.ne)
      (by simp [h24]; exact hf24.ne)
  have hD0 : D = 0 := by
    have e3 : ∀ v, ⟪x v, F.N 3⟫ = ⟪F.N 3, x v⟫ := fun v => real_inner_comm _ _
    have e4 : ∀ v, ⟪x v, F.N 4⟫ = ⟪F.N 4, x v⟫ := fun v => real_inner_comm _ _
    have e2 : ∀ v, ⟪x v, F.N 2⟫ = ⟪F.N 2, x v⟫ := fun v => real_inner_comm _ _
    have hD3 : ⟪D, F.N 3⟫ = 0 := by
      simp only [D, inner_sub_left, inner_add_left, real_inner_smul_left, e3,
        ← inner_sub_right, F.inner_sub, F.zero 3 3 (by decide), F.zero 3 0 (by decide),
        F.zero 3 4 (by decide), F.zero 3 5 (by decide), sub_self, mul_zero, add_zero]
    have hD4 : ⟪D, F.N 4⟫ = 0 := by
      have hf45' : F.f 4 (x 5) ≠ 0 := hf45.ne
      simp only [D, inner_sub_left, inner_add_left, real_inner_smul_left, e4,
        ← inner_sub_right, F.inner_sub, F.zero 4 0 (by decide), F.zero 4 4 (by decide),
        sub_zero, sub_self, mul_zero, zero_add]
      dsimp only [τ]; field_simp; ring
    have hD2 : ⟪D, F.N 2⟫ = 0 := by
      have hf24' : F.f 2 (x 4) ≠ 0 := hf24.ne
      simp only [D, inner_sub_left, inner_add_left, real_inner_smul_left, e2,
        ← inner_sub_right, F.inner_sub, F.zero 2 0 (by decide), F.zero 2 5 (by decide),
        sub_zero, sub_self, mul_zero, add_zero]
      dsimp only [σ]; field_simp; ring
    exact eq_zero_of_inner_basis hdet hD3 hD4 hD2
  have hrep : x 3 - x 0 = σ • (x 4 - x 0) + τ • (x 5 - x 0) := sub_eq_zero.1 hD0
  have hst : 1 < σ + τ := by
    have h8 : ⟪F.N 8, x 3 - x 0⟫ = ⟪F.N 8, σ • (x 4 - x 0) + τ • (x 5 - x 0)⟫ := by rw [hrep]
    simp only [inner_add_right, real_inner_smul_right, F.inner_sub,
      F.zero 8 3 (by decide), F.zero 8 4 (by decide), zero_sub] at h8
    have hf80 : 0 < -F.f 8 (x 0) := neg_pos.2 (F.neg 8 0 (by decide))
    have hf85 : F.f 8 (x 5) < 0 := F.neg 8 5 (by decide)
    nlinarith
  have h1 : ⟪x 3 - x 0, -F.N 1⟫ = σ * ⟪x 4 - x 0, -F.N 1⟫ + τ * ⟪x 5 - x 0, -F.N 1⟫ := by
    rw [hrep, inner_add_left, real_inner_smul_left, real_inner_smul_left]
  simp only [inner_sub_left] at h1
  have h03 : 0 < ⟪x 3, -F.N 1⟫ - ⟪x 0, -F.N 1⟫ := sub_pos.2 (h0lt 3 (by decide))
  have h04 : 0 < ⟪x 4, -F.N 1⟫ - ⟪x 0, -F.N 1⟫ := sub_pos.2 (h0lt 4 (by decide))
  have h05 : 0 < ⟪x 5, -F.N 1⟫ - ⟪x 0, -F.N 1⟫ := sub_pos.2 (h0lt 5 (by decide))
  by_contra hnot
  push Not at hnot
  nlinarith [mul_le_mul_of_nonneg_left (show ⟪x 3, -F.N 1⟫ - ⟪x 0, -F.N 1⟫ ≤ ⟪x 4, -F.N 1⟫ - ⟪x 0, -F.N 1⟫ by linarith) hσ.le,
    mul_le_mul_of_nonneg_left (show ⟪x 3, -F.N 1⟫ - ⟪x 0, -F.N 1⟫ ≤ ⟪x 5, -F.N 1⟫ - ⟪x 0, -F.N 1⟫ by linarith) hτ.le]

private theorem lexLt3_of_fst {p q : ℝ × ℝ × ℝ} (h : p.1 < q.1) : LexLt3 p q :=
  Or.inl (sub_pos.2 h)

private theorem lexLt3_of_snd {p q : ℝ × ℝ × ℝ} (h1 : p.1 = q.1) (h2 : p.2.1 < q.2.1) :
    LexLt3 p q :=
  Or.inr ⟨sub_eq_zero.2 h1.symm, Or.inl (sub_pos.2 h2)⟩

private theorem lexLt3_of_thd {p q : ℝ × ℝ × ℝ} (h1 : p.1 = q.1) (h2 : p.2.1 = q.2.1)
    (h3 : p.2.2 < q.2.2) : LexLt3 p q :=
  Or.inr ⟨sub_eq_zero.2 h1.symm, Or.inr ⟨sub_eq_zero.2 h2.symm, sub_pos.2 h3⟩⟩

private theorem robUniLex_of_arc {k : ℕ} [NeZero k] {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (c : ZMod k → Fin 7) (hc : Function.Injective c) (d1 d2 : ℝ³)
    (harc : ∀ B : ZMod k, ∀ b c' d : ℕ, 0 < b → b < c' → c' < d → d < k →
      (c B ≠ 2 ∧ c B ≠ 6) → (c (B + c') ≠ 2 ∧ c (B + c') ≠ 6) →
      (c (B + b) ≠ 2 ∧ c (B + b) ≠ 6 ∧
        (LexLt3 (⟪x (c B), F.N 3⟫, ⟪x (c B), d1⟫, ⟪x (c B), d2⟫)
            (⟪x (c (B + b)), F.N 3⟫, ⟪x (c (B + b)), d1⟫, ⟪x (c (B + b)), d2⟫) ∨
         LexLt3 (⟪x (c (B + c')), F.N 3⟫, ⟪x (c (B + c')), d1⟫, ⟪x (c (B + c')), d2⟫)
            (⟪x (c (B + b)), F.N 3⟫, ⟪x (c (B + b)), d1⟫, ⟪x (c (B + b)), d2⟫))) ∨
      (c (B + d) ≠ 2 ∧ c (B + d) ≠ 6 ∧
        (LexLt3 (⟪x (c B), F.N 3⟫, ⟪x (c B), d1⟫, ⟪x (c B), d2⟫)
            (⟪x (c (B + d)), F.N 3⟫, ⟪x (c (B + d)), d1⟫, ⟪x (c (B + d)), d2⟫) ∨
         LexLt3 (⟪x (c (B + c')), F.N 3⟫, ⟪x (c (B + c')), d1⟫, ⟪x (c (B + c')), d2⟫)
            (⟪x (c (B + d)), F.N 3⟫, ⟪x (c (B + d)), d1⟫, ⟪x (c (B + d)), d2⟫))))
    (hrange : ∀ i : ZMod k, c i ∈ ({0, 2, 3, 4, 5, 6} : Finset (Fin 7))) :
    RobUniLex (fun i => (⟪x (c i), F.N 3⟫, ⟪x (c i), d1⟫, ⟪x (c i), d2⟫)) := by
  have hZmax : ∀ v : Fin 7, v ∈ ({0, 3, 4, 5} : Finset (Fin 7)) →
      ⟪x v, F.N 3⟫ = ⟪x 0, F.N 3⟫ := by
    intro v hv
    rw [← sub_eq_zero, ← inner_sub_left, real_inner_comm, F.inner_sub,
      F.zero 3 0 (by decide), F.zero 3 v (by simpa [s0x_S24] using hv), sub_zero]
  have hZlt2 : ⟪x 2, F.N 3⟫ < ⟪x 0, F.N 3⟫ := by
    rw [← sub_lt_zero, ← inner_sub_left, real_inner_comm, F.inner_sub, F.zero 3 0 (by decide), sub_zero]
    exact F.neg 3 2 (by decide)
  have hZlt6 : ⟪x 6, F.N 3⟫ < ⟪x 0, F.N 3⟫ := by
    rw [← sub_lt_zero, ← inner_sub_left, real_inner_comm, F.inner_sub, F.zero 3 0 (by decide), sub_zero]
    exact F.neg 3 6 (by decide)
  have hZlt : ∀ v : Fin 7, v = 2 ∨ v = 6 → ⟪x v, F.N 3⟫ < ⟪x 0, F.N 3⟫ := by
    rintro v (rfl | rfl) <;> assumption
  have hmem_quad : ∀ i : ZMod k, ¬ (c i = 2 ∨ c i = 6) →
      c i ∈ ({0, 3, 4, 5} : Finset (Fin 7)) := by
    intro i hi
    have hri := hrange i
    simp only [mem_insert, mem_singleton] at hri ⊢
    rcases hri with h | h | h | h | h | h
    · exact Or.inl h
    · exact absurd (Or.inl h) hi
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
    · exact absurd (Or.inr h) hi
  intro B b c' d hb hbc hcd hd
  have hne : ∀ {p q : ℕ}, p < q → q < k → B + p ≠ B + q := by
    intro p q hpq hqk heq
    have h1 : ((q : ZMod k) - (p : ZMod k)) = 0 := by
      have := congrArg (fun t => t - B) heq
      linear_combination -this
    rw [← Nat.cast_sub hpq.le, ZMod.natCast_eq_zero_iff] at h1
    exact absurd (Nat.le_of_dvd (Nat.sub_pos_of_lt hpq) h1) (by omega)
  by_cases hB26 : c B = 2 ∨ c B = 6
  · by_cases hC26 : c (B + c') = 2 ∨ c (B + c') = 6
    · have hBneC : B ≠ B + c' := by simpa using hne (by omega : 0 < c') (by omega)
      have hBneB : B ≠ B + b := by simpa using hne hb (by omega)
      have hCneB : B + c' ≠ B + b := (hne hbc (by omega)).symm
      have hBb26 : ¬ (c (B + b) = 2 ∨ c (B + b) = 6) := by
        rintro (h | h) <;> rcases hB26 with hB | hB <;> rcases hC26 with hC | hC
        · exact hBneC (hc (hB.trans hC.symm))
        · exact hBneB (hc (hB.trans h.symm))
        · exact hCneB (hc (hC.trans h.symm))
        · exact hBneC (hc (hB.trans hC.symm))
        · exact hBneC (hc (hB.trans hC.symm))
        · exact hCneB (hc (hC.trans h.symm))
        · exact hBneB (hc (hB.trans h.symm))
        · exact hBneC (hc (hB.trans hC.symm))
      left
      exact lexLt3_of_fst (by dsimp only; rw [hZmax _ (hmem_quad _ hBb26)]; exact hZlt _ hB26)
    · by_cases hBb26 : c (B + b) = 2 ∨ c (B + b) = 6
      · by_cases hBd26 : c (B + d) = 2 ∨ c (B + d) = 6
        · exfalso
          have hBneB : B ≠ B + b := by simpa using hne hb (by omega)
          have hBneD : B ≠ B + d := by simpa using hne (by omega : 0 < d) hd
          have hBneBD : B + b ≠ B + d := hne (by omega) hd
          rcases hB26 with h1 | h1 <;> rcases hBb26 with h2 | h2 <;> rcases hBd26 with h3 | h3
          · exact hBneB (hc (h1.trans h2.symm))
          · exact hBneB (hc (h1.trans h2.symm))
          · exact hBneD (hc (h1.trans h3.symm))
          · exact hBneBD (hc (h2.trans h3.symm))
          · exact hBneBD (hc (h2.trans h3.symm))
          · exact hBneD (hc (h1.trans h3.symm))
          · exact hBneB (hc (h1.trans h2.symm))
          · exact hBneB (hc (h1.trans h2.symm))
        · right; right; left
          exact lexLt3_of_fst (by dsimp only; rw [hZmax _ (hmem_quad _ hBd26)]; exact hZlt _ hB26)
      · left
        exact lexLt3_of_fst (by dsimp only; rw [hZmax _ (hmem_quad _ hBb26)]; exact hZlt _ hB26)
  · by_cases hC26 : c (B + c') = 2 ∨ c (B + c') = 6
    · by_cases hBb26 : c (B + b) = 2 ∨ c (B + b) = 6
      · by_cases hBd26 : c (B + d) = 2 ∨ c (B + d) = 6
        · exfalso
          have hCneB : B + c' ≠ B + b := (hne hbc (by omega)).symm
          have hCneD : B + c' ≠ B + d := hne hcd hd
          have hBneD : B + b ≠ B + d := hne (by omega) hd
          rcases hC26 with h1 | h1 <;> rcases hBb26 with h2 | h2 <;> rcases hBd26 with h3 | h3
          · exact hCneB (hc (h1.trans h2.symm))
          · exact hCneB (hc (h1.trans h2.symm))
          · exact hCneD (hc (h1.trans h3.symm))
          · exact hBneD (hc (h2.trans h3.symm))
          · exact hBneD (hc (h2.trans h3.symm))
          · exact hCneD (hc (h1.trans h3.symm))
          · exact hCneB (hc (h1.trans h2.symm))
          · exact hCneB (hc (h1.trans h2.symm))
        · right; right; right
          exact lexLt3_of_fst (by dsimp only; rw [hZmax _ (hmem_quad _ hBd26)]; exact hZlt _ hC26)
      · right; left
        exact lexLt3_of_fst (by dsimp only; rw [hZmax _ (hmem_quad _ hBb26)]; exact hZlt _ hC26)
    · have hB26' : c B ≠ 2 ∧ c B ≠ 6 := by tauto
      have hC26' : c (B + c') ≠ 2 ∧ c (B + c') ≠ 6 := by tauto
      rcases harc B b c' d hb hbc hcd hd hB26' hC26' with ⟨_, _, h1 | h2⟩ | ⟨_, _, h1 | h2⟩
      · exact Or.inl h1
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr (Or.inl h1))
      · exact Or.inr (Or.inr (Or.inr h2))

private def checkArcR1 {k : ℕ} [NeZero k] (c : ZMod k → Fin 7) : Bool :=
  (List.finRange k).all fun B =>
    (List.finRange k).all fun b =>
      (List.finRange k).all fun c' =>
        (List.finRange k).all fun d =>
          let Bz : ZMod k := (B.val : ZMod k)
          if 0 < b.val && b.val < c'.val && c'.val < d.val &&
              c Bz != 2 && c Bz != 6 && c (Bz + c'.val) != 2 && c (Bz + c'.val) != 6 then
            (c (Bz + b.val) != 2 && c (Bz + b.val) != 6 && c (Bz + b.val) != 0 &&
              (c Bz == 0 || c (Bz + c'.val) == 0 || c (Bz + b.val) == 3)) ||
            (c (Bz + d.val) != 2 && c (Bz + d.val) != 6 && c (Bz + d.val) != 0 &&
              (c Bz == 0 || c (Bz + c'.val) == 0 || c (Bz + d.val) == 3))
          else true

private theorem robUniLex_r1 {k : ℕ} [NeZero k] {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (c : ZMod k → Fin 7) (hc : Function.Injective c)
    (hrange : ∀ i : ZMod k, c i ∈ ({0, 2, 3, 4, 5, 6} : Finset (Fin 7)))
    (hcomb : checkArcR1 c = true) :
    RobUniLex (fun i => (⟪x (c i), F.N 3⟫, ⟪x (c i), -F.N 1⟫, ⟪x (c i), -F.N 0⟫)) := by
  obtain ⟨h03, h04, h05, h3m⟩ := lemmaM_quad F
  have hZmax : ∀ v : Fin 7, v ∈ ({0, 3, 4, 5} : Finset (Fin 7)) →
      ⟪x v, F.N 3⟫ = ⟪x 0, F.N 3⟫ := fun v hv => by
    rw [← sub_eq_zero, ← inner_sub_left, real_inner_comm, F.inner_sub,
      F.zero 3 0 (by decide), F.zero 3 v (by simpa [s0x_S24] using hv), sub_zero]
  have hcmp : ∀ p q r : ZMod k, (c p ≠ 2 ∧ c p ≠ 6) → (c q ≠ 2 ∧ c q ≠ 6) →
      (c r ≠ 2 ∧ c r ≠ 6) → p ≠ q → r ≠ q → p ≠ r →
      c q ≠ 0 → (c p = 0 ∨ c r = 0 ∨ c q = 3) →
      LexLt3 (⟪x (c p), F.N 3⟫, ⟪x (c p), -F.N 1⟫, ⟪x (c p), -F.N 0⟫)
          (⟪x (c q), F.N 3⟫, ⟪x (c q), -F.N 1⟫, ⟪x (c q), -F.N 0⟫) ∨
        LexLt3 (⟪x (c r), F.N 3⟫, ⟪x (c r), -F.N 1⟫, ⟪x (c r), -F.N 0⟫)
          (⟪x (c q), F.N 3⟫, ⟪x (c q), -F.N 1⟫, ⟪x (c q), -F.N 0⟫) := by
    intro p q r hp hq hr hpq hrq hpr hq0 hcase
    have mem4 : ∀ {i}, c i ≠ 2 ∧ c i ≠ 6 → c i = 0 ∨ c i = 3 ∨ c i = 4 ∨ c i = 5 := by
      intro i hi
      have := hrange i
      simp only [mem_insert, mem_singleton] at this
      tauto
    have hZeq : ∀ {u v}, (c u ≠ 2 ∧ c u ≠ 6) → (c v ≠ 2 ∧ c v ≠ 6) →
        ⟪x (c u), F.N 3⟫ = ⟪x (c v), F.N 3⟫ := by
      intro u v hu hv
      have h1 : c u ∈ ({0, 3, 4, 5} : Finset (Fin 7)) := by
        rcases mem4 hu with h | h | h | h <;> simp [h]
      have h2 : c v ∈ ({0, 3, 4, 5} : Finset (Fin 7)) := by
        rcases mem4 hv with h | h | h | h <;> simp [h]
      rw [hZmax _ h1, hZmax _ h2]
    rcases hcase with hp0 | hr0 | hq3
    · left
      refine lexLt3_of_snd (hZeq hp hq) ?_
      rw [hp0]
      rcases mem4 hq with h | h | h | h
      · exact absurd h hq0
      · rw [h]; exact h03
      · rw [h]; exact h04
      · rw [h]; exact h05
    · right
      refine lexLt3_of_snd (hZeq hr hq) ?_
      rw [hr0]
      rcases mem4 hq with h | h | h | h
      · exact absurd h hq0
      · rw [h]; exact h03
      · rw [h]; exact h04
      · rw [h]; exact h05
    · have hcpq : c p ≠ c q := fun h => hpq (hc h)
      have hcrq : c r ≠ c q := fun h => hrq (hc h)
      have hcpr : c p ≠ c r := fun h => hpr (hc h)
      rcases h3m with h43 | h53
      · by_cases hp4 : c p = 4 ∨ c p = 0
        · left; refine lexLt3_of_snd (hZeq hp hq) ?_
          rw [hq3]; rcases hp4 with h | h <;> rw [h] <;> assumption
        · by_cases hr4 : c r = 4 ∨ c r = 0
          · right; refine lexLt3_of_snd (hZeq hr hq) ?_
            rw [hq3]; rcases hr4 with h | h <;> rw [h] <;> assumption
          · exfalso
            rcases mem4 hp with hp' | hp' | hp' | hp'
            · exact hp4 (Or.inr hp')
            · exact hcpq (hp'.trans hq3.symm)
            · exact hp4 (Or.inl hp')
            · rcases mem4 hr with hr' | hr' | hr' | hr'
              · exact hr4 (Or.inr hr')
              · exact hcrq (hr'.trans hq3.symm)
              · exact hr4 (Or.inl hr')
              · exact hcpr (hp'.trans hr'.symm)
      · by_cases hp5 : c p = 5 ∨ c p = 0
        · left; refine lexLt3_of_snd (hZeq hp hq) ?_
          rw [hq3]; rcases hp5 with h | h <;> rw [h] <;> assumption
        · by_cases hr5 : c r = 5 ∨ c r = 0
          · right; refine lexLt3_of_snd (hZeq hr hq) ?_
            rw [hq3]; rcases hr5 with h | h <;> rw [h] <;> assumption
          · exfalso
            rcases mem4 hp with hp' | hp' | hp' | hp'
            · exact hp5 (Or.inr hp')
            · exact hcpq (hp'.trans hq3.symm)
            · rcases mem4 hr with hr' | hr' | hr' | hr'
              · exact hr5 (Or.inr hr')
              · exact hcrq (hr'.trans hq3.symm)
              · exact hcpr (hp'.trans hr'.symm)
              · exact hr5 (Or.inl hr')
            · exact hp5 (Or.inl hp')
  refine robUniLex_of_arc F c hc (-F.N 1) (-F.N 0) ?_ hrange
  intro B b c' d hb hbc hcd hd hB hC
  have hne : ∀ {p q : ℕ}, p < q → q < k → B + p ≠ B + q := by
    intro p q hpq hqk heq
    have h1 : ((q : ZMod k) - (p : ZMod k)) = 0 := by
      have := congrArg (fun t => t - B) heq
      linear_combination -this
    rw [← Nat.cast_sub hpq.le, ZMod.natCast_eq_zero_iff] at h1
    exact absurd (Nat.le_of_dvd (Nat.sub_pos_of_lt hpq) h1) (by omega)
  have hBC : B ≠ B + c' := by simpa using hne (by omega : 0 < c') (by omega)
  have hcomb' : (c (B + b) ≠ 2 ∧ c (B + b) ≠ 6 ∧ c (B + b) ≠ 0 ∧
        (c B = 0 ∨ c (B + c') = 0 ∨ c (B + b) = 3)) ∨
      (c (B + d) ≠ 2 ∧ c (B + d) ≠ 6 ∧ c (B + d) ≠ 0 ∧
        (c B = 0 ∨ c (B + c') = 0 ∨ c (B + d) = 3)) := by
    simp only [checkArcR1, List.all_eq_true, List.mem_finRange, forall_true_left] at hcomb
    have hspec := hcomb ⟨B.val, ZMod.val_lt B⟩ ⟨b, by omega⟩ ⟨c', by omega⟩ ⟨d, hd⟩
    have hcond : (0 < b && b < c' && c' < d && c B != 2 && c B != 6 &&
        c (B + c') != 2 && c (B + c') != 6) = true := by
      simp [hb, hbc, hcd, hB.1, hB.2, hC.1, hC.2]
    simp only [ZMod.natCast_zmod_val] at hspec
    simp only [hcond, ↓reduceIte] at hspec
    simpa [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne,
      and_assoc, or_assoc] using hspec
  rcases hcomb' with
    ⟨hb1, hb2, hb0, hbcase⟩ | ⟨hd1, hd2, hd0, hdcase⟩
  · left
    refine ⟨hb1, hb2, hcmp B (B + b) (B + c') hB ⟨hb1, hb2⟩ hC
      (by simpa using hne hb (by omega)) (hne hbc (by omega)).symm hBC hb0 hbcase⟩
  · right
    refine ⟨hd1, hd2, hcmp B (B + d) (B + c') hB ⟨hd1, hd2⟩ hC
      (by simpa using hne (by omega : 0 < d) hd) (hne hcd hd) hBC hd0 hdcase⟩

private def checkArcR2 {k : ℕ} [NeZero k] (c : ZMod k → Fin 7) : Bool :=
  (List.finRange k).all fun B =>
    (List.finRange k).all fun b =>
      (List.finRange k).all fun c' =>
        (List.finRange k).all fun d =>
          let Bz : ZMod k := (B.val : ZMod k)
          if 0 < b.val && b.val < c'.val && c'.val < d.val &&
              c Bz != 2 && c Bz != 6 && c (Bz + c'.val) != 2 && c (Bz + c'.val) != 6 then
            (c (Bz + b.val) != 2 && c (Bz + b.val) != 6 && c (Bz + b.val) != 5 &&
              (!(c (Bz + b.val) == 3) || (c Bz == 5 || c (Bz + c'.val) == 5)) &&
              (!(c (Bz + b.val) == 0 || c (Bz + b.val) == 4) ||
                (c Bz == 3 || c Bz == 5 || c (Bz + c'.val) == 3 || c (Bz + c'.val) == 5))) ||
            (c (Bz + d.val) != 2 && c (Bz + d.val) != 6 && c (Bz + d.val) != 5 &&
              (!(c (Bz + d.val) == 3) || (c Bz == 5 || c (Bz + c'.val) == 5)) &&
              (!(c (Bz + d.val) == 0 || c (Bz + d.val) == 4) ||
                (c Bz == 3 || c Bz == 5 || c (Bz + c'.val) == 3 || c (Bz + c'.val) == 5)))
          else true

private theorem robUniLex_r2 {k : ℕ} [NeZero k] {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (c : ZMod k → Fin 7) (hc : Function.Injective c)
    (hrange : ∀ i : ZMod k, c i ∈ ({0, 2, 3, 4, 5, 6} : Finset (Fin 7)))
    (hcomb : checkArcR2 c = true) :
    RobUniLex (fun i => (⟪x (c i), F.N 3⟫, ⟪x (c i), -F.N 6⟫, ⟪x (c i), -F.N 2⟫)) := by
  have hZmax : ∀ v : Fin 7, v ∈ ({0, 3, 4, 5} : Finset (Fin 7)) →
      ⟪x v, F.N 3⟫ = ⟪x 0, F.N 3⟫ := fun v hv => by
    rw [← sub_eq_zero, ← inner_sub_left, real_inner_comm, F.inner_sub,
      F.zero 3 0 (by decide), F.zero 3 v (by simpa [s0x_S24] using hv), sub_zero]
  have h35_6 : ⟪x 5, -F.N 6⟫ = ⟪x 3, -F.N 6⟫ := by
    rw [← sub_eq_zero, ← inner_sub_left, real_inner_comm, inner_neg_left, F.inner_sub,
      F.zero 6 5 (by decide), F.zero 6 3 (by decide), sub_self, neg_zero]
  have h50_6 : ⟪x 5, -F.N 6⟫ < ⟪x 0, -F.N 6⟫ := by
    rw [← sub_pos, ← inner_sub_left, real_inner_comm, inner_neg_left, F.inner_sub,
      F.zero 6 5 (by decide), sub_zero]; exact neg_pos.2 (F.neg 6 0 (by decide))
  have h54_6 : ⟪x 5, -F.N 6⟫ < ⟪x 4, -F.N 6⟫ := by
    rw [← sub_pos, ← inner_sub_left, real_inner_comm, inner_neg_left, F.inner_sub,
      F.zero 6 5 (by decide), sub_zero]; exact neg_pos.2 (F.neg 6 4 (by decide))
  have h30_6 : ⟪x 3, -F.N 6⟫ < ⟪x 0, -F.N 6⟫ := by rwa [← h35_6]
  have h34_6 : ⟪x 3, -F.N 6⟫ < ⟪x 4, -F.N 6⟫ := by rwa [← h35_6]
  have h53_2 : ⟪x 5, -F.N 2⟫ < ⟪x 3, -F.N 2⟫ := by
    rw [← sub_pos, ← inner_sub_left, real_inner_comm, inner_neg_left, F.inner_sub,
      F.zero 2 5 (by decide), sub_zero]; exact neg_pos.2 (F.neg 2 3 (by decide))
  have hcmp : ∀ p q r : ZMod k, (c p ≠ 2 ∧ c p ≠ 6) → (c q ≠ 2 ∧ c q ≠ 6) →
      (c r ≠ 2 ∧ c r ≠ 6) → c q ≠ 5 →
      (c q = 3 → c p = 5 ∨ c r = 5) →
      (c q = 0 ∨ c q = 4 → c p = 3 ∨ c p = 5 ∨ c r = 3 ∨ c r = 5) →
      LexLt3 (⟪x (c p), F.N 3⟫, ⟪x (c p), -F.N 6⟫, ⟪x (c p), -F.N 2⟫)
          (⟪x (c q), F.N 3⟫, ⟪x (c q), -F.N 6⟫, ⟪x (c q), -F.N 2⟫) ∨
        LexLt3 (⟪x (c r), F.N 3⟫, ⟪x (c r), -F.N 6⟫, ⟪x (c r), -F.N 2⟫)
          (⟪x (c q), F.N 3⟫, ⟪x (c q), -F.N 6⟫, ⟪x (c q), -F.N 2⟫) := by
    intro p q r hp hq hr hq5 hq3 hq04
    have mem4 : ∀ {i}, c i ≠ 2 ∧ c i ≠ 6 → c i = 0 ∨ c i = 3 ∨ c i = 4 ∨ c i = 5 := by
      intro i hi; have := hrange i; simp only [mem_insert, mem_singleton] at this; tauto
    have hZeq : ∀ {u v}, (c u ≠ 2 ∧ c u ≠ 6) → (c v ≠ 2 ∧ c v ≠ 6) →
        ⟪x (c u), F.N 3⟫ = ⟪x (c v), F.N 3⟫ := by
      intro u v hu hv
      have h1 : c u ∈ ({0, 3, 4, 5} : Finset (Fin 7)) := by rcases mem4 hu with h | h | h | h <;> simp [h]
      have h2 : c v ∈ ({0, 3, 4, 5} : Finset (Fin 7)) := by rcases mem4 hv with h | h | h | h <;> simp [h]
      rw [hZmax _ h1, hZmax _ h2]
    rcases mem4 hq with hq' | hq' | hq' | hq'
    · rcases hq04 (Or.inl hq') with hp3 | hp5 | hr3 | hr5
      · left; exact lexLt3_of_snd (hZeq hp hq) (by rw [hp3, hq']; exact h30_6)
      · left; exact lexLt3_of_snd (hZeq hp hq) (by rw [hp5, hq']; exact h50_6)
      · right; exact lexLt3_of_snd (hZeq hr hq) (by rw [hr3, hq']; exact h30_6)
      · right; exact lexLt3_of_snd (hZeq hr hq) (by rw [hr5, hq']; exact h50_6)
    · rcases hq3 hq' with hp5 | hr5
      · left; exact lexLt3_of_thd (hZeq hp hq) (by rw [hp5, hq']; exact h35_6) (by rw [hp5, hq']; exact h53_2)
      · right; exact lexLt3_of_thd (hZeq hr hq) (by rw [hr5, hq']; exact h35_6) (by rw [hr5, hq']; exact h53_2)
    · rcases hq04 (Or.inr hq') with hp3 | hp5 | hr3 | hr5
      · left; exact lexLt3_of_snd (hZeq hp hq) (by rw [hp3, hq']; exact h34_6)
      · left; exact lexLt3_of_snd (hZeq hp hq) (by rw [hp5, hq']; exact h54_6)
      · right; exact lexLt3_of_snd (hZeq hr hq) (by rw [hr3, hq']; exact h34_6)
      · right; exact lexLt3_of_snd (hZeq hr hq) (by rw [hr5, hq']; exact h54_6)
    · exact absurd hq' hq5
  refine robUniLex_of_arc F c hc (-F.N 6) (-F.N 2) ?_ hrange
  intro B b c' d hb hbc hcd hd hB hC
  have hcomb' : (c (B + b) ≠ 2 ∧ c (B + b) ≠ 6 ∧ c (B + b) ≠ 5 ∧
        (c (B + b) = 3 → c B = 5 ∨ c (B + c') = 5) ∧
        (c (B + b) = 0 ∨ c (B + b) = 4 → c B = 3 ∨ c B = 5 ∨ c (B + c') = 3 ∨ c (B + c') = 5)) ∨
      (c (B + d) ≠ 2 ∧ c (B + d) ≠ 6 ∧ c (B + d) ≠ 5 ∧
        (c (B + d) = 3 → c B = 5 ∨ c (B + c') = 5) ∧
        (c (B + d) = 0 ∨ c (B + d) = 4 → c B = 3 ∨ c B = 5 ∨ c (B + c') = 3 ∨ c (B + c') = 5)) := by
    simp only [checkArcR2, List.all_eq_true, List.mem_finRange, forall_true_left] at hcomb
    have hspec := hcomb ⟨B.val, ZMod.val_lt B⟩ ⟨b, by omega⟩ ⟨c', by omega⟩ ⟨d, hd⟩
    have hcond : (0 < b && b < c' && c' < d && c B != 2 && c B != 6 &&
        c (B + c') != 2 && c (B + c') != 6) = true := by
      simp [hb, hbc, hcd, hB.1, hB.2, hC.1, hC.2]
    simp only [ZMod.natCast_zmod_val] at hspec
    simp only [hcond, ↓reduceIte] at hspec
    simpa [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
      beq_iff_eq, bne_iff_ne, imp_iff_not_or, and_assoc, or_assoc] using hspec
  rcases hcomb' with
    ⟨hb1, hb2, hb5, hb3, hb04⟩ | ⟨hd1, hd2, hd5, hd3, hd04⟩
  · left; exact ⟨hb1, hb2, hcmp B (B + b) (B + c') hB ⟨hb1, hb2⟩ hC hb5 hb3 hb04⟩
  · right; exact ⟨hd1, hd2, hcmp B (B + d) (B + c') hB ⟨hd1, hd2⟩ hC hd5 hd3 hd04⟩

private def checkArcR3 {k : ℕ} [NeZero k] (c : ZMod k → Fin 7) : Bool :=
  (List.finRange k).all fun B =>
    (List.finRange k).all fun b =>
      (List.finRange k).all fun c' =>
        (List.finRange k).all fun d =>
          let Bz : ZMod k := (B.val : ZMod k)
          if 0 < b.val && b.val < c'.val && c'.val < d.val &&
              c Bz != 2 && c Bz != 6 && c (Bz + c'.val) != 2 && c (Bz + c'.val) != 6 then
            (c (Bz + b.val) != 2 && c (Bz + b.val) != 6 && c (Bz + b.val) != 4 &&
              (!(c (Bz + b.val) == 3) || (c Bz == 4 || c (Bz + c'.val) == 4)) &&
              (!(c (Bz + b.val) == 0 || c (Bz + b.val) == 5) ||
                (c Bz == 3 || c Bz == 4 || c (Bz + c'.val) == 3 || c (Bz + c'.val) == 4))) ||
            (c (Bz + d.val) != 2 && c (Bz + d.val) != 6 && c (Bz + d.val) != 4 &&
              (!(c (Bz + d.val) == 3) || (c Bz == 4 || c (Bz + c'.val) == 4)) &&
              (!(c (Bz + d.val) == 0 || c (Bz + d.val) == 5) ||
                (c Bz == 3 || c Bz == 4 || c (Bz + c'.val) == 3 || c (Bz + c'.val) == 4)))
          else true

private theorem robUniLex_r3 {k : ℕ} [NeZero k] {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (c : ZMod k → Fin 7) (hc : Function.Injective c)
    (hrange : ∀ i : ZMod k, c i ∈ ({0, 2, 3, 4, 5, 6} : Finset (Fin 7)))
    (hcomb : checkArcR3 c = true) :
    RobUniLex (fun i => (⟪x (c i), F.N 3⟫, ⟪x (c i), -F.N 8⟫, ⟪x (c i), -F.N 4⟫)) := by
  have hZmax : ∀ v : Fin 7, v ∈ ({0, 3, 4, 5} : Finset (Fin 7)) →
      ⟪x v, F.N 3⟫ = ⟪x 0, F.N 3⟫ := fun v hv => by
    rw [← sub_eq_zero, ← inner_sub_left, real_inner_comm, F.inner_sub,
      F.zero 3 0 (by decide), F.zero 3 v (by simpa [s0x_S24] using hv), sub_zero]
  have h34_8 : ⟪x 4, -F.N 8⟫ = ⟪x 3, -F.N 8⟫ := by
    rw [← sub_eq_zero, ← inner_sub_left, real_inner_comm, inner_neg_left, F.inner_sub,
      F.zero 8 4 (by decide), F.zero 8 3 (by decide), sub_self, neg_zero]
  have h40_8 : ⟪x 4, -F.N 8⟫ < ⟪x 0, -F.N 8⟫ := by
    rw [← sub_pos, ← inner_sub_left, real_inner_comm, inner_neg_left, F.inner_sub,
      F.zero 8 4 (by decide), sub_zero]; exact neg_pos.2 (F.neg 8 0 (by decide))
  have h45_8 : ⟪x 4, -F.N 8⟫ < ⟪x 5, -F.N 8⟫ := by
    rw [← sub_pos, ← inner_sub_left, real_inner_comm, inner_neg_left, F.inner_sub,
      F.zero 8 4 (by decide), sub_zero]; exact neg_pos.2 (F.neg 8 5 (by decide))
  have h30_8 : ⟪x 3, -F.N 8⟫ < ⟪x 0, -F.N 8⟫ := by rwa [← h34_8]
  have h35_8 : ⟪x 3, -F.N 8⟫ < ⟪x 5, -F.N 8⟫ := by rwa [← h34_8]
  have h43_4 : ⟪x 4, -F.N 4⟫ < ⟪x 3, -F.N 4⟫ := by
    rw [← sub_pos, ← inner_sub_left, real_inner_comm, inner_neg_left, F.inner_sub,
      F.zero 4 4 (by decide), sub_zero]; exact neg_pos.2 (F.neg 4 3 (by decide))
  have hcmp : ∀ p q r : ZMod k, (c p ≠ 2 ∧ c p ≠ 6) → (c q ≠ 2 ∧ c q ≠ 6) →
      (c r ≠ 2 ∧ c r ≠ 6) → c q ≠ 4 →
      (c q = 3 → c p = 4 ∨ c r = 4) →
      (c q = 0 ∨ c q = 5 → c p = 3 ∨ c p = 4 ∨ c r = 3 ∨ c r = 4) →
      LexLt3 (⟪x (c p), F.N 3⟫, ⟪x (c p), -F.N 8⟫, ⟪x (c p), -F.N 4⟫)
          (⟪x (c q), F.N 3⟫, ⟪x (c q), -F.N 8⟫, ⟪x (c q), -F.N 4⟫) ∨
        LexLt3 (⟪x (c r), F.N 3⟫, ⟪x (c r), -F.N 8⟫, ⟪x (c r), -F.N 4⟫)
          (⟪x (c q), F.N 3⟫, ⟪x (c q), -F.N 8⟫, ⟪x (c q), -F.N 4⟫) := by
    intro p q r hp hq hr hq4 hq3 hq05
    have mem4 : ∀ {i}, c i ≠ 2 ∧ c i ≠ 6 → c i = 0 ∨ c i = 3 ∨ c i = 4 ∨ c i = 5 := by
      intro i hi; have := hrange i; simp only [mem_insert, mem_singleton] at this; tauto
    have hZeq : ∀ {u v}, (c u ≠ 2 ∧ c u ≠ 6) → (c v ≠ 2 ∧ c v ≠ 6) →
        ⟪x (c u), F.N 3⟫ = ⟪x (c v), F.N 3⟫ := by
      intro u v hu hv
      have h1 : c u ∈ ({0, 3, 4, 5} : Finset (Fin 7)) := by rcases mem4 hu with h | h | h | h <;> simp [h]
      have h2 : c v ∈ ({0, 3, 4, 5} : Finset (Fin 7)) := by rcases mem4 hv with h | h | h | h <;> simp [h]
      rw [hZmax _ h1, hZmax _ h2]
    rcases mem4 hq with hq' | hq' | hq' | hq'
    · rcases hq05 (Or.inl hq') with hp3 | hp4 | hr3 | hr4
      · left; exact lexLt3_of_snd (hZeq hp hq) (by rw [hp3, hq']; exact h30_8)
      · left; exact lexLt3_of_snd (hZeq hp hq) (by rw [hp4, hq']; exact h40_8)
      · right; exact lexLt3_of_snd (hZeq hr hq) (by rw [hr3, hq']; exact h30_8)
      · right; exact lexLt3_of_snd (hZeq hr hq) (by rw [hr4, hq']; exact h40_8)
    · rcases hq3 hq' with hp4 | hr4
      · left; exact lexLt3_of_thd (hZeq hp hq) (by rw [hp4, hq']; exact h34_8) (by rw [hp4, hq']; exact h43_4)
      · right; exact lexLt3_of_thd (hZeq hr hq) (by rw [hr4, hq']; exact h34_8) (by rw [hr4, hq']; exact h43_4)
    · exact absurd hq' hq4
    · rcases hq05 (Or.inr hq') with hp3 | hp4 | hr3 | hr4
      · left; exact lexLt3_of_snd (hZeq hp hq) (by rw [hp3, hq']; exact h35_8)
      · left; exact lexLt3_of_snd (hZeq hp hq) (by rw [hp4, hq']; exact h45_8)
      · right; exact lexLt3_of_snd (hZeq hr hq) (by rw [hr3, hq']; exact h35_8)
      · right; exact lexLt3_of_snd (hZeq hr hq) (by rw [hr4, hq']; exact h45_8)
  refine robUniLex_of_arc F c hc (-F.N 8) (-F.N 4) ?_ hrange
  intro B b c' d hb hbc hcd hd hB hC
  have hcomb' : (c (B + b) ≠ 2 ∧ c (B + b) ≠ 6 ∧ c (B + b) ≠ 4 ∧
        (c (B + b) = 3 → c B = 4 ∨ c (B + c') = 4) ∧
        (c (B + b) = 0 ∨ c (B + b) = 5 → c B = 3 ∨ c B = 4 ∨ c (B + c') = 3 ∨ c (B + c') = 4)) ∨
      (c (B + d) ≠ 2 ∧ c (B + d) ≠ 6 ∧ c (B + d) ≠ 4 ∧
        (c (B + d) = 3 → c B = 4 ∨ c (B + c') = 4) ∧
        (c (B + d) = 0 ∨ c (B + d) = 5 → c B = 3 ∨ c B = 4 ∨ c (B + c') = 3 ∨ c (B + c') = 4)) := by
    simp only [checkArcR3, List.all_eq_true, List.mem_finRange, forall_true_left] at hcomb
    have hspec := hcomb ⟨B.val, ZMod.val_lt B⟩ ⟨b, by omega⟩ ⟨c', by omega⟩ ⟨d, hd⟩
    have hcond : (0 < b && b < c' && c' < d && c B != 2 && c B != 6 &&
        c (B + c') != 2 && c (B + c') != 6) = true := by
      simp [hb, hbc, hcd, hB.1, hB.2, hC.1, hC.2]
    simp only [ZMod.natCast_zmod_val] at hspec
    simp only [hcond, ↓reduceIte] at hspec
    simpa [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
      beq_iff_eq, bne_iff_ne, imp_iff_not_or, and_assoc, or_assoc] using hspec
  rcases hcomb' with
    ⟨hb1, hb2, hb4, hb3, hb05⟩ | ⟨hd1, hd2, hd4, hd3, hd05⟩
  · left; exact ⟨hb1, hb2, hcmp B (B + b) (B + c') hB ⟨hb1, hb2⟩ hC hb4 hb3 hb05⟩
  · right; exact ⟨hd1, hd2, hcmp B (B + d) (B + c') hB ⟨hd1, hd2⟩ hC hd4 hd3 hd05⟩

private theorem u_comb_aux (c2 c4 c6 c7 c8 : Bool)
    (hv3 : c7 = true → c6 = true ∨ c8 = true)
    (hv2 : c7 = true → c2 = true → c6 = true)
    (hv6 : c7 = true → c4 = true → c8 = true)
    (hcbar : ¬ (c2 = true ∧ c4 = true ∧ c7 = true))
    (hnotTE : c7 ≠ true → (c2 ≠ true ∧ c6 ≠ true) ∨ (c4 ≠ true ∧ c8 ≠ true)) :
    (c2, c4, c6, c7, c8) = (false, false, false, false, false) ∨
    (c2, c4, c6, c7, c8) = (true, false, false, false, false) ∨
    (c2, c4, c6, c7, c8) = (false, false, true, false, false) ∨
    (c2, c4, c6, c7, c8) = (true, false, true, false, false) ∨
    (c2, c4, c6, c7, c8) = (false, true, false, false, false) ∨
    (c2, c4, c6, c7, c8) = (false, false, false, false, true) ∨
    (c2, c4, c6, c7, c8) = (false, true, false, false, true) ∨
    (c2, c4, c6, c7, c8) = (false, false, false, true, true) ∨
    (c2, c4, c6, c7, c8) = (false, true, false, true, true) ∨
    (c2, c4, c6, c7, c8) = (false, false, true, true, false) ∨
    (c2, c4, c6, c7, c8) = (true, false, true, true, false) ∨
    (c2, c4, c6, c7, c8) = (false, false, true, true, true) ∨
    (c2, c4, c6, c7, c8) = (false, true, true, true, true) ∨
    (c2, c4, c6, c7, c8) = (true, false, true, true, true) := by
  cases c2 <;> cases c4 <;> cases c6 <;> cases c7 <;> cases c8 <;> simp_all

private theorem u_subset_cases (U : Finset (Fin 9))
    (h3 : (3 : Fin 9) ∈ U) (h0 : (0 : Fin 9) ∉ U) (h1 : (1 : Fin 9) ∉ U) (h5 : (5 : Fin 9) ∉ U)
    (hv3 : (7 : Fin 9) ∈ U → (6 : Fin 9) ∈ U ∨ (8 : Fin 9) ∈ U)
    (hv2 : (7 : Fin 9) ∈ U → (2 : Fin 9) ∈ U → (6 : Fin 9) ∈ U)
    (hv6 : (7 : Fin 9) ∈ U → (4 : Fin 9) ∈ U → (8 : Fin 9) ∈ U)
    (hcbar : ¬ ((2 : Fin 9) ∈ U ∧ (4 : Fin 9) ∈ U ∧ (7 : Fin 9) ∈ U))
    (hnotTE : (7 : Fin 9) ∉ U → ((2 : Fin 9) ∉ U ∧ (6 : Fin 9) ∉ U) ∨ ((4 : Fin 9) ∉ U ∧ (8 : Fin 9) ∉ U)) :
    U = {3} ∨ U = {3, 2} ∨ U = {3, 6} ∨ U = {3, 2, 6} ∨
    U = {3, 4} ∨ U = {3, 8} ∨ U = {3, 4, 8} ∨
    U = {3, 7, 8} ∨ U = {3, 4, 7, 8} ∨ U = {3, 6, 7} ∨ U = {3, 2, 6, 7} ∨
    U = {3, 6, 7, 8} ∨ U = {3, 4, 6, 7, 8} ∨ U = {3, 2, 6, 7, 8} := by
  classical
  let b2 : Bool := decide ((2 : Fin 9) ∈ U)
  let b4 : Bool := decide ((4 : Fin 9) ∈ U)
  let b6 : Bool := decide ((6 : Fin 9) ∈ U)
  let b7 : Bool := decide ((7 : Fin 9) ∈ U)
  let b8 : Bool := decide ((8 : Fin 9) ∈ U)
  let S : Bool → Bool → Bool → Bool → Bool → Finset (Fin 9) := fun c2 c4 c6 c7 c8 =>
    {3} ∪ (if c2 = true then {2} else ∅) ∪ (if c4 = true then {4} else ∅) ∪
      (if c6 = true then {6} else ∅) ∪ (if c7 = true then {7} else ∅) ∪ (if c8 = true then {8} else ∅)
  have mem_ite : ∀ (p : Prop) [Decidable p] (a t : Fin 9),
      t ∈ (if p then ({a} : Finset (Fin 9)) else ∅) ↔ (p ∧ t = a) := by
    intro p _ a t; split_ifs with hp <;> simp [hp, eq_comm]
  have hUS : U = S b2 b4 b6 b7 b8 := by
    ext t
    fin_cases t <;> simp [S, mem_ite, h0, h1, h3, h5, b2, b4, b6, b7, b8]
  have hcomb := u_comb_aux b2 b4 b6 b7 b8
    (by simpa [b7, b6, b8] using hv3)
    (by simpa [b7, b2, b6] using hv2)
    (by simpa [b7, b4, b8] using hv6)
    (by simpa [b2, b4, b7] using hcbar)
    (by simpa [b7, b2, b6, b4, b8] using hnotTE)
  have mk : ∀ c2 c4 c6 c7 c8 : Bool, (b2, b4, b6, b7, b8) = (c2, c4, c6, c7, c8) →
      ∀ V : Finset (Fin 9), (∀ t : Fin 9, (t = 3 ∨ (c2 = true ∧ t = 2) ∨ (c4 = true ∧ t = 4) ∨
        (c6 = true ∧ t = 6) ∨ (c7 = true ∧ t = 7) ∨ (c8 = true ∧ t = 8)) ↔ t ∈ V) → U = V := by
    rintro c2 c4 c6 c7 c8 h V hV
    rw [hUS]
    have e2 : b2 = c2 := by simpa using congrArg Prod.fst h
    have e4 : b4 = c4 := by simpa using congrArg (fun p => p.2.1) h
    have e6 : b6 = c6 := by simpa using congrArg (fun p => p.2.2.1) h
    have e7 : b7 = c7 := by simpa using congrArg (fun p => p.2.2.2.1) h
    have e8 : b8 = c8 := by simpa using congrArg (fun p => p.2.2.2.2) h
    rw [e2, e4, e6, e7, e8]
    ext t; rw [← hV t]; simp [S, mem_ite]
  rcases hcomb with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact Or.inl (mk _ _ _ _ _ h _ (fun t => by fin_cases t <;> decide))
  · exact Or.inr (Or.inl (mk _ _ _ _ _ h _ (fun t => by fin_cases t <;> decide)))
  · exact Or.inr (Or.inr (Or.inl (mk _ _ _ _ _ h _ (fun t => by fin_cases t <;> decide))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (mk _ _ _ _ _ h _ (fun t => by fin_cases t <;> decide)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (mk _ _ _ _ _ h _ (fun t => by fin_cases t <;> decide))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (mk _ _ _ _ _ h _ (fun t => by fin_cases t <;> decide)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (mk _ _ _ _ _ h _ (fun t => by fin_cases t <;> decide))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (mk _ _ _ _ _ h _ (fun t => by fin_cases t <;> decide)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (mk _ _ _ _ _ h _ (fun t => by fin_cases t <;> decide))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (mk _ _ _ _ _ h _ (fun t => by fin_cases t <;> decide)))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (mk _ _ _ _ _ h _ (fun t => by fin_cases t <;> decide))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (mk _ _ _ _ _ h _ (fun t => by fin_cases t <;> decide)))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (mk _ _ _ _ _ h _ (fun t => by fin_cases t <;> decide))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (mk _ _ _ _ _ h _ (fun t => by fin_cases t <;> decide))))))))))))))

private abbrev cR0 : ZMod 4 → Fin 7 := ![0, 4, 3, 5]
private abbrev cB1 : ZMod 5 → Fin 7 := ![0, 4, 3, 5, 2]
private abbrev cB2 : ZMod 5 → Fin 7 := ![0, 4, 3, 2, 5]
private abbrev cB3 : ZMod 4 → Fin 7 := ![0, 4, 3, 2]
private abbrev cC1 : ZMod 5 → Fin 7 := ![0, 6, 4, 3, 5]
private abbrev cC2 : ZMod 5 → Fin 7 := ![0, 4, 6, 3, 5]
private abbrev cC3 : ZMod 4 → Fin 7 := ![0, 6, 3, 5]
private abbrev cA1 : ZMod 6 → Fin 7 := ![0, 4, 6, 2, 3, 5]
private abbrev cA2 : ZMod 5 → Fin 7 := ![0, 6, 2, 3, 5]
private abbrev cA3 : ZMod 6 → Fin 7 := ![0, 4, 3, 6, 2, 5]
private abbrev cA4 : ZMod 5 → Fin 7 := ![0, 4, 3, 6, 2]
private abbrev cA5 : ZMod 5 → Fin 7 := ![0, 4, 6, 2, 5]
private abbrev cA6 : ZMod 4 → Fin 7 := ![0, 6, 2, 5]
private abbrev cA7 : ZMod 4 → Fin 7 := ![0, 4, 6, 2]

private theorem inj_R0 : Function.Injective cR0 := by decide
private theorem inj_B1 : Function.Injective cB1 := by decide
private theorem inj_B2 : Function.Injective cB2 := by decide
private theorem inj_B3 : Function.Injective cB3 := by decide
private theorem inj_C1 : Function.Injective cC1 := by decide
private theorem inj_C2 : Function.Injective cC2 := by decide
private theorem inj_C3 : Function.Injective cC3 := by decide
private theorem inj_A1 : Function.Injective cA1 := by decide
private theorem inj_A2 : Function.Injective cA2 := by decide
private theorem inj_A3 : Function.Injective cA3 := by decide
private theorem inj_A4 : Function.Injective cA4 := by decide
private theorem inj_A5 : Function.Injective cA5 := by decide
private theorem inj_A6 : Function.Injective cA6 := by decide
private theorem inj_A7 : Function.Injective cA7 := by decide

private theorem cyc_R0 : S0xCycUD s0x_S24 cR0 {3} (univ \ {3}) := by decide
private theorem cyc_B1 : S0xCycUD s0x_S24 cB1 {3, 2} (univ \ {3, 2}) := by decide
private theorem cyc_B2 : S0xCycUD s0x_S24 cB2 {3, 6} (univ \ {3, 6}) := by decide
private theorem cyc_B3 : S0xCycUD s0x_S24 cB3 {3, 2, 6} (univ \ {3, 2, 6}) := by decide
private theorem cyc_C1 : S0xCycUD s0x_S24 cC1 {3, 4} (univ \ {3, 4}) := by decide
private theorem cyc_C2 : S0xCycUD s0x_S24 cC2 {3, 8} (univ \ {3, 8}) := by decide
private theorem cyc_C3 : S0xCycUD s0x_S24 cC3 {3, 4, 8} (univ \ {3, 4, 8}) := by decide
private theorem cyc_A1 : S0xCycUD s0x_S24 cA1 {3, 7, 8} (univ \ {3, 7, 8}) := by decide
private theorem cyc_A2 : S0xCycUD s0x_S24 cA2 {3, 4, 7, 8} (univ \ {3, 4, 7, 8}) := by decide
private theorem cyc_A3 : S0xCycUD s0x_S24 cA3 {3, 6, 7} (univ \ {3, 6, 7}) := by decide
private theorem cyc_A4 : S0xCycUD s0x_S24 cA4 {3, 2, 6, 7} (univ \ {3, 2, 6, 7}) := by decide
private theorem cyc_A5 : S0xCycUD s0x_S24 cA5 {3, 6, 7, 8} (univ \ {3, 6, 7, 8}) := by decide
private theorem cyc_A6 : S0xCycUD s0x_S24 cA6 {3, 4, 6, 7, 8} (univ \ {3, 4, 6, 7, 8}) := by decide
private theorem cyc_A7 : S0xCycUD s0x_S24 cA7 {3, 2, 6, 7, 8} (univ \ {3, 2, 6, 7, 8}) := by decide

private theorem rng_B1 : ∀ i, cB1 i ∈ ({0, 2, 3, 4, 5, 6} : Finset (Fin 7)) := by decide
private theorem rng_B2 : ∀ i, cB2 i ∈ ({0, 2, 3, 4, 5, 6} : Finset (Fin 7)) := by decide
private theorem rng_B3 : ∀ i, cB3 i ∈ ({0, 2, 3, 4, 5, 6} : Finset (Fin 7)) := by decide
private theorem rng_C1 : ∀ i, cC1 i ∈ ({0, 2, 3, 4, 5, 6} : Finset (Fin 7)) := by decide
private theorem rng_C2 : ∀ i, cC2 i ∈ ({0, 2, 3, 4, 5, 6} : Finset (Fin 7)) := by decide
private theorem rng_C3 : ∀ i, cC3 i ∈ ({0, 2, 3, 4, 5, 6} : Finset (Fin 7)) := by decide
private theorem rng_A1 : ∀ i, cA1 i ∈ ({0, 2, 3, 4, 5, 6} : Finset (Fin 7)) := by decide
private theorem rng_A2 : ∀ i, cA2 i ∈ ({0, 2, 3, 4, 5, 6} : Finset (Fin 7)) := by decide
private theorem rng_A3 : ∀ i, cA3 i ∈ ({0, 2, 3, 4, 5, 6} : Finset (Fin 7)) := by decide
private theorem rng_A4 : ∀ i, cA4 i ∈ ({0, 2, 3, 4, 5, 6} : Finset (Fin 7)) := by decide
private theorem rng_A5 : ∀ i, cA5 i ∈ ({0, 2, 3, 4, 5, 6} : Finset (Fin 7)) := by decide
private theorem rng_A6 : ∀ i, cA6 i ∈ ({0, 2, 3, 4, 5, 6} : Finset (Fin 7)) := by decide
private theorem rng_A7 : ∀ i, cA7 i ∈ ({0, 2, 3, 4, 5, 6} : Finset (Fin 7)) := by decide

private theorem r1_B1 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    RobUniLex (fun i => (⟪x (cB1 i), F.N 3⟫, ⟪x (cB1 i), -F.N 1⟫, ⟪x (cB1 i), -F.N 0⟫)) :=
  robUniLex_r1 F cB1 inj_B1 rng_B1 (by decide)
private theorem r1_B3 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    RobUniLex (fun i => (⟪x (cB3 i), F.N 3⟫, ⟪x (cB3 i), -F.N 1⟫, ⟪x (cB3 i), -F.N 0⟫)) :=
  robUniLex_r1 F cB3 inj_B3 rng_B3 (by decide)
private theorem r1_C1 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    RobUniLex (fun i => (⟪x (cC1 i), F.N 3⟫, ⟪x (cC1 i), -F.N 1⟫, ⟪x (cC1 i), -F.N 0⟫)) :=
  robUniLex_r1 F cC1 inj_C1 rng_C1 (by decide)
private theorem r1_C3 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    RobUniLex (fun i => (⟪x (cC3 i), F.N 3⟫, ⟪x (cC3 i), -F.N 1⟫, ⟪x (cC3 i), -F.N 0⟫)) :=
  robUniLex_r1 F cC3 inj_C3 rng_C3 (by decide)
private theorem r1_A2 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    RobUniLex (fun i => (⟪x (cA2 i), F.N 3⟫, ⟪x (cA2 i), -F.N 1⟫, ⟪x (cA2 i), -F.N 0⟫)) :=
  robUniLex_r1 F cA2 inj_A2 rng_A2 (by decide)
private theorem r1_A4 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    RobUniLex (fun i => (⟪x (cA4 i), F.N 3⟫, ⟪x (cA4 i), -F.N 1⟫, ⟪x (cA4 i), -F.N 0⟫)) :=
  robUniLex_r1 F cA4 inj_A4 rng_A4 (by decide)
private theorem r1_A6 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    RobUniLex (fun i => (⟪x (cA6 i), F.N 3⟫, ⟪x (cA6 i), -F.N 1⟫, ⟪x (cA6 i), -F.N 0⟫)) :=
  robUniLex_r1 F cA6 inj_A6 rng_A6 (by decide)
private theorem r1_A7 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    RobUniLex (fun i => (⟪x (cA7 i), F.N 3⟫, ⟪x (cA7 i), -F.N 1⟫, ⟪x (cA7 i), -F.N 0⟫)) :=
  robUniLex_r1 F cA7 inj_A7 rng_A7 (by decide)

private theorem r2_B1 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    RobUniLex (fun i => (⟪x (cB1 i), F.N 3⟫, ⟪x (cB1 i), -F.N 6⟫, ⟪x (cB1 i), -F.N 2⟫)) :=
  robUniLex_r2 F cB1 inj_B1 rng_B1 (by decide)
private theorem r2_B2 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    RobUniLex (fun i => (⟪x (cB2 i), F.N 3⟫, ⟪x (cB2 i), -F.N 6⟫, ⟪x (cB2 i), -F.N 2⟫)) :=
  robUniLex_r2 F cB2 inj_B2 rng_B2 (by decide)
private theorem r2_B3 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    RobUniLex (fun i => (⟪x (cB3 i), F.N 3⟫, ⟪x (cB3 i), -F.N 6⟫, ⟪x (cB3 i), -F.N 2⟫)) :=
  robUniLex_r2 F cB3 inj_B3 rng_B3 (by decide)
private theorem r2_A3 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    RobUniLex (fun i => (⟪x (cA3 i), F.N 3⟫, ⟪x (cA3 i), -F.N 6⟫, ⟪x (cA3 i), -F.N 2⟫)) :=
  robUniLex_r2 F cA3 inj_A3 rng_A3 (by decide)
private theorem r2_A4 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    RobUniLex (fun i => (⟪x (cA4 i), F.N 3⟫, ⟪x (cA4 i), -F.N 6⟫, ⟪x (cA4 i), -F.N 2⟫)) :=
  robUniLex_r2 F cA4 inj_A4 rng_A4 (by decide)
private theorem r2_A5 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    RobUniLex (fun i => (⟪x (cA5 i), F.N 3⟫, ⟪x (cA5 i), -F.N 6⟫, ⟪x (cA5 i), -F.N 2⟫)) :=
  robUniLex_r2 F cA5 inj_A5 rng_A5 (by decide)
private theorem r2_A6 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    RobUniLex (fun i => (⟪x (cA6 i), F.N 3⟫, ⟪x (cA6 i), -F.N 6⟫, ⟪x (cA6 i), -F.N 2⟫)) :=
  robUniLex_r2 F cA6 inj_A6 rng_A6 (by decide)
private theorem r2_A7 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    RobUniLex (fun i => (⟪x (cA7 i), F.N 3⟫, ⟪x (cA7 i), -F.N 6⟫, ⟪x (cA7 i), -F.N 2⟫)) :=
  robUniLex_r2 F cA7 inj_A7 rng_A7 (by decide)

private theorem r3_C1 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    RobUniLex (fun i => (⟪x (cC1 i), F.N 3⟫, ⟪x (cC1 i), -F.N 8⟫, ⟪x (cC1 i), -F.N 4⟫)) :=
  robUniLex_r3 F cC1 inj_C1 rng_C1 (by decide)
private theorem r3_C2 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    RobUniLex (fun i => (⟪x (cC2 i), F.N 3⟫, ⟪x (cC2 i), -F.N 8⟫, ⟪x (cC2 i), -F.N 4⟫)) :=
  robUniLex_r3 F cC2 inj_C2 rng_C2 (by decide)
private theorem r3_C3 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    RobUniLex (fun i => (⟪x (cC3 i), F.N 3⟫, ⟪x (cC3 i), -F.N 8⟫, ⟪x (cC3 i), -F.N 4⟫)) :=
  robUniLex_r3 F cC3 inj_C3 rng_C3 (by decide)
private theorem r3_A1 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    RobUniLex (fun i => (⟪x (cA1 i), F.N 3⟫, ⟪x (cA1 i), -F.N 8⟫, ⟪x (cA1 i), -F.N 4⟫)) :=
  robUniLex_r3 F cA1 inj_A1 rng_A1 (by decide)
private theorem r3_A2 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    RobUniLex (fun i => (⟪x (cA2 i), F.N 3⟫, ⟪x (cA2 i), -F.N 8⟫, ⟪x (cA2 i), -F.N 4⟫)) :=
  robUniLex_r3 F cA2 inj_A2 rng_A2 (by decide)
private theorem r3_A5 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    RobUniLex (fun i => (⟪x (cA5 i), F.N 3⟫, ⟪x (cA5 i), -F.N 8⟫, ⟪x (cA5 i), -F.N 4⟫)) :=
  robUniLex_r3 F cA5 inj_A5 rng_A5 (by decide)
private theorem r3_A6 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    RobUniLex (fun i => (⟪x (cA6 i), F.N 3⟫, ⟪x (cA6 i), -F.N 8⟫, ⟪x (cA6 i), -F.N 4⟫)) :=
  robUniLex_r3 F cA6 inj_A6 rng_A6 (by decide)
private theorem r3_A7 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    RobUniLex (fun i => (⟪x (cA7 i), F.N 3⟫, ⟪x (cA7 i), -F.N 8⟫, ⟪x (cA7 i), -F.N 4⟫)) :=
  robUniLex_r3 F cA7 inj_A7 rng_A7 (by decide)

end RimClosure

theorem lexAny_quadNormal {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hcb : Minimality.T24.CbarIn x)
    (hob : ⟪x 0 - x 1, x 2 - x 1⟫ ≤ 0 ∧ ⟪x 0 - x 1, x 6 - x 1⟫ ≤ 0 ∧ ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0)
    (hnB : F.f 3 (x 1) ≤ F.f 3 (x 2)) (hnC : F.f 3 (x 1) ≤ F.f 3 (x 6))
    (hTE : ¬ TwoEar F) :
    Minimality.T24.RCell.LexAny F := by
  obtain ⟨h01, h05, h15⟩ := ob1_cap_inner F hob
  obtain ⟨h53, h13, h03, h20_lt, h41_lt⟩ := quad_dot_cap_nonpos F hob hnB hnC
  have hcommon : ∀ (d1 d2 : ℝ³)
      (hindep : ∀ t : Fin 9, ¬ (⟪F.N t, F.N 3⟫ = 0 ∧ ⟪F.N t, d1⟫ = 0 ∧ ⟪F.N t, d2⟫ = 0))
      (h0_dn : ¬ LexPos3 ⟪F.N 0, F.N 3⟫ ⟪F.N 0, d1⟫ ⟪F.N 0, d2⟫)
      (h1_dn : ¬ LexPos3 ⟪F.N 1, F.N 3⟫ ⟪F.N 1, d1⟫ ⟪F.N 1, d2⟫),
      ∃ U : Finset (Fin 9),
        (∀ t : Fin 9, t ∈ U ↔ LexPos3 ⟪F.N t, F.N 3⟫ ⟪F.N t, d1⟫ ⟪F.N t, d2⟫) ∧
        (∀ t ∈ U, LexPos3 ⟪F.N t, F.N 3⟫ ⟪F.N t, d1⟫ ⟪F.N t, d2⟫) ∧
        (∀ t ∈ Finset.univ \ U, LexPos3 (-⟪F.N t, F.N 3⟫) (-⟪F.N t, d1⟫) (-⟪F.N t, d2⟫)) ∧
        (U = {3} ∨ U = {3, 2} ∨ U = {3, 6} ∨ U = {3, 2, 6} ∨
         U = {3, 4} ∨ U = {3, 8} ∨ U = {3, 4, 8} ∨
         U = {3, 7, 8} ∨ U = {3, 4, 7, 8} ∨ U = {3, 6, 7} ∨ U = {3, 2, 6, 7} ∨
         U = {3, 6, 7, 8} ∨ U = {3, 4, 6, 7, 8} ∨ U = {3, 2, 6, 7, 8}) := by
    intro d1 d2 hindep h0_dn h1_dn
    classical
    let U := Finset.univ.filter (fun t : Fin 9 => LexPos3 ⟪F.N t, F.N 3⟫ ⟪F.N t, d1⟫ ⟪F.N t, d2⟫)
    have hmem : ∀ t : Fin 9, t ∈ U ↔ LexPos3 ⟪F.N t, F.N 3⟫ ⟪F.N t, d1⟫ ⟪F.N t, d2⟫ := fun t => by
      simp [U]
    have hU : ∀ t ∈ U, LexPos3 ⟪F.N t, F.N 3⟫ ⟪F.N t, d1⟫ ⟪F.N t, d2⟫ := fun t ht =>
      (hmem t).1 ht
    have hDn : ∀ t ∈ Finset.univ \ U,
        LexPos3 (-⟪F.N t, F.N 3⟫) (-⟪F.N t, d1⟫) (-⟪F.N t, d2⟫) := by
      intro t ht
      have hnt : ¬ LexPos3 ⟪F.N t, F.N 3⟫ ⟪F.N t, d1⟫ ⟪F.N t, d2⟫ := by
        simpa [U] using (Finset.mem_sdiff.1 ht).2
      exact (lexPos3_pos_or_neg (hindep t)).resolve_left hnt
    have h3 : (3 : Fin 9) ∈ U := (hmem 3).2 (Or.inl (inner_pos_self F 3))
    have h0 : (0 : Fin 9) ∉ U := fun h => h0_dn (hU 0 h)
    have h1 : (1 : Fin 9) ∉ U := fun h => h1_dn (hU 1 h)
    have h5 : (5 : Fin 9) ∉ U := fun h =>
      lexPos3_neg_not_pos (Or.inl (neg_pos.2 h53)) (hU 5 h)
    have hv3 : (7 : Fin 9) ∈ U → (6 : Fin 9) ∈ U ∨ (8 : Fin 9) ∈ U := by
      intro h7
      by_contra h68; push Not at h68
      obtain ⟨a, b, c, d, ha, hb, hc, hd, heq⟩ := syzygy_v3 F
      have hL : LexPos3 ⟪a • F.N 3 + b • F.N 7, F.N 3⟫ ⟪a • F.N 3 + b • F.N 7, d1⟫
          ⟪a • F.N 3 + b • F.N 7, d2⟫ := by
        simp only [inner_add_left, real_inner_smul_left]
        exact lexPos3_add (lexPos3_smul ha (hU 3 h3)) (lexPos3_smul hb (hU 7 h7))
      have hR : LexPos3 (-(⟪c • F.N 6 + d • F.N 8, F.N 3⟫)) (-(⟪c • F.N 6 + d • F.N 8, d1⟫))
          (-(⟪c • F.N 6 + d • F.N 8, d2⟫)) := by
        simp only [inner_add_left, real_inner_smul_left, neg_add]
        have h6' := hDn 6 (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, h68.1⟩)
        have h8' := hDn 8 (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, h68.2⟩)
        simpa [mul_neg] using lexPos3_add (lexPos3_smul hc h6') (lexPos3_smul hd h8')
      rw [heq] at hL
      exact lexPos3_neg_not_pos hR hL
    have hv2 : (7 : Fin 9) ∈ U → (2 : Fin 9) ∈ U → (6 : Fin 9) ∈ U := by
      intro h7 h2
      by_contra h6n
      obtain ⟨a, b, c, d, ha, hb, hc, hd, heq⟩ := syzygy_v2 F
      have h5' := hDn 5 (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, h5⟩)
      have h6' := hDn 6 (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, h6n⟩)
      have hL : LexPos3 ⟪a • (-F.N 5) + b • F.N 7 + c • F.N 2, F.N 3⟫
          ⟪a • (-F.N 5) + b • F.N 7 + c • F.N 2, d1⟫
          ⟪a • (-F.N 5) + b • F.N 7 + c • F.N 2, d2⟫ := by
        simp only [inner_add_left, real_inner_smul_left, inner_neg_left]
        exact lexPos3_add (lexPos3_add (lexPos3_smul ha h5') (lexPos3_smul hb (hU 7 h7)))
          (lexPos3_smul hc (hU 2 h2))
      rw [heq] at hL
      simp only [real_inner_smul_left] at hL
      exact lexPos3_neg_not_pos h6' ((lexPos3_smul_iff hd).1 hL)
    have hv6 : (7 : Fin 9) ∈ U → (4 : Fin 9) ∈ U → (8 : Fin 9) ∈ U := by
      intro h7 h4
      by_contra h8n
      obtain ⟨a, b, c, d, ha, hb, hc, hd, heq⟩ := syzygy_v6 F
      have h5' := hDn 5 (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, h5⟩)
      have h8' := hDn 8 (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, h8n⟩)
      have hL : LexPos3 ⟪a • (-F.N 5) + b • F.N 7 + c • F.N 4, F.N 3⟫
          ⟪a • (-F.N 5) + b • F.N 7 + c • F.N 4, d1⟫
          ⟪a • (-F.N 5) + b • F.N 7 + c • F.N 4, d2⟫ := by
        simp only [inner_add_left, real_inner_smul_left, inner_neg_left]
        exact lexPos3_add (lexPos3_add (lexPos3_smul ha h5') (lexPos3_smul hb (hU 7 h7)))
          (lexPos3_smul hc (hU 4 h4))
      rw [heq] at hL
      simp only [real_inner_smul_left] at hL
      exact lexPos3_neg_not_pos h8' ((lexPos3_smul_iff hd).1 hL)
    have hcbar : ¬ ((2 : Fin 9) ∈ U ∧ (4 : Fin 9) ∈ U ∧ (7 : Fin 9) ∈ U) := by
      rintro ⟨h2, h4, h7⟩
      obtain ⟨a, b, c, d, ha, hb, hc, hd, heq⟩ := syzygy_cbar F hcb
      have hL : LexPos3 ⟪a • F.N 2 + b • F.N 4 + c • F.N 7, F.N 3⟫
          ⟪a • F.N 2 + b • F.N 4 + c • F.N 7, d1⟫
          ⟪a • F.N 2 + b • F.N 4 + c • F.N 7, d2⟫ := by
        simp only [inner_add_left, real_inner_smul_left]
        exact lexPos3_add (lexPos3_add (lexPos3_smul ha (hU 2 h2)) (lexPos3_smul hb (hU 4 h4)))
          (lexPos3_smul hc (hU 7 h7))
      rw [heq] at hL
      rcases eq_or_lt_of_le hd with rfl | hdpos
      · simp at hL
        rcases hL with h | ⟨_, h | ⟨_, h⟩⟩ <;> linarith
      · have h5' := hDn 5 (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, h5⟩)
        simp only [real_inner_smul_left] at hL
        exact lexPos3_neg_not_pos h5' ((lexPos3_smul_iff hdpos).1 hL)
    have hnotTE : (7 : Fin 9) ∉ U →
        ((2 : Fin 9) ∉ U ∧ (6 : Fin 9) ∉ U) ∨ ((4 : Fin 9) ∉ U ∧ (8 : Fin 9) ∉ U) := by
      intro h7n
      have h7le : ⟪F.N 7, F.N 3⟫ ≤ 0 := by
        by_contra hlt; push Not at hlt
        exact h7n ((hmem 7).2 (Or.inl hlt))
      have hnot : ¬ ((0 ≤ ⟪F.N 2, F.N 3⟫ ∨ 0 ≤ ⟪F.N 6, F.N 3⟫) ∧
          (0 ≤ ⟪F.N 4, F.N 3⟫ ∨ 0 ≤ ⟪F.N 8, F.N 3⟫)) := fun h => hTE ⟨h7le, h⟩
      rw [not_and_or] at hnot
      rcases hnot with h26 | h48
      · push Not at h26
        left; exact ⟨fun h => lexPos3_neg_not_pos (Or.inl (neg_pos.2 h26.1)) (hU 2 h),
          fun h => lexPos3_neg_not_pos (Or.inl (neg_pos.2 h26.2)) (hU 6 h)⟩
      · push Not at h48
        right; exact ⟨fun h => lexPos3_neg_not_pos (Or.inl (neg_pos.2 h48.1)) (hU 4 h),
          fun h => lexPos3_neg_not_pos (Or.inl (neg_pos.2 h48.2)) (hU 8 h)⟩
    exact ⟨U, hmem, hU, hDn, u_subset_cases U h3 h0 h1 h5 hv3 hv2 hv6 hcbar hnotTE⟩
  let closeRim := fun (k : ℕ) [NeZero k] (hk : 4 ≤ k) (c : ZMod k → Fin 7) (hc : Function.Injective c)
      (U : Finset (Fin 9)) (hcyc : S0xCycUD s0x_S24 c U (Finset.univ \ U)) (d1 d2 : ℝ³)
      (hU : ∀ t ∈ U, LexPos3 ⟪F.N t, F.N 3⟫ ⟪F.N t, d1⟫ ⟪F.N t, d2⟫)
      (hDn : ∀ t ∈ Finset.univ \ U, LexPos3 (-⟪F.N t, F.N 3⟫) (-⟪F.N t, d1⟫) (-⟪F.N t, d2⟫))
      (hR : RobUniLex (fun i => (⟪x (c i), F.N 3⟫, ⟪x (c i), d1⟫, ⟪x (c i), d2⟫))) =>
      (⟨k, inferInstance, c, U, Finset.univ \ U, F.N 3, d1, d2, hk, hc, hcyc, hU, hDn, hR⟩ :
        Minimality.T24.RCell.LexAny F)
  rcases regime_cover F hTE with hR1 | hR2 | hR3
  · -- Regime 1: (-F.N 1, -F.N 0)
    have h0_dn : ¬ LexPos3 ⟪F.N 0, F.N 3⟫ ⟪F.N 0, -F.N 1⟫ ⟪F.N 0, -F.N 0⟫ := by
      refine lexPos3_neg_not_pos ?_
      rcases lt_or_eq_of_le h03 with h03' | h03'
      · exact Or.inl (neg_pos.2 h03')
      · refine Or.inr ⟨by rw [h03', neg_zero], ?_⟩
        have h01' : ⟪F.N 0, -F.N 1⟫ ≤ 0 := by rw [inner_neg_right]; exact neg_nonpos.2 h01
        rcases lt_or_eq_of_le h01' with h01'' | h01''
        · exact Or.inl (neg_pos.2 h01'')
        · exact Or.inr ⟨by rw [h01'', neg_zero], by rw [inner_neg_right, neg_neg]; exact inner_pos_self F 0⟩
    have h1_dn : ¬ LexPos3 ⟪F.N 1, F.N 3⟫ ⟪F.N 1, -F.N 1⟫ ⟪F.N 1, -F.N 0⟫ := by
      refine lexPos3_neg_not_pos ?_
      rcases lt_or_eq_of_le h13 with h13' | h13'
      · exact Or.inl (neg_pos.2 h13')
      · refine Or.inr ⟨by rw [h13', neg_zero], Or.inl ?_⟩
        rw [inner_neg_right, neg_neg]; exact inner_pos_self F 1
    obtain ⟨U, hmem, hU, hDn, hcases⟩ := hcommon (-F.N 1) (-F.N 0) (r1_indep F) h0_dn h1_dn
    have h2or4 : (2 : Fin 9) ∈ U ∨ (4 : Fin 9) ∈ U := by
      rcases hR1 with h2 | h4
      · left; exact (hmem 2).2 (Or.inl h2)
      · right; exact (hmem 4).2 (Or.inl h4)
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exfalso; rcases h2or4 with h | h <;> simp at h
    · exact closeRim 5 (by omega) cB1 inj_B1 {3, 2} cyc_B1 (-F.N 1) (-F.N 0) hU hDn (r1_B1 F)
    · exfalso; rcases h2or4 with h | h <;> simp at h
    · exact closeRim 4 (by omega) cB3 inj_B3 {3, 2, 6} cyc_B3 (-F.N 1) (-F.N 0) hU hDn (r1_B3 F)
    · exact closeRim 5 (by omega) cC1 inj_C1 {3, 4} cyc_C1 (-F.N 1) (-F.N 0) hU hDn (r1_C1 F)
    · exfalso; rcases h2or4 with h | h <;> simp at h
    · exact closeRim 4 (by omega) cC3 inj_C3 {3, 4, 8} cyc_C3 (-F.N 1) (-F.N 0) hU hDn (r1_C3 F)
    · exfalso; rcases h2or4 with h | h <;> simp at h
    · exact closeRim 5 (by omega) cA2 inj_A2 {3, 4, 7, 8} cyc_A2 (-F.N 1) (-F.N 0) hU hDn (r1_A2 F)
    · exfalso; rcases h2or4 with h | h <;> simp at h
    · exact closeRim 5 (by omega) cA4 inj_A4 {3, 2, 6, 7} cyc_A4 (-F.N 1) (-F.N 0) hU hDn (r1_A4 F)
    · exfalso; rcases h2or4 with h | h <;> simp at h
    · exact closeRim 4 (by omega) cA6 inj_A6 {3, 4, 6, 7, 8} cyc_A6 (-F.N 1) (-F.N 0) hU hDn (r1_A6 F)
    · exact closeRim 4 (by omega) cA7 inj_A7 {3, 2, 6, 7, 8} cyc_A7 (-F.N 1) (-F.N 0) hU hDn (r1_A7 F)
  · -- Regime 2: (-F.N 6, -F.N 2)
    have h0_dn : ¬ LexPos3 ⟪F.N 0, F.N 3⟫ ⟪F.N 0, -F.N 6⟫ ⟪F.N 0, -F.N 2⟫ :=
      lexPos3_neg_not_pos (Or.inl (neg_pos.2 (h20_lt hR2.1)))
    have h1_dn : ¬ LexPos3 ⟪F.N 1, F.N 3⟫ ⟪F.N 1, -F.N 6⟫ ⟪F.N 1, -F.N 2⟫ :=
      lexPos3_neg_not_pos (Or.inl (neg_pos.2 (h41_lt hR2.2.1)))
    obtain ⟨U, hmem, hU, hDn, hcases⟩ := hcommon (-F.N 6) (-F.N 2) (r2_indep F) h0_dn h1_dn
    have hcond : (6 : Fin 9) ∈ U ∨ ((4 : Fin 9) ∉ U ∧ (8 : Fin 9) ∉ U) := by
      rcases hR2.2.2 with h6pos | ⟨_, h4lt, h8lt⟩
      · left; exact (hmem 6).2 (Or.inl h6pos)
      · right; exact ⟨fun h => lexPos3_neg_not_pos (Or.inl (neg_pos.2 h4lt)) (hU 4 h),
          fun h => lexPos3_neg_not_pos (Or.inl (neg_pos.2 h8lt)) (hU 8 h)⟩
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine closeRim 4 (by omega) cR0 inj_R0 {3} cyc_R0 (-F.N 6) (-F.N 2) hU hDn ?_
      have hc0 : cR0 0 = 0 := by decide
      have hc1 : cR0 1 = 4 := by decide
      have hc2 : cR0 2 = 3 := by decide
      have hc3 : cR0 3 = 5 := by decide
      refine robUniLex_four_of_mixed ?_ ?_
      · refine ⟨(2, 1), by decide, lexLt3_of_snd ?_ ?_⟩
        · dsimp only; rw [hc2, hc1, ← sub_eq_zero, ← inner_sub_left, real_inner_comm, F.inner_sub,
            F.zero 3 4 (by decide), F.zero 3 3 (by decide), sub_self]
        · dsimp only; rw [hc2, hc1, ← sub_pos, ← inner_sub_left, real_inner_comm, inner_neg_left, F.inner_sub,
            F.zero 6 3 (by decide), sub_zero]; exact neg_pos.2 (F.neg 6 4 (by decide))
      · refine ⟨(0, 3), by decide, lexLt3_of_snd ?_ ?_⟩
        · dsimp only; rw [hc3, hc0, ← sub_eq_zero, ← inner_sub_left, real_inner_comm, F.inner_sub,
            F.zero 3 5 (by decide), F.zero 3 0 (by decide), sub_self]
        · dsimp only; rw [hc3, hc0, ← sub_pos, ← inner_sub_left, real_inner_comm, inner_neg_left, F.inner_sub,
            F.zero 6 5 (by decide), sub_zero]; exact neg_pos.2 (F.neg 6 0 (by decide))
    · exact closeRim 5 (by omega) cB1 inj_B1 {3, 2} cyc_B1 (-F.N 6) (-F.N 2) hU hDn (r2_B1 F)
    · exact closeRim 5 (by omega) cB2 inj_B2 {3, 6} cyc_B2 (-F.N 6) (-F.N 2) hU hDn (r2_B2 F)
    · exact closeRim 4 (by omega) cB3 inj_B3 {3, 2, 6} cyc_B3 (-F.N 6) (-F.N 2) hU hDn (r2_B3 F)
    · exfalso; rcases hcond with h | ⟨h4, _⟩ <;> [exact absurd h (by decide); exact h4 (by decide)]
    · exfalso; rcases hcond with h | ⟨_, h8⟩ <;> [exact absurd h (by decide); exact h8 (by decide)]
    · exfalso; rcases hcond with h | ⟨h4, _⟩ <;> [exact absurd h (by decide); exact h4 (by decide)]
    · exfalso; rcases hcond with h | ⟨_, h8⟩ <;> [exact absurd h (by decide); exact h8 (by decide)]
    · exfalso; rcases hcond with h | ⟨h4, _⟩ <;> [exact absurd h (by decide); exact h4 (by decide)]
    · exact closeRim 6 (by omega) cA3 inj_A3 {3, 6, 7} cyc_A3 (-F.N 6) (-F.N 2) hU hDn (r2_A3 F)
    · exact closeRim 5 (by omega) cA4 inj_A4 {3, 2, 6, 7} cyc_A4 (-F.N 6) (-F.N 2) hU hDn (r2_A4 F)
    · exact closeRim 5 (by omega) cA5 inj_A5 {3, 6, 7, 8} cyc_A5 (-F.N 6) (-F.N 2) hU hDn (r2_A5 F)
    · exact closeRim 4 (by omega) cA6 inj_A6 {3, 4, 6, 7, 8} cyc_A6 (-F.N 6) (-F.N 2) hU hDn (r2_A6 F)
    · exact closeRim 4 (by omega) cA7 inj_A7 {3, 2, 6, 7, 8} cyc_A7 (-F.N 6) (-F.N 2) hU hDn (r2_A7 F)
  · -- Regime 3: (-F.N 8, -F.N 4)
    have h0_dn : ¬ LexPos3 ⟪F.N 0, F.N 3⟫ ⟪F.N 0, -F.N 8⟫ ⟪F.N 0, -F.N 4⟫ :=
      lexPos3_neg_not_pos (Or.inl (neg_pos.2 (h20_lt hR3.1)))
    have h1_dn : ¬ LexPos3 ⟪F.N 1, F.N 3⟫ ⟪F.N 1, -F.N 8⟫ ⟪F.N 1, -F.N 4⟫ :=
      lexPos3_neg_not_pos (Or.inl (neg_pos.2 (h41_lt hR3.2.1)))
    obtain ⟨U, hmem, hU, hDn, hcases⟩ := hcommon (-F.N 8) (-F.N 4) (r3_indep F) h0_dn h1_dn
    have hcond : (8 : Fin 9) ∈ U ∨ ((2 : Fin 9) ∉ U ∧ (6 : Fin 9) ∉ U) := by
      rcases hR3.2.2.2 with h8pos | ⟨_, h2lt, h6lt⟩
      · left; exact (hmem 8).2 (Or.inl h8pos)
      · right; exact ⟨fun h => lexPos3_neg_not_pos (Or.inl (neg_pos.2 h2lt)) (hU 2 h),
          fun h => lexPos3_neg_not_pos (Or.inl (neg_pos.2 h6lt)) (hU 6 h)⟩
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine closeRim 4 (by omega) cR0 inj_R0 {3} cyc_R0 (-F.N 8) (-F.N 4) hU hDn ?_
      have hc0 : cR0 0 = 0 := by decide
      have hc1 : cR0 1 = 4 := by decide
      have hc2 : cR0 2 = 3 := by decide
      have hc3 : cR0 3 = 5 := by decide
      refine robUniLex_four_of_mixed ?_ ?_
      · refine ⟨(2, 3), by decide, lexLt3_of_snd ?_ ?_⟩
        · dsimp only; rw [hc2, hc3, ← sub_eq_zero, ← inner_sub_left, real_inner_comm, F.inner_sub,
            F.zero 3 3 (by decide), F.zero 3 5 (by decide), sub_self]
        · dsimp only; rw [hc2, hc3, ← sub_pos, ← inner_sub_left, real_inner_comm, inner_neg_left, F.inner_sub,
            F.zero 8 3 (by decide), sub_zero]; exact neg_pos.2 (F.neg 8 5 (by decide))
      · refine ⟨(0, 1), by decide, lexLt3_of_snd ?_ ?_⟩
        · dsimp only; rw [hc1, hc0, ← sub_eq_zero, ← inner_sub_left, real_inner_comm, F.inner_sub,
            F.zero 3 4 (by decide), F.zero 3 0 (by decide), sub_self]
        · dsimp only; rw [hc1, hc0, ← sub_pos, ← inner_sub_left, real_inner_comm, inner_neg_left, F.inner_sub,
            F.zero 8 4 (by decide), sub_zero]; exact neg_pos.2 (F.neg 8 0 (by decide))
    · exfalso; rcases hcond with h | ⟨h2, _⟩ <;> [exact absurd h (by decide); exact h2 (by decide)]
    · exfalso; rcases hcond with h | ⟨_, h6⟩ <;> [exact absurd h (by decide); exact h6 (by decide)]
    · exfalso; rcases hcond with h | ⟨h2, _⟩ <;> [exact absurd h (by decide); exact h2 (by decide)]
    · exact closeRim 5 (by omega) cC1 inj_C1 {3, 4} cyc_C1 (-F.N 8) (-F.N 4) hU hDn (r3_C1 F)
    · exact closeRim 5 (by omega) cC2 inj_C2 {3, 8} cyc_C2 (-F.N 8) (-F.N 4) hU hDn (r3_C2 F)
    · exact closeRim 4 (by omega) cC3 inj_C3 {3, 4, 8} cyc_C3 (-F.N 8) (-F.N 4) hU hDn (r3_C3 F)
    · exact closeRim 6 (by omega) cA1 inj_A1 {3, 7, 8} cyc_A1 (-F.N 8) (-F.N 4) hU hDn (r3_A1 F)
    · exact closeRim 5 (by omega) cA2 inj_A2 {3, 4, 7, 8} cyc_A2 (-F.N 8) (-F.N 4) hU hDn (r3_A2 F)
    · exfalso; rcases hcond with h | ⟨_, h6⟩ <;> [exact absurd h (by decide); exact h6 (by decide)]
    · exfalso; rcases hcond with h | ⟨h2, _⟩ <;> [exact absurd h (by decide); exact h2 (by decide)]
    · exact closeRim 5 (by omega) cA5 inj_A5 {3, 6, 7, 8} cyc_A5 (-F.N 8) (-F.N 4) hU hDn (r3_A5 F)
    · exact closeRim 4 (by omega) cA6 inj_A6 {3, 4, 6, 7, 8} cyc_A6 (-F.N 8) (-F.N 4) hU hDn (r3_A6 F)
    · exact closeRim 4 (by omega) cA7 inj_A7 {3, 2, 6, 7, 8} cyc_A7 (-F.N 8) (-F.N 4) hU hDn (r3_A7 F)

end Minimality.T24.QN
