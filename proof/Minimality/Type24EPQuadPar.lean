module

public import Minimality.Type24EPQuad

/-!
# Parallel case of the quadrilateral facet cell (`QuadFacetEPPar`)

Discharges the residual `QuadFacetEPPar` of `Type24EPQuad.lean` (Carbon A79 Theorem 2.1):
when opposite edges of the planar quadrilateral `0345` (`rimG = [0, 4, 3, 5]`) are parallel,
an arbitrarily small tilt `w = w₀ + t • v` in the open cell of `0345` still yields
`Gen.EdgePlaneAny x` (and hence `EPF.QuadFacetEP` and `Stmt.OpenEP ↔ EPF.OpenEP'`
unconditionally).

Proof structure:
1. Rotate by `1` if needed so `E₀ ∥ E₂`, i.e., `E₂ = -lam • E₀` with `lam > 0` from `StrictRimN`.
2. Tilt `w` in the `StrictRimN` cell to avoid the finite planes `⟪E_i, w⟫ = 0`,
   `⟪X (i + 2) - X i, w⟫ = 0`, `⟪‖E₀‖² • E₁ - ⟪E₀, E₁⟫ • E₀, w⟫ = 0`,
   `⟪‖E₁‖² • E₂ - ⟪E₁, E₂⟫ • E₁, w⟫ = 0`, and hidden-triangle edge normals.
3. **Spin cancellation (`epRows_of_spinCancel`):** at `a = 0`, `edgePlaneSpin X w 0 2 2 =
   edgePlaneSpin X w 0 2 3 ≠ 0`; whenever `{z₁, z₂}` and `{z₃, z₀}` are strictly separated,
   `(s, M * α, M * μ)` for large `M` satisfies all 6 rows of `Split.EV.EPRows X w 0`.
4. If `{z₁, z₂}` and `{z₃, z₀}` are not separated:
   - If `lam = 1` (parallelogram), rotating by `1` gives `E₃ = -E₁` with `{z₂, z₃}` and
     `{z₀, z₁}` strictly separated, so spin cancellation at `a = 1` succeeds.
   - If `lam ≠ 1` (strict trapezoid), `det3 E₁ (-E₃) w ≠ 0` holds automatically and the depth
     order matches clause 2 at `r ∈ {0, 2}` or clause 3 at `r ∈ {1, 3}` of `EPQ.sr4_core`,
     giving `SplitRows` and `Gen.EdgePlaneAny x` via `Split.EV.split_core_ep`.
-/

@[expose] public section

set_option autoImplicit false

open scoped RealInnerProductSpace Topology
open Finset Filter
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.NC Minimality.T24.Z0 Minimality.T24.EPQ

namespace Minimality.T24.EPQP

private lemma det3_smul_left (c : ℝ) (a b w : ℝ³) :
    Split.det3 (c • a) b w = c * Split.det3 a b w := by
  simp only [Split.det3, PiLp.smul_apply, smul_eq_mul]; ring

private lemma det3_smul_mid (c : ℝ) (a b w : ℝ³) :
    Split.det3 a (c • b) w = c * Split.det3 a b w := by
  simp only [Split.det3, PiLp.smul_apply, smul_eq_mul]; ring

private lemma cross_eq_zero_iff_collinear {a b : ℝ³} (ha : a ≠ 0) :
    cross a b = 0 → ∃ c : ℝ, b = c • a := by
  intro hcr
  have hcr0 : a 1 * b 2 - a 2 * b 1 = 0 := by simpa [cross] using congrArg (fun v => v 0) hcr
  have hcr1 : a 2 * b 0 - a 0 * b 2 = 0 := by simpa [cross] using congrArg (fun v => v 1) hcr
  have hcr2 : a 0 * b 1 - a 1 * b 0 = 0 := by simpa [cross] using congrArg (fun v => v 2) hcr
  have ha012 : a 0 ≠ 0 ∨ a 1 ≠ 0 ∨ a 2 ≠ 0 := by
    by_contra h
    push Not at h
    apply ha
    ext i; fin_cases i <;> simp [h.1, h.2.1, h.2.2]
  rcases ha012 with h0 | h1 | h2
  · refine ⟨b 0 / a 0, ?_⟩
    ext i; fin_cases i <;> simp only [PiLp.smul_apply, smul_eq_mul, Fin.isValue, Fin.reduceFinMk]
    · exact (div_mul_cancel₀ _ h0).symm
    · field_simp [h0]; linarith [hcr2]
    · field_simp [h0]; linarith [hcr1]
  · refine ⟨b 1 / a 1, ?_⟩
    ext i; fin_cases i <;> simp only [PiLp.smul_apply, smul_eq_mul, Fin.isValue, Fin.reduceFinMk]
    · field_simp [h1]; linarith [hcr2]
    · exact (div_mul_cancel₀ _ h1).symm
    · field_simp [h1]; linarith [hcr0]
  · refine ⟨b 2 / a 2, ?_⟩
    ext i; fin_cases i <;> simp only [PiLp.smul_apply, smul_eq_mul, Fin.isValue, Fin.reduceFinMk]
    · field_simp [h2]; linarith [hcr1]
    · field_simp [h2]; linarith [hcr0]
    · exact (div_mul_cancel₀ _ h2).symm

/-- **Spin cancellation at `a = 0`** when `E₂ = -lam • E₀` (`lam > 0`) and `{z₁, z₂}` is
strictly separated from `{z₃, z₀}` on `ℝ`. -/
theorem epRows_of_spinCancel (X : ZMod 4 → ℝ³) (w : ℝ³) (lam : ℝ) (hlam : 0 < lam)
    (hw0 : w ≠ 0)
    (hE2 : X 3 - X 2 = (-lam) • (X 1 - X 0))
    (hdet1 : 0 < Split.det3 (X 1 - X 0) (X 2 - X 1) w)
    (hdet3 : 0 < Split.det3 (X 1 - X 0) (X 3 - X 0) w)
    (hD : ⟪X 1 - X 0, w⟫ ≠ 0)
    (hspin_ne : ⟪⟪X 1 - X 0, X 1 - X 0⟫ • (X 2 - X 1) -
        ⟪X 1 - X 0, X 2 - X 1⟫ • (X 1 - X 0), w⟫ ≠ 0)
    (hsep : (max ⟪X 1, w⟫ ⟪X 2, w⟫ < min ⟪X 3, w⟫ ⟪X 0, w⟫) ∨
            (max ⟪X 3, w⟫ ⟪X 0, w⟫ < min ⟪X 1, w⟫ ⟪X 2, w⟫)) :
    ∃ s α μ : ℝ, Split.EV.EPRows X w 0 s α μ := by
  set E0 := X 1 - X 0
  set E1 := X 2 - X 1
  set E2 := X 3 - X 2
  set E3 := X 0 - X 3
  set D := ⟪E0, w⟫
  have hww : 0 < ⟪w, w⟫ := real_inner_self_pos.2 hw0
  -- Spin identity at `i = 2`, `j = 2` and `j = 3`:
  have hS22 : Split.edgePlaneSpin X w 0 2 2 =
      lam * ⟪w, w⟫ * ⟪⟪E0, E0⟫ • E1 - ⟪E0, E1⟫ • E0, w⟫ / D := by
    have hX20 : X 2 - X 0 = E0 + E1 := by simp only [E0, E1]; abel
    simp only [Split.edgePlaneSpin, show (2 : ZMod 4) + 1 = 3 from rfl,
      show (0 : ZMod 4) + 1 = 1 from rfl]
    change Split.det3 E2 (cross w (X 2 - X 0)) w +
      (⟪X 2 - X 0, w⟫ / D) * Split.det3 E2 (cross E0 w) w = _
    rw [hE2, hX20]
    have e1 : Split.det3 ((-lam) • E0) (cross w (E0 + E1)) w =
        -lam * (⟪w, w⟫ * (⟪E0, E0⟫ + ⟪E0, E1⟫) - (D + ⟪E1, w⟫) * D) := by
      simp only [D, Split.det3, Split.inner3, Split.cross_0, Split.cross_1, Split.cross_2,
        PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
      ring
    have e2 : Split.det3 ((-lam) • E0) (cross E0 w) w =
        -lam * (D * D - ⟪w, w⟫ * ⟪E0, E0⟫) := by
      simp only [D, Split.det3, Split.inner3, Split.cross_0, Split.cross_1, Split.cross_2,
        PiLp.smul_apply, smul_eq_mul]
      ring
    have ew : ⟪E0 + E1, w⟫ = D + ⟪E1, w⟫ := by simp only [D, inner_add_left]
    have hlin : ⟪⟪E0, E0⟫ • E1 - ⟪E0, E1⟫ • E0, w⟫ = ⟪E0, E0⟫ * ⟪E1, w⟫ - ⟪E0, E1⟫ * D := by
      simp only [D, inner_sub_left, real_inner_smul_left]
    rw [e1, e2, ew, hlin]
    field_simp [hD]
    ring
  have hS23 : Split.edgePlaneSpin X w 0 2 3 = Split.edgePlaneSpin X w 0 2 2 := by
    simp only [Split.edgePlaneSpin, show (2 : ZMod 4) + 1 = 3 from rfl,
      show (0 : ZMod 4) + 1 = 1 from rfl]
    have hX30 : X 3 - X 0 = (X 2 - X 0) + (-lam) • E0 := by
      calc X 3 - X 0 = (X 2 - X 0) + (X 3 - X 2) := by abel
        _ = (X 2 - X 0) + (-lam) • E0 := by rw [show X 3 - X 2 = (-lam) • E0 from hE2]
    change Split.det3 E2 (cross w (X 3 - X 0)) w +
      (⟪X 3 - X 0, w⟫ / D) * Split.det3 E2 (cross E0 w) w =
      Split.det3 E2 (cross w (X 2 - X 0)) w +
      (⟪X 2 - X 0, w⟫ / D) * Split.det3 E2 (cross E0 w) w
    dsimp only [E2]
    rw [hX30, show X 3 - X 2 = (-lam) • E0 from hE2]
    have e1 : Split.det3 ((-lam) • E0) (cross w ((X 2 - X 0) + (-lam) • E0)) w =
        Split.det3 ((-lam) • E0) (cross w (X 2 - X 0)) w +
        (-lam) * (⟪w, w⟫ * ((-lam) * ⟪E0, E0⟫) - ((-lam) * D) * D) := by
      simp only [D, Split.det3, Split.inner3, Split.cross_0, Split.cross_1, Split.cross_2,
        PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
      ring
    have e2 : Split.det3 ((-lam) • E0) (cross E0 w) w =
        -lam * (D * D - ⟪w, w⟫ * ⟪E0, E0⟫) := by
      simp only [D, Split.det3, Split.inner3, Split.cross_0, Split.cross_1, Split.cross_2,
        PiLp.smul_apply, smul_eq_mul]
      ring
    have ew : ⟪(X 2 - X 0) + (-lam) • E0, w⟫ = ⟪X 2 - X 0, w⟫ + (-lam) * D := by
      simp only [D, inner_add_left, real_inner_smul_left]
    rw [e1, ew, e2]
    field_simp [hD]
    ring
  have hS22_ne : Split.edgePlaneSpin X w 0 2 2 ≠ 0 := by
    rw [hS22]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero hlam.ne' hww.ne') hspin_ne) hD
  let s : ℝ := if 0 < Split.edgePlaneSpin X w 0 2 2 then 1 else -1
  have hs_pos : 0 < s * Split.edgePlaneSpin X w 0 2 2 := by
    dsimp only [s]
    split_ifs with h
    · simpa using h
    · have hlt : Split.edgePlaneSpin X w 0 2 2 < 0 := lt_of_le_of_ne (not_lt.mp h) hS22_ne
      nlinarith
  -- Choose `(α₀, μ₀)` so that `(α₀ + μ₀ * ⟪X j - X 0, w⟫) * det3 E_i E_0 w > 0` for `i ∈ {1, 3}`
  have hd1_neg : Split.det3 E1 E0 w < 0 := by
    rw [EPQ.det3_swap]; dsimp only [E0, E1]; linarith
  have hd3_pos : 0 < Split.det3 E3 E0 w := by
    have hE3' : E3 = -(X 3 - X 0) := by simp only [E3]; abel
    rw [EPQ.det3_swap, hE3']
    dsimp only [E0]
    simp only [Split.det3, PiLp.neg_apply] at hdet3 ⊢
    linarith
  have hd2_zero : Split.det3 E2 E0 w = 0 := by
    rw [hE2]
    simp only [Split.det3, PiLp.smul_apply, smul_eq_mul]; ring
  -- Pick separating `α₀, μ₀`
  obtain ⟨α₀, μ₀, h11, h12, h33, h30⟩ : ∃ α₀ μ₀ : ℝ,
      0 < (α₀ + μ₀ * ⟪X 1 - X 0, w⟫) * Split.det3 E1 E0 w ∧
      0 < (α₀ + μ₀ * ⟪X 2 - X 0, w⟫) * Split.det3 E1 E0 w ∧
      0 < (α₀ + μ₀ * ⟪X 3 - X 0, w⟫) * Split.det3 E3 E0 w ∧
      0 < (α₀ + μ₀ * ⟪X 0 - X 0, w⟫) * Split.det3 E3 E0 w := by
    rcases hsep with hlt | hgt
    · let t := (max ⟪X 1, w⟫ ⟪X 2, w⟫ + min ⟪X 3, w⟫ ⟪X 0, w⟫) / 2
      refine ⟨⟪X 0, w⟫ - t, 1, ?_, ?_, ?_, ?_⟩
      · have h1 : ⟪X 1, w⟫ < t := by dsimp only [t]; linarith [le_max_left ⟪X 1, w⟫ ⟪X 2, w⟫]
        have hlin : ⟪X 0, w⟫ - t + 1 * ⟪X 1 - X 0, w⟫ = ⟪X 1, w⟫ - t := by
          rw [inner_sub_left]; ring
        rw [hlin]; exact mul_pos_of_neg_of_neg (by linarith) hd1_neg
      · have h2 : ⟪X 2, w⟫ < t := by dsimp only [t]; linarith [le_max_right ⟪X 1, w⟫ ⟪X 2, w⟫]
        have hlin : ⟪X 0, w⟫ - t + 1 * ⟪X 2 - X 0, w⟫ = ⟪X 2, w⟫ - t := by
          rw [inner_sub_left]; ring
        rw [hlin]; exact mul_pos_of_neg_of_neg (by linarith) hd1_neg
      · have h3 : t < ⟪X 3, w⟫ := by dsimp only [t]; linarith [min_le_left ⟪X 3, w⟫ ⟪X 0, w⟫]
        have hlin : ⟪X 0, w⟫ - t + 1 * ⟪X 3 - X 0, w⟫ = ⟪X 3, w⟫ - t := by
          rw [inner_sub_left]; ring
        rw [hlin]; exact mul_pos (by linarith) hd3_pos
      · have h0 : t < ⟪X 0, w⟫ := by dsimp only [t]; linarith [min_le_right ⟪X 3, w⟫ ⟪X 0, w⟫]
        have hlin : ⟪X 0, w⟫ - t + 1 * ⟪X 0 - X 0, w⟫ = ⟪X 0, w⟫ - t := by
          rw [inner_sub_left]; ring
        rw [hlin]; exact mul_pos (by linarith) hd3_pos
    · let t := (max ⟪X 3, w⟫ ⟪X 0, w⟫ + min ⟪X 1, w⟫ ⟪X 2, w⟫) / 2
      refine ⟨t - ⟪X 0, w⟫, -1, ?_, ?_, ?_, ?_⟩
      · have h1 : t < ⟪X 1, w⟫ := by dsimp only [t]; linarith [min_le_left ⟪X 1, w⟫ ⟪X 2, w⟫]
        have hlin : t - ⟪X 0, w⟫ + (-1) * ⟪X 1 - X 0, w⟫ = t - ⟪X 1, w⟫ := by
          rw [inner_sub_left]; ring
        rw [hlin]; exact mul_pos_of_neg_of_neg (by linarith) hd1_neg
      · have h2 : t < ⟪X 2, w⟫ := by dsimp only [t]; linarith [min_le_right ⟪X 1, w⟫ ⟪X 2, w⟫]
        have hlin : t - ⟪X 0, w⟫ + (-1) * ⟪X 2 - X 0, w⟫ = t - ⟪X 2, w⟫ := by
          rw [inner_sub_left]; ring
        rw [hlin]; exact mul_pos_of_neg_of_neg (by linarith) hd1_neg
      · have h3 : ⟪X 3, w⟫ < t := by dsimp only [t]; linarith [le_max_left ⟪X 3, w⟫ ⟪X 0, w⟫]
        have hlin : t - ⟪X 0, w⟫ + (-1) * ⟪X 3 - X 0, w⟫ = t - ⟪X 3, w⟫ := by
          rw [inner_sub_left]; ring
        rw [hlin]; exact mul_pos (by linarith) hd3_pos
      · have h0 : ⟪X 0, w⟫ < t := by dsimp only [t]; linarith [le_max_right ⟪X 3, w⟫ ⟪X 0, w⟫]
        have hlin : t - ⟪X 0, w⟫ + (-1) * ⟪X 0 - X 0, w⟫ = t - ⟪X 0, w⟫ := by
          rw [inner_sub_left]; ring
        rw [hlin]; exact mul_pos (by linarith) hd3_pos
  -- Scale `(α₀, μ₀)` by `M > 0` large enough to dominate `s * edgePlaneSpin`
  let r11 := (α₀ + μ₀ * ⟪X 1 - X 0, w⟫) * Split.det3 E1 E0 w
  let r12 := (α₀ + μ₀ * ⟪X 2 - X 0, w⟫) * Split.det3 E1 E0 w
  let r33 := (α₀ + μ₀ * ⟪X 3 - X 0, w⟫) * Split.det3 E3 E0 w
  let r30 := (α₀ + μ₀ * ⟪X 0 - X 0, w⟫) * Split.det3 E3 E0 w
  let B := max (|s * Split.edgePlaneSpin X w 0 1 1| / r11)
    (max (|s * Split.edgePlaneSpin X w 0 1 2| / r12)
      (max (|s * Split.edgePlaneSpin X w 0 3 3| / r33)
           (|s * Split.edgePlaneSpin X w 0 3 0| / r30)))
  let M := B + 1
  have hM : 0 < M := by
    have h0 : 0 ≤ B := le_trans (div_nonneg (abs_nonneg _) h11.le) (le_max_left _ _)
    linarith
  refine ⟨s, M * α₀, M * μ₀, fun i j hi hj => ?_⟩
  have hscale : ∀ (j' : ZMod 4) (A : ℝ),
      (M * α₀ + (M * μ₀) * ⟪X j' - X 0, w⟫) * A = M * ((α₀ + μ₀ * ⟪X j' - X 0, w⟫) * A) := by
    intro j' A; ring
  rcases four_cases i with rfl | rfl | rfl | rfl
  · exact absurd rfl hi
  · rcases hj with rfl | rfl
    · rw [show (1 : ZMod 4) + 1 = 2 from rfl, show (0 : ZMod 4) + 1 = 1 from rfl]
      change 0 < (M * α₀ + (M * μ₀) * ⟪X 1 - X 0, w⟫) * Split.det3 E1 E0 w + s * Split.edgePlaneSpin X w 0 1 1
      rw [hscale]
      have hB1 : |s * Split.edgePlaneSpin X w 0 1 1| / r11 ≤ B := le_max_left _ _
      have hMr : |s * Split.edgePlaneSpin X w 0 1 1| < M * r11 := by
        have := (div_le_iff₀ h11).mp hB1
        nlinarith [h11]
      linarith [neg_le_abs (s * Split.edgePlaneSpin X w 0 1 1)]
    · rw [show (1 : ZMod 4) + 1 = 2 from rfl, show (0 : ZMod 4) + 1 = 1 from rfl]
      change 0 < (M * α₀ + (M * μ₀) * ⟪X 2 - X 0, w⟫) * Split.det3 E1 E0 w + s * Split.edgePlaneSpin X w 0 1 2
      rw [hscale]
      have hB2 : |s * Split.edgePlaneSpin X w 0 1 2| / r12 ≤ B :=
        le_trans (le_max_left _ _) (le_max_right _ _)
      have hMr : |s * Split.edgePlaneSpin X w 0 1 2| < M * r12 := by
        have := (div_le_iff₀ h12).mp hB2
        nlinarith [h12]
      linarith [neg_le_abs (s * Split.edgePlaneSpin X w 0 1 2)]
  · rcases hj with rfl | rfl
    · rw [show (2 : ZMod 4) + 1 = 3 from rfl, show (0 : ZMod 4) + 1 = 1 from rfl]
      change 0 < (M * α₀ + (M * μ₀) * ⟪X 2 - X 0, w⟫) * Split.det3 E2 E0 w + s * Split.edgePlaneSpin X w 0 2 2
      rw [hd2_zero, mul_zero, zero_add]; exact hs_pos
    · rw [show (2 : ZMod 4) + 1 = 3 from rfl, show (0 : ZMod 4) + 1 = 1 from rfl]
      change 0 < (M * α₀ + (M * μ₀) * ⟪X 3 - X 0, w⟫) * Split.det3 E2 E0 w + s * Split.edgePlaneSpin X w 0 2 3
      rw [hd2_zero, mul_zero, zero_add, hS23]; exact hs_pos
  · rcases hj with rfl | rfl
    · rw [show (3 : ZMod 4) + 1 = 0 from rfl, show (0 : ZMod 4) + 1 = 1 from rfl]
      change 0 < (M * α₀ + (M * μ₀) * ⟪X 3 - X 0, w⟫) * Split.det3 E3 E0 w + s * Split.edgePlaneSpin X w 0 3 3
      rw [hscale]
      have hB3 : |s * Split.edgePlaneSpin X w 0 3 3| / r33 ≤ B :=
        le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
      have hMr : |s * Split.edgePlaneSpin X w 0 3 3| < M * r33 := by
        have := (div_le_iff₀ h33).mp hB3
        nlinarith [h33]
      linarith [neg_le_abs (s * Split.edgePlaneSpin X w 0 3 3)]
    · rw [show (3 : ZMod 4) + 1 = 0 from rfl, show (0 : ZMod 4) + 1 = 1 from rfl]
      change 0 < (M * α₀ + (M * μ₀) * ⟪X 0 - X 0, w⟫) * Split.det3 E3 E0 w + s * Split.edgePlaneSpin X w 0 3 0
      rw [hscale]
      have hB4 : |s * Split.edgePlaneSpin X w 0 3 0| / r30 ≤ B :=
        le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
      have hMr : |s * Split.edgePlaneSpin X w 0 3 0| < M * r30 := by
        have := (div_le_iff₀ h30).mp hB4
        nlinarith [h30]
      linarith [neg_le_abs (s * Split.edgePlaneSpin X w 0 3 0)]

private theorem sr4_clause1 {X : ZMod 4 → ℝ³} {w : ℝ³}
    (hcyc : ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 → 0 < Split.det3 (X (i + 1) - X i) (X j - X i) w)
    (hT : Split.det3 (X 2 - X 1) (X 0 - X 3) w ≠ 0)
    (hp : ⟪X 0, w⟫ < ⟪X 1, w⟫ ∧ ⟪X 1, w⟫ < ⟪X 2, w⟫ ∧ ⟪X 2, w⟫ < ⟪X 3, w⟫) :
    ∃ a c : ZMod 4, ∃ σ : ℝ, c ≠ a ∧ c ≠ a + 1 ∧ Split.SplitRows X w a c σ := by
  obtain ⟨_, _, _, e3⟩ := z4add
  rcases hp with ⟨h1, h2, h3⟩
  rcases lt_or_gt_of_ne hT with hTS | hTS
  · refine ⟨3, 2, 1, by decide, by decide, Split.splitRows_of_unimodal_separated (ρ := 1) (by norm_num)
      (fun i j h1 h2 => by simpa using hcyc i j h1 h2) (by decide) (by decide) ?_ ?_ ?_⟩
    · intro j hj1 hj2 hj3
      rcases four_cases j with rfl | rfl | rfl | rfl <;>
      first
      | exact (hj1 (by decide)).elim
      | exact (hj2 (by decide)).elim
      | exact (hj3 (by decide)).elim
      | (simp only [e3, one_mul]; simp only [Split.det3, PiLp.sub_apply] at hTS ⊢; linarith)
    · intro j hj; rcases four_cases j with rfl | rfl | rfl | rfl <;> first | (exfalso; revert hj; decide) | linarith
    · intro j hj; rcases four_cases j with rfl | rfl | rfl | rfl <;> first | (exfalso; revert hj; decide) | linarith
  · refine ⟨3, 1, 1, by decide, by decide, Split.splitRows_of_unimodal_separated (ρ := 1) (by norm_num)
      (fun i j h1 h2 => by simpa using hcyc i j h1 h2) (by decide) (by decide) ?_ ?_ ?_⟩
    · intro j hj1 hj2 hj3
      rcases four_cases j with rfl | rfl | rfl | rfl <;>
      first
      | exact (hj1 (by decide)).elim
      | exact (hj2 (by decide)).elim
      | exact (hj3 (by decide)).elim
      | (simp only [e3, one_mul]; simp only [Split.det3, PiLp.sub_apply] at hTS ⊢; linarith)
    · intro j hj; rcases four_cases j with rfl | rfl | rfl | rfl <;> first | (exfalso; revert hj; decide) | linarith
    · intro j hj; rcases four_cases j with rfl | rfl | rfl | rfl <;> first | (exfalso; revert hj; decide) | linarith

private theorem sr4_clause2 {X : ZMod 4 → ℝ³} {w : ℝ³}
    (hcyc : ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 → 0 < Split.det3 (X (i + 1) - X i) (X j - X i) w)
    (hT : Split.det3 (X 2 - X 1) (X 0 - X 3) w ≠ 0)
    (hp : ⟪X 0, w⟫ < ⟪X 1, w⟫ ∧ ⟪X 1, w⟫ < ⟪X 3, w⟫ ∧ ⟪X 3, w⟫ < ⟪X 2, w⟫) :
    ∃ a c : ZMod 4, ∃ σ : ℝ, c ≠ a ∧ c ≠ a + 1 ∧ Split.SplitRows X w a c σ := by
  obtain ⟨_, e1, _, e3⟩ := z4add
  rcases hp with ⟨h1, h2, h3⟩
  rcases lt_or_gt_of_ne hT with hTS | hTS
  · refine ⟨1, 3, -1, by decide, by decide, Split.splitRows_of_unimodal_separated (ρ := 1) (by norm_num)
      (fun i j h1 h2 => by simpa using hcyc i j h1 h2) (by decide) (by decide) ?_ ?_ ?_⟩
    · intro j hj1 hj2 hj3
      rcases four_cases j with rfl | rfl | rfl | rfl <;>
      first
      | exact (hj1 (by decide)).elim
      | exact (hj2 (by decide)).elim
      | exact (hj3 (by decide)).elim
      | (simp only [e1, one_mul]; simp only [Split.det3, PiLp.sub_apply] at hTS ⊢; linarith)
    · intro j hj; rcases four_cases j with rfl | rfl | rfl | rfl <;> first | (exfalso; revert hj; decide) | linarith
    · intro j hj; rcases four_cases j with rfl | rfl | rfl | rfl <;> first | (exfalso; revert hj; decide) | linarith
  · refine ⟨3, 1, 1, by decide, by decide, Split.splitRows_of_unimodal_separated (ρ := 1) (by norm_num)
      (fun i j h1 h2 => by simpa using hcyc i j h1 h2) (by decide) (by decide) ?_ ?_ ?_⟩
    · intro j hj1 hj2 hj3
      rcases four_cases j with rfl | rfl | rfl | rfl <;>
      first
      | exact (hj1 (by decide)).elim
      | exact (hj2 (by decide)).elim
      | exact (hj3 (by decide)).elim
      | (simp only [e3, one_mul]; simp only [Split.det3, PiLp.sub_apply] at hTS ⊢; linarith)
    · intro j hj; rcases four_cases j with rfl | rfl | rfl | rfl <;> first | (exfalso; revert hj; decide) | linarith
    · intro j hj; rcases four_cases j with rfl | rfl | rfl | rfl <;> first | (exfalso; revert hj; decide) | linarith

private theorem sr4_clause3 {X : ZMod 4 → ℝ³} {w : ℝ³}
    (hcyc : ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 → 0 < Split.det3 (X (i + 1) - X i) (X j - X i) w)
    (hS : Split.det3 (X 3 - X 2) (X 1 - X 0) w ≠ 0)
    (hp : ⟪X 0, w⟫ < ⟪X 3, w⟫ ∧ ⟪X 3, w⟫ < ⟪X 1, w⟫ ∧ ⟪X 1, w⟫ < ⟪X 2, w⟫) :
    ∃ a c : ZMod 4, ∃ σ : ℝ, c ≠ a ∧ c ≠ a + 1 ∧ Split.SplitRows X w a c σ := by
  obtain ⟨e0, _, e2, _⟩ := z4add
  rcases hp with ⟨h1, h2, h3⟩
  rcases lt_or_gt_of_ne hS with hTS | hTS
  · refine ⟨0, 3, -1, by decide, by decide, Split.splitRows_of_unimodal_separated (ρ := 1) (by norm_num)
      (fun i j h1 h2 => by simpa using hcyc i j h1 h2) (by decide) (by decide) ?_ ?_ ?_⟩
    · intro j hj1 hj2 hj3
      rcases four_cases j with rfl | rfl | rfl | rfl <;>
      first
      | exact (hj1 (by decide)).elim
      | exact (hj2 (by decide)).elim
      | exact (hj3 (by decide)).elim
      | (simp only [e0, one_mul]; simp only [Split.det3, PiLp.sub_apply] at hTS ⊢; linarith)
    · intro j hj; rcases four_cases j with rfl | rfl | rfl | rfl <;> first | (exfalso; revert hj; decide) | linarith
    · intro j hj; rcases four_cases j with rfl | rfl | rfl | rfl <;> first | (exfalso; revert hj; decide) | linarith
  · refine ⟨2, 1, 1, by decide, by decide, Split.splitRows_of_unimodal_separated (ρ := 1) (by norm_num)
      (fun i j h1 h2 => by simpa using hcyc i j h1 h2) (by decide) (by decide) ?_ ?_ ?_⟩
    · intro j hj1 hj2 hj3
      rcases four_cases j with rfl | rfl | rfl | rfl <;>
      first
      | exact (hj1 (by decide)).elim
      | exact (hj2 (by decide)).elim
      | exact (hj3 (by decide)).elim
      | (simp only [e2, one_mul]; simp only [Split.det3, PiLp.sub_apply] at hTS ⊢; linarith)
    · intro j hj; rcases four_cases j with rfl | rfl | rfl | rfl <;> first | (exfalso; revert hj; decide) | linarith
    · intro j hj; rcases four_cases j with rfl | rfl | rfl | rfl <;> first | (exfalso; revert hj; decide) | linarith

private theorem sr4_clause4 {X : ZMod 4 → ℝ³} {w : ℝ³}
    (hcyc : ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 → 0 < Split.det3 (X (i + 1) - X i) (X j - X i) w)
    (hS : Split.det3 (X 3 - X 2) (X 1 - X 0) w ≠ 0)
    (hp : ⟪X 0, w⟫ < ⟪X 3, w⟫ ∧ ⟪X 3, w⟫ < ⟪X 2, w⟫ ∧ ⟪X 2, w⟫ < ⟪X 1, w⟫) :
    ∃ a c : ZMod 4, ∃ σ : ℝ, c ≠ a ∧ c ≠ a + 1 ∧ Split.SplitRows X w a c σ := by
  obtain ⟨e0, _, _, _⟩ := z4add
  rcases hp with ⟨h1, h2, h3⟩
  rcases lt_or_gt_of_ne hS with hTS | hTS
  · refine ⟨0, 3, -1, by decide, by decide, Split.splitRows_of_unimodal_separated (ρ := 1) (by norm_num)
      (fun i j h1 h2 => by simpa using hcyc i j h1 h2) (by decide) (by decide) ?_ ?_ ?_⟩
    · intro j hj1 hj2 hj3
      rcases four_cases j with rfl | rfl | rfl | rfl <;>
      first
      | exact (hj1 (by decide)).elim
      | exact (hj2 (by decide)).elim
      | exact (hj3 (by decide)).elim
      | (simp only [e0, one_mul]; simp only [Split.det3, PiLp.sub_apply] at hTS ⊢; linarith)
    · intro j hj; rcases four_cases j with rfl | rfl | rfl | rfl <;> first | (exfalso; revert hj; decide) | linarith
    · intro j hj; rcases four_cases j with rfl | rfl | rfl | rfl <;> first | (exfalso; revert hj; decide) | linarith
  · refine ⟨0, 2, -1, by decide, by decide, Split.splitRows_of_unimodal_separated (ρ := 1) (by norm_num)
      (fun i j h1 h2 => by simpa using hcyc i j h1 h2) (by decide) (by decide) ?_ ?_ ?_⟩
    · intro j hj1 hj2 hj3
      rcases four_cases j with rfl | rfl | rfl | rfl <;>
      first
      | exact (hj1 (by decide)).elim
      | exact (hj2 (by decide)).elim
      | exact (hj3 (by decide)).elim
      | (simp only [e0, one_mul]; simp only [Split.det3, PiLp.sub_apply] at hTS ⊢; linarith)
    · intro j hj; rcases four_cases j with rfl | rfl | rfl | rfl <;> first | (exfalso; revert hj; decide) | linarith
    · intro j hj; rcases four_cases j with rfl | rfl | rfl | rfl <;> first | (exfalso; revert hj; decide) | linarith

private theorem sr4_trapezoid {X : ZMod 4 → ℝ³} {w : ℝ³} {lam : ℝ}
    (hlam : 0 < lam)
    (hcyc_w : ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 → 0 < Split.det3 (X (i + 1) - X i) (X j - X i) w)
    (hT0 : Split.det3 (X 2 - X 1) (X 0 - X 3) w ≠ 0)
    (hS1 : Split.det3 (X 0 - X 3) (X 2 - X 1) w ≠ 0)
    (hz : ∀ i j : ZMod 4, i ≠ j → ⟪X i, w⟫ ≠ ⟪X j, w⟫)
    (hsep0 : ¬(max ⟪X 1, w⟫ ⟪X 2, w⟫ < min ⟪X 3, w⟫ ⟪X 0, w⟫ ∨
      max ⟪X 3, w⟫ ⟪X 0, w⟫ < min ⟪X 1, w⟫ ⟪X 2, w⟫))
    (hrelz : ⟪X 2, w⟫ - ⟪X 0, w⟫ = 1 * (⟪X 3, w⟫ - ⟪X 0, w⟫) + lam * (⟪X 1, w⟫ - ⟪X 0, w⟫)) :
    ∃ a c : ZMod 4, ∃ σ : ℝ, c ≠ a ∧ c ≠ a + 1 ∧ Split.SplitRows X w a c σ := by
  have hna1 := noalt1 one_pos hlam (by linarith) hrelz
  have hna2 := noalt2 one_pos hlam (by linarith) hrelz
  have hrot : ∀ r : ZMod 4,
      ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
        0 < Split.det3 ((fun k => X (k + r)) (i + 1) - (fun k => X (k + r)) i)
          ((fun k => X (k + r)) j - (fun k => X (k + r)) i) w := by
    intro r i j hi hj
    have := hcyc_w (i + r) (j + r) (fun e => hi (add_right_cancel e))
      (fun e => hj (by rw [add_right_comm] at e; exact add_right_cancel e))
    simpa [add_right_comm] using this
  obtain ⟨e0, e1, e2, e3⟩ := z4add
  have hS1_r1 : Split.det3 ((fun k => X (k + 1)) 3 - (fun k => X (k + 1)) 2)
      ((fun k => X (k + 1)) 1 - (fun k => X (k + 1)) 0) w ≠ 0 := by
    simpa [e0, e1, e2, e3] using hS1
  have hS1_r2 : Split.det3 ((fun k => X (k + 2)) 2 - (fun k => X (k + 2)) 1)
      ((fun k => X (k + 2)) 0 - (fun k => X (k + 2)) 3) w ≠ 0 := by
    have a0 : (0 : ZMod 4) + 2 = 2 := rfl
    have a1 : (1 : ZMod 4) + 2 = 3 := rfl
    have a2 : (2 : ZMod 4) + 2 = 0 := rfl
    have a3 : (3 : ZMod 4) + 2 = 1 := rfl
    simpa [a0, a1, a2, a3] using hS1
  have hT0_r3 : Split.det3 ((fun k => X (k + 3)) 3 - (fun k => X (k + 3)) 2)
      ((fun k => X (k + 3)) 1 - (fun k => X (k + 3)) 0) w ≠ 0 := by
    have a0 : (0 : ZMod 4) + 3 = 3 := rfl
    have a1 : (1 : ZMod 4) + 3 = 0 := rfl
    have a2 : (2 : ZMod 4) + 3 = 1 := rfl
    have a3 : (3 : ZMod 4) + 3 = 2 := rfl
    simpa [a0, a1, a2, a3] using hT0
  have hpat := EPQ.pat_exists (hz 0 1 (by decide)) (hz 0 2 (by decide)) (hz 0 3 (by decide))
    (hz 1 2 (by decide)) (hz 1 3 (by decide)) (hz 2 3 (by decide)) hna1 hna2
  unfold EPQ.Pat at hpat
  rcases hpat with (h | h | h | h) | (h | h | h | h) | (h | h | h | h) | (h | h | h | h)
  · exact sr4_clause1 hcyc_w hT0 h
  · exact sr4_clause2 hcyc_w hT0 h
  · exfalso; apply hsep0; right; simp only [max_lt_iff, lt_min_iff]; exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  · exfalso; apply hsep0; right; simp only [max_lt_iff, lt_min_iff]; exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  · exfalso; apply hsep0; left; simp only [max_lt_iff, lt_min_iff]; exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  · exfalso; apply hsep0; left; simp only [max_lt_iff, lt_min_iff]; exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  · obtain ⟨a, c, σ, ha, hc1, hrows⟩ := @sr4_clause3 (fun k => X (k + 1)) w (hrot 1) hS1_r1 (by simpa [e0, e1, e2, e3] using h)
    exact ⟨a + 1, c + 1, σ, fun e => ha (add_right_cancel e),
      fun e => hc1 (add_right_cancel (by rw [add_right_comm] at e; exact e)), splitRows_rot hrows⟩
  · obtain ⟨a, c, σ, ha, hc1, hrows⟩ := @sr4_clause4 (fun k => X (k + 1)) w (hrot 1) hS1_r1 (by simpa [e0, e1, e2, e3] using h)
    exact ⟨a + 1, c + 1, σ, fun e => ha (add_right_cancel e),
      fun e => hc1 (add_right_cancel (by rw [add_right_comm] at e; exact e)), splitRows_rot hrows⟩
  · obtain ⟨a, c, σ, ha, hc1, hrows⟩ := @sr4_clause1 (fun k => X (k + 2)) w (hrot 2) hS1_r2
      (by simpa [show (0 : ZMod 4) + 2 = 2 from rfl, show (1 : ZMod 4) + 2 = 3 from rfl,
        show (2 : ZMod 4) + 2 = 0 from rfl, show (3 : ZMod 4) + 2 = 1 from rfl] using h)
    exact ⟨a + 2, c + 2, σ, fun e => ha (add_right_cancel e),
      fun e => hc1 (add_right_cancel (by rw [add_right_comm] at e; exact e)), splitRows_rot hrows⟩
  · obtain ⟨a, c, σ, ha, hc1, hrows⟩ := @sr4_clause2 (fun k => X (k + 2)) w (hrot 2) hS1_r2
      (by simpa [show (0 : ZMod 4) + 2 = 2 from rfl, show (1 : ZMod 4) + 2 = 3 from rfl,
        show (2 : ZMod 4) + 2 = 0 from rfl, show (3 : ZMod 4) + 2 = 1 from rfl] using h)
    exact ⟨a + 2, c + 2, σ, fun e => ha (add_right_cancel e),
      fun e => hc1 (add_right_cancel (by rw [add_right_comm] at e; exact e)), splitRows_rot hrows⟩
  · exfalso; apply hsep0; left; simp only [max_lt_iff, lt_min_iff]; exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  · exfalso; apply hsep0; left; simp only [max_lt_iff, lt_min_iff]; exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  · exfalso; apply hsep0; right; simp only [max_lt_iff, lt_min_iff]; exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  · exfalso; apply hsep0; right; simp only [max_lt_iff, lt_min_iff]; exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  · obtain ⟨a, c, σ, ha, hc1, hrows⟩ := @sr4_clause3 (fun k => X (k + 3)) w (hrot 3) hT0_r3
      (by simpa [show (0 : ZMod 4) + 3 = 3 from rfl, show (1 : ZMod 4) + 3 = 0 from rfl,
        show (2 : ZMod 4) + 3 = 1 from rfl, show (3 : ZMod 4) + 3 = 2 from rfl] using h)
    exact ⟨a + 3, c + 3, σ, fun e => ha (add_right_cancel e),
      fun e => hc1 (add_right_cancel (by rw [add_right_comm] at e; exact e)), splitRows_rot hrows⟩
  · obtain ⟨a, c, σ, ha, hc1, hrows⟩ := @sr4_clause4 (fun k => X (k + 3)) w (hrot 3) hT0_r3
      (by simpa [show (0 : ZMod 4) + 3 = 3 from rfl, show (1 : ZMod 4) + 3 = 0 from rfl,
        show (2 : ZMod 4) + 3 = 1 from rfl, show (3 : ZMod 4) + 3 = 2 from rfl] using h)
    exact ⟨a + 3, c + 3, σ, fun e => ha (add_right_cancel e),
      fun e => hc1 (add_right_cancel (by rw [add_right_comm] at e; exact e)), splitRows_rot hrows⟩

/-- **Parallel quadrilateral rim (`E₀ ∥ E₂`).**  A strict planar quadrilateral rim with
`cross (E₀) (E₂) = 0` yields `Gen.EdgePlaneAny x`. -/
theorem edgePlaneAny_of_strictRim4_par0 (x : Fin 7 → ℝ³) (hseg : Split.NoBetween x)
    (hx : Function.Injective x) (lab : ZMod 4 → Fin 7)
    (hinj : Function.Injective lab) (w₀ : ℝ³) (hR : Split.StrictRimN x w₀ lab) (al be : ℝ)
    (_hal : 0 < al) (_hbe : 0 < be) (_hab : 1 < al + be)
    (hrel : x (lab 2) - x (lab 0) = al • (x (lab 3) - x (lab 0)) + be • (x (lab 1) - x (lab 0)))
    (hpar : cross (x (lab 1) - x (lab 0)) (x (lab 3) - x (lab 2)) = 0) :
    Gen.EdgePlaneAny x := by
  let X : ZMod 4 → ℝ³ := fun i => x (lab i)
  have hcyc0 : ∀ w : ℝ³, Split.StrictRimN x w lab → ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      0 < Split.det3 (X (i + 1) - X i) (X j - X i) w :=
    fun w hw i j h1 h2 => hw (lab j) i (fun h => h1 (hinj h)) (fun h => h2 (hinj h))
  have hE0_ne : X 1 - X 0 ≠ 0 := by
    intro h0
    have := hcyc0 w₀ hR 0 2 (by decide) (by decide)
    rw [show (0 : ZMod 4) + 1 = 1 from rfl, h0] at this
    simp [Split.det3] at this
  have hE2_ne : X 3 - X 2 ≠ 0 := by
    intro h0
    have := hcyc0 w₀ hR 2 0 (by decide) (by decide)
    rw [show (2 : ZMod 4) + 1 = 3 from rfl, h0] at this
    simp [Split.det3] at this
  obtain ⟨c_par, hc_par⟩ := cross_eq_zero_iff_collinear hE0_ne hpar
  set lam : ℝ := -c_par
  have hE2_eq : X 3 - X 2 = (-lam) • (X 1 - X 0) := by simpa [lam] using hc_par
  have hlam : 0 < lam := by
    have h02 := hcyc0 w₀ hR 0 2 (by decide) (by decide)
    have h20 := hcyc0 w₀ hR 2 0 (by decide) (by decide)
    rw [show (0 : ZMod 4) + 1 = 1 from rfl] at h02
    rw [show (2 : ZMod 4) + 1 = 3 from rfl, hE2_eq, det3_smul_left] at h20
    have hskew : Split.det3 (X 1 - X 0) (X 0 - X 2) w₀ =
        -Split.det3 (X 1 - X 0) (X 2 - X 0) w₀ := by
      simp only [Split.det3, PiLp.sub_apply]; ring
    rw [hskew] at h20
    have hprod : 0 < lam * Split.det3 (X 1 - X 0) (X 2 - X 0) w₀ := by linarith
    exact (mul_pos_iff_of_pos_right h02).mp hprod
  -- From `hE2_eq` and `hrel`, deduce `al = 1` and `be = lam`
  have hal_one : al = 1 := by
    have h03 := hcyc0 w₀ hR 0 3 (by decide) (by decide)
    rw [show (0 : ZMod 4) + 1 = 1 from rfl] at h03
    have hX20 : X 2 - X 0 = (X 3 - X 0) + lam • (X 1 - X 0) := by
      calc X 2 - X 0 = (X 3 - X 0) - (X 3 - X 2) := by abel
        _ = (X 3 - X 0) - (-lam) • (X 1 - X 0) := by rw [hE2_eq]
        _ = (X 3 - X 0) + lam • (X 1 - X 0) := by module
    have hdet_l : Split.det3 (X 1 - X 0) (X 2 - X 0) w₀ = Split.det3 (X 1 - X 0) (X 3 - X 0) w₀ := by
      rw [hX20]
      simp only [Split.det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
    have hdet_r : Split.det3 (X 1 - X 0) (X 2 - X 0) w₀ =
        al * Split.det3 (X 1 - X 0) (X 3 - X 0) w₀ := by
      change Split.det3 (X 1 - X 0) (x (lab 2) - x (lab 0)) w₀ = _
      rw [hrel]
      simp only [Split.det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
    have : (al - 1) * Split.det3 (X 1 - X 0) (X 3 - X 0) w₀ = 0 := by linarith
    have := (mul_eq_zero.mp this).resolve_right h03.ne'
    linarith
  have hbe_lam : be = lam := by
    have h03 := hcyc0 w₀ hR 0 3 (by decide) (by decide)
    rw [show (0 : ZMod 4) + 1 = 1 from rfl] at h03
    have hX20 : X 2 - X 0 = (X 3 - X 0) + lam • (X 1 - X 0) := by
      calc X 2 - X 0 = (X 3 - X 0) - (X 3 - X 2) := by abel
        _ = (X 3 - X 0) - (-lam) • (X 1 - X 0) := by rw [hE2_eq]
        _ = (X 3 - X 0) + lam • (X 1 - X 0) := by module
    have hsub : (be - lam) • (X 1 - X 0) = 0 := by
      calc (be - lam) • (X 1 - X 0)
          = (al • (X 3 - X 0) + be • (X 1 - X 0)) - ((X 3 - X 0) + lam • (X 1 - X 0)) := by
            rw [hal_one, one_smul]; module
        _ = (x (lab 2) - x (lab 0)) - (X 2 - X 0) := by rw [← hrel, ← hX20]
        _ = 0 := sub_self _
    rcases smul_eq_zero.mp hsub with h | h
    · linarith
    · exact absurd h hE0_ne
  -- Hyperplane avoidance in `StrictRimN` neighborhood of `w₀`
  let n01 := ⟪X 1 - X 0, X 1 - X 0⟫ • (X 2 - X 1) - ⟪X 1 - X 0, X 2 - X 1⟫ • (X 1 - X 0)
  let n12 := ⟪X 2 - X 1, X 2 - X 1⟫ • (X 3 - X 2) - ⟪X 2 - X 1, X 3 - X 2⟫ • (X 2 - X 1)
  have hn01 : n01 ≠ 0 := by
    intro h0
    have h01 := hcyc0 w₀ hR 0 2 (by decide) (by decide)
    rw [show (0 : ZMod 4) + 1 = 1 from rfl] at h01
    have h01' : Split.det3 (X 1 - X 0) (X 2 - X 1) w₀ = Split.det3 (X 1 - X 0) (X 2 - X 0) w₀ := by
      simp only [Split.det3, PiLp.sub_apply]; ring
    rw [← h01'] at h01
    have h00 : Split.det3 (X 1 - X 0) n01 w₀ = ⟪X 1 - X 0, X 1 - X 0⟫ * Split.det3 (X 1 - X 0) (X 2 - X 1) w₀ := by
      dsimp only [n01]
      simp only [Split.det3, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [h0] at h00
    have hz : Split.det3 (X 1 - X 0) 0 w₀ = 0 := by simp [Split.det3]
    rw [hz] at h00
    have hE0_sq : 0 < ⟪X 1 - X 0, X 1 - X 0⟫ := real_inner_self_pos.2 hE0_ne
    nlinarith
  have hn12 : n12 ≠ 0 := by
    intro h0
    have h12 := hcyc0 w₀ hR 1 3 (by decide) (by decide)
    have h12' : Split.det3 (X 2 - X 1) (X 3 - X 2) w₀ = Split.det3 (X 2 - X 1) (X 3 - X 1) w₀ := by
      simp only [Split.det3, PiLp.sub_apply]; ring
    rw [show (1 : ZMod 4) + 1 = 2 from rfl, ← h12'] at h12
    have h00 : Split.det3 (X 2 - X 1) n12 w₀ = ⟪X 2 - X 1, X 2 - X 1⟫ * Split.det3 (X 2 - X 1) (X 3 - X 2) w₀ := by
      dsimp only [n12]
      simp only [Split.det3, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [h0] at h00
    have hz : Split.det3 (X 2 - X 1) 0 w₀ = 0 := by simp [Split.det3]
    rw [hz] at h00
    have hE1_ne : X 2 - X 1 ≠ 0 := by
      intro he1
      rw [he1] at h12; simp [Split.det3] at h12
    have hE1_sq : 0 < ⟪X 2 - X 1, X 2 - X 1⟫ := real_inner_self_pos.2 hE1_ne
    nlinarith
  have hne2 : ∀ k : ZMod 4, k + 2 ≠ k := by decide
  have hne21 : ∀ k : ZMod 4, k + 2 ≠ k + 1 := by decide
  have hd1 : ∀ i : ZMod 4, X (i + 1) - X i ≠ 0 := by
    intro i h0
    have := hcyc0 w₀ hR i (i + 2) (hne2 i) (hne21 i)
    rw [h0] at this; simp [Split.det3] at this
  have hd2 : ∀ i : ZMod 4, X (i + 2) - X i ≠ 0 := by
    intro i h0
    have := hcyc0 w₀ hR i (i + 2) (hne2 i) (hne21 i)
    rw [h0] at this; simp [Split.det3] at this
  let mOff := (Finset.univ : Finset (Fin 7)).filter (fun m => ∀ j : ZMod 4, m ≠ lab j)
  let triVec : {m : Fin 7 // m ∈ mOff} × ZMod 4 → ℝ³ := fun ⟨m, j⟩ =>
    cross (x (lab j) - x (lab 0)) (x m.1 - x (lab 0))
  let Fset : Finset ℝ³ :=
    {n01, n12} ∪
    ((Finset.univ : Finset (ZMod 4)).image fun i => X (i + 1) - X i) ∪
    ((Finset.univ : Finset (ZMod 4)).image fun i => X (i + 2) - X i) ∪
    (((Finset.univ : Finset ({m : Fin 7 // m ∈ mOff} × ZMod 4)).image triVec).filter (· ≠ 0))
  have hFset : ∀ y ∈ Fset, y ≠ 0 := by
    intro y hy
    simp only [Fset, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    rcases hy with (((rfl | rfl) | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨⟨p, _⟩, hy0⟩
    · exact hn01
    · exact hn12
    · exact hd1 i
    · exact hd2 i
    · exact hy0
  obtain ⟨v, -, hv⟩ := Minimality.exists_avoid_kernels (ι := {y : ℝ³ // y ∈ Fset})
    (fun y => innerₗ ℝ³ y.1)
    (fun y hy => by
      have h1 := LinearMap.congr_fun hy y.1
      simp only [innerₗ_apply_apply, LinearMap.zero_apply, inner_self_eq_zero] at h1
      exact hFset y.1 y.2 h1) isOpen_univ Set.univ_nonempty
  have hK : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ y ∈ Fset, ⟪y, w₀⟫ + t * ⟪y, v⟫ ≠ 0 := by
    have h_all : ∀ y : {y : ℝ³ // y ∈ Fset}, ∀ᶠ t in 𝓝[>] (0 : ℝ), ⟪y.1, w₀⟫ + t * ⟪y.1, v⟫ ≠ 0 :=
      fun y => Minimality.eventually_affine_ne fun _ => by simpa using hv y
    rw [← eventually_all] at h_all
    filter_upwards [h_all] with t ht y hy
    exact ht ⟨y, hy⟩
  obtain ⟨t, ht_rim, ht_K⟩ := ((Split.strictRim_ev hR v).and hK).exists
  set w := w₀ + t • v with hw
  have hw_ne : ∀ y ∈ Fset, ⟪y, w⟫ ≠ 0 := fun y hy => by
    have hne := ht_K y hy
    rw [hw, inner_add_right, real_inner_smul_right]
    exact hne
  have hw0 : w ≠ 0 := by
    intro h0
    have := hcyc0 w ht_rim 0 2 (by decide) (by decide)
    rw [h0] at this; simp [Split.det3] at this
  have hhid : Split.HiddenInTriangles x w lab := by
    refine Split.hidden_of_rim (by norm_num) x hx hseg w lab hinj ht_rim fun m hm j _ hcr => ?_
    rw [Split.det3_eq_inner_cross]
    have hm_mem : m ∈ mOff := Finset.mem_filter.mpr ⟨Finset.mem_univ m, hm⟩
    have hmem : triVec ⟨⟨m, hm_mem⟩, j⟩ ∈ Fset :=
      Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), hcr⟩)
    exact hw_ne _ hmem
  have hD0 : ⟪X 1 - X 0, w⟫ ≠ 0 :=
    hw_ne _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image_of_mem _ (Finset.mem_univ 0)))))
  have hn01_w : ⟪n01, w⟫ ≠ 0 :=
    hw_ne _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_insert_self _ _))))
  have hn12_w : ⟪n12, w⟫ ≠ 0 :=
    hw_ne _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))))
  have hdet01 : 0 < Split.det3 (X 1 - X 0) (X 2 - X 1) w := by
    have h02 := hcyc0 w ht_rim 0 2 (by decide) (by decide)
    rw [show (0 : ZMod 4) + 1 = 1 from rfl] at h02
    have h01' : Split.det3 (X 1 - X 0) (X 2 - X 1) w = Split.det3 (X 1 - X 0) (X 2 - X 0) w := by
      simp only [Split.det3, PiLp.sub_apply]; ring
    linarith
  have hdet03 : 0 < Split.det3 (X 1 - X 0) (X 3 - X 0) w := by
    have h03 := hcyc0 w ht_rim 0 3 (by decide) (by decide)
    rw [show (0 : ZMod 4) + 1 = 1 from rfl] at h03
    exact h03
  -- Pairwise distinct depths at `w`
  have hz : ∀ i j : ZMod 4, i ≠ j → ⟪X i, w⟫ ≠ ⟪X j, w⟫ := by
    intro i j hij h
    have hsub : ∀ a b : ZMod 4, ⟪X a, w⟫ = ⟪X b, w⟫ → ⟪X a - X b, w⟫ = 0 := fun a b h => by
      rw [inner_sub_left, h, sub_self]
    rcases zmod4_ne_cases i j hij with e | e | e
    · apply hw_ne (X (i + 1) - X i) (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))))
      have := hsub _ _ h; rw [e] at this
      rw [← neg_sub, inner_neg_left, this, neg_zero]
    · apply hw_ne (X (i + 2) - X i) (Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_image_of_mem _ (Finset.mem_univ i))))
      have := hsub _ _ h; rw [e] at this
      rw [← neg_sub, inner_neg_left, this, neg_zero]
    · apply hw_ne (X (j + 1) - X j) (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j)))))
      have := hsub _ _ h; rw [e] at this; exact this
  -- Case split on whether `{z₁, z₂}` and `{z₃, z₀}` are separated on `ℝ`
  by_cases hsep0 : (max ⟪X 1, w⟫ ⟪X 2, w⟫ < min ⟪X 3, w⟫ ⟪X 0, w⟫) ∨
                   (max ⟪X 3, w⟫ ⟪X 0, w⟫ < min ⟪X 1, w⟫ ⟪X 2, w⟫)
  · obtain ⟨s, α, μ, hrow⟩ := epRows_of_spinCancel X w lam hlam hw0 hE2_eq hdet01 hdet03 hD0 hn01_w hsep0
    exact ⟨4, inferInstance, lab, w, 0, s, α, μ, by norm_num, hinj, ht_rim, hhid, hD0, hrow⟩
  · -- `{z₁, z₂}` and `{z₃, z₀}` interleave!
    have hrelz : ⟪X 2, w⟫ - ⟪X 0, w⟫ =
        1 * (⟪X 3, w⟫ - ⟪X 0, w⟫) + lam * (⟪X 1, w⟫ - ⟪X 0, w⟫) := by
      have hq : X 2 - X 0 = (X 3 - X 0) + lam • (X 1 - X 0) := by
        calc X 2 - X 0 = (X 3 - X 0) - (X 3 - X 2) := by abel
          _ = (X 3 - X 0) - (-lam) • (X 1 - X 0) := by rw [hE2_eq]
          _ = (X 3 - X 0) + lam • (X 1 - X 0) := by module
      have := congrArg (fun v => ⟪v, w⟫) hq
      simpa [inner_sub_left, inner_add_left, real_inner_smul_left] using this
    by_cases hlam1 : lam = 1
    · -- **Case A (`lam = 1`, parallelogram):** rotate by `1`!
      rw [hlam1] at hE2_eq hrelz
      let lab1 : ZMod 4 → Fin 7 := fun i => lab (i + 1)
      have hinj1 : Function.Injective lab1 := fun i j hij => by
        have := hinj hij; exact add_right_cancel this
      have ht_rim1 : Split.StrictRimN x w lab1 := fun m i hm1 hm2 =>
        ht_rim m (i + 1) hm1 (by simpa [lab1, add_assoc] using hm2)
      have hhid1 : Split.HiddenInTriangles x w lab1 := fun m hm =>
        hhid m (fun i => by simpa [lab1] using hm (i - 1))
      let Y : ZMod 4 → ℝ³ := fun i => x (lab1 i)
      have hY0 : Y 0 = X 1 := rfl
      have hY1 : Y 1 = X 2 := rfl
      have hY2 : Y 2 = X 3 := rfl
      have hY3 : Y 3 = X 0 := rfl
      have hE31 : Y 3 - Y 2 = (-1 : ℝ) • (Y 1 - Y 0) := by
        rw [hY3, hY2, hY1, hY0]
        have : X 3 - X 2 = (-1 : ℝ) • (X 1 - X 0) := hE2_eq
        calc X 0 - X 3 = (X 0 - X 2) - (X 3 - X 2) := by abel
          _ = (X 0 - X 2) - (-1 : ℝ) • (X 1 - X 0) := by rw [this]
          _ = (-1 : ℝ) • (X 2 - X 1) := by module
      have hD1 : ⟪Y 1 - Y 0, w⟫ ≠ 0 := by
        rw [hY1, hY0]
        exact hw_ne _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_image_of_mem _ (Finset.mem_univ 1)))))
      have hdet12 : 0 < Split.det3 (Y 1 - Y 0) (Y 2 - Y 1) w := by
        rw [hY0, hY1, hY2]
        have h13 := hcyc0 w ht_rim 1 3 (by decide) (by decide)
        rw [show (1 : ZMod 4) + 1 = 2 from rfl] at h13
        have h12' : Split.det3 (X 2 - X 1) (X 3 - X 2) w = Split.det3 (X 2 - X 1) (X 3 - X 1) w := by
          simp only [Split.det3, PiLp.sub_apply]; ring
        linarith
      have hdet10 : 0 < Split.det3 (Y 1 - Y 0) (Y 3 - Y 0) w := by
        rw [hY0, hY1, hY3]
        have h10 := hcyc0 w ht_rim 1 0 (by decide) (by decide)
        rw [show (1 : ZMod 4) + 1 = 2 from rfl] at h10
        exact h10
      have hn12_Y : ⟪⟪Y 1 - Y 0, Y 1 - Y 0⟫ • (Y 2 - Y 1) -
          ⟪Y 1 - Y 0, Y 2 - Y 1⟫ • (Y 1 - Y 0), w⟫ ≠ 0 := by
        dsimp only [n12] at hn12_w
        simpa only [Y, lab1, hY0, hY1, hY2, real_inner_self_eq_norm_sq] using hn12_w
      have hsep1 : (max ⟪Y 1, w⟫ ⟪Y 2, w⟫ < min ⟪Y 3, w⟫ ⟪Y 0, w⟫) ∨
                   (max ⟪Y 3, w⟫ ⟪Y 0, w⟫ < min ⟪Y 1, w⟫ ⟪Y 2, w⟫) := by
        rw [hY0, hY1, hY2, hY3]
        have hz01 := hz 0 1 (by decide)
        have hz02 := hz 0 2 (by decide)
        have hz03 := hz 0 3 (by decide)
        have hz12 := hz 1 2 (by decide)
        have hz13 := hz 1 3 (by decide)
        have hz23 := hz 2 3 (by decide)
        rw [one_mul, one_mul] at hrelz
        rcases lt_or_gt_of_ne hz01 with h01 | h01 <;>
        rcases lt_or_gt_of_ne hz02 with h02 | h02 <;>
        rcases lt_or_gt_of_ne hz03 with h03 | h03 <;>
        rcases lt_or_gt_of_ne hz12 with h12 | h12 <;>
        rcases lt_or_gt_of_ne hz13 with h13 | h13 <;>
        rcases lt_or_gt_of_ne hz23 with h23 | h23 <;>
        first
        | (exfalso; linarith)
        | (exfalso; apply hsep0; left; simp only [max_lt_iff, lt_min_iff]; exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩)
        | (exfalso; apply hsep0; right; simp only [max_lt_iff, lt_min_iff]; exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩)
        | (left; simp only [max_lt_iff, lt_min_iff]; exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩)
        | (right; simp only [max_lt_iff, lt_min_iff]; exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩)
      obtain ⟨s, α, μ, hrow⟩ := epRows_of_spinCancel Y w 1 one_pos hw0 hE31 hdet12 hdet10 hD1 hn12_Y hsep1
      exact ⟨4, inferInstance, lab1, w, 0, s, α, μ, by norm_num, hinj1, ht_rim1, hhid1, hD1, hrow⟩
    · -- **Case B (`lam ≠ 1`, strict trapezoid):** `det3 E₁ (-E₃) w ≠ 0` and `sr4_core` gives `SplitRows`!
      have hT0 : Split.det3 (X 2 - X 1) (X 0 - X 3) w ≠ 0 := by
        have hE13 : X 2 - X 1 = (X 3 - X 0) + (lam - 1) • (X 1 - X 0) := by
          calc X 2 - X 1 = (X 2 - X 0) - (X 1 - X 0) := by abel
            _ = ((X 3 - X 0) - (X 3 - X 2)) - (X 1 - X 0) := by abel
            _ = ((X 3 - X 0) - (-lam) • (X 1 - X 0)) - (X 1 - X 0) := by rw [hE2_eq]
            _ = (X 3 - X 0) + (lam - 1) • (X 1 - X 0) := by module
        have hdet_eq : Split.det3 (X 2 - X 1) (X 0 - X 3) w =
            (lam - 1) * Split.det3 (X 1 - X 0) (X 0 - X 3) w := by
          rw [hE13]
          simp only [Split.det3, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
        rw [hdet_eq]
        have hskew : Split.det3 (X 1 - X 0) (X 0 - X 3) w = -Split.det3 (X 1 - X 0) (X 3 - X 0) w := by
          simp only [Split.det3, PiLp.sub_apply]; ring
        rw [hskew]
        exact mul_ne_zero (sub_ne_zero.mpr hlam1) (neg_ne_zero.mpr hdet03.ne')
      have hS1 : Split.det3 (X 0 - X 3) (X 2 - X 1) w ≠ 0 := by
        rw [EPQ.det3_swap]; exact neg_ne_zero.mpr hT0
      obtain ⟨a, c, σ, hca, hca1, hrows⟩ :=
        sr4_trapezoid hlam (hcyc0 w ht_rim) hT0 hS1 hz hsep0 hrelz
      exact Split.EV.split_core_ep (k := 4) (by norm_num) x hx hseg lab hinj w ht_rim a c σ hca hca1 hrows

private theorem s24_sep_par :
    ∀ i j : Fin 7, j ≠ i → ∃ t : Fin 9, i ∈ s0x_S24 t ∧ j ∉ s0x_S24 t := by decide

/-- **Discharges `QuadFacetEPPar` (Task FD):** any open cell view on the quadrilateral facet `0345`
with two parallel opposite edges yields `Gen.EdgePlaneAny x`. -/
theorem quadFacetEPPar : QuadFacetEPPar := by
  intro x F u hu hnotnp
  have hx := Minimality.H24.SAT.inj_of_fac F
  have hc : Function.Injective rimG := by decide
  obtain ⟨D⟩ := silL_of_cell F rimG_cyc hu.cellLe hu
  choose μ hμ0 hμ using fun i => h21b_exists_mu (by norm_num) hx hc D i
  have hsign := h21b_sign_agree (by norm_num) hx hc D μ hμ0 hμ
  have Q : ∀ i m, m ≠ rimG i → m ≠ rimG (i + 1) →
      0 < D.fA i (x m) * ⟪D.B i, u⟫ - D.fB i (x m) * ⟪D.A i, u⟫ := by
    intro i m h0 h1
    have := h21b_Q_pos D i m h0 h1
    rcases this with h | ⟨h0', h⟩
    · exact h
    · rw [h0'] at h; exact absurd h (lt_irrefl _)
  have key : ∀ (i : ZMod 4) (m : Fin 7),
      Split.det3 (x (rimG (i + 1)) - x (rimG i)) (x m - x (rimG i)) u =
        μ i * (D.fA i (x m) * ⟪D.B i, u⟫ - D.fB i (x m) * ⟪D.A i, u⟫) := by
    intro i m
    rw [Split.det3_eq_minimality]
    exact h21b_det_eq D i (μ i) (hμ i) m u
  obtain ⟨al, be, hal, hbe, hab, hq⟩ := Minimality.T24.Par.par2546_quad F
  have hrel : x (rimG 2) - x (rimG 0) =
      al • (x (rimG 3) - x (rimG 0)) + be • (x (rimG 1) - x (rimG 0)) := by
    simpa [rimG] using hq
  have hseg := Split.noBetween_of_fac F s24_sep_par
  have hR_pos : ∃ w₀ : ℝ³, Split.StrictRimN x w₀ rimG := by
    rcases hsign with h | h
    · refine ⟨u, fun m i h0 h1 => ?_⟩
      rw [key i m]
      exact mul_pos (h i) (Q i m h0 h1)
    · refine ⟨-u, fun m i h0 h1 => ?_⟩
      have e : Split.det3 (x (rimG (i + 1)) - x (rimG i)) (x m - x (rimG i)) (-u) =
          -Split.det3 (x (rimG (i + 1)) - x (rimG i)) (x m - x (rimG i)) u := by
        rw [Split.det3_eq_inner_cross, Split.det3_eq_inner_cross, inner_neg_right]
      rw [e, key i m]
      have := Q i m h0 h1
      nlinarith [h i]
  obtain ⟨w₀, hR⟩ := hR_pos
  have hpar_cases : cross (x (rimG 1) - x (rimG 0)) (x (rimG 3) - x (rimG 2)) = 0 ∨
      cross (x (rimG 2) - x (rimG 1)) (x (rimG 0) - x (rimG 3)) = 0 := by
    unfold QuadNoParallel at hnotnp
    push Not at hnotnp
    by_cases h02 : cross (x 4 - x 0) (x 5 - x 3) = 0
    · left; simpa [rimG] using h02
    · right; simpa [rimG] using hnotnp h02
  rcases hpar_cases with h02 | h13
  · exact edgePlaneAny_of_strictRim4_par0 x hseg hx rimG hc w₀ hR al be hal hbe hab hrel h02
  · let rim1 : ZMod 4 → Fin 7 := fun i => rimG (i + 1)
    have hc1 : Function.Injective rim1 := fun i j hij => add_right_cancel (hc hij)
    have hR1 : Split.StrictRimN x w₀ rim1 := fun m i h0 h1 =>
      hR m (i + 1) h0 (by simpa [rim1, add_assoc] using h1)
    have hrel1 : x (rim1 2) - x (rim1 0) =
        ((al + be - 1) / al) • (x (rim1 3) - x (rim1 0)) +
          (1 / al) • (x (rim1 1) - x (rim1 0)) := by
      have h0 : rim1 0 = rimG 1 := rfl
      have h1 : rim1 1 = rimG 2 := rfl
      have h2 : rim1 2 = rimG 3 := rfl
      have h3 : rim1 3 = rimG 0 := rfl
      rw [h0, h1, h2, h3]
      have h_smul : al • (x (rimG 3) - x (rimG 1)) =
          (al + be - 1) • (x (rimG 0) - x (rimG 1)) + (1 : ℝ) • (x (rimG 2) - x (rimG 1)) := by
        calc al • (x (rimG 3) - x (rimG 1))
            = al • (x (rimG 3) - x (rimG 0)) + al • (x (rimG 0) - x (rimG 1)) := by module
          _ = ((x (rimG 2) - x (rimG 0)) - be • (x (rimG 1) - x (rimG 0))) +
                al • (x (rimG 0) - x (rimG 1)) := by rw [hrel]; module
          _ = (al + be - 1) • (x (rimG 0) - x (rimG 1)) + (1 : ℝ) • (x (rimG 2) - x (rimG 1)) := by
                module
      calc x (rimG 3) - x (rimG 1)
          = (1 / al) • (al • (x (rimG 3) - x (rimG 1))) := by
              rw [smul_smul, one_div_mul_cancel hal.ne', one_smul]
        _ = (1 / al) • ((al + be - 1) • (x (rimG 0) - x (rimG 1)) +
              (1 : ℝ) • (x (rimG 2) - x (rimG 1))) := by rw [h_smul]
        _ = ((al + be - 1) / al) • (x (rimG 0) - x (rimG 1)) +
              (1 / al) • (x (rimG 2) - x (rimG 1)) := by
              simp only [smul_add, smul_smul, div_eq_mul_inv]; ring_nf
    exact edgePlaneAny_of_strictRim4_par0 x hseg hx rim1 hc1 w₀ hR1
      ((al + be - 1) / al) (1 / al) (div_pos (by linarith) hal) (one_div_pos.mpr hal)
      (by have : (al + be - 1) / al + 1 / al = 1 + be / al := by field_simp [hal.ne']; ring
          rw [this]; linarith [div_pos hbe hal])
      hrel1 h13

/-- **Unconditional `QuadFacetEP`:** any open cell view on `0345` yields `Gen.EdgePlaneAny x`. -/
theorem quadFacetEP_all : EPF.QuadFacetEP :=
  quadFacetEP quadFacetEPPar

/-- **Unconditional `OpenEP ↔ OpenEP'`:** removes the `QuadFacetEPPar` hypothesis from
`Type24EPQuad.openEP_iff_openEP'_par`. -/
theorem openEP_iff_openEP'_all : Stmt.OpenEP ↔ EPF.OpenEP' :=
  EPF.openEP_iff_openEP' quadFacetEP_all

/-! ## Satisfiability example -/

/-- Concrete 7-point configuration in `ℝ³` whose 4-rim `0, 1, 2, 3` is a parallelogram
(`E₂ = -E₀`) at `w₀ = (0, 0, 1)`, satisfying `edgePlaneAny_of_strictRim4_par0`. -/
def exPar4Z : Fin 7 → Fin 3 → ℤ
  | 0 => ![0, 0, 0]
  | 1 => ![4, 0, 1]
  | 2 => ![5, 4, 3]
  | 3 => ![1, 4, 2]
  | 4 => ![2, 2, 1]
  | 5 => ![3, 2, 2]
  | 6 => ![2, 1, 0]

noncomputable def exPar4 : Fin 7 → ℝ³ := fun i =>
  !₂[(exPar4Z i 0 : ℝ), (exPar4Z i 1 : ℝ), (exPar4Z i 2 : ℝ)]

def exParLab4 : ZMod 4 → Fin 7
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

private theorem exPar4Z_noBetween : ∀ a b c : Fin 7, a ≠ b → a ≠ c → b ≠ c →
    (exPar4Z b 1 - exPar4Z a 1) * (exPar4Z c 2 - exPar4Z a 2) -
      (exPar4Z b 2 - exPar4Z a 2) * (exPar4Z c 1 - exPar4Z a 1) ≠ 0 ∨
    (exPar4Z b 2 - exPar4Z a 2) * (exPar4Z c 0 - exPar4Z a 0) -
      (exPar4Z b 0 - exPar4Z a 0) * (exPar4Z c 2 - exPar4Z a 2) ≠ 0 ∨
    (exPar4Z b 0 - exPar4Z a 0) * (exPar4Z c 1 - exPar4Z a 1) -
      (exPar4Z b 1 - exPar4Z a 1) * (exPar4Z c 0 - exPar4Z a 0) ≠ 0 := by decide

private theorem exPar4Z_inj : ∀ a b : Fin 7,
    exPar4Z a 0 = exPar4Z b 0 → exPar4Z a 1 = exPar4Z b 1 → exPar4Z a 2 = exPar4Z b 2 → a = b := by decide

theorem example_quad_par_edgePlane : Gen.EdgePlaneAny exPar4 := by
  let w₀ : ℝ³ := !₂[0, 0, 1]
  have hx : Function.Injective exPar4 := by
    intro a b hab
    have h0 : (exPar4Z a 0 : ℝ) = exPar4Z b 0 := by simpa [exPar4] using congrArg (fun v => v 0) hab
    have h1 : (exPar4Z a 1 : ℝ) = exPar4Z b 1 := by simpa [exPar4] using congrArg (fun v => v 1) hab
    have h2 : (exPar4Z a 2 : ℝ) = exPar4Z b 2 := by simpa [exPar4] using congrArg (fun v => v 2) hab
    exact exPar4Z_inj a b (by exact_mod_cast h0) (by exact_mod_cast h1) (by exact_mod_cast h2)
  have hseg : Split.NoBetween exPar4 := by
    intro m p q hp hq t _ _ hmem
    have hpq : p ≠ q := by
      rintro rfl
      simp only [sub_self, smul_zero, add_zero] at hmem
      exact hp (hx hmem).symm
    have hm0 : (exPar4Z m 0 : ℝ) = exPar4Z p 0 + t * (exPar4Z q 0 - exPar4Z p 0) := by
      simpa [exPar4] using congrArg (fun v => v 0) hmem
    have hm1 : (exPar4Z m 1 : ℝ) = exPar4Z p 1 + t * (exPar4Z q 1 - exPar4Z p 1) := by
      simpa [exPar4] using congrArg (fun v => v 1) hmem
    have hm2 : (exPar4Z m 2 : ℝ) = exPar4Z p 2 + t * (exPar4Z q 2 - exPar4Z p 2) := by
      simpa [exPar4] using congrArg (fun v => v 2) hmem
    rcases exPar4Z_noBetween p q m hpq hp hq with h | h | h
    · apply h
      have hr : ((exPar4Z q 1 - exPar4Z p 1 : ℤ) : ℝ) * (exPar4Z m 2 - exPar4Z p 2) -
          (exPar4Z q 2 - exPar4Z p 2) * (exPar4Z m 1 - exPar4Z p 1) = 0 := by
        rw [hm1, hm2]; push_cast; ring
      exact_mod_cast hr
    · apply h
      have hr : ((exPar4Z q 2 - exPar4Z p 2 : ℤ) : ℝ) * (exPar4Z m 0 - exPar4Z p 0) -
          (exPar4Z q 0 - exPar4Z p 0) * (exPar4Z m 2 - exPar4Z p 2) = 0 := by
        rw [hm2, hm0]; push_cast; ring
      exact_mod_cast hr
    · apply h
      have hr : ((exPar4Z q 0 - exPar4Z p 0 : ℤ) : ℝ) * (exPar4Z m 1 - exPar4Z p 1) -
          (exPar4Z q 1 - exPar4Z p 1) * (exPar4Z m 0 - exPar4Z p 0) = 0 := by
        rw [hm0, hm1]; push_cast; ring
      exact_mod_cast hr
  have hinj : Function.Injective exParLab4 := by decide
  have hR : Split.StrictRimN exPar4 w₀ exParLab4 := by
    intro p i hp1 hp2
    rcases four_cases i with rfl | rfl | rfl | rfl <;>
      (try rw [show (3 + 1 : ZMod 4) = 0 from rfl] at hp2 ⊢) <;>
      (try rw [show (2 + 1 : ZMod 4) = 3 from rfl] at hp2 ⊢) <;>
      (try rw [show (1 + 1 : ZMod 4) = 2 from rfl] at hp2 ⊢) <;>
      (try rw [show (0 + 1 : ZMod 4) = 1 from rfl] at hp2 ⊢) <;>
      fin_cases p <;>
      simp_all [exParLab4, exPar4, exPar4Z, w₀, Split.det3, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
      try norm_num
  refine edgePlaneAny_of_strictRim4_par0 exPar4 hseg hx exParLab4 hinj w₀ hR 1 1
    one_pos one_pos (by norm_num) ?_ ?_
  · ext i; fin_cases i <;> simp [exParLab4, exPar4, exPar4Z] <;> norm_num
  · ext i; fin_cases i <;> (simp [exParLab4, exPar4, exPar4Z, cross]; try norm_num)

end Minimality.T24.EPQP
