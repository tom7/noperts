module

public import Minimality.Type08S.C2K46ZA

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace
namespace Minimality.Type08Sp.C2

/-- Frame points of the C1 view: `P = (a-d)/β1`, `Q = (c'-a)/β1`, `R = (c-d) + (ν/β1)(a-d)`. -/
theorem k86_pts_c1 {a a' b b' c c' d R : ℝ³} {α1 β1 β6 γ6 ν : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hβ : 1 < β1)
    (hR : R = (c - d) + (ν / β1) • (a - d)) :
    det3 (β1⁻¹ • (a - d)) (β1⁻¹ • (c' - a)) R ≠ 0 ∧
    fpoint (β1⁻¹ • (a - d)) (β1⁻¹ • (c' - a)) R d (0, 0, 0) = d ∧
    fpoint (β1⁻¹ • (a - d)) (β1⁻¹ • (c' - a)) R d (β1, 0, 0) = a ∧
    fpoint (β1⁻¹ • (a - d)) (β1⁻¹ • (c' - a)) R d (1 - α1, 1, 0) = b ∧
    fpoint (β1⁻¹ • (a - d)) (β1⁻¹ • (c' - a)) R d (-ν, 0, 1) = c ∧
    fpoint (β1⁻¹ • (a - d)) (β1⁻¹ • (c' - a)) R d (β6 * (1 - α1) - γ6 * ν, β6, γ6) = a' ∧
    fpoint (β1⁻¹ • (a - d)) (β1⁻¹ • (c' - a)) R d (β1 * (α1 - ν), 0, β1) = b' ∧
    fpoint (β1⁻¹ • (a - d)) (β1⁻¹ • (c' - a)) R d (β1, β1, 0) = c' := by
  obtain ⟨hdet, hc', hb', ha', -⟩ := hC
  have hb0 : β1 ≠ 0 := by linarith
  have hca : c' - a = (α1 - 1) • (a - d) + β1 • (b - d) := by rw [hc']; module
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e : det3 (β1⁻¹ • (a - d)) (β1⁻¹ • (c' - a)) R = β1⁻¹ * det3 (a - d) (b - d) (c - d) := by
      rw [hca, hR]
      simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      field_simp; ring
    rw [e]; exact mul_ne_zero (inv_ne_zero hb0) hdet
  · rw [k17f_fp]; module
  · rw [k17f_fp]; match_scalars <;> (try field_simp) <;> (try ring)
  · rw [k17f_fp, hca, hR]; match_scalars <;> (try field_simp) <;> (try ring)
  · rw [k17f_fp, hR]; match_scalars <;> (try field_simp) <;> (try ring)
  · rw [k17f_fp, hca, hR, ha']; match_scalars <;> (try field_simp) <;> (try ring)
  · rw [k17f_fp, hca, hR, hb']; match_scalars <;> (try field_simp) <;> (try ring)
  · rw [k17f_fp, hc']; match_scalars <;> (try field_simp) <;> (try ring)
end Minimality.Type08Sp.C2
