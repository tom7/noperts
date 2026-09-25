import Noperthedron.BalancedSupport.AxisFree

open scoped RealInnerProductSpace

theorem sphere_triangle_cover
    (p1 p2 p3 v : ℝ³) (c : ℝ)
    (hdot1 : c ≤ inner ℝ p1 v)
    (hdot2 : c ≤ inner ℝ p2 v)
    (hdot3 : c ≤ inner ℝ p3 v)
    (hc : 0 ≤ c)
    {a : ℝ³}
    (α1 α2 α3 : ℝ) (hα1 : 0 ≤ α1) (hα2 : 0 ≤ α2) (hα3 : 0 ≤ α3)
    (ha_decomp : a = α1 • p1 + α2 • p2 + α3 • p3)
    (h_sum : 1 ≤ α1 + α2 + α3) :
    c ≤ inner ℝ a v := by
  have hav : inner ℝ a v = α1 * inner ℝ p1 v + α2 * inner ℝ p2 v + α3 * inner ℝ p3 v := by
    rw [ha_decomp]
    simp only [inner_add_left, inner_smul_left, starRingEnd_apply, star_trivial]
  have h1 : α1 * c ≤ α1 * inner ℝ p1 v := mul_le_mul_of_nonneg_left hdot1 hα1
  have h2 : α2 * c ≤ α2 * inner ℝ p2 v := mul_le_mul_of_nonneg_left hdot2 hα2
  have h3 : α3 * c ≤ α3 * inner ℝ p3 v := mul_le_mul_of_nonneg_left hdot3 hα3
  have h4 : c ≤ (α1 + α2 + α3) * c := by
    have := mul_le_mul_of_nonneg_right h_sum hc
    linarith
  linarith

theorem unit_sum_ge_one
    (p1 p2 p3 : ℝ³)
    (hp1 : ‖p1‖ ≤ 1) (hp2 : ‖p2‖ ≤ 1) (hp3 : ‖p3‖ ≤ 1)
    {a : ℝ³} (ha : 1 ≤ ‖a‖)
    (α1 α2 α3 : ℝ) (hα1 : 0 ≤ α1) (hα2 : 0 ≤ α2) (hα3 : 0 ≤ α3)
    (ha_decomp : a = α1 • p1 + α2 • p2 + α3 • p3) :
    1 ≤ α1 + α2 + α3 := by
  have h_norm : ‖a‖ ≤ α1 * ‖p1‖ + α2 * ‖p2‖ + α3 * ‖p3‖ := by
    rw [ha_decomp]
    have h1 := norm_add_le (α1 • p1 + α2 • p2) (α3 • p3)
    have h2 := norm_add_le (α1 • p1) (α2 • p2)
    rw [norm_smul, norm_smul] at h2
    rw [norm_smul] at h1
    rw [Real.norm_of_nonneg hα1, Real.norm_of_nonneg hα2] at h2
    rw [Real.norm_of_nonneg hα3] at h1
    linarith
  have h_le : α1 * ‖p1‖ + α2 * ‖p2‖ + α3 * ‖p3‖ ≤ α1 + α2 + α3 := by
    have h1 : α1 * ‖p1‖ ≤ α1 * 1 := mul_le_mul_of_nonneg_left hp1 hα1
    have h2 : α2 * ‖p2‖ ≤ α2 * 1 := mul_le_mul_of_nonneg_left hp2 hα2
    have h3 : α3 * ‖p3‖ ≤ α3 * 1 := mul_le_mul_of_nonneg_left hp3 hα3
    linarith
  linarith

theorem cone_axis_cover
    (p1 p2 p3 v : ℝ³) (c : ℝ)
    (hp1 : ‖p1‖ ≤ 1) (hp2 : ‖p2‖ ≤ 1) (hp3 : ‖p3‖ ≤ 1)
    (hdot1 : c ≤ inner ℝ p1 v)
    (hdot2 : c ≤ inner ℝ p2 v)
    (hdot3 : c ≤ inner ℝ p3 v)
    (hc : 0 ≤ c)
    {a : ℝ³} (ha : ‖a‖ = 1)
    (α1 α2 α3 : ℝ) (hα1 : 0 ≤ α1) (hα2 : 0 ≤ α2) (hα3 : 0 ≤ α3)
    (ha_decomp : a = α1 • p1 + α2 • p2 + α3 • p3) :
    c ≤ inner ℝ a v := by
  have ha1 : 1 ≤ ‖a‖ := by rw [ha]
  have h_sum := unit_sum_ge_one p1 p2 p3 hp1 hp2 hp3 ha1 α1 α2 α3 hα1 hα2 hα3 ha_decomp
  exact sphere_triangle_cover p1 p2 p3 v c hdot1 hdot2 hdot3 hc α1 α2 α3 hα1 hα2 hα3 ha_decomp h_sum
