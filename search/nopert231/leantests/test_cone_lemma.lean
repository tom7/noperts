import Noperthedron.Nopert229.AtlasProjectiveAnnularCertificate

open Noperthedron.Nopert229
open Noperthedron.Nopert229.AtlasProjectiveLocalCertificate

/-- Triangle inequality cone containment lemma:
If `‖a‖ = 1`, `‖u‖ = 1`, `‖v‖ = 1`, and `inner a u ≥ c_u`,
then `inner a v ≥ c_v`. -/
theorem inner_ge_of_triangle_inequality
    (a u v : ℝ³)
    (ha : ‖a‖ = 1) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (c_u c_v μ : ℝ)
    (h_cu : c_u ≤ inner ℝ a u)
    (h_mu : inner ℝ u v = μ)
    (h_pos : 0 ≤ 2 * c_u + 2 * μ - 2 - 2 * c_v)
    (h_poly : 4 * (2 - 2 * c_u) * (2 - 2 * μ) ≤ (2 * c_u + 2 * μ - 2 - 2 * c_v) ^ 2) :
    c_v ≤ inner ℝ a v := by
  sorry
