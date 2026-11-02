module

public import Mathlib

@[expose] public section


namespace Minimality.MRB

open Real Finset

/-- Sum of three sines over a cyclically ordered triple is positive. -/
theorem mrb_tri {x y z : ℝ} (hxy : x < y) (hyz : y < z) (hz : z - x < 2 * π) :
    0 < sin (y - x) + sin (z - y) + sin (x - z) := by
  set u := (y - x) / 2 with hu
  set v := (z - y) / 2 with hv
  have hu0 : 0 < u := by rw [hu]; linarith
  have hv0 : 0 < v := by rw [hv]; linarith
  have huv : u + v < π := by rw [hu, hv]; linarith
  have h1 : y - x = 2 * u := by rw [hu]; ring
  have h2 : z - y = 2 * v := by rw [hv]; ring
  have h3 : x - z = -(2 * u + 2 * v) := by rw [hu, hv]; ring
  have key : sin (y - x) + sin (z - y) + sin (x - z) = 4 * (sin u * sin v * sin (u + v)) := by
    rw [h1, h2, h3, sin_neg, show 2 * u + 2 * v = 2 * (u + v) by ring]
    simp only [sin_two_mul, sin_add, cos_add]
    have hu2 := sin_sq_add_cos_sq u
    have hv2 := sin_sq_add_cos_sq v
    linear_combination (-2 * sin u * cos u) * hv2 + (-2 * sin v * cos v) * hu2
  rw [key]
  have a1 : 0 < sin u := sin_pos_of_pos_of_lt_pi hu0 (by linarith)
  have a2 : 0 < sin v := sin_pos_of_pos_of_lt_pi hv0 (by linarith)
  have a3 : 0 < sin (u + v) := sin_pos_of_pos_of_lt_pi (by linarith) huv
  positivity

end Minimality.MRB
