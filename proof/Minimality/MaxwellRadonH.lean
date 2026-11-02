module

public import Minimality.MaxwellRadonG

@[expose] public section


namespace Minimality.MRB

open Real Finset

/-- A crown needs four indices, so loads with at most three distinct normals are level. -/
theorem mrb_level_of_le_three (r : ℕ) (hr : 2 ≤ r) (hr3 : r ≤ 3) (θ L z : ℕ → ℝ)
    (hθ : ∀ i j, i < j → j < r → θ i < θ j)
    (hwin : θ (r - 1) < θ 0 + 2 * π)
    (hL : ∀ k, k < r → 0 < L k)
    (hF1 : ∑ k ∈ Finset.range r, L k * cos (θ k) = 0)
    (hF2 : ∑ k ∈ Finset.range r, L k * sin (θ k) = 0)
    (hM1 : ∑ k ∈ Finset.range r, z k * (L k * cos (θ k)) = 0)
    (hM2 : ∑ k ∈ Finset.range r, z k * (L k * sin (θ k)) = 0) :
    ∀ k, k < r → z k = z 0 := by
  rcases mrb_main r hr θ L z hθ hwin hL hF1 hF2 hM1 hM2 with h | ⟨a, b, c, d, hab, hbc, hcd, hd, _⟩
  · exact h
  · omega

/-- A crown-free load is level (restatement: no alternating quartet of `δ`). -/
theorem mrb_level_of_no_crown (r : ℕ) (hr : 2 ≤ r) (θ L z : ℕ → ℝ)
    (hθ : ∀ i j, i < j → j < r → θ i < θ j)
    (hwin : θ (r - 1) < θ 0 + 2 * π)
    (hL : ∀ k, k < r → 0 < L k)
    (hF1 : ∑ k ∈ Finset.range r, L k * cos (θ k) = 0)
    (hF2 : ∑ k ∈ Finset.range r, L k * sin (θ k) = 0)
    (hM1 : ∑ k ∈ Finset.range r, z k * (L k * cos (θ k)) = 0)
    (hM2 : ∑ k ∈ Finset.range r, z k * (L k * sin (θ k)) = 0)
    (hnc : ¬ mrb_crown r (fun k => z k - z ((k + 1) % r))) :
    ∀ k, k < r → z k = z 0 := by
  rcases mrb_main r hr θ L z hθ hwin hL hF1 hF2 hM1 hM2 with h | h
  · exact h
  · exact absurd h hnc

end Minimality.MRB
