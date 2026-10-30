module

public import Minimality.Type08S.P2RKT4

@[expose] public section

set_option relaxedAutoImplicit true
/-!
# pkR / K2 / KT4: tilt tests of the face cell (orientation `Δ < 0`, cycle `(d, c, b', a)`).
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- The cycle `(d, c, b', a)` in frame coordinates. -/
def faceCycN (α γ : ℝ) : ZMod 4 → ℝ × ℝ × ℝ := quad (0, 0, 0) (0, 1, 0) (α, γ, 0) (1, 0, 0)

set_option maxHeartbeats 1600000 in
theorem faceN_cyc {D α γ lam : ℝ} (hD : D < 0) (hα : 1 < α) (hγ : 0 < γ) (hlam : 0 < lam) :
    ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      TSc D (faceCycN α γ (i + 1) - faceCycN α γ i) (faceCycN α γ j - faceCycN α γ i) (-lam, -1, 0) := by
  obtain ⟨s0, s1, s2, s3⟩ := z4_add
  have k1 := neg_pos.2 hD
  have kγ := mul_pos (neg_pos.2 hD) hγ
  have kα := mul_pos (neg_pos.2 hD) (by linarith : (0:ℝ) < α)
  have kαγ := mul_pos (neg_pos.2 hD) (by linarith : (0:ℝ) < α + γ - 1)
  intro i j h1 h2'
  rcases z4_cases i with rfl | rfl | rfl | rfl <;>
    rcases z4_cases j with rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact (h2' (by decide)).elim
    | (simp only [TSc, d3, faceCycN, s0, s1, s2, s3, quad4_0, quad4_1, quad4_2, quad4_3,
        Prod.fst_sub, Prod.snd_sub]
       left; nlinarith)

set_option maxHeartbeats 1600000 in
theorem faceN_rest {D α γ lam β1 β6 γ6 : ℝ} (hD : D < 0) (hα : 1 < α) (hγ : 0 < γ) (hlam : 0 < lam)
    (hlam2 : lam * γ < α - 1) (hβ1 : 0 < β1) (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1) :
    (∀ i : ZMod 4, TSc D (faceCycN α γ (i + 1) - faceCycN α γ i) ((0, 0, 1) - faceCycN α γ i) (-lam, -1, 0)) ∧
    (∀ i : ZMod 4, TSc D (faceCycN α γ (i + 1) - faceCycN α γ i) ((1, 0, β1) - faceCycN α γ i) (-lam, -1, 0)) ∧
    (∀ i : ZMod 4, TSc D (faceCycN α γ (i + 1) - faceCycN α γ i) ((0, γ6, β6) - faceCycN α γ i) (-lam, -1, 0)) := by
  obtain ⟨s0, s1, s2, s3⟩ := z4_add
  have k1 := neg_pos.2 hD
  have kγ := mul_pos (neg_pos.2 hD) hγ
  have kα := mul_pos (neg_pos.2 hD) (by linarith : (0:ℝ) < α)
  have kαγ := mul_pos (neg_pos.2 hD) (by linarith : (0:ℝ) < α + γ - 1)
  have kl := mul_pos (neg_pos.2 hD) hlam
  have kb1 := mul_pos (neg_pos.2 hD) hβ1
  have kg6' := mul_pos (neg_pos.2 hD) (by linarith : (0:ℝ) < 1 - γ6)
  have kA := mul_pos (neg_pos.2 hD) (by nlinarith : (0:ℝ) < (α - 1) * γ6 + γ)
  have kB := mul_pos (neg_pos.2 hD) (by nlinarith : (0:ℝ) < α * (1 - γ6))
  have kC := mul_pos (mul_pos (neg_pos.2 hD) hβ1) (by nlinarith : (0:ℝ) < α - 1 - γ * lam)
  have kD := mul_pos (mul_pos (neg_pos.2 hD) hlam) hβ6
  have kE := mul_pos (neg_pos.2 hD) hγ6
  refine ⟨?_, ?_, ?_⟩ <;> intro i <;>
  rcases z4_cases i with rfl | rfl | rfl | rfl <;>
    (simp only [TSc, d3, faceCycN, s0, s1, s2, s3, quad4_0, quad4_1, quad4_2, quad4_3,
        Prod.fst_sub, Prod.snd_sub]
     first
     | (left; nlinarith)
     | (right; refine ⟨by ring, by nlinarith⟩))

end Type08Sp
end Minimality
