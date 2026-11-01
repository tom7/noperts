module

public import Minimality.Type08S.C2K5FI

@[expose] public section


set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- Box E, pair (b', b) of E1: real contradiction.  Depths (rel. `d`): `a = x`, `b' = α4 x + γ4 y`,
`a' = -t m x + y - t k s`, `b = -m x - k s`.  Here `hrel : (γ4-1)(m+k) = α4(1-k)` (κ_a). -/
theorem k5f_E1_real {m k t α4 γ4 x y s : ℝ} (hm : 0 < m) (hk : 0 < k) (hk1 : k < 1) (ht : 0 < t) (ht1 : t < 1)
    (hα4 : 1 < α4) (hγ4 : 1 < γ4) (hrel : (γ4 - 1) * (m + k) = α4 * (1 - k)) (hs : 0 < s)
    (hb : -m * x - k * s ≥ 0)
    (hζ : -t * m * x + y - t * k * s < -m * x - k * s)
    (hd : α4 * x + γ4 * y ≥ -t * m * x + y - t * k * s) : False := by
  have hG : 0 < γ4 - 1 := by linarith
  have hα4p : 0 < α4 := by linarith
  have hGm : m * (γ4 - 1) < α4 := by nlinarith [mul_pos hk hG]
  obtain ⟨W, hW⟩ : ∃ W, W = -(m * x + k * s) := ⟨_, rfl⟩
  have hW0 : 0 ≤ W := by rw [hW]; linarith
  have e1 : m * (γ4 - 1) * y ≥ (α4 + t * m) * W + α4 * k * s := by
    have := mul_le_mul_of_nonneg_left hd hm.le
    rw [hW]; nlinarith [this]
  have e2 : m * (γ4 - 1) * y < m * (γ4 - 1) * ((1 - t) * W) := by
    apply mul_lt_mul_of_pos_left _ (mul_pos hm hG)
    rw [hW]; nlinarith
  have e3 : m * (γ4 - 1) * ((1 - t) * W) ≤ α4 * W := by
    have : m * (γ4 - 1) * ((1 - t) * W) ≤ α4 * ((1 - t) * W) :=
      mul_le_mul_of_nonneg_right hGm.le (mul_nonneg (by linarith) hW0)
    nlinarith [mul_nonneg ht.le (mul_nonneg hα4p.le hW0), mul_nonneg hα4p.le hW0]
  nlinarith [mul_nonneg ht.le (mul_nonneg hm.le hW0), mul_pos (mul_pos hα4p hk) hs]

/-- Box E, pair (c', a') of E2: real contradiction.  `c' = x - s`. -/
theorem k5f_E2_real {m k t α4 γ4 x y s : ℝ} (hm : 0 < m) (hk : 0 < k) (hk1 : k < 1) (ht : 0 < t) (ht1 : t < 1)
    (hα4 : 1 < α4) (hγ4 : 1 < γ4) (hrel : (γ4 - 1) * (m + k) = α4 * (1 - k)) (hs : 0 < s)
    (hζ : -m * x - k * s < -t * m * x + y - t * k * s)
    (hc : x - s ≥ -m * x - k * s)
    (ha : -t * m * x + y - t * k * s ≥ α4 * x + γ4 * y) : False := by
  have hG : 0 < γ4 - 1 := by linarith
  have hα4p : 0 < α4 := by linarith
  have hGm : m * (γ4 - 1) < α4 := by nlinarith [mul_pos hk hG]
  have hx : (1 + m) * x ≥ (1 - k) * s := by nlinarith
  have hx0 : 0 < x := by
    have : 0 < (1 + m) * x := by nlinarith [mul_pos (sub_pos.2 hk1) hs]
    exact pos_of_mul_pos_right this (by linarith) |> fun h => by nlinarith
  -- M: K1 x < k (G (1-t) - t) s
  have hy : -(1 - t) * (m * x + k * s) < y := by nlinarith
  have M0 : (γ4 - 1) * (-(1 - t) * (m * x + k * s)) < (γ4 - 1) * y := mul_lt_mul_of_pos_left hy hG
  have M : (α4 + t * m - (γ4 - 1) * (1 - t) * m) * x < k * ((γ4 - 1) * (1 - t) - t) * s := by nlinarith
  have hK1 : 0 < α4 + t * m - (γ4 - 1) * (1 - t) * m := by
    nlinarith [mul_pos ht hm, mul_pos ht hα4p, mul_pos (mul_pos ht hm) hm, mul_pos hm hG, mul_pos (sub_pos.2 ht1) (mul_pos hm hG)]
  have h1 := mul_le_mul_of_nonneg_left hx hK1.le
  have h2 := mul_lt_mul_of_pos_left M (by linarith : 0 < 1 + m)
  have hr2 : (γ4 - 1) * (m + k) * ((1 - t) * s) = α4 * (1 - k) * ((1 - t) * s) := by rw [hrel]
  nlinarith [mul_pos (mul_pos ht hα4p) (mul_pos (sub_pos.2 hk1) hs), mul_pos ht (mul_pos hk hs),
    mul_pos (mul_pos ht hm) (mul_pos (sub_pos.2 hk1) hs), mul_pos (mul_pos ht hm) (mul_pos hk hs)]

theorem k5f_E1_real30 {m k x s : ℝ} (hm : 0 < m) (hk : 0 < k) (hs : 0 < s)
    (hb : 0 ≤ -m * x - k * s) (ha : 0 ≤ x) : False := by
  nlinarith [mul_nonneg hm.le ha, mul_pos hk hs]

theorem k5f_E1_real41 {m k t α4 γ4 x y s : ℝ} (hm : 0 < m) (hk : 0 < k) (ht1 : t < 1)
    (hα4 : 1 < α4) (hγ4 : 1 < γ4) (hs : 0 < s)
    (hb : -m * x - k * s ≤ 0) (ha : x ≤ 0) (hc : x ≤ α4 * x + γ4 * y)
    (hζ : -t * m * x + y - t * k * s < -m * x - k * s) : False := by
  have h1 : 0 ≤ m * x + k * s := by linarith
  have hy : y < 0 := by nlinarith [mul_nonneg (sub_pos.2 ht1).le h1]
  nlinarith [mul_nonneg (sub_pos.2 hα4).le (neg_nonneg.2 ha), mul_pos (neg_pos.2 hy) (by linarith : (0:ℝ) < γ4)]

end C2
end Type08Sp
end Minimality
