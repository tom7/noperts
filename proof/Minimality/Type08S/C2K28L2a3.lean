import Minimality.Type08S.C2K28L2a2
import Minimality.Type08S.C2K16E
import Minimality.Type08S.C2K6HF

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- Pure Gram algebra of leaf A.  `mp = (1-α1)pp - β1 s`, `mr = (1-α1)s - β1 qr`, `μ = -mp`. -/
theorem k28l2a_alg {α1 β1 pp s qr qq rr : ℝ} (hα1 : 1 < α1) (hβ1 : 1 < β1) (hpp : 0 < pp)
    (hqq : qr < qq) (hrr : qr < rr) (hD : 0 < qq * rr - qr ^ 2)
    (hrel : α1 * s * (qq + rr - 2 * qr) = -(β1 - 1) * (qq * rr - qr ^ 2))
    (hX3 : (α1 - 1) ^ 2 * pp + 2 * β1 * (α1 - 1) * s + β1 ^ 2 * qr < 0)
    (hX4 : 0 < (α1 - 1) * α1 * pp + ((α1 - 1) * (β1 - 1) + α1 * β1) * s + β1 * (β1 - 1) * qr) :
    0 < -((1 - α1) * pp - β1 * s) ∧ 0 < (1 - α1) * s - β1 * qr ∧
    α1 - 1 < β1 * (((1 - α1) * s - β1 * qr) / (-((1 - α1) * pp - β1 * s))) ∧
    (β1 - 1) * (((1 - α1) * s - β1 * qr) / (-((1 - α1) * pp - β1 * s))) < α1 ∧
    0 < pp * ((1 - α1) * s - β1 * qr) + (-((1 - α1) * pp - β1 * s)) * s ∧
    0 < s * ((1 - α1) * s - β1 * qr) + (-((1 - α1) * pp - β1 * s)) * rr := by
  have hT : 0 < α1 + β1 - 1 := by linarith
  have hB : 0 < β1 - 1 := by linarith
  have hA : 0 < α1 - 1 := by linarith
  have hW : 0 < qq + rr - 2 * qr := by linarith
  have hs : s < 0 := by
    by_contra hn; push_neg at hn
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ α1) hn) hW.le, mul_pos hB hD]
  obtain ⟨μ, hμd⟩ : ∃ μ, μ = -((1 - α1) * pp - β1 * s) := ⟨_, rfl⟩
  obtain ⟨mr, hmrd⟩ : ∃ mr, mr = (1 - α1) * s - β1 * qr := ⟨_, rfl⟩
  have hμ : 0 < μ := by
    have h : (α1 + β1 - 1) * μ = β1 * ((α1 - 1) * α1 * pp + ((α1 - 1) * (β1 - 1) + α1 * β1) * s + β1 * (β1 - 1) * qr)
        + (β1 - 1) * (-((α1 - 1) ^ 2 * pp + 2 * β1 * (α1 - 1) * s + β1 ^ 2 * qr)) := by
      rw [hμd]; ring
    have : 0 < (α1 + β1 - 1) * μ := by
      rw [h]; nlinarith [mul_pos (by linarith : (0:ℝ) < β1) hX4, mul_pos hB (neg_pos.2 hX3)]
    exact pos_of_mul_pos_right this hT.le |> fun h => by nlinarith
  have hmr : β1 * mr = -((α1 - 1) ^ 2 * pp + 2 * β1 * (α1 - 1) * s + β1 ^ 2 * qr) + (α1 - 1) * μ := by
    rw [hmrd, hμd]; ring
  have hmr0 : 0 < mr := by
    have : 0 < β1 * mr := by rw [hmr]; nlinarith [neg_pos.2 hX3, mul_pos hA hμ]
    nlinarith
  have hZp : β1 * (pp * mr + μ * s) = pp * (-((α1 - 1) ^ 2 * pp + 2 * β1 * (α1 - 1) * s + β1 ^ 2 * qr)) + μ ^ 2 := by
    rw [hmrd, hμd]; ring
  have hk : 0 < (β1 - 1) * rr + α1 * s := by
    have h : (qq + rr - 2 * qr) * ((β1 - 1) * rr + α1 * s) = (β1 - 1) * (rr - qr) ^ 2 := by
      linear_combination hrel
    have : 0 < (qq + rr - 2 * qr) * ((β1 - 1) * rr + α1 * s) := by
      rw [h]; exact mul_pos hB (pow_pos (by linarith) 2)
    exact pos_of_mul_pos_right this hW.le |> fun h => by nlinarith
  have hX4' : (α1 - 1) * α1 * pp + ((α1 - 1) * (β1 - 1) + α1 * β1) * s + β1 * (β1 - 1) * qr = α1 * μ - (β1 - 1) * mr := by
    rw [hmrd, hμd]; ring
  have hZr : (β1 - 1) * (s * mr + μ * rr) = (-s) * ((α1 - 1) * α1 * pp + ((α1 - 1) * (β1 - 1) + α1 * β1) * s + β1 * (β1 - 1) * qr) + μ * ((β1 - 1) * rr + α1 * s) := by
    rw [hmrd, hμd]; ring
  rw [← hμd, ← hmrd]
  refine ⟨hμ, hmr0, ?_, ?_, ?_, ?_⟩
  · rw [← mul_div_assoc, lt_div_iff₀ hμ]; nlinarith [neg_pos.2 hX3]
  · rw [← mul_div_assoc, div_lt_iff₀ hμ]; nlinarith
  · have : 0 < β1 * (pp * mr + μ * s) := by
      rw [hZp]; nlinarith [mul_pos hpp (neg_pos.2 hX3), pow_pos hμ 2]
    nlinarith
  · have : 0 < (β1 - 1) * (s * mr + μ * rr) := by
      rw [hZr]; exact add_pos (mul_pos (neg_pos.2 hs) hX4) (mul_pos hμ hk)
    exact (mul_pos_iff_of_pos_left hB).1 this

end C2
end Type08Sp
end Minimality
