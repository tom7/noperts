module

public import Minimality.Type08S.C2K16E

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

theorem k28l2b_alg {α1 β1 pp s qq rr qr mp mr : ℝ} (hα1 : 1 < α1) (hβ1 : 1 < β1)
    (hq : qr < qq) (hr : qr < rr) (hK : 0 < qq * rr - qr ^ 2)
    (hrel : α1 * s * (qq + rr - 2 * qr) = -(β1 - 1) * (qq * rr - qr ^ 2))
    (hmp : mp = (1 - α1) * pp - β1 * s) (hmr : mr = (1 - α1) * s - β1 * qr)
    (hD : (1 - α1) * mp - β1 * mr ≤ 0)
    (hB : α1 * mp + (β1 - 1) * mr ≤ 0)
    (hBs : α1 * mp + (β1 - 1) * mr ≠ 0)
    (hne : mp ≠ 0 ∨ mr ≠ 0) :
    s < 0 ∧ mp < 0 ∧ 0 < mr ∧ α1 * mp + (β1 - 1) * mr < 0 ∧ 0 < -mp * rr + mr * s := by
  have hN : 0 < qq + rr - 2 * qr := by linarith
  have hs : s < 0 := by
    by_contra hn; push Not at hn
    have h1 : 0 ≤ α1 * s * (qq + rr - 2 * qr) := mul_nonneg (mul_nonneg (by linarith) hn) hN.le
    have h2 : 0 < (β1 - 1) * (qq * rr - qr ^ 2) := mul_pos (by linarith) hK
    linarith
  have a1 : 0 < α1 - 1 := by linarith
  have b1 : 0 < β1 - 1 := by linarith
  have h5 : 0 ≤ β1 * mr + (α1 - 1) * mp := by linarith
  have h6 : 0 ≤ -(α1 * mp + (β1 - 1) * mr) := by linarith
  have ht0 : 0 ≤ -mp := by
    by_contra hn; push Not at hn
    have : 0 ≤ (-mp) * (α1 + β1 - 1) := by
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ β1) h6, mul_nonneg b1.le h5]
    nlinarith
  have hmp0 : mp < 0 := by
    rcases ht0.lt_or_eq with h | h
    · linarith
    · exfalso
      have hm0 : mp = 0 := by linarith
      have hmr0 : mr = 0 := by
        rw [hm0] at h5 h6
        have : mr ≤ 0 := by nlinarith
        have : 0 ≤ mr := by nlinarith
        linarith
      rcases hne with h' | h' <;> contradiction
  have hmr0 : 0 < mr := by nlinarith
  have hBlt : α1 * mp + (β1 - 1) * mr < 0 := lt_of_le_of_ne hB hBs
  refine ⟨hs, hmp0, hmr0, hBlt, ?_⟩
  have hX : 0 < (β1 - 1) * rr + α1 * s := by
    have e : ((β1 - 1) * rr + α1 * s) * (qq + rr - 2 * qr) = (β1 - 1) * (rr - qr) ^ 2 := by
      linear_combination hrel
    have : 0 < ((β1 - 1) * rr + α1 * s) * (qq + rr - 2 * qr) := by
      rw [e]; exact mul_pos b1 (pow_pos (by linarith) 2)
    by_contra hn; push Not at hn
    nlinarith
  have ht : 0 < -mp := by linarith
  have key : (β1 - 1) * (-mp * rr + mr * s) ≥ (-mp) * ((β1 - 1) * rr + α1 * s) := by
    nlinarith [mul_nonneg (neg_nonneg.2 hs.le) h6, mul_pos ht b1]
  have : 0 < (β1 - 1) * (-mp * rr + mr * s) := by
    have := mul_pos ht hX; linarith
  by_contra hn; push Not at hn
  nlinarith

end C2
end Type08Sp
end Minimality
