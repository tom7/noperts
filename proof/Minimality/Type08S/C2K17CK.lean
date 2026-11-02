module

public import Minimality.Type08S.C2K17CJ

@[expose] public section


/-!
# K17C / P3K: S3.6a: `γ6 ≤ 1` and not `K17cBad` closes the slice.
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

theorem k17c_eps (x y : ℝ) (hx : 0 < x) : ∃ ε : ℝ, 0 < ε ∧ ε * |y| ≤ x := by
  refine ⟨x / (|y| + 1), by positivity, ?_⟩
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith [abs_nonneg y]

theorem k17c_lin_pos {X Y ε lam : ℝ} (hε : 0 < ε) (h0 : 0 < lam) (h1 : lam < 1) (h : ε * |Y| ≤ X) :
    0 ≤ X + lam * ε * Y := by
  have h2 := neg_abs_le Y
  have h3 := abs_nonneg Y
  have a : 0 ≤ lam * ε * (Y + |Y|) := mul_nonneg (mul_pos h0 hε).le (by linarith)
  have b : 0 ≤ (1 - lam) * ε * |Y| := mul_nonneg (mul_nonneg (sub_pos.2 h1).le hε.le) h3
  nlinarith

set_option maxHeartbeats 1600000 in
theorem k17c_s36a_hasLexCell {a a' b b' c c' d : ℝ³} {α1 β6 γ6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + (1 : ℝ) • (b - d)) (hb' : b' = d + α1 • (a - d) + (1 : ℝ) • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d))
    (hα1 : 1 ≤ α1) (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (h3 : 1 < β6 + γ6) (hγ61 : γ6 ≤ 1)
    (hM : K6sM a a' b b' c c' d) (hm0 : ⟪a - d, b - d⟫ = 0)
    (hnb : ¬ K17cBad β6 γ6 ⟪b - d, b - d⟫ ⟪b - d, c - d⟫ ⟪c - d, c - d⟫) :
    HasLexCell (V8 a a' b b' c c' d) := by
  have hc3 := k17c_c3 hβ6 hγ6 hγ61 h3
  unfold K17cBad at hnb
  set qq := ⟪b - d, b - d⟫
  set qr := ⟪b - d, c - d⟫
  set rr := ⟪c - d, c - d⟫
  have key : 0 < k17cG3 β6 γ6 qq qr rr ∨ 0 < k17cG4 β6 γ6 qq qr rr ∨ k17cA3 β6 γ6 qq qr < 0 ∨
      k17cA4 β6 γ6 qq qr < 0 := by
    by_contra hcon
    push Not at hcon
    exact hnb ⟨hcon.1, hcon.2.1, hcon.2.2.1, hcon.2.2.2⟩
  have W := fun {l1 m1 l2 m2 : ℝ} (hl1 : 0 ≤ l1) (hm1 : 0 ≤ m1) (hl2 : 0 ≤ l2) (hm2 : 0 ≤ m2)
    (hl : 0 < l1 + l2) (hm : 0 < m1 + m2) (hlm : l1 * m2 - m1 * l2 ≠ 0) hmet =>
    k17c_A_weights hdet hc' hb' ha' hα1 hβ6 hγ6 h3 hγ61 hM hm0 hl1 hm1 hl2 hm2 hl hm hlm hmet
  rcases key with h | h | h | h
  · obtain ⟨ε, hε, hε2⟩ := k17c_eps _ (k17cG4 β6 γ6 qq qr rr) h
    refine W (l1 := 1) (m1 := 0) (l2 := 1) (m2 := ε) (by norm_num) le_rfl (by norm_num) hε.le (by norm_num)
      (by linarith) (by simpa using hε.ne') ?_
    intro lam h0 h1
    right
    have := k17c_lin_pos hε h0 h1 hε2
    nlinarith
  · obtain ⟨ε, hε, hε2⟩ := k17c_eps _ (k17cG3 β6 γ6 qq qr rr) h
    refine W (l1 := 0) (m1 := 1) (l2 := ε) (m2 := 1) le_rfl (by norm_num) hε.le (by norm_num)
      (by linarith) (by norm_num) (by simpa using hε.ne') ?_
    intro lam h0 h1
    right
    have := k17c_lin_pos hε h0 h1 hε2
    nlinarith
  · obtain ⟨ε, hε, hε2⟩ := k17c_eps _ (k17cA4 β6 γ6 qq qr) (neg_pos.2 h)
    refine W (l1 := 1) (m1 := 0) (l2 := 1) (m2 := ε) (by norm_num) le_rfl (by norm_num) hε.le (by norm_num)
      (by linarith) (by simpa using hε.ne') ?_
    intro lam h0 h1
    left
    have := k17c_lin_pos (X := -k17cA3 β6 γ6 qq qr) (Y := -k17cA4 β6 γ6 qq qr) hε h0 h1 (by rwa [abs_neg])
    nlinarith
  · obtain ⟨ε, hε, hε2⟩ := k17c_eps _ (k17cA3 β6 γ6 qq qr) (neg_pos.2 h)
    refine W (l1 := 0) (m1 := 1) (l2 := ε) (m2 := 1) le_rfl (by norm_num) hε.le (by norm_num)
      (by linarith) (by norm_num) (by simpa using hε.ne') ?_
    intro lam h0 h1
    left
    have := k17c_lin_pos (X := -k17cA4 β6 γ6 qq qr) (Y := -k17cA3 β6 γ6 qq qr) hε h0 h1 (by rwa [abs_neg])
    nlinarith

end C2
end Type08Sp
end Minimality
