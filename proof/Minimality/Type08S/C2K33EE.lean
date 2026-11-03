module

public import Minimality.Type08S.C2K33ED

@[expose] public section

set_option maxHeartbeats 1000000
set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace

namespace Minimality
namespace Type08Sp
open C2

/-- Common L2 data: the Gram expansion of the view `U`. -/
theorem k32e_U {a b c d : ℝ³} {α1 β1 : ℝ} :
    k28l2aU0 a b c d α1 β1 =
      ((1 - α1) * ⟪a - d, b - d⟫ - β1 * ⟪b - d, c - d⟫) • (a - d) + (0:ℝ) • (b - d) +
        (-((1 - α1) * ⟪a - d, a - d⟫ - β1 * ⟪a - d, b - d⟫)) • (c - d) := by
  unfold k28l2aU0; module

theorem k32e_l2x4 {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (hH1 : K6mH1Left a a' b b' c c' d α1 β1 β6 γ6)
    (hL2 : K17b2L2Left a a' b b' c c' d α1 β1 β6 γ6)
    (hX3 : ⟪a - c', a - b'⟫ ≤ 0) (hX4 : ⟪c' - a, b' - c⟫ = 0) :
    0 ≤ ⟪a - a', k28l2aU0 a b c d α1 β1⟫ := by
  obtain ⟨hPR, hpp, hqq, hrr⟩ := k32e_facts hC hM
  have hα : 1 < α1 := hH1.1.1
  have hβ : 1 < β1 := hH1.1.2.1
  have hH : 0 ≤ ⟪c' - a', b' - c⟫ := hL2.1.2.2.1
  obtain ⟨hdet, hc', hb', ha', -, -, -, -, hγ6, -⟩ := hC
  have e1 : c' - a' = α1 • (a - d) + (β1 - β6) • (b - d) + (-γ6) • (c - d) := by
    rw [hc', ha']; module
  have e2 : b' - c = α1 • (a - d) + (0:ℝ) • (b - d) + (β1 - 1) • (c - d) := by rw [hb']; module
  have e5 : c' - a = (α1 - 1) • (a - d) + β1 • (b - d) + (0:ℝ) • (c - d) := by rw [hc']; module
  have e6 : a - c' = (1 - α1) • (a - d) + (-β1) • (b - d) + (0:ℝ) • (c - d) := by rw [hc']; module
  have e7 : a - b' = (1 - α1) • (a - d) + (0:ℝ) • (b - d) + (-β1) • (c - d) := by rw [hb']; module
  have e8 : a - a' = (1:ℝ) • (a - d) + (-β6) • (b - d) + (-γ6) • (c - d) := by rw [ha']; module
  rw [e1, e2] at hH
  rw [e6, e7] at hX3
  rw [e5, e2] at hX4
  rw [e8, k32e_U, k32e_ip _ _ _ hPR]
  rw [k32e_ip _ _ _ hPR] at hH hX3 hX4
  have hW : 0 < ⟪b - d, b - d⟫ + ⟪c - d, c - d⟫ - 2 * ⟪b - d, c - d⟫ := by linarith
  have hid := k32e_core_x4 α1 β1 β6 γ6 _ _ _ _ _ hα hβ
    (by have := hrel.1; linarith) hW hX4
  have : 0 ≤ -(k32e_G ⟪a - d, a - d⟫ ⟪a - d, b - d⟫ ⟪b - d, b - d⟫ ⟪b - d, c - d⟫ ⟪c - d, c - d⟫
      (1 - α1) (-β1) 0 (1 - α1) 0 (-β1)) *
      k32e_G ⟪a - d, a - d⟫ ⟪a - d, b - d⟫ ⟪b - d, b - d⟫ ⟪b - d, c - d⟫ ⟪c - d, c - d⟫
      α1 (β1 - β6) (-γ6) α1 0 (β1 - 1) :=
    mul_nonneg (neg_nonneg.2 hX3) hH
  rw [← hid] at this
  by_contra hn; rw [not_le] at hn
  nlinarith [mul_pos (by linarith : (0:ℝ) < α1 + β1 - 1) (neg_pos.2 hn)]

theorem k32e_l2x3 {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (hH1 : K6mH1Left a a' b b' c c' d α1 β1 β6 γ6)
    (hL2 : K17b2L2Left a a' b b' c c' d α1 β1 β6 γ6)
    (hX3 : ⟪a - c', a - b'⟫ = 0) (hpos : 0 < ⟪c - a', a - b'⟫) :
    (α1 + β1 - 1) * (⟪c, k28l2aU0 a b c d α1 β1⟫ - ⟪a', k28l2aU0 a b c d α1 β1⟫) =
        -(⟪c' - a, b' - c⟫ * ⟪c - a', a - b'⟫) ∧
      ⟪c, k28l2aU0 a b c d α1 β1⟫ ≤ ⟪a', k28l2aU0 a b c d α1 β1⟫ ∧
      (0 < ⟪c' - a, b' - c⟫ → ⟪c, k28l2aU0 a b c d α1 β1⟫ < ⟪a', k28l2aU0 a b c d α1 β1⟫) := by
  obtain ⟨hPR, hpp, hqq, hrr⟩ := k32e_facts hC hM
  have hα : 1 < α1 := hH1.1.1
  have hβ : 1 < β1 := hH1.1.2.1
  have hX4 : 0 ≤ ⟪c' - a, b' - c⟫ := hL2.1.2.1
  obtain ⟨hdet, hc', hb', ha', -, -, -, -, hγ6, -⟩ := hC
  have e2 : b' - c = α1 • (a - d) + (0:ℝ) • (b - d) + (β1 - 1) • (c - d) := by rw [hb']; module
  have e5 : c' - a = (α1 - 1) • (a - d) + β1 • (b - d) + (0:ℝ) • (c - d) := by rw [hc']; module
  have e6 : a - c' = (1 - α1) • (a - d) + (-β1) • (b - d) + (0:ℝ) • (c - d) := by rw [hc']; module
  have e7 : a - b' = (1 - α1) • (a - d) + (0:ℝ) • (b - d) + (-β1) • (c - d) := by rw [hb']; module
  have e9 : c - a' = (0:ℝ) • (a - d) + (-β6) • (b - d) + (1 - γ6) • (c - d) := by rw [ha']; module
  have hz : ⟪c, k28l2aU0 a b c d α1 β1⟫ - ⟪a', k28l2aU0 a b c d α1 β1⟫ =
      ⟪c - a', k28l2aU0 a b c d α1 β1⟫ := (inner_sub_left _ _ _).symm
  rw [hz]
  have hX3' := hX3
  rw [e6, e7] at hX3'
  rw [k32e_ip _ _ _ hPR] at hX3'
  have hW : 0 < ⟪b - d, b - d⟫ + ⟪c - d, c - d⟫ - 2 * ⟪b - d, c - d⟫ := by linarith
  have hid := k32e_core_x3 α1 β1 β6 γ6 _ _ _ _ _ hα hβ
    (by have := hrel.1; linarith) hW hX3'
  have key : (α1 + β1 - 1) * ⟪c - a', k28l2aU0 a b c d α1 β1⟫ =
      -(⟪c' - a, b' - c⟫ * ⟪c - a', a - b'⟫) := by
    rw [e5, e2, e9, e7, k32e_U]
    simp only [k32e_ip (a - d) (b - d) (c - d) hPR]
    rw [neg_mul] at hid; exact hid
  have hpos' : 0 < α1 + β1 - 1 := by linarith
  refine ⟨key, ?_, fun h4 => ?_⟩
  · by_contra hn; rw [not_le] at hn
    nlinarith [mul_nonneg hX4 hpos.le, mul_pos hpos' (sub_pos.2 hn)]
  · by_contra hn; rw [not_lt] at hn
    nlinarith [mul_pos h4 hpos, mul_nonneg hpos'.le (sub_nonneg.2 hn)]

end Type08Sp
end Minimality
