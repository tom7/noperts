module

public import Minimality.Type08S.C2K6PB

@[expose] public section


set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped RealInnerProductSpace Topology
open Finset Filter
namespace Minimality
namespace Type08Sp
namespace C2

theorem k6p_leaf_N2w
    {x y R α1 β1 β6 γ6 t : ℝ} (hα1 : 0 < α1) (hβ1 : 0 < β1) (hβ6 : 0 < β6) (hγ6 : 0 < γ6)
    (hs : 1 < β6 + γ6) (hab : 1 < α1 + β1) (hcond : 0 < (α1 - 1) * (β6 + γ6) + β1) (hR : 0 < R)
    (ht1 : -β1 ≤ t) (ht2 : t ≤ 1) (hrel : α1 * x + (β1 - 1) * y = t * R)
    (hA : 0 ≤ x) (hC : α1 * x + β1 * y + β1 * R ≤ 0) (hD : 0 < x ∨ α1 * x + β1 * y + β1 * R < 0) :
    k5b_ex5 x (α1 * x + β1 * y) ((β6 + γ6) * y + β6 * R) (y + R) 0 := by
  have hg : 0 < α1 + β1 - 1 := by linarith
  have hs1 : 0 < β6 + γ6 - 1 := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · by_contra h; push Not at h; obtain ⟨h1, h2, h3, h4⟩ := h
    rcases hD with hD | hD
    · nlinarith [mul_pos hα1 hR, mul_pos hβ1 hR, mul_pos hβ6 hR, mul_pos hγ6 hR, mul_pos hα1 hβ1, mul_nonneg hα1.le hA, mul_pos hα1 hD]
    · nlinarith [mul_pos hα1 hR, mul_pos hβ1 hR, mul_pos hβ6 hR, mul_pos hγ6 hR, mul_pos hα1 hβ1, mul_nonneg hα1.le hA]
  · by_contra h; push Not at h; obtain ⟨h1, h2, h3, h4⟩ := h
    rcases hD with hD | hD
    · nlinarith [mul_pos hα1 hR, mul_pos hβ1 hR, mul_pos hβ6 hR, mul_pos hγ6 hR, mul_pos hα1 hβ1, mul_nonneg hα1.le hA, mul_pos hα1 hD]
    · nlinarith [mul_pos hα1 hR, mul_pos hβ1 hR, mul_pos hβ6 hR, mul_pos hγ6 hR, mul_pos hα1 hβ1, mul_nonneg hα1.le hA]
  · by_contra h; push Not at h; obtain ⟨h1, h2, h3, h4⟩ := h
    rcases hD with hD | hD
    · nlinarith [mul_pos hα1 hR, mul_pos hβ1 hR, mul_pos hβ6 hR, mul_pos hγ6 hR, mul_pos hα1 hβ1, mul_nonneg hα1.le hA, mul_pos hα1 hD]
    · nlinarith [mul_pos hα1 hR, mul_pos hβ1 hR, mul_pos hβ6 hR, mul_pos hγ6 hR, mul_pos hα1 hβ1, mul_nonneg hα1.le hA]
  · by_contra h; push Not at h; obtain ⟨h1, h2, h3, h4⟩ := h
    rcases hD with hD | hD
    · nlinarith [mul_pos hα1 hR, mul_pos hβ1 hR, mul_pos hβ6 hR, mul_pos hγ6 hR, mul_pos hα1 hβ1, mul_nonneg hα1.le hA, mul_pos hα1 hD]
    · nlinarith [mul_pos hα1 hR, mul_pos hβ1 hR, mul_pos hβ6 hR, mul_pos hγ6 hR, mul_pos hα1 hβ1, mul_nonneg hα1.le hA]
  · by_contra h; push Not at h; obtain ⟨h1, h2, h3, h4⟩ := h
    rcases hD with hD | hD
    · nlinarith [mul_pos hα1 hR, mul_pos hβ1 hR, mul_pos hβ6 hR, mul_pos hγ6 hR, mul_pos hα1 hβ1, mul_nonneg hα1.le hA, mul_pos hα1 hD]
    · nlinarith [mul_pos hα1 hR, mul_pos hβ1 hR, mul_pos hβ6 hR, mul_pos hγ6 hR, mul_pos hα1 hβ1, mul_nonneg hα1.le hA]

theorem k6p_leaf_N1w
    {x y R α1 β1 β6 γ6 t : ℝ} (hα1 : 0 < α1) (hβ1 : 0 < β1) (hβ6 : 0 < β6) (hγ6 : 0 < γ6)
    (hs : 1 < β6 + γ6) (hab : 1 < α1 + β1) (hcond : 0 < (α1 - 1) * (β6 + γ6) + β1) (hR : 0 < R)
    (ht1 : -β1 ≤ t) (ht2 : t ≤ 1) (hrel : α1 * x + (β1 - 1) * y = t * R)
    (hA : 0 ≤ x) (hC : 0 < α1 * x + β1 * y + β1 * R) (hD : 0 < x ∨ 0 < α1 * x + β1 * y) :
    k5b_ex5 x (α1 * x + β1 * y + β1 * R) ((β6 + γ6) * y + β6 * R) y 0 := by
  have hg : 0 < α1 + β1 - 1 := by linarith
  have hs1 : 0 < β6 + γ6 - 1 := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · by_contra h; push Not at h; obtain ⟨h1, h2, h3, h4⟩ := h
    have e1 : (1 - β1) * y + t * R ≥ α1 * (y + t * R + β1 * R) := by
      nlinarith [mul_le_mul_of_nonneg_left h2 hα1.le]
    have hm : 0 < t + β1 - 1 := by
      have : 0 < (α1 + β1 - 1) * (y + (t + β1) * R) := mul_pos hg (by nlinarith)
      nlinarith [mul_pos hβ1 hR]
    nlinarith [mul_pos hcond (mul_pos hm hR), mul_pos hγ6 (mul_pos hg hR), mul_nonneg hs1.le (sub_nonneg.2 e1),
      mul_nonneg hg.le (sub_nonneg.2 h3)]
  · by_contra h; push Not at h; obtain ⟨h1, h2, h3, h4⟩ := h
    rcases hD with hD | hD
    · nlinarith [mul_pos hα1 hR, mul_pos hβ1 hR, mul_pos hβ6 hR, mul_pos hγ6 hR, mul_pos hα1 hβ1, mul_nonneg hα1.le hA, mul_pos hα1 hD]
    · nlinarith [mul_pos hα1 hR, mul_pos hβ1 hR, mul_pos hβ6 hR, mul_pos hγ6 hR, mul_pos hα1 hβ1, mul_nonneg hα1.le hA]
  · by_contra h; push Not at h; obtain ⟨h1, h2, h3, h4⟩ := h
    rcases hD with hD | hD
    · nlinarith [mul_pos hα1 hR, mul_pos hβ1 hR, mul_pos hβ6 hR, mul_pos hγ6 hR, mul_pos hα1 hβ1, mul_nonneg hα1.le hA, mul_pos hα1 hD]
    · nlinarith [mul_pos hα1 hR, mul_pos hβ1 hR, mul_pos hβ6 hR, mul_pos hγ6 hR, mul_pos hα1 hβ1, mul_nonneg hα1.le hA]
  · by_contra h; push Not at h; obtain ⟨h1, h2, h3, h4⟩ := h
    rcases hD with hD | hD
    · nlinarith [mul_pos hα1 hR, mul_pos hβ1 hR, mul_pos hβ6 hR, mul_pos hγ6 hR, mul_pos hα1 hβ1, mul_nonneg hα1.le hA, mul_pos hα1 hD]
    · nlinarith [mul_pos hα1 hR, mul_pos hβ1 hR, mul_pos hβ6 hR, mul_pos hγ6 hR, mul_pos hα1 hβ1, mul_nonneg hα1.le hA]
  · by_contra h; push Not at h; obtain ⟨h1, h2, h3, h4⟩ := h
    rcases hD with hD | hD
    · nlinarith [mul_pos hα1 hR, mul_pos hβ1 hR, mul_pos hβ6 hR, mul_pos hγ6 hR, mul_pos hα1 hβ1, mul_nonneg hα1.le hA, mul_pos hα1 hD]
    · nlinarith [mul_pos hα1 hR, mul_pos hβ1 hR, mul_pos hβ6 hR, mul_pos hγ6 hR, mul_pos hα1 hβ1, mul_nonneg hα1.le hA]

theorem k6p_leaf_N4w
    {x y R α1 β1 β6 γ6 t : ℝ} (hα1 : 0 < α1) (hβ1 : 0 < β1) (hβ6 : 0 < β6) (hγ6 : 0 < γ6)
    (hs : 1 < β6 + γ6) (hab : 1 < α1 + β1) (hcond : 0 < (α1 - 1) * (β6 + γ6) + β1) (hR : 0 < R)
    (ht1 : -β1 ≤ t) (ht2 : t ≤ 1) (hrel : α1 * x + (β1 - 1) * y = t * R)
    (hA : x < 0) (hB : 0 ≤ α1 * x + β1 * y) :
    k5b_ex5 x (α1 * x + β1 * y + β1 * R) ((β6 + γ6) * y + β6 * R) y 0 := by
  have hg : 0 < α1 + β1 - 1 := by linarith
  have hs1 : 0 < β6 + γ6 - 1 := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · by_contra h; push Not at h; obtain ⟨h1, h2, h3, h4⟩ := h
    nlinarith [mul_pos hα1 hR, mul_pos hβ1 hR, mul_pos hβ6 hR, mul_pos hγ6 hR, mul_pos hα1 hβ1]
  · by_contra h; push Not at h; obtain ⟨h1, h2, h3, h4⟩ := h
    nlinarith [mul_pos hα1 hR, mul_pos hβ1 hR, mul_pos hβ6 hR, mul_pos hγ6 hR, mul_pos hα1 hβ1]
  · by_contra h; push Not at h; obtain ⟨h1, h2, h3, h4⟩ := h
    nlinarith [mul_pos hα1 hR, mul_pos hβ1 hR, mul_pos hβ6 hR, mul_pos hγ6 hR, mul_pos hα1 hβ1]
  · by_contra h; push Not at h; obtain ⟨h1, h2, h3, h4⟩ := h
    nlinarith [mul_pos hα1 hR, mul_pos hβ1 hR, mul_pos hβ6 hR, mul_pos hγ6 hR, mul_pos hα1 hβ1]
  · by_contra h; push Not at h; obtain ⟨h1, h2, h3, h4⟩ := h
    nlinarith [mul_pos hα1 hR, mul_pos hβ1 hR, mul_pos hβ6 hR, mul_pos hγ6 hR, mul_pos hα1 hβ1]

theorem k6p_leaf_K1w
    {x y R α1 β1 β6 γ6 t : ℝ} (hα1 : 1 < α1) (hβ1 : 0 < β1) (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1)
    (hs : 1 < β6 + γ6) (hR : 0 < R)
    (ht1 : -β1 ≤ t) (ht2 : t ≤ 1) (hrel : α1 * x + (β1 - 1) * y = t * R)
    (hC : α1 * x + β1 * y + β1 * R ≤ x) (hD : α1 * x + β1 * y + β1 * R < x ∨ x ≠ 0) :
    k5b_ex5 x (α1 * x + β1 * y) ((β6 + γ6) * y + β6 * R) (y + R) 0 := by
  have hα1' : 0 < α1 := by linarith
  have ha : 0 < α1 - 1 := by linarith
  have hab : 1 < α1 + β1 := by linarith
  have hcond : 0 < (α1 - 1) * (β6 + γ6) + β1 := by nlinarith
  have hg : 0 < α1 + β1 - 1 := by linarith
  have hs1 : 0 < β6 + γ6 - 1 := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · by_contra h; push Not at h; obtain ⟨h1, h2, h3, h4⟩ := h
    have hxt : (β1 - 1) * y ≤ t * R := by nlinarith [mul_nonneg hα1'.le h1]
    have e1 : α1 * (y + t * R + β1 * R) ≤ (1 - β1) * y + t * R := by
      nlinarith [mul_le_mul_of_nonneg_left hC hα1'.le]
    have hy : y < -R := by
      have := mul_nonneg ha.le (sub_nonneg.2 hxt)
      have hab' : 0 < α1 * β1 := mul_pos hα1' hβ1
      nlinarith [mul_pos hab' hR]
    nlinarith [mul_pos hs1 hR]
  · by_contra h; push Not at h; obtain ⟨h1, h2, h3, h4⟩ := h
    nlinarith [mul_pos hα1' hR, mul_pos hβ1 hR, mul_pos hβ6 hR, mul_pos hγ6 hR, mul_pos hα1' hβ1]
  · by_contra h; push Not at h; obtain ⟨h1, h2, h3, h4⟩ := h
    nlinarith [mul_pos hα1' hR, mul_pos hβ1 hR, mul_pos hβ6 hR, mul_pos hγ6 hR, mul_pos hα1' hβ1]
  · by_contra h; push Not at h; obtain ⟨h1, h2, h3, h4⟩ := h
    have k2 : 0 ≤ β1 * (y + R) := mul_nonneg hβ1.le h2
    have hx : x = 0 := by
      apply le_antisymm _ h3
      by_contra hx; push Not at hx
      nlinarith [mul_pos ha hx]
    rcases hD with hD | hD
    · subst hx; nlinarith
    · exact hD hx
  · by_contra h; push Not at h; obtain ⟨h1, h2, h3, h4⟩ := h
    nlinarith [mul_pos hα1' hR, mul_pos hβ1 hR, mul_pos hβ6 hR, mul_pos hγ6 hR, mul_pos hα1' hβ1]

theorem k6p_leaf_K4w
    {x y R α1 β1 β6 γ6 t : ℝ} (hα1 : 1 < α1) (hβ1 : 0 < β1) (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1)
    (hs : 1 < β6 + γ6) (hR : 0 < R)
    (ht1 : -β1 ≤ t) (ht2 : t ≤ 1) (hrel : α1 * x + (β1 - 1) * y = t * R)
    (hC : x < α1 * x + β1 * y + β1 * R) (hA : x < 0) (hB : x ≤ α1 * x + β1 * y) :
    k5b_ex5 x (α1 * x + β1 * y + β1 * R) ((β6 + γ6) * y + β6 * R) y 0 := by
  have hα1' : 0 < α1 := by linarith
  have ha : 0 < α1 - 1 := by linarith
  have hab : 1 < α1 + β1 := by linarith
  have hcond : 0 < (α1 - 1) * (β6 + γ6) + β1 := by nlinarith
  have hg : 0 < α1 + β1 - 1 := by linarith
  have hs1 : 0 < β6 + γ6 - 1 := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · by_contra h; push Not at h; obtain ⟨h1, h2, h3, h4⟩ := h
    nlinarith [mul_pos hα1' hR, mul_pos hβ1 hR, mul_pos hβ6 hR, mul_pos hγ6 hR, mul_pos hα1' hβ1]
  · by_contra h; push Not at h; obtain ⟨h1, h2, h3, h4⟩ := h
    nlinarith [mul_pos hα1' hR, mul_pos hβ1 hR, mul_pos hβ6 hR, mul_pos hγ6 hR, mul_pos hα1' hβ1]
  · by_contra h; push Not at h; obtain ⟨h1, h2, h3, h4⟩ := h
    have e1 : (1 - β1) * y + t * R ≤ α1 * (y + t * R) := by
      nlinarith [mul_le_mul_of_nonneg_left hB hα1'.le]
    nlinarith [mul_pos hs1 hR, mul_pos hg hR, mul_pos ha hR, mul_nonneg ha.le (sub_nonneg.2 ht2),
      mul_nonneg ha.le (neg_le_iff_add_nonneg.1 ht1), mul_pos hβ1 hR, mul_pos hγ6 hR,
      mul_nonneg hs1.le (sub_nonneg.2 e1), mul_nonneg hg.le (sub_nonneg.2 h1), mul_nonneg hg.le (neg_nonneg.2 h3),
      mul_nonneg (sub_nonneg.2 hγ61.le) hR.le]
  · by_contra h; push Not at h; obtain ⟨h1, h2, h3, h4⟩ := h
    nlinarith [mul_pos hα1' hR, mul_pos hβ1 hR, mul_pos hβ6 hR, mul_pos hγ6 hR, mul_pos hα1' hβ1]
  · by_contra h; push Not at h; obtain ⟨h1, h2, h3, h4⟩ := h
    have e1 : (1 - β1) * y + t * R ≤ α1 * (y + t * R) := by
      nlinarith [mul_le_mul_of_nonneg_left hB hα1'.le]
    nlinarith [mul_pos hs1 hR, mul_pos hg hR, mul_pos ha hR, mul_nonneg ha.le (sub_nonneg.2 ht2),
      mul_nonneg ha.le (neg_le_iff_add_nonneg.1 ht1), mul_pos hβ1 hR, mul_pos hγ6 hR,
      mul_nonneg hs1.le (sub_nonneg.2 e1), mul_nonneg hg.le (sub_nonneg.2 h4), mul_nonneg hg.le (neg_nonneg.2 h1),
      mul_nonneg (sub_nonneg.2 hγ61.le) hR.le]


end C2
end Type08Sp
end Minimality
