module

public import Minimality.Type08S.GT_Sminus

@[expose] public section

set_option autoImplicit true

/-!
# GT, group C: Lemma 1.1 and Lemma 1.2 of sp08b (weakly beyond; `z_a > 0` and `x_a > x_2`)

Real-number form in the frame coordinates of `HFrame` (`g = (E, 0, 0)`, `h = f = (b1, b2, 0)`,
`r = (r1, r2, 0)`, weights `E`, `M` of the horizontal metric).
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- "r weakly beyond" (sp08b §0): `(r-g)·g, (r-g)·h, (r-h)·g, (r-h)·h ≥ 0`, weighted metric, `g = (E,0)`. -/
def WeakBeyond (E M b1 b2 r1 r2 : ℝ) : Prop :=
  0 ≤ (r1 - E) * E / E ∧ 0 ≤ (r1 - E) * b1 / E + (r2 - 0) * b2 / M ∧
  0 ≤ (r1 - b1) * E / E ∧ 0 ≤ (r1 - b1) * b1 / E + (r2 - b2) * b2 / M

/-- **Lemma 1.1 (B1′, B2′).** -/
theorem weakBeyond_B1 {E M b1 b2 r1 r2 : ℝ} (hE : 0 < E) (hM : 0 < M)
    (h : WeakBeyond E M b1 b2 r1 r2) (hne : ¬ (r1 = b1 ∧ r2 = b2)) :
    E ≤ r1 ∧ b1 ≤ r1 ∧ (r2 = b2 → b1 < r1) := by
  obtain ⟨w1, w2, w3, w4⟩ := h
  have e1 : (r1 - E) * E / E = r1 - E := by field_simp
  have e3 : (r1 - b1) * E / E = r1 - b1 := by field_simp
  rw [e1] at w1; rw [e3] at w3
  refine ⟨by linarith, by linarith, fun h2 => ?_⟩
  rcases lt_or_eq_of_le (show b1 ≤ r1 by linarith) with h | h
  · exact h
  · exact absurd ⟨h.symm, h2⟩ hne

theorem weakBeyond_B2 {E M b1 b2 r1 r2 : ℝ} (hE : 0 < E) (hM : 0 < M)
    (hb2 : 0 < b2) (h : WeakBeyond E M b1 b2 r1 r2) (hb : r2 < b2) : 0 < b1 := by
  obtain ⟨w1, w2, w3, w4⟩ := h
  have e3 : (r1 - b1) * E / E = r1 - b1 := by field_simp
  rw [e3] at w3
  have hlt : (r2 - b2) * b2 / M < 0 :=
    div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith) hb2) hM
  have : 0 < (r1 - b1) * b1 / E := by linarith
  have h5 : 0 < (r1 - b1) * b1 := by
    have := (div_pos_iff.mp this)
    rcases this with ⟨a, _⟩ | ⟨a, b⟩
    · exact a
    · linarith
  rcases lt_or_ge 0 b1 with h6 | h6
  · exact h6
  · nlinarith

/-- The upper face planes of Lemma 1.2: `Q_ac` and `Q_ab` as affine functions of the screen point. -/
noncomputable def planeAC (A zv β x y : ℝ) : ℝ := zv * (1 - x / A) + β * y
noncomputable def planeAB (b1 b2 r1 r2 μ x y : ℝ) : ℝ := μ * ((r2 - b2) * (x - b1) - (r1 - b1) * (y - b2))

/-- **Lemma 1.2 (N2): `x_a > x_2`** (sp08b §1; the planes of `Q_ac` through `g, p` and `Q_ab`
through `r̄, h̄`; `2̄ = s h̄` and `ā` lie on both; `ā` is on the `g` side of the line `p h̄`).
(`z_a > 0` is part of the picture hypotheses of Proposition H.) -/
theorem lemma12_xa {A zv β μ b1 b2 r1 r2 s a1 a2 : ℝ} (hA : 0 < A) (hzv : 0 ≤ zv) (hr2 : 0 < r2)
    (hB1 : A ≤ r1) (hB2 : b1 ≤ r1)
    (hr : 0 < planeAC A zv β r1 r2) (hh : 0 ≤ planeAC A zv β b1 b2)
    (hμ : zv < planeAB b1 b2 r1 r2 μ 0 0)
    (hdet : 0 < r1 * b2 - r2 * b1)
    (e2 : planeAC A zv β (s * b1) (s * b2) = planeAB b1 b2 r1 r2 μ (s * b1) (s * b2))
    (ea : planeAC A zv β a1 a2 = planeAB b1 b2 r1 r2 μ a1 a2)
    (side : 0 < b2 * a1 - b1 * a2) : s * b1 < a1 := by
  simp only [planeAC, planeAB] at *
  have hβ : 0 < β := by
    have h1 : 0 ≤ zv * (r1 - A) / A := div_nonneg (mul_nonneg hzv (by linarith)) hA.le
    have h2 : zv * (1 - r1 / A) = -(zv * (r1 - A) / A) := by field_simp; ring
    rw [h2] at hr
    by_contra hc
    push_neg at hc
    nlinarith [mul_nonneg (neg_nonneg.mpr hc) hr2.le]
  have hμ0 : 0 < μ := by
    have : μ * (r1 * b2 - r2 * b1) > zv := by
      have := hμ
      have e : μ * ((r2 - b2) * (0 - b1) - (r1 - b1) * (0 - b2)) = μ * (r1 * b2 - r2 * b1) := by ring
      rw [e] at this; exact this
    by_contra hc
    push_neg at hc
    nlinarith [mul_nonneg (neg_nonneg.mpr hc) hdet.le]
  set dx := β + μ * (r1 - b1) with hdx
  set dy := zv / A + μ * (r2 - b2) with hdy
  have hdx0 : 0 < dx := by nlinarith [mul_nonneg hμ0.le (sub_nonneg.mpr hB2)]
  have hK : 0 < b2 * dx - b1 * dy := by
    have e : b2 * dx - b1 * dy = (zv * (1 - b1 / A) + β * b2) +
        (μ * (r1 * b2 - r2 * b1) - zv) := by
      simp only [hdx, hdy]; field_simp; ring
    rw [e]
    have : μ * ((r2 - b2) * (0 - b1) - (r1 - b1) * (0 - b2)) = μ * (r1 * b2 - r2 * b1) := by ring
    nlinarith
  have hpar : (a1 - s * b1) * dy = (a2 - s * b2) * dx := by
    simp only [hdx, hdy]
    have : zv * (1 - a1 / A) + β * a2 - μ * ((r2 - b2) * (a1 - b1) - (r1 - b1) * (a2 - b2)) -
      (zv * (1 - s * b1 / A) + β * (s * b2) - μ * ((r2 - b2) * (s * b1 - b1) - (r1 - b1) * (s * b2 - b2))) = 0 := by
      linarith
    field_simp at this ⊢
    nlinarith [this]
  have key : (a1 - s * b1) * (b2 * dx - b1 * dy) = dx * (b2 * a1 - b1 * a2) := by
    have : b2 * (a1 - s * b1) - b1 * (a2 - s * b2) = b2 * a1 - b1 * a2 := by ring
    calc (a1 - s * b1) * (b2 * dx - b1 * dy) = b2 * dx * (a1 - s * b1) - b1 * ((a1 - s * b1) * dy) := by ring
      _ = b2 * dx * (a1 - s * b1) - b1 * ((a2 - s * b2) * dx) := by rw [hpar]
      _ = dx * (b2 * (a1 - s * b1) - b1 * (a2 - s * b2)) := by ring
      _ = _ := by rw [this]
  have : 0 < (a1 - s * b1) * (b2 * dx - b1 * dy) := by rw [key]; exact mul_pos hdx0 side
  have := (pos_iff_pos_of_mul_pos this).mpr hK
  linarith

end Type08Sp
end Minimality
