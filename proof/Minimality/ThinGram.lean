module

public import Minimality.ThinCases
public import Minimality.RimCellView

@[expose] public section

namespace Minimality

open scoped RealInnerProductSpace
open Matrix Minimality.RimCell

theorem boxApplies_of_thin_gram {k : ℕ} (X : Fin k → Fin 3 → ℝ) (E : Matrix (Fin 3) (Fin 3) ℝ)
    (hE : 0 < E.det)
    (hsol : (interior (convexHull ℝ
      ((Finset.univ.image (fun i => emb E (X i)) : Finset ℝ³) : Set ℝ³))).Nonempty)
    (m kv : Fin 3 → ℝ) (hmk : m ⬝ᵥ kv ≠ 0) (A : ℝ)
    (hA : ∀ i j, |m ⬝ᵥ (X i - X j)| ≤ A * |m ⬝ᵥ kv|)
    (i₀ j₀ : Fin k) (hthin : A * ‖emb E kv‖ < thinAlpha k * ‖emb E (X i₀) - emb E (X j₀)‖) :
    BoxApplies (Finset.univ.image (fun i => emb E (X i))) := by
  have hU : IsUnit E.det := isUnit_iff_ne_zero.mpr hE.ne'
  set N : ℝ³ := WithLp.toLp 2 ((E⁻¹)ᵀ *ᵥ m) with hN
  have hNy : ∀ y, ⟪N, emb E y⟫ = m ⬝ᵥ y := by
    intro y
    have h := inner_emb E y y
    -- direct computation
    have : ⟪N, emb E y⟫ = (E *ᵥ y) ⬝ᵥ ((E⁻¹)ᵀ *ᵥ m) := by
      simp [hN, emb, PiLp.inner_apply, dotProduct]
    rw [this, dotProduct_mulVec, vecMul_transpose, mulVec_mulVec,
      Matrix.nonsing_inv_mul _ hU, one_mulVec]
    exact dotProduct_comm _ _
  have hm : m ≠ 0 := by rintro rfl; simp at hmk
  have hN0 : N ≠ 0 := by
    intro h
    apply hmk
    rw [← hNy kv, h]; simp
  have hNpos : 0 < ‖N‖ := norm_pos_iff.mpr hN0
  have hA0 : 0 ≤ A := by
    have := hA i₀ i₀
    simp at this
    have hp : 0 < |m ⬝ᵥ kv| := abs_pos.mpr hmk
    by_contra hc; push Not at hc; nlinarith
  refine boxApplies_of_thin_fin (fun i => emb E (X i)) hsol (‖N‖⁻¹ • N) ?_ (A * ‖emb E kv‖) ?_
    i₀ j₀ hthin
  · rw [inner_smul_left, inner_smul_right, real_inner_self_eq_norm_sq]
    simp; field_simp
  · intro i j
    rw [← emb_sub, inner_smul_left, hNy]
    simp only [conj_trivial]
    rw [abs_mul, abs_inv, abs_of_pos hNpos]
    have h1 : |m ⬝ᵥ kv| ≤ ‖N‖ * ‖emb E kv‖ := by
      rw [← hNy]; exact abs_real_inner_le_norm _ _
    rw [inv_mul_le_iff₀ hNpos]
    calc |m ⬝ᵥ (X i - X j)| ≤ A * |m ⬝ᵥ kv| := hA i j
      _ ≤ A * (‖N‖ * ‖emb E kv‖) := mul_le_mul_of_nonneg_left h1 hA0
      _ = ‖N‖ * (A * ‖emb E kv‖) := by ring

end Minimality
#print axioms Minimality.boxApplies_of_thin_gram
