module

public import Minimality.HiddenCap
public import Minimality.CornerKite

@[expose] public section

/-!
# Apex normal cone lemma (nopert229 report NCLEAN).
-/

set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace

namespace Minimality.NCone
open Matrix Finset Minimality.CornerEQ

/-- Gram matrix of three edge vectors. -/
noncomputable def gram3 (e : Fin 3 → ℝ³) : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of fun a b => ⟪e a, e b⟫

/-- The apex view `u = Σ (G⁻¹ w)_a e_a`. -/
noncomputable def apexView (e : Fin 3 → ℝ³) (w : Fin 3 → ℝ) : ℝ³ :=
  ∑ a, ((gram3 e)⁻¹ *ᵥ w) a • e a

theorem gram3_posDef {e : Fin 3 → ℝ³} (hli : LinearIndependent ℝ e) : (gram3 e).PosDef :=
  Matrix.posDef_gram_of_linearIndependent hli

/-- (i) `H = G⁻¹ ≥ 0` entrywise, `H w > 0` for `w > 0`. -/
theorem H_nonneg {e : Fin 3 → ℝ³} (hli : LinearIndependent ℝ e)
    (hobt : ∀ a b, a ≠ b → ⟪e a, e b⟫ ≤ 0) (i j : Fin 3) : 0 ≤ (gram3 e)⁻¹ i j :=
  inv_nonneg_fin3 (gram3_posDef hli) (fun a b h => hobt a b h) i j

theorem Hw_pos {e : Fin 3 → ℝ³} (hli : LinearIndependent ℝ e)
    (hobt : ∀ a b, a ≠ b → ⟪e a, e b⟫ ≤ 0) {w : Fin 3 → ℝ} (hw : ∀ a, 0 < w a) (i : Fin 3) :
    0 < ((gram3 e)⁻¹ *ᵥ w) i :=
  inv_mulVec_pos_fin3 (gram3_posDef hli) (fun a b h => hobt a b h) hw i

/-- the view has covector `w`: `⟪e_b, u⟫ = w_b`. -/
theorem inner_edge_apexView {e : Fin 3 → ℝ³} (hli : LinearIndependent ℝ e) (w : Fin 3 → ℝ)
    (b : Fin 3) : ⟪e b, apexView e w⟫ = w b := by
  have hG := gram3_posDef hli
  have hu : IsUnit (gram3 e) := by
    rw [Matrix.isUnit_iff_isUnit_det]; exact hG.det_pos.ne'.isUnit
  have h : (gram3 e *ᵥ ((gram3 e)⁻¹ *ᵥ w)) b = w b := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hG.det_pos.ne'.isUnit, Matrix.one_mulVec]
  rw [← h]
  simp only [apexView, inner_sum, inner_smul_right, Matrix.mulVec, dotProduct, gram3, Matrix.of_apply]
  apply Finset.sum_congr rfl; intro a _; ring

/-- (iii) depth: for `p = v + Σ y_a e_a`, `⟪p - v, u⟫ = y ⬝ᵥ w`. -/
theorem inner_comb_apexView {e : Fin 3 → ℝ³} (hli : LinearIndependent ℝ e) (w y : Fin 3 → ℝ) :
    ⟪∑ a, y a • e a, apexView e w⟫ = y ⬝ᵥ w := by
  simp only [sum_inner, inner_smul_left, dotProduct]
  apply Finset.sum_congr rfl; intro a _
  rw [inner_edge_apexView hli]; simp

/-- (iv) facing: for a covector `n`, `⟪n, u⟫ = (⟪n, e_a⟫)_a ⬝ᵥ (G⁻¹ w)`. -/
theorem inner_apexView (e : Fin 3 → ℝ³) (n : ℝ³) (w : Fin 3 → ℝ) :
    ⟪n, apexView e w⟫ = (fun a => ⟪n, e a⟫) ⬝ᵥ ((gram3 e)⁻¹ *ᵥ w) := by
  simp only [apexView, inner_sum, inner_smul_right, dotProduct]
  apply Finset.sum_congr rfl; intro a _; ring

/-- (ii) the apex is hidden. -/
theorem hidden_apexView (O : Finset ℝ³) (v a b c : ℝ³) (ha : a ∈ O) (hb : b ∈ O) (hc : c ∈ O)
    (hli : LinearIndependent ℝ ![a - v, b - v, c - v])
    (hobt : ∀ i j : Fin 3, i ≠ j → ⟪![a - v, b - v, c - v] i, ![a - v, b - v, c - v] j⟫ ≤ 0)
    {w : Fin 3 → ℝ} (hw : ∀ i, 0 < w i) :
    HiddenAt O (apexView ![a - v, b - v, c - v] w) v := by
  have hp := fun i => Hw_pos hli hobt hw i
  have key : apexView ![a - v, b - v, c - v] w
      = (((gram3 ![a - v, b - v, c - v])⁻¹ *ᵥ w) 0) • (a - v)
        + (((gram3 ![a - v, b - v, c - v])⁻¹ *ᵥ w) 1) • (b - v)
        + (((gram3 ![a - v, b - v, c - v])⁻¹ *ᵥ w) 2) • (c - v) := by
    simp [apexView, Fin.sum_univ_three]
  rw [key]
  exact hiddenAt_of_cone O v a b c ha hb hc hli _ _ _ (hp 0) (hp 1) (hp 2)

end Minimality.NCone
