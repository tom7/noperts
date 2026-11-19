module

public import Mathlib
public import Minimality.ApexNormalCone
public import Minimality.CornerKite
public import Minimality.HiddenCap
public import Minimality.OrthoView

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped RealInnerProductSpace
open Matrix Finset Minimality.CornerEQ Minimality.NCone

namespace Minimality.OrthoCorner

/-- **Stieltjes 3x3 matrix inverse.**
If `G` is a symmetric positive definite 3x3 real matrix with nonpositive off-diagonal entries
(`G a b ≤ 0` for `a ≠ b`), then `G` is invertible, its inverse `G⁻¹` is entrywise nonnegative
with strictly positive diagonal `0 < G⁻¹ i i`, and `(G⁻¹ *ᵥ 1) i > 0` for all `i`. -/
theorem stieltjes_inv_pos_fin3 {G : Matrix (Fin 3) (Fin 3) ℝ} (hG : G.PosDef)
    (hGo : ∀ a b, a ≠ b → G a b ≤ 0) :
    IsUnit G ∧
    (∀ i j, 0 ≤ G⁻¹ i j) ∧
    (∀ i, 0 < G⁻¹ i i) ∧
    (∀ i, 0 < (G⁻¹ *ᵥ 1) i) := by
  have hu : IsUnit G := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact hG.det_pos.ne'.isUnit
  have hnonneg : ∀ i j, 0 ≤ G⁻¹ i j := inv_nonneg_fin3 hG hGo
  have hdiag : ∀ i, 0 < G⁻¹ i i := inv_diag_pos_fin3 hG
  have hpos : ∀ i, 0 < (G⁻¹ *ᵥ (1 : Fin 3 → ℝ)) i :=
    inv_mulVec_pos_fin3 hG hGo (fun _ => one_pos)
  exact ⟨hu, hnonneg, hdiag, hpos⟩

/-- **Orthocentre view at an obtuse corner.**
For linearly independent edge vectors `v : Fin 3 → ℝ³` with pairwise non-acute angles
(`⟪v e, v f⟫ ≤ 0` for `e ≠ f`), there exists a view `u : ℝ³` and strictly positive coefficients
`c : Fin 3 → ℝ` such that `⟪v e, u⟫ = 1` for all `e`, and `u = ∑ e, c e • v e`. -/
theorem exists_orthocentre_view (v : Fin 3 → ℝ³) (hli : LinearIndependent ℝ v)
    (hobt : ∀ e f, e ≠ f → ⟪v e, v f⟫ ≤ 0) :
    ∃ (u : ℝ³) (c : Fin 3 → ℝ),
      (∀ e, ⟪v e, u⟫ = 1) ∧ (∀ e, 0 < c e) ∧ u = ∑ e, c e • v e := by
  set G := gram3 v with hG
  have hG_pos : G.PosDef := gram3_posDef hli
  set c := G⁻¹ *ᵥ (1 : Fin 3 → ℝ) with hc
  set u := ∑ e, c e • v e with hu
  have hc_pos : ∀ e, 0 < c e :=
    inv_mulVec_pos_fin3 hG_pos (fun a b h => hobt a b h) (fun _ => one_pos)
  have hu_inner : ∀ e, ⟪v e, u⟫ = 1 := by
    intro e
    have h := inner_edge_apexView hli (1 : Fin 3 → ℝ) e
    rw [apexView] at h
    exact h
  exact ⟨u, c, hu_inner, hc_pos, rfl⟩

/-- **Hidden apex at the orthocentre view.**
If `v e = x_e - v₀` for three vertices `a, b, c ∈ O` with independent edge vectors
and `u = ∑ e, c e • v e` with `c e > 0`, then the apex `v₀` is hidden by `O` at view `u`. -/
theorem hiddenAt_orthocentre (O : Finset ℝ³) (v₀ a b c : ℝ³) (ha : a ∈ O) (hb : b ∈ O) (hc : c ∈ O)
    (hli : LinearIndependent ℝ ![a - v₀, b - v₀, c - v₀]) (c_coeff : Fin 3 → ℝ)
    (hc_pos : ∀ i, 0 < c_coeff i)
    {u : ℝ³} (hu : u = c_coeff 0 • (a - v₀) + c_coeff 1 • (b - v₀) + c_coeff 2 • (c - v₀)) :
    HiddenAt O u v₀ := by
  rw [hu]
  exact hiddenAt_of_cone O v₀ a b c ha hb hc hli (c_coeff 0) (c_coeff 1) (c_coeff 2)
    (hc_pos 0) (hc_pos 1) (hc_pos 2)

/-- **Hidden apex corollary for indexed vertices (Theorem P form).**
For a vertex set `Finset.univ.image x`, an apex `x i₀`, three corner ends `x (e 0), x (e 1), x (e 2)`
distinct from `x i₀`, with edge vectors `v k = x (e k) - x i₀` that are linearly independent and
pairwise non-acute, the orthocentre view `u` with `⟪v k, u⟫ = 1` and cone representation
`u = ∑ k, c k • v k` with `c k > 0` hides the apex `x i₀`. -/
theorem hiddenAt_apex_orthocentre {n : ℕ} (x : Fin n → ℝ³) (i₀ : Fin n)
    (e : Fin 3 → Fin n)
    (hli : LinearIndependent ℝ fun k => x (e k) - x i₀)
    (c_coeff : Fin 3 → ℝ) (hc_pos : ∀ k, 0 < c_coeff k)
    {u : ℝ³} (hu : u = ∑ k, c_coeff k • (x (e k) - x i₀)) :
    HiddenAt (Finset.univ.image x) u (x i₀) := by
  have ha : x (e 0) ∈ Finset.univ.image x := Finset.mem_image_of_mem x (Finset.mem_univ _)
  have hb : x (e 1) ∈ Finset.univ.image x := Finset.mem_image_of_mem x (Finset.mem_univ _)
  have hc : x (e 2) ∈ Finset.univ.image x := Finset.mem_image_of_mem x (Finset.mem_univ _)
  have hli' : LinearIndependent ℝ ![x (e 0) - x i₀, x (e 1) - x i₀, x (e 2) - x i₀] := by
    have heq : ![x (e 0) - x i₀, x (e 1) - x i₀, x (e 2) - x i₀] = (fun k => x (e k) - x i₀) := by
      ext k
      fin_cases k <;> rfl
    rwa [heq]
  have hu' : u = c_coeff 0 • (x (e 0) - x i₀) + c_coeff 1 • (x (e 1) - x i₀) + c_coeff 2 • (x (e 2) - x i₀) := by
    rw [hu, Fin.sum_univ_three]
  exact hiddenAt_orthocentre (Finset.univ.image x) (x i₀) (x (e 0)) (x (e 1)) (x (e 2))
    ha hb hc hli' c_coeff hc_pos hu'

end Minimality.OrthoCorner
