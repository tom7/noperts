module

public import SmallRupert.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

@[expose] public section

/-!
# Planes in `ℝ³`: normals, coplanarity, the cross product

Concrete tools for the ≤ 5-vertex and bicapped-tetrahedron proofs:
* `exists_plane_of_coplanar`, `coplanar_of_plane`: Mathlib's `Coplanar` versus a
  plane equation `⟪N, x⟫ = c` with `N ≠ 0`;
* `interior_convexHull_eq_empty_of_plane`: a planar set has no interior;
* `exists_affineIndependent_triple`: a non-collinear set contains an affinely
  independent triple;
* `cross`, `det4` with `coplanar_of_det4_eq_zero`.
-/

namespace SmallRupert

open scoped RealInnerProductSpace Matrix
open Module

/-- A coplanar set lies on a plane `⟪N, x⟫ = c`. -/
theorem exists_plane_of_coplanar {S : Set ℝ³} (hS : Coplanar ℝ S) :
    ∃ N : ℝ³, N ≠ 0 ∧ ∃ c : ℝ, ∀ x ∈ S, ⟪N, x⟫ = c := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨s₀, hs₀⟩
  · exact ⟨ez, by simp [ez], 0, by simp⟩
  set K := vectorSpan ℝ S
  have hK : K ≠ ⊤ := by
    intro hK
    have h := hS
    unfold Coplanar at h
    have h3 : Module.rank ℝ ℝ³ = 3 := by rw [← finrank_eq_rank]; simp
    rw [show vectorSpan ℝ S = K from rfl, hK, rank_top, h3] at h
    norm_num at h
  have hKo : Kᗮ ≠ ⊥ := fun h => hK (Submodule.orthogonal_eq_bot_iff.mp h)
  obtain ⟨N, hN, hN0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hKo
  refine ⟨N, hN0, ⟪N, s₀⟫, fun x hx => ?_⟩
  have := Submodule.inner_left_of_mem_orthogonal (vsub_mem_vectorSpan ℝ hx hs₀) hN
  rw [vsub_eq_sub, inner_sub_right] at this
  linarith

/-- A set on a plane is coplanar. -/
theorem coplanar_of_plane {S : Set ℝ³} {N : ℝ³} (hN : N ≠ 0) {c : ℝ}
    (h : ∀ x ∈ S, ⟪N, x⟫ = c) : Coplanar ℝ S := by
  have hle : vectorSpan ℝ S ≤ (ℝ ∙ N)ᗮ := by
    rw [vectorSpan_def, Submodule.span_le]
    rintro _ ⟨x, hx, y, hy, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
    show ⟪N, x - y⟫ = 0
    rw [inner_sub_right, h x hx, h y hy, sub_self]
  haveI : Fact (finrank ℝ ℝ³ = 2 + 1) := ⟨by simp⟩
  have h2 : finrank ℝ (ℝ ∙ N)ᗮ = 2 := Submodule.finrank_orthogonal_span_singleton hN
  unfold Coplanar
  calc Module.rank ℝ (vectorSpan ℝ S) ≤ Module.rank ℝ (ℝ ∙ N)ᗮ := Submodule.rank_mono hle
    _ = 2 := by rw [← finrank_eq_rank, h2]; rfl

/-- A plane has empty interior. -/
theorem interior_plane_eq_empty {N : ℝ³} (hN : N ≠ 0) (c : ℝ) :
    interior {x : ℝ³ | ⟪N, x⟫ = c} = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
  have hNpos : 0 < ‖N‖ := norm_pos_iff.mpr hN
  have h1 : x + (r / 2 / ‖N‖) • N ∈ {x : ℝ³ | ⟪N, x⟫ = c} := interior_subset (hball (by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity), div_mul_cancel₀ _ hNpos.ne']
    linarith))
  have h0 : x ∈ {x : ℝ³ | ⟪N, x⟫ = c} := interior_subset hx
  simp only [Set.mem_setOf_eq] at h0
  simp only [Set.mem_setOf_eq, inner_add_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, h0] at h1
  have : 0 < r / 2 / ‖N‖ * ‖N‖ ^ 2 := by positivity
  linarith

/-- The hull of a planar set has empty interior. -/
theorem interior_convexHull_eq_empty_of_plane {S : Set ℝ³} {N : ℝ³} (hN : N ≠ 0) {c : ℝ}
    (h : ∀ x ∈ S, ⟪N, x⟫ = c) : interior (convexHull ℝ S) = ∅ := by
  apply Set.eq_empty_of_subset_empty
  rw [← interior_plane_eq_empty hN c]
  exact interior_mono (convexHull_min h (convex_hyperplane (innerₛₗ ℝ N).isLinear c))

/-- A solid hull is not coplanar. -/
theorem not_coplanar_of_interior_nonempty {S : Set ℝ³}
    (hint : (interior (convexHull ℝ S)).Nonempty) : ¬ Coplanar ℝ S := by
  intro hS
  obtain ⟨N, hN, c, h⟩ := exists_plane_of_coplanar hS
  rw [interior_convexHull_eq_empty_of_plane hN h] at hint
  exact Set.not_nonempty_empty hint

/-- A non-collinear set contains an affinely independent triple. -/
theorem exists_affineIndependent_triple {S : Set ℝ³} (hS : ¬ Collinear ℝ S) :
    ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, AffineIndependent ℝ ![a, b, c] := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · exact absurd (collinear_empty ℝ ℝ³) hS
  by_cases hb : ∃ b ∈ S, b ≠ a
  · obtain ⟨b, hbS, hba⟩ := hb
    by_contra hcon
    push Not at hcon
    apply hS
    rw [collinear_iff_of_mem ha]
    refine ⟨b - a, fun p hp => ?_⟩
    have hcol : Collinear ℝ ({a, b, p} : Set ℝ³) := by
      by_contra h'
      exact hcon a ha b hbS p hp (affineIndependent_iff_not_collinear_set.mpr h')
    have hmem := hcol.mem_affineSpan_of_mem_of_ne (p₁ := a) (p₂ := b) (p₃ := p)
      (by simp) (by simp) (by simp) hba.symm
    obtain ⟨r, hr⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).mp hmem
    exact ⟨r, by rw [← hr, AffineMap.lineMap_apply]; rfl⟩
  · push Not at hb
    exact absurd ((collinear_singleton ℝ a).subset fun p hp => hb p hp) hS

/-- The cross product on `ℝ³`. -/
noncomputable def cross (a b : ℝ³) : ℝ³ :=
  !₂[a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]

theorem inner_cross_left (a b : ℝ³) : ⟪cross a b, a⟫ = 0 := by
  simp [cross, PiLp.inner_apply, Fin.sum_univ_three]; ring

theorem inner_cross_right (a b : ℝ³) : ⟪cross a b, b⟫ = 0 := by
  simp [cross, PiLp.inner_apply, Fin.sum_univ_three]; ring

/-- The orientation determinant of four points. -/
noncomputable def det4 (a b c d : ℝ³) : ℝ := ⟪cross (b - a) (c - a), d - a⟫

/-- Four points with vanishing determinant are coplanar. -/
theorem coplanar_of_det4_eq_zero {a b c d : ℝ³} (h : det4 a b c d = 0) :
    Coplanar ℝ ({a, b, c, d} : Set ℝ³) := by
  let M : Matrix (Fin 3) (Fin 3) ℝ := !![b 0 - a 0, c 0 - a 0, d 0 - a 0;
    b 1 - a 1, c 1 - a 1, d 1 - a 1; b 2 - a 2, c 2 - a 2, d 2 - a 2]
  have hdet : M.det = 0 := by
    rw [Matrix.det_fin_three]
    simp only [det4, cross, PiLp.inner_apply, Fin.sum_univ_three] at h
    simp [M] at h ⊢
    linear_combination h
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
  set N : ℝ³ := WithLp.toLp 2 v
  have hN : N ≠ 0 := fun h0 => hv (by simpa [N] using congrArg WithLp.ofLp h0)
  have hcol : ∀ j : Fin 3, v 0 * M 0 j + v 1 * M 1 j + v 2 * M 2 j = 0 := fun j => by
    have := congrFun hMv j
    simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_three] using this
  have h0 := hcol 0; have h1 := hcol 1; have h2 := hcol 2
  simp [M] at h0 h1 h2
  refine coplanar_of_plane hN (c := ⟪N, a⟫) ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · rfl
  · simp [N, PiLp.inner_apply, Fin.sum_univ_three]; linear_combination h0
  · simp [N, PiLp.inner_apply, Fin.sum_univ_three]; linear_combination h1
  · simp [N, PiLp.inner_apply, Fin.sum_univ_three]; linear_combination h2

end SmallRupert

end
