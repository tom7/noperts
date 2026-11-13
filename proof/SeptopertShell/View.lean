module

public import SeptopertShell.Basic
public import SeptopertFamily.Geometry

/-!
# Rupert passages from a view direction

The certificate form of the shell (written by an external C++ certificate generator): a view `v` (`ViewOk v`: not a
nonpositive multiple of `e_z`), an inner
rotation `Q` and a translation `t`; every inner vertex `w = Q x + t` lies, seen along `v`, strictly inside a
triangle of outer vertices, i.e. three triple products `v · ((b − w) × (c − w))` are positive. The outer rotation
is built from `v`: the quaternion `(|v| + v₂, v₁, −v₀, 0)` turns `v` to `|v| e_z`, and the third row of its matrix is
`2 (|v| + v₂) v`, so projected cross products are positive multiples of the triple products.
-/

@[expose] public section

namespace SeptopertShell

open SeptopertFamily

/-- The triple product `v · (a × b)`. -/
def triple (v a b : ℝ³) : ℝ :=
  v 0 * (a 1 * b 2 - a 2 * b 1) + v 1 * (a 2 * b 0 - a 0 * b 2) + v 2 * (a 0 * b 1 - a 1 * b 0)

/-- The quaternion turning `v` to `|v| e_z`. -/
noncomputable def viewQuat (v : ℝ³) : Fin 4 → ℝ :=
  ![√(v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2) + v 2, v 1, -v 0, 0]

/-- The view condition: `v` is not a nonpositive multiple of `e_z`. -/
def ViewOk (v : ℝ³) : Prop := 0 < v 2 ∨ v 0 ≠ 0 ∨ v 1 ≠ 0

theorem viewOk_sqrt_add_pos {v : ℝ³} (hv : ViewOk v) : 0 < √(v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2) + v 2 := by
  rcases hv with h | h
  · have := Real.sqrt_nonneg (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2); linarith
  · have h01 : 0 < v 0 ^ 2 + v 1 ^ 2 := by
      rcases h with h | h
      · have := pow_pos (abs_pos.mpr h) 2; rw [sq_abs] at this; nlinarith [sq_nonneg (v 1)]
      · have := pow_pos (abs_pos.mpr h) 2; rw [sq_abs] at this; nlinarith [sq_nonneg (v 0)]
    have : |v 2| < √(v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2) := by
      rw [Real.lt_sqrt (abs_nonneg _), sq_abs]; linarith
    linarith [neg_abs_le (v 2)]

theorem viewQuat_norm_pos {v : ℝ³} (hv : ViewOk v) : 0 < quatNorm (viewQuat v) := by
  have hs := viewOk_sqrt_add_pos hv
  simp only [quatNorm, viewQuat, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  nlinarith [sq_nonneg (v 1), sq_nonneg (v 0)]

/-- Seen through the outer rotation of `v`, projected cross products are positive multiples of triple
products with `v`. -/
theorem cross2_proj_viewRot (v X Y : ℝ³) :
    cross2 (proj_xy ((quatRot (viewQuat v)).toEuclideanLin X))
        (proj_xy ((quatRot (viewQuat v)).toEuclideanLin Y)) =
      2 * (√(v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2) + v 2) / quatNorm (viewQuat v) * triple v X Y := by
  set s := √(v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2) with hs_def
  have hs : s ^ 2 = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := Real.sq_sqrt (by positivity)
  have e : ∀ Z : ℝ³, ∀ r : Fin 2, proj_xy ((quatRot (viewQuat v)).toEuclideanLin Z) r =
      (quatNorm (viewQuat v))⁻¹ * ∑ j, quatMat (viewQuat v) (Fin.castSucc r) j * Z j := by
    intro Z r
    fin_cases r <;>
      simp [proj_xy, Matrix.toLpLin_apply, quatRot, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  simp only [cross2, e]
  set N := quatNorm (viewQuat v)
  set M := quatMat (viewQuat v)
  have key : (∑ j, M (Fin.castSucc 0) j * X j) * (∑ j, M (Fin.castSucc 1) j * Y j) -
      (∑ j, M (Fin.castSucc 1) j * X j) * (∑ j, M (Fin.castSucc 0) j * Y j) =
      N * (2 * (s + v 2) * triple v X Y) := by
    simp only [M, N, quatNorm, quatMat, viewQuat, triple, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.castSucc_zero,
      Fin.castSucc_one, Fin.isValue]
    linear_combination ((s + v 2) ^ 2 + v 1 ^ 2 + (-v 0) ^ 2 + 0 ^ 2) * (X 0 * Y 1 - X 1 * Y 0) * hs
  by_cases hN : N = 0
  · simp [hN]
  calc N⁻¹ * (∑ j, M (Fin.castSucc 0) j * X j) * (N⁻¹ * ∑ j, M (Fin.castSucc 1) j * Y j) -
        N⁻¹ * (∑ j, M (Fin.castSucc 1) j * X j) * (N⁻¹ * ∑ j, M (Fin.castSucc 0) j * Y j)
      = N⁻¹ ^ 2 * ((∑ j, M (Fin.castSucc 0) j * X j) * (∑ j, M (Fin.castSucc 1) j * Y j) -
        (∑ j, M (Fin.castSucc 1) j * X j) * (∑ j, M (Fin.castSucc 0) j * Y j)) := by ring
    _ = 2 * (s + v 2) / N * triple v X Y := by rw [key]; field_simp

/-- **A Rupert passage seen along a view `v`.** -/
theorem isRupert_of_view (V : Finset ℝ³) (v : ℝ³) (hv : ViewOk v) {Q : Matrix (Fin 3) (Fin 3) ℝ}
    (hQ : Q ∈ SO3) (t : ℝ³)
    (h : ∀ x ∈ V, ∃ a ∈ V, ∃ b ∈ V, ∃ c ∈ V,
      0 < triple v (b - (Q.toEuclideanLin x + t)) (c - (Q.toEuclideanLin x + t)) ∧
      0 < triple v (c - (Q.toEuclideanLin x + t)) (a - (Q.toEuclideanLin x + t)) ∧
      0 < triple v (a - (Q.toEuclideanLin x + t)) (b - (Q.toEuclideanLin x + t))) :
    IsRupert V := by
  set Ro := quatRot (viewQuat v)
  have hN := viewQuat_norm_pos hv
  have hRo : Ro ∈ SO3 := quatRot_mem_SO3 _ hN.ne'
  have hRi : Ro * Q ∈ SO3 := Submonoid.mul_mem _ hRo hQ
  have hk : 0 < 2 * (√(v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2) + v 2) / quatNorm (viewQuat v) := by
    have := viewOk_sqrt_add_pos hv; positivity
  have hlin : ∀ X Y : ℝ³, proj_xy (Ro.toEuclideanLin X) - proj_xy (Ro.toEuclideanLin Y) =
      proj_xy (Ro.toEuclideanLin (X - Y)) := by
    intro X Y; ext r; fin_cases r <;> simp [proj_xy, map_sub]
  refine isRupert_of_forall_mem_interior V hRi hRo (proj_xy (Ro.toEuclideanLin t)) ?_
  intro x hx
  obtain ⟨a, ha, b, hb, c, hc, h1, h2, h3⟩ := h x hx
  set w := Q.toEuclideanLin x + t
  have hw : proj_xy (Ro.toEuclideanLin t) + proj_xy ((Ro * Q).toEuclideanLin x) =
      proj_xy (Ro.toEuclideanLin w) := by
    ext r; fin_cases r <;> simp [w, proj_xy, Matrix.toLpLin_apply, Matrix.mulVec_mulVec, Matrix.mulVec_add,
      add_comm]
  rw [hw]
  have tri : proj_xy (Ro.toEuclideanLin w) ∈ interior (convexHull ℝ
      ({proj_xy (Ro.toEuclideanLin a), proj_xy (Ro.toEuclideanLin b), proj_xy (Ro.toEuclideanLin c)} :
        Set ℝ²)) := by
    apply mem_interior_convexHull_triangle
    · rw [hlin, hlin, cross2_proj_viewRot]; exact mul_pos hk h1
    · rw [hlin, hlin, cross2_proj_viewRot]; exact mul_pos hk h2
    · rw [hlin, hlin, cross2_proj_viewRot]; exact mul_pos hk h3
  refine interior_mono (convexHull_mono ?_) tri
  intro u hu
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
  rcases hu with rfl | rfl | rfl
  · exact ⟨a, ha, rfl⟩
  · exact ⟨b, hb, rfl⟩
  · exact ⟨c, hc, rfl⟩

end SeptopertShell

end
