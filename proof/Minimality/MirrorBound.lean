module

public import Minimality.Basic

@[expose] public section

/-!
# Mirror lemma (core inequality)

Lemma MR of `nopert229/out/bottleneck/clopen/draft.md` §6.  Let `u₀ = (a, 0, b)` with
`a, b > 0` and let `ρ` be the reflection in the plane through the origin with normal `u₀`.
If `V` is `ρ`-invariant, `S = proj_xy '' conv V`, and `n` is a (weak) outward normal of `S`
at `proj_xy v` for some `v ∈ V`, then the unit rotation `ω = -e_y = (0, -1, 0)`
(`[ω]× x = (-x_z, 0, x_x)`, so `screenVel ω 0 x = (-x_z, 0)`) satisfies
`⟪n, screenVel ω 0 v⟫ ≤ ‖n‖ * |v_x| * (a / b)`.

At a view at angle `s` from a mirror normal, `tan s = a / b`; hence every silhouette
constraint of this unit rotation is `≤ R tan s`, so the first-order margin tends to `≤ 0` at
mirror normals (a polytope with a mirror plane is never strictly first-order rigid).
-/

namespace Minimality

open scoped RealInnerProductSpace

/-- `screenVel (0,-1,0) 0 x = (-x_z, 0)`. -/
theorem screenVel_neg_ey (x : ℝ³) :
    screenVel !₂[0, -1, 0] 0 x = !₂[-x 2, 0] := by
  ext i
  fin_cases i <;> simp [screenVel, proj_xy, crossMatrix, Matrix.toLpLin_apply,
    dotProduct, Fin.sum_univ_three]

theorem mirror_screenVel_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (V : Finset ℝ³)
    (hρ : ∀ v ∈ V, v - (2 * ⟪v, !₂[a, 0, b]⟫ / (a ^ 2 + b ^ 2)) • !₂[a, 0, b] ∈ V)
    {v : ℝ³} (hv : v ∈ V) {n : ℝ²}
    (hn : ∀ y ∈ proj_xy '' convexHull ℝ (V : Set ℝ³), ⟪n, y - proj_xy v⟫ ≤ 0) :
    ⟪n, screenVel !₂[0, -1, 0] 0 v⟫ ≤ ‖n‖ * |v 0| * (a / b) := by
  have hmem : proj_xy (v - (2 * ⟪v, !₂[a, 0, b]⟫ / (a ^ 2 + b ^ 2)) • !₂[a, 0, b]) ∈
      proj_xy '' convexHull ℝ (V : Set ℝ³) :=
    ⟨_, subset_convexHull ℝ _ (hρ v hv), rfl⟩
  have h1 := hn _ hmem
  have hc : ⟪v, !₂[a, 0, b]⟫ = a * v 0 + b * v 2 := by
    simp [PiLp.inner_apply, Fin.sum_univ_three]
  set c := a * v 0 + b * v 2 with hcdef
  have hab : 0 < a ^ 2 + b ^ 2 := by positivity
  rw [hc] at h1
  have h2 : n 0 * c ≥ 0 := by
    have : ⟪n, proj_xy (v - (2 * c / (a ^ 2 + b ^ 2)) • !₂[a, 0, b]) - proj_xy v⟫
        = -(2 * c / (a ^ 2 + b ^ 2)) * a * n 0 := by
      simp [PiLp.inner_apply, Fin.sum_univ_two, proj_xy]
    rw [this] at h1
    have h3 : 0 ≤ (2 / (a ^ 2 + b ^ 2)) * a * (n 0 * c) := by
      have : (2 / (a ^ 2 + b ^ 2)) * a * (n 0 * c) = -(-(2 * c / (a ^ 2 + b ^ 2)) * a * n 0) := by
        ring
      linarith
    have h4 : 0 < (2 / (a ^ 2 + b ^ 2)) * a := by positivity
    by_contra h
    push Not at h
    nlinarith
  rw [screenVel_neg_ey]
  have hz : v 2 = (c - a * v 0) / b := by rw [hcdef]; field_simp; ring
  have hn0 : |n 0| ≤ ‖n‖ := by
    simpa using PiLp.norm_apply_le n 0
  have hinner : ⟪n, !₂[-v 2, 0]⟫ = -(n 0) * v 2 := by
    simp [PiLp.inner_apply, Fin.sum_univ_two]; ring
  rw [hinner, hz]
  have e1 : -(n 0) * ((c - a * v 0) / b) = -(n 0 * c) / b + (n 0 * v 0) * (a / b) := by
    field_simp; ring
  rw [e1]
  have e2 : -(n 0 * c) / b ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg <;> linarith
  have e3 : (n 0 * v 0) * (a / b) ≤ ‖n‖ * |v 0| * (a / b) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    calc n 0 * v 0 ≤ |n 0 * v 0| := le_abs_self _
      _ = |n 0| * |v 0| := abs_mul _ _
      _ ≤ ‖n‖ * |v 0| := mul_le_mul_of_nonneg_right hn0 (abs_nonneg _)
  linarith

end Minimality
