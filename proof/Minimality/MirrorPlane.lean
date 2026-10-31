module

public import Minimality.FirstOrder

@[expose] public section

/-!
# Lemma MP: views in a mirror plane are never first-order free

nopert229/out/bottleneck/clopen/draft.md §6.  If `V` is invariant under `y ↦ −y`, no first-order motion is
strictly inward at the view `e_z` (which lies in the mirror plane): averaging a free motion with its mirror image
gives a symmetric one, whose screen velocities are horizontal, so it cannot move the top of the shadow inward
(`not_firstOrderInward_of_mirror`).
-/

namespace Minimality

open scoped RealInnerProductSpace

/-- The mirror `(x, y) ↦ (x, -y)` of the screen. -/
noncomputable def mirS (p : ℝ²) : ℝ² := !₂[p 0, -p 1]

/-- The mirror `y ↦ -y` of space, as a linear map. -/
noncomputable def mirL : ℝ³ →ₗ[ℝ] ℝ³ :=
  Matrix.toEuclideanLin !![1, 0, 0; 0, -1, 0; 0, 0, 1]

theorem mirL_apply (x : ℝ³) : mirL x = !₂[x 0, -x 1, x 2] := by
  ext i
  fin_cases i <;> simp [mirL, Matrix.toLpLin_apply, dotProduct, Fin.sum_univ_three,
    Matrix.mulVec, Matrix.vecHead, Matrix.vecTail]

theorem mirS_mirS (p : ℝ²) : mirS (mirS p) = p := by
  ext i; fin_cases i <;> simp [mirS]

theorem mirS_add_smul (p d : ℝ²) (t : ℝ) : mirS (p + t • d) = mirS p + t • mirS d := by
  ext i; fin_cases i <;> simp [mirS] <;> ring

theorem continuous_mirS : Continuous mirS := by
  have : mirS = fun p : ℝ² => p - (2 * p 1) • (!₂[0, 1] : ℝ²) := by
    funext p; ext i; fin_cases i <;> simp [mirS] <;> ring
  rw [this]
  have h1 : Continuous fun p : ℝ² => p 1 := by fun_prop
  fun_prop

theorem proj_mir (x : ℝ³) : proj_xy (mirL x) = mirS (proj_xy x) := by
  ext i; fin_cases i <;> simp [proj_xy, mirS, mirL_apply]

theorem screenVel_mir (ω τ x : ℝ³) :
    screenVel ω τ (mirL x) = mirS (screenVel !₂[-ω 0, ω 1, -ω 2] !₂[τ 0, -τ 1, τ 2] x) := by
  ext i
  fin_cases i <;> simp [screenVel, proj_xy, mirS, mirL_apply, crossMatrix, Matrix.toLpLin_apply,
    dotProduct, Fin.sum_univ_three] <;> ring

theorem screenVel_avg (ω τ ω' τ' x : ℝ³) :
    screenVel ((1/2 : ℝ) • (ω + ω')) ((1/2 : ℝ) • (τ + τ')) x
      = (1/2 : ℝ) • (screenVel ω τ x + screenVel ω' τ' x) := by
  ext i
  fin_cases i <;> simp [screenVel, proj_xy, crossMatrix, Matrix.toLpLin_apply,
    dotProduct, Fin.sum_univ_three] <;> ring

theorem avg_inward {S : Set ℝ²} (hS : Convex ℝ S) {p d₁ d₂ : ℝ²} (hp : p ∈ closure S)
    (h₁ : IsInwardAt S p d₁) (h₂ : IsInwardAt S p d₂) :
    IsInwardAt S p ((1/2 : ℝ) • (d₁ + d₂)) := by
  obtain ⟨t, ⟨ht1, ht2⟩, ht⟩ := (((h₁.eventually hS hp).and (h₂.eventually hS hp)).and
    self_mem_nhdsWithin).exists
  refine ⟨t, ht, ?_⟩
  have := hS.interior ht1 ht2 (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num)
  convert this using 1
  module

theorem not_firstOrderInward_of_mirror (V : Finset ℝ³) (hne : V.Nonempty)
    (hρ : ∀ v ∈ V, !₂[v 0, -v 1, v 2] ∈ V) (ω τ : ℝ³) : ¬ FirstOrderInward V ω τ := by
  intro hin
  set S := proj_xy '' convexHull ℝ (V : Set ℝ³) with hSdef
  have hSc : Convex ℝ S := (convex_convexHull ℝ _).linear_image projL
  have hSσ : ∀ y ∈ S, mirS y ∈ S := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨mirL x, ?_, proj_mir x⟩
    have h1 : mirL '' (V : Set ℝ³) ⊆ V := by
      rintro _ ⟨v, hv, rfl⟩
      rw [mirL_apply]; exact hρ v hv
    have := convexHull_mono (𝕜 := ℝ) h1
    rw [← LinearMap.image_convexHull] at this
    exact this ⟨x, hx, rfl⟩
  have hint : ∀ q ∈ interior S, mirS q ∈ interior S := by
    have : mirS ⁻¹' interior S ⊆ interior S := by
      apply interior_maximal
      · intro q hq
        have := hSσ _ (interior_subset hq)
        rwa [mirS_mirS] at this
      · exact isOpen_interior.preimage continuous_mirS
    intro q hq
    exact this (by simpa [mirS_mirS] using hq)
  obtain ⟨v, hv, hmax⟩ := Finset.exists_max_image V (fun v => v 1) hne
  have hvS : proj_xy v ∈ S := ⟨v, subset_convexHull ℝ _ hv, rfl⟩
  -- the mirrored motion is inward at v
  have hin1 := hin v hv
  have hin2 : IsInwardAt S (proj_xy v)
      (screenVel !₂[-ω 0, ω 1, -ω 2] !₂[τ 0, -τ 1, τ 2] v) := by
    obtain ⟨ε, hε, hm⟩ := hin (mirL v) (by rw [mirL_apply]; exact hρ v hv)
    rw [proj_mir, screenVel_mir, ← mirS_add_smul] at hm
    refine ⟨ε, hε, ?_⟩
    simpa [mirS_mirS] using hint _ hm
  have hav := avg_inward hSc (subset_closure hvS) hin1 hin2
  rw [← screenVel_avg] at hav
  obtain ⟨ε, hε, hq⟩ := hav
  -- half-space bound
  have hbound : ∀ y ∈ S, y 1 ≤ v 1 := by
    rintro _ ⟨x, hx, rfl⟩
    have hsub : convexHull ℝ (V : Set ℝ³) ⊆ (EuclideanSpace.proj 1 : ℝ³ →L[ℝ] ℝ) ⁻¹' Set.Iic (v 1) := by
      apply convexHull_min
      · intro w hw
        exact hmax w hw
      · exact (convex_Iic _).linear_preimage (EuclideanSpace.proj 1 : ℝ³ →L[ℝ] ℝ).toLinearMap
    exact hsub hx
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior _ hq
  set q := proj_xy v + ε • screenVel ((1/2 : ℝ) • (ω + !₂[-ω 0, ω 1, -ω 2]))
    ((1/2 : ℝ) • (τ + !₂[τ 0, -τ 1, τ 2])) v with hqdef
  have hq1 : q 1 = v 1 := by
    simp [hqdef, screenVel, proj_xy, crossMatrix, Matrix.toLpLin_apply, dotProduct,
      Fin.sum_univ_three]
  have hmem : q + (r / 2) • (EuclideanSpace.single 1 1 : ℝ²) ∈ interior S := by
    apply hball
    rw [Metric.mem_ball, dist_eq_norm]
    rw [add_sub_cancel_left, norm_smul, EuclideanSpace.norm_single, norm_one, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
    linarith
  have := hbound _ (interior_subset hmem)
  simp [hq1] at this
  linarith

end Minimality
