module

public import MinimalityExtra.TetraViews

/-!
# First-order freedom depends on the metric (proof of `ExistsMetricChangingFreedom`)

The tetrahedron `TX` of `TetraViews` with its free two-peaked view `WB = (-7,4,6)`
(`freeB`), and the matrix `AM = [[2,0,-2],[-1,0,0],[1,1,1]]` (determinant `2`). The image
`TY = AM TX` with view `WY = AM WB = (-26,7,3)` has the same rim `0,1,2,3` and depths
`0,109,57,58` in the same order as `0,11,9,10`, but is rigid: a certificate at a vertex gives
the two true rim inequalities (case split), and a positive combination of six of them
vanishes (the weights were found by an LP, closed by `linarith`).
-/

@[expose] public section

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

namespace MinimalityExtra
open scoped RealInnerProductSpace
open Finset

def AM : Matrix (Fin 3) (Fin 3) ℝ := !![2, 0, -2; -1, 0, 0; 1, 1, 1]

noncomputable def TY : Fin 4 → ℝ³ :=
  ![!₂[0, 0, 0], !₂[-4, -1, 4], !₂[-2, -1, 4], !₂[-2, 0, 2]]
noncomputable def WY : ℝ³ := !₂[-26, 7, 3]

theorem AM_det : 0 < AM.det := by
  simp [AM, Matrix.det_fin_three]

theorem AM_apply (u : ℝ³) :
    Matrix.toEuclideanLin AM u = !₂[2 * u 0 - 2 * u 2, - u 0, u 0 + u 1 + u 2] := by
  ext j
  fin_cases j <;>
    simp [AM, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

theorem AM_TX (i : Fin 4) : Matrix.toEuclideanLin AM (TX i) = TY i := by
  rw [AM_apply]
  rcases all4 i with rfl | rfl | rfl | rfl <;> (ext j; fin_cases j <;> norm_num [TX, TY])

theorem AM_WB : Matrix.toEuclideanLin AM WB = WY := by
  rw [AM_apply]; ext j; fin_cases j <;> norm_num [WB, WY]

set_option maxHeartbeats 1600000 in
/-- At view `WY`, a certificate at vertex `i` gives the two inequalities of the true rim. -/
theorem certY (ω τ : ℝ³) (i : Fin 4) (h : TiltCert (univ.image TY) WY ω τ (TY i)) :
    0 < det3 (TY (![1, 2, 3, 0] i) - TY i) (cross ω (TY i) + τ) WY ∧
    0 < det3 (TY i - TY (![3, 0, 1, 2] i)) (cross ω (TY i) + τ) WY := by
  rcases h with ⟨y0, hy0, y1, hy1, h1, h2, h3⟩ | ⟨a, ha, b, hb, c, hc, h1, h2, h3, h4⟩
  · simp only [Finset.mem_image, Finset.mem_univ, true_and] at hy0 hy1
    obtain ⟨j0, rfl⟩ := hy0
    obtain ⟨j1, rfl⟩ := hy1
    rcases all4 i with rfl | rfl | rfl | rfl <;> rcases all4 j0 with rfl | rfl | rfl | rfl <;>
      rcases all4 j1 with rfl | rfl | rfl | rfl <;>
      norm_num [det3, cross, TY, WY] at h1 <;> norm_num [det3, cross, TY, WY] at h2 <;>
      norm_num [det3, cross, TY, WY] at h3 <;> refine ⟨?_, ?_⟩ <;>
      norm_num [det3, cross, TY, WY] <;> linarith
  · simp only [Finset.mem_image, Finset.mem_univ, true_and] at ha hb hc
    obtain ⟨j0, rfl⟩ := ha
    obtain ⟨j1, rfl⟩ := hb
    obtain ⟨j2, rfl⟩ := hc
    rcases all4 i with rfl | rfl | rfl | rfl <;> rcases all4 j0 with rfl | rfl | rfl | rfl <;>
      rcases all4 j1 with rfl | rfl | rfl | rfl <;> rcases all4 j2 with rfl | rfl | rfl | rfl <;>
      norm_num [det3, TY, WY] at h1 <;> norm_num [det3, TY, WY] at h2 <;>
      norm_num [det3, TY, WY] at h3 <;> norm_num [det3, TY, WY] at h4

/-- Rigid at `WY`: a positive combination of the next-side inequalities at vertices 0, 2, 3 and
the previous-side inequalities at vertices 0, 1, 2 vanishes. -/
theorem rigidY : ¬ FreeAt (univ.image TY) WY := by
  rintro ⟨ω, τ, h⟩
  have m : ∀ i, TY i ∈ univ.image TY := fun i => Finset.mem_image_of_mem _ (Finset.mem_univ i)
  have a0 := (certY ω τ 0 (h _ (m 0))).1
  have b0 := (certY ω τ 0 (h _ (m 0))).2
  have b1 := (certY ω τ 1 (h _ (m 1))).2
  have a2 := (certY ω τ 2 (h _ (m 2))).1
  have b2 := (certY ω τ 2 (h _ (m 2))).2
  have a3 := (certY ω τ 3 (h _ (m 3))).1
  norm_num [det3, cross, TY, WY] at a0 b0 b1 a2 b2 a3
  linarith

theorem peaks_Y (z : ZMod 4 → ℝ) (h0 : z 0 = 0) (h1 : z 1 = 109) (h2 : z 2 = 57) (h3 : z 3 = 58) :
    IsCyclicTwoPeaked z := by
  have e0 : ((0 : ZMod 4) - 1) = 3 := by decide
  have e1 : ((1 : ZMod 4) - 1) = 0 := by decide
  have e2 : ((2 : ZMod 4) - 1) = 1 := by decide
  have e3 : ((3 : ZMod 4) - 1) = 2 := by decide
  have f0 : ((0 : ZMod 4) + 1) = 1 := by decide
  have f1 : ((1 : ZMod 4) + 1) = 2 := by decide
  have f2 : ((2 : ZMod 4) + 1) = 3 := by decide
  have f3 : ((3 : ZMod 4) + 1) = 0 := by decide
  refine ⟨?_, Finset.card_eq_two.2 ⟨1, 3, by decide, ?_⟩⟩
  · intro a b hab
    rcases all4z a with rfl | rfl | rfl | rfl <;> rcases all4z b with rfl | rfl | rfl | rfl <;>
      first | rfl | (exfalso; simp only [h0, h1, h2, h3] at hab; norm_num at hab)
  · ext i
    rcases all4z i with rfl | rfl | rfl | rfl <;>
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton, e0, e1, e2, e3,
        f0, f1, f2, f3, h0, h1, h2, h3] <;> norm_num <;> decide

theorem strictY : StrictRimN (k := 4) TY WY (![0, 1, 2, 3] : ZMod 4 → Fin 4) := by
  intro m i h1 h2
  rcases all4z i with rfl | rfl | rfl | rfl <;> fin_cases m <;>
    first | exact absurd rfl h1 | exact absurd rfl h2 | skip
  all_goals norm_num [det3, TY, WY]

theorem strictX : StrictRimN (k := 4) TX WB (![0, 1, 2, 3] : ZMod 4 → Fin 4) := by
  intro m i h1 h2
  rcases all4z i with rfl | rfl | rfl | rfl <;> fin_cases m <;>
    first | exact absurd rfl h1 | exact absurd rfl h2 | skip
  all_goals norm_num [det3, TX, WB]

theorem dX (i : Fin 4) : ⟪TX i, WB⟫ = ![(0:ℝ), 11, 9, 10] i := by
  rcases all4 i with rfl | rfl | rfl | rfl <;>
    simp [TX, WB, PiLp.inner_apply, Fin.sum_univ_three] <;> norm_num

theorem dY (i : Fin 4) : ⟪TY i, WY⟫ = ![(0:ℝ), 109, 57, 58] i := by
  rcases all4 i with rfl | rfl | rfl | rfl <;>
    simp [TY, WY, PiLp.inner_apply, Fin.sum_univ_three] <;> norm_num

theorem existsMetricChangingFreedom : ExistsMetricChangingFreedom := by
  have hf : (fun i : Fin 4 => Matrix.toEuclideanLin AM (TX i)) = TY := funext AM_TX
  refine ⟨TX, WB, (![0, 1, 2, 3] : ZMod 4 → Fin 4), AM, tx_noncoplanar, AM_det, inj4 _ (by decide), strictX, ?_,
    ?_, ?_, ?_, freeB, ?_⟩
  · rw [hf, AM_WB]; exact strictY
  · exact peaks_B _ (by simpa using dX 0) (by simpa using dX 1) (by simpa using dX 2)
      (by simpa using dX 3)
  · rw [AM_WB]; simp only [AM_TX]
    exact peaks_Y _ (by simpa using dY 0) (by simpa using dY 1) (by simpa using dY 2)
      (by simpa using dY 3)
  · intro i j
    rw [AM_WB]; simp only [AM_TX]
    simp only [dX, dY]
    rcases all4z i with rfl | rfl | rfl | rfl <;> rcases all4z j with rfl | rfl | rfl | rfl <;>
      norm_num
  · rw [hf, AM_WB]; exact rigidY

end MinimalityExtra

#print axioms MinimalityExtra.existsMetricChangingFreedom
