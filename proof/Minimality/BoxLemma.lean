module

public import Minimality.Global

@[expose] public section

/-! # Lemma R (box lemma) in Lean -/

namespace Minimality

open scoped RealInnerProductSpace

/-- Points of the plane that are positive-weight convex combinations of the outer projected vertices. -/
def PosComb (V : Finset ℝ³) (R₂ : Matrix (Fin 3) (Fin 3) ℝ) (q : ℝ²) : Prop :=
  ∃ μ : ℝ³ → ℝ, (∀ w ∈ V, 0 < μ w) ∧ ∑ w ∈ V, μ w = 1 ∧
    q = ∑ w ∈ V, μ w • proj_xy (R₂.toEuclideanLin w)

theorem PosComb.convex (V : Finset ℝ³) (R₂ : Matrix (Fin 3) (Fin 3) ℝ) :
    Convex ℝ {q : ℝ² | PosComb V R₂ q} := by
  intro p hp q hq a b ha hb hab
  obtain ⟨μ, hμ, hμ1, hp⟩ := hp
  obtain ⟨ν, hν, hν1, hq⟩ := hq
  refine ⟨fun w => a * μ w + b * ν w, ?_, ?_, ?_⟩
  · intro w hw
    have h1 := hμ w hw
    have h2 := hν w hw
    rcases ha.eq_or_lt with rfl | ha'
    · have : b = 1 := by linarith
      subst this; simpa using h2
    · nlinarith [mul_pos ha' h1, mul_nonneg hb h2.le]
  · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hμ1, hν1]; linarith
  · show a • p + b • q = _
    rw [hp, hq, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [smul_smul, smul_smul, add_smul]

/-- **Lemma R (box lemma), barycentric form.** -/
theorem isRupert_of_box (V : Finset ℝ³)
    (hsol : (interior (convexHull ℝ (V : Set ℝ³))).Nonempty)
    {R₁ R₂ : Matrix (Fin 3) (Fin 3) ℝ} (hR₁ : R₁ ∈ SO3) (hR₂ : R₂ ∈ SO3)
    (a b μ w c₀ c₁ L H : ℝ) (hL : 0 < L) (hH : 0 < H) (hμL : μ ≤ L) (hwH : w ≤ H)
    (hbox : ∀ v ∈ V, a ≤ (R₁.toEuclideanLin v) 0 ∧ (R₁.toEuclideanLin v) 0 ≤ a + μ ∧
      b ≤ (R₁.toEuclideanLin v) 1 ∧ (R₁.toEuclideanLin v) 1 ≤ b + w)
    (hcorner : ∀ s t : ℝ, (s = 0 ∨ s = 1) → (t = 0 ∨ t = 1) →
      PosComb V R₂ !₂[c₀ + s * L, c₁ + t * H]) :
    IsRupert V := by
  refine isRupert_of_pos_combinations V hsol hR₁ hR₂ !₂[c₀ - a, c₁ - b] ?_
  intro v hv
  obtain ⟨h1, h2, h3, h4⟩ := hbox v hv
  set x := (R₁.toEuclideanLin v) 0
  set y := (R₁.toEuclideanLin v) 1
  set s := (x - a) / L
  set t := (y - b) / H
  have hs0 : 0 ≤ s := div_nonneg (by linarith) hL.le
  have hs1 : s ≤ 1 := by rw [div_le_one hL]; linarith
  have ht0 : 0 ≤ t := div_nonneg (by linarith) hH.le
  have ht1 : t ≤ 1 := by rw [div_le_one hH]; linarith
  have hC := PosComb.convex V R₂
  have m0 : PosComb V R₂ (((1 - s) • !₂[c₀ + 0 * L, c₁ + 0 * H] + s • !₂[c₀ + 1 * L, c₁ + 0 * H])) :=
    hC (hcorner 0 0 (Or.inl rfl) (Or.inl rfl)) (hcorner 1 0 (Or.inr rfl) (Or.inl rfl))
      (show (0:ℝ) ≤ 1 - s by linarith) hs0 (by ring)
  have m1 : PosComb V R₂ (((1 - s) • !₂[c₀ + 0 * L, c₁ + 1 * H] + s • !₂[c₀ + 1 * L, c₁ + 1 * H])) :=
    hC (hcorner 0 1 (Or.inl rfl) (Or.inr rfl)) (hcorner 1 1 (Or.inr rfl) (Or.inr rfl))
      (show (0:ℝ) ≤ 1 - s by linarith) hs0 (by ring)
  have m := hC m0 m1 (show (0:ℝ) ≤ 1 - t by linarith) ht0 (by ring)
  obtain ⟨μ', hpos, hsum, heq⟩ := m
  refine ⟨μ', hpos, hsum, ?_⟩
  rw [← heq]
  ext i
  fin_cases i
  · simp [proj_xy, s, x]
    field_simp
    ring
  · simp [proj_xy, t, y]
    field_simp
    ring

/-- The frame matrix with rows `e`, `n`, `e × n`. -/
noncomputable def frameMat (e n : ℝ³) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![e 0, e 1, e 2; n 0, n 1, n 2; (cross e n) 0, (cross e n) 1, (cross e n) 2]

theorem frameMat_mem_SO3 (e n : ℝ³) (hee : ⟪e, e⟫ = 1) (hnn : ⟪n, n⟫ = 1) (hen : ⟪e, n⟫ = 0) :
    frameMat e n ∈ SO3 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial] at hee hnn hen
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
  have key : ∀ a0 a1 a2 b0 b1 b2 : ℝ, a0*a0+a1*a1+a2*a2=1 → b0*b0+b1*b1+b2*b2=1 →
      b0*a0+b1*a1+b2*a2=0 →
      (a1*b2-a2*b1)^2+(a2*b0-a0*b2)^2+(a0*b1-a1*b0)^2 = 1 := by
    intro a0 a1 a2 b0 b1 b2 hee hnn hen
    linear_combination (b0*b0+b1*b1+b2*b2)*hee + hnn - (a0*b0+a1*b1+a2*b2)*hen
  have hc := key _ _ _ _ _ _ hee hnn hen
  have hd : (frameMat e n).det = 1 := by
    simp only [frameMat, Matrix.det_fin_three, cross]
    simp
    linear_combination hc
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [frameMat, Matrix.mul_apply, Fin.sum_univ_three, cross] <;>
        first
          | ring1
          | linear_combination hee
          | linear_combination hnn
          | linear_combination hen
          | linear_combination hc
          | skip
  · exact hd

/-- **Lemma R (box lemma), frame form.** `e, n` orthonormal with all vertices in the box
`⟪e,p⟫ ∈ [a,a+μ]`, `⟪n,p⟫ ∈ [b,b+w]`; the outer view `R₂` has the rectangle
`[c₀,c₀+L]×[c₁,c₁+H]` (`μ ≤ L`, `w ≤ H`) with every corner a positive combination. -/
theorem isRupert_of_box_frame (V : Finset ℝ³)
    (hsol : (interior (convexHull ℝ (V : Set ℝ³))).Nonempty)
    (e n : ℝ³) (hee : ⟪e, e⟫ = 1) (hnn : ⟪n, n⟫ = 1) (hen : ⟪e, n⟫ = 0)
    {R₂ : Matrix (Fin 3) (Fin 3) ℝ} (hR₂ : R₂ ∈ SO3)
    (a b μ w c₀ c₁ L H : ℝ) (hL : 0 < L) (hH : 0 < H) (hμL : μ ≤ L) (hwH : w ≤ H)
    (hbox : ∀ v ∈ V, a ≤ ⟪e, v⟫ ∧ ⟪e, v⟫ ≤ a + μ ∧ b ≤ ⟪n, v⟫ ∧ ⟪n, v⟫ ≤ b + w)
    (hcorner : ∀ s t : ℝ, (s = 0 ∨ s = 1) → (t = 0 ∨ t = 1) →
      PosComb V R₂ !₂[c₀ + s * L, c₁ + t * H]) :
    IsRupert V := by
  refine isRupert_of_box V hsol (frameMat_mem_SO3 e n hee hnn hen) hR₂ a b μ w c₀ c₁ L H
    hL hH hμL hwH ?_ hcorner
  intro v hv
  have h0 : (Matrix.toEuclideanLin (frameMat e n) v) 0 = ⟪e, v⟫ := by
    simp [frameMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three, PiLp.inner_apply]; ring
  have h1 : (Matrix.toEuclideanLin (frameMat e n) v) 1 = ⟪n, v⟫ := by
    simp [frameMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three, PiLp.inner_apply]; ring
  rw [h0, h1]; exact hbox v hv

end Minimality

end
