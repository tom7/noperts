module

public import SmallRupert.Octahedron

@[expose] public section

/-!
# Theorem 7.7: translation prisms

`K = T + [0, w]` over a triangle `T = ABC`.  At suitable views the silhouette
is the pentagon `X Z Y (Y + w) (X + w)` with `Z + w` hidden, and its depths
`x, ζ, y, y + δ, x + δ` (`δ = u·w > 0`) are unimodal iff `ζ < max(x, y)`.
-/

namespace SmallRupert

open scoped RealInnerProductSpace Topology
open Finset Filter

/-! ### 5-cycles -/

/-- The 5-cycle `p₀ p₁ p₂ p₃ p₄`. -/
def quint {α : Type*} (p₀ p₁ p₂ p₃ p₄ : α) : ZMod 5 → α := ![p₀, p₁, p₂, p₃, p₄]

section quint
variable {α : Type*} (p₀ p₁ p₂ p₃ p₄ : α)
theorem quint_0 : quint p₀ p₁ p₂ p₃ p₄ 0 = p₀ := rfl
theorem quint_1 : quint p₀ p₁ p₂ p₃ p₄ 1 = p₁ := rfl
theorem quint_2 : quint p₀ p₁ p₂ p₃ p₄ 2 = p₂ := rfl
theorem quint_3 : quint p₀ p₁ p₂ p₃ p₄ 3 = p₃ := rfl
theorem quint_4 : quint p₀ p₁ p₂ p₃ p₄ 4 = p₄ := rfl
end quint

theorem zmod5_add_one :
    (0 : ZMod 5) + 1 = 1 ∧ (1 : ZMod 5) + 1 = 2 ∧ (2 : ZMod 5) + 1 = 3 ∧ (3 : ZMod 5) + 1 = 4 ∧
      (4 : ZMod 5) + 1 = 0 := by decide

theorem zmod5_sub_one :
    (0 : ZMod 5) - 1 = 4 ∧ (1 : ZMod 5) - 1 = 0 ∧ (2 : ZMod 5) - 1 = 1 ∧ (3 : ZMod 5) - 1 = 2 ∧
      (4 : ZMod 5) - 1 = 3 := by decide

theorem zmod5_cases (i : ZMod 5) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by revert i; decide

/-- The open depth condition of the prism pentagon `X X' Y' Y Z`: the lifts
`X → X'`, `Y → Y'` go up and `Z` is below `X` or `Y`. -/
def PentaCond (z : ZMod 5 → ℝ) : Prop := z 0 < z 1 ∧ z 3 < z 2 ∧ (z 4 < z 0 ∨ z 4 < z 3)

theorem isOpen_pentaCond : IsOpen {z : ZMod 5 → ℝ | PentaCond z} := by
  have hlt : ∀ i j : ZMod 5, IsOpen {z : ZMod 5 → ℝ | z i < z j} := fun i j =>
    isOpen_lt (continuous_apply i) (continuous_apply j)
  simp only [PentaCond, Set.setOf_and, Set.setOf_or]
  exact (hlt 0 1).inter ((hlt 3 2).inter ((hlt 4 0).union (hlt 4 3)))

theorem isCyclicUnimodal_five {z : ZMod 5 → ℝ} (hinj : Function.Injective z) (h : PentaCond z) :
    IsCyclicUnimodal z := by
  obtain ⟨h01, h32, h4⟩ := h
  obtain ⟨a0, a1, a2, a3, a4⟩ := zmod5_add_one
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_sub_one
  have hmem : ∀ i, z (i - 1) < z i ∧ z (i + 1) < z i → i = 1 ∨ i = 2 := by
    intro i hi
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
    · rw [a0] at hi; linarith [hi.2]
    · exact Or.inl rfl
    · exact Or.inr rfl
    · rw [b3] at hi; linarith [hi.1]
    · rw [b4, a4] at hi; rcases h4 with h4 | h4 <;> linarith [hi.1, hi.2]
  refine ⟨hinj, le_antisymm ?_ ?_⟩
  · rw [Finset.card_le_one]
    intro i hi j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    rcases hmem i hi with rfl | rfl <;> rcases hmem j hj with rfl | rfl
    · rfl
    · rw [b2] at hj; rw [a1] at hi; linarith [hi.2, hj.1]
    · rw [b2] at hi; rw [a1] at hj; linarith [hi.1, hj.2]
    · rfl
  · obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ z ⟨0, Finset.mem_univ _⟩
    have c1 : ∀ m : ZMod 5, m - 1 ≠ m := by decide
    have c2 : ∀ m : ZMod 5, m + 1 ≠ m := by decide
    refine Finset.card_pos.mpr ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩⟩
    · exact lt_of_le_of_ne (hm _ (Finset.mem_univ _)) (hinj.ne (c1 m))
    · exact lt_of_le_of_ne (hm _ (Finset.mem_univ _)) (hinj.ne (c2 m))

/-! ### The prism pentagon -/

/-- The shadow pentagon `X, X + s, Y + s, Y, Z` of a translation prism is
strictly convex and counterclockwise, with `Z + s` inside, when `Z` lies
strictly between `X` and `Y` across `s` and on the far side of `XY` from `s`. -/
theorem pentagon {X Y Z s : ℝ²} (h1 : 0 < cross2 s (Z - X)) (h2 : 0 < cross2 s (Y - Z))
    (h3 : 0 < cross2 (Y - X) (Z - X)) :
    IsCcwPolygon (quint X (X + s) (Y + s) Y Z) ∧
      ∀ i, 0 < cross2 (quint X (X + s) (Y + s) Y Z (i + 1) - quint X (X + s) (Y + s) Y Z i)
        (Z + s - quint X (X + s) (Y + s) Y Z i) := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := zmod5_add_one
  have hcase : ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      (i = 0 ∧ (j = 2 ∨ j = 3 ∨ j = 4)) ∨ (i = 1 ∧ (j = 3 ∨ j = 4 ∨ j = 0)) ∨
      (i = 2 ∧ (j = 4 ∨ j = 0 ∨ j = 1)) ∨ (i = 3 ∧ (j = 0 ∨ j = 1 ∨ j = 2)) ∨
      (i = 4 ∧ (j = 1 ∨ j = 2 ∨ j = 3)) := by decide
  simp only [cross2, PiLp.sub_apply] at h1 h2 h3
  refine ⟨⟨by norm_num, fun i j hji hji' => ?_⟩, fun i => ?_⟩
  · rcases hcase i j hji hji' with ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ |
      ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ <;>
    simp only [a0, a1, a2, a3, a4, quint_0, quint_1, quint_2, quint_3, quint_4, cross2,
      PiLp.add_apply, PiLp.sub_apply] <;> linarith
  · rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    simp only [a0, a1, a2, a3, a4, quint_0, quint_1, quint_2, quint_3, quint_4, cross2,
      PiLp.add_apply, PiLp.sub_apply] <;> linarith

theorem quint_injective {α : Type*} {p₀ p₁ p₂ p₃ p₄ : α} (h01 : p₀ ≠ p₁) (h02 : p₀ ≠ p₂)
    (h03 : p₀ ≠ p₃) (h04 : p₀ ≠ p₄) (h12 : p₁ ≠ p₂) (h13 : p₁ ≠ p₃) (h14 : p₁ ≠ p₄)
    (h23 : p₂ ≠ p₃) (h24 : p₂ ≠ p₄) (h34 : p₃ ≠ p₄) :
    Function.Injective (quint p₀ p₁ p₂ p₃ p₄) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals first
    | rfl
    | exact absurd hij h01
    | exact absurd hij h02
    | exact absurd hij h03
    | exact absurd hij h04
    | exact absurd hij h12
    | exact absurd hij h13
    | exact absurd hij h14
    | exact absurd hij h23
    | exact absurd hij h24
    | exact absurd hij h34
    | exact absurd hij.symm h01
    | exact absurd hij.symm h02
    | exact absurd hij.symm h03
    | exact absurd hij.symm h04
    | exact absurd hij.symm h12
    | exact absurd hij.symm h13
    | exact absurd hij.symm h14
    | exact absurd hij.symm h23
    | exact absurd hij.symm h24
    | exact absurd hij.symm h34

/-! ### The tilted view -/

theorem proj_rotX_mul (c s : ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ) (v : ℝ³) :
    proj_xy ((rotX c s * R).toEuclideanLin v) =
      !₂[(R.toEuclideanLin v) 0, c * (R.toEuclideanLin v) 1 - s * (R.toEuclideanLin v) 2] := by
  have e : (rotX c s * R).toEuclideanLin v = (rotX c s).toEuclideanLin (R.toEuclideanLin v) := by
    simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
  rw [e]
  generalize R.toEuclideanLin v = u
  ext i; fin_cases i <;>
    simp [proj_xy, rotX, Matrix.toLpLin_apply, dotProduct, Fin.sum_univ_three]; ring

theorem depth_rotX_mul (c s : ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ) (v : ℝ³) :
    ((rotX c s * R).toEuclideanLin v) 2 =
      s * (R.toEuclideanLin v) 1 + c * (R.toEuclideanLin v) 2 := by
  have e : (rotX c s * R).toEuclideanLin v = (rotX c s).toEuclideanLin (R.toEuclideanLin v) := by
    simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
  rw [e]
  generalize R.toEuclideanLin v = u
  simp [rotX, Matrix.toLpLin_apply, dotProduct, Fin.sum_univ_three]

/-- **Translation prisms at a tilted view.**  In the frame of `R₁` (with `w`
vertical and pointing up), `Z` is strictly between `X` and `Y` in the first
coordinate and above the line `XY`, and for small tilts `ε > 0` towards the
second axis `Z` is deeper than `X` or `Y`.  Then the prism is Rupert. -/
theorem isRupert_prism_view {X Y Z w : ℝ³} {R₁ : Matrix (Fin 3) (Fin 3) ℝ} (hR₁ : R₁ ∈ SO3) {lam : ℝ} (hlam : 0 < lam)
    (hw : R₁.toEuclideanLin w = lam • ez)
    (h1 : (R₁.toEuclideanLin X) 0 < (R₁.toEuclideanLin Z) 0)
    (h2 : (R₁.toEuclideanLin Z) 0 < (R₁.toEuclideanLin Y) 0)
    (h3 : 0 < cross2 (proj_xy (R₁.toEuclideanLin Y) - proj_xy (R₁.toEuclideanLin X))
      (proj_xy (R₁.toEuclideanLin Z) - proj_xy (R₁.toEuclideanLin X)))
    (h4 : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      Real.sin ε * (R₁.toEuclideanLin Z) 1 + Real.cos ε * (R₁.toEuclideanLin Z) 2 <
        Real.sin ε * (R₁.toEuclideanLin X) 1 + Real.cos ε * (R₁.toEuclideanLin X) 2 ∨
      Real.sin ε * (R₁.toEuclideanLin Z) 1 + Real.cos ε * (R₁.toEuclideanLin Z) 2 <
        Real.sin ε * (R₁.toEuclideanLin Y) 1 + Real.cos ε * (R₁.toEuclideanLin Y) 2) :
    IsRupert {X, Y, Z, X + w, Y + w, Z + w} := by
  classical
  have hw0 : (R₁.toEuclideanLin w) 0 = 0 := by rw [hw]; simp [ez]
  have hw1 : (R₁.toEuclideanLin w) 1 = 0 := by rw [hw]; simp [ez]
  have hw2 : (R₁.toEuclideanLin w) 2 = lam := by rw [hw]; simp [ez]
  -- the projected orientation persists for small tilts
  set F : ℝ → ℝ := fun ε => ((R₁.toEuclideanLin Y) 0 - (R₁.toEuclideanLin X) 0) *
    ((Real.cos ε * (R₁.toEuclideanLin Z) 1 - Real.sin ε * (R₁.toEuclideanLin Z) 2) -
    (Real.cos ε * (R₁.toEuclideanLin X) 1 - Real.sin ε * (R₁.toEuclideanLin X) 2)) -
    ((Real.cos ε * (R₁.toEuclideanLin Y) 1 - Real.sin ε * (R₁.toEuclideanLin Y) 2) -
    (Real.cos ε * (R₁.toEuclideanLin X) 1 - Real.sin ε * (R₁.toEuclideanLin X) 2)) *
    ((R₁.toEuclideanLin Z) 0 - (R₁.toEuclideanLin X) 0) with hF
  have hF0 : 0 < F 0 := by
    simp only [hF, Real.cos_zero, Real.sin_zero, one_mul, zero_mul, sub_zero]
    simpa [cross2, proj_xy] using h3
  have hFc : Continuous F := by rw [hF]; fun_prop
  have h3e : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < F ε :=
    (hFc.continuousAt.eventually (lt_mem_nhds hF0)).filter_mono nhdsWithin_le_nhds
  obtain ⟨ε, ⟨hε0, hε1⟩, hFε, h4ε⟩ :=
    ((show ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Set.Ioo 0 (Real.pi / 2) from
      Ioo_mem_nhdsGT (by positivity)).and (h3e.and h4)).exists
  have hs : 0 < Real.sin ε := Real.sin_pos_of_pos_of_lt_pi hε0 (by linarith [Real.pi_pos])
  have hc : 0 < Real.cos ε := Real.cos_pos_of_mem_Ioo ⟨by linarith, hε1⟩
  set R₀ := rotX (Real.cos ε) (Real.sin ε) * R₁ with hR₀def
  have hR₀ : R₀ ∈ SO3 :=
    mul_mem (rotX_mem_SO3 (by rw [add_comm]; exact Real.sin_sq_add_cos_sq ε)) hR₁
  have hP : ∀ v, proj_xy (R₀.toEuclideanLin v) = !₂[(R₁.toEuclideanLin v) 0,
      Real.cos ε * (R₁.toEuclideanLin v) 1 - Real.sin ε * (R₁.toEuclideanLin v) 2] :=
    fun v => proj_rotX_mul _ _ _ v
  have hD : ∀ v, (R₀.toEuclideanLin v) 2 =
      Real.sin ε * (R₁.toEuclideanLin v) 1 + Real.cos ε * (R₁.toEuclideanLin v) 2 :=
    fun v => depth_rotX_mul _ _ _ v
  set S := proj_xy (R₀.toEuclideanLin w) with hS
  have hPadd : ∀ v, proj_xy (R₀.toEuclideanLin (v + w)) = proj_xy (R₀.toEuclideanLin v) + S := by
    intro v; rw [map_add, proj_xy_add']
  have hS0 : S 0 = 0 := by rw [hS, hP]; simp [hw0]
  have hS1 : S 1 = -(Real.sin ε * lam) := by rw [hS, hP]; simp [hw1, hw2]
  -- the pentagon
  have hpent := pentagon (X := proj_xy (R₀.toEuclideanLin X)) (Y := proj_xy (R₀.toEuclideanLin Y))
    (Z := proj_xy (R₀.toEuclideanLin Z)) (s := S)
    (by
      simp only [cross2, PiLp.sub_apply, hS0, hS1, hP, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      nlinarith [mul_pos hs hlam])
    (by
      simp only [cross2, PiLp.sub_apply, hS0, hS1, hP, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      nlinarith [mul_pos hs hlam])
    (by
      simp only [cross2, PiLp.sub_apply, hP, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      exact hFε)
  set V : Finset ℝ³ := {X, Y, Z, X + w, Y + w, Z + w} with hV
  have hxV : ∀ i, quint X (X + w) (Y + w) Y Z i ∈ V := by
    intro i; rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;> simp [hV, quint_0,
      quint_1, quint_2, quint_3, quint_4]
  have hPx : (fun i => proj_xy (R₀.toEuclideanLin (quint X (X + w) (Y + w) Y Z i))) =
      quint (proj_xy (R₀.toEuclideanLin X)) (proj_xy (R₀.toEuclideanLin X) + S)
        (proj_xy (R₀.toEuclideanLin Y) + S) (proj_xy (R₀.toEuclideanLin Y))
        (proj_xy (R₀.toEuclideanLin Z)) := by
    funext i
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
    · rfl
    · exact hPadd X
    · exact hPadd Y
    · rfl
    · rfl
  -- the corners are distinct since their projections are
  have hinj : Function.Injective (quint X (X + w) (Y + w) Y Z) := by
    intro i j hij
    apply hpent.1.injective
    rw [← congrFun hPx i, ← congrFun hPx j]
    simp only [hij]
  refine isRupert_of_open_unimodal V hR₀ (quint X (X + w) (Y + w) Y Z) hxV hinj ?_ ?_ PentaCond
    isOpen_pentaCond ?_ (fun z hz hQ => isCyclicUnimodal_five hz hQ)
  · rw [hPx]; exact hpent.1
  · intro v hv hvx i
    have hPi := fun j => congrFun hPx j
    rw [hPi, hPi]
    have hvZ : v = Z + w := by
      simp only [hV, mem_insert, mem_singleton] at hv
      have e0 := hvx 0; have e1 := hvx 1; have e2 := hvx 2; have e3 := hvx 3; have e4 := hvx 4
      change v ≠ X at e0; change v ≠ X + w at e1; change v ≠ Y + w at e2; change v ≠ Y at e3
      change v ≠ Z at e4
      tauto
    rw [hvZ, hPadd]; exact hpent.2 i
  · have hdw : (R₀.toEuclideanLin w) 2 = Real.cos ε * lam := by rw [hD, hw1, hw2]; ring
    have hpos : 0 < Real.cos ε * lam := mul_pos hc hlam
    refine ⟨?_, ?_, ?_⟩
    · show (R₀.toEuclideanLin X) 2 < (R₀.toEuclideanLin (X + w)) 2
      rw [map_add, PiLp.add_apply, hdw]; linarith
    · show (R₀.toEuclideanLin Y) 2 < (R₀.toEuclideanLin (Y + w)) 2
      rw [map_add, PiLp.add_apply, hdw]; linarith
    · show (R₀.toEuclideanLin Z) 2 < (R₀.toEuclideanLin X) 2 ∨
        (R₀.toEuclideanLin Z) 2 < (R₀.toEuclideanLin Y) 2
      rw [hD, hD, hD]; exact h4ε

theorem rotZ_mul_apply (c s : ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ) (v : ℝ³) :
    (rotZ c s * R).toEuclideanLin v = !₂[c * (R.toEuclideanLin v) 0 - s * (R.toEuclideanLin v) 1,
      s * (R.toEuclideanLin v) 0 + c * (R.toEuclideanLin v) 1, (R.toEuclideanLin v) 2] := by
  have e : (rotZ c s * R).toEuclideanLin v = (rotZ c s).toEuclideanLin (R.toEuclideanLin v) := by
    simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
  rw [e]
  generalize R.toEuclideanLin v = u
  ext i; fin_cases i <;> simp [rotZ, Matrix.toLpLin_apply, dotProduct, Fin.sum_univ_three] <;> ring

/-- **Translation prisms in a frame with `w` vertical.**  In the frame of `R`
(`R w = λ e_z`, `λ > 0`), with screen projections `p`, a direction `a` puts the
projection of `Z` strictly between those of `X` and `Y`, `Z` lies left of
`XY`, and either `Z` is strictly below `X` or `Y` in depth, or `X, Z` have equal
depth and `Z` is behind `X` across `a`.  Then the prism is Rupert. -/
theorem isRupert_prism_frame {X Y Z w : ℝ³} {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ SO3)
    {lam : ℝ} (hlam : 0 < lam) (hw : R.toEuclideanLin w = lam • ez) (a : ℝ²)
    (ha1 : 0 < ⟪a, proj_xy (R.toEuclideanLin Z) - proj_xy (R.toEuclideanLin X)⟫)
    (ha2 : 0 < ⟪a, proj_xy (R.toEuclideanLin Y) - proj_xy (R.toEuclideanLin Z)⟫)
    (h3 : 0 < cross2 (proj_xy (R.toEuclideanLin Y) - proj_xy (R.toEuclideanLin X))
      (proj_xy (R.toEuclideanLin Z) - proj_xy (R.toEuclideanLin X)))
    (h4 : ((R.toEuclideanLin Z) 2 < (R.toEuclideanLin X) 2 ∨
        (R.toEuclideanLin Z) 2 < (R.toEuclideanLin Y) 2) ∨
      ((R.toEuclideanLin Z) 2 = (R.toEuclideanLin X) 2 ∧
        cross2 a (proj_xy (R.toEuclideanLin Z) - proj_xy (R.toEuclideanLin X)) < 0)) :
    IsRupert {X, Y, Z, X + w, Y + w, Z + w} := by
  set na := Real.sqrt (a 0 ^ 2 + a 1 ^ 2) with hna
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha1
  have hpos : 0 < a 0 ^ 2 + a 1 ^ 2 := by
    by_contra hc; push Not at hc
    apply ha0; ext i; fin_cases i
    · simp; nlinarith [sq_nonneg (a 0), sq_nonneg (a 1)]
    · simp; nlinarith [sq_nonneg (a 0), sq_nonneg (a 1)]
  have hna0 : 0 < na := Real.sqrt_pos.mpr hpos
  have hna2 : na ^ 2 = a 0 ^ 2 + a 1 ^ 2 := Real.sq_sqrt hpos.le
  set c := a 0 / na
  set s := -(a 1 / na)
  have hcs : c ^ 2 + s ^ 2 = 1 := by
    simp only [c, s, div_pow, neg_sq]; rw [← add_div, ← hna2]; exact div_self (by positivity)
  set R₁ := rotZ c s * R with hR₁def
  have hR₁ : R₁ ∈ SO3 := mul_mem (rotZ_mem_SO3 hcs) hR
  have hc0 : ∀ v, (R₁.toEuclideanLin v) 0 =
      ⟪a, proj_xy (R.toEuclideanLin v)⟫ / na := fun v => by
    rw [hR₁def, rotZ_mul_apply]
    simp [c, s, proj_xy, PiLp.inner_apply, Fin.sum_univ_two]; ring
  have hc1 : ∀ v, (R₁.toEuclideanLin v) 1 = cross2 a (proj_xy (R.toEuclideanLin v)) / na :=
    fun v => by
      rw [hR₁def, rotZ_mul_apply]
      simp [c, s, proj_xy, cross2]; ring
  have hc2 : ∀ v, (R₁.toEuclideanLin v) 2 = (R.toEuclideanLin v) 2 := fun v => by
    rw [hR₁def, rotZ_mul_apply]; simp
  have hw' : R₁.toEuclideanLin w = lam • ez := by
    rw [hR₁def, rotZ_mul_apply, hw]
    ext i; fin_cases i <;> simp [ez]
  refine isRupert_prism_view hR₁ hlam hw' ?_ ?_ ?_ ?_
  · rw [hc0, hc0]
    rw [inner_sub_right] at ha1
    exact div_lt_div_of_pos_right (by linarith) hna0
  · rw [hc0, hc0]
    rw [inner_sub_right] at ha2
    exact div_lt_div_of_pos_right (by linarith) hna0
  · have key : ∀ v, proj_xy (R₁.toEuclideanLin v) =
        !₂[c * (R.toEuclideanLin v) 0 - s * (R.toEuclideanLin v) 1,
          s * (R.toEuclideanLin v) 0 + c * (R.toEuclideanLin v) 1] := fun v => by
      rw [hR₁def, rotZ_mul_apply]; ext i; fin_cases i <;> simp [proj_xy]
    rw [key, key, key]
    clear_value c s
    generalize R.toEuclideanLin X = x at h3 ⊢
    generalize R.toEuclideanLin Y = y at h3 ⊢
    generalize R.toEuclideanLin Z = z at h3 ⊢
    have e : cross2 (!₂[c * y 0 - s * y 1, s * y 0 + c * y 1] - !₂[c * x 0 - s * x 1,
        s * x 0 + c * x 1]) (!₂[c * z 0 - s * z 1, s * z 0 + c * z 1] - !₂[c * x 0 - s * x 1,
        s * x 0 + c * x 1]) = (c ^ 2 + s ^ 2) * cross2 (proj_xy y - proj_xy x)
          (proj_xy z - proj_xy x) := by
      simp [cross2, proj_xy]; ring
    rw [e, hcs, one_mul]; exact h3
  · simp only [hc1, hc2]
    rcases h4 with (hZX | hZY) | ⟨heq, hcr⟩
    · have hG : Continuous fun ε : ℝ =>
          Real.sin ε * (cross2 a (proj_xy (R.toEuclideanLin Z)) / na) +
            Real.cos ε * (R.toEuclideanLin Z) 2 -
          (Real.sin ε * (cross2 a (proj_xy (R.toEuclideanLin X)) / na) +
            Real.cos ε * (R.toEuclideanLin X) 2) := by fun_prop
      have h0 : (fun ε : ℝ =>
          Real.sin ε * (cross2 a (proj_xy (R.toEuclideanLin Z)) / na) +
            Real.cos ε * (R.toEuclideanLin Z) 2 -
          (Real.sin ε * (cross2 a (proj_xy (R.toEuclideanLin X)) / na) +
            Real.cos ε * (R.toEuclideanLin X) 2)) 0 < 0 := by
        simp only [Real.sin_zero, Real.cos_zero, zero_mul, one_mul, zero_add]; linarith
      filter_upwards [(hG.continuousAt.eventually (gt_mem_nhds h0)).filter_mono
        nhdsWithin_le_nhds] with ε hε
      left; linarith
    · have hG : Continuous fun ε : ℝ =>
          Real.sin ε * (cross2 a (proj_xy (R.toEuclideanLin Z)) / na) +
            Real.cos ε * (R.toEuclideanLin Z) 2 -
          (Real.sin ε * (cross2 a (proj_xy (R.toEuclideanLin Y)) / na) +
            Real.cos ε * (R.toEuclideanLin Y) 2) := by fun_prop
      have h0 : (fun ε : ℝ =>
          Real.sin ε * (cross2 a (proj_xy (R.toEuclideanLin Z)) / na) +
            Real.cos ε * (R.toEuclideanLin Z) 2 -
          (Real.sin ε * (cross2 a (proj_xy (R.toEuclideanLin Y)) / na) +
            Real.cos ε * (R.toEuclideanLin Y) 2)) 0 < 0 := by
        simp only [Real.sin_zero, Real.cos_zero, zero_mul, one_mul, zero_add]; linarith
      filter_upwards [(hG.continuousAt.eventually (gt_mem_nhds h0)).filter_mono
        nhdsWithin_le_nhds] with ε hε
      right; linarith
    · filter_upwards [Ioo_mem_nhdsGT Real.pi_pos] with ε hε
      left
      have hs : 0 < Real.sin ε := Real.sin_pos_of_pos_of_lt_pi hε.1 hε.2
      rw [cross2_sub_right] at hcr
      have : Real.sin ε * ((cross2 a (proj_xy (R.toEuclideanLin Z)) -
          cross2 a (proj_xy (R.toEuclideanLin X))) / na) < 0 :=
        mul_neg_of_pos_of_neg hs (div_neg_of_neg_of_pos hcr hna0)
      rw [heq]
      have e : Real.sin ε * ((cross2 a (proj_xy (R.toEuclideanLin Z)) -
          cross2 a (proj_xy (R.toEuclideanLin X))) / na) =
          Real.sin ε * (cross2 a (proj_xy (R.toEuclideanLin Z)) / na) -
          Real.sin ε * (cross2 a (proj_xy (R.toEuclideanLin X)) / na) := by ring
      linarith

/-- **Theorem 7.7 (translation prisms).**  `K = T + [0, w]` for a triangle
`T = ABC` and `w` not parallel to its plane.  If `w` is not perpendicular to
the plane of `T`, or `T` has an obtuse angle, `K` is Rupert.  (Right prisms over
non-obtuse triangles remain open.) -/
theorem isRupert_translationPrism (A B C w : ℝ³) (hind : AffineIndependent ℝ ![A, B, C, A + w])
    (h : ⟪w, B - A⟫ ≠ 0 ∨ ⟪w, C - A⟫ ≠ 0 ∨ ⟪B - A, C - A⟫ < 0 ∨ ⟪A - B, C - B⟫ < 0 ∨
      ⟪A - C, B - C⟫ < 0) :
    IsRupert {A, B, C, A + w, B + w, C + w} := by
  sorry

end SmallRupert

end
