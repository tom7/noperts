module

public import Minimality.PlateRule
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Convex.Intrinsic

@[expose] public section

namespace Minimality

open scoped RealInnerProductSpace
open Finset

/-! ## L0 -/

theorem not_collinear_of_interior_nonempty (V : Finset ℝ³)
    (hsol : (interior (convexHull ℝ (V : Set ℝ³))).Nonempty) :
    ¬ Collinear ℝ (V : Set ℝ³) := by
  intro hc
  have h1 := (interior_convexHull_nonempty_iff_affineSpan_eq_top (s := (V : Set ℝ³))).1 hsol
  have h2 : vectorSpan ℝ (V : Set ℝ³) = ⊤ := by
    rw [← direction_affineSpan, h1, AffineSubspace.direction_top]
  have h3 := hc.finrank_le_one
  rw [h2, finrank_top, finrank_euclideanSpace_fin] at h3
  omega

/-! ## L1 -/

def HullComb (V : Finset ℝ³) (P : ℝ³) : Prop :=
  ∃ ν : ℝ³ → ℝ, (∀ v ∈ V, 0 ≤ ν v) ∧ ∑ v ∈ V, ν v = 1 ∧ P = ∑ v ∈ V, ν v • v

theorem hullComb_of_mem {V : Finset ℝ³} {p : ℝ³} (hp : p ∈ V) : HullComb V p := by
  classical
  refine ⟨fun v => if v = p then 1 else 0, ?_, ?_, ?_⟩
  · intro v _; dsimp only; split_ifs <;> norm_num
  · simp [hp]
  · simp [ite_smul, hp]

theorem hullComb_segment {V : Finset ℝ³} {p q : ℝ³} (hp : p ∈ V) (hq : q ∈ V) {θ : ℝ}
    (h0 : 0 ≤ θ) (h1 : θ ≤ 1) : HullComb V ((1 - θ) • p + θ • q) := by
  classical
  refine ⟨fun v => (1 - θ) * (if v = p then 1 else 0) + θ * (if v = q then 1 else 0), ?_, ?_, ?_⟩
  · intro v _
    have : 0 ≤ 1 - θ := by linarith
    dsimp only
    split_ifs <;> nlinarith
  · simp [Finset.sum_add_distrib, hp, hq]
  · simp only [add_smul, Finset.sum_add_distrib, mul_smul, ← Finset.smul_sum, ite_smul, one_smul,
      zero_smul, Finset.sum_ite_eq', hp, hq, ite_true]

theorem posComb_of_bary_hull (V : Finset ℝ³) (R₂ : Matrix (Fin 3) (Fin 3) ℝ)
    (P₁ P₂ P₃ : ℝ³) (h₁ : HullComb V P₁) (h₂ : HullComb V P₂) (h₃ : HullComb V P₃)
    (l₁ l₂ l₃ : ℝ² → ℝ) (hsum : ∀ z, l₁ z + l₂ z + l₃ z = 1)
    (hrec : ∀ z, l₁ z • proj_xy (R₂.toEuclideanLin P₁) + l₂ z • proj_xy (R₂.toEuclideanLin P₂)
      + l₃ z • proj_xy (R₂.toEuclideanLin P₃) = z)
    (x : ℝ²) (hx₁ : 0 < l₁ x) (hx₂ : 0 < l₂ x) (hx₃ : 0 < l₃ x) :
    PosComb V R₂ x := by
  classical
  obtain ⟨ν₁, hν₁, hs₁, e₁⟩ := h₁
  obtain ⟨ν₂, hν₂, hs₂, e₂⟩ := h₂
  obtain ⟨ν₃, hν₃, hs₃, e₃⟩ := h₃
  set φ : ℝ³ → ℝ² := fun w => proj_xy (R₂.toEuclideanLin w) with hφ
  have hφsum : ∀ ν : ℝ³ → ℝ, φ (∑ v ∈ V, ν v • v) = ∑ v ∈ V, ν v • φ v := by
    intro ν
    simp only [hφ, map_sum, map_smul, ← projL_apply, map_sum projL]
  have hne : V.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    simp [h] at hs₁
  set n : ℝ := (V.card : ℝ) with hn
  have hnpos : 0 < n := by rw [hn]; exact_mod_cast hne.card_pos
  set c : ℝ² := ∑ w ∈ V, (1 / n) • φ w with hc
  set m : ℝ := min (l₁ x) (min (l₂ x) (l₃ x)) with hm
  have hmpos : 0 < m := lt_min hx₁ (lt_min hx₂ hx₃)
  set K : ℝ := |l₁ c| + |l₂ c| + |l₃ c| with hK
  have hK0 : 0 ≤ K := by positivity
  set ε : ℝ := m / (1 + K) with hε
  have hεpos : 0 < ε := by positivity
  have hεK : ε * K < m := by
    rw [hε, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]; nlinarith
  have hbd : ∀ t : ℝ, |t| ≤ K → ε * t < m := by
    intro t ht
    have := neg_abs_le t
    have := le_abs_self t
    nlinarith
  have ha₁ : 0 < l₁ x - ε * l₁ c := by
    have := hbd (l₁ c) (by simp only [hK]; linarith [abs_nonneg (l₂ c), abs_nonneg (l₃ c)])
    have := min_le_left (l₁ x) (min (l₂ x) (l₃ x))
    linarith
  have ha₂ : 0 < l₂ x - ε * l₂ c := by
    have := hbd (l₂ c) (by simp only [hK]; linarith [abs_nonneg (l₁ c), abs_nonneg (l₃ c)])
    have := (min_le_right (l₁ x) (min (l₂ x) (l₃ x))).trans (min_le_left _ (l₃ x))
    linarith
  have ha₃ : 0 < l₃ x - ε * l₃ c := by
    have := hbd (l₃ c) (by simp only [hK]; linarith [abs_nonneg (l₂ c), abs_nonneg (l₁ c)])
    have := (min_le_right (l₁ x) (min (l₂ x) (l₃ x))).trans (min_le_right _ (l₃ x))
    linarith
  set a₁ := l₁ x - ε * l₁ c
  set a₂ := l₂ x - ε * l₂ c
  set a₃ := l₃ x - ε * l₃ c
  refine ⟨fun w => ε / n + a₁ * ν₁ w + a₂ * ν₂ w + a₃ * ν₃ w, ?_, ?_, ?_⟩
  · intro w hw
    have : 0 < ε / n := by positivity
    have := mul_nonneg ha₁.le (hν₁ w hw)
    have := mul_nonneg ha₂.le (hν₂ w hw)
    have := mul_nonneg ha₃.le (hν₃ w hw)
    linarith
  · simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, hs₁, hs₂,
      hs₃]
    rw [← hn]
    have : n ≠ 0 := hnpos.ne'
    have h1 := hsum x
    have h2 := hsum c
    field_simp
    simp only [a₁, a₂, a₃]
    nlinarith [h1, h2]
  · have hcsum : ε • c = ∑ w ∈ V, (ε / n) • φ w := by
      rw [hc, Finset.smul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [smul_smul]; congr 1; field_simp
    have k1 : φ P₁ = ∑ v ∈ V, ν₁ v • φ v := by rw [e₁]; exact hφsum ν₁
    have k2 : φ P₂ = ∑ v ∈ V, ν₂ v • φ v := by rw [e₂]; exact hφsum ν₂
    have k3 : φ P₃ = ∑ v ∈ V, ν₃ v • φ v := by rw [e₃]; exact hφsum ν₃
    have goal : ∑ w ∈ V, (ε / n + a₁ * ν₁ w + a₂ * ν₂ w + a₃ * ν₃ w) • φ w
        = ε • c + a₁ • φ P₁ + a₂ • φ P₂ + a₃ • φ P₃ := by
      rw [hcsum, k1, k2, k3]
      simp only [Finset.smul_sum, add_smul, Finset.sum_add_distrib, mul_smul]
    show x = ∑ w ∈ V, (ε / n + a₁ * ν₁ w + a₂ * ν₂ w + a₃ * ν₃ w) • φ w
    rw [goal]
    have e1 := hrec x
    have e2 := hrec c
    have : ε • c = ε • (l₁ c • φ P₁ + l₂ c • φ P₂ + l₃ c • φ P₃) := by rw [e2]
    rw [smul_add, smul_add] at this
    rw [this]
    simp only [a₁, a₂, a₃, sub_smul, mul_smul]
    conv_lhs => rw [← e1]
    abel

/-! ## L2 -/

theorem triangle_corner_pos (μ w D h x₃ s t : ℝ) (hμ : 0 < μ) (hw : 0 < w)
    (hh : 0 < h) (hs : 0 ≤ s ∧ s ≤ 1) (ht : 0 ≤ t ∧ t ≤ 1)
    (hsmall : μ * h + w * (|x₃| + |D - x₃|) < D * h) :
    let A := |x₃|; let B := |D - x₃|; let γ := D * h - μ * h - w * (A + B)
    let σ := γ / (2 * (A + B + 1)); let X := ((σ + w) * A + γ / 4) / h
    let ξ := X + s * μ; let η := σ + t * w
    0 < η ∧ 0 < ξ * h - η * x₃ ∧ 0 < D * h - ξ * h - η * (D - x₃) := by
  intro A B γ σ X ξ η
  have hA : 0 ≤ A := abs_nonneg _
  have hB : 0 ≤ B := abs_nonneg _
  have hγ : 0 < γ := by simp only [γ, A, B]; linarith
  have hσ : 0 < σ := by positivity
  have hσAB : σ * (A + B) ≤ γ / 2 := by
    simp only [σ]; rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
  have hx1 : x₃ ≤ A := le_abs_self _
  have hx2 : D - x₃ ≤ B := le_abs_self _
  have hXh : X * h = (σ + w) * A + γ / 4 := by simp only [X]; field_simp
  have hη0 : 0 < η := by simp only [η]; nlinarith [ht.1]
  have hηw : η ≤ σ + w := by simp only [η]; nlinarith [ht.2]
  refine ⟨hη0, ?_, ?_⟩
  · have : ξ * h = X * h + s * μ * h := by simp only [ξ]; ring
    nlinarith [mul_nonneg (mul_nonneg hs.1 hμ.le) hh.le, mul_le_mul_of_nonneg_right hηw hA,
      mul_le_mul_of_nonneg_left hx1 hη0.le]
  · have : ξ * h = X * h + s * μ * h := by simp only [ξ]; ring
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hs.2) hμ.le) hh.le,
      mul_le_mul_of_nonneg_right hηw hB, mul_le_mul_of_nonneg_left hx2 hη0.le]

theorem boxApplies_of_triangle (V : Finset ℝ³)
    (e n u u' : ℝ³) (hee : ⟪e, e⟫ = 1) (hnn : ⟪n, n⟫ = 1) (hen : ⟪e, n⟫ = 0)
    (huu : ⟪u, u⟫ = 1) (hu'u' : ⟪u', u'⟫ = 1) (huu' : ⟪u, u'⟫ = 0)
    (a b μ w D h x₀ y₀ x₃ : ℝ) (hμ : 0 < μ) (hw : 0 < w) (hh : 0 < h)
    (hbox : ∀ v ∈ V, a ≤ ⟪e, v⟫ ∧ ⟪e, v⟫ ≤ a + μ ∧ b ≤ ⟪n, v⟫ ∧ ⟪n, v⟫ ≤ b + w)
    (P₁ P₂ P₃ : ℝ³) (h₁ : HullComb V P₁) (h₂ : HullComb V P₂) (h₃ : HullComb V P₃)
    (hp₁ : ⟪u, P₁⟫ = x₀ ∧ ⟪u', P₁⟫ = y₀)
    (hp₂ : ⟪u, P₂⟫ = x₀ + D ∧ ⟪u', P₂⟫ = y₀)
    (hp₃ : ⟪u, P₃⟫ = x₃ ∧ ⟪u', P₃⟫ = y₀ + h)
    (hsmall : μ * h + w * (|x₃ - x₀| + |x₀ + D - x₃|) < D * h) :
    BoxApplies V := by
  have hR₂ := frameMat_mem_SO3 u u' huu hu'u' huu'
  have hDpos : 0 < D := by
    have : 0 ≤ w * (|x₃ - x₀| + |x₀ + D - x₃|) := by positivity
    by_contra hD
    push Not at hD
    nlinarith [mul_pos hμ hh, mul_nonneg (neg_nonneg.2 hD) hh.le]
  have hsm : μ * h + w * (|x₃ - x₀| + |D - (x₃ - x₀)|) < D * h := by
    have : D - (x₃ - x₀) = x₀ + D - x₃ := by ring
    rw [this]; exact hsmall
  set A := |x₃ - x₀| with hA
  set B := |D - (x₃ - x₀)| with hB
  set γ := D * h - μ * h - w * (A + B) with hγ
  set σ := γ / (2 * (A + B + 1)) with hσ
  set X := ((σ + w) * A + γ / 4) / h with hX
  let l₃ : ℝ² → ℝ := fun z => (z 1 - y₀) / h
  let l₂ : ℝ² → ℝ := fun z => (z 0 - x₀ - l₃ z * (x₃ - x₀)) / D
  let l₁ : ℝ² → ℝ := fun z => 1 - l₂ z - l₃ z
  refine ⟨e, n, hee, hnn, hen, frameMat u u', hR₂, a, b, μ, w, x₀ + X, y₀ + σ, μ, w, hμ, hw,
    le_rfl, le_rfl, hbox, ?_⟩
  intro s t hs ht
  have hs' : 0 ≤ s ∧ s ≤ 1 := by rcases hs with rfl | rfl <;> norm_num
  have ht' : 0 ≤ t ∧ t ≤ 1 := by rcases ht with rfl | rfl <;> norm_num
  obtain ⟨c1, c2, c3⟩ := triangle_corner_pos μ w D h (x₃ - x₀) s t hμ hw hh hs' ht' hsm
  have hz1 : (!₂[x₀ + X + s * μ, y₀ + σ + t * w] : ℝ²) 1 = y₀ + (σ + t * w) := by
    simp; ring
  have hz0 : (!₂[x₀ + X + s * μ, y₀ + σ + t * w] : ℝ²) 0 = x₀ + (X + s * μ) := by simp; ring
  refine posComb_of_bary_hull V (frameMat u u') P₁ P₂ P₃ h₁ h₂ h₃ l₁ l₂ l₃ ?_ ?_ _ ?_ ?_ ?_
  · intro z; simp only [l₁]; ring
  · intro z
    rw [proj_frameMat, proj_frameMat, proj_frameMat, hp₁.1, hp₁.2, hp₂.1, hp₂.2, hp₃.1, hp₃.2]
    ext i
    fin_cases i
    · simp only [l₁, l₂, l₃]
      simp
      field_simp
      ring
    · simp only [l₁, l₂, l₃]
      simp
      field_simp
      ring
  · simp only [l₁, l₂, l₃]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    have : 0 < (D * h - (X + s * μ) * h - (σ + t * w) * (D - (x₃ - x₀))) / (D * h) :=
      div_pos c3 (by positivity)
    convert this using 1
    field_simp
    ring
  · simp only [l₂, l₃]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    have : 0 < ((X + s * μ) * h - (σ + t * w) * (x₃ - x₀)) / (D * h) :=
      div_pos c2 (by positivity)
    convert this using 1
    field_simp
    ring
  · simp only [l₃]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    have := div_pos c1 hh
    convert this using 2; ring

/-! ## L7 -/

theorem exists_diam_pair (V : Finset ℝ³) (hV : V.Nonempty) :
    ∃ p ∈ V, ∃ q ∈ V, ∀ x ∈ V, ∀ y ∈ V, ‖x - y‖ ≤ ‖q - p‖ := by
  obtain ⟨z, hz, hmax⟩ := Finset.exists_max_image (V ×ˢ V) (fun z : ℝ³ × ℝ³ => ‖z.2 - z.1‖)
    (hV.product hV)
  rw [Finset.mem_product] at hz
  refine ⟨z.1, hz.1, z.2, hz.2, fun x hx y hy => ?_⟩
  exact hmax (y, x) (Finset.mem_product.2 ⟨hy, hx⟩)

theorem inner_mem_of_diam {V : Finset ℝ³} {p q : ℝ³} (hp : p ∈ V) (hq : q ∈ V)
    (hdiam : ∀ x ∈ V, ∀ y ∈ V, ‖x - y‖ ≤ ‖q - p‖) :
    ∀ v ∈ V, 0 ≤ ⟪q - p, v - p⟫ ∧ ⟪q - p, v - p⟫ ≤ ‖q - p‖ ^ 2 := by
  intro v hv
  have h1 := hdiam v hv q hq
  have h2 := hdiam v hv p hp
  have e : v - q = (v - p) - (q - p) := by abel
  rw [e] at h1
  have n1 : ‖(v - p) - (q - p)‖ ^ 2 ≤ ‖q - p‖ ^ 2 := by gcongr
  have n2 : ‖v - p‖ ^ 2 ≤ ‖q - p‖ ^ 2 := by gcongr
  rw [norm_sub_sq_real] at n1
  have cs := real_inner_le_norm (q - p) (v - p)
  have c0 : 0 ≤ ‖q - p‖ := norm_nonneg _
  have c1 : 0 ≤ ‖v - p‖ := norm_nonneg _
  rw [real_inner_comm] at n1
  refine ⟨by nlinarith [sq_nonneg ‖v - p‖], ?_⟩
  have : ‖v - p‖ ≤ ‖q - p‖ := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left this c0]

end Minimality

end
