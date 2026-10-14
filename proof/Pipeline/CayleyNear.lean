module

public import Cayley

@[expose] public section

/-!
# Rotations near the identity in Cayley coordinates

A rotation A with ‖A − 1‖ ≤ r (operator norm) has trace at least
3 − 3r²/2 (`trace_ge_of_opNorm_sub_one_le`), and a rotation of large trace
is the Cayley rotation of a short vector (`exists_cayleyMatrix_of_trace_ge`):
together, every rotation within r ≤ ρ ≤ 1 of the identity is the Cayley
rotation of a vector of Euclidean length at most ρ
(`exists_cayleyMatrix_of_opNorm_le`). The identity blow-up certificates
(`Pipeline.IdCap`) are stated in Cayley vectors; the identity-tube claim
bounds the relative rotation's distance from the identity.
-/

namespace Noperts

open scoped Matrix RealInnerProductSpace

open BalancedSupport

/-- A rotation whose trace is at least (3 − s)/(1 + s) is the Cayley rotation of a vector of
squared length at most s. -/
theorem exists_cayleyMatrix_of_trace_ge
    (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : A ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) (s : ℝ) (hs : 0 ≤ s)
    (htrace : (3 - s) / (1 + s) ≤ Matrix.trace A) :
    ∃ x y z : ℝ, x ^ 2 + y ^ 2 + z ^ 2 ≤ s ∧ A = cayleyMatrix x y z := by
  obtain ⟨a⟩ := BalancedSupport.exists_axisAngle A hA
  let co := Real.cos a.angle
  let si := Real.sin a.angle
  let c := si / (1 + co)
  have htr : Matrix.trace A = 1 + 2 * co := a.matrix_trace_eq
  have hs1 : 0 < 1 + s := by linarith
  have hco : (1 - s) / (1 + s) ≤ co := by
    have h1 : (3 - s) / (1 + s) = 1 + 2 * ((1 - s) / (1 + s)) := by
      field_simp; ring
    linarith
  have hco' : 1 - s ≤ co * (1 + s) := by
    have := (div_le_iff₀ hs1).mp hco
    linarith
  have hdenomPos : 0 < 1 + co := by
    have h2 : (1 - s) / (1 + s) > -1 := by
      rw [gt_iff_lt, lt_div_iff₀ hs1]; linarith
    linarith
  have hcircle : si ^ 2 + co ^ 2 = 1 := by
    dsimp only [si, co]
    exact Real.sin_sq_add_cos_sq a.angle
  have hhalfDenom : (1 + co) ^ 2 + si ^ 2 = 2 * (1 + co) := by
    nlinarith
  have hcSqMul : c ^ 2 * (1 + co) = 1 - co := by
    dsimp only [c]
    field_simp [ne_of_gt hdenomPos]
    nlinarith
  have hcSq : c ^ 2 ≤ s := by
    by_contra hlt
    push Not at hlt
    have : s * (1 + co) < c ^ 2 * (1 + co) := mul_lt_mul_of_pos_right hlt hdenomPos
    nlinarith
  have hcFirst : 2 * c / (1 + c ^ 2) = si := by
    dsimp only [c]
    field_simp [ne_of_gt hdenomPos]
    rw [hhalfDenom]
    ring
  have hcRemainder : 2 * c ^ 2 / (1 + c ^ 2) = 1 - co := by
    dsimp only [c]
    field_simp [ne_of_gt hdenomPos]
    nlinarith
  let x := c * a.axis 0
  let y := c * a.axis 1
  let z := c * a.axis 2
  have haxisSq : a.axis 0 ^ 2 + a.axis 1 ^ 2 + a.axis 2 ^ 2 = 1 := by
    have h := congrArg (fun r : ℝ => r ^ 2) a.axis_norm
    simpa [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three] using h
  have hxyz : x ^ 2 + y ^ 2 + z ^ 2 = c ^ 2 := by
    dsimp only [x, y, z]
    nlinarith
  refine ⟨x, y, z, hxyz.le.trans hcSq, ?_⟩
  apply Matrix.toEuclideanLin.injective
  apply LinearMap.ext
  intro v
  have hcay := cayleyMatrix_smul_unit_apply_sub c a.axis v a.axis_norm
  have hrot := a.apply_sub_exact v
  dsimp only [x, y, z]
  rw [hcFirst, hcRemainder, ← a.remainder_eq_cross3_cross3,
    ← a.first_eq_cross3] at hcay
  dsimp only [si, co] at hcay
  have hsub :
      (cayleyMatrix (c * a.axis 0) (c * a.axis 1)
        (c * a.axis 2)).toEuclideanLin v - v = A.toEuclideanLin v - v :=
    hcay.trans hrot.symm
  exact (sub_left_inj.mp hsub).symm

/-- Column j of a rotation is a unit vector: Σ_i A_ij² = 1. -/
theorem col_sq_sum_eq_one {A : Matrix (Fin 3) (Fin 3) ℝ}
    (hA : A ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) (j : Fin 3) :
    A 0 j ^ 2 + A 1 j ^ 2 + A 2 j ^ 2 = 1 := by
  have h := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hA.1
  have hjj := congrFun (congrFun h j) j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, Matrix.one_apply_eq] at hjj
  nlinarith [hjj]

/-- A rotation within r of the identity (operator norm) has trace at least 3 − 3r²/2. -/
theorem trace_ge_of_opNorm_sub_one_le (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : A ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) (r : ℝ)
    (h : ‖A.toEuclideanLin.toContinuousLinearMap - 1‖ ≤ r) :
    3 - 3 * r ^ 2 / 2 ≤ Matrix.trace A := by
  have key : ∀ j : Fin 3, 2 - 2 * A j j ≤ r ^ 2 := by
    intro j
    set e : ℝ³ := EuclideanSpace.single j 1 with he
    have hn : ‖(A.toEuclideanLin.toContinuousLinearMap - 1) e‖ ≤ r := by
      calc ‖(A.toEuclideanLin.toContinuousLinearMap - 1) e‖
          ≤ ‖A.toEuclideanLin.toContinuousLinearMap - 1‖ * ‖e‖ := ContinuousLinearMap.le_opNorm _ _
        _ = ‖A.toEuclideanLin.toContinuousLinearMap - 1‖ := by simp [e]
        _ ≤ r := h
    have hr0 : 0 ≤ r := (norm_nonneg _).trans h
    have hsq : ‖(A.toEuclideanLin.toContinuousLinearMap - 1) e‖ ^ 2 = 2 - 2 * A j j := by
      rw [EuclideanSpace.norm_sq_eq]
      have hcol := col_sq_sum_eq_one hA j
      fin_cases j <;>
        simp [e, Matrix.toLpLin_apply, Fin.sum_univ_three, PiLp.single_apply] at hcol ⊢ <;>
        nlinarith [hcol]
    have := pow_le_pow_left₀ (norm_nonneg _) hn 2
    linarith
  have h0 := key 0
  have h1 := key 1
  have h2 := key 2
  simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_three]
  linarith

/-- A rotation within r ≤ ρ ≤ 1 of the identity (operator norm) is the Cayley rotation of a
vector of Euclidean length at most ρ. -/
theorem exists_cayleyMatrix_of_opNorm_le (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : A ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) (r ρ : ℝ) (hr : r ≤ ρ) (hρ1 : ρ ≤ 1)
    (h : ‖A.toEuclideanLin.toContinuousLinearMap - 1‖ ≤ r) :
    ∃ x y z : ℝ, x ^ 2 + y ^ 2 + z ^ 2 ≤ ρ ^ 2 ∧ A = cayleyMatrix x y z := by
  have hr0 : 0 ≤ r := (norm_nonneg _).trans h
  have htr := trace_ge_of_opNorm_sub_one_le A hA r h
  apply exists_cayleyMatrix_of_trace_ge A hA (ρ ^ 2) (sq_nonneg ρ)
  have hrr : r ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ hr0 hr 2
  have hρ2 : ρ ^ 2 ≤ 1 := by nlinarith
  have hpos : 0 < 1 + ρ ^ 2 := by positivity
  rw [div_le_iff₀ hpos]
  nlinarith [sq_nonneg ρ]

end Noperts

end
