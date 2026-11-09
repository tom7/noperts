module

public import Minimality.Generic.PV.PVDefs
public import Minimality.Generic.PV.PVChain

@[expose] public section


/-! Face chains in space: the lower/upper chain of a face seen edge-on along `d`, with all the
outputs needed by the rim (sign-parametrized by `s = ±1`). -/

namespace Minimality
open scoped RealInnerProductSpace Topology
open Finset Filter

/-- Chart of the plane `⟪n,·⟫ = h` along `d`, with the depth multiplied by `s = ±1`. -/
noncomputable def chartS (s : ℝ) (n d : ℝ³) (p : ℝ³) : ℝ² := !₂[⟪cross n d, p⟫, s * ⟪d, p⟫]

theorem chartS_sub (s : ℝ) (n d p q : ℝ³) : chartS s n d p - chartS s n d q = chartS s n d (p - q) := by
  ext i; fin_cases i <;> simp [chartS, inner_sub_right] <;> ring

theorem chartS_zero (s : ℝ) (n d p : ℝ³) : chartS s n d p 0 = ⟪cross n d, p⟫ := by simp [chartS]
theorem chartS_one (s : ℝ) (n d p : ℝ³) : chartS s n d p 1 = s * ⟪d, p⟫ := by simp [chartS]

theorem planeChart_eq (n d : ℝ³) : planeChart n d = chartS 1 n d := by
  funext p; simp [planeChart, chartS]

/-- The planar cross product of two chart vectors is the (negated) determinant against `n`. -/
theorem cross2_chartS (s : ℝ) (n d e q : ℝ³) (hnd : ⟪n, d⟫ = 0) :
    cross2 (chartS s n d e) (chartS s n d q) = - s * ⟪d, d⟫ * det3 e q n := by
  simp only [cross2, chartS_zero, chartS_one, det3, cross, PiLp.inner_apply, Fin.sum_univ_three]
  simp only [PiLp.inner_apply, Fin.sum_univ_three] at hnd
  simp at hnd ⊢
  linear_combination (1) * s * ((e 1 * q 2 - e 2 * q 1) * d 0 + (e 2 * q 0 - e 0 * q 2) * d 1 + (e 0 * q 1 - e 1 * q 0) * d 2) * hnd


/-- Reciprocal-basis identity (no hypotheses). -/
theorem triple_basis (n d u : ℝ³) :
    (⟪n, n⟫ * ⟪d, d⟫ - ⟪n, d⟫ ^ 2) • u =
      ⟪n, u⟫ • (⟪d, d⟫ • n - ⟪n, d⟫ • d) + ⟪d, u⟫ • (⟪n, n⟫ • d - ⟪n, d⟫ • n)
        + ⟪cross n d, u⟫ • cross n d := by
  ext i
  fin_cases i <;> simp only [cross, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial,
    PiLp.smul_apply, PiLp.add_apply, PiLp.sub_apply, smul_eq_mul, Fin.zero_eta, Fin.isValue,
    Fin.mk_one, Fin.reduceFinMk] <;> simp <;> ring

/-- A vector orthogonal to `n`, `d`, `n × d` (with `n ⊥ d`, both nonzero) vanishes. -/
theorem eq_zero_of_orth {n d u : ℝ³} (hn : n ≠ 0) (hd : d ≠ 0) (hnd : ⟪n, d⟫ = 0)
    (h1 : ⟪n, u⟫ = 0) (h2 : ⟪d, u⟫ = 0) (h3 : ⟪cross n d, u⟫ = 0) : u = 0 := by
  have := triple_basis n d u
  rw [h1, h2, h3, hnd] at this
  simp only [zero_smul, add_zero] at this
  have hp : 0 < ⟪n, n⟫ * ⟪d, d⟫ - 0 ^ 2 := by
    have := real_inner_self_pos.mpr hn
    have := real_inner_self_pos.mpr hd
    nlinarith
  rcases smul_eq_zero.mp this with h | h
  · exact absurd h hp.ne'
  · exact h

theorem chartS_injOn {s : ℝ} (hs : s = 1 ∨ s = -1) {n d : ℝ³} (hn : n ≠ 0) (hd : d ≠ 0)
    (hnd : ⟪n, d⟫ = 0) {h : ℝ} {p q : ℝ³} (hp : ⟪n, p⟫ = h) (hq : ⟪n, q⟫ = h)
    (he : chartS s n d p = chartS s n d q) : p = q := by
  have h0 := congrArg (fun z : ℝ² => z 0) he
  have h1 := congrArg (fun z : ℝ² => z 1) he
  simp only [chartS_zero, chartS_one] at h0 h1
  have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
  have h1' : ⟪d, p⟫ = ⟪d, q⟫ := mul_left_cancel₀ hs0 h1
  have : p - q = 0 := eq_zero_of_orth hn hd hnd (by rw [inner_sub_right, hp, hq]; ring)
    (by rw [inner_sub_right, h1']; ring) (by rw [inner_sub_right, h0]; ring)
  exact sub_eq_zero.mp this

end Minimality
