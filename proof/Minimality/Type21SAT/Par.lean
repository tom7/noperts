module

public import Minimality.Type21SAT.Lex2

@[expose] public section

/-!
# Type 21 three valued bridge (L3), part 1b: two facets edge-on at `u` and zero at `d` are parallel

Used by the double zero witnesses (`witness2` of B3Geom): normals `a, b` both orthogonal to `u` and `d`,
with `u, d` independent (a third normal `s` orthogonal to `u` but not to `d` shows it), are proportional.
-/

set_option autoImplicit false
open scoped RealInnerProductSpace

namespace Minimality.H21

/-- Polynomial form: `a` orthogonal to `u` and `d` is `<n, a> / |n|^2` times `n = u x d` (three coordinates). -/
theorem perp_coords (u0 u1 u2 d0 d1 d2 a0 a1 a2 : ℝ) (hu : a0 * u0 + a1 * u1 + a2 * u2 = 0)
    (hd : a0 * d0 + a1 * d1 + a2 * d2 = 0) :
    let n0 := u1 * d2 - u2 * d1
    let n1 := u2 * d0 - u0 * d2
    let n2 := u0 * d1 - u1 * d0
    (n0 ^ 2 + n1 ^ 2 + n2 ^ 2) * a0 = (n0 * a0 + n1 * a1 + n2 * a2) * n0 ∧
    (n0 ^ 2 + n1 ^ 2 + n2 ^ 2) * a1 = (n0 * a0 + n1 * a1 + n2 * a2) * n1 ∧
    (n0 ^ 2 + n1 ^ 2 + n2 ^ 2) * a2 = (n0 * a0 + n1 * a1 + n2 * a2) * n2 := by
  intro n0 n1 n2
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (n1 * u2 - n2 * u1) * hd - (n1 * d2 - n2 * d1) * hu
  · linear_combination (n2 * u0 - n0 * u2) * hd - (n2 * d0 - n0 * d2) * hu
  · linear_combination (n0 * u1 - n1 * u0) * hd - (n0 * d1 - n1 * d0) * hu

/-- `u != 0`, `s` orthogonal to `u`, `<s, d> != 0`: the cross product `u x d` is not zero. -/
theorem cross_ne (u0 u1 u2 d0 d1 d2 s0 s1 s2 : ℝ) (hu : u0 ^ 2 + u1 ^ 2 + u2 ^ 2 ≠ 0)
    (hs : s0 * u0 + s1 * u1 + s2 * u2 = 0) (hsd : s0 * d0 + s1 * d1 + s2 * d2 ≠ 0) :
    (u1 * d2 - u2 * d1) ^ 2 + (u2 * d0 - u0 * d2) ^ 2 + (u0 * d1 - u1 * d0) ^ 2 ≠ 0 := by
  intro h
  have sq3 : ∀ p q r : ℝ, p ^ 2 + q ^ 2 + r ^ 2 = 0 → p = 0 ∧ q = 0 ∧ r = 0 := by
    intro p q r h
    refine ⟨?_, ?_, ?_⟩ <;> nlinarith [sq_nonneg p, sq_nonneg q, sq_nonneg r]
  obtain ⟨h0, h1, h2⟩ := sq3 _ _ _ h
  apply hsd
  have : (u0 ^ 2 + u1 ^ 2 + u2 ^ 2) * (s0 * d0 + s1 * d1 + s2 * d2) = 0 := by
    linear_combination (u0 * d0 + u1 * d1 + u2 * d2) * hs + (u1 * s2 - u2 * s1) * h0
      + (u2 * s0 - u0 * s2) * h1 + (u0 * s1 - u1 * s0) * h2
  exact (mul_eq_zero.mp this).resolve_left hu

/-- **Parallel normals.**  `a, b` orthogonal to `u` and `d`, `a != 0`, a third vector `s` orthogonal to `u`
but not to `d`, `u != 0`: `b` is a multiple of `a`. -/
theorem parallel_of_perp (u d a b s : ℝ³) (hu : u ≠ 0) (ha : a ≠ 0)
    (hau : ⟪a, u⟫ = 0) (had : ⟪a, d⟫ = 0) (hbu : ⟪b, u⟫ = 0) (hbd : ⟪b, d⟫ = 0)
    (hsu : ⟪s, u⟫ = 0) (hsd : ⟪s, d⟫ ≠ 0) : ∃ r : ℝ, b = r • a := by
  simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial] at hau had hbu hbd hsu hsd
  have hu2 : u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 ≠ 0 := by
    intro h
    apply hu
    have sq3 : ∀ p q r : ℝ, p ^ 2 + q ^ 2 + r ^ 2 = 0 → p = 0 ∧ q = 0 ∧ r = 0 := by
      intro p q r h
      refine ⟨?_, ?_, ?_⟩ <;> nlinarith [sq_nonneg p, sq_nonneg q, sq_nonneg r]
    obtain ⟨h0, h1, h2⟩ := sq3 _ _ _ h
    ext i; fin_cases i <;> simp [h0, h1, h2]
  have hn := cross_ne (u 0) (u 1) (u 2) (d 0) (d 1) (d 2) (s 0) (s 1) (s 2) hu2
    (by linarith [hsu]) (by intro h; apply hsd; linarith [h])
  obtain ⟨a0, a1, a2⟩ := perp_coords (u 0) (u 1) (u 2) (d 0) (d 1) (d 2) (a 0) (a 1) (a 2)
    (by linarith [hau]) (by linarith [had])
  obtain ⟨b0, b1, b2⟩ := perp_coords (u 0) (u 1) (u 2) (d 0) (d 1) (d 2) (b 0) (b 1) (b 2)
    (by linarith [hbu]) (by linarith [hbd])
  set n0 := u 1 * d 2 - u 2 * d 1
  set n1 := u 2 * d 0 - u 0 * d 2
  set n2 := u 0 * d 1 - u 1 * d 0
  set N2 := n0 ^ 2 + n1 ^ 2 + n2 ^ 2 with hN2
  set pa := n0 * a 0 + n1 * a 1 + n2 * a 2 with hpa
  set pb := n0 * b 0 + n1 * b 1 + n2 * b 2 with hpb
  have hpa0 : pa ≠ 0 := by
    intro h0
    apply ha
    have e0 : N2 * a 0 = 0 := by rw [a0, h0]; ring
    have e1 : N2 * a 1 = 0 := by rw [a1, h0]; ring
    have e2 : N2 * a 2 = 0 := by rw [a2, h0]; ring
    ext i; fin_cases i <;> simp [(mul_eq_zero.mp e0).resolve_left hn, (mul_eq_zero.mp e1).resolve_left hn,
      (mul_eq_zero.mp e2).resolve_left hn]
  have k0 : pa * b 0 = pb * a 0 := mul_left_cancel₀ hn (by linear_combination pa * b0 - pb * a0)
  have k1 : pa * b 1 = pb * a 1 := mul_left_cancel₀ hn (by linear_combination pa * b1 - pb * a1)
  have k2 : pa * b 2 = pb * a 2 := mul_left_cancel₀ hn (by linear_combination pa * b2 - pb * a2)
  refine ⟨pb / pa, ?_⟩
  ext i; fin_cases i
  · show b 0 = pb / pa * a 0
    rw [div_mul_eq_mul_div, eq_div_iff hpa0]; linear_combination k0
  · show b 1 = pb / pa * a 1
    rw [div_mul_eq_mul_div, eq_div_iff hpa0]; linear_combination k1
  · show b 2 = pb / pa * a 2
    rw [div_mul_eq_mul_div, eq_div_iff hpa0]; linear_combination k2

end Minimality.H21
