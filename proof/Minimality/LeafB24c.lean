module

public import Minimality.LeafB24b

@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace

namespace Minimality
open HDNApex

namespace LeafB24

/-- Abstract pentagon core: the ten triple brackets of five points in convex position, their
linear (affine) and one quadratic Plücker relation, and the key row. -/
theorem pent_core (d012 d013 d014 d023 d024 d034 d123 d124 d134 d234 : ℝ)
    (h012 : 0 < d012) (h013 : 0 < d013) (h014 : 0 < d014) (h023 : 0 < d023) (h024 : 0 < d024)
    (h034 : 0 < d034) (h123 : 0 < d123) (h124 : 0 < d124) (h134 : 0 < d134)
    (p0123 : d012 - d013 + d023 - d123 = 0) (p0124 : d012 - d014 + d024 - d124 = 0)
    (p0134 : d013 - d014 + d034 - d134 = 0) (p0234 : d023 - d024 + d034 - d234 = 0)
    (g1 : d012 * d034 - d013 * d024 + d014 * d023 = 0)
    (key : d124 < d123) :
    d012 < d123 ∧ d034 < d234 ∧ d134 < d234 ∧ (d014 < d012 ∨ d014 < d013) ∧
      (d014 < d024 ∨ d014 < d034) := by
  have H1 : d012 < d123 := by
    nlinarith [mul_pos h012 h034, mul_pos h013 h024, mul_pos h014 h023, mul_pos h012 h134,
      mul_pos h124 h034, mul_pos h123 h024]
  refine ⟨H1, ?_, by linarith, ?_, ?_⟩
  · nlinarith [mul_pos h012 h034, mul_pos h013 h024, mul_pos h014 h023, mul_pos h012 h134,
      mul_pos h124 h034, mul_pos h123 h024]
  · by_contra h; push Not at h
    nlinarith [mul_pos h012 h034, mul_pos h013 h024, mul_pos h014 h023, mul_pos h012 h134,
      mul_pos h124 h034, mul_pos h123 h024]
  · by_contra h; push Not at h
    nlinarith [mul_pos h012 h034, mul_pos h013 h024, mul_pos h014 h023, mul_pos h012 h134,
      mul_pos h124 h034, mul_pos h123 h024]

/-- A tilt with prescribed inner products `1` against two vectors exists when `det3 a b u ≠ 0`
(so `a`, `b` independent): `e = (b × n + n × a) / |n|²`, `n = a × b`.  (LeafB24b.md, open tilt item:
for the wedge `z6 < z2 < z0` take `a = x2 - x6`, `b = x0 - x2`; non-collinearity of the screen
triangle `x0, x6, x2` is `hcyc`.) -/
theorem exists_tilt {a b u : ℝ³} (h : det3 a b u ≠ 0) : ∃ e : ℝ³, ⟪a, e⟫ = 1 ∧ ⟪b, e⟫ = 1 := by
  have hN : ⟪cross a b, cross a b⟫ ≠ 0 := by
    intro h0
    apply h
    have : cross a b = 0 := inner_self_eq_zero.1 h0
    simp [det3, this]
  have ha : ⟪a, cross b (cross a b) + cross (cross a b) a⟫ = ⟪cross a b, cross a b⟫ := by
    simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial,
      cross_apply_zero, cross_apply_one, cross_apply_two, PiLp.add_apply]
    ring
  have hb : ⟪b, cross b (cross a b) + cross (cross a b) a⟫ = ⟪cross a b, cross a b⟫ := by
    simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial,
      cross_apply_zero, cross_apply_one, cross_apply_two, PiLp.add_apply]
    ring
  refine ⟨(⟪cross a b, cross a b⟫)⁻¹ • (cross b (cross a b) + cross (cross a b) a), ?_, ?_⟩
  · rw [real_inner_smul_right, ha]; field_simp
  · rw [real_inner_smul_right, hb]; field_simp

end LeafB24
end Minimality
