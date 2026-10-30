module

public import Minimality.Type08S.P2RDefs

@[expose] public section

set_option relaxedAutoImplicit true
set_option autoImplicit true
open scoped RealInnerProductSpace Topology
open Finset Filter
namespace Minimality
namespace Type08Sp

theorem det3_orth {x y z l : ℝ³} (hx : ⟪x, l⟫ = 0) (hy : ⟪y, l⟫ = 0) (hz : ⟪z, l⟫ = 0)
    (hl : l ≠ 0) : det3 x y z = 0 := by
  by_contra hne
  apply hl
  simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial] at hx hy hz
  have e0 : det3 x y z * l 0 = 0 := by
    simp only [det3_expand]; linear_combination (y 1 * z 2 - y 2 * z 1) * hx + (z 1 * x 2 - z 2 * x 1) * hy + (x 1 * y 2 - x 2 * y 1) * hz
  have e1 : det3 x y z * l 1 = 0 := by
    simp only [det3_expand]; linear_combination (y 2 * z 0 - y 0 * z 2) * hx + (z 2 * x 0 - z 0 * x 2) * hy + (x 2 * y 0 - x 0 * y 2) * hz
  have e2 : det3 x y z * l 2 = 0 := by
    simp only [det3_expand]; linear_combination (y 0 * z 1 - y 1 * z 0) * hx + (z 0 * x 1 - z 1 * x 0) * hy + (x 0 * y 1 - x 1 * y 0) * hz
  ext i; fin_cases i
  · exact (mul_eq_zero.mp e0).resolve_left hne
  · exact (mul_eq_zero.mp e1).resolve_left hne
  · exact (mul_eq_zero.mp e2).resolve_left hne

theorem touchT_eq_false {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hT : IsT a' b c d)
    (h : TouchT b b' c c' d) (heq : ⟪c, b - d⟫ = ⟪b, b - d⟫) : False := by
  obtain ⟨⟨h1, h2⟩, -, -⟩ := h
  have hl : b - d ≠ 0 := sub_ne_zero.mpr (Ne.symm N.hd.ne.2.2.1)
  apply norm08_nonplanar N
  refine det3_orth (l := b - d) ?_ ?_ ?_ hl
  · rw [inner_sub_left]; linarith
  · rw [inner_sub_left]; linarith
  · rw [inner_sub_left]; linarith

end Type08Sp
end Minimality
