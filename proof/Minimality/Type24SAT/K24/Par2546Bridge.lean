module

public import Minimality.Type24SAT.K24.Par2546
public import Minimality.Type24SAT.K24.Wire24
public import Minimality.Type21Ridge
public import Minimality.BadViews

@[expose] public section

open scoped RealInnerProductSpace
open Finset

namespace Minimality.T24.Par
open Minimality Minimality.H21 Minimality.T24.SAT

theorem b2456_eq_det3 (x : Fin 7 → ℝ³) :
    Minimality.T24.b2456 x = - det3 (x 6 - x 4) (x 5 - x 2) (x 4 - x 2) := by
  simp only [Minimality.T24.b2456, det3_expand, PiLp.sub_apply]
  ring

/-- **Parallelism `25 ∥ 46` from coplanarity `b2456 = 0` and facet 4 orthogonality `hE`.**
When `2, 4, 5, 6` are coplanar (`b2456 = 0`) and facet 4 normal `N_4` is orthogonal to `x 5 - x 2`,
the edges `x 6 - x 4` and `x 5 - x 2` are parallel. -/
theorem par2546_of_E25 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hb : Minimality.T24.b2456 x = 0)
    (hE : ⟪F.N 4, x 5 - x 2⟫ = 0) : ∃ l : ℝ, x 6 - x 4 = l • (x 5 - x 2) := by
  set A := x 6 - x 4
  set U := x 5 - x 2
  have hAU_cross : cross A U = 0 := by
    by_contra hAU
    have hNA4 : ⟪F.N 4, A⟫ = 0 := by
      have := (F.hN 4 (x 6) (x 4)).symm
      rw [F.zero 4 6 (by decide), F.zero 4 4 (by decide), sub_self] at this
      exact this
    have hcr : cross (cross A U) (F.N 4) = 0 :=
      cross_eq_zero_of_perp2 (inner_cross_left A U) (inner_cross_right A U) hNA4 hE hAU
    have hk : F.N 4 = (⟪F.N 4, cross A U⟫ / ⟪cross A U, cross A U⟫) • (cross A U) :=
      eq_smul_of_cross_eq_zero hAU hcr
    have hdet : ⟪cross A U, x 4 - x 2⟫ = 0 := by
      have h1 := b2456_eq_det3 x
      rw [hb, zero_eq_neg] at h1
      exact h1
    have hN4_inner : ⟪F.N 4, x 4 - x 2⟫ = 0 := by
      rw [hk, real_inner_smul_left, hdet, mul_zero]
    have hf4_2 : F.f 4 (x 2) < 0 := F.neg 4 2 (by decide)
    have hN4_f : ⟪F.N 4, x 4 - x 2⟫ = - F.f 4 (x 2) := by
      have := (F.hN 4 (x 4) (x 2)).symm
      rw [F.zero 4 4 (by decide), zero_sub] at this
      exact this
    linarith [hN4_inner, hN4_f, hf4_2]
  have hU_ne : U ≠ 0 := by
    intro h
    have hx := Minimality.H24.SAT.inj_of_fac F
    have : x 5 = x 2 := sub_eq_zero.mp h
    exact absurd (hx this) (by decide)
  have hUA_cross : cross U A = 0 := by
    rw [show cross U A = - cross A U by ext j; fin_cases j <;> simp [cross] <;> ring, hAU_cross, neg_zero]
  obtain ⟨l, hl⟩ : ∃ l : ℝ, A = l • U := ⟨_, eq_smul_of_cross_eq_zero hU_ne hUA_cross⟩
  exact ⟨l, hl⟩

/-- **Type 24, `25 ∥ 46` off the double wall via `b2456 = 0` and facet 4 chord condition.** -/
theorem isRupert_of_E25 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hb : Minimality.T24.b2456 x = 0)
    (hE : ⟪F.N 4, x 5 - x 2⟫ = 0)
    (hw : ¬(⟪x 0 - x 5, x 5 - x 2⟫ = 0 ∧ ⟪x 0 - x 4, x 5 - x 2⟫ = 0)) :
    IsRupert (univ.image x) := by
  obtain ⟨l, hl⟩ := par2546_of_E25 F hb hE
  exact isRupert_par2546 F hl hw

end Minimality.T24.Par
