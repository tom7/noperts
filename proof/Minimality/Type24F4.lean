module

public import Minimality.Type24A2Lam

/-!
# Type 24, region A2: Lemma F4 (`CEGAR-A2.md` §5)

Formalizes the polynomial identity `lemma_f4_id`, the positive-definite algebraic obstruction
`lemma_f4_alg`, and the geometric corollary `lemma_f4_A2` on `CbarIn` / `OB1` (using
`A20.u27_z_bound` for `0 ≤ ⟪x 2 - x 0, u27 x⟫`).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.RCell Minimality.LexCell

namespace Minimality.T24

theorem lemma_f4_id (e_a e_b e_c : ℝ³) (ω3 ω5 : ℝ) :
    let u07 : ℝ³ := e_a + ω3 • e_b
    let u27 : ℝ³ := (1 + ω5) • e_a + (ω3 * ω5 - 1) • e_b + (ω3 + 1) • e_c
    (ω5 * (ω3 - 1) ^ 2 + 4) * ⟪e_a - e_b, u07⟫ +
    4 * (ω3 + 1) * ⟪e_c - e_a, u07⟫ +
    (ω3 - 1) ^ 2 * ⟪e_b - e_a, u27⟫ +
    (ω3 + 1) ^ 2 * ((3 - ω3) * (-⟪e_a, e_c⟫) + (ω3 + 1) * (-⟪e_b, e_c⟫) +
      ⟪e_a + e_b, e_a + e_b⟫) = 0 := by
  simp only [inner_sub_left, inner_add_left, inner_add_right, inner_smul_right,
    real_inner_comm e_b e_a, real_inner_comm e_c e_a, real_inner_comm e_c e_b]
  ring

theorem lemma_f4_alg (e_a e_b e_c : ℝ³) (hne : e_a + e_b ≠ 0)
    (h02 : ⟪e_a, e_c⟫ ≤ 0) (h12 : ⟪e_b, e_c⟫ ≤ 0)
    {ω3 ω5 : ℝ} (hω3_gt : -1 < ω3) (hω3_le : ω3 ≤ 3) (hω5 : 0 ≤ ω5) :
    let u07 : ℝ³ := e_a + ω3 • e_b
    let u27 : ℝ³ := (1 + ω5) • e_a + (ω3 * ω5 - 1) • e_b + (ω3 + 1) • e_c
    ¬ (0 ≤ ⟪e_a - e_b, u07⟫ ∧ 0 ≤ ⟪e_c - e_a, u07⟫ ∧ 0 ≤ ⟪e_b - e_a, u27⟫) := by
  dsimp only
  intro ⟨h1, h2, h3⟩
  have hid := lemma_f4_id e_a e_b e_c ω3 ω5
  dsimp only at hid
  have hnorm : 0 < ⟪e_a + e_b, e_a + e_b⟫ := real_inner_self_pos.mpr hne
  have hc1 : 0 ≤ ω5 * (ω3 - 1) ^ 2 + 4 := by positivity
  have hc2 : 0 ≤ 4 * (ω3 + 1) := by linarith
  have hc3 : 0 ≤ (ω3 - 1) ^ 2 := sq_nonneg _
  have hc4 : 0 < (ω3 + 1) ^ 2 := sq_pos_of_pos (by linarith)
  have hpd : 0 < (3 - ω3) * (-⟪e_a, e_c⟫) + (ω3 + 1) * (-⟪e_b, e_c⟫) +
      ⟪e_a + e_b, e_a + e_b⟫ := by
    nlinarith
  nlinarith [mul_nonneg hc1 h1, mul_nonneg hc2 h2, mul_nonneg hc3 h3, mul_pos hc4 hpd]

theorem lemma_f4_A2 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (hOB : H24K.SAT.OB1 x)
    (hω3 : omega3 x ≤ 3)
    (hu3 : 0 < ⟪F.N 3, A10.u27 x⟫) (hu8 : 0 < ⟪F.N 8, A10.u27 x⟫)
    (hL : ¬ LexAny F) :
    ¬ (0 ≤ ⟪x 0 - x 2, (x 0 - x 1) + omega3 x • (x 2 - x 1)⟫ ∧
       0 ≤ ⟪x 6 - x 0, (x 0 - x 1) + omega3 x • (x 2 - x 1)⟫) := by
  intro ⟨hz02, hz60⟩
  have hu27 : 0 ≤ ⟪x 2 - x 0, A10.u27 x⟫ := A20.u27_z_bound F hC hu3 hu8 hL
  have hne : (x 0 - x 1) + (x 2 - x 1) ≠ 0 := by
    intro h0
    have h5 := congrArg (fun w => ⟪F.N 5, w⟫) h0
    rw [inner_zero_right, inner_add_right, ← F.hN 5 (x 0) (x 1), ← F.hN 5 (x 2) (x 1),
      F.zero 5 1 (by decide), F.zero 5 2 (by decide), sub_zero, sub_self, add_zero] at h5
    exact (F.neg 5 0 (by decide)).ne h5
  have halg := lemma_f4_alg (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) hne
    hOB.2.1 hOB.2.2 (by linarith [hC.1]) hω3 hC.2.2.1.le
  apply halg
  refine ⟨?_, ?_, ?_⟩
  · simpa only [show (x 0 - x 1) - (x 2 - x 1) = x 0 - x 2 from by abel] using hz02
  · simpa only [show (x 6 - x 1) - (x 0 - x 1) = x 6 - x 0 from by abel] using hz60
  · simpa only [show (x 2 - x 1) - (x 0 - x 1) = x 2 - x 0 from by abel, A10.u27,
      show 1 + omega3 x = omega3 x + 1 from add_comm _ _] using hu27

end Minimality.T24
