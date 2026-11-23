module

public import Minimality.SVCTieGeo
public import Minimality.Type24TBVac
public import Minimality.Type24TBData_c01
public import Minimality.Type24SVCCells

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped RealInnerProductSpace
open Minimality Minimality.H21 Minimality.SVCC Minimality.SVCC.Cells Minimality.T24.SAT Minimality.SVC Minimality.SVC.Geo

namespace Minimality.SVCC.CellsTB

theorem c01_W0_real (EA EB h : ℝ) (hEA : 0 < EA) (hEB : 0 < EB) (hD : h ^ 2 < EA * EB) :
    (∃ lA lB : ℝ, 0 < lA ∧ lB < 0 ∧ 0 < 1 * (lA * EA + lB * h) + 0 * (lA * h + lB * EB) ∧ 0 < 0 * (lA * EA + lB * h) + (-1) * (lA * h + lB * EB) ∧ 0 < 1 * (lA * EA + lB * h) + (-1) * (lA * h + lB * EB)) := by
  have hD' : 0 < EA * EB - h ^ 2 := by linarith
  rcases lt_trichotomy h 0 with hh | hh | hh
  · have hh' : 0 < -h := by linarith
    refine ⟨(EB*(EA-h) - h*(-(EB-h))), (EA*(-(EB-h)) - h*(EA-h)), ?_, ?_, ?_, ?_, ?_⟩
    all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hh' hEA, mul_pos hh' hEB]
  · subst hh
    refine ⟨(EB*1 - 0*(-3)), (EA*(-3) - 0*1), ?_, ?_, ?_, ?_, ?_⟩
    all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB]
  · have hh' : 0 < h := hh
    rcases lt_trichotomy EA h with hA | hA | hA
    · rcases lt_trichotomy EB h with hB | hB | hB
      · exfalso; nlinarith [mul_pos hEA hEB]
      · exfalso; subst hB; nlinarith [mul_pos hEA hEB]
      · have hA' : 0 < h - EA := by linarith
        have hB' : 0 < EB - h := by linarith
        refine ⟨(EB*1 - h*(-3)), (EA*(-3) - h*1), ?_, ?_, ?_, ?_, ?_⟩
        all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hh' hEA, mul_pos hh' hEB]
    · subst hA
      have hB' : 0 < EB - EA := by nlinarith [mul_pos hEA hEB]
      refine ⟨(EB*1 - EA*(-3)), (EA*(-3) - EA*1), ?_, ?_, ?_, ?_, ?_⟩
      all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hh' hEA, mul_pos hh' hEB]
    · rcases lt_trichotomy EB h with hB | hB | hB
      · have hA' : 0 < EA - h := by linarith
        have hB' : 0 < h - EB := by linarith
        refine ⟨(EB*1 - h*(-3)), (EA*(-3) - h*1), ?_, ?_, ?_, ?_, ?_⟩
        all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hh' hEA, mul_pos hh' hEB]
      · subst hB
        have hA' : 0 < EA - EB := by linarith
        refine ⟨(EB*1 - EB*(-3)), (EA*(-3) - EB*1), ?_, ?_, ?_, ?_, ?_⟩
        all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hh' hEA, mul_pos hh' hEB]
      · have hA' : 0 < EA - h := by linarith
        have hB' : 0 < EB - h := by linarith
        refine ⟨(EB*1 - h*(-3)), (EA*(-3) - h*1), ?_, ?_, ?_, ?_, ?_⟩
        all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hh' hEA, mul_pos hh' hEB]

theorem c01_W0_leaf {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (w : ℝ³)
    (hA : ⟪F.N 0, w⟫ = 0) (hB : ⟪F.N 3, w⟫ = 0) (ht0 : ⟪F.N 1, w⟫ ≠ 0)
    (hW : TBLevel (fun i => ⟪x (c01_P i), w⟫) [[1], [4], [0, 2, 3], [5]]) :
    ∃ c ∈ c01_certs, c.W = [[1], [4], [0, 2, 3], [5]] ∧ TBReal F c01_P w c01_sw c01_R c := by
  have e1 : ⟪x 2, w⟫ = ⟪x 0, w⟫ := hW.1 [0, 2, 3] (by decide) 2 (by decide) 0 (by decide)
  have e2 : ⟪x 3, w⟫ = ⟪x 0, w⟫ := hW.1 [0, 2, 3] (by decide) 3 (by decide) 0 (by decide)
  have T : Tilt2 F 0 3 0 2 3 w :=
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, hA, hB,
      by rw [inner_sub_left, e1]; ring, by rw [inner_sub_left, e2]; ring,
      fun h => ht0 (by rw [h, inner_zero_right])⟩
  have key := c01_W0_real ⟪(x 2 - x 0), (x 2 - x 0)⟫ ⟪(x 3 - x 0), (x 3 - x 0)⟫ ⟪(x 2 - x 0), (x 3 - x 0)⟫ T.EA_pos T.EB_pos T.gram_pos
  rcases key with ⟨lA, lB, hqA, hqB, i0, i1, i2⟩
  · refine ⟨⟨[[1], [4], [0, 2, 3], [5]], 1, [1, 4, 3, 0, 2, 5]⟩, by decide, rfl, ?_⟩
    refine tbReal_of_tilt2 c01_P c01_sw c01_R _ T (by decide) 1 ht0 (c01_R[1]'(by decide)) (by simp) lA lB hqB.ne
      ((Tilt2.sign_pos_of_neg_mul hqB T.fAB_neg).trans (by decide))
      ((Tilt2.sign_neg_of_pos_mul hqA T.fBA_neg).trans (by decide)) ?_
    have dA := tb_depth_sub (x 2) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 1 0 (by simp)
    have dB := tb_depth_sub (x 3) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 0 1 (by simp)
    refine tb_htie_of_pairs (fun i => ⟪x (c01_P i), w⟫) (fun k => ⟪x (c01_P k), (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫) [[1], [4], [0, 2, 3], [5]] hW [1, 4, 3, 0, 2, 5]
      ([(0, 2), (3, 0), (3, 2)] : List (Fin 6 × Fin 6)) (by decide) ?_
    intro pr hpr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpr
    rcases hpr with rfl | rfl | rfl
    · show ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i0]
    · show ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i1]
    · show ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i2]

theorem c01_W1_real (EA EB h : ℝ) (hEA : 0 < EA) (hEB : 0 < EB) (hD : h ^ 2 < EA * EB) :
    (∃ lA lB : ℝ, 0 < lA ∧ 0 < lB ∧ 0 < 1 * (lA * EA + lB * h) + 0 * (lA * h + lB * EB) ∧ 0 < 0 * (lA * EA + lB * h) + 1 * (lA * h + lB * EB) ∧ 0 < (-1) * (lA * EA + lB * h) + 1 * (lA * h + lB * EB)) ∨ (∃ lA lB : ℝ, 0 < lA ∧ lB < 0 ∧ 0 < (-1) * (lA * EA + lB * h) + 0 * (lA * h + lB * EB) ∧ 0 < (-1) * (lA * EA + lB * h) + 1 * (lA * h + lB * EB) ∧ 0 < 0 * (lA * EA + lB * h) + (-1) * (lA * h + lB * EB)) ∨ (∃ lA lB : ℝ, 0 < lA ∧ lB < 0 ∧ 0 < (-1) * (lA * EA + lB * h) + 0 * (lA * h + lB * EB) ∧ 0 < 0 * (lA * EA + lB * h) + (-1) * (lA * h + lB * EB) ∧ 0 < 1 * (lA * EA + lB * h) + (-1) * (lA * h + lB * EB)) := by
  have hD' : 0 < EA * EB - h ^ 2 := by linarith
  rcases lt_trichotomy h 0 with hh | hh | hh
  · have hh' : 0 < -h := by linarith
    refine Or.inl (⟨(EB*1 - h*2), (EA*2 - h*1), ?_, ?_, ?_, ?_, ?_⟩)
    all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hh' hEA, mul_pos hh' hEB]
  · subst hh
    refine Or.inl (⟨(EB*1 - 0*2), (EA*2 - 0*1), ?_, ?_, ?_, ?_, ?_⟩)
    all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB]
  · have hh' : 0 < h := hh
    rcases lt_trichotomy EA h with hA | hA | hA
    · rcases lt_trichotomy EB h with hB | hB | hB
      · exfalso; nlinarith [mul_pos hEA hEB]
      · exfalso; subst hB; nlinarith [mul_pos hEA hEB]
      · have hA' : 0 < h - EA := by linarith
        have hB' : 0 < EB - h := by linarith
        refine Or.inl (⟨(EB*(EA+h) - h*(EB+h)), (EA*(EB+h) - h*(EA+h)), ?_, ?_, ?_, ?_, ?_⟩)
        all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hh' hEA, mul_pos hh' hEB]
    · subst hA
      have hB' : 0 < EB - EA := by nlinarith [mul_pos hEA hEB]
      refine Or.inl (⟨(EB*(EA+EA) - EA*(EB+EA)), (EA*(EB+EA) - EA*(EA+EA)), ?_, ?_, ?_, ?_, ?_⟩)
      all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hh' hEA, mul_pos hh' hEB]
    · rcases lt_trichotomy EB h with hB | hB | hB
      · have hA' : 0 < EA - h := by linarith
        have hB' : 0 < h - EB := by linarith
        refine Or.inr (Or.inl (⟨(EB*(-(EA+h)) - h*(-(EA+EB))), (EA*(-(EA+EB)) - h*(-(EA+h))), ?_, ?_, ?_, ?_, ?_⟩))
        all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hh' hEA, mul_pos hh' hEB]
      · subst hB
        have hA' : 0 < EA - EB := by linarith
        refine Or.inr (Or.inr (⟨(EB*(-2) - EB*(-3)), (EA*(-3) - EB*(-2)), ?_, ?_, ?_, ?_, ?_⟩))
        all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hh' hEA, mul_pos hh' hEB]
      · have hA' : 0 < EA - h := by linarith
        have hB' : 0 < EB - h := by linarith
        refine Or.inl (⟨(EB*(EA+h) - h*(EA+EB)), (EA*(EA+EB) - h*(EA+h)), ?_, ?_, ?_, ?_, ?_⟩)
        all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hh' hEA, mul_pos hh' hEB]

theorem c01_W1_leaf {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (w : ℝ³)
    (hA : ⟪F.N 0, w⟫ = 0) (hB : ⟪F.N 3, w⟫ = 0) (ht0 : ⟪F.N 1, w⟫ ≠ 0)
    (hW : TBLevel (fun i => ⟪x (c01_P i), w⟫) [[1], [5], [0, 2, 3], [4]]) :
    ∃ c ∈ c01_certs, c.W = [[1], [5], [0, 2, 3], [4]] ∧ TBReal F c01_P w c01_sw c01_R c := by
  have e1 : ⟪x 2, w⟫ = ⟪x 0, w⟫ := hW.1 [0, 2, 3] (by decide) 2 (by decide) 0 (by decide)
  have e2 : ⟪x 3, w⟫ = ⟪x 0, w⟫ := hW.1 [0, 2, 3] (by decide) 3 (by decide) 0 (by decide)
  have T : Tilt2 F 0 3 0 2 3 w :=
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, hA, hB,
      by rw [inner_sub_left, e1]; ring, by rw [inner_sub_left, e2]; ring,
      fun h => ht0 (by rw [h, inner_zero_right])⟩
  have key := c01_W1_real ⟪(x 2 - x 0), (x 2 - x 0)⟫ ⟪(x 3 - x 0), (x 3 - x 0)⟫ ⟪(x 2 - x 0), (x 3 - x 0)⟫ T.EA_pos T.EB_pos T.gram_pos
  rcases key with ⟨lA, lB, hqA, hqB, i0, i1, i2⟩ | ⟨lA, lB, hqA, hqB, i0, i1, i2⟩ | ⟨lA, lB, hqA, hqB, i0, i1, i2⟩
  · refine ⟨⟨[[1], [5], [0, 2, 3], [4]], 0, [1, 5, 0, 2, 3, 4]⟩, by decide, rfl, ?_⟩
    refine tbReal_of_tilt2 c01_P c01_sw c01_R _ T (by decide) 1 ht0 (c01_R[0]'(by decide)) (by simp) lA lB hqB.ne'
      ((Tilt2.sign_neg_of_pos_mul hqB T.fAB_neg).trans (by decide))
      ((Tilt2.sign_neg_of_pos_mul hqA T.fBA_neg).trans (by decide)) ?_
    have dA := tb_depth_sub (x 2) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 1 0 (by simp)
    have dB := tb_depth_sub (x 3) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 0 1 (by simp)
    refine tb_htie_of_pairs (fun i => ⟪x (c01_P i), w⟫) (fun k => ⟪x (c01_P k), (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫) [[1], [5], [0, 2, 3], [4]] hW [1, 5, 0, 2, 3, 4]
      ([(0, 2), (0, 3), (2, 3)] : List (Fin 6 × Fin 6)) (by decide) ?_
    intro pr hpr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpr
    rcases hpr with rfl | rfl | rfl
    · show ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i0]
    · show ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i1]
    · show ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i2]
  · refine ⟨⟨[[1], [5], [0, 2, 3], [4]], 1, [1, 5, 2, 3, 0, 4]⟩, by decide, rfl, ?_⟩
    refine tbReal_of_tilt2 c01_P c01_sw c01_R _ T (by decide) 1 ht0 (c01_R[1]'(by decide)) (by simp) lA lB hqB.ne
      ((Tilt2.sign_pos_of_neg_mul hqB T.fAB_neg).trans (by decide))
      ((Tilt2.sign_neg_of_pos_mul hqA T.fBA_neg).trans (by decide)) ?_
    have dA := tb_depth_sub (x 2) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 1 0 (by simp)
    have dB := tb_depth_sub (x 3) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 0 1 (by simp)
    refine tb_htie_of_pairs (fun i => ⟪x (c01_P i), w⟫) (fun k => ⟪x (c01_P k), (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫) [[1], [5], [0, 2, 3], [4]] hW [1, 5, 2, 3, 0, 4]
      ([(2, 0), (2, 3), (3, 0)] : List (Fin 6 × Fin 6)) (by decide) ?_
    intro pr hpr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpr
    rcases hpr with rfl | rfl | rfl
    · show ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i0]
    · show ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i1]
    · show ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i2]
  · refine ⟨⟨[[1], [5], [0, 2, 3], [4]], 1, [1, 5, 3, 2, 0, 4]⟩, by decide, rfl, ?_⟩
    refine tbReal_of_tilt2 c01_P c01_sw c01_R _ T (by decide) 1 ht0 (c01_R[1]'(by decide)) (by simp) lA lB hqB.ne
      ((Tilt2.sign_pos_of_neg_mul hqB T.fAB_neg).trans (by decide))
      ((Tilt2.sign_neg_of_pos_mul hqA T.fBA_neg).trans (by decide)) ?_
    have dA := tb_depth_sub (x 2) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 1 0 (by simp)
    have dB := tb_depth_sub (x 3) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 0 1 (by simp)
    refine tb_htie_of_pairs (fun i => ⟪x (c01_P i), w⟫) (fun k => ⟪x (c01_P k), (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫) [[1], [5], [0, 2, 3], [4]] hW [1, 5, 3, 2, 0, 4]
      ([(2, 0), (3, 0), (3, 2)] : List (Fin 6 × Fin 6)) (by decide) ?_
    intro pr hpr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpr
    rcases hpr with rfl | rfl | rfl
    · show ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i0]
    · show ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i1]
    · show ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i2]

theorem c01_W2_real (EA EB h : ℝ) (hEA : 0 < EA) (hEB : 0 < EB) (hD : h ^ 2 < EA * EB) :
    (∃ lA lB : ℝ, 0 < lA ∧ lB < 0 ∧ 0 < 1 * (lA * EA + lB * h) + 0 * (lA * h + lB * EB) ∧ 0 < 0 * (lA * EA + lB * h) + (-1) * (lA * h + lB * EB) ∧ 0 < 1 * (lA * EA + lB * h) + (-1) * (lA * h + lB * EB)) := by
  have hD' : 0 < EA * EB - h ^ 2 := by linarith
  rcases lt_trichotomy h 0 with hh | hh | hh
  · have hh' : 0 < -h := by linarith
    refine ⟨(EB*(EA-h) - h*(-(EB-h))), (EA*(-(EB-h)) - h*(EA-h)), ?_, ?_, ?_, ?_, ?_⟩
    all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hh' hEA, mul_pos hh' hEB]
  · subst hh
    refine ⟨(EB*1 - 0*(-3)), (EA*(-3) - 0*1), ?_, ?_, ?_, ?_, ?_⟩
    all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB]
  · have hh' : 0 < h := hh
    rcases lt_trichotomy EA h with hA | hA | hA
    · rcases lt_trichotomy EB h with hB | hB | hB
      · exfalso; nlinarith [mul_pos hEA hEB]
      · exfalso; subst hB; nlinarith [mul_pos hEA hEB]
      · have hA' : 0 < h - EA := by linarith
        have hB' : 0 < EB - h := by linarith
        refine ⟨(EB*1 - h*(-3)), (EA*(-3) - h*1), ?_, ?_, ?_, ?_, ?_⟩
        all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hh' hEA, mul_pos hh' hEB]
    · subst hA
      have hB' : 0 < EB - EA := by nlinarith [mul_pos hEA hEB]
      refine ⟨(EB*1 - EA*(-3)), (EA*(-3) - EA*1), ?_, ?_, ?_, ?_, ?_⟩
      all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hh' hEA, mul_pos hh' hEB]
    · rcases lt_trichotomy EB h with hB | hB | hB
      · have hA' : 0 < EA - h := by linarith
        have hB' : 0 < h - EB := by linarith
        refine ⟨(EB*1 - h*(-3)), (EA*(-3) - h*1), ?_, ?_, ?_, ?_, ?_⟩
        all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hh' hEA, mul_pos hh' hEB]
      · subst hB
        have hA' : 0 < EA - EB := by linarith
        refine ⟨(EB*1 - EB*(-3)), (EA*(-3) - EB*1), ?_, ?_, ?_, ?_, ?_⟩
        all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hh' hEA, mul_pos hh' hEB]
      · have hA' : 0 < EA - h := by linarith
        have hB' : 0 < EB - h := by linarith
        refine ⟨(EB*1 - h*(-3)), (EA*(-3) - h*1), ?_, ?_, ?_, ?_, ?_⟩
        all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hh' hEA, mul_pos hh' hEB]

theorem c01_W2_leaf {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (w : ℝ³)
    (hA : ⟪F.N 0, w⟫ = 0) (hB : ⟪F.N 3, w⟫ = 0) (ht0 : ⟪F.N 1, w⟫ ≠ 0)
    (hW : TBLevel (fun i => ⟪x (c01_P i), w⟫) [[4], [1], [0, 2, 3], [5]]) :
    ∃ c ∈ c01_certs, c.W = [[4], [1], [0, 2, 3], [5]] ∧ TBReal F c01_P w c01_sw c01_R c := by
  have e1 : ⟪x 2, w⟫ = ⟪x 0, w⟫ := hW.1 [0, 2, 3] (by decide) 2 (by decide) 0 (by decide)
  have e2 : ⟪x 3, w⟫ = ⟪x 0, w⟫ := hW.1 [0, 2, 3] (by decide) 3 (by decide) 0 (by decide)
  have T : Tilt2 F 0 3 0 2 3 w :=
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, hA, hB,
      by rw [inner_sub_left, e1]; ring, by rw [inner_sub_left, e2]; ring,
      fun h => ht0 (by rw [h, inner_zero_right])⟩
  have key := c01_W2_real ⟪(x 2 - x 0), (x 2 - x 0)⟫ ⟪(x 3 - x 0), (x 3 - x 0)⟫ ⟪(x 2 - x 0), (x 3 - x 0)⟫ T.EA_pos T.EB_pos T.gram_pos
  rcases key with ⟨lA, lB, hqA, hqB, i0, i1, i2⟩
  · refine ⟨⟨[[4], [1], [0, 2, 3], [5]], 1, [4, 1, 3, 0, 2, 5]⟩, by decide, rfl, ?_⟩
    refine tbReal_of_tilt2 c01_P c01_sw c01_R _ T (by decide) 1 ht0 (c01_R[1]'(by decide)) (by simp) lA lB hqB.ne
      ((Tilt2.sign_pos_of_neg_mul hqB T.fAB_neg).trans (by decide))
      ((Tilt2.sign_neg_of_pos_mul hqA T.fBA_neg).trans (by decide)) ?_
    have dA := tb_depth_sub (x 2) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 1 0 (by simp)
    have dB := tb_depth_sub (x 3) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 0 1 (by simp)
    refine tb_htie_of_pairs (fun i => ⟪x (c01_P i), w⟫) (fun k => ⟪x (c01_P k), (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫) [[4], [1], [0, 2, 3], [5]] hW [4, 1, 3, 0, 2, 5]
      ([(0, 2), (3, 0), (3, 2)] : List (Fin 6 × Fin 6)) (by decide) ?_
    intro pr hpr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpr
    rcases hpr with rfl | rfl | rfl
    · show ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i0]
    · show ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i1]
    · show ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i2]

theorem c01_W3_real (EA EB h : ℝ) (hEA : 0 < EA) (hEB : 0 < EB) (hD : h ^ 2 < EA * EB) :
    (∃ lA lB : ℝ, 0 < lA ∧ 0 < lB ∧ 0 < 1 * (lA * EA + lB * h) + 0 * (lA * h + lB * EB) ∧ 0 < 0 * (lA * EA + lB * h) + 1 * (lA * h + lB * EB) ∧ 0 < 1 * (lA * EA + lB * h) + (-1) * (lA * h + lB * EB)) ∨ (∃ lA lB : ℝ, 0 < lA ∧ lB < 0 ∧ 0 < 1 * (lA * EA + lB * h) + 0 * (lA * h + lB * EB) ∧ 0 < 0 * (lA * EA + lB * h) + 1 * (lA * h + lB * EB) ∧ 0 < (-1) * (lA * EA + lB * h) + 1 * (lA * h + lB * EB)) ∨ (∃ lA lB : ℝ, 0 < lA ∧ lB < 0 ∧ 0 < 1 * (lA * EA + lB * h) + 0 * (lA * h + lB * EB) ∧ 0 < 0 * (lA * EA + lB * h) + 1 * (lA * h + lB * EB) ∧ 0 < 1 * (lA * EA + lB * h) + (-1) * (lA * h + lB * EB)) := by
  have hD' : 0 < EA * EB - h ^ 2 := by linarith
  rcases lt_trichotomy h 0 with hh | hh | hh
  · have hh' : 0 < -h := by linarith
    refine Or.inl (⟨(EB*2 - h*1), (EA*1 - h*2), ?_, ?_, ?_, ?_, ?_⟩)
    all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hh' hEA, mul_pos hh' hEB]
  · subst hh
    refine Or.inl (⟨(EB*2 - 0*1), (EA*1 - 0*2), ?_, ?_, ?_, ?_, ?_⟩)
    all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB]
  · have hh' : 0 < h := hh
    rcases lt_trichotomy EA h with hA | hA | hA
    · rcases lt_trichotomy EB h with hB | hB | hB
      · exfalso; nlinarith [mul_pos hEA hEB]
      · exfalso; subst hB; nlinarith [mul_pos hEA hEB]
      · have hA' : 0 < h - EA := by linarith
        have hB' : 0 < EB - h := by linarith
        refine Or.inr (Or.inl (⟨(EB*(EA+EB) - h*(EB+h)), (EA*(EB+h) - h*(EA+EB)), ?_, ?_, ?_, ?_, ?_⟩))
        all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hh' hEA, mul_pos hh' hEB]
    · subst hA
      have hB' : 0 < EB - EA := by nlinarith [mul_pos hEA hEB]
      refine Or.inr (Or.inr (⟨(EB*2 - EA*1), (EA*1 - EA*2), ?_, ?_, ?_, ?_, ?_⟩))
      all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hh' hEA, mul_pos hh' hEB]
    · rcases lt_trichotomy EB h with hB | hB | hB
      · have hA' : 0 < EA - h := by linarith
        have hB' : 0 < h - EB := by linarith
        refine Or.inl (⟨(EB*(EA+h) - h*(EB+h)), (EA*(EB+h) - h*(EA+h)), ?_, ?_, ?_, ?_, ?_⟩)
        all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hh' hEA, mul_pos hh' hEB]
      · subst hB
        have hA' : 0 < EA - EB := by linarith
        refine Or.inl (⟨(EB*(EA+EB) - EB*(EB+EB)), (EA*(EB+EB) - EB*(EA+EB)), ?_, ?_, ?_, ?_, ?_⟩)
        all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hh' hEA, mul_pos hh' hEB]
      · have hA' : 0 < EA - h := by linarith
        have hB' : 0 < EB - h := by linarith
        refine Or.inl (⟨(EB*(EA+EB) - h*(EB+h)), (EA*(EB+h) - h*(EA+EB)), ?_, ?_, ?_, ?_, ?_⟩)
        all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hh' hEA, mul_pos hh' hEB]

theorem c01_W3_leaf {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (w : ℝ³)
    (hA : ⟪F.N 0, w⟫ = 0) (hB : ⟪F.N 3, w⟫ = 0) (ht0 : ⟪F.N 1, w⟫ ≠ 0)
    (hW : TBLevel (fun i => ⟪x (c01_P i), w⟫) [[4], [0, 2, 3], [1], [5]]) :
    ∃ c ∈ c01_certs, c.W = [[4], [0, 2, 3], [1], [5]] ∧ TBReal F c01_P w c01_sw c01_R c := by
  have e1 : ⟪x 2, w⟫ = ⟪x 0, w⟫ := hW.1 [0, 2, 3] (by decide) 2 (by decide) 0 (by decide)
  have e2 : ⟪x 3, w⟫ = ⟪x 0, w⟫ := hW.1 [0, 2, 3] (by decide) 3 (by decide) 0 (by decide)
  have T : Tilt2 F 0 3 0 2 3 w :=
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, hA, hB,
      by rw [inner_sub_left, e1]; ring, by rw [inner_sub_left, e2]; ring,
      fun h => ht0 (by rw [h, inner_zero_right])⟩
  have key := c01_W3_real ⟪(x 2 - x 0), (x 2 - x 0)⟫ ⟪(x 3 - x 0), (x 3 - x 0)⟫ ⟪(x 2 - x 0), (x 3 - x 0)⟫ T.EA_pos T.EB_pos T.gram_pos
  rcases key with ⟨lA, lB, hqA, hqB, i0, i1, i2⟩ | ⟨lA, lB, hqA, hqB, i0, i1, i2⟩ | ⟨lA, lB, hqA, hqB, i0, i1, i2⟩
  · refine ⟨⟨[[4], [0, 2, 3], [1], [5]], 0, [4, 0, 3, 2, 1, 5]⟩, by decide, rfl, ?_⟩
    refine tbReal_of_tilt2 c01_P c01_sw c01_R _ T (by decide) 1 ht0 (c01_R[0]'(by decide)) (by simp) lA lB hqB.ne'
      ((Tilt2.sign_neg_of_pos_mul hqB T.fAB_neg).trans (by decide))
      ((Tilt2.sign_neg_of_pos_mul hqA T.fBA_neg).trans (by decide)) ?_
    have dA := tb_depth_sub (x 2) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 1 0 (by simp)
    have dB := tb_depth_sub (x 3) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 0 1 (by simp)
    refine tb_htie_of_pairs (fun i => ⟪x (c01_P i), w⟫) (fun k => ⟪x (c01_P k), (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫) [[4], [0, 2, 3], [1], [5]] hW [4, 0, 3, 2, 1, 5]
      ([(0, 2), (0, 3), (3, 2)] : List (Fin 6 × Fin 6)) (by decide) ?_
    intro pr hpr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpr
    rcases hpr with rfl | rfl | rfl
    · show ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i0]
    · show ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i1]
    · show ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i2]
  · refine ⟨⟨[[4], [0, 2, 3], [1], [5]], 1, [4, 0, 2, 3, 1, 5]⟩, by decide, rfl, ?_⟩
    refine tbReal_of_tilt2 c01_P c01_sw c01_R _ T (by decide) 1 ht0 (c01_R[1]'(by decide)) (by simp) lA lB hqB.ne
      ((Tilt2.sign_pos_of_neg_mul hqB T.fAB_neg).trans (by decide))
      ((Tilt2.sign_neg_of_pos_mul hqA T.fBA_neg).trans (by decide)) ?_
    have dA := tb_depth_sub (x 2) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 1 0 (by simp)
    have dB := tb_depth_sub (x 3) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 0 1 (by simp)
    refine tb_htie_of_pairs (fun i => ⟪x (c01_P i), w⟫) (fun k => ⟪x (c01_P k), (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫) [[4], [0, 2, 3], [1], [5]] hW [4, 0, 2, 3, 1, 5]
      ([(0, 2), (0, 3), (2, 3)] : List (Fin 6 × Fin 6)) (by decide) ?_
    intro pr hpr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpr
    rcases hpr with rfl | rfl | rfl
    · show ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i0]
    · show ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i1]
    · show ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i2]
  · refine ⟨⟨[[4], [0, 2, 3], [1], [5]], 1, [4, 0, 3, 2, 1, 5]⟩, by decide, rfl, ?_⟩
    refine tbReal_of_tilt2 c01_P c01_sw c01_R _ T (by decide) 1 ht0 (c01_R[1]'(by decide)) (by simp) lA lB hqB.ne
      ((Tilt2.sign_pos_of_neg_mul hqB T.fAB_neg).trans (by decide))
      ((Tilt2.sign_neg_of_pos_mul hqA T.fBA_neg).trans (by decide)) ?_
    have dA := tb_depth_sub (x 2) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 1 0 (by simp)
    have dB := tb_depth_sub (x 3) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 0 1 (by simp)
    refine tb_htie_of_pairs (fun i => ⟪x (c01_P i), w⟫) (fun k => ⟪x (c01_P k), (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫) [[4], [0, 2, 3], [1], [5]] hW [4, 0, 3, 2, 1, 5]
      ([(0, 2), (0, 3), (3, 2)] : List (Fin 6 × Fin 6)) (by decide) ?_
    intro pr hpr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpr
    rcases hpr with rfl | rfl | rfl
    · show ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i0]
    · show ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i1]
    · show ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i2]

theorem c01_W4_real (EA EB h : ℝ) (hEA : 0 < EA) (hEB : 0 < EB) (hD : h ^ 2 < EA * EB) :
    (∃ lA lB : ℝ, 0 < lA ∧ 0 < lB ∧ 0 < 1 * (lA * EA + lB * h) + 0 * (lA * h + lB * EB) ∧ 0 < 0 * (lA * EA + lB * h) + 1 * (lA * h + lB * EB) ∧ 0 < 1 * (lA * EA + lB * h) + (-1) * (lA * h + lB * EB)) ∨ (∃ lA lB : ℝ, 0 < lA ∧ lB < 0 ∧ 0 < 1 * (lA * EA + lB * h) + 0 * (lA * h + lB * EB) ∧ 0 < 0 * (lA * EA + lB * h) + 1 * (lA * h + lB * EB) ∧ 0 < (-1) * (lA * EA + lB * h) + 1 * (lA * h + lB * EB)) ∨ (∃ lA lB : ℝ, 0 < lA ∧ lB < 0 ∧ 0 < 1 * (lA * EA + lB * h) + 0 * (lA * h + lB * EB) ∧ 0 < 0 * (lA * EA + lB * h) + 1 * (lA * h + lB * EB) ∧ 0 < 1 * (lA * EA + lB * h) + (-1) * (lA * h + lB * EB)) := by
  have hD' : 0 < EA * EB - h ^ 2 := by linarith
  rcases lt_trichotomy h 0 with hh | hh | hh
  · have hh' : 0 < -h := by linarith
    refine Or.inl (⟨(EB*2 - h*1), (EA*1 - h*2), ?_, ?_, ?_, ?_, ?_⟩)
    all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hh' hEA, mul_pos hh' hEB]
  · subst hh
    refine Or.inl (⟨(EB*2 - 0*1), (EA*1 - 0*2), ?_, ?_, ?_, ?_, ?_⟩)
    all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB]
  · have hh' : 0 < h := hh
    rcases lt_trichotomy EA h with hA | hA | hA
    · rcases lt_trichotomy EB h with hB | hB | hB
      · exfalso; nlinarith [mul_pos hEA hEB]
      · exfalso; subst hB; nlinarith [mul_pos hEA hEB]
      · have hA' : 0 < h - EA := by linarith
        have hB' : 0 < EB - h := by linarith
        refine Or.inr (Or.inl (⟨(EB*(EA+EB) - h*(EB+h)), (EA*(EB+h) - h*(EA+EB)), ?_, ?_, ?_, ?_, ?_⟩))
        all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hh' hEA, mul_pos hh' hEB]
    · subst hA
      have hB' : 0 < EB - EA := by nlinarith [mul_pos hEA hEB]
      refine Or.inr (Or.inr (⟨(EB*2 - EA*1), (EA*1 - EA*2), ?_, ?_, ?_, ?_, ?_⟩))
      all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hh' hEA, mul_pos hh' hEB]
    · rcases lt_trichotomy EB h with hB | hB | hB
      · have hA' : 0 < EA - h := by linarith
        have hB' : 0 < h - EB := by linarith
        refine Or.inl (⟨(EB*(EA+h) - h*(EB+h)), (EA*(EB+h) - h*(EA+h)), ?_, ?_, ?_, ?_, ?_⟩)
        all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hh' hEA, mul_pos hh' hEB]
      · subst hB
        have hA' : 0 < EA - EB := by linarith
        refine Or.inl (⟨(EB*(EA+EB) - EB*(EB+EB)), (EA*(EB+EB) - EB*(EA+EB)), ?_, ?_, ?_, ?_, ?_⟩)
        all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hh' hEA, mul_pos hh' hEB]
      · have hA' : 0 < EA - h := by linarith
        have hB' : 0 < EB - h := by linarith
        refine Or.inl (⟨(EB*(EA+EB) - h*(EB+h)), (EA*(EB+h) - h*(EA+EB)), ?_, ?_, ?_, ?_, ?_⟩)
        all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hh' hEA, mul_pos hh' hEB]

theorem c01_W4_leaf {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (w : ℝ³)
    (hA : ⟪F.N 0, w⟫ = 0) (hB : ⟪F.N 3, w⟫ = 0) (ht0 : ⟪F.N 1, w⟫ ≠ 0)
    (hW : TBLevel (fun i => ⟪x (c01_P i), w⟫) [[4], [0, 2, 3], [5], [1]]) :
    ∃ c ∈ c01_certs, c.W = [[4], [0, 2, 3], [5], [1]] ∧ TBReal F c01_P w c01_sw c01_R c := by
  have e1 : ⟪x 2, w⟫ = ⟪x 0, w⟫ := hW.1 [0, 2, 3] (by decide) 2 (by decide) 0 (by decide)
  have e2 : ⟪x 3, w⟫ = ⟪x 0, w⟫ := hW.1 [0, 2, 3] (by decide) 3 (by decide) 0 (by decide)
  have T : Tilt2 F 0 3 0 2 3 w :=
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, hA, hB,
      by rw [inner_sub_left, e1]; ring, by rw [inner_sub_left, e2]; ring,
      fun h => ht0 (by rw [h, inner_zero_right])⟩
  have key := c01_W4_real ⟪(x 2 - x 0), (x 2 - x 0)⟫ ⟪(x 3 - x 0), (x 3 - x 0)⟫ ⟪(x 2 - x 0), (x 3 - x 0)⟫ T.EA_pos T.EB_pos T.gram_pos
  rcases key with ⟨lA, lB, hqA, hqB, i0, i1, i2⟩ | ⟨lA, lB, hqA, hqB, i0, i1, i2⟩ | ⟨lA, lB, hqA, hqB, i0, i1, i2⟩
  · refine ⟨⟨[[4], [0, 2, 3], [5], [1]], 0, [4, 0, 3, 2, 5, 1]⟩, by decide, rfl, ?_⟩
    refine tbReal_of_tilt2 c01_P c01_sw c01_R _ T (by decide) 1 ht0 (c01_R[0]'(by decide)) (by simp) lA lB hqB.ne'
      ((Tilt2.sign_neg_of_pos_mul hqB T.fAB_neg).trans (by decide))
      ((Tilt2.sign_neg_of_pos_mul hqA T.fBA_neg).trans (by decide)) ?_
    have dA := tb_depth_sub (x 2) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 1 0 (by simp)
    have dB := tb_depth_sub (x 3) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 0 1 (by simp)
    refine tb_htie_of_pairs (fun i => ⟪x (c01_P i), w⟫) (fun k => ⟪x (c01_P k), (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫) [[4], [0, 2, 3], [5], [1]] hW [4, 0, 3, 2, 5, 1]
      ([(0, 2), (0, 3), (3, 2)] : List (Fin 6 × Fin 6)) (by decide) ?_
    intro pr hpr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpr
    rcases hpr with rfl | rfl | rfl
    · show ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i0]
    · show ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i1]
    · show ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i2]
  · refine ⟨⟨[[4], [0, 2, 3], [5], [1]], 1, [4, 0, 2, 3, 5, 1]⟩, by decide, rfl, ?_⟩
    refine tbReal_of_tilt2 c01_P c01_sw c01_R _ T (by decide) 1 ht0 (c01_R[1]'(by decide)) (by simp) lA lB hqB.ne
      ((Tilt2.sign_pos_of_neg_mul hqB T.fAB_neg).trans (by decide))
      ((Tilt2.sign_neg_of_pos_mul hqA T.fBA_neg).trans (by decide)) ?_
    have dA := tb_depth_sub (x 2) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 1 0 (by simp)
    have dB := tb_depth_sub (x 3) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 0 1 (by simp)
    refine tb_htie_of_pairs (fun i => ⟪x (c01_P i), w⟫) (fun k => ⟪x (c01_P k), (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫) [[4], [0, 2, 3], [5], [1]] hW [4, 0, 2, 3, 5, 1]
      ([(0, 2), (0, 3), (2, 3)] : List (Fin 6 × Fin 6)) (by decide) ?_
    intro pr hpr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpr
    rcases hpr with rfl | rfl | rfl
    · show ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i0]
    · show ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i1]
    · show ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i2]
  · refine ⟨⟨[[4], [0, 2, 3], [5], [1]], 1, [4, 0, 3, 2, 5, 1]⟩, by decide, rfl, ?_⟩
    refine tbReal_of_tilt2 c01_P c01_sw c01_R _ T (by decide) 1 ht0 (c01_R[1]'(by decide)) (by simp) lA lB hqB.ne
      ((Tilt2.sign_pos_of_neg_mul hqB T.fAB_neg).trans (by decide))
      ((Tilt2.sign_neg_of_pos_mul hqA T.fBA_neg).trans (by decide)) ?_
    have dA := tb_depth_sub (x 2) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 1 0 (by simp)
    have dB := tb_depth_sub (x 3) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 0 1 (by simp)
    refine tb_htie_of_pairs (fun i => ⟪x (c01_P i), w⟫) (fun k => ⟪x (c01_P k), (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫) [[4], [0, 2, 3], [5], [1]] hW [4, 0, 3, 2, 5, 1]
      ([(0, 2), (0, 3), (3, 2)] : List (Fin 6 × Fin 6)) (by decide) ?_
    intro pr hpr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpr
    rcases hpr with rfl | rfl | rfl
    · show ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i0]
    · show ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i1]
    · show ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i2]

theorem c01_W5_real (EA EB h al be : ℝ) (hEA : 0 < EA) (hEB : 0 < EB) (hD : h ^ 2 < EA * EB) (hal : 0 < al) (hbe : 0 < be) :
    (∃ lA lB : ℝ, 0 < lA ∧ 0 < lB ∧ 0 < 1 * (lA * EA + lB * h) + 0 * (lA * h + lB * EB) ∧ 0 < 0 * (lA * EA + lB * h) + 1 * (lA * h + lB * EB) ∧ 0 < 1 * (lA * EA + lB * h) + (-1) * (lA * h + lB * EB) ∧ 0 < al * (lA * EA + lB * h) + (-be) * (lA * h + lB * EB)) ∨ (∃ lA lB : ℝ, 0 < lA ∧ lB < 0 ∧ 0 < 1 * (lA * EA + lB * h) + 0 * (lA * h + lB * EB) ∧ 0 < 0 * (lA * EA + lB * h) + 1 * (lA * h + lB * EB) ∧ 0 < 1 * (lA * EA + lB * h) + (-1) * (lA * h + lB * EB) ∧ 0 < al * (lA * EA + lB * h) + (-be) * (lA * h + lB * EB)) ∨ (∃ lA lB : ℝ, 0 < lA ∧ lB < 0 ∧ 0 < 1 * (lA * EA + lB * h) + 0 * (lA * h + lB * EB) ∧ 0 < 0 * (lA * EA + lB * h) + (-1) * (lA * h + lB * EB) ∧ 0 < 1 * (lA * EA + lB * h) + (-1) * (lA * h + lB * EB) ∧ 0 < al * (lA * EA + lB * h) + (-be) * (lA * h + lB * EB)) := by
  have hD' : 0 < EA * EB - h ^ 2 := by linarith
  rcases lt_trichotomy h 0 with hh | hh | hh
  · have hh' : 0 < -h := by linarith
    refine Or.inl (⟨(EB*(al+be) - h*(al)), (EA*(al) - h*(al+be)), ?_, ?_, ?_, ?_, ?_, ?_⟩)
    all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hal hbe, mul_pos hal hD', mul_pos hbe hD', mul_pos hal hEA, mul_pos hal hEB, mul_pos hbe hEA, mul_pos hbe hEB, mul_pos hh' hEA, mul_pos hh' hEB]
  · subst hh
    refine Or.inl (⟨(EB*(al+be) - 0*(al)), (EA*(al) - 0*(al+be)), ?_, ?_, ?_, ?_, ?_, ?_⟩)
    all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hal hbe, mul_pos hal hD', mul_pos hbe hD', mul_pos hal hEA, mul_pos hal hEB, mul_pos hbe hEA, mul_pos hbe hEB]
  · have hh' : 0 < h := hh
    rcases lt_trichotomy EA h with hA | hA | hA
    · rcases lt_trichotomy EB h with hB | hB | hB
      · exfalso; nlinarith [mul_pos hEA hEB]
      · exfalso; subst hB; nlinarith [mul_pos hEA hEB]
      · have hA' : 0 < h - EA := by linarith
        have hB' : 0 < EB - h := by linarith
        refine Or.inr (Or.inl (⟨(EB*(al+be) - h*(al)), (EA*(al) - h*(al+be)), ?_, ?_, ?_, ?_, ?_, ?_⟩))
        all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hal hbe, mul_pos hal hD', mul_pos hbe hD', mul_pos hal hEA, mul_pos hal hEB, mul_pos hbe hEA, mul_pos hbe hEB, mul_pos hh' hEA, mul_pos hh' hEB]
    · subst hA
      have hB' : 0 < EB - EA := by nlinarith [mul_pos hEA hEB]
      refine Or.inr (Or.inl (⟨(EB*(al+be) - EA*(al)), (EA*(al) - EA*(al+be)), ?_, ?_, ?_, ?_, ?_, ?_⟩))
      all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hal hbe, mul_pos hal hD', mul_pos hbe hD', mul_pos hal hEA, mul_pos hal hEB, mul_pos hbe hEA, mul_pos hbe hEB, mul_pos hh' hEA, mul_pos hh' hEB]
    · rcases lt_trichotomy EB h with hB | hB | hB
      · have hA' : 0 < EA - h := by linarith
        have hB' : 0 < h - EB := by linarith
        refine Or.inr (Or.inr (⟨(EB*1 - h*(-3)), (EA*(-3) - h*1), ?_, ?_, ?_, ?_, ?_, ?_⟩))
        all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hal hbe, mul_pos hal hD', mul_pos hbe hD', mul_pos hal hEA, mul_pos hal hEB, mul_pos hbe hEA, mul_pos hbe hEB, mul_pos hh' hEA, mul_pos hh' hEB]
      · subst hB
        have hA' : 0 < EA - EB := by linarith
        refine Or.inr (Or.inr (⟨(EB*1 - EB*(-3)), (EA*(-3) - EB*1), ?_, ?_, ?_, ?_, ?_, ?_⟩))
        all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hal hbe, mul_pos hal hD', mul_pos hbe hD', mul_pos hal hEA, mul_pos hal hEB, mul_pos hbe hEA, mul_pos hbe hEB, mul_pos hh' hEA, mul_pos hh' hEB]
      · have hA' : 0 < EA - h := by linarith
        have hB' : 0 < EB - h := by linarith
        refine Or.inr (Or.inr (⟨(EB*1 - h*(-3)), (EA*(-3) - h*1), ?_, ?_, ?_, ?_, ?_, ?_⟩))
        all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hal hbe, mul_pos hal hD', mul_pos hbe hD', mul_pos hal hEA, mul_pos hal hEB, mul_pos hbe hEA, mul_pos hbe hEB, mul_pos hh' hEA, mul_pos hh' hEB]

theorem c01_W5_leaf {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (w : ℝ³)
    (hA : ⟪F.N 0, w⟫ = 0) (hB : ⟪F.N 3, w⟫ = 0) (ht0 : ⟪F.N 1, w⟫ ≠ 0)
    (hW : TBLevel (fun i => ⟪x (c01_P i), w⟫) [[4], [0, 2, 3], [1, 5]]) :
    ∃ c ∈ c01_certs, c.W = [[4], [0, 2, 3], [1, 5]] ∧ TBReal F c01_P w c01_sw c01_R c := by
  have e1 : ⟪x 2, w⟫ = ⟪x 0, w⟫ := hW.1 [0, 2, 3] (by decide) 2 (by decide) 0 (by decide)
  have e2 : ⟪x 3, w⟫ = ⟪x 0, w⟫ := hW.1 [0, 2, 3] (by decide) 3 (by decide) 0 (by decide)
  have T : Tilt2 F 0 3 0 2 3 w :=
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, hA, hB,
      by rw [inner_sub_left, e1]; ring, by rw [inner_sub_left, e2]; ring,
      fun h => ht0 (by rw [h, inner_zero_right])⟩
  have e3 : ⟪x 5, w⟫ = ⟪x 1, w⟫ := hW.1 [1, 5] (by decide) 5 (by decide) 1 (by decide)
  obtain ⟨al, be, hal, hbe, hpv⟩ := T.pair (p := 1) (q := 5) (by decide) (by decide) (by decide) (by decide) e3
  have key := c01_W5_real ⟪(x 2 - x 0), (x 2 - x 0)⟫ ⟪(x 3 - x 0), (x 3 - x 0)⟫ ⟪(x 2 - x 0), (x 3 - x 0)⟫ al be T.EA_pos T.EB_pos T.gram_pos hal hbe
  rcases key with ⟨lA, lB, hqA, hqB, i0, i1, i2, i3⟩ | ⟨lA, lB, hqA, hqB, i0, i1, i2, i3⟩ | ⟨lA, lB, hqA, hqB, i0, i1, i2, i3⟩
  · refine ⟨⟨[[4], [0, 2, 3], [1, 5]], 0, [4, 0, 3, 2, 5, 1]⟩, by decide, rfl, ?_⟩
    refine tbReal_of_tilt2 c01_P c01_sw c01_R _ T (by decide) 1 ht0 (c01_R[0]'(by decide)) (by simp) lA lB hqB.ne'
      ((Tilt2.sign_neg_of_pos_mul hqB T.fAB_neg).trans (by decide))
      ((Tilt2.sign_neg_of_pos_mul hqA T.fBA_neg).trans (by decide)) ?_
    have dA := tb_depth_sub (x 2) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 1 0 (by simp)
    have dB := tb_depth_sub (x 3) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 0 1 (by simp)
    have dP := tb_depth_sub (x 5) (x 1) (x 2 - x 0) (x 3 - x 0) lA lB (-al) be hpv
    refine tb_htie_of_pairs (fun i => ⟪x (c01_P i), w⟫) (fun k => ⟪x (c01_P k), (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫) [[4], [0, 2, 3], [1, 5]] hW [4, 0, 3, 2, 5, 1]
      ([(0, 2), (0, 3), (3, 2), (5, 1)] : List (Fin 6 × Fin 6)) (by decide) ?_
    intro pr hpr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpr
    rcases hpr with rfl | rfl | rfl | rfl
    · show ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, dP, i0]
    · show ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, dP, i1]
    · show ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, dP, i2]
    · show ⟪x 5, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 1, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, dP, i3]
  · refine ⟨⟨[[4], [0, 2, 3], [1, 5]], 1, [4, 0, 3, 2, 5, 1]⟩, by decide, rfl, ?_⟩
    refine tbReal_of_tilt2 c01_P c01_sw c01_R _ T (by decide) 1 ht0 (c01_R[1]'(by decide)) (by simp) lA lB hqB.ne
      ((Tilt2.sign_pos_of_neg_mul hqB T.fAB_neg).trans (by decide))
      ((Tilt2.sign_neg_of_pos_mul hqA T.fBA_neg).trans (by decide)) ?_
    have dA := tb_depth_sub (x 2) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 1 0 (by simp)
    have dB := tb_depth_sub (x 3) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 0 1 (by simp)
    have dP := tb_depth_sub (x 5) (x 1) (x 2 - x 0) (x 3 - x 0) lA lB (-al) be hpv
    refine tb_htie_of_pairs (fun i => ⟪x (c01_P i), w⟫) (fun k => ⟪x (c01_P k), (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫) [[4], [0, 2, 3], [1, 5]] hW [4, 0, 3, 2, 5, 1]
      ([(0, 2), (0, 3), (3, 2), (5, 1)] : List (Fin 6 × Fin 6)) (by decide) ?_
    intro pr hpr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpr
    rcases hpr with rfl | rfl | rfl | rfl
    · show ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, dP, i0]
    · show ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, dP, i1]
    · show ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, dP, i2]
    · show ⟪x 5, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 1, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, dP, i3]
  · refine ⟨⟨[[4], [0, 2, 3], [1, 5]], 1, [4, 3, 0, 2, 5, 1]⟩, by decide, rfl, ?_⟩
    refine tbReal_of_tilt2 c01_P c01_sw c01_R _ T (by decide) 1 ht0 (c01_R[1]'(by decide)) (by simp) lA lB hqB.ne
      ((Tilt2.sign_pos_of_neg_mul hqB T.fAB_neg).trans (by decide))
      ((Tilt2.sign_neg_of_pos_mul hqA T.fBA_neg).trans (by decide)) ?_
    have dA := tb_depth_sub (x 2) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 1 0 (by simp)
    have dB := tb_depth_sub (x 3) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 0 1 (by simp)
    have dP := tb_depth_sub (x 5) (x 1) (x 2 - x 0) (x 3 - x 0) lA lB (-al) be hpv
    refine tb_htie_of_pairs (fun i => ⟪x (c01_P i), w⟫) (fun k => ⟪x (c01_P k), (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫) [[4], [0, 2, 3], [1, 5]] hW [4, 3, 0, 2, 5, 1]
      ([(0, 2), (3, 0), (3, 2), (5, 1)] : List (Fin 6 × Fin 6)) (by decide) ?_
    intro pr hpr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpr
    rcases hpr with rfl | rfl | rfl | rfl
    · show ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, dP, i0]
    · show ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, dP, i1]
    · show ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, dP, i2]
    · show ⟪x 5, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 1, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, dP, i3]

theorem c01_W6_real (EA EB h al be : ℝ) (hEA : 0 < EA) (hEB : 0 < EB) (hD : h ^ 2 < EA * EB) (hal : 0 < al) (hbe : 0 < be) :
    (∃ lA lB : ℝ, 0 < lA ∧ lB < 0 ∧ 0 < al * (lA * EA + lB * h) + (-be) * (lA * h + lB * EB) ∧ 0 < 1 * (lA * EA + lB * h) + 0 * (lA * h + lB * EB) ∧ 0 < 0 * (lA * EA + lB * h) + (-1) * (lA * h + lB * EB) ∧ 0 < 1 * (lA * EA + lB * h) + (-1) * (lA * h + lB * EB)) := by
  have hD' : 0 < EA * EB - h ^ 2 := by linarith
  rcases lt_trichotomy h 0 with hh | hh | hh
  · have hh' : 0 < -h := by linarith
    refine ⟨(EB*(EA-h) - h*(-(EB-h))), (EA*(-(EB-h)) - h*(EA-h)), ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hal hbe, mul_pos hal hD', mul_pos hbe hD', mul_pos hal hEA, mul_pos hal hEB, mul_pos hbe hEA, mul_pos hbe hEB, mul_pos hh' hEA, mul_pos hh' hEB]
  · subst hh
    refine ⟨(EB*1 - 0*(-3)), (EA*(-3) - 0*1), ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hal hbe, mul_pos hal hD', mul_pos hbe hD', mul_pos hal hEA, mul_pos hal hEB, mul_pos hbe hEA, mul_pos hbe hEB]
  · have hh' : 0 < h := hh
    rcases lt_trichotomy EA h with hA | hA | hA
    · rcases lt_trichotomy EB h with hB | hB | hB
      · exfalso; nlinarith [mul_pos hEA hEB]
      · exfalso; subst hB; nlinarith [mul_pos hEA hEB]
      · have hA' : 0 < h - EA := by linarith
        have hB' : 0 < EB - h := by linarith
        refine ⟨(EB*1 - h*(-3)), (EA*(-3) - h*1), ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hal hbe, mul_pos hal hD', mul_pos hbe hD', mul_pos hal hEA, mul_pos hal hEB, mul_pos hbe hEA, mul_pos hbe hEB, mul_pos hh' hEA, mul_pos hh' hEB]
    · subst hA
      have hB' : 0 < EB - EA := by nlinarith [mul_pos hEA hEB]
      refine ⟨(EB*1 - EA*(-3)), (EA*(-3) - EA*1), ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hal hbe, mul_pos hal hD', mul_pos hbe hD', mul_pos hal hEA, mul_pos hal hEB, mul_pos hbe hEA, mul_pos hbe hEB, mul_pos hh' hEA, mul_pos hh' hEB]
    · rcases lt_trichotomy EB h with hB | hB | hB
      · have hA' : 0 < EA - h := by linarith
        have hB' : 0 < h - EB := by linarith
        refine ⟨(EB*1 - h*(-3)), (EA*(-3) - h*1), ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hal hbe, mul_pos hal hD', mul_pos hbe hD', mul_pos hal hEA, mul_pos hal hEB, mul_pos hbe hEA, mul_pos hbe hEB, mul_pos hh' hEA, mul_pos hh' hEB]
      · subst hB
        have hA' : 0 < EA - EB := by linarith
        refine ⟨(EB*1 - EB*(-3)), (EA*(-3) - EB*1), ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hal hbe, mul_pos hal hD', mul_pos hbe hD', mul_pos hal hEA, mul_pos hal hEB, mul_pos hbe hEA, mul_pos hbe hEB, mul_pos hh' hEA, mul_pos hh' hEB]
      · have hA' : 0 < EA - h := by linarith
        have hB' : 0 < EB - h := by linarith
        refine ⟨(EB*1 - h*(-3)), (EA*(-3) - h*1), ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hal hbe, mul_pos hal hD', mul_pos hbe hD', mul_pos hal hEA, mul_pos hal hEB, mul_pos hbe hEA, mul_pos hbe hEB, mul_pos hh' hEA, mul_pos hh' hEB]

theorem c01_W6_leaf {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (w : ℝ³)
    (hA : ⟪F.N 0, w⟫ = 0) (hB : ⟪F.N 3, w⟫ = 0) (ht0 : ⟪F.N 1, w⟫ ≠ 0)
    (hW : TBLevel (fun i => ⟪x (c01_P i), w⟫) [[1, 4], [0, 2, 3], [5]]) :
    ∃ c ∈ c01_certs, c.W = [[1, 4], [0, 2, 3], [5]] ∧ TBReal F c01_P w c01_sw c01_R c := by
  have e1 : ⟪x 2, w⟫ = ⟪x 0, w⟫ := hW.1 [0, 2, 3] (by decide) 2 (by decide) 0 (by decide)
  have e2 : ⟪x 3, w⟫ = ⟪x 0, w⟫ := hW.1 [0, 2, 3] (by decide) 3 (by decide) 0 (by decide)
  have T : Tilt2 F 0 3 0 2 3 w :=
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, hA, hB,
      by rw [inner_sub_left, e1]; ring, by rw [inner_sub_left, e2]; ring,
      fun h => ht0 (by rw [h, inner_zero_right])⟩
  have e3 : ⟪x 4, w⟫ = ⟪x 1, w⟫ := hW.1 [1, 4] (by decide) 4 (by decide) 1 (by decide)
  obtain ⟨al, be, hal, hbe, hpv⟩ := T.pair (p := 1) (q := 4) (by decide) (by decide) (by decide) (by decide) e3
  have key := c01_W6_real ⟪(x 2 - x 0), (x 2 - x 0)⟫ ⟪(x 3 - x 0), (x 3 - x 0)⟫ ⟪(x 2 - x 0), (x 3 - x 0)⟫ al be T.EA_pos T.EB_pos T.gram_pos hal hbe
  rcases key with ⟨lA, lB, hqA, hqB, i0, i1, i2, i3⟩
  · refine ⟨⟨[[1, 4], [0, 2, 3], [5]], 1, [4, 1, 3, 0, 2, 5]⟩, by decide, rfl, ?_⟩
    refine tbReal_of_tilt2 c01_P c01_sw c01_R _ T (by decide) 1 ht0 (c01_R[1]'(by decide)) (by simp) lA lB hqB.ne
      ((Tilt2.sign_pos_of_neg_mul hqB T.fAB_neg).trans (by decide))
      ((Tilt2.sign_neg_of_pos_mul hqA T.fBA_neg).trans (by decide)) ?_
    have dA := tb_depth_sub (x 2) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 1 0 (by simp)
    have dB := tb_depth_sub (x 3) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 0 1 (by simp)
    have dP := tb_depth_sub (x 4) (x 1) (x 2 - x 0) (x 3 - x 0) lA lB (-al) be hpv
    refine tb_htie_of_pairs (fun i => ⟪x (c01_P i), w⟫) (fun k => ⟪x (c01_P k), (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫) [[1, 4], [0, 2, 3], [5]] hW [4, 1, 3, 0, 2, 5]
      ([(4, 1), (0, 2), (3, 0), (3, 2)] : List (Fin 6 × Fin 6)) (by decide) ?_
    intro pr hpr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpr
    rcases hpr with rfl | rfl | rfl | rfl
    · show ⟪x 4, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 1, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, dP, i0]
    · show ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, dP, i1]
    · show ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, dP, i2]
    · show ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, dP, i3]

theorem c01_W7_real (EA EB h : ℝ) (hEA : 0 < EA) (hEB : 0 < EB) (hD : h ^ 2 < EA * EB) :
    (∃ lA lB : ℝ, 0 < lA ∧ 0 < lB ∧ 0 < 1 * (lA * EA + lB * h) + 0 * (lA * h + lB * EB) ∧ 0 < 0 * (lA * EA + lB * h) + 1 * (lA * h + lB * EB) ∧ 0 < (-1) * (lA * EA + lB * h) + 1 * (lA * h + lB * EB)) ∨ (∃ lA lB : ℝ, 0 < lA ∧ lB < 0 ∧ 0 < (-1) * (lA * EA + lB * h) + 0 * (lA * h + lB * EB) ∧ 0 < (-1) * (lA * EA + lB * h) + 1 * (lA * h + lB * EB) ∧ 0 < 0 * (lA * EA + lB * h) + (-1) * (lA * h + lB * EB)) ∨ (∃ lA lB : ℝ, 0 < lA ∧ lB < 0 ∧ 0 < (-1) * (lA * EA + lB * h) + 0 * (lA * h + lB * EB) ∧ 0 < 0 * (lA * EA + lB * h) + (-1) * (lA * h + lB * EB) ∧ 0 < 1 * (lA * EA + lB * h) + (-1) * (lA * h + lB * EB)) := by
  have hD' : 0 < EA * EB - h ^ 2 := by linarith
  rcases lt_trichotomy h 0 with hh | hh | hh
  · have hh' : 0 < -h := by linarith
    refine Or.inl (⟨(EB*1 - h*2), (EA*2 - h*1), ?_, ?_, ?_, ?_, ?_⟩)
    all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hh' hEA, mul_pos hh' hEB]
  · subst hh
    refine Or.inl (⟨(EB*1 - 0*2), (EA*2 - 0*1), ?_, ?_, ?_, ?_, ?_⟩)
    all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB]
  · have hh' : 0 < h := hh
    rcases lt_trichotomy EA h with hA | hA | hA
    · rcases lt_trichotomy EB h with hB | hB | hB
      · exfalso; nlinarith [mul_pos hEA hEB]
      · exfalso; subst hB; nlinarith [mul_pos hEA hEB]
      · have hA' : 0 < h - EA := by linarith
        have hB' : 0 < EB - h := by linarith
        refine Or.inl (⟨(EB*(EA+h) - h*(EB+h)), (EA*(EB+h) - h*(EA+h)), ?_, ?_, ?_, ?_, ?_⟩)
        all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hh' hEA, mul_pos hh' hEB]
    · subst hA
      have hB' : 0 < EB - EA := by nlinarith [mul_pos hEA hEB]
      refine Or.inl (⟨(EB*(EA+EA) - EA*(EB+EA)), (EA*(EB+EA) - EA*(EA+EA)), ?_, ?_, ?_, ?_, ?_⟩)
      all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hh' hEA, mul_pos hh' hEB]
    · rcases lt_trichotomy EB h with hB | hB | hB
      · have hA' : 0 < EA - h := by linarith
        have hB' : 0 < h - EB := by linarith
        refine Or.inr (Or.inl (⟨(EB*(-(EA+h)) - h*(-(EA+EB))), (EA*(-(EA+EB)) - h*(-(EA+h))), ?_, ?_, ?_, ?_, ?_⟩))
        all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hh' hEA, mul_pos hh' hEB]
      · subst hB
        have hA' : 0 < EA - EB := by linarith
        refine Or.inr (Or.inr (⟨(EB*(-2) - EB*(-3)), (EA*(-3) - EB*(-2)), ?_, ?_, ?_, ?_, ?_⟩))
        all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hh' hEA, mul_pos hh' hEB]
      · have hA' : 0 < EA - h := by linarith
        have hB' : 0 < EB - h := by linarith
        refine Or.inl (⟨(EB*(EA+h) - h*(EA+EB)), (EA*(EA+EB) - h*(EA+h)), ?_, ?_, ?_, ?_, ?_⟩)
        all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hh' hEA, mul_pos hh' hEB]

theorem c01_W7_leaf {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (w : ℝ³)
    (hA : ⟪F.N 0, w⟫ = 0) (hB : ⟪F.N 3, w⟫ = 0) (ht0 : ⟪F.N 1, w⟫ ≠ 0)
    (hW : TBLevel (fun i => ⟪x (c01_P i), w⟫) [[5], [1], [0, 2, 3], [4]]) :
    ∃ c ∈ c01_certs, c.W = [[5], [1], [0, 2, 3], [4]] ∧ TBReal F c01_P w c01_sw c01_R c := by
  have e1 : ⟪x 2, w⟫ = ⟪x 0, w⟫ := hW.1 [0, 2, 3] (by decide) 2 (by decide) 0 (by decide)
  have e2 : ⟪x 3, w⟫ = ⟪x 0, w⟫ := hW.1 [0, 2, 3] (by decide) 3 (by decide) 0 (by decide)
  have T : Tilt2 F 0 3 0 2 3 w :=
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, hA, hB,
      by rw [inner_sub_left, e1]; ring, by rw [inner_sub_left, e2]; ring,
      fun h => ht0 (by rw [h, inner_zero_right])⟩
  have key := c01_W7_real ⟪(x 2 - x 0), (x 2 - x 0)⟫ ⟪(x 3 - x 0), (x 3 - x 0)⟫ ⟪(x 2 - x 0), (x 3 - x 0)⟫ T.EA_pos T.EB_pos T.gram_pos
  rcases key with ⟨lA, lB, hqA, hqB, i0, i1, i2⟩ | ⟨lA, lB, hqA, hqB, i0, i1, i2⟩ | ⟨lA, lB, hqA, hqB, i0, i1, i2⟩
  · refine ⟨⟨[[5], [1], [0, 2, 3], [4]], 0, [5, 1, 0, 2, 3, 4]⟩, by decide, rfl, ?_⟩
    refine tbReal_of_tilt2 c01_P c01_sw c01_R _ T (by decide) 1 ht0 (c01_R[0]'(by decide)) (by simp) lA lB hqB.ne'
      ((Tilt2.sign_neg_of_pos_mul hqB T.fAB_neg).trans (by decide))
      ((Tilt2.sign_neg_of_pos_mul hqA T.fBA_neg).trans (by decide)) ?_
    have dA := tb_depth_sub (x 2) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 1 0 (by simp)
    have dB := tb_depth_sub (x 3) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 0 1 (by simp)
    refine tb_htie_of_pairs (fun i => ⟪x (c01_P i), w⟫) (fun k => ⟪x (c01_P k), (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫) [[5], [1], [0, 2, 3], [4]] hW [5, 1, 0, 2, 3, 4]
      ([(0, 2), (0, 3), (2, 3)] : List (Fin 6 × Fin 6)) (by decide) ?_
    intro pr hpr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpr
    rcases hpr with rfl | rfl | rfl
    · show ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i0]
    · show ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i1]
    · show ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i2]
  · refine ⟨⟨[[5], [1], [0, 2, 3], [4]], 1, [5, 1, 2, 3, 0, 4]⟩, by decide, rfl, ?_⟩
    refine tbReal_of_tilt2 c01_P c01_sw c01_R _ T (by decide) 1 ht0 (c01_R[1]'(by decide)) (by simp) lA lB hqB.ne
      ((Tilt2.sign_pos_of_neg_mul hqB T.fAB_neg).trans (by decide))
      ((Tilt2.sign_neg_of_pos_mul hqA T.fBA_neg).trans (by decide)) ?_
    have dA := tb_depth_sub (x 2) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 1 0 (by simp)
    have dB := tb_depth_sub (x 3) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 0 1 (by simp)
    refine tb_htie_of_pairs (fun i => ⟪x (c01_P i), w⟫) (fun k => ⟪x (c01_P k), (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫) [[5], [1], [0, 2, 3], [4]] hW [5, 1, 2, 3, 0, 4]
      ([(2, 0), (2, 3), (3, 0)] : List (Fin 6 × Fin 6)) (by decide) ?_
    intro pr hpr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpr
    rcases hpr with rfl | rfl | rfl
    · show ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i0]
    · show ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i1]
    · show ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i2]
  · refine ⟨⟨[[5], [1], [0, 2, 3], [4]], 1, [5, 1, 3, 2, 0, 4]⟩, by decide, rfl, ?_⟩
    refine tbReal_of_tilt2 c01_P c01_sw c01_R _ T (by decide) 1 ht0 (c01_R[1]'(by decide)) (by simp) lA lB hqB.ne
      ((Tilt2.sign_pos_of_neg_mul hqB T.fAB_neg).trans (by decide))
      ((Tilt2.sign_neg_of_pos_mul hqA T.fBA_neg).trans (by decide)) ?_
    have dA := tb_depth_sub (x 2) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 1 0 (by simp)
    have dB := tb_depth_sub (x 3) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 0 1 (by simp)
    refine tb_htie_of_pairs (fun i => ⟪x (c01_P i), w⟫) (fun k => ⟪x (c01_P k), (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫) [[5], [1], [0, 2, 3], [4]] hW [5, 1, 3, 2, 0, 4]
      ([(2, 0), (3, 0), (3, 2)] : List (Fin 6 × Fin 6)) (by decide) ?_
    intro pr hpr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpr
    rcases hpr with rfl | rfl | rfl
    · show ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i0]
    · show ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i1]
    · show ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i2]

theorem c01_W8_real (EA EB h : ℝ) (hEA : 0 < EA) (hEB : 0 < EB) (hD : h ^ 2 < EA * EB) :
    (∃ lA lB : ℝ, lA < 0 ∧ lB < 0 ∧ 0 < 1 * (lA * EA + lB * h) + 0 * (lA * h + lB * EB) ∧ 0 < 0 * (lA * EA + lB * h) + (-1) * (lA * h + lB * EB) ∧ 0 < 1 * (lA * EA + lB * h) + (-1) * (lA * h + lB * EB)) ∨ (∃ lA lB : ℝ, lA < 0 ∧ lB < 0 ∧ 0 < (-1) * (lA * EA + lB * h) + 0 * (lA * h + lB * EB) ∧ 0 < 0 * (lA * EA + lB * h) + (-1) * (lA * h + lB * EB) ∧ 0 < 1 * (lA * EA + lB * h) + (-1) * (lA * h + lB * EB)) ∨ (∃ lA lB : ℝ, 0 < lA ∧ lB < 0 ∧ 0 < (-1) * (lA * EA + lB * h) + 0 * (lA * h + lB * EB) ∧ 0 < (-1) * (lA * EA + lB * h) + 1 * (lA * h + lB * EB) ∧ 0 < 0 * (lA * EA + lB * h) + (-1) * (lA * h + lB * EB)) ∨ (∃ lA lB : ℝ, 0 < lA ∧ lB < 0 ∧ 0 < (-1) * (lA * EA + lB * h) + 0 * (lA * h + lB * EB) ∧ 0 < 0 * (lA * EA + lB * h) + (-1) * (lA * h + lB * EB) ∧ 0 < 1 * (lA * EA + lB * h) + (-1) * (lA * h + lB * EB)) := by
  have hD' : 0 < EA * EB - h ^ 2 := by linarith
  rcases lt_trichotomy h 0 with hh | hh | hh
  · have hh' : 0 < -h := by linarith
    refine Or.inl (⟨(EB*(-(h)) - h*(-(EA+EB))), (EA*(-(EA+EB)) - h*(-(h))), ?_, ?_, ?_, ?_, ?_⟩)
    all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hh' hEA, mul_pos hh' hEB]
  · subst hh
    refine Or.inr (Or.inl (⟨(EB*(-2) - 0*(-3)), (EA*(-3) - 0*(-2)), ?_, ?_, ?_, ?_, ?_⟩))
    all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB]
  · have hh' : 0 < h := hh
    rcases lt_trichotomy EA h with hA | hA | hA
    · rcases lt_trichotomy EB h with hB | hB | hB
      · exfalso; nlinarith [mul_pos hEA hEB]
      · exfalso; subst hB; nlinarith [mul_pos hEA hEB]
      · have hA' : 0 < h - EA := by linarith
        have hB' : 0 < EB - h := by linarith
        refine Or.inr (Or.inl (⟨(EB*(-(EA+h)) - h*(-(EB+h))), (EA*(-(EB+h)) - h*(-(EA+h))), ?_, ?_, ?_, ?_, ?_⟩))
        all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hh' hEA, mul_pos hh' hEB]
    · subst hA
      have hB' : 0 < EB - EA := by nlinarith [mul_pos hEA hEB]
      refine Or.inr (Or.inl (⟨(EB*(-(EA+EA)) - EA*(-(EB+EA))), (EA*(-(EB+EA)) - EA*(-(EA+EA))), ?_, ?_, ?_, ?_, ?_⟩))
      all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hh' hEA, mul_pos hh' hEB]
    · rcases lt_trichotomy EB h with hB | hB | hB
      · have hA' : 0 < EA - h := by linarith
        have hB' : 0 < h - EB := by linarith
        refine Or.inr (Or.inr (Or.inl (⟨(EB*(-(EA+h)) - h*(-(EA+EB))), (EA*(-(EA+EB)) - h*(-(EA+h))), ?_, ?_, ?_, ?_, ?_⟩)))
        all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hh' hEA, mul_pos hh' hEB]
      · subst hB
        have hA' : 0 < EA - EB := by linarith
        refine Or.inr (Or.inr (Or.inr (⟨(EB*(-2) - EB*(-3)), (EA*(-3) - EB*(-2)), ?_, ?_, ?_, ?_, ?_⟩)))
        all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hh' hEA, mul_pos hh' hEB]
      · have hA' : 0 < EA - h := by linarith
        have hB' : 0 < EB - h := by linarith
        refine Or.inr (Or.inl (⟨(EB*(-(EA+h)) - h*(-(EA+EB))), (EA*(-(EA+EB)) - h*(-(EA+h))), ?_, ?_, ?_, ?_, ?_⟩))
        all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hh' hEA, mul_pos hh' hEB]

theorem c01_W8_leaf {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (w : ℝ³)
    (hA : ⟪F.N 0, w⟫ = 0) (hB : ⟪F.N 3, w⟫ = 0) (ht0 : ⟪F.N 1, w⟫ ≠ 0)
    (hW : TBLevel (fun i => ⟪x (c01_P i), w⟫) [[5], [0, 2, 3], [1], [4]]) :
    ∃ c ∈ c01_certs, c.W = [[5], [0, 2, 3], [1], [4]] ∧ TBReal F c01_P w c01_sw c01_R c := by
  have e1 : ⟪x 2, w⟫ = ⟪x 0, w⟫ := hW.1 [0, 2, 3] (by decide) 2 (by decide) 0 (by decide)
  have e2 : ⟪x 3, w⟫ = ⟪x 0, w⟫ := hW.1 [0, 2, 3] (by decide) 3 (by decide) 0 (by decide)
  have T : Tilt2 F 0 3 0 2 3 w :=
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, hA, hB,
      by rw [inner_sub_left, e1]; ring, by rw [inner_sub_left, e2]; ring,
      fun h => ht0 (by rw [h, inner_zero_right])⟩
  have key := c01_W8_real ⟪(x 2 - x 0), (x 2 - x 0)⟫ ⟪(x 3 - x 0), (x 3 - x 0)⟫ ⟪(x 2 - x 0), (x 3 - x 0)⟫ T.EA_pos T.EB_pos T.gram_pos
  rcases key with ⟨lA, lB, hqA, hqB, i0, i1, i2⟩ | ⟨lA, lB, hqA, hqB, i0, i1, i2⟩ | ⟨lA, lB, hqA, hqB, i0, i1, i2⟩ | ⟨lA, lB, hqA, hqB, i0, i1, i2⟩
  · refine ⟨⟨[[5], [0, 2, 3], [1], [4]], 3, [5, 3, 0, 2, 1, 4]⟩, by decide, rfl, ?_⟩
    refine tbReal_of_tilt2 c01_P c01_sw c01_R _ T (by decide) 1 ht0 (c01_R[3]'(by decide)) (by simp) lA lB hqB.ne
      ((Tilt2.sign_pos_of_neg_mul hqB T.fAB_neg).trans (by decide))
      ((Tilt2.sign_pos_of_neg_mul hqA T.fBA_neg).trans (by decide)) ?_
    have dA := tb_depth_sub (x 2) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 1 0 (by simp)
    have dB := tb_depth_sub (x 3) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 0 1 (by simp)
    refine tb_htie_of_pairs (fun i => ⟪x (c01_P i), w⟫) (fun k => ⟪x (c01_P k), (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫) [[5], [0, 2, 3], [1], [4]] hW [5, 3, 0, 2, 1, 4]
      ([(0, 2), (3, 0), (3, 2)] : List (Fin 6 × Fin 6)) (by decide) ?_
    intro pr hpr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpr
    rcases hpr with rfl | rfl | rfl
    · show ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i0]
    · show ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i1]
    · show ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i2]
  · refine ⟨⟨[[5], [0, 2, 3], [1], [4]], 3, [5, 3, 2, 0, 1, 4]⟩, by decide, rfl, ?_⟩
    refine tbReal_of_tilt2 c01_P c01_sw c01_R _ T (by decide) 1 ht0 (c01_R[3]'(by decide)) (by simp) lA lB hqB.ne
      ((Tilt2.sign_pos_of_neg_mul hqB T.fAB_neg).trans (by decide))
      ((Tilt2.sign_pos_of_neg_mul hqA T.fBA_neg).trans (by decide)) ?_
    have dA := tb_depth_sub (x 2) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 1 0 (by simp)
    have dB := tb_depth_sub (x 3) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 0 1 (by simp)
    refine tb_htie_of_pairs (fun i => ⟪x (c01_P i), w⟫) (fun k => ⟪x (c01_P k), (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫) [[5], [0, 2, 3], [1], [4]] hW [5, 3, 2, 0, 1, 4]
      ([(2, 0), (3, 0), (3, 2)] : List (Fin 6 × Fin 6)) (by decide) ?_
    intro pr hpr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpr
    rcases hpr with rfl | rfl | rfl
    · show ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i0]
    · show ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i1]
    · show ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i2]
  · refine ⟨⟨[[5], [0, 2, 3], [1], [4]], 1, [5, 2, 3, 0, 1, 4]⟩, by decide, rfl, ?_⟩
    refine tbReal_of_tilt2 c01_P c01_sw c01_R _ T (by decide) 1 ht0 (c01_R[1]'(by decide)) (by simp) lA lB hqB.ne
      ((Tilt2.sign_pos_of_neg_mul hqB T.fAB_neg).trans (by decide))
      ((Tilt2.sign_neg_of_pos_mul hqA T.fBA_neg).trans (by decide)) ?_
    have dA := tb_depth_sub (x 2) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 1 0 (by simp)
    have dB := tb_depth_sub (x 3) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 0 1 (by simp)
    refine tb_htie_of_pairs (fun i => ⟪x (c01_P i), w⟫) (fun k => ⟪x (c01_P k), (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫) [[5], [0, 2, 3], [1], [4]] hW [5, 2, 3, 0, 1, 4]
      ([(2, 0), (2, 3), (3, 0)] : List (Fin 6 × Fin 6)) (by decide) ?_
    intro pr hpr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpr
    rcases hpr with rfl | rfl | rfl
    · show ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i0]
    · show ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i1]
    · show ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i2]
  · refine ⟨⟨[[5], [0, 2, 3], [1], [4]], 1, [5, 3, 2, 0, 1, 4]⟩, by decide, rfl, ?_⟩
    refine tbReal_of_tilt2 c01_P c01_sw c01_R _ T (by decide) 1 ht0 (c01_R[1]'(by decide)) (by simp) lA lB hqB.ne
      ((Tilt2.sign_pos_of_neg_mul hqB T.fAB_neg).trans (by decide))
      ((Tilt2.sign_neg_of_pos_mul hqA T.fBA_neg).trans (by decide)) ?_
    have dA := tb_depth_sub (x 2) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 1 0 (by simp)
    have dB := tb_depth_sub (x 3) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 0 1 (by simp)
    refine tb_htie_of_pairs (fun i => ⟪x (c01_P i), w⟫) (fun k => ⟪x (c01_P k), (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫) [[5], [0, 2, 3], [1], [4]] hW [5, 3, 2, 0, 1, 4]
      ([(2, 0), (3, 0), (3, 2)] : List (Fin 6 × Fin 6)) (by decide) ?_
    intro pr hpr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpr
    rcases hpr with rfl | rfl | rfl
    · show ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i0]
    · show ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i1]
    · show ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i2]

theorem c01_W9_real (EA EB h : ℝ) (hEA : 0 < EA) (hEB : 0 < EB) (hD : h ^ 2 < EA * EB) :
    (∃ lA lB : ℝ, lA < 0 ∧ lB < 0 ∧ 0 < 1 * (lA * EA + lB * h) + 0 * (lA * h + lB * EB) ∧ 0 < 0 * (lA * EA + lB * h) + (-1) * (lA * h + lB * EB) ∧ 0 < 1 * (lA * EA + lB * h) + (-1) * (lA * h + lB * EB)) ∨ (∃ lA lB : ℝ, lA < 0 ∧ lB < 0 ∧ 0 < (-1) * (lA * EA + lB * h) + 0 * (lA * h + lB * EB) ∧ 0 < 0 * (lA * EA + lB * h) + (-1) * (lA * h + lB * EB) ∧ 0 < 1 * (lA * EA + lB * h) + (-1) * (lA * h + lB * EB)) ∨ (∃ lA lB : ℝ, 0 < lA ∧ lB < 0 ∧ 0 < (-1) * (lA * EA + lB * h) + 0 * (lA * h + lB * EB) ∧ 0 < (-1) * (lA * EA + lB * h) + 1 * (lA * h + lB * EB) ∧ 0 < 0 * (lA * EA + lB * h) + (-1) * (lA * h + lB * EB)) ∨ (∃ lA lB : ℝ, 0 < lA ∧ lB < 0 ∧ 0 < (-1) * (lA * EA + lB * h) + 0 * (lA * h + lB * EB) ∧ 0 < 0 * (lA * EA + lB * h) + (-1) * (lA * h + lB * EB) ∧ 0 < 1 * (lA * EA + lB * h) + (-1) * (lA * h + lB * EB)) := by
  have hD' : 0 < EA * EB - h ^ 2 := by linarith
  rcases lt_trichotomy h 0 with hh | hh | hh
  · have hh' : 0 < -h := by linarith
    refine Or.inl (⟨(EB*(-(h)) - h*(-(EA+EB))), (EA*(-(EA+EB)) - h*(-(h))), ?_, ?_, ?_, ?_, ?_⟩)
    all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hh' hEA, mul_pos hh' hEB]
  · subst hh
    refine Or.inr (Or.inl (⟨(EB*(-2) - 0*(-3)), (EA*(-3) - 0*(-2)), ?_, ?_, ?_, ?_, ?_⟩))
    all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB]
  · have hh' : 0 < h := hh
    rcases lt_trichotomy EA h with hA | hA | hA
    · rcases lt_trichotomy EB h with hB | hB | hB
      · exfalso; nlinarith [mul_pos hEA hEB]
      · exfalso; subst hB; nlinarith [mul_pos hEA hEB]
      · have hA' : 0 < h - EA := by linarith
        have hB' : 0 < EB - h := by linarith
        refine Or.inr (Or.inl (⟨(EB*(-(EA+h)) - h*(-(EB+h))), (EA*(-(EB+h)) - h*(-(EA+h))), ?_, ?_, ?_, ?_, ?_⟩))
        all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hh' hEA, mul_pos hh' hEB]
    · subst hA
      have hB' : 0 < EB - EA := by nlinarith [mul_pos hEA hEB]
      refine Or.inr (Or.inl (⟨(EB*(-(EA+EA)) - EA*(-(EB+EA))), (EA*(-(EB+EA)) - EA*(-(EA+EA))), ?_, ?_, ?_, ?_, ?_⟩))
      all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hh' hEA, mul_pos hh' hEB]
    · rcases lt_trichotomy EB h with hB | hB | hB
      · have hA' : 0 < EA - h := by linarith
        have hB' : 0 < h - EB := by linarith
        refine Or.inr (Or.inr (Or.inl (⟨(EB*(-(EA+h)) - h*(-(EA+EB))), (EA*(-(EA+EB)) - h*(-(EA+h))), ?_, ?_, ?_, ?_, ?_⟩)))
        all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hh' hEA, mul_pos hh' hEB]
      · subst hB
        have hA' : 0 < EA - EB := by linarith
        refine Or.inr (Or.inr (Or.inr (⟨(EB*(-2) - EB*(-3)), (EA*(-3) - EB*(-2)), ?_, ?_, ?_, ?_, ?_⟩)))
        all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hh' hEA, mul_pos hh' hEB]
      · have hA' : 0 < EA - h := by linarith
        have hB' : 0 < EB - h := by linarith
        refine Or.inr (Or.inl (⟨(EB*(-(EA+h)) - h*(-(EA+EB))), (EA*(-(EA+EB)) - h*(-(EA+h))), ?_, ?_, ?_, ?_, ?_⟩))
        all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hh' hEA, mul_pos hh' hEB]

theorem c01_W9_leaf {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (w : ℝ³)
    (hA : ⟪F.N 0, w⟫ = 0) (hB : ⟪F.N 3, w⟫ = 0) (ht0 : ⟪F.N 1, w⟫ ≠ 0)
    (hW : TBLevel (fun i => ⟪x (c01_P i), w⟫) [[5], [0, 2, 3], [4], [1]]) :
    ∃ c ∈ c01_certs, c.W = [[5], [0, 2, 3], [4], [1]] ∧ TBReal F c01_P w c01_sw c01_R c := by
  have e1 : ⟪x 2, w⟫ = ⟪x 0, w⟫ := hW.1 [0, 2, 3] (by decide) 2 (by decide) 0 (by decide)
  have e2 : ⟪x 3, w⟫ = ⟪x 0, w⟫ := hW.1 [0, 2, 3] (by decide) 3 (by decide) 0 (by decide)
  have T : Tilt2 F 0 3 0 2 3 w :=
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, hA, hB,
      by rw [inner_sub_left, e1]; ring, by rw [inner_sub_left, e2]; ring,
      fun h => ht0 (by rw [h, inner_zero_right])⟩
  have key := c01_W9_real ⟪(x 2 - x 0), (x 2 - x 0)⟫ ⟪(x 3 - x 0), (x 3 - x 0)⟫ ⟪(x 2 - x 0), (x 3 - x 0)⟫ T.EA_pos T.EB_pos T.gram_pos
  rcases key with ⟨lA, lB, hqA, hqB, i0, i1, i2⟩ | ⟨lA, lB, hqA, hqB, i0, i1, i2⟩ | ⟨lA, lB, hqA, hqB, i0, i1, i2⟩ | ⟨lA, lB, hqA, hqB, i0, i1, i2⟩
  · refine ⟨⟨[[5], [0, 2, 3], [4], [1]], 3, [5, 3, 0, 2, 4, 1]⟩, by decide, rfl, ?_⟩
    refine tbReal_of_tilt2 c01_P c01_sw c01_R _ T (by decide) 1 ht0 (c01_R[3]'(by decide)) (by simp) lA lB hqB.ne
      ((Tilt2.sign_pos_of_neg_mul hqB T.fAB_neg).trans (by decide))
      ((Tilt2.sign_pos_of_neg_mul hqA T.fBA_neg).trans (by decide)) ?_
    have dA := tb_depth_sub (x 2) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 1 0 (by simp)
    have dB := tb_depth_sub (x 3) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 0 1 (by simp)
    refine tb_htie_of_pairs (fun i => ⟪x (c01_P i), w⟫) (fun k => ⟪x (c01_P k), (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫) [[5], [0, 2, 3], [4], [1]] hW [5, 3, 0, 2, 4, 1]
      ([(0, 2), (3, 0), (3, 2)] : List (Fin 6 × Fin 6)) (by decide) ?_
    intro pr hpr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpr
    rcases hpr with rfl | rfl | rfl
    · show ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i0]
    · show ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i1]
    · show ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i2]
  · refine ⟨⟨[[5], [0, 2, 3], [4], [1]], 3, [5, 3, 2, 0, 4, 1]⟩, by decide, rfl, ?_⟩
    refine tbReal_of_tilt2 c01_P c01_sw c01_R _ T (by decide) 1 ht0 (c01_R[3]'(by decide)) (by simp) lA lB hqB.ne
      ((Tilt2.sign_pos_of_neg_mul hqB T.fAB_neg).trans (by decide))
      ((Tilt2.sign_pos_of_neg_mul hqA T.fBA_neg).trans (by decide)) ?_
    have dA := tb_depth_sub (x 2) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 1 0 (by simp)
    have dB := tb_depth_sub (x 3) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 0 1 (by simp)
    refine tb_htie_of_pairs (fun i => ⟪x (c01_P i), w⟫) (fun k => ⟪x (c01_P k), (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫) [[5], [0, 2, 3], [4], [1]] hW [5, 3, 2, 0, 4, 1]
      ([(2, 0), (3, 0), (3, 2)] : List (Fin 6 × Fin 6)) (by decide) ?_
    intro pr hpr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpr
    rcases hpr with rfl | rfl | rfl
    · show ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i0]
    · show ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i1]
    · show ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i2]
  · refine ⟨⟨[[5], [0, 2, 3], [4], [1]], 1, [5, 2, 3, 0, 4, 1]⟩, by decide, rfl, ?_⟩
    refine tbReal_of_tilt2 c01_P c01_sw c01_R _ T (by decide) 1 ht0 (c01_R[1]'(by decide)) (by simp) lA lB hqB.ne
      ((Tilt2.sign_pos_of_neg_mul hqB T.fAB_neg).trans (by decide))
      ((Tilt2.sign_neg_of_pos_mul hqA T.fBA_neg).trans (by decide)) ?_
    have dA := tb_depth_sub (x 2) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 1 0 (by simp)
    have dB := tb_depth_sub (x 3) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 0 1 (by simp)
    refine tb_htie_of_pairs (fun i => ⟪x (c01_P i), w⟫) (fun k => ⟪x (c01_P k), (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫) [[5], [0, 2, 3], [4], [1]] hW [5, 2, 3, 0, 4, 1]
      ([(2, 0), (2, 3), (3, 0)] : List (Fin 6 × Fin 6)) (by decide) ?_
    intro pr hpr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpr
    rcases hpr with rfl | rfl | rfl
    · show ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i0]
    · show ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i1]
    · show ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i2]
  · refine ⟨⟨[[5], [0, 2, 3], [4], [1]], 1, [5, 3, 2, 0, 4, 1]⟩, by decide, rfl, ?_⟩
    refine tbReal_of_tilt2 c01_P c01_sw c01_R _ T (by decide) 1 ht0 (c01_R[1]'(by decide)) (by simp) lA lB hqB.ne
      ((Tilt2.sign_pos_of_neg_mul hqB T.fAB_neg).trans (by decide))
      ((Tilt2.sign_neg_of_pos_mul hqA T.fBA_neg).trans (by decide)) ?_
    have dA := tb_depth_sub (x 2) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 1 0 (by simp)
    have dB := tb_depth_sub (x 3) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 0 1 (by simp)
    refine tb_htie_of_pairs (fun i => ⟪x (c01_P i), w⟫) (fun k => ⟪x (c01_P k), (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫) [[5], [0, 2, 3], [4], [1]] hW [5, 3, 2, 0, 4, 1]
      ([(2, 0), (3, 0), (3, 2)] : List (Fin 6 × Fin 6)) (by decide) ?_
    intro pr hpr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpr
    rcases hpr with rfl | rfl | rfl
    · show ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i0]
    · show ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i1]
    · show ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, i2]

theorem c01_W10_real (EA EB h al be : ℝ) (hEA : 0 < EA) (hEB : 0 < EB) (hD : h ^ 2 < EA * EB) (hal : 0 < al) (hbe : 0 < be) :
    (∃ lA lB : ℝ, lA < 0 ∧ lB < 0 ∧ 0 < 1 * (lA * EA + lB * h) + 0 * (lA * h + lB * EB) ∧ 0 < 0 * (lA * EA + lB * h) + (-1) * (lA * h + lB * EB) ∧ 0 < 1 * (lA * EA + lB * h) + (-1) * (lA * h + lB * EB) ∧ 0 < al * (lA * EA + lB * h) + (-be) * (lA * h + lB * EB)) ∨ (∃ lA lB : ℝ, lA < 0 ∧ lB < 0 ∧ 0 < (-1) * (lA * EA + lB * h) + 0 * (lA * h + lB * EB) ∧ 0 < 0 * (lA * EA + lB * h) + (-1) * (lA * h + lB * EB) ∧ 0 < 1 * (lA * EA + lB * h) + (-1) * (lA * h + lB * EB) ∧ 0 < al * (lA * EA + lB * h) + (-be) * (lA * h + lB * EB)) ∨ (∃ lA lB : ℝ, 0 < lA ∧ lB < 0 ∧ 0 < (-1) * (lA * EA + lB * h) + 0 * (lA * h + lB * EB) ∧ 0 < 0 * (lA * EA + lB * h) + (-1) * (lA * h + lB * EB) ∧ 0 < 1 * (lA * EA + lB * h) + (-1) * (lA * h + lB * EB) ∧ 0 < al * (lA * EA + lB * h) + (-be) * (lA * h + lB * EB)) := by
  have hD' : 0 < EA * EB - h ^ 2 := by linarith
  rcases lt_trichotomy h 0 with hh | hh | hh
  · have hh' : 0 < -h := by linarith
    refine Or.inl (⟨(EB*(-(h)) - h*(-(EA+EB))), (EA*(-(EA+EB)) - h*(-(h))), ?_, ?_, ?_, ?_, ?_, ?_⟩)
    all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hal hbe, mul_pos hal hD', mul_pos hbe hD', mul_pos hal hEA, mul_pos hal hEB, mul_pos hbe hEA, mul_pos hbe hEB, mul_pos hh' hEA, mul_pos hh' hEB]
  · subst hh
    refine Or.inr (Or.inl (⟨(EB*(-(be)) - 0*(-(al+be))), (EA*(-(al+be)) - 0*(-(be))), ?_, ?_, ?_, ?_, ?_, ?_⟩))
    all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hal hbe, mul_pos hal hD', mul_pos hbe hD', mul_pos hal hEA, mul_pos hal hEB, mul_pos hbe hEA, mul_pos hbe hEB]
  · have hh' : 0 < h := hh
    rcases lt_trichotomy EA h with hA | hA | hA
    · rcases lt_trichotomy EB h with hB | hB | hB
      · exfalso; nlinarith [mul_pos hEA hEB]
      · exfalso; subst hB; nlinarith [mul_pos hEA hEB]
      · have hA' : 0 < h - EA := by linarith
        have hB' : 0 < EB - h := by linarith
        refine Or.inr (Or.inr (⟨(EB*(-(be*h*EA)) - h*(-(be*h*EA + al*h*EA + be*EB*EA + be*h^2))), (EA*(-(be*h*EA + al*h*EA + be*EB*EA + be*h^2)) - h*(-(be*h*EA))), ?_, ?_, ?_, ?_, ?_, ?_⟩))
        all_goals nlinarith [mul_pos (pow_pos hh' 2) (by positivity : (0:ℝ) < be*EA + al*EA + be*h), mul_pos (pow_pos hEA 2) (by positivity : (0:ℝ) < be*h + al*h + be*EB), mul_pos hD' (by positivity : (0:ℝ) < be*h*EA), mul_pos hD' (by positivity : (0:ℝ) < al*h*EA + be*EB*EA + be*h^2), mul_pos hD' (by positivity : (0:ℝ) < be*h*EA + al*h*EA + be*EB*EA + be*h^2), mul_pos hD' (by positivity : (0:ℝ) < be^2*(EA*EB + h^2 + h*EA))]
    · subst hA
      have hB' : 0 < EB - EA := by nlinarith [mul_pos hEA hEB]
      refine Or.inr (Or.inr (⟨(EB*(-(be*EA*EA)) - EA*(-(be*EA*EA + al*EA*EA + be*EB*EA + be*EA^2))), (EA*(-(be*EA*EA + al*EA*EA + be*EB*EA + be*EA^2)) - EA*(-(be*EA*EA))), ?_, ?_, ?_, ?_, ?_, ?_⟩))
      all_goals nlinarith [mul_pos (pow_pos hh' 2) (by positivity : (0:ℝ) < be*EA + al*EA + be*EA), mul_pos (pow_pos hEA 2) (by positivity : (0:ℝ) < be*EA + al*EA + be*EB), mul_pos hD' (by positivity : (0:ℝ) < be*EA*EA), mul_pos hD' (by positivity : (0:ℝ) < al*EA*EA + be*EB*EA + be*EA^2), mul_pos hD' (by positivity : (0:ℝ) < be*EA*EA + al*EA*EA + be*EB*EA + be*EA^2), mul_pos hD' (by positivity : (0:ℝ) < be^2*(EA*EB + EA^2 + EA*EA))]
    · rcases lt_trichotomy EB h with hB | hB | hB
      · have hA' : 0 < EA - h := by linarith
        have hB' : 0 < h - EB := by linarith
        refine Or.inr (Or.inr (⟨(EB*(-(be)) - h*(-(al+be))), (EA*(-(al+be)) - h*(-(be))), ?_, ?_, ?_, ?_, ?_, ?_⟩))
        all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hal hbe, mul_pos hal hD', mul_pos hbe hD', mul_pos hal hEA, mul_pos hal hEB, mul_pos hbe hEA, mul_pos hbe hEB, mul_pos hh' hEA, mul_pos hh' hEB]
      · subst hB
        have hA' : 0 < EA - EB := by linarith
        refine Or.inr (Or.inr (⟨(EB*(-(be)) - EB*(-(al+be))), (EA*(-(al+be)) - EB*(-(be))), ?_, ?_, ?_, ?_, ?_, ?_⟩))
        all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hal hbe, mul_pos hal hD', mul_pos hbe hD', mul_pos hal hEA, mul_pos hal hEB, mul_pos hbe hEA, mul_pos hbe hEB, mul_pos hh' hEA, mul_pos hh' hEB]
      · have hA' : 0 < EA - h := by linarith
        have hB' : 0 < EB - h := by linarith
        refine Or.inr (Or.inr (⟨(EB*(-(be*h*EA)) - h*(-(be*h*EA + al*h*EA + be*EB*EA + be*h^2))), (EA*(-(be*h*EA + al*h*EA + be*EB*EA + be*h^2)) - h*(-(be*h*EA))), ?_, ?_, ?_, ?_, ?_, ?_⟩))
        all_goals nlinarith [mul_pos (pow_pos hh' 2) (by positivity : (0:ℝ) < be*EA + al*EA + be*h), mul_pos (pow_pos hEA 2) (by positivity : (0:ℝ) < be*h + al*h + be*EB), mul_pos hD' (by positivity : (0:ℝ) < be*h*EA), mul_pos hD' (by positivity : (0:ℝ) < al*h*EA + be*EB*EA + be*h^2), mul_pos hD' (by positivity : (0:ℝ) < be*h*EA + al*h*EA + be*EB*EA + be*h^2), mul_pos hD' (by positivity : (0:ℝ) < be^2*(EA*EB + h^2 + h*EA))]

theorem c01_W10_leaf {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (w : ℝ³)
    (hA : ⟪F.N 0, w⟫ = 0) (hB : ⟪F.N 3, w⟫ = 0) (ht0 : ⟪F.N 1, w⟫ ≠ 0)
    (hW : TBLevel (fun i => ⟪x (c01_P i), w⟫) [[5], [0, 2, 3], [1, 4]]) :
    ∃ c ∈ c01_certs, c.W = [[5], [0, 2, 3], [1, 4]] ∧ TBReal F c01_P w c01_sw c01_R c := by
  have e1 : ⟪x 2, w⟫ = ⟪x 0, w⟫ := hW.1 [0, 2, 3] (by decide) 2 (by decide) 0 (by decide)
  have e2 : ⟪x 3, w⟫ = ⟪x 0, w⟫ := hW.1 [0, 2, 3] (by decide) 3 (by decide) 0 (by decide)
  have T : Tilt2 F 0 3 0 2 3 w :=
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, hA, hB,
      by rw [inner_sub_left, e1]; ring, by rw [inner_sub_left, e2]; ring,
      fun h => ht0 (by rw [h, inner_zero_right])⟩
  have e3 : ⟪x 4, w⟫ = ⟪x 1, w⟫ := hW.1 [1, 4] (by decide) 4 (by decide) 1 (by decide)
  obtain ⟨al, be, hal, hbe, hpv⟩ := T.pair (p := 1) (q := 4) (by decide) (by decide) (by decide) (by decide) e3
  have key := c01_W10_real ⟪(x 2 - x 0), (x 2 - x 0)⟫ ⟪(x 3 - x 0), (x 3 - x 0)⟫ ⟪(x 2 - x 0), (x 3 - x 0)⟫ al be T.EA_pos T.EB_pos T.gram_pos hal hbe
  rcases key with ⟨lA, lB, hqA, hqB, i0, i1, i2, i3⟩ | ⟨lA, lB, hqA, hqB, i0, i1, i2, i3⟩ | ⟨lA, lB, hqA, hqB, i0, i1, i2, i3⟩
  · refine ⟨⟨[[5], [0, 2, 3], [1, 4]], 3, [5, 3, 0, 2, 4, 1]⟩, by decide, rfl, ?_⟩
    refine tbReal_of_tilt2 c01_P c01_sw c01_R _ T (by decide) 1 ht0 (c01_R[3]'(by decide)) (by simp) lA lB hqB.ne
      ((Tilt2.sign_pos_of_neg_mul hqB T.fAB_neg).trans (by decide))
      ((Tilt2.sign_pos_of_neg_mul hqA T.fBA_neg).trans (by decide)) ?_
    have dA := tb_depth_sub (x 2) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 1 0 (by simp)
    have dB := tb_depth_sub (x 3) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 0 1 (by simp)
    have dP := tb_depth_sub (x 4) (x 1) (x 2 - x 0) (x 3 - x 0) lA lB (-al) be hpv
    refine tb_htie_of_pairs (fun i => ⟪x (c01_P i), w⟫) (fun k => ⟪x (c01_P k), (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫) [[5], [0, 2, 3], [1, 4]] hW [5, 3, 0, 2, 4, 1]
      ([(0, 2), (3, 0), (3, 2), (4, 1)] : List (Fin 6 × Fin 6)) (by decide) ?_
    intro pr hpr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpr
    rcases hpr with rfl | rfl | rfl | rfl
    · show ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, dP, i0]
    · show ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, dP, i1]
    · show ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, dP, i2]
    · show ⟪x 4, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 1, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, dP, i3]
  · refine ⟨⟨[[5], [0, 2, 3], [1, 4]], 3, [5, 3, 2, 0, 4, 1]⟩, by decide, rfl, ?_⟩
    refine tbReal_of_tilt2 c01_P c01_sw c01_R _ T (by decide) 1 ht0 (c01_R[3]'(by decide)) (by simp) lA lB hqB.ne
      ((Tilt2.sign_pos_of_neg_mul hqB T.fAB_neg).trans (by decide))
      ((Tilt2.sign_pos_of_neg_mul hqA T.fBA_neg).trans (by decide)) ?_
    have dA := tb_depth_sub (x 2) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 1 0 (by simp)
    have dB := tb_depth_sub (x 3) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 0 1 (by simp)
    have dP := tb_depth_sub (x 4) (x 1) (x 2 - x 0) (x 3 - x 0) lA lB (-al) be hpv
    refine tb_htie_of_pairs (fun i => ⟪x (c01_P i), w⟫) (fun k => ⟪x (c01_P k), (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫) [[5], [0, 2, 3], [1, 4]] hW [5, 3, 2, 0, 4, 1]
      ([(2, 0), (3, 0), (3, 2), (4, 1)] : List (Fin 6 × Fin 6)) (by decide) ?_
    intro pr hpr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpr
    rcases hpr with rfl | rfl | rfl | rfl
    · show ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, dP, i0]
    · show ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, dP, i1]
    · show ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, dP, i2]
    · show ⟪x 4, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 1, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, dP, i3]
  · refine ⟨⟨[[5], [0, 2, 3], [1, 4]], 1, [5, 3, 2, 0, 4, 1]⟩, by decide, rfl, ?_⟩
    refine tbReal_of_tilt2 c01_P c01_sw c01_R _ T (by decide) 1 ht0 (c01_R[1]'(by decide)) (by simp) lA lB hqB.ne
      ((Tilt2.sign_pos_of_neg_mul hqB T.fAB_neg).trans (by decide))
      ((Tilt2.sign_neg_of_pos_mul hqA T.fBA_neg).trans (by decide)) ?_
    have dA := tb_depth_sub (x 2) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 1 0 (by simp)
    have dB := tb_depth_sub (x 3) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 0 1 (by simp)
    have dP := tb_depth_sub (x 4) (x 1) (x 2 - x 0) (x 3 - x 0) lA lB (-al) be hpv
    refine tb_htie_of_pairs (fun i => ⟪x (c01_P i), w⟫) (fun k => ⟪x (c01_P k), (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫) [[5], [0, 2, 3], [1, 4]] hW [5, 3, 2, 0, 4, 1]
      ([(2, 0), (3, 0), (3, 2), (4, 1)] : List (Fin 6 × Fin 6)) (by decide) ?_
    intro pr hpr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpr
    rcases hpr with rfl | rfl | rfl | rfl
    · show ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, dP, i0]
    · show ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, dP, i1]
    · show ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, dP, i2]
    · show ⟪x 4, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 1, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, dP, i3]

theorem c01_W11_real (EA EB h al be : ℝ) (hEA : 0 < EA) (hEB : 0 < EB) (hD : h ^ 2 < EA * EB) (hal : 0 < al) (hbe : 0 < be) :
    (∃ lA lB : ℝ, 0 < lA ∧ 0 < lB ∧ 0 < (-al) * (lA * EA + lB * h) + be * (lA * h + lB * EB) ∧ 0 < 1 * (lA * EA + lB * h) + 0 * (lA * h + lB * EB) ∧ 0 < 0 * (lA * EA + lB * h) + 1 * (lA * h + lB * EB) ∧ 0 < (-1) * (lA * EA + lB * h) + 1 * (lA * h + lB * EB)) ∨ (∃ lA lB : ℝ, 0 < lA ∧ lB < 0 ∧ 0 < al * (lA * EA + lB * h) + (-be) * (lA * h + lB * EB) ∧ 0 < (-1) * (lA * EA + lB * h) + 0 * (lA * h + lB * EB) ∧ 0 < 0 * (lA * EA + lB * h) + (-1) * (lA * h + lB * EB) ∧ 0 < 1 * (lA * EA + lB * h) + (-1) * (lA * h + lB * EB)) := by
  have hD' : 0 < EA * EB - h ^ 2 := by linarith
  rcases lt_trichotomy h 0 with hh | hh | hh
  · have hh' : 0 < -h := by linarith
    refine Or.inl (⟨(EB*(be) - h*(al+be)), (EA*(al+be) - h*(be)), ?_, ?_, ?_, ?_, ?_, ?_⟩)
    all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hal hbe, mul_pos hal hD', mul_pos hbe hD', mul_pos hal hEA, mul_pos hal hEB, mul_pos hbe hEA, mul_pos hbe hEB, mul_pos hh' hEA, mul_pos hh' hEB]
  · subst hh
    refine Or.inl (⟨(EB*(be) - 0*(al+be)), (EA*(al+be) - 0*(be)), ?_, ?_, ?_, ?_, ?_, ?_⟩)
    all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hal hbe, mul_pos hal hD', mul_pos hbe hD', mul_pos hal hEA, mul_pos hal hEB, mul_pos hbe hEA, mul_pos hbe hEB]
  · have hh' : 0 < h := hh
    rcases lt_trichotomy EA h with hA | hA | hA
    · rcases lt_trichotomy EB h with hB | hB | hB
      · exfalso; nlinarith [mul_pos hEA hEB]
      · exfalso; subst hB; nlinarith [mul_pos hEA hEB]
      · have hA' : 0 < h - EA := by linarith
        have hB' : 0 < EB - h := by linarith
        refine Or.inr (⟨(EB*(-(be*h*EA)) - h*(-(be*h*EA + al*h*EA + be*EB*EA + be*h^2))), (EA*(-(be*h*EA + al*h*EA + be*EB*EA + be*h^2)) - h*(-(be*h*EA))), ?_, ?_, ?_, ?_, ?_, ?_⟩)
        all_goals nlinarith [mul_pos (pow_pos hh' 2) (by positivity : (0:ℝ) < be*EA + al*EA + be*h), mul_pos (pow_pos hEA 2) (by positivity : (0:ℝ) < be*h + al*h + be*EB), mul_pos hD' (by positivity : (0:ℝ) < be*h*EA), mul_pos hD' (by positivity : (0:ℝ) < al*h*EA + be*EB*EA + be*h^2), mul_pos hD' (by positivity : (0:ℝ) < be*h*EA + al*h*EA + be*EB*EA + be*h^2), mul_pos hD' (by positivity : (0:ℝ) < be^2*(EA*EB + h^2 + h*EA))]
    · subst hA
      have hB' : 0 < EB - EA := by nlinarith [mul_pos hEA hEB]
      refine Or.inr (⟨(EB*(-(be*EA*EA)) - EA*(-(be*EA*EA + al*EA*EA + be*EB*EA + be*EA^2))), (EA*(-(be*EA*EA + al*EA*EA + be*EB*EA + be*EA^2)) - EA*(-(be*EA*EA))), ?_, ?_, ?_, ?_, ?_, ?_⟩)
      all_goals nlinarith [mul_pos (pow_pos hh' 2) (by positivity : (0:ℝ) < be*EA + al*EA + be*EA), mul_pos (pow_pos hEA 2) (by positivity : (0:ℝ) < be*EA + al*EA + be*EB), mul_pos hD' (by positivity : (0:ℝ) < be*EA*EA), mul_pos hD' (by positivity : (0:ℝ) < al*EA*EA + be*EB*EA + be*EA^2), mul_pos hD' (by positivity : (0:ℝ) < be*EA*EA + al*EA*EA + be*EB*EA + be*EA^2), mul_pos hD' (by positivity : (0:ℝ) < be^2*(EA*EB + EA^2 + EA*EA))]
    · rcases lt_trichotomy EB h with hB | hB | hB
      · have hA' : 0 < EA - h := by linarith
        have hB' : 0 < h - EB := by linarith
        refine Or.inr (⟨(EB*(-(be)) - h*(-(al+be))), (EA*(-(al+be)) - h*(-(be))), ?_, ?_, ?_, ?_, ?_, ?_⟩)
        all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hal hbe, mul_pos hal hD', mul_pos hbe hD', mul_pos hal hEA, mul_pos hal hEB, mul_pos hbe hEA, mul_pos hbe hEB, mul_pos hh' hEA, mul_pos hh' hEB]
      · subst hB
        have hA' : 0 < EA - EB := by linarith
        refine Or.inr (⟨(EB*(-(be)) - EB*(-(al+be))), (EA*(-(al+be)) - EB*(-(be))), ?_, ?_, ?_, ?_, ?_, ?_⟩)
        all_goals nlinarith [mul_pos hEA hEB, mul_pos hD' hEA, mul_pos hD' hEB, mul_pos hal hbe, mul_pos hal hD', mul_pos hbe hD', mul_pos hal hEA, mul_pos hal hEB, mul_pos hbe hEA, mul_pos hbe hEB, mul_pos hh' hEA, mul_pos hh' hEB]
      · have hA' : 0 < EA - h := by linarith
        have hB' : 0 < EB - h := by linarith
        refine Or.inr (⟨(EB*(-(be*h*EA)) - h*(-(be*h*EA + al*h*EA + be*EB*EA + be*h^2))), (EA*(-(be*h*EA + al*h*EA + be*EB*EA + be*h^2)) - h*(-(be*h*EA))), ?_, ?_, ?_, ?_, ?_, ?_⟩)
        all_goals nlinarith [mul_pos (pow_pos hh' 2) (by positivity : (0:ℝ) < be*EA + al*EA + be*h), mul_pos (pow_pos hEA 2) (by positivity : (0:ℝ) < be*h + al*h + be*EB), mul_pos hD' (by positivity : (0:ℝ) < be*h*EA), mul_pos hD' (by positivity : (0:ℝ) < al*h*EA + be*EB*EA + be*h^2), mul_pos hD' (by positivity : (0:ℝ) < be*h*EA + al*h*EA + be*EB*EA + be*h^2), mul_pos hD' (by positivity : (0:ℝ) < be^2*(EA*EB + h^2 + h*EA))]

theorem c01_W11_leaf {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (w : ℝ³)
    (hA : ⟪F.N 0, w⟫ = 0) (hB : ⟪F.N 3, w⟫ = 0) (ht0 : ⟪F.N 1, w⟫ ≠ 0)
    (hW : TBLevel (fun i => ⟪x (c01_P i), w⟫) [[1, 5], [0, 2, 3], [4]]) :
    ∃ c ∈ c01_certs, c.W = [[1, 5], [0, 2, 3], [4]] ∧ TBReal F c01_P w c01_sw c01_R c := by
  have e1 : ⟪x 2, w⟫ = ⟪x 0, w⟫ := hW.1 [0, 2, 3] (by decide) 2 (by decide) 0 (by decide)
  have e2 : ⟪x 3, w⟫ = ⟪x 0, w⟫ := hW.1 [0, 2, 3] (by decide) 3 (by decide) 0 (by decide)
  have T : Tilt2 F 0 3 0 2 3 w :=
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, hA, hB,
      by rw [inner_sub_left, e1]; ring, by rw [inner_sub_left, e2]; ring,
      fun h => ht0 (by rw [h, inner_zero_right])⟩
  have e3 : ⟪x 5, w⟫ = ⟪x 1, w⟫ := hW.1 [1, 5] (by decide) 5 (by decide) 1 (by decide)
  obtain ⟨al, be, hal, hbe, hpv⟩ := T.pair (p := 1) (q := 5) (by decide) (by decide) (by decide) (by decide) e3
  have key := c01_W11_real ⟪(x 2 - x 0), (x 2 - x 0)⟫ ⟪(x 3 - x 0), (x 3 - x 0)⟫ ⟪(x 2 - x 0), (x 3 - x 0)⟫ al be T.EA_pos T.EB_pos T.gram_pos hal hbe
  rcases key with ⟨lA, lB, hqA, hqB, i0, i1, i2, i3⟩ | ⟨lA, lB, hqA, hqB, i0, i1, i2, i3⟩
  · refine ⟨⟨[[1, 5], [0, 2, 3], [4]], 0, [1, 5, 0, 2, 3, 4]⟩, by decide, rfl, ?_⟩
    refine tbReal_of_tilt2 c01_P c01_sw c01_R _ T (by decide) 1 ht0 (c01_R[0]'(by decide)) (by simp) lA lB hqB.ne'
      ((Tilt2.sign_neg_of_pos_mul hqB T.fAB_neg).trans (by decide))
      ((Tilt2.sign_neg_of_pos_mul hqA T.fBA_neg).trans (by decide)) ?_
    have dA := tb_depth_sub (x 2) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 1 0 (by simp)
    have dB := tb_depth_sub (x 3) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 0 1 (by simp)
    have dP := tb_depth_sub (x 5) (x 1) (x 2 - x 0) (x 3 - x 0) lA lB (-al) be hpv
    refine tb_htie_of_pairs (fun i => ⟪x (c01_P i), w⟫) (fun k => ⟪x (c01_P k), (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫) [[1, 5], [0, 2, 3], [4]] hW [1, 5, 0, 2, 3, 4]
      ([(1, 5), (0, 2), (0, 3), (2, 3)] : List (Fin 6 × Fin 6)) (by decide) ?_
    intro pr hpr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpr
    rcases hpr with rfl | rfl | rfl | rfl
    · show ⟪x 1, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 5, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, dP, i0]
    · show ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, dP, i1]
    · show ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, dP, i2]
    · show ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, dP, i3]
  · refine ⟨⟨[[1, 5], [0, 2, 3], [4]], 1, [5, 1, 3, 2, 0, 4]⟩, by decide, rfl, ?_⟩
    refine tbReal_of_tilt2 c01_P c01_sw c01_R _ T (by decide) 1 ht0 (c01_R[1]'(by decide)) (by simp) lA lB hqB.ne
      ((Tilt2.sign_pos_of_neg_mul hqB T.fAB_neg).trans (by decide))
      ((Tilt2.sign_neg_of_pos_mul hqA T.fBA_neg).trans (by decide)) ?_
    have dA := tb_depth_sub (x 2) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 1 0 (by simp)
    have dB := tb_depth_sub (x 3) (x 0) (x 2 - x 0) (x 3 - x 0) lA lB 0 1 (by simp)
    have dP := tb_depth_sub (x 5) (x 1) (x 2 - x 0) (x 3 - x 0) lA lB (-al) be hpv
    refine tb_htie_of_pairs (fun i => ⟪x (c01_P i), w⟫) (fun k => ⟪x (c01_P k), (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫) [[1, 5], [0, 2, 3], [4]] hW [5, 1, 3, 2, 0, 4]
      ([(5, 1), (2, 0), (3, 0), (3, 2)] : List (Fin 6 × Fin 6)) (by decide) ?_
    intro pr hpr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpr
    rcases hpr with rfl | rfl | rfl | rfl
    · show ⟪x 5, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 1, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, dP, i0]
    · show ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, dP, i1]
    · show ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 0, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, dP, i2]
    · show ⟪x 3, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫ < ⟪x 2, (lA • (x 2 - x 0) + lB • (x 3 - x 0))⟫
      linarith [dA, dB, dP, i3]

theorem c01_hreal {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (w : ℝ³)
    (hA : ⟪F.N 0, w⟫ = 0) (hB : ⟪F.N 3, w⟫ = 0) (ht0 : ⟪F.N 1, w⟫ ≠ 0) :
    ∀ W, TBLevel (fun i => ⟪x (c01_P i), w⟫) W → (∃ c ∈ c01_certs, c.W = W) →
      ∃ c ∈ c01_certs, c.W = W ∧ TBReal F c01_P w c01_sw c01_R c := by
  intro W hW ⟨c0, hc0, hc0W⟩
  have hmem : W ∈ c01_Ws := by rw [← hc0W]; exact c01_certs_W c0 hc0
  simp only [c01_Ws, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact c01_W0_leaf F w hA hB ht0 hW
  · exact c01_W1_leaf F w hA hB ht0 hW
  · exact c01_W2_leaf F w hA hB ht0 hW
  · exact c01_W3_leaf F w hA hB ht0 hW
  · exact c01_W4_leaf F w hA hB ht0 hW
  · exact c01_W5_leaf F w hA hB ht0 hW
  · exact c01_W6_leaf F w hA hB ht0 hW
  · exact c01_W7_leaf F w hA hB ht0 hW
  · exact c01_W8_leaf F w hA hB ht0 hW
  · exact c01_W9_leaf F w hA hB ht0 hW
  · exact c01_W10_leaf F w hA hB ht0 hW
  · exact c01_W11_leaf F w hA hB ht0 hW

theorem c01_hvac {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {w : ℝ³} (hw : w ≠ 0)
    (hq : ⟪F.N 3, w⟫ = 0) (ht : ⟪F.N 0, w⟫ = 0) :
    ∀ tr ∈ c01_vacs, ¬ (⟪x (c01_P tr.1), w⟫ = ⟪x (c01_P tr.2.1), w⟫ ∧
      ⟪x (c01_P tr.2.1), w⟫ = ⟪x (c01_P tr.2.2), w⟫) := by
  obtain ⟨q1, q2, q3, q4⟩ := cross_ne_quad F
  intro tr htr
  simp only [c01_vacs, List.mem_cons, List.mem_nil_iff, or_false] at htr
  rcases htr with rfl | rfl | rfl | rfl | rfl
  · rintro ⟨h1, h2⟩
    exact cross_ne_F0 F (tbg_vac F 0 (a := 0) (b := 1) (c := 2) (v := 3) (by decide) (by decide) (by decide) (by decide) hw ht h1 h2)
  · rintro ⟨h1, h2⟩
    exact q1 (tbg_vac F 3 (a := 0) (b := 3) (c := 4) (v := 1) (by decide) (by decide) (by decide) (by decide) hw hq h1 h2)
  · rintro ⟨h1, h2⟩
    exact q2 (tbg_vac F 3 (a := 0) (b := 3) (c := 5) (v := 1) (by decide) (by decide) (by decide) (by decide) hw hq h1 h2)
  · rintro ⟨h1, h2⟩
    exact q3 (tbg_vac F 3 (a := 0) (b := 4) (c := 5) (v := 1) (by decide) (by decide) (by decide) (by decide) hw hq h1 h2)
  · rintro ⟨h1, h2⟩
    exact q4 (tbg_vac F 3 (a := 3) (b := 4) (c := 5) (v := 1) (by decide) (by decide) (by decide) (by decide) hw hq h1 h2)

end Minimality.SVCC.CellsTB
