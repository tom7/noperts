module

public import Minimality.Type24Pieces236
public import Minimality.Type24SAT.K24.CornerOB1

@[expose] public section

/-!
# EP: No-Wall-D_A for circle 236 (Carbon A67 Q67.2)

Formalization of `EPSpec.lean` in module form (Hydrogen Task EP):
- `noWallDA_I`: under `CbarIn` and `OB1`, the dominance pattern `D_A` never holds at `wallI x`.
- `noWallDA_III`: mirror result at `wallIII x`.
- `isRupert_pieceI_wall`, `isRupert_pieceIII_wall`: wall-end corollaries requiring only `hp`.
-/

set_option autoImplicit false
open scoped RealInnerProductSpace
open Finset

namespace Minimality.T24.EP

open Minimality Minimality.H21 Minimality.T24.SAT Minimality.RimCell Minimality.T24.HC Minimality.T24.EG

variable {x : Fin 7 → ℝ³}

private lemma li24_comb_ne_zero (F : S0xFac 9 s0x_S24 x) (c0 c2 c6 : ℝ) (hc0 : c0 ≠ 0) :
    capView x c0 c2 c6 ≠ 0 := by
  intro h0
  have hli := li24 F
  have hzero := Fintype.linearIndependent_iff.1 hli ![c0, c2, c6]
    (by simpa [Fin.sum_univ_three, capView] using h0)
  exact hc0 (by simpa using hzero 0)

private lemma n7_fac_lt_zero (F : S0xFac 9 s0x_S24 x) (v : Fin 7) (hv : v ∉ s0x_S24 7) :
    oblX2 x v + oblX6 x v - 1 < omega3 x * oblX0 x v := by
  have T := M4.type24OfFac F
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have hf73 : 0 = F.f 7 (x 1) + oblX0 x 3 * (F.f 7 (x 0) - F.f 7 (x 1)) +
      oblX2 x 3 * (0 - F.f 7 (x 1)) + oblX6 x 3 * (0 - F.f 7 (x 1)) := by
    have hv3 := T.rep 3
    have hi := congrArg (fun w => ⟪F.N 7, w⟫) (show x 3 - x 1 = oblX0 x 3 • (x 0 - x 1) +
        oblX2 x 3 • (x 2 - x 1) + oblX6 x 3 • (x 6 - x 1) by rw [sub_eq_iff_eq_add, hv3]; abel)
    simp only [inner_add_right, real_inner_smul_right, F.inner_sub,
      F.zero 7 3 (by decide), F.zero 7 2 (by decide), F.zero 7 6 (by decide)] at hi
    linarith
  have e3 : oblX2 x 3 + oblX6 x 3 - 1 = omega3 x * oblX0 x 3 := by
    dsimp [omega3]; field_simp [ha3.ne']
  have h70 : F.f 7 (x 0) - F.f 7 (x 1) = omega3 x * F.f 7 (x 1) := by
    apply mul_left_cancel₀ ha3.ne'; linear_combination -hf73 + F.f 7 (x 1) * e3
  have hf7v : F.f 7 (x v) = F.f 7 (x 1) + oblX0 x v * (F.f 7 (x 0) - F.f 7 (x 1)) +
      oblX2 x v * (0 - F.f 7 (x 1)) + oblX6 x v * (0 - F.f 7 (x 1)) := by
    have hvv := T.rep v
    have hi := congrArg (fun w => ⟪F.N 7, w⟫) (show x v - x 1 = oblX0 x v • (x 0 - x 1) +
        oblX2 x v • (x 2 - x 1) + oblX6 x v • (x 6 - x 1) by rw [sub_eq_iff_eq_add, hvv]; abel)
    simp only [inner_add_right, real_inner_smul_right, F.inner_sub,
      F.zero 7 2 (by decide), F.zero 7 6 (by decide)] at hi
    linarith
  have hneg : F.f 7 (x v) < 0 := F.neg 7 v hv
  have h71 : F.f 7 (x 1) < 0 := F.neg 7 1 (by decide)
  rw [hf7v, h70] at hneg
  have hfac : F.f 7 (x 1) + oblX0 x v * (omega3 x * F.f 7 (x 1)) +
      oblX2 x v * (0 - F.f 7 (x 1)) + oblX6 x v * (0 - F.f 7 (x 1)) =
      (omega3 x * oblX0 x v - (oblX2 x v + oblX6 x v - 1)) * F.f 7 (x 1) := by ring
  rw [hfac] at hneg
  have hpos : 0 < omega3 x * oblX0 x v - (oblX2 x v + oblX6 x v - 1) := by nlinarith
  linarith

/-- No-Wall-D_A, piece I (Carbon A67 Q67.2): under CbarIn and OB1 the dominance pattern D_A
(min(z0, z2) >= max(z5, z6)) never holds at the wall end c_0 = wallI of circle 236. -/
theorem noWallDA_I (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (hob : H24K.SAT.OB1 x) :
    ¬ ∀ p ∈ diagPairs, 0 ≤ ⟪x (cI p.1) - x (cI p.2), wallI x⟫ := by
  intro hDA
  have h52 : ⟪x 5 - x 1, wallI x⟫ ≤ ⟪x 2 - x 1, wallI x⟫ := by
    have h := hDA (2, 1) (by decide)
    have h1 : x (cI 2) - x (cI 1) = (x 2 - x 1) - (x 5 - x 1) := by simp [cI]
    rw [h1, inner_sub_left] at h; linarith
  have h62 : ⟪x 6 - x 1, wallI x⟫ ≤ ⟪x 2 - x 1, wallI x⟫ := by
    have h := hDA (2, 3) (by decide)
    have h1 : x (cI 2) - x (cI 3) = (x 2 - x 1) - (x 6 - x 1) := by simp [cI]
    rw [h1, inner_sub_left] at h; linarith
  have hz2_le : ⟪x 2 - x 1, wallI x⟫ ≤ 0 := by
    obtain ⟨o01, _, o26⟩ := hob
    have hom3 : 0 < omega3 x := hC.1
    have ho20 : ⟪x 2 - x 1, x 0 - x 1⟫ ≤ 0 := by rw [real_inner_comm]; exact o01
    simp only [wallI, capView, inner_add_right, real_inner_smul_right, zero_smul, add_zero]
    nlinarith
  have hz6_le : ⟪x 6 - x 1, wallI x⟫ ≤ 0 := le_trans h62 hz2_le
  have hwall_pos : 0 < ⟪x 0 - x 1, wallI x⟫ + omega3 x * ⟪x 6 - x 1, wallI x⟫ := by
    have hne : wallI x ≠ 0 := li24_comb_ne_zero F 1 0 (omega3 x) one_ne_zero
    have hpos := real_inner_self_pos.2 hne
    have hexp : ⟪wallI x, wallI x⟫ = ⟪x 0 - x 1, wallI x⟫ + omega3 x * ⟪x 6 - x 1, wallI x⟫ := by
      have hw : wallI x = (1 : ℝ) • (x 0 - x 1) + omega3 x • (x 6 - x 1) := by simp [wallI, capView]
      calc ⟪wallI x, wallI x⟫ = ⟪(1 : ℝ) • (x 0 - x 1) + omega3 x • (x 6 - x 1), wallI x⟫ :=
            congrArg (fun w => ⟪w, wallI x⟫) hw
        _ = ⟪x 0 - x 1, wallI x⟫ + omega3 x * ⟪x 6 - x 1, wallI x⟫ := by
          simp [inner_add_left, real_inner_smul_left]
    linarith
  have T := M4.type24OfFac F
  have ha5 : 0 < oblX0 x 5 := T.X0_pos (v := 5) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hz5_exp : ⟪x 5 - x 1, wallI x⟫ =
      oblX0 x 5 * ⟪x 0 - x 1, wallI x⟫ + oblX2 x 5 * ⟪x 2 - x 1, wallI x⟫ +
        oblX6 x 5 * ⟪x 6 - x 1, wallI x⟫ := by
    have h5 := T.rep 5
    rw [show x 5 - x 1 = oblX0 x 5 • (x 0 - x 1) + oblX2 x 5 • (x 2 - x 1) +
        oblX6 x 5 • (x 6 - x 1) by rw [sub_eq_iff_eq_add, h5]; abel]
    simp only [inner_add_left, real_inner_smul_left]
  have hz5_gt : ⟪x 2 - x 1, wallI x⟫ < ⟪x 5 - x 1, wallI x⟫ := by
    rw [hz5_exp]
    rcases le_or_gt (oblX2 x 5) 1 with hb5 | hb5
    · have hom3 : 0 < omega3 x := hC.1
      have hom4 : 0 < omega4 x := hC.2.1
      have hom5 : 0 < omega5 x := hC.2.2.1
      have hD : 0 ≤ Delta24 x := hC.2.2.2
      have hD_eq : Delta24 x = omega3 x * omega4 x * omega5 x - omega3 x - omega4 x - omega5 x - 2 := rfl
      have hom35 : 1 < omega3 x * omega5 x := by nlinarith
      have he5 : oblX0 x 5 + oblX2 x 5 - 1 = omega5 x * oblX6 x 5 := by
        dsimp [omega5]; field_simp [hc5.ne']
      have ha5_ge : omega5 x * oblX6 x 5 ≤ oblX0 x 5 := by linarith
      have hc5_lt : oblX6 x 5 < omega3 x * oblX0 x 5 := by nlinarith
      have h1 : 0 ≤ (oblX2 x 5 - 1) * ⟪x 2 - x 1, wallI x⟫ :=
        mul_nonneg_of_nonpos_of_nonpos (by linarith) hz2_le
      have h2 : oblX6 x 5 * ⟪x 6 - x 1, wallI x⟫ ≥ omega3 x * oblX0 x 5 * ⟪x 6 - x 1, wallI x⟫ := by
        nlinarith
      nlinarith
    · have h75 : oblX2 x 5 + oblX6 x 5 - 1 < omega3 x * oblX0 x 5 := n7_fac_lt_zero F 5 (by decide)
      have h1 : (oblX2 x 5 - 1) * ⟪x 6 - x 1, wallI x⟫ ≤ (oblX2 x 5 - 1) * ⟪x 2 - x 1, wallI x⟫ :=
        mul_le_mul_of_nonneg_left h62 (by linarith)
      have h2 : omega3 x * oblX0 x 5 * ⟪x 6 - x 1, wallI x⟫ ≤
          (oblX2 x 5 + oblX6 x 5 - 1) * ⟪x 6 - x 1, wallI x⟫ := by
        nlinarith
      nlinarith
  linarith

/-- No-Wall-D_A, piece III: D_A (min(z0, z6) >= max(z2, z4)) never holds at c_oo = wallIII. -/
theorem noWallDA_III (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (hob : H24K.SAT.OB1 x) :
    ¬ ∀ p ∈ diagPairs, 0 ≤ ⟪x (cIII p.1) - x (cIII p.2), wallIII x⟫ := by
  intro hDA
  have h26 : ⟪x 2 - x 1, wallIII x⟫ ≤ ⟪x 6 - x 1, wallIII x⟫ := by
    have h := hDA (2, 1) (by decide)
    have h1 : x (cIII 2) - x (cIII 1) = (x 6 - x 1) - (x 2 - x 1) := by simp [cIII]
    rw [h1, inner_sub_left] at h; linarith
  have h46 : ⟪x 4 - x 1, wallIII x⟫ ≤ ⟪x 6 - x 1, wallIII x⟫ := by
    have h := hDA (2, 3) (by decide)
    have h1 : x (cIII 2) - x (cIII 3) = (x 6 - x 1) - (x 4 - x 1) := by simp [cIII]
    rw [h1, inner_sub_left] at h; linarith
  have hz6_le : ⟪x 6 - x 1, wallIII x⟫ ≤ 0 := by
    obtain ⟨_, o06, o26⟩ := hob
    have hom3 : 0 < omega3 x := hC.1
    have ho60 : ⟪x 6 - x 1, x 0 - x 1⟫ ≤ 0 := by rw [real_inner_comm]; exact o06
    have ho62 : ⟪x 6 - x 1, x 2 - x 1⟫ ≤ 0 := by rw [real_inner_comm]; exact o26
    simp only [wallIII, capView, inner_add_right, real_inner_smul_right, zero_smul, add_zero]
    nlinarith
  have hz2_le : ⟪x 2 - x 1, wallIII x⟫ ≤ 0 := le_trans h26 hz6_le
  have hwall_pos : 0 < ⟪x 0 - x 1, wallIII x⟫ + omega3 x * ⟪x 2 - x 1, wallIII x⟫ := by
    have hne : wallIII x ≠ 0 := li24_comb_ne_zero F 1 (omega3 x) 0 one_ne_zero
    have hpos := real_inner_self_pos.2 hne
    have hexp : ⟪wallIII x, wallIII x⟫ = ⟪x 0 - x 1, wallIII x⟫ + omega3 x * ⟪x 2 - x 1, wallIII x⟫ := by
      have hw : wallIII x = (1 : ℝ) • (x 0 - x 1) + omega3 x • (x 2 - x 1) := by simp [wallIII, capView]
      calc ⟪wallIII x, wallIII x⟫ = ⟪(1 : ℝ) • (x 0 - x 1) + omega3 x • (x 2 - x 1), wallIII x⟫ :=
            congrArg (fun w => ⟪w, wallIII x⟫) hw
        _ = ⟪x 0 - x 1, wallIII x⟫ + omega3 x * ⟪x 2 - x 1, wallIII x⟫ := by
          simp [inner_add_left, real_inner_smul_left]
    linarith
  have T := M4.type24OfFac F
  have ha4 : 0 < oblX0 x 4 := T.X0_pos (v := 4) (by decide)
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
  have hz4_exp : ⟪x 4 - x 1, wallIII x⟫ =
      oblX0 x 4 * ⟪x 0 - x 1, wallIII x⟫ + oblX2 x 4 * ⟪x 2 - x 1, wallIII x⟫ +
        oblX6 x 4 * ⟪x 6 - x 1, wallIII x⟫ := by
    have h4 := T.rep 4
    rw [show x 4 - x 1 = oblX0 x 4 • (x 0 - x 1) + oblX2 x 4 • (x 2 - x 1) +
        oblX6 x 4 • (x 6 - x 1) by rw [sub_eq_iff_eq_add, h4]; abel]
    simp only [inner_add_left, real_inner_smul_left]
  have hz4_gt : ⟪x 6 - x 1, wallIII x⟫ < ⟪x 4 - x 1, wallIII x⟫ := by
    rw [hz4_exp]
    rcases le_or_gt (oblX6 x 4) 1 with hc4 | hc4
    · have hom3 : 0 < omega3 x := hC.1
      have hom4 : 0 < omega4 x := hC.2.1
      have hom5 : 0 < omega5 x := hC.2.2.1
      have hD : 0 ≤ Delta24 x := hC.2.2.2
      have hD_eq : Delta24 x = omega3 x * omega4 x * omega5 x - omega3 x - omega4 x - omega5 x - 2 := rfl
      have hom34 : 1 < omega3 x * omega4 x := by nlinarith
      have he4 : oblX0 x 4 + oblX6 x 4 - 1 = omega4 x * oblX2 x 4 := by
        dsimp [omega4]; field_simp [hb4.ne']
      have ha4_ge : omega4 x * oblX2 x 4 ≤ oblX0 x 4 := by linarith
      have hb4_lt : oblX2 x 4 < omega3 x * oblX0 x 4 := by nlinarith
      have h1 : 0 ≤ (oblX6 x 4 - 1) * ⟪x 6 - x 1, wallIII x⟫ :=
        mul_nonneg_of_nonpos_of_nonpos (by linarith) hz6_le
      have h2 : oblX2 x 4 * ⟪x 2 - x 1, wallIII x⟫ ≥ omega3 x * oblX0 x 4 * ⟪x 2 - x 1, wallIII x⟫ := by
        nlinarith
      nlinarith
    · have h74 : oblX2 x 4 + oblX6 x 4 - 1 < omega3 x * oblX0 x 4 := n7_fac_lt_zero F 4 (by decide)
      have h1 : (oblX6 x 4 - 1) * ⟪x 2 - x 1, wallIII x⟫ ≤ (oblX6 x 4 - 1) * ⟪x 6 - x 1, wallIII x⟫ :=
        mul_le_mul_of_nonneg_left h26 (by linarith)
      have h2 : omega3 x * oblX0 x 4 * ⟪x 2 - x 1, wallIII x⟫ ≤
          (oblX2 x 4 + oblX6 x 4 - 1) * ⟪x 2 - x 1, wallIII x⟫ := by
        nlinarith
      nlinarith
  linarith

/-- Piece I with the wall end: only the positive half of the two-end criterion is needed. -/
theorem isRupert_pieceI_wall (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (hob : H24K.SAT.OB1 x)
    (hb : oblX2 x 3 ≤ 1)
    (hp : (∃ p ∈ diagPairs, 0 < ⟪x (cI p.1) - x (cI p.2), endIL x⟫) ∨
      ∃ p ∈ diagPairs, 0 < ⟪x (cI p.1) - x (cI p.2), viewM74 x⟫) :
    IsRupert (univ.image x) := by
  have hn : ∃ p ∈ diagPairs, ⟪x (cI p.1) - x (cI p.2), endIL x⟫ < 0 := by
    have hnot := noWallDA_I F hC hob
    push Not at hnot
    simpa [endIL, hb] using hnot
  exact isRupert_pieceI F hC (h4_of_b3_le F hC hb) (Or.inl hn) hp

/-- Piece III with the wall end. -/
theorem isRupert_pieceIII_wall (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (hob : H24K.SAT.OB1 x)
    (hc : oblX6 x 3 ≤ 1)
    (hp : (∃ p ∈ diagPairs, 0 < ⟪x (cIII p.1) - x (cIII p.2), viewM27 x⟫) ∨
      ∃ p ∈ diagPairs, 0 < ⟪x (cIII p.1) - x (cIII p.2), endIIIR x⟫) :
    IsRupert (univ.image x) := by
  have hn : ∃ p ∈ diagPairs, ⟪x (cIII p.1) - x (cIII p.2), endIIIR x⟫ < 0 := by
    have hnot := noWallDA_III F hC hob
    push Not at hnot
    simpa [endIIIR, hc] using hnot
  exact isRupert_pieceIII F hC (h2_of_c3_le F hC hc) (Or.inr hn) hp

end Minimality.T24.EP
