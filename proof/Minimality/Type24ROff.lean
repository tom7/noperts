module

public import Minimality.Type24Regions
public import Minimality.M4iType24
public import Minimality.M4jType24

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.H24.SAT Minimality.T24.SAT Minimality.T24.RCell
  Minimality.Split Minimality.T24.M4 Minimality.T24.A7 Minimality.T24.A8 Minimality.T24.Sym
  Minimality.T24.Reg Minimality.T24.A17

/-!
# Type 24: S7 `offOB1_closed` on `R_off`

`rOff_closed'` closes `Hole24R` on `ROff` except for the named ties `ROffTie` (`nB = 0`, and `nu346b = 0` with
`nB < 0`, at the edge view `e_b`, or the `pi24` twin).
-/

namespace Minimality.T24.A19

/-- Frame form of `b1245`: `a5 c4 - a4 c5`. -/
theorem frame1245 {x : Fin 7 → ℝ³} (hD : det24 x ≠ 0) :
    oblX0 x 5 * oblX6 x 4 - oblX0 x 4 * oblX6 x 5 = b1245 x / det24 x := by
  have := plucker (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) (x 4 - x 1) (x 5 - x 1)
  unfold oblX0 oblX6 b1245
  unfold det24 at hD ⊢
  rw [eq_div_iff hD]; field_simp
  linear_combination (-1 : ℝ) * this

/-- On `Resid24` off `OB1`, the frame bracket `[1245]` is positive (class `.p.` in both orientations). -/
theorem resid24_b1245 {x : Fin 7 → ℝ³} (h : Resid24 x) (hO : ¬ H24K.SAT.OB1 x) :
    0 < oblX0 x 5 * oblX6 x 4 - oblX0 x 4 * oblX6 x 5 := by
  have hc := chi24_eq x
  have key : (chi24 x < 0 ∧ 0 < b1245 x) ∨ (0 < chi24 x ∧ b1245 x < 0) := by
    rcases h with h | h | h | h
    · exact absurd h hO
    · unfold ZRes24 clsz24 at h
      simp only [sgz, flipz, sg, Bool.not_true, Bool.not_false] at h
      rcases h with ⟨a, -, e, -, -, -⟩ | ⟨a, -, e, -, -, -⟩
      · exact Or.inl ⟨a, e⟩
      · exact Or.inr ⟨a, e⟩
    · unfold cls24 at h
      simp only [sg, Bool.not_true, Bool.not_false] at h
      rcases h with ⟨a, -, e, -, -, -⟩ | ⟨a, -, e, -, -, -⟩
      · exact Or.inl ⟨a, e⟩
      · exact Or.inr ⟨a, e⟩
    · unfold cls24 at h
      simp only [sg, Bool.not_true, Bool.not_false] at h
      rcases h with ⟨a, -, e, -, -, -⟩ | ⟨a, -, e, -, -, -⟩
      · exact Or.inl ⟨a, e⟩
      · exact Or.inr ⟨a, e⟩
  rcases key with ⟨a, e⟩ | ⟨a, e⟩
  · have hD : 0 < det24 x := by linarith
    rw [frame1245 hD.ne']
    exact div_pos e hD
  · have hD : det24 x < 0 := by linarith
    rw [frame1245 hD.ne]
    exact div_pos_of_neg_of_neg e hD

/-- `nB`-twin of `fac3_lin` (private in `M4bType24`). -/
theorem fac3_linB {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    (-F.f 3 (x 1)) * nB x = (F.f 3 (x 2) - F.f 3 (x 1)) * D45 x := by
  have f3_0 : F.f 3 (x 0) = 0 := F.zero 3 0 (by decide)
  have f3_4 : F.f 3 (x 4) = 0 := F.zero 3 4 (by decide)
  have f3_5 : F.f 3 (x 5) = 0 := F.zero 3 5 (by decide)
  have ev4 := fac_eval F 3 4
  have ev5 := fac_eval F 3 5
  rw [f3_4, f3_0] at ev4
  rw [f3_5, f3_0] at ev5
  dsimp [nB, D45]
  linear_combination oblX6 x 4 * ev5 - oblX6 x 5 * ev4

theorem nB_neg_iff {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    nB x < 0 ↔ F.f 3 (x 2) < F.f 3 (x 1) := by
  have h1 : 0 < -F.f 3 (x 1) := by linarith [F.neg 3 1 (by decide)]
  have hD : 0 < D45 x := d45_pos F
  have hlin := fac3_linB F
  constructor
  · intro h
    have : (-F.f 3 (x 1)) * nB x < 0 := mul_neg_of_pos_of_neg h1 h
    rw [hlin] at this
    by_contra hc
    push Not at hc
    nlinarith [mul_nonneg (sub_nonneg.mpr hc) hD.le]
  · intro h
    have : (F.f 3 (x 2) - F.f 3 (x 1)) * D45 x < 0 := mul_neg_of_neg_of_pos (by linarith) hD
    rw [← hlin] at this
    by_contra hc
    push Not at hc
    nlinarith [mul_nonneg h1.le hc]

/-- The ties of the core argument at the edge view `e_b` (with `nC > 0`): `nB = 0`, or `nu346b = 0` with
`nB < 0`. -/
def CoreTie {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  nB x = 0 ∨ (nB x < 0 ∧ F.f 8 (x 1) = F.f 8 (x 2))

/-- The named leftover of `rOff_closed'`: the ties, in `x` (`nC > 0`) or in the `pi24` twin (`nB > 0`). -/
def ROffTie {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  (0 < nC x ∧ CoreTie F) ∨ (0 < nB x ∧ CoreTie (sym24 F))

/-- **Core of S7** (case `nC > 0`): off `OB1`, no lex leaf, brackets in frame form, off the ties. -/
theorem rOff_core {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    (h1234 : oblX0 x 4 * oblX6 x 3 - oblX0 x 3 * oblX6 x 4 < 0)
    (h1356 : 0 < oblX0 x 3 * oblX2 x 5 - oblX0 x 5 * oblX2 x 3)
    (h1456 : 0 < oblX0 x 4 * oblX2 x 5 - oblX0 x 5 * oblX2 x 4)
    (hO : ¬ H24K.SAT.OB1 x) (hU : ¬ LexAny F) (hnC : 0 < nC x) (hT : ¬ CoreTie F) : False := by
  have hnc : F.f 3 (x 1) < F.f 3 (x 6) := (nC_pos_iff F).mp hnC
  have h235 : F.f 6 (x 1) < F.f 6 (x 6) := nu235c_pos F hC h1356 hnC.le
  obtain ⟨hac, hbc⟩ := e16_sym F hC hnc h235 hU
  have hab : 0 < ⟪x 0 - x 1, x 2 - x 1⟫ := by
    by_contra h
    exact hO ⟨not_lt.mp h, hac, hbc⟩
  unfold CoreTie at hT
  push Not at hT
  rcases lt_trichotomy (nB x) 0 with hB | hB | hB
  · have hnb : F.f 3 (x 2) < F.f 3 (x 1) := (nB_neg_iff F).mp hB
    have hne := hT.2 hB
    rcases lt_or_gt_of_ne hne with h346 | h346
    · exact hU (e12_neg6 F hC hnb h346 h1356 h1456 hab hbc)
    · exact e12_A2 F hC hnb h346 hab hbc hU
  · exact hT.1 hB
  · have hnb : F.f 3 (x 1) < F.f 3 (x 2) := (nB_pos_iff F).mp hB
    have h346 : F.f 8 (x 1) < F.f 8 (x 2) := nu346b_pos F hC h1234 hB.le
    have := (e12_sym F hC hnb h346 hU).1
    linarith

theorem ob1_comp_pi24 (x : Fin 7 → ℝ³) : H24K.SAT.OB1 (x ∘ pi24) ↔ H24K.SAT.OB1 x := by
  unfold H24K.SAT.OB1
  simp only [Function.comp_apply, pi24_0, pi24_1, pi24_2, pi24_6, real_inner_comm (x 6 - x 1) (x 2 - x 1)]
  tauto

/-- **S7 (`offOB1_closed`) on `R_off`, off the ties**: `Hole24R` and `ROff` give `False` unless `ROffTie`. -/
theorem rOff_closed' {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hR : Hole24R x F) (hRo : Reg.ROff x)
    (hT : ¬ ROffTie F) : False := by
  obtain ⟨hO, h1234, h1356, h1456, ha⟩ := hRo
  have hC : CbarIn x := hR.1
  have hU : ¬ LexAny F := hR.2.2.2.2.1
  have h1245 := resid24_b1245 hR.2.1 hO
  unfold ROffTie at hT
  push Not at hT
  rcases nBC_pos F ha with hB | hCp
  · by_cases hCn : 0 < nC x
    · exact rOff_core F hC h1234 h1356 h1456 hO hU hCn (hT.1 hCn)
    · -- twin
      have hnC' : 0 < nC (x ∘ pi24) := by rw [nC_comp_pi24]; exact hB
      refine rOff_core (sym24 F) ((cbarIn_comp_pi24 x).2 hC) ?_ ?_ ?_ ?_ ?_ hnC' (hT.2 hB)
      · simp only [oblX0_comp_pi24, oblX6_comp_pi24, pi24_3, pi24_4]
        linarith
      · simp only [oblX0_comp_pi24, oblX2_comp_pi24, pi24_3, pi24_5]
        linarith
      · simp only [oblX0_comp_pi24, oblX2_comp_pi24, pi24_4, pi24_5]
        linarith
      · rwa [ob1_comp_pi24]
      · exact fun h => hU (lexAny_sym F h)
  · exact rOff_core F hC h1234 h1356 h1456 hO hU hCp (hT.1 hCp)

end Minimality.T24.A19
