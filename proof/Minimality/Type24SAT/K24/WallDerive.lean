module

public import Minimality.Type24SAT.K24.CasesWall
public import Minimality.Type24SAT.K24.FinalPpmpzDw
public import Minimality.Type24SAT.K24.FinalPpppzDw
public import Minimality.Type24SAT.K24.FinalMpmpzDw

@[expose] public section

/-!
# Type 24 double wall: `WallHyp` from the geometric wall

The geometric wall of `Par2546.lean`: `hl : x 6 - x 4 = l • (x 5 - x 2)` (`25 ∥ 46`) and the double wall
`hwall : ⟪x 0 - x 5, x 5 - x 2⟫ = 0 ∧ ⟪x 0 - x 4, x 5 - x 2⟫ = 0` (the excluded case of `isRupert_par2546`).
* `wallHyp_of_wall`: `WallHyp F`.  `l ≠ 0` is not an extra input: `l < 0` follows from facet `H`.
* `isRupert_offOB1_{ppmpz,ppppz,mpmpz}_wall`: the three `_Dw` theorems with the geometric wall in place of
  `hW`; the z bracket `hb` follows from `hl` and is dropped.
-/

set_option autoImplicit false
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24K.SAT
open Minimality.T24.SAT (s0x_S24)

variable {x : Fin 7 → ℝ³}

theorem wall_det_tri (v w : ℝ³) : det3 v w (v - w) = 0 := by
  simp [det3, cross, PiLp.inner_apply, Fin.sum_univ_three]; ring

theorem wall_det_tri' (v w : ℝ³) : det3 w v (v - w) = 0 := by
  simp [det3, cross, PiLp.inner_apply, Fin.sum_univ_three]; ring

theorem wall_det_vwv (v w : ℝ³) : det3 v w v = 0 := by
  simp [det3, cross, PiLp.inner_apply, Fin.sum_univ_three]; ring

/-- `l < 0` on the parallel edges, from facet `H`. -/
theorem wall_l_neg (F : S0xFac 9 s0x_S24 x) {l : ℝ} (hl : x 6 - x 4 = l • (x 5 - x 2)) : l < 0 := by
  have IS := F.inner_sub
  have zH2 := F.zero 7 2 (by decide); have zH6 := F.zero 7 6 (by decide)
  have hH5 := F.neg 7 5 (by decide)
  have h1 : ⟪F.N 7, x 6 - x 4⟫ = l * ⟪F.N 7, x 5 - x 2⟫ := by rw [hl, inner_smul_right]
  rw [IS 7 6 4, IS 7 5 2, zH6, zH2] at h1
  have hH4 := F.neg 7 4 (by decide)
  by_contra h; push Not at h
  nlinarith [mul_nonneg h (neg_nonneg.2 hH5.le)]

/-- **The double wall gives `WallHyp`.** -/
theorem wallHyp_of_wall (F : S0xFac 9 s0x_S24 x) {l : ℝ} (hl : x 6 - x 4 = l • (x 5 - x 2))
    (hwall : ⟪x 0 - x 5, x 5 - x 2⟫ = 0 ∧ ⟪x 0 - x 4, x 5 - x 2⟫ = 0) : WallHyp F := by
  have IS := F.inner_sub
  have hlneg := wall_l_neg F hl
  obtain ⟨al, be, -, -, -, hq⟩ := Minimality.T24.Par.par2546_quad F
  set d := x 2 - x 5 with hd
  have e : x 5 - x 2 = -d := by rw [hd]; abel
  have hm : x 6 - x 4 = (-l) • d := by rw [hl, hd]; module
  have hm' : x 4 - x 6 = l • d := by
    have : x 4 - x 6 = -(x 6 - x 4) := by abel
    rw [this, hm]; module
  have hd' : d = (-l)⁻¹ • (x 6 - x 4) := by
    rw [hm, smul_smul, inv_mul_cancel₀ (neg_ne_zero.2 hlneg.ne), one_smul]
  have dinner : ∀ t, ⟪F.N t, x 6 - x 4⟫ = (-l) * ⟪F.N t, d⟫ := by
    intro t; rw [hm, inner_smul_right]
  have zE4 := F.zero 4 4 (by decide); have zE6 := F.zero 4 6 (by decide)
  have zI4 := F.zero 8 4 (by decide); have zI6 := F.zero 8 6 (by decide)
  have zG2 := F.zero 6 2 (by decide); have zG5 := F.zero 6 5 (by decide)
  have dE : ⟪F.N 4, d⟫ = 0 := by
    have h := dinner 4
    rw [IS 4 6 4, zE6, zE4, sub_self] at h
    exact (mul_eq_zero.1 h.symm).resolve_left (neg_ne_zero.2 hlneg.ne)
  have dI : ⟪F.N 8, d⟫ = 0 := by
    have h := dinner 8
    rw [IS 8 6 4, zI6, zI4, sub_self] at h
    exact (mul_eq_zero.1 h.symm).resolve_left (neg_ne_zero.2 hlneg.ne)
  have dG : ⟪F.N 6, x 4 - x 6⟫ = 0 := by
    rw [hm', inner_smul_right, hd, IS, zG2, zG5]; ring
  have w0 : ⟪x 0 - x 5, d⟫ = 0 := by
    have := hwall.1; rw [e, inner_neg_right, neg_eq_zero] at this; exact this
  have w4 : ⟪x 0 - x 4, d⟫ = 0 := by
    have := hwall.2; rw [e, inner_neg_right, neg_eq_zero] at this; exact this
  refine ⟨?_, ?_, ?_, ?_, ?_, w0, ?_⟩
  · exact dE
  · exact dG
  · exact dI
  · rw [hm', det3_smul_right, hd]; rw [show x 2 - x 5 = (x 2 - x 1) - (x 5 - x 1) by abel, wall_det_tri, mul_zero]
  · rw [← hd, hd']
    have h' : det3 (x 4 - x 1) (x 6 - x 1) (x 6 - x 4) = 0 := by
      have : x 6 - x 4 = (x 6 - x 1) - (x 4 - x 1) := by abel
      rw [this]; exact wall_det_tri' _ _
    rw [det3_smul_right, h', mul_zero]
  · -- ⟪d, x 3 - x 5⟫ = 0
    have h5 : ⟪x 5 - x 0, d⟫ = 0 := by
      have : x 5 - x 0 = -(x 0 - x 5) := by abel
      rw [this, inner_neg_left, w0, neg_zero]
    have h4 : ⟪x 4 - x 0, d⟫ = 0 := by
      have : x 4 - x 0 = -(x 0 - x 4) := by abel
      rw [this, inner_neg_left, w4, neg_zero]
    have h3 : x 3 - x 5 = al • (x 5 - x 0) + be • (x 4 - x 0) + (x 0 - x 5) := by
      have : x 3 - x 5 = (x 3 - x 0) + (x 0 - x 5) := by abel
      rw [this, hq]
    rw [real_inner_comm, h3, inner_add_left, inner_add_left, inner_smul_left, inner_smul_left, h5, h4, w0]
    simp

end Minimality.H24K.SAT

namespace Minimality.T24
open Minimality.H24K.SAT

/-- det of the z bracket vanishes on `25 ∥ 46`. -/
theorem wall_hb {x : Fin 7 → ℝ³} {l : ℝ} (hl : x 6 - x 4 = l • (x 5 - x 2)) :
    det3 (x 4 - x 2) (x 5 - x 2) (x 6 - x 2) = 0 := by
  have : x 6 - x 2 = (x 4 - x 2) + l • (x 5 - x 2) := by
    have h : x 6 = x 4 + l • (x 5 - x 2) := by rw [← hl]; abel
    rw [h]; abel
  rw [this, det3_add_right, det3_smul_right, det3_self_right', wall_det_vwv]; ring

/-- **Class {c} off `OB1` on the double wall**: `_Dw` with the geometric wall (`25 ∥ 46` and `z0 = z3 = z4 = z5`). -/
theorem isRupert_offOB1_ppmpz_wall {x : Fin 7 → EuclideanSpace ℝ (Fin 3)}
    (F : S0xFac 9 Minimality.T24.SAT.s0x_S24 x)
    (hcls : (det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) < 0 ∧ 0 < det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1) ∧ 0 < det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1) ∧ det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1) < 0 ∧ 0 < det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1)) ∨
      (0 < det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) ∧ det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1) < 0 ∧ det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1) < 0 ∧ 0 < det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1) ∧ det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1) < 0))
    (hO : ¬ Minimality.H24K.SAT.OB1 x)
    (hP : ¬ (det3 (x 0 - x 4) (x 3 - x 5) (F.N 3) = 0 ∧ det3 (x 0 - x 5) (x 3 - x 4) (F.N 3) = 0))
    {l : ℝ} (hl : x 6 - x 4 = l • (x 5 - x 2))
    (hwall : ⟪x 0 - x 5, x 5 - x 2⟫ = 0 ∧ ⟪x 0 - x 4, x 5 - x 2⟫ = 0) :
    IsRupert (Finset.univ.image x) :=
  isRupert_offOB1_ppmpz_Dw F hcls hO (wall_hb hl) hP (wallHyp_of_wall F hl hwall)

/-- **Class {c} off `OB1` on the double wall**: `_Dw` with the geometric wall (`25 ∥ 46` and `z0 = z3 = z4 = z5`). -/
theorem isRupert_offOB1_ppppz_wall {x : Fin 7 → EuclideanSpace ℝ (Fin 3)}
    (F : S0xFac 9 Minimality.T24.SAT.s0x_S24 x)
    (hcls : (det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) < 0 ∧ 0 < det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1) ∧ 0 < det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1) ∧ 0 < det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1) ∧ 0 < det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1)) ∨
      (0 < det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) ∧ det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1) < 0 ∧ det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1) < 0 ∧ det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1) < 0 ∧ det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1) < 0))
    (hO : ¬ Minimality.H24K.SAT.OB1 x)
    (hP : ¬ (det3 (x 0 - x 4) (x 3 - x 5) (F.N 3) = 0 ∧ det3 (x 0 - x 5) (x 3 - x 4) (F.N 3) = 0))
    {l : ℝ} (hl : x 6 - x 4 = l • (x 5 - x 2))
    (hwall : ⟪x 0 - x 5, x 5 - x 2⟫ = 0 ∧ ⟪x 0 - x 4, x 5 - x 2⟫ = 0) :
    IsRupert (Finset.univ.image x) :=
  isRupert_offOB1_ppppz_Dw F hcls hO (wall_hb hl) hP (wallHyp_of_wall F hl hwall)

/-- **Class {c} off `OB1` on the double wall**: `_Dw` with the geometric wall (`25 ∥ 46` and `z0 = z3 = z4 = z5`). -/
theorem isRupert_offOB1_mpmpz_wall {x : Fin 7 → EuclideanSpace ℝ (Fin 3)}
    (F : S0xFac 9 Minimality.T24.SAT.s0x_S24 x)
    (hcls : (det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) < 0 ∧ det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1) < 0 ∧ 0 < det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1) ∧ det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1) < 0 ∧ 0 < det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1)) ∨
      (0 < det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) ∧ 0 < det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1) ∧ det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1) < 0 ∧ 0 < det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1) ∧ det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1) < 0))
    (hO : ¬ Minimality.H24K.SAT.OB1 x)
    (hP : ¬ (det3 (x 0 - x 4) (x 3 - x 5) (F.N 3) = 0 ∧ det3 (x 0 - x 5) (x 3 - x 4) (F.N 3) = 0))
    {l : ℝ} (hl : x 6 - x 4 = l • (x 5 - x 2))
    (hwall : ⟪x 0 - x 5, x 5 - x 2⟫ = 0 ∧ ⟪x 0 - x 4, x 5 - x 2⟫ = 0) :
    IsRupert (Finset.univ.image x) :=
  isRupert_offOB1_mpmpz_Dw F hcls hO (wall_hb hl) hP (wallHyp_of_wall F hl hwall)

end Minimality.T24

#print axioms Minimality.T24.isRupert_offOB1_ppmpz_wall
#print axioms Minimality.T24.isRupert_offOB1_ppppz_wall
#print axioms Minimality.T24.isRupert_offOB1_mpmpz_wall
