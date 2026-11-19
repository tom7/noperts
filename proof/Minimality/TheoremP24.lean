module

public import Mathlib
public import Minimality.RimCellClosed
public import Minimality.OrthoView
public import Minimality.OrthoView2
public import Minimality.OrthoView3
public import Minimality.OrthoCorner
public import Minimality.QuadCross
public import Minimality.Type24SAT.Facets24
public import Minimality.Type24SAT.Geo.Top

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped RealInnerProductSpace Topology
open Filter Finset
open Minimality Minimality.H21 Minimality.T24.SAT

namespace Minimality.T24.TheoremP

variable {x : Fin 7 → ℝ³}

/-- Whether a vertex of Type 24 is one of the three ends `0, 2, 6` of the obtuse corner at `1`. -/
def isEnd (v : Fin 7) : Bool :=
  v == 0 || v == 2 || v == 6

/-- Number of transitions from non-end to end along a cycle `c : ZMod k → Fin 7`. -/
def countEndTransitions {k : ℕ} [NeZero k] (c : ZMod k → Fin 7) : ℕ :=
  (Finset.univ : Finset (ZMod k)).filter (fun i => !isEnd (c i) && isEnd (c (i + 1))) |>.card

/-- The ends are contiguous along the rim cycle `c` (at most one transition from non-end to end). -/
def isContiguousEnds {k : ℕ} [NeZero k] (c : ZMod k → Fin 7) : Bool :=
  countEndTransitions c ≤ 1

-- ----------------------------------------------------------------------------
-- Derivation of Depth Ordering from Facet Data (Task B)
-- ----------------------------------------------------------------------------

/-- Affine evaluation of facet functional `F.f t` in corner coordinates. -/
theorem s0x_affine_eval (F : S0xFac 9 s0x_S24 x) (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hp : p = x 1)
    (hv0 : v 0 = x 0 - x 1) (hv1 : v 1 = x 2 - x 1) (hv2 : v 2 = x 6 - x 1)
    (t : Fin 9) (i : Fin 7) :
    F.f t (x i) - F.f t (x 1) =
      y i 0 * (F.f t (x 0) - F.f t (x 1)) +
      y i 1 * (F.f t (x 2) - F.f t (x 1)) +
      y i 2 * (F.f t (x 6) - F.f t (x 1)) := by
  have hsub : x i - x 1 = y i 0 • (x 0 - x 1) + y i 1 • (x 2 - x 1) + y i 2 • (x 6 - x 1) := by
    have h1 := hxy i
    rw [hp, Fin.sum_univ_three, hv0, hv1, hv2] at h1
    rw [h1, add_sub_cancel_left]
  have hlin : F.f t (x i) - F.f t (x 1) = ⟪F.N t, x i - x 1⟫ := F.hN t (x i) (x 1)
  rw [hlin, hsub]
  simp only [inner_add_right, inner_smul_right]
  rw [← F.hN t (x 0) (x 1), ← F.hN t (x 2) (x 1), ← F.hN t (x 6) (x 1)]

theorem type24_sigma5_gt_one (F : S0xFac 9 s0x_S24 x) (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hp : p = x 1)
    (hv0 : v 0 = x 0 - x 1) (hv1 : v 1 = x 2 - x 1) (hv2 : v 2 = x 6 - x 1) :
    1 < ∑ e, y 5 e := by
  have he0 := s0x_affine_eval F p v y hxy hp hv0 hv1 hv2 0 5
  have hz00 : F.f 0 (x 0) = 0 := F.zero 0 0 (by decide)
  have hz01 : F.f 0 (x 1) = 0 := F.zero 0 1 (by decide)
  have hz02 : F.f 0 (x 2) = 0 := F.zero 0 2 (by decide)
  have hn06 : F.f 0 (x 6) < 0 := F.neg 0 6 (by decide)
  rw [hz00, hz01, hz02] at he0
  simp only [sub_zero, mul_zero, add_zero, zero_add] at he0
  have hy52_pos : 0 < y 5 2 := by
    by_contra hc
    have hle : y 5 2 ≤ 0 := not_lt.mp hc
    have hge : 0 ≤ y 5 2 * F.f 0 (x 6) := mul_nonneg_of_nonpos_of_nonpos hle hn06.le
    rw [← he0] at hge
    have hn05 : F.f 0 (x 5) < 0 := F.neg 0 5 (by decide)
    linarith
  have he2 := s0x_affine_eval F p v y hxy hp hv0 hv1 hv2 2 5
  have hz20 : F.f 2 (x 0) = 0 := F.zero 2 0 (by decide)
  have hz22 : F.f 2 (x 2) = 0 := F.zero 2 2 (by decide)
  have hz25 : F.f 2 (x 5) = 0 := F.zero 2 5 (by decide)
  have hn21 : F.f 2 (x 1) < 0 := F.neg 2 1 (by decide)
  have hn26 : F.f 2 (x 6) < 0 := F.neg 2 6 (by decide)
  rw [hz20, hz22, hz25] at he2
  rw [Fin.sum_univ_three]
  have heq : (1 - (y 5 0 + y 5 1 + y 5 2)) * F.f 2 (x 1) = - y 5 2 * F.f 2 (x 6) := by
    linear_combination -he2
  have hrhs : 0 < - y 5 2 * F.f 2 (x 6) := by
    have : 0 < - F.f 2 (x 6) := by linarith
    have := mul_pos hy52_pos this
    linarith
  rw [← heq] at hrhs
  have hdiff : 1 - (y 5 0 + y 5 1 + y 5 2) < 0 := by
    by_contra hc
    have hle : 0 ≤ 1 - (y 5 0 + y 5 1 + y 5 2) := not_lt.mp hc
    have hnonpos : (1 - (y 5 0 + y 5 1 + y 5 2)) * F.f 2 (x 1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hle hn21.le
    linarith
  linarith

theorem type24_sigma4_gt_one (F : S0xFac 9 s0x_S24 x) (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hp : p = x 1)
    (hv0 : v 0 = x 0 - x 1) (hv1 : v 1 = x 2 - x 1) (hv2 : v 2 = x 6 - x 1) :
    1 < ∑ e, y 4 e := by
  have he1 := s0x_affine_eval F p v y hxy hp hv0 hv1 hv2 1 4
  have hz10 : F.f 1 (x 0) = 0 := F.zero 1 0 (by decide)
  have hz11 : F.f 1 (x 1) = 0 := F.zero 1 1 (by decide)
  have hz16 : F.f 1 (x 6) = 0 := F.zero 1 6 (by decide)
  have hn12 : F.f 1 (x 2) < 0 := F.neg 1 2 (by decide)
  rw [hz10, hz11, hz16] at he1
  simp only [sub_zero, mul_zero, add_zero, zero_add] at he1
  have hy41_pos : 0 < y 4 1 := by
    by_contra hc
    have hle : y 4 1 ≤ 0 := not_lt.mp hc
    have hge : 0 ≤ y 4 1 * F.f 1 (x 2) := mul_nonneg_of_nonpos_of_nonpos hle hn12.le
    rw [← he1] at hge
    have hn14 : F.f 1 (x 4) < 0 := F.neg 1 4 (by decide)
    linarith
  have he4 := s0x_affine_eval F p v y hxy hp hv0 hv1 hv2 4 4
  have hz40 : F.f 4 (x 0) = 0 := F.zero 4 0 (by decide)
  have hz44 : F.f 4 (x 4) = 0 := F.zero 4 4 (by decide)
  have hz46 : F.f 4 (x 6) = 0 := F.zero 4 6 (by decide)
  have hn41 : F.f 4 (x 1) < 0 := F.neg 4 1 (by decide)
  have hn42 : F.f 4 (x 2) < 0 := F.neg 4 2 (by decide)
  rw [hz40, hz44, hz46] at he4
  rw [Fin.sum_univ_three]
  have heq : (1 - (y 4 0 + y 4 1 + y 4 2)) * F.f 4 (x 1) = - y 4 1 * F.f 4 (x 2) := by
    linear_combination -he4
  have hrhs : 0 < - y 4 1 * F.f 4 (x 2) := by
    have : 0 < - F.f 4 (x 2) := by linarith
    have := mul_pos hy41_pos this
    linarith
  rw [← heq] at hrhs
  have hdiff : 1 - (y 4 0 + y 4 1 + y 4 2) < 0 := by
    by_contra hc
    have hle : 0 ≤ 1 - (y 4 0 + y 4 1 + y 4 2) := not_lt.mp hc
    have hnonpos : (1 - (y 4 0 + y 4 1 + y 4 2)) * F.f 4 (x 1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hle hn41.le
    linarith
  linarith

theorem type24_sigma3_gt_one (F : S0xFac 9 s0x_S24 x) (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hp : p = x 1)
    (hv0 : v 0 = x 0 - x 1) (hv1 : v 1 = x 2 - x 1) (hv2 : v 2 = x 6 - x 1) :
    1 < ∑ e, y 3 e := by
  have he5 := s0x_affine_eval F p v y hxy hp hv0 hv1 hv2 5 3
  have hz51 : F.f 5 (x 1) = 0 := F.zero 5 1 (by decide)
  have hz52 : F.f 5 (x 2) = 0 := F.zero 5 2 (by decide)
  have hz56 : F.f 5 (x 6) = 0 := F.zero 5 6 (by decide)
  have hn50 : F.f 5 (x 0) < 0 := F.neg 5 0 (by decide)
  rw [hz51, hz52, hz56] at he5
  simp only [sub_zero, mul_zero, add_zero] at he5
  have hy30_pos : 0 < y 3 0 := by
    by_contra hc
    have hle : y 3 0 ≤ 0 := not_lt.mp hc
    have hge : 0 ≤ y 3 0 * F.f 5 (x 0) := mul_nonneg_of_nonpos_of_nonpos hle hn50.le
    rw [← he5] at hge
    have hn53 : F.f 5 (x 3) < 0 := F.neg 5 3 (by decide)
    linarith
  have he7 := s0x_affine_eval F p v y hxy hp hv0 hv1 hv2 7 3
  have hz72 : F.f 7 (x 2) = 0 := F.zero 7 2 (by decide)
  have hz73 : F.f 7 (x 3) = 0 := F.zero 7 3 (by decide)
  have hz76 : F.f 7 (x 6) = 0 := F.zero 7 6 (by decide)
  have hn71 : F.f 7 (x 1) < 0 := F.neg 7 1 (by decide)
  have hn70 : F.f 7 (x 0) < 0 := F.neg 7 0 (by decide)
  rw [hz72, hz73, hz76] at he7
  rw [Fin.sum_univ_three]
  have heq : (1 - (y 3 0 + y 3 1 + y 3 2)) * F.f 7 (x 1) = - y 3 0 * F.f 7 (x 0) := by
    linear_combination -he7
  have hrhs : 0 < - y 3 0 * F.f 7 (x 0) := by
    have : 0 < - F.f 7 (x 0) := by linarith
    have := mul_pos hy30_pos this
    linarith
  rw [← heq] at hrhs
  have hdiff : 1 - (y 3 0 + y 3 1 + y 3 2) < 0 := by
    by_contra hc
    have hle : 0 ≤ 1 - (y 3 0 + y 3 1 + y 3 2) := not_lt.mp hc
    have hnonpos : (1 - (y 3 0 + y 3 1 + y 3 2)) * F.f 7 (x 1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hle hn71.le
    linarith
  linarith

theorem type24_sigma_ends (F : S0xFac 9 s0x_S24 x) (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hp : p = x 1)
    (hv0 : v 0 = x 0 - x 1) (hv1 : v 1 = x 2 - x 1) (hv2 : v 2 = x 6 - x 1) :
    (∑ e, y 0 e = 1) ∧ (∑ e, y 2 e = 1) ∧ (∑ e, y 6 e = 1) := by
  -- For 0:
  have he0_0 := s0x_affine_eval F p v y hxy hp hv0 hv1 hv2 0 0
  have hz00 : F.f 0 (x 0) = 0 := F.zero 0 0 (by decide)
  have hz01 : F.f 0 (x 1) = 0 := F.zero 0 1 (by decide)
  have hz02 : F.f 0 (x 2) = 0 := F.zero 0 2 (by decide)
  have hn06 : F.f 0 (x 6) < 0 := F.neg 0 6 (by decide)
  rw [hz00, hz01, hz02] at he0_0
  simp only [sub_zero, mul_zero, add_zero, zero_add] at he0_0
  have hy02_zero : y 0 2 = 0 := by
    have h1 : y 0 2 * F.f 0 (x 6) = 0 := he0_0.symm
    exact (mul_eq_zero.mp h1).resolve_right hn06.ne

  have he1_0 := s0x_affine_eval F p v y hxy hp hv0 hv1 hv2 1 0
  have hz10 : F.f 1 (x 0) = 0 := F.zero 1 0 (by decide)
  have hz11 : F.f 1 (x 1) = 0 := F.zero 1 1 (by decide)
  have hz16 : F.f 1 (x 6) = 0 := F.zero 1 6 (by decide)
  have hn12 : F.f 1 (x 2) < 0 := F.neg 1 2 (by decide)
  rw [hz10, hz11, hz16] at he1_0
  simp only [sub_zero, mul_zero, add_zero, zero_add] at he1_0
  have hy01_zero : y 0 1 = 0 := by
    have h1 : y 0 1 * F.f 1 (x 2) = 0 := he1_0.symm
    exact (mul_eq_zero.mp h1).resolve_right hn12.ne

  have he5_0 := s0x_affine_eval F p v y hxy hp hv0 hv1 hv2 5 0
  have hz51 : F.f 5 (x 1) = 0 := F.zero 5 1 (by decide)
  have hz52 : F.f 5 (x 2) = 0 := F.zero 5 2 (by decide)
  have hz56 : F.f 5 (x 6) = 0 := F.zero 5 6 (by decide)
  have hn50 : F.f 5 (x 0) < 0 := F.neg 5 0 (by decide)
  rw [hz51, hz52, hz56] at he5_0
  simp only [sub_zero, mul_zero, add_zero] at he5_0
  have hy00_one : y 0 0 = 1 := by
    have h1 : (y 0 0 - 1) * F.f 5 (x 0) = 0 := by
      calc (y 0 0 - 1) * F.f 5 (x 0) = y 0 0 * F.f 5 (x 0) - F.f 5 (x 0) := by ring
        _ = 0 := by rw [← he5_0, sub_self]
    have h2 := (mul_eq_zero.mp h1).resolve_right hn50.ne
    linarith
  have hE0 : ∑ e, y 0 e = 1 := by
    rw [Fin.sum_univ_three, hy00_one, hy01_zero, hy02_zero]; ring

  -- For 2:
  have he0_2 := s0x_affine_eval F p v y hxy hp hv0 hv1 hv2 0 2
  rw [hz00, hz01, hz02] at he0_2
  simp only [sub_zero, mul_zero, add_zero, zero_add] at he0_2
  have hy22_zero : y 2 2 = 0 := by
    have h1 : y 2 2 * F.f 0 (x 6) = 0 := he0_2.symm
    exact (mul_eq_zero.mp h1).resolve_right hn06.ne

  have he5_2 := s0x_affine_eval F p v y hxy hp hv0 hv1 hv2 5 2
  rw [hz51, hz52, hz56] at he5_2
  simp only [sub_zero, mul_zero, add_zero] at he5_2
  have hy20_zero : y 2 0 = 0 := by
    have h1 : y 2 0 * F.f 5 (x 0) = 0 := he5_2.symm
    exact (mul_eq_zero.mp h1).resolve_right hn50.ne

  have he1_2 := s0x_affine_eval F p v y hxy hp hv0 hv1 hv2 1 2
  rw [hz10, hz11, hz16] at he1_2
  simp only [sub_zero, mul_zero, add_zero, zero_add] at he1_2
  have hy21_one : y 2 1 = 1 := by
    have h1 : (y 2 1 - 1) * F.f 1 (x 2) = 0 := by
      calc (y 2 1 - 1) * F.f 1 (x 2) = y 2 1 * F.f 1 (x 2) - F.f 1 (x 2) := by ring
        _ = 0 := by rw [← he1_2, sub_self]
    have h2 := (mul_eq_zero.mp h1).resolve_right hn12.ne
    linarith
  have hE2 : ∑ e, y 2 e = 1 := by
    rw [Fin.sum_univ_three, hy20_zero, hy21_one, hy22_zero]; ring

  -- For 6:
  have he1_6 := s0x_affine_eval F p v y hxy hp hv0 hv1 hv2 1 6
  rw [hz10, hz11, hz16] at he1_6
  simp only [sub_zero, mul_zero, add_zero, zero_add] at he1_6
  have hy61_zero : y 6 1 = 0 := by
    have h1 : y 6 1 * F.f 1 (x 2) = 0 := he1_6.symm
    exact (mul_eq_zero.mp h1).resolve_right hn12.ne

  have he5_6 := s0x_affine_eval F p v y hxy hp hv0 hv1 hv2 5 6
  rw [hz51, hz52, hz56] at he5_6
  simp only [sub_zero, mul_zero, add_zero] at he5_6
  have hy60_zero : y 6 0 = 0 := by
    have h1 : y 6 0 * F.f 5 (x 0) = 0 := he5_6.symm
    exact (mul_eq_zero.mp h1).resolve_right hn50.ne

  have he0_6 := s0x_affine_eval F p v y hxy hp hv0 hv1 hv2 0 6
  rw [hz00, hz01, hz02] at he0_6
  simp only [sub_zero, mul_zero, add_zero, zero_add] at he0_6
  have hy62_one : y 6 2 = 1 := by
    have h1 : (y 6 2 - 1) * F.f 0 (x 6) = 0 := by
      calc (y 6 2 - 1) * F.f 0 (x 6) = y 6 2 * F.f 0 (x 6) - F.f 0 (x 6) := by ring
        _ = 0 := by rw [← he0_6, sub_self]
    have h2 := (mul_eq_zero.mp h1).resolve_right hn06.ne
    linarith
  have hE6 : ∑ e, y 6 e = 1 := by
    rw [Fin.sum_univ_three, hy60_zero, hy61_zero, hy62_one]; ring

  exact ⟨hE0, hE2, hE6⟩

/-- **Theorem: σ > 1 for v = 3, 4, 5 and σ = 1 for ends 0, 2, 6.**
Derivation of all edge-coordinate depth sums directly from the facet data of Type 24. -/
theorem type24_sigma_gt_one (F : S0xFac 9 s0x_S24 x) (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hp : p = x 1)
    (hv0 : v 0 = x 0 - x 1) (hv1 : v 1 = x 2 - x 1) (hv2 : v 2 = x 6 - x 1) :
    1 < (∑ e, y 3 e) ∧ 1 < (∑ e, y 4 e) ∧ 1 < (∑ e, y 5 e) ∧
    (∑ e, y 0 e = 1) ∧ (∑ e, y 2 e = 1) ∧ (∑ e, y 6 e = 1) := by
  have h3 := type24_sigma3_gt_one F p v y hxy hp hv0 hv1 hv2
  have h4 := type24_sigma4_gt_one F p v y hxy hp hv0 hv1 hv2
  have h5 := type24_sigma5_gt_one F p v y hxy hp hv0 hv1 hv2
  have ⟨e0, e2, e6⟩ := type24_sigma_ends F p v y hxy hp hv0 hv1 hv2
  exact ⟨h3, h4, h5, e0, e2, e6⟩

/-- Direction from middle end to apex breaks end ties at an obtuse corner. -/
theorem tilt_sign_middle_end (a b apex : ℝ³)
    (hne : b ≠ apex)
    (hobt : ⟪a - apex, b - apex⟫ ≤ 0) :
    0 < ⟪a - b, apex - b⟫ := by
  have heq : ⟪a - b, apex - b⟫ = ⟪b - apex, b - apex⟫ - ⟪a - apex, b - apex⟫ := by
    have h1 : a - b = (a - apex) - (b - apex) := by abel
    have h2 : apex - b = - (b - apex) := by abel
    rw [h1, h2, inner_sub_left, inner_neg_right, inner_neg_right]
    ring
  rw [heq]
  have hpos : 0 < ⟪b - apex, b - apex⟫ := real_inner_self_pos.2 (sub_ne_zero.2 hne)
  linarith

-- ----------------------------------------------------------------------------
-- Canonical Rim Cycles in C (the Orthocentre Silhouette Chamber)
-- ----------------------------------------------------------------------------

/-- Rim 0435 (EVVV): quad diagonal crossing. -/
def c0435 : ZMod 4 → Fin 7 := ![0, 4, 3, 5]
def U0435 : Finset (Fin 9) := {3}
def D0435 : Finset (Fin 9) := {0, 1, 2, 4, 5, 6, 7, 8}

/-- Rim 0234 (EEVV). -/
def c0234 : ZMod 4 → Fin 7 := ![0, 2, 3, 4]
def U0234 : Finset (Fin 9) := {2, 3, 6}
def D0234 : Finset (Fin 9) := {0, 1, 4, 5, 7, 8}

/-- Rim 0235 (EEVV). -/
def c0235 : ZMod 4 → Fin 7 := ![0, 2, 3, 5]
def U0235 : Finset (Fin 9) := {2, 6}
def D0235 : Finset (Fin 9) := {0, 1, 3, 4, 5, 7, 8}

/-- Rim 6043 (EEVV, rotation of 0436). -/
def c6043 : ZMod 4 → Fin 7 := ![6, 0, 4, 3]
def U6043 : Finset (Fin 9) := {4, 8}
def D6043 : Finset (Fin 9) := {0, 1, 2, 3, 5, 6, 7}

/-- Rim 6053 (EEVV, rotation of 0536). -/
def c6053 : ZMod 4 → Fin 7 := ![6, 0, 5, 3]
def U6053 : Finset (Fin 9) := {3, 4, 8}
def D6053 : Finset (Fin 9) := {0, 1, 2, 5, 6, 7}

/-- Rim 6253 (EEVV, rotation of 2536). -/
def c6253 : ZMod 4 → Fin 7 := ![6, 2, 5, 3]
def U6253 : Finset (Fin 9) := {6, 7}
def D6253 : Finset (Fin 9) := {0, 1, 2, 3, 4, 5, 8}

/-- Rim 6234 (EEVV, rotation of 2346). -/
def c6234 : ZMod 4 → Fin 7 := ![6, 2, 3, 4]
def U6234 : Finset (Fin 9) := {7, 8}
def D6234 : Finset (Fin 9) := {0, 1, 2, 3, 4, 5, 6}

/-- Rim 0526 (EEEV). -/
def c0526 : ZMod 4 → Fin 7 := ![0, 5, 2, 6]
def U0526 : Finset (Fin 9) := {3, 4, 6, 7, 8}
def D0526 : Finset (Fin 9) := {0, 1, 2, 5}

/-- Rim 6402 (EEEV, rotation of 0264). -/
def c6402 : ZMod 4 → Fin 7 := ![6, 4, 0, 2]
def U6402 : Finset (Fin 9) := {2, 3, 6, 7, 8}
def D6402 : Finset (Fin 9) := {0, 1, 4, 5}

/-- Rim 2360 (EEEV, rotation of 0236). -/
def c2360 : ZMod 4 → Fin 7 := ![2, 3, 6, 0]
def U2360 : Finset (Fin 9) := {2, 3, 4, 6, 8}
def D2360 : Finset (Fin 9) := {0, 1, 5, 7}

/-- Rim 26053 (5-rim EEEVV, rotation of 05326). -/
def c26053 : ZMod 5 → Fin 7 := ![2, 6, 0, 5, 3]
def U26053 : Finset (Fin 9) := {3, 4, 7, 8}
def D26053 : Finset (Fin 9) := {0, 1, 2, 5, 6}

/-- Rim 26043 (5-rim EEEVV, rotation of 04326). -/
def c26043 : ZMod 5 → Fin 7 := ![2, 6, 0, 4, 3]
def U26043 : Finset (Fin 9) := {4, 7, 8}
def D26043 : Finset (Fin 9) := {0, 1, 2, 3, 5, 6}

/-- Rim 60234 (5-rim EEEVV, rotation of 02346). -/
def c60234 : ZMod 5 → Fin 7 := ![6, 0, 2, 3, 4]
def U60234 : Finset (Fin 9) := {2, 3, 4, 6}
def D60234 : Finset (Fin 9) := {0, 1, 5, 7, 8}

/-- Rim 02635 (5-rim EEEVV). -/
def c02635 : ZMod 5 → Fin 7 := ![0, 2, 6, 3, 5]
def U02635 : Finset (Fin 9) := {2, 6, 7}
def D02635 : Finset (Fin 9) := {0, 1, 3, 4, 5, 8}

/-- Rim 02634 (5-rim EEEVV). -/
def c02634 : ZMod 5 → Fin 7 := ![0, 2, 6, 3, 4]
def U02634 : Finset (Fin 9) := {2, 3, 6, 7}
def D02634 : Finset (Fin 9) := {0, 1, 4, 5, 8}

/-- Rim 60253 (5-rim EEEVV, rotation of 02536). -/
def c60253 : ZMod 5 → Fin 7 := ![6, 0, 2, 5, 3]
def U60253 : Finset (Fin 9) := {2, 3, 4, 8}
def D60253 : Finset (Fin 9) := {0, 1, 5, 6, 7}

/-- Rim 60534 (5-rim EEVVV, rotation of 05346). -/
def c60534 : ZMod 5 → Fin 7 := ![6, 0, 5, 3, 4]
def U60534 : Finset (Fin 9) := {3, 4}
def D60534 : Finset (Fin 9) := {0, 1, 2, 5, 6, 7, 8}

/-- Rim 62534 (5-rim EEVVV, rotation of 25346). -/
def c62534 : ZMod 5 → Fin 7 := ![6, 2, 5, 3, 4]
def U62534 : Finset (Fin 9) := {6, 7, 8}
def D62534 : Finset (Fin 9) := {0, 1, 2, 3, 4, 5}

/-- Rim 02534 (5-rim EEVVV). -/
def c02534 : ZMod 5 → Fin 7 := ![0, 2, 5, 3, 4]
def U02534 : Finset (Fin 9) := {2, 3}
def D02534 : Finset (Fin 9) := {0, 1, 4, 5, 6, 7, 8}

/-- Rim 026435 (6-rim EEEVVV). -/
def c026435 : ZMod 6 → Fin 7 := ![0, 2, 6, 4, 3, 5]
def U026435 : Finset (Fin 9) := {2, 6, 7, 8}
def D026435 : Finset (Fin 9) := {0, 1, 3, 4, 5}

/-- Rim 602534 (6-rim EEEVVV, rotation of 025346). -/
def c602534 : ZMod 6 → Fin 7 := ![6, 0, 2, 5, 3, 4]
def U602534 : Finset (Fin 9) := {2, 3, 4}
def D602534 : Finset (Fin 9) := {0, 1, 5, 6, 7, 8}

/-- Rim 260435 (6-rim EEEVVV, rotation of 043526). -/
def c260435 : ZMod 6 → Fin 7 := ![2, 6, 0, 4, 3, 5]
def U260435 : Finset (Fin 9) := {4, 6, 7, 8}
def D260435 : Finset (Fin 9) := {0, 1, 2, 3, 5}

-- ----------------------------------------------------------------------------
-- S0xCycUD Certificates and Injective Rims (All by kernel decision)
-- ----------------------------------------------------------------------------

theorem cyc0435 : S0xCycUD s0x_S24 c0435 U0435 D0435 := by decide
theorem cyc0234 : S0xCycUD s0x_S24 c0234 U0234 D0234 := by decide
theorem cyc0235 : S0xCycUD s0x_S24 c0235 U0235 D0235 := by decide
theorem cyc6043 : S0xCycUD s0x_S24 c6043 U6043 D6043 := by decide
theorem cyc6053 : S0xCycUD s0x_S24 c6053 U6053 D6053 := by decide
theorem cyc6253 : S0xCycUD s0x_S24 c6253 U6253 D6253 := by decide
theorem cyc6234 : S0xCycUD s0x_S24 c6234 U6234 D6234 := by decide
theorem cyc0526 : S0xCycUD s0x_S24 c0526 U0526 D0526 := by decide
theorem cyc6402 : S0xCycUD s0x_S24 c6402 U6402 D6402 := by decide
theorem cyc2360 : S0xCycUD s0x_S24 c2360 U2360 D2360 := by decide
theorem cyc26053 : S0xCycUD s0x_S24 c26053 U26053 D26053 := by decide
theorem cyc26043 : S0xCycUD s0x_S24 c26043 U26043 D26043 := by decide
theorem cyc60234 : S0xCycUD s0x_S24 c60234 U60234 D60234 := by decide
theorem cyc02635 : S0xCycUD s0x_S24 c02635 U02635 D02635 := by decide
theorem cyc02634 : S0xCycUD s0x_S24 c02634 U02634 D02634 := by decide
theorem cyc60253 : S0xCycUD s0x_S24 c60253 U60253 D60253 := by decide
theorem cyc60534 : S0xCycUD s0x_S24 c60534 U60534 D60534 := by decide
theorem cyc62534 : S0xCycUD s0x_S24 c62534 U62534 D62534 := by decide
theorem cyc02534 : S0xCycUD s0x_S24 c02534 U02534 D02534 := by decide
theorem cyc026435 : S0xCycUD s0x_S24 c026435 U026435 D026435 := by decide
theorem cyc602534 : S0xCycUD s0x_S24 c602534 U602534 D602534 := by decide
theorem cyc260435 : S0xCycUD s0x_S24 c260435 U260435 D260435 := by decide

theorem inj_c0435 : Function.Injective c0435 := by decide
theorem inj_c0234 : Function.Injective c0234 := by decide
theorem inj_c0235 : Function.Injective c0235 := by decide
theorem inj_c6043 : Function.Injective c6043 := by decide
theorem inj_c6053 : Function.Injective c6053 := by decide
theorem inj_c6253 : Function.Injective c6253 := by decide
theorem inj_c6234 : Function.Injective c6234 := by decide
theorem inj_c0526 : Function.Injective c0526 := by decide
theorem inj_c6402 : Function.Injective c6402 := by decide
theorem inj_c2360 : Function.Injective c2360 := by decide
theorem inj_c26053 : Function.Injective c26053 := by decide
theorem inj_c26043 : Function.Injective c26043 := by decide
theorem inj_c60234 : Function.Injective c60234 := by decide
theorem inj_c02635 : Function.Injective c02635 := by decide
theorem inj_c02634 : Function.Injective c02634 := by decide
theorem inj_c60253 : Function.Injective c60253 := by decide
theorem inj_c60534 : Function.Injective c60534 := by decide
theorem inj_c62534 : Function.Injective c62534 := by decide
theorem inj_c02534 : Function.Injective c02534 := by decide
theorem inj_c026435 : Function.Injective c026435 := by decide
theorem inj_c602534 : Function.Injective c602534 := by decide
theorem inj_c260435 : Function.Injective c260435 := by decide

-- ----------------------------------------------------------------------------
-- Reversed Rim Cycles for Lemma S Branching
-- ----------------------------------------------------------------------------

def c60534_rev : ZMod 5 → Fin 7 := ![0, 6, 4, 3, 5]
def c62534_rev : ZMod 5 → Fin 7 := ![2, 6, 4, 3, 5]
def c02534_rev : ZMod 5 → Fin 7 := ![2, 0, 4, 3, 5]

def c026435_rev : ZMod 6 → Fin 7 := ![6, 2, 0, 5, 3, 4]
def c602534_rev : ZMod 6 → Fin 7 := ![2, 0, 6, 4, 3, 5]
def c260435_rev : ZMod 6 → Fin 7 := ![0, 6, 2, 5, 3, 4]

theorem cyc60534_rev : S0xCycUD s0x_S24 c60534_rev U60534 D60534 := by decide
theorem cyc62534_rev : S0xCycUD s0x_S24 c62534_rev U62534 D62534 := by decide
theorem cyc02534_rev : S0xCycUD s0x_S24 c02534_rev U02534 D02534 := by decide

theorem cyc026435_rev : S0xCycUD s0x_S24 c026435_rev U026435 D026435 := by decide
theorem cyc602534_rev : S0xCycUD s0x_S24 c602534_rev U602534 D602534 := by decide
theorem cyc260435_rev : S0xCycUD s0x_S24 c260435_rev U260435 D260435 := by decide

theorem inj_c60534_rev : Function.Injective c60534_rev := by decide
theorem inj_c62534_rev : Function.Injective c62534_rev := by decide
theorem inj_c02534_rev : Function.Injective c02534_rev := by decide

theorem inj_c026435_rev : Function.Injective c026435_rev := by decide
theorem inj_c602534_rev : Function.Injective c602534_rev := by decide
theorem inj_c260435_rev : Function.Injective c260435_rev := by decide

theorem depth_all_cases (a b c : ℝ) :
    a < b ∨ a < c ∨ (b < a ∧ c < a) ∨ a = b ∨ a = c := by
  rcases lt_trichotomy a b with h1 | rfl | h1
  · exact Or.inl h1
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · rcases lt_trichotomy a c with h2 | rfl | h2
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
    · exact Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))

theorem exists_tilt_for_tie (w1 w2 w3 : ℝ³) (d0 : ℝ³)
    (h1 : 0 < ⟪w1, d0⟫) (h2 : 0 < ⟪w2, d0⟫)
    (hw3 : w3 ≠ 0) (hB : 0 ≤ ⟪w3, d0⟫) :
    ∃ d : ℝ³, 0 < ⟪w1, d⟫ ∧ 0 < ⟪w2, d⟫ ∧ 0 < ⟪w3, d⟫ := by
  have e1 : ∀ ε : ℝ, ⟪w1, d0 + ε • w3⟫ = ⟪w1, d0⟫ + ε * ⟪w1, w3⟫ := by
    intro ε; rw [inner_add_right, inner_smul_right]
  have e2 : ∀ ε : ℝ, ⟪w2, d0 + ε • w3⟫ = ⟪w2, d0⟫ + ε * ⟪w2, w3⟫ := by
    intro ε; rw [inner_add_right, inner_smul_right]
  have e3 : ∀ ε : ℝ, ⟪w3, d0 + ε • w3⟫ = ⟪w3, d0⟫ + ε * ⟪w3, w3⟫ := by
    intro ε; rw [inner_add_right, inner_smul_right]
  have ev1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ⟪w1, d0 + ε • w3⟫ := by
    refine (eventually_pos_affine (Or.inl h1)).mono fun ε hε => by
      rw [e1]; exact hε
  have ev2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ⟪w2, d0 + ε • w3⟫ := by
    refine (eventually_pos_affine (Or.inl h2)).mono fun ε hε => by
      rw [e2]; exact hε
  have hpos3 : 0 < ⟪w3, w3⟫ := real_inner_self_pos.2 hw3
  obtain ⟨ε, ⟨hε1, hε2⟩, hε0⟩ := (ev1.and ev2 |>.and self_mem_nhdsWithin).exists
  refine ⟨d0 + ε • w3, hε1, hε2, ?_⟩
  rw [e3]
  have hmul : 0 < ε * ⟪w3, w3⟫ := mul_pos hε0 hpos3
  linarith

-- ----------------------------------------------------------------------------
-- Contiguous Ends Verification
-- ----------------------------------------------------------------------------

theorem cont_c0435 : isContiguousEnds c0435 = true := by decide
theorem cont_c0234 : isContiguousEnds c0234 = true := by decide
theorem cont_c0235 : isContiguousEnds c0235 = true := by decide
theorem cont_c6043 : isContiguousEnds c6043 = true := by decide
theorem cont_c6053 : isContiguousEnds c6053 = true := by decide
theorem cont_c6253 : isContiguousEnds c6253 = true := by decide
theorem cont_c6234 : isContiguousEnds c6234 = true := by decide
theorem cont_c0526 : isContiguousEnds c0526 = true := by decide
theorem cont_c6402 : isContiguousEnds c6402 = true := by decide
theorem cont_c2360 : isContiguousEnds c2360 = true := by decide
theorem cont_c26053 : isContiguousEnds c26053 = true := by decide
theorem cont_c26043 : isContiguousEnds c26043 = true := by decide
theorem cont_c60234 : isContiguousEnds c60234 = true := by decide
theorem cont_c02635 : isContiguousEnds c02635 = true := by decide
theorem cont_c02634 : isContiguousEnds c02634 = true := by decide
theorem cont_c60253 : isContiguousEnds c60253 = true := by decide
theorem cont_c60534 : isContiguousEnds c60534 = true := by decide
theorem cont_c62534 : isContiguousEnds c62534 = true := by decide
theorem cont_c02534 : isContiguousEnds c02534 = true := by decide
theorem cont_c026435 : isContiguousEnds c026435 = true := by decide
theorem cont_c602534 : isContiguousEnds c602534 = true := by decide
theorem cont_c260435 : isContiguousEnds c260435 = true := by decide

-- ----------------------------------------------------------------------------
-- Feasible Cell Enumeration in C
-- ----------------------------------------------------------------------------

/-- The feasible rim cells occurring in the orthocentre silhouette chamber `C`. -/
inductive FeasibleCellC where
  | c0435 : FeasibleCellC
  | c0234 : FeasibleCellC
  | c0235 : FeasibleCellC
  | c6043 : FeasibleCellC
  | c6053 : FeasibleCellC
  | c6253 : FeasibleCellC
  | c6234 : FeasibleCellC
  | c0526 : FeasibleCellC
  | c6402 : FeasibleCellC
  | c2360 : FeasibleCellC
  | c26053 : FeasibleCellC
  | c26043 : FeasibleCellC
  | c60234 : FeasibleCellC
  | c02635 : FeasibleCellC
  | c02634 : FeasibleCellC
  | c60253 : FeasibleCellC
  | c60534 : FeasibleCellC
  | c62534 : FeasibleCellC
  | c02534 : FeasibleCellC
  | c026435 : FeasibleCellC
  | c602534 : FeasibleCellC
  | c260435 : FeasibleCellC

/-- A view `u` lies in candidate cell `c`. -/
def InFeasibleCell (F : S0xFac 9 s0x_S24 x) (u : ℝ³) : FeasibleCellC → Prop
  | FeasibleCellC.c0435 => CellAt F U0435 D0435 u
  | FeasibleCellC.c0234 => CellAt F U0234 D0234 u
  | FeasibleCellC.c0235 => CellAt F U0235 D0235 u
  | FeasibleCellC.c6043 => CellAt F U6043 D6043 u
  | FeasibleCellC.c6053 => CellAt F U6053 D6053 u
  | FeasibleCellC.c6253 => CellAt F U6253 D6253 u
  | FeasibleCellC.c6234 => CellAt F U6234 D6234 u
  | FeasibleCellC.c0526 => CellAt F U0526 D0526 u
  | FeasibleCellC.c6402 => CellAt F U6402 D6402 u
  | FeasibleCellC.c2360 => CellAt F U2360 D2360 u
  | FeasibleCellC.c26053 => CellAt F U26053 D26053 u
  | FeasibleCellC.c26043 => CellAt F U26043 D26043 u
  | FeasibleCellC.c60234 => CellAt F U60234 D60234 u
  | FeasibleCellC.c02635 => CellAt F U02635 D02635 u
  | FeasibleCellC.c02634 => CellAt F U02634 D02634 u
  | FeasibleCellC.c60253 => CellAt F U60253 D60253 u
  | FeasibleCellC.c60534 => CellAt F U60534 D60534 u
  | FeasibleCellC.c62534 => CellAt F U62534 D62534 u
  | FeasibleCellC.c02534 => CellAt F U02534 D02534 u
  | FeasibleCellC.c026435 => CellAt F U026435 D026435 u
  | FeasibleCellC.c602534 => CellAt F U602534 D602534 u
  | FeasibleCellC.c260435 => CellAt F U260435 D260435 u

-- ----------------------------------------------------------------------------
-- The Dispatches: Per-Cell Leaves of Theorem P
-- ----------------------------------------------------------------------------

/-- Theorem P dispatch for `c0435` (EVVV / QuadCross): tilt discharged via Lemma S branching. -/
theorem isRupert_of_c0435 (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hu : CellAt F U0435 D0435 u) (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hv : ∀ e, ⟪v e, u⟫ = 1)
    (hE0 : (∑ e, y 0 e) = 1) (hV4 : 1 < ∑ e, y 4 e) (hV5 : 1 < ∑ e, y 5 e) :
    IsRupert (univ.image x) := by
  have D := depth_orthocentre x p v y hxy u hv
  have key : ∀ i j, ⟪u, x (c0435 i)⟫ - ⟪u, x (c0435 j)⟫ = (∑ e, y (c0435 i) e) - ∑ e, y (c0435 j) e := by
    intro i j; rw [← D, inner_sub_left, real_inner_comm u (x (c0435 i)),
      real_inner_comm u (x (c0435 j))]
  obtain ⟨s, t, hs, hs1, ht, ht1, hX⟩ := type24_quad_cross x F
  have h01 : (∑ e, y (c0435 0) e) < ∑ e, y (c0435 1) e := by
    change (∑ e, y 0 e) < ∑ e, y 4 e; linarith
  have h03 : (∑ e, y (c0435 0) e) < ∑ e, y (c0435 3) e := by
    change (∑ e, y 0 e) < ∑ e, y 5 e; linarith
  have hS := lemmaS (x (c0435 0)) (x (c0435 2)) (x (c0435 1)) (x (c0435 3)) u 0 s t hs hs1.le ht ht1 hX
    (by simp only [add_zero]; linarith [key 1 0]) (by simp only [add_zero]; linarith [key 3 0])
  simp only [add_zero] at hS
  have hn : ⟪x (c0435 0) - x (c0435 1), u⟫ < 0 := by rw [D]; exact sub_neg.2 h01
  have e1 : ⟪x (c0435 2) - x (c0435 1), u⟫ = (∑ e, y (c0435 2) e) - ∑ e, y (c0435 1) e := D _ _
  have e3 : ⟪x (c0435 2) - x (c0435 3), u⟫ = (∑ e, y (c0435 2) e) - ∑ e, y (c0435 3) e := D _ _
  have hx_inj := Minimality.H24.SAT.inj_of_fac F
  rcases le_total (⟪u, x (c0435 1)⟫) (⟪u, x (c0435 3)⟫) with h | h
  · refine isRupert_of_q4_lex F hx_inj inj_c0435 cyc0435 hu (x 3 - x 4) ⟨(0, 1), by decide, hn⟩
      ⟨(2, 1), by decide, ?_, ?_⟩
    · rw [e1]; rw [min_eq_left h] at hS
      have k21 := key 2 1; linarith
    · intro h0
      have hne : x 3 - x 4 ≠ 0 := sub_ne_zero.2 fun heq => by
        have := hx_inj heq; revert this; decide
      exact real_inner_self_pos.2 hne
  · refine isRupert_of_q4_lex F hx_inj inj_c0435 cyc0435 hu (x 3 - x 5) ⟨(0, 1), by decide, hn⟩
      ⟨(2, 3), by decide, ?_, ?_⟩
    · rw [e3]; rw [min_eq_right h] at hS
      have k23 := key 2 3; linarith
    · intro h0
      have hne : x 3 - x 5 ≠ 0 := sub_ne_zero.2 fun heq => by
        have := hx_inj heq; revert this; decide
      exact real_inner_self_pos.2 hne

/-- Theorem P dispatch for EEVV cell `c0234`. -/
theorem isRupert_of_c0234 (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hu : CellAt F U0234 D0234 u) (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hv : ∀ e, ⟪v e, u⟫ = 1)
    (hE0 : (∑ e, y 0 e) = 1) (hE2 : (∑ e, y 2 e) = 1)
    (hV3 : 1 < ∑ e, y 3 e) (hV4 : 1 < ∑ e, y 4 e) :
    IsRupert (univ.image x) :=
  isRupert_of_orthocentre_eevv F (Minimality.H24.SAT.inj_of_fac F) inj_c0234 cyc0234 hu p v y hxy hv
    hE0 hE2 hV3 hV4

/-- Theorem P dispatch for EEVV cell `c0235`. -/
theorem isRupert_of_c0235 (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hu : CellAt F U0235 D0235 u) (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hv : ∀ e, ⟪v e, u⟫ = 1)
    (hE0 : (∑ e, y 0 e) = 1) (hE2 : (∑ e, y 2 e) = 1)
    (hV3 : 1 < ∑ e, y 3 e) (hV5 : 1 < ∑ e, y 5 e) :
    IsRupert (univ.image x) :=
  isRupert_of_orthocentre_eevv F (Minimality.H24.SAT.inj_of_fac F) inj_c0235 cyc0235 hu p v y hxy hv
    hE0 hE2 hV3 hV5

/-- Theorem P dispatch for EEVV cell `c6043`. -/
theorem isRupert_of_c6043 (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hu : CellAt F U6043 D6043 u) (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hv : ∀ e, ⟪v e, u⟫ = 1)
    (hE6 : (∑ e, y 6 e) = 1) (hE0 : (∑ e, y 0 e) = 1)
    (hV4 : 1 < ∑ e, y 4 e) (hV3 : 1 < ∑ e, y 3 e) :
    IsRupert (univ.image x) :=
  isRupert_of_orthocentre_eevv F (Minimality.H24.SAT.inj_of_fac F) inj_c6043 cyc6043 hu p v y hxy hv
    hE6 hE0 hV4 hV3

/-- Theorem P dispatch for EEVV cell `c6053`. -/
theorem isRupert_of_c6053 (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hu : CellAt F U6053 D6053 u) (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hv : ∀ e, ⟪v e, u⟫ = 1)
    (hE6 : (∑ e, y 6 e) = 1) (hE0 : (∑ e, y 0 e) = 1)
    (hV5 : 1 < ∑ e, y 5 e) (hV3 : 1 < ∑ e, y 3 e) :
    IsRupert (univ.image x) :=
  isRupert_of_orthocentre_eevv F (Minimality.H24.SAT.inj_of_fac F) inj_c6053 cyc6053 hu p v y hxy hv
    hE6 hE0 hV5 hV3

/-- Theorem P dispatch for EEVV cell `c6253`. -/
theorem isRupert_of_c6253 (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hu : CellAt F U6253 D6253 u) (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hv : ∀ e, ⟪v e, u⟫ = 1)
    (hE6 : (∑ e, y 6 e) = 1) (hE2 : (∑ e, y 2 e) = 1)
    (hV5 : 1 < ∑ e, y 5 e) (hV3 : 1 < ∑ e, y 3 e) :
    IsRupert (univ.image x) :=
  isRupert_of_orthocentre_eevv F (Minimality.H24.SAT.inj_of_fac F) inj_c6253 cyc6253 hu p v y hxy hv
    hE6 hE2 hV5 hV3

/-- Theorem P dispatch for EEVV cell `c6234`. -/
theorem isRupert_of_c6234 (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hu : CellAt F U6234 D6234 u) (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hv : ∀ e, ⟪v e, u⟫ = 1)
    (hE6 : (∑ e, y 6 e) = 1) (hE2 : (∑ e, y 2 e) = 1)
    (hV3 : 1 < ∑ e, y 3 e) (hV4 : 1 < ∑ e, y 4 e) :
    IsRupert (univ.image x) :=
  isRupert_of_orthocentre_eevv F (Minimality.H24.SAT.inj_of_fac F) inj_c6234 cyc6234 hu p v y hxy hv
    hE6 hE2 hV3 hV4

/-- Theorem P dispatch for EEEV cell `c0526`. -/
theorem isRupert_of_c0526 (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hu : CellAt F U0526 D0526 u) (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hv : ∀ e, ⟪v e, u⟫ = 1)
    (hE0 : (∑ e, y 0 e) = 1) (hE6 : (∑ e, y 6 e) = 1) (hV5 : 1 < ∑ e, y 5 e) :
    IsRupert (univ.image x) :=
  isRupert_of_orthocentre_eeev' F (Minimality.H24.SAT.inj_of_fac F) inj_c0526 cyc0526 hu p v y hxy hv
    (show (∑ e, y (c0526 0) e) < ∑ e, y (c0526 1) e by change (∑ e, y 0 e) < ∑ e, y 5 e; linarith)
    (show (∑ e, y (c0526 0) e) = ∑ e, y (c0526 3) e by change (∑ e, y 0 e) = ∑ e, y 6 e; linarith)

/-- Theorem P dispatch for EEEV cell `c6402`. -/
theorem isRupert_of_c6402 (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hu : CellAt F U6402 D6402 u) (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hv : ∀ e, ⟪v e, u⟫ = 1)
    (hE6 : (∑ e, y 6 e) = 1) (hE2 : (∑ e, y 2 e) = 1) (hV4 : 1 < ∑ e, y 4 e) :
    IsRupert (univ.image x) :=
  isRupert_of_orthocentre_eeev' F (Minimality.H24.SAT.inj_of_fac F) inj_c6402 cyc6402 hu p v y hxy hv
    (show (∑ e, y (c6402 0) e) < ∑ e, y (c6402 1) e by change (∑ e, y 6 e) < ∑ e, y 4 e; linarith)
    (show (∑ e, y (c6402 0) e) = ∑ e, y (c6402 3) e by change (∑ e, y 6 e) = ∑ e, y 2 e; linarith)

/-- Theorem P dispatch for EEEV cell `c2360`. -/
theorem isRupert_of_c2360 (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hu : CellAt F U2360 D2360 u) (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hv : ∀ e, ⟪v e, u⟫ = 1)
    (hE2 : (∑ e, y 2 e) = 1) (hE0 : (∑ e, y 0 e) = 1) (hV3 : 1 < ∑ e, y 3 e) :
    IsRupert (univ.image x) :=
  isRupert_of_orthocentre_eeev' F (Minimality.H24.SAT.inj_of_fac F) inj_c2360 cyc2360 hu p v y hxy hv
    (show (∑ e, y (c2360 0) e) < ∑ e, y (c2360 1) e by change (∑ e, y 2 e) < ∑ e, y 3 e; linarith)
    (show (∑ e, y (c2360 0) e) = ∑ e, y (c2360 3) e by change (∑ e, y 2 e) = ∑ e, y 0 e; linarith)

/-- Theorem P dispatch for 5-rim EEEVV cell `c26053`. -/
theorem isRupert_of_c26053 (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hu : CellAt F U26053 D26053 u) (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hv : ∀ e, ⟪v e, u⟫ = 1)
    (hE2 : (∑ e, y 2 e) = 1) (hE6 : (∑ e, y 6 e) = 1) (hE0 : (∑ e, y 0 e) = 1)
    (hV5 : 1 < ∑ e, y 5 e) (hV3 : 1 < ∑ e, y 3 e) :
    IsRupert (univ.image x) :=
  isRupert_of_orthocentre_5rim_eeevv F (Minimality.H24.SAT.inj_of_fac F) inj_c26053 cyc26053 hu p v y hxy hv
    hE2 hE6 hE0 hV5 hV3

/-- Theorem P dispatch for 5-rim EEEVV cell `c26043`. -/
theorem isRupert_of_c26043 (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hu : CellAt F U26043 D26043 u) (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hv : ∀ e, ⟪v e, u⟫ = 1)
    (hE2 : (∑ e, y 2 e) = 1) (hE6 : (∑ e, y 6 e) = 1) (hE0 : (∑ e, y 0 e) = 1)
    (hV4 : 1 < ∑ e, y 4 e) (hV3 : 1 < ∑ e, y 3 e) :
    IsRupert (univ.image x) :=
  isRupert_of_orthocentre_5rim_eeevv F (Minimality.H24.SAT.inj_of_fac F) inj_c26043 cyc26043 hu p v y hxy hv
    hE2 hE6 hE0 hV4 hV3

/-- Theorem P dispatch for 5-rim EEEVV cell `c60234`. -/
theorem isRupert_of_c60234 (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hu : CellAt F U60234 D60234 u) (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hv : ∀ e, ⟪v e, u⟫ = 1)
    (hE6 : (∑ e, y 6 e) = 1) (hE0 : (∑ e, y 0 e) = 1) (hE2 : (∑ e, y 2 e) = 1)
    (hV3 : 1 < ∑ e, y 3 e) (hV4 : 1 < ∑ e, y 4 e) :
    IsRupert (univ.image x) :=
  isRupert_of_orthocentre_5rim_eeevv F (Minimality.H24.SAT.inj_of_fac F) inj_c60234 cyc60234 hu p v y hxy hv
    hE6 hE0 hE2 hV3 hV4

/-- Theorem P dispatch for 5-rim EEEVV cell `c02635`. -/
theorem isRupert_of_c02635 (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hu : CellAt F U02635 D02635 u) (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hv : ∀ e, ⟪v e, u⟫ = 1)
    (hE0 : (∑ e, y 0 e) = 1) (hE2 : (∑ e, y 2 e) = 1) (hE6 : (∑ e, y 6 e) = 1)
    (hV3 : 1 < ∑ e, y 3 e) (hV5 : 1 < ∑ e, y 5 e) :
    IsRupert (univ.image x) :=
  isRupert_of_orthocentre_5rim_eeevv F (Minimality.H24.SAT.inj_of_fac F) inj_c02635 cyc02635 hu p v y hxy hv
    hE0 hE2 hE6 hV3 hV5

/-- Theorem P dispatch for 5-rim EEEVV cell `c02634`. -/
theorem isRupert_of_c02634 (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hu : CellAt F U02634 D02634 u) (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hv : ∀ e, ⟪v e, u⟫ = 1)
    (hE0 : (∑ e, y 0 e) = 1) (hE2 : (∑ e, y 2 e) = 1) (hE6 : (∑ e, y 6 e) = 1)
    (hV3 : 1 < ∑ e, y 3 e) (hV4 : 1 < ∑ e, y 4 e) :
    IsRupert (univ.image x) :=
  isRupert_of_orthocentre_5rim_eeevv F (Minimality.H24.SAT.inj_of_fac F) inj_c02634 cyc02634 hu p v y hxy hv
    hE0 hE2 hE6 hV3 hV4

/-- Theorem P dispatch for 5-rim EEEVV cell `c60253`. -/
theorem isRupert_of_c60253 (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hu : CellAt F U60253 D60253 u) (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hv : ∀ e, ⟪v e, u⟫ = 1)
    (hE6 : (∑ e, y 6 e) = 1) (hE0 : (∑ e, y 0 e) = 1) (hE2 : (∑ e, y 2 e) = 1)
    (hV5 : 1 < ∑ e, y 5 e) (hV3 : 1 < ∑ e, y 3 e) :
    IsRupert (univ.image x) :=
  isRupert_of_orthocentre_5rim_eeevv F (Minimality.H24.SAT.inj_of_fac F) inj_c60253 cyc60253 hu p v y hxy hv
    hE6 hE0 hE2 hV5 hV3

/-- Theorem P dispatch for 5-rim EEVVV cell `c60534`. -/
theorem isRupert_of_c60534 (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hu : CellAt F U60534 D60534 u) (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hv : ∀ e, ⟪v e, u⟫ = 1)
    (hE6 : (∑ e, y 6 e) = 1) (hE0 : (∑ e, y 0 e) = 1)
    (hV3 : 1 < ∑ e, y 3 e) (hV4 : 1 < ∑ e, y 4 e) (hV5 : 1 < ∑ e, y 5 e) :
    IsRupert (univ.image x) := by
  have hx_inj := Minimality.H24.SAT.inj_of_fac F
  have d03 : 0 < ⟪x 3 - x 0, u⟫ := by rw [depth_orthocentre x p v y hxy u hv]; linarith
  have h03 : ⟪u, x 0⟫ < ⟪u, x 3⟫ := by
    rw [inner_sub_left] at d03
    linarith [real_inner_comm u (x 3), real_inner_comm u (x 0)]
  rcases type24_quad_depth_split F u h03 with h34 | h35
  · have hd : 0 < ⟪x 0 - x 6, x 0 - x 6⟫ := real_inner_self_pos.2 (sub_ne_zero.2 fun heq => by
      have := hx_inj heq; revert this; decide)
    exact isRupert_of_orthocentre_5rim_eevvv F hx_inj inj_c60534_rev cyc60534_rev hu p v y hxy hv
      hE0 hE6 hV5 (x 0 - x 6) hd (Or.inl h34)
  · have hd : 0 < ⟪x 6 - x 0, x 6 - x 0⟫ := real_inner_self_pos.2 (sub_ne_zero.2 fun heq => by
      have := hx_inj heq; revert this; decide)
    exact isRupert_of_orthocentre_5rim_eevvv F hx_inj inj_c60534 cyc60534 hu p v y hxy hv
      hE6 hE0 hV4 (x 6 - x 0) hd (Or.inl h35)

/-- Theorem P dispatch for 5-rim EEVVV cell `c62534`. -/
theorem isRupert_of_c62534 (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hu : CellAt F U62534 D62534 u) (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hv : ∀ e, ⟪v e, u⟫ = 1)
    (hE6 : (∑ e, y 6 e) = 1) (hE2 : (∑ e, y 2 e) = 1) (hE0 : (∑ e, y 0 e) = 1)
    (hV3 : 1 < ∑ e, y 3 e) (hV4 : 1 < ∑ e, y 4 e) (hV5 : 1 < ∑ e, y 5 e) :
    IsRupert (univ.image x) := by
  have hx_inj := Minimality.H24.SAT.inj_of_fac F
  have d03 : 0 < ⟪x 3 - x 0, u⟫ := by rw [depth_orthocentre x p v y hxy u hv]; linarith
  have h03 : ⟪u, x 0⟫ < ⟪u, x 3⟫ := by
    rw [inner_sub_left] at d03
    linarith [real_inner_comm u (x 3), real_inner_comm u (x 0)]
  rcases type24_quad_depth_split F u h03 with h34 | h35
  · have hd : 0 < ⟪x 2 - x 6, x 2 - x 6⟫ := real_inner_self_pos.2 (sub_ne_zero.2 fun heq => by
      have := hx_inj heq; revert this; decide)
    exact isRupert_of_orthocentre_5rim_eevvv F hx_inj inj_c62534_rev cyc62534_rev hu p v y hxy hv
      hE2 hE6 hV5 (x 2 - x 6) hd (Or.inl h34)
  · have hd : 0 < ⟪x 6 - x 2, x 6 - x 2⟫ := real_inner_self_pos.2 (sub_ne_zero.2 fun heq => by
      have := hx_inj heq; revert this; decide)
    exact isRupert_of_orthocentre_5rim_eevvv F hx_inj inj_c62534 cyc62534 hu p v y hxy hv
      hE6 hE2 hV4 (x 6 - x 2) hd (Or.inl h35)

/-- Theorem P dispatch for 5-rim EEVVV cell `c02534`. -/
theorem isRupert_of_c02534 (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hu : CellAt F U02534 D02534 u) (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hv : ∀ e, ⟪v e, u⟫ = 1)
    (hE0 : (∑ e, y 0 e) = 1) (hE2 : (∑ e, y 2 e) = 1)
    (hV3 : 1 < ∑ e, y 3 e) (hV4 : 1 < ∑ e, y 4 e) (hV5 : 1 < ∑ e, y 5 e) :
    IsRupert (univ.image x) := by
  have hx_inj := Minimality.H24.SAT.inj_of_fac F
  have d03 : 0 < ⟪x 3 - x 0, u⟫ := by rw [depth_orthocentre x p v y hxy u hv]; linarith
  have h03 : ⟪u, x 0⟫ < ⟪u, x 3⟫ := by
    rw [inner_sub_left] at d03
    linarith [real_inner_comm u (x 3), real_inner_comm u (x 0)]
  rcases type24_quad_depth_split F u h03 with h34 | h35
  · have hd : 0 < ⟪x 2 - x 0, x 2 - x 0⟫ := real_inner_self_pos.2 (sub_ne_zero.2 fun heq => by
      have := hx_inj heq; revert this; decide)
    exact isRupert_of_orthocentre_5rim_eevvv F hx_inj inj_c02534_rev cyc02534_rev hu p v y hxy hv
      hE2 hE0 hV5 (x 2 - x 0) hd (Or.inl h34)
  · have hd : 0 < ⟪x 0 - x 2, x 0 - x 2⟫ := real_inner_self_pos.2 (sub_ne_zero.2 fun heq => by
      have := hx_inj heq; revert this; decide)
    exact isRupert_of_orthocentre_5rim_eevvv F hx_inj inj_c02534 cyc02534 hu p v y hxy hv
      hE0 hE2 hV4 (x 0 - x 2) hd (Or.inl h35)

/-- Theorem P dispatch for 6-rim EEEVVV cell `c602534`. -/
theorem isRupert_of_c602534 (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hu : CellAt F U602534 D602534 u) (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hv : ∀ e, ⟪v e, u⟫ = 1)
    (hv0 : v 0 = x 0 - x 1) (hv1 : v 1 = x 2 - x 1) (hv2 : v 2 = x 6 - x 1)
    (hobt : ∀ e f, e ≠ f → ⟪v e, v f⟫ ≤ 0)
    (hE6 : (∑ e, y 6 e) = 1) (hE0 : (∑ e, y 0 e) = 1) (hE2 : (∑ e, y 2 e) = 1)
    (hV3 : 1 < ∑ e, y 3 e) (hV4 : 1 < ∑ e, y 4 e) (hV5 : 1 < ∑ e, y 5 e) :
    IsRupert (univ.image x) := by
  have hx_inj := Minimality.H24.SAT.inj_of_fac F
  have hne01 : x 0 ≠ x 1 := fun heq => by have := hx_inj heq; revert this; decide
  have hobt20 : ⟪x 6 - x 1, x 0 - x 1⟫ ≤ 0 := by rw [← hv2, ← hv0]; exact hobt 2 0 (by decide)
  have hobt10 : ⟪x 2 - x 1, x 0 - x 1⟫ ≤ 0 := by rw [← hv1, ← hv0]; exact hobt 1 0 (by decide)
  have hd10 : 0 < ⟪x 6 - x 0, x 1 - x 0⟫ := tilt_sign_middle_end (x 6) (x 0) (x 1) hne01 hobt20
  have hd12 : 0 < ⟪x 2 - x 0, x 1 - x 0⟫ := tilt_sign_middle_end (x 2) (x 0) (x 1) hne01 hobt10
  have d03 : 0 < ⟪x 3 - x 0, u⟫ := by rw [depth_orthocentre x p v y hxy u hv]; linarith
  have h03 : ⟪u, x 0⟫ < ⟪u, x 3⟫ := by
    rw [inner_sub_left] at d03
    linarith [real_inner_comm u (x 3), real_inner_comm u (x 0)]
  have ht := depth_all_cases ⟪u, x 3⟫ ⟪u, x 4⟫ ⟪u, x 5⟫
  rcases ht with hlt4 | hlt5 | ⟨hgt4, hgt5⟩ | heq4 | heq5
  · have h35 : 0 < ⟪x 3 - x 5, u⟫ := by
      rcases type24_quad_depth_split F u h03 with h | h
      · rw [inner_sub_left] at h
        linarith [real_inner_comm u (x 3), real_inner_comm u (x 4)]
      · exact h
    have h45 : 0 < ⟪x 4 - x 3, u⟫ := by
      rw [inner_sub_left]
      linarith [real_inner_comm u (x 4), real_inner_comm u (x 3)]
    exact isRupert_of_orthocentre_6rim_peak5 F hx_inj inj_c602534 cyc602534 hu p v y hxy hv
      hE6 hE0 hE2 hV5 hV4 (x 1 - x 0) hd10 hd12 (Or.inl h35) (Or.inl h45)
  · have h34 : 0 < ⟪x 3 - x 4, u⟫ := by
      rcases type24_quad_depth_split F u h03 with h | h
      · exact h
      · rw [inner_sub_left] at h
        linarith [real_inner_comm u (x 3), real_inner_comm u (x 5)]
    have h45 : 0 < ⟪x 5 - x 3, u⟫ := by
      rw [inner_sub_left]
      linarith [real_inner_comm u (x 5), real_inner_comm u (x 3)]
    exact isRupert_of_orthocentre_6rim_peak5 F hx_inj inj_c602534_rev cyc602534_rev hu p v y hxy hv
      hE2 hE0 hE6 hV4 hV5 (x 1 - x 0) hd12 hd10 (Or.inl h34) (Or.inl h45)
  · have h35 : 0 < ⟪x 3 - x 5, u⟫ := by
      rw [inner_sub_left]
      linarith [real_inner_comm u (x 3), real_inner_comm u (x 5)]
    have h34 : 0 < ⟪x 3 - x 4, u⟫ := by
      rw [inner_sub_left]
      linarith [real_inner_comm u (x 3), real_inner_comm u (x 4)]
    exact isRupert_of_orthocentre_6rim F hx_inj inj_c602534 cyc602534 hu p v y hxy hv
      hE6 hE0 hE2 hV5 hV4 (x 1 - x 0) hd10 hd12 (Or.inl h35) (Or.inl h34)
  · have h35 : 0 < ⟪x 3 - x 5, u⟫ := by
      rcases type24_quad_depth_split F u h03 with h | h
      · rw [inner_sub_left] at h
        linarith [real_inner_comm u (x 3), real_inner_comm u (x 4)]
      · exact h
    have heq_sub : ⟪x 4 - x 3, u⟫ = 0 := by
      rw [inner_sub_left]
      linarith [real_inner_comm u (x 3), real_inner_comm u (x 4)]
    have heq_sub34 : ⟪x 3 - x 4, u⟫ = 0 := by
      rw [inner_sub_left]
      linarith [real_inner_comm u (x 3), real_inner_comm u (x 4)]
    rcases lt_or_ge (⟪x 4 - x 3, x 1 - x 0⟫) 0 with hB | hB
    · have hd34 : 0 < ⟪x 3 - x 4, x 1 - x 0⟫ := by
        have : ⟪x 3 - x 4, x 1 - x 0⟫ = -⟪x 4 - x 3, x 1 - x 0⟫ := by
          rw [← inner_neg_left, neg_sub]
        linarith
      exact isRupert_of_orthocentre_6rim F hx_inj inj_c602534 cyc602534 hu p v y hxy hv
        hE6 hE0 hE2 hV5 hV4 (x 1 - x 0) hd10 hd12 (Or.inl h35) (Or.inr ⟨heq_sub34, hd34⟩)
    · have hw3 : x 4 - x 3 ≠ 0 := sub_ne_zero.2 fun heq => by
        have := hx_inj heq; revert this; decide
      obtain ⟨d, hd10', hd12', hd43⟩ :=
        exists_tilt_for_tie (x 6 - x 0) (x 2 - x 0) (x 4 - x 3) (x 1 - x 0) hd10 hd12 hw3 hB
      exact isRupert_of_orthocentre_6rim_peak5 F hx_inj inj_c602534 cyc602534 hu p v y hxy hv
        hE6 hE0 hE2 hV5 hV4 d hd10' hd12' (Or.inl h35) (Or.inr ⟨heq_sub, hd43⟩)
  · have h34 : 0 < ⟪x 3 - x 4, u⟫ := by
      rcases type24_quad_depth_split F u h03 with h | h
      · exact h
      · rw [inner_sub_left] at h
        linarith [real_inner_comm u (x 3), real_inner_comm u (x 5)]
    have heq_sub : ⟪x 5 - x 3, u⟫ = 0 := by
      rw [inner_sub_left]
      linarith [real_inner_comm u (x 3), real_inner_comm u (x 5)]
    have heq_sub35 : ⟪x 3 - x 5, u⟫ = 0 := by
      rw [inner_sub_left]
      linarith [real_inner_comm u (x 3), real_inner_comm u (x 5)]
    rcases lt_or_ge (⟪x 5 - x 3, x 1 - x 0⟫) 0 with hB | hB
    · have hd35 : 0 < ⟪x 3 - x 5, x 1 - x 0⟫ := by
        have : ⟪x 3 - x 5, x 1 - x 0⟫ = -⟪x 5 - x 3, x 1 - x 0⟫ := by
          rw [← inner_neg_left, neg_sub]
        linarith
      exact isRupert_of_orthocentre_6rim F hx_inj inj_c602534 cyc602534 hu p v y hxy hv
        hE6 hE0 hE2 hV5 hV4 (x 1 - x 0) hd10 hd12 (Or.inr ⟨heq_sub35, hd35⟩) (Or.inl h34)
    · have hw3 : x 5 - x 3 ≠ 0 := sub_ne_zero.2 fun heq => by
        have := hx_inj heq; revert this; decide
      obtain ⟨d, hd12', hd10', hd53⟩ :=
        exists_tilt_for_tie (x 2 - x 0) (x 6 - x 0) (x 5 - x 3) (x 1 - x 0) hd12 hd10 hw3 hB
      exact isRupert_of_orthocentre_6rim_peak5 F hx_inj inj_c602534_rev cyc602534_rev hu p v y hxy hv
        hE2 hE0 hE6 hV4 hV5 d hd12' hd10' (Or.inl h34) (Or.inr ⟨heq_sub, hd53⟩)

/-- Theorem P dispatch for 6-rim EEEVVV cell `c260435`. -/
theorem isRupert_of_c260435 (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hu : CellAt F U260435 D260435 u) (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hv : ∀ e, ⟪v e, u⟫ = 1)
    (hv0 : v 0 = x 0 - x 1) (hv1 : v 1 = x 2 - x 1) (hv2 : v 2 = x 6 - x 1)
    (hobt : ∀ e f, e ≠ f → ⟪v e, v f⟫ ≤ 0)
    (hE2 : (∑ e, y 2 e) = 1) (hE6 : (∑ e, y 6 e) = 1) (hE0 : (∑ e, y 0 e) = 1)
    (hV3 : 1 < ∑ e, y 3 e) (hV4 : 1 < ∑ e, y 4 e) (hV5 : 1 < ∑ e, y 5 e) :
    IsRupert (univ.image x) := by
  have hx_inj := Minimality.H24.SAT.inj_of_fac F
  have hne61 : x 6 ≠ x 1 := fun heq => by have := hx_inj heq; revert this; decide
  have hobt12 : ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0 := by rw [← hv1, ← hv2]; exact hobt 1 2 (by decide)
  have hobt02 : ⟪x 0 - x 1, x 6 - x 1⟫ ≤ 0 := by rw [← hv0, ← hv2]; exact hobt 0 2 (by decide)
  have hd10 : 0 < ⟪x 2 - x 6, x 1 - x 6⟫ := tilt_sign_middle_end (x 2) (x 6) (x 1) hne61 hobt12
  have hd12 : 0 < ⟪x 0 - x 6, x 1 - x 6⟫ := tilt_sign_middle_end (x 0) (x 6) (x 1) hne61 hobt02
  have d03 : 0 < ⟪x 3 - x 0, u⟫ := by rw [depth_orthocentre x p v y hxy u hv]; linarith
  have h03 : ⟪u, x 0⟫ < ⟪u, x 3⟫ := by
    rw [inner_sub_left] at d03
    linarith [real_inner_comm u (x 3), real_inner_comm u (x 0)]
  have ht := depth_all_cases ⟪u, x 3⟫ ⟪u, x 4⟫ ⟪u, x 5⟫
  rcases ht with hlt4 | hlt5 | ⟨hgt4, hgt5⟩ | heq4 | heq5
  · have h35 : 0 < ⟪x 3 - x 5, u⟫ := by
      rcases type24_quad_depth_split F u h03 with h | h
      · rw [inner_sub_left] at h
        linarith [real_inner_comm u (x 3), real_inner_comm u (x 4)]
      · exact h
    have h45 : 0 < ⟪x 4 - x 3, u⟫ := by
      rw [inner_sub_left]
      linarith [real_inner_comm u (x 4), real_inner_comm u (x 3)]
    exact isRupert_of_orthocentre_6rim_peak5 F hx_inj inj_c260435_rev cyc260435_rev hu p v y hxy hv
      hE0 hE6 hE2 hV5 hV4 (x 1 - x 6) hd12 hd10 (Or.inl h35) (Or.inl h45)
  · have h34 : 0 < ⟪x 3 - x 4, u⟫ := by
      rcases type24_quad_depth_split F u h03 with h | h
      · exact h
      · rw [inner_sub_left] at h
        linarith [real_inner_comm u (x 3), real_inner_comm u (x 5)]
    have h45 : 0 < ⟪x 5 - x 3, u⟫ := by
      rw [inner_sub_left]
      linarith [real_inner_comm u (x 5), real_inner_comm u (x 3)]
    exact isRupert_of_orthocentre_6rim_peak5 F hx_inj inj_c260435 cyc260435 hu p v y hxy hv
      hE2 hE6 hE0 hV4 hV5 (x 1 - x 6) hd10 hd12 (Or.inl h34) (Or.inl h45)
  · have h34 : 0 < ⟪x 3 - x 4, u⟫ := by
      rw [inner_sub_left]
      linarith [real_inner_comm u (x 3), real_inner_comm u (x 4)]
    have h35 : 0 < ⟪x 3 - x 5, u⟫ := by
      rw [inner_sub_left]
      linarith [real_inner_comm u (x 3), real_inner_comm u (x 5)]
    exact isRupert_of_orthocentre_6rim F hx_inj inj_c260435 cyc260435 hu p v y hxy hv
      hE2 hE6 hE0 hV4 hV5 (x 1 - x 6) hd10 hd12 (Or.inl h34) (Or.inl h35)
  · have h35 : 0 < ⟪x 3 - x 5, u⟫ := by
      rcases type24_quad_depth_split F u h03 with h | h
      · rw [inner_sub_left] at h
        linarith [real_inner_comm u (x 3), real_inner_comm u (x 4)]
      · exact h
    have heq_sub : ⟪x 4 - x 3, u⟫ = 0 := by
      rw [inner_sub_left]
      linarith [real_inner_comm u (x 3), real_inner_comm u (x 4)]
    have heq_sub34 : ⟪x 3 - x 4, u⟫ = 0 := by
      rw [inner_sub_left]
      linarith [real_inner_comm u (x 3), real_inner_comm u (x 4)]
    rcases lt_or_ge (⟪x 4 - x 3, x 1 - x 6⟫) 0 with hB | hB
    · have hd34 : 0 < ⟪x 3 - x 4, x 1 - x 6⟫ := by
        have : ⟪x 3 - x 4, x 1 - x 6⟫ = -⟪x 4 - x 3, x 1 - x 6⟫ := by
          rw [← inner_neg_left, neg_sub]
        linarith
      exact isRupert_of_orthocentre_6rim F hx_inj inj_c260435 cyc260435 hu p v y hxy hv
        hE2 hE6 hE0 hV4 hV5 (x 1 - x 6) hd10 hd12 (Or.inr ⟨heq_sub34, hd34⟩) (Or.inl h35)
    · have hw3 : x 4 - x 3 ≠ 0 := sub_ne_zero.2 fun heq => by
        have := hx_inj heq; revert this; decide
      obtain ⟨d, hd12', hd10', hd43⟩ :=
        exists_tilt_for_tie (x 0 - x 6) (x 2 - x 6) (x 4 - x 3) (x 1 - x 6) hd12 hd10 hw3 hB
      exact isRupert_of_orthocentre_6rim_peak5 F hx_inj inj_c260435_rev cyc260435_rev hu p v y hxy hv
        hE0 hE6 hE2 hV5 hV4 d hd12' hd10' (Or.inl h35) (Or.inr ⟨heq_sub, hd43⟩)
  · have h34 : 0 < ⟪x 3 - x 4, u⟫ := by
      rcases type24_quad_depth_split F u h03 with h | h
      · exact h
      · rw [inner_sub_left] at h
        linarith [real_inner_comm u (x 3), real_inner_comm u (x 5)]
    have heq_sub : ⟪x 5 - x 3, u⟫ = 0 := by
      rw [inner_sub_left]
      linarith [real_inner_comm u (x 3), real_inner_comm u (x 5)]
    have heq_sub35 : ⟪x 3 - x 5, u⟫ = 0 := by
      rw [inner_sub_left]
      linarith [real_inner_comm u (x 3), real_inner_comm u (x 5)]
    rcases lt_or_ge (⟪x 5 - x 3, x 1 - x 6⟫) 0 with hB | hB
    · have hd35 : 0 < ⟪x 3 - x 5, x 1 - x 6⟫ := by
        have : ⟪x 3 - x 5, x 1 - x 6⟫ = -⟪x 5 - x 3, x 1 - x 6⟫ := by
          rw [← inner_neg_left, neg_sub]
        linarith
      exact isRupert_of_orthocentre_6rim F hx_inj inj_c260435 cyc260435 hu p v y hxy hv
        hE2 hE6 hE0 hV4 hV5 (x 1 - x 6) hd10 hd12 (Or.inl h34) (Or.inr ⟨heq_sub35, hd35⟩)
    · have hw3 : x 5 - x 3 ≠ 0 := sub_ne_zero.2 fun heq => by
        have := hx_inj heq; revert this; decide
      obtain ⟨d, hd10', hd12', hd53⟩ :=
        exists_tilt_for_tie (x 2 - x 6) (x 0 - x 6) (x 5 - x 3) (x 1 - x 6) hd10 hd12 hw3 hB
      exact isRupert_of_orthocentre_6rim_peak5 F hx_inj inj_c260435 cyc260435 hu p v y hxy hv
        hE2 hE6 hE0 hV4 hV5 d hd10' hd12' (Or.inl h34) (Or.inr ⟨heq_sub, hd53⟩)

/-- Theorem P dispatch for 6-rim EEEVVV cell `c026435`. -/
theorem isRupert_of_c026435 (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hu : CellAt F U026435 D026435 u) (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hv : ∀ e, ⟪v e, u⟫ = 1)
    (hv0 : v 0 = x 0 - x 1) (hv1 : v 1 = x 2 - x 1) (hv2 : v 2 = x 6 - x 1)
    (hobt : ∀ e f, e ≠ f → ⟪v e, v f⟫ ≤ 0)
    (hE0 : (∑ e, y 0 e) = 1) (hE2 : (∑ e, y 2 e) = 1) (hE6 : (∑ e, y 6 e) = 1)
    (hV3 : 1 < ∑ e, y 3 e) (hV4 : 1 < ∑ e, y 4 e) (hV5 : 1 < ∑ e, y 5 e) :
    IsRupert (univ.image x) := by
  have hx_inj := Minimality.H24.SAT.inj_of_fac F
  have hne21 : x 2 ≠ x 1 := fun heq => by have := hx_inj heq; revert this; decide
  have hobt01 : ⟪x 0 - x 1, x 2 - x 1⟫ ≤ 0 := by rw [← hv0, ← hv1]; exact hobt 0 1 (by decide)
  have hobt21 : ⟪x 6 - x 1, x 2 - x 1⟫ ≤ 0 := by rw [← hv2, ← hv1]; exact hobt 2 1 (by decide)
  have hd10 : 0 < ⟪x 0 - x 2, x 1 - x 2⟫ := tilt_sign_middle_end (x 0) (x 2) (x 1) hne21 hobt01
  have hd12 : 0 < ⟪x 6 - x 2, x 1 - x 2⟫ := tilt_sign_middle_end (x 6) (x 2) (x 1) hne21 hobt21
  have d03 : 0 < ⟪x 3 - x 0, u⟫ := by rw [depth_orthocentre x p v y hxy u hv]; linarith
  have h03 : ⟪u, x 0⟫ < ⟪u, x 3⟫ := by
    rw [inner_sub_left] at d03
    linarith [real_inner_comm u (x 3), real_inner_comm u (x 0)]
  have ht := depth_all_cases ⟪u, x 3⟫ ⟪u, x 4⟫ ⟪u, x 5⟫
  rcases ht with hlt4 | hlt5 | ⟨hgt4, hgt5⟩ | heq4 | heq5
  · have h35 : 0 < ⟪x 3 - x 5, u⟫ := by
      rcases type24_quad_depth_split F u h03 with h | h
      · rw [inner_sub_left] at h
        linarith [real_inner_comm u (x 3), real_inner_comm u (x 4)]
      · exact h
    have h45 : 0 < ⟪x 4 - x 3, u⟫ := by
      rw [inner_sub_left]
      linarith [real_inner_comm u (x 4), real_inner_comm u (x 3)]
    exact isRupert_of_orthocentre_6rim_peak5 F hx_inj inj_c026435_rev cyc026435_rev hu p v y hxy hv
      hE6 hE2 hE0 hV5 hV4 (x 1 - x 2) hd12 hd10 (Or.inl h35) (Or.inl h45)
  · have h34 : 0 < ⟪x 3 - x 4, u⟫ := by
      rcases type24_quad_depth_split F u h03 with h | h
      · exact h
      · rw [inner_sub_left] at h
        linarith [real_inner_comm u (x 3), real_inner_comm u (x 5)]
    have h45 : 0 < ⟪x 5 - x 3, u⟫ := by
      rw [inner_sub_left]
      linarith [real_inner_comm u (x 5), real_inner_comm u (x 3)]
    exact isRupert_of_orthocentre_6rim_peak5 F hx_inj inj_c026435 cyc026435 hu p v y hxy hv
      hE0 hE2 hE6 hV4 hV5 (x 1 - x 2) hd10 hd12 (Or.inl h34) (Or.inl h45)
  · have h34 : 0 < ⟪x 3 - x 4, u⟫ := by
      rw [inner_sub_left]
      linarith [real_inner_comm u (x 3), real_inner_comm u (x 4)]
    have h35 : 0 < ⟪x 3 - x 5, u⟫ := by
      rw [inner_sub_left]
      linarith [real_inner_comm u (x 3), real_inner_comm u (x 5)]
    exact isRupert_of_orthocentre_6rim F hx_inj inj_c026435 cyc026435 hu p v y hxy hv
      hE0 hE2 hE6 hV4 hV5 (x 1 - x 2) hd10 hd12 (Or.inl h34) (Or.inl h35)
  · have h35 : 0 < ⟪x 3 - x 5, u⟫ := by
      rcases type24_quad_depth_split F u h03 with h | h
      · rw [inner_sub_left] at h
        linarith [real_inner_comm u (x 3), real_inner_comm u (x 4)]
      · exact h
    have heq_sub : ⟪x 4 - x 3, u⟫ = 0 := by
      rw [inner_sub_left]
      linarith [real_inner_comm u (x 3), real_inner_comm u (x 4)]
    have heq_sub34 : ⟪x 3 - x 4, u⟫ = 0 := by
      rw [inner_sub_left]
      linarith [real_inner_comm u (x 3), real_inner_comm u (x 4)]
    rcases lt_or_ge (⟪x 4 - x 3, x 1 - x 2⟫) 0 with hB | hB
    · have hd34 : 0 < ⟪x 3 - x 4, x 1 - x 2⟫ := by
        have : ⟪x 3 - x 4, x 1 - x 2⟫ = -⟪x 4 - x 3, x 1 - x 2⟫ := by
          rw [← inner_neg_left, neg_sub]
        linarith
      exact isRupert_of_orthocentre_6rim F hx_inj inj_c026435 cyc026435 hu p v y hxy hv
        hE0 hE2 hE6 hV4 hV5 (x 1 - x 2) hd10 hd12 (Or.inr ⟨heq_sub34, hd34⟩) (Or.inl h35)
    · have hw3 : x 4 - x 3 ≠ 0 := sub_ne_zero.2 fun heq => by
        have := hx_inj heq; revert this; decide
      obtain ⟨d, hd12', hd10', hd43⟩ :=
        exists_tilt_for_tie (x 6 - x 2) (x 0 - x 2) (x 4 - x 3) (x 1 - x 2) hd12 hd10 hw3 hB
      exact isRupert_of_orthocentre_6rim_peak5 F hx_inj inj_c026435_rev cyc026435_rev hu p v y hxy hv
        hE6 hE2 hE0 hV5 hV4 d hd12' hd10' (Or.inl h35) (Or.inr ⟨heq_sub, hd43⟩)
  · have h34 : 0 < ⟪x 3 - x 4, u⟫ := by
      rcases type24_quad_depth_split F u h03 with h | h
      · exact h
      · rw [inner_sub_left] at h
        linarith [real_inner_comm u (x 3), real_inner_comm u (x 5)]
    have heq_sub : ⟪x 5 - x 3, u⟫ = 0 := by
      rw [inner_sub_left]
      linarith [real_inner_comm u (x 3), real_inner_comm u (x 5)]
    have heq_sub35 : ⟪x 3 - x 5, u⟫ = 0 := by
      rw [inner_sub_left]
      linarith [real_inner_comm u (x 3), real_inner_comm u (x 5)]
    rcases lt_or_ge (⟪x 5 - x 3, x 1 - x 2⟫) 0 with hB | hB
    · have hd35 : 0 < ⟪x 3 - x 5, x 1 - x 2⟫ := by
        have : ⟪x 3 - x 5, x 1 - x 2⟫ = -⟪x 5 - x 3, x 1 - x 2⟫ := by
          rw [← inner_neg_left, neg_sub]
        linarith
      exact isRupert_of_orthocentre_6rim F hx_inj inj_c026435 cyc026435 hu p v y hxy hv
        hE0 hE2 hE6 hV4 hV5 (x 1 - x 2) hd10 hd12 (Or.inl h34) (Or.inr ⟨heq_sub35, hd35⟩)
    · have hw3 : x 5 - x 3 ≠ 0 := sub_ne_zero.2 fun heq => by
        have := hx_inj heq; revert this; decide
      obtain ⟨d, hd10', hd12', hd53⟩ :=
        exists_tilt_for_tie (x 0 - x 2) (x 6 - x 2) (x 5 - x 3) (x 1 - x 2) hd10 hd12 hw3 hB
      exact isRupert_of_orthocentre_6rim_peak5 F hx_inj inj_c026435 cyc026435 hu p v y hxy hv
        hE0 hE2 hE6 hV4 hV5 d hd10' hd12' (Or.inl h34) (Or.inr ⟨heq_sub, hd53⟩)

-- ----------------------------------------------------------------------------
-- Theorem P (Type 24 End-to-End Dispatch)
-- ----------------------------------------------------------------------------

/-- **Theorem P for Type 24.**
For any solid of Type 24 (`F : S0xFac 9 s0x_S24 x`), with an obtuse corner at vertex 1
represented by edge coordinates `y`, and `u` the orthocentre view (`⟪v e, u⟫ = 1`)
lying in any of the candidate cells of `C` with contiguous ends: `IsRupert (univ.image x)`. -/
theorem theoremP24_of_candidateCell (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (cell : FeasibleCellC) (hcell : InFeasibleCell F u cell)
    (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hv : ∀ e, ⟪v e, u⟫ = 1)
    (hp : p = x 1)
    (hv0 : v 0 = x 0 - x 1) (hv1 : v 1 = x 2 - x 1) (hv2 : v 2 = x 6 - x 1)
    (hobt : ∀ e f, e ≠ f → ⟪v e, v f⟫ ≤ 0) :
    IsRupert (univ.image x) := by
  have ⟨hV3, hV4, hV5, hE0, hE2, hE6⟩ := type24_sigma_gt_one F p v y hxy hp hv0 hv1 hv2
  cases cell with
  | c0435 => exact isRupert_of_c0435 F hcell p v y hxy hv hE0 hV4 hV5
  | c0234 => exact isRupert_of_c0234 F hcell p v y hxy hv hE0 hE2 hV3 hV4
  | c0235 => exact isRupert_of_c0235 F hcell p v y hxy hv hE0 hE2 hV3 hV5
  | c6043 => exact isRupert_of_c6043 F hcell p v y hxy hv hE6 hE0 hV4 hV3
  | c6053 => exact isRupert_of_c6053 F hcell p v y hxy hv hE6 hE0 hV5 hV3
  | c6253 => exact isRupert_of_c6253 F hcell p v y hxy hv hE6 hE2 hV5 hV3
  | c6234 => exact isRupert_of_c6234 F hcell p v y hxy hv hE6 hE2 hV3 hV4
  | c0526 => exact isRupert_of_c0526 F hcell p v y hxy hv hE0 hE6 hV5
  | c6402 => exact isRupert_of_c6402 F hcell p v y hxy hv hE6 hE2 hV4
  | c2360 => exact isRupert_of_c2360 F hcell p v y hxy hv hE2 hE0 hV3
  | c26053 => exact isRupert_of_c26053 F hcell p v y hxy hv hE2 hE6 hE0 hV5 hV3
  | c26043 => exact isRupert_of_c26043 F hcell p v y hxy hv hE2 hE6 hE0 hV4 hV3
  | c60234 => exact isRupert_of_c60234 F hcell p v y hxy hv hE6 hE0 hE2 hV3 hV4
  | c02635 => exact isRupert_of_c02635 F hcell p v y hxy hv hE0 hE2 hE6 hV3 hV5
  | c02634 => exact isRupert_of_c02634 F hcell p v y hxy hv hE0 hE2 hE6 hV3 hV4
  | c60253 => exact isRupert_of_c60253 F hcell p v y hxy hv hE6 hE0 hE2 hV5 hV3
  | c60534 => exact isRupert_of_c60534 F hcell p v y hxy hv hE6 hE0 hV3 hV4 hV5
  | c62534 => exact isRupert_of_c62534 F hcell p v y hxy hv hE6 hE2 hE0 hV3 hV4 hV5
  | c02534 => exact isRupert_of_c02534 F hcell p v y hxy hv hE0 hE2 hV3 hV4 hV5
  | c026435 => exact isRupert_of_c026435 F hcell p v y hxy hv hv0 hv1 hv2 hobt hE0 hE2 hE6 hV3 hV4 hV5
  | c602534 => exact isRupert_of_c602534 F hcell p v y hxy hv hv0 hv1 hv2 hobt hE6 hE0 hE2 hV3 hV4 hV5
  | c260435 => exact isRupert_of_c260435 F hcell p v y hxy hv hv0 hv1 hv2 hobt hE2 hE6 hE0 hV3 hV4 hV5

/-- **Theorem P (Type 24 Orthocentre Corollary).**
For any solid of Type 24 (`F : S0xFac 9 s0x_S24 x`), with vertex 1 an obtuse corner
with linearly independent edges `![x 0 - x 1, x 2 - x 1, x 6 - x 1]` that are pairwise non-acute,
if the orthocentre view `u` lies in a candidate cell with contiguous ends:
`IsRupert (univ.image x)`. -/
theorem theoremP24_orthocentre (F : S0xFac 9 s0x_S24 x)
    (hli : LinearIndependent ℝ ![x 0 - x 1, x 2 - x 1, x 6 - x 1])
    (hobt : ∀ e f, e ≠ f → ⟪![x 0 - x 1, x 2 - x 1, x 6 - x 1] e, ![x 0 - x 1, x 2 - x 1, x 6 - x 1] f⟫ ≤ 0)
    {cell : FeasibleCellC} {u : ℝ³}
    (hu : ∀ e, ⟪![x 0 - x 1, x 2 - x 1, x 6 - x 1] e, u⟫ = 1)
    (hcell : InFeasibleCell F u cell) :
    IsRupert (univ.image x) := by
  set p := x 1
  set v := ![x 0 - x 1, x 2 - x 1, x 6 - x 1]
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ ℝ³ := by simp
  set B := basisOfLinearIndependentOfCardEqFinrank hli hcard
  set y : Fin 7 → Fin 3 → ℝ := fun i e => B.repr (x i - p) e
  have hxy : ∀ i, x i = p + ∑ e, y i e • v e := by
    intro i
    have hrepr := B.sum_repr (x i - p)
    have hcoe : ⇑B = v := coe_basisOfLinearIndependentOfCardEqFinrank hli hcard
    have hsum : ∑ e, y i e • v e = x i - p := by
      show ∑ e, B.repr (x i - p) e • v e = x i - p
      rw [← hcoe]
      exact hrepr
    rw [hsum]
    abel
  exact theoremP24_of_candidateCell F cell hcell p v y hxy hu rfl rfl rfl rfl hobt

/-- **Theorem P (5-Rim EEVVV Orthocentre Corollary, Unconditional).**
For any solid of Type 24 (`F : S0xFac 9 s0x_S24 x`), with vertex 1 an obtuse corner
with linearly independent edges `![x 0 - x 1, x 2 - x 1, x 6 - x 1]` that are pairwise non-acute,
if the orthocentre view `u` lies in any of the 5-rim EEVVV cells `c60534, c62534, c02534`:
`IsRupert (univ.image x)` unconditionally (without any depth hypotheses). -/
theorem theoremP24_orthocentre_5rim (F : S0xFac 9 s0x_S24 x)
    (hli : LinearIndependent ℝ ![x 0 - x 1, x 2 - x 1, x 6 - x 1])
    (_hobt : ∀ e f, e ≠ f → ⟪![x 0 - x 1, x 2 - x 1, x 6 - x 1] e, ![x 0 - x 1, x 2 - x 1, x 6 - x 1] f⟫ ≤ 0)
    {cell : FeasibleCellC} {u : ℝ³}
    (hu : ∀ e, ⟪![x 0 - x 1, x 2 - x 1, x 6 - x 1] e, u⟫ = 1)
    (hcell : InFeasibleCell F u cell)
    (h5rim : cell = .c60534 ∨ cell = .c62534 ∨ cell = .c02534) :
    IsRupert (univ.image x) := by
  set p := x 1
  set v := ![x 0 - x 1, x 2 - x 1, x 6 - x 1]
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ ℝ³ := by simp
  set B := basisOfLinearIndependentOfCardEqFinrank hli hcard
  set y : Fin 7 → Fin 3 → ℝ := fun i e => B.repr (x i - p) e
  have hxy : ∀ i, x i = p + ∑ e, y i e • v e := by
    intro i
    have hrepr := B.sum_repr (x i - p)
    have hcoe : ⇑B = v := coe_basisOfLinearIndependentOfCardEqFinrank hli hcard
    have hsum : ∑ e, y i e • v e = x i - p := by
      show ∑ e, B.repr (x i - p) e • v e = x i - p
      rw [← hcoe]
      exact hrepr
    rw [hsum]
    abel
  have ⟨hV3, hV4, hV5, hE0, hE2, hE6⟩ := type24_sigma_gt_one F p v y hxy rfl rfl rfl rfl
  rcases h5rim with rfl | rfl | rfl
  · exact isRupert_of_c60534 F hcell p v y hxy hu hE6 hE0 hV3 hV4 hV5
  · exact isRupert_of_c62534 F hcell p v y hxy hu hE6 hE2 hE0 hV3 hV4 hV5
  · exact isRupert_of_c02534 F hcell p v y hxy hu hE0 hE2 hV3 hV4 hV5

end Minimality.T24.TheoremP
