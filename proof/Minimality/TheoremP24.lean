module

public import Mathlib
public import Minimality.RimCellClosed
public import Minimality.OrthoView
public import Minimality.OrthoView2
public import Minimality.OrthoView3
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


-- ----------------------------------------------------------------------------
-- Canonical Rim Cycles in C (the Orthocentre Silhouette Chamber)
-- ----------------------------------------------------------------------------























-- ----------------------------------------------------------------------------
-- S0xCycUD Certificates and Injective Rims (All by kernel decision)
-- ----------------------------------------------------------------------------



-- ----------------------------------------------------------------------------
-- Reversed Rim Cycles for Lemma S Branching
-- ----------------------------------------------------------------------------









-- ----------------------------------------------------------------------------
-- Contiguous Ends Verification
-- ----------------------------------------------------------------------------


-- ----------------------------------------------------------------------------
-- Feasible Cell Enumeration in C
-- ----------------------------------------------------------------------------



-- ----------------------------------------------------------------------------
-- The Dispatches: Per-Cell Leaves of Theorem P
-- ----------------------------------------------------------------------------























/-- Rim 0526 (EEEV, rotation of 0265). -/
def c0526 : ZMod 4 → Fin 7 := ![0, 5, 2, 6]
def U0526 : Finset (Fin 9) := {3, 4, 6, 7, 8}
def D0526 : Finset (Fin 9) := {0, 1, 2, 5}
theorem cyc0526 : S0xCycUD s0x_S24 c0526 U0526 D0526 := by decide
theorem inj_c0526 : Function.Injective c0526 := by decide

/-- Rim 6402 (EEEV, rotation of 0264). -/
def c6402 : ZMod 4 → Fin 7 := ![6, 4, 0, 2]
def U6402 : Finset (Fin 9) := {2, 3, 6, 7, 8}
def D6402 : Finset (Fin 9) := {0, 1, 4, 5}
theorem cyc6402 : S0xCycUD s0x_S24 c6402 U6402 D6402 := by decide
theorem inj_c6402 : Function.Injective c6402 := by decide

-- ----------------------------------------------------------------------------
-- Theorem P (Type 24 End-to-End Dispatch)
-- ----------------------------------------------------------------------------





end Minimality.T24.TheoremP
