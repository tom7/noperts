module

public import Minimality.FaceChordFac
public import Minimality.SplitTie
public import Minimality.FiveRim
public import Minimality.Q45Signs
public import Minimality.RimFromSigns
public import Minimality.Type24
public import Minimality.Type24SAT.Facets24
public import Minimality.ZModLemmas

@[expose] public section

open scoped RealInnerProductSpace Topology
open Finset Filter
open Minimality Minimality.H21 Minimality.FaceChord Minimality.T24.SAT Minimality.RimFromSigns Minimality.T24.Q45

namespace Minimality.T24.R012

/-!
# R012: The First R-Leaf and 012 Plane Machinery

This module formalizes:
1. **AL1 (`facetSigns_012`)**: Frame-free facet sign formulas along the line
   `u0(t) := (x 0 - x 1) + t • (x 2 - x 1)` in the 012 facet plane for all nine facets,
   roots `omega3_012`, `inv_omega4_012`, `t6_012`, `t8_012`, `t3_012`,
   and the C-bar consequence `1 / omega4 < omega3` from `omega_prod_gt_one`.
2. **AL2 (`fiveRim_of_signs`)**: Generic 5-rim convexity and interior positioning from silhouette signs
   (pentagon analogue of `quadRim_of_signs`), and its specialization to the 5-rim `(0, 4, 6, 3, 2)`.
3. **AL3 (`q012_LC_plus`, `q012_LC_minus`)**: Carbon's Theorem LC-K5 level-chord leaves on facet 0 (`012`),
   yielding `FaceChordView F 0`.
-/

-- =========================================================================
-- AL1: Facet signs on the 012 plane
-- =========================================================================

/-- Direction vector `u0(t)` on the plane of facet 0 (`012`), parametrized by `t : ℝ`.
Basis from vertex 1: `v0 = x 0 - x 1`, `v2 = x 2 - x 1`. -/
def u0 (x : Fin 7 → ℝ³) (t : ℝ) : ℝ³ := (x 0 - x 1) + t • (x 2 - x 1)

variable {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)

/-- Facet 1 (`016`) slope coefficient `λ1 = - F.f 1 (x 2) > 0`. -/
def lambda1 (F : S0xFac 9 s0x_S24 x) : ℝ := - F.f 1 (x 2)

/-- Facet 2 (`025`) scale coefficient `λ2 = - F.f 2 (x 1) > 0`. -/
def lambda2 (F : S0xFac 9 s0x_S24 x) : ℝ := - F.f 2 (x 1)

/-- Facet 4 (`046`) intercept coefficient `λ4 = - F.f 4 (x 1) > 0`. -/
def lambda4 (F : S0xFac 9 s0x_S24 x) : ℝ := - F.f 4 (x 1)

/-- Facet 7 (`236`) slope coefficient `λ7 = - F.f 7 (x 1) > 0`. -/
def lambda7 (F : S0xFac 9 s0x_S24 x) : ℝ := - F.f 7 (x 1)

/-- Facet 6 (`235`) slope coefficient `λ6 = - F.f 6 (x 1) > 0`. -/
def lambda6 (F : S0xFac 9 s0x_S24 x) : ℝ := - F.f 6 (x 1)

/-- Facet 3 (`0345`) intercept coefficient `λ3 = - F.f 3 (x 1) > 0`. -/
def lambda3 (F : S0xFac 9 s0x_S24 x) : ℝ := - F.f 3 (x 1)

/-- `ω3` of facet 7 (`236`) expressed frame-free as the root of `⟪F.N 7, u0(t)⟫`. -/
noncomputable def omega3_012 (F : S0xFac 9 s0x_S24 x) : ℝ :=
  - ⟪F.N 7, x 0 - x 1⟫ / ⟪F.N 7, x 2 - x 1⟫

/-- `1 / ω4` of facet 4 (`046`) expressed frame-free as the root of `⟪F.N 4, u0(t)⟫`. -/
noncomputable def inv_omega4_012 (F : S0xFac 9 s0x_S24 x) : ℝ :=
  - ⟪F.N 4, x 0 - x 1⟫ / ⟪F.N 4, x 2 - x 1⟫

/-- `ω4` of facet 4 (`046`) expressed frame-free. -/
noncomputable def omega4_012 (F : S0xFac 9 s0x_S24 x) : ℝ :=
  - ⟪F.N 4, x 2 - x 1⟫ / ⟪F.N 4, x 0 - x 1⟫

/-- Root of facet 6 (`235`) along `u0(t)`. -/
noncomputable def t6_012 (F : S0xFac 9 s0x_S24 x) : ℝ :=
  - ⟪F.N 6, x 0 - x 1⟫ / ⟪F.N 6, x 2 - x 1⟫

/-- Root of facet 8 (`346`) along `u0(t)`. -/
noncomputable def t8_012 (F : S0xFac 9 s0x_S24 x) : ℝ :=
  - ⟪F.N 8, x 0 - x 1⟫ / ⟪F.N 8, x 2 - x 1⟫

/-- Root of facet 3 (`0345`) along `u0(t)`. -/
noncomputable def t3_012 (F : S0xFac 9 s0x_S24 x) : ℝ :=
  - ⟪F.N 3, x 0 - x 1⟫ / ⟪F.N 3, x 2 - x 1⟫

theorem lambda1_pos : 0 < lambda1 F := by
  dsimp [lambda1]
  linarith [F.neg 1 2 (by decide)]

theorem lambda2_pos : 0 < lambda2 F := by
  dsimp [lambda2]
  linarith [F.neg 2 1 (by decide)]

theorem lambda4_pos : 0 < lambda4 F := by
  dsimp [lambda4]
  linarith [F.neg 4 1 (by decide)]

theorem lambda7_pos : 0 < lambda7 F := by
  dsimp [lambda7]
  linarith [F.neg 7 1 (by decide)]

theorem lambda6_pos : 0 < lambda6 F := by
  dsimp [lambda6]
  linarith [F.neg 6 1 (by decide)]

theorem lambda3_pos : 0 < lambda3 F := by
  dsimp [lambda3]
  linarith [F.neg 3 1 (by decide)]

/-- Facet 0 (`012`) is edge-on along `u0(t)`: `⟪F.N 0, u0 x t⟫ = 0`. -/
theorem inner_N0_u0 (t : ℝ) : ⟪F.N 0, u0 x t⟫ = 0 := by
  dsimp [u0]
  rw [inner_add_right, real_inner_smul_right]
  have h0 : ⟪F.N 0, x 0 - x 1⟫ = 0 := by
    have := (F.hN 0 (x 0) (x 1)).symm
    rw [F.zero 0 0 (by decide), F.zero 0 1 (by decide), sub_self] at this
    exact this
  have h2 : ⟪F.N 0, x 2 - x 1⟫ = 0 := by
    have := (F.hN 0 (x 2) (x 1)).symm
    rw [F.zero 0 2 (by decide), F.zero 0 1 (by decide), sub_self] at this
    exact this
  rw [h0, h2, mul_zero, add_zero]

/-- Facet 5 (`126`) is constant negative along `u0(t)`: `⟪F.N 5, u0 x t⟫ = F.f 5 (x 0) < 0`. -/
theorem inner_N5_u0 (t : ℝ) : ⟪F.N 5, u0 x t⟫ = F.f 5 (x 0) := by
  dsimp [u0]
  rw [inner_add_right, real_inner_smul_right]
  have h0 : ⟪F.N 5, x 0 - x 1⟫ = F.f 5 (x 0) := by
    have := (F.hN 5 (x 0) (x 1)).symm
    rw [F.zero 5 1 (by decide), sub_zero] at this
    exact this
  have h2 : ⟪F.N 5, x 2 - x 1⟫ = 0 := by
    have := (F.hN 5 (x 2) (x 1)).symm
    rw [F.zero 5 2 (by decide), F.zero 5 1 (by decide), sub_self] at this
    exact this
  rw [h0, h2, mul_zero, add_zero]

theorem inner_N5_u0_neg (t : ℝ) : ⟪F.N 5, u0 x t⟫ < 0 := by
  rw [inner_N5_u0]
  exact F.neg 5 0 (by decide)

/-- Facet 1 (`016`) is linear in `t`: `⟪F.N 1, u0 x t⟫ = - lambda1 F * t`. -/
theorem inner_N1_u0 (t : ℝ) : ⟪F.N 1, u0 x t⟫ = - lambda1 F * t := by
  dsimp [u0, lambda1]
  rw [inner_add_right, real_inner_smul_right]
  have h0 : ⟪F.N 1, x 0 - x 1⟫ = 0 := by
    have := (F.hN 1 (x 0) (x 1)).symm
    rw [F.zero 1 0 (by decide), F.zero 1 1 (by decide), sub_self] at this
    exact this
  have h2 : ⟪F.N 1, x 2 - x 1⟫ = F.f 1 (x 2) := by
    have := (F.hN 1 (x 2) (x 1)).symm
    rw [F.zero 1 1 (by decide), sub_zero] at this
    exact this
  rw [h0, h2, zero_add]
  ring

/-- Facet 2 (`025`) is linear in `t`: `⟪F.N 2, u0 x t⟫ = lambda2 F * (1 + t)`. -/
theorem inner_N2_u0 (t : ℝ) : ⟪F.N 2, u0 x t⟫ = lambda2 F * (1 + t) := by
  dsimp [u0, lambda2]
  rw [inner_add_right, real_inner_smul_right]
  have h0 : ⟪F.N 2, x 0 - x 1⟫ = - F.f 2 (x 1) := by
    have := (F.hN 2 (x 0) (x 1)).symm
    rw [F.zero 2 0 (by decide), zero_sub] at this
    exact this
  have h2 : ⟪F.N 2, x 2 - x 1⟫ = - F.f 2 (x 1) := by
    have := (F.hN 2 (x 2) (x 1)).symm
    rw [F.zero 2 2 (by decide), zero_sub] at this
    exact this
  rw [h0, h2]
  ring

/-- Facet 4 (`046`) linear formula: `⟪F.N 4, u0 x t⟫ = lambda4 F * (1 - omega4_012 F * t)`. -/
theorem inner_N4_u0 (t : ℝ) :
    ⟪F.N 4, u0 x t⟫ = lambda4 F * (1 - omega4_012 F * t) := by
  sorry

/-- Facet 7 (`236`) linear formula: `⟪F.N 7, u0 x t⟫ = lambda7 F * (t - omega3_012 F)`. -/
theorem inner_N7_u0 (t : ℝ) :
    ⟪F.N 7, u0 x t⟫ = lambda7 F * (t - omega3_012 F) := by
  sorry

/-- Facet 6 (`235`) affine formula: `⟪F.N 6, u0 x t⟫ = lambda6 F * (t - t6_012 F)`. -/
theorem inner_N6_u0 (t : ℝ) :
    ⟪F.N 6, u0 x t⟫ = lambda6 F * (t - t6_012 F) := by
  sorry

/-- Facet 3 (`0345`) affine formula. -/
theorem inner_N3_u0 (t : ℝ) :
    ⟪F.N 3, u0 x t⟫ = - F.f 3 (x 1) + t * (F.f 3 (x 2) - F.f 3 (x 1)) := by
  dsimp [u0]
  rw [inner_add_right, real_inner_smul_right]
  have h0 : ⟪F.N 3, x 0 - x 1⟫ = - F.f 3 (x 1) := by
    have := (F.hN 3 (x 0) (x 1)).symm
    rw [F.zero 3 0 (by decide), zero_sub] at this
    exact this
  have h2 : ⟪F.N 3, x 2 - x 1⟫ = F.f 3 (x 2) - F.f 3 (x 1) := (F.hN 3 (x 2) (x 1)).symm
  rw [h0, h2]

/-- Facet 8 (`346`) affine formula. -/
theorem inner_N8_u0 (t : ℝ) :
    ⟪F.N 8, u0 x t⟫ = (F.f 8 (x 0) - F.f 8 (x 1)) + t * (F.f 8 (x 2) - F.f 8 (x 1)) := by
  dsimp [u0]
  rw [inner_add_right, real_inner_smul_right]
  have h0 : ⟪F.N 8, x 0 - x 1⟫ = F.f 8 (x 0) - F.f 8 (x 1) := (F.hN 8 (x 0) (x 1)).symm
  have h2 : ⟪F.N 8, x 2 - x 1⟫ = F.f 8 (x 2) - F.f 8 (x 1) := (F.hN 8 (x 2) (x 1)).symm
  rw [h0, h2]

/-- C-bar consequence: `1 / ω4 < ω3` creates the non-empty window on `{t > 0}`. -/
theorem window_012_nonempty {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hΔ : 0 ≤ a * b * c - a - b - c - 2) : 1 / b < a := by
  have := omega_prod_gt_one ha hb hc hΔ
  exact (div_lt_iff₀ hb).mpr (by linarith)

-- =========================================================================
-- AL2: Generic 5-rim from silhouette signs
-- =========================================================================

/-- Cyclic labeling of the 5-rim `(0, 4, 6, 3, 2)` for facet 0 (`012`). -/
def rim012 : ZMod 5 → Fin 7
  | 0 => 0
  | 1 => 4
  | 2 => 6
  | 3 => 3
  | 4 => 2

theorem rim012_injective : Function.Injective rim012 := by
  intro i j hij
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
  rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
  first | rfl | revert hij; decide

/-- **Generic 5-Rim from Silhouette Signs (`fiveRim_of_signs`)**.
Pentagon analogue of `quadRim_of_signs`: given 5 rim vertices `p : ZMod 5 → Fin 7`,
an edge-on chord facet `tc` on `p 4 - p 0`, 4 ridge edges with opposing facet signs,
an interior vertex `I` off all facets, and middle vertex `M` on the chord `p 4 - p 0`,
the rim is strictly convex (`StrictConvex5`) and vertex `I` is strictly interior. -/
theorem fiveRim_of_signs {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (p : ZMod 5 → Fin 7) (I M : Fin 7)
    (t01 t01' t12 t12' t23 t23' t34 t34' tc : Fin 9)
    -- Edge-on chord on facet tc:
    (hP4_c : p 4 ∈ s0x_S24 tc) (hP0_c : p 0 ∈ s0x_S24 tc)
    (hN_c : ⟪F.N tc, u⟫ = 0)
    -- Ridge edges with opposing facet signs:
    (hP0_01 : p 0 ∈ s0x_S24 t01 ∧ p 0 ∈ s0x_S24 t01')
    (hP1_01 : p 1 ∈ s0x_S24 t01 ∧ p 1 ∈ s0x_S24 t01')
    (h_opp01 : ⟪F.N t01, u⟫ < 0 ∧ 0 < ⟪F.N t01', u⟫)
    (hP1_12 : p 1 ∈ s0x_S24 t12 ∧ p 1 ∈ s0x_S24 t12')
    (hP2_12 : p 2 ∈ s0x_S24 t12 ∧ p 2 ∈ s0x_S24 t12')
    (h_opp12 : ⟪F.N t12, u⟫ < 0 ∧ 0 < ⟪F.N t12', u⟫)
    (hP2_23 : p 2 ∈ s0x_S24 t23 ∧ p 2 ∈ s0x_S24 t23')
    (hP3_23 : p 3 ∈ s0x_S24 t23 ∧ p 3 ∈ s0x_S24 t23')
    (h_opp23 : ⟪F.N t23, u⟫ < 0 ∧ 0 < ⟪F.N t23', u⟫)
    (hP3_34 : p 3 ∈ s0x_S24 t34 ∧ p 3 ∈ s0x_S24 t34')
    (hP4_34 : p 4 ∈ s0x_S24 t34 ∧ p 4 ∈ s0x_S24 t34')
    (h_opp34 : ⟪F.N t34, u⟫ < 0 ∧ 0 < ⟪F.N t34', u⟫)
    -- Non-zero cross products along all edges:
    (hne_01 : cross u (x (p 1) - x (p 0)) ≠ 0)
    (hne_12 : cross u (x (p 2) - x (p 1)) ≠ 0)
    (hne_23 : cross u (x (p 3) - x (p 2)) ≠ 0)
    (hne_34 : cross u (x (p 4) - x (p 3)) ≠ 0)
    (hne_40 : cross u (x (p 0) - x (p 4)) ≠ 0)
    -- Interior point I off the facets:
    (hI_c : I ∉ s0x_S24 tc)
    (hI_01 : I ∉ s0x_S24 t01 ∨ I ∉ s0x_S24 t01')
    (hI_12 : I ∉ s0x_S24 t12 ∨ I ∉ s0x_S24 t12')
    (hI_23 : I ∉ s0x_S24 t23 ∨ I ∉ s0x_S24 t23')
    (hI_34 : I ∉ s0x_S24 t34 ∨ I ∉ s0x_S24 t34')
    -- Vertex separation for ridges:
    (hP2_off01 : p 2 ∉ s0x_S24 t01 ∨ p 2 ∉ s0x_S24 t01')
    (hP3_off12 : p 3 ∉ s0x_S24 t12 ∨ p 3 ∉ s0x_S24 t12')
    (hP4_off23 : p 4 ∉ s0x_S24 t23 ∨ p 4 ∉ s0x_S24 t23')
    (hP0_off34 : p 0 ∉ s0x_S24 t34 ∨ p 0 ∉ s0x_S24 t34')
    (hP1_offc : p 1 ∉ s0x_S24 tc) :
    ∃ ρ : ℝ, ρ ≠ 0 ∧
      StrictConvex5 (fun i => x (p i)) u ρ ∧
      (∀ i : ZMod 5,
        0 < ρ * det3 (x (p (i + 1)) - x (p i))
          (x I - x (p i)) u) := by
  sorry

/-- On the window `t ∈ (max(1/ω4, t6), ω3)`, the rim `(0, 4, 6, 3, 2)` satisfies strict convexity
and vertex 5 interior positioning with `ρ = -1`. -/
theorem fiveRim_04632_of_window {t : ℝ}
    (h_w4 : inv_omega4_012 F < t) (h_t6 : t6_012 F < t) (h_w3 : t < omega3_012 F)
    (hne_04 : cross (u0 x t) (x 4 - x 0) ≠ 0)
    (hne_46 : cross (u0 x t) (x 6 - x 4) ≠ 0)
    (hne_63 : cross (u0 x t) (x 3 - x 6) ≠ 0)
    (hne_32 : cross (u0 x t) (x 2 - x 3) ≠ 0)
    (hne_20 : cross (u0 x t) (x 0 - x 2) ≠ 0) :
    (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      0 < (-1 : ℝ) * det3 (x (rim012 (i + 1)) - x (rim012 i))
        (x (rim012 j) - x (rim012 i)) (u0 x t)) ∧
    (∀ i : ZMod 5,
      0 < (-1 : ℝ) * det3 (x (rim012 (i + 1)) - x (rim012 i))
        (x 5 - x (rim012 i)) (u0 x t)) := by
  sorry

-- =========================================================================
-- AL3: The Level-Chord Leaves q012_LC_plus and q012_LC_minus
-- =========================================================================

/-- Level-chord parameter `t_LC` on facet 0 (`012`), equating depths `⟪x 0, u0(t)⟫ = ⟪x 2, u0(t)⟫`. -/
noncomputable def t_LC (x : Fin 7 → ℝ³) : ℝ :=
  - ⟪x 0 - x 2, x 0 - x 1⟫ / ⟪x 0 - x 2, x 2 - x 1⟫

/-- Level-chord view direction `u_LC := u0(t_LC)`. -/
noncomputable def u_LC (x : Fin 7 → ℝ³) : ℝ³ := u0 x (t_LC x)

/-- Perturbation direction along the chord edge: `d_chord = x 2 - x 1`. -/
def d_chord (x : Fin 7 → ℝ³) : ℝ³ := x 2 - x 1

/-- At `u_LC`, vertices 0 and 2 have identical depth: `⟪x 0, u_LC x⟫ = ⟪x 2, u_LC x⟫`. -/
theorem inner_diff_u_LC (hdenom : ⟪x 0 - x 2, x 2 - x 1⟫ ≠ 0) :
    ⟪x 0, u_LC x⟫ = ⟪x 2, u_LC x⟫ := by
  have : ⟪x 0 - x 2, u_LC x⟫ = 0 := by
    dsimp [u_LC, u0, t_LC]
    rw [inner_add_right, real_inner_smul_right]
    have : - ⟪x 0 - x 2, x 0 - x 1⟫ / ⟪x 0 - x 2, x 2 - x 1⟫ * ⟪x 0 - x 2, x 2 - x 1⟫ =
        - ⟪x 0 - x 2, x 0 - x 1⟫ := by
      exact div_mul_cancel₀ (- ⟪x 0 - x 2, x 0 - x 1⟫) hdenom
    rw [this]
    ring
  rw [← sub_eq_zero]
  rw [← inner_sub_left]
  exact this

/-- **Theorem LC-K5 (Plus): Level-chord leaf with `u_LC + ε • d`.**
Under the window condition `t_LC ∈ (max(1/ω4, t6), ω3)`, frame-free `c3, c4 < 1`
(vertex 6 farthest below facet 0), and depth condition `⟪x 4, u_LC⟫ < ⟪x 0, u_LC⟫`,
the perturbed view `u_LC + ε • d` yields `FaceChordView F 0`. -/
theorem q012_LC_plus (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x)
    -- Window condition:
    (h_w4 : inv_omega4_012 F < t_LC x)
    (h_t6 : t6_012 F < t_LC x)
    (h_w3 : t_LC x < omega3_012 F)
    -- Frame-free c3, c4 < 1: vertex 6 strictly minimizes F.f 0 among off-facet rim vertices:
    (h_c3 : F.f 0 (x 6) < F.f 0 (x 3))
    (h_c4 : F.f 0 (x 6) < F.f 0 (x 4))
    -- Depth condition:
    (h_depth : ⟪x 4, u_LC x⟫ < ⟪x 0, u_LC x⟫)
    -- Non-degeneracy:
    (hdenom : ⟪x 0 - x 2, x 2 - x 1⟫ ≠ 0)
    (hdir : ⟪x 0 - x 2, d_chord x⟫ ≠ 0)
    (hne_20 : cross (u_LC x) (x 0 - x 2) ≠ 0)
    (hne_04 : cross (u_LC x) (x 4 - x 0) ≠ 0)
    (hne_46 : cross (u_LC x) (x 6 - x 4) ≠ 0)
    (hne_63 : cross (u_LC x) (x 3 - x 6) ≠ 0)
    (hne_32 : cross (u_LC x) (x 2 - x 3) ≠ 0)
    (hoff : ⟪F.N 0, cross (x 0 - x 2) (x 6 - x 2)⟫ ≠ 0 ∨
      ⟪x 6 - x 2, x 0 - x 2⟫ < 0 ∨ ⟪x 6 - x 0, x 2 - x 0⟫ < 0) :
    FaceChordView F 0 := by
  sorry

/-- **Theorem LC-K5 (Minus): Level-chord leaf with `u_LC - ε • d`.**
Under the window condition `t_LC ∈ (max(1/ω4, t6), ω3)`, frame-free `c3, c4 < 1`
(vertex 6 farthest below facet 0), and depth condition `⟪x 3, u_LC⟫ < ⟪x 0, u_LC⟫`,
the perturbed view `u_LC - ε • d` yields `FaceChordView F 0`. -/
theorem q012_LC_minus (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x)
    -- Window condition:
    (h_w4 : inv_omega4_012 F < t_LC x)
    (h_t6 : t6_012 F < t_LC x)
    (h_w3 : t_LC x < omega3_012 F)
    -- Frame-free c3, c4 < 1: vertex 6 strictly minimizes F.f 0 among off-facet rim vertices:
    (h_c3 : F.f 0 (x 6) < F.f 0 (x 3))
    (h_c4 : F.f 0 (x 6) < F.f 0 (x 4))
    -- Depth condition:
    (h_depth : ⟪x 3, u_LC x⟫ < ⟪x 0, u_LC x⟫)
    -- Non-degeneracy:
    (hdenom : ⟪x 0 - x 2, x 2 - x 1⟫ ≠ 0)
    (hdir : ⟪x 0 - x 2, d_chord x⟫ ≠ 0)
    (hne_20 : cross (u_LC x) (x 0 - x 2) ≠ 0)
    (hne_04 : cross (u_LC x) (x 4 - x 0) ≠ 0)
    (hne_46 : cross (u_LC x) (x 6 - x 4) ≠ 0)
    (hne_63 : cross (u_LC x) (x 3 - x 6) ≠ 0)
    (hne_32 : cross (u_LC x) (x 2 - x 3) ≠ 0)
    (hoff : ⟪F.N 0, cross (x 0 - x 2) (x 6 - x 2)⟫ ≠ 0 ∨
      ⟪x 6 - x 2, x 0 - x 2⟫ < 0 ∨ ⟪x 6 - x 0, x 2 - x 0⟫ < 0) :
    FaceChordView F 0 := by
  sorry

end Minimality.T24.R012
