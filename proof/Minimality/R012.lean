module

public import Minimality.FaceChordFac
public import Minimality.SplitTie
public import Minimality.FiveRim
public import Minimality.Q45Signs
public import Minimality.Q45Orient
public import Minimality.CornerU
public import Minimality.RimCell
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
  dsimp [u0, lambda4, omega4_012]
  rw [inner_add_right, real_inner_smul_right]
  have h0 : ⟪F.N 4, x 0 - x 1⟫ = - F.f 4 (x 1) := by
    have := (F.hN 4 (x 0) (x 1)).symm
    rw [F.zero 4 0 (by decide), zero_sub] at this
    exact this
  have hlam : - F.f 4 (x 1) ≠ 0 := (lambda4_pos F).ne'
  rw [h0]
  have h_div : (- ⟪F.N 4, x 2 - x 1⟫ / - F.f 4 (x 1)) * (- F.f 4 (x 1)) = - ⟪F.N 4, x 2 - x 1⟫ :=
    div_mul_cancel₀ _ hlam
  calc
    - F.f 4 (x 1) + t * ⟪F.N 4, x 2 - x 1⟫ =
      - F.f 4 (x 1) - t * (- ⟪F.N 4, x 2 - x 1⟫) := by ring
    _ = - F.f 4 (x 1) - t * ((- ⟪F.N 4, x 2 - x 1⟫ / - F.f 4 (x 1)) * (- F.f 4 (x 1))) := by rw [h_div]
    _ = - F.f 4 (x 1) * (1 - (- ⟪F.N 4, x 2 - x 1⟫ / - F.f 4 (x 1)) * t) := by ring

/-- Facet 7 (`236`) linear formula: `⟪F.N 7, u0 x t⟫ = lambda7 F * (t - omega3_012 F)`. -/
theorem inner_N7_u0 (t : ℝ) :
    ⟪F.N 7, u0 x t⟫ = lambda7 F * (t - omega3_012 F) := by
  dsimp [u0, lambda7, omega3_012]
  rw [inner_add_right, real_inner_smul_right]
  have h2 : ⟪F.N 7, x 2 - x 1⟫ = - F.f 7 (x 1) := by
    have := (F.hN 7 (x 2) (x 1)).symm
    rw [F.zero 7 2 (by decide), zero_sub] at this
    exact this
  have hlam : - F.f 7 (x 1) ≠ 0 := (lambda7_pos F).ne'
  rw [h2]
  have h_div : (- ⟪F.N 7, x 0 - x 1⟫ / - F.f 7 (x 1)) * (- F.f 7 (x 1)) = - ⟪F.N 7, x 0 - x 1⟫ :=
    div_mul_cancel₀ _ hlam
  calc
    ⟪F.N 7, x 0 - x 1⟫ + t * (- F.f 7 (x 1)) =
      - (- ⟪F.N 7, x 0 - x 1⟫) + t * (- F.f 7 (x 1)) := by ring
    _ = - ((- ⟪F.N 7, x 0 - x 1⟫ / - F.f 7 (x 1)) * (- F.f 7 (x 1))) + t * (- F.f 7 (x 1)) := by rw [h_div]
    _ = - F.f 7 (x 1) * (t - (- ⟪F.N 7, x 0 - x 1⟫ / - F.f 7 (x 1))) := by ring

/-- Facet 6 (`235`) affine formula: `⟪F.N 6, u0 x t⟫ = lambda6 F * (t - t6_012 F)`. -/
theorem inner_N6_u0 (t : ℝ) :
    ⟪F.N 6, u0 x t⟫ = lambda6 F * (t - t6_012 F) := by
  dsimp [u0, lambda6, t6_012]
  rw [inner_add_right, real_inner_smul_right]
  have h2 : ⟪F.N 6, x 2 - x 1⟫ = - F.f 6 (x 1) := by
    have := (F.hN 6 (x 2) (x 1)).symm
    rw [F.zero 6 2 (by decide), zero_sub] at this
    exact this
  have hlam : - F.f 6 (x 1) ≠ 0 := (lambda6_pos F).ne'
  rw [h2]
  have h_div : (- ⟪F.N 6, x 0 - x 1⟫ / - F.f 6 (x 1)) * (- F.f 6 (x 1)) = - ⟪F.N 6, x 0 - x 1⟫ :=
    div_mul_cancel₀ _ hlam
  calc
    ⟪F.N 6, x 0 - x 1⟫ + t * (- F.f 6 (x 1)) =
      - (- ⟪F.N 6, x 0 - x 1⟫) + t * (- F.f 6 (x 1)) := by ring
    _ = - ((- ⟪F.N 6, x 0 - x 1⟫ / - F.f 6 (x 1)) * (- F.f 6 (x 1))) + t * (- F.f 6 (x 1)) := by rw [h_div]
    _ = - F.f 6 (x 1) * (t - (- ⟪F.N 6, x 0 - x 1⟫ / - F.f 6 (x 1))) := by ring

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

/-- Distinct points on a polyhedron from differing facet membership. -/
lemma pt_ne_of_facet {N nf : ℕ} {S : Fin nf → Finset (Fin N)} {x : Fin N → ℝ³}
    (F : S0xFac nf S x) (t : Fin nf) (P Q : Fin N) (hP : P ∈ S t) (hQ : Q ∉ S t) :
    x Q - x P ≠ 0 := by
  intro h
  have h1 := F.zero t P hP
  have h2 := F.neg t Q hQ
  have : x Q = x P := sub_eq_zero.mp h
  rw [this, h1] at h2
  exact lt_irrefl 0 h2

/-- Non-zero cross product of view with edge vector from non-zero facet inner product. -/
lemma cross_ne_zero_of_facet_two {N nf : ℕ} {S : Fin nf → Finset (Fin N)} {x : Fin N → ℝ³}
    (F : S0xFac nf S x) (t : Fin nf) (P Q : Fin N) (hP : P ∈ S t) (hQ : Q ∈ S t)
    (he : x Q - x P ≠ 0) {u : ℝ³} (h_inner : ⟪F.N t, u⟫ ≠ 0) :
    cross u (x Q - x P) ≠ 0 := by
  intro hcr
  have hcr' : cross (x Q - x P) u = 0 := by
    rw [show cross (x Q - x P) u = - cross u (x Q - x P) by ext j; fin_cases j <;> simp [cross] <;> ring, hcr, neg_zero]
  obtain ⟨k, hk⟩ : ∃ k : ℝ, u = k • (x Q - x P) := ⟨_, eq_smul_of_cross_eq_zero he hcr'⟩
  have hz : ⟪F.N t, x Q - x P⟫ = 0 := by
    have := (F.hN t (x Q) (x P)).symm
    rw [F.zero t Q hQ, F.zero t P hP, sub_self] at this
    exact this
  have h0 : ⟪F.N t, u⟫ = 0 := by
    rw [hk, real_inner_smul_right, hz, mul_zero]
  exact h_inner h0

/-- Vertex 1 is a chord middle over `2 → 0` along `u0(t)` for all `t > 0`. -/
lemma chord_middle_012 {t : ℝ} (ht : 0 < t) :
    ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      x 1 = x 2 + s • (x 0 - x 2) + δ • (u0 x t) := by
  refine ⟨(1 + t)⁻¹, - (1 + t)⁻¹, ?_, ?_, ?_, ?_⟩
  · positivity
  · rw [inv_lt_one_iff₀]
    right; linarith
  · have : (1 + t)⁻¹ ≠ 0 := by positivity
    exact neg_ne_zero.mpr this
  · dsimp [u0]
    ext j
    have ht1 : 1 + t ≠ 0 := by positivity
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    set x0 := (x 0) j
    set x1 := (x 1) j
    set x2 := (x 2) j
    symm
    calc x2 + (1 + t)⁻¹ * (x0 - x2) + - (1 + t)⁻¹ * ((x0 - x1) + t * (x2 - x1))
      _ = x2 + (1 + t)⁻¹ * (x0 - x2 - (x0 - x1 + t * (x2 - x1))) := by ring
      _ = x2 + (1 + t)⁻¹ * ((1 + t) * (x1 - x2)) := by ring_nf
      _ = x2 + (1 + t)⁻¹ * (1 + t) * (x1 - x2) := by ring
      _ = x2 + 1 * (x1 - x2) := by rw [inv_mul_cancel₀ ht1]
      _ = x1 := by ring

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
an interior vertex `I` off all facets,
the rim is strictly convex (`StrictConvex5`) and vertex `I` is strictly interior. -/
theorem fiveRim_of_signs {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (p : ZMod 5 → Fin 7) (I : Fin 7)
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
    -- Off-facet conditions for ridges and chord:
    (hP2_off01 : p 2 ∉ s0x_S24 t01 ∨ p 2 ∉ s0x_S24 t01')
    (hP3_off01 : p 3 ∉ s0x_S24 t01 ∨ p 3 ∉ s0x_S24 t01')
    (hP4_off01 : p 4 ∉ s0x_S24 t01 ∨ p 4 ∉ s0x_S24 t01')
    (hI_01 : I ∉ s0x_S24 t01 ∨ I ∉ s0x_S24 t01')
    (hP0_off12 : p 0 ∉ s0x_S24 t12 ∨ p 0 ∉ s0x_S24 t12')
    (hP3_off12 : p 3 ∉ s0x_S24 t12 ∨ p 3 ∉ s0x_S24 t12')
    (hP4_off12 : p 4 ∉ s0x_S24 t12 ∨ p 4 ∉ s0x_S24 t12')
    (hI_12 : I ∉ s0x_S24 t12 ∨ I ∉ s0x_S24 t12')
    (hP0_off23 : p 0 ∉ s0x_S24 t23 ∨ p 0 ∉ s0x_S24 t23')
    (hP1_off23 : p 1 ∉ s0x_S24 t23 ∨ p 1 ∉ s0x_S24 t23')
    (hP4_off23 : p 4 ∉ s0x_S24 t23 ∨ p 4 ∉ s0x_S24 t23')
    (hI_23 : I ∉ s0x_S24 t23 ∨ I ∉ s0x_S24 t23')
    (hP0_off34 : p 0 ∉ s0x_S24 t34 ∨ p 0 ∉ s0x_S24 t34')
    (hP1_off34 : p 1 ∉ s0x_S24 t34 ∨ p 1 ∉ s0x_S24 t34')
    (hP2_off34 : p 2 ∉ s0x_S24 t34 ∨ p 2 ∉ s0x_S24 t34')
    (hI_34 : I ∉ s0x_S24 t34 ∨ I ∉ s0x_S24 t34')
    (hP1_offc : p 1 ∉ s0x_S24 tc)
    (hP2_offc : p 2 ∉ s0x_S24 tc)
    (hP3_offc : p 3 ∉ s0x_S24 tc)
    (hI_c : I ∉ s0x_S24 tc) :
    ∃ ρ : ℝ, ρ ≠ 0 ∧
      StrictConvex5 (fun i => x (p i)) u ρ ∧
      (∀ i : ZMod 5,
        0 < ρ * det3 (x (p (i + 1)) - x (p i))
          (x I - x (p i)) u) := by
  obtain ⟨σ₀, hσ₀_ne, hσ₀⟩ := det3_sign_ridge F t01 t01' (p 0) (p 1) hP0_01 hP1_01 u h_opp01 hne_01
  obtain ⟨σ₁, hσ₁_ne, hσ₁⟩ := det3_sign_ridge F t12 t12' (p 1) (p 2) hP1_12 hP2_12 u h_opp12 hne_12
  obtain ⟨σ₂, hσ₂_ne, hσ₂⟩ := det3_sign_ridge F t23 t23' (p 2) (p 3) hP2_23 hP3_23 u h_opp23 hne_23
  obtain ⟨σ₃, hσ₃_ne, hσ₃⟩ := det3_sign_ridge F t34 t34' (p 3) (p 4) hP3_34 hP4_34 u h_opp34 hne_34
  obtain ⟨σ₄, hσ₄_ne, hσ₄⟩ := det3_sign_edgeOn F tc (p 4) (p 0) hP4_c hP0_c u hN_c hne_40

  have hcyc01 : det3 (x (p 1) - x (p 0)) (x (p 2) - x (p 0)) u = det3 (x (p 2) - x (p 1)) (x (p 0) - x (p 1)) u :=
    det3_cycle_triangle (x (p 0)) (x (p 1)) (x (p 2)) u
  have hcyc12 : det3 (x (p 2) - x (p 1)) (x (p 3) - x (p 1)) u = det3 (x (p 3) - x (p 2)) (x (p 1) - x (p 2)) u :=
    det3_cycle_triangle (x (p 1)) (x (p 2)) (x (p 3)) u
  have hcyc23 : det3 (x (p 3) - x (p 2)) (x (p 4) - x (p 2)) u = det3 (x (p 4) - x (p 3)) (x (p 2) - x (p 3)) u :=
    det3_cycle_triangle (x (p 2)) (x (p 3)) (x (p 4)) u
  have hcyc34 : det3 (x (p 4) - x (p 3)) (x (p 0) - x (p 3)) u = det3 (x (p 0) - x (p 4)) (x (p 3) - x (p 4)) u :=
    det3_cycle_triangle (x (p 3)) (x (p 4)) (x (p 0)) u

  have h0_p2 : 0 < σ₀ * det3 (x (p 1) - x (p 0)) (x (p 2) - x (p 0)) u := hσ₀ (p 2) hP2_off01
  have h1_p0 : 0 < σ₁ * det3 (x (p 2) - x (p 1)) (x (p 0) - x (p 1)) u := hσ₁ (p 0) hP0_off12
  have h1_p0' : 0 < σ₁ * det3 (x (p 1) - x (p 0)) (x (p 2) - x (p 0)) u := by rw [hcyc01]; exact h1_p0
  have hσ01 : 0 < σ₀ * σ₁ := sign_prod h0_p2 h1_p0'

  have h1_p3 : 0 < σ₁ * det3 (x (p 2) - x (p 1)) (x (p 3) - x (p 1)) u := hσ₁ (p 3) hP3_off12
  have h2_p1 : 0 < σ₂ * det3 (x (p 3) - x (p 2)) (x (p 1) - x (p 2)) u := hσ₂ (p 1) hP1_off23
  have h2_p1' : 0 < σ₂ * det3 (x (p 2) - x (p 1)) (x (p 3) - x (p 1)) u := by rw [hcyc12]; exact h2_p1
  have hσ12 : 0 < σ₁ * σ₂ := sign_prod h1_p3 h2_p1'
  have hσ02 : 0 < σ₀ * σ₂ := sign_transfer hσ01 hσ12

  have h2_p4 : 0 < σ₂ * det3 (x (p 3) - x (p 2)) (x (p 4) - x (p 2)) u := hσ₂ (p 4) hP4_off23
  have h3_p2 : 0 < σ₃ * det3 (x (p 4) - x (p 3)) (x (p 2) - x (p 3)) u := hσ₃ (p 2) hP2_off34
  have h3_p2' : 0 < σ₃ * det3 (x (p 3) - x (p 2)) (x (p 4) - x (p 2)) u := by rw [hcyc23]; exact h3_p2
  have hσ23 : 0 < σ₂ * σ₃ := sign_prod h2_p4 h3_p2'
  have hσ03 : 0 < σ₀ * σ₃ := sign_transfer hσ02 hσ23

  have h3_p0 : 0 < σ₃ * det3 (x (p 4) - x (p 3)) (x (p 0) - x (p 3)) u := hσ₃ (p 0) hP0_off34
  have h4_p3 : 0 < σ₄ * det3 (x (p 0) - x (p 4)) (x (p 3) - x (p 4)) u := hσ₄ (p 3) hP3_offc
  have h4_p3' : 0 < σ₄ * det3 (x (p 4) - x (p 3)) (x (p 0) - x (p 3)) u := by rw [hcyc34]; exact h4_p3
  have hσ34 : 0 < σ₃ * σ₄ := sign_prod h3_p0 h4_p3'
  have hσ04 : 0 < σ₀ * σ₄ := sign_transfer hσ03 hσ34

  refine ⟨σ₀, hσ₀_ne, ?_, ?_⟩
  · intro i j hj1 hj2
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl
    · exact False.elim (hj1 rfl)
    · exact False.elim (hj2 rfl)
    · exact h0_p2
    · exact hσ₀ (p 3) hP3_off01
    · exact hσ₀ (p 4) hP4_off01
    · exact sign_transfer hσ01 h1_p0
    · exact False.elim (hj1 rfl)
    · exact False.elim (hj2 rfl)
    · exact sign_transfer hσ01 h1_p3
    · exact sign_transfer hσ01 (hσ₁ (p 4) hP4_off12)
    · exact sign_transfer hσ02 (hσ₂ (p 0) hP0_off23)
    · exact sign_transfer hσ02 h2_p1
    · exact False.elim (hj1 rfl)
    · exact False.elim (hj2 rfl)
    · exact sign_transfer hσ02 h2_p4
    · exact sign_transfer hσ03 h3_p0
    · exact sign_transfer hσ03 (hσ₃ (p 1) hP1_off34)
    · exact sign_transfer hσ03 h3_p2
    · exact False.elim (hj1 rfl)
    · exact False.elim (hj2 rfl)
    · exact False.elim (hj2 rfl)
    · exact sign_transfer hσ04 (hσ₄ (p 1) hP1_offc)
    · exact sign_transfer hσ04 (hσ₄ (p 2) hP2_offc)
    · exact sign_transfer hσ04 h4_p3
    · exact False.elim (hj1 rfl)
  · intro i
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
    · exact hσ₀ I hI_01
    · exact sign_transfer hσ01 (hσ₁ I hI_12)
    · exact sign_transfer hσ02 (hσ₂ I hI_23)
    · exact sign_transfer hσ03 (hσ₃ I hI_34)
    · exact sign_transfer hσ04 (hσ₄ I hI_c)

/-- On the window `t ∈ (max(1/ω4, t6), ω3)`, the rim `(0, 4, 6, 3, 2)` satisfies strict convexity
and vertex 5 interior positioning. -/
theorem fiveRim_04632_of_window {t : ℝ}
    (ht_pos : 0 < t)
    (hN4_neg : ⟪F.N 4, u0 x t⟫ < 0)
    (hN7_neg : ⟪F.N 7, u0 x t⟫ < 0)
    (hN6_pos : 0 < ⟪F.N 6, u0 x t⟫)
    (hN3_pos : 0 < ⟪F.N 3, u0 x t⟫)
    (hN8_pos : 0 < ⟪F.N 8, u0 x t⟫) :
    ∃ ρ : ℝ, ρ ≠ 0 ∧
      StrictConvex5 (fun i => x (rim012 i)) (u0 x t) ρ ∧
      (∀ i : ZMod 5,
        0 < ρ * det3 (x (rim012 (i + 1)) - x (rim012 i))
          (x 5 - x (rim012 i)) (u0 x t)) := by
  have hne_04 : cross (u0 x t) (x 4 - x 0) ≠ 0 :=
    cross_ne_zero_of_facet_sign F 4 0 4 (by decide) (by decide) hN4_neg.ne 0 (by decide) (by decide)
  have hne_46 : cross (u0 x t) (x 6 - x 4) ≠ 0 :=
    cross_ne_zero_of_facet_sign F 4 4 6 (by decide) (by decide) hN4_neg.ne 3 (by decide) (by decide)
  have hne_63 : cross (u0 x t) (x 3 - x 6) ≠ 0 :=
    cross_ne_zero_of_facet_sign F 7 6 3 (by decide) (by decide) hN7_neg.ne 4 (by decide) (by decide)
  have hne_32 : cross (u0 x t) (x 2 - x 3) ≠ 0 :=
    cross_ne_zero_of_facet_sign F 7 3 2 (by decide) (by decide) hN7_neg.ne 3 (by decide) (by decide)
  have hN2_pos : 0 < ⟪F.N 2, u0 x t⟫ := by
    rw [inner_N2_u0]
    have h1 : 0 < lambda2 F := lambda2_pos F
    have h2 : 0 < 1 + t := by linarith
    exact mul_pos h1 h2
  have hne_20 : cross (u0 x t) (x 0 - x 2) ≠ 0 :=
    cross_ne_zero_of_facet_sign F 2 2 0 (by decide) (by decide) hN2_pos.ne' 7 (by decide) (by decide)
  refine fiveRim_of_signs F (u := u0 x t) rim012 5 4 3 4 8 7 8 7 6 0
    (by decide) (by decide) (inner_N0_u0 F t)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ ⟨hN4_neg, hN3_pos⟩
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ ⟨hN4_neg, hN8_pos⟩
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ ⟨hN7_neg, hN8_pos⟩
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ ⟨hN7_neg, hN6_pos⟩
    hne_04 hne_46 hne_63 hne_32 hne_20
    (Or.inr (by decide)) (Or.inl (by decide)) (Or.inl (by decide)) (Or.inl (by decide))
    (Or.inr (by decide)) (Or.inl (by decide)) (Or.inl (by decide)) (Or.inl (by decide))
    (Or.inl (by decide)) (Or.inl (by decide)) (Or.inr (by decide)) (Or.inl (by decide))
    (Or.inl (by decide)) (Or.inl (by decide)) (Or.inr (by decide)) (Or.inl (by decide))
    (by decide) (by decide) (by decide) (by decide)

-- =========================================================================
-- AL3: The Level-Chord Leaves q012_LC_plus and q012_LC_minus
-- =========================================================================

lemma eventually_lt_of_continuous {f : ℝ → ℝ} (hf : Continuous f) {c : ℝ} (h : c < f 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), c < f ε :=
  (hf.continuousAt.eventually_const_lt h).filter_mono nhdsWithin_le_nhds

lemma eventually_gt_of_continuous {f : ℝ → ℝ} (hf : Continuous f) {c : ℝ} (h : f 0 < c) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), f ε < c :=
  (hf.continuousAt.eventually_lt_const h).filter_mono nhdsWithin_le_nhds

/-- Level-chord parameter `t_LC` on facet 0 (`012`), equating depths `⟪x 0, u0(t)⟫ = ⟪x 2, u0(t)⟫`. -/
noncomputable def t_LC (x : Fin 7 → ℝ³) : ℝ :=
  - ⟪x 0 - x 2, x 0 - x 1⟫ / ⟪x 0 - x 2, x 2 - x 1⟫

/-- Level-chord view direction `u_LC := u0(t_LC)`. -/
noncomputable def u_LC (x : Fin 7 → ℝ³) : ℝ³ := u0 x (t_LC x)

/-- Perturbation direction along the chord edge: `d_chord = x 2 - x 1`. -/
def d_chord (x : Fin 7 → ℝ³) : ℝ³ := x 2 - x 1

/-- Codimension-1 special locus on 012 at `u_LC`: pairwise depth equalities among rim vertices
`{0, 4, 6, 3}` other than the intended level-chord tie `⟪x 0, u_LC⟫ = ⟪x 2, u_LC⟫`. -/
def R012Special (x : Fin 7 → ℝ³) : Prop :=
  ⟪x 4, u_LC x⟫ = ⟪x 0, u_LC x⟫ ∨ ⟪x 6, u_LC x⟫ = ⟪x 0, u_LC x⟫ ∨ ⟪x 3, u_LC x⟫ = ⟪x 0, u_LC x⟫ ∨
  ⟪x 4, u_LC x⟫ = ⟪x 6, u_LC x⟫ ∨ ⟪x 4, u_LC x⟫ = ⟪x 3, u_LC x⟫ ∨ ⟪x 6, u_LC x⟫ = ⟪x 3, u_LC x⟫

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

lemma u0_add (x : Fin 7 → ℝ³) (t δ : ℝ) :
    u0 x (t + δ) = u0 x t + δ • (x 2 - x 1) := by
  dsimp [u0]
  rw [add_smul]
  abel

lemma inner_u0_add (N : ℝ³) (x : Fin 7 → ℝ³) (t δ : ℝ) :
    ⟪N, u0 x (t + δ)⟫ = ⟪N, u0 x t⟫ + δ * ⟪N, x 2 - x 1⟫ := by
  rw [u0_add, inner_add_right, real_inner_smul_right]

lemma u0_t_LC_add (x : Fin 7 → ℝ³) (σ ε : ℝ) :
    u0 x (t_LC x + σ * ε) = u_LC x + (σ * ε) • d_chord x := by
  exact u0_add x (t_LC x) (σ * ε)

/-- Farthest-vertex choice for facet 0: a unique minimiser `w` of `F.f 0` among the rim vertices
`3, 4, 6` off facet 0, with the matching `hoff` for the chord `0 - 2`. -/
def FarOff012 (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ w : Fin 7, (w = 3 ∨ w = 4 ∨ w = 6) ∧
    (∀ m : Fin 7, (m = 3 ∨ m = 4 ∨ m = 6) → m ≠ w → F.f 0 (x w) < F.f 0 (x m)) ∧
    (⟪F.N 0, cross (x 0 - x 2) (x w - x 2)⟫ ≠ 0 ∨
      ⟪x w - x 2, x 0 - x 2⟫ < 0 ∨ ⟪x w - x 0, x 2 - x 0⟫ < 0)

lemma farOff012_six (F : S0xFac 9 s0x_S24 x)
    (h_c3 : F.f 0 (x 6) < F.f 0 (x 3)) (h_c4 : F.f 0 (x 6) < F.f 0 (x 4))
    (hoff : ⟪F.N 0, cross (x 0 - x 2) (x 6 - x 2)⟫ ≠ 0 ∨
      ⟪x 6 - x 2, x 0 - x 2⟫ < 0 ∨ ⟪x 6 - x 0, x 2 - x 0⟫ < 0) : FarOff012 F := by
  refine ⟨6, Or.inr (Or.inr rfl), ?_, hoff⟩
  intro m hm hne
  rcases hm with rfl | rfl | rfl
  · exact h_c3
  · exact h_c4
  · exact absurd rfl hne

theorem exists_faceChordView_012_gen (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x)
    (hfar : FarOff012 F)
    (h_view : ∃ t : ℝ, 0 < t ∧
      (∃ ρ : ℝ, ρ ≠ 0 ∧ StrictConvex5 (fun i => x (rim012 i)) (u0 x t) ρ ∧
        (∀ i : ZMod 5, 0 < ρ * det3 (x (rim012 (i + 1)) - x (rim012 i)) (x 5 - x (rim012 i)) (u0 x t))) ∧
      Function.Injective (fun i => ⟪x (rim012 i), u0 x t⟫) ∧
      IsCyclicUnimodal (fun i => ⟪x (rim012 i), u0 x t⟫)) :
    FaceChordView F 0 := by
  obtain ⟨w, hw, hmin, hoff⟩ := hfar
  obtain ⟨t, ht_pos, ⟨ρ, hρ_ne, hcyc, hin5⟩, hinj, huni⟩ := h_view
  set u := u0 x t
  obtain ⟨wi, hwi, hwr⟩ : ∃ wi : ZMod 5, (wi = 1 ∨ wi = 2 ∨ wi = 3) ∧ rim012 wi = w := by
    rcases hw with rfl | rfl | rfl
    · exact ⟨3, by decide, rfl⟩
    · exact ⟨1, by decide, rfl⟩
    · exact ⟨2, by decide, rfl⟩
  subst hwr
  refine ⟨u, 5, by infer_instance, rim012, 4, wi, ρ, ?_, by decide, by decide, by decide, hρ_ne,
    hcyc, ?_, ?_, hinj, Or.inl (strictUnimodal_of_cyclic (by omega) huni), (by rcases hwi with rfl | rfl | rfl <;> decide), ?_, hoff⟩
  · exact inner_N0_u0 F t
  · intro q hq0 hqr i
    have hq5 : q = 5 := by
      fin_cases q
      · revert hq0; decide
      · revert hq0; decide
      · revert hq0; decide
      · exfalso; exact hqr 3 rfl
      · exfalso; exact hqr 1 rfl
      · rfl
      · exfalso; exact hqr 2 rfl
    subst hq5
    exact hin5 i
  · intro q hq0 hqr
    have hq1 : q = 1 := by
      fin_cases q
      · exfalso; exact hqr 0 rfl
      · rfl
      · exfalso; exact hqr 4 rfl
      · revert hq0; decide
      · revert hq0; decide
      · revert hq0; decide
      · revert hq0; decide
    subst hq1
    obtain ⟨s, δ, hs0, hs1, hδ, heq⟩ := chord_middle_012 (x := x) ht_pos
    refine ⟨s, δ, hs0, hs1, hδ, ?_⟩
    show x 1 = x (rim012 4) + s • (x (rim012 (4 + 1)) - x (rim012 4)) + δ • u
    change x 1 = x 2 + s • (x 0 - x 2) + δ • u
    exact heq
  · intro m hm hmr
    have hm' : rim012 m = 3 ∨ rim012 m = 4 ∨ rim012 m = 6 := by
      rcases zmod5_cases m with rfl | rfl | rfl | rfl | rfl
      · exfalso; apply hmr; decide
      · right; left; rfl
      · right; right; rfl
      · left; rfl
      · exfalso; apply hmr; decide
    exact hmin _ hm' (fun h => hm (rim012_injective h))



/-- **Universal Wiring Lemma for Facet 0 (`012`)**.
Any parameter `t > 0` on the facet line `u0(t)` where the 5-rim is strictly convex,
vertex 5 is interior, and the rim depths are injective and cyclically unimodal,
yields `FaceChordView F 0`. -/
lemma exists_faceChordView_012 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x)
    (h_c3 : F.f 0 (x 6) < F.f 0 (x 3)) (h_c4 : F.f 0 (x 6) < F.f 0 (x 4))
    (hoff : ⟪F.N 0, cross (x 0 - x 2) (x 6 - x 2)⟫ ≠ 0 ∨
      ⟪x 6 - x 2, x 0 - x 2⟫ < 0 ∨ ⟪x 6 - x 0, x 2 - x 0⟫ < 0)
    (h_view : ∃ t : ℝ, 0 < t ∧
      (∃ ρ : ℝ, ρ ≠ 0 ∧ StrictConvex5 (fun i => x (rim012 i)) (u0 x t) ρ ∧
        (∀ i : ZMod 5, 0 < ρ * det3 (x (rim012 (i + 1)) - x (rim012 i)) (x 5 - x (rim012 i)) (u0 x t))) ∧
      Function.Injective (fun i => ⟪x (rim012 i), u0 x t⟫) ∧
      IsCyclicUnimodal (fun i => ⟪x (rim012 i), u0 x t⟫)) :
    FaceChordView F 0 := by
  obtain ⟨t, ht_pos, ⟨ρ, hρ_ne, hcyc, hin5⟩, hinj, huni⟩ := h_view
  set u := u0 x t
  refine ⟨u, 5, by infer_instance, rim012, 4, 2, ρ, ?_, by decide, by decide, by decide, hρ_ne,
    hcyc, ?_, ?_, hinj, Or.inl (strictUnimodal_of_cyclic (by omega) huni), by decide, ?_, hoff⟩
  · exact inner_N0_u0 F t
  · intro q hq0 hqr i
    have hq5 : q = 5 := by
      fin_cases q
      · revert hq0; decide
      · revert hq0; decide
      · revert hq0; decide
      · exfalso; exact hqr 3 rfl
      · exfalso; exact hqr 1 rfl
      · rfl
      · exfalso; exact hqr 2 rfl
    subst hq5
    exact hin5 i
  · intro q hq0 hqr
    have hq1 : q = 1 := by
      fin_cases q
      · exfalso; exact hqr 0 rfl
      · rfl
      · exfalso; exact hqr 4 rfl
      · revert hq0; decide
      · revert hq0; decide
      · revert hq0; decide
      · revert hq0; decide
    subst hq1
    obtain ⟨s, δ, hs0, hs1, hδ, heq⟩ := chord_middle_012 (x := x) ht_pos
    refine ⟨s, δ, hs0, hs1, hδ, ?_⟩
    show x 1 = x (rim012 4) + s • (x (rim012 (4 + 1)) - x (rim012 4)) + δ • u
    change x 1 = x 2 + s • (x 0 - x 2) + δ • u
    exact heq
  · intro m hm hmr
    rcases zmod5_cases m with rfl | rfl | rfl | rfl | rfl
    · exfalso; apply hmr; decide
    · exact h_c4
    · exact False.elim (hm rfl)
    · exact h_c3
    · exfalso; apply hmr; decide

private lemma cramer_facet_eq {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (t : Fin 9) (o a b c d : Fin 7)
    (ho : o ∈ s0x_S24 t) (ha : a ∈ s0x_S24 t) (hb : b ∈ s0x_S24 t) :
    det3 (x a - x o) (x b - x o) (x c - x o) * F.f t (x d) =
    det3 (x a - x o) (x b - x o) (x d - x o) * F.f t (x c) := by
  have zo : F.f t (x o) = 0 := F.zero t o ho
  have za : F.f t (x a) = 0 := F.zero t a ha
  have zb : F.f t (x b) = 0 := F.zero t b hb
  have ha' : ⟪F.N t, x a - x o⟫ = 0 := by rw [F.inner_sub t a o, za, zo, sub_self]
  have hb' : ⟪F.N t, x b - x o⟫ = 0 := by rw [F.inner_sub t b o, zb, zo, sub_self]
  have hc' : ⟪F.N t, x c - x o⟫ = F.f t (x c) := by rw [F.inner_sub t c o, zo, sub_zero]
  have hd' : ⟪F.N t, x d - x o⟫ = F.f t (x d) := by rw [F.inner_sub t d o, zo, sub_zero]
  have hc := vol3_smul_cramer (x a - x o) (x b - x o) (x c - x o) (x d - x o)
  have h_inner := congr_arg (fun v => ⟪F.N t, v⟫) hc
  rw [real_inner_smul_right, inner_add_right, inner_add_right,
      real_inner_smul_right, real_inner_smul_right, real_inner_smul_right,
      ha', hb', mul_zero, mul_zero, zero_add, zero_add] at h_inner
  have hv1 : vol3 (x a - x o) (x b - x o) (x c - x o) = det3 (x a - x o) (x b - x o) (x c - x o) := by
    simp only [det3_expand, vol3, PiLp.sub_apply]; ring
  have hv2 : vol3 (x a - x o) (x b - x o) (x d - x o) = det3 (x a - x o) (x b - x o) (x d - x o) := by
    simp only [det3_expand, vol3, PiLp.sub_apply]; ring
  rw [hv1, hv2, hc', hd'] at h_inner
  exact h_inner

/-- For the 5-rim `(0, 4, 6, 3, 2)` at `u0 x t` (`t > 0`), deleting corner `4` (`2`) gives
sub-quad `(0, 4, 6, 3)` with `ρ * κ < 0` (Carbon's A21 Rank 2 / A24 Lemma D3). -/
lemma kappa_sign_product_0463 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (t ρ : ℝ) (ht : 0 < t)
    (hin5_chord : 0 < ρ * det3 (x 0 - x 2) (x 5 - x 2) (u0 x t)) :
    ρ * quadKappa (subquad (fun i => x (rim012 i)) 4) < 0 := by
  have h_cross : det3 (x 0 - x 2) (x 5 - x 2) (u0 x t) =
      - (1 + t) * det3 (x 0 - x 1) (x 2 - x 1) (x 5 - x 1) := by
    dsimp [u0]; simp only [det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  have hid_om : det3 (x 1 - x 0) (x 6 - x 0) (x 2 - x 0) = det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have hid_461 : det3 (x 4 - x 0) (x 6 - x 0) (x 1 - x 0) = - det3 (x 1 - x 0) (x 6 - x 0) (x 4 - x 0) := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have hid_kap : det3 (x 6 - x 0) (x 3 - x 4) (x 0 - x 4) = - det3 (x 4 - x 0) (x 6 - x 0) (x 3 - x 0) := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have hcr0 := cramer_facet_eq F 0 1 0 2 6 5 (by decide) (by decide) (by decide)
  have hcr1 := cramer_facet_eq F 1 0 1 6 2 4 (by decide) (by decide) (by decide)
  have hcr4 := cramer_facet_eq F 4 0 4 6 1 3 (by decide) (by decide) (by decide)
  have hq_kap : quadKappa (subquad (fun i => x (rim012 i)) 4) =
      det3 (x 6 - x 0) (x 3 - x 4) (x 0 - x 4) := rfl
  rw [hq_kap, hid_kap]
  set Ω := det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)
  have h_om_ne := omega_ne_zero F
  have h_om_sq : 0 < Ω ^ 2 := sq_pos_of_ne_zero h_om_ne
  have nf05 : F.f 0 (x 5) < 0 := F.neg 0 5 (by decide)
  have nf06 : F.f 0 (x 6) < 0 := F.neg 0 6 (by decide)
  have nf12 : F.f 1 (x 2) < 0 := F.neg 1 2 (by decide)
  have nf14 : F.f 1 (x 4) < 0 := F.neg 1 4 (by decide)
  have nf41 : F.f 4 (x 1) < 0 := F.neg 4 1 (by decide)
  have nf43 : F.f 4 (x 3) < 0 := F.neg 4 3 (by decide)
  have h_in_prod : 0 < ρ * (- (1 + t) * det3 (x 0 - x 1) (x 2 - x 1) (x 5 - x 1)) := by
    rwa [h_cross] at hin5_chord
  have h_prod1 : (ρ * (- (1 + t) * det3 (x 0 - x 1) (x 2 - x 1) (x 5 - x 1))) * F.f 0 (x 6) < 0 :=
    mul_neg_of_pos_of_neg h_in_prod nf06
  have hcr0' : det3 (x 0 - x 1) (x 2 - x 1) (x 5 - x 1) * F.f 0 (x 6) = Ω * F.f 0 (x 5) := by
    have hdet_eq : det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) = det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) := rfl
    exact hcr0.symm
  have h_id_c0 : (ρ * (- (1 + t) * det3 (x 0 - x 1) (x 2 - x 1) (x 5 - x 1))) * F.f 0 (x 6) =
      (- (1 + t) * F.f 0 (x 5)) * (ρ * Ω) := by
    calc
      _ = - (1 + t) * ρ * (det3 (x 0 - x 1) (x 2 - x 1) (x 5 - x 1) * F.f 0 (x 6)) := by ring
      _ = - (1 + t) * ρ * (Ω * F.f 0 (x 5)) := by rw [hcr0']
      _ = (- (1 + t) * F.f 0 (x 5)) * (ρ * Ω) := by ring
  rw [h_id_c0] at h_prod1
  have h_coeff_pos : 0 < - (1 + t) * F.f 0 (x 5) := by
    have : 0 < 1 + t := by linarith
    have : 0 < - F.f 0 (x 5) := by linarith
    nlinarith
  have h_rho_om : ρ * Ω < 0 := neg_of_mul_neg_right h_prod1 h_coeff_pos.le
  have h_k_c4 : det3 (x 4 - x 0) (x 6 - x 0) (x 3 - x 0) * F.f 4 (x 1) * F.f 1 (x 2) =
      - (Ω * F.f 1 (x 4) * F.f 4 (x 3)) := by
    calc
      det3 (x 4 - x 0) (x 6 - x 0) (x 3 - x 0) * F.f 4 (x 1) * F.f 1 (x 2) =
        (det3 (x 4 - x 0) (x 6 - x 0) (x 3 - x 0) * F.f 4 (x 1)) * F.f 1 (x 2) := by ring
      _ = (det3 (x 4 - x 0) (x 6 - x 0) (x 1 - x 0) * F.f 4 (x 3)) * F.f 1 (x 2) := by rw [← hcr4]
      _ = F.f 4 (x 3) * (det3 (x 4 - x 0) (x 6 - x 0) (x 1 - x 0) * F.f 1 (x 2)) := by ring
      _ = F.f 4 (x 3) * (- det3 (x 1 - x 0) (x 6 - x 0) (x 4 - x 0) * F.f 1 (x 2)) := by rw [hid_461]
      _ = - F.f 4 (x 3) * (det3 (x 1 - x 0) (x 6 - x 0) (x 4 - x 0) * F.f 1 (x 2)) := by ring
      _ = - F.f 4 (x 3) * (det3 (x 1 - x 0) (x 6 - x 0) (x 2 - x 0) * F.f 1 (x 4)) := by rw [← hcr1]
      _ = - (Ω * F.f 1 (x 4) * F.f 4 (x 3)) := by rw [hid_om]; ring
  have h_om_k : 0 < (Ω * - det3 (x 4 - x 0) (x 6 - x 0) (x 3 - x 0)) * (F.f 4 (x 1) * F.f 1 (x 2)) := by
    calc
      (Ω * - det3 (x 4 - x 0) (x 6 - x 0) (x 3 - x 0)) * (F.f 4 (x 1) * F.f 1 (x 2)) =
        - Ω * (det3 (x 4 - x 0) (x 6 - x 0) (x 3 - x 0) * F.f 4 (x 1) * F.f 1 (x 2)) := by ring
      _ = - Ω * (- (Ω * F.f 1 (x 4) * F.f 4 (x 3))) := by rw [h_k_c4]
      _ = Ω ^ 2 * (F.f 1 (x 4) * F.f 4 (x 3)) := by ring
      _ > 0 := mul_pos h_om_sq (mul_pos_of_neg_of_neg nf14 nf43)
  have h_om_k_pos : 0 < Ω * - det3 (x 4 - x 0) (x 6 - x 0) (x 3 - x 0) :=
    pos_of_mul_pos_left h_om_k (mul_pos_of_neg_of_neg nf41 nf12).le
  have h_prod : (ρ * Ω) * (Ω * - det3 (x 4 - x 0) (x 6 - x 0) (x 3 - x 0)) < 0 :=
    mul_neg_of_neg_of_pos h_rho_om h_om_k_pos
  have h_sq_kap : (ρ * Ω) * (Ω * - det3 (x 4 - x 0) (x 6 - x 0) (x 3 - x 0)) =
      Ω ^ 2 * (ρ * - det3 (x 4 - x 0) (x 6 - x 0) (x 3 - x 0)) := by ring
  rw [h_sq_kap] at h_prod
  exact neg_of_mul_neg_right h_prod h_om_sq.le

lemma merged_inj_of_singleAdjacentTie {k : ℕ} [NeZero k] (p : ZMod (k + 1) → ℝ³) (b : ℝ³)
    (a : ZMod (k + 1)) (htie : SingleAdjacentTie p b a) :
    Function.Injective (mergedDepths (fun i => ⟪p i, b⟫) a) := by
  have hphi_ne : ∀ m : ZMod k, phi a m ≠ a := by
    intro m h
    have h1 : ((m.val + 1 : ℕ) : ZMod (k + 1)) = 0 := by
      push_cast
      calc (m.val : ZMod (k + 1)) + 1 = phi a m - a := by dsimp [phi]; ring
        _ = a - a := by rw [h]
        _ = 0 := sub_self a
    have hm_lt := m.val_lt
    have hval := congrArg ZMod.val h1
    rw [ZMod.val_cast_of_lt (by omega), ZMod.val_zero] at hval
    omega
  intro i j hij
  rcases htie.2 (phi a i) (phi a j) hij with h_same | ⟨h1, _⟩ | ⟨_, h2⟩
  · exact phi_inj a h_same
  · exact False.elim (hphi_ne i h1)
  · exact False.elim (hphi_ne j h2)

lemma unimodal_merged_LC {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (ρ : ℝ)
    (ht_pos : 0 < t_LC x)
    (hcvx : StrictConvex5 (fun i => x (rim012 i)) (u_LC x) ρ)
    (hin5_chord : 0 < ρ * det3 (x 0 - x 2) (x 5 - x 2) (u_LC x))
    (hgen_LC : SingleAdjacentTie (fun i => x (rim012 i)) (u_LC x) 4)
    (hp : let w := mergedDepths (fun i => ⟪x (rim012 i), u_LC x⟫) 4
      w 1 < w 0 ∨ w 3 < w 0 ∨ w 1 < w 2 ∨ w 3 < w 2) :
    IsCyclicUnimodal (mergedDepths (fun i => ⟪x (rim012 i), u_LC x⟫) 4) := by
  have hk_neg : ρ * quadKappa (subquad (fun i => x (rim012 i)) 4) < 0 :=
    kappa_sign_product_0463 F (t_LC x) ρ ht_pos hin5_chord
  set q := subquad (fun i => x (rim012 i)) 4
  have hcvx4 : ∀ i, 0 < ρ * triD q (u_LC x) i :=
    subquad_strictConvex (fun i => x (rim012 i)) (u_LC x) ρ hcvx 4
  have hnh : ¬ (max ⟪q 1, u_LC x⟫ ⟪q 3, u_LC x⟫ ≤ min ⟪q 0, u_LC x⟫ ⟪q 2, u_LC x⟫) :=
    diagCross_not_high q (u_LC x) hcvx4 hk_neg
  have hmin_lt : min ⟪q 0, u_LC x⟫ ⟪q 2, u_LC x⟫ < max ⟪q 1, u_LC x⟫ ⟪q 3, u_LC x⟫ :=
    min_lt_max_of_not_le hnh
  set w := mergedDepths (fun i => ⟪x (rim012 i), u_LC x⟫) 4
  have hw0 : w 0 = ⟪q 0, u_LC x⟫ := rfl
  have hw1 : w 1 = ⟪q 1, u_LC x⟫ := rfl
  have hw2 : w 2 = ⟪q 2, u_LC x⟫ := rfl
  have hw3 : w 3 = ⟪q 3, u_LC x⟫ := rfl
  have h_hn_min : min (w 0) (w 2) < max (w 1) (w 3) := by
    rw [hw0, hw1, hw2, hw3]; exact hmin_lt
  have hn := hn_of_min_lt_max (z := w) h_hn_min
  have hinj : Function.Injective w :=
    merged_inj_of_singleAdjacentTie (fun i => x (rim012 i)) (u_LC x) 4 hgen_LC
  exact Minimality.RimCell.isCyclicUnimodal_four w hinj hn hp

theorem q012_LC_plus_gen (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x)
    -- Window condition & facet signs at u_LC:
    (ht_pos : 0 < t_LC x)
    (hN4 : ⟪F.N 4, u_LC x⟫ < 0)
    (hN7 : ⟪F.N 7, u_LC x⟫ < 0)
    (hN6 : 0 < ⟪F.N 6, u_LC x⟫)
    (hN3 : 0 < ⟪F.N 3, u_LC x⟫)
    (hN8 : 0 < ⟪F.N 8, u_LC x⟫)
    -- Farthest vertex w in {3,4,6}:
    (hfar : FarOff012 F)
    -- Depth condition:
    (h_depth : ⟪x 4, u_LC x⟫ < ⟪x 0, u_LC x⟫)
    -- Genericity off R012Special (single adjacent tie at a = 4, where rim012 4 = 2 and rim012 0 = 0):
    (hgen_LC : SingleAdjacentTie (fun i => x (rim012 i)) (u_LC x) 4)
    -- Strict obtuseness at vertex 1:
    (hdenom : ⟪x 0 - x 2, x 2 - x 1⟫ < 0)
    :
    FaceChordView F 0 := by
  obtain ⟨ρ0, _, hcvx0, hin5_0⟩ := fiveRim_04632_of_window F ht_pos hN4 hN7 hN6 hN3 hN8
  have huni : IsCyclicUnimodal (mergedDepths (fun i => ⟪x (rim012 i), u_LC x⟫) 4) := by
    refine unimodal_merged_LC F ρ0 ht_pos hcvx0 (hin5_0 4) hgen_LC (Or.inl ?_)
    have hw0_0 : mergedDepths (fun i => ⟪x (rim012 i), u_LC x⟫) 4 0 = ⟪x 0, u_LC x⟫ :=
      mergedDepths_zero' _ 4
    have hw0_1 : mergedDepths (fun i => ⟪x (rim012 i), u_LC x⟫) 4 1 = ⟪x 4, u_LC x⟫ :=
      mergedDepths_one (by omega) _ 4
    rw [hw0_0, hw0_1]
    exact h_depth
  have hdir : 0 < ⟪x 2 - x 0, x 2 - x 1⟫ := by
    have : x 2 - x 0 = - (x 0 - x 2) := by abel
    rw [this, inner_neg_left]
    linarith
  have hdiff_dir : ⟪x (rim012 4) - x (rim012 (4 + 1)), x 2 - x 1⟫ = ⟪x 2 - x 0, x 2 - x 1⟫ := by
    change ⟪x 2 - x 0, x 2 - x 1⟫ = ⟪x 2 - x 0, x 2 - x 1⟫
    rfl
  have hdir_ne : ⟪x (rim012 4) - x (rim012 (4 + 1)), x 2 - x 1⟫ ≠ 0 := by
    rw [hdiff_dir]
    exact hdir.ne'
  set w0 := mergedDepths (fun i => ⟪x (rim012 i), u_LC x⟫) 4
  have hw0_0 : w0 0 = ⟪x 0, u_LC x⟫ := mergedDepths_zero' _ 4
  have hw0_1 : w0 1 = ⟪x 4, u_LC x⟫ := mergedDepths_one (by omega) _ 4
  have hw0_m1 : w0 (-1) = ⟪x 3, u_LC x⟫ := mergedDepths_neg_one _ 4
  have hw0_inj : Function.Injective w0 := huni.1
  have hm1_ne_0 : (-1 : ZMod 4) ≠ 0 := by decide
  have hw0_m1_ne : w0 (-1) ≠ w0 0 := fun h => hm1_ne_0 (hw0_inj h)
  have hw0_1_lt : w0 1 < w0 0 := by rw [hw0_1, hw0_0]; exact h_depth
  have hbranch :
      (IsMergedExtremum w0) ∨
      (IsMergedMonotone w0 ∧
        (0 < ⟪x (rim012 (4 - 1)), u_LC x⟫ - ⟪x (rim012 (4 + 2)), u_LC x⟫ ↔
          0 < (1 : ℝ) * ⟪x (rim012 4) - x (rim012 (4 + 1)), x 2 - x 1⟫)) := by
    rcases lt_or_gt_of_ne hw0_m1_ne with h_m1 | h_m1
    · left
      exact Or.inl ⟨h_m1, hw0_1_lt⟩
    · right
      refine ⟨Or.inr ⟨hw0_1_lt, h_m1⟩, ?_⟩
      have h3_idx : rim012 (4 - 1) = 3 := rfl
      have h4_idx : rim012 (4 + 2) = 4 := rfl
      have h2_idx : rim012 4 = 2 := rfl
      have h0_idx : rim012 (4 + 1) = 0 := rfl
      rw [h3_idx, h4_idx, h2_idx, h0_idx]
      have hdiff_pos : 0 < ⟪x 3, u_LC x⟫ - ⟪x 4, u_LC x⟫ := by
        have : ⟪x 3, u_LC x⟫ = w0 (-1) := hw0_m1.symm
        have : ⟪x 4, u_LC x⟫ = w0 1 := hw0_1.symm
        linarith
      have hprod_pos : 0 < (1 : ℝ) * ⟪x 2 - x 0, x 2 - x 1⟫ := by
        simp only [one_mul]
        exact hdir
      exact iff_of_true hdiff_pos hprod_pos

  have hev_uni := splitUnimodal_step (m := 4) (by omega)
    (fun i => x (rim012 i)) (u_LC x) (x 2 - x 1) 4 1 (Or.inl rfl)
    hgen_LC hdir_ne huni hbranch

  have hev_uni' : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      Function.Injective (fun i => ⟪x (rim012 i), u0 x (t_LC x + ε)⟫) ∧
      IsCyclicUnimodal (fun i => ⟪x (rim012 i), u0 x (t_LC x + ε)⟫) := by
    filter_upwards [hev_uni] with ε hε
    have heq : u_LC x + (1 * ε) • (x 2 - x 1) = u0 x (t_LC x + ε) := by
      dsimp [u0, u_LC]
      rw [show t_LC x + ε = t_LC x + (1 * ε) by ring]
      rw [add_smul]
      abel
    rwa [heq] at hε

  have hcont_t : Continuous (fun ε : ℝ => t_LC x + ε) := continuous_const.add continuous_id
  have hev_t : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < t_LC x + ε :=
    eventually_lt_of_continuous hcont_t (by simpa using ht_pos)

  have hcont_N4 : Continuous (fun ε : ℝ => ⟪F.N 4, u0 x (t_LC x + ε)⟫) := by
    simp only [inner_u0_add]
    exact continuous_const.add (continuous_id.mul continuous_const)
  have hev_N4 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪F.N 4, u0 x (t_LC x + ε)⟫ < 0 :=
    eventually_gt_of_continuous hcont_N4 (by simpa [u_LC] using hN4)

  have hcont_N7 : Continuous (fun ε : ℝ => ⟪F.N 7, u0 x (t_LC x + ε)⟫) := by
    simp only [inner_u0_add]
    exact continuous_const.add (continuous_id.mul continuous_const)
  have hev_N7 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪F.N 7, u0 x (t_LC x + ε)⟫ < 0 :=
    eventually_gt_of_continuous hcont_N7 (by simpa [u_LC] using hN7)

  have hcont_N6 : Continuous (fun ε : ℝ => ⟪F.N 6, u0 x (t_LC x + ε)⟫) := by
    simp only [inner_u0_add]
    exact continuous_const.add (continuous_id.mul continuous_const)
  have hev_N6 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ⟪F.N 6, u0 x (t_LC x + ε)⟫ :=
    eventually_lt_of_continuous hcont_N6 (by simpa [u_LC] using hN6)

  have hcont_N3 : Continuous (fun ε : ℝ => ⟪F.N 3, u0 x (t_LC x + ε)⟫) := by
    simp only [inner_u0_add]
    exact continuous_const.add (continuous_id.mul continuous_const)
  have hev_N3 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ⟪F.N 3, u0 x (t_LC x + ε)⟫ :=
    eventually_lt_of_continuous hcont_N3 (by simpa [u_LC] using hN3)

  have hcont_N8 : Continuous (fun ε : ℝ => ⟪F.N 8, u0 x (t_LC x + ε)⟫) := by
    simp only [inner_u0_add]
    exact continuous_const.add (continuous_id.mul continuous_const)
  have hev_N8 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ⟪F.N 8, u0 x (t_LC x + ε)⟫ :=
    eventually_lt_of_continuous hcont_N8 (by simpa [u_LC] using hN8)

  have hev_all := hev_uni'.and (hev_t.and (hev_N4.and (hev_N7.and (hev_N6.and (hev_N3.and hev_N8)))))
  obtain ⟨ε, ⟨hinj, hcyc_uni⟩, ht_pos, hN4, hN7, hN6, hN3, hN8⟩ := hev_all.exists
  obtain ⟨ρ, hρ_ne, hcvx, hin5⟩ := fiveRim_04632_of_window F ht_pos hN4 hN7 hN6 hN3 hN8
  refine exists_faceChordView_012_gen x F hfar ⟨t_LC x + ε, ht_pos, ⟨ρ, hρ_ne, hcvx, hin5⟩, hinj, hcyc_uni⟩

/-- **Theorem LC-K5 (Minus): Level-chord leaf with `u_LC - ε • d`.**
Under the window condition `t_LC ∈ (max(1/ω4, t6), ω3)`, frame-free `c3, c4 < 1`
(vertex 6 farthest below facet 0), depth condition `⟪x 3, u_LC⟫ < ⟪x 0, u_LC⟫`,
and the single adjacent tie condition `hgen_LC` off the `R012Special` locus,
the perturbed view `u_LC - ε • d` yields `FaceChordView F 0`.

Note: `hdenom : ⟪x 0 - x 2, x 2 - x 1⟫ < 0` follows from strict obtuseness at vertex 1:
`⟪x 0 - x 2, x 2 - x 1⟫ = ⟪x 0 - x 1, x 2 - x 1⟫ - ‖x 2 - x 1‖² < 0`. -/
theorem q012_LC_minus_gen (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x)
    -- Window condition & facet signs at u_LC:
    (ht_pos : 0 < t_LC x)
    (hN4 : ⟪F.N 4, u_LC x⟫ < 0)
    (hN7 : ⟪F.N 7, u_LC x⟫ < 0)
    (hN6 : 0 < ⟪F.N 6, u_LC x⟫)
    (hN3 : 0 < ⟪F.N 3, u_LC x⟫)
    (hN8 : 0 < ⟪F.N 8, u_LC x⟫)
    -- Farthest vertex w in {3,4,6}:
    (hfar : FarOff012 F)
    -- Depth condition:
    (h_depth : ⟪x 3, u_LC x⟫ < ⟪x 0, u_LC x⟫)
    -- Genericity off R012Special (single adjacent tie at a = 4, where rim012 4 = 2 and rim012 0 = 0):
    (hgen_LC : SingleAdjacentTie (fun i => x (rim012 i)) (u_LC x) 4)
    -- Strict obtuseness at vertex 1:
    (hdenom : ⟪x 0 - x 2, x 2 - x 1⟫ < 0)
    :
    FaceChordView F 0 := by
  obtain ⟨ρ0, _, hcvx0, hin5_0⟩ := fiveRim_04632_of_window F ht_pos hN4 hN7 hN6 hN3 hN8
  have huni : IsCyclicUnimodal (mergedDepths (fun i => ⟪x (rim012 i), u_LC x⟫) 4) := by
    refine unimodal_merged_LC F ρ0 ht_pos hcvx0 (hin5_0 4) hgen_LC (Or.inr (Or.inl ?_))
    have hw0_0 : mergedDepths (fun i => ⟪x (rim012 i), u_LC x⟫) 4 0 = ⟪x 0, u_LC x⟫ :=
      mergedDepths_zero' _ 4
    have hw0_m1 : mergedDepths (fun i => ⟪x (rim012 i), u_LC x⟫) 4 (-1) = ⟪x 3, u_LC x⟫ :=
      mergedDepths_neg_one _ 4
    have hm1_eq : (-1 : ZMod 4) = 3 := by decide
    rw [← hm1_eq, hw0_m1, hw0_0]
    exact h_depth
  have hdir : 0 < ⟪x 2 - x 0, x 2 - x 1⟫ := by
    have : x 2 - x 0 = - (x 0 - x 2) := by abel
    rw [this, inner_neg_left]
    linarith
  have hdiff_dir : ⟪x (rim012 4) - x (rim012 (4 + 1)), x 2 - x 1⟫ = ⟪x 2 - x 0, x 2 - x 1⟫ := by
    change ⟪x 2 - x 0, x 2 - x 1⟫ = ⟪x 2 - x 0, x 2 - x 1⟫
    rfl
  have hdir_ne : ⟪x (rim012 4) - x (rim012 (4 + 1)), x 2 - x 1⟫ ≠ 0 := by
    rw [hdiff_dir]
    exact hdir.ne'
  set w0 := mergedDepths (fun i => ⟪x (rim012 i), u_LC x⟫) 4
  have hw0_0 : w0 0 = ⟪x 0, u_LC x⟫ := mergedDepths_zero' _ 4
  have hw0_1 : w0 1 = ⟪x 4, u_LC x⟫ := mergedDepths_one (by omega) _ 4
  have hw0_m1 : w0 (-1) = ⟪x 3, u_LC x⟫ := mergedDepths_neg_one _ 4
  have hw0_inj : Function.Injective w0 := huni.1
  have h1_ne_0 : (1 : ZMod 4) ≠ 0 := by decide
  have hw0_1_ne : w0 1 ≠ w0 0 := fun h => h1_ne_0 (hw0_inj h)
  have hw0_m1_lt : w0 (-1) < w0 0 := by rw [hw0_m1, hw0_0]; exact h_depth
  have hbranch :
      (IsMergedExtremum w0) ∨
      (IsMergedMonotone w0 ∧
        (0 < ⟪x (rim012 (4 - 1)), u_LC x⟫ - ⟪x (rim012 (4 + 2)), u_LC x⟫ ↔
          0 < (-1 : ℝ) * ⟪x (rim012 4) - x (rim012 (4 + 1)), x 2 - x 1⟫)) := by
    rcases lt_or_gt_of_ne hw0_1_ne with h_1 | h_1
    · left
      exact Or.inl ⟨hw0_m1_lt, h_1⟩
    · right
      refine ⟨Or.inl ⟨hw0_m1_lt, h_1⟩, ?_⟩
      have h3_idx : rim012 (4 - 1) = 3 := rfl
      have h4_idx : rim012 (4 + 2) = 4 := rfl
      have h2_idx : rim012 4 = 2 := rfl
      have h0_idx : rim012 (4 + 1) = 0 := rfl
      rw [h3_idx, h4_idx, h2_idx, h0_idx]
      have hdiff_neg : ⟪x 3, u_LC x⟫ - ⟪x 4, u_LC x⟫ < 0 := by
        have : ⟪x 3, u_LC x⟫ = w0 (-1) := hw0_m1.symm
        have : ⟪x 4, u_LC x⟫ = w0 1 := hw0_1.symm
        linarith
      have hprod_neg : (-1 : ℝ) * ⟪x 2 - x 0, x 2 - x 1⟫ < 0 := by
        nlinarith
      exact iff_of_false (not_lt_of_gt hdiff_neg) (not_lt_of_gt hprod_neg)

  have hev_uni := splitUnimodal_step (m := 4) (by omega)
    (fun i => x (rim012 i)) (u_LC x) (x 2 - x 1) 4 (-1) (Or.inr rfl)
    hgen_LC hdir_ne huni hbranch

  have hev_uni' : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      Function.Injective (fun i => ⟪x (rim012 i), u0 x (t_LC x - ε)⟫) ∧
      IsCyclicUnimodal (fun i => ⟪x (rim012 i), u0 x (t_LC x - ε)⟫) := by
    filter_upwards [hev_uni] with ε hε
    have heq : u_LC x + (-1 * ε) • (x 2 - x 1) = u0 x (t_LC x - ε) := by
      dsimp [u0, u_LC]
      rw [show t_LC x - ε = t_LC x + (-1 * ε) by ring]
      rw [add_smul]
      abel
    rwa [heq] at hε

  have hcont_t : Continuous (fun ε : ℝ => t_LC x - ε) := continuous_const.sub continuous_id
  have hev_t : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < t_LC x - ε :=
    eventually_lt_of_continuous hcont_t (by simpa using ht_pos)

  have hcont_N4 : Continuous (fun ε : ℝ => ⟪F.N 4, u0 x (t_LC x - ε)⟫) := by
    simp only [show ∀ ε : ℝ, t_LC x - ε = t_LC x + (-ε) by intro; ring, inner_u0_add]
    exact continuous_const.add (continuous_id.neg.mul continuous_const)
  have hev_N4 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪F.N 4, u0 x (t_LC x - ε)⟫ < 0 :=
    eventually_gt_of_continuous hcont_N4 (by simpa [u_LC] using hN4)

  have hcont_N7 : Continuous (fun ε : ℝ => ⟪F.N 7, u0 x (t_LC x - ε)⟫) := by
    simp only [show ∀ ε : ℝ, t_LC x - ε = t_LC x + (-ε) by intro; ring, inner_u0_add]
    exact continuous_const.add (continuous_id.neg.mul continuous_const)
  have hev_N7 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪F.N 7, u0 x (t_LC x - ε)⟫ < 0 :=
    eventually_gt_of_continuous hcont_N7 (by simpa [u_LC] using hN7)

  have hcont_N6 : Continuous (fun ε : ℝ => ⟪F.N 6, u0 x (t_LC x - ε)⟫) := by
    simp only [show ∀ ε : ℝ, t_LC x - ε = t_LC x + (-ε) by intro; ring, inner_u0_add]
    exact continuous_const.add (continuous_id.neg.mul continuous_const)
  have hev_N6 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ⟪F.N 6, u0 x (t_LC x - ε)⟫ :=
    eventually_lt_of_continuous hcont_N6 (by simpa [u_LC] using hN6)

  have hcont_N3 : Continuous (fun ε : ℝ => ⟪F.N 3, u0 x (t_LC x - ε)⟫) := by
    simp only [show ∀ ε : ℝ, t_LC x - ε = t_LC x + (-ε) by intro; ring, inner_u0_add]
    exact continuous_const.add (continuous_id.neg.mul continuous_const)
  have hev_N3 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ⟪F.N 3, u0 x (t_LC x - ε)⟫ :=
    eventually_lt_of_continuous hcont_N3 (by simpa [u_LC] using hN3)

  have hcont_N8 : Continuous (fun ε : ℝ => ⟪F.N 8, u0 x (t_LC x - ε)⟫) := by
    simp only [show ∀ ε : ℝ, t_LC x - ε = t_LC x + (-ε) by intro; ring, inner_u0_add]
    exact continuous_const.add (continuous_id.neg.mul continuous_const)
  have hev_N8 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ⟪F.N 8, u0 x (t_LC x - ε)⟫ :=
    eventually_lt_of_continuous hcont_N8 (by simpa [u_LC] using hN8)

  have hev_all := hev_uni'.and (hev_t.and (hev_N4.and (hev_N7.and (hev_N6.and (hev_N3.and hev_N8)))))
  obtain ⟨ε, ⟨hinj, hcyc_uni⟩, ht_pos, hN4, hN7, hN6, hN3, hN8⟩ := hev_all.exists
  obtain ⟨ρ, hρ_ne, hcvx, hin5⟩ := fiveRim_04632_of_window F ht_pos hN4 hN7 hN6 hN3 hN8
  refine exists_faceChordView_012_gen x F hfar ⟨t_LC x - ε, ht_pos, ⟨ρ, hρ_ne, hcvx, hin5⟩, hinj, hcyc_uni⟩

theorem q012_LC_plus (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x)
    (ht_pos : 0 < t_LC x)
    (hN4 : ⟪F.N 4, u_LC x⟫ < 0)
    (hN7 : ⟪F.N 7, u_LC x⟫ < 0)
    (hN6 : 0 < ⟪F.N 6, u_LC x⟫)
    (hN3 : 0 < ⟪F.N 3, u_LC x⟫)
    (hN8 : 0 < ⟪F.N 8, u_LC x⟫)
    (h_c3 : F.f 0 (x 6) < F.f 0 (x 3))
    (h_c4 : F.f 0 (x 6) < F.f 0 (x 4))
    (h_depth : ⟪x 4, u_LC x⟫ < ⟪x 0, u_LC x⟫)
    (hgen_LC : SingleAdjacentTie (fun i => x (rim012 i)) (u_LC x) 4)
    (hdenom : ⟪x 0 - x 2, x 2 - x 1⟫ < 0)
    (hoff : ⟪F.N 0, cross (x 0 - x 2) (x 6 - x 2)⟫ ≠ 0 ∨
      ⟪x 6 - x 2, x 0 - x 2⟫ < 0 ∨ ⟪x 6 - x 0, x 2 - x 0⟫ < 0) :
    FaceChordView F 0 :=
  q012_LC_plus_gen x F ht_pos hN4 hN7 hN6 hN3 hN8 (farOff012_six F h_c3 h_c4 hoff) h_depth hgen_LC hdenom

theorem q012_LC_minus (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x)
    (ht_pos : 0 < t_LC x)
    (hN4 : ⟪F.N 4, u_LC x⟫ < 0)
    (hN7 : ⟪F.N 7, u_LC x⟫ < 0)
    (hN6 : 0 < ⟪F.N 6, u_LC x⟫)
    (hN3 : 0 < ⟪F.N 3, u_LC x⟫)
    (hN8 : 0 < ⟪F.N 8, u_LC x⟫)
    (h_c3 : F.f 0 (x 6) < F.f 0 (x 3))
    (h_c4 : F.f 0 (x 6) < F.f 0 (x 4))
    (h_depth : ⟪x 3, u_LC x⟫ < ⟪x 0, u_LC x⟫)
    (hgen_LC : SingleAdjacentTie (fun i => x (rim012 i)) (u_LC x) 4)
    (hdenom : ⟪x 0 - x 2, x 2 - x 1⟫ < 0)
    (hoff : ⟪F.N 0, cross (x 0 - x 2) (x 6 - x 2)⟫ ≠ 0 ∨
      ⟪x 6 - x 2, x 0 - x 2⟫ < 0 ∨ ⟪x 6 - x 0, x 2 - x 0⟫ < 0) :
    FaceChordView F 0 :=
  q012_LC_minus_gen x F ht_pos hN4 hN7 hN6 hN3 hN8 (farOff012_six F h_c3 h_c4 hoff) h_depth hgen_LC hdenom

end Minimality.T24.R012
