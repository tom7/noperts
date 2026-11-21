module

public import Minimality.SilS0XC
public import Minimality.RimFromSigns
public import Minimality.Type24SAT.Facets24
public import Minimality.Type24SAT.K24.Par2546

@[expose] public section

open scoped RealInnerProductSpace
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.RimFromSigns

namespace Minimality.T24.Q45

/-!
# Q45 Signs on Plane Pi and Generalized Quad Rim of Signs

This module formalizes:
1. **AA1 (`facetSigns_Pi`)**: Facet signs on the plane $\Pi$ of facet 3 (`0345`),
   with view direction $u = \alpha e_5 + \beta e_4$ and facet 7 in basis $(e_{35}, e_{34})$.
2. **AA2 (`quadRim_of_signs`)**: Generalized quad rim convexity and vertex 1 interior
   position for rim $(x P, x A, x B, x Q)$ with chord $A-B$ on edge-on facet 3,
   and its six rim instances from section 2.3 (`6402`, `6302`, `6352`, `6052`, `6032`, `6432`),
   re-deriving `lemmaX5_quad_signs` and `lemmaX4_quad_signs` as corollaries.
-/

-- =========================================================================
-- AA1: facetSigns_Pi
-- =========================================================================

/-- Basis vector `e4 = x 4 - x 0` on facet 3 (`0345`).
Corner-frame meaning: displacement from vertex 0 to vertex 4. -/
def e4 (x : Fin 7 → ℝ³) : ℝ³ := x 4 - x 0

/-- Basis vector `e5 = x 5 - x 0` on facet 3 (`0345`).
Corner-frame meaning: displacement from vertex 0 to vertex 5. -/
def e5 (x : Fin 7 → ℝ³) : ℝ³ := x 5 - x 0

/-- Basis vector `e35 = x 3 - x 5` on facet 3 (`0345`).
Corner-frame meaning: displacement from vertex 5 to vertex 3 along edge 5-3. -/
def e35 (x : Fin 7 → ℝ³) : ℝ³ := x 3 - x 5

/-- Basis vector `e34 = x 3 - x 4` on facet 3 (`0345`).
Corner-frame meaning: displacement from vertex 4 to vertex 3 along edge 4-3. -/
def e34 (x : Fin 7 → ℝ³) : ℝ³ := x 3 - x 4

/-- Vector `u` in the plane $\Pi$ of facet 3 decomposed in the basis `(e5, e4)`.
`u = α • e5 + β • e4`. -/
def u_Pi (x : Fin 7 → ℝ³) (α β : ℝ) : ℝ³ := α • e5 x + β • e4 x

variable {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)


/-- Normal 0 inner `e5` is negative: `⟪F.N 0, e5 x⟫ < 0`.
Corner-frame meaning: `e5` points away from bottom face `012`. -/
theorem inner_N0_e5_neg : ⟪F.N 0, e5 x⟫ < 0 := by
  dsimp [e5]
  have := (F.hN 0 (x 5) (x 0)).symm
  rw [F.zero 0 0 (by decide), sub_zero] at this
  rw [this]
  exact F.neg 0 5 (by decide)

/-- Normal 1 inner `e4` is negative: `⟪F.N 1, e4 x⟫ < 0`.
Corner-frame meaning: `F.N 1` is normal to `016`; `e4` points away from `016`. -/
theorem inner_N1_e4_neg : ⟪F.N 1, e4 x⟫ < 0 := by
  dsimp [e4]
  have := (F.hN 1 (x 4) (x 0)).symm
  rw [F.zero 1 0 (by decide), sub_zero] at this
  rw [this]
  exact F.neg 1 4 (by decide)


/-- Normal 2 inner `e5` is zero: `⟪F.N 2, e5 x⟫ = 0`.
Corner-frame meaning: facet 2 is `025`, which contains the edge `0 -> 5` (`e5`). -/
theorem inner_N2_e5_eq_zero : ⟪F.N 2, e5 x⟫ = 0 := by
  dsimp [e5]
  have := (F.hN 2 (x 5) (x 0)).symm
  rw [F.zero 2 5 (by decide), F.zero 2 0 (by decide), sub_self] at this
  exact this

/-- Normal 2 inner `e4` is negative: `⟪F.N 2, e4 x⟫ < 0`.
Corner-frame meaning: `4 ∉ facet 2` (`025`), so `e4` points outward from facet 2. -/
theorem inner_N2_e4_neg : ⟪F.N 2, e4 x⟫ < 0 := by
  dsimp [e4]
  have := (F.hN 2 (x 4) (x 0)).symm
  rw [F.zero 2 0 (by decide), sub_zero] at this
  rw [this]
  exact F.neg 2 4 (by decide)

/-- Normal 3 inner `e4` is zero: `⟪F.N 3, e4 x⟫ = 0`.
Corner-frame meaning: facet 3 is `0345`, which contains `e4`. -/
theorem inner_N3_e4_eq_zero : ⟪F.N 3, e4 x⟫ = 0 := by
  dsimp [e4]
  have := (F.hN 3 (x 4) (x 0)).symm
  rw [F.zero 3 4 (by decide), F.zero 3 0 (by decide), sub_self] at this
  exact this

/-- Normal 3 inner `e5` is zero: `⟪F.N 3, e5 x⟫ = 0`.
Corner-frame meaning: facet 3 is `0345`, which contains `e5`. -/
theorem inner_N3_e5_eq_zero : ⟪F.N 3, e5 x⟫ = 0 := by
  dsimp [e5]
  have := (F.hN 3 (x 5) (x 0)).symm
  rw [F.zero 3 5 (by decide), F.zero 3 0 (by decide), sub_self] at this
  exact this

/-- Normal 4 inner `e4` is zero: `⟪F.N 4, e4 x⟫ = 0`.
Corner-frame meaning: facet 4 is `046`, which contains `e4`. -/
theorem inner_N4_e4_eq_zero : ⟪F.N 4, e4 x⟫ = 0 := by
  dsimp [e4]
  have := (F.hN 4 (x 4) (x 0)).symm
  rw [F.zero 4 4 (by decide), F.zero 4 0 (by decide), sub_self] at this
  exact this

/-- Normal 4 inner `e5` is negative: `⟪F.N 4, e5 x⟫ < 0`.
Corner-frame meaning: `5 ∉ facet 4` (`046`), so `e5` points outward from facet 4. -/
theorem inner_N4_e5_neg : ⟪F.N 4, e5 x⟫ < 0 := by
  dsimp [e5]
  have := (F.hN 4 (x 5) (x 0)).symm
  rw [F.zero 4 0 (by decide), sub_zero] at this
  rw [this]
  exact F.neg 4 5 (by decide)

/-- Normal 6 inner `e5` is positive: `0 < ⟪F.N 6, e5 x⟫`.
Corner-frame meaning: facet 6 is `235`. Vertex 5 is on facet 6, vertex 0 is behind,
so displacement `e5 = x 5 - x 0` has positive projection onto inward normal. -/
theorem inner_N6_e5_pos : 0 < ⟪F.N 6, e5 x⟫ := by
  dsimp [e5]
  have := (F.hN 6 (x 5) (x 0)).symm
  rw [F.zero 6 5 (by decide), zero_sub] at this
  rw [this]
  linarith [F.neg 6 0 (by decide)]

/-- Normal 6 coefficient relation: `s * ⟪F.N 6, e4 x⟫ = (1 - t) * ⟪F.N 6, e5 x⟫`.
Corner-frame meaning: follows from `x 3 - x 0 = s • e4 + t • e5` and vertices 3, 5 on facet 6. -/
theorem inner_N6_e4_eq (s t : ℝ) (hdecomp : x 3 - x 0 = s • e4 x + t • e5 x) :
    s * ⟪F.N 6, e4 x⟫ = (1 - t) * ⟪F.N 6, e5 x⟫ := by
  have h3 : ⟪F.N 6, x 3 - x 0⟫ = ⟪F.N 6, e5 x⟫ := by
    dsimp [e5]
    have h1 := (F.hN 6 (x 3) (x 0)).symm
    have h2 := (F.hN 6 (x 5) (x 0)).symm
    rw [F.zero 6 3 (by decide)] at h1
    rw [F.zero 6 5 (by decide)] at h2
    linarith
  have hlin : ⟪F.N 6, x 3 - x 0⟫ = s * ⟪F.N 6, e4 x⟫ + t * ⟪F.N 6, e5 x⟫ := by
    rw [hdecomp, inner_add_right, real_inner_smul_right, real_inner_smul_right]
  linarith

/-- Normal 8 inner `e4` is positive: `0 < ⟪F.N 8, e4 x⟫`.
Corner-frame meaning: facet 8 is `346`. Vertex 4 is on facet 8, vertex 0 is behind,
so displacement `e4 = x 4 - x 0` has positive projection onto inward normal. -/
theorem inner_N8_e4_pos : 0 < ⟪F.N 8, e4 x⟫ := by
  dsimp [e4]
  have := (F.hN 8 (x 4) (x 0)).symm
  rw [F.zero 8 4 (by decide), zero_sub] at this
  rw [this]
  linarith [F.neg 8 0 (by decide)]

/-- Normal 8 coefficient relation: `t * ⟪F.N 8, e5 x⟫ = (1 - s) * ⟪F.N 8, e4 x⟫`.
Corner-frame meaning: follows from `x 3 - x 0 = s • e4 + t • e5` and vertices 3, 4 on facet 8. -/
theorem inner_N8_e5_eq (s t : ℝ) (hdecomp : x 3 - x 0 = s • e4 x + t • e5 x) :
    t * ⟪F.N 8, e5 x⟫ = (1 - s) * ⟪F.N 8, e4 x⟫ := by
  have h3 : ⟪F.N 8, x 3 - x 0⟫ = ⟪F.N 8, e4 x⟫ := by
    dsimp [e4]
    have h1 := (F.hN 8 (x 3) (x 0)).symm
    have h2 := (F.hN 8 (x 4) (x 0)).symm
    rw [F.zero 8 3 (by decide)] at h1
    rw [F.zero 8 4 (by decide)] at h2
    linarith
  have hlin : ⟪F.N 8, x 3 - x 0⟫ = s * ⟪F.N 8, e4 x⟫ + t * ⟪F.N 8, e5 x⟫ := by
    rw [hdecomp, inner_add_right, real_inner_smul_right, real_inner_smul_right]
  linarith

/-- Normal 7 inner `e35` is positive: `0 < ⟪F.N 7, e35 x⟫`.
Corner-frame meaning: facet 7 is `236`. Vertex 3 is on facet 7, vertex 5 is behind,
so displacement `e35 = x 3 - x 5` has positive projection onto inward normal. -/
theorem inner_N7_e35_pos : 0 < ⟪F.N 7, e35 x⟫ := by
  dsimp [e35]
  have := (F.hN 7 (x 3) (x 5)).symm
  rw [F.zero 7 3 (by decide), zero_sub] at this
  rw [this]
  linarith [F.neg 7 5 (by decide)]

/-- Normal 7 inner `e34` is positive: `0 < ⟪F.N 7, e34 x⟫`.
Corner-frame meaning: facet 7 is `236`. Vertex 3 is on facet 7, vertex 4 is behind,
so displacement `e34 = x 3 - x 4` has positive projection onto inward normal. -/
theorem inner_N7_e34_pos : 0 < ⟪F.N 7, e34 x⟫ := by
  dsimp [e34]
  have := (F.hN 7 (x 3) (x 4)).symm
  rw [F.zero 7 3 (by decide), zero_sub] at this
  rw [this]
  linarith [F.neg 7 4 (by decide)]

/-- Facet 0 sign on `u_Pi x α β`: `⟪F.N 0, u_Pi x α β⟫ = α * ⟪F.N 0, e5 x⟫ + β * ⟪F.N 0, e4 x⟫`. -/
theorem inner_N0_u_Pi (α β : ℝ) :
    ⟪F.N 0, u_Pi x α β⟫ = α * ⟪F.N 0, e5 x⟫ + β * ⟪F.N 0, e4 x⟫ := by
  simp only [u_Pi, inner_add_right, real_inner_smul_right]

/-- Facet 1 sign on `u_Pi x α β`: `⟪F.N 1, u_Pi x α β⟫ = α * ⟪F.N 1, e5 x⟫ + β * ⟪F.N 1, e4 x⟫`. -/
theorem inner_N1_u_Pi (α β : ℝ) :
    ⟪F.N 1, u_Pi x α β⟫ = α * ⟪F.N 1, e5 x⟫ + β * ⟪F.N 1, e4 x⟫ := by
  simp only [u_Pi, inner_add_right, real_inner_smul_right]

/-- Facet 2 sign on `u_Pi x α β`: `⟪F.N 2, u_Pi x α β⟫ = β * ⟪F.N 2, e4 x⟫`. -/
theorem inner_N2_u_Pi (α β : ℝ) :
    ⟪F.N 2, u_Pi x α β⟫ = β * ⟪F.N 2, e4 x⟫ := by
  simp only [u_Pi, inner_add_right, real_inner_smul_right, inner_N2_e5_eq_zero F, mul_zero, zero_add]

/-- Facet 3 sign on `u_Pi x α β`: `⟪F.N 3, u_Pi x α β⟫ = 0`. -/
theorem inner_N3_u_Pi (α β : ℝ) :
    ⟪F.N 3, u_Pi x α β⟫ = 0 := by
  simp only [u_Pi, inner_add_right, real_inner_smul_right, inner_N3_e4_eq_zero F, inner_N3_e5_eq_zero F, mul_zero, add_zero]

/-- Facet 4 sign on `u_Pi x α β`: `⟪F.N 4, u_Pi x α β⟫ = α * ⟪F.N 4, e5 x⟫`. -/
theorem inner_N4_u_Pi (α β : ℝ) :
    ⟪F.N 4, u_Pi x α β⟫ = α * ⟪F.N 4, e5 x⟫ := by
  simp only [u_Pi, inner_add_right, real_inner_smul_right, inner_N4_e4_eq_zero F, mul_zero, add_zero]

/-- Facet 5 sign on `u_Pi x α β`: `⟪F.N 5, u_Pi x α β⟫ = α * ⟪F.N 5, e5 x⟫ + β * ⟪F.N 5, e4 x⟫`. -/
theorem inner_N5_u_Pi (α β : ℝ) :
    ⟪F.N 5, u_Pi x α β⟫ = α * ⟪F.N 5, e5 x⟫ + β * ⟪F.N 5, e4 x⟫ := by
  simp only [u_Pi, inner_add_right, real_inner_smul_right]

/-- Facet 6 sign on `u_Pi x α β`: `s * ⟪F.N 6, u_Pi x α β⟫ = (α * s + β * (1 - t)) * ⟪F.N 6, e5 x⟫`. -/
theorem inner_N6_u_Pi (s t α β : ℝ) (hdecomp : x 3 - x 0 = s • e4 x + t • e5 x) :
    s * ⟪F.N 6, u_Pi x α β⟫ = (α * s + β * (1 - t)) * ⟪F.N 6, e5 x⟫ := by
  have hu : ⟪F.N 6, u_Pi x α β⟫ = α * ⟪F.N 6, e5 x⟫ + β * ⟪F.N 6, e4 x⟫ := by
    simp only [u_Pi, inner_add_right, real_inner_smul_right]
  have hrel := inner_N6_e4_eq F s t hdecomp
  calc
    s * ⟪F.N 6, u_Pi x α β⟫ = s * (α * ⟪F.N 6, e5 x⟫ + β * ⟪F.N 6, e4 x⟫) := by rw [hu]
    _ = α * s * ⟪F.N 6, e5 x⟫ + β * (s * ⟪F.N 6, e4 x⟫) := by ring
    _ = α * s * ⟪F.N 6, e5 x⟫ + β * ((1 - t) * ⟪F.N 6, e5 x⟫) := by rw [hrel]
    _ = (α * s + β * (1 - t)) * ⟪F.N 6, e5 x⟫ := by ring

/-- Facet 8 sign on `u_Pi x α β`: `t * ⟪F.N 8, u_Pi x α β⟫ = (α * (1 - s) + β * t) * ⟪F.N 8, e4 x⟫`. -/
theorem inner_N8_u_Pi (s t α β : ℝ) (hdecomp : x 3 - x 0 = s • e4 x + t • e5 x) :
    t * ⟪F.N 8, u_Pi x α β⟫ = (α * (1 - s) + β * t) * ⟪F.N 8, e4 x⟫ := by
  have hu : ⟪F.N 8, u_Pi x α β⟫ = α * ⟪F.N 8, e5 x⟫ + β * ⟪F.N 8, e4 x⟫ := by
    simp only [u_Pi, inner_add_right, real_inner_smul_right]
  have hrel := inner_N8_e5_eq F s t hdecomp
  calc
    t * ⟪F.N 8, u_Pi x α β⟫ = t * (α * ⟪F.N 8, e5 x⟫ + β * ⟪F.N 8, e4 x⟫) := by rw [hu]
    _ = α * (t * ⟪F.N 8, e5 x⟫) + β * t * ⟪F.N 8, e4 x⟫ := by ring
    _ = α * ((1 - s) * ⟪F.N 8, e4 x⟫) + β * t * ⟪F.N 8, e4 x⟫ := by rw [hrel]
    _ = (α * (1 - s) + β * t) * ⟪F.N 8, e4 x⟫ := by ring



/-- Decomposition of `(s + t - 1) • u_Pi x α β` into the basis `(e35, e34)`. -/
theorem u_Pi_in_e35_e34 (s t α β : ℝ) (hdecomp : x 3 - x 0 = s • e4 x + t • e5 x) :
    (s + t - 1) • u_Pi x α β = (α * (1 - s) + β * t) • e35 x + (α * s + β * (1 - t)) • e34 x := by
  ext j
  have hd := congr_arg (fun (v : ℝ³) => v j) hdecomp
  dsimp [u_Pi, e4, e5, e35, e34] at hd ⊢
  linear_combination - (α + β) * hd

/-- Facet 7 (`236`) formula in the basis `(e35, e34)`:
`(s + t - 1) * ⟪F.N 7, u_Pi x α β⟫ = (α * (1 - s) + β * t) * ⟪F.N 7, e35 x⟫ + (α * s + β * (1 - t)) * ⟪F.N 7, e34 x⟫`. -/
theorem inner_N7_u_Pi (s t α β : ℝ) (hdecomp : x 3 - x 0 = s • e4 x + t • e5 x) :
    (s + t - 1) * ⟪F.N 7, u_Pi x α β⟫ =
      (α * (1 - s) + β * t) * ⟪F.N 7, e35 x⟫ + (α * s + β * (1 - t)) * ⟪F.N 7, e34 x⟫ := by
  have heq : (s + t - 1) * ⟪F.N 7, u_Pi x α β⟫ = ⟪F.N 7, (s + t - 1) • u_Pi x α β⟫ := by
    rw [real_inner_smul_right]
  rw [heq, u_Pi_in_e35_e34 s t α β hdecomp, inner_add_right, real_inner_smul_right, real_inner_smul_right]

/-- Facet 7 (`236`) is strictly negative when both basis coordinates are non-positive and at least one is negative. -/
theorem inner_N7_u_Pi_neg (s t α β : ℝ) (hdecomp : x 3 - x 0 = s • e4 x + t • e5 x)
    (h_sum : 1 < s + t)
    (h35 : α * (1 - s) + β * t ≤ 0)
    (h34 : α * s + β * (1 - t) ≤ 0)
    (h_strict : α * (1 - s) + β * t < 0 ∨ α * s + β * (1 - t) < 0) :
    ⟪F.N 7, u_Pi x α β⟫ < 0 := by
  have hN35 := inner_N7_e35_pos F
  have hN34 := inner_N7_e34_pos F
  have hD : 0 < s + t - 1 := by linarith
  have h_comb : (α * (1 - s) + β * t) * ⟪F.N 7, e35 x⟫ + (α * s + β * (1 - t)) * ⟪F.N 7, e34 x⟫ < 0 := by
    rcases h_strict with h1 | h2
    · have term1 : (α * (1 - s) + β * t) * ⟪F.N 7, e35 x⟫ < 0 := mul_neg_of_neg_of_pos h1 hN35
      have term2 : (α * s + β * (1 - t)) * ⟪F.N 7, e34 x⟫ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h34 hN34.le
      linarith
    · have term1 : (α * (1 - s) + β * t) * ⟪F.N 7, e35 x⟫ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h35 hN35.le
      have term2 : (α * s + β * (1 - t)) * ⟪F.N 7, e34 x⟫ < 0 := mul_neg_of_neg_of_pos h2 hN34
      linarith
  have h_eq := inner_N7_u_Pi F s t α β hdecomp
  have h_prod : (s + t - 1) * ⟪F.N 7, u_Pi x α β⟫ < 0 := by linarith [h_eq]
  exact neg_of_mul_neg_right h_prod hD.le

-- =========================================================================
-- AA2: quadRim_of_signs and 6 rim instances
-- =========================================================================

/-- Non-zero cross product from a non-zero facet inner product. -/
theorem cross_ne_zero_of_facet_sign {N nf : ℕ} {S : Fin nf → Finset (Fin N)} {x : Fin N → ℝ³}
    (F : S0xFac nf S x) (f : Fin nf) (p q : Fin N)
    (hp : p ∈ S f) (hq : q ∈ S f)
    {u : ℝ³} (hu : ⟪F.N f, u⟫ ≠ 0)
    (f_sep : Fin nf) (hp_sep : p ∈ S f_sep) (hq_sep : q ∉ S f_sep) :
    cross u (x q - x p) ≠ 0 := by
  intro hcr
  have he : x q - x p ≠ 0 := by
    intro h
    have h1 : F.f f_sep (x p) = 0 := F.zero f_sep p hp_sep
    have h2 : F.f f_sep (x q) < 0 := F.neg f_sep q hq_sep
    have : x q = x p := sub_eq_zero.mp h
    rw [this, h1] at h2
    exact lt_irrefl 0 h2
  have hcr' : cross (x q - x p) u = 0 := by
    rw [show cross (x q - x p) u = - cross u (x q - x p) by ext j; fin_cases j <;> simp [cross] <;> ring, hcr, neg_zero]
  obtain ⟨k, hk⟩ : ∃ k : ℝ, u = k • (x q - x p) := ⟨_, eq_smul_of_cross_eq_zero he hcr'⟩
  have hz : ⟪F.N f, x q - x p⟫ = 0 := by
    have := (F.hN f (x q) (x p)).symm
    rw [F.zero f q hq, F.zero f p hp, sub_self] at this
    exact this
  have h0 : ⟪F.N f, u⟫ = 0 := by
    rw [hk, real_inner_smul_right, hz, mul_zero]
  exact hu h0

/-- Non-zero cross product from opposing signs at distinct endpoints. -/
theorem cross_ne_zero_of_opp_endpoints {N nf : ℕ} {S : Fin nf → Finset (Fin N)} {x : Fin N → ℝ³}
    (F : S0xFac nf S x) (f1 f2 : Fin nf) (p q : Fin N)
    (hp1 : p ∈ S f1) (hq1 : q ∉ S f1)
    (hp2 : p ∉ S f2) (hq2 : q ∈ S f2)
    {u : ℝ³} (hu1 : 0 < ⟪F.N f1, u⟫) (hu2 : 0 < ⟪F.N f2, u⟫) :
    cross u (x q - x p) ≠ 0 := by
  intro hcr
  have he : x q - x p ≠ 0 := by
    intro h
    have h1 : F.f f1 (x p) = 0 := F.zero f1 p hp1
    have h2 : F.f f1 (x q) < 0 := F.neg f1 q hq1
    have : x q = x p := sub_eq_zero.mp h
    rw [this, h1] at h2
    exact lt_irrefl 0 h2
  have hcr' : cross (x q - x p) u = 0 := by
    rw [show cross (x q - x p) u = - cross u (x q - x p) by ext j; fin_cases j <;> simp [cross] <;> ring, hcr, neg_zero]
  obtain ⟨k, hk⟩ : ∃ k : ℝ, u = k • (x q - x p) := ⟨_, eq_smul_of_cross_eq_zero he hcr'⟩
  have hq1_neg : F.f f1 (x q) < 0 := F.neg f1 q hq1
  have hp2_neg : F.f f2 (x p) < 0 := F.neg f2 p hp2
  have h_inner1 : ⟪F.N f1, u⟫ = k * F.f f1 (x q) := by
    rw [hk, real_inner_smul_right]
    have := (F.hN f1 (x q) (x p)).symm
    rw [F.zero f1 p hp1, sub_zero] at this
    rw [this]
  have h_inner2 : ⟪F.N f2, u⟫ = - k * F.f f2 (x p) := by
    rw [hk, real_inner_smul_right]
    have := (F.hN f2 (x q) (x p)).symm
    rw [F.zero f2 q hq2, zero_sub] at this
    rw [this, mul_neg, neg_mul]
  have hk_neg : k < 0 := by
    by_contra hge
    have hle : 0 ≤ k := not_lt.mp hge
    have hprod : k * F.f f1 (x q) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hle hq1_neg.le
    linarith [h_inner1, hu1]
  have hk_pos : 0 < k := by
    by_contra hle
    have hge : k ≤ 0 := not_lt.mp hle
    have hprod : - k * F.f f2 (x p) ≤ 0 := by
      have : 0 ≤ -k := neg_nonneg.mpr hge
      have h1 : (-k) * F.f f2 (x p) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos this hp2_neg.le
      linarith
    linarith [h_inner2, hu2]
  linarith

/-- Generalized rim convexity and interior positioning from silhouette signs
for an arbitrary edge-on facet `tc : Fin 9` and any interior vertex `I : Fin 7`
off all four rim facets. -/
theorem quadRim_of_signs_gen {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (P A B Q : Fin 7)
    (t0 t0' tc t2 t2' t3 t3' : Fin 9)
    (hP0 : P ∈ s0x_S24 t0 ∧ P ∈ s0x_S24 t0')
    (hA0 : A ∈ s0x_S24 t0 ∧ A ∈ s0x_S24 t0')
    (hAc : A ∈ s0x_S24 tc)
    (hBc : B ∈ s0x_S24 tc)
    (hB2 : B ∈ s0x_S24 t2 ∧ B ∈ s0x_S24 t2')
    (hQ2 : Q ∈ s0x_S24 t2 ∧ Q ∈ s0x_S24 t2')
    (hQ3 : Q ∈ s0x_S24 t3 ∧ Q ∈ s0x_S24 t3')
    (hP3 : P ∈ s0x_S24 t3 ∧ P ∈ s0x_S24 t3')
    (hB_off0 : B ∉ s0x_S24 t0 ∨ B ∉ s0x_S24 t0')
    (hQ_off0 : Q ∉ s0x_S24 t0 ∨ Q ∉ s0x_S24 t0')
    (hP_offc : P ∉ s0x_S24 tc)
    (hQ_offc : Q ∉ s0x_S24 tc)
    (hA_off2 : A ∉ s0x_S24 t2 ∨ A ∉ s0x_S24 t2')
    (hP_off2 : P ∉ s0x_S24 t2 ∨ P ∉ s0x_S24 t2')
    (hA_off3 : A ∉ s0x_S24 t3 ∨ A ∉ s0x_S24 t3')
    (hB_off3 : B ∉ s0x_S24 t3 ∨ B ∉ s0x_S24 t3')
    (hne_PA : cross u (x A - x P) ≠ 0)
    (hne_AB : cross u (x B - x A) ≠ 0)
    (hne_BQ : cross u (x Q - x B) ≠ 0)
    (hne_QP : cross u (x P - x Q) ≠ 0)
    (h_opp0 : ⟪F.N t0, u⟫ < 0 ∧ 0 < ⟪F.N t0', u⟫)
    (hNc : ⟪F.N tc, u⟫ = 0)
    (h_opp2 : ⟪F.N t2, u⟫ < 0 ∧ 0 < ⟪F.N t2', u⟫)
    (h_opp3 : ⟪F.N t3, u⟫ < 0 ∧ 0 < ⟪F.N t3', u⟫) :
    ∃ ρ : ℝ, ρ ≠ 0 ∧
      (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
        0 < ρ * det3 (quad (x P) (x A) (x B) (x Q) (i + 1) - quad (x P) (x A) (x B) (x Q) i)
          (quad (x P) (x A) (x B) (x Q) j - quad (x P) (x A) (x B) (x Q) i) u) ∧
      (∀ I : Fin 7,
        (I ∉ s0x_S24 t0 ∨ I ∉ s0x_S24 t0') →
        (I ∉ s0x_S24 tc) →
        (I ∉ s0x_S24 t2 ∨ I ∉ s0x_S24 t2') →
        (I ∉ s0x_S24 t3 ∨ I ∉ s0x_S24 t3') →
        ∀ i : ZMod 4,
          0 < ρ * det3 (quad (x P) (x A) (x B) (x Q) (i + 1) - quad (x P) (x A) (x B) (x Q) i)
            (x I - quad (x P) (x A) (x B) (x Q) i) u) := by
  obtain ⟨σ₀, hσ₀_ne, hσ₀⟩ := det3_sign_ridge F t0 t0' P A hP0 hA0 u h_opp0 hne_PA
  obtain ⟨σ₁, hσ₁_ne, hσ₁⟩ := det3_sign_edgeOn F tc A B hAc hBc u hNc hne_AB
  obtain ⟨σ₂, hσ₂_ne, hσ₂⟩ := det3_sign_ridge F t2 t2' B Q hB2 hQ2 u h_opp2 hne_BQ
  obtain ⟨σ₃, hσ₃_ne, hσ₃⟩ := det3_sign_ridge F t3 t3' Q P hQ3 hP3 u h_opp3 hne_QP
  have hcyc01 : det3 (x A - x P) (x B - x P) u = det3 (x B - x A) (x P - x A) u :=
    det3_cycle_triangle (x P) (x A) (x B) u
  have hcyc12 : det3 (x B - x A) (x Q - x A) u = det3 (x Q - x B) (x A - x B) u :=
    det3_cycle_triangle (x A) (x B) (x Q) u
  have hcyc23 : det3 (x Q - x B) (x P - x B) u = det3 (x P - x Q) (x B - x Q) u :=
    det3_cycle_triangle (x B) (x Q) (x P) u
  have h0_B : 0 < σ₀ * det3 (x A - x P) (x B - x P) u := hσ₀ B hB_off0
  have h1_P : 0 < σ₁ * det3 (x B - x A) (x P - x A) u := hσ₁ P hP_offc
  have h1_P' : 0 < σ₁ * det3 (x A - x P) (x B - x P) u := by rw [hcyc01]; exact h1_P
  have hσ01 : 0 < σ₀ * σ₁ := sign_prod h0_B h1_P'
  have h1_Q : 0 < σ₁ * det3 (x B - x A) (x Q - x A) u := hσ₁ Q hQ_offc
  have h2_A : 0 < σ₂ * det3 (x Q - x B) (x A - x B) u := hσ₂ A hA_off2
  have h2_A' : 0 < σ₂ * det3 (x B - x A) (x Q - x A) u := by rw [hcyc12]; exact h2_A
  have hσ12 : 0 < σ₁ * σ₂ := sign_prod h1_Q h2_A'
  have hσ02 : 0 < σ₀ * σ₂ := sign_transfer hσ01 hσ12
  have h2_P : 0 < σ₂ * det3 (x Q - x B) (x P - x B) u := hσ₂ P hP_off2
  have h3_B : 0 < σ₃ * det3 (x P - x Q) (x B - x Q) u := hσ₃ B hB_off3
  have h3_B' : 0 < σ₃ * det3 (x Q - x B) (x P - x B) u := by rw [hcyc23]; exact h3_B
  have hσ23 : 0 < σ₂ * σ₃ := sign_prod h2_P h3_B'
  have hσ03 : 0 < σ₀ * σ₃ := sign_transfer hσ02 hσ23
  have h0_Q : 0 < σ₀ * det3 (x A - x P) (x Q - x P) u := hσ₀ Q hQ_off0
  have h3_A : 0 < σ₃ * det3 (x P - x Q) (x A - x Q) u := hσ₃ A hA_off3
  refine ⟨σ₀, hσ₀_ne, ?_, ?_⟩
  · intro i j hj1 hj2
    fin_cases i <;> fin_cases j
    · exact False.elim (hj1 rfl)
    · exact False.elim (hj2 rfl)
    · exact h0_B
    · exact h0_Q
    · exact sign_transfer hσ01 h1_P
    · exact False.elim (hj1 rfl)
    · exact False.elim (hj2 rfl)
    · exact sign_transfer hσ01 h1_Q
    · exact sign_transfer hσ02 h2_P
    · exact sign_transfer hσ02 h2_A
    · exact False.elim (hj1 rfl)
    · exact False.elim (hj2 rfl)
    · exact False.elim (hj2 rfl)
    · exact sign_transfer hσ03 h3_A
    · exact sign_transfer hσ03 h3_B
    · exact False.elim (hj1 rfl)
  · intro I hI0 hIc hI2 hI3 i
    fin_cases i
    · exact hσ₀ I hI0
    · exact sign_transfer hσ01 (hσ₁ I hIc)
    · exact sign_transfer hσ02 (hσ₂ I hI2)
    · exact sign_transfer hσ03 (hσ₃ I hI3)

/-- Algebraic chord-middle decomposition in `ℝ³`: expresses `a` as a convex combination
along `b - c` plus a view-plane offset `α • (a - b) + β • (a - c)`. -/
theorem middle_eq (a b c : ℝ³) (α β : ℝ) (hκ : α + β ≠ 0) :
    a = c + (α / (α + β)) • (b - c) + (1 / (α + β)) • (α • (a - b) + β • (a - c)) := by
  ext j
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  field_simp
  ring

/-- Generalized rim convexity and vertex 1 interior position from silhouette signs. -/
theorem quadRim_of_signs {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (P A B Q : Fin 7)
    (t0 t0' t2 t2' t3 t3' : Fin 9)
    (hP0 : P ∈ s0x_S24 t0 ∧ P ∈ s0x_S24 t0')
    (hA0 : A ∈ s0x_S24 t0 ∧ A ∈ s0x_S24 t0')
    (hA3 : A ∈ s0x_S24 3)
    (hB3 : B ∈ s0x_S24 3)
    (hB2 : B ∈ s0x_S24 t2 ∧ B ∈ s0x_S24 t2')
    (hQ2 : Q ∈ s0x_S24 t2 ∧ Q ∈ s0x_S24 t2')
    (hQ3 : Q ∈ s0x_S24 t3 ∧ Q ∈ s0x_S24 t3')
    (hP3 : P ∈ s0x_S24 t3 ∧ P ∈ s0x_S24 t3')
    (hB_off0 : B ∉ s0x_S24 t0 ∨ B ∉ s0x_S24 t0')
    (hQ_off0 : Q ∉ s0x_S24 t0 ∨ Q ∉ s0x_S24 t0')
    (h1_off0 : (1 : Fin 7) ∉ s0x_S24 t0 ∨ (1 : Fin 7) ∉ s0x_S24 t0')
    (hP_off3 : P ∉ s0x_S24 3)
    (hQ_off3 : Q ∉ s0x_S24 3)
    (h1_off3 : (1 : Fin 7) ∉ s0x_S24 3)
    (hA_off2 : A ∉ s0x_S24 t2 ∨ A ∉ s0x_S24 t2')
    (hP_off2 : P ∉ s0x_S24 t2 ∨ P ∉ s0x_S24 t2')
    (h1_off2 : (1 : Fin 7) ∉ s0x_S24 t2 ∨ (1 : Fin 7) ∉ s0x_S24 t2')
    (hA_off3 : A ∉ s0x_S24 t3 ∨ A ∉ s0x_S24 t3')
    (hB_off3 : B ∉ s0x_S24 t3 ∨ B ∉ s0x_S24 t3')
    (h1_off3' : (1 : Fin 7) ∉ s0x_S24 t3 ∨ (1 : Fin 7) ∉ s0x_S24 t3')
    (hne_PA : cross u (x A - x P) ≠ 0)
    (hne_AB : cross u (x B - x A) ≠ 0)
    (hne_BQ : cross u (x Q - x B) ≠ 0)
    (hne_QP : cross u (x P - x Q) ≠ 0)
    (h_opp0 : ⟪F.N t0, u⟫ < 0 ∧ 0 < ⟪F.N t0', u⟫)
    (hN3 : ⟪F.N 3, u⟫ = 0)
    (h_opp2 : ⟪F.N t2, u⟫ < 0 ∧ 0 < ⟪F.N t2', u⟫)
    (h_opp3 : ⟪F.N t3, u⟫ < 0 ∧ 0 < ⟪F.N t3', u⟫) :
    ∃ ρ : ℝ, ρ ≠ 0 ∧
      (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
        0 < ρ * det3 (quad (x P) (x A) (x B) (x Q) (i + 1) - quad (x P) (x A) (x B) (x Q) i)
          (quad (x P) (x A) (x B) (x Q) j - quad (x P) (x A) (x B) (x Q) i) u) ∧
      (∀ i : ZMod 4,
        0 < ρ * det3 (quad (x P) (x A) (x B) (x Q) (i + 1) - quad (x P) (x A) (x B) (x Q) i)
          (x 1 - quad (x P) (x A) (x B) (x Q) i) u) := by
  obtain ⟨ρ, hρ_ne, hcvx, hint⟩ := quadRim_of_signs_gen F P A B Q t0 t0' 3 t2 t2' t3 t3'
    hP0 hA0 hA3 hB3 hB2 hQ2 hQ3 hP3 hB_off0 hQ_off0 hP_off3 hQ_off3
    hA_off2 hP_off2 hA_off3 hB_off3 hne_PA hne_AB hne_BQ hne_QP h_opp0 hN3 h_opp2 h_opp3
  exact ⟨ρ, hρ_ne, hcvx, hint 1 h1_off0 h1_off3 h1_off2 h1_off3'⟩

/-- Rim 6402 convexity and vertex 1 interior position from silhouette signs.
Satisfiability at intended view (Regime B1, `σ < 1`, view `u = - (e5 - ε e4)`):
In the vertex 1 corner frame, `α = 1 > 0` and `β = -ε < 0`.
`⟪F.N 4, u⟫ = - α ⟪F.N 4, e5⟫ > 0` (`0 < N4`).
`τ ⟪F.N 8, u_doc⟫ = (1 - σ) - ε τ > 0` since `σ < 1`, so `⟪F.N 8, u⟫ < 0` (`N8 < 0`).
`β < 0` gives `0 < N0` and `N2 < 0`.
`σ < 1 < σ + τ` gives `λ, μ > 0` at `e5`, so `N7 < 0`.
`a5 > 1` gives `0 < N5`.
All hypotheses strictly hold. -/
theorem rim6402_of_signs {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hN3 : ⟪F.N 3, u⟫ = 0)
    (hN4 : 0 < ⟪F.N 4, u⟫) (hN8 : ⟪F.N 8, u⟫ < 0)
    (hN0 : 0 < ⟪F.N 0, u⟫) (hN2 : ⟪F.N 2, u⟫ < 0)
    (hN7 : ⟪F.N 7, u⟫ < 0) (hN5 : 0 < ⟪F.N 5, u⟫) :
    ∃ ρ : ℝ, ρ ≠ 0 ∧
      (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
        0 < ρ * det3 (quad (x 6) (x 4) (x 0) (x 2) (i + 1) - quad (x 6) (x 4) (x 0) (x 2) i)
          (quad (x 6) (x 4) (x 0) (x 2) j - quad (x 6) (x 4) (x 0) (x 2) i) u) ∧
      (∀ i : ZMod 4,
        0 < ρ * det3 (quad (x 6) (x 4) (x 0) (x 2) (i + 1) - quad (x 6) (x 4) (x 0) (x 2) i)
          (x 1 - quad (x 6) (x 4) (x 0) (x 2) i) u) := by
  have hne_64 := cross_ne_zero_of_facet_sign F 4 6 4 (by decide) (by decide) hN4.ne' 1 (by decide) (by decide)
  have hne_40 := cross_ne_zero_of_facet_sign F 4 4 0 (by decide) (by decide) hN4.ne' 8 (by decide) (by decide)
  have hne_02 := cross_ne_zero_of_facet_sign F 0 0 2 (by decide) (by decide) hN0.ne' 4 (by decide) (by decide)
  have hne_26 := cross_ne_zero_of_facet_sign F 5 2 6 (by decide) (by decide) hN5.ne' 0 (by decide) (by decide)
  exact quadRim_of_signs F 6 4 0 2 8 4 2 0 7 5
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide) (by decide)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
    (Or.inl (by decide)) (Or.inl (by decide)) (Or.inl (by decide))
    (by decide) (by decide) (by decide)
    (Or.inl (by decide)) (Or.inr (by decide)) (Or.inl (by decide))
    (Or.inl (by decide)) (Or.inr (by decide)) (Or.inl (by decide))
    hne_64 hne_40 hne_02 hne_26
    ⟨hN8, hN4⟩ hN3 ⟨hN2, hN0⟩ ⟨hN7, hN5⟩

/-- Rim 6302 convexity and vertex 1 interior position from silhouette signs.
Satisfiability at intended view (Regime Bs1, `σ = 1`, view `u = - (e5 - ε e4)`):
In the vertex 1 corner frame, `α = 1 > 0` and `β = -ε < 0`.
`σ = 1` gives `τ ⟪F.N 8, u_doc⟫ = - ε τ < 0`, so `0 < N8`.
`N7 < 0, N2 < 0, 0 < N0, 0 < N5` hold as in B1.
All hypotheses strictly hold. -/
theorem rim6302_of_signs {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hN3 : ⟪F.N 3, u⟫ = 0)
    (hN7 : ⟪F.N 7, u⟫ < 0) (hN8 : 0 < ⟪F.N 8, u⟫)
    (hN2 : ⟪F.N 2, u⟫ < 0) (hN0 : 0 < ⟪F.N 0, u⟫)
    (hN5 : 0 < ⟪F.N 5, u⟫) :
    ∃ ρ : ℝ, ρ ≠ 0 ∧
      (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
        0 < ρ * det3 (quad (x 6) (x 3) (x 0) (x 2) (i + 1) - quad (x 6) (x 3) (x 0) (x 2) i)
          (quad (x 6) (x 3) (x 0) (x 2) j - quad (x 6) (x 3) (x 0) (x 2) i) u) ∧
      (∀ i : ZMod 4,
        0 < ρ * det3 (quad (x 6) (x 3) (x 0) (x 2) (i + 1) - quad (x 6) (x 3) (x 0) (x 2) i)
          (x 1 - quad (x 6) (x 3) (x 0) (x 2) i) u) := by
  have hne_63 := cross_ne_zero_of_facet_sign F 8 6 3 (by decide) (by decide) hN8.ne' 4 (by decide) (by decide)
  have hne_30 := cross_ne_zero_of_opp_endpoints F 8 0 3 0 (by decide) (by decide) (by decide) (by decide) hN8 hN0
  have hne_02 := cross_ne_zero_of_facet_sign F 0 0 2 (by decide) (by decide) hN0.ne' 4 (by decide) (by decide)
  have hne_26 := cross_ne_zero_of_facet_sign F 5 2 6 (by decide) (by decide) hN5.ne' 0 (by decide) (by decide)
  exact quadRim_of_signs F 6 3 0 2 7 8 2 0 7 5
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide) (by decide)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
    (Or.inl (by decide)) (Or.inr (by decide)) (Or.inl (by decide))
    (by decide) (by decide) (by decide)
    (Or.inl (by decide)) (Or.inr (by decide)) (Or.inl (by decide))
    (Or.inr (by decide)) (Or.inr (by decide)) (Or.inl (by decide))
    hne_63 hne_30 hne_02 hne_26
    ⟨hN7, hN8⟩ hN3 ⟨hN2, hN0⟩ ⟨hN7, hN5⟩

/-- Rim 6352 convexity and vertex 1 interior position from silhouette signs.
Satisfiability at intended view (Regime B2, `σ > 1`, view `u = - (e34 + ε e5)`):
In the vertex 1 corner frame, `e34 = (σ - 1) e4 + τ e5`. Since `σ > 1`, `β = σ - 1 > 0`.
`⟪F.N 2, u⟫ = - β ⟪F.N 2, e4⟫ > 0` (facet 2 front, `0 < N2`).
Along `e34`, `L(3) = L(4) > L(5)` so `⟪F.N 6, u_doc⟫ > 0`, hence `⟪F.N 6, u⟫ < 0` (facet 6 back, `N6 < 0`).
Ridge 5-2 between facet 6 and facet 2 has `(t2, t2') = (6, 2)`.
Along `e34`, `⟪F.N 8, e34⟫ = 0`; `+ ε e5` gives `τ ⟪F.N 8, u_doc⟫ = - ε (σ - 1) c8 < 0`, so `0 < N8`.
`⟪F.N 7, e34⟫ = -f7(x4) > 0`, so `N7 < 0`. `e34` in positive orthant gives `0 < N5`.
All hypotheses strictly hold. -/
theorem rim6352_of_signs {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hN3 : ⟪F.N 3, u⟫ = 0)
    (hN7 : ⟪F.N 7, u⟫ < 0) (hN8 : 0 < ⟪F.N 8, u⟫)
    (hN6 : ⟪F.N 6, u⟫ < 0) (hN2 : 0 < ⟪F.N 2, u⟫)
    (hN5 : 0 < ⟪F.N 5, u⟫) :
    ∃ ρ : ℝ, ρ ≠ 0 ∧
      (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
        0 < ρ * det3 (quad (x 6) (x 3) (x 5) (x 2) (i + 1) - quad (x 6) (x 3) (x 5) (x 2) i)
          (quad (x 6) (x 3) (x 5) (x 2) j - quad (x 6) (x 3) (x 5) (x 2) i) u) ∧
      (∀ i : ZMod 4,
        0 < ρ * det3 (quad (x 6) (x 3) (x 5) (x 2) (i + 1) - quad (x 6) (x 3) (x 5) (x 2) i)
          (x 1 - quad (x 6) (x 3) (x 5) (x 2) i) u) := by
  have hne_63 := cross_ne_zero_of_facet_sign F 8 6 3 (by decide) (by decide) hN8.ne' 4 (by decide) (by decide)
  have hne_35 := cross_ne_zero_of_facet_sign F 6 3 5 (by decide) (by decide) hN6.ne 8 (by decide) (by decide)
  have hne_52 := cross_ne_zero_of_facet_sign F 6 5 2 (by decide) (by decide) hN6.ne 3 (by decide) (by decide)
  have hne_26 := cross_ne_zero_of_facet_sign F 5 2 6 (by decide) (by decide) hN5.ne' 0 (by decide) (by decide)
  exact quadRim_of_signs F 6 3 5 2 7 8 6 2 7 5
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide) (by decide)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
    (Or.inl (by decide)) (Or.inr (by decide)) (Or.inl (by decide))
    (by decide) (by decide) (by decide)
    (Or.inr (by decide)) (Or.inr (by decide)) (Or.inl (by decide))
    (Or.inr (by decide)) (Or.inr (by decide)) (Or.inl (by decide))
    hne_63 hne_35 hne_52 hne_26
    ⟨hN7, hN8⟩ hN3 ⟨hN6, hN2⟩ ⟨hN7, hN5⟩


/-- Canonical rim 6052 starting at apex 6: quad `(x 6) (x 0) (x 5) (x 2)`.
Instantiates `quadRim_of_signs` with `(t2, t2') = (6, 2)`. -/
theorem rim6052_canonical_of_signs {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hN3 : ⟪F.N 3, u⟫ = 0)
    (hN4 : ⟪F.N 4, u⟫ < 0) (hN1 : 0 < ⟪F.N 1, u⟫)
    (hN6 : ⟪F.N 6, u⟫ < 0) (hN2 : 0 < ⟪F.N 2, u⟫)
    (hN7 : ⟪F.N 7, u⟫ < 0) (hN5 : 0 < ⟪F.N 5, u⟫) :
    ∃ ρ : ℝ, ρ ≠ 0 ∧
      (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
        0 < ρ * det3 (quad (x 6) (x 0) (x 5) (x 2) (i + 1) - quad (x 6) (x 0) (x 5) (x 2) i)
          (quad (x 6) (x 0) (x 5) (x 2) j - quad (x 6) (x 0) (x 5) (x 2) i) u) ∧
      (∀ i : ZMod 4,
        0 < ρ * det3 (quad (x 6) (x 0) (x 5) (x 2) (i + 1) - quad (x 6) (x 0) (x 5) (x 2) i)
          (x 1 - quad (x 6) (x 0) (x 5) (x 2) i) u) := by
  have hne_60 := cross_ne_zero_of_facet_sign F 1 6 0 (by decide) (by decide) hN1.ne' 8 (by decide) (by decide)
  have hne_05 := cross_ne_zero_of_facet_sign F 2 0 5 (by decide) (by decide) hN2.ne' 0 (by decide) (by decide)
  have hne_52 := cross_ne_zero_of_facet_sign F 6 5 2 (by decide) (by decide) hN6.ne 3 (by decide) (by decide)
  have hne_26 := cross_ne_zero_of_facet_sign F 5 2 6 (by decide) (by decide) hN5.ne' 0 (by decide) (by decide)
  exact quadRim_of_signs F 6 0 5 2 4 1 6 2 7 5
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide) (by decide)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
    (Or.inl (by decide)) (Or.inl (by decide)) (Or.inl (by decide))
    (by decide) (by decide) (by decide)
    (Or.inl (by decide)) (Or.inl (by decide)) (Or.inl (by decide))
    (Or.inl (by decide)) (Or.inl (by decide)) (Or.inl (by decide))
    hne_60 hne_05 hne_52 hne_26
    ⟨hN4, hN1⟩ hN3 ⟨hN6, hN2⟩ ⟨hN7, hN5⟩

/-- Rim 6032 convexity and vertex 1 interior position from silhouette signs.
Satisfiability at intended view (Regime Ct1, `τ = 1`, view `u = - (e4 - ε e5)`):
In the vertex 1 corner frame, `β = 1 > 0` and `α = -ε < 0`.
`τ = 1` gives `σ ⟪F.N 6, u_doc⟫ = - ε σ c6 < 0`, so `0 < N6`.
`N4 < 0, 0 < N1, N7 < 0, 0 < N5` hold as in C1.
All hypotheses strictly hold. -/
theorem rim6032_of_signs {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hN3 : ⟪F.N 3, u⟫ = 0)
    (hN4 : ⟪F.N 4, u⟫ < 0) (hN1 : 0 < ⟪F.N 1, u⟫)
    (hN7 : ⟪F.N 7, u⟫ < 0) (hN6 : 0 < ⟪F.N 6, u⟫)
    (hN5 : 0 < ⟪F.N 5, u⟫) :
    ∃ ρ : ℝ, ρ ≠ 0 ∧
      (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
        0 < ρ * det3 (quad (x 6) (x 0) (x 3) (x 2) (i + 1) - quad (x 6) (x 0) (x 3) (x 2) i)
          (quad (x 6) (x 0) (x 3) (x 2) j - quad (x 6) (x 0) (x 3) (x 2) i) u) ∧
      (∀ i : ZMod 4,
        0 < ρ * det3 (quad (x 6) (x 0) (x 3) (x 2) (i + 1) - quad (x 6) (x 0) (x 3) (x 2) i)
          (x 1 - quad (x 6) (x 0) (x 3) (x 2) i) u) := by
  have hne_60 := cross_ne_zero_of_facet_sign F 1 6 0 (by decide) (by decide) hN1.ne' 8 (by decide) (by decide)
  have hne_03 := cross_ne_zero_of_opp_endpoints F 1 6 0 3 (by decide) (by decide) (by decide) (by decide) hN1 hN6
  have hne_32 := cross_ne_zero_of_facet_sign F 6 3 2 (by decide) (by decide) hN6.ne' 8 (by decide) (by decide)
  have hne_26 := cross_ne_zero_of_facet_sign F 5 2 6 (by decide) (by decide) hN5.ne' 0 (by decide) (by decide)
  exact quadRim_of_signs F 6 0 3 2 4 1 7 6 7 5
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide) (by decide)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
    (Or.inl (by decide)) (Or.inl (by decide)) (Or.inl (by decide))
    (by decide) (by decide) (by decide)
    (Or.inl (by decide)) (Or.inr (by decide)) (Or.inl (by decide))
    (Or.inr (by decide)) (Or.inr (by decide)) (Or.inl (by decide))
    hne_60 hne_03 hne_32 hne_26
    ⟨hN4, hN1⟩ hN3 ⟨hN7, hN6⟩ ⟨hN7, hN5⟩

/-- Rim 6432 convexity and vertex 1 interior position from silhouette signs.
Satisfiability at intended view (Regime C2, `τ > 1`, view `u = - (e35 + ε e4)`):
In the vertex 1 corner frame, `e35 = σ e4 + (τ - 1) e5`. Since `τ > 1`, `α = τ - 1 > 0`.
`⟪F.N 4, u⟫ = - α ⟪F.N 4, e5⟫ > 0` (`0 < N4`).
Along `e35`, `L(3) = L(5) > L(4)` so `⟪F.N 8, u_doc⟫ > 0`, hence `⟪F.N 8, u⟫ < 0` (`N8 < 0`).
Along `e35`, `⟪F.N 6, e35⟫ = 0`; `+ ε e4` gives `σ ⟪F.N 6, u_doc⟫ = - ε (τ - 1) c6 < 0`, so `0 < N6`.
`⟪F.N 7, e35⟫ = -f7(x5) > 0`, so `N7 < 0`. `e35` in positive orthant gives `0 < N5`.
All hypotheses strictly hold. -/
theorem rim6432_of_signs {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hN3 : ⟪F.N 3, u⟫ = 0)
    (hN8 : ⟪F.N 8, u⟫ < 0) (hN4 : 0 < ⟪F.N 4, u⟫)
    (hN7 : ⟪F.N 7, u⟫ < 0) (hN6 : 0 < ⟪F.N 6, u⟫)
    (hN5 : 0 < ⟪F.N 5, u⟫) :
    ∃ ρ : ℝ, ρ ≠ 0 ∧
      (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
        0 < ρ * det3 (quad (x 6) (x 4) (x 3) (x 2) (i + 1) - quad (x 6) (x 4) (x 3) (x 2) i)
          (quad (x 6) (x 4) (x 3) (x 2) j - quad (x 6) (x 4) (x 3) (x 2) i) u) ∧
      (∀ i : ZMod 4,
        0 < ρ * det3 (quad (x 6) (x 4) (x 3) (x 2) (i + 1) - quad (x 6) (x 4) (x 3) (x 2) i)
          (x 1 - quad (x 6) (x 4) (x 3) (x 2) i) u) := by
  have hne_64 := cross_ne_zero_of_facet_sign F 4 6 4 (by decide) (by decide) hN4.ne' 1 (by decide) (by decide)
  have hne_43 := cross_ne_zero_of_facet_sign F 8 4 3 (by decide) (by decide) hN8.ne 4 (by decide) (by decide)
  have hne_32 := cross_ne_zero_of_facet_sign F 6 3 2 (by decide) (by decide) hN6.ne' 8 (by decide) (by decide)
  have hne_26 := cross_ne_zero_of_facet_sign F 5 2 6 (by decide) (by decide) hN5.ne' 0 (by decide) (by decide)
  exact quadRim_of_signs F 6 4 3 2 8 4 7 6 7 5
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide) (by decide)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
    (Or.inr (by decide)) (Or.inl (by decide)) (Or.inl (by decide))
    (by decide) (by decide) (by decide)
    (Or.inl (by decide)) (Or.inr (by decide)) (Or.inl (by decide))
    (Or.inr (by decide)) (Or.inr (by decide)) (Or.inl (by decide))
    hne_64 hne_43 hne_32 hne_26
    ⟨hN8, hN4⟩ hN3 ⟨hN7, hN6⟩ ⟨hN7, hN5⟩

end Minimality.T24.Q45
