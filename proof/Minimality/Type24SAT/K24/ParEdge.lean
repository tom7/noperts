module

public import Minimality.RimCellClosed
public import Minimality.Type24SAT.K24.ParLeaves
public import Minimality.Type24SAT.K24.WallCI

@[expose] public section

/-!
# Type 24, `D` a parallelogram, `E ∥ G`: the view along the edge `23`

`u₀ = x 2 - x 3` (the ray `E^H = G^H` when `E ∥ G`).  Depths `z i = ⟪x i, u₀⟫`.
* `eg_decomp`: `E ∥ G` (`⟪N_E, x 2 - x 3⟫ = 0`) and the parallelogram give
  `x 4 - x 0 = -q (x 2 - x 3) + u (x 6 - x 0)` with `0 < q < 1`, `0 < u < 1`.
* `isRupert_eg_offWall`: if moreover `⟪x 5 - x 0, x 2 - x 3⟫ ≠ 0` (edge `05` not perpendicular to
  edge `23`), the solid is Rupert: for `< 0` the rim `0 5 3 6` (leaf P0536) has mixed diagonal signs
  at `u₀`, for `> 0` the rim `0 4 6 2 5` (leaf V04625) is robustly unimodal at `u₀`.
  No obtuse, off-OB1 or acute hypothesis.
* `isRupert_ci_offWall`: the image under `σ = (2 6)(4 5)` (`C ∥ I`, view along `63`, tie `z 4 = z 0`).
* `isRupert_eg_wall` / `isRupert_ci_wall`: on the wall, with `s = ⟪x 5 - x 0, x 6 - x 0⟫` and
  `h = ⟪x 6 - x 0, x 2 - x 3⟫`: Rupert if `s < 0`, `h < 0`, or `h, s > 0` (views `d`, `d + t (x 6 - x 0)`,
  `d + t (x 0 - x 6)` with the rims `0 5 3 6` and `0 5 3 2 6`).  Open: the wall with `s = 0, h ≥ 0`
  (`D` a rectangle perpendicular to `E` and `G`) or `h = 0, s ≥ 0` (`23` perpendicular to `05` and `06`).
-/

set_option autoImplicit false
open scoped RealInnerProductSpace Topology
open Filter
open Finset

namespace Minimality.T24.Par
open Minimality Minimality.H21 Minimality.T24.SAT

/-- A robustly unimodal 5-cycle `(v0, v4, v6, v2, v5)` (the rim `0 4 6 2 5` at the edge-23 view). -/
theorem robUni_v5 (z : ZMod 5 → ℝ) (v0 v4 v6 v2 v5 : ℝ) (e0 : z 0 = v0) (e1 : z 1 = v4)
    (e2 : z 2 = v6) (e3 : z 3 = v2) (e4 : z 4 = v5) (hz5 : v0 < v5)
    (f1 : v0 ≤ v6 → v4 < v6) (f2 : v0 ≤ v6 → v5 < v2) (f3 : v6 < v0 → v4 < v0)
    (f4 : v6 < v0 → v6 < v2) : RobUni z := by
  have tab : ((0 : ZMod 5) + 1 = 1) ∧
      ((0 : ZMod 5) + 2 = 2) ∧
      ((0 : ZMod 5) + 3 = 3) ∧
      ((0 : ZMod 5) + 4 = 4) ∧
      ((1 : ZMod 5) + 1 = 2) ∧
      ((1 : ZMod 5) + 2 = 3) ∧
      ((1 : ZMod 5) + 3 = 4) ∧
      ((1 : ZMod 5) + 4 = 0) ∧
      ((2 : ZMod 5) + 1 = 3) ∧
      ((2 : ZMod 5) + 2 = 4) ∧
      ((2 : ZMod 5) + 3 = 0) ∧
      ((2 : ZMod 5) + 4 = 1) ∧
      ((3 : ZMod 5) + 1 = 4) ∧
      ((3 : ZMod 5) + 2 = 0) ∧
      ((3 : ZMod 5) + 3 = 1) ∧
      ((3 : ZMod 5) + 4 = 2) ∧
      ((4 : ZMod 5) + 1 = 0) ∧
      ((4 : ZMod 5) + 2 = 1) ∧
      ((4 : ZMod 5) + 3 = 2) ∧
      ((4 : ZMod 5) + 4 = 3) := by decide
  obtain ⟨a01, a02, a03, a04, a11, a12, a13, a14, a21, a22, a23, a24, a31, a32, a33, a34, a41, a42, a43, a44⟩ := tab
  intro B b c d hb hbc hcd hd
  have hB : B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 ∨ B = 4 := by revert B; decide
  have hbcd : (b = 1 ∧ c = 2 ∧ d = 3) ∨ (b = 1 ∧ c = 2 ∧ d = 4) ∨ (b = 1 ∧ c = 3 ∧ d = 4) ∨
      (b = 2 ∧ c = 3 ∧ d = 4) := by omega
  rintro ⟨h1, h2, h3, h4⟩
  rcases hbcd with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
  rcases hB with rfl | rfl | rfl | rfl | rfl <;>
  simp only [Nat.cast_one, Nat.cast_ofNat, a01, a02, a03, a04, a11, a12, a13, a14, a21, a22, a23, a24, a31, a32, a33, a34, a41, a42, a43, a44] at h1 h2 h3 h4 <;>
  simp only [e0, e1, e2, e3, e4] at h1 h2 h3 h4 <;>
  rcases le_or_gt v0 v6 with h | h <;>
  first
  | (have := f1 h; have := f2 h; linarith)
  | (have := f3 h; have := f4 h; linarith)

/-- A robustly unimodal 5-cycle with one valley at `{1, 2}` and one peak at `{3, 4}`:
`z 0 > z 1`, `z 2 < z 3`, `z 4 > z 0`. -/
theorem robUni_v5b (z : ZMod 5 → ℝ) (h01 : z 1 < z 0) (h23 : z 2 < z 3) (h40 : z 0 < z 4) :
    RobUni z := by
  have tab : ((0 : ZMod 5) + 1 = 1) ∧
      ((0 : ZMod 5) + 2 = 2) ∧
      ((0 : ZMod 5) + 3 = 3) ∧
      ((0 : ZMod 5) + 4 = 4) ∧
      ((1 : ZMod 5) + 1 = 2) ∧
      ((1 : ZMod 5) + 2 = 3) ∧
      ((1 : ZMod 5) + 3 = 4) ∧
      ((1 : ZMod 5) + 4 = 0) ∧
      ((2 : ZMod 5) + 1 = 3) ∧
      ((2 : ZMod 5) + 2 = 4) ∧
      ((2 : ZMod 5) + 3 = 0) ∧
      ((2 : ZMod 5) + 4 = 1) ∧
      ((3 : ZMod 5) + 1 = 4) ∧
      ((3 : ZMod 5) + 2 = 0) ∧
      ((3 : ZMod 5) + 3 = 1) ∧
      ((3 : ZMod 5) + 4 = 2) ∧
      ((4 : ZMod 5) + 1 = 0) ∧
      ((4 : ZMod 5) + 2 = 1) ∧
      ((4 : ZMod 5) + 3 = 2) ∧
      ((4 : ZMod 5) + 4 = 3) := by decide
  obtain ⟨a01, a02, a03, a04, a11, a12, a13, a14, a21, a22, a23, a24, a31, a32, a33, a34, a41, a42, a43, a44⟩ := tab
  intro B b c d hb hbc hcd hd
  have hB : B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 ∨ B = 4 := by revert B; decide
  have hbcd : (b = 1 ∧ c = 2 ∧ d = 3) ∨ (b = 1 ∧ c = 2 ∧ d = 4) ∨ (b = 1 ∧ c = 3 ∧ d = 4) ∨
      (b = 2 ∧ c = 3 ∧ d = 4) := by omega
  rintro ⟨h1, h2, h3, h4⟩
  rcases hbcd with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
  rcases hB with rfl | rfl | rfl | rfl | rfl <;>
  simp only [Nat.cast_one, Nat.cast_ofNat, a01, a02, a03, a04, a11, a12, a13, a14, a21, a22, a23, a24, a31, a32, a33, a34, a41, a42, a43, a44] at h1 h2 h3 h4 <;>
  linarith

variable {x : Fin 7 → ℝ³}

/-- **`E ∥ G` and the parallelogram, in the plane of `E`.**  `x 4 - x 0 = -q (x 2 - x 3) + u (x 6 - x 0)`
with `0 < q < 1`, `0 < u < 1` (from the facets `C D H I`). -/
theorem eg_decomp (F : S0xFac 9 s0x_S24 x) (hP : x 3 = x 4 + x 5 - x 0)
    (hE : ⟪F.N 4, x 2 - x 3⟫ = 0) :
    ∃ q u : ℝ, 0 < q ∧ q < 1 ∧ 0 < u ∧ u < 1 ∧
      x 4 - x 0 = -q • (x 2 - x 3) + u • (x 6 - x 0) := by
  have IS := F.inner_sub
  -- facet values
  have hH0 := F.neg 7 0 (by decide); have hH4 := F.neg 7 4 (by decide)
  have zH2 := F.zero 7 2 (by decide); have zH3 := F.zero 7 3 (by decide)
  have zH6 := F.zero 7 6 (by decide)
  have hI0 := F.neg 8 0 (by decide); have hI2 := F.neg 8 2 (by decide)
  have zI3 := F.zero 8 3 (by decide); have zI4 := F.zero 8 4 (by decide)
  have zI6 := F.zero 8 6 (by decide)
  have hD2 := F.neg 3 2 (by decide); have hD6 := F.neg 3 6 (by decide)
  have zD0 := F.zero 3 0 (by decide); have zD3 := F.zero 3 3 (by decide)
  have zD4 := F.zero 3 4 (by decide)
  have hC3 := F.neg 2 3 (by decide); have hC4 := F.neg 2 4 (by decide)
  have hC6 := F.neg 2 6 (by decide)
  have zC0 := F.zero 2 0 (by decide); have zC2 := F.zero 2 2 (by decide)
  have zC5 := F.zero 2 5 (by decide)
  have hE3 := F.neg 4 3 (by decide)
  have zE0 := F.zero 4 0 (by decide); have zE4 := F.zero 4 4 (by decide)
  have zE6 := F.zero 4 6 (by decide)
  obtain ⟨u, hu'⟩ : ∃ u : ℝ, u * (-F.f 7 (x 0)) = F.f 7 (x 4) - F.f 7 (x 0) :=
    ⟨_, div_mul_cancel₀ _ (by linarith)⟩
  have hu1 : u < 1 := by
    by_contra h; push Not at h
    linarith only [hu', hH4, mul_le_mul_of_nonneg_right h (by linarith : (0:ℝ) ≤ -F.f 7 (x 0))]
  obtain ⟨q, hq'⟩ : ∃ q : ℝ, q * F.f 8 (x 2) = F.f 8 (x 0) * (1 - u) :=
    ⟨_, div_mul_cancel₀ _ hI2.ne⟩
  have hq0 : 0 < q := by
    by_contra h; push Not at h
    linarith only [hq', mul_nonneg_of_nonpos_of_nonpos h hI2.le, mul_pos (neg_pos.2 hI0) (sub_pos.2 hu1)]
  -- the vector identity
  set v : ℝ³ := (x 4 - x 0) + q • (x 2 - x 3) - u • (x 6 - x 0) with hv
  have ev : ∀ t, ⟪F.N t, v⟫ = ⟪F.N t, x 4 - x 0⟫ + q * ⟪F.N t, x 2 - x 3⟫ - u * ⟪F.N t, x 6 - x 0⟫ := by
    intro t; rw [hv, inner_sub_right, inner_add_right, inner_smul_right, inner_smul_right]
  have vH : ⟪F.N 7, v⟫ = 0 := by
    rw [ev, IS, IS, IS, zH2, zH3, zH6]; linarith
  have vI : ⟪F.N 8, v⟫ = 0 := by
    rw [ev, IS, IS, IS, zI3, zI4, zI6]; linarith
  have vE : ⟪F.N 4, v⟫ = 0 := by
    rw [ev, hE, IS, IS, zE0, zE4, zE6]; ring
  have hcr : cross (F.N 7) (F.N 8) ≠ 0 := by
    intro h
    have hb := h21_binet (F.N 7) (F.N 8) (x 0 - x 3) (x 2 - x 3)
    rw [h, inner_zero_left, IS, IS, IS, IS, zH2, zH3, zI3] at hb
    nlinarith only [hb, mul_pos (neg_pos.2 hH0) (neg_pos.2 hI2)]
  obtain ⟨μ, hμ⟩ := h21_mul_cross hcr vH vI
  obtain ⟨l, hl⟩ := h21_mul_cross hcr
    (by rw [IS, zH6, zH3]; ring : ⟪F.N 7, x 6 - x 3⟫ = 0)
    (by rw [IS, zI6, zI3]; ring : ⟪F.N 8, x 6 - x 3⟫ = 0)
  have hEc : ⟪F.N 4, cross (F.N 7) (F.N 8)⟫ ≠ 0 := by
    intro h0
    have : ⟪F.N 4, x 6 - x 3⟫ = 0 := by rw [hl, inner_smul_right, h0, mul_zero]
    rw [IS, zE6] at this; linarith
  have hv0 : v = 0 := by
    have : μ * ⟪F.N 4, cross (F.N 7) (F.N 8)⟫ = 0 := by
      rw [← inner_smul_right, ← hμ, vE]
    rcases mul_eq_zero.1 this with h | h
    · rw [hμ, h, zero_smul]
    · exact absurd h hEc
  have hdec : x 4 - x 0 = -q • (x 2 - x 3) + u • (x 6 - x 0) := by
    have := hv0; rw [hv] at this
    rw [neg_smul]; linear_combination (norm := module) this
  have ed : ∀ t, ⟪F.N t, x 4 - x 0⟫ = -q * ⟪F.N t, x 2 - x 3⟫ + u * ⟪F.N t, x 6 - x 0⟫ := by
    intro t; rw [hdec, inner_add_right, inner_smul_right, inner_smul_right]
  -- u > 0 from D
  have eD := ed 3
  rw [IS, IS, IS, zD4, zD0, zD3] at eD
  have hu0 : 0 < u := by
    by_contra h; push Not at h
    linarith only [eD, mul_nonneg_of_nonpos_of_nonpos h hD6.le, mul_pos hq0 (neg_pos.2 hD2)]
  -- q < 1 from C and the parallelogram
  have eC := ed 2
  rw [IS, IS, IS, zC0, zC2] at eC
  have hC34 : F.f 2 (x 3) = F.f 2 (x 4) := by
    have h1 := IS 2 3 0
    have e : x 3 - x 0 = (x 4 - x 0) + (x 5 - x 0) := by rw [hP]; abel
    rw [e, inner_add_right, IS, IS, zC0, zC5] at h1
    linarith
  rw [hC34] at eC
  have hq1 : q < 1 := by
    by_contra h; push Not at h
    linarith only [eC, mul_nonneg (sub_nonneg.2 h) (neg_nonneg.2 hC4.le), mul_pos hu0 (neg_pos.2 hC6)]
  exact ⟨q, u, hq0, hq1, hu0, hu1, hdec⟩

open Minimality.RimCell in
/-- **Type 24, `D` a parallelogram, `E ∥ G`, off the wall: Rupert.**  `E ∥ G` is stated as
`⟪N_E, x 2 - x 3⟫ = 0` (edge `23` parallel to `E`); the wall is `⟪x 5 - x 0, x 2 - x 3⟫ = 0`
(edge `05` perpendicular to edge `23`).  One view, `x 2 - x 3`: leaf P0536 on one side, leaf V04625
on the other. -/
theorem isRupert_eg_offWall (F : S0xFac 9 s0x_S24 x) (hP : x 3 = x 4 + x 5 - x 0)
    (hE : ⟪F.N 4, x 2 - x 3⟫ = 0) (hw : ⟪x 5 - x 0, x 2 - x 3⟫ ≠ 0) :
    IsRupert (univ.image x) := by
  obtain ⟨q, u, hq0, hq1, hu0, hu1, hdec⟩ := eg_decomp F hP hE
  have IS := F.inner_sub
  have hx := Minimality.H24.SAT.inj_of_fac F
  set d := x 2 - x 3 with hd
  have ha : 0 < ⟪d, d⟫ := by
    have : d ≠ 0 := fun h => absurd (hx (sub_eq_zero.1 h)) (by decide)
    exact real_inner_self_pos.2 this
  have e3 : ⟪x 3, d⟫ = ⟪x 4, d⟫ + ⟪x 5, d⟫ - ⟪x 0, d⟫ := by
    rw [hP, inner_sub_left, inner_add_left]
  have e2 : ⟪x 2, d⟫ = ⟪x 3, d⟫ + ⟪d, d⟫ := by
    have : ⟪d, d⟫ = ⟪x 2, d⟫ - ⟪x 3, d⟫ := by
      conv_lhs => rw [hd]
      rw [inner_sub_left]
    linarith
  have e4 : ⟪x 4, d⟫ - ⟪x 0, d⟫ = -q * ⟪d, d⟫ + u * (⟪x 6, d⟫ - ⟪x 0, d⟫) := by
    have h := congrArg (fun v => ⟪v, d⟫) hdec
    simp only [inner_add_left, inner_smul_left, inner_sub_left, RCLike.conj_to_real] at h
    linarith
  have hw' : ⟪x 5, d⟫ - ⟪x 0, d⟫ ≠ 0 := by rwa [← inner_sub_left]
  have qa := mul_pos hq0 ha
  -- facet values
  have zB0 := F.zero 1 0 (by decide); have zB6 := F.zero 1 6 (by decide)
  have hB4 := F.neg 1 4 (by decide)
  have zC2 := F.zero 2 2 (by decide); have hC3 := F.neg 2 3 (by decide)
  have zD3 := F.zero 3 3 (by decide); have hD2 := F.neg 3 2 (by decide)
  have zE0 := F.zero 4 0 (by decide); have hE2 := F.neg 4 2 (by decide)
  have zF2 := F.zero 5 2 (by decide); have hF3 := F.neg 5 3 (by decide)
  have zG2 := F.zero 6 2 (by decide); have zG3 := F.zero 6 3 (by decide)
  have hG0 := F.neg 6 0 (by decide)
  have zH2 := F.zero 7 2 (by decide); have zH3 := F.zero 7 3 (by decide)
  have hH0 := F.neg 7 0 (by decide)
  have zI3 := F.zero 8 3 (by decide); have hI2 := F.neg 8 2 (by decide)
  -- B faces up along d (from the decomposition)
  have hBd : 0 < ⟪F.N 1, d⟫ := by
    have h1 : ⟪F.N 1, x 4 - x 0⟫ = -q * ⟪F.N 1, d⟫ + u * ⟪F.N 1, x 6 - x 0⟫ := by
      rw [hdec, inner_add_right, inner_smul_right, inner_smul_right]
    rw [IS, IS 1 6 0, zB0, zB6] at h1
    by_contra h; push Not at h
    linarith [mul_nonneg hq0.le (neg_nonneg.2 h)]
  have dC : ⟪F.N 2, d⟫ = -F.f 2 (x 3) := by rw [hd, IS, zC2]; ring
  have dD : ⟪F.N 3, d⟫ = F.f 3 (x 2) := by rw [hd, IS, zD3]; ring
  have dF : ⟪F.N 5, d⟫ = -F.f 5 (x 3) := by rw [hd, IS, zF2]; ring
  have dG : ⟪F.N 6, d⟫ = 0 := by rw [hd, IS, zG2, zG3]; ring
  have dH : ⟪F.N 7, d⟫ = 0 := by rw [hd, IS, zH2, zH3]; ring
  have dI : ⟪F.N 8, d⟫ = F.f 8 (x 2) := by rw [hd, IS, zI3]; ring
  rcases lt_or_gt_of_ne hw' with h5 | h5
  · -- z5 < z0: leaf P0536 at the closed-cell point d, tilt x 2 - x 0
    have tE : ⟪F.N 4, x 2 - x 0⟫ = F.f 4 (x 2) := by rw [IS, zE0]; ring
    have tG : ⟪F.N 6, x 2 - x 0⟫ = -F.f 6 (x 0) := by rw [IS, zG2]; ring
    have tH : ⟪F.N 7, x 2 - x 0⟫ = -F.f 7 (x 0) := by rw [IS, zH2]; ring
    obtain ⟨a, hA⟩ := exists_cellAt_of_lex (F := F) (U := U0536) (Dn := D0536) (u₀ := d)
      (v := x 2 - x 0)
      (by
        intro t ht; simp only [U0536, Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl | rfl
        · exact Or.inl hBd
        · exact Or.inl (by rw [dC]; linarith)
        · exact Or.inr ⟨dG, by rw [tG]; linarith⟩
        · exact Or.inr ⟨dH, by rw [tH]; linarith⟩)
      (by
        intro t ht; simp only [D0536, Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl
        · exact Or.inl (by rw [dD]; linarith)
        · exact Or.inr ⟨by rw [hE]; simp, by rw [tE]; linarith⟩
        · exact Or.inl (by rw [dI]; linarith))
    have hle : CellLe F U0536 D0536 d := by
      refine ⟨fun t ht => ?_, fun t ht => ?_⟩
      · simp only [U0536, Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl | rfl
        · exact hBd.le
        · rw [dC]; linarith
        · rw [dG]
        · rw [dH]
      · simp only [D0536, Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl
        · rw [dD]; linarith
        · rw [hE]
        · rw [dI]; linarith
    have c0 : c0536 0 = 0 := rfl
    have c1 : c0536 1 = 5 := rfl
    have c2 : c0536 2 = 3 := rfl
    have c3 : c0536 3 = 6 := rfl
    refine isRupert_of_closedCell le_rfl F hx (by decide) cyc0536 hA hle
      (robUni_four_of_mixed ?_ ⟨(0, 1), by decide, by simp only [c0, c1]; linarith⟩)
    rcases lt_or_ge ⟪x 0, d⟫ ⟪x 6, d⟫ with h6 | h6
    · exact ⟨(0, 3), by decide, by simp only [c0, c3]; linarith⟩
    · refine ⟨(2, 1), by decide, ?_⟩
      simp only [c2, c1]
      linarith [mul_nonneg hu0.le (sub_nonneg.2 h6)]
  · -- z5 > z0: leaf V04625 at d, tilt x 0 - x 2
    have tE : ⟪F.N 4, x 0 - x 2⟫ = -F.f 4 (x 2) := by rw [IS, zE0]; ring
    have tG : ⟪F.N 6, x 0 - x 2⟫ = F.f 6 (x 0) := by rw [IS, zG2]; ring
    have tH : ⟪F.N 7, x 0 - x 2⟫ = F.f 7 (x 0) := by rw [IS, zH2]; ring
    obtain ⟨a, hA⟩ := exists_cellAt_of_lex (F := F) (U := U04625) (Dn := D04625) (u₀ := d)
      (v := x 0 - x 2)
      (by
        intro t ht; simp only [U04625, Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl
        · exact Or.inl (by rw [dC]; linarith)
        · exact Or.inr ⟨hE, by rw [tE]; linarith⟩
        · exact Or.inl (by rw [dF]; linarith))
      (by
        intro t ht; simp only [D04625, Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl | rfl
        · exact Or.inl (by rw [dD]; linarith)
        · exact Or.inr ⟨by rw [dG]; simp, by rw [tG]; linarith⟩
        · exact Or.inr ⟨by rw [dH]; simp, by rw [tH]; linarith⟩
        · exact Or.inl (by rw [dI]; linarith))
    have hle : CellLe F U04625 D04625 d := by
      refine ⟨fun t ht => ?_, fun t ht => ?_⟩
      · simp only [U04625, Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl
        · rw [dC]; linarith
        · rw [hE]
        · rw [dF]; linarith
      · simp only [D04625, Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl | rfl
        · rw [dD]; linarith
        · rw [dG]
        · rw [dH]
        · rw [dI]; linarith
    refine isRupert_of_closedCell (by norm_num) F hx (by decide) cyc04625 hA hle
      (robUni_v5 _ ⟪x 0, d⟫ ⟪x 4, d⟫ ⟪x 6, d⟫ ⟪x 2, d⟫ ⟪x 5, d⟫ rfl rfl rfl rfl rfl (by linarith)
        ?_ ?_ ?_ ?_)
    · intro h; linarith [mul_nonneg (sub_nonneg.2 hu1.le) (sub_nonneg.2 h)]
    · intro h; linarith [mul_nonneg hu0.le (sub_nonneg.2 h), mul_pos (sub_pos.2 hq1) ha]
    · intro h; linarith [mul_nonneg hu0.le (sub_nonneg.2 h.le)]
    · intro h; linarith [mul_nonneg (sub_nonneg.2 hu1.le) (sub_nonneg.2 h.le), mul_pos (sub_pos.2 hq1) ha]

open Minimality.RimCell in
/-- **The wall `05 ⊥ 23`.**  Type 24, `D` a parallelogram, `E ∥ G`, `⟪x 5 - x 0, x 2 - x 3⟫ = 0`,
and with `s = ⟪x 5 - x 0, x 6 - x 0⟫`, `h = ⟪x 6 - x 0, x 2 - x 3⟫`: `s < 0`, or `h < 0`, or
`h > 0` and `s > 0`.  Then Rupert: for `h < 0` leaf P0536 at `d = x 2 - x 3`; for `s < 0` leaf
P0536 at `d + t (x 6 - x 0)`; for `h, s > 0` the rim `0 5 3 2 6` at `d + t (x 0 - x 6)` (small `t > 0`). -/
theorem isRupert_eg_wall (F : S0xFac 9 s0x_S24 x) (hP : x 3 = x 4 + x 5 - x 0)
    (hE : ⟪F.N 4, x 2 - x 3⟫ = 0) (hw : ⟪x 5 - x 0, x 2 - x 3⟫ = 0)
    (hs : ⟪x 5 - x 0, x 6 - x 0⟫ < 0 ∨ ⟪x 6 - x 0, x 2 - x 3⟫ < 0 ∨
      (0 < ⟪x 6 - x 0, x 2 - x 3⟫ ∧ 0 < ⟪x 5 - x 0, x 6 - x 0⟫)) :
    IsRupert (univ.image x) := by
  obtain ⟨q, u, hq0, hq1, hu0, hu1, hdec⟩ := eg_decomp F hP hE
  have IS := F.inner_sub
  have hx := Minimality.H24.SAT.inj_of_fac F
  set d := x 2 - x 3 with hd
  have ha : 0 < ⟪d, d⟫ := by
    have : d ≠ 0 := fun h => absurd (hx (sub_eq_zero.1 h)) (by decide)
    exact real_inner_self_pos.2 this
  have lin : ∀ (p w : ℝ³) (t : ℝ), ⟪p, d + t • w⟫ = ⟪p, d⟫ + t * ⟪p, w⟫ := by
    intro p w t; rw [inner_add_right, inner_smul_right]
  have e4 : ⟪x 4 - x 0, d⟫ = -q * ⟪d, d⟫ + u * ⟪x 6 - x 0, d⟫ := by
    rw [hdec, inner_add_left, inner_smul_left, inner_smul_left]; simp
  have e35 : x 3 - x 5 = x 4 - x 0 := by rw [hP]; abel
  -- depth differences at d
  have f23 : ⟪x 3 - x 5, d⟫ = ⟪x 4 - x 0, d⟫ := by rw [e35]
  have f36 : ⟪x 3 - x 6, d⟫ = ⟪x 4 - x 0, d⟫ - ⟪x 6 - x 0, d⟫ + ⟪x 5 - x 0, d⟫ := by
    rw [show x 3 - x 6 = (x 4 - x 0) - (x 6 - x 0) + (x 5 - x 0) by rw [hP]; abel,
      inner_add_left, inner_sub_left]
  have f05 : ⟪x 0 - x 5, d⟫ = 0 := by
    rw [show x 0 - x 5 = -(x 5 - x 0) by abel, inner_neg_left, hw, neg_zero]
  -- facet values
  have zB0 := F.zero 1 0 (by decide); have zB6 := F.zero 1 6 (by decide)
  have hB4 := F.neg 1 4 (by decide)
  have zC0 := F.zero 2 0 (by decide); have zC2 := F.zero 2 2 (by decide)
  have hC3 := F.neg 2 3 (by decide)
  have zD3 := F.zero 3 3 (by decide); have hD2 := F.neg 3 2 (by decide)
  have zE0 := F.zero 4 0 (by decide); have zE6 := F.zero 4 6 (by decide)
  have hE2 := F.neg 4 2 (by decide)
  have zF2 := F.zero 5 2 (by decide); have hF3 := F.neg 5 3 (by decide)
  have zG2 := F.zero 6 2 (by decide); have zG3 := F.zero 6 3 (by decide)
  have zG5 := F.zero 6 5 (by decide); have hG0 := F.neg 6 0 (by decide)
  have hG6 := F.neg 6 6 (by decide)
  have zH2 := F.zero 7 2 (by decide); have zH3 := F.zero 7 3 (by decide)
  have zH6 := F.zero 7 6 (by decide); have hH0 := F.neg 7 0 (by decide)
  have zI3 := F.zero 8 3 (by decide); have hI2 := F.neg 8 2 (by decide)
  have hBd : 0 < ⟪F.N 1, d⟫ := by
    have h1 : ⟪F.N 1, x 4 - x 0⟫ = -q * ⟪F.N 1, d⟫ + u * ⟪F.N 1, x 6 - x 0⟫ := by
      rw [hdec, inner_add_right, inner_smul_right, inner_smul_right]
    rw [IS, IS 1 6 0, zB0, zB6] at h1
    by_contra h; push Not at h
    linarith [mul_nonneg hq0.le (neg_nonneg.2 h)]
  have dC : ⟪F.N 2, d⟫ = -F.f 2 (x 3) := by rw [hd, IS, zC2]; ring
  have dD : ⟪F.N 3, d⟫ = F.f 3 (x 2) := by rw [hd, IS, zD3]; ring
  have dF : ⟪F.N 5, d⟫ = -F.f 5 (x 3) := by rw [hd, IS, zF2]; ring
  have dG : ⟪F.N 6, d⟫ = 0 := by rw [hd, IS, zG2, zG3]; ring
  have dH : ⟪F.N 7, d⟫ = 0 := by rw [hd, IS, zH2, zH3]; ring
  have dI : ⟪F.N 8, d⟫ = F.f 8 (x 2) := by rw [hd, IS, zI3]; ring
  -- G is parallel to E: `⟪N_G, x 6 - x 0⟫ = 0`
  have G60 : ⟪F.N 6, x 6 - x 0⟫ = 0 := by
    have h1 : ⟪F.N 6, x 4 - x 0⟫ = -q * ⟪F.N 6, d⟫ + u * ⟪F.N 6, x 6 - x 0⟫ := by
      rw [hdec, inner_add_right, inner_smul_right, inner_smul_right]
    rw [← e35, IS, zG3, zG5, dG] at h1
    have : u * ⟪F.N 6, x 6 - x 0⟫ = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hu0.ne'
    · exact h
  have B60 : ⟪F.N 1, x 6 - x 0⟫ = 0 := by rw [IS, zB6, zB0]; ring
  have E60 : ⟪F.N 4, x 6 - x 0⟫ = 0 := by rw [IS, zE6, zE0]; ring
  have H60 : ⟪F.N 7, x 6 - x 0⟫ = -F.f 7 (x 0) := by rw [IS, zH6]; ring
  -- the P0536 cell point
  obtain ⟨aP, hAP⟩ := exists_cellAt_of_lex (F := F) (U := U0536) (Dn := D0536) (u₀ := d)
    (v := x 2 - x 0)
    (by
      intro t ht; simp only [U0536, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl
      · exact Or.inl hBd
      · exact Or.inl (by rw [dC]; linarith)
      · exact Or.inr ⟨dG, by rw [IS, zG2]; linarith⟩
      · exact Or.inr ⟨dH, by rw [IS, zH2]; linarith⟩)
    (by
      intro t ht; simp only [D0536, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      · exact Or.inl (by rw [dD]; linarith)
      · exact Or.inr ⟨by rw [hE]; simp, by rw [IS, zE0]; linarith⟩
      · exact Or.inl (by rw [dI]; linarith))
  have c0 : c0536 0 = 0 := rfl
  have c1 : c0536 1 = 5 := rfl
  have c2 : c0536 2 = 3 := rfl
  have c3 : c0536 3 = 6 := rfl
  rcases hs with hs | hh | ⟨hh, hs⟩
  · -- s < 0: P0536 at d + t (x 6 - x 0)
    by_cases hh : ⟪x 6 - x 0, d⟫ < 0
    · -- already mixed at d
      refine isRupert_of_closedCell (u₀ := d) le_rfl F hx (by decide) cyc0536 hAP ?_
        (robUni_four_of_mixed ?_ ?_)
      · refine ⟨fun t ht => ?_, fun t ht => ?_⟩
        · simp only [U0536, Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with rfl | rfl | rfl | rfl
          · exact hBd.le
          · rw [dC]; linarith
          · rw [dG]
          · rw [dH]
        · simp only [D0536, Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with rfl | rfl | rfl
          · rw [dD]; linarith
          · rw [hE]
          · rw [dI]; linarith
      · refine ⟨(2, 1), by decide, ?_⟩
        simp only [c2, c1]; rw [← inner_sub_left, f23, e4]
        linarith [mul_pos hq0 ha, mul_pos hu0 (neg_pos.2 hh)]
      · refine ⟨(0, 3), by decide, ?_⟩
        simp only [c0, c3]; rw [← inner_sub_left]
        rw [show x 0 - x 6 = -(x 6 - x 0) by abel, inner_neg_left]; linarith
    push Not at hh
    have h36 : ⟪x 3 - x 6, d⟫ < 0 := by
      rw [f36, e4, hw]
      linarith [mul_pos hq0 ha, mul_nonneg (sub_nonneg.2 hu1.le) hh]
    have g1 := eventually_pos_affine (B := ⟪F.N 2, x 6 - x 0⟫)
      (Or.inl (by rw [dC]; linarith : 0 < ⟪F.N 2, d⟫))
    have g2 := eventually_pos_affine (B := -⟪F.N 3, x 6 - x 0⟫)
      (Or.inl (by rw [dD]; linarith : 0 < -⟪F.N 3, d⟫))
    have g3 := eventually_pos_affine (B := -⟪F.N 8, x 6 - x 0⟫)
      (Or.inl (by rw [dI]; linarith : 0 < -⟪F.N 8, d⟫))
    have g4 := eventually_pos_affine (B := -⟪x 3 - x 6, x 6 - x 0⟫)
      (Or.inl (by linarith : 0 < -⟪x 3 - x 6, d⟫))
    have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), (0 < ⟪F.N 2, d + t • (x 6 - x 0)⟫ ∧
        0 < -⟪F.N 3, d + t • (x 6 - x 0)⟫ ∧ 0 < -⟪F.N 8, d + t • (x 6 - x 0)⟫ ∧
        0 < -⟪x 3 - x 6, d + t • (x 6 - x 0)⟫) ∧ 0 < t := by
      filter_upwards [g1, g2, g3, g4, self_mem_nhdsWithin] with t h1 h2 h3 h4 ht
      refine ⟨⟨?_, ?_, ?_, ?_⟩, ht⟩
      · rw [lin]; exact h1
      · rw [lin]; linarith
      · rw [lin]; linarith
      · rw [lin]; linarith
    obtain ⟨t, ⟨h1, h2, h3, h4⟩, ht⟩ := hev.exists
    refine isRupert_of_closedCell (u₀ := d + t • (x 6 - x 0)) le_rfl F hx (by decide) cyc0536 hAP ?_
      (robUni_four_of_mixed ⟨(2, 3), by decide, ?_⟩ ⟨(0, 1), by decide, ?_⟩)
    · refine ⟨fun r hr => ?_, fun r hr => ?_⟩
      · simp only [U0536, Finset.mem_insert, Finset.mem_singleton] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · rw [lin, B60]; linarith
        · exact h1.le
        · rw [lin, dG, G60]; simp
        · rw [lin, dH, H60]; linarith [mul_pos ht (neg_pos.2 hH0)]
      · simp only [D0536, Finset.mem_insert, Finset.mem_singleton] at hr
        rcases hr with rfl | rfl | rfl
        · linarith
        · rw [lin, hE, E60]; simp
        · linarith
    · simp only [c2, c3]; rw [← inner_sub_left]; linarith
    · simp only [c0, c1]; rw [← inner_sub_left, lin, f05]
      rw [show x 0 - x 5 = -(x 5 - x 0) by abel, inner_neg_left]; linarith [mul_pos ht (neg_pos.2 hs)]
  · -- h < 0: P0536 at d
    refine isRupert_of_closedCell (u₀ := d) le_rfl F hx (by decide) cyc0536 hAP ?_
      (robUni_four_of_mixed ?_ ?_)
    · refine ⟨fun t ht => ?_, fun t ht => ?_⟩
      · simp only [U0536, Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl | rfl
        · exact hBd.le
        · rw [dC]; linarith
        · rw [dG]
        · rw [dH]
      · simp only [D0536, Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl
        · rw [dD]; linarith
        · rw [hE]
        · rw [dI]; linarith
    · refine ⟨(2, 1), by decide, ?_⟩
      simp only [c2, c1]; rw [← inner_sub_left, f23, e4]
      linarith [mul_pos hq0 ha, mul_pos hu0 (neg_pos.2 hh)]
    · refine ⟨(0, 3), by decide, ?_⟩
      simp only [c0, c3]; rw [← inner_sub_left]
      rw [show x 0 - x 6 = -(x 6 - x 0) by abel, inner_neg_left]; linarith
  · -- h > 0, s > 0: rim 0 5 3 2 6 at d + t (x 0 - x 6)
    obtain ⟨aR, hAR⟩ := exists_cellAt_of_lex (F := F) (U := U05326) (Dn := D05326) (u₀ := d)
      (v := (x 2 - x 6) + (x 0 - x 6))
      (by
        intro t ht; simp only [U05326, Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl | rfl
        · exact Or.inl hBd
        · exact Or.inl (by rw [dC]; linarith)
        · exact Or.inl (by rw [dF]; linarith)
        · refine Or.inr ⟨dG, ?_⟩
          rw [inner_add_right, IS, zG2, show x 0 - x 6 = -(x 6 - x 0) by abel, inner_neg_right,
            G60]; linarith)
      (by
        intro t ht; simp only [D05326, Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl
        · exact Or.inl (by rw [dD]; linarith)
        · refine Or.inr ⟨by rw [hE]; simp, ?_⟩
          rw [inner_add_right, IS, zE6, show x 0 - x 6 = -(x 6 - x 0) by abel, inner_neg_right,
            E60]; linarith
        · refine Or.inr ⟨by rw [dH]; simp, ?_⟩
          rw [inner_add_right, IS, zH2, zH6, show x 0 - x 6 = -(x 6 - x 0) by abel,
            inner_neg_right, H60]; linarith)
    have g1 := eventually_pos_affine (B := ⟪F.N 2, x 0 - x 6⟫)
      (Or.inl (by rw [dC]; linarith : 0 < ⟪F.N 2, d⟫))
    have g2 := eventually_pos_affine (B := ⟪F.N 5, x 0 - x 6⟫)
      (Or.inl (by rw [dF]; linarith : 0 < ⟪F.N 5, d⟫))
    have g3 := eventually_pos_affine (B := -⟪F.N 3, x 0 - x 6⟫)
      (Or.inl (by rw [dD]; linarith : 0 < -⟪F.N 3, d⟫))
    have g4 := eventually_pos_affine (B := ⟪d, x 0 - x 6⟫) (Or.inl ha)
    have g5 := eventually_pos_affine (B := ⟪x 6 - x 0, x 0 - x 6⟫) (Or.inl hh)
    have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), (0 < ⟪F.N 2, d + t • (x 0 - x 6)⟫ ∧
        0 < ⟪F.N 5, d + t • (x 0 - x 6)⟫ ∧ 0 < -⟪F.N 3, d + t • (x 0 - x 6)⟫ ∧
        0 < ⟪d, d + t • (x 0 - x 6)⟫ ∧ 0 < ⟪x 6 - x 0, d + t • (x 0 - x 6)⟫) ∧ 0 < t := by
      filter_upwards [g1, g2, g3, g4, g5, self_mem_nhdsWithin] with t h1 h2 h3 h4 h5 ht
      refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ht⟩
      · rw [lin]; exact h1
      · rw [lin]; exact h2
      · rw [lin]; linarith
      · rw [lin]; exact h4
      · rw [lin]; exact h5
    obtain ⟨t, ⟨h1, h2, h3, h4, h5⟩, ht⟩ := hev.exists
    have r0 : c05326 0 = 0 := rfl
    have r1 : c05326 1 = 5 := rfl
    have r2 : c05326 2 = 3 := rfl
    have r3 : c05326 3 = 2 := rfl
    have r4 : c05326 4 = 6 := rfl
    refine isRupert_of_closedCell (u₀ := d + t • (x 0 - x 6)) (by norm_num) F hx (by decide) cyc05326 hAR ?_
      (robUni_v5b _ ?_ ?_ ?_)
    · have N60 : ∀ r, ⟪F.N r, x 0 - x 6⟫ = -⟪F.N r, x 6 - x 0⟫ := fun r => by
        rw [show x 0 - x 6 = -(x 6 - x 0) by abel, inner_neg_right]
      refine ⟨fun r hr => ?_, fun r hr => ?_⟩
      · simp only [U05326, Finset.mem_insert, Finset.mem_singleton] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · rw [lin, N60, B60]; linarith
        · exact h1.le
        · exact h2.le
        · rw [lin, N60, dG, G60]; simp
      · simp only [D05326, Finset.mem_insert, Finset.mem_singleton] at hr
        rcases hr with rfl | rfl | rfl
        · linarith
        · rw [lin, N60, hE, E60]; simp
        · rw [lin, N60, dH, H60]; linarith [mul_pos ht (neg_pos.2 hH0)]
    · simp only [r0, r1]
      have : 0 < ⟪x 0 - x 5, d + t • (x 0 - x 6)⟫ := by
        rw [lin, f05, show x 0 - x 5 = -(x 5 - x 0) by abel,
          show x 0 - x 6 = -(x 6 - x 0) by abel, inner_neg_left, inner_neg_right, neg_neg]
        linarith [mul_pos ht hs]
      rw [inner_sub_left] at this; linarith
    · simp only [r2, r3]
      have := h4; rw [hd, inner_sub_left] at this; linarith
    · simp only [r0, r4]
      have := h5; rw [inner_sub_left] at this; linarith

open Minimality.H24K.SAT in
/-- **Type 24, `D` a parallelogram, `C ∥ I`, off the wall: Rupert** (the image of
`isRupert_eg_offWall` under `σ = (2 6)(4 5)`): `C ∥ I` as `⟪N_C, x 6 - x 3⟫ = 0`, the wall is
`⟪x 4 - x 0, x 6 - x 3⟫ = 0` (edge `04` perpendicular to edge `36`); the view is `x 6 - x 3`, the
leaves are P0234 (rim `0 4 3 2`, the image of `0 5 3 6`) and V04625 (σ-invariant). -/
theorem isRupert_ci_offWall (F : S0xFac 9 s0x_S24 x) (hP : x 3 = x 4 + x 5 - x 0)
    (hC : ⟪F.N 2, x 6 - x 3⟫ = 0) (hw : ⟪x 4 - x 0, x 6 - x 3⟫ ≠ 0) :
    IsRupert (univ.image x) := by
  have h := isRupert_eg_offWall (facSig F) (x := x ∘ wallSig)
    (by show x 3 = x 5 + x 4 - x 0; rw [hP]; abel) hC hw
  have e : Finset.univ.image (x ∘ wallSig) = Finset.univ.image x := by
    ext y
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp]
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨_, rfl⟩
    · rintro ⟨i, rfl⟩; exact ⟨wallSig i, by rw [wallSig_invol]⟩
  rwa [e] at h

open Minimality.H24K.SAT in
/-- **The wall `04 ⊥ 36` of `C ∥ I`** (the image of `isRupert_eg_wall` under `σ = (2 6)(4 5)`):
`⟪x 4 - x 0, x 6 - x 3⟫ = 0` and, with `s = ⟪x 4 - x 0, x 2 - x 0⟫`, `h = ⟪x 2 - x 0, x 6 - x 3⟫`:
`s < 0`, or `h < 0`, or `h > 0` and `s > 0`. -/
theorem isRupert_ci_wall (F : S0xFac 9 s0x_S24 x) (hP : x 3 = x 4 + x 5 - x 0)
    (hC : ⟪F.N 2, x 6 - x 3⟫ = 0) (hw : ⟪x 4 - x 0, x 6 - x 3⟫ = 0)
    (hs : ⟪x 4 - x 0, x 2 - x 0⟫ < 0 ∨ ⟪x 2 - x 0, x 6 - x 3⟫ < 0 ∨
      (0 < ⟪x 2 - x 0, x 6 - x 3⟫ ∧ 0 < ⟪x 4 - x 0, x 2 - x 0⟫)) :
    IsRupert (univ.image x) := by
  have h := isRupert_eg_wall (facSig F) (x := x ∘ wallSig)
    (by show x 3 = x 5 + x 4 - x 0; rw [hP]; abel) hC hw hs
  have e : Finset.univ.image (x ∘ wallSig) = Finset.univ.image x := by
    ext y
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp]
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨_, rfl⟩
    · rintro ⟨i, rfl⟩; exact ⟨wallSig i, by rw [wallSig_invol]⟩
  rwa [e] at h

end Minimality.T24.Par
