module

public import Mathlib
public import Minimality.SilS0XA
public import Minimality.OrthoView
public import Minimality.OrthoView2
public import Minimality.Tilt
public import Minimality.Type24SAT.K24.ParEdge

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped RealInnerProductSpace Topology
open Filter Finset
open Minimality Minimality.H21 Minimality.T24.Par

namespace Minimality.H21

/-- **Affine inner product comparison holds eventually along a ray.**
If `⟪y - x, u⟫ > 0`, or `⟪y - x, u⟫ = 0` and `⟪y - x, d⟫ > 0`, then
`⟪x, u + ε • d⟫ < ⟪y, u + ε • d⟫` for all small `ε > 0`. -/
theorem eventually_inner_sub_pos (x y u d : ℝ³)
    (h : 0 < ⟪y - x, u⟫ ∨ (⟪y - x, u⟫ = 0 ∧ 0 < ⟪y - x, d⟫)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪x, u + ε • d⟫ < ⟪y, u + ε • d⟫ := by
  have ev := eventually_pos_affine (A := ⟪y - x, u⟫) (B := ⟪y - x, d⟫) h
  filter_upwards [ev] with ε hε
  have hlin : ⟪y - x, u + ε • d⟫ = ⟪y - x, u⟫ + ε * ⟪y - x, d⟫ := by
    rw [inner_add_right, real_inner_smul_right]
  rw [inner_sub_left] at hlin
  linarith

set_option maxHeartbeats 1000000

/-- **Robust unimodality for a 6-cycle with valley at 1 and peak at 4.** -/
theorem robUni_v6 (z : ZMod 6 → ℝ)
    (h10 : z 1 < z 0) (h12 : z 1 < z 2)
    (h23 : z 2 < z 3) (h34 : z 3 < z 4)
    (h54 : z 5 < z 4) (h05 : z 0 < z 5) :
    RobUni z := by
  have tab :
      ((0 : ZMod 6) + 1 = 1) ∧
      ((0 : ZMod 6) + 2 = 2) ∧
      ((0 : ZMod 6) + 3 = 3) ∧
      ((0 : ZMod 6) + 4 = 4) ∧
      ((0 : ZMod 6) + 5 = 5) ∧
      ((1 : ZMod 6) + 1 = 2) ∧
      ((1 : ZMod 6) + 2 = 3) ∧
      ((1 : ZMod 6) + 3 = 4) ∧
      ((1 : ZMod 6) + 4 = 5) ∧
      ((1 : ZMod 6) + 5 = 0) ∧
      ((2 : ZMod 6) + 1 = 3) ∧
      ((2 : ZMod 6) + 2 = 4) ∧
      ((2 : ZMod 6) + 3 = 5) ∧
      ((2 : ZMod 6) + 4 = 0) ∧
      ((2 : ZMod 6) + 5 = 1) ∧
      ((3 : ZMod 6) + 1 = 4) ∧
      ((3 : ZMod 6) + 2 = 5) ∧
      ((3 : ZMod 6) + 3 = 0) ∧
      ((3 : ZMod 6) + 4 = 1) ∧
      ((3 : ZMod 6) + 5 = 2) ∧
      ((4 : ZMod 6) + 1 = 5) ∧
      ((4 : ZMod 6) + 2 = 0) ∧
      ((4 : ZMod 6) + 3 = 1) ∧
      ((4 : ZMod 6) + 4 = 2) ∧
      ((4 : ZMod 6) + 5 = 3) ∧
      ((5 : ZMod 6) + 1 = 0) ∧
      ((5 : ZMod 6) + 2 = 1) ∧
      ((5 : ZMod 6) + 3 = 2) ∧
      ((5 : ZMod 6) + 4 = 3) ∧
      ((5 : ZMod 6) + 5 = 4) := by decide
  obtain ⟨a01, a02, a03, a04, a05, a11, a12, a13, a14, a15, a21, a22, a23, a24, a25,
          a31, a32, a33, a34, a35, a41, a42, a43, a44, a45, a51, a52, a53, a54, a55⟩ := tab
  intro B b c d hb hbc hcd hd
  have hB : B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 ∨ B = 4 ∨ B = 5 := by revert B; decide
  have hbcd :
      (b = 1 ∧ c = 2 ∧ d = 3) ∨ (b = 1 ∧ c = 2 ∧ d = 4) ∨ (b = 1 ∧ c = 2 ∧ d = 5) ∨
      (b = 1 ∧ c = 3 ∧ d = 4) ∨ (b = 1 ∧ c = 3 ∧ d = 5) ∨ (b = 1 ∧ c = 4 ∧ d = 5) ∨
      (b = 2 ∧ c = 3 ∧ d = 4) ∨ (b = 2 ∧ c = 3 ∧ d = 5) ∨ (b = 2 ∧ c = 4 ∧ d = 5) ∨
      (b = 3 ∧ c = 4 ∧ d = 5) := by omega
  rintro ⟨h1, h2, h3, h4⟩
  rcases hbcd with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
  rcases hB with rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp only [Nat.cast_one, Nat.cast_ofNat, a01, a02, a03, a04, a05, a11, a12, a13, a14, a15,
             a21, a22, a23, a24, a25, a31, a32, a33, a34, a35, a41, a42, a43, a44, a45,
             a51, a52, a53, a54, a55] at h1 h2 h3 h4 <;>
  linarith

set_option maxHeartbeats 200000

/-- **Ray unimodality for 5-cycle (EEEVV).**
The ends `c 0, c 1, c 2` have `σ = 1`, and the non-ends `c 3, c 4` have `σ > 1`.
Along any tilt direction `d` with `⟪x (c 0) - x (c 1), d⟫ > 0`, the depths are `RobUni`
for all small `ε > 0`. -/
theorem robUni_ray_5_eeevv {n k : ℕ} (x : Fin n → ℝ³) (p : ℝ³) (v : Fin k → ℝ³)
    (y : Fin n → Fin k → ℝ) (hxy : ∀ i, x i = p + ∑ e, y i e • v e)
    {u : ℝ³} (hv : ∀ e, ⟪v e, u⟫ = 1)
    (c : ZMod 5 → Fin n)
    (hE0 : (∑ e, y (c 0) e) = 1) (hE1 : (∑ e, y (c 1) e) = 1) (hE2 : (∑ e, y (c 2) e) = 1)
    (hV3 : 1 < ∑ e, y (c 3) e) (hV4 : 1 < ∑ e, y (c 4) e)
    (d : ℝ³) (hd01 : 0 < ⟪x (c 0) - x (c 1), d⟫) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), RobUni (fun i => ⟪x (c i), u + ε • d⟫) := by
  have d01 : ⟪x (c 0) - x (c 1), u⟫ = 0 := by
    rw [depth_orthocentre x p v y hxy u hv]; linarith
  have d23 : 0 < ⟪x (c 3) - x (c 2), u⟫ := by
    rw [depth_orthocentre x p v y hxy u hv]; linarith
  have d04 : 0 < ⟪x (c 4) - x (c 0), u⟫ := by
    rw [depth_orthocentre x p v y hxy u hv]; linarith
  have ev1 := eventually_inner_sub_pos (x (c 1)) (x (c 0)) u d (Or.inr ⟨d01, hd01⟩)
  have ev2 := eventually_inner_sub_pos (x (c 2)) (x (c 3)) u d (Or.inl d23)
  have ev3 := eventually_inner_sub_pos (x (c 0)) (x (c 4)) u d (Or.inl d04)
  filter_upwards [ev1, ev2, ev3] with ε h1 h2 h3
  exact robUni_v5b _ h1 h2 h3

/-- **Theorem P, 5-rim EEEVV case.**
The three contiguous ends `c 0, c 1, c 2` have `σ = 1` and `c 3, c 4` have `σ > 1`.
The tilt direction `d = x (c 0) - x (c 1)` discharges the ray hypothesis. -/
theorem isRupert_of_orthocentre_5rim_eeevv {m n k : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}
    (F : S0xFac m S x) (hx : Function.Injective x) {c : ZMod 5 → Fin n}
    (hc : Function.Injective c) {U Dn : Finset (Fin m)} (hcyc : S0xCycUD S c U Dn)
    {u : ℝ³} (hu : CellAt F U Dn u) (p : ℝ³) (v : Fin k → ℝ³) (y : Fin n → Fin k → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hv : ∀ e, ⟪v e, u⟫ = 1)
    (hE0 : (∑ e, y (c 0) e) = 1) (hE1 : (∑ e, y (c 1) e) = 1) (hE2 : (∑ e, y (c 2) e) = 1)
    (hV3 : 1 < ∑ e, y (c 3) e) (hV4 : 1 < ∑ e, y (c 4) e) :
    IsRupert (Finset.univ.image x) := by
  set d := x (c 0) - x (c 1)
  have hd : 0 < ⟪x (c 0) - x (c 1), d⟫ := by
    rw [real_inner_self_pos]
    intro h0
    have := sub_eq_zero.mp h0
    exact absurd (hc (hx this)) (by decide)
  have hR := robUni_ray_5_eeevv x p v y hxy hv c hE0 hE1 hE2 hV3 hV4 d hd
  exact isRupert_of_closedCell_ray (by norm_num) F hx hc hcyc hu d hR

/-- **Ray unimodality for 5-cycle (EEVVV).**
The ends `c 0, c 1` have `σ = 1`, and the non-ends `c 2, c 3, c 4` have `σ > 1`.
With peak at `c 3` (`σ (c 2) ≤ σ (c 3)`), along a tilt direction `d` breaking any tie
between `c 2` and `c 3` and making `c 1` lower than `c 0`, depths are `RobUni`. -/
theorem robUni_ray_5_eevvv {n k : ℕ} (x : Fin n → ℝ³) (p : ℝ³) (v : Fin k → ℝ³)
    (y : Fin n → Fin k → ℝ) (hxy : ∀ i, x i = p + ∑ e, y i e • v e)
    {u : ℝ³} (hv : ∀ e, ⟪v e, u⟫ = 1)
    (c : ZMod 5 → Fin n)
    (hE0 : (∑ e, y (c 0) e) = 1) (hE1 : (∑ e, y (c 1) e) = 1)
    (hV4 : 1 < ∑ e, y (c 4) e)
    (d : ℝ³) (hd01 : 0 < ⟪x (c 0) - x (c 1), d⟫)
    (h23 : 0 < ⟪x (c 3) - x (c 2), u⟫ ∨ (⟪x (c 3) - x (c 2), u⟫ = 0 ∧ 0 < ⟪x (c 3) - x (c 2), d⟫)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), RobUni (fun i => ⟪x (c i), u + ε • d⟫) := by
  have d01 : ⟪x (c 0) - x (c 1), u⟫ = 0 := by
    rw [depth_orthocentre x p v y hxy u hv]; linarith
  have d04 : 0 < ⟪x (c 4) - x (c 0), u⟫ := by
    rw [depth_orthocentre x p v y hxy u hv]; linarith
  have ev1 := eventually_inner_sub_pos (x (c 1)) (x (c 0)) u d (Or.inr ⟨d01, hd01⟩)
  have ev2 := eventually_inner_sub_pos (x (c 2)) (x (c 3)) u d h23
  have ev3 := eventually_inner_sub_pos (x (c 0)) (x (c 4)) u d (Or.inl d04)
  filter_upwards [ev1, ev2, ev3] with ε h1 h2 h3
  exact robUni_v5b _ h1 h2 h3

/-- **Theorem P, 5-rim EEVVV case.** -/
theorem isRupert_of_orthocentre_5rim_eevvv {m n k : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}
    (F : S0xFac m S x) (hx : Function.Injective x) {c : ZMod 5 → Fin n}
    (hc : Function.Injective c) {U Dn : Finset (Fin m)} (hcyc : S0xCycUD S c U Dn)
    {u : ℝ³} (hu : CellAt F U Dn u) (p : ℝ³) (v : Fin k → ℝ³) (y : Fin n → Fin k → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hv : ∀ e, ⟪v e, u⟫ = 1)
    (hE0 : (∑ e, y (c 0) e) = 1) (hE1 : (∑ e, y (c 1) e) = 1)
    (hV4 : 1 < ∑ e, y (c 4) e)
    (d : ℝ³) (hd01 : 0 < ⟪x (c 0) - x (c 1), d⟫)
    (h23 : 0 < ⟪x (c 3) - x (c 2), u⟫ ∨ (⟪x (c 3) - x (c 2), u⟫ = 0 ∧ 0 < ⟪x (c 3) - x (c 2), d⟫)) :
    IsRupert (Finset.univ.image x) := by
  have hR := robUni_ray_5_eevvv x p v y hxy hv c hE0 hE1 hV4 d hd01 h23
  exact isRupert_of_closedCell_ray (by norm_num) F hx hc hcyc hu d hR

/-- **Ray unimodality for 6-cycle (EEEVVV).**
The ends `c 0, c 1, c 2` have `σ = 1`, and the non-ends `c 3, c 4, c 5` have `σ > 1`.
With peak at `c 4`, along a tilt direction `d` breaking ties and making `c 1` the lowest end,
depths are `RobUni` for all small `ε > 0`. -/
theorem robUni_ray_6 {n k : ℕ} (x : Fin n → ℝ³) (p : ℝ³) (v : Fin k → ℝ³)
    (y : Fin n → Fin k → ℝ) (hxy : ∀ i, x i = p + ∑ e, y i e • v e)
    {u : ℝ³} (hv : ∀ e, ⟪v e, u⟫ = 1)
    (c : ZMod 6 → Fin n)
    (hE0 : (∑ e, y (c 0) e) = 1) (hE1 : (∑ e, y (c 1) e) = 1) (hE2 : (∑ e, y (c 2) e) = 1)
    (hV3 : 1 < ∑ e, y (c 3) e) (hV5 : 1 < ∑ e, y (c 5) e)
    (d : ℝ³) (hd10 : 0 < ⟪x (c 0) - x (c 1), d⟫) (hd12 : 0 < ⟪x (c 2) - x (c 1), d⟫)
    (h34 : 0 < ⟪x (c 4) - x (c 3), u⟫ ∨ (⟪x (c 4) - x (c 3), u⟫ = 0 ∧ 0 < ⟪x (c 4) - x (c 3), d⟫))
    (h54 : 0 < ⟪x (c 4) - x (c 5), u⟫ ∨ (⟪x (c 4) - x (c 5), u⟫ = 0 ∧ 0 < ⟪x (c 4) - x (c 5), d⟫)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), RobUni (fun i => ⟪x (c i), u + ε • d⟫) := by
  have d10 : ⟪x (c 0) - x (c 1), u⟫ = 0 := by
    rw [depth_orthocentre x p v y hxy u hv]; linarith
  have d12 : ⟪x (c 2) - x (c 1), u⟫ = 0 := by
    rw [depth_orthocentre x p v y hxy u hv]; linarith
  have d23 : 0 < ⟪x (c 3) - x (c 2), u⟫ := by
    rw [depth_orthocentre x p v y hxy u hv]; linarith
  have d05 : 0 < ⟪x (c 5) - x (c 0), u⟫ := by
    rw [depth_orthocentre x p v y hxy u hv]; linarith
  have ev10 := eventually_inner_sub_pos (x (c 1)) (x (c 0)) u d (Or.inr ⟨d10, hd10⟩)
  have ev12 := eventually_inner_sub_pos (x (c 1)) (x (c 2)) u d (Or.inr ⟨d12, hd12⟩)
  have ev23 := eventually_inner_sub_pos (x (c 2)) (x (c 3)) u d (Or.inl d23)
  have ev34 := eventually_inner_sub_pos (x (c 3)) (x (c 4)) u d h34
  have ev54 := eventually_inner_sub_pos (x (c 5)) (x (c 4)) u d h54
  have ev05 := eventually_inner_sub_pos (x (c 0)) (x (c 5)) u d (Or.inl d05)
  filter_upwards [ev10, ev12, ev23, ev34, ev54, ev05] with ε h1 h2 h3 h4 h5 h6
  exact robUni_v6 _ h1 h2 h3 h4 h5 h6

/-- **Theorem P, 6-rim EEEVVV case.** -/
theorem isRupert_of_orthocentre_6rim {m n k : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}
    (F : S0xFac m S x) (hx : Function.Injective x) {c : ZMod 6 → Fin n}
    (hc : Function.Injective c) {U Dn : Finset (Fin m)} (hcyc : S0xCycUD S c U Dn)
    {u : ℝ³} (hu : CellAt F U Dn u) (p : ℝ³) (v : Fin k → ℝ³) (y : Fin n → Fin k → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hv : ∀ e, ⟪v e, u⟫ = 1)
    (hE0 : (∑ e, y (c 0) e) = 1) (hE1 : (∑ e, y (c 1) e) = 1) (hE2 : (∑ e, y (c 2) e) = 1)
    (hV3 : 1 < ∑ e, y (c 3) e) (hV5 : 1 < ∑ e, y (c 5) e)
    (d : ℝ³) (hd10 : 0 < ⟪x (c 0) - x (c 1), d⟫) (hd12 : 0 < ⟪x (c 2) - x (c 1), d⟫)
    (h34 : 0 < ⟪x (c 4) - x (c 3), u⟫ ∨ (⟪x (c 4) - x (c 3), u⟫ = 0 ∧ 0 < ⟪x (c 4) - x (c 3), d⟫))
    (h54 : 0 < ⟪x (c 4) - x (c 5), u⟫ ∨ (⟪x (c 4) - x (c 5), u⟫ = 0 ∧ 0 < ⟪x (c 4) - x (c 5), d⟫)) :
    IsRupert (Finset.univ.image x) := by
  have hR := robUni_ray_6 x p v y hxy hv c hE0 hE1 hE2 hV3 hV5 d hd10 hd12 h34 h54
  exact isRupert_of_closedCell_ray (by norm_num) F hx hc hcyc hu d hR

end Minimality.H21
