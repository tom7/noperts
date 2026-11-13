module

public import Minimality.Type24SAT.K24.ParRect
public import Minimality.Type24

@[expose] public section

/-!
# Type 24, `D` a parallelogram, `E ∥ G`: the wall piece `S` (`23 ⊥ 06`)

`h = ⟪x 6 - x 0, x 2 - x 3⟫ = 0` (edge `06` perpendicular to edge `23`).  With
`k = ⟪x 6 - x 3, x 6 - x 0⟫` and `s = ⟪x 5 - x 0, x 6 - x 0⟫`:
* `k > 0`: leaf P0536 at `d + t (x 3 - x 6)` (`d = x 2 - x 3`, small `t > 0`): the diagonal form `z 3 - z 5`
  is `-q |d|² < 0` and `z 0 - z 6` is `t k > 0`.
* `k ≤ 0`, `s > 0`: leaf V01234 at `x 0 - x 6` (the view along `06`): depths `z 2 = z 3 < z 4 < z 0` and
  `z 1 > z 2` (from the facets `G`, `H` at `1` and `k ≤ 0`).
The wall `⟪x 5 - x 0, x 2 - x 3⟫ = 0` is not used.
-/

set_option autoImplicit false
open scoped RealInnerProductSpace Topology
open Filter
open Finset

namespace Minimality.T24.Par
open Minimality Minimality.H21 Minimality.T24.SAT

/-- A robustly unimodal 5-cycle with a tied valley `{2, 3}`: `z 2 = z 3 < z 4 < z 0`, `z 2 < z 1`. -/
theorem robUni_v5c (z : ZMod 5 → ℝ) (h23 : z 2 = z 3) (h21 : z 2 < z 1) (h34 : z 3 < z 4)
    (h40 : z 4 < z 0) : RobUni z := by
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
  rcases le_or_gt (z 0) (z 1) with h | h <;>
  linarith

variable {x : Fin 7 → ℝ³}

open Minimality.RimCell in
/-- **The piece `23 ⊥ 06`, `k > 0`.**  Type 24, `D` a parallelogram, `E ∥ G`,
`⟪x 6 - x 0, x 2 - x 3⟫ = 0` and `⟪x 6 - x 3, x 6 - x 0⟫ > 0`: Rupert (leaf P0536 at
`x 2 - x 3 + t (x 3 - x 6)`, small `t > 0`). -/
theorem isRupert_eg_h0k (F : S0xFac 9 s0x_S24 x) (hP : x 3 = x 4 + x 5 - x 0)
    (hE : ⟪F.N 4, x 2 - x 3⟫ = 0) (hh : ⟪x 6 - x 0, x 2 - x 3⟫ = 0)
    (hk : 0 < ⟪x 6 - x 3, x 6 - x 0⟫) :
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
  have f35 : ⟪x 3 - x 5, d⟫ < 0 := by
    rw [e35, e4, hh]; nlinarith [mul_pos hq0 ha]
  have f06 : ⟪x 0 - x 6, x 3 - x 6⟫ = ⟪x 6 - x 3, x 6 - x 0⟫ := by
    rw [show x 0 - x 6 = -(x 6 - x 0) by abel, show x 3 - x 6 = -(x 6 - x 3) by abel, inner_neg_neg,
      real_inner_comm]
  have f06d : ⟪x 0 - x 6, d⟫ = 0 := by
    rw [show x 0 - x 6 = -(x 6 - x 0) by abel, inner_neg_left, hh, neg_zero]
  -- facet values
  have zB0 := F.zero 1 0 (by decide); have zB6 := F.zero 1 6 (by decide)
  have zC2 := F.zero 2 2 (by decide); have hC3 := F.neg 2 3 (by decide)
  have zD3 := F.zero 3 3 (by decide); have hD2 := F.neg 3 2 (by decide)
  have zE0 := F.zero 4 0 (by decide); have zE6 := F.zero 4 6 (by decide)
  have hE3 := F.neg 4 3 (by decide)
  have zG2 := F.zero 6 2 (by decide); have zG3 := F.zero 6 3 (by decide)
  have zG5 := F.zero 6 5 (by decide); have hG0 := F.neg 6 0 (by decide)
  have hG6 := F.neg 6 6 (by decide)
  have zH2 := F.zero 7 2 (by decide); have zH3 := F.zero 7 3 (by decide)
  have zH6 := F.zero 7 6 (by decide)
  have zI3 := F.zero 8 3 (by decide); have hI2 := F.neg 8 2 (by decide)
  have hBd : 0 < ⟪F.N 1, d⟫ := by
    have h1 : ⟪F.N 1, x 4 - x 0⟫ = -q * ⟪F.N 1, d⟫ + u * ⟪F.N 1, x 6 - x 0⟫ := by
      rw [hdec, inner_add_right, inner_smul_right, inner_smul_right]
    have hB4 := F.neg 1 4 (by decide)
    rw [IS, IS 1 6 0, zB0, zB6] at h1
    by_contra h; push Not at h
    linarith [mul_nonneg hq0.le (neg_nonneg.2 h)]
  have dC : ⟪F.N 2, d⟫ = -F.f 2 (x 3) := by rw [hd, IS, zC2]; ring
  have dD : ⟪F.N 3, d⟫ = F.f 3 (x 2) := by rw [hd, IS, zD3]; ring
  have dG : ⟪F.N 6, d⟫ = 0 := by rw [hd, IS, zG2, zG3]; ring
  have dH : ⟪F.N 7, d⟫ = 0 := by rw [hd, IS, zH2, zH3]; ring
  have dI : ⟪F.N 8, d⟫ = F.f 8 (x 2) := by rw [hd, IS, zI3]; ring
  have wG : ⟪F.N 6, x 3 - x 6⟫ = -F.f 6 (x 6) := by rw [IS, zG3]; ring
  have wH : ⟪F.N 7, x 3 - x 6⟫ = 0 := by rw [IS, zH3, zH6]; ring
  have wE : ⟪F.N 4, x 3 - x 6⟫ = F.f 4 (x 3) := by rw [IS, zE6]; ring
  -- the P0536 cell point
  obtain ⟨aP, hAP⟩ := exists_cellAt_of_lex (F := F) (U := U0536) (Dn := D0536) (u₀ := d)
    (v := x 2 - x 0)
    (by
      intro t ht; simp only [U0536, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl
      · exact Or.inl hBd
      · exact Or.inl (by rw [dC]; linarith)
      · exact Or.inr ⟨dG, by rw [IS, zG2]; linarith⟩
      · exact Or.inr ⟨dH, by rw [IS, zH2]; linarith [F.neg 7 0 (by decide)]⟩)
    (by
      intro t ht; simp only [D0536, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      · exact Or.inl (by rw [dD]; linarith)
      · exact Or.inr ⟨by rw [hE]; simp, by rw [IS, zE0]; linarith [F.neg 4 2 (by decide)]⟩
      · exact Or.inl (by rw [dI]; linarith))
  have c0 : c0536 0 = 0 := rfl
  have c1 : c0536 1 = 5 := rfl
  have c2 : c0536 2 = 3 := rfl
  have c3 : c0536 3 = 6 := rfl
  have g1 := eventually_pos_affine (B := ⟪F.N 1, x 3 - x 6⟫) (Or.inl hBd)
  have g2 := eventually_pos_affine (B := ⟪F.N 2, x 3 - x 6⟫)
    (Or.inl (by rw [dC]; linarith : 0 < ⟪F.N 2, d⟫))
  have g3 := eventually_pos_affine (B := -⟪F.N 3, x 3 - x 6⟫)
    (Or.inl (by rw [dD]; linarith : 0 < -⟪F.N 3, d⟫))
  have g4 := eventually_pos_affine (B := -⟪F.N 8, x 3 - x 6⟫)
    (Or.inl (by rw [dI]; linarith : 0 < -⟪F.N 8, d⟫))
  have g5 := eventually_pos_affine (B := -⟪x 3 - x 5, x 3 - x 6⟫)
    (Or.inl (by linarith : 0 < -⟪x 3 - x 5, d⟫))
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), (0 < ⟪F.N 1, d + t • (x 3 - x 6)⟫ ∧
      0 < ⟪F.N 2, d + t • (x 3 - x 6)⟫ ∧ 0 < -⟪F.N 3, d + t • (x 3 - x 6)⟫ ∧
      0 < -⟪F.N 8, d + t • (x 3 - x 6)⟫ ∧ 0 < -⟪x 3 - x 5, d + t • (x 3 - x 6)⟫) ∧ 0 < t := by
    filter_upwards [g1, g2, g3, g4, g5, self_mem_nhdsWithin] with t h1 h2 h3 h4 h5 ht
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ht⟩
    · rw [lin]; exact h1
    · rw [lin]; exact h2
    · rw [lin]; linarith
    · rw [lin]; linarith
    · rw [lin]; linarith
  obtain ⟨t, ⟨h1, h2, h3, h4, h5⟩, ht⟩ := hev.exists
  refine isRupert_of_closedCell (u₀ := d + t • (x 3 - x 6)) le_rfl F hx (by decide) cyc0536 hAP ?_
    (robUni_four_of_mixed ⟨(2, 1), by decide, ?_⟩ ⟨(0, 3), by decide, ?_⟩)
  · refine ⟨fun r hr => ?_, fun r hr => ?_⟩
    · simp only [U0536, Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact h1.le
      · exact h2.le
      · rw [lin, dG, wG]; have := mul_pos ht (neg_pos.2 hG6); linarith
      · rw [lin, dH, wH]; simp
    · simp only [D0536, Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl | rfl
      · linarith
      · rw [lin, hE, wE]; have := mul_neg_of_pos_of_neg ht hE3; linarith
      · linarith
  · simp only [c2, c1]; rw [← inner_sub_left]; linarith
  · simp only [c0, c3]; rw [← inner_sub_left, lin, f06d, f06]; have := mul_pos ht hk; linarith

open Minimality.RimCell in
/-- **The piece `23 ⊥ 06`, `k ≤ 0`, `s > 0`.**  Type 24, `D` a parallelogram, `E ∥ G`,
`⟪x 6 - x 0, x 2 - x 3⟫ = 0`, `⟪x 5 - x 0, x 6 - x 0⟫ > 0`, `⟪x 6 - x 3, x 6 - x 0⟫ ≤ 0`: Rupert
(leaf V01234 at the view `x 0 - x 6` along the edge `06`). -/
theorem isRupert_eg_h0s (F : S0xFac 9 s0x_S24 x) (hP : x 3 = x 4 + x 5 - x 0)
    (hE : ⟪F.N 4, x 2 - x 3⟫ = 0) (hh : ⟪x 6 - x 0, x 2 - x 3⟫ = 0)
    (hs : 0 < ⟪x 5 - x 0, x 6 - x 0⟫) (hk : ⟪x 6 - x 3, x 6 - x 0⟫ ≤ 0) :
    IsRupert (univ.image x) := by
  obtain ⟨q, u, hq0, hq1, hu0, hu1, hdec⟩ := eg_decomp F hP hE
  have IS := F.inner_sub
  have hx := Minimality.H24.SAT.inj_of_fac F
  set d := x 2 - x 3 with hd
  set w := x 6 - x 0 with hw
  have hW : 0 < ⟪w, w⟫ := by
    have : w ≠ 0 := fun h => absurd (hx (sub_eq_zero.1 h)) (by decide)
    exact real_inner_self_pos.2 this
  have e35 : x 3 - x 5 = x 4 - x 0 := by rw [hP]; abel
  -- facet values
  have zA0 := F.zero 0 0 (by decide); have hA6 := F.neg 0 6 (by decide)
  have zB0 := F.zero 1 0 (by decide); have zB6 := F.zero 1 6 (by decide)
  have hB5 := F.neg 1 5 (by decide)
  have zD0 := F.zero 3 0 (by decide); have zD3 := F.zero 3 3 (by decide)
  have hD6 := F.neg 3 6 (by decide)
  have zE0 := F.zero 4 0 (by decide); have zE6 := F.zero 4 6 (by decide)
  have hE5 := F.neg 4 5 (by decide)
  have zF6 := F.zero 5 6 (by decide); have hF0 := F.neg 5 0 (by decide)
  have zG2 := F.zero 6 2 (by decide); have zG3 := F.zero 6 3 (by decide)
  have zG5 := F.zero 6 5 (by decide); have hG0 := F.neg 6 0 (by decide)
  have hG6 := F.neg 6 6 (by decide); have hG1 := F.neg 6 1 (by decide)
  have zH2 := F.zero 7 2 (by decide); have zH3 := F.zero 7 3 (by decide)
  have zH6 := F.zero 7 6 (by decide); have hH0 := F.neg 7 0 (by decide)
  have hH1 := F.neg 7 1 (by decide)
  have zI3 := F.zero 8 3 (by decide); have zI6 := F.zero 8 6 (by decide)
  have hI0 := F.neg 8 0 (by decide); have hI2 := F.neg 8 2 (by decide)
  have dG : ⟪F.N 6, d⟫ = 0 := by rw [hd, IS, zG2, zG3]; ring
  have dH : ⟪F.N 7, d⟫ = 0 := by rw [hd, IS, zH2, zH3]; ring
  have dI : ⟪F.N 8, d⟫ = F.f 8 (x 2) := by rw [hd, IS, zI3]; ring
  -- G is parallel to E: `⟪N_G, x 6 - x 0⟫ = 0`
  have G60 : ⟪F.N 6, w⟫ = 0 := by
    have h1 : ⟪F.N 6, x 4 - x 0⟫ = -q * ⟪F.N 6, d⟫ + u * ⟪F.N 6, w⟫ := by
      rw [hdec, inner_add_right, inner_smul_right, inner_smul_right]
    rw [← e35, IS, zG3, zG5, dG] at h1
    have : u * ⟪F.N 6, w⟫ = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hu0.ne'
    · exact h
  -- the frame `d, x 0 - x 6, x 3 - x 6`
  have hD : vol3 d (x 0 - x 6) (x 3 - x 6) ≠ 0 := by
    have h := vol3_mul_inner (F.N 7) (F.N 6) (F.N 8) d (x 0 - x 6) (x 3 - x 6)
    have e1 : ⟪F.N 7, x 0 - x 6⟫ = F.f 7 (x 0) := by rw [IS, zH6]; ring
    have e2 : ⟪F.N 7, x 3 - x 6⟫ = 0 := by rw [IS, zH3, zH6]; ring
    have e3 : ⟪F.N 6, x 0 - x 6⟫ = 0 := by
      rw [show x 0 - x 6 = -w by rw [hw]; abel, inner_neg_right, G60, neg_zero]
    have e4 : ⟪F.N 6, x 3 - x 6⟫ = -F.f 6 (x 6) := by rw [IS, zG3]; ring
    have e5 : ⟪F.N 8, x 3 - x 6⟫ = 0 := by rw [IS, zI3, zI6]; ring
    rw [dH, dG, dI, e1, e2, e3, e4, e5] at h
    intro h0
    rw [h0, mul_zero] at h
    have h1 : F.f 7 (x 0) * (F.f 6 (x 6) * F.f 8 (x 2)) = 0 := by linear_combination h
    have h2 : F.f 7 (x 0) * (F.f 6 (x 6) * F.f 8 (x 2)) < 0 :=
      mul_neg_of_neg_of_pos hH0 (mul_pos_of_neg_of_neg hG6 hI2)
    linarith
  -- 1 in the frame
  have hcr := vol3_smul_cramer d (x 0 - x 6) (x 3 - x 6) (x 1 - x 6)
  set D := vol3 d (x 0 - x 6) (x 3 - x 6)
  set P := vol3 (x 1 - x 6) (x 0 - x 6) (x 3 - x 6)
  set R := vol3 d (x 1 - x 6) (x 3 - x 6)
  set M := vol3 d (x 0 - x 6) (x 1 - x 6)
  have ap : ∀ v : ℝ³, D * ⟪v, x 1 - x 6⟫ = P * ⟪v, d⟫ + R * ⟪v, x 0 - x 6⟫ + M * ⟪v, x 3 - x 6⟫ := by
    intro v
    have := congrArg (fun y => ⟪v, y⟫) hcr
    simp only [inner_add_right, inner_smul_right] at this
    exact this
  have aH := ap (F.N 7)
  rw [dH, IS, IS, IS, zH6, zH3] at aH
  have aG := ap (F.N 6)
  rw [dG, IS 6 3 6, IS 6 1 6, zG3, show x 0 - x 6 = -w by rw [hw]; abel, inner_neg_right, G60] at aG
  have aW := ap w
  have wd : ⟪w, d⟫ = 0 := hh
  have w06 : ⟪w, x 0 - x 6⟫ = -⟪w, w⟫ := by
    rw [show x 0 - x 6 = -w by rw [hw]; abel, inner_neg_right]
  have w36 : ⟪w, x 3 - x 6⟫ = -⟪x 6 - x 3, x 6 - x 0⟫ := by
    rw [real_inner_comm, show x 3 - x 6 = -(x 6 - x 3) by abel, inner_neg_left]
  rw [wd, w06, w36] at aW
  -- `⟪w, x 2 - x 1⟫ > 0`
  have key : 0 < ⟪w, x 2 - x 1⟫ := by
    have e21 : ⟪w, x 2 - x 1⟫ = ⟪w, d⟫ + ⟪w, x 3 - x 6⟫ - ⟪w, x 1 - x 6⟫ := by
      rw [← inner_add_right, ← inner_sub_right]; congr 1; rw [hd]; abel
    rw [e21, wd, w36]
    set X := ⟪w, x 1 - x 6⟫
    set k := ⟪x 6 - x 3, x 6 - x 0⟫
    have hX : X * (F.f 7 (x 0) * F.f 6 (x 6)) =
        -(F.f 7 (x 1) * F.f 6 (x 6)) * ⟪w, w⟫ + (F.f 6 (x 1) - F.f 6 (x 6)) * k * F.f 7 (x 0) := by
      apply mul_left_cancel₀ hD
      linear_combination (F.f 7 (x 0) * F.f 6 (x 6)) * aW + F.f 6 (x 6) * ⟪w, w⟫ * aH
        - k * F.f 7 (x 0) * aG
    have p1 : 0 < F.f 7 (x 0) * F.f 6 (x 6) := mul_pos_of_neg_of_neg hH0 hG6
    have p2 : 0 < F.f 7 (x 1) * F.f 6 (x 6) := mul_pos_of_neg_of_neg hH1 hG6
    have p3 : 0 ≤ F.f 6 (x 1) * F.f 7 (x 0) * (-k) :=
      mul_nonneg (mul_pos_of_neg_of_neg hG1 hH0).le (by linarith)
    have e : (0 + -k - X) * (F.f 7 (x 0) * F.f 6 (x 6)) =
        (F.f 7 (x 1) * F.f 6 (x 6)) * ⟪w, w⟫ + F.f 6 (x 1) * F.f 7 (x 0) * (-k) := by
      linear_combination (-1 : ℝ) * hX
    have : 0 < (0 + -k - X) * (F.f 7 (x 0) * F.f 6 (x 6)) := by
      rw [e]; linarith [mul_pos p2 hW]
    exact pos_of_mul_pos_left this p1.le
  -- the V01234 cell point (lex at `x 0 - x 6`, tilt `x 5 - x 0`)
  have s06 : ∀ t, ⟪F.N t, x 0 - x 6⟫ = F.f t (x 0) - F.f t (x 6) := fun t => IS t 0 6
  have s50 : ∀ t, ⟪F.N t, x 5 - x 0⟫ = F.f t (x 5) - F.f t (x 0) := fun t => IS t 5 0
  have G06 : ⟪F.N 6, x 0 - x 6⟫ = 0 := by
    rw [show x 0 - x 6 = -w by rw [hw]; abel, inner_neg_right, G60, neg_zero]
  obtain ⟨aV, hAV⟩ := exists_cellAt_of_lex (F := F) (U := U01234) (Dn := D01234)
    (u₀ := x 0 - x 6) (v := x 5 - x 0)
    (by
      intro t ht; simp only [U01234, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      · exact Or.inl (by rw [s06, zA0]; linarith)
      · exact Or.inl (by rw [s06, zD0]; linarith)
      · exact Or.inr ⟨G06, by rw [s50, zG5]; linarith⟩)
    (by
      intro t ht; simp only [D01234, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl
      · exact Or.inr ⟨by rw [s06, zB0, zB6]; simp, by rw [s50, zB0]; linarith⟩
      · exact Or.inr ⟨by rw [s06, zE0, zE6]; simp, by rw [s50, zE0]; linarith⟩
      · exact Or.inl (by rw [s06, zF6]; linarith)
      · exact Or.inl (by rw [s06, zH6]; linarith)
      · exact Or.inl (by rw [s06, zI6]; linarith))
  refine leaf_V01234 (u := x 0 - x 6) F hAV ?_ ?_
  · refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · simp only [U01234, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      · rw [s06, zA0]; linarith
      · rw [s06, zD0]; linarith
      · rw [G06]
    · simp only [D01234, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl
      · rw [s06, zB0, zB6]; simp
      · rw [s06, zE0, zE6]; simp
      · rw [s06, zF6]; linarith
      · rw [s06, zH6]; linarith
      · rw [s06, zI6]; linarith
  · have c0 : c01234 0 = 0 := rfl
    have c1 : c01234 1 = 1 := rfl
    have c2 : c01234 2 = 2 := rfl
    have c3 : c01234 3 = 3 := rfl
    have c4 : c01234 4 = 4 := rfl
    have neg06 : ∀ v : ℝ³, ⟪v, x 0 - x 6⟫ = -⟪v, w⟫ := fun v => by
      rw [show x 0 - x 6 = -w by rw [hw]; abel, inner_neg_right]
    have e4w : ⟪x 4 - x 0, w⟫ = u * ⟪w, w⟫ := by
      rw [hdec, inner_add_left, inner_smul_left, inner_smul_left, real_inner_comm w d, hh]; simp
    apply robUni_v5c
    · simp only [c2, c3]
      have : ⟪x 2 - x 3, x 0 - x 6⟫ = 0 := by rw [neg06, real_inner_comm, ← hd, hh, neg_zero]
      rw [inner_sub_left] at this; linarith
    · simp only [c2, c1]
      have : ⟪x 1 - x 2, x 0 - x 6⟫ = ⟪w, x 2 - x 1⟫ := by
        rw [neg06, real_inner_comm, ← inner_neg_right, neg_sub]
      rw [inner_sub_left] at this; linarith
    · simp only [c3, c4]
      have : ⟪x 4 - x 3, x 0 - x 6⟫ = ⟪x 5 - x 0, x 6 - x 0⟫ := by
        rw [neg06, show x 4 - x 3 = -(x 5 - x 0) by rw [hP]; abel, inner_neg_left, neg_neg]
      rw [inner_sub_left] at this; linarith
    · simp only [c4, c0]
      have : ⟪x 0 - x 4, x 0 - x 6⟫ = u * ⟪w, w⟫ := by
        rw [neg06, show x 0 - x 4 = -(x 4 - x 0) by abel, inner_neg_left, neg_neg, e4w]
      rw [inner_sub_left] at this; have := mul_pos hu0 hW; linarith

/-- **The wall piece `S`: `23 ⊥ 06`.**  Type 24, `D` a parallelogram, `E ∥ G`,
`⟪x 6 - x 0, x 2 - x 3⟫ = 0` and `⟪x 5 - x 0, x 6 - x 0⟫ > 0`: Rupert. -/
theorem isRupert_eg_h0 (F : S0xFac 9 s0x_S24 x) (hP : x 3 = x 4 + x 5 - x 0)
    (hE : ⟪F.N 4, x 2 - x 3⟫ = 0) (hh : ⟪x 6 - x 0, x 2 - x 3⟫ = 0)
    (hs : 0 < ⟪x 5 - x 0, x 6 - x 0⟫) :
    IsRupert (univ.image x) := by
  rcases lt_or_ge 0 ⟪x 6 - x 3, x 6 - x 0⟫ with hk | hk
  · exact isRupert_eg_h0k F hP hE hh hk
  · exact isRupert_eg_h0s F hP hE hh hs hk

open Minimality.H24K.SAT in
/-- **The piece `S` of the `C ∥ I` wall** (the image of `isRupert_eg_h0` under `σ = (2 6)(4 5)`):
`⟪x 2 - x 0, x 6 - x 3⟫ = 0` (edge `02` perpendicular to edge `36`) and `⟪x 4 - x 0, x 2 - x 0⟫ > 0`. -/
theorem isRupert_ci_h0 (F : S0xFac 9 s0x_S24 x) (hP : x 3 = x 4 + x 5 - x 0)
    (hC : ⟪F.N 2, x 6 - x 3⟫ = 0) (hh : ⟪x 2 - x 0, x 6 - x 3⟫ = 0)
    (hs : 0 < ⟪x 4 - x 0, x 2 - x 0⟫) :
    IsRupert (univ.image x) := by
  have h := isRupert_eg_h0 (facSig F) (x := x ∘ wallSig)
    (by show x 3 = x 5 + x 4 - x 0; rw [hP]; abel) hC hh hs
  have e : Finset.univ.image (x ∘ wallSig) = Finset.univ.image x := by
    ext y
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp]
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨_, rfl⟩
    · rintro ⟨i, rfl⟩; exact ⟨wallSig i, by rw [wallSig_invol]⟩
  rwa [e] at h

end Minimality.T24.Par
