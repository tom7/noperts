import Minimality.Type24TieSigma
import Minimality.Type24Quad
import Minimality.M4dType24

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset

namespace Minimality.T24.A1

open Minimality Minimality.H21 Minimality.H24.SAT Minimality.T24.SAT Minimality.T24.RCell
  Minimality.LexCell Minimality.Split Minimality.T24.A15 Minimality.T24.M4 Minimality.T24.A7 Minimality.T24.A10 Minimality.T24.Q24

/-- Frame at vertex 5: existence of the coordinates of any vertex, with the facet formulas for the
coefficients (c1 from facet 3, c2 from facet 6, c3 from facet 2). -/
theorem frame5_exists {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (v : Fin 7) :
    ∃ c1 c2 c3 : ℝ, x v - x 5 = c1 • (x 2 - x 5) + c2 • (x 0 - x 5) + c3 • (x 3 - x 5) ∧
      c1 = F.f 3 (x v) / F.f 3 (x 2) ∧ c2 = F.f 6 (x v) / F.f 6 (x 0) ∧
      c3 = F.f 2 (x v) / F.f 2 (x 3) := by
  have z : ∀ (t : Fin 9) (i j : Fin 7), i ∈ s0x_S24 t → j ∈ s0x_S24 t → ⟪F.N t, x i - x j⟫ = 0 := by
    intro t i j hi hj; rw [F.inner_sub, F.zero t i hi, F.zero t j hj]; ring
  have n3_2 : ⟪F.N 3, x 2 - x 5⟫ = F.f 3 (x 2) := by
    rw [F.inner_sub, F.zero 3 5 (by decide)]; ring
  have n6_0 : ⟪F.N 6, x 0 - x 5⟫ = F.f 6 (x 0) := by
    rw [F.inner_sub, F.zero 6 5 (by decide)]; ring
  have n2_3 : ⟪F.N 2, x 3 - x 5⟫ = F.f 2 (x 3) := by
    rw [F.inner_sub, F.zero 2 5 (by decide)]; ring
  have a3_0 := z 3 0 5 (by decide) (by decide)
  have a3_3 := z 3 3 5 (by decide) (by decide)
  have a6_2 := z 6 2 5 (by decide) (by decide)
  have a6_3 := z 6 3 5 (by decide) (by decide)
  have a2_2 := z 2 2 5 (by decide) (by decide)
  have a2_0 := z 2 0 5 (by decide) (by decide)
  have h32 : F.f 3 (x 2) < 0 := F.neg 3 2 (by decide)
  have h60 : F.f 6 (x 0) < 0 := F.neg 6 0 (by decide)
  have h23 : F.f 2 (x 3) < 0 := F.neg 2 3 (by decide)
  let e : Fin 3 → ℝ³ := ![x 2 - x 5, x 0 - x 5, x 3 - x 5]
  have hli : LinearIndependent ℝ e := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hs : g 0 • (x 2 - x 5) + g 1 • (x 0 - x 5) + g 2 • (x 3 - x 5) = 0 := by
      simpa [Fin.sum_univ_three, e] using hg
    have i3 := congrArg (fun w => ⟪F.N 3, w⟫) hs
    have i6 := congrArg (fun w => ⟪F.N 6, w⟫) hs
    have i2 := congrArg (fun w => ⟪F.N 2, w⟫) hs
    simp only [inner_add_right, inner_smul_right, inner_zero_right] at i3 i6 i2
    rw [n3_2, a3_0, a3_3] at i3
    rw [n6_0, a6_2, a6_3] at i6
    rw [n2_3, a2_2, a2_0] at i2
    have g0 : g 0 = 0 := by
      have : g 0 * F.f 3 (x 2) = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_right h32.ne
    have g1 : g 1 = 0 := by
      have : g 1 * F.f 6 (x 0) = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_right h60.ne
    have g2 : g 2 = 0 := by
      have : g 2 * F.f 2 (x 3) = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_right h23.ne
    intro i; fin_cases i <;> assumption
  have hspan : Submodule.span ℝ (Set.range e) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by simp)
  have hmem : x v - x 5 ∈ Submodule.span ℝ (Set.range e) := by rw [hspan]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hmem
  have hs : x v - x 5 = c 0 • (x 2 - x 5) + c 1 • (x 0 - x 5) + c 2 • (x 3 - x 5) := by
    rw [← hc]; simp [Fin.sum_univ_three, e]
  have i3 := congrArg (fun w => ⟪F.N 3, w⟫) hs
  have i6 := congrArg (fun w => ⟪F.N 6, w⟫) hs
  have i2 := congrArg (fun w => ⟪F.N 2, w⟫) hs
  simp only [inner_add_right, inner_smul_right] at i3 i6 i2
  have f3v : ⟪F.N 3, x v - x 5⟫ = F.f 3 (x v) := by
    rw [F.inner_sub, F.zero 3 5 (by decide)]; ring
  have f6v : ⟪F.N 6, x v - x 5⟫ = F.f 6 (x v) := by
    rw [F.inner_sub, F.zero 6 5 (by decide)]; ring
  have f2v : ⟪F.N 2, x v - x 5⟫ = F.f 2 (x v) := by
    rw [F.inner_sub, F.zero 2 5 (by decide)]; ring
  rw [f3v, n3_2, a3_0, a3_3] at i3
  rw [f6v, n6_0, a6_2, a6_3] at i6
  rw [f2v, n2_3, a2_2, a2_0] at i2
  refine ⟨c 0, c 1, c 2, hs, ?_, ?_, ?_⟩
  · field_simp [h32.ne]; linarith
  · field_simp [h60.ne]; linarith
  · field_simp [h23.ne]; linarith

theorem x6_frame {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    ∃ c61 c62 c63 : ℝ, x 6 - x 5 = c61 • (x 2 - x 5) + c62 • (x 0 - x 5) + c63 • (x 3 - x 5) ∧
      0 < c61 ∧ 0 < c62 ∧ 0 < c63 := by
  obtain ⟨c1, c2, c3, h, e1, e2, e3⟩ := frame5_exists F 6
  refine ⟨c1, c2, c3, h, ?_, ?_, ?_⟩
  · rw [e1]; exact div_pos_of_neg_of_neg (F.neg 3 6 (by decide)) (F.neg 3 2 (by decide))
  · rw [e2]; exact div_pos_of_neg_of_neg (F.neg 6 6 (by decide)) (F.neg 6 0 (by decide))
  · rw [e3]; exact div_pos_of_neg_of_neg (F.neg 2 6 (by decide)) (F.neg 2 3 (by decide))

theorem x1_frame {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    ∃ c11 c12 c13 : ℝ, x 1 - x 5 = c11 • (x 2 - x 5) + c12 • (x 0 - x 5) + c13 • (x 3 - x 5) ∧
      0 < c11 ∧ 0 < c12 ∧ 0 < c13 := by
  obtain ⟨c1, c2, c3, h, e1, e2, e3⟩ := frame5_exists F 1
  refine ⟨c1, c2, c3, h, ?_, ?_, ?_⟩
  · rw [e1]; exact div_pos_of_neg_of_neg (F.neg 3 1 (by decide)) (F.neg 3 2 (by decide))
  · rw [e2]; exact div_pos_of_neg_of_neg (F.neg 6 1 (by decide)) (F.neg 6 0 (by decide))
  · rw [e3]; exact div_pos_of_neg_of_neg (F.neg 2 1 (by decide)) (F.neg 2 3 (by decide))


theorem x4_frame {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    ∃ p4 q4 : ℝ, x 4 - x 5 = p4 • (x 0 - x 5) + q4 • (x 3 - x 5) ∧ 0 < p4 ∧ 0 < q4 ∧
      (F.f 8 (x 0) ≤ F.f 8 (x 5) → 1 ≤ q4) ∧ (F.f 8 (x 0) < F.f 8 (x 5) → 1 < q4) := by
  obtain ⟨s, t, hs, ht, hdec, -⟩ := lemmaM_coords F
  have hA : F.f 8 (x 0) < 0 := F.neg 8 0 (by decide)
  have hB : F.f 8 (x 5) < 0 := F.neg 8 5 (by decide)
  have h3 : F.f 8 (x 3) = 0 := F.zero 8 3 (by decide)
  have h4 : F.f 8 (x 4) = 0 := F.zero 8 4 (by decide)
  have hN := congrArg (fun w => ⟪F.N 8, w⟫) hdec
  simp only [inner_add_right, inner_smul_right, F.inner_sub, h3, h4] at hN
  have key : t * F.f 8 (x 5) = (s + t - 1) * F.f 8 (x 0) := by linarith
  have hpos : 0 < s + t - 1 := by
    by_contra h; push Not at h
    nlinarith [mul_pos ht (neg_pos.2 hB), mul_nonneg (neg_nonneg.2 h) (neg_pos.2 hA).le]
  have hvec : s • (x 4 - x 5) = (s + t - 1) • (x 0 - x 5) + (x 3 - x 5) := by
    linear_combination (norm := module) -hdec
  refine ⟨(s + t - 1) / s, 1 / s, ?_, div_pos hpos hs, one_div_pos.2 hs, ?_, ?_⟩
  · apply smul_right_injective _ hs.ne'
    simp only [smul_add, smul_smul]
    rw [mul_div_cancel₀ _ hs.ne', mul_one_div_cancel hs.ne', one_smul]
    exact hvec
  · intro h
    have : s ≤ 1 := by nlinarith
    rw [le_div_iff₀ hs]; linarith
  · intro h
    have : s < 1 := by nlinarith
    rw [lt_div_iff₀ hs]; linarith

theorem rim_pair_lemma {p4 q4 a c61 c62 c63 : ℝ} (hp4 : 0 < p4) (hc61 : 0 < c61) (hc62 : 0 < c62)
    (ha : 1 < a) (hc63 : 1 ≤ c63) (h8 : p4 * (c63 - 1) - (q4 - 1) * c62 < 0) :
    1 < q4 ∧ 0 < (q4 - 1) * (a * c61 + (a - 1) * c62) - (a - 1) * p4 * (c63 - 1) := by
  have h0 : 0 ≤ p4 * (c63 - 1) := mul_nonneg hp4.le (by linarith)
  have hq : 0 < q4 - 1 := by
    by_contra h; push Not at h
    nlinarith [mul_nonneg (neg_nonneg.2 h) hc62.le]
  refine ⟨by linarith, ?_⟩
  nlinarith [mul_pos hq (mul_pos (by linarith : (0:ℝ) < a) hc61),
    mul_pos (by linarith : (0:ℝ) < a - 1) (sub_pos.2 (by linarith : p4 * (c63 - 1) < (q4 - 1) * c62))]


/-- Copy of the front-diagonal part of `u07_bound` (M4Type24): `24` over `06` at `u07`. Needs only `CbarIn`. -/
theorem u07_front {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) :
    FrontDiag (x 2) (x 4) (x 0) (x 6) (u07 x) := by
  have T := type24OfFac F
  have hom3 : 0 < omega3 x := hC.1
  have hom4 : 0 < omega4 x := hC.2.1
  have hom34 : 1 < omega3 x * omega4 x :=
    Minimality.omega_prod_gt_one hC.1 hC.2.1 hC.2.2.1 hC.2.2.2
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
  have hc4 : 0 < oblX6 x 4 := T.X6_pos (v := 4) (by decide)
  -- Front diagonal `24` over `06` at `u07`:
  set den : ℝ := (1 + omega3 x) + oblX2 x 4 * (omega3 x * omega4 x - 1)
  have hden_pos : 0 < den := by
    dsimp [den]; nlinarith [mul_pos hb4 (show 0 < omega3 x * omega4 x - 1 by linarith)]
  set s : ℝ := (1 + omega3 x) / den
  set t : ℝ := s * oblX6 x 4
  set γ : ℝ := oblX2 x 4 * (1 + omega4 x) / den
  have hs0 : 0 < s := div_pos (by linarith) hden_pos
  have hs1 : s < 1 := by
    rw [div_lt_one hden_pos]
    dsimp [den]; nlinarith [mul_pos hb4 (show 0 < omega3 x * omega4 x - 1 by linarith)]
  have ht0 : 0 < t := mul_pos hs0 hc4
  have ht1 : t < 1 := by
    have h236_4 : oblX2 x 4 + oblX6 x 4 - omega3 x * oblX0 x 4 < 1 := by
      have ev := fac_eval F 7 4
      rw [F.zero 7 2 (by decide), F.zero 7 6 (by decide)] at ev
      have e3 := eq3 F
      have h70 : F.f 7 (x 0) - F.f 7 (x 1) = omega3 x * F.f 7 (x 1) := by
        have ev3 := fac_eval F 7 3
        rw [F.zero 7 3 (by decide), F.zero 7 2 (by decide), F.zero 7 6 (by decide)] at ev3
        have : oblX0 x 3 * ((F.f 7 (x 0) - F.f 7 (x 1)) - omega3 x * F.f 7 (x 1)) = 0 := by
          linear_combination -ev3 + F.f 7 (x 1) * e3
        exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left ha3.ne')
      have h71 : 0 < -F.f 7 (x 1) := by linarith [F.neg 7 1 (by decide)]
      have hprod : (-F.f 7 (x 1)) * (oblX2 x 4 + oblX6 x 4 - omega3 x * oblX0 x 4 - 1) = F.f 7 (x 4) := by
        rw [ev, h70]; ring
      nlinarith [F.neg 7 4 (by decide)]
    -- From `h236_4` and `eq4 F`: `(1 + omega3) * c4 < (1 + omega3) + b4 * (omega3 * omega4 - 1) = den`!
    have hlt_den : (1 + omega3 x) * oblX6 x 4 < den := by
      have := eq4 F
      dsimp [den]
      nlinarith
    dsimp [t, s]
    rw [div_mul_eq_mul_div, div_lt_one hden_pos]
    exact hlt_den
  have hγ0 : 0 < γ := div_pos (mul_pos hb4 (by linarith)) hden_pos
  have hdiag_vec : (x 2 + s • (x 4 - x 2)) - (x 0 + t • (x 6 - x 0)) = γ • u07 x := by
    have hrep4 : x 4 - x 1 = oblX0 x 4 • (x 0 - x 1) + oblX2 x 4 • (x 2 - x 1) +
        oblX6 x 4 • (x 6 - x 1) := by rw [T.rep 4]; abel
    have hshift : (x 2 + s • (x 4 - x 2)) - (x 0 + t • (x 6 - x 0)) =
        (1 - s) • (x 2 - x 1) + s • (x 4 - x 1) - (1 - t) • (x 0 - x 1) - t • (x 6 - x 1) := by
      simp only [sub_smul, one_smul, smul_sub]; abel
    rw [hshift, hrep4]
    have e4 := eq4 F
    have hden_ne : den ≠ 0 := hden_pos.ne'
    have c0 : s * oblX0 x 4 - (1 - t) = γ := by
      dsimp [s, t, γ]
      field_simp [hden_ne]
      dsimp [den]
      linear_combination (1 + omega3 x) * e4
    have c2 : (1 - s) + s * oblX2 x 4 = γ * omega3 x := by
      dsimp [s, γ]
      field_simp [hden_ne]
      dsimp [den]; ring
    have c6 : s * oblX6 x 4 - t = 0 := by dsimp [t]; ring
    dsimp [u07]
    calc (1 - s) • (x 2 - x 1) +
          s • (oblX0 x 4 • (x 0 - x 1) + oblX2 x 4 • (x 2 - x 1) + oblX6 x 4 • (x 6 - x 1)) -
          (1 - t) • (x 0 - x 1) - t • (x 6 - x 1)
        = (s * oblX0 x 4 - (1 - t)) • (x 0 - x 1) + ((1 - s) + s * oblX2 x 4) • (x 2 - x 1) +
          (s * oblX6 x 4 - t) • (x 6 - x 1) := by
          simp only [smul_add, smul_smul, add_smul, sub_smul]; abel
      _ = γ • (x 0 - x 1) + (γ * omega3 x) • (x 2 - x 1) + (0 : ℝ) • (x 6 - x 1) := by
          rw [c0, c2, c6]
      _ = γ • ((x 0 - x 1) + omega3 x • (x 2 - x 1)) := by
          simp only [zero_smul, add_zero, smul_add, smul_smul]
  exact ⟨s, t, γ, hs0.le, hs1.le, ht0.le, ht1.le, hγ0, hdiag_vec⟩


theorem det24_eq_det3 (x : Fin 7 → ℝ³) :
    det24 x = Split.det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) := by
  simp [det24, vol3, Split.det3]; ring

private theorem d3_21 (A B C : ℝ³) (a b c : ℝ) :
    Split.det3 (B - A) ((a - 1) • A + b • B + c • C) B = c * Split.det3 A B C := by
  simp [Split.det3]; ring

private theorem d3_61 (A B C : ℝ³) (a b c : ℝ) :
    Split.det3 (B - A) ((a - 1) • A + b • B + c • C) C = -(a + b - 1) * Split.det3 A B C := by
  simp [Split.det3]; ring

/-- `bT26` in the vertex-5 frame: `bT26 x = det24 x • ((a5 - 1) e1 - a5 e2)`, `a5 = oblX0 x 5`.
The factor `μ = det24 x` carries the orientation of the labelled frame (it flips under a mirror). -/
theorem bT26_frame_gen {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    bT26 x = det24 x • ((oblX0 x 5 - 1) • (x 2 - x 5) - oblX0 x 5 • (x 0 - x 5)) := by
  have T := type24OfFac F
  have hrep : x 5 - x 1 = oblX0 x 5 • (x 0 - x 1) + oblX2 x 5 • (x 2 - x 1) +
      oblX6 x 5 • (x 6 - x 1) := by rw [T.rep 5]; abel
  have h20 : x 5 - x 0 = (oblX0 x 5 - 1) • (x 0 - x 1) + oblX2 x 5 • (x 2 - x 1) +
      oblX6 x 5 • (x 6 - x 1) := by
    linear_combination (norm := module) hrep
  have e2 : x 2 - x 0 = (x 2 - x 1) - (x 0 - x 1) := by abel
  unfold bT26
  rw [e2, h20, d3_21, d3_61, ← det24_eq_det3]
  linear_combination (norm := module) (-(det24 x)) • hrep

/-- `bT26_frame`: with the labelled frame positively oriented (`0 < det24 x`) the factor is positive. -/
theorem bT26_frame {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hdet : 0 < det24 x) :
    ∃ μ : ℝ, 0 < μ ∧ bT26 x = μ • ((oblX0 x 5 - 1) • (x 2 - x 5) - oblX0 x 5 • (x 0 - x 5)) :=
  ⟨det24 x, hdet, bT26_frame_gen F⟩

/-- `csl24` hypotheses `h1`, `h6` from the frame coefficients (on the corner `W`). -/
theorem csl24_h16 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {c11 c12 c13 c61 c62 c63 : ℝ}
    (h1 : x 1 - x 5 = c11 • (x 2 - x 5) + c12 • (x 0 - x 5) + c13 • (x 3 - x 5))
    (h6 : x 6 - x 5 = c61 • (x 2 - x 5) + c62 • (x 0 - x 5) + c63 • (x 3 - x 5))
    (h20 : ⟪x 2 - x 5, x 0 - x 5⟫ = 0) (h23 : ⟪x 2 - x 5, x 3 - x 5⟫ = 0)
    (hc11 : c11 < 1) (hc61 : c61 < 1) :
    ⟪x 1 - x 2, x 2 - x 5⟫ < 0 ∧ ⟪x 6 - x 2, x 2 - x 5⟫ < 0 := by
  have hne : x 2 - x 5 ≠ 0 := by
    intro h
    have : F.f 3 (x 2) = F.f 3 (x 5) := by
      have := F.inner_sub 3 2 5; rw [h, inner_zero_right] at this; linarith
    rw [F.zero 3 5 (by decide)] at this
    exact (F.neg 3 2 (by decide)).ne this
  have hpos : 0 < ⟪x 2 - x 5, x 2 - x 5⟫ := real_inner_self_pos.2 hne
  have key : ∀ (c a b : ℝ) (v : ℝ³), v - x 5 = c • (x 2 - x 5) + a • (x 0 - x 5) + b • (x 3 - x 5) →
      ⟪v - x 2, x 2 - x 5⟫ = (c - 1) * ⟪x 2 - x 5, x 2 - x 5⟫ := by
    intro c a b v hv
    have : v - x 2 = (c - 1) • (x 2 - x 5) + a • (x 0 - x 5) + b • (x 3 - x 5) := by
      linear_combination (norm := module) hv
    rw [this, inner_add_left, inner_add_left, inner_smul_left, inner_smul_left, inner_smul_left,
      real_inner_comm (x 2 - x 5) (x 0 - x 5), real_inner_comm (x 2 - x 5) (x 3 - x 5), h20, h23]
    simp
  rw [key c11 c12 c13 _ h1, key c61 c62 c63 _ h6]
  exact ⟨mul_neg_of_neg_of_pos (by linarith) hpos, mul_neg_of_neg_of_pos (by linarith) hpos⟩


/-! ### Link between the vertex-5 frame coefficient and `c1coord` -/

/-- Oblique-coordinate point of vertex `v` (the `y_v` of `c1coord`). -/
noncomputable def yobl (x : Fin 7 → ℝ³) (v : Fin 7) : ℝ³ := yv (oblX0 x v) (oblX2 x v) (oblX6 x v)

private theorem obl_vertices {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    yobl x 0 = yv 1 0 0 ∧ yobl x 2 = yv 0 1 0 ∧ yobl x 6 = yv 0 0 1 ∧ yobl x 1 = yv 0 0 0 := by
  have T := type24OfFac F
  have hD : det24 x ≠ 0 := T.det_ne
  have z : ∀ a c : ℝ³, vol3 a a c = 0 ∧ vol3 a c a = 0 ∧ vol3 c a a = 0 := by
    intro a c; refine ⟨?_, ?_, ?_⟩ <;> simp [vol3] <;> ring
  have z0 : ∀ a b : ℝ³, vol3 (0 : ℝ³) a b = 0 ∧ vol3 a (0 : ℝ³) b = 0 ∧ vol3 a b (0 : ℝ³) = 0 := by
    intro a b; refine ⟨?_, ?_, ?_⟩ <;> simp [vol3]
  have hA := z (x 0 - x 1) (x 2 - x 1)
  have hB := z (x 2 - x 1) (x 0 - x 1)
  have hA' := z (x 0 - x 1) (x 6 - x 1)
  have hC := z (x 6 - x 1) (x 2 - x 1)
  have hB' := z (x 2 - x 1) (x 6 - x 1)
  have hC' := z (x 6 - x 1) (x 0 - x 1)
  have hO := z0 (x 2 - x 1) (x 6 - x 1)
  have hO' := z0 (x 0 - x 1) (x 6 - x 1)
  have hO'' := z0 (x 0 - x 1) (x 2 - x 1)
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [yobl, oblX0, oblX2, oblX6, yv] <;>
    simp [hA, hB, hA', hC, hB', hC', hO, hO', hO'', det24] at hD ⊢ <;> exact hD


private theorem yobl_comb {x : Fin 7 → ℝ³} (v w a b c : Fin 7) {c1 c2 c3 : ℝ}
    (hv : x v - x w = c1 • (x a - x w) + c2 • (x b - x w) + c3 • (x c - x w)) :
    yobl x v - yobl x w =
      c1 • (yobl x a - yobl x w) + c2 • (yobl x b - yobl x w) + c3 • (yobl x c - yobl x w) := by
  have s0 : ∀ u w : Fin 7, oblX0 x u - oblX0 x w = vol3 (x u - x w) (x 2 - x 1) (x 6 - x 1) / det24 x := by
    intro u w; simp only [oblX0]; rw [← sub_div]; congr 1; simp [vol3]; ring
  have s2 : ∀ u w : Fin 7, oblX2 x u - oblX2 x w = vol3 (x 0 - x 1) (x u - x w) (x 6 - x 1) / det24 x := by
    intro u w; simp only [oblX2]; rw [← sub_div]; congr 1; simp [vol3]; ring
  have s6 : ∀ u w : Fin 7, oblX6 x u - oblX6 x w = vol3 (x 0 - x 1) (x 2 - x 1) (x u - x w) / det24 x := by
    intro u w; simp only [oblX6]; rw [← sub_div]; congr 1; simp [vol3]; ring
  have k0 : oblX0 x v - oblX0 x w = c1 * (oblX0 x a - oblX0 x w) + c2 * (oblX0 x b - oblX0 x w) +
      c3 * (oblX0 x c - oblX0 x w) := by
    rw [s0 v w, s0 a w, s0 b w, s0 c w, hv]
    simp only [vol3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  have k2 : oblX2 x v - oblX2 x w = c1 * (oblX2 x a - oblX2 x w) + c2 * (oblX2 x b - oblX2 x w) +
      c3 * (oblX2 x c - oblX2 x w) := by
    rw [s2 v w, s2 a w, s2 b w, s2 c w, hv]
    simp only [vol3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  have k6 : oblX6 x v - oblX6 x w = c1 * (oblX6 x a - oblX6 x w) + c2 * (oblX6 x b - oblX6 x w) +
      c3 * (oblX6 x c - oblX6 x w) := by
    rw [s6 v w, s6 a w, s6 b w, s6 c w, hv]
    simp only [vol3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  ext i; fin_cases i <;> simp [yobl, yv] <;> assumption


private theorem det3_c1 (E1 E2 E3 : ℝ³) (c1 c2 c3 p q : ℝ) :
    Split.det3 (c1 • E1 + c2 • E2 + c3 • E3) E2 ((0 : ℝ) • E1 + p • E2 + q • E3) =
        c1 * q * Split.det3 E1 E2 E3 ∧
    Split.det3 E1 E2 ((0 : ℝ) • E1 + p • E2 + q • E3) = q * Split.det3 E1 E2 E3 := by
  constructor <;> simp [Split.det3] <;> ring

/-- **c1_frame_link**: the `e1`-coefficient of `x v - x 5` in the vertex-5 frame is
`c1coord (y_v) (y_4) (y_5)` (the quantity bounded by `c1_lt_one`), with `y_v = (oblX0, oblX2, oblX6)`.
`hden` is the denominator of `c1coord` (positive on the region: `c1_den_pos`). -/
theorem c1_frame_link {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (v : Fin 7) {c1 c2 c3 p4 q4 : ℝ}
    (hv : x v - x 5 = c1 • (x 2 - x 5) + c2 • (x 0 - x 5) + c3 • (x 3 - x 5))
    (h4 : x 4 - x 5 = p4 • (x 0 - x 5) + q4 • (x 3 - x 5)) (hq : q4 ≠ 0)
    (hden : Split.det3 (yv 0 1 0 - yobl x 5) (yv 1 0 0 - yobl x 5) (yobl x 4 - yobl x 5) ≠ 0) :
    c1coord (yobl x v) (yobl x 4) (yobl x 5) = c1 := by
  obtain ⟨h0, h2, -, -⟩ := obl_vertices F
  have h4' : x 4 - x 5 = (0 : ℝ) • (x 2 - x 5) + p4 • (x 0 - x 5) + q4 • (x 3 - x 5) := by
    rw [h4]; simp
  have kv := yobl_comb v 5 2 0 3 hv
  have k4 := yobl_comb 4 5 2 0 3 h4'
  obtain ⟨d1, d2⟩ := det3_c1 (yobl x 2 - yobl x 5) (yobl x 0 - yobl x 5) (yobl x 3 - yobl x 5) c1 c2 c3 p4 q4
  unfold c1coord
  rw [← h0, ← h2] at hden ⊢
  rw [k4] at hden ⊢
  rw [kv, d1, d2]
  rw [d2] at hden
  have hΔ : Split.det3 (yobl x 2 - yobl x 5) (yobl x 0 - yobl x 5) (yobl x 3 - yobl x 5) ≠ 0 := by
    intro h; apply hden; rw [h]; ring
  field_simp


/-- `c11 < 1` and `c61 < 1` (frame coefficients of `x 1`, `x 6`) from `c1_lt_one`. The three region
hypotheses are `a4 <= 1`, `1 < a5` and `D45 > 0` in the vertex-1 coordinates. -/
theorem frame_c1_lt_one {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    {c11 c12 c13 c61 c62 c63 p4 q4 : ℝ}
    (h1 : x 1 - x 5 = c11 • (x 2 - x 5) + c12 • (x 0 - x 5) + c13 • (x 3 - x 5))
    (h6 : x 6 - x 5 = c61 • (x 2 - x 5) + c62 • (x 0 - x 5) + c63 • (x 3 - x 5))
    (h4 : x 4 - x 5 = p4 • (x 0 - x 5) + q4 • (x 3 - x 5)) (hq : q4 ≠ 0)
    (ha4 : oblX0 x 4 ≤ 1) (ha5 : 1 < oblX0 x 5)
    (hD : 0 < oblX2 x 5 * oblX6 x 4 - oblX2 x 4 * oblX6 x 5) :
    c11 < 1 ∧ c61 < 1 := by
  have T := type24OfFac F
  obtain ⟨-, -, h6y, h1y⟩ := obl_vertices F
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
  have hc4 : 0 < oblX6 x 4 := T.X6_pos (v := 4) (by decide)
  have hb5 : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hden : Split.det3 (yv 0 1 0 - yobl x 5) (yv 1 0 0 - yobl x 5) (yobl x 4 - yobl x 5) ≠ 0 := by
    have := c1_den (oblX0 x 4) (oblX2 x 4) (oblX6 x 4) (oblX0 x 5) (oblX2 x 5) (oblX6 x 5)
    have hn : 0 < oblX6 x 4 * (oblX0 x 5 - 1) + oblX6 x 5 * (1 - oblX0 x 4) := by
      nlinarith [mul_pos hc4 (sub_pos.2 ha5), mul_nonneg hc5.le (sub_nonneg.2 ha4)]
    simp only [yobl]; rw [this]; linarith
  have key := c1_lt_one (oblX0 x 4) (oblX2 x 4) (oblX6 x 4) (oblX0 x 5) (oblX2 x 5) (oblX6 x 5)
    ha4 ha5 hb4 hc4 hb5 hc5 hD
  have l1 := c1_frame_link F 1 h1 h4 hq hden
  have l6 := c1_frame_link F 6 h6 h4 hq hden
  rw [h1y] at l1; rw [h6y] at l6
  simp only [yobl] at l1 l6
  rw [l1] at key; rw [l6] at key
  exact key

/-- The two `csl24` inner-product hypotheses `h1`, `h6` on the region `a4 <= 1 < a5`, `D45 > 0`
(no sigma hypothesis), from the corner `W` (`h20`, `h23`). -/
theorem csl24_h16_of_region {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (h20 : ⟪x 2 - x 5, x 0 - x 5⟫ = 0) (h23 : ⟪x 2 - x 5, x 3 - x 5⟫ = 0)
    (ha4 : oblX0 x 4 ≤ 1) (ha5 : 1 < oblX0 x 5)
    (hD : 0 < oblX2 x 5 * oblX6 x 4 - oblX2 x 4 * oblX6 x 5) :
    ⟪x 1 - x 2, x 2 - x 5⟫ < 0 ∧ ⟪x 6 - x 2, x 2 - x 5⟫ < 0 := by
  obtain ⟨c11, c12, c13, h1, -, -, -⟩ := x1_frame F
  obtain ⟨c61, c62, c63, h6, -, -, -⟩ := x6_frame F
  obtain ⟨p4, q4, h4, -, hq, -⟩ := x4_frame F
  obtain ⟨hc11, hc61⟩ := frame_c1_lt_one F h1 h6 h4 hq.ne' ha4 ha5 hD
  exact csl24_h16 F h1 h6 h20 h23 hc11 hc61

end Minimality.T24.A1
