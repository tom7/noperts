module

public import Minimality.M4jType24
public import Minimality.GenQuadLex
public import Minimality.Type24TiltFac

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

open scoped RealInnerProductSpace
open Finset Filter Topology
open Minimality Minimality.LexCell Minimality.H21 Minimality.H24.SAT
  Minimality.T24.SAT Minimality.T24.RCell Minimality.Split Minimality.T24.M4
  Minimality.T24.A7 Minimality.T24.A8 Minimality.T24.A15 Minimality.T24.Q24 Minimality.T24.A19

namespace Minimality.T24.A19.Tilt

/-- The tilt direction `d1 = -ea - ec`. -/
noncomputable def dd (x : Fin 7 → ℝ³) : ℝ³ := -(x 0 - x 1) - (x 6 - x 1)

theorem xs_ne (x : Fin 7 → ℝ³) (d : ℝ³) (ε : ℝ) {i : Fin 7} (h : i ≠ 2) : xs x d ε i = x i := by
  simp [xs, Function.update_of_ne h]

theorem xs_two (x : Fin 7 → ℝ³) (d : ℝ³) (ε : ℝ) : xs x d ε 2 = x 2 + ε • d := by
  simp [xs]

theorem det24_xs (x : Fin 7 → ℝ³) (ε : ℝ) : det24 (xs x (dd x) ε) = det24 x := by
  simp only [det24, xs_ne _ _ _ (show (0 : Fin 7) ≠ 2 by decide), xs_ne _ _ _ (show (1 : Fin 7) ≠ 2 by decide),
    xs_ne _ _ _ (show (6 : Fin 7) ≠ 2 by decide), xs_two, dd, vol3]
  simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]
  ring

theorem tilt_obl {x : Fin 7 → ℝ³} (ε : ℝ) {p : Fin 7} (hp : p ≠ 2) :
    oblX0 (xs x (dd x) ε) p = oblX0 x p + ε * oblX2 x p ∧
    oblX2 (xs x (dd x) ε) p = oblX2 x p ∧
    oblX6 (xs x (dd x) ε) p = oblX6 x p + ε * oblX2 x p := by
  have hD' := det24_xs x ε
  have e : ∀ q : Fin 7, q ≠ 2 → xs x (dd x) ε q = x q := fun q hq => xs_ne _ _ _ hq
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp only [oblX0, oblX2, oblX6]
    simp only [hD', e p hp, e 0 (by decide), e 1 (by decide), e 6 (by decide), xs_two]
    try simp only [dd, vol3, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]
    try ring

theorem tiltFac_f_unmoved {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (d : ℝ³) (ε : ℝ) {hden hneg} {t : Fin 9}
    (ht : (2 : Fin 7) ∉ s0x_S24 t) (y : ℝ³) : (tiltFac F d ε hden hneg).f t y = F.f t y := by
  simp [tiltFac, muT, ht]

/-- The lex clauses of the 14 fronts of the 6-rim at the tilted view, from the strict fronts of the tilted solid. -/
theorem tilt_neg6 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hω4 : 0 < omega4 x)
    (hnb0 : F.f 3 (x 2) = F.f 3 (x 1)) (hnc : F.f 3 (x 1) < F.f 3 (x 6))
    (h346 : F.f 8 (x 1) < F.f 8 (x 2))
    (h1356 : 0 < oblX0 x 3 * oblX2 x 5 - oblX0 x 5 * oblX2 x 3)
    (h1456 : 0 < oblX0 x 4 * oblX2 x 5 - oblX0 x 5 * oblX2 x 4) :
    ∃ ε : ℝ, 0 < ε ∧ 0 < ⟪x 2 + ε • dd x - x 1, x 2 - x 1⟫ ∧
      GenQuad.FrontOf (x 1) (x 5) (x 0) (x 3) (x 2 + ε • dd x - x 1) ∧
      GenQuad.FrontOf (x 1) (x 5) (x 0) (x 4) (x 2 + ε • dd x - x 1) ∧
      GenQuad.FrontOf (x 1) (x 5) (x 0) (x 6) (x 2 + ε • dd x - x 1) ∧
      GenQuad.FrontOf (x 1) (x 3) (x 0) (x 4) (x 2 + ε • dd x - x 1) ∧
      GenQuad.FrontOf (x 1) (x 3) (x 0) (x 6) (x 2 + ε • dd x - x 1) ∧
      GenQuad.FrontOf (x 1) (x 4) (x 0) (x 6) (x 2 + ε • dd x - x 1) ∧
      GenQuad.FrontOf (x 1) (x 3) (x 5) (x 4) (x 2 + ε • dd x - x 1) ∧
      GenQuad.FrontOf (x 5) (x 6) (x 1) (x 3) (x 2 + ε • dd x - x 1) ∧
      GenQuad.FrontOf (x 5) (x 6) (x 1) (x 4) (x 2 + ε • dd x - x 1) ∧
      GenQuad.FrontOf (x 3) (x 6) (x 1) (x 4) (x 2 + ε • dd x - x 1) ∧
      GenQuad.FrontOf (x 5) (x 6) (x 0) (x 3) (x 2 + ε • dd x - x 1) ∧
      GenQuad.FrontOf (x 5) (x 6) (x 0) (x 4) (x 2 + ε • dd x - x 1) ∧
      GenQuad.FrontOf (x 3) (x 6) (x 0) (x 4) (x 2 + ε • dd x - x 1) ∧
      GenQuad.FrontOf (x 3) (x 6) (x 5) (x 4) (x 2 + ε • dd x - x 1) := by
  have T := type24OfFac F
  have hb : x 2 - x 1 ≠ 0 := sub_ne_zero.mpr fun h => absurd (T.inj h) (by decide)
  have hbb : 0 < ⟪x 2 - x 1, x 2 - x 1⟫ := real_inner_self_pos.mpr hb
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ((∀ t : Fin 9, (2 : Fin 7) ∈ s0x_S24 t → F.f (parT t) (x 2 + ε • dd x) ≠ 0) ∧
      (∀ (t : Fin 9) (i : Fin 7), i ∉ s0x_S24 t →
        F.f t (xs x (dd x) ε i) + muT F (dd x) ε t * F.f (parT t) (xs x (dd x) ε i) < 0)) ∧
      F.f 8 (x 1) < F.f 8 (x 2 + ε • dd x) ∧ 0 < ⟪x 2 + ε • dd x - x 1, x 2 - x 1⟫ ∧ 0 < ε := by
    refine Filter.Eventually.and ((tilt_eventually F (dd x)).filter_mono nhdsWithin_le_nhds) ?_
    refine Filter.Eventually.and ?_ (Filter.Eventually.and ?_ self_mem_nhdsWithin)
    · have hc : Continuous fun ε : ℝ => F.f 8 (x 2 + ε • dd x) := by
        have := F_cont F 8; fun_prop
      exact (hc.continuousAt.eventually (lt_mem_nhds (show F.f 8 (x 1) < F.f 8 (x 2 + (0 : ℝ) • dd x) by
        simpa using h346))).filter_mono nhdsWithin_le_nhds
    · have hc : Continuous fun ε : ℝ => ⟪x 2 + ε • dd x - x 1, x 2 - x 1⟫ := by fun_prop
      exact (hc.continuousAt.eventually (lt_mem_nhds (show 0 < ⟪x 2 + (0 : ℝ) • dd x - x 1, x 2 - x 1⟫ by
        simpa using hbb))).filter_mono nhdsWithin_le_nhds
  obtain ⟨ε, ⟨⟨hden, hneg⟩, h8, hv, hε⟩⟩ := hev.exists
  refine ⟨ε, hε, hv, ?_⟩
  let Fs := tiltFac F (dd x) ε hden hneg
  have n3 : (2 : Fin 7) ∉ s0x_S24 3 := by decide
  have n8 : (2 : Fin 7) ∉ s0x_S24 8 := by decide
  have e1 : xs x (dd x) ε 1 = x 1 := xs_ne _ _ _ (by decide)
  have e2 : xs x (dd x) ε 2 = x 2 + ε • dd x := xs_two _ _ _
  have e0 : xs x (dd x) ε 0 = x 0 := xs_ne _ _ _ (by decide)
  have e3 : xs x (dd x) ε 3 = x 3 := xs_ne _ _ _ (by decide)
  have e4 : xs x (dd x) ε 4 = x 4 := xs_ne _ _ _ (by decide)
  have e5 : xs x (dd x) ε 5 = x 5 := xs_ne _ _ _ (by decide)
  have e6 : xs x (dd x) ε 6 = x 6 := xs_ne _ _ _ (by decide)
  have hN3 : ⟪F.N 3, dd x⟫ < 0 := by
    have h1 := F.inner_sub 3 0 1
    have h2 := F.inner_sub 3 6 1
    have h0 := F.zero 3 0 (by decide)
    have hneg1 := F.neg 3 1 (by decide)
    unfold dd
    rw [inner_sub_right, inner_neg_right]
    linarith
  have hnb' : Fs.f 3 (xs x (dd x) ε 2) < Fs.f 3 (xs x (dd x) ε 1) := by
    rw [tiltFac_f_unmoved F _ _ n3, tiltFac_f_unmoved F _ _ n3, e1, e2]
    have := F.hN 3 (x 2 + ε • dd x) (x 2)
    rw [add_sub_cancel_left, inner_smul_right] at this
    have := mul_neg_of_pos_of_neg hε hN3
    linarith
  have h346' : Fs.f 8 (xs x (dd x) ε 1) < Fs.f 8 (xs x (dd x) ε 2) := by
    rw [tiltFac_f_unmoved F _ _ n8, tiltFac_f_unmoved F _ _ n8, e1, e2]
    exact h8
  have hD : det24 x ≠ 0 := T.det_ne
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
  have o3 := tilt_obl (x := x) ε (p := 3) (by decide)
  have o4 := tilt_obl (x := x) ε (p := 4) (by decide)
  have o5 := tilt_obl (x := x) ε (p := 5) (by decide)
  have hω4' : 0 < omega4 (xs x (dd x) ε) := by
    have : omega4 (xs x (dd x) ε) = omega4 x + 2 * ε := by
      unfold omega4
      rw [o4.1, o4.2.1, o4.2.2]
      field_simp
      ring
    rw [this]; linarith
  have h1356' : 0 < oblX0 (xs x (dd x) ε) 3 * oblX2 (xs x (dd x) ε) 5 -
      oblX0 (xs x (dd x) ε) 5 * oblX2 (xs x (dd x) ε) 3 := by
    rw [o3.1, o3.2.1, o5.1, o5.2.1]; nlinarith
  have h1456' : 0 < oblX0 (xs x (dd x) ε) 4 * oblX2 (xs x (dd x) ε) 5 -
      oblX0 (xs x (dd x) ε) 5 * oblX2 (xs x (dd x) ε) 4 := by
    rw [o4.1, o4.2.1, o5.1, o5.2.1]; nlinarith
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14⟩ :=
    neg6_fronts Fs hω4' hnb' h346' h1356' h1456'
  simp only [e0, e1, e2, e3, e4, e5, e6] at f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14
  exact ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14⟩

end Minimality.T24.A19.Tilt

namespace Minimality.T24.A19

/-- **Tie (a) closed.** Facet 0345 edge-on at `e_b` (`nB = 0`) with `nC > 0`: the 6-rim leaf of `e12_neg6_fo`, with
the 14 front clauses obtained from the strict fronts of the solid with vertex 2 tilted by `ε d1`
(`Tilt.tilt_neg6`) through `frontOf_lex`. -/
theorem tieA_lexAny {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    (hnb0 : F.f 3 (x 2) = F.f 3 (x 1)) (hnc : F.f 3 (x 1) < F.f 3 (x 6))
    (h346 : F.f 8 (x 1) < F.f 8 (x 2))
    (h1356 : 0 < oblX0 x 3 * oblX2 x 5 - oblX0 x 5 * oblX2 x 3)
    (h1456 : 0 < oblX0 x 4 * oblX2 x 5 - oblX0 x 5 * oblX2 x 4)
    (hab : 0 < ⟪x 0 - x 1, x 2 - x 1⟫) (hbc : ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0) : LexAny F := by
  obtain ⟨ε, hε, hv, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14⟩ :=
    Tilt.tilt_neg6 F hC.2.1 hnb0 hnc h346 h1356 h1456
  have hl : LexPos3 ⟪x 2 + ε • Tilt.dd x - x 1, x 2 - x 1⟫
      ⟪x 2 + ε • Tilt.dd x - x 1, Tilt.dd x⟫ ⟪x 2 + ε • Tilt.dd x - x 1, x 0 - x 1⟫ := Or.inl hv
  have h8 : LexPos3 ⟪F.N 8, x 2 - x 1⟫ ⟪F.N 8, -(x 0 - x 1) - (x 6 - x 1)⟫ ⟪F.N 8, x 0 - x 1⟫ := by
    left; rw [← F.hN]; linarith
  exact e12_neg6_fo F hC.2.1 (Or.inr ⟨hnb0, hnc⟩) h8 hab hbc
    (GenQuad.frontOf_lex f1 hl) (GenQuad.frontOf_lex f2 hl) (GenQuad.frontOf_lex f3 hl)
    (GenQuad.frontOf_lex f4 hl) (GenQuad.frontOf_lex f5 hl) (GenQuad.frontOf_lex f6 hl)
    (GenQuad.frontOf_lex f7 hl) (GenQuad.frontOf_lex f8 hl) (GenQuad.frontOf_lex f9 hl)
    (GenQuad.frontOf_lex f10 hl) (GenQuad.frontOf_lex f11 hl) (GenQuad.frontOf_lex f12 hl)
    (GenQuad.frontOf_lex f13 hl) (GenQuad.frontOf_lex f14 hl)

end Minimality.T24.A19
