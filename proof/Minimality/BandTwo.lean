module

public import Minimality.RimCellClosed

@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace

namespace Minimality.H21

/-- **Lemma B2, algebraic core (Case 3).**  Real numbers `al, be, ga > 0`, `0 < b3, c3 < 1`,
`h, g > 0`, `s > 0`.  If `Xh0, Xh6, Yg0, Yg2 <= 0` (Cases 1 and 2 fail) and one of the shape
conditions `C1, C2, C3, C3'` holds, then `P2 < 0` or `P6 < 0` (`z3` above `z2` or `z6` at `r3`).
Farkas identities ID1, ID2, ID3, ID3' of `BAND2LEMMA24.md`. -/
theorem band2_core (sa sb sc al be ga b3 c3 ha hb hc gA gB gC : ℝ)
    (hsb : 0 < sb) (hsc : 0 < sc) (hal : 0 < al) (hbe : 0 < be) (hga : 0 < ga)
    (hb3 : 0 < b3) (hb31 : b3 < 1) (hc3 : 0 < c3) (hc31 : c3 < 1)
    (hha : 0 < ha) (hhc : 0 < hc) (hgA : 0 < gA) (hgB : 0 < gB)
    (hX0 : sa * ha - sb * hb ≤ 0) (hX6 : sc * hc - sb * hb ≤ 0)
    (hY0 : sa * gA - sc * gC ≤ 0) (hY2 : sb * gB - sc * gC ≤ 0)
    (hC : 0 < (b3 + c3 - 1) * be * ha - al * hb ∨ 0 < (b3 + c3 - 1) * ga * gA - al * gC ∨
      0 < b3 * be * ha * hc - al * hb * hc - (1 - c3) * ga * ha * hb ∨
      0 < c3 * ga * gA * gB - al * gB * gC - (1 - b3) * be * gA * gC) :
    al * sa + (1 - b3) * be * sb - c3 * ga * sc < 0 ∨
      al * sa - b3 * be * sb + (1 - c3) * ga * sc < 0 := by
  by_contra hcon
  simp only [not_or, not_lt] at hcon
  obtain ⟨hP2, hP6⟩ := hcon
  have h1c3 : 0 < 1 - c3 := by linarith
  have h1b3 : 0 < 1 - b3 := by linarith
  rcases hC with C | C | C | C
  · -- ID1
    have id : ha * ((1 - c3) * (al * sa + (1 - b3) * be * sb - c3 * ga * sc) +
        c3 * (al * sa - b3 * be * sb + (1 - c3) * ga * sc)) + al * (-(sa * ha - sb * hb)) =
        -(((b3 + c3 - 1) * be * ha - al * hb) * sb) := by ring
    have : 0 ≤ ha * ((1 - c3) * (al * sa + (1 - b3) * be * sb - c3 * ga * sc) +
        c3 * (al * sa - b3 * be * sb + (1 - c3) * ga * sc)) + al * (-(sa * ha - sb * hb)) := by
      have := mul_nonneg h1c3.le hP2
      have := mul_nonneg hc3.le hP6
      have := mul_nonneg hal.le (neg_nonneg.2 hX0)
      nlinarith [mul_nonneg hha.le (add_nonneg ‹0 ≤ (1 - c3) * _› ‹0 ≤ c3 * _›)]
    nlinarith [mul_pos C hsb]
  · -- ID2
    have id : gA * (b3 * (al * sa + (1 - b3) * be * sb - c3 * ga * sc) +
        (1 - b3) * (al * sa - b3 * be * sb + (1 - c3) * ga * sc)) +
        al * (-(sa * gA - sc * gC)) =
        -(((b3 + c3 - 1) * ga * gA - al * gC) * sc) := by ring
    have : 0 ≤ gA * (b3 * (al * sa + (1 - b3) * be * sb - c3 * ga * sc) +
        (1 - b3) * (al * sa - b3 * be * sb + (1 - c3) * ga * sc)) +
        al * (-(sa * gA - sc * gC)) := by
      have e1 := mul_nonneg hb3.le hP2
      have e2 := mul_nonneg h1b3.le hP6
      have e3 := mul_nonneg hal.le (neg_nonneg.2 hY0)
      nlinarith [mul_nonneg hgA.le (add_nonneg e1 e2)]
    nlinarith [mul_pos C hsc]
  · -- ID3
    have id : ha * hc * (al * sa - b3 * be * sb + (1 - c3) * ga * sc) +
        al * hc * (-(sa * ha - sb * hb)) + (1 - c3) * ga * ha * (-(sc * hc - sb * hb)) =
        -((b3 * be * ha * hc - al * hb * hc - (1 - c3) * ga * ha * hb) * sb) := by ring
    have e1 := mul_nonneg (mul_pos hha hhc).le hP6
    have e2 := mul_nonneg (mul_pos hal hhc).le (neg_nonneg.2 hX0)
    have e3 := mul_nonneg (mul_pos (mul_pos h1c3 hga) hha).le (neg_nonneg.2 hX6)
    nlinarith [mul_pos C hsb]
  · -- ID3'
    have id : gA * gB * (al * sa + (1 - b3) * be * sb - c3 * ga * sc) +
        al * gB * (-(sa * gA - sc * gC)) + (1 - b3) * be * gA * (-(sb * gB - sc * gC)) =
        -((c3 * ga * gA * gB - al * gB * gC - (1 - b3) * be * gA * gC) * sc) := by ring
    have e1 := mul_nonneg (mul_pos hgA hgB).le hP2
    have e2 := mul_nonneg (mul_pos hal hgB).le (neg_nonneg.2 hY0)
    have e3 := mul_nonneg (mul_pos (mul_pos h1b3 hbe) hgA).le (neg_nonneg.2 hY2)
    nlinarith [mul_pos C hsc]


/-- **Lemma B2 (second band lemma), geometric wrapper.**  Seven points `x : Fin 7 -> R^3`, three
4-rim cells (rims `0 2 6 4`, `0 5 2 6`, `1 2 3 6`) with cell certificates and closure points
`wc, h` (cell 0264), `wb, g` (cell 0526), `r3` (cell 1236, one point for both signs).  The
depth differences at those points are given as real expressions in `s = (sa, sb, sc)` and the
shape numbers (the caller derives them from the frame, `BAND2LEMMA24.md` section 2); with the
shape conditions of region R2 (`la < 0`, `0 < b3, c3 < 1`, signs, one of `C1, C2, C3, C3'`)
the conclusion is `IsRupert`. -/
theorem isRupert_of_band2 {m : ℕ} {S : Fin m → Finset (Fin 7)} {x : Fin 7 → ℝ³}
    (F : S0xFac m S x) (hx : Function.Injective x)
    {c1 c2 c3' : ZMod 4 → Fin 7} (hc1 : c1 = ![0, 2, 6, 4]) (hc2 : c2 = ![0, 5, 2, 6])
    (hc3 : c3' = ![1, 2, 3, 6])
    {U1 D1 U2 D2 U3 D3 : Finset (Fin m)}
    (hcyc1 : S0xCycUD S c1 U1 D1) (hcyc2 : S0xCycUD S c2 U2 D2) (hcyc3 : S0xCycUD S c3' U3 D3)
    {a1 a2 a3' : ℝ³} (ha1 : CellAt F U1 D1 a1) (ha2 : CellAt F U2 D2 a2) (ha3 : CellAt F U3 D3 a3')
    {wc h wb g r3 : ℝ³}
    (hwc : CellLe F U1 D1 wc) (hh : CellLe F U1 D1 h)
    (hwb : CellLe F U2 D2 wb) (hg : CellLe F U2 D2 g) (hr : CellLe F U3 D3 r3)
    (sa sb sc la al be ga b3 c3 ha hb hc gA gB gC : ℝ)
    (hsb : 0 < sb) (hsc : 0 < sc) (hla : la < 0) (hal : 0 < al) (hbe : 0 < be) (hga : 0 < ga)
    (hb3 : 0 < b3) (hb31 : b3 < 1) (hc3p : 0 < c3) (hc31 : c3 < 1)
    (hha : 0 < ha) (hhc : 0 < hc) (hgA : 0 < gA) (hgB : 0 < gB)
    (hC : 0 < (b3 + c3 - 1) * be * ha - al * hb ∨ 0 < (b3 + c3 - 1) * ga * gA - al * gC ∨
      0 < b3 * be * ha * hc - al * hb * hc - (1 - c3) * ga * ha * hb ∨
      0 < c3 * ga * gA * gB - al * gB * gC - (1 - b3) * be * gA * gC)
    (e_wc : ⟪x 6 - x 2, wc⟫ = la * sb) (e_wb : ⟪x 2 - x 6, wb⟫ = la * sc)
    (e_h0 : ⟪x 0 - x 2, h⟫ = sa * ha - sb * hb) (e_h6 : ⟪x 6 - x 2, h⟫ = sc * hc - sb * hb)
    (e_g0 : ⟪x 0 - x 6, g⟫ = sa * gA - sc * gC) (e_g2 : ⟪x 2 - x 6, g⟫ = sb * gB - sc * gC)
    (e_r1 : ⟪x 1 - x 2, r3⟫ = -(sb * be))
    (e_r2 : ⟪x 3 - x 2, r3⟫ = -(al * sa + (1 - b3) * be * sb - c3 * ga * sc))
    (e_r6 : ⟪x 3 - x 6, r3⟫ = -(al * sa - b3 * be * sb + (1 - c3) * ga * sc)) :
    IsRupert (Finset.univ.image x) := by
  subst hc1 hc2 hc3
  by_cases k1 : 0 < sa * ha - sb * hb ∨ 0 < sc * hc - sb * hb
  · refine isRupert_of_closedCell_q4 F hx (c := ![0, 2, 6, 4]) ?_ hcyc1 ha1 hwc hh
      ⟨(2, 1), by decide, ?_⟩ ?_
    · intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)
    · simp only [Matrix.cons_val]; rw [e_wc]; nlinarith
    · rcases k1 with k | k
      · exact ⟨(0, 1), by decide, by simp only [Matrix.cons_val]; linarith [e_h0]⟩
      · exact ⟨(2, 1), by decide, by simp only [Matrix.cons_val]; linarith [e_h6]⟩
  by_cases k2 : 0 < sa * gA - sc * gC ∨ 0 < sb * gB - sc * gC
  · refine isRupert_of_closedCell_q4 F hx (c := ![0, 5, 2, 6]) ?_ hcyc2 ha2 hwb hg
      ⟨(2, 3), by decide, ?_⟩ ?_
    · intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)
    · simp only [Matrix.cons_val]; rw [e_wb]; nlinarith
    · rcases k2 with k | k
      · exact ⟨(0, 3), by decide, by simp only [Matrix.cons_val]; linarith [e_g0]⟩
      · exact ⟨(2, 3), by decide, by simp only [Matrix.cons_val]; linarith [e_g2]⟩
  push Not at k1 k2
  have core := band2_core sa sb sc al be ga b3 c3 ha hb hc gA gB gC hsb hsc hal hbe hga hb3 hb31
    hc3p hc31 hha hhc hgA hgB k1.1 k1.2 k2.1 k2.2 hC
  refine isRupert_of_closedCell_q4 F hx (c := ![1, 2, 3, 6]) ?_ hcyc3 ha3 hr hr
    ⟨(0, 1), by decide, ?_⟩ ?_
  · intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)
  · simp only [Matrix.cons_val]; rw [e_r1]; nlinarith
  · rcases core with k | k
    · exact ⟨(2, 1), by decide, by simp only [Matrix.cons_val]; linarith [e_r2]⟩
    · exact ⟨(2, 3), by decide, by simp only [Matrix.cons_val]; linarith [e_r6]⟩

end Minimality.H21
