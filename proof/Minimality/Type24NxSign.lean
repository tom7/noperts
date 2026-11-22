module

public import Minimality.Type24C3One

@[expose] public section

/-!
# Type 24: the bracket sign `Nx < 0` (`NXSIGN`)

`nx_neg`: `Nx = b4 c5 - c4 b5 < 0` from facets 025 and 046 and positive coordinates only (no CbarIn,
no OB1). Identity: with `S4 = a4 + b4 + c4 - 1`, `S5 = a5 + b5 + c5 - 1`,
`-S4 Nx = b4 (c4 S5 - c5 S4) + c4 (b5 S4 - b4 S5)`, both brackets positive (facet 025 at x4, x6;
facet 046 at x5, x2), `S4 > 0` (facet 046 at x4). Used by the `F012 x F0345` line theorems (L0345).
-/

set_option autoImplicit false

open scoped RealInnerProductSpace
open Finset

namespace Minimality.T24.A20
open Minimality Minimality.H21 Minimality.H24.SAT Minimality.T24.SAT Minimality.T24.RCell

/-- Nx = b4 c5 - c4 b5 < 0 from facets 025 (at x4, x6) and 046 (at x5, x2). -/
theorem nx_neg {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    oblX2 x 4 * oblX6 x 5 - oblX6 x 4 * oblX2 x 5 < 0 := by
  have T := Minimality.T24.M4.type24OfFac F
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hc4 : 0 < oblX6 x 4 := T.X6_pos (v := 4) (by decide)
  have hb5 : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
  -- facet 025 (index 2)
  have p1 : F.f 2 (x 1) < 0 := F.neg 2 1 (by decide)
  have p6 : F.f 2 (x 6) < 0 := F.neg 2 6 (by decide)
  have p4 : F.f 2 (x 4) < 0 := F.neg 2 4 (by decide)
  have p0 : F.f 2 (x 0) = 0 := F.zero 2 0 (by decide)
  have p2 : F.f 2 (x 2) = 0 := F.zero 2 2 (by decide)
  have p5 : F.f 2 (x 5) = 0 := F.zero 2 5 (by decide)
  have e4 := Minimality.T24.M4.fac_eval F 2 4
  have e5 := Minimality.T24.M4.fac_eval F 2 5
  rw [p0, p2] at e4 e5
  rw [p5] at e5
  -- facet 046 (index 4)
  have q1 : F.f 4 (x 1) < 0 := F.neg 4 1 (by decide)
  have q2 : F.f 4 (x 2) < 0 := F.neg 4 2 (by decide)
  have q5 : F.f 4 (x 5) < 0 := F.neg 4 5 (by decide)
  have q0 : F.f 4 (x 0) = 0 := F.zero 4 0 (by decide)
  have q6 : F.f 4 (x 6) = 0 := F.zero 4 6 (by decide)
  have q4 : F.f 4 (x 4) = 0 := F.zero 4 4 (by decide)
  have g4 := Minimality.T24.M4.fac_eval F 4 4
  have g5 := Minimality.T24.M4.fac_eval F 4 5
  rw [q0, q6] at g4 g5
  rw [q4] at g4
  generalize oblX0 x 4 = a4 at *
  generalize oblX0 x 5 = a5 at *
  generalize oblX2 x 4 = b4 at *
  generalize oblX2 x 5 = b5 at *
  generalize oblX6 x 4 = c4 at *
  generalize oblX6 x 5 = c5 at *
  generalize F.f 2 (x 1) = f1 at *
  generalize F.f 2 (x 6) = f6 at *
  generalize F.f 2 (x 4) = f4 at *
  generalize F.f 4 (x 1) = h1 at *
  generalize F.f 4 (x 2) = h2 at *
  generalize F.f 4 (x 5) = h5 at *
  -- S4 = a4+b4+c4-1, S5 = a5+b5+c5-1
  -- facet 025: u S5 = -c5 g, u S4 + c4 g < 0 with u = -f1, g = f6
  -- PA = c4 S5 - c5 S4 > 0 ;  PB = b5 S4 - b4 S5 > 0 ; S4 > 0
  have hS4 : 0 < a4 + b4 + c4 - 1 := by
    by_contra h
    push Not at h
    nlinarith [mul_pos hb4 (neg_pos.mpr q1), mul_nonneg hb4.le (neg_nonneg.mpr h), mul_pos hb4 (neg_pos.mpr q2)]
  have hPA : 0 < c4 * (a5 + b5 + c5 - 1) - c5 * (a4 + b4 + c4 - 1) := by
    by_contra h
    push Not at h
    nlinarith [mul_pos hc5 (neg_pos.mpr p1), mul_pos hc4 (neg_pos.mpr p6), mul_nonneg (neg_pos.mpr p1).le (neg_nonneg.mpr h), mul_pos hc5 (neg_pos.mpr p4)]
  have hPB : 0 < b5 * (a4 + b4 + c4 - 1) - b4 * (a5 + b5 + c5 - 1) := by
    by_contra h
    push Not at h
    nlinarith [mul_pos hb4 (neg_pos.mpr q1), mul_pos hb4 (neg_pos.mpr q2), mul_pos hb5 (neg_pos.mpr q2), mul_pos hb4 (neg_pos.mpr q5)]
  have key : (a4 + b4 + c4 - 1) * (b4 * c5 - c4 * b5) = -(b4 * (c4 * (a5 + b5 + c5 - 1) - c5 * (a4 + b4 + c4 - 1)) + c4 * (b5 * (a4 + b4 + c4 - 1) - b4 * (a5 + b5 + c5 - 1))) := by ring
  have : (a4 + b4 + c4 - 1) * (b4 * c5 - c4 * b5) < 0 := by
    rw [key]; nlinarith [mul_pos hb4 hPA, mul_pos hc4 hPB]
  by_contra hh
  push Not at hh
  nlinarith [mul_nonneg hS4.le hh]

end Minimality.T24.A20
