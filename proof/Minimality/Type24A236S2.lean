module

public import Minimality.Type24GapLemmas2

/-!
# A236S2: the shape fact S2 of the `A2.236` wall (two Pluecker identities on a convex 5-rim)

nopert229 notes/A236-MECHANISM.md (S2), Fable's hand proof in notes/FABLE-A236-REPLY.md section 1.

* `rim5_pluecker`: five points `p0, p5, p3, p6, p1` of `ℝ³` and a view `w`, with the rim `0.5.3.6.1` strictly
  convex at `w` in the sense of the six rim-side letters `0 < det(q - p, y - p, w)` (edges `p → q` of the cycle, `y`
  another corner).  Then `Q = det(p5 - p3, p1 - p6, w) ≥ 0` forces
  `det(p0 - p5, p6 - p1, w) < 0`, `det(p5 - p3, p1 - p0, w) < 0`, `det(p0 - p3, p1 - p6, w) > 0` and
  `det(p0 - p6, p3 - p5, w) > 0`.  Meaning: `Q ≥ 0` says `p3` is at least as far as `p5` from the screen line `p1 p6`;
  the unimodality of a linear function round a convex polygon then puts `p0` strictly below `p5`.
* `a236_S2`: the instance on the `236` wall `t2e236 x s` of the `T_2` cell `A2` in a positively oriented frame
  (`0 < det24 x`; S2 flips under a mirror).  The six letters come from `rimSign_of_cell`, the orientation `ρ = 1`
  from facet `016` in front.  No `CbarIn`, no `OB1`, no `0 < s`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset

namespace Minimality.T24.Cell

open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.HC Minimality.T24.SF Minimality.T24.Stmt

/-- **Two Pluecker identities on a strictly convex 5-rim.** -/
theorem rim5_pluecker (p0 p5 p3 p6 p1 w : ℝ³)
    (h1 : 0 < Split.det3 (p3 - p5) (p0 - p5) w) (h2 : 0 < Split.det3 (p5 - p0) (p1 - p0) w)
    (h3 : 0 < Split.det3 (p0 - p1) (p6 - p1) w) (h4 : 0 < Split.det3 (p3 - p5) (p6 - p5) w)
    (h5 : 0 < Split.det3 (p5 - p0) (p6 - p0) w) (h6 : 0 < Split.det3 (p1 - p6) (p5 - p6) w)
    (hQ : 0 ≤ Split.det3 (p5 - p3) (p1 - p6) w) :
    Split.det3 (p0 - p5) (p6 - p1) w < 0 ∧ Split.det3 (p5 - p3) (p1 - p0) w < 0 ∧
      0 < Split.det3 (p0 - p3) (p1 - p6) w ∧ 0 < Split.det3 (p0 - p6) (p3 - p5) w := by
  -- Step 1 (Pluecker): `det(p3-p5,p6-p5) * Y = -h1 h6 - Q h5`
  have e1 : Split.det3 (p3 - p5) (p6 - p5) w * Split.det3 (p0 - p5) (p6 - p1) w =
      -(Split.det3 (p3 - p5) (p0 - p5) w * Split.det3 (p1 - p6) (p5 - p6) w) -
        Split.det3 (p5 - p3) (p1 - p6) w * Split.det3 (p5 - p0) (p6 - p0) w := by
    simp only [Split.det3, PiLp.sub_apply]; ring
  have hY : Split.det3 (p0 - p5) (p6 - p1) w < 0 := by
    by_contra hc
    push Not at hc
    nlinarith [mul_pos h1 h6, mul_nonneg hQ h5.le, mul_nonneg h4.le hc]
  -- Step 2 (Pluecker): `Z * Y = h1 h3 + Q h2`
  have e2 : Split.det3 (p5 - p3) (p1 - p0) w * Split.det3 (p0 - p5) (p6 - p1) w =
      Split.det3 (p3 - p5) (p0 - p5) w * Split.det3 (p0 - p1) (p6 - p1) w +
        Split.det3 (p5 - p3) (p1 - p6) w * Split.det3 (p5 - p0) (p1 - p0) w := by
    simp only [Split.det3, PiLp.sub_apply]; ring
  have hZ : Split.det3 (p5 - p3) (p1 - p0) w < 0 := by
    by_contra hc
    push Not at hc
    nlinarith [mul_pos h1 h3, mul_nonneg hQ h2.le, mul_nonneg hc (neg_nonneg.mpr hY.le)]
  refine ⟨hY, hZ, ?_, ?_⟩
  · have : Split.det3 (p0 - p3) (p1 - p6) w = -Split.det3 (p0 - p5) (p6 - p1) w + Split.det3 (p5 - p3) (p1 - p6) w := by
      simp only [Split.det3, PiLp.sub_apply]; ring
    linarith
  · have : Split.det3 (p0 - p6) (p3 - p5) w = -Split.det3 (p5 - p3) (p1 - p0) w + Split.det3 (p5 - p3) (p1 - p6) w := by
      simp only [Split.det3, PiLp.sub_apply]; ring
    linarith

/-- **S2 on the `236` wall of `A2`.**  In a positively oriented frame (`0 < det24 x`), on the wall view
`w = t2e236 x s` in the open cell `A2` (`016, 0345, 046, 346` in front, `012, 025, 126, 235, 236` behind), the shape
letter `Q = det(x₅ - x₃, x₁ - x₆, w) ≥ 0` forces `det(x₀ - x₅, x₆ - x₁, w) < 0`, `det(x₅ - x₃, x₁ - x₀, w) < 0`,
`g63 = det(x₀ - x₃, x₁ - x₆, w) > 0` and `g36 = det(x₀ - x₆, x₃ - x₅, w) > 0`.  The orientation hypothesis is needed
(S2 flips under a mirror); `CbarIn`, `OB1` and `0 < s` are not. -/
theorem a236_S2 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hdet : 0 < det24 x) {s : ℝ}
    (hcell : CellAt F cellA2.U (univ \ cellA2.U) (t2e236 x s))
    (hQ : 0 ≤ Split.det3 (x 5 - x 3) (x 1 - x 6) (t2e236 x s)) :
    Split.det3 (x 0 - x 5) (x 6 - x 1) (t2e236 x s) < 0 ∧
      Split.det3 (x 5 - x 3) (x 1 - x 0) (t2e236 x s) < 0 ∧
      0 < Split.det3 (x 0 - x 3) (x 1 - x 6) (t2e236 x s) ∧
      0 < Split.det3 (x 0 - x 6) (x 3 - x 5) (t2e236 x s) := by
  obtain ⟨ρ, hρ, hrim⟩ := rimSign_of_cell F cellA2 hcell
  generalize t2e236 x s = w at hcell hQ hrim
  have l1 : 0 < ρ * Split.det3 (x 3 - x 5) (x 0 - x 5) w := hrim 1 0 (by decide) (by decide)
  have l2 : 0 < ρ * Split.det3 (x 5 - x 0) (x 1 - x 0) w := hrim 0 4 (by decide) (by decide)
  have l3 : 0 < ρ * Split.det3 (x 0 - x 1) (x 6 - x 1) w := hrim 4 3 (by decide) (by decide)
  have l4 : 0 < ρ * Split.det3 (x 3 - x 5) (x 6 - x 5) w := hrim 1 3 (by decide) (by decide)
  have l5 : 0 < ρ * Split.det3 (x 5 - x 0) (x 6 - x 0) w := hrim 0 3 (by decide) (by decide)
  have l6 : 0 < ρ * Split.det3 (x 1 - x 6) (x 5 - x 6) w := hrim 3 1 (by decide) (by decide)
  -- the orientation `ρ = 1`, from facet `016` in front and `0 < det24 x`
  have hw1 : 0 < ⟪F.N 1, w⟫ := hcell.1 1 (by decide)
  have hq : ⟪F.N 1, x 2 - x 0⟫ < 0 := by
    rw [F.inner_sub, F.zero 1 0 (by decide)]; simpa using F.neg 1 2 (by decide)
  have key := det3_mul_inner_of_perp (F.N 1) (x 1 - x 0) (x 6 - x 0) (x 2 - x 0) w
    (by rw [F.inner_sub, F.zero 1 1 (by decide), F.zero 1 0 (by decide)]; ring)
    (by rw [F.inner_sub, F.zero 1 6 (by decide), F.zero 1 0 (by decide)]; ring)
  have hor : Split.det3 (x 1 - x 0) (x 6 - x 0) (x 2 - x 0) = det24 x := by
    simp only [det24, vol3, Split.det3, PiLp.sub_apply]; ring
  rw [hor] at key
  have hneg : Split.det3 (x 1 - x 0) (x 6 - x 0) w < 0 := by
    by_contra hc
    push Not at hc
    nlinarith [mul_nonneg hc (neg_nonneg.mpr hq.le), mul_pos hdet hw1]
  have e3 : Split.det3 (x 0 - x 1) (x 6 - x 1) w = -Split.det3 (x 1 - x 0) (x 6 - x 0) w := by
    simp only [Split.det3, PiLp.sub_apply]; ring
  have hρ1 : ρ = 1 := by
    rcases hρ with rfl | rfl
    · rfl
    · exfalso; rw [e3] at l3; linarith
  subst hρ1
  simp only [one_mul] at l1 l2 l3 l4 l5 l6
  exact rim5_pluecker (x 0) (x 5) (x 3) (x 6) (x 1) w l1 l2 l3 l4 l5 l6 hQ

end Minimality.T24.Cell
