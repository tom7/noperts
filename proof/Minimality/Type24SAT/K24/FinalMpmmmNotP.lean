module

public import Minimality.Type24SAT.K24.LinkMpmmmNotP

@[expose] public section

/-!
# Type 24, class mpmmm off the obtuse corner: `Minimality.T24.isRupert_offOB1_mpmmm_notP`

A type 24 shape (nine facets `s0x_S24`) with the five brackets `[1234]- [1245]+ [1356]- [1456]- [2456]-` and chirality `[0126] < 0`, or with all six signs
reversed (the mirror image), and with an acute face angle at vertex `1` (not all of `⟪x0 - x1, x2 - x1⟫`, `⟪x0 - x1, x6 - x1⟫`,
`⟪x2 - x1, x6 - x1⟫` are `≤ 0`) is Rupert.  The proof is the kernel-checked unsatisfiability of a core of the tie view encoding,
with the brackets as class literals and the acute-angle clause as class clause (`rupert_of_coreMpmmmNotP`); the mirror orientation is
the reflection of the reference one.

Case `notP` (parallelogram split): the quad facet `D = {0, 3, 4, 5}` is not a parallelogram, i.e. the opposite side pairs
`x0 - x4`, `x3 - x5` and `x0 - x5`, `x3 - x4` do not both have vanishing `det3 (.) (.) (F.N 3)` (`F.N 3` the normal of `D`; `D` is
planar, so `det3 a b n = 0` iff `a`, `b` are parallel).
-/

set_option autoImplicit false
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.H29.SAT

/-- **Class mpmmm off the obtuse corner `OB1` is closed, case `D` is not a parallelogram.**  The chirality bracket and the five class brackets all have the
reference signs, or all the opposite signs. -/
theorem Minimality.T24.isRupert_offOB1_mpmmm_notP {x : Fin 7 → EuclideanSpace ℝ (Fin 3)}
    (F : S0xFac 9 Minimality.T24.SAT.s0x_S24 x)
    (hcls : (det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) < 0 ∧ det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1) < 0 ∧ 0 < det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1) ∧ det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1) < 0 ∧ det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1) < 0 ∧ det3 (x 4 - x 2) (x 5 - x 2) (x 6 - x 2) < 0) ∨
      (0 < det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) ∧ 0 < det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1) ∧ det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1) < 0 ∧ 0 < det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1) ∧ 0 < det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1) ∧ 0 < det3 (x 4 - x 2) (x 5 - x 2) (x 6 - x 2)))
    (hO : ¬ Minimality.H24K.SAT.OB1 x)
    (hP : ¬ (det3 (x 0 - x 4) (x 3 - x 5) (F.N 3) = 0 ∧ det3 (x 0 - x 5) (x 3 - x 4) (F.N 3) = 0)) :
    IsRupert (Finset.univ.image x) := by
  rcases hcls with ⟨hc, h0, h1, h2, h3, h4⟩ | ⟨hc, h0, h1, h2, h3, h4⟩
  · exact Minimality.H24K.SAT.rupert_of_coreMpmmmNotP Minimality.H24K.SAT.coreUnsatMpmmmNotP F hc h0 h1 h2 h3 h4 hO hP
  · refine isRupert_of_mir (Minimality.H24K.SAT.rupert_of_coreMpmmmNotP Minimality.H24K.SAT.coreUnsatMpmmmNotP (mirFac F) ?_ ?_ ?_ ?_ ?_ ?_
      (Minimality.H24K.SAT.ob1_mir hO) (Minimality.H24K.SAT.notP_mir F hP))
    · show det3 (mir (x 1) - mir (x 0)) (mir (x 2) - mir (x 0)) (mir (x 6) - mir (x 0)) < 0
      rw [← mir_sub, ← mir_sub, ← mir_sub, mir_det3]; linarith
    · show det3 (mir (x 2) - mir (x 1)) (mir (x 3) - mir (x 1)) (mir (x 4) - mir (x 1)) < 0
      rw [← mir_sub, ← mir_sub, ← mir_sub, mir_det3]; linarith
    · show 0 < det3 (mir (x 2) - mir (x 1)) (mir (x 4) - mir (x 1)) (mir (x 5) - mir (x 1))
      rw [← mir_sub, ← mir_sub, ← mir_sub, mir_det3]; linarith
    · show det3 (mir (x 3) - mir (x 1)) (mir (x 5) - mir (x 1)) (mir (x 6) - mir (x 1)) < 0
      rw [← mir_sub, ← mir_sub, ← mir_sub, mir_det3]; linarith
    · show det3 (mir (x 4) - mir (x 1)) (mir (x 5) - mir (x 1)) (mir (x 6) - mir (x 1)) < 0
      rw [← mir_sub, ← mir_sub, ← mir_sub, mir_det3]; linarith
    · show det3 (mir (x 4) - mir (x 2)) (mir (x 5) - mir (x 2)) (mir (x 6) - mir (x 2)) < 0
      rw [← mir_sub, ← mir_sub, ← mir_sub, mir_det3]; linarith

#print axioms Minimality.T24.isRupert_offOB1_mpmmm_notP
