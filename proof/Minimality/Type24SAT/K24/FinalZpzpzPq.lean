module

public import Minimality.Type24SAT.K24.LinkZpzpzPq

@[expose] public section

/-!
# Type 24, class zpzpz off the obtuse corner: `Minimality.T24.isRupert_offOB1_zpzpz_Pq`

A type 24 shape (nine facets `s0x_S24`) with the five brackets `[1234]0 [1245]+ [1356]0 [1456]+ [2456]0` and chirality `[0126] < 0`, or with all six signs
reversed (the mirror image), and with an acute face angle at vertex `1` (not all of `⟪x0 - x1, x2 - x1⟫`, `⟪x0 - x1, x6 - x1⟫`,
`⟪x2 - x1, x6 - x1⟫` are `≤ 0`) is Rupert.  The proof is the kernel-checked unsatisfiability of a core of the tie view encoding,
with the brackets as class literals and the acute-angle clause as class clause (`rupert_of_coreZpzpzPq`); the mirror orientation is
the reflection of the reference one.

Case `Pq` (parallelogram split): `D = {0, 3, 4, 5}` is a parallelogram (both `det3` of the opposite side pairs against `F.N 3`
vanish), the normal `F.N 4` of facet `E = 046` is not orthogonal to the plane of `G = 235` (`E` not parallel to `G`) and the
normal `F.N 2` of `C = 025` is not orthogonal to the plane of `I = 346` (`C` not parallel to `I`).
-/

set_option autoImplicit false
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.H29.SAT

/-- **Class zpzpz off the obtuse corner `OB1` is closed, case `D` a parallelogram without parallel facet pairs `E // G`, `C // I`.**  The chirality bracket and the five class brackets all have the
reference signs, or all the opposite signs. -/
theorem Minimality.T24.isRupert_offOB1_zpzpz_Pq {x : Fin 7 → EuclideanSpace ℝ (Fin 3)}
    (F : S0xFac 9 Minimality.T24.SAT.s0x_S24 x)
    (hcls : (det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) < 0 ∧ 0 < det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1) ∧ 0 < det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1)) ∨
      (0 < det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) ∧ det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1) < 0 ∧ det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1) < 0))
    (hO : ¬ Minimality.H24K.SAT.OB1 x)
    (hb0 : det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1) = 0)
    (hb2 : det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1) = 0)
    (hb4 : det3 (x 4 - x 2) (x 5 - x 2) (x 6 - x 2) = 0)
    (hD : det3 (x 0 - x 4) (x 3 - x 5) (F.N 3) = 0 ∧ det3 (x 0 - x 5) (x 3 - x 4) (F.N 3) = 0)
    (hEG : ¬ (⟪F.N 4, x 2 - x 3⟫ = 0 ∧ ⟪F.N 4, x 2 - x 5⟫ = 0))
    (hCI : ¬ (⟪F.N 2, x 3 - x 6⟫ = 0 ∧ ⟪F.N 2, x 4 - x 6⟫ = 0)) :
    IsRupert (Finset.univ.image x) := by
  rcases hcls with ⟨hc, h1, h3⟩ | ⟨hc, h1, h3⟩
  · exact Minimality.H24K.SAT.rupert_of_coreZpzpzPq Minimality.H24K.SAT.coreUnsatZpzpzPq F hc hb0 h1 hb2 h3 hb4 hO hD hEG hCI
  · refine isRupert_of_mir (Minimality.H24K.SAT.rupert_of_coreZpzpzPq Minimality.H24K.SAT.coreUnsatZpzpzPq (mirFac F) ?_ ?_ ?_ ?_ ?_ ?_
      (Minimality.H24K.SAT.ob1_mir hO) (Minimality.H24K.SAT.hD_mir F hD) (Minimality.H24K.SAT.pq_mir F hEG hCI).1 (Minimality.H24K.SAT.pq_mir F hEG hCI).2)
    · show det3 (mir (x 1) - mir (x 0)) (mir (x 2) - mir (x 0)) (mir (x 6) - mir (x 0)) < 0
      rw [← mir_sub, ← mir_sub, ← mir_sub, mir_det3]; linarith
    · show det3 (mir (x 2) - mir (x 1)) (mir (x 3) - mir (x 1)) (mir (x 4) - mir (x 1)) = 0
      rw [← mir_sub, ← mir_sub, ← mir_sub, mir_det3, neg_eq_zero]; exact hb0
    · show 0 < det3 (mir (x 2) - mir (x 1)) (mir (x 4) - mir (x 1)) (mir (x 5) - mir (x 1))
      rw [← mir_sub, ← mir_sub, ← mir_sub, mir_det3]; linarith
    · show det3 (mir (x 3) - mir (x 1)) (mir (x 5) - mir (x 1)) (mir (x 6) - mir (x 1)) = 0
      rw [← mir_sub, ← mir_sub, ← mir_sub, mir_det3, neg_eq_zero]; exact hb2
    · show 0 < det3 (mir (x 4) - mir (x 1)) (mir (x 5) - mir (x 1)) (mir (x 6) - mir (x 1))
      rw [← mir_sub, ← mir_sub, ← mir_sub, mir_det3]; linarith
    · show det3 (mir (x 4) - mir (x 2)) (mir (x 5) - mir (x 2)) (mir (x 6) - mir (x 2)) = 0
      rw [← mir_sub, ← mir_sub, ← mir_sub, mir_det3, neg_eq_zero]; exact hb4

#print axioms Minimality.T24.isRupert_offOB1_zpzpz_Pq
