module

public import Minimality.Type24SAT.K24.LinkPpmpzDw

@[expose] public section

/-!
# Type 24, class ppmpz off the obtuse corner: `Minimality.T24.isRupert_offOB1_ppmpz_Dw`

A type 24 shape (nine facets `s0x_S24`) with the five brackets `[1234]+ [1245]+ [1356]- [1456]+ [2456]0` and chirality `[0126] < 0`, or with all six signs
reversed (the mirror image), and with an acute face angle at vertex `1` (not all of `⟪x0 - x1, x2 - x1⟫`, `⟪x0 - x1, x6 - x1⟫`,
`⟪x2 - x1, x6 - x1⟫` are `≤ 0`) is Rupert.  The proof is the kernel-checked unsatisfiability of a core of the tie view encoding,
with the brackets as class literals and the acute-angle clause as class clause (`rupert_of_corePpmpzDw`); the mirror orientation is
the reflection of the reference one.

Case `Dw` (double wall): as `notP`, and the wall `25 // 46`, `z0 = z3 = z4 = z5` holds in the form `WallHyp F` (CasesWall.lean): the
nine zero literals of `unitsWall` are class literals of the core.
-/

set_option autoImplicit false
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.H29.SAT

/-- **Class ppmpz off the obtuse corner `OB1` is closed, double wall `25 // 46`, `z0 = z3 = z4 = z5`, `D` not a parallelogram.**  The chirality bracket and the five class brackets all have the
reference signs, or all the opposite signs. -/
theorem Minimality.T24.isRupert_offOB1_ppmpz_Dw {x : Fin 7 → EuclideanSpace ℝ (Fin 3)}
    (F : S0xFac 9 Minimality.T24.SAT.s0x_S24 x)
    (hcls : (det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) < 0 ∧ 0 < det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1) ∧ 0 < det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1) ∧ det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1) < 0 ∧ 0 < det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1)) ∨
      (0 < det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) ∧ det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1) < 0 ∧ det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1) < 0 ∧ 0 < det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1) ∧ det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1) < 0))
    (hO : ¬ Minimality.H24K.SAT.OB1 x)
    (hb : det3 (x 4 - x 2) (x 5 - x 2) (x 6 - x 2) = 0)
    (hP : ¬ (det3 (x 0 - x 4) (x 3 - x 5) (F.N 3) = 0 ∧ det3 (x 0 - x 5) (x 3 - x 4) (F.N 3) = 0))
    (hW : Minimality.H24K.SAT.WallHyp F) :
    IsRupert (Finset.univ.image x) := by
  rcases hcls with ⟨hc, h0, h1, h2, h3⟩ | ⟨hc, h0, h1, h2, h3⟩
  · exact Minimality.H24K.SAT.rupert_of_corePpmpzDw Minimality.H24K.SAT.coreUnsatPpmpzDw F hc h0 h1 h2 h3 hb hO hP hW
  · refine isRupert_of_mir (Minimality.H24K.SAT.rupert_of_corePpmpzDw Minimality.H24K.SAT.coreUnsatPpmpzDw (mirFac F) ?_ ?_ ?_ ?_ ?_ ?_
      (Minimality.H24K.SAT.ob1_mir hO) (Minimality.H24K.SAT.notP_mir F hP) (Minimality.H24K.SAT.wall_mir F hW))
    · show det3 (mir (x 1) - mir (x 0)) (mir (x 2) - mir (x 0)) (mir (x 6) - mir (x 0)) < 0
      rw [← mir_sub, ← mir_sub, ← mir_sub, mir_det3]; linarith
    · show 0 < det3 (mir (x 2) - mir (x 1)) (mir (x 3) - mir (x 1)) (mir (x 4) - mir (x 1))
      rw [← mir_sub, ← mir_sub, ← mir_sub, mir_det3]; linarith
    · show 0 < det3 (mir (x 2) - mir (x 1)) (mir (x 4) - mir (x 1)) (mir (x 5) - mir (x 1))
      rw [← mir_sub, ← mir_sub, ← mir_sub, mir_det3]; linarith
    · show det3 (mir (x 3) - mir (x 1)) (mir (x 5) - mir (x 1)) (mir (x 6) - mir (x 1)) < 0
      rw [← mir_sub, ← mir_sub, ← mir_sub, mir_det3]; linarith
    · show 0 < det3 (mir (x 4) - mir (x 1)) (mir (x 5) - mir (x 1)) (mir (x 6) - mir (x 1))
      rw [← mir_sub, ← mir_sub, ← mir_sub, mir_det3]; linarith
    · show det3 (mir (x 4) - mir (x 2)) (mir (x 5) - mir (x 2)) (mir (x 6) - mir (x 2)) = 0
      rw [← mir_sub, ← mir_sub, ← mir_sub, mir_det3, neg_eq_zero]; exact hb

#print axioms Minimality.T24.isRupert_offOB1_ppmpz_Dw
