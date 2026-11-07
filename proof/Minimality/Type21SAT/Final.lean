module

public import Minimality.Type21SAT.TopB
public import Minimality.Type21SAT.Mir

@[expose] public section

/-!
# L3, part 29: the top theorem, `type21_of_unsat`

Split on `D ∥ H` (the normals of `D` and `H` proportional): core B for parallel, core A otherwise, both chiralities
(the reflection, `B3Mir`).  No genericity hypothesis.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H21.SAT

variable {x : Fin 7 → ℝ³}

/-- **The facets of a realized type 21 shape.** -/
theorem facets_of_realizes3 (hR : RealizesFaces x (sevenTypeFaces 20)) : Nonempty (Facets21 x) := by
  have hf : sevenTypeFaces 20 = [{0, 1, 4}, {0, 1, 5}, {0, 2, 5, 6}, {0, 4, 6}, {1, 3, 4}, {1, 3, 5},
      {2, 3, 4, 6}, {2, 3, 5}] := by decide
  have key : ∀ i j : Fin 7, i ≠ j → ∃ f ∈ sevenTypeFaces 20, i ∈ f ∧ j ∉ f := by
    rw [hf]; decide
  have hx : Function.Injective x := by
    intro i j hij
    by_contra hne
    obtain ⟨f, hfm, hi, hj⟩ := key i j hne
    obtain ⟨φ, hφ⟩ := hR f hfm
    have h1 := (hφ i).1 hi
    have h2 := (hφ j).2 hj
    rw [hij] at h1
    linarith
  rw [hf] at hR
  obtain ⟨fA, hA⟩ := hR ({0, 1, 4} : Finset (Fin 7)) (by simp)
  obtain ⟨fB, hB⟩ := hR ({0, 1, 5} : Finset (Fin 7)) (by simp)
  obtain ⟨fC, hC⟩ := hR ({0, 2, 5, 6} : Finset (Fin 7)) (by simp)
  obtain ⟨fD, hD⟩ := hR ({0, 4, 6} : Finset (Fin 7)) (by simp)
  obtain ⟨fE, hE⟩ := hR ({1, 3, 4} : Finset (Fin 7)) (by simp)
  obtain ⟨fF, hF⟩ := hR ({1, 3, 5} : Finset (Fin 7)) (by simp)
  obtain ⟨fG, hG⟩ := hR ({2, 3, 4, 6} : Finset (Fin 7)) (by simp)
  obtain ⟨fH, hH⟩ := hR ({2, 3, 5} : Finset (Fin 7)) (by simp)
  exact ⟨Facets21.ofAffine x hx fA fB fC fD fE fF fG fH hA hB hC hD hE hF hG hH⟩


/-- **Case B, both chiralities.**  If the numbered clauses of core B are unsatisfiable, every shape with `Facets21 x` and
`D ∥ H` is Rupert (the other chirality by the reflection). -/
theorem caseB_all (hB : CoreUnsatB) {x : Fin 7 → ℝ³} (T : Facets21 x)
    (hpar : ∃ r : ℝ, T.f046.N = r • T.f235.N) : IsRupert (univ.image x) := by
  by_cases hc : 0 < det3 (x 0 - x 2) (x 3 - x 2) (x 6 - x 2)
  · exact caseB_of_unsat_T hB T hc hpar
  · have hne := T.det_ne
    have hneg : det3 (x 0 - x 2) (x 3 - x 2) (x 6 - x 2) < 0 :=
      lt_of_le_of_ne (not_lt.mp hc) hne
    have hc' : 0 < det3 (mir (x 0) - mir (x 2)) (mir (x 3) - mir (x 2)) (mir (x 6) - mir (x 2)) := by
      rw [chir_mir]; linarith
    refine isRupert_of_mir (caseB_of_unsat_T hB T.mir' hc' ?_)
    obtain ⟨r, hr⟩ := hpar
    refine ⟨r, ?_⟩
    have h : mir (T.f046.N) = r • mir (T.f235.N) := by rw [hr]; ext i; fin_cases i <;> simp [mir]
    exact h

/-- **Top theorem.**  If the numbered clauses of the cores A and B are unsatisfiable, every shape realizing the faces
of type 21 (`sevenTypeFaces 20`) is Rupert.  No genericity hypothesis. -/
theorem type21_of_unsat (hA : CoreUnsatA) (hB : CoreUnsatB) (x : Fin 7 → ℝ³)
    (hR : RealizesFaces x (sevenTypeFaces 20)) : IsRupert (univ.image x) := by
  obtain ⟨T⟩ := facets_of_realizes3 hR
  by_cases hpar : ∃ r : ℝ, T.f046.N = r • T.f235.N
  · exact caseB_all hB T hpar
  · exact caseA_all hA T hpar

end Minimality.H21.SAT

