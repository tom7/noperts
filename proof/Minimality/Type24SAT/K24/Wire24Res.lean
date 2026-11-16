module

public import Minimality.Type24SAT.K24.Wire24
public import Minimality.Type24SAT.K24.Wire24Zero

@[expose] public section

/-!
# Type 24: the refined residual

`Resid24Wide` (`Wire24`) keeps every zero class bracket as residual.  `Wire24Zero` wires the zero-bracket classes off
`OB1`, leaving only `ZRes24` (the class `mpppz`).  `Resid24` is the refined residual: `OB1`, the zero class `mpppz`,
or one of the open classes `mpppp`, `mpppm`.
-/

open scoped RealInnerProductSpace
open Finset

namespace Minimality.T24
open Minimality Minimality.H21 Minimality.T24.SAT

/-- **The type 24 residual**: the obtuse corner `OB1`, the open zero class `mpppz` (`ZRes24`), or one of the open
classes `mpppp`, `mpppm`. -/
def Resid24 (x : Fin 7 → ℝ³) : Prop :=
  H24K.SAT.OB1 x ∨ ZRes24 x ∨ cls24 x false true true true true ∨ cls24 x false true true true false

theorem resid24_of_wide {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (h : Resid24Wide x) :
    IsRupert (univ.image x) ∨ Resid24 x := by
  rcases h with h | h | h | h
  · exact Or.inr (Or.inl h)
  · by_cases hO : H24K.SAT.OB1 x
    · exact Or.inr (Or.inl hO)
    rcases rupert_or_zres24 F hO h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

/-- **The type 24 branch, closed off the residual**: from the nine facet witnesses (`012 016 126 236 046 025 0345 235
346`, the skeleton's `hR`), the points are Rupert or `Resid24 x` holds. -/
theorem rupert_or_resid24 {x : Fin 7 → ℝ³} (fA fB fC fD fE fF fG fH fI : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 1, 2} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 1, 2} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({0, 1, 6} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({0, 1, 6} : Finset (Fin 7)) → fB (x i) < 0))
    (hC : ∀ i, (i ∈ ({1, 2, 6} : Finset (Fin 7)) → fC (x i) = 0) ∧
      (i ∉ ({1, 2, 6} : Finset (Fin 7)) → fC (x i) < 0))
    (hD : ∀ i, (i ∈ ({2, 3, 6} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({2, 3, 6} : Finset (Fin 7)) → fD (x i) < 0))
    (hE : ∀ i, (i ∈ ({0, 4, 6} : Finset (Fin 7)) → fE (x i) = 0) ∧
      (i ∉ ({0, 4, 6} : Finset (Fin 7)) → fE (x i) < 0))
    (hF : ∀ i, (i ∈ ({0, 2, 5} : Finset (Fin 7)) → fF (x i) = 0) ∧
      (i ∉ ({0, 2, 5} : Finset (Fin 7)) → fF (x i) < 0))
    (hG : ∀ i, (i ∈ ({0, 3, 4, 5} : Finset (Fin 7)) → fG (x i) = 0) ∧
      (i ∉ ({0, 3, 4, 5} : Finset (Fin 7)) → fG (x i) < 0))
    (hH : ∀ i, (i ∈ ({2, 3, 5} : Finset (Fin 7)) → fH (x i) = 0) ∧
      (i ∉ ({2, 3, 5} : Finset (Fin 7)) → fH (x i) < 0))
    (hI : ∀ i, (i ∈ ({3, 4, 6} : Finset (Fin 7)) → fI (x i) = 0) ∧
      (i ∉ ({3, 4, 6} : Finset (Fin 7)) → fI (x i) < 0)) :
    IsRupert (univ.image x) ∨ Resid24 x := by
  rcases rupert_or_resid24_wide fA fB fC fD fE fF fG fH fI hA hB hC hD hE hF hG hH hI with h | h
  · exact Or.inl h
  · refine resid24_of_wide (mkFac24 ![fA, fB, fF, fG, fE, fC, fH, fD, fI] ?_) h
    intro t i
    fin_cases t
    exacts [hA i, hB i, hF i, hG i, hE i, hC i, hH i, hD i, hI i]

end Minimality.T24
