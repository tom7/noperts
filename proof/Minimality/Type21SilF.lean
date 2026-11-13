module

public import Minimality.Type21SilE

@[expose] public section

set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace H21

/-- Facet vertex sets, indexed `A..H = 0..7`: `014, 015, 0256, 046, 134, 135, 2346, 235`. -/
def h21S : Fin 8 → Finset (Fin 7) :=
  ![{0, 1, 4}, {0, 1, 5}, {0, 2, 5, 6}, {0, 4, 6}, {1, 3, 4}, {1, 3, 5}, {2, 3, 4, 6}, {2, 3, 5}]

/-- The eight facets of type 21 as an indexed family. -/
structure Fac8 (x : Fin 7 → ℝ³) where
  f : Fin 8 → ℝ³ → ℝ
  N : Fin 8 → ℝ³
  hN : ∀ t y z, f t y - f t z = ⟪N t, y - z⟫
  zero : ∀ t, ∀ i ∈ h21S t, f t (x i) = 0
  neg : ∀ t, ∀ i ∉ h21S t, f t (x i) < 0

noncomputable def fac8 {x : Fin 7 → ℝ³} (T : Facets21 x) : Fac8 x where
  f := ![T.f014.f, T.f015.f, T.f0256.f, T.f046.f, T.f134.f, T.f135.f, T.f2346.f, T.f235.f]
  N := ![T.f014.N, T.f015.N, T.f0256.N, T.f046.N, T.f134.N, T.f135.N, T.f2346.N, T.f235.N]
  hN t := by
    fin_cases t
    exacts [T.f014.hN, T.f015.hN, T.f0256.hN, T.f046.hN, T.f134.hN, T.f135.hN, T.f2346.hN,
      T.f235.hN]
  zero t := by
    fin_cases t
    exacts [T.f014.zero, T.f015.zero, T.f0256.zero, T.f046.zero, T.f134.zero, T.f135.zero,
      T.f2346.zero, T.f235.zero]
  neg t := by
    fin_cases t
    exacts [T.f014.neg, T.f015.neg, T.f0256.neg, T.f046.neg, T.f134.neg, T.f135.neg,
      T.f2346.neg, T.f235.neg]

variable {x : Fin 7 → ℝ³}

theorem Fac8.le (F : Fac8 x) (t : Fin 8) (m : Fin 7) : F.f t (x m) ≤ 0 := by
  by_cases h : m ∈ h21S t
  · rw [F.zero t m h]
  · exact (F.neg t m h).le

/-- Facing up: `j` in the facet, `i` not. -/
theorem Fac8.up (F : Fac8 x) (t : Fin 8) {i j : Fin 7} (hj : j ∈ h21S t) (hi : i ∉ h21S t) :
    0 < F.f t (x j) - F.f t (x i) := by
  rw [F.zero t j hj]; linarith [F.neg t i hi]

/-- Facing down: `i` in the facet, `j` not. -/
theorem Fac8.dn (F : Fac8 x) (t : Fin 8) {i j : Fin 7} (hi : i ∈ h21S t) (hj : j ∉ h21S t) :
    F.f t (x j) - F.f t (x i) < 0 := by
  rw [F.zero t i hi]; linarith [F.neg t j hj]

end H21
end Minimality
